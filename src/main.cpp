#include <iostream>
#include <fstream>
#include <vector>
#include <cstdio>
#include <cstdlib>
#include <cmath>
#include <cctype>
#include <limits>

// cstdint would be better, but it's in C++0x; gcc's 0x support is still beta.
#include <stdint.h>

extern "C" {
#include "hexdump.h"
}

using namespace std;

// CRC-16/CCITT implementation
// Based on code from http://www.sanity-free.org/133/crc_16_ccitt_in_csharp.html
class CRC16 {
	private:
		static const unsigned int poly = 4129;
		unsigned int table[256];
		unsigned int crcval, initval;
	public:
		CRC16(unsigned int initval = 0xFFFF) {
			this->initval = this->crcval = initval;

			unsigned int temp, a;
			for (size_t i=0; i<(sizeof(this->table)/sizeof(this->table[0])); ++i) {
				temp = 0;

				a = (unsigned int) i << 8;
				
				for (int j=0; j < 8; ++j) {
					if(((temp ^ a) & 0x8000) != 0) {
						temp = (unsigned int)((temp << 1) ^ poly);
					} else {
						temp <<= 1;
					}
					a <<= 1;
				}

				table[i] = temp;
			}
		}

		// calculate crc without updating internal state
		unsigned int calculate(void *buf, size_t len) {
			unsigned int crc = this->crcval;

			for (size_t i=0; i<len; i++) {
				char x = ((unsigned char *)buf)[i];
				crc = ((crc << 8) ^ this->table[((crc >> 8) ^ x) & 0xff]) & 0xffff;
			}

			return crc;
		}

		// calculate crc and update internal state afterwards
		// used for partial crcs
		unsigned int update(void *buf, size_t len) {
			this->crcval = this->calculate(buf, len);
			return this->crcval;
		}

		// reset crc to initialisation default
		void reset(void) {
			this->crcval = this->initval;
		}

		// reset crc to arbitrary value and change init default accordingly
		void reset(unsigned int initval) {
			this->crcval = this->initval = initval;
		}
};

/////////////////////////////////////////////////////////////////////////////

class DiscFerretImage {
	private:
		ifstream file;
		size_t file_len;
		int file_version;
	public:
		DiscFerretImage(const char *filename);
		void NextTrack(vector<int> &timings, vector<int> &indexes, unsigned int &cyl, unsigned int &head, unsigned int &sec);
};

DiscFerretImage::DiscFerretImage(const char *filename)
{
	// open the file
	file.exceptions(ifstream::failbit | ifstream::badbit);
	file.open(filename, ios::in | ios::binary);

	// find out how big the file is
	file.seekg(0, ios::end);
	file_len = file.tellg();
	file.seekg(0, ios::beg);

	// read magic number
	char mnum[4];
	file.read(mnum, 4);
	if ((mnum[0] != 'D') || (mnum[1] != 'F') || (mnum[2] != 'E')) {
		printf("ERROR: File has bad magic!\n");
		throw exception();
	}

	switch (mnum[3]) {
		case 'R':
			file_version = 1;
			printf("WARNING: This is an old-format DiscFerret image. The data stream may contain invalid data and should not be trusted.\n");
			break;
		case '2':
			file_version = 2;
			break;
		default:
			printf("ERROR: File has bad magic!\n");
			throw exception();
	}
}

void DiscFerretImage::NextTrack(vector<int> &timings, vector<int> &indexes, unsigned int &cyl, unsigned int &head, unsigned int &sec)
{
	uint8_t hdr[10];
	uint32_t plen;

	// Read the track header
	file.read((char *)hdr, 10);
	cyl  = ((uint16_t)hdr[0] << 8) + (uint16_t)hdr[1];
	head = ((uint16_t)hdr[2] << 8) + (uint16_t)hdr[3];
	sec  = ((uint16_t)hdr[4] << 8) + (uint16_t)hdr[5];
	plen = ((uint32_t)hdr[6] << 24) +
		((uint32_t)hdr[7] << 16) +
		((uint32_t)hdr[8] << 8) +
		(uint16_t)hdr[9];

	// Make sure payload length is sane
	if (plen > (file_len - file.tellg())) {
		throw exception();
	}

	// Read trackdata into a buffer and decode
	uint8_t *tbuf = new uint8_t[plen];
	file.read(reinterpret_cast<char *>(tbuf), plen);

	// Carry and current absolute time offset
	uint32_t carry = 0, cur_t = 0;

	// Clear the output buffers
	indexes.clear();
	timings.clear();

	if (file_version == 1) {
		// Old-style DFER image
		carry = 0;
		for (streampos i=0; i<plen; i+=1) {
			uint8_t d = tbuf[i] & 0x7f;

			if (tbuf[i] & 0x80) {
				// MSBit set - index pulse
				indexes.push_back(cur_t + carry + static_cast<uint32_t>(d));
			}

			if (d == 0) {
				// timing value == 0 --> carry
				carry += 127;
			} else {
				// timing value != 0 --> timing tick
				timings.push_back(carry + static_cast<uint32_t>(d));
				carry = 0;
			}
		}
	} else if (file_version == 2) {
		// New-style DFE2 image
		carry = cur_t = 0;

		for (streampos i=0; i<plen; i+=1) {
			uint8_t d = tbuf[i] & 0x7f;

			if (d == 0x7F) {
				// Lower 7 bit value == 0x7F --> there was a carry
				carry += 127;
				cur_t += 127;
			} else if (tbuf[i] & 0x80) {
				// MSbit set --> index store
				carry += d;
				cur_t += d;
				indexes.push_back(cur_t);
			} else {
				// MSbit clear and not an index store - must be a timing store
				timings.push_back(carry + static_cast<uint32_t>(d));
				cur_t += d;
				carry = 0;
			}
		}

		// Carry may be nonzero at this point. If that is the case, we have
		// only captured part of a transition and we should ignore it, not
		// add it to the data buffer (which will cause corruption).
	} else {
		// No idea what happened here... don't recognise this file version.
		throw exception();
	}
}


// Decode 16 MFM bits into a single byte
unsigned char decodeMFM(vector<bool> bits, size_t startpos)
{
	uint8_t buf;
	int cnt = 1;

	// Get 8 bits of data, discard every other bit
	for (vector<bool>::iterator i = bits.begin()+startpos; i<bits.begin()+startpos+16; i++) {
		if ((cnt % 2) == 0) {
			buf = (buf << 1) + (*i ? 1 : 0);
		}
		cnt++;
	}

	return buf;
}

void dump_array(unsigned char *d, size_t len)
{
#if 0
	int i=0;

	printf("unsigned char data_array[] = {\n");
	while (len > 0) {
		printf("0x%02X%s", *(d++), (len-->1)?", ":"");
		if (i++ == 15) {
			printf("\n");
			i=0;
		}
	}
	printf("%s};\n", i>0?"\n":"");
#endif
}

// main fnc
int main(int argc, char **argv)
{
	unsigned int buf[128*1024];
	size_t buflen;

	if (argc < 2) {
		cout << "syntax: " << argv[0] << " filename\n";
		return -1;
	}

	// limit scope of 'x'
	{
		DiscFerretImage dfi(argv[1]);

		vector<int> timing, index;
		unsigned int cyl, head, sec;

		dfi.NextTrack(timing, index, cyl, head, sec);

		buflen = timing.size();
		for (size_t x=0; x<buflen; x++) {
			buf[x] = timing[x];
		}

		printf("DFI track CHS %u:%u:%u; buflen = %lu\n", cyl, head, sec, (unsigned long)buflen);
	}

	// Data separator begins here.
	vector<bool> mfmbits;
#ifdef VCD
	FILE *vcd = fopen("values.vcd", "wt");
	fprintf(vcd, "$version DiscFerret Analyser D2/DPLL 0.1 $end\n"
			"$timescale 1 ns $end\n"
			"$var reg 1 * clock $end\n"
			"$var reg 1 ' pll_clock $end\n"
			"$var reg 1 ! rd_data $end\n"
			"$var reg 1 %% rd_data_latched $end\n"
			"$var reg 1 ^ shaped_data $end\n"
			"$var reg 8 & pjl_shifter $end\n"
			"$var reg 1 ( data_window $end\n"
			"$upscope $end\n"
			"$enddefinitions $end\n"
			"$dumpall\n"
			"0*\n"
			"0'\n"
			"0!\n"
			"0%%\n"
			"0^\n"
			"b00000000 &\n"
			"0(\n"
			"$end\n"
		   );
#endif
	/**
	 * This is a software implementation of Jim Thompson's Phase-Jerked Loop
	 * design, available from AnalogInnovations.com as the PDF file
	 * "FloppyDataExtractor.pdf".
	 *
	 * This consists of:
	 *   A data synchroniser which forces RD_DATA to be active for 2 clock cycles.
	 *   A counter which increments constantly while the PLL is running, and is 
	 *     reset to zero when a data bit is detected.
	 *   A flip-flop which changes state when the counter reaches half its maximum
	 *     value
	 *
	 * The actual values of NSECS_PER_ACQ and NSECS_PER_PLLCK don't really matter.
	 * What actually matters is the ratio between the two -- if you have a 40MHz
	 * acquisition clock and a PLL clock of 16MHz (data rate 500kbps), then the
	 * starting values will be NSECS_PER_ACQ=25 and NSECS_PER_PLLCK=62.5. Problem
	 * is, 62.5 isn't an integer multiple, so we might have issues with
	 * short-term clock jitter. So we multiply by two, which gives us
	 * NSECS_PER_ACQ=50 and NSECS_PER_PLLCK=125, and a timestep of 0.5ns. Much
	 * better.
	 *
	 * We can also change the PJL Counter maximum value if it makes the math
	 * work out better. Be careful though -- reducing the value WILL reduce the
	 * number of available phase-shift steps and thus the PLL accuracy.
	 *
	 * Now we know the ticks-per-acqclk and ticks-per-pllclk values, we can
	 * figure out the optimal timer increment --
	 *   TIMER_INCREMENT = gcd(NSECS_PER_ACQ, NSECS_PER_PLLCK)
	 *   (gcd == greatest common divisor)
	 *
	 * Ideally we want a TIMER_INCREMENT greater than 1. If we get an increment
	 * of 1, then the loop has to run at 1x speed and will be SLOW. Try
	 * increasing NSECS_PER_ACQ and NSECS_PER_PLLCK (multiply them by the same
	 * number e.g. 2, 4, 8, ...), then run the gcd again. Problem is, this isn't
	 * going to gain much if anything in speed because you're going to be running
	 * more loops at a faster rate, thus it's a zero-gain :-/
	 */

	// Nanoseconds counters. Increment once per loop or "virtual" nanosecond.
	unsigned long nsecs1 = 0, nsecs2=0;
	// Number of nanoseconds per acq tick -- (1/freq)*1e9. This is valid for 40MHz.
	const unsigned long NSECS_PER_ACQ = (1e10 / 100e6);
	// Number of nanoseconds per PLLCK tick -- (1/16e6)*1e9. 16MHz. 
	// This should be the reciprocal of 32 times the data rate in kbps, multiplied
	// by 1e9 to get the time in nanoseconds.
	// That is, (1/(TRANSITIONS_PER_BITCELL * PJL_COUNTER_MAX * DATA_RATE))*1e9
	const unsigned long NSECS_PER_PLLCK = (1e10 / 640e6);
	// Number of clock increments per loop (timing granularity). Best-case value
	// for this is gcd(NSECS_PER_ACQ, NSECS_PER_PLLCK).
	const unsigned long TIMER_INCREMENT = 1;
	// Maximum value of the PJL counter. Determines the granularity of phase changes.
	const unsigned char PJL_COUNTER_MAX = 64;

	// Iterator for data buffer
	size_t i = 0;

	// True if RD_DATA was high in this clock cycle
	bool rd_latch = false;
	// Same but only active for 2Tcy (SHAPED_DATA)
	int shaped_data = 0;

	// Phase Jerked Loop counter
	unsigned char pjl_shifter = 0;

	// data window
	unsigned char data_window = 0;

	do {
#ifdef VCD
		{ static unsigned long long clocks = 0; fprintf(vcd, "#%lld\n", clocks++); }
#endif
		// Increment counters
		nsecs1 += TIMER_INCREMENT;
		nsecs2 += TIMER_INCREMENT;
#ifdef VCD
		if ((nsecs1 % NSECS_PER_ACQ) == 0) { fprintf(vcd, "1*\n"); }
		if ((nsecs1 % NSECS_PER_ACQ) == (NSECS_PER_ACQ/2)) { fprintf(vcd, "0*\n"); }
		if (nsecs1 == (buf[i] * NSECS_PER_ACQ)) { fprintf(vcd, "0!\n"); } else { fprintf(vcd, "1!\n"); }
		if ((nsecs1 % NSECS_PER_PLLCK) == 0) { fprintf(vcd, "1'\n"); }
		if ((nsecs1 % NSECS_PER_PLLCK) == (NSECS_PER_PLLCK/2)) { fprintf(vcd, "0'\n"); }
#endif
		// Loop 1 -- floppy disc read channel
		if (nsecs1 >= (buf[i] * NSECS_PER_ACQ)) {
			// Flux transition. Set the read latches.
			rd_latch = true;
			shaped_data = 2;

			// Update nanoseconds counter for read channel, retain error factor
			nsecs1 -= (buf[i] * NSECS_PER_ACQ);

			// Update buffer position
			i++;
		}
#ifdef VCD
		fprintf(vcd, "%d%%\n", rd_latch);
		fprintf(vcd, "%d^\n", (shaped_data > 0) ? 1 : 0);
#endif
		// Loop 2 -- DPLL channel
		if (nsecs2 >= NSECS_PER_PLLCK) {
			// Update nanoseconds counter for PLL, retain error factor
			nsecs2 -= NSECS_PER_PLLCK;

			// PJL loop
			if (shaped_data > 0) {
				pjl_shifter = 0;
			} else {
				// increment shifter
				pjl_shifter = (pjl_shifter + 1) % PJL_COUNTER_MAX;
			}

			// DWIN detect
			if (pjl_shifter == (PJL_COUNTER_MAX / 2)) {
				// Data window toggle. Latch the current RD_LATCH blob into the output buffer.
				mfmbits.push_back(rd_latch);
				// Clear the data latch ready for the next data window.
				rd_latch = false;
				// Update DWIN
				data_window ^= 0x01;
			}

			// Update shaped-data time counter
			if (shaped_data > 0) shaped_data--;
		}

#ifdef VCD
		fprintf(vcd, "%d(\n", data_window);
		fputc('b', vcd);
		for (int x=0; x<8; x++) if (pjl_shifter & (1<<(7-x))) fputc('1', vcd); else fputc('0', vcd);
		fprintf(vcd, " &\n");
		if (mfmbits.size() == 1000) { printf("Got 1000 bits, terminating run.\n"); break; }
#endif
	} while (i < buflen);

#ifdef VCD
	fclose(vcd);
#endif

	printf("mfmbits count = %lu\n", mfmbits.size());

	// Now process the MFM bitstream to find the sync markers
	unsigned long bits = 0;
	unsigned int num_idam = 0, num_dam = 0;
	size_t next_data_dump = 0;
	bool chk_data_crc = false;
	for (size_t i=0; i<mfmbits.size(); i++) {
		size_t dump=0;

		// get next bit
		bits = ((bits << 1) + (mfmbits[i] ? 1 : 0)) & 0xffffffff;

		// Scan the last 32 MFM-bits (16 data bits) for an MFM pattern we recognise
		if ((bits & 0xffffFF30) == 0x44895510) {	// Sync-A1, 0b1111_x1xx ==> IDAM  (x=don't care)
			// ID Address Mark (IDAM)
			// i+1 because "i" is the last bit of the IDAM marker; we want the
			// first bit of the new data byte (encoded word).
			printf("IDAM at %lu\n", i+1);
			num_idam++;
			dump = 5;
			chk_data_crc = false;

			// decode the IDAM
			unsigned char *idambuf = new unsigned char[6];
			for (size_t x=0; x<5; x++) {
				idambuf[x] = decodeMFM(mfmbits, i+(x*16)+1);
			}

			// Decode Cylinder from IDENT byte and Cyl_Lo
			// (the three upper bits are stored in IDENT, rest are in CYL_LO)
			// Ref: WD2010-05 datasheet page 3-130, Western Digital
			unsigned int cylinder = 0;
			cylinder = decodeMFM(mfmbits, i-15);
			switch (cylinder) {
				case 0xFE:	cylinder = 0;    break;
				case 0xFF:	cylinder = 256;  break;
				case 0xFC:	cylinder = 512;  break;
				case 0xFD:	cylinder = 768;  break;
				case 0xF6:	cylinder = 1024; break;
				case 0xF7:	cylinder = 1280; break;
				case 0xF4:	cylinder = 1536; break;
				case 0xF5:	cylinder = 1792; break;
				default:	cylinder = 0;			// TODO flag error?
			}
			cylinder += static_cast<unsigned int>(idambuf[0]);

			printf("\tIDAM = Cylinder %4d, Head %d, Sector %2d; %s; sector size ",
					cylinder, idambuf[1] & 0x07, idambuf[2],
					(idambuf[1] & 0x80) ? "BAD BLOCK" : "ok  block");
			switch ((idambuf[1] >> 5) & 0x03) {
				case 0x00:
					next_data_dump = 256;
					break;
				case 0x01:
					next_data_dump = 512;
					break;
				case 0x02:
					next_data_dump = 1024;
					break;
				case 0x03:
					next_data_dump = 128;
					break;
				default:
					printf("unknown (0x%02X)", (idambuf[1] >> 5) & 0x03);
					next_data_dump = 0;
					break;
			}
			if (next_data_dump != 0) printf("%ld", next_data_dump);

			// check the CRC
			CRC16 c = CRC16();
			c.update((char *)"\xA1\xFE", 2);
			unsigned int crc = c.update(idambuf, 3);
			unsigned int got_crc = (idambuf[3] << 8) | idambuf[4];
			printf("; RCRC=%04X", c.update(&idambuf[3], 2));
			printf("; CRC=%04X (calc'd %04X) %s\n", got_crc, crc, (got_crc==crc) ? "(ok)" : "BAD");

			delete idambuf;
		} else if ((bits & 0xffffffff) == 0x4489554A) {		// Sync-A1, 0xF8 ==> DAM
			// Data Address Mark
			// i+1 because "i" is the last bit of the DAM marker; we want the
			// first bit of the new data byte (encoded word).
			printf("DAM at %lu%s\n", i+1, (next_data_dump == 0) ? " [ERR: no preceding IDAM]" : "");
			num_dam++;
			dump = next_data_dump;
			next_data_dump = 0;
			chk_data_crc = true;
		}

		if (dump > 0) {
			// dump next few bytes of data in hex
			// TODO: use hex_dump() and a char array instead
			// i+1 because "i" is the last bit of the (I)DAM marker; we want
			// the first bit of the new data byte (encoded word).
			//
			unsigned char *buffer = new unsigned char[dump+2];
			const size_t EXTRA=6*0;
			for (size_t x=0; x<dump+EXTRA; x++) {
				buffer[x] = decodeMFM(mfmbits, i+(x*16)+1);
			}
			hex_dump(buffer, dump+EXTRA);
			dump_array(buffer, dump+EXTRA);

			if (chk_data_crc) {
				CRC16 c = CRC16();
				c.update((char *)"\xA1\xF8", 2);
				unsigned int crc = c.update(buffer, dump);
				printf("\tData record CRC=%04X (calc'd %04X) %s\n", (buffer[dump+0] << 8) | buffer[dump+1],
						crc,
						((unsigned int)((buffer[dump+0] << 8) | buffer[dump+1])==crc) ? "(ok)" : "BAD");
			}

			delete[] buffer;
		}
	}

	printf("Seen: %d IDAMs, %d DAMs\n", num_idam, num_dam);

	// clean-up goes here
	return 0;
}
