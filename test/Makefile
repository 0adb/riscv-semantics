.PHONY: all clean

SRCDIR=src
BUILDDIR=build

SOURCES=$(notdir $(wildcard $(SRCDIR)/*.c))
TESTS=$(basename $(SOURCES))
ELF=$(addprefix build/,$(TESTS))
ELF32=$(addsuffix 32,$(ELF))
ELF64=$(addsuffix 64,$(ELF))
HEX32=$(addsuffix .hex,$(ELF32))
HEX64=$(addsuffix .hex,$(ELF64))
ELF2HEX=../elf2hex

SOURCESV=$(notdir $(wildcard $(SRCDIR)/vector/*.c))
TESTSV=$(basename $(SOURCESV))
ELFV=$(addprefix build/,$(TESTSV))
ELF64V=$(addsuffix 64v,$(ELFV))
HEX64V=$(addsuffix .hex, $(ELF64V))


RISCVCC64=riscv-none-embed-gcc -march=rv64im -mabi=lp64 -static -nostdlib -nostartfiles -mcmodel=medany
RISCVCC32=riscv-none-embed-gcc -march=rv32im -mabi=ilp32 -static -nostdlib -nostartfiles -mcmodel=medany
RISCVCC64V=riscv64-unknown-elf-gcc -march=rv64imv -mabi=lp64 -static -nostdlib -nostartfiles -mcmodel=medany
OBJDUMP64V=riscv64-unknown-elf-objdump -drCS 

all: $(HEX32) $(HEX64) $(HEX64V)
all64: $(HEX64) 

$(ELF2HEX)/elf2hex:
	$(MAKE) -C $(ELF2HEX)

mpFence: mpFence.S
	$(RISCVCC64) -c mpFence.S -o $(BUILDDIR)/mpFence64.o
	$(RISCVCC64) -o $(BUILDDIR)/mpFence64 $(BUILDDIR)/mpFence64.o
mp: mp.S
	$(RISCVCC64) -c mp.S -o $(BUILDDIR)/mp64.o
	$(RISCVCC64) -o $(BUILDDIR)/mp64 $(BUILDDIR)/mp64.o
sb: sbData.S
	$(RISCVCC64) -c sbData.S -o $(BUILDDIR)/sbData64.o
	$(RISCVCC64) -o $(BUILDDIR)/sbData64 $(BUILDDIR)/sbData64.o
sbFence: sbFence.S
	$(RISCVCC64) -c sbFence.S -o $(BUILDDIR)/sbFence64.o
	$(RISCVCC64) -o $(BUILDDIR)/sbFence64 $(BUILDDIR)/sbFence64.o



init32.o: init.S
	$(RISCVCC32) -c init.S -o init32.o

init64.o: init.S
	$(RISCVCC64) -c init.S -o init64.o

init64v.o: init.S
	$(RISCVCC64V) -c init.S -o init64v.o

mmio32.o: mmio.c
	$(RISCVCC32) -c mmio.c -o mmio32.o

mmio64.o: mmio.c
	$(RISCVCC64) -c mmio.c -o mmio64.o

mmio64v.o: mmio.c
	$(RISCVCC64V) -c mmio.c -o mmio64v.o

$(BUILDDIR)/%32.hex: $(ELF2HEX)/elf2hex $(SRCDIR)/%.c init32.o mmio32.o mmio.ld
	mkdir -p $(BUILDDIR)
	$(RISCVCC32) -c $(SRCDIR)/$*.c -o intermediate32.o
	$(RISCVCC32) -o $(BUILDDIR)/$*32 -Tmmio.ld intermediate32.o init32.o mmio32.o
	$(ELF2HEX)/elf2hex $(BUILDDIR)/$*32 0 16G $(BUILDDIR)/$*32.hex
	rm intermediate32.o

$(BUILDDIR)/%64.hex: $(ELF2HEX)/elf2hex $(SRCDIR)/%.c init64.o mmio64.o mmio.ld
	mkdir -p $(BUILDDIR)
	$(RISCVCC64) -c $(SRCDIR)/$*.c -o intermediate64.o
	$(RISCVCC64) -o $(BUILDDIR)/$*64 -Tmmio.ld intermediate64.o init64.o mmio64.o
	$(ELF2HEX)/elf2hex $(BUILDDIR)/$*64 0 16G $(BUILDDIR)/$*64.hex
	rm intermediate64.o


$(BUILDDIR)/%64v.hex: $(ELF2HEX)/elf2hex $(SRCDIR)/vector/%.c init64v.o mmio64v.o mmio.ld
	mkdir -p $(BUILDDIR)
	$(RISCVCC64V) -g -c $(SRCDIR)/vector/$*.c -o intermediate64v.o
	$(OBJDUMP64V) intermediate64v.o > $(BUILDDIR)/$*64v_objdump.txt
	$(RISCVCC64V) -o $(BUILDDIR)/$*64v -Tmmio.ld intermediate64v.o init64v.o mmio64v.o
	$(ELF2HEX)/elf2hex $(BUILDDIR)/$*64v 0 16G $(BUILDDIR)/$*64v.hex
	rm intermediate64v.o


clean:
	rm -f intermediate32.o init32.o mmio32.o
	rm -f intermediate64.o init64.o mmio64.o
	rm -f intermediate64v.o init64v.o mmio64v.o
	rm -rf build
