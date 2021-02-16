SRCS    := $(wildcard *.v)
OBJS := $(SRCS:.v=*.vos)

$(OBJS): Stlc.v Gadgets.v
	for f in $^; do coqc -vos $$f; done

Stlc.v: Stlc.ott
	ott -i $< -o $@
	patch -u $@ -i stlc.patch

.PHONY: ott
ott: Stlc.v

.PHONY: all
all: Stlc.v $(OBJS)

.PHONY: clean
clean:
	-rm Stlc.v *.vos *.glob *.vo *.vok
