all : Makefile.coq
	mkdir -p docs
	[ -d html ] || ln -s docs html
	$(MAKE) -f Makefile.coq html

Makefile.coq : _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean :
	rm -f \
	  Makefile.coq \
	  theories/*.glob \
	  theories/*.vo \
	  theories/*.d \
	  theories/*.aux \
	  theories/.*.aux

.PHONY: all clean
