# make            build the exercises and record the statement files (what you run while writing a statement)
# make check      run the mechanical checks after the LLM has worked (see README, "Checklist")
# make setup      first-time setup: download the prebuilt dependencies, then build
# make solutions  unpack the reference solutions into solutions/ (for after your own attempt)

.PHONY: build check check-model check-rust setup solutions pack-solutions

build:
	lake build
	@./check.sh snapshot

check:
	@./check.sh

check-model:
	@./check.sh model

check-rust:
	@./check.sh rust

setup:
	lake exe cache get
	lake build

solutions:
	tar xzf solutions.tar.gz
	@echo "unpacked into solutions/; build them with 'lake build Solutions'"

# Maintainers: re-create the archive from solutions/ after editing them.
pack-solutions:
	lake build Solutions
	tar czf solutions.tar.gz solutions
