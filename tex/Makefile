
.PHONY: Main
Main: Main.pdf

Main.pdf: tex
	latexmk -pdf Main

.PHONY: watch
watch: tex
	latexmk -pdf -pvc Main

.PHONY: tex
tex: Main.lhs
	lhs2TeX --agda Main.lhs -o Main.tex

.PHONY: clean
clean:
	latexmk -C Main
	rm Main.tex
