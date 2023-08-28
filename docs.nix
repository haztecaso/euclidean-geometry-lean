{ stdenv, texlive }:
stdenv.mkDerivation {
  name = "euclidean-geometry-lean-memoria";
  version = "0.0.2";

  src = ./memoria;

  buildInputs = [ texlive.combined.scheme-full ];

  buildPhase = ''
    mkdir -p .cache/texmf-var
    TEXMFHOME=.cache TEXMFVAR=.cache/texmf-var latexmk -interaction=nonstopmode -pdf -lualatex memoria.tex
    TEXMFHOME=.cache TEXMFVAR=.cache/texmf-var latexmk -interaction=nonstopmode -pdf -lualatex Axiomas\ y\ definiciones\ de\ Hilbert.tex
  '';

  installPhase = ''
    mkdir -p $out
    cp memoria.pdf $out/
  '';

}
