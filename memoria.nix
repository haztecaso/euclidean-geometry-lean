{ stdenv, texlive }:
stdenv.mkDerivation {
  name = "euclidean-geometry-lean-memoria";
  version = "0.0.2";

  src = ./.;

  buildInputs = [ texlive.combined.scheme-full ];

  buildPhase = ''
    mkdir -p .cache/texmf-var
    TEXMFHOME=.cache TEXMFVAR=.cache/texmf-var latexmk -interaction=nonstopmode -pdf -lualatex memoria.tex
  '';

  installPhase = ''
    mkdir -p $out
    cp memoria.pdf $out/
  '';

}
