{ stdenv, texlive }:
stdenv.mkDerivation {
  name = "euclidean-geometry-lean-memoria";
  version = "0.0.1";

  src = ./.;

  buildInputs = [ texlive.combined.scheme-full ];

  buildPhase = ''
    mkdir -p .cache/texmf-var
    TEXMFHOME=.cache TEXMFVAR=.cache/texmf-var latexmk -interaction=nonstopmode -pdf -lualatex main.tex
  '';

  installPhase = ''
    mkdir -p $out
    cp main.pdf $out/
  '';

}
