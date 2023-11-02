with import <nixpkgs> { };
mkShell {
  name = "coq_8_17";
  nativeBuildInputs = [ pkg-config ];
  buildInputs = [ coq_8_17 ];
}
