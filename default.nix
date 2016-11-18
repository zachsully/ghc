{ nixpkgs ? import <nixpkgs> {} }:

with nixpkgs;
stdenv.mkDerivation {
  name = "ghc-build-env-0.0.1";

  buildInputs = [
    haskellPackages.alex
    haskellPackages.happy
    haskellPackages.ghc
    bash
    automake
    autoconf
    gnumake
    ncurses
    m4
    gcc
    glibc
    git
    gmp
    perl
    python
  ];
  shellHook = "
    export PATH=$PATH:${haskellPackages.ghc}/bin
    export PATH=$PATH:${ncurses}/include:${ncurses}/lib
    export PATH=$PATH:${gmp}/include:${gmp}/lib
    export PATH=$PATH:${glibc}/include:${glibc}/lib
    export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:${ncurses}/lib
    export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:${gmp}/lib
    export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:${glibc}/lib
  ";

  # configureFlags = [
  #   "--with-cc=${stdenv.cc}/bin/cc"
  #   "--with-gmp-includes=${gmp.dev}/include" "--with-gmp-libraries=${gmp.out}/lib"
  #   "--with-curses-includes=${ncurses.dev}/include" "--with-curses-libraries=${ncurses.out}/lib"
  # ];
}
