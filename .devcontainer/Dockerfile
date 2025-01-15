# Use the official OCaml image as a base image
FROM ocaml/opam:alpine

# Install necessary dependencies
RUN sudo apk update && sudo apk add bash m4 curl git

# Initialize opam
RUN opam init -y --disable-sandboxing && \
    eval $(opam env) && \
    opam update

# Add the Coq opam repository
RUN opam repo add coq-released https://coq.inria.fr/opam/released && \
    opam update

# Install Coq and Coq-Elpi
RUN opam install -y coq coq-elpi
