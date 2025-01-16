# Use the official mathcomp image as a base image
FROM mathcomp/mathcomp-dev:coq-dev

# Install vscoq-language-server
RUN opam install -y vscoq-language-server
