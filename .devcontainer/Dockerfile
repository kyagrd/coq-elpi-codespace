# Use the official mathcomp image as a base image
FROM mathcomp/mathcomp-dev:coq-dev

# Install necessary dependencies
RUN sudo apk update && sudo apk add bash m4 curl git gmp-dev linux-headers

# Install Coq-Elpi
RUN opam install -y coq-elpi
