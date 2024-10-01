##################################################
# From https://github.com/srcML/Docker/blob/ubuntu_latest/base/Dockerfile
##################################################
FROM ubuntu:22.04
LABEL org.srcml.email="srcmldev@gmail.com" \
      org.srcml.url="srcml.org" \
      org.srcml.distro="ubuntu" \
      org.srcml.osversion="latest" \
      org.srcml.architecture="x86_64" \
      org.srcml.cmake="3.14.1" \
      org.srcml.boost="1.69.0"

ENV PLATFORM=ubuntu:latest

# Update and install dependencies
RUN apt-get update && apt-get install --no-install-recommends -y \
    curl \
    zip \
    g++ \
    make \
    git \
    ninja-build \
    antlr \
    libantlr-dev \
    libxml2-dev \
    libxml2-utils \
    libxslt1-dev \
    libarchive-dev \
    libssl-dev \
    libcurl4-openssl-dev \
    cpio \
    man \
    file \
    dpkg-dev \
    && rm -rf /var/lib/apt/lists/*

# Download and install a newer binary version of cmake
ARG CMAKE_BIN_URL=https://cmake.org/files/v3.14/cmake-3.14.1-Linux-x86_64.tar.gz
RUN curl -L $CMAKE_BIN_URL | tar xz --strip-components=1 -C /usr/local/

# Download and install only needed boost files
RUN curl -L http://www.sdml.cs.kent.edu/build/srcML-1.0.0-Boost.tar.gz | \
    tar xz -C /usr/local/include

# Allow man pages to be installed
RUN sed -i '/path-exclude=\/usr\/share\/man\/*/c\#path-exclude=\/usr\/share\/man\/*' /etc/dpkg/dpkg.cfg.d/excludes

##################################################
# For custom srcML
##################################################
WORKDIR /usr/src
RUN git clone https://github.com/srcML/srcML.git
WORKDIR /usr/src/srcML

# Create a build directory and navigate to it
RUN mkdir build && cd build && \
    cmake .. && \
    make -j$(nproc)

# Install srcML
RUN cd build && make install

# Update the shared library cache
RUN ldconfig

# Verify srcML installation
RUN srcml --version

# Set the default command
CMD ["srcml", "--help"]

# RUN mkdir srcML-1.0.0/build && \
#     cd srcML-1.0.0/build && \
#     cmake ../ && \
#     cmake --build . && \
#     cd bin

# WORKDIR /usr/src/erbe/srcML-1.0.0/build/bin
##################################################
