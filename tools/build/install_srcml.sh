#!/bin/bash

# Script to install srcML on Ubuntu

# Exit if any command fails
set -e

# Variables (adjust these paths if necessary)
SRCML_BIN_PATH="./srcml"              # Path to the srcML binary
LIBSRCML_PATH="./libsrcml.so.1"        # Path to the srcML library

# Ensure the script is run as root
if [ "$EUID" -ne 0 ]; then
  echo "Please run as root using sudo."
  exit 1
fi

# Check if required files exist
if [ ! -f "$SRCML_BIN_PATH" ]; then
    echo "srcML binary not found at $SRCML_BIN_PATH"
    exit 1
fi

if [ ! -f "$LIBSRCML_PATH" ]; then
    echo "srcML library not found at $LIBSRCML_PATH"
    exit 1
fi

echo "Installing srcML..."

# Copy srcML binary to /usr/local/bin/
cp "$SRCML_BIN_PATH" /usr/local/bin/

# Set executable permissions for the binary
chmod +x /usr/local/bin/srcml

# Copy the srcML library to /usr/local/lib/
cp "$LIBSRCML_PATH" /usr/local/lib/

# Update library cache
ldconfig

# Verify installation
if command -v srcml &> /dev/null; then
    echo "srcML installed successfully!"
else
    echo "srcML installation failed."
    exit 1
fi

# Optional: Display srcML version
echo "srcML version:"
srcml --version
