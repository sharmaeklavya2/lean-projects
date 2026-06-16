FROM debian:bookworm-slim

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y \
    curl git build-essential \
    nodejs npm python3 \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean version manager)
# --default-toolchain none: don't download a toolchain at build time;
# the lean-toolchain file in the project will pin the exact version.
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- --default-toolchain none -y
ENV PATH="/root/.elan/bin:$PATH"

# Install Claude Code CLI
RUN npm install -g @anthropic-ai/claude-code

WORKDIR /workspace
