# GSK-LeanBio — reproducible toolchain.
#
# Pins the Lean toolchain from lean/lean-toolchain and builds the Mathlib-backed
# project, so every command (verify, certify, the flagship) runs in the image.
#
#   docker build -t gsk-leanbio .
#   docker run --rm gsk-leanbio check   examples/A-enzyme-kinetics/model.bsl
#   docker run --rm gsk-leanbio verify  examples/D-linear-pathway/model.bsl
#   docker run --rm gsk-leanbio certify examples/E-reversible/model.bsl
FROM python:3.11-slim

RUN apt-get update \
    && apt-get install -y --no-install-recommends curl ca-certificates git \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app
COPY lean/lean-toolchain /app/lean/lean-toolchain
# Lean 4 via elan, pinned to the project's toolchain (not "stable").
RUN curl -fsSL https://elan.lean-lang.org/elan-init.sh \
      | sh -s -- -y --default-toolchain "$(cat /app/lean/lean-toolchain)"
ENV PATH="/root/.elan/bin:${PATH}"

COPY . /app
# Mathlib from its prebuilt cache, pinned by lean/lake-manifest.json.
RUN cd lean && lake exe cache get && lake build
RUN pip install --no-cache-dir -e .

ENTRYPOINT ["bsl"]
CMD ["--help"]
