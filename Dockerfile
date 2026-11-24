FROM debian:trixie-20261123-slim

RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates curl \
    && rm -rf /var/lib/apt/lists/*

ARG ELAN_VERSION=v4.4.0
RUN curl -sSfL "https://raw.githubusercontent.com/leanprover/elan/${ELAN_VERSION}/elan-init.sh" \
    | sh -s -- -y --no-modify-path --default-toolchain none
ENV PATH=/root/.elan/bin:$PATH

WORKDIR /proof
COPY lean-toolchain ./
RUN elan toolchain install "$(cat lean-toolchain)"
COPY *.lean verify.sh ./

CMD ["sh", "verify.sh"]
