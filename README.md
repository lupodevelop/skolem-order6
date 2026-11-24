# The order-6 example of the Skolem survey has no zeros

[![Paper DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24507477.svg)](https://doi.org/10.5281/zenodo.24507477)
[![Code DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24484086.svg)](https://doi.org/10.5281/zenodo.24484086)

Section 8.3 of Bacik, Karimov, Luca, Nieuwveld, Ouaknine, Purser and Worrell, *A survey of the Skolem and Positivity Problems for linear recurrence sequences* (2026), presents the sequence

$$
u_n = 2(-4+7i)^n + 2(-4-7i)^n + 4(8+i)^n + 4(8-i)^n + n
$$

as an instance whose Skolem Problem its authors could not settle. This repository proves in Lean 4 that $u_n \ne 0$ for every natural number $n$. [Survey, §8.3](https://people.mpi-sws.org/~joel/publications/skolem_and_positivity_survey26.pdf#page=43)

## Proof

Write $\alpha=-4+7i$, $\beta=8+i$ and $V_n = u_n - n = 4\mathrm{Re}\,(\alpha^n) + 8\mathrm{Re}\,(\beta^n)$.

1. **Index class.** From $u_n \equiv n \pmod 4$ and $u_{4m} \equiv 4m+12 \pmod{16}$, a zero has $n \equiv 4 \pmod{16}$. Since $\alpha \equiv \beta \pmod 3$, $V_n \equiv 12\mathrm{Re}\,(\alpha^n) \equiv 0 \pmod 3$, so $3 \mid n$. Hence $n \equiv 12 \pmod{24}$.
2. **Divisibility by 23.** $\mathrm{Re}\,(\alpha^{12}) = 75311256833 = 23 \cdot 3274402471$ and $\mathrm{Re}\,(\beta^{12}) = 5917040513 = 23 \cdot 257262631$.
3. **Odd powers.** For $z = r+is$ and odd $k$, $\mathrm{Re}\,(z^k) = rA$ with $A \equiv k(-s^2)^{(k-1)/2} \pmod{r^2}$. So $r \mid \mathrm{Re}\,(z^k)$, and if $23^{e+1} \mid r$ then $23^{e+2} \mid \mathrm{Re}\,(z^{23})$.
4. **23-adic valuation.** For every $n \equiv 12 \pmod{24}$, induction on $e$ over the whole class gives: $23^e \mid n$ implies $23^{e+1} \mid V_n$.
5. **Conclusion.** At a zero $n = -V_n$, so $23^e \mid n$ for every $e$. This is impossible for $n > 0$, and $u_0 = 12$.

## Relation to twisted zeros

The argument is an instance of the twisted zeros of Bilu, Luca, Nieuwveld, Ouaknine and Worrell. Their Theorem 1.4 states that if $\nu_p(u_{n_k}) \to \infty$ and $\nu_p(n_k - a) \to \infty$, then $a$ is a twisted zero; their Example 1.3 shows the same phenomenon for $2^n+1$. Here $0$ is a twisted zero: with $\xi_1=\xi_2=1$ and $\xi_3,\xi_4$ the primitive cube roots of unity, $2\xi_1+2\xi_2+4\xi_3+4\xi_4 = 0$, and the term $n$ vanishes at $0$. [Bilu et al., Twisted rational zeros of linear recurrence sequences](https://arxiv.org/abs/2401.06537)

The method comes from that work. Example 2.7.5 of Nieuwveld's PhD thesis (Saarland University, 2025) applies it to a related sequence and names this one as an example the method does not reach. Neither Bilu et al. nor Bacik's later [arXiv:2609.16392](https://arxiv.org/abs/2609.16392) proves that this sequence has no zero.

## Lean development

The formal statement starts from the recurrence and the six initial terms given in the survey, not from the closed form.

| File | Content |
| --- | --- |
| [`Skolem.lean`](Skolem.lean) | Linear recurrences over $\mathbb Q$ and the predicate `HasZero`. |
| [`Frontier.lean`](Frontier.lean) | The survey's recurrence and initial terms. |
| [`FrontierTerms.lean`](FrontierTerms.lean) | Equality with the Gaussian closed form; the class $n \equiv 1012 \pmod{1024}$. |
| [`Gaussian.lean`](Gaussian.lean) | Gaussian integer powers. |
| [`NoZero.lean`](NoZero.lean) | `no_zero : ∀ n, frontier.term n ≠ 0` and a general form for $n + A\mathrm{Re}\,(x^n) + B\mathrm{Re}\,(y^n)$. |

The development uses only Lean's core library: no Mathlib and no `native_decide`. `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`.

The module [Survey13.lean](Survey13.lean) transcribes equation (13) with all four Gaussian bases, their coefficients, and the final $+n$. The kernel proves `frontier_eq_survey13` for every natural index and `survey13_ne_zero` directly for this expression. The audit covers both statements.

## Verification

With Lean installed through Elan:

```sh
sh verify.sh
```

The script compiles each module in order into an empty temporary directory. Run `sh verify.sh --kernel` to also replay the declarations of each project module with Lean’s kernel checker. The Lean version is pinned in `lean-toolchain`. Without a local Lean install:

```sh
docker build -t skolem-order6 .
docker run --rm skolem-order6
```

A prebuilt image for amd64 and arm64 is published on each release:

```sh
docker run --rm ghcr.io/lupodevelop/skolem-order6:1.1.0
```

## Manuscript

[`paper/skolem-order6-no-zeros.pdf`](paper/skolem-order6-no-zeros.pdf) is a short note with the human proof, two figures, the relation to twisted zeros and the formal statement. It is archived as a preprint at [doi:10.5281/zenodo.24507477](https://doi.org/10.5281/zenodo.24507477).

## Citation

Cite the paper:

Daniele Scaratti ([ORCID 0009-0008-3931-8821](https://orcid.org/0009-0008-3931-8821)), *The order-6 example of the Skolem survey has no zeros*, preprint, Zenodo, 2026. [doi:10.5281/zenodo.24507477](https://doi.org/10.5281/zenodo.24507477)

The Lean sources are archived separately at [doi:10.5281/zenodo.24484086](https://doi.org/10.5281/zenodo.24484086).
