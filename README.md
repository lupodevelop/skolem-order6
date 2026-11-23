# The order-6 example of the Skolem survey has no zeros

Section 8.3 of Bacik, Karimov, Luca, Nieuwveld, Ouaknine, Purser and Worrell, *A survey of the Skolem and Positivity Problems for linear recurrence sequences* (2026), presents the sequence

$$
u_n = 2(-4+7i)^n + 2(-4-7i)^n + 4(8+i)^n + 4(8-i)^n + n
$$

as an instance whose Skolem Problem is open. This repository proves in Lean 4 that $u_n \ne 0$ for every natural number $n$. [Survey, §8.3](https://people.mpi-sws.org/~joel/publications/skolem_and_positivity_survey26.pdf#page=43)

## Proof

Write $\alpha=-4+7i$, $\beta=8+i$ and $V_n = u_n - n = 4\mathrm{Re}\,(\alpha^n) + 8\mathrm{Re}\,(\beta^n)$.

1. **Index class.** From $u_n \equiv n \pmod 4$ and $u_{4m} \equiv 4m+12 \pmod{16}$, a zero has $n \equiv 4 \pmod 8$. Since $\alpha \equiv \beta \pmod 3$, $V_n = 12\mathrm{Re}\,(\alpha^n) \equiv 0 \pmod 3$, so $3 \mid n$. Hence $n \equiv 12 \pmod{24}$.
2. **Divisibility by 23.** $\mathrm{Re}\,(\alpha^{12}) = 75311256833 = 23 \cdot 3274402471$ and $\mathrm{Re}\,(\beta^{12}) = 5917040513 = 23 \cdot 257262631$.
3. **Odd powers.** For $z = r+is$ and odd $k$, $\mathrm{Re}\,(z^k) = rA$ with $A \equiv k(-s^2)^{(k-1)/2} \pmod{r^2}$. So $r \mid \mathrm{Re}\,(z^k)$, and if $23^{e+1} \mid r$ then $23^{e+2} \mid \mathrm{Re}\,(z^{23})$.
4. **23-adic valuation.** For $n \equiv 12 \pmod{24}$, induction on $e$ gives: $23^e \mid n$ implies $23^{e+1} \mid V_n$.
5. **Conclusion.** At a zero $n = -V_n$, so $23^e \mid n$ for every $e$. This is impossible for $n > 0$, and $u_0 = 12$.

## Relation to twisted zeros

The argument is an instance of the twisted zeros of Bilu, Luca, Nieuwveld, Ouaknine and Worrell. Their Theorem 1.4 states that if $\nu_p(u_{n_k}) \to \infty$ and $\nu_p(n_k - a) \to \infty$, then $a$ is a twisted zero; their Example 1.3 shows the same phenomenon for $2^n+1$. Here $0$ is a twisted zero: with $\xi_1=\xi_2=1$ and $\xi_3,\xi_4$ the primitive cube roots of unity, $2\xi_1+2\xi_2+4\xi_3+4\xi_4 = 0$, and the term $n$ vanishes at $0$. [Bilu et al., Twisted rational zeros of linear recurrence sequences](https://arxiv.org/abs/2401.06537)

The method comes from that work. Neither that paper nor Bacik's later [arXiv:2609.16392](https://arxiv.org/abs/2609.16392) treats this sequence.

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

## Verification

With Lean installed through Elan:

```sh
sh verify.sh
```

The Lean version is pinned in `lean-toolchain`.
