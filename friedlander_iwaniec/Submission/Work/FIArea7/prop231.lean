import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7.P231M.Coprime
import Submission.Work.FIArea7.P231M.Reduced
import Submission.Work.FIArea7.P231M.ReducedToCoprime

namespace Work.FIArea7

/-- **FI Proposition 23.1, (23.8)**, with the loss the proof actually gives.

The present result proves `Work.FIArea7.Prop231` (`Submission/Work/FIArea7/Classical172Defs.lean`)
from `h : Work.FIArea7.Prop214` (Prop. 21.4 / (21.13), the bilinear form in the Jacobi–Kubota
symbol; its proof is the separate file `Submission/Work/FIArea7/prop214.lean`).

`Prop231` states: for every `ε > 0` there is `C > 0` such that for all `M N c d : ℕ` with
`1 ≤ c, 1 ≤ M, 1 ≤ N, 1 ≤ d`, all `k : ℤ`, all `χ : GaussianInt → ℂ` with `‖χ‖ ≤ 1` and
multiplicative on coprime arguments, and all `α β : ℕ → ℂ` with `‖α m‖ ≤ 1` (`m ∈ [1,M]`),
`‖β n‖ ≤ 1` (`n ∈ [1,N]`),

  `‖Σ_{m≤M} Σ_{n≤N} α m β n λ(cmn)‖ ≤ C·τ(c)·(M+N)^{1/12}·(MN)^{11/12}·(MN+c+2)^ε`,
  `‖Σ_{m≤M} Σ_{n≤N,(m,n)=1} α m β n λ(cmn)‖ ≤ C·τ(c)·(M+N)^{1/12}·(MN)^{11/12}·(MN+c+2)^ε`,

with `λ(n) = Σ^∧_{zz̄=n} ψ(z)[z]` the quadratic eigenvalue (23.1) (`quadEigen`, `LBilin`,
`LBilinStar`), `ψ = Work.FIArea7.grossenChar χ k` (17.17), `[·] = JKSym` (20.1),
`τ(c) = c.divisors.card`.

**Why the loss is a power and not a polylogarithm** (established by the previous attempt at this
path, which is why it was released as mis-stated): *FI* p. 1032 removes `(c,mn) = 1` by writing
`m = a m'`, `n = b n'` with `a, b | c^∞`, `(a,b) = 1`, and asserts
`Σ_{a,b|c^∞,(a,b)=1} τ(cab)(ab)^{-11/12} ≪ τ(c)`; that assertion is **false** — its local factor at
`p | c` is `2/(1-p^{-11/12}) + 2p^{-11/12}/((e_p+1)(1-p^{-11/12})²) - 1 ≥ (1+p^{-11/12})/(1-p^{-11/12})`,
so the quotient is `≥ Π_{p|c}(1+2p^{-11/12})`, unbounded in `ω(c)` (numerically `5.5, 16.2, 31.0,
49.6, 67.3` for `c = 2, 6, 30, 210, 2310`).  But that product is `≤ c^ε` for every `ε > 0` (indeed
`Σ_{p|c}p^{-11/12} ≪ (log c)^{1/12}`, so it is `≤ exp(C(log c)^{1/12})`), hence the power loss above
— which is exactly the paper's own `(23.8)` shape `τ(c)(M+N)^{1/12}(MN)^{11/12+ε}` (their `(MN)^ε`
absorbs the `c`-factor because in every application `c ≤ MN`).  The `(log(MN+2))^A` of `Prop214` is
`≤ (MN+c+2)^{ε/2}` for large `MN+c+2`, so a small `ε` handles both losses.

**Scaffold already in the workspace** (`Submission/Work/FIArea7/P231/`, sorry-free).  The
*reusable* part (see the reviewer's caveat): `kstar_from_prop214.lean` (each primary `e` of norm
`c` gives a `K∗(N)`-form bounded by `h : Prop214`), `multEps_expansion.lean`/`multEps_uniform.lean`
(the (20.15)+(20.19) separation of the multiplier sign), `card_strip_le.lean` (the exceptional-pair
strip count), `sqrt_error_le.lean`, `LBilinStar_eq_epsSums.lean`, `quadEigen_triple.lean` (the
factorisation `λ(cmn) = Σ_{eē=c}Σ_{ww̄=m}Σ_{zz̄=n}ψ(e)ψ(w)ψ(z)[ewz]` for pairwise coprime norms),
`SmoothSumBound.lean`, and the `(m,n) = 1` removal by the `d`-dilation.  **Not** reusable:
`P231Defs.lean`'s `ReducedBound`/`CoprimeBound` (polylog `∃ C A` Props, and `CoprimeBound` *is* the
false step) and `P231/prop231_of_coprime.lean` — do not try to instantiate those against the new
power-loss statement; redo that interface with the `(MN+c+2)^ε` loss.

PROOF ROUTE (*FI* Prop. 23.1, pp. 1031–1033): as in the scaffold, with the final comparison
replaced by

  `Σ_{a,b | c^∞, (a,b)=1} τ(cab)(a^{-1}M + b^{-1}N)^{1/12}((ab)^{-1}MN)^{11/12}`
    `≤ τ(c)·(Π_{p|c}(1+2p^{-11/12}))·(M+N)^{1/12}(MN)^{11/12}`
    `≤ τ(c)·(MN+c+2)^ε·(M+N)^{1/12}(MN)^{11/12}`,

the last step because `Π_{p|c}(1+2p^{-11/12}) ≤ (MN+c+2)^ε` (enlarge `C`). -/
theorem prop231 (h : Work.FIArea7.Prop214) : Work.FIArea7.Prop231 :=
  Work.FIArea7.P231M.prop231_of_coprimeEps (fun ε hε =>
    Work.FIArea7.P231M.coprimeBound_of_reduced (Work.FIArea7.P231M.reducedBound_of_prop214 h) ε hε)

end Work.FIArea7
