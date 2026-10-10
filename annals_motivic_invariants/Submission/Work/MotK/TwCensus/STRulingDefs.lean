import Mathlib
import Submission.Work.MotK.TwCensus.Defs
import Submission.Work.MotK.TwCensus.STClass
import Submission.Work.MotK.TGen.CensusFactors

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Node K5, made explicit: the ruling lines of the source ruling divisor `sT`

`Work.MotK.TwCensus.STRuling` asks that `(sT a b h)` be a height-one prime whose residue field is
the function field of `C' × 𝔸¹`, where `C'` is the curve cut out in the affine chart by the five
cubics `Work.MotK.TwCensus.Zcub a b h j` of the inverse map `kleinTwR`.

This file collects the **explicit ruling data** of that node (found, and verified numerically over
`𝔽₁₃` and `𝔽₁₀₁₃`, during the K5 investigation).  It is sorry-free so that the identities about
these objects can be proved in parallel by other agents.

## What the ruling is

Write `c' = (0, X₀, X₁, X₂, 1) ∈ 𝔸³ ⊂ ℙ⁴` for the general point of the target chart, so that
`Amat a b h c'` (`Submission/Work/MotK/TwCensus/STClass.lean`; `AmatP` below is the same matrix,
written over an arbitrary commutative ring as `h^{twW i (l-i)} · (0,a,b,-b,-a)_{l-2i} · c'_{l-i}`)
is the matrix of the linear system whose kernel is the fibre of the twisted quadro map
`kleinTwP a b h` over `[c']` (`Work.MotK.TGen.KleinTwFibre_eq_ker`).  The key facts are:

* the rows of `AmatP a b h c'` with indices `1,2,3` are triangular with diagonal `-b, b, a`, hence
  **independent for all `c'`**; therefore `ker (AmatP a b h c') ⊆ span{rv, rw}` for *every* `c'`,
  with `rv`, `rw` the two explicit vectors below;
* `AmatP a b h c' · rv = h·Pt1·e₀` and `AmatP a b h c' · rw = h·Pt2·e₀` (the other four components
  vanish identically: `AmatP_mulVec_rv`, `AmatP_mulVec_rw`); hence
  **`ker (AmatP a b h c') = span{rv, rw}` exactly on the locus `Pt1 = Pt2 = 0`**;
* that locus is the curve `C'`: `Ideal.span {Pt1, Pt2} = ZI a b h` (both containments are
  polynomial certificates — see `Work.MotK.TwCensus.STRulingIdentities`), and numerically
  `V(Pt1,Pt2) ∩ 𝔸³ = V(Zcub a b h)` over `𝔽₁₃`;
* the ruling line `span{rv,rw}` lies on the twisted quadric (`quad_lin_comb`: `kleinTwQ (T·rv + w)`
  vanishes identically in the ruling parameter `T`) and on the divisor `{s = 0}` (the identity
  `s (T·rv + w) ∈ (Pt1, Pt2)`, delegated);
* the resulting parametrisation of the surface `{sT = 0}` over `C' × 𝔸¹` is the map `sig` below
  (affine-linear in the ruling parameter `T`).

## The parametrisation

With `xq i` the class of `X i` in `A = K[X] ⧸ Ideal.radical (ZI a b h)` and `T = Polynomial.X`,
the chart coordinate of `π_p(T·rv + w)` is

```
sig a b h (x 0) = C (h·a/b·xq 1) · T + C (h · xq 2)
sig a b h (x 1) = C (h·a/b·xq 1·(xq 1 - 1)) · T + C (h·xq 1·xq 2 + h·b/a·xq 0 - h·xq 2)
sig a b h (x 2) = C (1 - xq 1) · T - C (b/a · xq 2)
```

(the chart of `H = {v₀ = 0}` is `(v₁/v₄, (v₂-v₀)/v₄, (v₃ - (b/(a h))·v₀)/v₄)` and
`π_p(y) = y - y₀·p`).
-/

namespace Work.MotK.TwCensus

open MvPolynomial Matrix

variable {K : Type*} [Field K]

/-! ## The two cubics cutting out the ruling base curve `C'` -/

/-- The first cubic of the ruling base curve: `AmatP a b h c' · rv = h · Pt1 · e₀`. -/
noncomputable def Pt1 (a b h : K) : MvPolynomial (Fin 3) K :=
  C (a ^ 2 * h / b) * X 0 ^ 2 - C (a ^ 3 * h / b ^ 2) * X 0 * X 1 * X 2
    + C (a * h) * X 1 ^ 3 - C b * X 2

/-- The second cubic of the ruling base curve: `AmatP a b h c' · rw = h · Pt2 · e₀`. -/
noncomputable def Pt2 (a b h : K) : MvPolynomial (Fin 3) K :=
  -C (h * a ^ 2 / b) * X 0 * X 2 ^ 2 + C (h * b) * X 1 ^ 2 * X 2
    + C (h * b ^ 2 / a) * X 0 * X 1 - C a

/-- The pair `(Pt1, Pt2)` of cubics cutting out the ruling base curve. -/
noncomputable def Pt (a b h : K) : Fin 2 → MvPolynomial (Fin 3) K := ![Pt1 a b h, Pt2 a b h]

/-! ## The two vectors spanning the ruling line -/

/-- **The first ruling vector.** -/
noncomputable def rv (a b h : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  ![C (h * a / b) * X 1,
    C (h * a / b) * X 0 - C (h * a ^ 2 / b ^ 2) * X 1 * X 2,
    C (h * a / b) * X 1 ^ 2, 1, 0]

/-- **The second ruling vector.** -/
noncomputable def rw (a b h : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  ![C h * X 2, -C (h * a / b) * X 2 ^ 2, C h * X 1 * X 2 + C (h * b / a) * X 0, 0, 1]

/-- The general point `c' = (0, X₀, X₁, X₂, 1)` of the target chart. -/
noncomputable def chartPt : Fin 5 → MvPolynomial (Fin 3) K := ![0, X 0, X 1, X 2, 1]

/-- The point `T·rv + w` of the ruling line, as a vector in `K[X₀,X₁,X₂,T]`
(`X 3` is the ruling parameter `T`). -/
noncomputable def rulingPt (a b h : K) : Fin 5 → MvPolynomial (Fin 4) K :=
  ![C (h * a / b) * X 1 + X 3 * (C h * X 2),
    (C (h * a / b) * X 0 - C (h * a ^ 2 / b ^ 2) * X 1 * X 2) + X 3 * (-C (h * a / b) * X 2 ^ 2),
    C (h * a / b) * X 1 ^ 2 + X 3 * (C h * X 1 * X 2 + C (h * b / a) * X 0),
    C 1 + X 3 * 0,
    0 + X 3 * C 1]

/-! ## The ruling matrix over a commutative ring -/

/-- The Klein coefficient vector `(0, a, b, -b, -a)`. -/
def kc {R : Type*} [CommRing R] (a b : R) : Fin 5 → R := ![0, a, b, -b, -a]

/-- **The ruling matrix `Amat` over an arbitrary commutative ring**: the entry `(i,l)` of the
linear-in-`y` system whose kernel is the fibre of the quadro map over `c'`.  This is
`Work.MotK.TwCensus.Amat` (`Submission/Work/MotK/TwCensus/STClass.lean`) with the closed form of
its entries, made available over a `CommRing` so that it can be evaluated at the *polynomial* point
`c' = (0, X₀, X₁, X₂, 1)`. -/
def AmatP {R : Type*} [CommRing R] (a b h : R) (c' : Fin 5 → R) : Matrix (Fin 5) (Fin 5) R :=
  fun i l => h ^ twW i (l - i) * kc a b (l - 2 * i) * c' (l - i)

/-! ## The identities (proved in the sibling file)

The three identities listed in the docstring above are proved in
`Submission/Work/MotK/TwCensus/STRulingIdentities.lean`:

* `Work.MotK.TwCensus.AmatP_mulVec_rv` : `AmatP a b h c' · rv = h · Pt1 · e₀`;
* `Work.MotK.TwCensus.AmatP_mulVec_rw` : `AmatP a b h c' · rw = h · Pt2 · e₀`;
* `Work.MotK.TwCensus.quad_lin_comb`   : `kleinTwQ (T·rv + w) = 0`;
* `Work.MotK.TwCensus.s_ruling_mem`    : `s (T·rv + w) ∈ Ideal.span {Pt1, Pt2}`.

`AmatP` agrees with `Work.MotK.TwCensus.Amat` over a field
(`Work.MotK.TwCensus.AmatP_eq_Amat`), and `Ideal.span {Pt1, Pt2} = ZI a b h`
(`Work.MotK.TwCensus.span_Pt_eq_ZI`), so the ruling data above are phrased in the vocabulary of the
existing fibre lemma `Work.MotK.TGen.KleinTwFibre_eq_ker`.
-/

end Work.MotK.TwCensus
