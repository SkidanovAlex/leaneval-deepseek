import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseB4.Kafz_sum
import Submission.Work.BoseB4.Split_ann_excited
import Submission.Work.BoseB4.Split_ann_zero
import Submission.Work.BoseB4.Split_cre_excited
import Submission.Work.BoseB4.Split_cre_zero
import Submission.Work.BoseB4.Split_inner
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.H2nd` — FS `eq:HLambdaSecond` on the mode lattice

FS's second-quantised box Hamiltonian `𝓗^{2nd}_Λ(μ)` is the operator
`eq:HLambdaSecond`:

```
𝓗^{2nd} = (2π)⁻³ℓ³∫τ(k)a_k†a_k dk
        + (b/2ℓ²)n₊ + ε_T(b/2d²ℓ²)n₊^H
        + ½ℓ⁻³(a₀†)²a₀²(ĝ(0)+ĝω(0)) − μĝ(0)a₀†a₀
        + ((ℓ⁻³a₀†a₀ − μ)Ŵ₁(0)(2π)⁻³∫χ̂_Λ(k)a_k†a₀ dk + h.c.)
        + (ℓ⁻³a₀†a₀Ŵω₁(0)(2π)⁻³∫χ̂_Λ(k)a_k†a₀ dk + h.c.)
        + (2π)⁻³∫(Ŵ₁(k)+Ŵ₁ω(k))a₀†a_k†a_k a₀ dk
        + ½(2π)⁻³∫Ŵ₁(k)(a₀†a₀†a_ka_{−k} + h.c.)dk
        + ((ℓ⁻³a₀†a₀−μ)Ŵ₁(0) + ℓ⁻³a₀†a₀Ŵ₁ω(0))(2π)⁻³ℓ⁻³∫a_k†a_k dk
        + Q̃₃,
```

with `(2π)⁻³ℓ³∫dk` the normalised sum over the mode lattice and `k = 0` the
condensate.  This module defines it (without `Q̃₃`, whose second-quantised side is
`Submission/Work/BoseB4/Q3sq.lean`) as an explicit operator on the mode lattice
`Work.BoseB4.RealFock m`, split into the named sub-operators `Hkin`, `Hgap`,
`HgapH`, `Hcontact`, `Hmu`, `HW` (`a₀†a_k†a_k a₀`), `Hbog` (`a₀†a₀†a_ka_{−k}+h.c.`),
`Hchi`, `HchiOm` and `Hnn`.

`Work.BoseB4.Kafz_H2nd` then discharges `Work.BoseB4.Kafz_lattice`'s hypothesis
`hW` for `H2nd` (each sub-operator is transported by the four `Split_*` lemmas and
reordered into the anti-normal form `monoOp` by `Wick_expansion`), giving FS
`thm:Kafz` for the box Hamiltonian on the mode lattice.

## Two conventions worth recording

* **Momentum measure.**  The mode lattice carries the normalised measure
  `(2π)⁻³ℓ³∫ dk = Σ_{k ∈ modes}` (FS `eq:HLambdaSecond`'s integral over one
  Brillouin zone).  Every row is therefore stored as a **plain finite sum over the
  mode index with no prefactor**, and the whole weight `(2π)⁻³ℓ³ · (symbol)`
  is carried by the corresponding kernel `tau`, `W1`, `W1omega` of `H2ndData`
  (e.g. `Hkin = Σ_k tau(k) a_k†a_k`).  Moments/`χ̂`-rows without a `k`-integral
  are stored with their scalar in the coefficient instead (`Hchi`, `HchiOm`).
  There is no place where a residual `(2π)⁻³` is left implicit: a consumer fixing
  the kernels to FS §4's Fourier transforms must include that weight in `tau`,
  `W1`, `W1omega` and in the `chiHat` row weights.
* **Scalars must be annotated.**  Every coefficient of a row is a *real* scalar;
  in particular `Hbog`'s `½` is written `(1 / 2 : ℝ)`.  An un-annotated `(1 / 2)`
  in that position elaborates at `ℕ`, where `1 / 2 = 0`, and the row vanishes
  identically (this happened in an earlier revision; see `README.md` §8).
-/

noncomputable section

open scoped lp BigOperators

namespace Work.BoseB4

set_option autoImplicit false

variable {m : ℕ} [NeZero m]

/-- The scalar and kernel data of one parameter point of FS `eq:HLambdaSecond`:
the box side `ℓ`, the chemical potential `μ`, the gap data `b, ε_T, d`, the
contact/scattering numbers `ĝ(0), ĝω(0), Ŵ₁(0), Ŵ₁ω(0)`, the low-momentum
localisation `χ̂_Λ`, and the mode kernels `τ, Ŵ₁, Ŵ₁ω` together with the
high-momentum set `P_H`. -/
structure H2ndData (m : ℕ) [NeZero m] where
  /-- FS's box side `ℓ` (`eq:def_ell`). -/
  ell : ℝ
  /-- FS's chemical potential `μ`. -/
  mu : ℝ
  /-- FS `eq:DefT`: the universal gap coefficient `b`. -/
  b : ℝ
  /-- FS `eq:DefT`: `ε_T`. -/
  eT : ℝ
  /-- FS's `d` (`sec:params`). -/
  d : ℝ
  /-- FS's `ĝ(0)`. -/
  g0 : ℝ
  /-- FS's `ĝω(0)`. -/
  gomega0 : ℝ
  /-- FS's `Ŵ₁(0)`. -/
  W10 : ℝ
  /-- FS's `Ŵ₁ω(0)`. -/
  W1omega0 : ℝ
  /-- FS `def:tau`, the kinetic symbol on the mode lattice. -/
  tau : Fin m → ℝ
  /-- FS's `Ŵ₁(k)`. -/
  W1 : Fin m → ℝ
  /-- FS's `Ŵ₁ω(k)`. -/
  W1omega : Fin m → ℝ
  /-- FS's `χ̂_Λ`, mode-indexed. -/
  chiHat : Fin m → ℝ
  /-- FS's high-momentum region `P_H` of the mode lattice. -/
  PHset : Finset (Fin m)

/-- The excited modes of the mode lattice. -/
noncomputable def exc (m : ℕ) [NeZero m] : Finset (Fin m) := Finset.univ.erase 0

/-- `(2π)⁻³ℓ³∫τ(k)a_k†a_k dk = Σ_{k≠0} τ(k) a_k†a_k`. -/
noncomputable def Hkin (D : H2ndData m) : RealFock m →ₗ[ℝ] RealFock m :=
  ∑ k ∈ exc m, D.tau k • (cre m k).comp (ann m k)

/-- `(b/2ℓ²)n₊`. -/
noncomputable def Hgap (D : H2ndData m) : RealFock m →ₗ[ℝ] RealFock m :=
  (D.b / (2 * D.ell ^ 2)) • (∑ k ∈ exc m, (cre m k).comp (ann m k))

/-- `ε_T(b/2d²ℓ²)n₊^H`. -/
noncomputable def HgapH (D : H2ndData m) : RealFock m →ₗ[ℝ] RealFock m :=
  (D.eT * D.b / (2 * D.d ^ 2 * D.ell ^ 2)) •
    (∑ k ∈ (exc m).filter (fun k => k ∈ D.PHset), (cre m k).comp (ann m k))

/-- `½ℓ⁻³(ĝ(0)+ĝω(0))(a₀†)²a₀²`. -/
noncomputable def Hcontact (D : H2ndData m) : RealFock m →ₗ[ℝ] RealFock m :=
  ((1 / 2) * D.ell ^ (-(3 : ℝ)) * (D.g0 + D.gomega0)) •
    ((cre m 0).comp ((cre m 0).comp ((ann m 0).comp (ann m 0))))

/-- `−μĝ(0)a₀†a₀`. -/
noncomputable def Hmu (D : H2ndData m) : RealFock m →ₗ[ℝ] RealFock m :=
  (-(D.mu * D.g0)) • ((cre m 0).comp (ann m 0))

/-- `(2π)⁻³∫(Ŵ₁(k)+Ŵ₁ω(k))a₀†a_k†a_k a₀ dk`. -/
noncomputable def HW (D : H2ndData m) : RealFock m →ₗ[ℝ] RealFock m :=
  ∑ k ∈ exc m, (D.W1 k + D.W1omega k) •
    ((cre m 0).comp ((cre m k).comp ((ann m k).comp (ann m 0))))

/-- `½(2π)⁻³∫Ŵ₁(k)(a₀†a₀†a_ka_{−k} + h.c.)dk`, the Bogoliubov pair row.  The
coefficient is the **real** scalar `(1 / 2 : ℝ)`; see the file header for why the
annotation is not optional. -/
noncomputable def Hbog (D : H2ndData m) : RealFock m →ₗ[ℝ] RealFock m :=
  (1 / 2 : ℝ) • ∑ k ∈ exc m, D.W1 k •
    (((cre m 0).comp ((cre m 0).comp ((ann m k).comp (ann m (-k))))) +
      ((cre m k).comp ((cre m (-k)).comp ((ann m 0).comp (ann m 0)))))

/-- The `(ℓ⁻³a₀†a₀ − μ)Ŵ₁(0)χ̂_Λ` linear terms and their `h.c.`. -/
noncomputable def Hchi (D : H2ndData m) : RealFock m →ₗ[ℝ] RealFock m :=
  ((D.ell ^ (-(3 : ℝ))) • ((cre m 0).comp (ann m 0)) - D.mu • (1 : RealFock m →ₗ[ℝ] RealFock m)).comp
      (D.W10 • ∑ k ∈ exc m, D.chiHat k • ((cre m k).comp (ann m 0)))
    + ((D.ell ^ (-(3 : ℝ))) • ((cre m 0).comp (ann m 0)) - D.mu • (1 : RealFock m →ₗ[ℝ] RealFock m)).comp
      (D.W10 • ∑ k ∈ exc m, D.chiHat k • ((cre m 0).comp (ann m k)))

/-- The `ℓ⁻³a₀†a₀Ŵ₁ω(0)χ̂_Λ` linear terms and their `h.c.`. -/
noncomputable def HchiOm (D : H2ndData m) : RealFock m →ₗ[ℝ] RealFock m :=
  ((D.ell ^ (-(3 : ℝ))) • ((cre m 0).comp (ann m 0))).comp
      (D.W1omega0 • ∑ k ∈ exc m, D.chiHat k • ((cre m k).comp (ann m 0)))
    + ((D.ell ^ (-(3 : ℝ))) • ((cre m 0).comp (ann m 0))).comp
      (D.W1omega0 • ∑ k ∈ exc m, D.chiHat k • ((cre m 0).comp (ann m k)))

/-- The `((ℓ⁻³a₀†a₀−μ)Ŵ₁(0) + ℓ⁻³a₀†a₀Ŵ₁ω(0))ℓ⁻³∫a_k†a_k dk` term. -/
noncomputable def Hnn (D : H2ndData m) : RealFock m →ₗ[ℝ] RealFock m :=
  ((D.ell ^ (-(3 : ℝ))) • ((cre m 0).comp (ann m 0)) - D.mu • (1 : RealFock m →ₗ[ℝ] RealFock m)).comp
      ((D.W10) • ((D.ell ^ (-(3 : ℝ))) • ∑ k ∈ exc m, (cre m k).comp (ann m k)))
    + ((D.ell ^ (-(3 : ℝ))) • ((cre m 0).comp (ann m 0))).comp
      ((D.W1omega0) • ((D.ell ^ (-(3 : ℝ))) • ∑ k ∈ exc m, (cre m k).comp (ann m k)))

/-- **FS `eq:HLambdaSecond` without `Q̃₃`, as an operator on the mode lattice.** -/
noncomputable def H2nd (D : H2ndData m) : RealFock m →ₗ[ℝ] RealFock m :=
  Hkin D + Hgap D + HgapH D + Hcontact D + Hmu D + HW D + Hbog D + Hchi D + HchiOm D + Hnn D

end Work.BoseB4
