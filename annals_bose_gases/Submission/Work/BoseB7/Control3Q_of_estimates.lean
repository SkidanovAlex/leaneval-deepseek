import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7.Estimates
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.Control3Q_of_estimates` — FS §10, the assembly of `thm:Control3Q`

FS's `thm:Control3Q` (`eq:Q3Cancels`) is obtained by *adding* the three estimates
of `lem:EstimatesOnQ3-js` (`eq:EstimateQ3Tilde1`, `eq:EstimateQ3Tilde2+3`,
`eq:EstimateQ3Tilde4`) and using that the `K`'s are larger than `1`.  The
mathematical content of that addition is a piece of operator algebra.

Writing `𝒟PH` for the `P_H`-restricted Bogoliubov quadratic
`(2π)^{-3}ℓ³∫_{P_H}𝒟_kb_k†b_k` and `𝒟_all` for the unrestricted one, the three
left-hand sides of `lem:EstimatesOnQ3-js` carry

* `Q₃^(1)`, `(1-𝓁²)𝒟PH`, `Q₂^ex`, `(b/100)gapOp`,
* `Q₃^(2)+Q₃^(3)`, `𝓁²𝒟PH`,
* `Q₃^(4)`, `linOp`, `(b/100)ℓ^{-2}n₊`,

so `(1-𝓁²)𝒟PH + 𝓁²𝒟PH = 𝒟PH` and `(b/100)gapOp + (b/100)ℓ^{-2}n₊ = (b/50)gapOp`
(using `gapOp = ℓ^{-2}n₊ + ε_T(dℓ)^{-2}n₊^H`).  The *target* operator
`controlWord` uses `𝒟_all` and `(b/50)gapOp`, so the difference between the two is
exactly the sum of the two corrections

* `𝒟_all - 𝒟PH` (nonnegative form: `hkin`, the `𝒟_k ≥ 0` monotonicity in the
  momentum region),
* `(b/100)gapOp - (b/100)ℓ^{-2}n₊` (nonnegative form: `hgap`),

and it remains to add FS's remainders `err1 + err23 + err4`, dominated by
`controlErr` (`ErrDominated` — FS's "using that the `K`'s are larger than `1`
and `con:KBellKM` to simplify the total remainder").

## Contents

* `FockData.qw_add`, `qw_sub`, `qw_smul`, `normSq_nonneg` — linearity of the
  quadratic form `⟨Φ, XΦ⟩` in `X`.
* `Control3Q_of_estimates` — the assembly.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

namespace FockData

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable (F : FockData Mode)

omit [DecidableEq Mode] in
/-- The quadratic form `qw` is additive in the operator. -/
lemma qw_add (Φ : F.H) (X Y : F.H →ₗ[ℝ] F.H) :
    F.qw Φ (X + Y) = F.qw Φ X + F.qw Φ Y := by
  simp [FockData.qw, map_add]

omit [DecidableEq Mode] in
/-- The quadratic form `qw` is subtractive in the operator. -/
lemma qw_sub (Φ : F.H) (X Y : F.H →ₗ[ℝ] F.H) :
    F.qw Φ (X - Y) = F.qw Φ X - F.qw Φ Y := by
  simp [FockData.qw, map_sub]

omit [DecidableEq Mode] in
/-- The quadratic form `qw` is homogeneous in the operator. -/
lemma qw_smul (Φ : F.H) (c : ℝ) (X : F.H →ₗ[ℝ] F.H) :
    F.qw Φ (c • X) = c * F.qw Φ X := by
  simp [FockData.qw]

omit [DecidableEq Mode] in
/-- `‖Φ‖² = ⟨Φ,Φ⟩ ≥ 0`. -/
lemma normSq_nonneg (Φ : F.H) : 0 ≤ F.normSq Φ := by
  rw [FockData.normSq]
  exact F.bp_nonneg Φ

end FockData

theorem Control3Q_of_estimates {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    {C1 C23 C4 C : ℝ}
    (hsplit : F.Q3 E = F.Q3one E + F.Q3two E + F.Q3three E + F.Q3four E)
    (hkin : ∀ f : F.H, F.bp (F.dNumOpR E (F.PH E.KH E.aScat) f) f ≤
      F.bp (F.dNumOpR E (fun _ => True) f) f)
    (hgap : ∀ f : F.H, F.bp (((1 / 100 : ℝ) * (E.b * E.ell ^ (-(2 : ℝ)))) • F.nPlus f) f ≤
      F.bp (((E.b / 100) • F.gapOp E) f) f)
    (hdom : Work.BoseB7.ErrDominated E C1 C23 C4 C)
    (h1 : Work.BoseB7.EstQ3one F E C1) (h23 : Work.BoseB7.EstQ3twoThree F E C23)
    (h4 : Work.BoseB7.EstQ3four F E C4) :
    Work.BoseB7.Control3Q F E C := by
  intro Φ hΦ
  -- the three estimates at the state `Φ`, and the two monotonicity hypotheses
  have hA1 := h1 Φ hΦ
  have hA2 := h23 Φ hΦ
  have hA3 := h4 Φ hΦ
  have hkin' := hkin Φ
  have hgap' := hgap Φ
  have hdom' : err1 E C1 + err23 E C23 + err4 E C4 ≤ controlErr E C := hdom
  have hn : 0 ≤ F.normSq Φ := F.normSq_nonneg Φ
  -- (i) the sum of the three estimates, at the level of quadratic forms
  have hsum : -((err1 E C1 + err23 E C23 + err4 E C4) * F.normSq Φ) ≤
      F.qw Φ ((F.Q3one E + (1 - E.lille ^ 2) • F.dNumOpR E (F.PH E.KH E.aScat) + F.Q2ex E +
            (E.b / 100) • F.gapOp E) +
          (F.Q3two E + F.Q3three E + E.lille ^ 2 • F.dNumOpR E (F.PH E.KH E.aScat)) +
          (F.Q3four E + F.linOp E +
            ((1 / 100 : ℝ) * (E.b * E.ell ^ (-(2 : ℝ)))) • F.nPlus)) := by
    simp only [FockData.qw_add] at hA1 hA2 hA3 ⊢
    nlinarith [hA1, hA2, hA3, hn]
  -- (ii) the two corrections have nonnegative quadratic form
  have hX1 : 0 ≤ F.qw Φ
      (F.dNumOpR E (fun _ => True) - F.dNumOpR E (F.PH E.KH E.aScat)) := by
    simp only [FockData.qw, LinearMap.sub_apply, map_sub]
    linarith
  have hX2 : 0 ≤ F.qw Φ ((E.b / 100) • F.gapOp E -
      ((1 / 100 : ℝ) * (E.b * E.ell ^ (-(2 : ℝ)))) • F.nPlus) := by
    have hg := hgap Φ
    simp only [FockData.qw, LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul,
      smul_eq_mul] at hg ⊢
    linarith
  -- (iii) the operator identity: `controlWord` is FS's sum plus the two corrections
  have hkey : F.controlWord E =
      ((F.Q3one E + (1 - E.lille ^ 2) • F.dNumOpR E (F.PH E.KH E.aScat) + F.Q2ex E +
            (E.b / 100) • F.gapOp E) +
          (F.Q3two E + F.Q3three E + E.lille ^ 2 • F.dNumOpR E (F.PH E.KH E.aScat)) +
          (F.Q3four E + F.linOp E +
            ((1 / 100 : ℝ) * (E.b * E.ell ^ (-(2 : ℝ)))) • F.nPlus)) +
        ((F.dNumOpR E (fun _ => True) - F.dNumOpR E (F.PH E.KH E.aScat)) +
          ((E.b / 100) • F.gapOp E -
            ((1 / 100 : ℝ) * (E.b * E.ell ^ (-(2 : ℝ)))) • F.nPlus)) := by
    simp only [FockData.controlWord]
    rw [hsplit]
    ext f
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
    module
  -- (iv) hence the same sum is a lower bound for the target form
  have hup : F.qw Φ ((F.Q3one E + (1 - E.lille ^ 2) • F.dNumOpR E (F.PH E.KH E.aScat) +
            F.Q2ex E + (E.b / 100) • F.gapOp E) +
          (F.Q3two E + F.Q3three E + E.lille ^ 2 • F.dNumOpR E (F.PH E.KH E.aScat)) +
          (F.Q3four E + F.linOp E +
            ((1 / 100 : ℝ) * (E.b * E.ell ^ (-(2 : ℝ)))) • F.nPlus)) ≤
      F.qw Φ (F.controlWord E) := by
    rw [hkey]
    simp only [FockData.qw_add]
    linarith
  -- (v) FS's arithmetic: `err1 + err23 + err4 ≤ controlErr`
  have hdomn : (err1 E C1 + err23 E C23 + err4 E C4) * F.normSq Φ ≤
      controlErr E C * F.normSq Φ :=
    mul_le_mul_of_nonneg_right hdom' hn
  have hmain : -(controlErr E C) * F.normSq Φ ≤ F.qw Φ (F.controlWord E) := by
    nlinarith [hsum, hup, hdomn, hn]
  simpa only [neg_mul] using hmain

end Work.BoseB7
