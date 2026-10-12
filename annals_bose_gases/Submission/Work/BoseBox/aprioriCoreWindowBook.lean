import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBox.Windows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.aprioriCoreWindowBook` — the a-priori windows at FS's parameters, in `fsXp` form

This module rewrites FS `eq:apriorinn+`'s two windows — and the three auxiliary
quantities that accompany them — in the *normalised* form in which the box
theorem's bookkeeping uses them: every occurrence of the box side `ℓ = sideAt μ A`
is kept, and the remaining factors are collected into the monomials
`fsXp (μA³) c = (μA³)^{c/323}`.

Concretely, with `t = μA³ ≤ 1` and `ℓ = sideAt μ A = K_ℓ(μA)^{-1/2}`,

* `nWindow = μℓ³·K_B^{3/2}K_ℓ·t^{1/4} = μℓ³·fsXp t (−21/2)·t^{1/4}`,
* `nPlusWindow = μℓ³·K_B³K_ℓ²·t^{1/2} = μℓ³·fsXp t (−21)·t^{1/2}`,
* `K_B³ = fsXp t (−18)`,
* `(μA)ℓ² = K_ℓ² = fsXp t (−3)`,
* `ℓ > 0`, and `fsXp t c ≥ 1` for `c ≤ 0`.

The two window identities are the statements that the per-state a-priori bounds
(`aprioriWindows`) consume: they compare the window *at the parameters*
`paramsAt μ A` with the *sharp* monomial that the rest of the chapter uses, and
they show that the `(μA)`-dependence of `μℓ³` is exactly the `t^{-1/2}` that
cancels the `(μA)^{1/2}` of the healing length.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBox

set_option linter.unusedVariables false
set_option autoImplicit false

/-- `1 ≤ fsXp t c` for `c ≤ 0` and `0 < t ≤ 1`: `c ↦ fsXp t c` is antitone and
`fsXp t 0 = 1` (`fsXp_le_fsXp`). -/
lemma fsXp_one_le_of_nonpos {t c : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) (hc : c ≤ 0) :
    1 ≤ fsXp t c := by
  have h := fsXp_le_fsXp (t := t) (a := 0) (b := c) h0 h1 hc
  have h0' : fsXp t (0 : ℝ) = 1 := by norm_num [fsXp]
  rwa [h0'] at h

/-- `K_B³ = fsXp (μA³) (−18)` at FS's parameters. -/
lemma KB_cube_paramsAt_fsXp {μ A : ℝ} (hμ : 0 < μ) (hA : 0 < A) :
    (paramsAt μ A).KB ^ 3 = fsXp (μ * A ^ 3) (-18) := by
  have ht : 0 < μ * A ^ 3 := by positivity
  rw [show (paramsAt μ A).KB = fsXp (μ * A ^ 3) (-6) from rfl, fsXp_pow ht.le]
  norm_num

/-- `K_B^{3/2}K_ℓ = fsXp (μA³) (−21/2)`: the `K`-part of `nWindow`. -/
lemma KB_rpow_mul_Kl_paramsAt {μ A : ℝ} (hμ : 0 < μ) (hA : 0 < A) :
    (paramsAt μ A).KB ^ (3 / 2 : ℝ) * (paramsAt μ A).Kl = fsXp (μ * A ^ 3) (-(21 / 2)) := by
  have ht : 0 < μ * A ^ 3 := by positivity
  have h1 : (paramsAt μ A).KB ^ (3 / 2 : ℝ) = fsXp (μ * A ^ 3) (-9) := by
    rw [show (paramsAt μ A).KB = fsXp (μ * A ^ 3) (-6) from rfl, fsXp_rpow ht.le]
    norm_num
  rw [h1, show (paramsAt μ A).Kl = fsXp (μ * A ^ 3) (-(3 / 2)) from rfl, fsXp_mul ht]
  norm_num

/-- `K_B³K_ℓ² = fsXp (μA³) (−21)`: the `K`-part of `nPlusWindow`. -/
lemma KB_cube_mul_Kl_sq_paramsAt {μ A : ℝ} (hμ : 0 < μ) (hA : 0 < A) :
    (paramsAt μ A).KB ^ 3 * (paramsAt μ A).Kl ^ 2 = fsXp (μ * A ^ 3) (-21) := by
  have ht : 0 < μ * A ^ 3 := by positivity
  have h1 : (paramsAt μ A).KB ^ 3 = fsXp (μ * A ^ 3) (-18) := KB_cube_paramsAt_fsXp hμ hA
  have h2 : (paramsAt μ A).Kl ^ 2 = fsXp (μ * A ^ 3) (-3) := by
    rw [show (paramsAt μ A).Kl = fsXp (μ * A ^ 3) (-(3 / 2)) from rfl, fsXp_pow ht.le]
    norm_num
  rw [h1, h2, fsXp_mul ht]
  norm_num

/-- **FS `eq:apriorinn+`, first window, normalised.**  At FS's parameters the
particle window is `μℓ³·fsXp (μA³) (−21/2)·(μA³)^{1/4}`: the entire `(μA)`
dependence is inside `μℓ³`, and the `K_B^{3/2}K_ℓ` factor is the single monomial
`fsXp (μA³) (−21/2)`. -/
lemma nWindow_paramsAt_fsXp {μ A : ℝ} (hμ : 0 < μ) (hA : 0 < A) :
    nWindow (paramsAt μ A) μ A
      = μ * sideAt μ A ^ 3 * fsXp (μ * A ^ 3) (-(21 / 2)) * (μ * A ^ 3) ^ (1 / 4 : ℝ) := by
  have hKB := KB_rpow_mul_Kl_paramsAt hμ hA
  calc nWindow (paramsAt μ A) μ A
      = μ * boxSide (paramsAt μ A) μ A ^ 3
          * ((paramsAt μ A).KB ^ (3 / 2 : ℝ) * (paramsAt μ A).Kl)
          * (μ * A ^ 3) ^ (1 / 4 : ℝ) := by
        simp only [nWindow]; ring
    _ = μ * boxSide (paramsAt μ A) μ A ^ 3 * fsXp (μ * A ^ 3) (-(21 / 2))
          * (μ * A ^ 3) ^ (1 / 4 : ℝ) := by rw [hKB]
    _ = μ * sideAt μ A ^ 3 * fsXp (μ * A ^ 3) (-(21 / 2)) * (μ * A ^ 3) ^ (1 / 4 : ℝ) := by
        rw [show sideAt μ A = boxSide (paramsAt μ A) μ A from rfl]

/-- **FS `eq:apriorinn+`, second window, normalised.**  At FS's parameters the
excited-particle window is `μℓ³·fsXp (μA³) (−21)·(μA³)^{1/2}`. -/
lemma nPlusWindow_paramsAt_fsXp {μ A : ℝ} (hμ : 0 < μ) (hA : 0 < A) :
    nPlusWindow (paramsAt μ A) μ A
      = μ * sideAt μ A ^ 3 * fsXp (μ * A ^ 3) (-21) * (μ * A ^ 3) ^ (1 / 2 : ℝ) := by
  have hKB := KB_cube_mul_Kl_sq_paramsAt hμ hA
  calc nPlusWindow (paramsAt μ A) μ A
      = μ * boxSide (paramsAt μ A) μ A ^ 3
          * ((paramsAt μ A).KB ^ 3 * (paramsAt μ A).Kl ^ 2)
          * (μ * A ^ 3) ^ (1 / 2 : ℝ) := by
        simp only [nPlusWindow]; ring
    _ = μ * boxSide (paramsAt μ A) μ A ^ 3 * fsXp (μ * A ^ 3) (-21)
          * (μ * A ^ 3) ^ (1 / 2 : ℝ) := by rw [hKB]
    _ = μ * sideAt μ A ^ 3 * fsXp (μ * A ^ 3) (-21) * (μ * A ^ 3) ^ (1 / 2 : ℝ) := by
        rw [show sideAt μ A = boxSide (paramsAt μ A) μ A from rfl]

/-- **The healing-length identity in `fsXp` form.**  `(μA)ℓ² = K_ℓ² = fsXp (μA³) (−3)`:
the `(μA)^{-1}` of `ℓ² = K_ℓ²(μA)^{-1}` is exactly cancelled by the explicit
`μA` factor.  This is the `k`-dependence that the error term
`4πAℓ³(μA³)^{1/2}` of the a-priori bounds carries. -/
lemma mu_mul_sideAt_sq_fsXp {μ A : ℝ} (hμ : 0 < μ) (hA : 0 < A) :
    (μ * A) * sideAt μ A ^ 2 = fsXp (μ * A ^ 3) (-3) := by
  have ht : 0 < μ * A ^ 3 := by positivity
  have hμA : 0 < μ * A := mul_pos hμ hA
  have hhalf : ((μ * A) ^ (-(1 / 2 : ℝ))) ^ 2 = (μ * A)⁻¹ := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hμA.le]
    norm_num
    rw [Real.rpow_neg_one, mul_inv_rev]
  have hKl2 : (paramsAt μ A).Kl ^ 2 = fsXp (μ * A ^ 3) (-3) := by
    rw [show (paramsAt μ A).Kl = fsXp (μ * A ^ 3) (-(3 / 2)) from rfl, fsXp_pow ht.le]
    norm_num
  rw [show sideAt μ A = (paramsAt μ A).Kl * (μ * A) ^ (-(1 / 2 : ℝ)) from rfl, mul_pow,
    hhalf, hKl2]
  calc (μ * A) * (fsXp (μ * A ^ 3) (-3) * (μ * A)⁻¹)
      = fsXp (μ * A ^ 3) (-3) * ((μ * A) * (μ * A)⁻¹) := by ring
    _ = fsXp (μ * A ^ 3) (-3) := by rw [mul_inv_cancel₀ (ne_of_gt hμA), mul_one]

/-- **The a-priori window bookkeeping at FS's parameters.**  For `0 < μ`,
`0 < A` and diluteness `μA³ ≤ 1`, the windows of FS `eq:apriorinn+` at the
parameters `paramsAt μ A` are the sharp monomials times `μℓ³`, the box side is
positive, `(μA)ℓ² = fsXp (μA³) (−3)`, and the three `K`-monomials are all `≥ 1`
(as they must be: they are inverse powers of `X = (μA³)^{1/323} ≤ 1`). -/
theorem aprioriCoreWindowBook {μ A : ℝ} (hμ : 0 < μ) (hA : 0 < A) (ht1 : μ * A ^ 3 ≤ 1) :
    Work.BoseBox.nWindow (Work.BoseBox.paramsAt μ A) μ A
        = μ * Work.BoseBox.sideAt μ A ^ 3 * Work.BoseBox.fsXp (μ * A ^ 3) (-(21 / 2))
            * (μ * A ^ 3) ^ (1 / 4 : ℝ) ∧
      Work.BoseBox.nPlusWindow (Work.BoseBox.paramsAt μ A) μ A
        = μ * Work.BoseBox.sideAt μ A ^ 3 * Work.BoseBox.fsXp (μ * A ^ 3) (-21)
            * (μ * A ^ 3) ^ (1 / 2 : ℝ) ∧
      (Work.BoseBox.paramsAt μ A).KB ^ 3 = Work.BoseBox.fsXp (μ * A ^ 3) (-18) ∧
      0 < Work.BoseBox.sideAt μ A ∧
      (μ * A) * Work.BoseBox.sideAt μ A ^ 2 = Work.BoseBox.fsXp (μ * A ^ 3) (-3) ∧
      1 ≤ Work.BoseBox.fsXp (μ * A ^ 3) (-(21 / 2)) ∧
      1 ≤ Work.BoseBox.fsXp (μ * A ^ 3) (-21) ∧
      1 ≤ Work.BoseBox.fsXp (μ * A ^ 3) (-18) := by
  have ht : 0 < μ * A ^ 3 := by positivity
  refine ⟨nWindow_paramsAt_fsXp hμ hA, nPlusWindow_paramsAt_fsXp hμ hA,
    KB_cube_paramsAt_fsXp hμ hA, ?_, mu_mul_sideAt_sq_fsXp hμ hA, ?_, ?_, ?_⟩
  · exact boxSide_pos hμ hA (fsXp_pos ht)
  · exact fsXp_one_le_of_nonpos ht ht1 (by norm_num)
  · exact fsXp_one_le_of_nonpos ht ht1 (by norm_num)
  · exact fsXp_one_le_of_nonpos ht ht1 (by norm_num)

end Work.BoseBox
