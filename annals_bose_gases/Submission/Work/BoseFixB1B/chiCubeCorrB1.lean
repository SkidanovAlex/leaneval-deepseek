import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.chiCubeSlots
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B/chiCubeCorrB1.lean` — the `chiCubeB` autocorrelation

**Session-4 repair file** of the holder of `Work.BoseFixB1B.sectorCountSmallboxBox`.  Read
`Submission/Work/BoseFixB1B/FINDING_chiCorr_lipschitz_FALSE.md` **first**: the ball-bump twin of
every statement below (`chiCorrB1.lean` + the (A3) block of `omegaAverageA3.lean`) is *false*,
because `chiScale ℓ = chi((ℓ⁻¹)·)` uses Mathlib's ball-supported, super-decaying `ContDiffBump`
profile (whose values are in fact opaque in Lean: `someContDiffBumpBase = Nonempty.some _` does not
reduce — machine-checked).  The statements below are *geometry-only*, so they transfer verbatim to
the smooth cube bump `chiCubeB` of `chiCubeBump.lean` (decision (B) of the lead) — and there the
support is exactly the box `dlBox ℓ d u`, which is what FS's Appendix `sec:chiproperties` needs.

## Contents

* `chiCubeBase_eq_zero_of_half_le_coord` / `chiCubeScale_eq_zero_of_half_le_coord` — coordinate-wise
  vanishing of the bump (the API of `chiCubeBump.lean` is stated at coordinate `0`);
* `chiCubeB_mem_dlBox` — `chiCubeB M ℓ d u x ≠ 0 ⟹ x ∈ dlBox ℓ d u` (the
  `chiSmallB_support_mem_dlBox` twin), and `chiCubeB_support_subset_dlBox`;
* `chiCubeCorr` — the autocorrelation `z ↦ ∫ y, χ(y+z)·χ y` (the object (B2-Fub) produces);
* `chiCubeCorr_nonneg`, `chiCubeCorr_zero` (`= chiCubeMassB`), `chiCubeCorr_support` (supported in
  the box's side: `|z_j| ≤ ℓd`);
* `chiCubeScale_pos`, `chiCubeB_centre_pos` — nondegeneracy of the window at the box centre.

The *mass* identity `∫ z, chiCubeCorr z = (∫ y, χ y)²` is filed separately — it is pure
Fubini/translation-invariance and is delegated.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. Coordinate API -/

lemma ofLp_add_apply (x y : E3) (j : Fin 3) : (x + y).ofLp j = x.ofLp j + y.ofLp j := by simp

lemma ofLp_sub_apply (x y : E3) (j : Fin 3) : (x - y).ofLp j = x.ofLp j - y.ofLp j := by simp

lemma ofLp_smul_apply (c : ℝ) (x : E3) (j : Fin 3) : (c • x).ofLp j = c * x.ofLp j := by simp

lemma chiCubeBase_eq_zero_of_half_le_coord {z : E3} {j : Fin 3} (h : 1 / 2 ≤ |z.ofLp j|) :
    chiCubeBase z = 0 := by
  fin_cases j
  · exact chiCubeBase_eq_zero_of_half_le z (Or.inl h)
  · exact chiCubeBase_eq_zero_of_half_le z (Or.inr (Or.inl h))
  · exact chiCubeBase_eq_zero_of_half_le z (Or.inr (Or.inr h))

lemma chiCubeScale_eq_zero_of_half_le_coord {ℓ : ℝ} {x : E3} {j : Fin 3}
    (h : 1 / 2 ≤ |((ℓ⁻¹ : ℝ) • x).ofLp j|) : chiCubeScale ℓ x = 0 := by
  unfold chiCubeScale
  exact chiCubeBase_eq_zero_of_half_le_coord h

/-! ## 1. Support -/

/-- **The support of the smooth cube twin lies in the box `dlBox`** — the `chiCubeB` twin of
`Work.SlotWord.chiSmallB_support_mem_dlBox` (here *both* factors are cube bumps, so the support is
exactly the intersection of the two cubes: no ball cut). -/
theorem chiCubeB_mem_dlBox {M : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u x : E3}
    (hx : chiCubeB M ℓ d u x ≠ 0) : x ∈ dlBox ℓ d u := by
  have hℓd : 0 < ℓ * d := mul_pos hℓ hd
  have h1 : chiCubeScale ℓ x ≠ 0 := fun h => hx (by rw [chiCubeB, h, zero_mul])
  have h2 : chiCubeScale (ℓ * d) (x - (ℓ * d) • u) ≠ 0 :=
    fun h => hx (by rw [chiCubeB, h, mul_zero])
  rw [mem_dlBox_iff]
  refine ⟨?_, ?_⟩
  · rw [mem_acube_iff]
    intro j
    rw [Set.mem_Icc]
    have hj : |((ℓ⁻¹ : ℝ) • x).ofLp j| < 1 / 2 := by
      by_contra hc
      exact h1 (chiCubeScale_eq_zero_of_half_le_coord (le_of_not_gt hc))
    have hx' : |x.ofLp j| < ℓ / 2 := by
      rw [ofLp_smul_apply, abs_mul, abs_of_pos (inv_pos.mpr hℓ)] at hj
      have h3 := mul_lt_mul_of_pos_left hj hℓ
      have h3' : ℓ * (ℓ⁻¹ * |x.ofLp j|) = |x.ofLp j| := by field_simp
      linarith [h3, h3']
    have hb := abs_le.mp (le_of_lt hx')
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  · rw [mem_acube_iff]
    intro j
    rw [Set.mem_Icc]
    have hj : |((ℓ * d)⁻¹ : ℝ) * (x - (ℓ * d) • u).ofLp j| < 1 / 2 := by
      have hsm : (((ℓ * d)⁻¹ : ℝ) • (x - (ℓ * d) • u)).ofLp j
          = (ℓ * d)⁻¹ * (x - (ℓ * d) • u).ofLp j := ofLp_smul_apply _ _ _
      by_contra hc
      have hle : 1 / 2 ≤ |(((ℓ * d)⁻¹ : ℝ) • (x - (ℓ * d) • u)).ofLp j| := by
        rw [hsm]
        exact le_of_not_gt hc
      exact h2 (chiCubeScale_eq_zero_of_half_le_coord hle)
    have hx' : |(x - (ℓ * d) • u).ofLp j| < ℓ * d / 2 := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hℓd)] at hj
      have h3 := mul_lt_mul_of_pos_left hj hℓd
      have h3' : ℓ * d * ((ℓ * d)⁻¹ * |(x - (ℓ * d) • u).ofLp j|)
          = |(x - (ℓ * d) • u).ofLp j| := by field_simp
      linarith [h3, h3']
    have hb := abs_le.mp (le_of_lt hx')
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

lemma chiCubeB_support_subset_dlBox {M : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) :
    Function.support (chiCubeB M ℓ d u) ⊆ dlBox ℓ d u :=
  fun _ hx => chiCubeB_mem_dlBox hℓ hd hx

/-! ## 2. Positivity of the window and of its mass -/

/-- `chiCubeScale` is positive where every coordinate is strictly inside its cube. -/
lemma chiCubeScale_pos {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3} (hx : ∀ j : Fin 3, |x.ofLp j| < ℓ / 2) :
    0 < chiCubeScale ℓ x := by
  have hfac : ∀ j : Fin 3, 0 < Real.smoothTransition (2 - 4 * |((ℓ⁻¹ : ℝ) • x).ofLp j|) := by
    intro j
    refine Real.smoothTransition.pos_of_pos ?_
    rw [ofLp_smul_apply, abs_mul, abs_of_pos (inv_pos.mpr hℓ)]
    have h3 := mul_lt_mul_of_pos_left (hx j) (inv_pos.mpr hℓ)
    have h4 : (ℓ⁻¹ : ℝ) * (ℓ / 2) = 1 / 2 := by field_simp
    linarith [h3, h4]
  unfold chiCubeScale chiCubeBase
  exact mul_pos (mul_pos (hfac 0) (hfac 1)) (hfac 2)

/-- **Pointwise nondegeneracy of the cube window**: at the centre of the small box, `chiCubeB` is
positive as soon as that centre is strictly inside `acube ℓ` (the first factor) — the second factor
is *always* positive there.  The measure-theoretic version `0 < chiCubeMassB M ℓ d u` follows from
this by continuity as soon as `HasCompactSupport (chiCubeB M ℓ d u)` is available; that is filed as
a follow-up (it is not needed for the support/autocorrelation statements below). -/
theorem chiCubeB_centre_pos {M : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u : E3}
    (hu : ∀ j : Fin 3, |((ℓ * d) • u).ofLp j| < ℓ / 2) :
    0 < chiCubeB M ℓ d u ((ℓ * d) • u) := by
  rw [chiCubeB, sub_self]
  refine mul_pos (chiCubeScale_pos hℓ hu) (chiCubeScale_pos (mul_pos hℓ hd) ?_)
  intro j
  have h : (0 : E3).ofLp j = 0 := by simp
  rw [h]
  have hlt := mul_pos hℓ hd
  linarith

/-! ## 3. The autocorrelation -/

/-- The `chiCubeB` autocorrelation at the lag `z` — the object produced by the substitution
`x ↦ (y, x − y)` in the pair integral (FS (B2-Fub) of `FINDING_sectorCountSmallboxBox_session3.md`
§A10). -/
noncomputable def chiCubeCorr (M : ℕ) (ℓ d : ℝ) (u : E3) (z : E3) : ℝ :=
  ∫ y : E3, chiCubeB M ℓ d u (y + z) * chiCubeB M ℓ d u y

theorem chiCubeCorr_nonneg (M : ℕ) (ℓ d : ℝ) (u : E3) (z : E3) :
    0 ≤ chiCubeCorr M ℓ d u z :=
  integral_nonneg fun y =>
    mul_nonneg (chiCubeB_nonneg M ℓ d u (y + z)) (chiCubeB_nonneg M ℓ d u y)

/-- The diagonal value of the autocorrelation is the mass. -/
theorem chiCubeCorr_zero (M : ℕ) (ℓ d : ℝ) (u : E3) :
    chiCubeCorr M ℓ d u 0 = chiCubeMassB M ℓ d u := by
  rw [chiCubeMassB_def, chiCubeCorr]
  refine integral_congr_ae ?_
  filter_upwards with y
  rw [add_zero]
  ring

/-- **Support of the autocorrelation**: it vanishes as soon as some coordinate of the lag exceeds
the box's side `ℓ·d` (two points of the box differ by at most `ℓ·d` in each coordinate). -/
theorem chiCubeCorr_support {M : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) {z : E3}
    (hz : ∃ j : Fin 3, ℓ * d < |z.ofLp j|) : chiCubeCorr M ℓ d u z = 0 := by
  rw [chiCubeCorr]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
  by_contra hcon
  have hprod : chiCubeB M ℓ d u (y + z) * chiCubeB M ℓ d u y ≠ 0 := hcon
  have h1 := chiCubeB_mem_dlBox hℓ hd (mul_ne_zero_iff.mp hprod).1
  have h2 := chiCubeB_mem_dlBox hℓ hd (mul_ne_zero_iff.mp hprod).2
  rw [mem_dlBox_iff] at h1 h2
  obtain ⟨j, hj⟩ := hz
  have hb1 := (mem_acube_iff (ℓ * d) _).mp h1.2 j
  have hb2 := (mem_acube_iff (ℓ * d) _).mp h2.2 j
  rw [Set.mem_Icc] at hb1 hb2
  have hz_eq : z.ofLp j
      = ((y + z) - (ℓ * d) • u).ofLp j - (y - (ℓ * d) • u).ofLp j := by
    rw [ofLp_sub_apply, ofLp_sub_apply, ofLp_add_apply]
    ring
  have hle : |z.ofLp j| ≤ ℓ * d := by
    rw [hz_eq]
    rw [abs_le]
    constructor <;> linarith [hb1.1, hb1.2, hb2.1, hb2.2]
  linarith [hle, hj]


end Work.BoseFixB1B
