import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PCFU.chBslotAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chiLam_mul_le_of_alias`

**The lattice-aliasing decay of the box window.**  If two points `z`, `w` of the box are related
by a *nonzero* lattice translate up to an error `ρ`, then the product of the window values decays
like `(ρ/ℓ)^{2N}`, for every `N`.

The mechanism is that the corpus bump `χ` (`Submission.BoseGases.chi`, the Mathlib
`ContDiffBump (0 : ℝ³)` with `rIn = 1/4`, `rOut = 1/2`) is *flat to all orders* at the boundary
of its support (`Work.BoseFixB1.chi_boundary_taylor`), together with the elementary observation
that the lattice constraint forces *both* points into the `ρ/ℓ`-collar of that boundary: if
`χ(ℓ⁻¹z) ≠ 0` and `χ(ℓ⁻¹w) ≠ 0` then both `ℓ⁻¹z` and `ℓ⁻¹w` lie in the unit cube, and
`(ℓ⁻¹z) - (ℓ⁻¹w)` is within `ρ/ℓ` of `-d` with `d ∈ ℤ³ \ {0}`, which for the coordinate `j`
with `d j ≠ 0` (so `|d j| ≥ 1`) pins both `j`-coordinates into `[-1/2, -1/2 + ρ/ℓ]` or
`[1/2 - ρ/ℓ, 1/2]`; hence `1/2 - ‖ℓ⁻¹z‖ ≤ ρ/ℓ` and `1/2 - ‖ℓ⁻¹w‖ ≤ ρ/ℓ`.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The corpus bump vanishes outside the closed ball of radius `1/2`: the contrapositive of
`Submission.BoseGases.chi_eq_zero_of_norm_gt`. -/
private lemma norm_le_half_of_chi_ne_zero {u : E3} (hu : Submission.BoseGases.chi u ≠ 0) :
    ‖u‖ ≤ 1 / 2 :=
  le_of_not_gt fun h => hu (Submission.BoseGases.chi_eq_zero_of_norm_gt u h)

/-- Each coordinate of a point where `χ` does not vanish is bounded by `1/2` (support cube). -/
private lemma abs_coord_le_half_of_chi_ne_zero {u : E3} (hu : Submission.BoseGases.chi u ≠ 0)
    (j : Fin 3) : |u j| ≤ 1 / 2 :=
  Work.BoseK15.chi_support_subset_unitCell hu j

/-- **The lattice-aliasing geometry.**  Let `d ∈ ℤ³ \ {0}` and let `a`, `b` lie in the unit cube
with `a - b` within `ε` of `-d`.  Then both `a` and `b` are within `ε` of the boundary
`‖·‖ = 1/2` of the unit ball of the cube:

`1/2 - ‖a‖ ≤ ε` and `1/2 - ‖b‖ ≤ ε`. -/
private lemma half_sub_norm_le_of_alias {ε : ℝ} {d : Fin 3 → ℤ} (hd : d ≠ 0) {a b : E3}
    (ha : ∀ j, |a j| ≤ 1 / 2) (hb : ∀ j, |b j| ≤ 1 / 2)
    (hnorm : ‖a - b + Work.BoseBoxFock.latVec d‖ ≤ ε) :
    1 / 2 - ‖a‖ ≤ ε ∧ 1 / 2 - ‖b‖ ≤ ε := by
  -- a nonzero integer vector has a nonzero coordinate `j`
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hd
  have hj0 : d j ≠ 0 := by simpa using hj
  -- the `j`-th coordinate of the constraint
  have ht : |a j - b j + ((d j : ℤ) : ℝ)| ≤ ε := by
    have h1 : |(a - b + Work.BoseBoxFock.latVec d) j| ≤ ‖a - b + Work.BoseBoxFock.latVec d‖ := by
      simpa using PiLp.norm_apply_le (a - b + Work.BoseBoxFock.latVec d) j
    have h2 : (a - b + Work.BoseBoxFock.latVec d) j = a j - b j + ((d j : ℤ) : ℝ) := by
      simp
    rw [h2] at h1
    exact le_trans h1 hnorm
  -- coordinate bounds
  have haj := abs_le.mp (ha j)          -- `-(1/2) ≤ a j`, `a j ≤ 1/2`
  have hbj := abs_le.mp (hb j)          -- `-(1/2) ≤ b j`, `b j ≤ 1/2`
  have ht' := abs_le.mp ht              -- `-ε ≤ a j - b j + d j`, `a j - b j + d j ≤ ε`
  have hna : |a j| ≤ ‖a‖ := by simpa using PiLp.norm_apply_le a j
  have hnb : |b j| ≤ ‖b‖ := by simpa using PiLp.norm_apply_le b j
  -- `|d j| ≥ 1`
  have hdj : (1 : ℝ) ≤ ((d j : ℤ) : ℝ) ∨ ((d j : ℤ) : ℝ) ≤ -1 := by
    have h1 : (1 : ℤ) ≤ |d j| := Int.one_le_abs hj0
    have h2 : (1 : ℝ) ≤ |((d j : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast h1
    rcases le_total (0 : ℝ) ((d j : ℤ) : ℝ) with h | h
    · left; rwa [abs_of_nonneg h] at h2
    · right; rw [abs_of_nonpos h] at h2; linarith
  rcases hdj with hD | hD
  · -- `d j ≥ 1`: `a j` is near `-1/2` and `b j` near `1/2`
    constructor
    · have h1 : a j ≤ ε - 1 / 2 := by linarith [ht'.2, hbj.2, hD]
      have h2 : -(a j) ≤ |a j| := neg_le_abs _
      have h3 : (1 / 2 : ℝ) - ε ≤ ‖a‖ := by linarith [h2, hna]
      linarith
    · have h1 : (1 / 2 : ℝ) - ε ≤ b j := by linarith [ht'.1, haj.1, hD]
      have h2 : b j ≤ |b j| := le_abs_self _
      have h3 : b j ≤ ‖b‖ := le_trans h2 hnb
      linarith
  · -- `d j ≤ -1`: `a j` is near `1/2` and `b j` near `-1/2`
    constructor
    · have h1 : (1 / 2 : ℝ) - ε ≤ a j := by linarith [ht'.1, hbj.1, hD]
      have h2 : a j ≤ |a j| := le_abs_self _
      have h3 : a j ≤ ‖a‖ := le_trans h2 hna
      linarith
    · have h1 : b j ≤ -1 / 2 + ε := by linarith [ht'.2, haj.2, hD]
      have h2 : -(b j) ≤ |b j| := neg_le_abs _
      have h3 : (1 / 2 : ℝ) - ε ≤ ‖b‖ := by linarith [h1, h2, hnb]
      linarith

theorem chiLam_mul_le_of_alias (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ℓ ρ : ℝ}, 0 < ℓ → 0 ≤ ρ →
      ∀ {d : Fin 3 → ℤ}, d ≠ 0 → ∀ z w : EuclideanSpace ℝ (Fin 3),
        ‖z - w + ℓ • Work.BoseBoxFock.latVec d‖ ≤ ρ →
          Work.BoseK15.corpusBox.chiLam ℓ z * Work.BoseK15.corpusBox.chiLam ℓ w
            ≤ C * (ρ / ℓ) ^ (2 * N) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.BoseFixB1.chi_boundary_taylor N
  refine ⟨C₀ ^ 2, sq_nonneg C₀, ?_⟩
  intro ℓ ρ hℓ hρ d hd z w hzw
  have hε0 : 0 ≤ ρ / ℓ := div_nonneg hρ hℓ.le
  set a : E3 := ℓ⁻¹ • z with ha
  set b : E3 := ℓ⁻¹ • w with hb
  have hchi_z : Work.BoseK15.corpusBox.chiLam ℓ z = Submission.BoseGases.chi a := by
    rw [Work.BoseB4.BoxData.chiLam_apply, Work.BoseK15.corpusBox_chi, ha]
  have hchi_w : Work.BoseK15.corpusBox.chiLam ℓ w = Submission.BoseGases.chi b := by
    rw [Work.BoseB4.BoxData.chiLam_apply, Work.BoseK15.corpusBox_chi, hb]
  -- the constraint, rescaled by `ℓ⁻¹`
  have hscale : ‖a - b + Work.BoseBoxFock.latVec d‖ ≤ ρ / ℓ := by
    have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
    have hℓinv : 0 ≤ ℓ⁻¹ := inv_nonneg.mpr hℓ.le
    have h2 : a - b + Work.BoseBoxFock.latVec d
        = ℓ⁻¹ • (z - w + ℓ • Work.BoseBoxFock.latVec d) := by
      rw [ha, hb]
      simp only [smul_add, smul_sub, smul_smul, inv_mul_cancel₀ hℓne, one_smul]
    calc ‖a - b + Work.BoseBoxFock.latVec d‖
        = ‖(ℓ⁻¹ : ℝ) • (z - w + ℓ • Work.BoseBoxFock.latVec d)‖ := by rw [h2]
      _ = ℓ⁻¹ * ‖z - w + ℓ • Work.BoseBoxFock.latVec d‖ := by
            rw [norm_smul, Real.norm_of_nonneg hℓinv]
      _ ≤ ℓ⁻¹ * ρ := mul_le_mul_of_nonneg_left hzw hℓinv
      _ = ρ / ℓ := by rw [div_eq_inv_mul]
  -- the trivial cases: one of the two factors vanishes
  by_cases hza : Submission.BoseGases.chi a = 0
  · rw [hchi_z, hchi_w, hza, zero_mul]
    exact mul_nonneg (sq_nonneg C₀) (pow_nonneg hε0 _)
  by_cases hwb : Submission.BoseGases.chi b = 0
  · rw [hchi_z, hchi_w, hwb, mul_zero]
    exact mul_nonneg (sq_nonneg C₀) (pow_nonneg hε0 _)
  -- both factors are nonzero: the flatness and the geometry apply
  obtain ⟨hgeomA, hgeomB⟩ :=
    half_sub_norm_le_of_alias hd (fun j => abs_coord_le_half_of_chi_ne_zero hza j)
      (fun j => abs_coord_le_half_of_chi_ne_zero hwb j) hscale
  have hna : ‖a‖ ≤ 1 / 2 := norm_le_half_of_chi_ne_zero hza
  have hnb : ‖b‖ ≤ 1 / 2 := norm_le_half_of_chi_ne_zero hwb
  have hpa : Submission.BoseGases.chi a ≤ C₀ * (ρ / ℓ) ^ N := by
    have h1 := hC₀ a hna
    have h2 : ((1 : ℝ) / 2 - ‖a‖) ^ N ≤ (ρ / ℓ) ^ N :=
      pow_le_pow_left₀ (by linarith [hna]) hgeomA N
    calc Submission.BoseGases.chi a ≤ C₀ * ((1 : ℝ) / 2 - ‖a‖) ^ N := h1
      _ ≤ C₀ * (ρ / ℓ) ^ N := mul_le_mul_of_nonneg_left h2 hC₀pos.le
  have hpb : Submission.BoseGases.chi b ≤ C₀ * (ρ / ℓ) ^ N := by
    have h1 := hC₀ b hnb
    have h2 : ((1 : ℝ) / 2 - ‖b‖) ^ N ≤ (ρ / ℓ) ^ N :=
      pow_le_pow_left₀ (by linarith [hnb]) hgeomB N
    calc Submission.BoseGases.chi b ≤ C₀ * ((1 : ℝ) / 2 - ‖b‖) ^ N := h1
      _ ≤ C₀ * (ρ / ℓ) ^ N := mul_le_mul_of_nonneg_left h2 hC₀pos.le
  calc Work.BoseK15.corpusBox.chiLam ℓ z * Work.BoseK15.corpusBox.chiLam ℓ w
      = Submission.BoseGases.chi a * Submission.BoseGases.chi b := by rw [hchi_z, hchi_w]
    _ ≤ (C₀ * (ρ / ℓ) ^ N) * (C₀ * (ρ / ℓ) ^ N) :=
        mul_le_mul hpa hpb (Submission.BoseGases.chi_nonneg b) (by positivity)
    _ = C₀ ^ 2 * (ρ / ℓ) ^ (2 * N) := by
        rw [mul_mul_mul_comm, ← pow_two, ← pow_add, show N + N = 2 * N by omega]

end Work.BoseBoxFock.PCFU
