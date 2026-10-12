import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseRowsL.LatticeCoulomb.cosCellAverage
import Submission.Work.BoseRowsL.LatticeCoulomb.kernelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.kernelBoundsCore`

The elementary bounds on the cell-averaging data of the lattice Coulomb comparison:

* `sigma z = ∫_{ucell 0} cos (2π⟪q,z⟫) dq` (see `cosCellAverage`) equals
  `∏ᵢ sinc (π zᵢ)`, whence `sigma 0 = 1` and `|1 - sigma z| ≤ 50 ‖z‖²`;
* the sine first moment `sigBullet z = ∫_{ucell 0} sin (2π⟪q,z⟫) • q dq` satisfies
  `‖sigBullet z‖ ≤ 10 ‖z‖` (the integrand is `≤ 2π‖z‖‖q‖² ≤ 2π‖z‖·(3/4) ≤ 10‖z‖`,
  since `‖q‖ ≤ 1` on the unit cell);
* the vector `sinVec z = (sin (2π zᵢ))ᵢ` satisfies `‖sinVec z‖ ≤ 2π‖z‖ ≤ 10‖z‖`;
* hence `gam z = ⟪sigBullet z, sinVec z⟫` satisfies `|gam z| ≤ 100 ‖z‖²`, and
  `gam 0 = 0`;
* and one coordinate of `z` always carries a non-negligible amount of the quadratic
  cancellation of `1 - cos`: for the largest coordinate `j`,
  `‖z‖² ≤ 3 (z_j)² ≤ 6 (1 - cos (2π z_j))` (using `1 - cos t ≥ t²/8` for `|t| ≤ π`).

All statements are elementary; the only non-trivial input is the exact cell-average
identity `cosCellAverage` for the product form of `sigma`.
-/

noncomputable section

open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

/-! ## Elementary coordinate facts about `E3 = EuclideanSpace ℝ (Fin 3)` -/

private lemma norm_sq_eq_sum_coord (q : E3) : ‖q‖ ^ 2 = ∑ i : Fin 3, (q.ofLp i) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma coord_sq_le_norm_sq (z : E3) (i : Fin 3) : (z.ofLp i) ^ 2 ≤ ‖z‖ ^ 2 := by
  rw [norm_sq_eq_sum_coord]
  exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)

private lemma abs_coord_le_norm (z : E3) (i : Fin 3) : |z.ofLp i| ≤ ‖z‖ := by
  have h := coord_sq_le_norm_sq z i
  nlinarith [abs_nonneg (z.ofLp i), norm_nonneg z, sq_abs (z.ofLp i)]

private lemma coord_mem_ucell_zero {q : E3} (hq : q ∈ ucell (0 : Fin 3 → ℤ)) (i : Fin 3) :
    |q.ofLp i| ≤ 1 / 2 := by
  have h := hq i
  simpa using h

private lemma norm_sq_le_three_quarters {q : E3} (hq : q ∈ ucell (0 : Fin 3 → ℤ)) :
    ‖q‖ ^ 2 ≤ 3 / 4 := by
  rw [norm_sq_eq_sum_coord]
  calc ∑ i : Fin 3, (q.ofLp i) ^ 2 ≤ ∑ _i : Fin 3, ((1 : ℝ) / 2) ^ 2 :=
        Finset.sum_le_sum fun i _ => by
          have h := abs_le.mp (coord_mem_ucell_zero hq i)
          nlinarith [h.1, h.2]
    _ = 3 / 4 := by simp [Finset.sum_const, Finset.card_univ]; norm_num

private lemma norm_le_one_of_mem_ucell_zero {q : E3} (hq : q ∈ ucell (0 : Fin 3 → ℤ)) :
    ‖q‖ ≤ 1 := by
  have h := norm_sq_le_three_quarters hq
  nlinarith [norm_nonneg q]

/-! ## The cell average `sigma` -/

/-- The exact cell-average identity of `cosCellAverage` at the origin, in product form. -/
private lemma sigma_eq_prod (z : E3) : sigma z = ∏ i : Fin 3, Real.sinc (Real.pi * z.ofLp i) := by
  have h := cosCellAverage (0 : Fin 3 → ℤ) z
  have hz : inner ℝ (nvec (0 : Fin 3 → ℤ)) z = 0 := by
    rw [nvec_zero]; simp
  rw [hz, mul_zero, Real.cos_zero, mul_one] at h
  rw [sigma]
  exact h

private lemma sigma_zero : sigma 0 = 1 := by
  rw [sigma_eq_prod]
  simp

/-- Telescoping bound on a product: `|1 - ∏ aᵢ| ≤ Σ |1 - aᵢ|` when `|aᵢ| ≤ 1`. -/
private lemma abs_one_sub_prod_le {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) :
    |1 - ∏ i ∈ s, a i| ≤ ∑ i ∈ s, |1 - a i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hjs ih =>
    have ha' : ∀ i ∈ s, |a i| ≤ 1 := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hih := ih ha'
    have hprod : |∏ i ∈ s, a i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) (fun i hi => ha' i hi)
    have hkey : 1 - a j * ∏ i ∈ s, a i = (1 - a j) + a j * (1 - ∏ i ∈ s, a i) := by ring
    rw [Finset.prod_insert hjs, Finset.sum_insert hjs, hkey]
    calc |(1 - a j) + a j * (1 - ∏ i ∈ s, a i)|
        ≤ |1 - a j| + |a j * (1 - ∏ i ∈ s, a i)| := abs_add_le _ _
      _ = |1 - a j| + |a j| * |1 - ∏ i ∈ s, a i| := by rw [abs_mul]
      _ ≤ |1 - a j| + 1 * |1 - ∏ i ∈ s, a i| := by
            nlinarith [ha j (Finset.mem_insert_self j s), abs_nonneg (1 - ∏ i ∈ s, a i),
              abs_nonneg (a j)]
      _ = |1 - a j| + |1 - ∏ i ∈ s, a i| := by ring
      _ ≤ |1 - a j| + ∑ i ∈ s, |1 - a i| := by linarith

/-- The quadratic cancellation of `sinc` at `0`: `|1 - sinc x| ≤ x²/6`. -/
private lemma abs_one_sub_sinc_le (x : ℝ) : |1 - Real.sinc x| ≤ x ^ 2 / 6 := by
  rcases eq_or_ne x 0 with h | h
  · rw [h, Real.sinc_zero]; simp
  · rw [Real.sinc_of_ne_zero h]
    have h1 : 1 - Real.sin x / x = (x - Real.sin x) / x := by field_simp
    rw [h1, abs_div, div_le_iff₀ (abs_pos.mpr h)]
    calc |x - Real.sin x| ≤ |x| ^ 3 / 6 := Real.abs_sub_sin_le x
      _ = x ^ 2 / 6 * |x| := by
            have : |x| ^ 3 = x ^ 2 * |x| := by rw [← sq_abs]; ring
            rw [this]; ring

/-- `|1 - sigma z| ≤ 50 ‖z‖²` (in fact with the sharp constant `π²/6`). -/
private lemma abs_one_sub_sigma_le (z : E3) : |1 - sigma z| ≤ 50 * ‖z‖ ^ 2 := by
  rw [sigma_eq_prod]
  have h := abs_one_sub_prod_le (Finset.univ : Finset (Fin 3))
    (fun i => Real.sinc (Real.pi * z.ofLp i)) (fun i _ => Real.abs_sinc_le_one _)
  have hsum : ∑ i : Fin 3, |1 - Real.sinc (Real.pi * z.ofLp i)|
      ≤ ∑ i : Fin 3, (Real.pi * z.ofLp i) ^ 2 / 6 :=
    Finset.sum_le_sum (fun i _ => abs_one_sub_sinc_le _)
  have h2 : ∑ i : Fin 3, (Real.pi * z.ofLp i) ^ 2 / 6 = Real.pi ^ 2 / 6 * ‖z‖ ^ 2 := by
    rw [norm_sq_eq_sum_coord, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have h3 : Real.pi ^ 2 / 6 * ‖z‖ ^ 2 ≤ 50 * ‖z‖ ^ 2 := by
    have h4 : Real.pi ^ 2 / 6 ≤ 50 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
    exact mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
  linarith

/-! ## The sine first moment and the sine vector -/

/-- `‖sigBullet z‖ ≤ 2π‖z‖·(3/4) ≤ 10‖z‖`: on the unit cell the integrand is
`|sin(2π⟪q,z⟫)| ‖q‖ ≤ 2π‖z‖ ‖q‖²`, and `∫_{ucell 0}‖q‖² ≤ 3/4`. -/
private lemma sigBullet_le (z : E3) : ‖sigBullet z‖ ≤ 10 * ‖z‖ := by
  have hvol : volume (ucell (0 : Fin 3 → ℤ)) < ⊤ := by rw [volume_ucell]; norm_num
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := ucell (0 : Fin 3 → ℤ))
    (f := fun q : E3 => (Real.sin (2 * Real.pi * inner ℝ q z)) • q) (C := 10 * ‖z‖) hvol ?_
  · rw [Measure.real_def, volume_ucell, ENNReal.toReal_one, mul_one] at h
    simpa only [sigBullet] using h
  · intro q hq
    rw [norm_smul, Real.norm_eq_abs]
    have h1 := Real.abs_sin_le_abs (x := 2 * Real.pi * inner ℝ q z)
    have h3 : ‖q‖ ≤ 1 := norm_le_one_of_mem_ucell_zero hq
    have h2 : |2 * Real.pi * inner ℝ q z| ≤ 2 * Real.pi * ‖z‖ := by
      have hi := abs_real_inner_le_norm q z
      have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
      have hmul : (2 * Real.pi) * |inner ℝ q z| ≤ (2 * Real.pi) * (‖q‖ * ‖z‖) :=
        mul_le_mul_of_nonneg_left hi hpi
      have hqz : ‖q‖ * ‖z‖ ≤ ‖z‖ := by
        simpa using mul_le_mul_of_nonneg_right h3 (norm_nonneg z)
      calc |2 * Real.pi * inner ℝ q z| = (2 * Real.pi) * |inner ℝ q z| := by
            rw [abs_mul, abs_of_nonneg hpi]
        _ ≤ (2 * Real.pi) * (‖q‖ * ‖z‖) := hmul
        _ ≤ (2 * Real.pi) * ‖z‖ := mul_le_mul_of_nonneg_left hqz hpi
    have h4 : 2 * Real.pi * ‖z‖ ≤ 10 * ‖z‖ := by nlinarith [Real.pi_lt_four, norm_nonneg z]
    nlinarith [h1, h2, h3, h4, abs_nonneg (2 * Real.pi * inner ℝ q z), norm_nonneg q]

private lemma sinVec_zero : sinVec 0 = 0 := by
  ext i
  rw [sinVec_apply]
  simp

/-- `‖sinVec z‖² = Σ sin²(2π zᵢ) ≤ Σ (2π zᵢ)² = 4π²‖z‖² ≤ 100‖z‖²`. -/
private lemma sinVec_le (z : E3) : ‖sinVec z‖ ≤ 10 * ‖z‖ := by
  have hsq : ‖sinVec z‖ ^ 2 ≤ 100 * ‖z‖ ^ 2 := by
    rw [norm_sq_eq_sum_coord]
    have h : ∀ i : Fin 3, ((sinVec z).ofLp i) ^ 2 ≤ 100 * (z.ofLp i) ^ 2 := by
      intro i
      rw [sinVec_apply]
      have h1 := Real.sin_sq_le_sq (x := 2 * Real.pi * z.ofLp i)
      have hpi : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
      have h16 : (4 : ℝ) * Real.pi ^ 2 ≤ 100 := by linarith
      calc Real.sin (2 * Real.pi * z.ofLp i) ^ 2 ≤ (2 * Real.pi * z.ofLp i) ^ 2 := h1
        _ = 4 * Real.pi ^ 2 * (z.ofLp i) ^ 2 := by ring
        _ ≤ 100 * (z.ofLp i) ^ 2 := by
              have := mul_le_mul_of_nonneg_right h16 (sq_nonneg (z.ofLp i))
              linarith
    calc ∑ i : Fin 3, ((sinVec z).ofLp i) ^ 2 ≤ ∑ i : Fin 3, 100 * (z.ofLp i) ^ 2 :=
          Finset.sum_le_sum (fun i _ => h i)
      _ = 100 * ‖z‖ ^ 2 := by rw [← Finset.mul_sum, ← norm_sq_eq_sum_coord]
  nlinarith [norm_nonneg (sinVec z), norm_nonneg z, hsq]

private lemma gam_le (z : E3) : |gam z| ≤ 100 * ‖z‖ ^ 2 := by
  have h1 := sigBullet_le z
  have h2 := sinVec_le z
  have h3 : |inner ℝ (sigBullet z) (sinVec z)| ≤ ‖sigBullet z‖ * ‖sinVec z‖ :=
    abs_real_inner_le_norm _ _
  have h4 : ‖sigBullet z‖ * ‖sinVec z‖ ≤ (10 * ‖z‖) * (10 * ‖z‖) :=
    mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  calc |gam z| = |inner ℝ (sigBullet z) (sinVec z)| := rfl
    _ ≤ (10 * ‖z‖) * (10 * ‖z‖) := le_trans h3 h4
    _ = 100 * ‖z‖ ^ 2 := by ring

private lemma gam_zero : gam 0 = 0 := by
  rw [gam, sinVec_zero, inner_zero_right]

/-! ## The quadratic cancellation of `1 - cos` in some coordinate -/

private lemma exists_coord_sq_ge (z : E3) : ∃ j : Fin 3, ‖z‖ ^ 2 ≤ 3 * (z.ofLp j) ^ 2 := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3))
    (fun i => (z.ofLp i) ^ 2) Finset.univ_nonempty
  refine ⟨j, ?_⟩
  rw [norm_sq_eq_sum_coord]
  calc ∑ i : Fin 3, (z.ofLp i) ^ 2 ≤ ∑ _i : Fin 3, (z.ofLp j) ^ 2 :=
        Finset.sum_le_sum fun i _ => hj i (Finset.mem_univ i)
    _ = 3 * (z.ofLp j) ^ 2 := by simp [Finset.sum_const, Finset.card_univ]

/-- `t²/8 ≤ 1 - cos t` for `|t| ≤ π` (from `cos t ≤ 1 - 2t²/π²` and `π² ≤ 16`). -/
private lemma one_sub_cos_ge (t : ℝ) (ht : |t| ≤ Real.pi) : t ^ 2 / 8 ≤ 1 - Real.cos t := by
  have h := Real.cos_le_one_sub_mul_cos_sq ht
  have h3 : 0 < Real.pi ^ 2 := by positivity
  have h5 : (1 : ℝ) / 8 ≤ 2 / Real.pi ^ 2 := by
    rw [le_div_iff₀ h3]
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  have h7 : (1 / 8) * t ^ 2 ≤ (2 / Real.pi ^ 2) * t ^ 2 :=
    mul_le_mul_of_nonneg_right h5 (sq_nonneg t)
  have h6 : t ^ 2 / 8 ≤ 2 / Real.pi ^ 2 * t ^ 2 := by
    calc t ^ 2 / 8 = (1 / 8) * t ^ 2 := by ring
      _ ≤ 2 / Real.pi ^ 2 * t ^ 2 := h7
  linarith

private lemma exists_cos_coord (z : E3) (hz : ‖z‖ ≤ 1 / 2) :
    ∃ j : Fin 3, ‖z‖ ^ 2 ≤ 6 * (1 - Real.cos (2 * Real.pi * z.ofLp j)) := by
  obtain ⟨j, hj⟩ := exists_coord_sq_ge z
  refine ⟨j, ?_⟩
  have hzj : |z.ofLp j| ≤ 1 / 2 := le_trans (abs_coord_le_norm z j) hz
  have ht : |2 * Real.pi * z.ofLp j| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    nlinarith [hzj, Real.pi_pos]
  have h := one_sub_cos_ge (2 * Real.pi * z.ofLp j) ht
  have h6 : 6 * ((2 * Real.pi * z.ofLp j) ^ 2 / 8)
      = 3 * Real.pi ^ 2 * (z.ofLp j) ^ 2 := by ring
  have h7 : 3 * (z.ofLp j) ^ 2 ≤ 3 * Real.pi ^ 2 * (z.ofLp j) ^ 2 := by
    have hpi2 : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    nlinarith [mul_le_mul_of_nonneg_right hpi2 (sq_nonneg (z.ofLp j))]
  have h8 : 6 * ((2 * Real.pi * z.ofLp j) ^ 2 / 8)
      ≤ 6 * (1 - Real.cos (2 * Real.pi * z.ofLp j)) := by linarith [h]
  linarith [hj, h6, h7, h8]

theorem kernelBoundsCore (z : E3) (hz : ‖z‖ ≤ 1 / 2) :
    (1 - sigma 0 = 0) ∧ (gam 0 = 0) ∧ (|1 - sigma z| ≤ 50 * ‖z‖ ^ 2)
    ∧ (|gam z| ≤ 100 * ‖z‖ ^ 2) ∧ (‖sigBullet z‖ ≤ 10 * ‖z‖) ∧ (‖sinVec z‖ ≤ 10 * ‖z‖)
    ∧ (∃ j : Fin 3, ‖z‖ ^ 2 ≤ 6 * (1 - Real.cos (2 * Real.pi * z.ofLp j))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sigma_zero]; ring
  · exact gam_zero
  · exact abs_one_sub_sigma_le z
  · exact gam_le z
  · exact sigBullet_le z
  · exact sinVec_le z
  · exact exists_cos_coord z hz

end Work.BoseRowsL.LatticeCoulomb
