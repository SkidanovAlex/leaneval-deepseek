import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.LWP.VorticityAPI
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.PhiStar.Gegenbauer.gC_span_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.Gegenbauer

set_option autoImplicit false

/-! ## The low-index monomials and the two explicit low-degree values -/

lemma X_zero : X 0 = fun _ : ℝ => (1 : ℝ) := by
  funext x
  show x ^ (2 * 0) = 1
  rw [show 2 * 0 = 0 by norm_num, pow_zero]

lemma X_one : X 1 = fun x : ℝ => x ^ 2 := by
  funext x
  show x ^ (2 * 1) = x ^ 2
  rw [show 2 * 1 = 2 by norm_num]

lemma Y_zero : Y 0 = fun x : ℝ => x := by
  funext x
  show x ^ (2 * 0 + 1) = x
  rw [show 2 * 0 + 1 = 1 by norm_num, pow_one]

lemma Y_one : Y 1 = fun x : ℝ => x ^ 3 := by
  funext x
  show x ^ (2 * 1 + 1) = x ^ 3
  rw [show 2 * 1 + 1 = 3 by norm_num]

lemma gC_two (x : ℝ) : gC 2 x = (15 * x ^ 2 - 3) / 2 := by
  simp only [gC]; norm_num; ring

lemma gC_three (x : ℝ) : gC 3 x = (35 * x ^ 3 - 15 * x) / 2 := by
  simp only [gC]; norm_num; ring

lemma a_one : a 1 = 15 / 2 := by
  rw [show a 1 = cfA 0 * c 0 from a_succ 0, c_zero, cfA]
  norm_num

lemma c_one : c 1 = 35 / 2 := by
  rw [show c 1 = cfC 0 * (cfA 0 * c 0) from c_succ 0, c_zero, cfC, cfA]
  norm_num

/-! ## The structural (triangularity) induction -/

/-- The tails of the odd/even indexed Gegenbauer polynomials drop one degree: the difference of
`gC (2k+2) = A (k+1)` from its leading term `a (k+1) • x^{2k+2}` is an even polynomial of degree
`≤ 2k`, and likewise for `gC (2k+3) = B (k+1)` with `c (k+1) • x^{2k+3}`. -/
lemma gC_tail_struct (k : ℕ) :
    A (k + 1) - a (k + 1) • X (k + 1) ∈ evenSpan k ∧
      B (k + 1) - c (k + 1) • Y (k + 1) ∈ oddSpan k := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · have h : A 1 - a 1 • X 1 = (-(3 / 2) : ℝ) • X 0 := by
        funext x
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [show A 1 x = (15 * x ^ 2 - 3) / 2 from gC_two x, a_one, X_one, X_zero]
        norm_num
        ring
      rw [h]
      exact Submodule.smul_mem _ _ (X_mem 0)
    · have h : B 1 - c 1 • Y 1 = (-(15 / 2) : ℝ) • Y 0 := by
        funext x
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [show B 1 x = (35 * x ^ 3 - 15 * x) / 2 from gC_three x, c_one, Y_one, Y_zero]
        norm_num
        ring
      rw [h]
      exact Submodule.smul_mem _ _ (Y_mem 0)
  | succ k ih =>
    obtain ⟨hU, hT⟩ := ih
    -- `A (k+1) ∈ evenSpan (k+1)` and `B (k+1) ∈ oddSpan (k+1)`, from the tails at level `k`
    have hA : A (k + 1) ∈ evenSpan (k + 1) := by
      have h1 : A (k + 1) - a (k + 1) • X (k + 1) ∈ evenSpan (k + 1) :=
        evenSpan_mono (Nat.le_succ k) hU
      have h2 : a (k + 1) • X (k + 1) ∈ evenSpan (k + 1) :=
        Submodule.smul_mem _ _ (X_mem (k + 1))
      have h3 := Submodule.add_mem _ h1 h2
      rwa [sub_add_cancel] at h3
    have hB : B (k + 1) ∈ oddSpan (k + 1) := by
      have h1 : B (k + 1) - c (k + 1) • Y (k + 1) ∈ oddSpan (k + 1) :=
        oddSpan_mono (Nat.le_succ k) hT
      have h2 : c (k + 1) • Y (k + 1) ∈ oddSpan (k + 1) :=
        Submodule.smul_mem _ _ (Y_mem (k + 1))
      have h3 := Submodule.add_mem _ h1 h2
      rwa [sub_add_cancel] at h3
    -- the new even tail, from `A_tail`
    have hU2 : A (k + 2) - a (k + 2) • X (k + 2) ∈ evenSpan (k + 1) := by
      rw [A_tail (k + 1)]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (mulX_mem_of_mem_oddSpan hT))
        (Submodule.smul_mem _ _ hA)
    refine ⟨hU2, ?_⟩
    -- the new odd tail, from `B_tail`
    rw [B_tail (k + 1)]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (mulX_mem_of_mem_evenSpan hU2))
      (Submodule.smul_mem _ _ hB)

/-! ## The reverse inclusion -/

/-- Every odd monomial `x^{2j+1}`, `j ≤ k`, is a linear combination of `gC 1, gC 3, …,
gC (2k+1)`. -/
lemma oddSpan_le_span_B (k : ℕ) : oddSpan k ≤ Submodule.span ℝ (B '' Set.Iic k) := by
  induction k with
  | zero =>
    rw [oddSpan, Submodule.span_le]
    rintro f ⟨j, hj, rfl⟩
    have hj0 : j = 0 := Nat.le_zero.mp (Set.mem_Iic.mp hj)
    subst hj0
    have h : Y 0 = (1 / 3 : ℝ) • B 0 := by
      funext x
      show x ^ (2 * 0 + 1) = (1 / 3 : ℝ) * (3 * x)
      norm_num
      ring
    rw [h]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨0, Set.mem_Iic.mpr le_rfl, rfl⟩)
  | succ k ih =>
    have hT : B (k + 1) - c (k + 1) • Y (k + 1) ∈ oddSpan k := (gC_tail_struct k).2
    have hmono : Submodule.span ℝ (B '' Set.Iic k) ≤ Submodule.span ℝ (B '' Set.Iic (k + 1)) :=
      Submodule.span_mono (Set.image_mono (fun j hj => le_trans hj (Nat.le_succ k)))
    have hV : B (k + 1) - c (k + 1) • Y (k + 1)
        ∈ Submodule.span ℝ (B '' Set.Iic (k + 1)) := hmono (ih hT)
    have hB1 : B (k + 1) ∈ Submodule.span ℝ (B '' Set.Iic (k + 1)) :=
      Submodule.subset_span ⟨k + 1, Set.mem_Iic.mpr le_rfl, rfl⟩
    have hY : Y (k + 1) ∈ Submodule.span ℝ (B '' Set.Iic (k + 1)) := by
      have htail : B (k + 1) - (B (k + 1) - c (k + 1) • Y (k + 1))
          = c (k + 1) • Y (k + 1) := by abel
      have hcz : (c (k + 1))⁻¹
          • (B (k + 1) - (B (k + 1) - c (k + 1) • Y (k + 1))) = Y (k + 1) := by
        rw [htail, smul_smul, inv_mul_cancel₀ (c_ne_zero (k + 1)), one_smul]
      rw [← hcz]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hB1 hV)
    rw [oddSpan_succ]
    refine sup_le ?_ ?_
    · rwa [Submodule.span_singleton_le_iff_mem]
    · exact le_trans ih hmono


/-! ## The target -/


end Work.FTS.PhiStar.Gegenbauer
end
end
-- ===== merged: Submission.Work.H2W.PsiSlices.HkMem_dilate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2W.PsiSlices

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Real Topology

/-! ## Elementary facts about the radial weight `w` -/

/-- The radial weight is positive where `z > 0`. -/
theorem w_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  simp only [Work.Spaces.w]
  exact div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)

/-- The radial weight does not vanish where `z > 0`. -/
theorem w_ne_zero {z : ℝ} (hz : 0 < z) : Work.Spaces.w z ≠ 0 := (w_pos hz).ne'

/-- The radial weight is (everywhere) measurable: division is measurable without any side
condition. -/
theorem w_measurable : Measurable Work.Spaces.w := by
  change Measurable (fun z : ℝ => (1 + z) ^ 2 / z ^ 2)
  exact ((measurable_const.add measurable_id).pow_const 2).div (measurable_id.pow_const 2)


/-! ## The `H^k` integrand at `z = 0` -/

theorem HkIntegrand_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.w]

/-! ## The integrand with the radial weight removed

The Euler derivatives commute with a dilation while the weight does not; isolating the weight
makes the dilation invariance of the derivative part a purely combinatorial statement. -/





/-! ## The multiplier `(w z / w (lam z))²` is bounded on `[0,∞)` -/



/-! ## The main lemma -/


end Work.H2W.PsiSlices
end
-- ===== merged: Submission.Work.LWP.BiotSavart.farField_decay_fderiv =====
section

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

open FiniteTimeSingularity MeasureTheory Set Filter Topology
open scoped Matrix Topology

set_option autoImplicit false

namespace Work.LWP.BiotSavart

/-! ## Elementary estimates for the kernel `a ↦ a/‖a‖³` -/

/-- Elementary estimate for the difference of cubes: on `[m, 7m]` with `m > 0` the map
`t ↦ t³` is `3(7m)²`-Lipschitz. -/
theorem abs_pow_three_sub_le {s t m : ℝ} (hm : 0 < m) (hs : m ≤ s) (ht : m ≤ t)
    (hsC : s ≤ 7 * m) (htC : t ≤ 7 * m) :
    |t ^ 3 - s ^ 3| ≤ 3 * (7 * m) ^ 2 * |t - s| := by
  have hs0 : 0 ≤ s := le_trans (le_of_lt hm) hs
  have ht0 : 0 ≤ t := le_trans (le_of_lt hm) ht
  have h1 : t ^ 3 - s ^ 3 = (t - s) * (t ^ 2 + t * s + s ^ 2) := by ring
  have h2 : 0 ≤ t ^ 2 + t * s + s ^ 2 := by positivity
  have h3 : t ^ 2 + t * s + s ^ 2 ≤ 3 * (7 * m) ^ 2 := by nlinarith
  rw [h1, abs_mul, abs_of_nonneg h2]
  calc |t - s| * (t ^ 2 + t * s + s ^ 2)
      ≤ |t - s| * (3 * (7 * m) ^ 2) := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    _ = 3 * (7 * m) ^ 2 * |t - s| := by ring

/-- The map `t ↦ t⁻³` is Lipschitz on `[m, 7m]` with constant `147/m⁴`. -/
theorem abs_inv_cube_sub_le {s t m : ℝ} (hm : 0 < m) (hs : m ≤ s) (ht : m ≤ t)
    (hsC : s ≤ 7 * m) (htC : t ≤ 7 * m) :
    |(s ^ 3)⁻¹ - (t ^ 3)⁻¹| ≤ 147 / m ^ 4 * |s - t| := by
  have hs0 : 0 < s := lt_of_lt_of_le hm hs
  have ht0 : 0 < t := lt_of_lt_of_le hm ht
  have h1 : (s ^ 3)⁻¹ - (t ^ 3)⁻¹ = (t ^ 3 - s ^ 3) * ((s ^ 3)⁻¹ * (t ^ 3)⁻¹) := by
    have hm0 : m ≠ 0 := ne_of_gt hm
    rw [← mul_inv]
    field_simp
  have hsi : |(s ^ 3)⁻¹| ≤ (m ^ 3)⁻¹ := by
    rw [abs_of_nonneg (by positivity)]
    refine (inv_le_inv₀ (by positivity) (by positivity)).mpr ?_
    exact pow_le_pow_left₀ (le_of_lt hm) hs 3
  have hti : |(t ^ 3)⁻¹| ≤ (m ^ 3)⁻¹ := by
    rw [abs_of_nonneg (by positivity)]
    refine (inv_le_inv₀ (by positivity) (by positivity)).mpr ?_
    exact pow_le_pow_left₀ (le_of_lt hm) ht 3
  have hcube := abs_pow_three_sub_le hm hs ht hsC htC
  have hm3 : 0 ≤ (m ^ 3)⁻¹ := by positivity
  rw [h1, abs_mul, abs_mul]
  calc |t ^ 3 - s ^ 3| * (|(s ^ 3)⁻¹| * |(t ^ 3)⁻¹|)
      ≤ (3 * (7 * m) ^ 2 * |t - s|) * ((m ^ 3)⁻¹ * (m ^ 3)⁻¹) := by
        refine mul_le_mul hcube (mul_le_mul hsi hti (abs_nonneg _) hm3) (by positivity) ?_
        positivity
    _ = 3 * (7 * m) ^ 2 * ((m ^ 3)⁻¹ * (m ^ 3)⁻¹) * |t - s| := by ring
    _ = 147 / m ^ 4 * |s - t| := by
        rw [abs_sub_comm]
        have hcoef : 3 * (7 * m) ^ 2 * ((m ^ 3)⁻¹ * (m ^ 3)⁻¹) = 147 / m ^ 4 := by
          have hm0 : m ≠ 0 := ne_of_gt hm
          field_simp
          ring
        rw [hcoef]

/-- The elementary Lipschitz estimate for the Biot–Savart kernel `a ↦ a/‖a‖³` on the annulus
`m ≤ ‖·‖ ≤ 7m`: `‖a/‖a‖³ - b/‖b‖³‖ ≤ 1030 ‖a - b‖/m³`. -/
theorem norm_smul_inv_norm_cube_sub_le {a b : R3} {m : ℝ} (hm : 0 < m)
    (ha : m ≤ ‖a‖) (hb : m ≤ ‖b‖) (haC : ‖a‖ ≤ 7 * m) (hbC : ‖b‖ ≤ 7 * m) :
    ‖(‖a‖ ^ 3)⁻¹ • a - (‖b‖ ^ 3)⁻¹ • b‖ ≤ 1030 / m ^ 3 * ‖a - b‖ := by
  have hm3 : 0 < m ^ 3 := by positivity
  have hdecomp : (‖a‖ ^ 3)⁻¹ • a - (‖b‖ ^ 3)⁻¹ • b
      = (‖a‖ ^ 3)⁻¹ • (a - b) + ((‖a‖ ^ 3)⁻¹ - (‖b‖ ^ 3)⁻¹) • b := by
    rw [smul_sub, sub_smul]
    abel
  have hscal := abs_inv_cube_sub_le hm ha hb haC hbC
  have hnorm : |‖a‖ - ‖b‖| ≤ ‖a - b‖ := abs_norm_sub_norm_le a b
  have ha_inv : (‖a‖ ^ 3)⁻¹ ≤ (m ^ 3)⁻¹ := by
    refine (inv_le_inv₀ (pow_pos (lt_of_lt_of_le hm ha) 3)
      (pow_pos hm 3)).mpr ?_
    exact pow_le_pow_left₀ (le_of_lt hm) ha 3
  have hb_le : ‖b‖ ≤ 7 * m := hbC
  have hb_nonneg : 0 ≤ ‖b‖ := norm_nonneg b
  rw [hdecomp]
  calc ‖(‖a‖ ^ 3)⁻¹ • (a - b) + ((‖a‖ ^ 3)⁻¹ - (‖b‖ ^ 3)⁻¹) • b‖
      ≤ ‖(‖a‖ ^ 3)⁻¹ • (a - b)‖ + ‖((‖a‖ ^ 3)⁻¹ - (‖b‖ ^ 3)⁻¹) • b‖ := norm_add_le _ _
    _ = (‖a‖ ^ 3)⁻¹ * ‖a - b‖ + |(‖a‖ ^ 3)⁻¹ - (‖b‖ ^ 3)⁻¹| * ‖b‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]
    _ ≤ (m ^ 3)⁻¹ * ‖a - b‖ + (147 / m ^ 4 * ‖a - b‖) * (7 * m) := by
        have h1 : (‖a‖ ^ 3)⁻¹ * ‖a - b‖ ≤ (m ^ 3)⁻¹ * ‖a - b‖ :=
          mul_le_mul_of_nonneg_right ha_inv (norm_nonneg _)
        have h2 : |(‖a‖ ^ 3)⁻¹ - (‖b‖ ^ 3)⁻¹| * ‖b‖ ≤ (147 / m ^ 4 * ‖a - b‖) * (7 * m) := by
          have h3 : |(‖a‖ ^ 3)⁻¹ - (‖b‖ ^ 3)⁻¹| ≤ 147 / m ^ 4 * ‖a - b‖ := by
            refine hscal.trans ?_
            exact mul_le_mul_of_nonneg_left hnorm (by positivity)
          exact mul_le_mul h3 hb_le hb_nonneg (by positivity)
        linarith
    _ ≤ 1030 / m ^ 3 * ‖a - b‖ := by
        have hc : 147 / m ^ 4 * (7 * m) = 1029 / m ^ 3 := by
          have hm0 : m ≠ 0 := ne_of_gt hm
          field_simp
          ring
        have hcomb : (m ^ 3)⁻¹ * ‖a - b‖ + (147 / m ^ 4 * ‖a - b‖) * (7 * m)
            = (1030 / m ^ 3) * ‖a - b‖ := by
          have hc' : (147 / m ^ 4 * ‖a - b‖) * (7 * m) = (1029 / m ^ 3) * ‖a - b‖ := by
            rw [mul_assoc, mul_comm ‖a - b‖ (7 * m), ← mul_assoc, hc]
          rw [show (m ^ 3)⁻¹ = 1 / m ^ 3 by ring, hc']
          ring
        rw [hcomb]

/-! ## The Biot–Savart integrand -/

/-- The integrand of the Newtonian-potential Biot–Savart operator,
`bsK ω x y = (‖x - y‖³)⁻¹ • (ω y × (x - y))`, so that `biotSavart ω x = (4π)⁻¹ • ∫ y, bsK ω x y`. -/
noncomputable def bsK (ω : R3 → R3) (x : R3) : R3 → R3 :=
  fun y => WithLp.toLp 2 ((‖x - y‖ ^ (3 : ℕ))⁻¹ • crossProduct (ω y) (x - y))

theorem biotSavart_apply (ω : R3 → R3) (x : R3) :
    biotSavart ω x = (4 * Real.pi)⁻¹ • ∫ y, bsK ω x y := rfl

theorem bsK_eq_zero {ω : R3 → R3} {x y : R3} (h : ω y = 0) : bsK ω x y = 0 := by
  simp [bsK, h]

/-- The pointwise size of the integrand: `‖((‖x-y‖³)⁻¹ • (ω y × (x-y)))‖ ≤ ‖ω y‖/‖x-y‖²`. -/
theorem norm_bsK_le (ω : R3 → R3) (x y : R3) :
    ‖bsK ω x y‖ ≤ (‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖ω y‖ * ‖x - y‖ := by
  rw [bsK, WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
  have h := norm_toLp_crossProduct_le (ω y) (x - y)
  calc (‖x - y‖ ^ 3)⁻¹ * ‖WithLp.toLp 2 (crossProduct (ω y) (x - y))‖
      ≤ (‖x - y‖ ^ 3)⁻¹ * (‖ω y‖ * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (by positivity))
    _ = (‖x - y‖ ^ 3)⁻¹ * ‖ω y‖ * ‖x - y‖ := by ring

/-! ## Measurability and integrability of the integrand -/

theorem aestronglyMeasurable_bsK {ω : R3 → R3} (hω : AEStronglyMeasurable ω volume) (x : R3) :
    AEStronglyMeasurable (bsK ω x) volume := by
  have h1 : AEStronglyMeasurable (fun y : R3 => crossProduct (ω y) (x - y)) volume := by
    have hp : AEStronglyMeasurable (fun y : R3 => ((ω y, x - y) : R3 × R3)) volume :=
      hω.prodMk ((continuous_const.sub continuous_id).aestronglyMeasurable)
    exact (by fun_prop : Continuous fun p : R3 × R3 => crossProduct p.1 p.2).comp_aestronglyMeasurable hp
  have h2 : AEStronglyMeasurable (fun y : R3 => (‖x - y‖ ^ (3 : ℕ))⁻¹) volume :=
    (Measurable.inv (by fun_prop : Measurable fun y : R3 => ‖x - y‖ ^ (3 : ℕ))).aestronglyMeasurable
  have h3 : AEStronglyMeasurable
      (fun y : R3 => (‖x - y‖ ^ (3 : ℕ))⁻¹ • crossProduct (ω y) (x - y)) volume := h2.smul h1
  exact (by fun_prop : Continuous fun (v : Fin 3 → ℝ) => WithLp.toLp 2 v).comp_aestronglyMeasurable h3

/-- `bsK ω x` is integrable whenever the support of `ω` lies in the closed ball of radius `R`
and `R < ‖x‖`: it is bounded by `M/(‖x‖-R)²` on a set of finite measure and vanishes outside. -/
theorem integrable_bsK {ω : R3 → R3} {R M : ℝ} (hM : 0 ≤ M) (hω : ∀ y, ‖ω y‖ ≤ M)
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : AEStronglyMeasurable ω volume) {x : R3} (hx : R < ‖x‖) :
    Integrable (bsK ω x) volume := by
  have hfin : volume (Metric.closedBall (0 : R3) R) ≠ ⊤ :=
    (isCompact_closedBall 0 R).measure_lt_top.ne
  have hc : 0 < ‖x‖ - R := sub_pos.mpr hx
  set C : ℝ := M / (‖x‖ - R) ^ 2 with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hg : Integrable ((Metric.closedBall (0 : R3) R).indicator (fun _ => C)) volume := by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const hfin (by simp)
  refine Integrable.mono' hg (aestronglyMeasurable_bsK hmeas x) ?_
  filter_upwards with y
  by_cases hy : ω y = 0
  · rw [bsK_eq_zero hy]
    simp only [norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hCnn) y
  · have hyR : ‖y‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hsupp y hy
    rw [Set.indicator_of_mem (by simpa [Metric.mem_closedBall, dist_eq_norm] using hyR)]
    have hd : ‖x‖ - R ≤ ‖x - y‖ := by
      have h := norm_sub_norm_le x y
      linarith
    have hpos : 0 < ‖x - y‖ := lt_of_lt_of_le hc hd
    have hd3 : (‖x - y‖ ^ 3)⁻¹ * ‖x - y‖ = (‖x - y‖ ^ 2)⁻¹ := by
      rw [show (‖x - y‖ ^ 3) = ‖x - y‖ ^ 2 * ‖x - y‖ by ring, mul_inv]
      field_simp
    have hstep : (‖x - y‖ ^ 3)⁻¹ * ‖ω y‖ * ‖x - y‖ ≤ M * (‖x - y‖ ^ 2)⁻¹ := by
      calc (‖x - y‖ ^ 3)⁻¹ * ‖ω y‖ * ‖x - y‖
          = ‖ω y‖ * ((‖x - y‖ ^ 3)⁻¹ * ‖x - y‖) := by ring
        _ = ‖ω y‖ * (‖x - y‖ ^ 2)⁻¹ := by rw [hd3]
        _ ≤ M * (‖x - y‖ ^ 2)⁻¹ := mul_le_mul_of_nonneg_right (hω y) (by positivity)
    refine (norm_bsK_le ω x y).trans (hstep.trans ?_)
    rw [hCdef, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      ((inv_le_inv₀ (by positivity) (by positivity)).mpr (by nlinarith)) hM

/-! ## The pointwise Lipschitz estimate for the integrand -/

/-- On `ball x (‖x‖/4)` and on the support of `ω`, the integrand `bsK ω z y` is Lipschitz in `z`
with constant `1030·64·M/‖x‖³`. -/
theorem bsK_diff_le {ω : R3 → R3} {R M : ℝ} (hM : 0 ≤ M) (hω : ∀ y, ‖ω y‖ ≤ M)
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R) {x : R3} (hxR : 2 * R ≤ ‖x‖)
    {z z' : R3} (hz : z ∈ Metric.ball x (‖x‖ / 4)) (hz' : z' ∈ Metric.ball x (‖x‖ / 4))
    (y : R3) :
    ‖bsK ω z y - bsK ω z' y‖ ≤ (1030 * 64) * M / ‖x‖ ^ 3 * ‖z - z'‖ := by
  rcases eq_or_lt_of_le (norm_nonneg x) with hx0 | hx0
  · exfalso
    have h : dist z x < ‖x‖ / 4 := hz
    have h4 : ‖x‖ / 4 = 0 := by nlinarith [hx0]
    linarith [dist_nonneg (x := z) (y := x)]
  · have hR2 : R ≤ ‖x‖ / 2 := by linarith
    by_cases hy : ω y = 0
    · rw [bsK_eq_zero hy, bsK_eq_zero hy, sub_zero, norm_zero]
      have h1 : 0 ≤ (1030 * 64) * M := by positivity
      have h2 : 0 ≤ (‖x‖ ^ 3)⁻¹ := inv_nonneg.mpr (by positivity)
      have h3 : 0 ≤ (1030 * 64) * M / ‖x‖ ^ 3 := by
        rw [div_eq_mul_inv]; exact mul_nonneg h1 h2
      exact mul_nonneg h3 (norm_nonneg _)
    · have hyR : ‖y‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hsupp y hy
      have hy2 : ‖y‖ ≤ ‖x‖ / 2 := le_trans hyR hR2
      have hzx : dist z x < ‖x‖ / 4 := hz
      have hz'x : dist z' x < ‖x‖ / 4 := hz'
      rw [dist_eq_norm] at hzx hz'x
      have hxy : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
      have hzx' : ‖z - x‖ < ‖x‖ / 4 := by first | exact hzx | rwa [norm_sub_rev] at hzx
      have hz'x' : ‖z' - x‖ < ‖x‖ / 4 := by first | exact hz'x | rwa [norm_sub_rev] at hz'x
      have hlo : ‖x‖ / 4 ≤ ‖z - y‖ := by
        have h1 : ‖x - y‖ ≤ ‖z - x‖ + ‖z - y‖ := by
          rw [show x - y = (x - z) + (z - y) by abel]
          simpa [norm_sub_rev] using norm_add_le (x - z) (z - y)
        have h3 : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
        linarith
      have hlo' : ‖x‖ / 4 ≤ ‖z' - y‖ := by
        have h1 : ‖x - y‖ ≤ ‖z' - x‖ + ‖z' - y‖ := by
          rw [show x - y = (x - z') + (z' - y) by abel]
          simpa [norm_sub_rev] using norm_add_le (x - z') (z' - y)
        have h3 : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
        linarith
      have hhi : ‖z - y‖ ≤ 7 * (‖x‖ / 4) := by
        have h2 : ‖z - y‖ ≤ ‖z - x‖ + ‖x - y‖ := by
          rw [show z - y = (z - x) + (x - y) by abel]
          exact norm_add_le _ _
        have h3 : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
        linarith
      have hhi' : ‖z' - y‖ ≤ 7 * (‖x‖ / 4) := by
        have h2 : ‖z' - y‖ ≤ ‖z' - x‖ + ‖x - y‖ := by
          rw [show z' - y = (z' - x) + (x - y) by abel]
          exact norm_add_le _ _
        have h3 : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
        linarith
      have hm : 0 < ‖x‖ / 4 := by positivity
      have hbd : ‖(‖z - y‖ ^ 3)⁻¹ • (z - y) - (‖z' - y‖ ^ 3)⁻¹ • (z' - y)‖
          ≤ 1030 / (‖x‖ / 4) ^ 3 * ‖z - z'‖ := by
        have h := norm_smul_inv_norm_cube_sub_le hm hlo hlo' hhi hhi'
        have heq : (z - y) - (z' - y) = z - z' := by abel
        rwa [heq] at h
      have hrew : bsK ω z y - bsK ω z' y
          = WithLp.toLp 2 (crossProduct (ω y)
              ((‖z - y‖ ^ 3)⁻¹ • (z - y) - (‖z' - y‖ ^ 3)⁻¹ • (z' - y))) := by
        simp only [bsK, WithLp.toLp_sub, map_sub, map_smul]
      calc ‖bsK ω z y - bsK ω z' y‖
          = ‖WithLp.toLp 2 (crossProduct (ω y)
              ((‖z - y‖ ^ 3)⁻¹ • (z - y) - (‖z' - y‖ ^ 3)⁻¹ • (z' - y)))‖ := by rw [hrew]
        _ ≤ ‖ω y‖ * ‖(‖z - y‖ ^ 3)⁻¹ • (z - y) - (‖z' - y‖ ^ 3)⁻¹ • (z' - y)‖ :=
            norm_toLp_crossProduct_le _ _
        _ ≤ M * (1030 / (‖x‖ / 4) ^ 3 * ‖z - z'‖) :=
            mul_le_mul (hω y) hbd (norm_nonneg _) hM
        _ = (1030 * 64) * M / ‖x‖ ^ 3 * ‖z - z'‖ := by
            have hxne : ‖x‖ ≠ 0 := ne_of_gt hx0
            field_simp
            ring

/-! ## The congr--- version of the measurability transfer -/

/-- Stripping the `toLp` wrapper and the (ae nonzero) scalar factor `(‖z - y‖³)⁻¹` from the
ae strong measurability of the Biot–Savart integrand. -/
theorem aestronglyMeasurable_cross_of_bsK {ω : R3 → R3} {z : R3}
    (hz : AEStronglyMeasurable (bsK ω z) volume) :
    AEStronglyMeasurable (fun y : R3 => crossProduct (ω y) (z - y)) volume := by
  have h1 : AEStronglyMeasurable
      (fun y : R3 => (‖z - y‖ ^ (3 : ℕ))⁻¹ • crossProduct (ω y) (z - y)) volume :=
    (by fun_prop : Continuous fun v : R3 => WithLp.ofLp v).comp_aestronglyMeasurable hz
  have h2 : AEStronglyMeasurable (fun y : R3 =>
      (‖z - y‖ ^ (3 : ℕ)) • ((‖z - y‖ ^ (3 : ℕ))⁻¹ • crossProduct (ω y) (z - y))) volume :=
    (((by fun_prop : Continuous fun y : R3 => ‖z - y‖ ^ (3 : ℕ))).aestronglyMeasurable).smul h1
  refine h2.congr ?_
  have hne : ∀ᵐ y ∂(volume : Measure R3), y ≠ z := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton z
  filter_upwards [hne] with y hy
  rw [smul_smul,
    mul_inv_cancel₀ (pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hy)))),
    one_smul]

/-! ## Lipschitz decay of `biotSavart ω` in the far field -/

/-- On the ball of radius `‖x‖/4` around a far point `x` (`2R ≤ ‖x‖`), the Biot–Savart field of a
bounded, compactly supported, ae strongly measurable vorticity is Lipschitz with constant
`2^20 · M R³/‖x‖³`. -/
theorem biotSavart_lipschitzOn_far {ω : R3 → R3} {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hω : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : AEStronglyMeasurable ω volume) {x : R3} (hxR : 2 * R ≤ ‖x‖) :
    LipschitzOnWith ((2 ^ 20 : ℝ) * M * R ^ 3 / ‖x‖ ^ 3).toNNReal (biotSavart ω)
      (Metric.ball x (‖x‖ / 4)) := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro z hz z' hz'
  rcases eq_or_lt_of_le (norm_nonneg x) with hx0 | hx0
  · exfalso
    have h : dist z x < ‖x‖ / 4 := hz
    have h4 : ‖x‖ / 4 = 0 := by nlinarith [hx0]
    linarith [dist_nonneg (x := z) (y := x)]
  · have hK : 0 ≤ (2 ^ 20 : ℝ) * M * R ^ 3 / ‖x‖ ^ 3 := by positivity
    rw [Real.coe_toNNReal _ hK]
    have hR2 : R ≤ ‖x‖ / 2 := by linarith
    -- the two points are outside the support
    have hsq : ∀ w ∈ Metric.ball x (‖x‖ / 4), R < ‖w‖ := by
      intro w hw
      have hwx : ‖w - x‖ < ‖x‖ / 4 := by simpa [dist_eq_norm] using hw
      have h1 : ‖x‖ ≤ ‖w - x‖ + ‖w‖ := by
        rw [show x = (x - w) + w by abel]
        simpa [norm_sub_rev] using norm_add_le (x - w) w
      linarith
    have hi_z : Integrable (bsK ω z) volume := integrable_bsK hM hω hsupp hmeas (hsq z hz)
    have hi_z' : Integrable (bsK ω z') volume := integrable_bsK hM hω hsupp hmeas (hsq z' hz')
    have hsub : (∫ y, bsK ω z y) - (∫ y, bsK ω z' y) = ∫ y, (bsK ω z y - bsK ω z' y) :=
      (integral_sub hi_z hi_z').symm
    have hF : biotSavart ω z - biotSavart ω z'
        = (4 * Real.pi)⁻¹ • ∫ y, (bsK ω z y - bsK ω z' y) := by
      rw [biotSavart_apply, biotSavart_apply, ← smul_sub, ← hsub]
    have hvanish : ∀ y ∉ Metric.closedBall (0 : R3) R, bsK ω z y - bsK ω z' y = 0 := by
      intro y hy
      have h0 : ω y = 0 := by
        by_contra h
        exact hy (hsupp y h)
      rw [bsK_eq_zero h0, bsK_eq_zero h0, sub_zero]
    have hset : ‖∫ y, (bsK ω z y - bsK ω z' y)‖
        = ‖∫ y in Metric.closedBall (0 : R3) R, (bsK ω z y - bsK ω z' y)‖ := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hvanish]
    have hbound : ‖∫ y in Metric.closedBall (0 : R3) R, (bsK ω z y - bsK ω z' y)‖
        ≤ ((1030 * 64) * M / ‖x‖ ^ 3 * ‖z - z'‖)
            * (R ^ 3 * (Real.pi * 4 / 3)) := by
      have h1 : ‖∫ y in Metric.closedBall (0 : R3) R, (bsK ω z y - bsK ω z' y)‖
          ≤ ((1030 * 64) * M / ‖x‖ ^ 3 * ‖z - z'‖)
              * Measure.real volume (Metric.closedBall (0 : R3) R) := by
        apply norm_setIntegral_le_of_norm_le_const
        · rw [EuclideanSpace.volume_closedBall_fin_three]
          exact ENNReal.mul_lt_top (ENNReal.pow_lt_top (n := 3) ENNReal.ofReal_lt_top)
            ENNReal.ofReal_lt_top
        · intro y _
          exact bsK_diff_le hM hω hsupp hxR hz hz' y
      rwa [volume_closedBall_real R hR] at h1
    have hcoef : (4 * Real.pi)⁻¹ * (1030 * 64) * (Real.pi * 4 / 3) ≤ (2 : ℝ) ^ 20 := by
      have h1 : (4 * Real.pi)⁻¹ * (Real.pi * 4) = 1 := by
        rw [mul_comm 4 Real.pi, inv_mul_cancel₀ (by positivity)]
      nlinarith [h1, Real.pi_pos]
    have hX : 0 ≤ M * R ^ 3 / ‖x‖ ^ 3 * ‖z - z'‖ := by
      have h1 : 0 ≤ M * R ^ 3 := by positivity
      exact mul_nonneg (div_nonneg h1 (by positivity)) (norm_nonneg _)
    calc ‖biotSavart ω z - biotSavart ω z'‖
        = (4 * Real.pi)⁻¹ * ‖∫ y, (bsK ω z y - bsK ω z' y)‖ := by
          rw [hF, norm_smul, Real.norm_of_nonneg (by positivity)]
      _ = (4 * Real.pi)⁻¹
            * ‖∫ y in Metric.closedBall (0 : R3) R, (bsK ω z y - bsK ω z' y)‖ := by rw [hset]
      _ ≤ (4 * Real.pi)⁻¹ * (((1030 * 64) * M / ‖x‖ ^ 3 * ‖z - z'‖)
            * (R ^ 3 * (Real.pi * 4 / 3))) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = ((4 * Real.pi)⁻¹ * (1030 * 64) * (Real.pi * 4 / 3))
            * (M * R ^ 3 / ‖x‖ ^ 3 * ‖z - z'‖) := by ring
      _ ≤ (2 : ℝ) ^ 20 * (M * R ^ 3 / ‖x‖ ^ 3 * ‖z - z'‖) :=
          mul_le_mul_of_nonneg_right hcoef hX
      _ = ((2 ^ 20 : ℝ) * M * R ^ 3 / ‖x‖ ^ 3) * ‖z - z'‖ := by ring


/-- A function that vanishes off a single point has zero Fréchet derivative everywhere: off the
point it is locally zero, and at the point it is either discontinuous (hence not differentiable)
or identically zero. -/
theorem fderiv_eq_zero_of_eq_zero_off_single {F : R3 → R3} {p : R3}
    (h : ∀ z, z ≠ p → F z = 0) (x : R3) : fderiv ℝ F x = 0 := by
  by_cases hxp : x = p
  · have h' : ∀ z, z ≠ x → F z = 0 := by
      intro z hz
      exact h z (fun hzp => hz (by rw [hxp, hzp]))
    by_cases hd : DifferentiableAt ℝ F x
    · have hcont : ContinuousAt F x := hd.continuousAt
      have hev : F =ᶠ[𝓝[≠] x] 0 := by
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact h' z hz
      have hlim : Tendsto F (𝓝[≠] x) (𝓝 0) :=
        Filter.Tendsto.congr' hev.symm
          (tendsto_const_nhds : Tendsto (fun _ : R3 => (0 : R3)) (𝓝[≠] x) (𝓝 0))
      have hfx : F x = 0 :=
        tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds) hlim
      have hzero : F = fun _ => 0 := by
        funext z
        by_cases hz : z = x
        · rw [hz]; exact hfx
        · exact h' z hz
      rw [hzero]
      simp
    · exact fderiv_zero_of_not_differentiableAt hd
  · have hev : F =ᶠ[𝓝 x] (fun _ : R3 => 0) := by
      have hball : Metric.ball x (dist x p / 2) ∈ 𝓝 x :=
        Metric.ball_mem_nhds x (div_pos (dist_pos.mpr hxp) two_pos)
      filter_upwards [hball] with z hz
      refine h z ?_
      intro hzp
      have h1 : dist z x < dist x p / 2 := hz
      subst hzp
      rw [dist_comm] at h1
      linarith [dist_pos.mpr hxp]
    rw [hev.fderiv_eq]
    simp


/-! ## The main theorem -/


end Work.LWP.BiotSavart
end
-- ===== merged: Submission.Work.LWP.BiotSavart.nearField_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity MeasureTheory WithLp
open scoped Matrix ENNReal

namespace Work.LWP.BiotSavart

/-- The Biot–Savart integrand of `biotSavart` at `(x,y)`: `(‖x-y‖³)⁻¹ • (ω y × (x-y))`, as an
element of `ℝ³`; `biotSavart ω x = (4π)⁻¹ • ∫ y, bsIntegrand ω x y`. -/
noncomputable def bsIntegrand (ω : R3 → R3) (x y : R3) : R3 :=
  WithLp.toLp 2 ((‖x - y‖ ^ (3 : ℕ))⁻¹ • crossProduct (ω y) (x - y))

lemma biotSavart_eq_integral (ω : R3 → R3) (x : R3) :
    biotSavart ω x = (4 * Real.pi)⁻¹ • ∫ y, bsIntegrand ω x y := rfl

/-- **Pointwise bound on the Biot–Savart integrand** (no hypothesis on the size of `y`):
`‖(‖x-y‖³)⁻¹ • (ω y × (x-y))‖ ≤ M ‖x-y‖⁻²` whenever `‖ω y‖ ≤ M`. -/
lemma bsIntegrand_norm_le {ω : R3 → R3} {M : ℝ} (hM : 0 ≤ M)
    (hω : ∀ y, ‖ω y‖ ≤ M) (x y : R3) :
    ‖bsIntegrand ω x y‖ ≤ M * ((‖x - y‖ ^ (2 : ℕ))⁻¹) := by
  have ha : (0 : ℝ) ≤ ‖x - y‖ := norm_nonneg _
  have hcross : ‖WithLp.toLp 2 (crossProduct (ω y) (x - y))‖ ≤ M * ‖x - y‖ :=
    le_trans (norm_toLp_crossProduct_le (ω y) (x - y))
      (mul_le_mul_of_nonneg_right (hω y) ha)
  have hkey : (‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖x - y‖ ≤ (‖x - y‖ ^ (2 : ℕ))⁻¹ := by
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h]; norm_num
    · have heq : (‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖x - y‖ = (‖x - y‖ ^ (2 : ℕ))⁻¹ := by
        rw [show ‖x - y‖ ^ (3 : ℕ) = ‖x - y‖ ^ (2 : ℕ) * ‖x - y‖ by ring, mul_inv]
        field_simp
      rw [heq]
  rw [bsIntegrand, WithLp.toLp_smul, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
  calc (‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖WithLp.toLp 2 (crossProduct (ω y) (x - y))‖
      ≤ (‖x - y‖ ^ (3 : ℕ))⁻¹ * (M * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left hcross (inv_nonneg.mpr (by positivity))
    _ = M * ((‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖x - y‖) := by ring
    _ ≤ M * (‖x - y‖ ^ (2 : ℕ))⁻¹ := mul_le_mul_of_nonneg_left hkey hM

/-- The integral of `‖z‖⁻²` over the closed ball of radius `r ≥ 0` about the origin of `ℝ³` is
`4πr` — the Jacobian `4πs²` of the spherical shell of radius `s` cancels the `s⁻²` of the
integrand exactly, so the borderline `r`-integrable case is finite.  The proof radially reduces
the integral with `MeasureTheory.integral_fun_norm_addHaar` (`Module.finrank ℝ R3 = 3`) and then
evaluates the resulting one-dimensional integral `∫ y in Ioi 0, y² · f y = r`. -/
lemma inv_sq_lintegral_closedBall_le (r : ℝ) (hr : 0 ≤ r) :
    ∫⁻ z in Metric.closedBall (0 : R3) r, ENNReal.ofReal ((‖z‖ ^ (2 : ℕ))⁻¹)
      ≤ ENNReal.ofReal (4 * Real.pi * r) := by
  classical
  let f : ℝ → ℝ := fun s => if s ≤ r then (s ^ 2)⁻¹ else 0
  have hf_nn : ∀ s, 0 ≤ f s := by
    intro s
    by_cases h : s ≤ r
    · simp only [f, if_pos h]; positivity
    · simp only [f, if_neg h]; exact le_refl 0
  have hcongr1 : ∀ y ∈ Set.Ioi (0 : ℝ), y ^ (2 : ℕ) * f y
      = (Set.Ioc (0 : ℝ) r).indicator (fun _ => (1 : ℝ)) y := by
    intro y hy
    have hypos : (0 : ℝ) < y := hy
    by_cases h : y ≤ r
    · rw [Set.indicator_of_mem (show y ∈ Set.Ioc (0 : ℝ) r from ⟨hypos, h⟩)]
      change y ^ 2 * (if y ≤ r then (y ^ 2)⁻¹ else 0) = (1 : ℝ)
      rw [if_pos h]
      field_simp
    · rw [Set.indicator_of_notMem (fun hh => h hh.2)]
      change y ^ 2 * (if y ≤ r then (y ^ 2)⁻¹ else 0) = (0 : ℝ)
      rw [if_neg h, mul_zero]
  have hI : ∫ y in Set.Ioi (0 : ℝ), y ^ (2 : ℕ) * f y = r := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr1,
      MeasureTheory.setIntegral_indicator measurableSet_Ioc]
    have hset : Set.Ioi (0 : ℝ) ∩ Set.Ioc (0 : ℝ) r = Set.Ioc (0 : ℝ) r := by
      ext y; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]; tauto
    rw [hset, MeasureTheory.setIntegral_const, MeasureTheory.Measure.real, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith)]
    simp
  have hfr : Module.finrank ℝ R3 = 3 := by simp [Work.LWP.R3]
  have hvol : MeasureTheory.Measure.real MeasureTheory.volume (Metric.ball (0 : R3) 1)
      = Real.pi * 4 / 3 := by
    rw [MeasureTheory.Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ Real.pi * 4 / 3)]
    norm_num
  have hbear : ∫ z : R3, f ‖z‖ = 4 * Real.pi * r := by
    rw [MeasureTheory.integral_fun_norm_addHaar (MeasureTheory.volume) f]
    simp only [hfr, Nat.reduceSub, smul_eq_mul]
    rw [hI, hvol]
    ring
  have hbase : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc (0 : ℝ) r) := by
    refine MeasureTheory.integrableOn_const ?_ ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    · simp
  have hind : Integrable ((Set.Ioc (0 : ℝ) r).indicator (fun _ => (1 : ℝ))) := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioc]
    exact hbase
  have hIntOn : IntegrableOn (fun y : ℝ => y ^ (2 : ℕ) * f y) (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.IntegrableOn.congr_fun hind.integrableOn
      (fun y hy => (hcongr1 y hy).symm) measurableSet_Ioi
  have hInt : Integrable (fun z : R3 => f ‖z‖) := by
    rw [MeasureTheory.integrable_fun_norm_addHaar (MeasureTheory.volume) (f := f)]
    simp only [hfr, Nat.reduceSub, smul_eq_mul]
    exact hIntOn
  have hlin : ∫⁻ z : R3, ENNReal.ofReal (f ‖z‖) < ⊤ := hInt.lintegral_lt_top
  have htoReal : (∫⁻ z : R3, ENNReal.ofReal (f ‖z‖)).toReal = 4 * Real.pi * r := by
    rw [← MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun z => hf_nn ‖z‖) hInt.aestronglyMeasurable]
    exact hbear
  have hval : ∫⁻ z : R3, ENNReal.ofReal (f ‖z‖) = ENNReal.ofReal (4 * Real.pi * r) := by
    rw [← ENNReal.ofReal_toReal (a := ∫⁻ z : R3, ENNReal.ofReal (f ‖z‖)) hlin.ne, htoReal]
  have hpt : ∀ z : R3, ENNReal.ofReal (f ‖z‖)
      = (Metric.closedBall (0 : R3) r).indicator
          (fun z => ENNReal.ofReal ((‖z‖ ^ (2 : ℕ))⁻¹)) z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall (0 : R3) r
    · rw [Set.indicator_of_mem hz]
      have hz' : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      simp only [f, if_pos hz']
    · rw [Set.indicator_of_notMem hz]
      have hz' : ¬ (‖z‖ ≤ r) := by
        intro h
        exact hz (by simpa [Metric.mem_closedBall, dist_eq_norm] using h)
      simp only [f, if_neg hz', ENNReal.ofReal_zero]
  have hred : ∫⁻ z in Metric.closedBall (0 : R3) r, ENNReal.ofReal ((‖z‖ ^ (2 : ℕ))⁻¹)
      = ∫⁻ z : R3, ENNReal.ofReal (f ‖z‖) := by
    rw [← MeasureTheory.lintegral_indicator (Metric.isClosed_closedBall.measurableSet)
      (fun z => ENNReal.ofReal ((‖z‖ ^ (2 : ℕ))⁻¹))]
    exact MeasureTheory.lintegral_congr (fun z => (hpt z).symm)
  rw [hred, hval]

/-- Translation invariance of the set integral over a closed ball: replacing the centre by a
translate and the variable by its difference from the centre does not change the integral. -/
lemma lintegral_closedBall_sub_eq (c : R3) (r : ℝ) (F : R3 → ℝ≥0∞) :
    ∫⁻ y in Metric.closedBall c r, F (y - c) = ∫⁻ z in Metric.closedBall (0 : R3) r, F z := by
  classical
  have hs : MeasurableSet (Metric.closedBall c r) := Metric.isClosed_closedBall.measurableSet
  have hs0 : MeasurableSet (Metric.closedBall (0 : R3) r) :=
    Metric.isClosed_closedBall.measurableSet
  have hmem : ∀ y : R3, y ∈ Metric.closedBall c r ↔ y - c ∈ Metric.closedBall (0 : R3) r := by
    intro y
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  rw [← MeasureTheory.lintegral_indicator hs (fun y => F (y - c))]
  have h1 : (fun y => (Metric.closedBall c r).indicator (fun y => F (y - c)) y)
      = fun y => (Metric.closedBall (0 : R3) r).indicator F (y - c) := by
    funext y
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hy : y ∈ Metric.closedBall c r
    · simp [hy, (hmem y).mp hy]
    · have hy' : y - c ∉ Metric.closedBall (0 : R3) r := fun h => hy ((hmem y).mpr h)
      simp [hy, hy']
  rw [h1, MeasureTheory.lintegral_sub_right_eq_self
    (fun z => (Metric.closedBall (0 : R3) r).indicator F z) c]
  rw [MeasureTheory.lintegral_indicator hs0 F]

/-- The shifted version of `inv_sq_lintegral_closedBall_le_aux`: the singularity may sit at the
centre of the ball. -/
lemma inv_sq_lintegral_closedBall_shifted_le (c : R3) {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ y in Metric.closedBall c r, ENNReal.ofReal ((‖y - c‖ ^ (2 : ℕ))⁻¹)
      ≤ ENNReal.ofReal (4 * Real.pi * r) := by
  rw [lintegral_closedBall_sub_eq c r (fun z => ENNReal.ofReal ((‖z‖ ^ (2 : ℕ))⁻¹))]
  exact inv_sq_lintegral_closedBall_le r hr

/-- **The scalar near-field estimate**: for `‖x‖ ≤ 2R` the singular weight `‖x-y‖⁻²` has
integral at most `12πR = 4π·3R` over the ball of radius `R` about the origin, because that ball
is contained in the ball of radius `3R` about `x`. -/
lemma near_lintegral_scalar {R : ℝ} (hR : 0 ≤ R) {x : R3} (hx : ‖x‖ ≤ 2 * R) :
    ∫⁻ y in Metric.closedBall (0 : R3) R, ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)
      ≤ ENNReal.ofReal (12 * Real.pi * R) := by
  have hsub : Metric.closedBall (0 : R3) R ⊆ Metric.closedBall x (3 * R) := by
    intro y hy
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy
    simp only [Metric.mem_closedBall, dist_eq_norm]
    calc ‖y - x‖ = ‖x - y‖ := norm_sub_rev _ _
      _ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ 3 * R := by linarith
  calc ∫⁻ y in Metric.closedBall (0 : R3) R, ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)
      ≤ ∫⁻ y in Metric.closedBall x (3 * R), ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹) :=
        lintegral_mono_set hsub
    _ = ∫⁻ y in Metric.closedBall x (3 * R), ENNReal.ofReal ((‖y - x‖ ^ (2 : ℕ))⁻¹) := by
        apply lintegral_congr
        intro y
        rw [norm_sub_rev]
    _ ≤ ENNReal.ofReal (4 * Real.pi * (3 * R)) :=
        inv_sq_lintegral_closedBall_shifted_le x (by linarith)
    _ = ENNReal.ofReal (12 * Real.pi * R) := by
        congr 1
        ring

/-- **Reduction of the vector-valued integrand to the scalar singular weight.**  Since `ω`
vanishes off the closed ball of radius `R`, the `ℝ³`-valued integrand of `biotSavart` is
dominated by `M` times the scalar weight `‖x-y‖⁻²` on that ball. -/
lemma lintegral_bsIntegrand_le {ω : R3 → R3} {R M : ℝ} (hM : 0 ≤ M)
    (hω : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (x : R3)
    (hscal : ∫⁻ y in Metric.closedBall (0 : R3) R, ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)
      ≤ ENNReal.ofReal (12 * Real.pi * R)) :
    ∫⁻ y, ENNReal.ofReal ‖bsIntegrand ω x y‖ ≤ ENNReal.ofReal (12 * Real.pi * M * R) := by
  classical
  have hsmeas : MeasurableSet (Metric.closedBall (0 : R3) R) :=
    Metric.isClosed_closedBall.measurableSet
  have hpoint : ∀ y, ENNReal.ofReal ‖bsIntegrand ω x y‖
      ≤ (Metric.closedBall (0 : R3) R).indicator
          (fun y => ENNReal.ofReal M * ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y := by
    intro y
    by_cases hy : y ∈ Metric.closedBall (0 : R3) R
    · rw [Set.indicator_of_mem hy, ← ENNReal.ofReal_mul hM]
      exact ENNReal.ofReal_le_ofReal (bsIntegrand_norm_le hM hω x y)
    · rw [Set.indicator_of_notMem hy]
      have hωy : ω y = 0 := by
        by_contra hne
        exact hy (hsupp y hne)
      simp [bsIntegrand, hωy]
  have hsplit : (fun y => (Metric.closedBall (0 : R3) R).indicator
        (fun y => ENNReal.ofReal M * ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y)
      = fun y => ENNReal.ofReal M * (Metric.closedBall (0 : R3) R).indicator
          (fun y => ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y := by
    funext y
    by_cases hy : y ∈ Metric.closedBall (0 : R3) R <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
  calc ∫⁻ y, ENNReal.ofReal ‖bsIntegrand ω x y‖
      ≤ ∫⁻ y, (Metric.closedBall (0 : R3) R).indicator
          (fun y => ENNReal.ofReal M * ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y :=
        lintegral_mono hpoint
    _ = ∫⁻ y, ENNReal.ofReal M * (Metric.closedBall (0 : R3) R).indicator
          (fun y => ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y := by rw [hsplit]
    _ = ENNReal.ofReal M * ∫⁻ y, (Metric.closedBall (0 : R3) R).indicator
          (fun y => ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y :=
        MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal M * ∫⁻ y in Metric.closedBall (0 : R3) R,
          ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹) := by
        rw [MeasureTheory.lintegral_indicator hsmeas]
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal (12 * Real.pi * R) :=
        mul_le_mul_right hscal _
    _ = ENNReal.ofReal (12 * Real.pi * M * R) := by
        rw [← ENNReal.ofReal_mul hM]
        congr 1
        ring

/-- **The near-field bound**: for `‖x‖ ≤ 2R`, `‖biotSavart ω x‖ ≤ 3 M R`. -/
lemma norm_biotSavart_near {ω : R3 → R3} {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hω : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    {x : R3} (hx : ‖x‖ ≤ 2 * R) :
    ‖biotSavart ω x‖ ≤ 3 * M * R := by
  rw [biotSavart_eq_integral, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : ‖∫ y, bsIntegrand ω x y‖
      ≤ (∫⁻ y, ENNReal.ofReal ‖bsIntegrand ω x y‖).toReal :=
    norm_integral_le_lintegral_norm _
  have h2 : (∫⁻ y, ENNReal.ofReal ‖bsIntegrand ω x y‖).toReal ≤ 12 * Real.pi * M * R :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (lintegral_bsIntegrand_le hM hω hsupp x (near_lintegral_scalar hR hx))).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  calc (4 * Real.pi)⁻¹ * ‖∫ y, bsIntegrand ω x y‖
      ≤ (4 * Real.pi)⁻¹ * (12 * Real.pi * M * R) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ = 3 * M * R := by
        field_simp
        ring


end Work.LWP.BiotSavart
end
