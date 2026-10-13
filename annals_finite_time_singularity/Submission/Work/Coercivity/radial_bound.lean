/-
# The radial bound of the commutator defect `E₁`

This module proves `Work.Coercivity.radial_bound`: in the *Hardy* case
`A₁(f)(0) = A₂(f)(0) = 0` (where `A₁ = L₁₂(D_θ f)`, `A₂ = L₁₂(f)`), the two radial factors

  `F₁ = pcoef α · A₁ - Wcoef α · KC1`,   `F₂ = Wcoef α · KC0 - pcoef α · A₂`

of the commutator defect `E₁ = Γ(θ)F₁(z) + D_θΓ(θ)F₂(z)` of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (3) 2021,

satisfy `∫_0^∞ (D_z^j F)² w² ≤ C |f|²_{ℋ^n}` for all `j ≤ n`, with `C` depending only on
`α` and `n`.  This is the analytic ingredient `CT.radial_bound` of
`Work.Coercivity.commutTheta_of_children`.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Coercivity.CTDefs
import Submission.Work.Coercivity.DzRIter_L12f
import Submission.Work.Coercivity.radial_algebra
import Submission.Work.Coercivity.F1F2_smooth
import Submission.Work.Coercivity.HkMem_terms
import Submission.Work.Coercivity.L12_w_sq_le
import Submission.Work.Coercivity.KC_sq_le
import Submission.Work.Coercivity.L12_facts_n
import Submission.Work.Coercivity.L12dens_integrableOn
import Submission.Work.Coercivity.L12dens_sq_slice
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Coercivity.DzRIter_mul
import Submission.Work.Coercivity.aesm_angAvg
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Elliptic.HardyLeftW
import Submission.Work.Elliptic.HardyRightW

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Linearity of the iterates of `D_z = z ∂_z` -/

/-- `D_z^j` is additive on functions `C^∞` on `(0,∞)`. -/
theorem rb_DzRIter_add {A B : ℝ → ℝ} (hA : ContDiffOn ℝ ⊤ A (Set.Ioi 0))
    (hB : ContDiffOn ℝ ⊤ B (Set.Ioi 0)) (j : ℕ) :
    Set.EqOn (CT.DzRIter j (A + B)) (fun z => CT.DzRIter j A z + CT.DzRIter j B z)
      (Set.Ioi 0) := by
  intro z hz
  have h := Spaces.DerivLike.iterate_add (s := Set.Ioi 0) (P := SmoothIoi0) DzR_DerivLike j hA hB
  have hz' := h hz
  rw [DzRIter_eq_iterate j (A + B), DzRIter_eq_iterate j A, DzRIter_eq_iterate j B]
  simpa using hz'

/-- `D_z^j` commutes with multiplication by a constant, on functions `C^∞` on `(0,∞)`. -/
theorem rb_DzRIter_const_mul (c : ℝ) {A : ℝ → ℝ} (hA : ContDiffOn ℝ ⊤ A (Set.Ioi 0)) (j : ℕ) :
    Set.EqOn (CT.DzRIter j (fun z => c * A z)) (fun z => c * CT.DzRIter j A z) (Set.Ioi 0) := by
  intro z hz
  have h := Spaces.DerivLike.iterate_smul (s := Set.Ioi 0) (P := SmoothIoi0) DzR_DerivLike j c hA
  have hz' := h hz
  rw [DzRIter_eq_iterate j (fun z => c * A z), DzRIter_eq_iterate j A]
  simpa using hz'

/-! ## Elementary bounds for the weight `z ↦ 1/(1+z)²` -/

theorem rb_inv_sq_le_inv_sq {a b : ℝ} (ha : 0 < a) (h : a ≤ b) : 1 / b ^ 2 ≤ 1 / a ^ 2 := by
  have hb : 0 < b := lt_of_lt_of_le ha h
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem rb_continuousOn_inv_one_add_sq (s : Set ℝ) (h : ∀ z ∈ s, 0 < 1 + z) :
    ContinuousOn (fun z : ℝ => 1 / (1 + z) ^ 2) s := by
  refine ContinuousOn.div continuousOn_const
    (((continuousOn_const (c := (1 : ℝ))).add continuousOn_id).pow 2) ?_
  intro z hz
  have hz1 := h z hz
  positivity

theorem rb_integrableOn_inv_one_add_sq :
    IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) (Set.Ioc (0 : ℝ) 1) :=
  ((rb_continuousOn_inv_one_add_sq (Set.Icc (0 : ℝ) 1) (fun z hz => by linarith [hz.1])).integrableOn_compact
    isCompact_Icc).mono_set Set.Ioc_subset_Icc_self

theorem rb_integral_Ioc_inv_one_add_sq_le :
    ∫ z in Set.Ioc (0 : ℝ) 1, 1 / (1 + z) ^ 2 ≤ 1 := by
  have hle : ∀ z ∈ Set.Ioc (0 : ℝ) 1, 1 / (1 + z) ^ 2 ≤ (1 : ℝ) := by
    intro z hz
    have h := rb_inv_sq_le_inv_sq (a := (1 : ℝ)) (b := 1 + z) (by norm_num) (by linarith [hz.1])
    simpa using h
  have hInt1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc (0 : ℝ) 1) :=
    MeasureTheory.integrableOn_const (by rw [Real.volume_Ioc]; simp)
  have hmono : ∫ z in Set.Ioc (0 : ℝ) 1, 1 / (1 + z) ^ 2
      ≤ ∫ z in Set.Ioc (0 : ℝ) 1, (1 : ℝ) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity) hInt1 ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with z hz
    exact hle z hz
  have hone : (∫ z in Set.Ioc (0 : ℝ) 1, (1 : ℝ)) = 1 := by
    rw [MeasureTheory.setIntegral_const]
    simp
  linarith [hmono, hone]

theorem rb_integrableOn_Ioi_inv_one_add_sq :
    IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) (Set.Ioi (1 : ℝ)) := by
  have hbase : IntegrableOn (fun t : ℝ => t ^ (-(2 : ℝ))) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  rw [IntegrableOn] at hbase ⊢
  refine hbase.mono' (((rb_continuousOn_inv_one_add_sq (Set.Ioi (1 : ℝ))
    (fun z hz => by have hz1 : (1 : ℝ) < z := hz; linarith)).aestronglyMeasurable
      measurableSet_Ioi)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  have hz1 : (1 : ℝ) < z := hz
  have hz0 : (0 : ℝ) < z := lt_trans one_pos hz1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (1 + z) ^ 2)]
  have hrw : z ^ (-(2 : ℝ)) = (z ^ 2)⁻¹ := by
    rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (le_of_lt hz0),
      Real.rpow_natCast]
  rw [hrw, inv_eq_one_div]
  exact rb_inv_sq_le_inv_sq hz0 (by linarith)

theorem rb_integral_Ioi_inv_one_add_sq_le :
    ∫ z in Set.Ioi (1 : ℝ), 1 / (1 + z) ^ 2 ≤ 1 := by
  have hbase : IntegrableOn (fun t : ℝ => t ^ (-(2 : ℝ))) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hle : ∀ᵐ z ∂(volume.restrict (Set.Ioi (1 : ℝ))), 1 / (1 + z) ^ 2 ≤ z ^ (-(2 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hz1 : (1 : ℝ) < z := hz
    have hz0 : (0 : ℝ) < z := lt_trans one_pos hz1
    have hrw : z ^ (-(2 : ℝ)) = (z ^ 2)⁻¹ := by
      rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (le_of_lt hz0),
        Real.rpow_natCast]
    rw [hrw, inv_eq_one_div]
    exact rb_inv_sq_le_inv_sq hz0 (by linarith)
  have hmono := integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity) hbase hle
  rw [integral_Ioi_rpow_of_lt (a := -(2 : ℝ)) (c := 1) (by norm_num) (by norm_num)] at hmono
  norm_num at hmono
  simpa only [one_div] using hmono

theorem rb_integrableOn_inv_one_add_sq_Iz :
    IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) Spaces.Iz := by
  have h0 : IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
    exact rb_integrableOn_inv_one_add_sq.union rb_integrableOn_Ioi_inv_one_add_sq
  rw [show Spaces.Iz = Set.Ici (0 : ℝ) from rfl, IntegrableOn]
  rw [← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  rw [IntegrableOn] at h0
  exact h0

theorem rb_integral_Iz_inv_one_add_sq_le :
    ∫ z in Spaces.Iz, 1 / (1 + z) ^ 2 ≤ 2 := by
  have hIntIoc := rb_integrableOn_inv_one_add_sq
  have hIntIoi := rb_integrableOn_Ioi_inv_one_add_sq
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) :=
    Set.disjoint_left.mpr (fun z hz1 hz2 => (not_le.mpr hz2) hz1.2)
  have hdecomp : ∫ z in Set.Ioi (0 : ℝ), 1 / (1 + z) ^ 2
      = (∫ z in Set.Ioc (0 : ℝ) 1, 1 / (1 + z) ^ 2)
        + ∫ z in Set.Ioi (1 : ℝ), 1 / (1 + z) ^ 2 := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hIntIoc hIntIoi
  have hIz : (∫ z in Spaces.Iz, 1 / (1 + z) ^ 2)
      = ∫ z in Set.Ioi (0 : ℝ), 1 / (1 + z) ^ 2 :=
    MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm
  rw [hIz, hdecomp]
  have h1 := rb_integral_Ioc_inv_one_add_sq_le
  have h2 := rb_integral_Ioi_inv_one_add_sq_le
  linarith

/-- On `Iz = [0,∞)` one has `z > 0` almost everywhere. -/
theorem rb_ae_pos_of_Iz_radial : ∀ᵐ z ∂(volume.restrict Spaces.Iz), 0 < z := by
  rw [show Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
    ← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  exact ae_restrict_mem measurableSet_Ioi

/-! ## The weighted iterates of `Wcoef` -/

theorem rb_measurable_w : Measurable (fun z : ℝ => Spaces.w z) := by
  unfold Spaces.w
  fun_prop

theorem rb_measurable_DzRIter_Wcoef (α : ℝ) (j : ℕ) :
    AEStronglyMeasurable (CT.DzRIter j (CT.Wcoef α)) (volume.restrict Spaces.Iz) := by
  induction j with
  | zero =>
      have h : Measurable (CT.Wcoef α) := by
        unfold CT.Wcoef
        fun_prop
      exact h.aestronglyMeasurable
  | succ k ih =>
      have h : CT.DzRIter (k + 1) (CT.Wcoef α)
          = fun z : ℝ => z * deriv (CT.DzRIter k (CT.Wcoef α)) z := by
        rw [CT.DzRIter_succ]
        rfl
      rw [h]
      exact (measurable_id.mul (measurable_deriv _)).aestronglyMeasurable

/-- The weighted square of every `D_z`-iterate of `Wcoef α` has integral at most `2M²`,
when `M` bounds `|D_z^k(Wcoef α)(z)| w z ≤ M/(1+z)` on `(0,∞)`. -/
theorem rb_Wcoef_w_sq (α : ℝ) (n : ℕ) (M : ℝ) (hM : 0 < M)
    (hMw : ∀ k ≤ n, ∀ z : ℝ, 0 < z →
        |CT.DzRIter k (CT.Wcoef α) z| * Spaces.w z ≤ M / (1 + z)) :
    ∀ j ≤ n, IntegrableOn (fun z => (CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2)
        Spaces.Iz
      ∧ ∫ z in Spaces.Iz, (CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2 ≤ 2 * M ^ 2 := by
  intro j hj
  have hpt0 : ∀ z ∈ Spaces.Iz,
      (CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2 ≤ M ^ 2 * (1 / (1 + z) ^ 2) := by
    intro z hz
    have hw0 : 0 ≤ Spaces.w z := by rw [Spaces.w]; positivity
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h | h
    · subst h
      have hw : (Spaces.w 0) ^ 2 = 0 := by
        rw [Spaces.w]; norm_num
      rw [hw, mul_zero]
      have : (0 : ℝ) ≤ 1 / (1 + 0) ^ 2 := by positivity
      nlinarith [sq_nonneg M]
    · have h1 := hMw j hj z h
      have hsq : (|CT.DzRIter j (CT.Wcoef α) z| * Spaces.w z) ^ 2 ≤ (M / (1 + z)) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) hw0) h1 2
      rw [mul_pow, sq_abs] at hsq
      have heq : (M / (1 + z)) ^ 2 = M ^ 2 * (1 / (1 + z) ^ 2) := by
        field_simp
      rw [← heq]
      exact hsq
  have hIntMaj : IntegrableOn (fun z : ℝ => M ^ 2 * (1 / (1 + z) ^ 2)) Spaces.Iz :=
    rb_integrableOn_inv_one_add_sq_Iz.const_mul (M ^ 2)
  constructor
  · rw [IntegrableOn] at hIntMaj ⊢
    refine hIntMaj.mono' (((rb_measurable_DzRIter_Wcoef α j).pow 2).mul
      ((rb_measurable_w.aestronglyMeasurable).pow 2)) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hpt0 z hz
  · have hle : ∀ᵐ z ∂(volume.restrict Spaces.Iz),
        (CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2 ≤ M ^ 2 * (1 / (1 + z) ^ 2) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ici] with z hz
      exact hpt0 z hz
    have hmono := integral_mono_of_nonneg
      (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hIntMaj hle
    have hbound : (∫ z in Spaces.Iz, M ^ 2 * (1 / (1 + z) ^ 2)) ≤ 2 * M ^ 2 := by
      rw [MeasureTheory.integral_const_mul]
      have h := rb_integral_Iz_inv_one_add_sq_le
      nlinarith [sq_nonneg M]
    linarith

/-! ## The product of a radial factor with the coefficient `pcoef` -/

theorem rb_inv_sq_le_w_sq {z : ℝ} (hz : 0 < z) : 1 / z ^ 2 ≤ (Spaces.w z) ^ 2 := by
  have h2 : z ^ 2 ≤ (1 + z) ^ 2 := by nlinarith
  have h3 : (1 + z) ^ 2 ≤ (1 + z) ^ 4 := by nlinarith [sq_nonneg z]
  have h4 : z ^ 2 ≤ (1 + z) ^ 4 := le_trans h2 h3
  have hw : (Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
    unfold Spaces.w
    rw [div_pow]
    ring
  rw [hw, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right h4 (sq_nonneg z)]

theorem rb_aestronglyMeasurable_of_continuousOn_Ioi {g : ℝ → ℝ} (h : ContinuousOn g (Set.Ioi 0)) :
    AEStronglyMeasurable g (volume.restrict Spaces.Iz) := by
  rw [show Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
    ← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  exact h.aestronglyMeasurable measurableSet_Ioi

theorem rb_AEStronglyMeasurable_DzRIter {A : ℝ → ℝ} (m : ℕ)
    (hA : AEStronglyMeasurable A (volume.restrict Spaces.Iz)) :
    AEStronglyMeasurable (CT.DzRIter m A) (volume.restrict Spaces.Iz) := by
  induction m with
  | zero => simpa using hA
  | succ k _ =>
      have h : CT.DzRIter (k + 1) A = fun z : ℝ => z * deriv (CT.DzRIter k A) z := by
        rw [CT.DzRIter_succ]
        rfl
      rw [h]
      exact (measurable_id.mul (measurable_deriv _)).aestronglyMeasurable

theorem rb_sum_choose_sq_le (j n : ℕ) (hj : j ≤ n) :
    (∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) ^ 2) ≤ ((2 : ℝ) ^ n) ^ 2 := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.range (j + 1))
    (f := fun k => (j.choose k : ℝ)) (fun k _ => by positivity)
  have h2 : (∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ)) = (2 : ℝ) ^ j := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    simp
  rw [h2] at h
  refine le_trans h ?_
  exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hj) 2

theorem rb_pcoef_mul_w_sq (α : ℝ) (n : ℕ) (A : ℝ → ℝ) (hA : ContDiffOn ℝ ⊤ A (Set.Ioi 0))
    (M H : ℝ) (hM : 0 < M)
    (hMp : ∀ k ≤ n, ∀ z : ℝ, 0 < z →
        |CT.DzRIter k (CT.pcoef α) z| * Spaces.w z ≤ M / z)
    (hBnd : ∀ m ≤ n, IntegrableOn (fun z =>
        (CT.DzRIter m A z) ^ 2 * (Spaces.w z) ^ 2) Spaces.Iz
      ∧ ∫ z in Spaces.Iz, (CT.DzRIter m A z) ^ 2 * (Spaces.w z) ^ 2 ≤ H) :
    ∀ j ≤ n, IntegrableOn (fun z =>
        (CT.DzRIter j (fun t => CT.pcoef α t * A t) z) ^ 2 * (Spaces.w z) ^ 2) Spaces.Iz
      ∧ ∫ z in Spaces.Iz,
          (CT.DzRIter j (fun t => CT.pcoef α t * A t) z) ^ 2 * (Spaces.w z) ^ 2
            ≤ 2 * ((n : ℝ) + 1) * M ^ 2 * ((2 : ℝ) ^ n) ^ 2 * H := by
  have hHnn : 0 ≤ H := by
    have h0 := (hBnd 0 (Nat.zero_le n)).2
    have h0' : 0 ≤ ∫ z in Spaces.Iz, (CT.DzRIter 0 A z) ^ 2 * (Spaces.w z) ^ 2 :=
      integral_nonneg fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  have hpc : ContDiffOn ℝ ⊤ (CT.pcoef α) (Set.Ioi 0) := by
    by_cases hc : Spaces.c α = 0
    · rw [show CT.pcoef α = fun _ : ℝ => 0 from by
        funext z; unfold CT.pcoef; rw [hc]; ring]
      exact contDiffOn_const
    · exact pcoef_contDiffOn α hc
  intro j hj
  -- ## The `D_z`-iterates of `pcoef α · A` are a.e. strongly measurable
  have hPA_meas : AEStronglyMeasurable (fun z : ℝ => CT.pcoef α z * A z)
      (volume.restrict Spaces.Iz) :=
    rb_aestronglyMeasurable_of_continuousOn_Ioi (hpc.continuousOn.mul hA.continuousOn)
  have hmeas : AEStronglyMeasurable (fun z =>
      (CT.DzRIter j (fun t => CT.pcoef α t * A t) z) ^ 2 * (Spaces.w z) ^ 2)
      (volume.restrict Spaces.Iz) :=
    ((rb_AEStronglyMeasurable_DzRIter j hPA_meas).pow 2).mul
      ((rb_measurable_w.aestronglyMeasurable).pow 2)
  -- ## The Leibniz expansion on `(0,∞)`
  have hleib : ∀ z : ℝ, 0 < z → CT.DzRIter j (fun t => CT.pcoef α t * A t) z
      = ∑ k ∈ Finset.range (j + 1),
          (j.choose k : ℝ) * CT.DzRIter k (CT.pcoef α) z * CT.DzRIter (j - k) A z :=
    fun z hz => DzRIter_mul j (CT.pcoef α) A hpc hA z hz
  -- ## The pointwise bound on `(0,∞)`
  have hterm : ∀ (z : ℝ), 0 < z → ∀ k ∈ Finset.range (j + 1),
      ((j.choose k : ℝ) * CT.DzRIter k (CT.pcoef α) z * CT.DzRIter (j - k) A z) ^ 2
          * (Spaces.w z) ^ 2
        ≤ M ^ 2 * ((j.choose k : ℝ) ^ 2 * ((CT.DzRIter (j - k) A z) ^ 2
            * (Spaces.w z) ^ 2)) := by
    intro z hz k hk
    have hwz : 0 < Spaces.w z := by unfold Spaces.w; positivity
    have hw1 : (1 / z ^ 2 : ℝ) ≤ (Spaces.w z) ^ 2 := rb_inv_sq_le_w_sq hz
    have hk' : k ≤ n := by
      have : k < j + 1 := Finset.mem_range.mp hk
      omega
    have hkb := hMp k hk' z hz
    have hsq : (CT.DzRIter k (CT.pcoef α) z) ^ 2 * (Spaces.w z) ^ 2 ≤ (M / z) ^ 2 := by
      have h := pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (le_of_lt hwz)) hkb 2
      rwa [mul_pow, sq_abs] at h
    calc ((j.choose k : ℝ) * CT.DzRIter k (CT.pcoef α) z * CT.DzRIter (j - k) A z) ^ 2
          * (Spaces.w z) ^ 2
        = (j.choose k : ℝ) ^ 2 * ((CT.DzRIter k (CT.pcoef α) z) ^ 2 * (Spaces.w z) ^ 2)
            * (CT.DzRIter (j - k) A z) ^ 2 := by ring
      _ ≤ (j.choose k : ℝ) ^ 2 * ((M / z) ^ 2) * (CT.DzRIter (j - k) A z) ^ 2 := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (sq_nonneg _))
            (sq_nonneg _)
      _ = M ^ 2 * ((j.choose k : ℝ) ^ 2 * ((CT.DzRIter (j - k) A z) ^ 2
            * (1 / z ^ 2))) := by ring
      _ ≤ M ^ 2 * ((j.choose k : ℝ) ^ 2 * ((CT.DzRIter (j - k) A z) ^ 2
            * (Spaces.w z) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg M)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw1 (sq_nonneg _))
            (sq_nonneg _)
  have hpt : ∀ z : ℝ, 0 < z →
      (CT.DzRIter j (fun t => CT.pcoef α t * A t) z) ^ 2 * (Spaces.w z) ^ 2
        ≤ ((j : ℝ) + 1) * (M ^ 2 * ∑ k ∈ Finset.range (j + 1),
            (j.choose k : ℝ) ^ 2 * ((CT.DzRIter (j - k) A z) ^ 2 * (Spaces.w z) ^ 2)) := by
    intro z hz
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
      (f := fun k => (j.choose k : ℝ) * CT.DzRIter k (CT.pcoef α) z * CT.DzRIter (j - k) A z)
    have hcard : ((Finset.range (j + 1)).card : ℝ) = (j : ℝ) + 1 := by simp
    rw [hcard] at hcs
    rw [hleib z hz]
    calc ((∑ k ∈ Finset.range (j + 1),
            (j.choose k : ℝ) * CT.DzRIter k (CT.pcoef α) z * CT.DzRIter (j - k) A z)) ^ 2
            * (Spaces.w z) ^ 2
          ≤ (((j : ℝ) + 1) * ∑ k ∈ Finset.range (j + 1),
              ((j.choose k : ℝ) * CT.DzRIter k (CT.pcoef α) z * CT.DzRIter (j - k) A z) ^ 2)
              * (Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hcs (sq_nonneg _)
        _ = ((j : ℝ) + 1) * (∑ k ∈ Finset.range (j + 1),
              ((j.choose k : ℝ) * CT.DzRIter k (CT.pcoef α) z * CT.DzRIter (j - k) A z) ^ 2
                * (Spaces.w z) ^ 2) := by
            rw [← Finset.sum_mul]
            ring
        _ ≤ ((j : ℝ) + 1) * (M ^ 2 * ∑ k ∈ Finset.range (j + 1),
              (j.choose k : ℝ) ^ 2 * ((CT.DzRIter (j - k) A z) ^ 2 * (Spaces.w z) ^ 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [Finset.mul_sum]
            exact Finset.sum_le_sum (hterm z hz)
  -- ## Integrability of the majorant
  have hIntInner : IntegrableOn (fun z => M ^ 2 * ∑ k ∈ Finset.range (j + 1),
      (j.choose k : ℝ) ^ 2 * ((CT.DzRIter (j - k) A z) ^ 2 * (Spaces.w z) ^ 2)) Spaces.Iz := by
    rw [IntegrableOn]
    refine (integrable_finsetSum _ (fun k hk => ?_)).const_mul (M ^ 2)
    have hk' : j - k ≤ n := by
      have : k < j + 1 := Finset.mem_range.mp hk
      omega
    exact ((hBnd (j - k) hk').1).const_mul ((j.choose k : ℝ) ^ 2)
  have hIntMajor : IntegrableOn (fun z => ((j : ℝ) + 1) * (M ^ 2 * ∑ k ∈ Finset.range (j + 1),
      (j.choose k : ℝ) ^ 2 * ((CT.DzRIter (j - k) A z) ^ 2 * (Spaces.w z) ^ 2))) Spaces.Iz :=
    hIntInner.const_mul _
  constructor
  · rw [IntegrableOn] at hIntMajor ⊢
    refine hIntMajor.mono' hmeas ?_
    filter_upwards [rb_ae_pos_of_Iz_radial] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hpt z hz
  · have hle : ∀ᵐ z ∂(volume.restrict Spaces.Iz),
        (CT.DzRIter j (fun t => CT.pcoef α t * A t) z) ^ 2 * (Spaces.w z) ^ 2
          ≤ ((j : ℝ) + 1) * (M ^ 2 * ∑ k ∈ Finset.range (j + 1),
              (j.choose k : ℝ) ^ 2 * ((CT.DzRIter (j - k) A z) ^ 2 * (Spaces.w z) ^ 2)) := by
      filter_upwards [rb_ae_pos_of_Iz_radial] with z hz
      exact hpt z hz
    have hmono := integral_mono_of_nonneg
      (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hIntMajor hle
    -- ## The integral of the majorant
    have hsplit : (∫ z in Spaces.Iz, ((j : ℝ) + 1) * (M ^ 2 * ∑ k ∈ Finset.range (j + 1),
          (j.choose k : ℝ) ^ 2 * ((CT.DzRIter (j - k) A z) ^ 2 * (Spaces.w z) ^ 2)))
        = ((j : ℝ) + 1) * (M ^ 2 * ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) ^ 2 *
            (∫ z in Spaces.Iz, (CT.DzRIter (j - k) A z) ^ 2 * (Spaces.w z) ^ 2)) := by
      have hInt : ∀ k ∈ Finset.range (j + 1), Integrable (fun z => (j.choose k : ℝ) ^ 2 *
          ((CT.DzRIter (j - k) A z) ^ 2 * (Spaces.w z) ^ 2)) (volume.restrict Spaces.Iz) := by
        intro k hk
        have hk' : j - k ≤ n := by
          have : k < j + 1 := Finset.mem_range.mp hk
          omega
        exact ((hBnd (j - k) hk').1).const_mul ((j.choose k : ℝ) ^ 2)
      have hsum := MeasureTheory.integral_finsetSum (μ := volume.restrict Spaces.Iz)
        (s := Finset.range (j + 1)) (f := fun k (z : ℝ) => (j.choose k : ℝ) ^ 2 *
          ((CT.DzRIter (j - k) A z) ^ 2 * (Spaces.w z) ^ 2)) hInt
      calc (∫ z in Spaces.Iz, ((j : ℝ) + 1) * (M ^ 2 * ∑ k ∈ Finset.range (j + 1),
            (j.choose k : ℝ) ^ 2 * ((CT.DzRIter (j - k) A z) ^ 2 * (Spaces.w z) ^ 2)))
          = ((j : ℝ) + 1) * (M ^ 2 * ∫ z in Spaces.Iz, ∑ k ∈ Finset.range (j + 1),
              (j.choose k : ℝ) ^ 2 * ((CT.DzRIter (j - k) A z) ^ 2
                * (Spaces.w z) ^ 2)) := by
            rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
        _ = ((j : ℝ) + 1) * (M ^ 2 * ∑ k ∈ Finset.range (j + 1),
              (∫ z in Spaces.Iz, (j.choose k : ℝ) ^ 2 * ((CT.DzRIter (j - k) A z) ^ 2
                * (Spaces.w z) ^ 2))) := by
            rw [hsum]
        _ = ((j : ℝ) + 1) * (M ^ 2 * ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) ^ 2 *
              (∫ z in Spaces.Iz, (CT.DzRIter (j - k) A z) ^ 2 * (Spaces.w z) ^ 2)) := by
            congr 2
            refine Finset.sum_congr rfl (fun k hk => ?_)
            rw [MeasureTheory.integral_const_mul]
    have hInts : (∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) ^ 2 *
          (∫ z in Spaces.Iz, (CT.DzRIter (j - k) A z) ^ 2 * (Spaces.w z) ^ 2))
        ≤ (∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) ^ 2) * H := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun k hk => ?_)
      have hk' : j - k ≤ n := by
        have : k < j + 1 := Finset.mem_range.mp hk
        omega
      exact mul_le_mul_of_nonneg_left ((hBnd (j - k) hk').2) (sq_nonneg _)
    have hSnn : (0 : ℝ) ≤ ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) ^ 2 :=
      Finset.sum_nonneg (fun k _ => sq_nonneg _)
    have hP : (0 : ℝ) ≤ ((2 : ℝ) ^ n) ^ 2 := by positivity
    have hmain : (∫ z in Spaces.Iz, ((j : ℝ) + 1) * (M ^ 2 * ∑ k ∈ Finset.range (j + 1),
          (j.choose k : ℝ) ^ 2 * ((CT.DzRIter (j - k) A z) ^ 2 * (Spaces.w z) ^ 2)))
        ≤ ((j : ℝ) + 1) * M ^ 2 * ((∑ k ∈ Finset.range (j + 1),
            (j.choose k : ℝ) ^ 2) * H) := by
      rw [hsplit]
      refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hInts
        (sq_nonneg M)) (by positivity)) (le_of_eq ?_)
      ring
    have hfinal : ((j : ℝ) + 1) * M ^ 2 * ((∑ k ∈ Finset.range (j + 1),
          (j.choose k : ℝ) ^ 2) * H)
        ≤ 2 * ((n : ℝ) + 1) * M ^ 2 * ((2 : ℝ) ^ n) ^ 2 * H := by
      have hjn : (j : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1) := by
        have h : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
        linarith
      have hS := rb_sum_choose_sq_le j n hj
      calc ((j : ℝ) + 1) * M ^ 2 * ((∑ k ∈ Finset.range (j + 1),
            (j.choose k : ℝ) ^ 2) * H)
          ≤ ((j : ℝ) + 1) * M ^ 2 * (((2 : ℝ) ^ n) ^ 2 * H) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hS hHnn) ?_
            positivity
        _ = ((j : ℝ) + 1) * M ^ 2 * ((2 : ℝ) ^ n) ^ 2 * H := by ring
        _ ≤ (2 * ((n : ℝ) + 1)) * M ^ 2 * ((2 : ℝ) ^ n) ^ 2 * H := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hjn (sq_nonneg M)) hP) hHnn
        _ = 2 * ((n : ℝ) + 1) * M ^ 2 * ((2 : ℝ) ^ n) ^ 2 * H := by ring
    linarith [hmono, hmain, hfinal]

/-! ## The Hardy bound and the integrability of `(L₁₂ g)² w²` -/

theorem rb_L12f_sq_w_sq_data (g : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd g)
    (hint : IntegrableOn (FM.L12dens Spaces.K g) (Set.Ioi 0))
    (h0 : L12f g 0 = 0)
    (hQ : IntegrableOn (fun z => (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) ^ 2
      * (Spaces.w z) ^ 2) (Set.Ioi 0)) :
    IntegrableOn (fun z => (L12f g z) ^ 2 * (Spaces.w z) ^ 2) Spaces.Iz
      ∧ ∫ z in Spaces.Iz, (L12f g z) ^ 2 * (Spaces.w z) ^ 2
        ≤ 107 * ∫ z in Set.Ioi 0, (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) ^ 2
            * (Spaces.w z) ^ 2 := by
  set Q : ℝ → ℝ := fun z => ∫ θ in Spaces.Iθ, Spaces.K θ * g z θ with hQdef
  have hdens : ∀ z : ℝ, z ≠ 0 → FM.L12dens Spaces.K g z = Q z / z := by
    intro z hz
    rw [FM.L12dens_eq (K := Spaces.K) (f := g) (s := z) hz]
    rfl
  have hderiv : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (L12f g) (-(Q z / z)) z := by
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    have hc : ContinuousAt (FM.L12dens Spaces.K g) z := L12dens_continuousAt_K g hsm z hz
    have hh := Work.FM.hasDerivAt_L12 (K := Spaces.K) (f := g) (a := 0) (ρ := z) hint hc hz
    rw [hdens z hz0] at hh
    exact hh
  have hdensE : Work.Elliptic.L12dens g = FM.L12dens Spaces.K g := by
    funext z
    simp only [Work.Elliptic.L12dens, Work.FM.L12dens, Work.Elliptic.Ktheta_eq_K, Spaces.Iθ]
  have hLEq : (fun z => Work.Elliptic.L12 g z) = L12f g := by
    funext z
    rw [Work.Elliptic.L12_eq_FM, ← K_eq_Kpaper]
    rfl
  have h0E : Work.Elliptic.L12 g 0 = 0 := by
    rw [Work.Elliptic.L12_eq_FM, ← K_eq_Kpaper]
    exact h0
  have hintE : IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi 0) := hdensE ▸ hint
  obtain ⟨_hval, hdecay, hcontIcc⟩ := Work.Elliptic.L12_values g hintE h0E
  have hcontU : ContinuousOn (L12f g) (Set.Icc 0 1) := hLEq ▸ hcontIcc
  have htendU : Tendsto (L12f g) atTop (𝓝 0) := hLEq ▸ hdecay
  have hQ1 : IntegrableOn (fun z => Q z ^ 2 * (Spaces.w z) ^ 2) (Set.Ioo 0 1) :=
    hQ.mono_set Set.Ioo_subset_Ioi_self
  have hQ2 : IntegrableOn (fun z => Q z ^ 2 * (Spaces.w z) ^ 2) (Set.Ioi 1) :=
    hQ.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  obtain ⟨hLWint, hLWle⟩ := Work.Elliptic.HardyLeftW Q (L12f g)
    (fun z hz => hderiv z (Set.mem_Ioi.mpr hz.1)) hcontU h0 hQ1
  obtain ⟨hRWint, hRWle⟩ := Work.Elliptic.HardyRightW Q (L12f g)
    (fun z hz => hderiv z (Set.mem_Ioi.mpr (lt_trans zero_lt_one hz))) htendU hQ2
  have hIci1_U : IntegrableOn (fun z => (L12f g z) ^ 2 * (Spaces.w z) ^ 2) (Set.Ici (1 : ℝ)) :=
    hRWint.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici (a := (1 : ℝ))).symm
  have hIci1_A : IntegrableOn (fun z => Q z ^ 2 * (Spaces.w z) ^ 2) (Set.Ici (1 : ℝ)) :=
    hQ2.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici (a := (1 : ℝ))).symm
  have hone : Set.Ioo (0 : ℝ) 1 ∪ Set.Ici 1 = Set.Ioi 0 := by
    ext z; constructor
    · rintro (hz | hz)
      · exact hz.1
      · exact lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp hz)
    · intro hz
      rcases lt_or_ge z 1 with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr h
  have hdisj : Disjoint (Set.Ioo (0 : ℝ) 1) (Set.Ici 1) :=
    Set.disjoint_left.mpr (fun z hz1 hz2 => (not_lt.mpr hz2) hz1.2)
  have hUdecomp : (∫ z in Set.Ioi (0 : ℝ), (L12f g z) ^ 2 * (Spaces.w z) ^ 2)
      = (∫ z in Set.Ioo (0 : ℝ) 1, (L12f g z) ^ 2 * (Spaces.w z) ^ 2)
        + (∫ z in Set.Ici (1 : ℝ), (L12f g z) ^ 2 * (Spaces.w z) ^ 2) := by
    rw [← hone]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ici hLWint hIci1_U
  have hUdecomp' : (∫ z in Set.Ici (1 : ℝ), (L12f g z) ^ 2 * (Spaces.w z) ^ 2)
      = ∫ z in Set.Ioi (1 : ℝ), (L12f g z) ^ 2 * (Spaces.w z) ^ 2 :=
    MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (1 : ℝ))).symm
  have hAdecomp : (∫ z in Set.Ioi (0 : ℝ), Q z ^ 2 * (Spaces.w z) ^ 2)
      = (∫ z in Set.Ioo (0 : ℝ) 1, Q z ^ 2 * (Spaces.w z) ^ 2)
        + (∫ z in Set.Ici (1 : ℝ), Q z ^ 2 * (Spaces.w z) ^ 2) := by
    rw [← hone]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ici hQ1 hIci1_A
  have hAdecomp' : (∫ z in Set.Ici (1 : ℝ), Q z ^ 2 * (Spaces.w z) ^ 2)
      = ∫ z in Set.Ioi (1 : ℝ), Q z ^ 2 * (Spaces.w z) ^ 2 :=
    MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (1 : ℝ))).symm
  have hIzU : (∫ z in Spaces.Iz, (L12f g z) ^ 2 * (Spaces.w z) ^ 2)
      = ∫ z in Set.Ioi (0 : ℝ), (L12f g z) ^ 2 * (Spaces.w z) ^ 2 :=
    MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm
  have hIzA : (∫ z in Spaces.Iz, Q z ^ 2 * (Spaces.w z) ^ 2)
      = ∫ z in Set.Ioi (0 : ℝ), Q z ^ 2 * (Spaces.w z) ^ 2 :=
    MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm
  have hover : IntegrableOn (fun z => (L12f g z) ^ 2 * (Spaces.w z) ^ 2) (Set.Ioi 0) := by
    rw [← hone]
    exact hLWint.union hIci1_U
  have hLWle' : (∫ z in Set.Ioo (0 : ℝ) 1, (L12f g z) ^ 2 * (Spaces.w z) ^ 2)
      ≤ 107 * ∫ z in Set.Ioo (0 : ℝ) 1,
          (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) ^ 2 * (Spaces.w z) ^ 2 := by
    simpa only [hQdef] using hLWle
  have hRWle' : (∫ z in Set.Ioi (1 : ℝ), (L12f g z) ^ 2 * (Spaces.w z) ^ 2)
      ≤ 107 * ∫ z in Set.Ioi (1 : ℝ),
          (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) ^ 2 * (Spaces.w z) ^ 2 := by
    simpa only [hQdef] using hRWle
  have hAdecomp'' : (∫ z in Set.Ioi (0 : ℝ),
        (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) ^ 2 * (Spaces.w z) ^ 2)
      = (∫ z in Set.Ioo (0 : ℝ) 1,
          (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) ^ 2 * (Spaces.w z) ^ 2)
        + (∫ z in Set.Ici (1 : ℝ),
          (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) ^ 2 * (Spaces.w z) ^ 2) := by
    simpa only [hQdef] using hAdecomp
  have hAdecomp''' : (∫ z in Set.Ici (1 : ℝ),
        (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) ^ 2 * (Spaces.w z) ^ 2)
      = ∫ z in Set.Ioi (1 : ℝ),
          (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) ^ 2 * (Spaces.w z) ^ 2 := by
    simpa only [hQdef] using hAdecomp'
  refine ⟨?_, ?_⟩
  · rw [show Spaces.Iz = Set.Ici (0 : ℝ) from rfl, IntegrableOn,
      ← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    rw [IntegrableOn] at hover
    exact hover
  · rw [hIzU, hUdecomp, hUdecomp', hAdecomp'', hAdecomp''']
    calc (∫ z in Set.Ioo (0 : ℝ) 1, (L12f g z) ^ 2 * (Spaces.w z) ^ 2)
          + (∫ z in Set.Ioi (1 : ℝ), (L12f g z) ^ 2 * (Spaces.w z) ^ 2)
        ≤ 107 * (∫ z in Set.Ioo (0 : ℝ) 1,
            (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) ^ 2 * (Spaces.w z) ^ 2)
          + 107 * (∫ z in Set.Ioi (1 : ℝ),
            (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) ^ 2 * (Spaces.w z) ^ 2) :=
          add_le_add hLWle' hRWle'
      _ = 107 * ((∫ z in Set.Ioo (0 : ℝ) 1,
            (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) ^ 2 * (Spaces.w z) ^ 2)
          + (∫ z in Set.Ioi (1 : ℝ),
            (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) ^ 2 * (Spaces.w z) ^ 2)) := by ring

/-! ## The core radial estimate for `L₁₂ g` -/

/-- The squared `K`-moment of the `θ`-slice of `g` at `z` is at most `3 ∫_θ g²`. -/
theorem rb_Qang_sq_le_three (g : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd g) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) ^ 2
      ≤ 3 * ∫ θ in Spaces.Iθ, (g z θ) ^ 2 := by
  have h1 := Work.Elliptic.Qang_sq_le g hsm 0 (z := z) (by linarith)
  rw [DzRIter_L12f_bridge_Qang g 0 z] at h1
  have hK : (∫ θ in Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) ≤ 3 := by
    rw [Work.Elliptic.Ktheta_eq_K]
    exact DzRIter_L12f_integral_K_sq_le_three
  refine le_trans h1 ?_
  simp only [Spaces.DzIter_zero]
  exact mul_le_mul_of_nonneg_right hK (integral_nonneg fun θ => sq_nonneg _)

theorem rb_L12f_per_m_bound (n : ℕ) (hn : 1 ≤ n) (g : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd g)
    (hint : IntegrableOn (FM.L12dens Spaces.K g) (Set.Ioi 0))
    (h0 : L12f g 0 = 0)
    (hQ : IntegrableOn (fun z => (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) ^ 2
      * (Spaces.w z) ^ 2) (Set.Ioi 0))
    (ρ : ℝ → ℝ → ℝ)
    (hρnn : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2), (Spaces.w z) ^ 2 ≤ ρ z θ)
    (hρslice : ∀ p : ℕ, p + 1 ≤ n → ∀ z : ℝ, 0 < z →
        IntegrableOn (fun θ => (Spaces.DzIter p g z θ) ^ 2 * ρ z θ) Spaces.Iθ)
    (hρint : ∀ p : ℕ, p + 1 ≤ n → IntegrableOn
        (fun z => ∫ θ in Spaces.Iθ, (Spaces.DzIter p g z θ) ^ 2 * ρ z θ) Spaces.Iz)
    (H : ℝ) (hH : 0 ≤ H)
    (hρbd : ∀ p : ℕ, p + 1 ≤ n →
        (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, (Spaces.DzIter p g z θ) ^ 2 * ρ z θ) ≤ H) :
    ∀ j ≤ n, IntegrableOn (fun z => (CT.DzRIter j (L12f g) z) ^ 2 * (Spaces.w z) ^ 2) Spaces.Iz
      ∧ ∫ z in Spaces.Iz, (CT.DzRIter j (L12f g) z) ^ 2 * (Spaces.w z) ^ 2 ≤ 321 * H := by
  have hcont : ∀ z : ℝ, 0 < z → ContinuousAt (FM.L12dens Spaces.K g) z :=
    L12dens_continuousAt_K g hsm
  have hAmeas : AEStronglyMeasurable (L12f g) (volume.restrict Spaces.Iz) :=
    rb_aestronglyMeasurable_of_continuousOn_Ioi (L12f_contDiffOn g hsm hint).continuousOn
  have hwmeas : AEStronglyMeasurable (fun z : ℝ => (Spaces.w z) ^ 2) (volume.restrict Spaces.Iz) :=
    ((rb_measurable_w.aestronglyMeasurable).pow 2)
  -- ## the comparison `∫_θ (D_z^p g)² w² ≤ ∫_θ (D_z^p g)² ρ` on a slice
  have hslice : ∀ p : ℕ, p + 1 ≤ n → ∀ z : ℝ, 0 < z →
      (∫ θ in Spaces.Iθ, (Spaces.DzIter p g z θ) ^ 2 * (Spaces.w z) ^ 2)
        ≤ ∫ θ in Spaces.Iθ, (Spaces.DzIter p g z θ) ^ 2 * ρ z θ := by
    intro p hp z hz
    refine integral_mono_of_nonneg (Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (hρslice p hp z hz) ?_
    filter_upwards [Work.Elliptic.ae_restrict_Iθ_of_Ioo (p := fun θ =>
      (Spaces.DzIter p g z θ) ^ 2 * (Spaces.w z) ^ 2 ≤ (Spaces.DzIter p g z θ) ^ 2 * ρ z θ)
      (by intro θ hθ0 hθ1
          exact mul_le_mul_of_nonneg_left (hρnn z (Set.mem_Ici.mpr (le_of_lt hz)) θ ⟨hθ0, hθ1⟩)
            (sq_nonneg _))] with θ hθ
    exact hθ
  -- ## the moment bound
  have hQbound : (∫ z in Set.Ioi 0, (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) ^ 2
      * (Spaces.w z) ^ 2) ≤ 3 * H := by
    have hpoint : ∀ z ∈ Set.Ioi (0 : ℝ),
        (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) ^ 2 * (Spaces.w z) ^ 2
          ≤ 3 * ∫ θ in Spaces.Iθ, (g z θ) ^ 2 * ρ z θ := by
      intro z hz
      have hCs := rb_Qang_sq_le_three g hsm hz
      calc (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) ^ 2 * (Spaces.w z) ^ 2
          ≤ (3 * ∫ θ in Spaces.Iθ, (g z θ) ^ 2) * (Spaces.w z) ^ 2 :=
            mul_le_mul_of_nonneg_right hCs (sq_nonneg _)
        _ = 3 * ∫ θ in Spaces.Iθ, (g z θ) ^ 2 * (Spaces.w z) ^ 2 := by
            rw [mul_assoc, MeasureTheory.integral_mul_const]
        _ ≤ 3 * ∫ θ in Spaces.Iθ, (g z θ) ^ 2 * ρ z θ := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            simpa only [Spaces.DzIter_zero] using hslice 0 hn z hz
    have hIntR : IntegrableOn (fun z => 3 * ∫ θ in Spaces.Iθ, (g z θ) ^ 2 * ρ z θ)
        (Set.Ioi (0 : ℝ)) :=
      ((hρint 0 hn).mono_set Set.Ioi_subset_Ici_self).const_mul 3
    have hmono : (∫ z in Set.Ioi (0 : ℝ), (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) ^ 2
          * (Spaces.w z) ^ 2)
        ≤ ∫ z in Set.Ioi (0 : ℝ), 3 * ∫ θ in Spaces.Iθ, (g z θ) ^ 2 * ρ z θ := by
      refine integral_mono_of_nonneg
        (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hIntR ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
      exact hpoint z hz
    have hEq : (∫ z in Set.Ioi (0 : ℝ), 3 * ∫ θ in Spaces.Iθ, (g z θ) ^ 2 * ρ z θ)
        = 3 * ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, (g z θ) ^ 2 * ρ z θ := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      exact MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))
    have hbd : (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, (g z θ) ^ 2 * ρ z θ) ≤ H := by
      simpa only [Spaces.DzIter_zero] using hρbd 0 hn
    calc (∫ z in Set.Ioi (0 : ℝ), (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) ^ 2
          * (Spaces.w z) ^ 2)
        ≤ ∫ z in Set.Ioi (0 : ℝ), 3 * ∫ θ in Spaces.Iθ, (g z θ) ^ 2 * ρ z θ := hmono
      _ = 3 * ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, (g z θ) ^ 2 * ρ z θ := hEq
      _ ≤ 3 * H := by linarith
  intro j hj
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    have hdata := rb_L12f_sq_w_sq_data g hsm hint h0 hQ
    simp only [CT.DzRIter_zero]
    refine ⟨hdata.1, ?_⟩
    linarith [hdata.2, hQbound]
  · have hm1 : 1 ≤ j := hjpos
    have hj' : j - 1 + 1 ≤ n := by omega
    have hstep : ∀ z : ℝ, 0 < z → (CT.DzRIter j (L12f g) z) ^ 2
        ≤ 3 * ∫ θ in Spaces.Iθ, (Spaces.DzIter (j - 1) g z θ) ^ 2 :=
      (DzRIter_L12f g hsm hint hcont j hm1).2
    have hpt : ∀ z : ℝ, 0 < z → (CT.DzRIter j (L12f g) z) ^ 2 * (Spaces.w z) ^ 2
        ≤ 3 * ∫ θ in Spaces.Iθ, (Spaces.DzIter (j - 1) g z θ) ^ 2 * ρ z θ := by
      intro z hz
      calc (CT.DzRIter j (L12f g) z) ^ 2 * (Spaces.w z) ^ 2
          ≤ (3 * ∫ θ in Spaces.Iθ, (Spaces.DzIter (j - 1) g z θ) ^ 2) * (Spaces.w z) ^ 2 :=
            mul_le_mul_of_nonneg_right (hstep z hz) (sq_nonneg _)
        _ = 3 * ∫ θ in Spaces.Iθ, (Spaces.DzIter (j - 1) g z θ) ^ 2 * (Spaces.w z) ^ 2 := by
            rw [mul_assoc, MeasureTheory.integral_mul_const]
        _ ≤ 3 * ∫ θ in Spaces.Iθ, (Spaces.DzIter (j - 1) g z θ) ^ 2 * ρ z θ :=
            mul_le_mul_of_nonneg_left (hslice (j - 1) hj' z hz) (by norm_num)
    have hIntR : IntegrableOn (fun z => 3 * ∫ θ in Spaces.Iθ,
        (Spaces.DzIter (j - 1) g z θ) ^ 2 * ρ z θ) Spaces.Iz := (hρint (j - 1) hj').const_mul 3
    refine ⟨?_, ?_⟩
    · rw [IntegrableOn] at hIntR ⊢
      refine hIntR.mono' (((rb_AEStronglyMeasurable_DzRIter j hAmeas).pow 2).mul
        (hwmeas)) ?_
      filter_upwards [rb_ae_pos_of_Iz_radial] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact hpt z hz
    · have hle : ∀ᵐ z ∂(volume.restrict Spaces.Iz),
          (CT.DzRIter j (L12f g) z) ^ 2 * (Spaces.w z) ^ 2
            ≤ 3 * ∫ θ in Spaces.Iθ, (Spaces.DzIter (j - 1) g z θ) ^ 2 * ρ z θ := by
        filter_upwards [rb_ae_pos_of_Iz_radial] with z hz
        exact hpt z hz
      have hmono := integral_mono_of_nonneg
        (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hIntR hle
      have hbd := hρbd (j - 1) hj'
      rw [MeasureTheory.integral_const_mul] at hmono
      linarith [hmono, hbd, hH]

/-! ## The weight identities for `Wt` and the pointwise domination of `D_θ f` -/

theorem rb_rpow_neg_half_sq {x γ : ℝ} (hx : 0 ≤ x) : (x ^ (-(γ / 2))) ^ 2 = x ^ (-γ) := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h
    by_cases hγ : γ = 0
    · subst hγ; norm_num
    · rw [Real.zero_rpow (by simp [hγ]), Real.zero_rpow (by simp [hγ])]
      norm_num
  · rw [sq, ← Real.rpow_add h]
    congr 1
    ring

/-- `(x ^ (γ/2))² = x ^ γ` for `x ≥ 0`. -/
theorem rb_rpow_half_sq {x γ : ℝ} (hx : 0 ≤ x) : (x ^ (γ / 2)) ^ 2 = x ^ γ := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h
    by_cases hγ : γ = 0
    · subst hγ; norm_num
    · rw [Real.zero_rpow (by simp [hγ]), Real.zero_rpow (by simp [hγ])]
      norm_num
  · rw [sq, ← Real.rpow_add h]
    congr 1
    ring

/-- `Wt α z θ² = w z² · sin(2θ)^{-γ}` on the closed quadrant. -/
theorem rb_Wt_sq_eq (α z θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    (Spaces.Wt α z θ) ^ 2 = (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  unfold Spaces.Wt Spaces.wTheta
  rw [mul_pow, rb_rpow_neg_half_sq hs0]

/-- On the open quadrant, `w z ≤ Wt α z θ` for `α > 0`. -/
theorem rb_w_le_Wt (α : ℝ) (hα : 0 < α) {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Spaces.w z ≤ Spaces.Wt α z θ := by
  have hθI : θ ∈ Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hw : 0 ≤ Spaces.w z := by unfold Spaces.w; positivity
  have hgam : 0 < Spaces.gam α := by unfold Spaces.gam; linarith
  unfold Spaces.Wt Spaces.wTheta
  have h2 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2)) := by
    rw [Real.rpow_neg (le_of_lt hs0), inv_eq_one_div, one_le_div (Real.rpow_pos_of_pos hs0 _)]
    exact Real.rpow_le_one (le_of_lt hs0) hs1 (by linarith)
  calc Spaces.w z = Spaces.w z * 1 := by ring
    _ ≤ Spaces.w z * (Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2)) := mul_le_mul_of_nonneg_left h2 hw

/-- The pointwise domination of the mixed derivative `D_θ f = mixed 0 1 f` by the
`ℋ^n`-integrand. -/
theorem rb_sq_Dth_le_HkIntegrand (α : ℝ) (n : ℕ) {hn : 1 ≤ n} (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (Spaces.Dth f z θ * Spaces.Wt α z θ) ^ 2 ≤ Spaces.HkIntegrand α n f z θ := by
  have h := Spaces.sq_le_HkIntegrand_mixed α n f z θ 1 0 (le_refl 1) (by omega)
  rwa [Spaces.mixed_zero_left, Spaces.DthIter_succ, Spaces.DthIter_zero] at h

/-- The `θ`-slice integral of `(D_θ f)²` is bounded by the `ℋ^n`-integrand. -/
theorem rb_Dth_sq_slice_le (α : ℝ) (hα : 0 < α) (n : ℕ) (hn : 1 ≤ n) (f : ℝ → ℝ → ℝ)
    (hmem : Spaces.HkMem α n f) {s : ℝ} (hs : 0 < s) :
    ∫ θ in Spaces.Iθ, (Spaces.Dth f s θ) ^ 2
      ≤ (s ^ 4 / (1 + s) ^ 4) * ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f s θ := by
  have hw : 0 < Spaces.w s := by unfold Spaces.w; positivity
  have hpt : ∀ θ ∈ Set.Ioo 0 (π / 2), (Spaces.Dth f s θ) ^ 2
      ≤ Spaces.HkIntegrand α n f s θ / (Spaces.w s) ^ 2 := by
    intro θ hθ
    have hbound : (Spaces.Dth f s θ * Spaces.w s) ^ 2
        ≤ (Spaces.Dth f s θ * Spaces.Wt α s θ) ^ 2 := by
      have h2 := rb_w_le_Wt α hα hθ (z := s)
      have hWtnn : 0 ≤ Spaces.Wt α s θ := le_trans (le_of_lt hw) h2
      rw [mul_pow, mul_pow]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      rw [sq, sq]
      exact mul_le_mul h2 h2 (le_of_lt hw) hWtnn
    have h3 := rb_sq_Dth_le_HkIntegrand α n (hn := hn) f s θ
    rw [mul_pow] at hbound
    have h4 : (Spaces.Dth f s θ) ^ 2 * (Spaces.w s) ^ 2 ≤ Spaces.HkIntegrand α n f s θ :=
      le_trans hbound h3
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (Spaces.w s) ^ 2)]
    exact h4
  have hIntMajor : IntegrableOn (fun θ => Spaces.HkIntegrand α n f s θ / (Spaces.w s) ^ 2)
      Spaces.Iθ := (hmem.1 s hs.le).div_const _
  refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
    hIntMajor ?_) ?_
  · filter_upwards [Work.Elliptic.ae_restrict_Iθ_of_Ioo (fun θ h0 h1 => hpt θ ⟨h0, h1⟩)]
      with θ hθ
    exact hθ
  rw [MeasureTheory.integral_div]
  have hw2 : (Spaces.w s) ^ 2 = (1 + s) ^ 4 / s ^ 4 := by
    unfold Spaces.w
    rw [div_pow]
    ring
  rw [hw2]
  refine le_of_eq ?_
  rw [div_eq_mul_inv, inv_div]
  ring

/-! ## Integrability of the `D_θ f`-density -/

theorem rb_L12dens_Dth_integrableOn (α : ℝ) (hα : 0 < α) (n : ℕ) (hn : 1 ≤ n) (f : ℝ → ℝ → ℝ)
    (hf : Spaces.SmoothNbhd f) (hmem : Spaces.HkMem α n f) :
    IntegrableOn (FM.L12dens Spaces.K (Spaces.Dth f)) (Set.Ioi 0) := by
  have hslice : ∀ s : ℝ, 0 < s → (∫ θ in Spaces.Iθ, (Spaces.Dth f s θ) ^ 2)
      ≤ (s ^ 4 / (1 + s) ^ 4) * ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f s θ :=
    fun s hs => rb_Dth_sq_slice_le α hα n hn f hmem hs
  have hbound : ∀ s : ℝ, 0 < s → |FM.L12dens Spaces.K (Spaces.Dth f) s|
      ≤ (Real.sqrt 3 * (s / (1 + s) ^ 2))
        * Real.sqrt (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f s θ) := by
    intro s hs
    have hd : FM.L12dens Spaces.K (Spaces.Dth f) s
        = (∫ θ in Spaces.Iθ, Spaces.K θ * Spaces.Dth f s θ) / s := by
      rw [FM.L12dens_eq (ne_of_gt hs)]
      rfl
    rw [hd, abs_div, abs_of_pos hs]
    have h1 := rb_Qang_sq_le_three (Spaces.Dth f) (SmoothNbhd_Dth f hf) hs
    have h2 := hslice s hs
    have h3 : |∫ θ in Spaces.Iθ, Spaces.K θ * Spaces.Dth f s θ|
        ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Spaces.Iθ, (Spaces.Dth f s θ) ^ 2) := by
      have h := Real.sqrt_le_sqrt h1
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq_eq_abs] at h
      exact h
    have h4 : Real.sqrt (∫ θ in Spaces.Iθ, (Spaces.Dth f s θ) ^ 2)
        ≤ (s ^ 2 / (1 + s) ^ 2)
          * Real.sqrt (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f s θ) := by
      have h := Real.sqrt_le_sqrt h2
      have hs4 : s ^ 4 / (1 + s) ^ 4 = (s ^ 2 / (1 + s) ^ 2) ^ 2 := by
        field_simp
      rw [hs4, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 2 / (1 + s) ^ 2)] at h
      exact h
    calc |∫ θ in Spaces.Iθ, Spaces.K θ * Spaces.Dth f s θ| / s
        ≤ (Real.sqrt 3 * Real.sqrt (∫ θ in Spaces.Iθ, (Spaces.Dth f s θ) ^ 2)) / s := by
          rw [div_le_div_iff_of_pos_right hs]
          exact h3
      _ ≤ (Real.sqrt 3 * ((s ^ 2 / (1 + s) ^ 2)
            * Real.sqrt (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f s θ))) / s := by
          rw [div_le_div_iff_of_pos_right hs]
          exact mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
      _ = (Real.sqrt 3 * (s / (1 + s) ^ 2))
            * Real.sqrt (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f s θ) := by
          field_simp
          try ring
  have hH_int : IntegrableOn (fun s => ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f s θ)
      (Set.Ioi 0) := hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hdom : IntegrableOn (fun s => (Real.sqrt 3 / 2) * ((s / (1 + s) ^ 2) ^ 2
      + ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f s θ)) (Set.Ioi 0) :=
    (Work.Elliptic.psi_sq_integrable_aux.add hH_int).const_mul _
  have haesm : AEStronglyMeasurable (FM.L12dens Spaces.K (Spaces.Dth f))
      (volume.restrict (Set.Ioi 0)) := by
    rw [L12dens_eq_fm]
    exact (Work.Elliptic.L12dens_continuousOn_aux (Spaces.Dth f) (SmoothNbhd_Dth f hf)
      ).aestronglyMeasurable measurableSet_Ioi
  rw [IntegrableOn]
  refine hdom.mono' haesm ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  rw [Real.norm_eq_abs]
  have hHnn : 0 ≤ ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f s θ :=
    integral_nonneg fun θ => Spaces.HkIntegrand_nonneg α n f s θ
  have hAM : 2 * ((s / (1 + s) ^ 2) * Real.sqrt (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f s θ))
      ≤ (s / (1 + s) ^ 2) ^ 2 + ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f s θ := by
    nlinarith [sq_nonneg ((s / (1 + s) ^ 2)
        - Real.sqrt (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f s θ)),
      Real.sq_sqrt hHnn]
  calc |FM.L12dens Spaces.K (Spaces.Dth f) s|
      ≤ (Real.sqrt 3 * (s / (1 + s) ^ 2))
          * Real.sqrt (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f s θ) := hbound s hs
    _ = (Real.sqrt 3 / 2) * (2 * ((s / (1 + s) ^ 2)
          * Real.sqrt (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f s θ))) := by ring
    _ ≤ (Real.sqrt 3 / 2) * ((s / (1 + s) ^ 2) ^ 2
          + ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f s θ) :=
        mul_le_mul_of_nonneg_left hAM (by positivity)

/-! ## The squared angular moments -/

theorem rb_continuousOn_FM_L12dens_Dth (α : ℝ) (f : ℝ → ℝ → ℝ) (hf : Spaces.SmoothNbhd f) :
    ContinuousOn (FM.L12dens Spaces.K (Spaces.Dth f)) (Set.Ioi 0) := by
  rw [L12dens_eq_fm]
  exact Work.Elliptic.L12dens_continuousOn_aux (Spaces.Dth f) (SmoothNbhd_Dth f hf)

theorem rb_Qang_Dth_sq_int_le (α : ℝ) (hα : 0 < α) (n : ℕ) (hn : 1 ≤ n) (f : ℝ → ℝ → ℝ)
    (hf : Spaces.SmoothNbhd f) (hmem : Spaces.HkMem α n f) :
    IntegrableOn (fun z => (∫ θ in Spaces.Iθ, Spaces.K θ * Spaces.Dth f z θ) ^ 2
        * (Spaces.w z) ^ 2) (Set.Ioi 0)
      ∧ (∫ z in Set.Ioi 0, (∫ θ in Spaces.Iθ, Spaces.K θ * Spaces.Dth f z θ) ^ 2
        * (Spaces.w z) ^ 2) ≤ 3 * Spaces.HkSq α n f := by
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫ θ in Spaces.Iθ, Spaces.K θ * Spaces.Dth f z θ) ^ 2 * (Spaces.w z) ^ 2
        ≤ 3 * ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f z θ := by
    intro z hz
    have hzpos : (0 : ℝ) < z := hz
    have h1 := rb_Qang_sq_le_three (Spaces.Dth f) (SmoothNbhd_Dth f hf) hzpos
    have hw : (∫ θ in Spaces.Iθ, (Spaces.Dth f z θ) ^ 2) * (Spaces.w z) ^ 2
        ≤ ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f z θ := by
      rw [← MeasureTheory.integral_mul_const]
      refine integral_mono_of_nonneg
        (Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (hmem.1 z (le_of_lt hzpos)) ?_
      filter_upwards [Work.Elliptic.ae_restrict_Iθ_of_Ioo (p := fun θ =>
        (Spaces.Dth f z θ) ^ 2 * (Spaces.w z) ^ 2 ≤ Spaces.HkIntegrand α n f z θ) (by
        intro θ hθ0 hθ1
        have h2 := rb_w_le_Wt α hα ⟨hθ0, hθ1⟩ (z := z)
        have hwnn : (0 : ℝ) ≤ Spaces.w z := by unfold Spaces.w; positivity
        have hWtnn : 0 ≤ Spaces.Wt α z θ := le_trans hwnn h2
        have h3 := rb_sq_Dth_le_HkIntegrand α n (hn := hn) f z θ
        rw [mul_pow] at h3
        refine le_trans ?_ h3
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        rw [sq, sq]
        exact mul_le_mul h2 h2 hwnn hWtnn)] with θ hθ
      exact hθ
    calc (∫ θ in Spaces.Iθ, Spaces.K θ * Spaces.Dth f z θ) ^ 2 * (Spaces.w z) ^ 2
        ≤ (3 * ∫ θ in Spaces.Iθ, (Spaces.Dth f z θ) ^ 2) * (Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = 3 * ((∫ θ in Spaces.Iθ, (Spaces.Dth f z θ) ^ 2) * (Spaces.w z) ^ 2) := by ring
      _ ≤ 3 * ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f z θ :=
          mul_le_mul_of_nonneg_left hw (by norm_num)
  have haesm : AEStronglyMeasurable (fun z =>
      (∫ θ in Spaces.Iθ, Spaces.K θ * Spaces.Dth f z θ) ^ 2 * (Spaces.w z) ^ 2)
      (volume.restrict (Set.Ioi 0)) := by
    have hcont1 : ContinuousOn (fun z => z * FM.L12dens Spaces.K (Spaces.Dth f) z) (Set.Ioi 0) :=
      continuousOn_id.mul (rb_continuousOn_FM_L12dens_Dth α f hf)
    have hcont : ContinuousOn (fun z =>
        (z * FM.L12dens Spaces.K (Spaces.Dth f) z) ^ 2 * (Spaces.w z) ^ 2) (Set.Ioi 0) :=
      (hcont1.pow 2).mul (continuousOn_w.pow 2)
    refine (hcont.aestronglyMeasurable measurableSet_Ioi).congr ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    rw [integral_K_mul_eq_mul_L12dens (Spaces.Dth f) hz]
  have hIntMajor : IntegrableOn (fun z => 3 * ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f z θ)
      (Set.Ioi (0 : ℝ)) := (hmem.2.mono_set Set.Ioi_subset_Ici_self).const_mul 3
  refine ⟨?_, ?_⟩
  · rw [IntegrableOn]
    refine hIntMajor.mono' haesm ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hpt z hz
  · have hle : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        (∫ θ in Spaces.Iθ, Spaces.K θ * Spaces.Dth f z θ) ^ 2 * (Spaces.w z) ^ 2
          ≤ 3 * ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f z θ := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
      exact hpt z hz
    have hmono := integral_mono_of_nonneg
      (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hIntMajor hle
    have hEq : (∫ z in Set.Ioi (0 : ℝ), 3 * ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f z θ)
        = 3 * Spaces.HkSq α n f := by
      rw [MeasureTheory.integral_const_mul, Spaces.HkSq]
      congr 1
      exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))
    linarith [hmono, hEq.le]

theorem rb_Qang_f_sq_int_le (α : ℝ) (n : ℕ) (hn : 1 ≤ n) (f : ℝ → ℝ → ℝ)
    (hf : Spaces.SmoothNbhd f) (hmem : Spaces.HkMem α n f) :
    IntegrableOn (fun z => (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) ^ 2
        * (Spaces.w z) ^ 2) (Set.Ioi 0)
      ∧ (∫ z in Set.Ioi 0, (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) ^ 2
        * (Spaces.w z) ^ 2) ≤ 3 * Spaces.HkSq α n f := by
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) ^ 2 * (Spaces.w z) ^ 2
        ≤ 3 * ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f z θ := by
    intro z hz
    have hzpos : (0 : ℝ) < z := hz
    have h1 := rb_Qang_sq_le_three f hf hzpos
    have hw : (∫ θ in Spaces.Iθ, (f z θ) ^ 2) * (Spaces.w z) ^ 2
        ≤ ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f z θ := by
      rw [← MeasureTheory.integral_mul_const]
      refine integral_mono_of_nonneg
        (Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (hmem.1 z (le_of_lt hzpos)) ?_
      filter_upwards [Work.Elliptic.ae_restrict_Iθ_of_Ioo (p := fun θ =>
        (f z θ) ^ 2 * (Spaces.w z) ^ 2 ≤ Spaces.HkIntegrand α n f z θ) (by
        intro θ hθ0 hθ1
        have hsin : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
        have h3 := Spaces.sq_le_HkIntegrand_z α n f z θ 0 (Nat.zero_le n)
        simp only [Spaces.DzIter_zero] at h3
        -- h3 : (f z θ * (w z / sin^{η/2}))² ≤ HkIntegrand
        have hwnn : (0 : ℝ) ≤ Spaces.w z := by unfold Spaces.w; positivity
        have hle : (Spaces.w z) ^ 2 ≤ (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2)) ^ 2 := by
          rw [div_pow]
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((Real.sin (2 * θ)) ^ (Spaces.eta / 2)) ^ 2)]
          have h1' : (Real.sin (2 * θ)) ^ Spaces.eta ≤ 1 :=
            Real.rpow_le_one (le_of_lt hsin) (Real.sin_le_one _) (le_of_lt Spaces.eta_pos)
          have hsq : ((Real.sin (2 * θ)) ^ (Spaces.eta / 2)) ^ 2
              = (Real.sin (2 * θ)) ^ Spaces.eta := rb_rpow_half_sq (le_of_lt hsin)
          rw [hsq]
          calc (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ Spaces.eta
              ≤ (Spaces.w z) ^ 2 * 1 := mul_le_mul_of_nonneg_left h1' (sq_nonneg _)
            _ = (Spaces.w z) ^ 2 := by ring
        refine le_trans ?_ h3
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left hle (sq_nonneg _))] with θ hθ
      exact hθ
    calc (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) ^ 2 * (Spaces.w z) ^ 2
        ≤ (3 * ∫ θ in Spaces.Iθ, (f z θ) ^ 2) * (Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = 3 * ((∫ θ in Spaces.Iθ, (f z θ) ^ 2) * (Spaces.w z) ^ 2) := by ring
      _ ≤ 3 * ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f z θ :=
          mul_le_mul_of_nonneg_left hw (by norm_num)
  have haesm : AEStronglyMeasurable (fun z =>
      (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) ^ 2 * (Spaces.w z) ^ 2)
      (volume.restrict (Set.Ioi 0)) := by
    have hcontD : ContinuousOn (FM.L12dens Spaces.K f) (Set.Ioi 0) := by
      rw [L12dens_eq_fm]
      exact Work.Elliptic.L12dens_continuousOn_aux f hf
    have hcont1 : ContinuousOn (fun z => z * FM.L12dens Spaces.K f z) (Set.Ioi 0) :=
      continuousOn_id.mul hcontD
    have hcont : ContinuousOn (fun z =>
        (z * FM.L12dens Spaces.K f z) ^ 2 * (Spaces.w z) ^ 2) (Set.Ioi 0) :=
      (hcont1.pow 2).mul (continuousOn_w.pow 2)
    refine (hcont.aestronglyMeasurable measurableSet_Ioi).congr ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    rw [integral_K_mul_eq_mul_L12dens f hz]
  have hIntMajor : IntegrableOn (fun z => 3 * ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f z θ)
      (Set.Ioi (0 : ℝ)) := (hmem.2.mono_set Set.Ioi_subset_Ici_self).const_mul 3
  refine ⟨?_, ?_⟩
  · rw [IntegrableOn]
    refine hIntMajor.mono' haesm ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hpt z hz
  · have hle : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) ^ 2 * (Spaces.w z) ^ 2
          ≤ 3 * ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f z θ := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
      exact hpt z hz
    have hmono := integral_mono_of_nonneg
      (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hIntMajor hle
    have hEq : (∫ z in Set.Ioi (0 : ℝ), 3 * ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α n f z θ)
        = 3 * Spaces.HkSq α n f := by
      rw [MeasureTheory.integral_const_mul, Spaces.HkSq]
      congr 1
      exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))
    linarith [hmono, hEq.le]

/-- `mixed 0 1 f = D_θ f`. -/
theorem rb_mixed_zero_one_eq (f : ℝ → ℝ → ℝ) : Spaces.mixed 0 1 f = Spaces.Dth f := by
  simp only [Spaces.mixed, Spaces.DthIter_succ, Spaces.DthIter_zero, Spaces.DzIter_zero]

/-- `mixed j 1 f = D_z^j (D_θ f)`. -/
theorem rb_mixed_one_eq (j : ℕ) (f : ℝ → ℝ → ℝ) :
    Spaces.mixed j 1 f = Spaces.DzIter j (Spaces.Dth f) := by
  simp only [Spaces.mixed, Spaces.DthIter_succ, Spaces.DthIter_zero]

/-- `(a + b)² ≤ 2a² + 2b²`. -/
theorem rb_add_sq_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem radial_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ → ℝ), Work.Spaces.SmoothNbhd f → Work.Spaces.HkMem α n f →
      Work.Coercivity.CT.A1 f 0 = 0 → Work.Coercivity.CT.A2 f 0 = 0 →
      (∀ j ≤ n, MeasureTheory.IntegrableOn
          (fun z => (Work.Coercivity.CT.DzRIter j (Work.Coercivity.CT.F1 α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz
        ∧ ∫ z in Work.Spaces.Iz, (Work.Coercivity.CT.DzRIter j (Work.Coercivity.CT.F1 α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2 ≤ C * Work.Spaces.HkSq α n f)
      ∧ (∀ j ≤ n, MeasureTheory.IntegrableOn
          (fun z => (Work.Coercivity.CT.DzRIter j (Work.Coercivity.CT.F2 α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz
        ∧ ∫ z in Work.Spaces.Iz, (Work.Coercivity.CT.DzRIter j (Work.Coercivity.CT.F2 α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2 ≤ C * Work.Spaces.HkSq α n f) := by
  obtain ⟨Mp, hMp_pos, hMp⟩ := (radial_algebra α hα hα1 n).1
  obtain ⟨Mw, hMw_pos, hMw⟩ := (radial_algebra α hα hα1 n).2.1
  obtain ⟨CKC, hCKC_pos, hKC⟩ := KC_sq_le α hα hα1
  have hc : Spaces.c α ≠ 0 := c_ne_zero hα hα1
  have hpcC : ContDiffOn ℝ ⊤ (CT.pcoef α) (Set.Ioi 0) := pcoef_contDiffOn α hc
  have hWcC : ContDiffOn ℝ ⊤ (CT.Wcoef α) (Set.Ioi 0) := Wcoef_contDiffOn α hc
  refine ⟨4 * ((n : ℝ) + 1) * Mp ^ 2 * ((2 : ℝ) ^ n) ^ 2 * 321 + 4 * CKC * Mw ^ 2 + 1,
    by positivity, ?_⟩
  intro f hf hmem hA1 hA2
  have hint1 : IntegrableOn (FM.L12dens Spaces.K (Spaces.Dth f)) (Set.Ioi 0) :=
    rb_L12dens_Dth_integrableOn α hα n hn f hf hmem
  have hint2 : IntegrableOn (FM.L12dens Spaces.K f) (Set.Ioi 0) :=
    L12dens_integrableOn α n f hf hmem
  have hQ1 := rb_Qang_Dth_sq_int_le α hα n hn f hf hmem
  have hQ2 := rb_Qang_f_sq_int_le α n hn f hf hmem
  have hmt := HkMem_terms α n hn f hf hmem
  have hHnn : 0 ≤ Spaces.HkSq α n f := Spaces.HkSq_nonneg α n f
  have hFsm := F1F2_smooth α hα hα1 f hf hint1 hint2
  have hA1sm : ContDiffOn ℝ ⊤ (CT.A1 f) (Set.Ioi 0) :=
    L12f_contDiffOn (Spaces.Dth f) (SmoothNbhd_Dth f hf) hint1
  have hA2sm : ContDiffOn ℝ ⊤ (CT.A2 f) (Set.Ioi 0) := L12f_contDiffOn f hf hint2
  -- ## the energy of `D_θ f` dominates `Ewgam α (D_θ f)`
  have hEwgam_le : CT.Ewgam α (Spaces.Dth f) ≤ Spaces.HkSq α n f := by
    have h := Spaces.L2Sq_mixed_le_HkSq α n f hmem 1 0 (le_refl 1) (by omega)
    have hEq : Spaces.L2Sq (fun z θ => Spaces.mixed 0 1 f z θ * Spaces.Wt α z θ)
        = CT.Ewgam α (Spaces.Dth f) := by
      rw [Spaces.L2Sq, CT.Ewgam]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with z
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with θ hθ
      rw [mul_pow, rb_Wt_sq_eq α z θ hθ, rb_mixed_zero_one_eq f]
      ring
    rwa [hEq] at h
  have hKC : (CT.KC0 f) ^ 2 ≤ CKC * Spaces.HkSq α n f
      ∧ (CT.KC1 f) ^ 2 ≤ CKC * Spaces.HkSq α n f := by
    obtain ⟨h1, h2⟩ := hKC f hf (hmt.2.2.1 1 le_rfl 0 (by omega))
      (hmt.2.2.2 1 le_rfl 0 (by omega))
    refine ⟨?_, ?_⟩ <;> nlinarith [hCKC_pos]
  -- ## the per-iterate bounds for the two radial factors `A₁`, `A₂`
  have hper1 : ∀ m ≤ n, IntegrableOn (fun z => (CT.DzRIter m (CT.A1 f) z) ^ 2 * (Spaces.w z) ^ 2)
        Spaces.Iz
      ∧ ∫ z in Spaces.Iz, (CT.DzRIter m (CT.A1 f) z) ^ 2 * (Spaces.w z) ^ 2
          ≤ 321 * Spaces.HkSq α n f := by
    refine rb_L12f_per_m_bound n hn (Spaces.Dth f) (SmoothNbhd_Dth f hf) hint1 hA1 hQ1.1
      (fun z θ => (Spaces.Wt α z θ) ^ 2) ?_ ?_ ?_ (Spaces.HkSq α n f) hHnn ?_
    · intro z hz θ hθ
      have h1 := rb_w_le_Wt α hα hθ (z := z)
      have h2 : (0 : ℝ) ≤ Spaces.w z := by unfold Spaces.w; positivity
      rw [sq, sq]
      exact mul_le_mul h1 h1 h2 (le_trans h2 h1)
    · intro p hp z hz
      have hp1 : 1 + p ≤ n := by omega
      have h := hmt.2.2.1 1 le_rfl p hp1 z hz
      refine (h.const_mul ((Spaces.w z) ^ 2)).congr ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with θ hθ
      rw [rb_Wt_sq_eq α z θ hθ, rb_mixed_one_eq p f]
      ring
    · intro p hp
      have hp1 : 1 + p ≤ n := by omega
      have h := hmt.2.2.2 1 le_rfl p hp1
      refine h.congr ?_
      filter_upwards with z
      show (∫ θ in Spaces.Iθ, Spaces.mixed p 1 f z θ ^ 2 * (Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
          = ∫ θ in Spaces.Iθ, (Spaces.DzIter p (Spaces.Dth f) z θ) ^ 2
              * (Spaces.Wt α z θ) ^ 2
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with θ hθ
      rw [rb_Wt_sq_eq α z θ hθ, rb_mixed_one_eq p f]
      ring
    · intro p hp
      have hp1 : 1 + p ≤ n := by omega
      have h := Spaces.L2Sq_mixed_le_HkSq α n f hmem 1 p (le_refl 1) hp1
      have hEq : Spaces.L2Sq (fun z θ => Spaces.mixed p 1 f z θ * Spaces.Wt α z θ)
          = ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, (Spaces.DzIter p (Spaces.Dth f) z θ) ^ 2
              * (Spaces.Wt α z θ) ^ 2 := by
        rw [Spaces.L2Sq]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with z
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [self_mem_ae_restrict measurableSet_Icc] with θ hθ
        rw [mul_pow, rb_mixed_one_eq p f]
      rwa [hEq] at h
  have hper2 : ∀ m ≤ n, IntegrableOn (fun z => (CT.DzRIter m (CT.A2 f) z) ^ 2 * (Spaces.w z) ^ 2)
        Spaces.Iz
      ∧ ∫ z in Spaces.Iz, (CT.DzRIter m (CT.A2 f) z) ^ 2 * (Spaces.w z) ^ 2
          ≤ 321 * Spaces.HkSq α n f := by
    refine rb_L12f_per_m_bound n hn f hf hint2 hA2 hQ2.1
      (fun z θ => (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2)) ^ 2) ?_ ?_ ?_
      (Spaces.HkSq α n f) hHnn ?_
    · intro z hz θ hθ
      have hsin : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      have h2 : (0 : ℝ) ≤ Spaces.w z := by unfold Spaces.w; positivity
      have h1 : (Real.sin (2 * θ)) ^ Spaces.eta ≤ 1 :=
        Real.rpow_le_one (le_of_lt hsin) (Real.sin_le_one _) (le_of_lt Spaces.eta_pos)
      rw [div_pow]
      rw [le_div_iff₀ (by positivity :
        (0 : ℝ) < ((Real.sin (2 * θ)) ^ (Spaces.eta / 2)) ^ 2)]
      have hsq : ((Real.sin (2 * θ)) ^ (Spaces.eta / 2)) ^ 2
          = (Real.sin (2 * θ)) ^ Spaces.eta := rb_rpow_half_sq (le_of_lt hsin)
      rw [hsq]
      calc (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ Spaces.eta
          ≤ (Spaces.w z) ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = (Spaces.w z) ^ 2 := by ring
    · intro p hp z hz
      have h := hmt.1 p (by omega : p ≤ n) z hz
      refine (h.const_mul ((Spaces.w z) ^ 2)).congr ?_
      filter_upwards [Work.Elliptic.ae_restrict_Iθ_of_Ioo (p := fun θ =>
        (Spaces.w z) ^ 2 * (Spaces.DzIter p f z θ ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
          = (Spaces.DzIter p f z θ) ^ 2
              * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2)) ^ 2) (by
        intro θ h0 h1
        have hsin : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
        rw [div_pow, rb_rpow_half_sq (le_of_lt hsin), Real.rpow_neg (le_of_lt hsin)]
        ring)] with θ hθ
      exact hθ
    · intro p hp
      have h := hmt.2.1 p (by omega : p ≤ n)
      refine h.congr ?_
      filter_upwards with z
      show (∫ θ in Spaces.Iθ, Spaces.DzIter p f z θ ^ 2 * (Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.eta))
          = ∫ θ in Spaces.Iθ, (Spaces.DzIter p f z θ) ^ 2
              * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2)) ^ 2
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [Work.Elliptic.ae_restrict_Iθ_of_Ioo (p := fun θ =>
        Spaces.DzIter p f z θ ^ 2 * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
          = (Spaces.DzIter p f z θ) ^ 2
              * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2)) ^ 2) (by
        intro θ h0 h1
        have hsin : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
        rw [div_pow, rb_rpow_half_sq (le_of_lt hsin), Real.rpow_neg (le_of_lt hsin)]
        ring)] with θ hθ
      exact hθ
    · intro p hp
      have hp1 : p ≤ n := by omega
      have h := Spaces.L2Sq_DzIter_le_HkSq α n f hmem p hp1
      have hEq : Spaces.L2Sq (fun z θ => Spaces.DzIter p f z θ
            * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2)))
          = ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, (Spaces.DzIter p f z θ) ^ 2
              * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2)) ^ 2 := by
        rw [Spaces.L2Sq]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with z
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with θ
        rw [mul_pow]
      rwa [hEq] at h
  -- ## the two halves of the conclusion
  have key : ∀ (A : ℝ → ℝ), ContDiffOn ℝ ⊤ A (Set.Ioi 0) → (∀ m ≤ n, IntegrableOn
        (fun z => (CT.DzRIter m A z) ^ 2 * (Spaces.w z) ^ 2) Spaces.Iz
      ∧ ∫ z in Spaces.Iz, (CT.DzRIter m A z) ^ 2 * (Spaces.w z) ^ 2
          ≤ 321 * Spaces.HkSq α n f) → ∀ (C0 : ℝ),
      (C0) ^ 2 ≤ CKC * Spaces.HkSq α n f → ∀ j ≤ n,
      (IntegrableOn (fun z => (CT.DzRIter j (fun t => CT.pcoef α t * A t) z) ^ 2
            * (Spaces.w z) ^ 2) Spaces.Iz
        ∧ ∫ z in Spaces.Iz, (CT.DzRIter j (fun t => CT.pcoef α t * A t) z) ^ 2
            * (Spaces.w z) ^ 2
            ≤ 2 * ((n : ℝ) + 1) * Mp ^ 2 * ((2 : ℝ) ^ n) ^ 2 * (321 * Spaces.HkSq α n f))
        ∧ (IntegrableOn (fun z => (CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2) Spaces.Iz
          ∧ ∫ z in Spaces.Iz, (CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2 ≤ 2 * Mw ^ 2)
        ∧ (C0) ^ 2 * (∫ z in Spaces.Iz, (CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2)
            ≤ (CKC * Spaces.HkSq α n f) * (2 * Mw ^ 2) := by
    intro A hAsm hper C0 hC0 j hj
    obtain ⟨hIntP, hBndP⟩ := rb_pcoef_mul_w_sq α n A hAsm Mp (321 * Spaces.HkSq α n f)
      hMp_pos hMp hper j hj
    obtain ⟨hIntW, hBndW⟩ := rb_Wcoef_w_sq α n Mw hMw_pos hMw j hj
    refine ⟨⟨hIntP, hBndP⟩, ⟨hIntW, hBndW⟩, ?_⟩
    exact mul_le_mul hC0 hBndW (integral_nonneg fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_nonneg hCKC_pos.le hHnn)
  constructor
  · -- ## the estimate for `F₁`
    intro j hj
    have hpcA1 : ContDiffOn ℝ ⊤ (fun t => CT.pcoef α t * CT.A1 f t) (Set.Ioi 0) := hpcC.mul hA1sm
    have hcW : ContDiffOn ℝ ⊤ (fun t => (-(CT.KC1 f)) * CT.Wcoef α t) (Set.Ioi 0) :=
      contDiffOn_const.mul hWcC
    have hF1eq : CT.F1 α f = (fun t => CT.pcoef α t * CT.A1 f t)
        + (fun t => (-(CT.KC1 f)) * CT.Wcoef α t) := by
      funext z
      show (2 * z / (Spaces.c α * (1 + z) ^ 2)) * CT.A1 f z
          - (2 * z ^ 2 / (Spaces.c α * (1 + z) ^ 3)) * CT.KC1 f
        = CT.pcoef α z * CT.A1 f z + (-(CT.KC1 f)) * CT.Wcoef α z
      unfold CT.pcoef CT.Wcoef
      ring
    have hdec : ∀ z ∈ Set.Ioi (0 : ℝ), CT.DzRIter j (CT.F1 α f) z
        = CT.DzRIter j (fun t => CT.pcoef α t * CT.A1 f t) z
          + (-(CT.KC1 f)) * CT.DzRIter j (CT.Wcoef α) z := by
      intro z hz
      have h1 := rb_DzRIter_add hpcA1 hcW j hz
      have h2 := rb_DzRIter_const_mul (-(CT.KC1 f)) hWcC j hz
      simp only [Pi.add_apply] at h1
      rw [hF1eq, h1, h2]
    obtain ⟨⟨hIntP, hBndP⟩, ⟨hIntW, hBndW⟩, _⟩ :=
      key (CT.A1 f) hA1sm hper1 (CT.KC1 f) hKC.2 j hj
    have hIntR : IntegrableOn (fun z => 2 * ((CT.DzRIter j
            (fun t => CT.pcoef α t * CT.A1 f t) z) ^ 2 * (Spaces.w z) ^ 2)
          + 2 * (CT.KC1 f) ^ 2 * ((CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2))
        Spaces.Iz :=
      (hIntP.const_mul 2).add (hIntW.const_mul (2 * (CT.KC1 f) ^ 2))
    have hpt : ∀ z : ℝ, 0 < z → (CT.DzRIter j (CT.F1 α f) z) ^ 2 * (Spaces.w z) ^ 2
        ≤ 2 * ((CT.DzRIter j (fun t => CT.pcoef α t * CT.A1 f t) z) ^ 2 * (Spaces.w z) ^ 2)
          + 2 * (CT.KC1 f) ^ 2 * ((CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2) := by
      intro z hz
      have h2 := rb_add_sq_le_two (CT.DzRIter j (fun t => CT.pcoef α t * CT.A1 f t) z)
        ((-(CT.KC1 f)) * CT.DzRIter j (CT.Wcoef α) z)
      rw [hdec z hz]
      calc (CT.DzRIter j (fun t => CT.pcoef α t * CT.A1 f t) z
              + (-(CT.KC1 f)) * CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2
          ≤ (2 * (CT.DzRIter j (fun t => CT.pcoef α t * CT.A1 f t) z) ^ 2
              + 2 * ((-(CT.KC1 f)) * CT.DzRIter j (CT.Wcoef α) z) ^ 2) * (Spaces.w z) ^ 2 :=
            mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
        _ = 2 * ((CT.DzRIter j (fun t => CT.pcoef α t * CT.A1 f t) z) ^ 2 * (Spaces.w z) ^ 2)
              + 2 * (CT.KC1 f) ^ 2
                * ((CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2) := by ring
    refine ⟨?_, ?_⟩
    · rw [IntegrableOn] at hIntR ⊢
      refine hIntR.mono' ?_ ?_
      · exact (((rb_AEStronglyMeasurable_DzRIter j
          (rb_aestronglyMeasurable_of_continuousOn_Ioi hFsm.1.continuousOn)).pow 2).mul
            ((rb_measurable_w.aestronglyMeasurable).pow 2))
      · filter_upwards [rb_ae_pos_of_Iz_radial] with z hz
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        exact hpt z hz
    · have hle : ∀ᵐ z ∂(volume.restrict Spaces.Iz), (CT.DzRIter j (CT.F1 α f) z) ^ 2
          * (Spaces.w z) ^ 2
          ≤ 2 * ((CT.DzRIter j (fun t => CT.pcoef α t * CT.A1 f t) z) ^ 2 * (Spaces.w z) ^ 2)
            + 2 * (CT.KC1 f) ^ 2 * ((CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2) := by
        filter_upwards [rb_ae_pos_of_Iz_radial] with z hz
        exact hpt z hz
      have hmono := integral_mono_of_nonneg
        (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hIntR hle
      have hIntAdd : (∫ z in Spaces.Iz, 2 * ((CT.DzRIter j
              (fun t => CT.pcoef α t * CT.A1 f t) z) ^ 2 * (Spaces.w z) ^ 2)
            + 2 * (CT.KC1 f) ^ 2 * ((CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2))
          = 2 * (∫ z in Spaces.Iz, (CT.DzRIter j
                (fun t => CT.pcoef α t * CT.A1 f t) z) ^ 2 * (Spaces.w z) ^ 2)
            + (2 * (CT.KC1 f) ^ 2) * (∫ z in Spaces.Iz,
                (CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2) := by
        rw [MeasureTheory.integral_add (hIntP.const_mul 2)
            (hIntW.const_mul (2 * (CT.KC1 f) ^ 2)),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      have hfin : (2 * (∫ z in Spaces.Iz, (CT.DzRIter j
              (fun t => CT.pcoef α t * CT.A1 f t) z) ^ 2 * (Spaces.w z) ^ 2)
            + (2 * (CT.KC1 f) ^ 2) * (∫ z in Spaces.Iz,
                (CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2))
          ≤ (4 * ((n : ℝ) + 1) * Mp ^ 2 * ((2 : ℝ) ^ n) ^ 2 * 321 + 4 * CKC * Mw ^ 2)
              * Spaces.HkSq α n f := by
        have hPA : (∫ z in Spaces.Iz, (CT.DzRIter j
              (fun t => CT.pcoef α t * CT.A1 f t) z) ^ 2 * (Spaces.w z) ^ 2)
            ≤ 2 * ((n : ℝ) + 1) * Mp ^ 2 * ((2 : ℝ) ^ n) ^ 2 * 321 * Spaces.HkSq α n f := by
          nlinarith [hBndP, hHnn]
        have h1 : 2 * (∫ z in Spaces.Iz, (CT.DzRIter j
              (fun t => CT.pcoef α t * CT.A1 f t) z) ^ 2 * (Spaces.w z) ^ 2)
            ≤ 4 * ((n : ℝ) + 1) * Mp ^ 2 * ((2 : ℝ) ^ n) ^ 2 * 321 * Spaces.HkSq α n f := by
          nlinarith [hPA, hHnn]
        have hKC2 : (CT.KC1 f) ^ 2 * (∫ z in Spaces.Iz,
              (CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2)
            ≤ (CKC * Spaces.HkSq α n f) * (2 * Mw ^ 2) :=
          mul_le_mul hKC.2 hBndW (integral_nonneg fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
            (mul_nonneg hCKC_pos.le hHnn)
        have h2 : (2 * (CT.KC1 f) ^ 2) * (∫ z in Spaces.Iz,
              (CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2)
            ≤ 4 * CKC * Mw ^ 2 * Spaces.HkSq α n f := by
          nlinarith [hKC2, hHnn, sq_nonneg Mw]
        nlinarith [h1, h2]
      calc (∫ z in Spaces.Iz, (CT.DzRIter j (CT.F1 α f) z) ^ 2 * (Spaces.w z) ^ 2)
          ≤ ∫ z in Spaces.Iz, 2 * ((CT.DzRIter j
                (fun t => CT.pcoef α t * CT.A1 f t) z) ^ 2 * (Spaces.w z) ^ 2)
              + 2 * (CT.KC1 f) ^ 2 * ((CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2) :=
            hmono
        _ = 2 * (∫ z in Spaces.Iz, (CT.DzRIter j
                (fun t => CT.pcoef α t * CT.A1 f t) z) ^ 2 * (Spaces.w z) ^ 2)
              + (2 * (CT.KC1 f) ^ 2) * (∫ z in Spaces.Iz,
                  (CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2) := hIntAdd
        _ ≤ (4 * ((n : ℝ) + 1) * Mp ^ 2 * ((2 : ℝ) ^ n) ^ 2 * 321 + 4 * CKC * Mw ^ 2)
              * Spaces.HkSq α n f := hfin
        _ ≤ (4 * ((n : ℝ) + 1) * Mp ^ 2 * ((2 : ℝ) ^ n) ^ 2 * 321 + 4 * CKC * Mw ^ 2 + 1)
              * Spaces.HkSq α n f := by nlinarith [hHnn]
  · -- ## the estimate for `F₂`
    intro j hj
    have hpcA2 : ContDiffOn ℝ ⊤ (fun t => CT.pcoef α t * CT.A2 f t) (Set.Ioi 0) := hpcC.mul hA2sm
    have hcW0 : ContDiffOn ℝ ⊤ (fun t => CT.KC0 f * CT.Wcoef α t) (Set.Ioi 0) :=
      contDiffOn_const.mul hWcC
    have hneg : ContDiffOn ℝ ⊤ (fun t => (-1 : ℝ) * (CT.pcoef α t * CT.A2 f t)) (Set.Ioi 0) :=
      contDiffOn_const.mul hpcA2
    have hF2eq : CT.F2 α f = (fun t => CT.KC0 f * CT.Wcoef α t)
        + (fun t => (-1 : ℝ) * (CT.pcoef α t * CT.A2 f t)) := by
      funext z
      show (2 * z ^ 2 / (Spaces.c α * (1 + z) ^ 3)) * CT.KC0 f
          - (2 * z / (Spaces.c α * (1 + z) ^ 2)) * CT.A2 f z
        = CT.KC0 f * CT.Wcoef α z + (-1 : ℝ) * (CT.pcoef α z * CT.A2 f z)
      unfold CT.pcoef CT.Wcoef
      ring
    have hdec : ∀ z ∈ Set.Ioi (0 : ℝ), CT.DzRIter j (CT.F2 α f) z
        = CT.KC0 f * CT.DzRIter j (CT.Wcoef α) z
          + (-1 : ℝ) * CT.DzRIter j (fun t => CT.pcoef α t * CT.A2 f t) z := by
      intro z hz
      have h1 := rb_DzRIter_add hcW0 hneg j hz
      have h2 := rb_DzRIter_const_mul (CT.KC0 f) hWcC j hz
      have h3 := rb_DzRIter_const_mul (-1 : ℝ) hpcA2 j hz
      simp only [Pi.add_apply] at h1
      rw [hF2eq, h1, h2, h3]
    obtain ⟨⟨hIntP, hBndP⟩, ⟨hIntW, hBndW⟩, _⟩ :=
      key (CT.A2 f) hA2sm hper2 (CT.KC0 f) hKC.1 j hj
    have hIntR : IntegrableOn (fun z => (2 * (CT.KC0 f) ^ 2)
          * ((CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2)
          + 2 * ((CT.DzRIter j (fun t => CT.pcoef α t * CT.A2 f t) z) ^ 2
              * (Spaces.w z) ^ 2)) Spaces.Iz :=
      (hIntW.const_mul (2 * (CT.KC0 f) ^ 2)).add (hIntP.const_mul 2)
    have hpt : ∀ z : ℝ, 0 < z → (CT.DzRIter j (CT.F2 α f) z) ^ 2 * (Spaces.w z) ^ 2
        ≤ (2 * (CT.KC0 f) ^ 2) * ((CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2)
          + 2 * ((CT.DzRIter j (fun t => CT.pcoef α t * CT.A2 f t) z) ^ 2
              * (Spaces.w z) ^ 2) := by
      intro z hz
      have h2 := rb_add_sq_le_two (CT.KC0 f * CT.DzRIter j (CT.Wcoef α) z)
        ((-1 : ℝ) * CT.DzRIter j (fun t => CT.pcoef α t * CT.A2 f t) z)
      rw [hdec z hz]
      calc (CT.KC0 f * CT.DzRIter j (CT.Wcoef α) z
              + (-1 : ℝ) * CT.DzRIter j (fun t => CT.pcoef α t * CT.A2 f t) z) ^ 2
            * (Spaces.w z) ^ 2
          ≤ (2 * (CT.KC0 f * CT.DzRIter j (CT.Wcoef α) z) ^ 2
              + 2 * ((-1 : ℝ) * CT.DzRIter j (fun t => CT.pcoef α t * CT.A2 f t) z) ^ 2)
              * (Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
        _ = (2 * (CT.KC0 f) ^ 2) * ((CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2)
              + 2 * ((CT.DzRIter j (fun t => CT.pcoef α t * CT.A2 f t) z) ^ 2
                * (Spaces.w z) ^ 2) := by ring
    refine ⟨?_, ?_⟩
    · rw [IntegrableOn] at hIntR ⊢
      refine hIntR.mono' ?_ ?_
      · exact (((rb_AEStronglyMeasurable_DzRIter j
          (rb_aestronglyMeasurable_of_continuousOn_Ioi hFsm.2.continuousOn)).pow 2).mul
            ((rb_measurable_w.aestronglyMeasurable).pow 2))
      · filter_upwards [rb_ae_pos_of_Iz_radial] with z hz
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        exact hpt z hz
    · have hle : ∀ᵐ z ∂(volume.restrict Spaces.Iz), (CT.DzRIter j (CT.F2 α f) z) ^ 2
          * (Spaces.w z) ^ 2
          ≤ (2 * (CT.KC0 f) ^ 2) * ((CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2)
            + 2 * ((CT.DzRIter j (fun t => CT.pcoef α t * CT.A2 f t) z) ^ 2
                * (Spaces.w z) ^ 2) := by
        filter_upwards [rb_ae_pos_of_Iz_radial] with z hz
        exact hpt z hz
      have hmono := integral_mono_of_nonneg
        (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hIntR hle
      have hIntAdd : (∫ z in Spaces.Iz, (2 * (CT.KC0 f) ^ 2) * ((CT.DzRIter j (CT.Wcoef α) z) ^ 2
              * (Spaces.w z) ^ 2)
            + 2 * ((CT.DzRIter j (fun t => CT.pcoef α t * CT.A2 f t) z) ^ 2
              * (Spaces.w z) ^ 2))
          = (2 * (CT.KC0 f) ^ 2) * (∫ z in Spaces.Iz,
                (CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2)
            + 2 * (∫ z in Spaces.Iz, (CT.DzRIter j
                (fun t => CT.pcoef α t * CT.A2 f t) z) ^ 2 * (Spaces.w z) ^ 2) := by
        rw [MeasureTheory.integral_add (hIntW.const_mul (2 * (CT.KC0 f) ^ 2))
            (hIntP.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      have hfin : ((2 * (CT.KC0 f) ^ 2) * (∫ z in Spaces.Iz,
              (CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2)
            + 2 * (∫ z in Spaces.Iz, (CT.DzRIter j
                (fun t => CT.pcoef α t * CT.A2 f t) z) ^ 2 * (Spaces.w z) ^ 2))
          ≤ (4 * ((n : ℝ) + 1) * Mp ^ 2 * ((2 : ℝ) ^ n) ^ 2 * 321 + 4 * CKC * Mw ^ 2)
              * Spaces.HkSq α n f := by
        have hPA : (∫ z in Spaces.Iz, (CT.DzRIter j
              (fun t => CT.pcoef α t * CT.A2 f t) z) ^ 2 * (Spaces.w z) ^ 2)
            ≤ 2 * ((n : ℝ) + 1) * Mp ^ 2 * ((2 : ℝ) ^ n) ^ 2 * 321 * Spaces.HkSq α n f := by
          nlinarith [hBndP, hHnn]
        have h1 : 2 * (∫ z in Spaces.Iz, (CT.DzRIter j
              (fun t => CT.pcoef α t * CT.A2 f t) z) ^ 2 * (Spaces.w z) ^ 2)
            ≤ 4 * ((n : ℝ) + 1) * Mp ^ 2 * ((2 : ℝ) ^ n) ^ 2 * 321 * Spaces.HkSq α n f := by
          nlinarith [hPA, hHnn]
        have hKC2 : (CT.KC0 f) ^ 2 * (∫ z in Spaces.Iz,
              (CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2)
            ≤ (CKC * Spaces.HkSq α n f) * (2 * Mw ^ 2) :=
          mul_le_mul hKC.1 hBndW (integral_nonneg fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
            (mul_nonneg hCKC_pos.le hHnn)
        have h2 : (2 * (CT.KC0 f) ^ 2) * (∫ z in Spaces.Iz,
              (CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2)
            ≤ 4 * CKC * Mw ^ 2 * Spaces.HkSq α n f := by
          nlinarith [hKC2, hHnn, sq_nonneg Mw]
        nlinarith [h1, h2]
      calc (∫ z in Spaces.Iz, (CT.DzRIter j (CT.F2 α f) z) ^ 2 * (Spaces.w z) ^ 2)
          ≤ ∫ z in Spaces.Iz, (2 * (CT.KC0 f) ^ 2) * ((CT.DzRIter j (CT.Wcoef α) z) ^ 2
                * (Spaces.w z) ^ 2)
              + 2 * ((CT.DzRIter j (fun t => CT.pcoef α t * CT.A2 f t) z) ^ 2
                * (Spaces.w z) ^ 2) := hmono
        _ = (2 * (CT.KC0 f) ^ 2) * (∫ z in Spaces.Iz,
                (CT.DzRIter j (CT.Wcoef α) z) ^ 2 * (Spaces.w z) ^ 2)
              + 2 * (∫ z in Spaces.Iz, (CT.DzRIter j
                  (fun t => CT.pcoef α t * CT.A2 f t) z) ^ 2 * (Spaces.w z) ^ 2) := hIntAdd
        _ ≤ (4 * ((n : ℝ) + 1) * Mp ^ 2 * ((2 : ℝ) ^ n) ^ 2 * 321 + 4 * CKC * Mw ^ 2)
              * Spaces.HkSq α n f := hfin
        _ ≤ (4 * ((n : ℝ) + 1) * Mp ^ 2 * ((2 : ℝ) ^ n) ^ 2 * 321 + 4 * CKC * Mw ^ 2 + 1)
              * Spaces.HkSq α n f := by nlinarith [hHnn]

end Work.Coercivity
