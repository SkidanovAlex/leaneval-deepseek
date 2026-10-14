import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.T1Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.Spaces.aesm_mixed_Wt_sq_prod
import Submission.Work.Spaces.bt_f_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.sup_mixed_le_H4
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.cmode_bessel =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

set_option autoImplicit false

lemma measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc

/-! ## The zeros of the mode weights -/

/-- `pG n` is the polynomial realising the Gegenbauer polynomial `gC n`
(`gC n x = (pG n).eval x`); it obeys the same three-term recurrence as `gC n`. -/
def pG : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.C 3 * Polynomial.X
  | (n + 2) => Polynomial.C (((n : ℝ) + 2)⁻¹) *
      (Polynomial.C (2 * ((n : ℝ) + 5 / 2)) * (Polynomial.X * pG (n + 1))
        - Polynomial.C ((n : ℝ) + 3) * pG n)

/-- The value of `gC n` at `1` is the binomial coefficient `(n+1)(n+2)/2`
(`C_n^{(3/2)}(1) = (n+1)(n+2)/2`); in particular `gC n` is not the zero function. -/
lemma gC_one (n : ℕ) :
    Work.FTS.PhiStar.Gegenbauer.gC n 1 = ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 := by
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [show Work.FTS.PhiStar.Gegenbauer.gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    norm_num
  | one =>
    rw [show Work.FTS.PhiStar.Gegenbauer.gC 1 = (fun x : ℝ => 3 * x) from rfl]
    norm_num
  | more k ihk ihk1 =>
    rw [show Work.FTS.PhiStar.Gegenbauer.gC (k + 2) 1
        = (2 * ((k : ℝ) + 5 / 2) * 1 * Work.FTS.PhiStar.Gegenbauer.gC (k + 1) 1
            - ((k : ℝ) + 3) * Work.FTS.PhiStar.Gegenbauer.gC k 1) / ((k : ℝ) + 2)
        from rfl]
    rw [ihk1, ihk]
    push_cast
    have hne : ((k : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring

/-- `pG n` evaluates to `gC n`. -/
lemma pG_eval : ∀ n : ℕ, ∀ x : ℝ,
    (pG n).eval x = Work.FTS.PhiStar.Gegenbauer.gC n x := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    intro x
    rw [show pG 0 = (1 : Polynomial ℝ) from rfl,
      show Work.FTS.PhiStar.Gegenbauer.gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    simp
  | one =>
    intro x
    rw [show pG 1 = Polynomial.C 3 * Polynomial.X from rfl,
      show Work.FTS.PhiStar.Gegenbauer.gC 1 = (fun x : ℝ => 3 * x) from rfl]
    simp
  | more k ihk ihk1 =>
    intro x
    rw [show pG (k + 2) = Polynomial.C (((k : ℝ) + 2)⁻¹) *
        (Polynomial.C (2 * ((k : ℝ) + 5 / 2)) * (Polynomial.X * pG (k + 1))
          - Polynomial.C ((k : ℝ) + 3) * pG k) from rfl]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X,
      ihk x, ihk1 x]
    rw [show Work.FTS.PhiStar.Gegenbauer.gC (k + 2) x
        = (2 * ((k : ℝ) + 5 / 2) * x * Work.FTS.PhiStar.Gegenbauer.gC (k + 1) x
            - ((k : ℝ) + 3) * Work.FTS.PhiStar.Gegenbauer.gC k x) / ((k : ℝ) + 2) from rfl]
    rw [div_eq_inv_mul]
    ring

lemma pG_ne_zero (n : ℕ) : pG n ≠ 0 := by
  intro h
  have h1 : Work.FTS.PhiStar.Gegenbauer.gC n 1 = 0 := by
    rw [← pG_eval n 1, h]
    simp
  rw [gC_one n] at h1
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 := by positivity
  linarith

/-- A nonzero polynomial has finitely many real roots, so `gC (2m+1)` has finitely many
zeros. -/
lemma gC_roots_finite (m : ℕ) :
    {x : ℝ | Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) x = 0}.Finite := by
  have h := Polynomial.finite_setOfPred_isRoot (pG_ne_zero (2 * m + 1))
  simpa only [Set.mem_setOf_eq, Polynomial.IsRoot, pG_eval] using h

/-- The mode weight `θ ↦ eFam m θ · cos θ` vanishes only on a finite subset of `Iθ`. -/
lemma eFam_zeroSet_finite (m : ℕ) :
    {θ ∈ Work.Spaces.Iθ |
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ = 0}.Finite := by
  have hsub : {θ ∈ Work.Spaces.Iθ |
        Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ = 0} ⊆
      ({θ ∈ Work.Spaces.Iθ | Real.cos θ = 0} ∪
        {θ ∈ Work.Spaces.Iθ |
          Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) = 0}) := by
    rintro θ ⟨hθ, h0⟩
    rw [Work.FTS.PhiStar.Gegenbauer.eFam] at h0
    simp only [mul_eq_zero] at h0
    rcases h0 with (h | h) | h
    · left; exact ⟨hθ, h⟩
    · right; exact ⟨hθ, h⟩
    · left; exact ⟨hθ, h⟩
  refine Set.Finite.subset (Set.Finite.union ?_ ?_) hsub
  · refine Set.Finite.subset (Set.finite_singleton (Real.pi / 2)) ?_
    rintro θ ⟨hθ, h0⟩
    exact Real.strictAntiOn_cos.injOn
      ⟨hθ.1, le_trans hθ.2 (by linarith [Real.pi_pos])⟩
      ⟨by positivity, by linarith [Real.pi_pos]⟩
      (by rw [h0, Real.cos_pi_div_two])
  · refine Set.Finite.subset ((gC_roots_finite m).image Real.arcsin) ?_
    rintro θ ⟨hθ, h0⟩
    exact ⟨Real.sin θ, h0, Real.arcsin_sin (by linarith [hθ.1, Real.pi_pos]) hθ.2⟩

/-- The mode weights vanish only on a null set. -/
lemma eFam_mul_cos_ae_ne_zero (m : ℕ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  have hmeas : MeasurableSet {θ : ℝ |
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ = 0} :=
    (isClosed_eq (continuous_eFam_mul_cos m) continuous_const).measurableSet
  rw [show {θ : ℝ |
        ¬ Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ ≠ 0}
      = {θ : ℝ | Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ = 0} from by
    ext θ; simp only [Set.mem_setOf_eq, ne_eq, not_not]]
  rw [MeasureTheory.Measure.restrict_apply hmeas]
  rw [show {θ : ℝ | Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ = 0}
        ∩ Work.Spaces.Iθ
      = {θ ∈ Work.Spaces.Iθ |
          Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ = 0} from by
    ext θ
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩]
  exact (eFam_zeroSet_finite m).measure_zero MeasureTheory.volume

/-! ## The modes as an orthonormal system of `L²(Iθ)` -/

lemma isFiniteMeasure_Iθ :
    MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
    MeasureTheory.isFiniteMeasure_restrict, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-- The squared `L²(Iθ, cos θ dθ)`-norm of the `m`-th Dirichlet mode. -/
def eNorm (m : ℕ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ

lemma eNorm_pos (m : ℕ) : 0 < eNorm m := by
  rw [eNorm, Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts m]
  positivity

lemma continuous_eFam (m : ℕ) :
    Continuous (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
  rw [show Work.FTS.PhiStar.Gegenbauer.eFam m
      = fun θ : ℝ => Real.cos θ
          * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) from rfl]
  exact Real.continuous_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp
      Real.continuous_sin)

/-- The normalised representative `(‖eFam m‖)⁻¹ · √(cos ·) · eFam m` of the `m`-th mode in
`L²(Iθ)`. -/
def eFun (m : ℕ) : ℝ → ℝ :=
  fun θ => (Real.sqrt (eNorm m))⁻¹ *
    (Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ)

lemma continuous_eFun (m : ℕ) : Continuous (eFun m) := by
  refine continuous_const.mul ?_
  exact (Real.continuous_sqrt.comp Real.continuous_cos).mul (continuous_eFam m)

lemma eFun_memLp (m : ℕ) :
    MeasureTheory.MemLp (eFun m) 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  haveI := isFiniteMeasure_Iθ
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (s := Work.Spaces.Iθ)
    isCompact_Icc (continuous_eFun m).continuousOn
  refine MeasureTheory.MemLp.of_bound (continuous_eFun m).aestronglyMeasurable C ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Iθ]
  filter_upwards with θ hθ
  exact hC θ hθ

/-- The normalised modes, as elements of `L²(Iθ)`. -/
def eLp (m : ℕ) : MeasureTheory.Lp ℝ 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  MeasureTheory.MemLp.toLp (eFun m) (eFun_memLp m)

lemma eLp_coe (m : ℕ) :
    (eLp m : ℝ → ℝ) =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] eFun m :=
  MeasureTheory.MemLp.coeFn_toLp (eFun_memLp m)

/-- The normalised Dirichlet modes are orthonormal in `L²(Iθ)`. -/
lemma eLp_orthonormal : Orthonormal ℝ eLp := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [MeasureTheory.L2.inner_def]
  have hone : (fun a => inner ℝ ((eLp n : ℝ → ℝ) a) ((eLp m : ℝ → ℝ) a))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun a => eFun n a * eFun m a) := by
    filter_upwards [eLp_coe n, eLp_coe m] with a ha hb
    rw [ha, hb, Real.inner_apply]
  rw [MeasureTheory.integral_congr_ae hone]
  have hsplit : (∫ a, eFun n a * eFun m a
        ∂MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = (Real.sqrt (eNorm n))⁻¹ * ((Real.sqrt (eNorm m))⁻¹ *
          ∫ a, (Real.sqrt (Real.cos a) * Work.FTS.PhiStar.Gegenbauer.eFam n a)
              * (Real.sqrt (Real.cos a) * Work.FTS.PhiStar.Gegenbauer.eFam m a)
            ∂MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have hpt : (fun a => eFun n a * eFun m a)
        = fun a => (Real.sqrt (eNorm n))⁻¹ * ((Real.sqrt (eNorm m))⁻¹ *
            ((Real.sqrt (Real.cos a) * Work.FTS.PhiStar.Gegenbauer.eFam n a)
              * (Real.sqrt (Real.cos a) * Work.FTS.PhiStar.Gegenbauer.eFam m a))) := by
      funext a
      simp only [eFun]
      ring
    rw [hpt, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hsplit]
  have hII : (∫ a, (Real.sqrt (Real.cos a) * Work.FTS.PhiStar.Gegenbauer.eFam n a)
        * (Real.sqrt (Real.cos a) * Work.FTS.PhiStar.Gegenbauer.eFam m a)
        ∂MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = ∫ a in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam n a
            * Work.FTS.PhiStar.Gegenbauer.eFam m a * Real.cos a := by
    refine MeasureTheory.integral_congr_ae ?_
    show ∀ᵐ a ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Real.sqrt (Real.cos a) * Work.FTS.PhiStar.Gegenbauer.eFam n a)
        * (Real.sqrt (Real.cos a) * Work.FTS.PhiStar.Gegenbauer.eFam m a)
        = Work.FTS.PhiStar.Gegenbauer.eFam n a
            * Work.FTS.PhiStar.Gegenbauer.eFam m a * Real.cos a
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Iθ]
    filter_upwards with a ha
    have hc : 0 ≤ Real.cos a :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [ha.1, Real.pi_pos], ha.2⟩
    conv_rhs => rw [← Real.sq_sqrt hc]
    ring
  rw [hII]
  by_cases hnm : n = m
  · rw [if_pos hnm, hnm]
    have hdiag : (∫ a in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam m a
            * Work.FTS.PhiStar.Gegenbauer.eFam m a * Real.cos a) = eNorm m := by
      rw [eNorm]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun a _ => ?_)
      ring
    rw [hdiag]
    have hsq : Real.sqrt (eNorm m) * Real.sqrt (eNorm m) = eNorm m := by
      rw [← sq, Real.sq_sqrt (le_of_lt (eNorm_pos m))]
    have hN : eNorm m ≠ 0 := ne_of_gt (eNorm_pos m)
    calc (Real.sqrt (eNorm m))⁻¹ * ((Real.sqrt (eNorm m))⁻¹ * eNorm m)
        = ((Real.sqrt (eNorm m))⁻¹ * (Real.sqrt (eNorm m))⁻¹) * eNorm m := by ring
      _ = (Real.sqrt (eNorm m) * Real.sqrt (eNorm m))⁻¹ * eNorm m := by rw [mul_inv]
      _ = (eNorm m)⁻¹ * eNorm m := by rw [hsq]
      _ = 1 := inv_mul_cancel₀ hN
  · rw [if_neg hnm, eFam_orthogonal_Iθ n m hnm]
    ring

/-- The inner product of the `m`-th normalised mode with the `L²`-class of an arbitrary
function `f`. -/
lemma inner_eLp (m : ℕ) {f : ℝ → ℝ}
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    inner ℝ (eLp m) (hf.toLp f)
      = (Real.sqrt (eNorm m))⁻¹ *
        (∫ θ in Work.Spaces.Iθ,
          (Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * f θ) := by
  rw [MeasureTheory.L2.inner_def]
  have hone : (fun a => inner ℝ ((eLp m : ℝ → ℝ) a) ((hf.toLp f : ℝ → ℝ) a))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun a => (Real.sqrt (eNorm m))⁻¹ *
          ((Real.sqrt (Real.cos a) * Work.FTS.PhiStar.Gegenbauer.eFam m a) * f a)) := by
    filter_upwards [eLp_coe m, MeasureTheory.MemLp.coeFn_toLp hf] with a ha hb
    rw [ha, hb, Real.inner_apply]
    simp only [eFun]
    ring
  rw [MeasureTheory.integral_congr_ae hone, MeasureTheory.integral_const_mul]

/-! ## The mode coefficients -/

/-- The interval integral over `(0, π/2)` equals the set integral over `Iθ`. -/
lemma intervalIntegral_eq_setIntegral (g : ℝ → ℝ) :
    (∫ θ in (0 : ℝ)..(Real.pi / 2), g θ) = ∫ θ in Work.Spaces.Iθ, g θ := by
  rw [intervalIntegral.integral_of_le
    (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- The numerator of `cmode m F z`, written in the `√(cos ·)`-form matching the `L²` inner
product. -/
def bInt (m : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ,
    (Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      * (Real.sqrt (Real.cos θ) * F z θ)

/-- `cmode m F z` is the quotient `bInt m F z / eNorm m`. -/
lemma cmode_eq (m : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Series.cmode m F z = bInt m F z / eNorm m := by
  rw [Work.FTS.PhiStar.Series.cmode, bInt, eNorm]
  congr 1
  · rw [intervalIntegral_eq_setIntegral
      (fun θ => F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun θ hθ => ?_)
    have hc : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    conv_lhs => rw [← Real.sq_sqrt hc]
    ring
  · rw [intervalIntegral_eq_setIntegral
      (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)]

/-! ## Bessel's inequality -/

theorem cmode_bessel (F : ℝ → ℝ → ℝ) (z : ℝ) (N : ℕ) :
    ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
        (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
          * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
      ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (F z θ ^ 2 * Real.cos θ) := by
  set A : ENNReal :=
    ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (F z θ ^ 2 * Real.cos θ) with hA
  set K : ℝ → ℝ := fun θ => Real.sqrt (Real.cos θ) * F z θ with hK
  change ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
      eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) ≤ A
  -- the pointwise identity `K θ ^ 2 = F z θ ^ 2 * cos θ` on `Iθ`
  have hKsq_pt : ∀ θ ∈ Work.Spaces.Iθ, K θ ^ 2 = F z θ ^ 2 * Real.cos θ := by
    intro θ hθ
    have hc : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    rw [hK]
    rw [show (Real.sqrt (Real.cos θ) * F z θ) ^ 2 = Real.cos θ * F z θ ^ 2 by
      rw [mul_pow, Real.sq_sqrt hc]]
    ring
  by_cases hAtop : A = ⊤
  · rw [hAtop]
    exact le_top
  · have hAlt : A < ⊤ := lt_top_iff_ne_top.mpr hAtop
    by_cases hKsm : MeasureTheory.AEStronglyMeasurable K
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
    · -- the `L²` case: Bessel's inequality
      have hKsq : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (K θ ^ 2)) = A := by
        rw [hA]
        refine MeasureTheory.lintegral_congr_ae ?_
        show ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          ENNReal.ofReal (K θ ^ 2) = ENNReal.ofReal (F z θ ^ 2 * Real.cos θ)
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Iθ]
        filter_upwards with θ hθ
        rw [hKsq_pt θ hθ]
      have hKfin : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (K θ ^ 2)) < ⊤ := by
        rw [hKsq]; exact hAlt
      have hKmem : MeasureTheory.MemLp K 2
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        rw [MeasureTheory.memLp_two_iff_integrable_sq hKsm]
        refine ⟨hKsm.pow 2, ?_⟩
        rw [MeasureTheory.hasFiniteIntegral_iff_norm]
        have heq : (∫⁻ a, ENNReal.ofReal ‖K a ^ 2‖
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
            = ∫⁻ a, ENNReal.ofReal (K a ^ 2)
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
          refine MeasureTheory.lintegral_congr_ae
            (Filter.Eventually.of_forall (fun a => ?_))
          show ENNReal.ofReal ‖K a ^ 2‖ = ENNReal.ofReal (K a ^ 2)
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (K a))]
        rw [heq]; exact hKfin
      have hbessel : (∑ m ∈ Finset.range (N + 1),
            ‖inner ℝ (eLp m) (hKmem.toLp K)‖ ^ 2) ≤ ‖hKmem.toLp K‖ ^ 2 :=
        Orthonormal.sum_inner_products_le (hKmem.toLp K) (v := eLp)
          (s := Finset.range (N + 1)) eLp_orthonormal
      have hnorm : ‖hKmem.toLp K‖ ^ 2
          = ∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ := by
        rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
        have h1 : (∫ a, inner ℝ ((hKmem.toLp K : ℝ → ℝ) a)
              ((hKmem.toLp K : ℝ → ℝ) a)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
            = ∫ a, K a ^ 2 ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [MeasureTheory.MemLp.coeFn_toLp hKmem] with a ha
          rw [ha, Real.inner_apply, sq]
        rw [h1]
        refine MeasureTheory.integral_congr_ae ?_
        show ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          K θ ^ 2 = F z θ ^ 2 * Real.cos θ
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Iθ]
        filter_upwards with θ hθ
        rw [hKsq_pt θ hθ]
      have hsummand : ∀ m : ℕ, eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
          = ‖inner ℝ (eLp m) (hKmem.toLp K)‖ ^ 2 := by
        intro m
        rw [cmode_eq m F z, inner_eLp m hKmem, Real.norm_eq_abs, sq_abs]
        rw [show (∫ θ in Work.Spaces.Iθ,
              (Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * K θ)
            = bInt m F z from by rw [bInt, hK]]
        have hN : eNorm m ≠ 0 := ne_of_gt (eNorm_pos m)
        have hs : Real.sqrt (eNorm m) ≠ 0 :=
          ne_of_gt (Real.sqrt_pos.2 (eNorm_pos m))
        field_simp
        rw [Real.sq_sqrt (le_of_lt (eNorm_pos m))]
        ring
      have hmain : (∑ m ∈ Finset.range (N + 1),
            eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
          ≤ ∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ := by
        calc (∑ m ∈ Finset.range (N + 1),
              eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
            = ∑ m ∈ Finset.range (N + 1),
                ‖inner ℝ (eLp m) (hKmem.toLp K)‖ ^ 2 :=
              Finset.sum_congr rfl (fun m _ => hsummand m)
          _ ≤ ‖hKmem.toLp K‖ ^ 2 := hbessel
          _ = ∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ := hnorm
      have hint : MeasureTheory.Integrable (fun θ => F z θ ^ 2 * Real.cos θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        refine hKmem.integrable_sq.congr ?_
        show ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          K θ ^ 2 = F z θ ^ 2 * Real.cos θ
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Iθ]
        filter_upwards with θ hθ
        exact hKsq_pt θ hθ
      have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
          (fun θ => F z θ ^ 2 * Real.cos θ) := by
        show ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          0 ≤ F z θ ^ 2 * Real.cos θ
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Iθ]
        filter_upwards with θ hθ
        exact mul_nonneg (sq_nonneg _)
          (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
      rw [hA, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun θ => F z θ ^ 2 * Real.cos θ) hint hnonneg]
      exact ENNReal.ofReal_le_ofReal hmain
    · -- the degenerate case: every mode coefficient vanishes
      have hKnm : ¬ MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => F z θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        intro h
        apply hKsm
        rw [hK]
        have hcont : Continuous (fun θ : ℝ => Real.sqrt (Real.cos θ)) :=
          Real.continuous_sqrt.comp Real.continuous_cos
        exact hcont.aestronglyMeasurable.mul h
      have hbzero : ∀ m : ℕ, bInt m F z = 0 := by
        intro m
        have hne := not_aestronglyMeasurable_mul_eFam hKnm eFam_mul_cos_ae_ne_zero m
        have hzero : (∫ θ in Work.Spaces.Iθ,
            F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) = 0 :=
          MeasureTheory.integral_non_aestronglyMeasurable hne
        have hbridge : (∫ θ in Work.Spaces.Iθ,
              (Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
                * (Real.sqrt (Real.cos θ) * F z θ))
            = ∫ θ in Work.Spaces.Iθ,
                F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun θ hθ => ?_)
          have hc : 0 ≤ Real.cos θ :=
            Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
          conv_rhs => rw [← Real.sq_sqrt hc]
          ring
        rw [bInt, hbridge]
        exact hzero
      have hsum0 : (∑ m ∈ Finset.range (N + 1),
          eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) = 0 := by
        refine Finset.sum_eq_zero (fun m _ => ?_)
        rw [cmode_eq m F z, hbzero m, zero_div]
        simp
      rw [hsum0, ENNReal.ofReal_zero]
      exact bot_le

end Work.EllipticEst.ModalSolution
end
end
-- ===== merged: Submission.Work.FTS.EllSol.K5cAux.thWeightCmp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.K5cAux

open Work.FTS.EllSol.PkgK5.K5c

local notation "σ" => Work.FTS.EllipticEst.thEta
local notation "η" => Work.Spaces.eta
local notation "Iθ" => Work.Spaces.Iθ


theorem thWeightCmp : ∃ K : ℝ, 0 < K ∧ ∀ (ε u : ℝ), 0 < ε → ε ≤ 1 / 2 →
    u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ *
        (Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - u) + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + u)
          + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + u - Real.pi)))
      ≤ K * Work.FTS.EllipticEst.thEta u := by
  set Clayer : ℝ := (Real.pi / 4) ^ η / (1 - η) with hCl
  set K₁ : ℝ := Clayer * 3 ^ (1 - η) * 4 ^ η * sMass⁻¹ with hK₁
  set K₂ : ℝ := Clayer * 2 ^ η * sMass⁻¹ with hK₂
  set K₃ : ℝ := 30000 * ((Real.pi / 12) * sMass)⁻¹ with hK₃
  set Kbig : ℝ := 1 + (K₁ + Real.pi ^ η) + 2 * K₂ + K₃ with hKbig
  have hCl_nn : 0 ≤ Clayer := by
    rw [hCl]; exact div_nonneg (Real.rpow_nonneg (by positivity) _) one_sub_eta_pos.le
  have hπ_nn : 0 ≤ Real.pi ^ η := Real.rpow_nonneg (by positivity) _
  have hK₁_nn : 0 ≤ K₁ := by
    rw [hK₁]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCl_nn (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (by norm_num) _)) (inv_nonneg.mpr sMass_pos.le)
  have hK₂_nn : 0 ≤ K₂ := by
    rw [hK₂]
    exact mul_nonneg (mul_nonneg hCl_nn (Real.rpow_nonneg (by norm_num) _))
      (inv_nonneg.mpr sMass_pos.le)
  have hK₃_nn : 0 ≤ K₃ := by
    rw [hK₃]
    exact mul_nonneg (by norm_num)
      (inv_nonneg.mpr (mul_nonneg (by positivity) sMass_pos.le))
  have hKbig_pos : 0 < Kbig := by rw [hKbig]; linarith
  refine ⟨Kbig, hKbig_pos, ?_⟩
  intro ε u hε hε2 hu
  obtain ⟨hu0, hu2⟩ := hu
  have hσu_pos : 0 < σ u := sigma_pos hu0 hu2
  have hσu_nn : 0 ≤ σ u := hσu_pos.le
  have hsMass_nn : 0 ≤ sMass := sMass_pos.le
  have hinv_nn : 0 ≤ (ε * sMass)⁻¹ := inv_nonneg.mpr (mul_nonneg hε.le hsMass_nn)
  have hshift₁ := integrableOn_sigma_sKer_shift (ε := ε) (v := -u) hε
  have hshift₂ := integrableOn_sigma_sKer_shift (ε := ε) (v := u) hε
  have hshift₃ := integrableOn_sigma_sKer_shift (ε := ε) (v := u - Real.pi) hε
  have hshift₁' : IntegrableOn (fun θ : ℝ => σ θ * sKer ε (θ - u)) Iθ := hshift₁
  have hshift₃' : IntegrableOn (fun θ : ℝ => σ θ * sKer ε (θ + u - Real.pi)) Iθ := by
    simpa only [sub_eq_add_neg, add_assoc] using hshift₃
  have hsum_eq : (fun θ : ℝ => σ θ *
        (sKer ε (θ - u) + sKer ε (θ + u) + sKer ε (θ + u - Real.pi)))
      = fun θ : ℝ => (σ θ * sKer ε (θ - u) + σ θ * sKer ε (θ + u))
          + σ θ * sKer ε (θ + u - Real.pi) := by
    funext θ; ring
  have hsplit : (∫ θ in Iθ, σ θ *
        (sKer ε (θ - u) + sKer ε (θ + u) + sKer ε (θ + u - Real.pi)))
      = (∫ θ in Iθ, σ θ * sKer ε (θ - u)) + (∫ θ in Iθ, σ θ * sKer ε (θ + u))
        + (∫ θ in Iθ, σ θ * sKer ε (θ + u - Real.pi)) := by
    have h1 : (∫ θ in Iθ, σ θ * sKer ε (θ - u) + σ θ * sKer ε (θ + u))
        = (∫ θ in Iθ, σ θ * sKer ε (θ - u)) + (∫ θ in Iθ, σ θ * sKer ε (θ + u)) :=
      integral_add hshift₁' hshift₂
    have h2 : (∫ θ in Iθ, (σ θ * sKer ε (θ - u) + σ θ * sKer ε (θ + u))
          + σ θ * sKer ε (θ + u - Real.pi))
        = (∫ θ in Iθ, σ θ * sKer ε (θ - u) + σ θ * sKer ε (θ + u))
          + (∫ θ in Iθ, σ θ * sKer ε (θ + u - Real.pi)) :=
      integral_add (hshift₁'.add hshift₂) hshift₃'
    rw [hsum_eq, h2, h1]
  by_cases hεbig : Real.pi / 12 < ε
  · -- Case I: `ε` is bounded below, so the crude bound suffices.
    have hpt : ∀ θ ∈ Iθ, σ θ * (sKer ε (θ - u) + sKer ε (θ + u) + sKer ε (θ + u - Real.pi))
        ≤ (3 * (ε * sMass)⁻¹) * σ θ := by
      intro θ hθ
      have hσ : 0 ≤ σ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
      have h1 := sKer_le_inv hε (θ - u)
      have h2 := sKer_le_inv hε (θ + u)
      have h3 := sKer_le_inv hε (θ + u - Real.pi)
      have hsum : sKer ε (θ - u) + sKer ε (θ + u) + sKer ε (θ + u - Real.pi)
          ≤ 3 * (ε * sMass)⁻¹ := by linarith
      calc σ θ * (sKer ε (θ - u) + sKer ε (θ + u) + sKer ε (θ + u - Real.pi))
          ≤ σ θ * (3 * (ε * sMass)⁻¹) := mul_le_mul_of_nonneg_left hsum hσ
        _ = (3 * (ε * sMass)⁻¹) * σ θ := by ring
    have hIntL : IntegrableOn (fun θ : ℝ => σ θ *
        (sKer ε (θ - u) + sKer ε (θ + u) + sKer ε (θ + u - Real.pi))) Iθ := by
      rw [hsum_eq]
      exact (hshift₁'.add hshift₂).add hshift₃'
    have hIntR : IntegrableOn (fun θ : ℝ => (3 * (ε * sMass)⁻¹) * σ θ) Iθ :=
      (Work.FTS.EllipticEst.integrableOn_thEta.1).const_mul _
    have hmono := integral_mono_ae hIntL hIntR
      (ae_restrict_of_forall_mem measurableSet_Icc hpt)
    rw [integral_const_mul] at hmono
    have hσint : (∫ θ in Iθ, σ θ) ≤ 10000 := Work.FTS.EllipticEst.integrableOn_thEta.2
    have hinv : (ε * sMass)⁻¹ ≤ ((Real.pi / 12) * sMass)⁻¹ :=
      inv_anti₀ (mul_pos (by positivity) sMass_pos)
        (mul_le_mul_of_nonneg_right hεbig.le hsMass_nn)
    have hstep : (∫ θ in Iθ, σ θ *
        (sKer ε (θ - u) + sKer ε (θ + u) + sKer ε (θ + u - Real.pi))) ≤ K₃ := by
      calc (∫ θ in Iθ, σ θ *
            (sKer ε (θ - u) + sKer ε (θ + u) + sKer ε (θ + u - Real.pi)))
          ≤ (3 * (ε * sMass)⁻¹) * (∫ θ in Iθ, σ θ) := hmono
        _ ≤ (3 * (ε * sMass)⁻¹) * 10000 :=
            mul_le_mul_of_nonneg_left hσint (by positivity)
        _ = 30000 * (ε * sMass)⁻¹ := by ring
        _ ≤ 30000 * ((Real.pi / 12) * sMass)⁻¹ := mul_le_mul_of_nonneg_left hinv (by norm_num)
        _ = K₃ := by rw [hK₃]
    calc (∫ θ in Iθ, σ θ *
          (sKer ε (θ - u) + sKer ε (θ + u) + sKer ε (θ + u - Real.pi))) ≤ K₃ := hstep
      _ = K₃ * 1 := (mul_one K₃).symm
      _ ≤ K₃ * σ u := mul_le_mul_of_nonneg_left (one_le_sigma hu0 hu2) hK₃_nn
      _ ≤ Kbig * σ u := by
          refine mul_le_mul_of_nonneg_right ?_ hσu_nn
          rw [hKbig]; linarith
  · -- Case II: `ε ≤ π/12`.
    push_neg at hεbig
    have h3ε : 3 * ε ≤ Real.pi / 4 := by linarith [Real.pi_pos]
    have h3π : 3 * ε ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    -- the middle kernel
    have hTmid : (∫ θ in Iθ, σ θ * sKer ε (θ - u)) ≤ max K₁ (Real.pi ^ η) * σ u := by
      by_cases hfar : 2 * ε ≤ min u (Real.pi / 2 - u)
      · have hpt : ∀ θ ∈ Iθ, σ θ * sKer ε (θ - u) ≤ (Real.pi ^ η * σ u) * sKer ε (θ - u) := by
          intro θ _
          by_cases hk : sKer ε (θ - u) = 0
          · rw [hk, mul_zero, mul_zero]
          · have hkpos : 0 < sKer ε (θ - u) :=
              lt_of_le_of_ne (sKer_nonneg hε _) (Ne.symm hk)
            have habs : |θ - u| < ε := by
              by_contra hcon
              exact hk (sKer_eq_zero_of_le_abs hε (not_lt.mp hcon))
            exact mul_le_mul_of_nonneg_right (sigma_le_of_far hu0 hu2 hε hfar habs) hkpos.le
        have hIntR : IntegrableOn (fun θ : ℝ => (Real.pi ^ η * σ u) * sKer ε (θ - u)) Iθ :=
          (((continuous_sKer ε).comp (continuous_id.sub continuous_const)).integrableOn_Icc
            |>.const_mul _)
        have hmono := integral_mono_ae hshift₁' hIntR
          (ae_restrict_of_forall_mem measurableSet_Icc hpt)
        rw [integral_const_mul] at hmono
        have hstep : (∫ θ in Iθ, σ θ * sKer ε (θ - u)) ≤ Real.pi ^ η * σ u :=
          calc (∫ θ in Iθ, σ θ * sKer ε (θ - u))
              ≤ (Real.pi ^ η * σ u) * ∫ θ in Iθ, sKer ε (θ - u) := hmono
            _ ≤ (Real.pi ^ η * σ u) * 1 :=
                mul_le_mul_of_nonneg_left (integral_Iθ_sKer_sub_le_one hε)
                  (mul_nonneg hπ_nn hσu_nn)
            _ = Real.pi ^ η * σ u := by ring
        calc (∫ θ in Iθ, σ θ * sKer ε (θ - u)) ≤ Real.pi ^ η * σ u := hstep
          _ ≤ max K₁ (Real.pi ^ η) * σ u :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) hσu_nn
      · have hnear : min u (Real.pi / 2 - u) < 2 * ε := not_le.mp hfar
        have h4η : ε ^ (-η) ≤ 4 ^ η * σ u :=
          inv_rpow_le_four_of_le hε (sigma_ge_four_eps hu0 hu2 hε hnear)
        have hstep : (∫ θ in Iθ, σ θ * sKer ε (θ - u))
            ≤ Clayer * 3 ^ (1 - η) * 4 ^ η * sMass⁻¹ * σ u := by
          by_cases hu2e : u < 2 * ε
          · have hpt : ∀ θ ∈ Iθ, σ θ * sKer ε (θ - u) ≤
                (ε * sMass)⁻¹ * (σ θ *
                  Set.indicator (Set.Icc 0 (3 * ε)) (fun _ => (1 : ℝ)) θ) := by
              intro θ hθ
              have hθ0 : 0 ≤ θ := (show θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from hθ).1
              have hσ : 0 ≤ σ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
              by_cases hle : θ ≤ 3 * ε
              · have hind : Set.indicator (Set.Icc (0 : ℝ) (3 * ε)) (fun _ => (1 : ℝ)) θ = 1 :=
                  Set.indicator_of_mem (by rw [Set.mem_Icc]; exact ⟨hθ0, hle⟩) _
                rw [hind, mul_one]
                calc σ θ * sKer ε (θ - u) ≤ σ θ * (ε * sMass)⁻¹ :=
                      mul_le_mul_of_nonneg_left (sKer_le_inv hε _) hσ
                  _ = (ε * sMass)⁻¹ * σ θ := by ring
              · have hzu : ε < θ - u := by linarith [not_le.mp hle]
                have hz : sKer ε (θ - u) = 0 := sKer_eq_zero_of_le_abs hε (by
                  rw [abs_of_pos (by linarith : (0 : ℝ) < θ - u)]; exact hzu.le)
                rw [hz, mul_zero]
                exact mul_nonneg hinv_nn
                  (mul_nonneg hσ (Set.indicator_nonneg (fun _ _ => zero_le_one) θ))
            have hmono := integral_mono_ae hshift₁'
              (integrableOn_sigma_indicator_mul (c := (ε * sMass)⁻¹) hinv_nn measurableSet_Icc)
              (ae_restrict_of_forall_mem measurableSet_Icc hpt)
            rw [integral_const_mul,
              indicator_left_setIntegral (b := 3 * ε) (by linarith) h3π] at hmono
            calc (∫ θ in Iθ, σ θ * sKer ε (θ - u))
                ≤ (ε * sMass)⁻¹ * (∫ θ in (0 : ℝ)..(3 * ε), σ θ) := hmono
              _ ≤ (ε * sMass)⁻¹ * (Clayer * (3 * ε) ^ (1 - η)) := by
                  refine mul_le_mul_of_nonneg_left ?_ hinv_nn
                  have h := integral_thEta_zero_a (a := 3 * ε) (by linarith) h3ε
                  rw [hCl]
                  calc ∫ θ in (0 : ℝ)..(3 * ε), σ θ
                      ≤ (Real.pi / 4) ^ η * (3 * ε) ^ (1 - η) / (1 - η) := h
                    _ = (Real.pi / 4) ^ η / (1 - η) * (3 * ε) ^ (1 - η) := by ring
              _ ≤ Clayer * 3 ^ (1 - η) * 4 ^ η * sMass⁻¹ * σ u := by
                  rw [hCl]; exact window_le_three hε h4η
          · have hu2e' : 2 * ε ≤ u := not_lt.mp hu2e
            have hpu : Real.pi / 2 - u < 2 * ε := by
              by_contra hcon
              exact absurd (le_min hu2e' (not_lt.mp hcon)) (not_le.mpr hnear)
            have hpt : ∀ θ ∈ Iθ, σ θ * sKer ε (θ - u) ≤
                (ε * sMass)⁻¹ * (σ θ *
                  Set.indicator (Set.Icc (Real.pi / 2 - 3 * ε) (Real.pi / 2))
                    (fun _ => (1 : ℝ)) θ) := by
              intro θ hθ
              have hθ1 : θ ≤ Real.pi / 2 := (show θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from hθ).2
              have hσ : 0 ≤ σ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
              by_cases hge : Real.pi / 2 - 3 * ε ≤ θ
              · have hind : Set.indicator (Set.Icc (Real.pi / 2 - 3 * ε) (Real.pi / 2))
                    (fun _ => (1 : ℝ)) θ = 1 :=
                  Set.indicator_of_mem (by rw [Set.mem_Icc]; exact ⟨hge, hθ1⟩) _
                rw [hind, mul_one]
                calc σ θ * sKer ε (θ - u) ≤ σ θ * (ε * sMass)⁻¹ :=
                      mul_le_mul_of_nonneg_left (sKer_le_inv hε _) hσ
                  _ = (ε * sMass)⁻¹ * σ θ := by ring
              · have hz : sKer ε (θ - u) = 0 := sKer_eq_zero_of_le_abs hε (by
                  rw [abs_of_neg (by linarith [not_le.mp hge])]; linarith [not_le.mp hge])
                rw [hz, mul_zero]
                exact mul_nonneg hinv_nn
                  (mul_nonneg hσ (Set.indicator_nonneg (fun _ _ => zero_le_one) θ))
            have hmono := integral_mono_ae hshift₁'
              (integrableOn_sigma_indicator_mul (c := (ε * sMass)⁻¹) hinv_nn measurableSet_Icc)
              (ae_restrict_of_forall_mem measurableSet_Icc hpt)
            rw [integral_const_mul,
              indicator_right_setIntegral (a := 3 * ε) (by linarith) (by linarith [Real.pi_pos])]
              at hmono
            calc (∫ θ in Iθ, σ θ * sKer ε (θ - u))
                ≤ (ε * sMass)⁻¹ * (∫ θ in (Real.pi / 2 - 3 * ε)..(Real.pi / 2), σ θ) := hmono
              _ ≤ (ε * sMass)⁻¹ * (Clayer * (3 * ε) ^ (1 - η)) := by
                  refine mul_le_mul_of_nonneg_left ?_ hinv_nn
                  have h := integral_thEta_right_layer (a := 3 * ε) (by linarith) h3ε
                  rw [hCl]
                  calc ∫ θ in (Real.pi / 2 - 3 * ε)..(Real.pi / 2), σ θ
                      ≤ (Real.pi / 4) ^ η * (3 * ε) ^ (1 - η) / (1 - η) := h
                    _ = (Real.pi / 4) ^ η / (1 - η) * (3 * ε) ^ (1 - η) := by ring
              _ ≤ Clayer * 3 ^ (1 - η) * 4 ^ η * sMass⁻¹ * σ u := by
                  rw [hCl]; exact window_le_three hε h4η
        calc (∫ θ in Iθ, σ θ * sKer ε (θ - u))
            ≤ Clayer * 3 ^ (1 - η) * 4 ^ η * sMass⁻¹ * σ u := hstep
          _ = K₁ * σ u := by rw [← hK₁]
          _ ≤ max K₁ (Real.pi ^ η) * σ u :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hσu_nn
    -- the reflected kernel
    have hTleft : (∫ θ in Iθ, σ θ * sKer ε (θ + u)) ≤ K₂ * σ u := by
      by_cases hu_lt : u < ε
      · have hδ0 : 0 < ε - u := by linarith
        have hδπ : ε - u ≤ Real.pi / 2 := by linarith [Real.pi_pos]
        have hδ4 : ε - u ≤ Real.pi / 4 := by linarith [Real.pi_pos, hεbig]
        have hpt : ∀ θ ∈ Iθ, σ θ * sKer ε (θ + u) ≤
            (ε * sMass)⁻¹ * (σ θ *
              Set.indicator (Set.Icc 0 (ε - u)) (fun _ => (1 : ℝ)) θ) := by
          intro θ hθ
          have hθ0 : 0 ≤ θ := (show θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from hθ).1
          have hσ : 0 ≤ σ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
          by_cases hle : θ ≤ ε - u
          · have hind : Set.indicator (Set.Icc (0 : ℝ) (ε - u)) (fun _ => (1 : ℝ)) θ = 1 :=
              Set.indicator_of_mem (by rw [Set.mem_Icc]; exact ⟨hθ0, hle⟩) _
            rw [hind, mul_one]
            calc σ θ * sKer ε (θ + u) ≤ σ θ * (ε * sMass)⁻¹ :=
                  mul_le_mul_of_nonneg_left (sKer_le_inv hε _) hσ
              _ = (ε * sMass)⁻¹ * σ θ := by ring
          · have hzu : ε < θ + u := by linarith [not_le.mp hle]
            have hz : sKer ε (θ + u) = 0 := sKer_eq_zero_of_le_abs hε (by
              rw [abs_of_pos (by linarith : (0 : ℝ) < θ + u)]; exact hzu.le)
            rw [hz, mul_zero]
            exact mul_nonneg hinv_nn
              (mul_nonneg hσ (Set.indicator_nonneg (fun _ _ => zero_le_one) θ))
        have hmono := integral_mono_ae hshift₂
          (integrableOn_sigma_indicator_mul (c := (ε * sMass)⁻¹) hinv_nn measurableSet_Icc)
          (ae_restrict_of_forall_mem measurableSet_Icc hpt)
        rw [integral_const_mul,
          indicator_left_setIntegral (b := ε - u) hδ0.le hδπ] at hmono
        have h2η : ε ^ (-η) ≤ 2 ^ η * σ u :=
          inv_rpow_le_two_of_le hε (sigma_ge_two_eps hu0 hu2 hε (Or.inl hu_lt))
        calc (∫ θ in Iθ, σ θ * sKer ε (θ + u))
            ≤ (ε * sMass)⁻¹ * (∫ θ in (0 : ℝ)..(ε - u), σ θ) := hmono
          _ ≤ (ε * sMass)⁻¹ * (Clayer * (ε - u) ^ (1 - η)) := by
              refine mul_le_mul_of_nonneg_left ?_ hinv_nn
              have h := integral_thEta_zero_a (a := ε - u) hδ0 hδ4
              rw [hCl]
              calc ∫ θ in (0 : ℝ)..(ε - u), σ θ
                  ≤ (Real.pi / 4) ^ η * (ε - u) ^ (1 - η) / (1 - η) := h
                _ = (Real.pi / 4) ^ η / (1 - η) * (ε - u) ^ (1 - η) := by ring
          _ ≤ Clayer * 2 ^ η * sMass⁻¹ * σ u := by
              rw [hCl]; exact window_le_two hε hδ0.le (by linarith) h2η
          _ = K₂ * σ u := by rw [← hK₂]
      · have hzero : (∫ θ in Iθ, σ θ * sKer ε (θ + u)) = 0 := by
          have h1 : (∫ θ in Iθ, σ θ * sKer ε (θ + u)) = ∫ θ in Iθ, (0 : ℝ) := by
            refine integral_congr_ae ?_
            filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
            have hθ0 : 0 ≤ θ := (show θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from hθ).1
            have hzu : ε ≤ θ + u := by linarith [not_lt.mp hu_lt]
            rw [sKer_eq_zero_of_le_abs hε (by
              rw [abs_of_pos (by linarith : (0 : ℝ) < θ + u)]; exact hzu), mul_zero]
          rw [h1, integral_zero]
        rw [hzero]
        exact mul_nonneg hK₂_nn hσu_nn
    -- the third (right reflected) kernel
    have hTright : (∫ θ in Iθ, σ θ * sKer ε (θ + u - Real.pi)) ≤ K₂ * σ u := by
      by_cases hpu_lt : Real.pi / 2 - u < ε
      · have hδ0 : 0 < ε - (Real.pi / 2 - u) := by linarith
        have hδπ : ε - (Real.pi / 2 - u) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
        have hδ4 : ε - (Real.pi / 2 - u) ≤ Real.pi / 4 := by linarith [Real.pi_pos, hεbig]
        have hpt : ∀ θ ∈ Iθ, σ θ * sKer ε (θ + u - Real.pi) ≤
            (ε * sMass)⁻¹ * (σ θ *
              Set.indicator (Set.Icc (Real.pi / 2 - (ε - (Real.pi / 2 - u))) (Real.pi / 2))
                (fun _ => (1 : ℝ)) θ) := by
          intro θ hθ
          have hθ1 : θ ≤ Real.pi / 2 := (show θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from hθ).2
          have hσ : 0 ≤ σ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
          by_cases hge : Real.pi / 2 - (ε - (Real.pi / 2 - u)) ≤ θ
          · have hind : Set.indicator (Set.Icc (Real.pi / 2 - (ε - (Real.pi / 2 - u)))
                  (Real.pi / 2)) (fun _ => (1 : ℝ)) θ = 1 :=
              Set.indicator_of_mem (by rw [Set.mem_Icc]; exact ⟨hge, hθ1⟩) _
            rw [hind, mul_one]
            calc σ θ * sKer ε (θ + u - Real.pi) ≤ σ θ * (ε * sMass)⁻¹ :=
                  mul_le_mul_of_nonneg_left (sKer_le_inv hε _) hσ
              _ = (ε * sMass)⁻¹ * σ θ := by ring
          · have hzu : θ + u - Real.pi < -ε := by linarith [not_le.mp hge]
            have hz : sKer ε (θ + u - Real.pi) = 0 := sKer_eq_zero_of_le_abs hε (by
              rw [abs_of_neg (by linarith)]; linarith)
            rw [hz, mul_zero]
            exact mul_nonneg hinv_nn
              (mul_nonneg hσ (Set.indicator_nonneg (fun _ _ => zero_le_one) θ))
        have hmono := integral_mono_ae hshift₃'
          (integrableOn_sigma_indicator_mul (c := (ε * sMass)⁻¹) hinv_nn measurableSet_Icc)
          (ae_restrict_of_forall_mem measurableSet_Icc hpt)
        rw [integral_const_mul,
          indicator_right_setIntegral (a := ε - (Real.pi / 2 - u)) hδ0.le hδπ] at hmono
        have h2η : ε ^ (-η) ≤ 2 ^ η * σ u :=
          inv_rpow_le_two_of_le hε (sigma_ge_two_eps hu0 hu2 hε (Or.inr hpu_lt))
        calc (∫ θ in Iθ, σ θ * sKer ε (θ + u - Real.pi))
            ≤ (ε * sMass)⁻¹ *
              (∫ θ in (Real.pi / 2 - (ε - (Real.pi / 2 - u)))..(Real.pi / 2), σ θ) := hmono
          _ ≤ (ε * sMass)⁻¹ * (Clayer * (ε - (Real.pi / 2 - u)) ^ (1 - η)) := by
              refine mul_le_mul_of_nonneg_left ?_ hinv_nn
              have h := integral_thEta_right_layer (a := ε - (Real.pi / 2 - u)) hδ0 hδ4
              rw [hCl]
              calc ∫ θ in (Real.pi / 2 - (ε - (Real.pi / 2 - u)))..(Real.pi / 2), σ θ
                  ≤ (Real.pi / 4) ^ η * (ε - (Real.pi / 2 - u)) ^ (1 - η) / (1 - η) := h
                _ = (Real.pi / 4) ^ η / (1 - η) * (ε - (Real.pi / 2 - u)) ^ (1 - η) := by ring
          _ ≤ Clayer * 2 ^ η * sMass⁻¹ * σ u := by
              rw [hCl]; exact window_le_two hε hδ0.le (by linarith) h2η
          _ = K₂ * σ u := by rw [← hK₂]
      · have hzero : (∫ θ in Iθ, σ θ * sKer ε (θ + u - Real.pi)) = 0 := by
          have h1 : (∫ θ in Iθ, σ θ * sKer ε (θ + u - Real.pi)) = ∫ θ in Iθ, (0 : ℝ) := by
            refine integral_congr_ae ?_
            filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
            have hθ1 : θ ≤ Real.pi / 2 := (show θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from hθ).2
            have hzu : θ + u - Real.pi ≤ -ε := by linarith [not_lt.mp hpu_lt]
            rw [sKer_eq_zero_of_le_abs hε (by rw [abs_of_neg (by linarith)]; linarith),
              mul_zero]
          rw [h1, integral_zero]
        rw [hzero]
        exact mul_nonneg hK₂_nn hσu_nn
    -- assembly
    rw [hsplit]
    have hmax_le : max K₁ (Real.pi ^ η) ≤ K₁ + Real.pi ^ η := max_le (by linarith) (by linarith)
    have hfin : max K₁ (Real.pi ^ η) * σ u + K₂ * σ u + K₂ * σ u ≤ Kbig * σ u := by
      have h1 : max K₁ (Real.pi ^ η) * σ u ≤ (K₁ + Real.pi ^ η) * σ u :=
        mul_le_mul_of_nonneg_right hmax_le hσu_nn
      have h2 : (K₁ + Real.pi ^ η) * σ u + K₂ * σ u + K₂ * σ u
          ≤ (1 + (K₁ + Real.pi ^ η) + 2 * K₂ + K₃) * σ u := by
        nlinarith [hK₂_nn, hK₃_nn, hσu_nn]
      rw [hKbig]
      linarith
    linarith [hTmid, hTleft, hTright, hfin]

end Work.FTS.EllSol.K5cAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.radialAuxBase =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Radial profiles vs. their `sin (2θ)`-multiples: the algebraic identities

Part 1 of the proof of `Work.FTS.EllSol.PkgK5.radialHkNorm_le_sinMul`: the one-variable
iterates `RIter j Λ` of the radial operator `D_z = z ∂_z`, the identity
`D_z^j (Λ · B θ) = (RIter j Λ) · B`, and the corresponding angular identities.
-/

namespace Work.FTS.EllSol.PkgK5

namespace Radial

/-! ## The one-dimensional radial operator `D_z = z ∂_z` -/

/-- The one-dimensional operator `h ↦ z ∂_z h`. -/
def RDz (h : ℝ → ℝ) : ℝ → ℝ := fun z => z * deriv h z

/-- The `j`-fold iterate of `RDz`. -/
def RIter (j : ℕ) (h : ℝ → ℝ) : ℝ → ℝ := RDz^[j] h

@[simp] theorem RIter_zero (h : ℝ → ℝ) : RIter 0 h = h := rfl

theorem RIter_succ (j : ℕ) (h : ℝ → ℝ) :
    RIter (j + 1) h = fun z => z * deriv (RIter j h) z := by
  rw [show RIter (j + 1) h = RDz (RIter j h) from Function.iterate_succ_apply' RDz j h]
  rfl

theorem RIter_succ_apply (j : ℕ) (h : ℝ → ℝ) (z : ℝ) :
    RIter (j + 1) h z = z * deriv (RIter j h) z := by
  rw [RIter_succ]

theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem sin_two_le_one (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

/-- `sin(2·)^p` is measurable. -/
theorem measurable_sin2_rpow (p : ℝ) : Measurable (fun θ : ℝ => Real.sin (2 * θ) ^ p) := by
  fun_prop

/-! ### Smoothness of the radial iterates -/

/-- The iterates `RIter j Λ` of a smooth `Λ` are smooth on `(0,∞)`. -/
theorem contDiffOn_RIter (Λ : ℝ → ℝ) (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) :
    ∀ j n : ℕ, ContDiffOn ℝ n (RIter j Λ) (Set.Ioi 0) := by
  intro j
  induction j with
  | zero => intro n; simpa using hΛ n
  | succ j ih =>
    intro n
    have h1 : ContDiffOn ℝ (n + 1) (RIter j Λ) (Set.Ioi 0) := ih (n + 1)
    have h2 : ContDiffOn ℝ n (deriv (RIter j Λ)) (Set.Ioi 0) :=
      h1.deriv_of_isOpen isOpen_Ioi (by simp)
    have h3 : ContDiffOn ℝ n (fun z : ℝ => z) (Set.Ioi 0) := contDiff_id.contDiffOn
    rw [RIter_succ]
    exact h3.mul h2

/-- Differentiability of the radial iterates at a positive point. -/
theorem differentiableAt_RIter (Λ : ℝ → ℝ) (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0))
    (j : ℕ) {z : ℝ} (hz : 0 < z) : DifferentiableAt ℝ (RIter j Λ) z :=
  ((contDiffOn_RIter Λ hΛ j 1).differentiableOn (by simp)).differentiableAt
    (isOpen_Ioi.mem_nhds hz)

theorem continuousOn_RIter (Λ : ℝ → ℝ) (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0))
    (j : ℕ) : ContinuousOn (RIter j Λ) (Set.Ioi 0) :=
  (contDiffOn_RIter Λ hΛ j 0).continuousOn

theorem continuousOn_w : ContinuousOn Work.Spaces.w (Set.Ioi 0) := by
  show ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0)
  refine ContinuousOn.div ?_ ?_ ?_
  · exact (continuousOn_const.add continuousOn_id).pow 2
  · exact continuousOn_id.pow 2
  · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)

/-! ### The iterates of `D_z` on a `θ`-dependent product -/

/-- On the open half-line, `D_z^j` of the *radial* function `(z,θ) ↦ Λ z` is the one-variable
iterate `RIter j Λ` (evaluated at `z`), independently of `θ`. -/
theorem DzIter_radial (Λ : ℝ → ℝ) (j : ℕ) :
    ∀ {z : ℝ}, 0 < z → ∀ θ : ℝ,
      Work.Spaces.DzIter j (fun z θ => Λ z) z θ = RIter j Λ z := by
  induction j with
  | zero => intro z hz θ; rfl
  | succ j ih =>
    intro z hz θ
    have hev : (fun z' => Work.Spaces.DzIter j (fun z θ => Λ z) z' θ)
        =ᶠ[𝓝 z] RIter j Λ := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact ih hz' θ
    have hder : deriv (fun z' => Work.Spaces.DzIter j (fun z θ => Λ z) z' θ) z
        = deriv (RIter j Λ) z := hev.deriv_eq
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
    rw [hder, RIter_succ_apply]

/-- On the open half-line, `D_z^j` of a function of the form `(z,θ) ↦ Λ z · B θ` is
`(RIter j Λ z) · B θ`: `D_z` only sees the `z`-dependence. -/
theorem DzIter_mul_theta (Λ : ℝ → ℝ) (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0))
    (B : ℝ → ℝ) (j : ℕ) :
    ∀ {z : ℝ}, 0 < z → ∀ θ : ℝ,
      Work.Spaces.DzIter j (fun z θ => Λ z * B θ) z θ = RIter j Λ z * B θ := by
  induction j with
  | zero => intro z hz θ; rfl
  | succ j ih =>
    intro z hz θ
    have hev : (fun z' => Work.Spaces.DzIter j (fun z θ => Λ z * B θ) z' θ)
        =ᶠ[𝓝 z] (fun z' => RIter j Λ z' * B θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact ih hz' θ
    have hder : deriv (fun z' => Work.Spaces.DzIter j (fun z θ => Λ z * B θ) z' θ) z
        = deriv (fun z' => RIter j Λ z' * B θ) z := hev.deriv_eq
    have hdm : deriv (fun z' => RIter j Λ z' * B θ) z = deriv (RIter j Λ) z * B θ :=
      deriv_mul_const (differentiableAt_RIter Λ hΛ j hz) (B θ)
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz, hder, hdm,
      RIter_succ_apply]
    ring

end Radial

end Work.FTS.EllSol.PkgK5
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.SliceDBook =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Blocks

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The open neighbourhood of `Iθ` on which a smooth slice is `C^∞` -/







/-! ## The numerical bounds on `γ = gam α` for `α ∈ (0,1]` -/

theorem gam_lt_two {α : ℝ} (hα : α ≤ 1) : Work.Spaces.gam α < 2 := by
  rw [Work.Spaces.gam]; linarith

theorem gam_le_two_add_eta {α : ℝ} (hα : α ≤ 1) :
    Work.Spaces.gam α ≤ 2 + Work.Spaces.eta := by
  rw [Work.Spaces.gam, Work.Spaces.eta]; linarith

/-! ## The two exponent comparisons on `Iθ`

On `Iθ` one has `0 ≤ sin(2θ) ≤ 1`, so `θ ↦ sin(2θ)^p` is antitone in `p` on the positive
exponents (`sin_two_rpow_le_rpow`).  Since `γ = 1 + α/10 ∈ (1, 11/10]` we have
`2 - γ ∈ [9/10, 1) ⊂ (0, ∞)`, `-η ≤ 2 - γ` (`η = 99/100`, `2 - γ ≥ 9/10 > -η`) and
`-γ ≤ 2 - γ`; hence `sin(2θ)^{2-γ}` is dominated both by `sin(2θ)^{-η}` and by
`sin(2θ)^{-γ}`. -/



/-! ## The dominating function `slicePhi` dominates its summands -/






end Work.FTS.EllipticEst.Blocks
end
end
-- ===== merged: Submission.Work.FTS.H2.T1HardAesm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

/-! ## Joint continuity of `T1Hard` on the open quadrant

Every factor of
`T1Hard α f g z θ = f z θ · w(z)² · ( D_θ(D_z^4 g) · D_z^4 g · sin(2θ)^{-η}
  + (∑_{(j,i)} D_θ(D_z^jD_θ^i g) · D_z^jD_θ^i g) · sin(2θ)^{-γ} )`
is continuous on `(0,∞) × (0,π/2)`: `f` and all the `D`-derivatives of `g` are smooth on
the open neighbourhood `nbhU ⊇ Qd` of the closed quadrant, while `w` is continuous off the
axis `z = 0` and `sin(2θ)^{-p}` is continuous where `sin(2θ) > 0`. -/









end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.Transport3Aux.num_int_1d_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliary estimates for `num_int_1d`

This file collects the one-dimensional analytic material used by the proof of
`Work.FTS.H2.Transport3Aux.num_int_1d`:

* `hardy_power_weak` : the weighted Hardy inequality with a boundary term, stated for a
  function which is only assumed continuous on `[0,b]`, differentiable on `(0,b)` with
  `deriv f` bounded there (no `C¹`-on-the-closed-interval hypothesis).  The proof is the
  one of `Submission/Work/FTS/H2/Transport3Aux/power_hardy_boundary` with the smoothness
  hypothesis replaced by the weaker ones used here.
* `sq_integral_le` : Cauchy–Schwarz for interval integrals, proved by completing the square.
* `young_pt`, `good_weight_pt`, `bad_conv` : pointwise `sin (2θ)`-weight comparisons.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Transport3Aux

set_option maxHeartbeats 1000000

/-! ## 1. The weighted Hardy inequality with a boundary term, weak hypotheses -/


/-! ## 2. Cauchy–Schwarz for interval integrals (by completing the square) -/

theorem sq_integral_le {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a b)
    (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume a b) :
    (∫ x in a..b, g x) ^ 2 ≤ (b - a) * ∫ x in a..b, g x ^ 2 := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h
    simp
  · have hlt : 0 < b - a := by linarith
    set c : ℝ := (∫ x in a..b, g x) / (b - a) with hc
    have hconst : (∫ _x in a..b, c ^ 2) = (b - a) * c ^ 2 := by
      rw [intervalIntegral.integral_const]; simp
    have hsq : (∫ x in a..b, (g x - c) ^ 2) = (∫ x in a..b, g x ^ 2) - 2 * c * (∫ x in a..b, g x)
        + (b - a) * c ^ 2 := by
      have h1 : (fun x : ℝ => (g x - c) ^ 2)
          = fun x : ℝ => g x ^ 2 - 2 * c * g x + c ^ 2 := by
        funext x; ring
      rw [h1]
      rw [intervalIntegral.integral_add]
      · rw [intervalIntegral.integral_sub]
        · rw [intervalIntegral.integral_const_mul, hconst]
        · exact hg2
        · exact hg.const_mul (2 * c)
      · exact hg2.sub (hg.const_mul (2 * c))
      · exact intervalIntegrable_const
    have hnn : 0 ≤ ∫ x in a..b, (g x - c) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)
    have hkey : 0 ≤ (∫ x in a..b, g x ^ 2) - 2 * c * (∫ x in a..b, g x) + (b - a) * c ^ 2 := by
      rw [← hsq]; exact hnn
    have hmain : (∫ x in a..b, g x) ^ 2 ≤ (b - a) * ∫ x in a..b, g x ^ 2 := by
      have hmult : (∫ x in a..b, g x) ^ 2 = (b - a) * (2 * c * (∫ x in a..b, g x) - (b - a) * c ^ 2) := by
        rw [hc]; field_simp; ring
      nlinarith [hkey, hmult, hlt]
    exact hmain

/-! ## 3. Pointwise weight comparisons -/






end Work.FTS.H2.Transport3Aux
end
end
-- ===== merged: Submission.Work.RPFresh.slice_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.RPFresh

open MeasureTheory Set intervalIntegral Filter
open scoped Real Topology

set_option autoImplicit false



end Work.RPFresh
end
