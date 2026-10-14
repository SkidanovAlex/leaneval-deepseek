import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.HQ.BadsummandQ
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS

open Work.FTS.EllipticEst (SmoothOpen)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Smoothness of finite sums -/

/-- A finite sum of functions that are `C^∞` on the open quadrant is `C^∞` there. -/
theorem smoothOpen_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ → ℝ}
    (hf : ∀ i ∈ s, SmoothOpen (f i)) :
    SmoothOpen (fun z θ => ∑ i ∈ s, f i z θ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (fun z θ : ℝ => ∑ i ∈ (∅ : Finset ι), f i z θ) = fun _ _ => (0 : ℝ) := by
        funext z θ; simp
      rw [h0, SmoothOpen]
      exact (contDiffOn_const (c := (0 : ℝ)) (s := Work.FTS.EllipticEst.Q0)).congr
        (fun p _ => rfl)
  | insert a s ha ih =>
      have hsum : (fun z θ : ℝ => ∑ i ∈ insert a s, f i z θ)
          = fun z θ => f a z θ + ∑ i ∈ s, f i z θ := by
        funext z θ; rw [Finset.sum_insert ha]
      rw [hsum]
      exact Work.FTS.EllipticEst.smoothOpen_add (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-! ## The zero function -/

/-- `D_z^j` of the zero function is zero. -/
theorem DzIter_zero_fun (j : ℕ) :
    Work.Spaces.DzIter j (fun _ _ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
  induction j with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.Dz, Work.Spaces.pz, deriv_const, mul_zero]

/-- `D_θ^i` of the zero function is zero. -/
theorem DthIter_zero_fun (i : ℕ) :
    Work.Spaces.DthIter i (fun _ _ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth, deriv_const, mul_zero]

/-- `D_z^j D_θ^i` of the zero function is zero. -/
theorem mixed_zero_fun (j i : ℕ) :
    Work.Spaces.mixed j i (fun _ _ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
  rw [Work.Spaces.mixed, DthIter_zero_fun, DzIter_zero_fun]

/-- The `ℋ^k`-integrand of the zero function vanishes. -/
theorem HkIntegrand_zero_fun (α : ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (fun _ _ => (0 : ℝ)) z θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, DzIter_zero_fun, mixed_zero_fun, Pi.zero_apply,
    zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, sq, mul_zero]
  simp

/-! ## Additivity of the slot operators for finite sums -/



/-! ## The pointwise subadditivity (two terms) -/

/-- **The `ℋ^k`-integrand is subadditive on the open class**:
`HkIntegrand α k (f + g) ≤ 2·(HkIntegrand α k f + HkIntegrand α k g)`.

This is the `SmoothOpen` version of `Work.FTS.Galerkin.Hilbert.HkIntegrand_add_le` (which needs
`SmoothNbhd`, i.e. analyticity on a neighbourhood of the closed quadrant). -/
theorem HkIntegrand_add_le_open (α : ℝ) (k : ℕ) (hα : 0 < α) {f g : ℝ → ℝ → ℝ}
    (hf : SmoothOpen f) (hg : SmoothOpen g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
        ≤ 2 * (Work.Spaces.HkIntegrand α k f z θ + Work.Spaces.HkIntegrand α k g z θ) := by
  intro z hz θ hθ
  have hzf := Work.FTS.EllipticEst.HkIntegrand_eq_zero_of_sin_eq_zero'
  by_cases hz0 : z = 0
  · rw [hz0, Work.FTS.EllipticEst.HkIntegrand_eq_zero_of_z_eq_zero']
    have h1 := Work.Spaces.HkIntegrand_nonneg α k f 0 θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α k g 0 θ
    linarith
  by_cases hsin : Real.sin (2 * θ) = 0
  · rw [Work.FTS.EllipticEst.HkIntegrand_eq_zero_of_sin_eq_zero' α k _ hα hsin,
      Work.FTS.EllipticEst.HkIntegrand_eq_zero_of_sin_eq_zero' α k f hα hsin,
      Work.FTS.EllipticEst.HkIntegrand_eq_zero_of_sin_eq_zero' α k g hα hsin]
    norm_num
  -- an interior point of the open quadrant
  have hθ' : θ ∈ Set.Ioo 0 (π / 2) := by
    refine ⟨?_, ?_⟩
    · rcases lt_or_eq_of_le hθ.1 with h | h
      · exact h
      · exact absurd (by rw [← h, mul_zero, Real.sin_zero]) hsin
    · rcases lt_or_eq_of_le hθ.2 with h | h
      · exact h
      · exact absurd (by rw [h, show 2 * (π / 2) = π by ring, Real.sin_pi]) hsin
  have hzg : 0 < z := lt_of_le_of_ne (Set.mem_Ici.mp hz) (Ne.symm hz0)
  have hDz : ∀ i : ℕ, Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.DzIter i f z θ + Work.Spaces.DzIter i g z θ :=
    fun i => Work.FTS.EllipticEst.SmoothOpen.DzIter_add hf hg i z θ hzg hθ'.1 hθ'.2
  have hMx : ∀ j i : ℕ, Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ :=
    fun j i => Work.FTS.EllipticEst.SmoothOpen.mixed_add hf hg j i z θ hzg hθ'.1 hθ'.2
  set T : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hT
  set U : ℝ := Work.Spaces.Wt α z θ with hU
  have hZ : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ * T) ^ 2)
      ≤ 2 * ((∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ * T) ^ 2)
        + (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i g z θ * T) ^ 2)) := by
    have hp : ∀ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ * T) ^ 2
          ≤ 2 * ((Work.Spaces.DzIter i f z θ * T) ^ 2 + (Work.Spaces.DzIter i g z θ * T) ^ 2) := by
      intro i _
      rw [hDz i]
      nlinarith [sq_nonneg (Work.Spaces.DzIter i f z θ * T - Work.Spaces.DzIter i g z θ * T)]
    refine (Finset.sum_le_sum hp).trans_eq ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ * U) ^ 2 else 0)
      ≤ 2 * ((∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * U) ^ 2 else 0)
        + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i g z θ * U) ^ 2 else 0)) := by
    have hp : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ * U) ^ 2 else 0)
          ≤ 2 * ((if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * U) ^ 2 else 0)
            + (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i g z θ * U) ^ 2 else 0)) := by
      intro i _ j _
      by_cases hP : 1 ≤ i ∧ i + j ≤ k
      · rw [hMx j i]
        simp only [if_pos hP]
        nlinarith [sq_nonneg (Work.Spaces.mixed j i f z θ * U - Work.Spaces.mixed j i g z θ * U)]
      · simp only [if_neg hP]
        norm_num
    refine (Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hp i hi j hj).trans_eq ?_
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          2 * ((if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * U) ^ 2 else 0)
            + (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i g z θ * U) ^ 2 else 0)))
        = ∑ i ∈ Finset.range (k + 1), 2 * ∑ j ∈ Finset.range (k + 1),
            ((if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * U) ^ 2 else 0)
              + (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i g z θ * U) ^ 2 else 0)) := by
          refine Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ 2).symm
      _ = ∑ i ∈ Finset.range (k + 1), 2 * ((∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * U) ^ 2 else 0)
            + (∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i g z θ * U) ^ 2 else 0)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_add_distrib]
      _ = 2 * ∑ i ∈ Finset.range (k + 1), ((∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * U) ^ 2 else 0)
            + (∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i g z θ * U) ^ 2 else 0)) :=
          (Finset.mul_sum _ _ 2).symm
      _ = 2 * ((∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * U) ^ 2 else 0)
            + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i g z θ * U) ^ 2 else 0)) := by
          rw [Finset.sum_add_distrib]
  simp only [Work.Spaces.HkIntegrand, hT, hU]
  linarith [hZ, hM]

/-! ## The pointwise subadditivity (finite sums) -/

/-- **The `ℋ^k`-integrand is subadditive for finite sums**: for functions smooth on the open
quadrant, `HkIntegrand α k (∑_{i ∈ s} f_i) ≤ (2|s|)·∑_{i ∈ s} HkIntegrand α k (f_i)`. -/
theorem HkIntegrand_finset_sum_le (α : ℝ) (k : ℕ) (hα : 0 < α) {ι : Type*} (s : Finset ι)
    {f : ι → ℝ → ℝ → ℝ} (hf : ∀ i ∈ s, SmoothOpen (f i)) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => ∑ i ∈ s, f i z θ) z θ
        ≤ (2 : ℝ) ^ s.card * ∑ i ∈ s, Work.Spaces.HkIntegrand α k (f i) z θ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro z hz θ hθ
      have h0 : (fun z θ : ℝ => ∑ i ∈ (∅ : Finset ι), f i z θ) = fun _ _ => (0 : ℝ) := by
        funext z θ; simp
      rw [h0]
      simp only [Finset.sum_empty, Finset.card_empty, pow_zero, one_mul]
      exact le_of_eq (HkIntegrand_zero_fun α k z θ)
  | insert a s ha ih =>
      intro z hz θ hθ
      have hsum : (fun z θ : ℝ => ∑ i ∈ insert a s, f i z θ)
          = fun z θ => f a z θ + ∑ i ∈ s, f i z θ := by
        funext z θ; rw [Finset.sum_insert ha]
      have hfa : SmoothOpen (f a) := hf a (Finset.mem_insert_self a s)
      have hfs : SmoothOpen (fun z θ => ∑ i ∈ s, f i z θ) :=
        smoothOpen_finset_sum s (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have hstep := HkIntegrand_add_le_open α k hα hfa hfs z hz θ hθ
      have hih := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) z hz θ hθ
      have hfa0 := Work.Spaces.HkIntegrand_nonneg α k (f a) z θ
      have hsum0 : (0 : ℝ) ≤ ∑ i ∈ s, Work.Spaces.HkIntegrand α k (f i) z θ :=
        Finset.sum_nonneg fun i _ => Work.Spaces.HkIntegrand_nonneg α k (f i) z θ
      have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ s.card := one_le_pow₀ (by norm_num)
      rw [hsum, Finset.sum_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
      nlinarith [hstep, hih, hfa0, hsum0, hpow]

/-! ## The integrated forms -/

/-- **The `ℋ^k`-energy is subadditive on the open class** (two terms). -/
theorem HkSq_add_le_open (α : ℝ) (k : ℕ) (hα : 0 < α) {f g : ℝ → ℝ → ℝ}
    (hf : SmoothOpen f) (hg : SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkSq α k (fun z θ => f z θ + g z θ)
      ≤ 2 * (Work.Spaces.HkSq α k f + Work.Spaces.HkSq α k g) := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
        ≤ 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
            + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) := by
    intro z hz
    have hint : Integrable (fun θ : ℝ =>
        Work.Spaces.HkIntegrand α k f z θ + Work.Spaces.HkIntegrand α k g z θ)
        (volume.restrict Work.Spaces.Iθ) := ((hmf.1 z hz).add (hmg.1 z hz))
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
      (g := fun θ => 2 * (Work.Spaces.HkIntegrand α k f z θ
        + Work.Spaces.HkIntegrand α k g z θ))
      (Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k (fun z θ => f z θ + g z θ) z θ)
      (hint.const_mul _)
      (ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => HkIntegrand_add_le_open α k hα hf hg z hz θ hθ))
    refine hmono.trans_eq ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add (hmf.1 z hz) (hmg.1 z hz)]
  rw [Work.Spaces.HkSq]
  have houter := MeasureTheory.integral_mono_of_nonneg
    (μ := volume.restrict Work.Spaces.Iz)
    (f := fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
    (g := fun z => 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ))
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α k (fun z θ => f z θ + g z θ) z θ)
    ((hmf.2.add hmg.2).const_mul _)
    (ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  refine houter.trans_eq ?_
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hmf.2 hmg.2,
    Work.Spaces.HkSq, Work.Spaces.HkSq]

/-- **The `ℋ^k`-norm is subadditive on the open class** (two terms), with the factor `2` — the
`√(2²)` of the general finite-sum statement `HkNorm_finset_sum_le`. -/
theorem HkNorm_add_le_open (α : ℝ) (k : ℕ) (hα : 0 < α) {f g : ℝ → ℝ → ℝ}
    (hf : SmoothOpen f) (hg : SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ)
      ≤ 2 * (Work.Spaces.HkNorm α k f + Work.Spaces.HkNorm α k g) := by
  have hSq := HkSq_add_le_open α k hα hf hg hmf hmg
  have h1 : Work.Spaces.HkSq α k f = (Work.Spaces.HkNorm α k f) ^ 2 := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k f)]
  have h2 : Work.Spaces.HkSq α k g = (Work.Spaces.HkNorm α k g) ^ 2 := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k g)]
  have hf0 : 0 ≤ Work.Spaces.HkNorm α k f := Work.Spaces.HkNorm_nonneg α k f
  have hg0 : 0 ≤ Work.Spaces.HkNorm α k g := Work.Spaces.HkNorm_nonneg α k g
  have hroot : Real.sqrt 2 ≤ 2 := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    calc Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      _ = 2 := h4
  calc Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ)
      = Real.sqrt (Work.Spaces.HkSq α k (fun z θ => f z θ + g z θ)) := rfl
    _ ≤ Real.sqrt (2 * (Work.Spaces.HkSq α k f + Work.Spaces.HkSq α k g)) := Real.sqrt_le_sqrt hSq
    _ = Real.sqrt 2 * Real.sqrt (Work.Spaces.HkSq α k f + Work.Spaces.HkSq α k g) :=
        Real.sqrt_mul (by norm_num) _
    _ = Real.sqrt 2 * Real.sqrt ((Work.Spaces.HkNorm α k f) ^ 2
          + (Work.Spaces.HkNorm α k g) ^ 2) := by rw [h1, h2]
    _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k f + Work.Spaces.HkNorm α k g) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        calc Real.sqrt ((Work.Spaces.HkNorm α k f) ^ 2 + (Work.Spaces.HkNorm α k g) ^ 2)
            ≤ Real.sqrt ((Work.Spaces.HkNorm α k f + Work.Spaces.HkNorm α k g) ^ 2) :=
              Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hf0 hg0])
          _ = |Work.Spaces.HkNorm α k f + Work.Spaces.HkNorm α k g| := Real.sqrt_sq_eq_abs _
          _ = Work.Spaces.HkNorm α k f + Work.Spaces.HkNorm α k g := abs_of_nonneg (by linarith)
    _ ≤ 2 * (Work.Spaces.HkNorm α k f + Work.Spaces.HkNorm α k g) :=
        mul_le_mul_of_nonneg_right hroot (by linarith)

/-- **The `ℋ^k`-energy is subadditive for finite sums.** -/
theorem HkSq_finset_sum_le (α : ℝ) (k : ℕ) (hα : 0 < α) {ι : Type*} (s : Finset ι)
    {f : ι → ℝ → ℝ → ℝ} (hf : ∀ i ∈ s, SmoothOpen (f i))
    (hm : ∀ i ∈ s, Work.Spaces.HkMem α k (f i)) :
    Work.Spaces.HkSq α k (fun z θ => ∑ i ∈ s, f i z θ)
      ≤ (2 : ℝ) ^ s.card * ∑ i ∈ s, Work.Spaces.HkSq α k (f i) := by
  classical
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => ∑ i ∈ s, f i z θ) z θ)
        ≤ (2 : ℝ) ^ s.card * ∑ i ∈ s,
            ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (f i) z θ := by
    intro z hz
    have hint : Integrable (fun θ : ℝ => ∑ i ∈ s, Work.Spaces.HkIntegrand α k (f i) z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      integrable_finsetSum s fun i hi => (hm i hi).1 z hz
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α k (fun z θ => ∑ i ∈ s, f i z θ) z θ)
      (g := fun θ => (2 : ℝ) ^ s.card * ∑ i ∈ s, Work.Spaces.HkIntegrand α k (f i) z θ)
      (Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k (fun z θ => ∑ i ∈ s, f i z θ) z θ)
      (hint.const_mul _)
      (ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => HkIntegrand_finset_sum_le α k hα s hf z hz θ hθ))
    refine hmono.trans_eq ?_
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum]
    exact fun i hi => (hm i hi).1 z hz
  rw [Work.Spaces.HkSq]
  have houter := MeasureTheory.integral_mono_of_nonneg
    (μ := volume.restrict Work.Spaces.Iz)
    (f := fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => ∑ i ∈ s, f i z θ) z θ)
    (g := fun z => (2 : ℝ) ^ s.card * ∑ i ∈ s,
      ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (f i) z θ)
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α k (fun z θ => ∑ i ∈ s, f i z θ) z θ)
    ((integrable_finsetSum s fun i hi => (hm i hi).2).const_mul _)
    (ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  refine houter.trans_eq ?_
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact MeasureTheory.integral_finsetSum s (fun i hi => (hm i hi).2)

/-- **The `ℋ^k`-norm is subadditive for finite sums**, with the `√(2^|s|)` loss. -/
theorem HkNorm_finset_sum_le (α : ℝ) (k : ℕ) (hα : 0 < α) {ι : Type*} (s : Finset ι)
    {f : ι → ℝ → ℝ → ℝ} (hf : ∀ i ∈ s, SmoothOpen (f i))
    (hm : ∀ i ∈ s, Work.Spaces.HkMem α k (f i)) :
    Work.Spaces.HkNorm α k (fun z θ => ∑ i ∈ s, f i z θ)
      ≤ Real.sqrt ((2 : ℝ) ^ s.card) * ∑ i ∈ s, Work.Spaces.HkNorm α k (f i) := by
  classical
  have hSq := HkSq_finset_sum_le α k hα s hf hm
  have hSqNorm : ∀ i ∈ s, Work.Spaces.HkSq α k (f i)
      = (Work.Spaces.HkNorm α k (f i)) ^ 2 := by
    intro i _
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k (f i))]
  have hsq : (∑ i ∈ s, Work.Spaces.HkSq α k (f i))
      ≤ (∑ i ∈ s, Work.Spaces.HkNorm α k (f i)) ^ 2 := by
    rw [Finset.sum_congr rfl hSqNorm]
    exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => Work.Spaces.HkNorm_nonneg α k (f i)
  have hsum0 : (0 : ℝ) ≤ ∑ i ∈ s, Work.Spaces.HkNorm α k (f i) :=
    Finset.sum_nonneg fun i _ => Work.Spaces.HkNorm_nonneg α k (f i)
  calc Work.Spaces.HkNorm α k (fun z θ => ∑ i ∈ s, f i z θ)
      = Real.sqrt (Work.Spaces.HkSq α k (fun z θ => ∑ i ∈ s, f i z θ)) := rfl
    _ ≤ Real.sqrt ((2 : ℝ) ^ s.card * ∑ i ∈ s, Work.Spaces.HkSq α k (f i)) :=
        Real.sqrt_le_sqrt hSq
    _ = Real.sqrt ((2 : ℝ) ^ s.card) * Real.sqrt (∑ i ∈ s, Work.Spaces.HkSq α k (f i)) :=
        Real.sqrt_mul (by positivity) _
    _ ≤ Real.sqrt ((2 : ℝ) ^ s.card) * ∑ i ∈ s, Work.Spaces.HkNorm α k (f i) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        calc Real.sqrt (∑ i ∈ s, Work.Spaces.HkSq α k (f i))
            ≤ Real.sqrt ((∑ i ∈ s, Work.Spaces.HkNorm α k (f i)) ^ 2) :=
              Real.sqrt_le_sqrt hsq
          _ = |∑ i ∈ s, Work.Spaces.HkNorm α k (f i)| := Real.sqrt_sq_eq_abs _
          _ = ∑ i ∈ s, Work.Spaces.HkNorm α k (f i) := abs_of_nonneg hsum0

end Work.FTS.GalFields.RHS
