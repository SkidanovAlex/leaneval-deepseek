/-
# `Work.FTS.OpenPkg.angmul_field` — angular multiplication in `ℋ⁴`, open-quadrant class

The field `angmul` of the migrated interface `Work.FTS.OpenPkg.N4Norm'`: multiplication of an
`ℋ⁴`-function by an angular profile is honest and norm-bounded, with a *universal* constant.

The hypothesis on the profile is
`Work.FTS.EllipticEst.SmoothOpen (fun _ θ => a θ)`, i.e. the uncurried profile
`(z, θ) ↦ a θ` is `C^∞` (in the honest sense `Work.Stability.smoothOrder`) on the *open*
quadrant `Q0 = (0,∞) × (0,π/2)`.  This is the open-quadrant counterpart of the `SmoothInt`
hypothesis of `Work.FTS.Nonlinear.N4Fields.angmul_field_smoothInt`; the latter is *stronger*
for such a `z`-independent profile (`Function.uncurry (fun _ θ => a θ) = fun p => a p.2`, and
`SmoothInt` demands analyticity on the strip plus the `z`-slice condition), while the estimates
only ever consume `C^∞`-on-`Q0` of `fun p => a p.2`.

The proof is the proof of `angmul_field_smoothInt` verbatim:

* the pointwise bound on the open quadrant is
  `Work.FTS.Nonlinear.N4Fields.HkIntegrand_ang_mul_unit_le_Int` (the *unit* profile rescaling);
* the rescaling `a = Ca · a'` with `a' = a / Ca` transfers it to the profile `a`, where
  `0 ≤ Ca` is *derived* from the hypothesis `∀ θ ∈ Iθ, |a θ| ≤ Ca` (`Iθ` is nonempty);
* `closed_of_interior` extends the pointwise bound to the closed quadrant and
  `HkMem_of_majorant` + `HkSq_le_of_integrand_le` integrate it, giving the norm bound.

The file is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.Nonlinear.N4Fields.angmul_field_smoothInt
import Submission.Work.FTS.Nonlinear.N4Fields.AngSmoothIntHelpers

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem angmul_field :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (a : ℝ → ℝ) (f : Work.FTS.Galerkin.Fn) (Ca : ℝ),
      Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
      (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ca) →
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ca * Real.sin (2 * θ)) →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Spaces.HkMem α 4 (fun z θ => a θ * f z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => a θ * f z θ) ≤ C * Ca * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.Nonlinear.N4Fields.HkIntegrand_ang_mul_unit_le_Int 4
  refine ⟨1 + Real.sqrt C₁, by positivity, ?_⟩
  intro α hα0 hα1 a f Ca hSO haB haIt hf hmem
  -- the profile hypothesis is `C^∞`-on-`Q0` of the uncurried profile
  have hCD : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2)
      Work.FTS.EllipticEst.Q0 := hSO
  -- the bound `|a θ| ≤ Ca` for the nonempty `Iθ` forces `0 ≤ Ca`
  have hCa : 0 ≤ Ca := le_trans (abs_nonneg (a 0)) (haB 0 Work.Spaces.zero_mem_Iθ)
  rcases eq_or_lt_of_le hCa with hCa0 | hCapos
  · -- ## `Ca = 0`: the profile vanishes on `Iθ`
    have ha0 : ∀ θ ∈ Work.Spaces.Iθ, a θ = 0 := by
      intro θ hθ
      have h1 := haB θ hθ
      rw [← hCa0] at h1
      exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    have hzero : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
        Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * f z θ) z θ = 0 := by
      intro z θ hθ
      rw [Work.Spaces.HkIntegrand]
      have h1 : (∑ i ∈ Finset.range (4 + 1),
          (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        simp only [Work.FTS.EllipticEst.Blocks.DzIter_angular_mul i a f]
        simp [ha0 θ hθ]
      have h2 : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
          if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0) = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        split_ifs with hc
        · rw [Work.Spaces.mixed]
          rw [Work.Coercivity.DzIter_eq_zero_of_forall_eq_zero
            (Work.Spaces.DthIter i (fun z θ => a θ * f z θ)) θ
            (fun z' => Work.FTS.Nonlinear.N4Fields.DthIter_angmul_eq_zero a f ha0 i hc.1 z' θ hθ)
            j z,
            zero_mul, sq, mul_zero]
        · rfl
      rw [h1, h2, add_zero]
    have hmem' : Work.Spaces.HkMem α 4 (fun z θ => a θ * f z θ) := by
      refine Work.FTS.LocData.HkMem_of_majorant (M := fun _ _ => (0 : ℝ)) α 4 ?_ ?_ ?_ ?_
      · have h0 : ContinuousOn (fun _ : ℝ × ℝ => (0 : ℝ)) Work.FTS.EllipticEst.Q0 :=
          continuousOn_const
        refine h0.congr ?_
        intro p hp
        exact hzero p.1 p.2 ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩
      · intro z hz; exact integrableOn_zero
      · have hthis : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (fun _ _ => (0 : ℝ)) z θ)
            = fun _ => (0 : ℝ) := by
          funext z; simp
        rw [hthis]
        exact integrableOn_zero
      · intro z hz θ hθ; rw [hzero z θ hθ]
    refine ⟨hmem', ?_⟩
    have hsq : Work.Spaces.HkSq α 4 (fun z θ => a θ * f z θ) = 0 := by
      rw [Work.Spaces.HkSq]
      have hinner : ∀ z : ℝ,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * f z θ) z θ)
            = 0 := by
        intro z
        rw [MeasureTheory.integral_eq_zero_of_ae]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => hzero z θ hθ)
      simp only [hinner, integral_zero]
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, hsq, Real.sqrt_zero, ← hCa0]
    simp
  · -- ## `Ca > 0`: rescale to `a' = a / Ca` and use the uniform unit bound
    set a' : ℝ → ℝ := fun θ => a θ / Ca with ha'def
    have hCane : Ca ≠ 0 := hCapos.ne'
    have ha'CD : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a' p.2)
        Work.FTS.EllipticEst.Q0 := by
      have h := hCD.div_const Ca
      simpa only [ha'def] using h
    have ha'1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |a' θ| ≤ 1 := by
      intro θ hθ
      have h1 := haB θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have h2 : |a' θ| = |a θ| / Ca := by
        rw [ha'def, abs_div, abs_of_pos hCapos]
      rw [h2]
      exact (div_le_one hCapos).mpr h1
    have ha'It : ∀ m : ℕ, 1 ≤ m → m ≤ 4 → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (Work.FTS.EllipticEst.LopIter m a' θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ 2 := by
      intro m hm1 hm4 θ hθ
      -- the `Lop`-iterate of the rescaled profile
      have hlin : ∀ θ' : ℝ,
          Work.FTS.EllipticEst.LopIter m a' θ'
            = Ca⁻¹ * Work.FTS.EllipticEst.LopIter m a θ' := by
        have h1 : a' = fun θ => Ca⁻¹ * a θ := by
          funext θ'; rw [ha'def]; field_simp
        intro θ'
        rw [h1, congrFun (Work.FTS.EllipticEst.Blocks.LopIter_const_mul Ca⁻¹ m a) θ']
      -- the interface hypothesis, in `Lop`-form
      have hbound : |Work.FTS.EllipticEst.LopIter m a θ| ≤ Ca * Real.sin (2 * θ) := by
        have h2 : Work.FTS.EllipticEst.LopIter m a θ
            = Work.Spaces.DthIter m (fun _ (θ' : ℝ) => a θ') 0 θ := by
          rw [Work.Spaces.DthIter_eq_iterate_Lop]
          rfl
        rw [h2]
        exact haIt m hm1 hm4 θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hsq : (Work.FTS.EllipticEst.LopIter m a θ) ^ 2
          ≤ (Ca * Real.sin (2 * θ)) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hbound 2
      rw [hlin θ]
      calc (Ca⁻¹ * Work.FTS.EllipticEst.LopIter m a θ) ^ 2
          = Ca⁻¹ ^ 2 * (Work.FTS.EllipticEst.LopIter m a θ) ^ 2 := by ring
        _ ≤ Ca⁻¹ ^ 2 * (Ca * Real.sin (2 * θ)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
        _ = (Real.sin (2 * θ)) ^ 2 := by
            field_simp
    -- the pointwise bound for the rescaled profile, on the open then on the closed quadrant
    have hopen : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α 4 (fun z θ => a' θ * f z θ) z θ
          ≤ C₁ * Work.Spaces.HkIntegrand α 4 f z θ :=
      hC₁ a' ha'1 ha'CD ha'It α f hα0 hα1 hf
    have hclosed := Work.FTS.Nonlinear.N4Fields.closed_of_interior (k := 4) (a := a') (C := C₁)
      (fun α' f' hα' hα'1 hf' => hC₁ a' ha'1 ha'CD ha'It α' f' hα' hα'1 hf') α f hα0 hα1 hf
    -- transport back to `a·f = Ca · (a'·f)`
    have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * f z θ) z θ
          ≤ (Ca ^ 2 * C₁) * Work.Spaces.HkIntegrand α 4 f z θ := by
      intro z hz θ hθ
      have hrew : (fun z θ => a θ * f z θ) = fun z θ => Ca * (a' θ * f z θ) := by
        funext z' θ'
        have hCamul : Ca * (a θ' / Ca) = a θ' := by field_simp
        rw [ha'def]
        calc a θ' * f z' θ' = (Ca * (a θ' / Ca)) * f z' θ' := by rw [hCamul]
          _ = Ca * (a θ' / Ca * f z' θ') := by ring
      rw [hrew, Work.FTS.LocData.HkIntegrand_const_mul]
      calc Ca ^ 2 * Work.Spaces.HkIntegrand α 4 (fun z θ => a' θ * f z θ) z θ
          ≤ Ca ^ 2 * (C₁ * Work.Spaces.HkIntegrand α 4 f z θ) :=
            mul_le_mul_of_nonneg_left (hclosed z hz θ hθ) (sq_nonneg Ca)
        _ = (Ca ^ 2 * C₁) * Work.Spaces.HkIntegrand α 4 f z θ := by ring
    have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * f z θ) p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.Nonlinear.N4Fields.smoothOpen_angMul_On hCD hf).continuousOn_HkIntegrand α 4
    have hmem' : Work.Spaces.HkMem α 4 (fun z θ => a θ * f z θ) := by
      refine Work.FTS.LocData.HkMem_of_majorant α 4 hcont ?_ ?_ hpt
      · intro z hz
        exact (hmem.1 z hz).const_mul (Ca ^ 2 * C₁)
      · have h2 := hmem.2.const_mul (Ca ^ 2 * C₁)
        have heq : (fun z => ∫ θ in Work.Spaces.Iθ,
              (Ca ^ 2 * C₁) * Work.Spaces.HkIntegrand α 4 f z θ)
            = fun z => (Ca ^ 2 * C₁) * ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 4 f z θ := by
          funext z
          rw [MeasureTheory.integral_const_mul]
        rw [heq]
        exact h2
    have hsq : Work.Spaces.HkSq α 4 (fun z θ => a θ * f z θ)
        ≤ (Ca ^ 2 * C₁) * Work.Spaces.HkSq α 4 f :=
      Work.FTS.Nonlinear.N4Fields.HkSq_le_of_integrand_le α 4 (Ca ^ 2 * C₁) hmem hpt
    refine ⟨hmem', ?_⟩
    have hsqrt : Work.Spaces.HkNorm α 4 (fun z θ => a θ * f z θ)
        ≤ (Ca * Real.sqrt C₁) * Work.FTS.Nonlin.Xn α f := by
      have h1 : Real.sqrt (Ca ^ 2 * C₁) = Ca * Real.sqrt C₁ := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Ca ^ 2), Real.sqrt_sq_eq_abs,
          abs_of_nonneg hCa]
      have h2 : Work.FTS.Nonlin.Xn α f = Real.sqrt (Work.Spaces.HkSq α 4 f) := rfl
      rw [Work.Spaces.HkNorm, h2]
      calc Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => a θ * f z θ))
          ≤ Real.sqrt ((Ca ^ 2 * C₁) * Work.Spaces.HkSq α 4 f) := Real.sqrt_le_sqrt hsq
        _ = Real.sqrt (Ca ^ 2 * C₁) * Real.sqrt (Work.Spaces.HkSq α 4 f) :=
            Real.sqrt_mul (by positivity) (Work.Spaces.HkSq α 4 f)
        _ = (Ca * Real.sqrt C₁) * Real.sqrt (Work.Spaces.HkSq α 4 f) := by rw [h1]
    have hXnnn : 0 ≤ Work.FTS.Nonlin.Xn α f := by
      rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
      exact Real.sqrt_nonneg _
    calc Work.FTS.Nonlin.Xn α (fun z θ => a θ * f z θ)
        ≤ (Ca * Real.sqrt C₁) * Work.FTS.Nonlin.Xn α f := hsqrt
      _ ≤ (1 + Real.sqrt C₁) * Ca * Work.FTS.Nonlin.Xn α f := by
          refine mul_le_mul_of_nonneg_right ?_ hXnnn
          nlinarith [hCa, Real.sqrt_nonneg C₁]

end Work.FTS.OpenPkg
