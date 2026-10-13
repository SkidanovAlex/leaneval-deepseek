import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Construction.Defs
import Submission.Work.Blocks.HkMul_ang_le
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.Nonlinear.N4Fields.angmul_field_smoothInt
import Submission.Work.FTS.Nonlinear.N4Fields.AngSmoothIntHelpers
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! # Multiplication by the bounded angular profile `c₂(θ) = cos 2θ - sin²θ`

The target `c2m_mul_HkSq_le` says that multiplication by the bounded angular profile
`Work.Construction.c2m` does not raise the weighted `ℋ³`-order: for `g` of class `C^∞` on the
open quadrant with `HkMem α 3 g`,

`HkMem α 3 (c₂ · g)` and `HkSq α 3 (c₂ · g) ≤ C · HkSq α 3 g`

with a constant `C` universal in `α ∈ (0,1]`.

The proof goes through the *general* angular-multiplication estimate `ang_mul_HkSq_le` below:
for an arbitrary profile `a : ℝ → ℝ` which is `C^∞` on `Q₀`, bounded by `B` on `Iθ` and whose
`D_θ`-iterates decay like `B · sin 2θ`, multiplication by `a` is honest and costs `C · B ^ 2`.

* The pointwise estimate on the open quadrant is the already-proved unit-profile inequality
  `Work.FTS.Nonlinear.N4Fields.HkIntegrand_ang_mul_unit_le_Int` (constant `1` on the profile);
  the general profile is reached by the rescaling `a = B · (a / B)` (`HkIntegrand_const_mul`
  contributes the factor `B ^ 2`) combined with `LopIter_const_mul` for the `D_θ`-iterates.
* It is extended to the closed quadrant by `Work.FTS.Nonlinear.N4Fields.closed_of_interior`.
* Integration is `Work.FTS.Nonlinear.N4Fields.HkSq_le_of_integrand_le` (`HkSq`) together with
  `Work.FTS.LocData.HkMem_of_majorant` (`HkMem`), the continuity hypothesis being supplied by
  `Work.FTS.Nonlinear.N4Fields.smoothOpen_angMul_On`.

The profile `c₂` is then fed in with `B = 1000`: `|c₂| ≤ 2` on `Iθ`
(`Work.FTS.Nonlinear.Pieces.abs_c2m_le_two`) and `|D_θ^i c₂| ≤ 1000 · sin(2θ)² ≤ 1000 · sin 2θ`
(`Work.FTS.Nonlinear.Pieces.DthIter_c2m_le`). -/

/-- **Angular multiplication in `ℋ^k`.**  There is a universal constant `C` such that for every
`α ∈ (0,1]`, every profile `a : ℝ → ℝ` which is `C^∞` on the open quadrant, bounded by
`B > 0` on `Iθ` with `D_θ`-iterates bounded by `B · sin 2θ`, and every `g` of class `C^∞` on the
open quadrant with `HkMem α k g`, the product `a · g` is honest and

`HkSq α k (a · g) ≤ C · B ^ 2 · HkSq α k g`.

(`HkIntegrand α k (a · g) ≤ C · B ^ 2 · HkIntegrand α k g` pointwise on the closed quadrant, in
fact.) -/
theorem ang_mul_HkSq_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (a : ℝ → ℝ) (B : ℝ), 0 < B →
      Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
      (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B) →
      (∀ i : ℕ, 1 ≤ i → i ≤ k → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B * Real.sin (2 * θ)) →
      ∀ f : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α k f →
      Work.Spaces.HkMem α k (fun z θ => a θ * f z θ) ∧
      Work.Spaces.HkSq α k (fun z θ => a θ * f z θ) ≤ C * B ^ 2 * Work.Spaces.HkSq α k f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.Nonlinear.N4Fields.HkIntegrand_ang_mul_unit_le_Int k
  refine ⟨C₁, hC₁pos, ?_⟩
  intro α hα0 hα1 a B hBpos hSO haB haIt f hf hmem
  have hCD : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2)
      Work.FTS.EllipticEst.Q0 := hSO
  have hBne : B ≠ 0 := hBpos.ne'
  -- the rescaled profile
  set a' : ℝ → ℝ := fun θ => a θ / B with ha'def
  have hCD' : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a' p.2)
      Work.FTS.EllipticEst.Q0 := by
    have h := hCD.div_const B
    simpa only [ha'def] using h
  have ha'1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |a' θ| ≤ 1 := by
    intro θ hθ
    have h1 := haB θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have h2 : |a' θ| = |a θ| / B := by rw [ha'def, abs_div, abs_of_pos hBpos]
    rw [h2]
    exact (div_le_one hBpos).mpr h1
  have ha'It : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.FTS.EllipticEst.LopIter m a' θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ 2 := by
    intro m hm1 hmk θ hθ
    have hlin : ∀ θ' : ℝ, Work.FTS.EllipticEst.LopIter m a' θ'
        = B⁻¹ * Work.FTS.EllipticEst.LopIter m a θ' := by
      have h1 : a' = fun θ => B⁻¹ * a θ := by
        funext θ'; rw [ha'def]; field_simp
      intro θ'
      rw [h1, congrFun (Work.FTS.EllipticEst.Blocks.LopIter_const_mul B⁻¹ m a) θ']
    have hbound : |Work.FTS.EllipticEst.LopIter m a θ| ≤ B * Real.sin (2 * θ) := by
      have h2 : Work.FTS.EllipticEst.LopIter m a θ
          = Work.Spaces.DthIter m (fun _ (θ' : ℝ) => a θ') 0 θ := by
        rw [Work.Spaces.DthIter_eq_iterate_Lop]
        rfl
      rw [h2]
      exact haIt m hm1 hmk θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsq : (Work.FTS.EllipticEst.LopIter m a θ) ^ 2
        ≤ (B * Real.sin (2 * θ)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hbound 2
    rw [hlin θ]
    calc (B⁻¹ * Work.FTS.EllipticEst.LopIter m a θ) ^ 2
        = B⁻¹ ^ 2 * (Work.FTS.EllipticEst.LopIter m a θ) ^ 2 := by ring
      _ ≤ B⁻¹ ^ 2 * (B * Real.sin (2 * θ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = (Real.sin (2 * θ)) ^ 2 := by
          have hBB : B⁻¹ ^ 2 * B ^ 2 = 1 := by
            rw [← mul_pow, inv_mul_cancel₀ hBne, one_pow]
          rw [mul_pow, ← mul_assoc, hBB, one_mul]
  -- the pointwise bound on the closed quadrant
  have hclosed := Work.FTS.Nonlinear.N4Fields.closed_of_interior (k := k) (a := a') (C := C₁)
    (fun α' f' hα' hα'1 hf' => hC₁ a' ha'1 hCD' ha'It α' f' hα' hα'1 hf') α f hα0 hα1 hf
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => a θ * f z θ) z θ
        ≤ (B ^ 2 * C₁) * Work.Spaces.HkIntegrand α k f z θ := by
    intro z hz θ hθ
    have hrew : (fun z θ => a θ * f z θ) = fun z θ => B * (a' θ * f z θ) := by
      funext z' θ'
      have hBmul : B * (a θ' / B) = a θ' := by
        rw [mul_comm]; exact div_mul_cancel₀ (a θ') hBne
      rw [ha'def]
      calc a θ' * f z' θ' = (B * (a θ' / B)) * f z' θ' := by rw [hBmul]
        _ = B * (a θ' / B * f z' θ') := by ring
    have hconst : Work.Spaces.HkIntegrand α k (fun z θ => B * (a' θ * f z θ)) z θ
        = B ^ 2 * Work.Spaces.HkIntegrand α k (fun z θ => a' θ * f z θ) z θ :=
      Work.FTS.LocData.HkIntegrand_const_mul α k B (fun z θ => a' θ * f z θ) z θ
    rw [hrew, hconst]
    calc B ^ 2 * Work.Spaces.HkIntegrand α k (fun z θ => a' θ * f z θ) z θ
        ≤ B ^ 2 * (C₁ * Work.Spaces.HkIntegrand α k f z θ) :=
          mul_le_mul_of_nonneg_left (hclosed z hz θ hθ) (sq_nonneg B)
      _ = (B ^ 2 * C₁) * Work.Spaces.HkIntegrand α k f z θ := by ring
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α k (fun z θ => a θ * f z θ) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.Nonlinear.N4Fields.smoothOpen_angMul_On hCD hf).continuousOn_HkIntegrand α k
  have hmem' : Work.Spaces.HkMem α k (fun z θ => a θ * f z θ) := by
    refine Work.FTS.LocData.HkMem_of_majorant α k hcont ?_ ?_ hpt
    · intro z hz
      exact (hmem.1 z hz).const_mul (B ^ 2 * C₁)
    · have h2 := hmem.2.const_mul (B ^ 2 * C₁)
      have heq : (fun z => ∫ θ in Work.Spaces.Iθ,
            (B ^ 2 * C₁) * Work.Spaces.HkIntegrand α k f z θ)
          = fun z => (B ^ 2 * C₁) * ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k f z θ := by
        funext z
        rw [MeasureTheory.integral_const_mul]
      rw [heq]
      exact h2
  refine ⟨hmem', ?_⟩
  have hsq := Work.FTS.Nonlinear.N4Fields.HkSq_le_of_integrand_le α k (B ^ 2 * C₁) hmem hpt
  calc Work.Spaces.HkSq α k (fun z θ => a θ * f z θ)
      ≤ (B ^ 2 * C₁) * Work.Spaces.HkSq α k f := hsq
    _ = C₁ * B ^ 2 * Work.Spaces.HkSq α k f := by ring

/-! ## The profile hypotheses for `c₂` -/

/-- `c₂` is `C^∞` on the open quadrant (as a constant-in-`z` profile). -/
private theorem contDiffOn_c2m_snd :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Work.Construction.c2m p.2)
      Work.FTS.EllipticEst.Q0 := by
  have h1 : ContDiff ℝ ⊤ (fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2) :=
    (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).sub
      ((Real.contDiff_sin).pow 2)
  have h2 : ContDiff ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2) := h1.of_le le_top
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2) Set.univ := h2.contDiffOn
  have h4 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos (2 * p.2) - Real.sin p.2 ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    h3.comp contDiffOn_snd (fun p _ => Set.mem_univ p.2)
  have hfun : (fun p : ℝ × ℝ => Real.cos (2 * p.2) - Real.sin p.2 ^ 2)
      = fun p : ℝ × ℝ => Work.Construction.c2m p.2 := by
    funext p
    rw [Work.Construction.c2m_eq]
  rwa [hfun] at h4

/-- `|c₂| ≤ 1000` on `Iθ`. -/
private theorem c2m_abs_le (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.c2m θ| ≤ 1000 := by
  have h := Work.FTS.Nonlinear.Pieces.abs_c2m_le_two hθ
  linarith

/-- `|D_θ^i c₂| ≤ 1000 · sin 2θ` on `Iθ`, for `1 ≤ i ≤ 3`. -/
private theorem c2m_dthIter_le (i : ℕ) (hi : 1 ≤ i) (hi3 : i ≤ 3) (θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
      ≤ 1000 * Real.sin (2 * θ) := by
  have h := Work.FTS.Nonlinear.Pieces.DthIter_c2m_le i hi (by omega) θ
  rw [show (Real.sin (2 * θ)) ^ (2 : ℝ) = (Real.sin (2 * θ)) ^ (2 : ℕ) from
    Real.rpow_natCast _ 2] at h
  have h0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsq : Real.sin (2 * θ) ^ 2 ≤ Real.sin (2 * θ) := by nlinarith
  calc |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
      ≤ 1000 * Real.sin (2 * θ) ^ 2 := h
    _ ≤ 1000 * Real.sin (2 * θ) := by linarith

/-! ## The target -/

theorem c2m_mul_HkSq_le : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ g : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 3 g →
      Work.Spaces.HkMem α 3 (fun z θ => Work.Construction.c2m θ * g z θ) ∧
      Work.Spaces.HkSq α 3 (fun z θ => Work.Construction.c2m θ * g z θ)
        ≤ C * Work.Spaces.HkSq α 3 g := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := ang_mul_HkSq_le 3
  refine ⟨C₁ * 1000 ^ 2, by positivity, ?_⟩
  intro α hα g hg hmem
  have hSOc : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Construction.c2m θ) :=
    contDiffOn_c2m_snd
  obtain ⟨hmem', hsq⟩ := hC₁ α hα.1 hα.2 (fun θ => Work.Construction.c2m θ) 1000
    (by norm_num) hSOc c2m_abs_le c2m_dthIter_le g hg hmem
  exact ⟨hmem', hsq⟩

end Work.FTS.StrongPersist.L3Rhs
