import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.OpenPkg.angmul_field
import Submission.Work.FTS.StrongPersist.L3Rhs.c2m_mul_HkSq_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-! # `angmul6` — angular multiplication in `ℋ⁶`, with the `HkNorm`-shaped conclusion

Multiplication of an `ℋ⁶`-function by an angular profile `a : ℝ → ℝ` which is `C^∞` on the
open quadrant, bounded by `Ca` on `Iθ` and whose `D_θ`-iterates up to order `6` decay like
`Ca · sin 2θ`, is honest and costs `C · Ca` in the `ℋ⁶`-norm, with `C` universal in
`α ∈ (0,1]`.

The `HkSq`-form of this statement at every order `k` is
`Work.FTS.StrongPersist.L3Rhs.ang_mul_HkSq_le` (proved via the unit-profile pointwise bound
`Work.FTS.Nonlinear.N4Fields.HkIntegrand_ang_mul_unit_le_Int`, the rescaling `a = B · a'`,
`closed_of_interior`, `HkSq_le_of_integrand_le` and `HkMem_of_majorant`).  Here we

* feed it `k = 6` in the case `Ca > 0`, and take square roots (`HkNorm = √HkSq`), which is
  where the norm-shape `C · Ca` comes from (the squared estimate carries `Ca²`);
* dispose of the degenerate case `Ca = 0`: the hypothesis `|a θ| ≤ Ca = 0` on the nonempty
  `Iθ` forces `a` to vanish on `Iθ`, so `HkIntegrand` of `a · f` vanishes on `Iz ×ˢ Iθ`
  (the angular iterates are killed by `DthIter_angmul_eq_zero`) and both conjuncts collapse
  to `0`.
-/

theorem angmul6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    ∀ (a : ℝ → ℝ) (f : Work.FTS.Galerkin.Fn) (Ca : ℝ),
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
    (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ca) →
    (∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ca * Real.sin (2 * θ)) →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    Work.Spaces.HkMem α 6 (fun z θ => a θ * f z θ) ∧
    Work.Spaces.HkNorm α 6 (fun z θ => a θ * f z θ)
      ≤ C * Ca * Work.Spaces.HkNorm α 6 f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := L3Rhs.ang_mul_HkSq_le 6
  refine ⟨Real.sqrt C₁, Real.sqrt_pos.mpr hC₁pos, ?_⟩
  intro α hα0 hα1 a f Ca hSO haB haIt hf hmem
  -- the nonemptiness of `Iθ` forces `0 ≤ Ca`
  have hCa : 0 ≤ Ca := le_trans (abs_nonneg (a 0)) (haB 0 Work.Spaces.zero_mem_Iθ)
  rcases eq_or_lt_of_le hCa with hCa0 | hCapos
  · -- ## `Ca = 0`: the profile vanishes on `Iθ`
    have ha0 : ∀ θ ∈ Work.Spaces.Iθ, a θ = 0 := by
      intro θ hθ
      have h1 := haB θ hθ
      rw [← hCa0] at h1
      exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    have hzero : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
        Work.Spaces.HkIntegrand α 6 (fun z θ => a θ * f z θ) z θ = 0 := by
      intro z θ hθ
      rw [Work.Spaces.HkIntegrand]
      have h1 : (∑ i ∈ Finset.range (6 + 1),
          (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        simp only [Work.FTS.EllipticEst.Blocks.DzIter_angular_mul i a f]
        simp [ha0 θ hθ]
      have h2 : (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
          if 1 ≤ i ∧ i + j ≤ 6 then
            (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0) = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        split_ifs with hc
        · rw [Work.Spaces.mixed]
          rw [Work.Coercivity.DzIter_eq_zero_of_forall_eq_zero
            (Work.Spaces.DthIter i (fun z θ => a θ * f z θ)) θ
            (fun z' => Work.FTS.Nonlinear.N4Fields.DthIter_angmul_eq_zero a f ha0 i hc.1
              z' θ hθ)
            j z,
            zero_mul, sq, mul_zero]
        · rfl
      rw [h1, h2, add_zero]
    have hmem' : Work.Spaces.HkMem α 6 (fun z θ => a θ * f z θ) := by
      refine Work.FTS.LocData.HkMem_of_majorant (M := fun _ _ => (0 : ℝ)) α 6 ?_ ?_ ?_ ?_
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
    have hsq : Work.Spaces.HkSq α 6 (fun z θ => a θ * f z θ) = 0 := by
      rw [Work.Spaces.HkSq]
      have hinner : ∀ z : ℝ,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (fun z θ => a θ * f z θ) z θ)
            = 0 := by
        intro z
        rw [MeasureTheory.integral_eq_zero_of_ae]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => hzero z θ hθ)
      simp only [hinner, integral_zero]
    rw [Work.Spaces.HkNorm, hsq, Real.sqrt_zero, ← hCa0]
    simp
  · -- ## `Ca > 0`: the `HkSq`-estimate of `ang_mul_HkSq_le 6`, then take square roots
    obtain ⟨hmem', hsq⟩ := hC₁ α hα0 hα1 a Ca hCapos hSO haB haIt f hf hmem
    refine ⟨hmem', ?_⟩
    have hCnn : 0 ≤ C₁ * Ca ^ 2 := by positivity
    have h1 : Real.sqrt (C₁ * Ca ^ 2) = Real.sqrt C₁ * Ca := by
      rw [Real.sqrt_mul hC₁pos.le, Real.sqrt_sq_eq_abs, abs_of_nonneg hCa]
    calc Work.Spaces.HkNorm α 6 (fun z θ => a θ * f z θ)
        = Real.sqrt (Work.Spaces.HkSq α 6 (fun z θ => a θ * f z θ)) := rfl
      _ ≤ Real.sqrt (C₁ * Ca ^ 2 * Work.Spaces.HkSq α 6 f) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (C₁ * Ca ^ 2) * Real.sqrt (Work.Spaces.HkSq α 6 f) :=
            Real.sqrt_mul hCnn _
      _ = Real.sqrt C₁ * Ca * Work.Spaces.HkNorm α 6 f := by
            rw [h1, Work.Spaces.HkNorm]

end

end Work.FTS.StrongPersist
