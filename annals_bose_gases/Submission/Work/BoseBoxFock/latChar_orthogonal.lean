import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseBoxFock.LatFourierDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Orthogonality of the lattice characters on the fundamental cell

`Work.BoseBoxFock.latChar_orthogonal`: for `0 < ℓ` and `j : Fin 3 → ℤ`, the character
`z ↦ e^{i⟪kmomInt ℓ j, z⟫}` integrates over the half-open fundamental cell `[0,ℓ)³` to `ℓ³`
if `j = 0` and to `0` otherwise.

The proof passes to the product measure on `Fin 3 → ℝ` through the volume preserving
equivalence `MeasurableEquiv.toLp 2 (Fin 3 → ℝ)`, uses Fubini in three variables
(`MeasureTheory.integral_fintype_prod_eq_prod`), and reduces to the elementary one-dimensional
integral `∫ t in Set.Ico 0 ℓ, e^{i c t}`, which equals `ℓ` when `c = 0` and vanishes when
`c * ℓ` is a nonzero integer multiple of `2π` (so that `e^{i c ℓ} = 1`).
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The one-dimensional lattice integral: if `c * ℓ` is an integer multiple of `2π`, then
`∫ t in [0,ℓ), e^{i c t}` equals `ℓ` when the multiple is `0` and `0` otherwise. -/
lemma integral_Ico_exp_I_mul {ℓ : ℝ} (hℓ : 0 < ℓ) {c : ℝ} {m : ℤ}
    (hcm : c * ℓ = 2 * Real.pi * m) :
    ∫ t in Set.Ico 0 ℓ, Complex.exp (Complex.I * ((c * t : ℝ) : ℂ))
      = if m = 0 then (ℓ : ℂ) else 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · have hc : c = 0 := by
      have h : c * ℓ = 0 := by simp [hcm]
      exact (mul_eq_zero.mp h).resolve_right hℓ.ne'
    subst hc
    simp only [zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [MeasureTheory.setIntegral_const]
    have hv : (volume : Measure ℝ).real (Set.Ico 0 ℓ) = ℓ := by
      rw [MeasureTheory.Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [hv]
    simp
  · have hc : c ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hcm
      have h2 : ((m : ℝ)) = 0 := (mul_eq_zero.mp hcm.symm).resolve_left (by positivity)
      exact hm (by exact_mod_cast h2)
    have hmain : ∫ t in Set.Ico 0 ℓ, Complex.exp (Complex.I * ((c * t : ℝ) : ℂ)) = 0 := by
      rw [MeasureTheory.integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hℓ.le]
      have hfun : (fun t : ℝ => Complex.exp (Complex.I * ((c * t : ℝ) : ℂ)))
          = fun t : ℝ => Complex.exp ((Complex.I * (c : ℂ)) * t) := by
        funext t; congr 1; push_cast; ring
      rw [hfun, integral_exp_mul_complex]
      · have h1 : Complex.exp ((Complex.I * (c : ℂ)) * ℓ) = 1 := by
          rw [show (Complex.I * (c:ℂ)) * (ℓ:ℂ) = Complex.I * ((c * ℓ : ℝ) : ℂ) by
            push_cast; ring]
          rw [hcm]
          have h3 : Complex.I * (((2 * Real.pi) * (m:ℝ) : ℝ) : ℂ)
              = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
          rw [h3, Complex.exp_int_mul_two_pi_mul_I]
        rw [h1]
        simp
      · exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hc)
    rw [if_neg hm]
    simpa only [Complex.ofReal_mul] using hmain

theorem latChar_orthogonal {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin 3 → ℤ) :
    ∫ z in Work.BoseBoxFock.LatFourier.latCell ℓ,
        Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ j) z : ℝ) : ℂ))
      = if j = 0 then ((ℓ ^ 3 : ℝ) : ℂ) else 0 := by
  classical
  set g : Fin 3 → ℝ → ℂ := fun i t =>
    Complex.exp (Complex.I * (((kmomInt ℓ j).ofLp i * t : ℝ) : ℂ)) with hg
  set F : E3 → ℂ := fun z => Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ j) z : ℝ) : ℂ)) with hF
  -- the volume preserving measurable equivalence identifying the cell with a product of intervals
  have hmp : MeasurePreserving (⇑(MeasurableEquiv.toLp 2 (Fin 3 → ℝ)))
      (volume : Measure (Fin 3 → ℝ)) (volume : Measure E3) := by
    rw [MeasurableEquiv.coe_toLp]
    exact PiLp.volume_preserving_toLp (Fin 3)
  have hpre : (⇑(MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) : (Fin 3 → ℝ) → E3) ⁻¹'
      LatFourier.latCell ℓ = Set.pi Set.univ (fun _ : Fin 3 => Set.Ico (0:ℝ) ℓ) := by
    ext x
    simp [LatFourier.latCell, MeasurableEquiv.coe_toLp]
  -- the inner product expands into a sum of coordinate contributions
  have hinner : ∀ x : Fin 3 → ℝ, inner ℝ (kmomInt ℓ j)
      ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ) : (Fin 3 → ℝ) ≃ᵐ E3) x)
      = ∑ i, (kmomInt ℓ j).ofLp i * x i := by
    intro x
    rw [MeasurableEquiv.coe_toLp, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    show inner ℝ ((kmomInt ℓ j).ofLp i) ((WithLp.toLp 2 x).ofLp i) = _
    rw [Real.inner_apply, WithLp.ofLp_toLp]
  -- the character factors as a product of the coordinate characters
  have hprod : ∀ x : Fin 3 → ℝ,
      F ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ) : (Fin 3 → ℝ) ≃ᵐ E3) x) = ∏ i, g i (x i) := by
    intro x
    simp only [hF, hg]
    rw [hinner x]
    have h : Complex.I * ↑(∑ i, (kmomInt ℓ j).ofLp i * x i)
        = ∑ i, Complex.I * ↑((kmomInt ℓ j).ofLp i * x i) := by
      push_cast; rw [Finset.mul_sum]
    rw [h, Complex.exp_sum]
  -- each coordinate frequency is an integer multiple of `2π / ℓ`
  have hcoef : ∀ i : Fin 3, (kmomInt ℓ j).ofLp i * ℓ = 2 * Real.pi * (j i : ℝ) := by
    intro i
    rw [LatFourier.kmomInt_eq_smul_latVec]
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    rw [show (latVec j).ofLp i = (j i : ℝ) from by simp [latVec]]
    field_simp
  -- transport the integral to the product of intervals
  rw [← hmp.setIntegral_preimage_emb (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
    F (LatFourier.latCell ℓ), hpre]
  rw [show (∫ x in Set.pi Set.univ (fun _ : Fin 3 => Set.Ico (0:ℝ) ℓ),
        F ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ) : (Fin 3 → ℝ) ≃ᵐ E3) x))
      = ∫ x, F ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ) : (Fin 3 → ℝ) ≃ᵐ E3) x)
          ∂((volume : Measure (Fin 3 → ℝ)).restrict
            (Set.pi Set.univ (fun _ : Fin 3 => Set.Ico (0:ℝ) ℓ))) from rfl]
  rw [show ((volume : Measure (Fin 3 → ℝ)).restrict
        (Set.pi Set.univ (fun _ : Fin 3 => Set.Ico (0:ℝ) ℓ)))
      = Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ).restrict (Set.Ico (0:ℝ) ℓ)) from by
    rw [show (volume : Measure (Fin 3 → ℝ))
        = Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ)) from rfl]
    rw [MeasureTheory.Measure.restrict_pi_pi]]
  rw [show (∫ x, F ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ) : (Fin 3 → ℝ) ≃ᵐ E3) x)
          ∂(Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ).restrict (Set.Ico (0:ℝ) ℓ))))
      = ∫ x, ∏ i, g i (x i)
          ∂(Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ).restrict (Set.Ico (0:ℝ) ℓ))) from
    integral_congr_ae (Filter.Eventually.of_forall (fun x => hprod x))]
  -- Fubini in the three coordinates
  have hfinal : (∫ x, ∏ i, g i (x i)
        ∂(Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ).restrict (Set.Ico (0:ℝ) ℓ))))
      = ∏ i : Fin 3, ∫ t in Set.Ico (0:ℝ) ℓ, g i t :=
    MeasureTheory.integral_fintype_prod_eq_prod (𝕜 := ℂ) (E := fun _ : Fin 3 => ℝ)
      (μ := fun _ : Fin 3 => (volume : Measure ℝ).restrict (Set.Ico (0:ℝ) ℓ)) g
  rw [hfinal]
  have hfac : (∏ i : Fin 3, ∫ t in Set.Ico (0:ℝ) ℓ, g i t)
      = ∏ i : Fin 3, (if j i = 0 then (ℓ : ℂ) else 0) := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [hg]
    exact integral_Ico_exp_I_mul hℓ (hcoef i)
  rw [hfac]
  by_cases hj : j = 0
  · subst hj
    simp [Finset.prod_const, Complex.ofReal_pow]
  · obtain ⟨i, hi⟩ : ∃ i, j i ≠ 0 := by
      by_contra h
      exact hj (funext fun i => by
        by_contra hi
        exact h ⟨i, hi⟩)
    rw [if_neg hj, Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)]

end Work.BoseBoxFock
