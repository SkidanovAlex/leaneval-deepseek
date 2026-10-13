/-
  annals_wilkies_conjecture, AREA E3, count half: the gradient of a cut form.

  The cut form `cutPoly ι μ x = Σ_{i : U k ι} C (μ i) * (X i - C (x i))` is affine in the
  `ιᶜ`-coordinates, so its `eaD c i`-derivative is the constant `μ i` when `i ∉ Set.range ι` and `0`
  otherwise.  This is what makes the corresponding rows of the cut system constant, so that their
  common kernel (intersected with the kernel of the `h`-rows) can be computed by the linear algebra
  of `CutForms`.
-/
import Mathlib
import Submission.Work.WilE3.Frame.CutSys
import Submission.Work.WilE3.API.eaEvalC_fderiv_analytic
import Submission.Work.WilE3.API.eaD_commute

open Classical
open WilkiesDesign.E

namespace Work.WilE3.Frame

set_option autoImplicit false
noncomputable section

/-- **Gradient of a cut form.**  The symbolic derivative of `cutPoly ι μ x` in the coordinate `i` is
the constant `μ i` if `i ∉ Set.range ι`, and `0` if `i ∈ Set.range ι`; consequently the row
functional of the cut system carried by such a form is the constant vector
`v ↦ Σ_i (μ a) i * v i` (only the `ιᶜ`-coordinates occur). -/
theorem grad_cutPoly {k r j : ℕ} (c : EAChain k r) (ι : Fin j → Fin k)
    (μ : U k ι → ℝ) (x : Fin k → ℝ) (z : Fin k → ℂ) (i : Fin k) :
    Work.WilE3.eaEvalC c (eaD c i (cutPoly ι μ x)) z =
      if h : i ∈ Set.range ι then 0 else (μ ⟨i, h⟩ : ℂ) := by
  have hstep : ∀ i' : U k ι,
      eaD c i (MvPolynomial.C (μ i') *
          (MvPolynomial.X (Sum.inl i'.1) - MvPolynomial.C (x i'.1)))
        = if i = i'.1 then MvPolynomial.C (μ i') else 0 := by
    intro i'
    rw [Work.WilE3.API.eaD_mul, Work.WilE3.API.eaD_C, zero_mul, zero_add]
    have hsub : eaD c i (MvPolynomial.X (Sum.inl i'.1) - MvPolynomial.C (x i'.1))
        = eaD c i (MvPolynomial.X (Sum.inl i'.1)) - eaD c i (MvPolynomial.C (x i'.1)) := by
      rw [← Work.WilE3.API.eaDlin_apply, map_sub,
        Work.WilE3.API.eaDlin_apply, Work.WilE3.API.eaDlin_apply]
    rw [hsub, Work.WilE3.API.eaD_X_inl, Work.WilE3.API.eaD_C, sub_zero]
    by_cases h : i = i'.1 <;> simp [h]
  have hpoly : eaD c i (cutPoly ι μ x)
      = ∑ i' : U k ι, (if i = i'.1 then MvPolynomial.C (μ i') else (0 : EAPoly k r)) := by
    rw [cutPoly, ← Work.WilE3.API.eaDlin_apply, map_sum]
    exact Finset.sum_congr rfl fun i' _ => by
      rw [Work.WilE3.API.eaDlin_apply]; exact hstep i'
  have heval : ∀ (s : Finset (U k ι)) (f : U k ι → EAPoly k r),
      Work.WilE3.eaEvalC c (∑ i' ∈ s, f i') z = ∑ i' ∈ s, Work.WilE3.eaEvalC c (f i') z := by
    intro s f
    have key : ∀ Q : EAPoly k r, Work.WilE3.eaEvalC c Q z
        = MvPolynomial.eval₂Hom (algebraMap ℝ ℂ)
            (Sum.elim z fun j => Complex.exp (∑ i : Fin k, (c.a j i : ℂ) * z i + (c.b j : ℂ))) Q :=
      fun Q => rfl
    simp only [key]
    exact map_sum (MvPolynomial.eval₂Hom (algebraMap ℝ ℂ)
      (Sum.elim z fun j => Complex.exp (∑ i : Fin k, (c.a j i : ℂ) * z i + (c.b j : ℂ)))) f s
  rw [hpoly]
  rw [heval Finset.univ (fun i' => if i = i'.1 then MvPolynomial.C (μ i') else (0 : EAPoly k r))]
  by_cases h : i ∈ Set.range ι
  · rw [dif_pos h]
    refine Finset.sum_eq_zero fun i' _ => ?_
    have hne : ¬ (i = i'.1) := fun he => i'.2 (he ▸ h)
    simp [hne, Work.WilE3.API.eaEvalC_zero]
  · rw [dif_neg h]
    rw [Finset.sum_eq_single (⟨i, h⟩ : U k ι)]
    · simp [Work.WilE3.API.eaEvalC_C]
    · intro b _ hb
      have hne : ¬ (i = b.1) := fun he => hb (Subtype.ext he.symm)
      simp [hne, Work.WilE3.API.eaEvalC_zero]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem

end

end Work.WilE3.Frame
