import Mathlib
import Submission.Work.CKFinal.EngineDefs

/-!
# `strip_structure`

Given a holomorphic `f : ℍ → ℂ` annihilated by `(T-I)²` (i.e. `T2op f = 0`) with decay of `f`
along the two lines `Re τ = ±1/2`, the two "shift" functions

  `shiftB f τ = f (τ+1) - f τ`,   `shiftA f τ = f τ - τ (shiftB f τ)`

are both `1`-periodic and holomorphic, reconstruct `f` by `f = shiftA f + τ · shiftB f`, and
`shiftB f` inherits the decay of `f` along `Re τ = -1/2`.

The proof is elementary: `(T-I)²f = 0` says exactly that `shiftB f (τ+1) = shiftB f τ`, and the
periodicity of `shiftA`, the holomorphy of both shifts and the splitting of `f` are immediate
consequences of the definitions together with the holomorphy of `f`.  The final decay estimate
follows by applying the hypothesis on `f` at `τ` and at `τ+1`.
-/

noncomputable section

open UpperHalfPlane

namespace Work.CKFinal

theorem strip_structure (m : ℕ) (f : UpperHalfPlane → ℂ)
    (hT2 : ∀ τ : UpperHalfPlane, Work.Kernels.T2op f τ = 0)
    (hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f)
    (hline : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane, (τ.re = 1 / 2 ∨ τ.re = -1 / 2) →
      Y ≤ τ.im → ‖f τ‖ * Real.exp (2 * Real.pi * ((m : ℝ) - 1) * τ.im) ≤ ε) :
    (∀ τ : UpperHalfPlane, Work.CKFinal.shiftB f ((1 : ℝ) +ᵥ τ) = Work.CKFinal.shiftB f τ) ∧
    (∀ τ : UpperHalfPlane, Work.CKFinal.shiftA f ((1 : ℝ) +ᵥ τ) = Work.CKFinal.shiftA f τ) ∧
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (Work.CKFinal.shiftB f) ∧
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (Work.CKFinal.shiftA f) ∧
    (∀ τ : UpperHalfPlane, f τ = Work.CKFinal.shiftA f τ + (τ : ℂ) * Work.CKFinal.shiftB f τ) ∧
    (∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane, τ.re = -1 / 2 → Y ≤ τ.im →
      ‖Work.CKFinal.shiftB f τ‖ * Real.exp (2 * Real.pi * ((m : ℝ) - 1) * τ.im) ≤ ε) := by
  -- Periodicity of `shiftB`, which is exactly the equation `(T-I)² f = 0`.
  have hBper : ∀ τ : UpperHalfPlane, shiftB f ((1 : ℝ) +ᵥ τ) = shiftB f τ := by
    intro τ
    have h := hT2 τ
    simp only [Work.Kernels.T2op] at h
    unfold shiftB
    rw [← Work.Kernels.vadd_one_add_one]
    linear_combination h
  -- `τ ↦ f (τ+1)` is holomorphic.
  have hg : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => f ((1 : ℝ) +ᵥ τ)) := by
    rw [UpperHalfPlane.mdifferentiable_iff] at hhol ⊢
    have hmap : Set.MapsTo (fun z : ℂ => z + 1) {z | 0 < z.im} {z | 0 < z.im} := by
      intro z hz; simpa using hz
    have hcomp : DifferentiableOn ℂ (fun z => (f ∘ ofComplex) (z + 1)) {z | 0 < z.im} :=
      hhol.comp (differentiableOn_id.add_const 1) hmap
    refine hcomp.congr ?_
    intro z hz
    simp only [Function.comp_apply]
    congr 1
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_vadd, UpperHalfPlane.ofComplex_apply_of_im_pos hz,
        UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hz)]
    simp [add_comm]
  have hB : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (shiftB f) :=
    MDifferentiable.sub hg hhol
  have hA : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (shiftA f) := by
    have hcoe : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => (τ : ℂ)) := mdifferentiable_coe
    exact MDifferentiable.sub hhol (hcoe.mul hB)
  refine ⟨hBper, ?_, hB, hA, ?_, ?_⟩
  · -- Periodicity of `shiftA`.
    intro τ
    have h := hBper τ
    unfold shiftA
    rw [h, Work.Kernels.coe_vadd_one]
    unfold shiftB
    ring
  · -- The reconstruction `f = shiftA f + τ · shiftB f`.
    intro τ
    unfold shiftA
    ring
  · -- Decay of `shiftB` on `Re τ = -1/2`, from the decay of `f` on both lines.
    intro ε hε
    obtain ⟨Y, hY⟩ := hline (ε / 2) (by positivity)
    refine ⟨Y, ?_⟩
    intro τ hre him
    have hE : (0 : ℝ) ≤ Real.exp (2 * Real.pi * ((m : ℝ) - 1) * τ.im) := Real.exp_nonneg _
    have hτ1 : (((1 : ℝ) +ᵥ τ : UpperHalfPlane).re = 1 / 2 ∨
        ((1 : ℝ) +ᵥ τ : UpperHalfPlane).re = -1 / 2) := by
      left; rw [UpperHalfPlane.vadd_re, hre]; norm_num
    have him1 : Y ≤ (((1 : ℝ) +ᵥ τ : UpperHalfPlane)).im := by
      rw [UpperHalfPlane.vadd_im]; exact him
    have h1 := hY ((1 : ℝ) +ᵥ τ) hτ1 him1
    have h2 := hY τ (Or.inr hre) him
    rw [UpperHalfPlane.vadd_im] at h1
    have hshift : shiftB f τ = f ((1 : ℝ) +ᵥ τ) - f τ := rfl
    calc ‖shiftB f τ‖ * Real.exp (2 * Real.pi * ((m : ℝ) - 1) * τ.im)
        = ‖f ((1 : ℝ) +ᵥ τ) - f τ‖ *
            Real.exp (2 * Real.pi * ((m : ℝ) - 1) * τ.im) := by rw [hshift]
      _ ≤ (‖f ((1 : ℝ) +ᵥ τ)‖ + ‖f τ‖) *
            Real.exp (2 * Real.pi * ((m : ℝ) - 1) * τ.im) :=
            mul_le_mul_of_nonneg_right (norm_sub_le _ _) hE
      _ = ‖f ((1 : ℝ) +ᵥ τ)‖ * Real.exp (2 * Real.pi * ((m : ℝ) - 1) * τ.im)
          + ‖f τ‖ * Real.exp (2 * Real.pi * ((m : ℝ) - 1) * τ.im) := by ring
      _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
      _ = ε := by ring

end Work.CKFinal
