import Mathlib
import Submission.Work.Drive.Mono.SphereFaceDefs

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open scoped RealInnerProductSpace

noncomputable section

/-- **Chain rule for the pulled-back height.**  The derivative, in the direction `w`, of
`q ↦ ⟪a, par ψ q⟫` at `p` is `⟪a, d(par ψ)_p w⟫`. -/
private lemma fderiv_par_height_apply (ψ : Submission.Diffeo) (a : R3) (p w : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => inner ℝ a (Work.BoxShrink.Pinch.par ψ q)) p w
      = inner ℝ a (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p w) := by
  have hd : DifferentiableAt ℝ (Work.BoxShrink.Pinch.par ψ) p :=
    ((Work.BoxShrink.Pinch.par_contDiff ψ).differentiable (by simp)).differentiableAt
  have h := fderiv_inner_apply (𝕜 := ℝ) (x := p) (G := ℝ × ℝ) (E := R3)
    (f := fun _ : ℝ × ℝ => a) (g := Work.BoxShrink.Pinch.par ψ)
    (differentiableAt_const a) hd w
  rw [h]
  simp

/-- **Three distinct signed faces of the box cannot all have the same nonzero derivative `M` at a
parameter point `p`** unless the derivative `L` of the pulled-back `v`-coordinate at `p` is a
multiple of `M`.  (Ingredients: two *opposite* faces of the same coordinate `i` have opposite
derivatives, so `M = -M`; and if the three coordinates `σ i₁, σ i₂, σ i₃` are distinct then they
exhaust `Fin 3`, so every functional `w ↦ ⟪v, fderiv (Pinch.par ψ) p w⟫` is a linear combination of
the three face derivatives, hence a multiple of `M`.  The face derivatives are computed by
`Work.Drive.Mono.fderiv_faceW_apply`.) -/
theorem not_three_active_faces {ψ : Submission.Diffeo} {s : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {v : LeanEval.KnotTheory.PardonDistortion.R3} {p : ℝ × ℝ}
    {M : (ℝ × ℝ) →L[ℝ] ℝ}
    {i₁ i₂ i₃ : Fin 3} {ε₁ ε₂ ε₃ : ℝ}
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (hε₃ : ε₃ = 1 ∨ ε₃ = -1)
    (hne₁₂ : (i₁, ε₁) ≠ (i₂, ε₂)) (hne₁₃ : (i₁, ε₁) ≠ (i₃, ε₃))
    (hne₂₃ : (i₂, ε₂) ≠ (i₃, ε₃))
    (hf₁ : fderiv ℝ (Work.Drive.Mono.faceW ψ s c σ i₁ ε₁) p = M)
    (hf₂ : fderiv ℝ (Work.Drive.Mono.faceW ψ s c σ i₂ ε₂) p = M)
    (hf₃ : fderiv ℝ (Work.Drive.Mono.faceW ψ s c σ i₃ ε₃) p = M)
    (hM : M ≠ 0)
    (hL : ∀ t : ℝ,
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ t • M) :
    False := by
  -- Reading `fderiv (faceW i ε) p = M` through `fderiv_faceW_apply`: the `σ i`-th coordinate of
  -- `d(par ψ)_p w` is `ε * boxSide i * M w`.
  have hrel : ∀ (i : Fin 3) (ε : ℝ), (ε = 1 ∨ ε = -1) →
      fderiv ℝ (faceW ψ s c σ i ε) p = M → ∀ w : ℝ × ℝ,
      (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p w) (σ i)
        = ε * Submission.boxSide i * (M w) := by
    intro i ε hε hf w
    have hb : Submission.boxSide i ≠ 0 := ne_of_gt (Submission.boxSide_pos i)
    have hm : M w = ε * ((fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p w) (σ i)
        / Submission.boxSide i) := by
      rw [← hf, fderiv_faceW_apply ψ s c σ i ε hε p w]
    rcases hε with rfl | rfl
    · rw [one_mul] at hm
      rw [hm]
      field_simp
    · rw [hm]
      field_simp
  -- Two faces with the same coordinate `i` but opposite signs have opposite derivatives, so if
  -- both are `M` then `M = 0`.
  have hMzero : ∀ {i i' : Fin 3} {ε ε' : ℝ}, (ε = 1 ∨ ε = -1) → (ε' = 1 ∨ ε' = -1) →
      i = i' → (i, ε) ≠ (i', ε') →
      fderiv ℝ (faceW ψ s c σ i ε) p = M → fderiv ℝ (faceW ψ s c σ i' ε') p = M →
      M = 0 := by
    intro i i' ε ε' hε hε' hii hne hf hf'
    have h1 := hf
    rw [hii] at h1
    have e1 : ∀ w : ℝ × ℝ, M w = ε * ((fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p w) (σ i')
        / Submission.boxSide i') := by
      intro w
      rw [← h1, fderiv_faceW_apply ψ s c σ i' ε hε p w]
    have e2 : ∀ w : ℝ × ℝ, M w = ε' * ((fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p w) (σ i')
        / Submission.boxSide i') := by
      intro w
      rw [← hf', fderiv_faceW_apply ψ s c σ i' ε' hε' p w]
    have hne' : ε ≠ ε' := by
      intro he
      exact hne (by rw [hii, he])
    refine ContinuousLinearMap.ext fun w => ?_
    have hy : (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p w) (σ i')
        / Submission.boxSide i' = 0 := by
      have hsub : (ε - ε') * ((fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p w) (σ i')
          / Submission.boxSide i') = 0 := by
        rw [sub_mul, ← e1 w, ← e2 w, sub_self]
      exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hne')
    rw [e1 w, hy]
    simp
  -- Hence the three coordinates `i₁, i₂, i₃` are pairwise distinct.
  have h12 : i₁ ≠ i₂ := by
    intro h
    subst h
    exact hM (hMzero hε₁ hε₂ rfl hne₁₂ hf₁ hf₂)
  have h13 : i₁ ≠ i₃ := by
    intro h
    subst h
    exact hM (hMzero hε₁ hε₃ rfl hne₁₃ hf₁ hf₃)
  have h23 : i₂ ≠ i₃ := by
    intro h
    subst h
    exact hM (hMzero hε₂ hε₃ rfl hne₂₃ hf₂ hf₃)
  -- Three pairwise distinct elements of `Fin 3` exhaust it: package them as a permutation.
  have hinj : Function.Injective ![i₁,i₂,i₃] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hbij : Function.Bijective ![i₁,i₂,i₃] :=
    (Fintype.bijective_iff_injective_and_card ![i₁,i₂,i₃]).mpr ⟨hinj, rfl⟩
  obtain ⟨π, hπ0, hπ1, hπ2⟩ : ∃ π : Equiv.Perm (Fin 3), π 0 = i₁ ∧ π 1 = i₂ ∧ π 2 = i₃ :=
    ⟨Equiv.ofBijective ![i₁,i₂,i₃] hbij, by simp [Equiv.ofBijective_apply],
      by simp [Equiv.ofBijective_apply], by simp [Equiv.ofBijective_apply]⟩
  -- The height functional is the corresponding linear combination of the three faces.
  set t : ℝ := ε₁ * Submission.boxSide i₁ * v (σ i₁)
    + ε₂ * Submission.boxSide i₂ * v (σ i₂) + ε₃ * Submission.boxSide i₃ * v (σ i₃) with ht
  have hpoint : ∀ w : ℝ × ℝ,
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p w = t * M w := by
    intro w
    rw [fderiv_par_height_apply ψ v p w]
    rw [show inner ℝ v (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p w)
        = ∑ j : Fin 3, (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p w) j * v j from by
      rw [PiLp.inner_apply]; simp [RCLike.inner_apply, mul_comm]]
    rw [← Equiv.sum_comp (π.trans σ) (fun j : Fin 3 =>
      (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p w) j * v j)]
    rw [Fin.sum_univ_three]
    simp only [Equiv.trans_apply, hπ0, hπ1, hπ2]
    rw [hrel i₁ ε₁ hε₁ hf₁ w, hrel i₂ ε₂ hε₂ hf₂ w, hrel i₃ ε₃ hε₃ hf₃ w, ht]
    ring
  have hLt : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p
      = t • M := by
    refine ContinuousLinearMap.ext fun w => ?_
    rw [hpoint w, smul_apply, smul_eq_mul]
  exact hL t hLt

end

end Work.Drive.Mono
