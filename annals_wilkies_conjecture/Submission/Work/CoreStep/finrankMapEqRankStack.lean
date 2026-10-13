import Mathlib

namespace Work.CoreStep

/-- **Rank–nullity for the restriction of a linear map to a submodule.**

For a linear map `g : V →ₗ[K] V₂` and a submodule `ker f` of a finite-dimensional space `V`,
the dimension of the image of `ker f` under `g` plus the dimension of the kernel of the
restriction of `g` to `ker f` equals the dimension of `ker f`.  Equivalently

`finrank ((ker f).map g) + finrank (ker f ⊓ ker g) = finrank (ker f)`.

This is the "subtract the two nullities" step in the proof of
`Work.CoreStep.finrankMapEqRankStack`. -/
private theorem finrank_map_add_finrank_inf_ker {K V V₁ V₂ : Type*} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
    [FiniteDimensional K V] (f : V →ₗ[K] V₁) (g : V →ₗ[K] V₂) :
    Module.finrank K ↥((LinearMap.ker f).map g) + Module.finrank K ↥(LinearMap.ker f ⊓ LinearMap.ker g)
      = Module.finrank K ↥(LinearMap.ker f) := by
  have hT := LinearMap.finrank_range_add_finrank_ker (g.comp (LinearMap.ker f).subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype] at hT
  rw [LinearMap.ker_comp] at hT
  have hfin : Module.finrank K ↥(Submodule.comap (LinearMap.ker f).subtype (LinearMap.ker g))
      = Module.finrank K ↥(LinearMap.ker f ⊓ LinearMap.ker g) := by
    have h := LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (LinearMap.ker f).subtype
      (Submodule.subtype_injective (LinearMap.ker f))
      (Submodule.comap (LinearMap.ker f).subtype (LinearMap.ker g)))
    rwa [Submodule.map_comap_subtype] at h
  rw [hfin] at hT
  exact hT

/-- The kernel of the `mulVec` map of the vertically stacked matrix `[A₁; A₂]` is the
intersection of the kernels of `A₁` and `A₂`. -/
private theorem ker_mulVecLin_sumElim {j n N : ℕ} (A₁ : Matrix (Fin j) (Fin N) ℝ)
    (A₂ : Matrix (Fin n) (Fin N) ℝ) :
    (Matrix.of (Sum.elim A₁ A₂) : Matrix (Fin j ⊕ Fin n) (Fin N) ℝ).mulVecLin.ker
      = A₁.mulVecLin.ker ⊓ A₂.mulVecLin.ker := by
  ext v
  simp only [LinearMap.mem_ker, Submodule.mem_inf, Matrix.mulVecLin_apply]
  constructor
  · intro h
    refine ⟨funext (fun a => ?_), funext (fun b => ?_)⟩
    · exact congrFun h (Sum.inl a)
    · exact congrFun h (Sum.inr b)
  · rintro ⟨h1, h2⟩
    funext s
    rcases s with a | b
    · exact congrFun h1 a
    · exact congrFun h2 b

theorem finrankMapEqRankStack {j n N : ℕ} (A₁ : Matrix (Fin j) (Fin N) ℝ)
    (A₂ : Matrix (Fin n) (Fin N) ℝ) :
    Module.finrank ℝ ((LinearMap.ker A₁.mulVecLin).map A₂.mulVecLin) + A₁.rank =
      (Matrix.of (Sum.elim A₁ A₂) : Matrix (Fin j ⊕ Fin n) (Fin N) ℝ).rank := by
  -- Notation: `f = A₁ *ᵥ ·`, `g = A₂ *ᵥ ·`, `h = [A₁; A₂] *ᵥ ·`.
  set f := A₁.mulVecLin with hf
  set g := A₂.mulVecLin with hg
  set h := (Matrix.of (Sum.elim A₁ A₂) : Matrix (Fin j ⊕ Fin n) (Fin N) ℝ).mulVecLin with hh
  have hN : Module.finrank ℝ (Fin N → ℝ) = N := by simp
  -- Rank–nullity for `f` and for the stacked map `h`: both nullities live in `ℝ^N`.
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := LinearMap.finrank_range_add_finrank_ker h
  -- The kernel of `h` is `ker f ⊓ ker g`.
  have h4 : LinearMap.ker h = LinearMap.ker f ⊓ LinearMap.ker g := by
    rw [hf, hg, hh]; exact ker_mulVecLin_sumElim A₁ A₂
  rw [h4] at h2
  -- Rank–nullity for `g` restricted to `ker f`.
  have h3 := finrank_map_add_finrank_inf_ker f g
  have key : Module.finrank ℝ ↥((LinearMap.ker f).map g) + Module.finrank ℝ ↥(LinearMap.range f)
      = Module.finrank ℝ ↥(LinearMap.range h) := by
    have h1' := h1
    rw [← h3] at h1'
    have h2' := h2
    rw [hN] at h1' h2'
    omega
  exact key

end Work.CoreStep
