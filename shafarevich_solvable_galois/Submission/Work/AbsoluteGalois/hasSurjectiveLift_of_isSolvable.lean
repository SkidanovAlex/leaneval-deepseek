/-
Copyright (c) 2025. All rights reserved.

# A solution of an embedding problem over `ℚ` yields a surjective lift in `G_ℚ`

Let `E : EmbeddingProblem ℚ` be an embedding problem over `ℚ`: a finite Galois extension
`E.L/ℚ` together with a surjection `E.π : E.G ↠ Gal(E.L/ℚ)`.  Suppose `E` has a (proper)
solution `E.IsSolvable`, i.e. a finite Galois extension `L'/ℚ ⊇ E.L` with `L'/E.L` Galois and
an isomorphism `e : E.G ≃* Gal(L'/ℚ)` compatible with `E.π`.

The lifting formulation of the same datum is
`Work.AbsoluteGalois.HasSurjectiveLift E`: an identification of `E.L` with a subfield
`M.L ⊆ ℚ̄` (a `ClosureModel`) together with a surjection `ψ : G_ℚ ↠ E.G` with open kernel
whose composite with `E.π` is the restriction map `G_ℚ →* Gal(M.L/ℚ)`.

Here we prove the implication *solution ⟹ lift*.  Embed the abstract solution field `L'` into
`ℚ̄` by a `ℚ`-embedding `f`, so that `M.L := f(image E.L) ⊆ L'' := f(L')`; the restriction map
`G_ℚ →* Gal(L''/ℚ)` is surjective with open kernel, and composing with the isomorphism
`Gal(L''/ℚ) ≃* Gal(L'/ℚ) ≃* E.G` produced by `f` and `e` gives `ψ`.  The compatibility
`E.π (ψ σ) = σ|_{M.L}` is exactly the compatibility built into the solution `e`.

The converse implication is `Work.AbsoluteGalois.isSolvable_of_hasSurjectiveLift`.
-/
import Mathlib
import Submission.Work.AbsoluteGalois.ClosureModel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteGalois

open scoped Classical

set_option linter.style.haveILetI false

noncomputable section

theorem hasSurjectiveLift_of_isSolvable (E : Submission.EmbeddingProblem ℚ)
    (h : E.IsSolvable) : Work.AbsoluteGalois.HasSurjectiveLift E := by
  -- unpack the solution: `L' / ℚ` is finite Galois, `L'/E.L` is Galois, and `e` is the
  -- system-compatible isomorphism `E.G ≃* Gal(L'/ℚ)`.
  obtain ⟨L', hF, hA, hFD, hGal, hA2, hST, hFD2, hGal2, e, he⟩ := h
  letI : Field L' := hF
  letI : Algebra ℚ L' := hA
  letI : FiniteDimensional ℚ L' := hFD
  letI : IsGalois ℚ L' := hGal
  letI : Algebra E.L L' := hA2
  letI : IsScalarTower ℚ E.L L' := hST
  letI : FiniteDimensional E.L L' := hFD2
  letI : IsGalois E.L L' := hGal2
  -- embed the solution field into a fixed algebraic closure of `ℚ`
  let f : L' →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift (R := ℚ) (S := L') (M := AlgebraicClosure ℚ)
  let L'' : IntermediateField ℚ (AlgebraicClosure ℚ) := f.fieldRange
  haveI hL''fd : FiniteDimensional ℚ L'' :=
    (AlgEquiv.ofInjectiveField f).toLinearEquiv.finiteDimensional
  haveI hL''gal : IsGalois ℚ L'' := IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField f)
  haveI hL''norm : Normal ℚ L'' := hL''gal.to_normal
  -- the base field `E.L` sits inside `L'`; push it into `ℚ̄`
  let g : E.L →ₐ[ℚ] L' := IsScalarTower.toAlgHom ℚ E.L L'
  let φ : E.L →ₐ[ℚ] AlgebraicClosure ℚ := f.comp g
  haveI hMfd : FiniteDimensional ℚ φ.fieldRange :=
    (AlgEquiv.ofInjectiveField φ).toLinearEquiv.finiteDimensional
  haveI hMgal : IsGalois ℚ φ.fieldRange := IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField φ)
  -- the closure model of `E` whose base field is the image of `E.L` in `ℚ̄`
  let M : E.ClosureModel :=
    { L := φ.fieldRange
      finiteDimensional := hMfd
      isGalois := hMgal
      e := AlgEquiv.ofInjectiveField φ }
  -- the identification `Gal(L'/ℚ) ≃* Gal(L''/ℚ)`, and the resulting isomorphism `E.G ≃* Gal(L''/ℚ)`
  let ι : L' ≃ₐ[ℚ] L'' := AlgEquiv.ofInjectiveField f
  let F : E.G ≃* (L'' ≃ₐ[ℚ] L'') := e.trans ι.autCongr
  -- restriction to `L''`, and the lift `ψ = F.symm ∘ res`
  let r : Field.absoluteGaloisGroup ℚ →* (L'' ≃ₐ[ℚ] L'') := restrictHom L''
  let ψ : Field.absoluteGaloisGroup ℚ →* E.G := F.symm.toMonoidHom.comp r
  refine ⟨M, ψ, ?_, ?_, ?_⟩
  · -- the kernel of `ψ` is the kernel of the restriction map, i.e. the (open) fixing subgroup
    rw [MonoidHom.ker_comp_of_injective r F.symm.toMonoidHom F.symm.injective]
    exact restrictHom_ker_isOpen L''
  · -- `ψ` is surjective because both `restrictHom L''` and `F.symm` are
    intro y
    obtain ⟨σ, hσ⟩ := restrictHom_surjective L'' (F y)
    refine ⟨σ, ?_⟩
    rw [show ψ σ = F.symm (r σ) from MonoidHom.comp_apply F.symm.toMonoidHom r σ]
    rw [show r σ = F y from hσ]
    exact F.symm_apply_apply y
  · -- compatibility of `ψ` with the projection `E.π` and the restriction to `M.L`
    intro σ
    -- `ι.autCongr` on `ι z` is `ι ∘ · ∘ ι⁻¹`, evaluated at `ι z`
    have aut : ∀ (u : L' ≃ₐ[ℚ] L') (z : L'), ι.autCongr u (ι z) = ι (u z) := by
      intro u z
      rw [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
        AlgEquiv.symm_apply_apply]
    -- `g` is the algebra map `E.L → L'`
    have hg : ∀ z : E.L, g z = algebraMap E.L L' z :=
      fun z => IsScalarTower.toAlgHom_apply ℚ E.L L' z
    -- `F (ψ σ) = r σ`, i.e. `ι.autCongr (e (ψ σ)) = r σ`
    have hFσ : ι.autCongr (e (ψ σ)) = r σ := by
      have h1 : F (ψ σ) = r σ := by
        rw [show ψ σ = F.symm (r σ) from MonoidHom.comp_apply F.symm.toMonoidHom r σ]
        exact F.apply_symm_apply (r σ)
      rwa [MulEquiv.trans_apply] at h1
    -- the key point: `E.π (ψ σ)` acts on `E.L` exactly as `σ` acts on `M.L = φ(E.L)`
    have key : ∀ y : E.L,
        (↑(M.e ((E.π (ψ σ)) y)) : AlgebraicClosure ℚ) = σ (↑(M.e y) : AlgebraicClosure ℚ) := by
      intro y
      have hu : (e (ψ σ)) (g y) = g ((E.π (ψ σ)) y) := by
        have := he (ψ σ) y
        rw [← hg y, ← hg ((E.π (ψ σ)) y)] at this
        exact this
      calc (↑(M.e ((E.π (ψ σ)) y)) : AlgebraicClosure ℚ)
          = f (g ((E.π (ψ σ)) y)) := rfl
        _ = f ((e (ψ σ)) (g y)) := by rw [← hu]
        _ = ↑(ι ((e (ψ σ)) (g y))) := rfl
        _ = ↑((ι.autCongr (e (ψ σ))) (ι (g y))) := by rw [← aut (e (ψ σ)) (g y)]
        _ = ↑((r σ) (ι (g y))) := by rw [hFσ]
        _ = σ (↑(ι (g y)) : AlgebraicClosure ℚ) := restrictHom_apply L'' σ (ι (g y))
        _ = σ (f (g y)) := rfl
        _ = σ (↑(M.e y) : AlgebraicClosure ℚ) := rfl
    ext x
    rw [Submission.EmbeddingProblem.ClosureModel.autCongr_apply, AlgEquiv.trans_apply,
      AlgEquiv.trans_apply]
    rw [key (M.e.symm x), AlgEquiv.apply_symm_apply M.e x, restrictHom_apply M.L σ x]

end

end Work.AbsoluteGalois
