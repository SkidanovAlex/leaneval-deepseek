import Mathlib
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.Toolkit.EA
import Submission.Work.ATOM.ZS.Topo.Defs
import Submission.Work.ATOM.zfreeTensorIso_natural

set_option linter.style.haveILetI false

namespace Work.ATOM.Toolkit

open CategoryTheory Limits MonoidalCategory MonoidalClosed LightCondensed LightProfinite

/-!
# Descent along `ℤ[(ℕ∪{∞}) ⊗ (ℕ∪{∞})] ⟶ P ⊗ P`

The proof is by a general categorical lemma, `exists_desc_tmul_cokernel`: for a morphism
`f : A₀ ⟶ A₁` in an abelian monoidal closed category and `φ : A₁ ⊗ A₁ ⟶ M` annihilated by
`f ▷ A₁` and `A₁ ◁ f`, there is a unique `ψ : cokernel f ⊗ cokernel f ⟶ M` with
`(π ▷ A₁) ≫ (cokernel f ◁ π) ≫ ψ = φ` (`π = cokernel.π f`).

The two descent steps use that the tensor functors are left adjoints, hence preserve cokernels
(`PreservesCokernel.iso`), together with `whisker_exchange` to commute `cokernel f ◁ f` past
`π ▷ A₁`.  The application to `f = P_map` and the transport of the hypotheses across
`zfreeTensorIso_natural` are the contents of `exists_desc_coker`.
-/

section General

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
  [Abelian C]

/-- **Two-step descent along `cokernel f`.**  Let `f : A₀ ⟶ A₁` be a morphism and
`φ : A₁ ⊗ A₁ ⟶ M` a morphism killed by both `f ▷ A₁` and `A₁ ◁ f`.  Then `φ` factors uniquely
through the projection `(cokernel.π f ▷ A₁) ≫ (cokernel f ◁ cokernel.π f)`.

The construction is: first descend along `cokernel.π f ▷ A₁` (the cokernel projection of
`f ▷ A₁`, since `- ⊗ A₁` preserves cokernels), then along `cokernel f ◁ cokernel.π f` (the
cokernel projection of `cokernel f ◁ f`); the vanishing of the latter is exactly what
`whisker_exchange` provides. -/
theorem exists_desc_tmul_cokernel {A₀ A₁ M : C} (f : A₀ ⟶ A₁) (φ : A₁ ⊗ A₁ ⟶ M)
    (h₁ : (MonoidalCategory.tensorRight A₁).map f ≫ φ = 0)
    (h₂ : (MonoidalCategory.tensorLeft A₁).map f ≫ φ = 0) :
    ∃! ψ : cokernel f ⊗ cokernel f ⟶ M,
      (MonoidalCategory.tensorRight A₁).map (cokernel.π f) ≫
        (MonoidalCategory.tensorLeft (cokernel f)).map (cokernel.π f) ≫ ψ = φ := by
  -- `- ⊗ A₁` and `- ⊗ A₀` preserve the cokernel of `f`, so the corresponding projections are
  -- epimorphisms.
  haveI hEpi₁ : Epi ((MonoidalCategory.tensorRight A₁).map (cokernel.π f)) := by
    have h := PreservesCokernel.π_iso_hom (MonoidalCategory.tensorRight A₁) f
    have hs : (MonoidalCategory.tensorRight A₁).map (cokernel.π f) =
        cokernel.π ((MonoidalCategory.tensorRight A₁).map f) ≫
          (PreservesCokernel.iso (MonoidalCategory.tensorRight A₁) f).inv := by
      rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hs]
    infer_instance
  haveI hEpi₀ : Epi ((MonoidalCategory.tensorRight A₀).map (cokernel.π f)) := by
    have h := PreservesCokernel.π_iso_hom (MonoidalCategory.tensorRight A₀) f
    have hs : (MonoidalCategory.tensorRight A₀).map (cokernel.π f) =
        cokernel.π ((MonoidalCategory.tensorRight A₀).map f) ≫
          (PreservesCokernel.iso (MonoidalCategory.tensorRight A₀) f).inv := by
      rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hs]
    infer_instance
  haveI hEpi₂ : Epi ((MonoidalCategory.tensorLeft (cokernel f)).map (cokernel.π f)) := by
    have h := PreservesCokernel.π_iso_hom (MonoidalCategory.tensorLeft (cokernel f)) f
    have hs : (MonoidalCategory.tensorLeft (cokernel f)).map (cokernel.π f) =
        cokernel.π ((MonoidalCategory.tensorLeft (cokernel f)).map f) ≫
          (PreservesCokernel.iso (MonoidalCategory.tensorLeft (cokernel f)) f).inv := by
      rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hs]
    infer_instance
  -- first descent: along `cokernel.π f ▷ A₁`
  have hc₁ := PreservesCokernel.π_iso_hom (MonoidalCategory.tensorRight A₁) f
  let ψ₁ : cokernel f ⊗ A₁ ⟶ M :=
    (PreservesCokernel.iso (MonoidalCategory.tensorRight A₁) f).hom ≫
      cokernel.desc ((MonoidalCategory.tensorRight A₁).map f) φ h₁
  have hψ₁ : (MonoidalCategory.tensorRight A₁).map (cokernel.π f) ≫ ψ₁ = φ := by
    show (MonoidalCategory.tensorRight A₁).map (cokernel.π f) ≫
      ((PreservesCokernel.iso (MonoidalCategory.tensorRight A₁) f).hom ≫
        cokernel.desc ((MonoidalCategory.tensorRight A₁).map f) φ h₁) = φ
    rw [← Category.assoc, hc₁, cokernel.π_desc]
  -- the compatibility needed for the second descent, from `whisker_exchange`
  have hex : (MonoidalCategory.tensorLeft A₁).map f ≫
      (MonoidalCategory.tensorRight A₁).map (cokernel.π f) =
      (MonoidalCategory.tensorRight A₀).map (cokernel.π f) ≫
        (MonoidalCategory.tensorLeft (cokernel f)).map f :=
    whisker_exchange (cokernel.π f) f
  have hzero : (MonoidalCategory.tensorLeft (cokernel f)).map f ≫ ψ₁ = 0 := by
    rw [← cancel_epi ((MonoidalCategory.tensorRight A₀).map (cokernel.π f))]
    rw [← Category.assoc, ← hex, Category.assoc, hψ₁, h₂, comp_zero]
  -- second descent: along `cokernel f ◁ cokernel.π f`
  have hc₂ := PreservesCokernel.π_iso_hom (MonoidalCategory.tensorLeft (cokernel f)) f
  let w : cokernel f ⊗ cokernel f ⟶ M :=
    (PreservesCokernel.iso (MonoidalCategory.tensorLeft (cokernel f)) f).hom ≫
      cokernel.desc ((MonoidalCategory.tensorLeft (cokernel f)).map f) ψ₁ hzero
  have hψ₂ : (MonoidalCategory.tensorLeft (cokernel f)).map (cokernel.π f) ≫ w = ψ₁ := by
    show (MonoidalCategory.tensorLeft (cokernel f)).map (cokernel.π f) ≫
      ((PreservesCokernel.iso (MonoidalCategory.tensorLeft (cokernel f)) f).hom ≫
        cokernel.desc ((MonoidalCategory.tensorLeft (cokernel f)).map f) ψ₁ hzero) = ψ₁
    rw [← Category.assoc, hc₂, cokernel.π_desc]
  refine ⟨w, ?_, ?_⟩
  · show (MonoidalCategory.tensorRight A₁).map (cokernel.π f) ≫
      (MonoidalCategory.tensorLeft (cokernel f)).map (cokernel.π f) ≫ w = φ
    rw [hψ₂, hψ₁]
  · intro ψ' hψ'
    -- uniqueness: cancel the two (epimorphic) projections
    have hB : (MonoidalCategory.tensorLeft (cokernel f)).map (cokernel.π f) ≫ ψ' = ψ₁ :=
      (cancel_epi ((MonoidalCategory.tensorRight A₁).map (cokernel.π f))).mp (hψ'.trans hψ₁.symm)
    exact (cancel_epi ((MonoidalCategory.tensorLeft (cokernel f)).map (cokernel.π f))).mp
      (hB.trans hψ₂.symm)

end General

/-- **Descent along `ℤ[(ℕ∪{∞}) ⊗ (ℕ∪{∞})] ⟶ P ⊗ P`, in the form used for the proof.**  This is
`exists_desc_tmul_cokernel` for `f = P_map`, `A₀ = ℤ[∗]`, `A₁ = ℤ[ℕ∪{∞}]`, with the two
hypotheses transported across `zfreeTensorIso_natural`; the conclusion is stated with `P_map`
in place of `P_proj` so that it matches the general lemma syntactically. -/
theorem exists_desc_coker {M : LightCondAb} (φ : Work.ATOM.zfree Work.ATOM.NS2 ⟶ M)
    (h₁ : Work.ATOM.zmap (MonoidalCategory.whiskerRight LightCondensed.ι
        (LightProfinite.NatUnionInfty)) ≫ φ = 0)
    (h₂ : Work.ATOM.zmap (MonoidalCategory.whiskerLeft (LightProfinite.NatUnionInfty)
        LightCondensed.ι) ≫ φ = 0) :
    ∃! ψ : cokernel LightCondensed.P_map ⊗ cokernel LightCondensed.P_map ⟶ M,
      ((Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty LightProfinite.NatUnionInfty).inv ≫
        (MonoidalCategory.tensorRight (Work.ATOM.zfree LightProfinite.NatUnionInfty)).map
          (cokernel.π LightCondensed.P_map) ≫
        (MonoidalCategory.tensorLeft (cokernel LightCondensed.P_map)).map
          (cokernel.π LightCondensed.P_map)) ≫ ψ = φ := by
  -- First variable: `(P_map ▷ ℤ[ℕ∪{∞}]) ≫ μ = μ ≫ zmap (ι ▷ ℕ∪{∞})`.
  have hn₁ : (MonoidalCategory.tensorRight (Work.ATOM.zfree LightProfinite.NatUnionInfty)).map
        LightCondensed.P_map ≫
      (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty LightProfinite.NatUnionInfty).hom =
      (Work.ATOM.zfreeTensorIso Work.ATOM.pt LightProfinite.NatUnionInfty).hom ≫
        Work.ATOM.zmap (MonoidalCategory.whiskerRight LightCondensed.ι
          LightProfinite.NatUnionInfty) := by
    have h := Work.ATOM.zfreeTensorIso_natural (X := Work.ATOM.pt)
      (X' := LightProfinite.NatUnionInfty) (Y := LightProfinite.NatUnionInfty)
      (Y' := LightProfinite.NatUnionInfty) LightCondensed.ι (𝟙 _)
    simpa [LightCondensed.P_map] using h
  -- Second variable: `(ℤ[ℕ∪{∞}] ◁ P_map) ≫ μ = μ ≫ zmap (ℕ∪{∞} ◁ ι)`.
  have hn₂ : (MonoidalCategory.tensorLeft (Work.ATOM.zfree LightProfinite.NatUnionInfty)).map
        LightCondensed.P_map ≫
      (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty LightProfinite.NatUnionInfty).hom =
      (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty Work.ATOM.pt).hom ≫
        Work.ATOM.zmap (MonoidalCategory.whiskerLeft LightProfinite.NatUnionInfty
          LightCondensed.ι) := by
    have h := Work.ATOM.zfreeTensorIso_natural (X := LightProfinite.NatUnionInfty)
      (X' := LightProfinite.NatUnionInfty) (Y := Work.ATOM.pt) (Y' := LightProfinite.NatUnionInfty)
      (𝟙 _) LightCondensed.ι
    simpa [LightCondensed.P_map] using h.symm
  have h₁' : (MonoidalCategory.tensorRight (Work.ATOM.zfree LightProfinite.NatUnionInfty)).map
        LightCondensed.P_map ≫
      ((Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty LightProfinite.NatUnionInfty).hom ≫
        φ) = 0 := by
    rw [← Category.assoc, hn₁, Category.assoc, h₁, comp_zero]
  have h₂' : (MonoidalCategory.tensorLeft (Work.ATOM.zfree LightProfinite.NatUnionInfty)).map
        LightCondensed.P_map ≫
      ((Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty LightProfinite.NatUnionInfty).hom ≫
        φ) = 0 := by
    rw [← Category.assoc, hn₂, Category.assoc, h₂, comp_zero]
  obtain ⟨ψ, hψ, huniq⟩ := exists_desc_tmul_cokernel (C := LightCondAb)
    (A₀ := Work.ATOM.zfree Work.ATOM.pt) (A₁ := Work.ATOM.zfree LightProfinite.NatUnionInfty)
    LightCondensed.P_map
    ((Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty LightProfinite.NatUnionInfty).hom ≫ φ)
    h₁' h₂'
  refine ⟨ψ, ?_, ?_⟩
  · simp only []
    rw [Category.assoc, Category.assoc, hψ]
    exact Iso.inv_hom_id_assoc
      (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty LightProfinite.NatUnionInfty) φ
  · intro ψ' hψ'
    refine huniq ψ' ?_
    rw [Category.assoc, Category.assoc] at hψ'
    calc (MonoidalCategory.tensorRight (Work.ATOM.zfree LightProfinite.NatUnionInfty)).map
            (cokernel.π LightCondensed.P_map) ≫
          (MonoidalCategory.tensorLeft (cokernel LightCondensed.P_map)).map
            (cokernel.π LightCondensed.P_map) ≫ ψ'
        = (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty LightProfinite.NatUnionInfty).hom ≫
            ((Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty LightProfinite.NatUnionInfty).inv ≫
              ((MonoidalCategory.tensorRight (Work.ATOM.zfree LightProfinite.NatUnionInfty)).map
                  (cokernel.π LightCondensed.P_map) ≫
                (MonoidalCategory.tensorLeft (cokernel LightCondensed.P_map)).map
                  (cokernel.π LightCondensed.P_map) ≫ ψ')) :=
          (Iso.hom_inv_id_assoc
            (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty LightProfinite.NatUnionInfty)
            _).symm
      _ = (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty LightProfinite.NatUnionInfty).hom ≫
            φ := by
          rw [hψ']

/-- **Descent along `ℤ[(ℕ∪{∞}) ⊗ (ℕ∪{∞})] ⟶ P ⊗ P`.**  A morphism out of `ℤ[(ℕ∪{∞})²]` which
kills the images of both `∞`-axes (the composites `zmap (whiskerRight ι ℕ∪{∞})` and
`zmap (whiskerLeft ℕ∪{∞} ι)`) descends uniquely along `Work.ATOM.EApp`.  Route: as for
`Work.ATOM.PS_desc`, using that `P_proj ▷ P` is the cokernel projection of `P_map ▷ P` and
`P ▷ P_proj` is the cokernel projection of `P ▷ P_map`, again across `zfreeTensorIso_natural`. -/
theorem PP_desc {M : LightCondAb}
    (φ : Work.ATOM.zfree Work.ATOM.NS2 ⟶ M)
    (h₁ : Work.ATOM.zmap (MonoidalCategory.whiskerRight LightCondensed.ι
        (LightProfinite.NatUnionInfty)) ≫ φ = 0)
    (h₂ : Work.ATOM.zmap (MonoidalCategory.whiskerLeft (LightProfinite.NatUnionInfty)
        LightCondensed.ι) ≫ φ = 0) :
    ∃! ψ : Work.ATOM.tmul LightCondensed.P LightCondensed.P ⟶ M,
      Work.ATOM.EApp ≫ ψ = φ := by
  exact exists_desc_coker φ h₁ h₂

end Work.ATOM.Toolkit
