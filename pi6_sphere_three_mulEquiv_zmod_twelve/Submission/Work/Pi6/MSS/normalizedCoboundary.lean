import Mathlib
import Submission.Work.Cohomology.CupRing
import Submission.Work.Pi6.SQM.SIG.Z4Defs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Normalized primitives for normalized coboundaries

Given a simplicial set `X` and a coefficient field `𝕜`, the *normalized* cochains are those
cochains vanishing on degenerate simplices, i.e. those that factor through the normalized chain
complex `X.normalizedChainComplex 𝕜`.  This file proves the elementary part of the fact that
normalization does not change cohomology in a degree-local form:

if a normalized `(n+1)`-cocycle `α` has zero cohomology class in the full (unnormalized) cochain
complex, then it has a primitive `β` which is *also* normalized.

The proof does not need any homotopy-theoretic input.  Writing `t = toNormalizedChainComplex` and
`f = fromNormalizedChainComplex` for the split epi/mono pair of Mathlib, with
`t ≫ f = PInfty` and `f ≫ t = 𝟙`, and using that `α` is normalized if and only if it is
annihilated by `QInfty = 𝟙 - PInfty` (`DoldKan.degeneraciesVanish_iff_QInfty_f_comp`), the
primitive is simply

`β = γ ∘ f ∘ t`,

where `γ` is any primitive of `α`.  The key points are

* `α = α ∘ PInfty` (`PInfty_fixed_of_kills_degenerate`), which makes `α` a pullback of a cochain
  on the normalized complex, and
* `ιNormalizedChainComplex_eq_zero`, which makes `β` vanish on degenerate simplices again,
  since `PInfty = t ≫ f` is a chain map.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.MSS

noncomputable section

/-- On generators, the simplicial degeneracy of the free `𝕜`-module on a simplicial set is given
by the degeneracy of the simplicial set. -/
lemma iota_comp_sigma (𝕜 : Type) [Field 𝕜] (X : SSet.{0}) (n : ℕ) (i : Fin (n + 1))
    (x : X _⦋n⦌) :
    X.ιChainComplex (R := ModuleCat.of 𝕜 𝕜) x ≫
        (SimplicialObject.σ (X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜)) i) =
      X.ιChainComplex (R := ModuleCat.of 𝕜 𝕜) (X.σ i x) := by
  simp only [SimplicialObject.σ_def]
  simp only [Functor.comp_map, sigmaConst_obj_map, SSet.ιChainComplex, Sigma.ι_comp_map',
    Category.id_comp]

/-- A cochain that vanishes on a simplex `σ` is annihilated by the generator `ι σ`: the corresponding
composite `𝕜 ⟶ 𝕜` is zero. -/
lemma iota_comp_eq_zero_of_genEval (𝕜 : Type) [Field 𝕜] (X : SSet.{0}) (m : ℕ)
    (σ : X _⦋m⦌) (α : Work.Cohomology.Cochain 𝕜 X m)
    (h : Work.Cohomology.genEval 𝕜 X α σ = 0) :
    X.ιChainComplex (R := ModuleCat.of 𝕜 𝕜) σ ≫ ModuleCat.ofHom α = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simpa [Work.Cohomology.genEval, ModuleCat.hom_comp] using h

/-- A cochain vanishing on all degenerate `(n+1)`-simplices is annihilated by `QInfty`
(`QInfty` is the projector onto the degenerate part of the chain complex). -/
lemma degeneraciesVanish_of_kills_degenerate (𝕜 : Type) [Field 𝕜] (X : SSet.{0}) (n : ℕ)
    (α : Work.Cohomology.Cochain 𝕜 X (n + 1))
    (hv : ∀ σ : X _⦋n + 1⦌, σ ∈ SSet.degenerate X (n + 1) →
      Work.Cohomology.genEval 𝕜 X α σ = 0) :
    DoldKan.DegeneraciesVanish (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))
      (ModuleCat.ofHom α) := by
  rw [DoldKan.degeneraciesVanish_succ_iff]
  intro i
  apply SSet.chainComplex_hom_ext
  intro x
  rw [← Category.assoc, iota_comp_sigma 𝕜 X n i x]
  exact iota_comp_eq_zero_of_genEval 𝕜 X (n + 1) (X.σ i x) α
    (hv (X.σ i x) (by
      rw [SSet.degenerate_eq_iUnion_range_σ]
      exact Set.mem_iUnion.mpr ⟨i, ⟨x, rfl⟩⟩))

/-- A cochain vanishing on degenerate simplices is fixed by `PInfty`. -/
lemma PInfty_fixed_of_kills_degenerate (𝕜 : Type) [Field 𝕜] (X : SSet.{0}) (n : ℕ)
    (α : Work.Cohomology.Cochain 𝕜 X (n + 1))
    (hv : ∀ σ : X _⦋n + 1⦌, σ ∈ SSet.degenerate X (n + 1) →
      Work.Cohomology.genEval 𝕜 X α σ = 0) :
    (ModuleCat.ofHom α : (X.chainComplex (ModuleCat.of 𝕜 𝕜)).X (n + 1) ⟶ ModuleCat.of 𝕜 𝕜)
      = (DoldKan.PInfty (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))).f (n + 1)
        ≫ ModuleCat.ofHom α := by
  have hdv : DoldKan.DegeneraciesVanish (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))
      (ModuleCat.ofHom α) := degeneraciesVanish_of_kills_degenerate 𝕜 X n α hv
  have hQ : (DoldKan.QInfty (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))).f (n + 1) ≫
      (ModuleCat.ofHom α : (X.chainComplex (ModuleCat.of 𝕜 𝕜)).X (n + 1) ⟶
        ModuleCat.of 𝕜 𝕜) = 0 :=
    (DoldKan.degeneraciesVanish_iff_QInfty_f_comp _).mp hdv
  have h1 : (𝟙 ((X.chainComplex (ModuleCat.of 𝕜 𝕜)).X (n + 1)) :
      (X.chainComplex (ModuleCat.of 𝕜 𝕜)).X (n + 1) ⟶
        (X.chainComplex (ModuleCat.of 𝕜 𝕜)).X (n + 1))
      = (DoldKan.PInfty (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))).f (n + 1)
        + (DoldKan.QInfty (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))).f (n + 1) :=
    (DoldKan.PInfty_f_add_QInfty_f (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜)) (n + 1)).symm
  calc (ModuleCat.ofHom α : (X.chainComplex (ModuleCat.of 𝕜 𝕜)).X (n + 1) ⟶ ModuleCat.of 𝕜 𝕜)
      = (𝟙 ((X.chainComplex (ModuleCat.of 𝕜 𝕜)).X (n + 1)) :
          (X.chainComplex (ModuleCat.of 𝕜 𝕜)).X (n + 1) ⟶
            (X.chainComplex (ModuleCat.of 𝕜 𝕜)).X (n + 1)) ≫ ModuleCat.ofHom α :=
        (Category.id_comp _).symm
    _ = ((DoldKan.PInfty (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))).f (n + 1)
          + (DoldKan.QInfty (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))).f (n + 1))
          ≫ ModuleCat.ofHom α := by rw [h1]
    _ = (DoldKan.PInfty (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))).f (n + 1)
          ≫ ModuleCat.ofHom α
        + (DoldKan.QInfty (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))).f (n + 1)
          ≫ ModuleCat.ofHom α := by
        rw [Preadditive.add_comp]
    _ = (DoldKan.PInfty (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))).f (n + 1)
          ≫ ModuleCat.ofHom α := by
        rw [hQ, add_zero]

/-- **A normalized cocycle with vanishing class has a normalized primitive.** -/
theorem normalizedCoboundary (𝕜 : Type) [Field 𝕜] (X : SSet.{0}) (n : ℕ)
    (α : Work.Cohomology.Cochain 𝕜 X (n + 1))
    (hα : Work.Cohomology.cochainDiff 𝕜 X α = 0)
    (hv : ∀ σ : X.obj (Opposite.op (SimplexCategory.mk (n + 1))),
            σ ∈ SSet.degenerate X (n + 1) → Work.Cohomology.genEval 𝕜 X α σ = 0)
    (h0 : Work.Cohomology.cohomologyClassOf 𝕜 X α hα = 0) :
    ∃ β : Work.Cohomology.Cochain 𝕜 X n,
      Work.Cohomology.cochainDiff 𝕜 X β = α ∧
      (∀ τ : X.obj (Opposite.op (SimplexCategory.mk n)),
          τ ∈ SSet.degenerate X n → Work.Cohomology.genEval 𝕜 X β τ = 0) := by
  obtain ⟨γ, hγ⟩ := Work.Pi6.SQM.SIG.classZeroCoboundary_R 𝕜 X n α hα h0
  have hPF : (X.toNormalizedChainComplex (ModuleCat.of 𝕜 𝕜)).f n ≫
      (X.fromNormalizedChainComplex (ModuleCat.of 𝕜 𝕜)).f n = DoldKan.PInfty.f n := by
    have h := congrArg (fun (f : X.chainComplex (ModuleCat.of 𝕜 𝕜) ⟶
        X.chainComplex (ModuleCat.of 𝕜 𝕜)) => f.f n)
      (X.toNormalizedChainComplex_fromNormalizedChainComplex (ModuleCat.of 𝕜 𝕜))
    simpa [HomologicalComplex.comp_f] using h
  have hcomm : (DoldKan.PInfty (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))).f (n + 1) ≫
      (X.chainComplex (ModuleCat.of 𝕜 𝕜)).d (n + 1) n
      = (X.chainComplex (ModuleCat.of 𝕜 𝕜)).d (n + 1) n ≫
        (DoldKan.PInfty (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))).f n :=
    HomologicalComplex.Hom.comm
      (DoldKan.PInfty (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))) (n + 1) n
  have hP : (ModuleCat.ofHom α : (X.chainComplex (ModuleCat.of 𝕜 𝕜)).X (n + 1) ⟶
        ModuleCat.of 𝕜 𝕜)
      = (DoldKan.PInfty (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))).f (n + 1)
        ≫ ModuleCat.ofHom α :=
    PInfty_fixed_of_kills_degenerate 𝕜 X n α hv
  have hDγ : (X.chainComplex (ModuleCat.of 𝕜 𝕜)).d (n + 1) n ≫ ModuleCat.ofHom γ
      = ModuleCat.ofHom (Work.Cohomology.cochainDiff 𝕜 X γ) := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    rfl
  refine ⟨((X.toNormalizedChainComplex (ModuleCat.of 𝕜 𝕜)).f n ≫
      (X.fromNormalizedChainComplex (ModuleCat.of 𝕜 𝕜)).f n ≫ ModuleCat.ofHom γ).hom, ?_, ?_⟩
  · have key : (X.chainComplex (ModuleCat.of 𝕜 𝕜)).d (n + 1) n
        ≫ ((X.toNormalizedChainComplex (ModuleCat.of 𝕜 𝕜)).f n ≫
            ((X.fromNormalizedChainComplex (ModuleCat.of 𝕜 𝕜)).f n ≫ ModuleCat.ofHom γ))
        = ModuleCat.ofHom α := by
      calc (X.chainComplex (ModuleCat.of 𝕜 𝕜)).d (n + 1) n
            ≫ ((X.toNormalizedChainComplex (ModuleCat.of 𝕜 𝕜)).f n ≫
                ((X.fromNormalizedChainComplex (ModuleCat.of 𝕜 𝕜)).f n ≫ ModuleCat.ofHom γ))
          = (X.chainComplex (ModuleCat.of 𝕜 𝕜)).d (n + 1) n
              ≫ (((X.toNormalizedChainComplex (ModuleCat.of 𝕜 𝕜)).f n ≫
                  (X.fromNormalizedChainComplex (ModuleCat.of 𝕜 𝕜)).f n) ≫ ModuleCat.ofHom γ) := by
            rw [Category.assoc]
        _ = (X.chainComplex (ModuleCat.of 𝕜 𝕜)).d (n + 1) n
              ≫ ((DoldKan.PInfty (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))).f n
                  ≫ ModuleCat.ofHom γ) := by
            rw [hPF]
        _ = ((X.chainComplex (ModuleCat.of 𝕜 𝕜)).d (n + 1) n
              ≫ (DoldKan.PInfty (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))).f n)
              ≫ ModuleCat.ofHom γ := by
            rw [Category.assoc]
        _ = ((DoldKan.PInfty (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))).f (n + 1)
              ≫ (X.chainComplex (ModuleCat.of 𝕜 𝕜)).d (n + 1) n) ≫ ModuleCat.ofHom γ := by
            rw [← hcomm]
        _ = (DoldKan.PInfty (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))).f (n + 1)
              ≫ ((X.chainComplex (ModuleCat.of 𝕜 𝕜)).d (n + 1) n ≫ ModuleCat.ofHom γ) := by
            rw [Category.assoc]
        _ = (DoldKan.PInfty (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))).f (n + 1)
              ≫ ModuleCat.ofHom (Work.Cohomology.cochainDiff 𝕜 X γ) := by
            rw [hDγ]
        _ = (DoldKan.PInfty (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))).f (n + 1)
              ≫ ModuleCat.ofHom α := by
            rw [hγ]
        _ = ModuleCat.ofHom α := hP.symm
    exact congrArg ModuleCat.Hom.hom key
  · intro τ hτ
    have hι : X.ιChainComplex (R := ModuleCat.of 𝕜 𝕜) τ ≫
        (X.toNormalizedChainComplex (ModuleCat.of 𝕜 𝕜)).f n = 0 := by
      rw [SSet.ιChainComplex_toNormalizedChainComplex_f,
        SSet.ιNormalizedChainComplex_eq_zero X τ hτ]
    have hz : X.ιChainComplex (R := ModuleCat.of 𝕜 𝕜) τ ≫
        ((X.toNormalizedChainComplex (ModuleCat.of 𝕜 𝕜)).f n ≫
          ((X.fromNormalizedChainComplex (ModuleCat.of 𝕜 𝕜)).f n ≫ ModuleCat.ofHom γ)) = 0 := by
      rw [← Category.assoc, ← Category.assoc, hι, zero_comp, zero_comp]
    have h4 := congrArg (fun (f : ModuleCat.of 𝕜 𝕜 ⟶ ModuleCat.of 𝕜 𝕜) => f.hom 1) hz
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at h4
    exact h4

end

end Work.Pi6.MSS
