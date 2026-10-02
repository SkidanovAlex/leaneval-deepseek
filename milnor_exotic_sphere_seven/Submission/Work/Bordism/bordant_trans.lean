import Mathlib
import Submission.Work.Bordism.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Transitivity of oriented bordism

`Work.Bordism.Bordant` is the relation "there is an oriented bordism from `M` to `N`", where a
bordism (see `Submission/Work/Bordism/Basic.lean`) records a space `W` together with two maps
`iM : M.X ⟶ W`, `iN : N.X ⟶ W` whose images of the fundamental classes agree in `Hₙ(W;ℤ)`.

This file proves that this relation is transitive.  The geometric construction is the gluing of a
bordism `W₁` from `M` to `N` and a bordism `W₂` from `N` to `P` along the common boundary piece
`N`: the pushout of `iN : N.X ⟶ W₁` and `iM : N.X ⟶ W₂`.  The induced maps `M.X ⟶ W` and
`P.X ⟶ W` then have equal pushforwards of the fundamental classes, because the two composites
`N.X ⟶ W` coincide by the universal property of the pushout:

`iM_*[M] = iN_*[N]` in `Hₙ(W₁)`, `iM_*[N] = iN_*[P]` in `Hₙ(W₂)`, both `N.X → W` maps agree
(`Work.Bordism.Bordism` fields, `CategoryTheory.Limits.pushout.condition`).
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology
open scoped Simplicial

namespace Work.Bordism

open Work.Cohomology

noncomputable section

/-- Functoriality of the singular chain map, in the form we need below:
`chainMap (f ≫ g) = chainMap f ≫ chainMap g`. -/
lemma bordantTrans_chainMap_comp (X Y Z : TopCat) (f : X ⟶ Y) (g : Y ⟶ Z) :
    chainMap ℤ X Z (f ≫ g) = chainMap ℤ X Y f ≫ chainMap ℤ Y Z g := by
  simp only [chainMap, Functor.map_comp]

/-- The homology of a composite chain map, evaluated on a class: the two maps act successively. -/
lemma bordantTrans_homologyMap_comp_apply {C D E : ChainComplex (ModuleCat ℤ) ℕ}
    (f : C ⟶ D) (g : D ⟶ E) (i : ℕ) (x : C.homology i) :
    HomologicalComplex.homologyMap (f ≫ g) i x
      = HomologicalComplex.homologyMap g i (HomologicalComplex.homologyMap f i x) := by
  rw [HomologicalComplex.homologyMap_comp]
  exact ModuleCat.comp_apply _ _ x

/-- **Transitivity of oriented bordism.**  Given a bordism from `M` to `N` and one from `N` to
`P`, glue them along `N`: the pushout of the two boundary maps `N → W₁`, `N → W₂`, with the
`M → W` and `P → W` maps induced by the coprojections.  The fundamental classes of `M` and `P`
have the same image in `Hₙ(W;ℤ)` because both are the image of `[N]` under the common composite
`N → W`. -/
theorem bordant_trans {n : ℕ} {M N P : Work.Bordism.ClosedOriented n}
    (h₁ : Work.Bordism.Bordant M N) (h₂ : Work.Bordism.Bordant N P) :
    Work.Bordism.Bordant M P := by
  obtain ⟨b₁⟩ := h₁
  obtain ⟨b₂⟩ := h₂
  -- the gluing space: the pushout of the two copies of the common boundary `N`
  let W : TopCat := CategoryTheory.Limits.pushout b₁.iN b₂.iM
  let inl : b₁.W ⟶ W := CategoryTheory.Limits.pushout.inl b₁.iN b₂.iM
  let inr : b₂.W ⟶ W := CategoryTheory.Limits.pushout.inr b₁.iN b₂.iM
  have hcond : b₁.iN ≫ inl = b₂.iM ≫ inr := CategoryTheory.Limits.pushout.condition
  refine ⟨{ W := W, iM := b₁.iM ≫ inl, iN := b₂.iN ≫ inr, hbd := ?_ }⟩
  -- split the two composite chain maps into their two factors
  have hfac₁ : chainMap ℤ M.X W (b₁.iM ≫ inl)
      = chainMap ℤ M.X b₁.W b₁.iM ≫ chainMap ℤ b₁.W W inl :=
    bordantTrans_chainMap_comp M.X b₁.W W b₁.iM inl
  have hfac₂ : chainMap ℤ P.X W (b₂.iN ≫ inr)
      = chainMap ℤ P.X b₂.W b₂.iN ≫ chainMap ℤ b₂.W W inr :=
    bordantTrans_chainMap_comp P.X b₂.W W b₂.iN inr
  have hfac₃ : chainMap ℤ N.X W (b₁.iN ≫ inl)
      = chainMap ℤ N.X b₁.W b₁.iN ≫ chainMap ℤ b₁.W W inl :=
    bordantTrans_chainMap_comp N.X b₁.W W b₁.iN inl
  have hfac₄ : chainMap ℤ N.X W (b₂.iM ≫ inr)
      = chainMap ℤ N.X b₂.W b₂.iM ≫ chainMap ℤ b₂.W W inr :=
    bordantTrans_chainMap_comp N.X b₂.W W b₂.iM inr
  -- the two composites `N.X ⟶ W` agree
  have hchain : chainMap ℤ N.X W (b₁.iN ≫ inl) = chainMap ℤ N.X W (b₂.iM ≫ inr) := by
    rw [hcond]
  -- `[M]` maps to the image of `[N]` in `Hₙ(W;ℤ)`
  have hL : HomologicalComplex.homologyMap (chainMap ℤ M.X W (b₁.iM ≫ inl)) n M.c
      = HomologicalComplex.homologyMap (chainMap ℤ N.X W (b₁.iN ≫ inl)) n N.c := by
    rw [hfac₁, bordantTrans_homologyMap_comp_apply, b₁.hbd,
      ← bordantTrans_homologyMap_comp_apply, ← hfac₃]
  -- and so does `[P]`
  have hR : HomologicalComplex.homologyMap (chainMap ℤ N.X W (b₁.iN ≫ inl)) n N.c
      = HomologicalComplex.homologyMap (chainMap ℤ P.X W (b₂.iN ≫ inr)) n P.c := by
    rw [hchain, hfac₄, bordantTrans_homologyMap_comp_apply, b₂.hbd,
      ← bordantTrans_homologyMap_comp_apply, ← hfac₂]
  exact hL.trans hR

end

end Work.Bordism
