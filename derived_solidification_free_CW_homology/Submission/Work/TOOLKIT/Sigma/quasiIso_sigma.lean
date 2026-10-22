import Mathlib
import Submission.Work.TOOLKIT.Basic
import Submission.Work.TOOLKIT.Instances
import Submission.Work.TOOLKIT.Coprod.quasiIso_colimMap

open CategoryTheory Limits

namespace Work.TOOLKIT.Sigma

/-- Quasi-isomorphisms of cochain complexes of light condensed abelian groups are stable under
small coproducts: `LightCondAb` is a Grothendieck abelian category, so it satisfies AB4 (small
coproducts are exact), hence coproducts of acyclic complexes are acyclic.

This is the coproduct (`J = Discrete J'`) instance of the general statement
`Work.TOOLKIT.Coprod.quasiIso_colimMap` that quasi-isomorphisms are stable under colimits of
any shape whose colimits are exact in `LightCondAb`: the coproduct `∐ j, K j` is the colimit of
the functor `Discrete.functor K`, and `Sigma.map f` is the corresponding colimit map. -/
theorem quasiIso_sigma (J : Type) (K L : J → Work.TOOLKIT.Cpx)
    [CategoryTheory.Limits.HasCoproduct K] [CategoryTheory.Limits.HasCoproduct L]
    (f : ∀ j, K j ⟶ L j) (hf : ∀ j, QuasiIso (f j)) :
    QuasiIso (CategoryTheory.Limits.Sigma.map f) := by
  -- The family `f` as a natural transformation of the corresponding `Discrete J`-indexed
  -- diagrams of complexes.
  let τ : Discrete.functor K ⟶ Discrete.functor L := Discrete.natTrans (fun j => f j.as)
  -- Colimits of the shape `Discrete J` are exact in `LightCondAb` (AB4), so the colimit of a
  -- family of quasi-isomorphisms is a quasi-isomorphism.
  have h := Work.TOOLKIT.Coprod.quasiIso_colimMap (J := Discrete J)
    (F := Discrete.functor K) (G := Discrete.functor L) τ (fun j => hf j.as)
  -- The colimit map of `τ` is the coproduct map of `f`.
  have heq : colimMap τ = Limits.Sigma.map f := by
    apply Limits.Sigma.hom_ext
    intro j
    calc Limits.Sigma.ι K j ≫ colimMap τ
        = τ.app (Discrete.mk j) ≫ Limits.Sigma.ι L j := ι_colimMap _ _
      _ = f j ≫ Limits.Sigma.ι L j := rfl
      _ = Limits.Sigma.ι K j ≫ Limits.Sigma.map f := (Limits.Sigma.ι_map f j).symm
  rwa [heq] at h

end Work.TOOLKIT.Sigma
