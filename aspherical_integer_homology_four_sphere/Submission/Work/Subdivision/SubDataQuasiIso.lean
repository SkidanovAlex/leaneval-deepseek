/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.SubDataSES
import Submission.Work.Subdivision.quasiIso_tau2
import Submission.Work.Subdivision.quasiIso_tau2_poly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The five lemma for a compatible subcomplex

If a chain map `f : C ⟶ C'` carries `S` into `S'`, the induced maps on the
subcomplexes and on the quotients are quasi-isomorphisms exactly when `f` is
(here: the direction needed for the skeletal induction — `f` is a
quasi-isomorphism as soon as its restriction and the induced quotient map are).

The diagram is the morphism of short exact sequences
`S.shortComplexHom S' f hf w w'`, and the five lemma for the middle term is
`Work.Subdivision.quasiIso_tau2_poly` (Mathlib has the companion statement for
the third term, `HomologicalComplex.HomologySequence.quasiIso_τ₃`).
-/

namespace Work.Subdivision

open CategoryTheory

variable {C C' : ChainComplex (ModuleCat ℤ) ℕ}

/-- **Five lemma for a compatible subcomplex.**  `f` is a quasi-isomorphism as
soon as its restriction to `S → S'` and the induced map `C/S → C'/S'` are. -/
theorem quasiIso_of_sub_quot (S : SubData C) (S' : SubData C') (f : C ⟶ C')
    (hf : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom)
    (w : S.incl ≫ S.proj = 0) (w' : S'.incl ≫ S'.proj = 0)
    (h₁ : QuasiIso (S.restrictMap S' f hf)) (h₃ : QuasiIso (S.quotMap S' f hf)) :
    QuasiIso f := by
  have h₁' : QuasiIso (S.shortComplexHom S' f hf w w').τ₁ := by
    rw [SubData.shortComplexHom_τ₁]
    exact h₁
  have h₃' : QuasiIso (S.shortComplexHom S' f hf w w').τ₃ := by
    rw [SubData.shortComplexHom_τ₃]
    exact h₃
  have h : QuasiIso (S.shortComplexHom S' f hf w w').τ₂ := quasiIso_tau2_poly
    (S.shortComplexHom S' f hf w w')
    (shortComplexOf_shortExact S w) (shortComplexOf_shortExact S' w') h₁' h₃'
  rwa [SubData.shortComplexHom_τ₂] at h

end Work.Subdivision
