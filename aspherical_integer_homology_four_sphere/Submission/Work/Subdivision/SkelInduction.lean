/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.SkelLevel
import Submission.Work.Subdivision.rel_hf
import Submission.Work.Subdivision.quasiIso_subdiv_of_maxDim
import Submission.Work.Subdivision.cellRelIso_subdivSkel
import Submission.Work.Subdivision.subdivSkel_zero
import Submission.Work.Subdivision.SubDataQuasiIso

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The skeletal induction for the subdivision quasi-isomorphism

This file assembles the proof that `PolyCW.subdiv` is a quasi-isomorphism from

* the base case `subdivSkel_zero`,
* the five lemma `Work.Subdivision.quasiIso_of_sub_quot`, applied to the short
  exact sequences `0 → cellRel n → (cellSub (n+1)).chain → …` and
  `0 → sdRel n → (sdSub (n+1)).chain → …`,
* the identification of the relative subcomplexes with the previous skeleta
  (`PolyCW.cellRelIso`, `PolyCW.sdRelIso`) and the naturality square
  `PolyCW.cellRelIso_subdivSkel`,
* the **local condition** `PolyCW.gradeMap` on the successive quotients,
  supplied as the hypothesis `hlocal`.

`hlocal n` is the quasi-isomorphism of the `n`-th graded piece of the
subdivision map; it is what the certificate data for the face lattices supplies
(the sphere condition on `∂L_e` together with the generator condition).
-/

namespace Work.Subdivision

open CategoryTheory

universe u

noncomputable section

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-- Quasi-isomorphisms are invariant under an isomorphism of squares: if
`e.hom ≫ f = f' ≫ e'.hom` with `e`, `e'` isomorphisms and `f` a
quasi-isomorphism, then so is `f'`. -/
theorem quasiIso_of_iso_square {A B A' B' : ChainComplex (ModuleCat ℤ) ℕ}
    (e : A' ≅ A) (e' : B' ≅ B) (f : A ⟶ B) (f' : A' ⟶ B')
    (h : e.hom ≫ f = f' ≫ e'.hom) (hf : QuasiIso f) : QuasiIso f' := by
  have h1 : f' = e.hom ≫ f ≫ e'.inv := by
    rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h1]
  haveI : QuasiIso f := hf
  infer_instance

namespace PolyCW

variable (P : PolyCW.{u})

/-- The map on the `n`-th graded pieces of the subdivision. -/
noncomputable def gradeMap (hdd : P.HasDdZero) (haug : P.HasAugZero) (n : ℕ) :
    (cellRel P hdd n).quot ⟶ (sdRel P n).quot :=
  (cellRel P hdd n).quotMap (sdRel P n) (subdivSkel P hdd haug (n + 1)) (Work.Subdivision.rel_hf P hdd haug n)

/-- **The induction step.**  If the subdivision is a quasi-isomorphism on the
`n`-skeleton and on the `n`-th graded piece, then it is on the `(n+1)`-skeleton. -/
theorem subdivSkel_succ (hdd : P.HasDdZero) (haug : P.HasAugZero) (n : ℕ)
    (ih : QuasiIso (subdivSkel P hdd haug n)) (hq : QuasiIso (gradeMap P hdd haug n)) :
    QuasiIso (subdivSkel P hdd haug (n + 1)) := by
  refine quasiIso_of_sub_quot (cellRel P hdd n) (sdRel P n) (subdivSkel P hdd haug (n + 1))
    (Work.Subdivision.rel_hf P hdd haug n) (incl_proj _) (incl_proj _) ?_ hq
  exact quasiIso_of_iso_square (cellRelIso P hdd n) (sdRelIso P n)
    (subdivSkel P hdd haug n)
    ((cellRel P hdd n).restrictMap (sdRel P n) (subdivSkel P hdd haug (n + 1))
      (Work.Subdivision.rel_hf P hdd haug n))
    (Work.Subdivision.cellRelIso_subdivSkel P hdd haug n (Work.Subdivision.rel_hf P hdd haug n)) ih

/-- **The skeletal induction**: the subdivision is a quasi-isomorphism on every
skeleton, assuming the graded pieces are. -/
theorem subdivSkel_quasiIso (hdd : P.HasDdZero) (haug : P.HasAugZero)
    (hlocal : ∀ n, QuasiIso (gradeMap P hdd haug n)) :
    ∀ n, QuasiIso (subdivSkel P hdd haug n) := by
  intro n
  induction n with
  | zero => exact Work.Subdivision.subdivSkel_zero P hdd haug
  | succ n ih => exact subdivSkel_succ P hdd haug n ih (hlocal n)

/-- **The subdivision chain map is a quasi-isomorphism.**  The hypothesis
`hlocal` is the quasi-isomorphism on the `n`-th graded pieces of the skeletal
filtrations; it is supplied by the certificate data for the face lattices of the
cells (the sphere condition on `∂L_e` together with the generator condition). -/
theorem subdiv_quasiIso (hdd : P.HasDdZero) (haug : P.HasAugZero)
    (hlocal : ∀ n, QuasiIso (gradeMap P hdd haug n)) :
    QuasiIso (subdiv P hdd haug) :=
  Work.Subdivision.quasiIso_subdiv_of_maxDim P hdd haug (subdivSkel_quasiIso P hdd haug hlocal P.maxDim)

end PolyCW

end

end Work.Subdivision
