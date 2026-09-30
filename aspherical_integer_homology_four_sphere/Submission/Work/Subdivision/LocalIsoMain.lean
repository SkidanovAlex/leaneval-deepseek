/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.LocalIsoCx
import Submission.Work.Subdivision.starLM_subdivCell

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The per-cell local condition is a local invariant

This file finishes the invariance of `PolyCW.LocallySpherical` under an
isomorphism of local structure (`PolyCW.LocalIso`): the generator of the local
complex is preserved (`locClsAux_map`, from `starLM_subdivCell`), hence so is the
local map (`locMapAux_comp_locCxIso`), and therefore the quasi-isomorphism of the
local maps is equivalent for the two cells
(`quasiIso_locMapAux_iff_of_localIso`, `quasiIso_locMapAux_iff_of_eq`,
`LocallySpherical.of_localIso`).

The corollary `LocallySpherical.of_representatives` is the interface for
certificates proved once per face-lattice type: given a choice of representative
`r e` of the local-isomorphism class of each cell, and the local condition at the
representatives, the local condition holds for every cell.
-/

namespace Work.Subdivision

open CategoryTheory

universe u

noncomputable section

namespace PolyCW

variable (P : PolyCW.{u}) {e f : P.Cell}

/-- The two cells of a local isomorphism have the same dimension. -/
theorem dim_eq_of_localIso (φ : LocalIso P e f) : P.dim f = P.dim e := by
  have h := φ.dim_eq ⟨e, le_rfl⟩
  rwa [φ.map_top] at h

/-- **The local isomorphism preserves the class of the subdivision chain of the
top cell.** -/
theorem locClsAux_map (φ : LocalIso P e f) {n : ℕ} (he : P.dim e = n) (hf : P.dim f = n) :
    (locCxIso P φ.toOrderIso).hom.f n (locClsAux P n ⟨e, he⟩) = locClsAux P n ⟨f, hf⟩ := by
  rw [locCxIso_hom_f]
  show locModLM P φ.toOrderIso n (Submodule.Quotient.mk (⟨subdivCell P n ⟨e, he⟩,
    subdivCell_mem_leSub P n ⟨e, he⟩⟩ : ↥(leSub P e n))) = _
  rw [locModLM_mk]
  show Submodule.Quotient.mk (starLMLeSub P φ.toOrderIso n ⟨subdivCell P n ⟨e, he⟩,
    subdivCell_mem_leSub P n ⟨e, he⟩⟩) = _
  congr 1
  apply Subtype.ext
  rw [starLMLeSub_coe]
  exact starLM_subdivCell P n ⟨e, he⟩ f φ hf

/-- **The local map is preserved by the isomorphism of local complexes.** -/
theorem locMapAux_comp_locCxIso (hdd : P.HasDdZero) (haug : P.HasAugZero) (φ : LocalIso P e f)
    {n : ℕ} (he : P.dim e = n) (hf : P.dim f = n) :
    locMapAux P hdd haug n ⟨f, hf⟩ =
      locMapAux P hdd haug n ⟨e, he⟩ ≫ (locCxIso P φ.toOrderIso).hom := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, locMapAux_f_eq, locMapAux_f_eq, Category.assoc, spanMap_comp,
    locClsAux_map P φ he hf]

/-- **The local condition is invariant under an isomorphism of local structure.** -/
theorem quasiIso_locMapAux_iff_of_localIso (hdd : P.HasDdZero) (haug : P.HasAugZero)
    (φ : LocalIso P e f) {n : ℕ} (he : P.dim e = n) (hf : P.dim f = n) :
    QuasiIso (locMapAux P hdd haug n ⟨e, he⟩) ↔ QuasiIso (locMapAux P hdd haug n ⟨f, hf⟩) := by
  have hsq := locMapAux_comp_locCxIso P hdd haug φ he hf
  constructor
  · intro h
    rw [hsq]
    infer_instance
  · intro h
    refine quasiIso_of_iso_square (Iso.refl _) (locCxIso P φ.toOrderIso)
      (locMapAux P hdd haug n ⟨f, hf⟩) (locMapAux P hdd haug n ⟨e, he⟩) ?_ h
    simpa using hsq

/-- The same statement with the two dimensions presented as possibly different
natural numbers. -/
theorem quasiIso_locMapAux_iff_of_eq (hdd : P.HasDdZero) (haug : P.HasAugZero)
    (φ : LocalIso P e f) {n m : ℕ} (h : n = m) (he : P.dim e = n) (hf : P.dim f = m) :
    QuasiIso (locMapAux P hdd haug n ⟨e, he⟩) ↔ QuasiIso (locMapAux P hdd haug m ⟨f, hf⟩) := by
  subst h
  exact quasiIso_locMapAux_iff_of_localIso P hdd haug φ he hf

/-- **Transport of the local condition along a local isomorphism.** -/
theorem LocallySpherical.transfer (hdd : P.HasDdZero) (haug : P.HasAugZero) (φ : LocalIso P e f)
    (h : QuasiIso (locMap P hdd haug f)) : QuasiIso (locMap P hdd haug e) :=
  (quasiIso_locMapAux_iff_of_eq P hdd haug φ (n := P.dim e) (m := P.dim f)
    (dim_eq_of_localIso P φ).symm rfl rfl).mpr h

/-- **The local condition follows from its truth at representatives of the
local-isomorphism classes.** -/
theorem LocallySpherical.of_representatives (hdd : P.HasDdZero) (haug : P.HasAugZero)
    (r : P.Cell → P.Cell) (hiso : ∀ e, Nonempty (LocalIso P e (r e)))
    (h : ∀ e, QuasiIso (locMap P hdd haug (r e))) : LocallySpherical P hdd haug :=
  fun e => LocallySpherical.transfer P hdd haug (Classical.choice (hiso e)) (h e)

end PolyCW

end

end Work.Subdivision
