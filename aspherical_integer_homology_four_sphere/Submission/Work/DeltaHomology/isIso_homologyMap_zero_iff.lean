import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory

set_option linter.style.haveILetI false

/-- For a morphism `f : K ⟶ L` of chain complexes of `ℤ`-modules with `K.d 1 0 = 0` and
`L.d 1 0 = 0`, the map induced on `H₀` is an isomorphism iff `f.f 0` is.  Indeed
`ChainComplex.isIso_homologyι₀` (an instance) identifies `H₀` with `opcycles 0 = coker (d 1 0)`;
`homologyι_naturality` transfers the question to `opcyclesMap f 0`; and `isIso_pOpcycles` (using
`d 1 0 = 0`, with `prev 0 = 1` for `ComplexShape.down ℕ`) together with `p_opcyclesMap` transfers
it to `f.f 0`.  All the maps involved are isomorphisms, so this is a chain of the equivalences
`isIso_comp_left_iff` / `isIso_comp_right_iff` (or `IsIso.of_isIso_comp_left` /
`IsIso.of_isIso_comp_right`). -/
theorem isIso_homologyMap_zero_iff {K L : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L)
    (hK : K.d 1 0 = 0) (hL : L.d 1 0 = 0) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap f 0) ↔ CategoryTheory.IsIso (f.f 0) := by
  haveI hKι : IsIso (K.homologyι 0) := ChainComplex.isIso_homologyι₀ K
  haveI hLι : IsIso (L.homologyι 0) := ChainComplex.isIso_homologyι₀ L
  haveI hpK : IsIso (K.pOpcycles 0) :=
    HomologicalComplex.isIso_pOpcycles K 1 0 (by rw [ComplexShape.prev]; simp) hK
  haveI hpL : IsIso (L.pOpcycles 0) :=
    HomologicalComplex.isIso_pOpcycles L 1 0 (by rw [ComplexShape.prev]; simp) hL
  have hA_iff : IsIso (HomologicalComplex.homologyMap f 0) ↔
      IsIso (HomologicalComplex.opcyclesMap f 0) := by
    constructor
    · intro _
      have h2 : IsIso (K.homologyι 0 ≫ HomologicalComplex.opcyclesMap f 0) := by
        rw [← HomologicalComplex.homologyι_naturality f 0]
        infer_instance
      exact IsIso.of_isIso_comp_left (K.homologyι 0) (HomologicalComplex.opcyclesMap f 0)
    · intro _
      have h2 : IsIso (HomologicalComplex.homologyMap f 0 ≫ L.homologyι 0) := by
        rw [HomologicalComplex.homologyι_naturality f 0]
        infer_instance
      exact IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap f 0) (L.homologyι 0)
  have hB_iff : IsIso (HomologicalComplex.opcyclesMap f 0) ↔ IsIso (f.f 0) := by
    constructor
    · intro _
      have h2 : IsIso (f.f 0 ≫ L.pOpcycles 0) := by
        rw [← HomologicalComplex.p_opcyclesMap f 0]
        infer_instance
      exact IsIso.of_isIso_comp_right (f.f 0) (L.pOpcycles 0)
    · intro _
      have h2 : IsIso (K.pOpcycles 0 ≫ HomologicalComplex.opcyclesMap f 0) := by
        rw [HomologicalComplex.p_opcyclesMap f 0]
        infer_instance
      exact IsIso.of_isIso_comp_left (K.pOpcycles 0) (HomologicalComplex.opcyclesMap f 0)
  exact hA_iff.trans hB_iff

end Work.DeltaHomology
