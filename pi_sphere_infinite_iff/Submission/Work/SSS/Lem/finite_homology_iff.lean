import Mathlib
import Submission.Work.SSS.baseRowDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Finiteness of the homology of a chain complex of `ℤ`-modules

For a chain complex `K` of `ℤ`-modules indexed by `ℕ`, the `n`-th homology `K.homology n`
is the quotient of the `n`-cycles `ker (K.d n (n - 1))` by the `n`-boundaries
`range (K.d (n + 1) n)`.  The point of this file is to record this fact in the form needed by the
spectral-sequence argument: the homology is finitely generated as a `ℤ`-module exactly when the
quotient of the cycles by the boundaries is, the latter being expressed by
`Work.SSS.FgQuot (LinearMap.range (K.d (n + 1) n).hom) (LinearMap.ker (K.d n (n - 1)).hom)`.

The substantive input is mathlib's explicit `LeftHomologyData` for a short complex of modules
(`ShortComplex.moduleCatLeftHomologyData`, `ShortComplex.moduleCatHomologyIso`), which presents
`S.homology` as the quotient of `LinearMap.ker S.g.hom` by `LinearMap.range S.moduleCatToCycles`.
-/

set_option autoImplicit false

namespace Work.SSS.Lem

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **Finiteness of the homology of a short complex of modules.**  For a short complex `S` of
`R`-modules, `S.homology` is a finitely generated `R`-module if and only if the quotient
`ker S.g / im S.f` is; the latter is the subquotient computed by `Work.SSS.FgQuot`.

Indeed `S.homology ≅ ker S.g ⧸ im S.f` by mathlib's explicit left homology data of a short complex
of modules, and `S.moduleCatToCycles : S.X₁ →ₗ LinearMap.ker S.g` has range
`LinearMap.comap (LinearMap.ker S.g).subtype S.f.range`, so that quotient is the image of `ker S.g`
inside `S.X₂ ⧸ im S.f`; the first isomorphism theorem identifies the two. -/
theorem finite_homology_iff_shortComplex {R : Type*} [CommRing R]
    (S : ShortComplex (ModuleCat R)) :
    Module.Finite R S.homology ↔ Work.SSS.FgQuot S.f.hom.range S.g.hom.ker := by
  -- the range of `moduleCatToCycles` is `im S.f` viewed inside `ker S.g`
  have hB' : S.moduleCatToCycles.range
      = Submodule.comap (S.g.hom.ker).subtype (S.f.hom.range) :=
    LinearMap.range_codRestrict _ _ _
  -- the linear map `ker S.g → S.X₂ ⧸ im S.f` restricted from the quotient projection
  have hfker : ((Submodule.mkQ S.f.hom.range).comp (S.g.hom.ker).subtype).ker
      = S.moduleCatToCycles.range := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, hB']
  have hfrange : ((Submodule.mkQ S.f.hom.range).comp (S.g.hom.ker).subtype).range
      = (S.g.hom.ker).map (Submodule.mkQ S.f.hom.range) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  -- mathlib's explicit description of the homology of a short complex of modules
  have h1 : Module.Finite R S.homology ↔
      Module.Finite R (↥(S.g.hom.ker) ⧸ S.moduleCatToCycles.range) :=
    Module.Finite.equiv_iff
      (S.moduleCatHomologyIso ≪≫
        eqToIso (ShortComplex.moduleCatLeftHomologyData_H S)).toLinearEquiv
  -- the first isomorphism theorem for `ker S.g → S.X₂ ⧸ im S.f`
  rw [Work.SSS.FgQuot, ← hfrange]
  exact h1.trans
    ((Module.Finite.equiv_iff (Submodule.quotEquivOfEq _ _ hfker.symm)).trans
      ((Module.Finite.equiv_iff (LinearMap.quotKerEquivRange _)).trans Module.Finite.iff_fg))

/-- **Finiteness of the `n`-th homology of a chain complex of `ℤ`-modules.**  The `n`-th homology
`K.homology n` is finitely generated if and only if the quotient of the `n`-cycles by the
`n`-boundaries is.  This is the form in which the finiteness hypotheses on the `E²` page of a
spectral sequence are stated. -/
theorem finite_homology_iff (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    Module.Finite ℤ (K.homology n) ↔
      Work.SSS.FgQuot (LinearMap.range (K.d (n + 1) n).hom) (LinearMap.ker (K.d n (n - 1)).hom) := by
  -- `K.homology n` is the homology of the short complex `K.X (n+1) → K.X n → K.X (n-1)`,
  -- which is `K.sc' (n+1) n (n-1)` up to the identification of `c.prev n` and `c.next n`
  have hp : (ComplexShape.down ℕ).prev n = n + 1 := by simp [ComplexShape.prev]
  have hq : (ComplexShape.down ℕ).next n = n - 1 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      rw [ComplexShape.next_eq_self' (ComplexShape.down ℕ) 0 (fun k hk => Nat.succ_ne_zero k hk)]
    · rw [ComplexShape.next_eq' (ComplexShape.down ℕ) (i := n) (j := n - 1)
        (ComplexShape.down_mk n (n - 1) (Nat.sub_add_cancel h))]
  have hiso : Module.Finite ℤ (K.homology n) ↔
      Module.Finite ℤ ((K.sc' (n + 1) n (n - 1)).homology) :=
    Module.Finite.equiv_iff
      (ShortComplex.homologyMapIso (K.isoSc' (n + 1) n (n - 1) hp hq)).toLinearEquiv
  rw [hiso]
  exact finite_homology_iff_shortComplex (K.sc' (n + 1) n (n - 1))

end

end Work.SSS.Lem
