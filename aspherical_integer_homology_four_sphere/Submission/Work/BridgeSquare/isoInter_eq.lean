/-
# `BridgeSquare/isoInter_eq.lean` — the two forms of the `A ∩ B` identification agree

`Work.BridgeSquare.isoInter` (cusp-major, the one used by the models) and
`Work.BridgeSquare.isoInterAlt` (the glued boundary form `isoABA`, transported along the canonical
homeomorphism `isoDopCop`) are two isomorphisms

`H_k(A ∩ B) ≅ H_k(⊔_v ∂[-1,1]² × T²_v)`,

built from *different* homotopy equivalences of `A ∩ B` onto that space: both start with the same
two factors

* `((homeoAnnXSrc a).symm.toHomotopyEquiv) : A ∩ B ≃ₕ AnnX a`,
* `(homeoAnnXAnnSig a).toHomotopyEquiv : AnnX a ≃ₕ AnnSig a`,

and then

* `isoInter` continues with the radial rescaling `heAnnBdry a : AnnSig a ≃ₕ BdrySig a`
  (`eABCompat`), while
* `isoABA` continues with `(heAnnBdry a).trans (homeoBdrySubSig a).symm.toHomotopyEquiv`
  (`eABACompat`), i.e. with the *same* rescaling followed by the canonical homeomorphism
  `homeoBdrySubSig a : {q : a.Y // q ∈ a.boundarySet} ≃ₜ BdrySig a` read backwards;
* `isoInterAlt = isoABA ≪≫ isoDopCop` then returns to the cusp-major form by `homeoBdrySubSig a`.

So the only difference between `isoInter` and `isoInterAlt` is the insertion of the pair
`(homeoBdrySubSig a).symm.toHomotopyEquiv`, `(homeoBdrySubSig a).toHomotopyEquiv` — a pair of
*inverse* homotopy equivalences, which cancels on homology.  This file makes that cancellation
precise:

* `intHomologyIsoOfHomotopyEquiv_toFun_congr` — the homology isomorphism induced by a homotopy
  equivalence depends only on its *forward map* (both are the homology map of the chain map of
  `e.toFun`), so it can be compared through `toFun`;
* `intHomologyIsoOfHomotopyEquiv_trans_eq` — `e ≃ₕ f` induces the composite of the induced maps
  (this is `Work.BridgeSquare.intHomologyIsoOfHomotopyEquiv_trans`, restated in the composite
  form used below);
* `intHomologyIsoOfHomotopyEquiv_refl` — the identity homotopy equivalence induces the identity;
* `intHomologyIsoOfHomotopyEquiv_homeomorph_symm_trans` — for a homeomorphism `φ`, the induced
  isomorphisms of `φ.symm` and of `φ` cancel.

The main theorem `isoInter_eq` is then `Iso.trans_assoc` together with the three lemmas above: the
inserted pair is exactly `symm ≪≫ toFun` of `homeoBdrySubSig`.
-/
import Mathlib
import Submission.Work.BridgeSquare.Spaces
import Submission.Work.BridgeSquare.intHomologyIsoOfHomotopyEquiv_trans

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1000000

open CategoryTheory

namespace Work.BridgeSquare

noncomputable section

/-! ## §1  The homology isomorphism of a homotopy equivalence depends only on its forward map -/

/-- **The induced homology isomorphism only sees the forward map of the homotopy equivalence.**
Both `intHomologyIsoOfHomotopyEquiv e k` and `intHomologyIsoOfHomotopyEquiv f k` have as their
forward map the homology map of the chain map of `toFun` (`intHomologyIsoOfHomotopyEquiv_hom`), so
they are equal as soon as `e.toFun = f.toFun`. -/
theorem intHomologyIsoOfHomotopyEquiv_toFun_congr {X Y : TopCat}
    {e f : ContinuousMap.HomotopyEquiv ↥X ↥Y} (h : e.toFun = f.toFun) (k : ℕ) :
    intHomologyIsoOfHomotopyEquiv e k = intHomologyIsoOfHomotopyEquiv f k := by
  apply CategoryTheory.Iso.ext
  rw [intHomologyIsoOfHomotopyEquiv_hom e k, intHomologyIsoOfHomotopyEquiv_hom f k]
  rw [h]

/-- **The identity homotopy equivalence induces the identity**, in the form in which the composite
of the induced isomorphisms of a homotopy equivalence and of its "inverse" is computed: its forward
map is `𝟙`, whose chain map is the identity chain map, whose homology map is the identity. -/
theorem intHomologyIsoOfHomotopyEquiv_refl (X : TopCat) (k : ℕ) :
    intHomologyIsoOfHomotopyEquiv (X := X) (Y := X) (ContinuousMap.HomotopyEquiv.refl ↥X) k
      = CategoryTheory.Iso.refl _ := by
  apply CategoryTheory.Iso.ext
  rw [Work.BridgeSquare.intHomologyIsoOfHomotopyEquiv_hom]
  rw [show TopCat.ofHom (ContinuousMap.HomotopyEquiv.refl ↥X).toFun = 𝟙 X from rfl]
  rw [show Work.Cohomology.chainMap ℤ X X (𝟙 X) = 𝟙 (Work.Cohomology.singularChains ℤ X) from
      CategoryTheory.Functor.map_id _ X]
  exact HomologicalComplex.homologyMap_id _ k

/-! ## §2  Functoriality in the composite form used below -/

/-- **The isomorphism induced by a composite homotopy equivalence is the composite of the induced
isomorphisms.**  This is `Work.BridgeSquare.intHomologyIsoOfHomotopyEquiv_trans` with the auxiliary
`intHomologyIsoOfHomotopyEquivComp` unfolded. -/
theorem intHomologyIsoOfHomotopyEquiv_trans_eq {X Y Z : TopCat}
    (e : ContinuousMap.HomotopyEquiv ↥X ↥Y) (f : ContinuousMap.HomotopyEquiv ↥Y ↥Z) (k : ℕ) :
    intHomologyIsoOfHomotopyEquiv (e.trans f) k =
      intHomologyIsoOfHomotopyEquiv e k ≪≫ intHomologyIsoOfHomotopyEquiv f k :=
  intHomologyIsoOfHomotopyEquiv_trans e f k

/-! ## §3  A homeomorphism and its inverse cancel -/

/-- **The isomorphisms induced by a homeomorphism `φ` and by `φ.symm` cancel.**
`φ.symm.toHomotopyEquiv.trans φ.toHomotopyEquiv` has forward map `φ ∘ φ.symm = id`
(`Homeomorph.apply_symm_apply`), so by §1 it induces the same isomorphism as the identity homotopy
equivalence, which is the identity by §2. -/
theorem intHomologyIsoOfHomotopyEquiv_homeomorph_symm_trans {X Y : TopCat} (φ : ↥X ≃ₜ ↥Y) (k : ℕ) :
    intHomologyIsoOfHomotopyEquiv (X := Y) (Y := X) (φ.symm.toHomotopyEquiv) k ≪≫
      intHomologyIsoOfHomotopyEquiv (X := X) (Y := Y) (φ.toHomotopyEquiv) k
      = CategoryTheory.Iso.refl _ := by
  rw [← intHomologyIsoOfHomotopyEquiv_trans_eq (φ.symm.toHomotopyEquiv) (φ.toHomotopyEquiv) k]
  rw [intHomologyIsoOfHomotopyEquiv_toFun_congr
      (e := φ.symm.toHomotopyEquiv.trans φ.toHomotopyEquiv)
      (f := ContinuousMap.HomotopyEquiv.refl ↥Y) ?_ k]
  · exact intHomologyIsoOfHomotopyEquiv_refl Y k
  · ext y
    show φ (φ.symm y) = y
    exact Homeomorph.apply_symm_apply φ y

/-! ## §4  The two forms of the `A ∩ B` identification -/

/-- **`isoInter = isoInterAlt`.**  Unfolding the two definitions, the statement is
`H(eABCompat) = H(eABACompat) ≪≫ H(homeoBdrySubSig)`.  Now
`eABACompat = eABCompat.trans (homeoBdrySubSig a).symm.toHomotopyEquiv`, because the two homotopy
equivalences are the same composite of the homeomorphism `homeoAnnXSrc`, of the homeomorphism
`homeoAnnXAnnSig` and of the radial rescaling `heAnnBdry`, followed by
`(homeoBdrySubSig a).symm.toHomotopyEquiv` in the second case; the forward maps therefore agree
(associativity of composition) and §1 applies.  §2 replaces the isomorphism of the composite by the
composite of the isomorphisms, associativity of `≪≫` regroups the factors, and §3 cancels the
inserted pair `(homeoBdrySubSig a).symm.toHomotopyEquiv`, `(homeoBdrySubSig a).toHomotopyEquiv`
against the last factor `isoDopCop`. -/
theorem isoInter_eq [rt : Work.Space.RTData] (k : ℕ) :
    Work.BridgeSquare.isoInter (rt := rt) k = Work.BridgeSquare.isoInterAlt (rt := rt) k := by
  show intHomologyIsoOfHomotopyEquiv (X := Iop) (Y := Cop) (Work.Space.Split.eABCompat rt.core) k
      = intHomologyIsoOfHomotopyEquiv (X := Iop) (Y := Dop)
            (Work.Space.Split.eABACompat rt.core) k
        ≪≫ intHomologyIsoOfHomotopyEquiv (X := Dop) (Y := Cop)
              ((Work.Space.Split.homeoBdrySubSig rt.core).toHomotopyEquiv) k
  rw [intHomologyIsoOfHomotopyEquiv_toFun_congr (X := Iop) (Y := Dop)
        (e := Work.Space.Split.eABACompat rt.core)
        (f := (Work.Space.Split.eABCompat rt.core).trans
                ((Work.Space.Split.homeoBdrySubSig rt.core).symm).toHomotopyEquiv) (by rfl) k]
  rw [intHomologyIsoOfHomotopyEquiv_trans_eq (X := Iop) (Y := Cop) (Z := Dop)
        (Work.Space.Split.eABCompat rt.core)
        ((Work.Space.Split.homeoBdrySubSig rt.core).symm).toHomotopyEquiv k]
  rw [CategoryTheory.Iso.trans_assoc]
  rw [intHomologyIsoOfHomotopyEquiv_homeomorph_symm_trans (X := Dop) (Y := Cop)
        (Work.Space.Split.homeoBdrySubSig rt.core) k]
  rw [CategoryTheory.Iso.trans_refl]

end

end Work.BridgeSquare
