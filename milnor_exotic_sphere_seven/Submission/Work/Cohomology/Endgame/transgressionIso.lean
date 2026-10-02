import Submission.Work.Cohomology.Endgame.overlapCap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The two Mayer–Vietoris connecting isomorphisms of the transgression identity

`Endgame/NOTES.md` §25(a)–(b): the transgression identity
`U₀ (a ⌢ c) = ± (ρ a) ⌢ (T₀ c)` needs the two connecting maps of the Mayer–Vietoris sequences as
*isomorphisms*:

* `ovlT` — the relative connecting map, from the relative homology of `(X,A)` in degree `8` to the
  relative homology of the overlap `(↥(U∩V), ovlA)` in degree `7`: the conjugate of
  `cruxδ X A U V 7` by the two quasi-isomorphisms `relMV_quasiIso` (top term) and
  `relMVUV_quasiIso` (§21, overlap term);
* `ovlU` — the absolute connecting map, from the homology of `X` in degree `4` to the homology of
  the overlap in degree `3`: the conjugate of the connecting map of the small-chains
  Mayer–Vietoris sequence `mvSmall_shortExact U V` by the quasi-isomorphisms `smallToSing U V` and
  `smallInToSingA U V (U ∩ V)`.

Both are isomorphisms as soon as the corresponding connecting maps are (`hδ`, `hδ'`), which for
`(Vk(-2), Mk(-2))` is the proved `Crux.vkOvlDefs.vkδabs_isIso` (absolute) together with
`Crux.vkOvlDefs.vkSabs_X₂_homology_isZero` (the vanishing of the two middle homologies); the
relative one is the corresponding statement for the two chart pairs.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Work.Cohomology

noncomputable section

/-- **The relative Mayer–Vietoris connecting isomorphism of the transgression identity**: the
conjugate of `cruxδ X A U V 7` by the two quasi-isomorphisms, from `H₈(X,A)` to `H₇(U∩V, U∩V∩A)`. -/
noncomputable def ovlT (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (hδ : IsIso (cruxδ X A U V 7)) :
    (relChains X A).homology 8 ≃ₗ[ℤ]
      (relChains (TopCat.of ↥(U ∩ V)) (ovlA X A U V)).homology 7 := by
  classical
  let phi := Classical.choose (relMV_quasiIso X A U V hU hV hcov)
  have hphi := (Classical.choose_spec (relMV_quasiIso X A U V hU hV hcov)).1
  haveI h1 : IsIso (HomologicalComplex.homologyMap phi 8) := hphi 8
  haveI h2 : IsIso (HomologicalComplex.homologyMap (relMVUVPhi X A U V) 7) :=
    relMVUV_quasiIso X A U V hU hV hcov 7
  haveI h3 : IsIso (cruxδ X A U V 7) := hδ
  exact ((asIso (HomologicalComplex.homologyMap phi 8)).toLinearEquiv).symm.trans
    (((asIso (cruxδ X A U V 7)).toLinearEquiv).trans
      ((asIso (HomologicalComplex.homologyMap (relMVUVPhi X A U V) 7)).toLinearEquiv))

/-- The defining property of `ovlT`: on an element it is the composite of the inverse of the
quasi-isomorphism on the top term, the relative Mayer–Vietoris connecting map, and the
quasi-isomorphism on the overlap term.  (The two `IsIso` arguments are the quasi-isomorphism
instances, passed explicitly since the statement itself mentions `asIso`.) -/
theorem ovlT_eq (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (hδ : IsIso (cruxδ X A U V 7))
    (h1 : IsIso (HomologicalComplex.homologyMap
      (Classical.choose (relMV_quasiIso X A U V hU hV hcov)) 8))
    (h2 : IsIso (HomologicalComplex.homologyMap (relMVUVPhi X A U V) 7))
    (c : (relChains X A).homology 8) :
    ovlT X A U V hU hV hcov hδ c
      = (asIso (HomologicalComplex.homologyMap (relMVUVPhi X A U V) 7)).toLinearEquiv
          ((asIso (cruxδ X A U V 7)).toLinearEquiv
            (((asIso (HomologicalComplex.homologyMap
              (Classical.choose (relMV_quasiIso X A U V hU hV hcov)) 8)).toLinearEquiv).symm c)) := by
  haveI := h1
  haveI := h2
  haveI := hδ
  rw [ovlT]
  simp only [LinearEquiv.trans_apply]

/-- **The absolute Mayer–Vietoris connecting isomorphism of the transgression identity**: the
conjugate of the connecting map of the small-chains Mayer–Vietoris sequence by the two
quasi-isomorphisms, from `H₄(X)` to `H₃(U∩V)`.  The connecting map itself (an iso, e.g. the
proved `Crux.vkOvlDefs.vkδabs_isIso` for `(Vk(-2), Mk(-2))`) is passed as `δmv` so that this
definition is independent of the spelling of its `Rel` argument. -/
noncomputable def ovlU (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ)
    (δmv : (smallChains U V).homology 4 ≃ₗ[ℤ] (smallInChains U V (U ∩ V)).homology 3) :
    (singularChains ℤ X).homology 4 ≃ₗ[ℤ]
      (singularChains ℤ (TopCat.of ↥(U ∩ V))).homology 3 := by
  classical
  haveI i1 : IsIso (HomologicalComplex.homologyMap (smallToSing U V) 4) :=
    smallChains_homology_iso U V hU hV hcov 4
  haveI i2 : IsIso (HomologicalComplex.homologyMap (smallInToSingA U V (U ∩ V)) 3) :=
    isIso_smallInToSingA U V (U ∩ V) hU hV hcov 3
  exact ((asIso (HomologicalComplex.homologyMap (smallToSing U V) 4)).toLinearEquiv).symm.trans
    (δmv.trans
      ((asIso (HomologicalComplex.homologyMap (smallInToSingA U V (U ∩ V)) 3)).toLinearEquiv))

/-- The defining property of `ovlU`. -/
theorem ovlU_eq (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ)
    (δmv : (smallChains U V).homology 4 ≃ₗ[ℤ] (smallInChains U V (U ∩ V)).homology 3)
    (h1 : IsIso (HomologicalComplex.homologyMap (smallToSing U V) 4))
    (h2 : IsIso (HomologicalComplex.homologyMap (smallInToSingA U V (U ∩ V)) 3))
    (c : (singularChains ℤ X).homology 4) :
    ovlU X U V hU hV hcov δmv c
      = (asIso (HomologicalComplex.homologyMap (smallInToSingA U V (U ∩ V)) 3)).toLinearEquiv
          (δmv (((asIso (HomologicalComplex.homologyMap (smallToSing U V) 4)).toLinearEquiv).symm c)) := by
  haveI := h1
  haveI := h2
  rw [ovlU]
  simp only [LinearEquiv.trans_apply]

end

end Work.Cohomology
