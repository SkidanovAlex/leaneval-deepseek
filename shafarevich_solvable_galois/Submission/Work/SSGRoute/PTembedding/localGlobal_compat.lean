import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.E0bClean.eBridge_natural
import Submission.Work.SSGRoute.brauer_single_place
import Submission.Work.SSGRoute.hbn_ext_units
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTembedding

open CategoryTheory SSGRoute.PTExt

/-! ## Two bookkeeping lemmas about `extHMap` and `extLoc`

The proof of the level-free local–global compatibility for the Brauer group transports the
`groupCohomology`-level theorem `Work.SSGRoute.brauer_single_place` along the E0b bridge
`E0bGroupCoeff.eBridge`, exactly as `E4Aux.ext_brauer_single_place` does for the
`extHRestrict`/`mk₀`-shaped hypothesis.  Here the hypothesis is stated through
`PTExt.extLoc` and `PTExt.extToIdeles`, so the bridge needs the identification

`extLoc w (extToIdeles a) = extHMap D_w.subtype (unitsToLocalUnits k K w) a`

which is the statement below: both sides are "restrict `a` to the decomposition group `D_w` and
push it forward along the local unit embedding `Kˣ → K_wˣ`".  The two identities used are the
`Rep`-morphism triangle `res_{D_w} (𝕀_K-incl) ≫ (𝕀_K → K_wˣ) = (Kˣ → K_wˣ)`
(`NK.HassePrinciple.res_ideleIncl_comp_ideleToLocalUnits`) and the fact that the outer
`mk₀ (unitRes _)` in `extHMap` is the identity (`Ext.mk₀_id_comp`, since `unitRes f = 𝟙 _` is
definitional). -/

/-- **`extHMap` is postcomposition with `mk₀` of the coefficient map.**

`extHMap f φ y = (extRes f y) ∘ mk₀ φ`, i.e. the outer `mk₀ (unitRes f)` occurring in the
definition of `extHMap` is the identity of `Ext^0` (`unitRes f = 𝟙 (unitRep H)` holds by `rfl`
and `mk₀` of an identity acts by `Ext.mk₀_id_comp`). -/
theorem extHMap_eq_comp {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (φ : Rep.res f A ⟶ B) {n : ℕ} (y : extH A n) :
    extHMap f φ y = (extRes f y).comp (Abelian.Ext.mk₀ φ) (add_zero n) := by
  unfold extHMap extRes
  rw [show unitRes f = 𝟙 (unitRep H) from rfl]
  exact Abelian.Ext.mk₀_id_comp _

/-- **Localising `extToIdeles a` at `w` is restricting `a` to the decomposition group of `w`
and pushing forward along `Kˣ → K_wˣ`.** -/
theorem extLoc_extToIdeles_eq (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (a : extH (unitsK k K) 2) :
    extLoc (k := k) w (extToIdeles (k := k) a) =
      extHMap (decompK (k := k) w).subtype (NK.HassePrinciple.unitsToLocalUnits k K w) a := by
  -- the restriction of `extToIdeles a` to `D_w` is `extRes a` followed by the restricted
  -- embedding of the principal idèles
  have h1 : extRes (decompK (k := k) w).subtype (extToIdeles (k := k) a)
      = (extRes (decompK (k := k) w).subtype a).comp
          (Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) w).subtype
            (NK.HassePrinciple.ideleIncl k K))) (add_zero 2) := by
    rw [extToIdeles, extRes, Abelian.Ext.mapExactFunctor_comp,
      Abelian.Ext.mapExactFunctor_mk₀]
    rfl
  rw [extLoc, h1]
  -- move the `w`-component of the idèles past the two degree-zero postcompositions
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero]
  rw [Abelian.Ext.mk₀_comp_mk₀]
  -- the coefficient triangle `𝕀_K ↪ K_wˣ` restricted to `D_w` equals `Kˣ ↪ K_wˣ`
  rw [NK.HassePrinciple.res_ideleIncl_comp_ideleToLocalUnits]
  rw [extHMap_eq_comp]

/-- **E8, restated (level-free local–global compatibility for the Brauer group).**

*Why the filed node is replaced rather than repaired.*  `Work.SSGRoute.PTembedding.localGlobal_annihilator`
(the node filed as "E8") quantifies over an **arbitrary** family `pair` of local pairings and concludes
that every functional on the dual cochains killing coboundaries and the locally trivial classes is a
finite sum of the values of *that* family.  As stated it is **false**: with the zero family it forces
every such functional to vanish.  It is also not repairable "as E8", for two reasons.
  (1) Its conclusion is the *annihilator realization* (the annihilator of the locally trivial classes
      contained in the image of the sum-of-local-pairings map), i.e. the hard half of the Poitou–Tate
      *middle exactness* (V equals W-perp), which is node E9's content and needs the *canonical* pairing
      of E7, not an arbitrary family satisfying some clause list.
  (2) Its shape is level-uniform in the sense that `PT/localTatePairing_deg02.lean` documents for the
      sibling clauses: a statement that realises functionals by local data attached to a *fixed* level
      is false as soon as one quantifies over higher levels `L ⊇ K` (their explicit counterexample:
      `k = K = ℚ`, `p = 2`, `M = 𝔽₂`, `L = ℚ(ζ₈)`: the level-`K` data has `𝔽₂`-dimension 1 while
      `H²((ℤ/2)², 𝔽₂)` has dimension 3).

*What E8 actually is.*  The local–global compatibility that the `Ext` core consumes is **level-free**:
a class of the Brauer group which is locally trivial at every place outside one `Gal(K/k)`-orbit is
**zero** — classically "no Brauer class is ramified at exactly one place".  In the generator-free
design (`SSGRoute/DESIGN_EXT.md` §2) this is the *only* compatibility input: *local perfectness
transfers through its injectivity*, while reciprocity is *free* from the exactness of the class
formation `Kˣ → 𝕀_K → C_K`.  The result is therefore **already proved**, in the NK vocabulary, as
`Work.SSGRoute.brauer_single_place` (E8-prime), which `SSGRoute/DESIGN_EXT.md` calls "the
generator-free substitute for E8".  The statement below is that result in the vocabulary of
`SSGRoute.PTDefs` (`extH`, `unitsK`, `idelesK`, `extToIdeles`, `extLoc`) — the shape in which the
`PTembedding`/E7 consumers look for the local–global compatibility, and the shape in which its
injectivity corollary is consumed.

*Intended consequence (to be added as a corollary in the same file).*  Taking the global class to be
the image of `a` under `extToIdeles`, and using that a locally trivial Brauer class is trivial, the
same proof gives the *usable* form: for every class `x` of the second Ext group over the ideles in the
range of `extToIdeles`, if its localisation vanishes at every place outside the orbit of `w₀`, then its
localisation at `w₀` vanishes as well ("the Brauer localisation is injective modulo the orbit"), which
is the input of the local-perfectness transfer in §2 of `DESIGN_EXT.md`.

*Proof route.*  Transport `Work.SSGRoute.brauer_single_place` along the group-cohomology ↔ `Ext`
bridge (cf. `PT/pt_ext_cohomology.lean`, `E0bGroupCoeff.eBridge` and its naturality
`E0bClean.eBridge_natural`), exactly as the worked analogue
`Submission/Work/SSGRoute/E4Aux/ext_brauer_single_place.lean` does for the shape with `extHRestrict`
and `mk₀ (NK.HassePrinciple.unitsToLocalUnits k K w)`.  The bridge to *this* statement's shape is the
equality of `extLoc w (extToIdeles a)` with that composite, which follows from the `.comp`-compatibility
of `extRes` with `Abelian.Ext.mk₀` (`Work.SSGRoute.extHRestrict_comp_mk0`) together with the
`Rep`-morphism identity `NK.HassePrinciple.res_ideleIncl_comp_ideleToLocalUnits` (in
`Submission/NK/HassePrinciple/LocalUnits_compatible.lean`, sorry-free) — both identified in review of
this statement. -/
theorem localGlobal_compat (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w₀ : NK.GlobalCFT.Place K) (a : SSGRoute.PTExt.extH (SSGRoute.PTExt.unitsK k K) 2)
    (h : ∀ w : NK.GlobalCFT.Place K, (∀ σ : K ≃ₐ[k] K, σ • w₀ ≠ w) →
      SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k) a) = 0) :
    a = 0 := by
  classical
  -- the E0b bridge at the level `K/k` and the `groupCohomology` class corresponding to `a`
  let e := Work.SSGRoute.E0bGroupCoeff.eBridge 2 (K ≃ₐ[k] K) (SSGRoute.PTExt.unitsK k K)
  let x : groupCohomology (SSGRoute.PTExt.unitsK k K) 2 := e.symm a
  have hax : e x = a := e.apply_symm_apply a
  -- it suffices to show that `x` is locally trivial away from the orbit of `w₀`
  have hx0 : x = 0 := by
    refine Work.SSGRoute.brauer_single_place k K x w₀ (fun w hw => ?_)
    -- the naturality of the bridge at the place `w`, with the decomposition group `D_w`
    have hnat := Work.SSGRoute.E0bClean.eBridge_natural
      (G := K ≃ₐ[k] K) (H := SSGRoute.PTExt.decompK (k := k) w)
      (A := SSGRoute.PTExt.unitsK k K) (B := NK.HassePrinciple.localUnitsRep k K w)
      (SSGRoute.PTExt.decompK (k := k) w).subtype
      (NK.HassePrinciple.unitsToLocalUnits k K w) 2 x
    -- the `Ext`-side form of the hypothesis at `w`
    have key : SSGRoute.PTExt.extHMap (SSGRoute.PTExt.decompK (k := k) w).subtype
        (NK.HassePrinciple.unitsToLocalUnits k K w) a = 0 := by
      rw [← extLoc_extToIdeles_eq (k := k) (K := K) w a]
      exact h w hw
    -- rewrite `locUnits` as a single change of group and coefficients
    rw [Work.SSGRoute.hbnAux_locUnits_eq_map (k := k) (L := K) w]
    refine (Work.SSGRoute.E0bGroupCoeff.eBridge 2 (SSGRoute.PTExt.decompK (k := k) w)
      (NK.HassePrinciple.localUnitsRep k K w)).injective ?_
    rw [map_zero, hnat, hax, key]
  calc a = e x := hax.symm
    _ = 0 := by rw [hx0, map_zero]

end Work.SSGRoute.PTembedding
