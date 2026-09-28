import Mathlib
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.csrGeom
import Submission.Work.Serre.csrExcisionRat
import Submission.Work.Serre.serreE2d
import Submission.Work.Serre.cubeAmbient_isZero
import Submission.Work.Serre.cubeBdry_isZero
import Submission.Work.Serre.cubeRelIso
import Submission.Work.Serre.Csr.Base
import Submission.Work.Serre.Csr.Chain
import Submission.Work.Serre.Csr.Target
import Submission.Work.Serre.Csr.Transfer
import Submission.Work.Serre.Csr.Section
import Submission.Work.Serre.Csr.Source
import Submission.Work.Serre.csrGlue
import Submission.Work.Serre.csrPairFunctoriality
import Submission.Work.Serre.Csr.Comp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

/-- **The per-cell computation of the rational cell step.**  For a Serre fibration `q : E → Z` with
`Z = attachCells n Y ι f`, whose fibres are rationally acyclic below `N`, the map of pairs
`(q⁻¹o_i, q⁻¹(o_i ∖ {c_i})) → (o_i, o_i ∖ {c_i})` (where `o_i = csrOpenBall i` is the open half-ball
around the centre `c_i = csrCentre i` of the `i`-th cell) induced by `q` is an isomorphism on
relative rational homology in degrees `≤ N`.

Both sides of the pair are `ℚ` in degree `n+2` and `0` in every other degree.  The target side is
computed by transporting, along the deformation of the punctured half-ball onto its boundary sphere
and the homeomorphism of the closed half-ball with the cube `I^{n+2}`, to the cube pair
`(I^{n+2}, ∂I^{n+2})`; the source side to the cube pair `(τ^*E, τ^*E|_{∂I^{n+2}})` of the pullback of
`q` along the characteristic map `τ`.  There, `Work.Serre.SerreE2d` computes
`H_{k+n+2}(τ^*E, τ^*E|_{∂I^{n+2}}) ≅ H_k(F;ℚ)` and `H_{k+n+2}(I^{n+2}, ∂I^{n+2}) ≅ H_k(pt;ℚ)`
(this is `Work.Serre.cubePairPUnit_isZero`/`Work.Serre.cubePair_iso` in degree `k`), the vanishing
below the cube dimension is `Work.Serre.cubeAmbient_isZero` (source) and
`Work.Serre.cubeBdry_isZero` (target), and surjectivity in the top degree follows from a section of
the projection over the contractible cube (`Work.Serre.exists_section_cubePullback`), since both
groups are then `ℚ`. -/
theorem csrPerCell (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (N : ℕ)
    (hacyc : ∀ z : Work.RatHurewicz.attachCells n Y ι f,
      (∀ k : ℕ, 0 < k → k ≤ N → CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q z))).homology k)) ∧
      Nonempty ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q z))).homology 0 ≅ ModuleCat.of ℚ ℚ))
    (i : ι) (m : ℕ) (hm : m ≤ N) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (X := ↥(q ⁻¹' (csrOpenBall n Y ι f i)))
        (Y := ↥(csrOpenBall n Y ι f i))
        {x : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) |
          (x : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})}
        {x : ↥(csrOpenBall n Y ι f i) |
          (x : Work.RatHurewicz.attachCells n Y ι f) ∈
            csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}}
        (csrRestrict q (csrOpenBall n Y ι f i))
        (by intro x hx; exact hx)) m) := by
  classical
  have hne : Nonempty (Work.StemsB.fibre q (csrCentre n Y ι f i)) :=
    Work.Serre.Csr.nonempty_of_nonempty_homologyZeroIso
      (TopCat.of (Work.StemsB.fibre q (csrCentre n Y ι f i)))
      (hacyc (csrCentre n Y ι f i)).2
  obtain ⟨s, hs⟩ := Work.Serre.Csr.csrOpenBallSection' n Y ι f q hq i hne
  have hsBA : Set.MapsTo s {x : ↥(csrOpenBall n Y ι f i) | (x : Work.RatHurewicz.attachCells n Y ι f) ∈ csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}} {x : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) | (x : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})} := by
    intro y hy
    show q (s y).1 ∈ csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}
    have h2 : q (s y).1 = (y : Work.RatHurewicz.attachCells n Y ι f) := by
      have h := congrFun (congrArg DFunLike.coe hs) y
      exact congrArg (fun z : ↥(csrOpenBall n Y ι f i) =>
        (z : Work.RatHurewicz.attachCells n Y ι f)) h
    rw [h2]
    exact hy
  have hcomp := Work.Serre.csrPairFunctoriality s
    (csrRestrict q (csrOpenBall n Y ι f i)) hsBA
    (show Set.MapsTo (csrRestrict q (csrOpenBall n Y ι f i)) {x : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) | (x : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})} {x : ↥(csrOpenBall n Y ι f i) | (x : Work.RatHurewicz.attachCells n Y ι f) ∈ csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}} from fun x hx => hx)
  rw [Work.Serre.Csr.relChainsRPairMap_congr' hs _ (fun x hx => hx),
    Work.Serre.relChainsRPairMap_id] at hcomp
  have hsurj : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap {x : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) | (x : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})} {x : ↥(csrOpenBall n Y ι f i) | (x : Work.RatHurewicz.attachCells n Y ι f) ∈ csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}} (csrRestrict q (csrOpenBall n Y ι f i)) (by intro x hx; exact hx)) m)) := by
    intro y
    refine ⟨(ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap {x : ↥(csrOpenBall n Y ι f i) | (x : Work.RatHurewicz.attachCells n Y ι f) ∈ csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}} {x : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) | (x : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})} s hsBA) m)) y, ?_⟩
    have h2 : HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap {x : ↥(csrOpenBall n Y ι f i) | (x : Work.RatHurewicz.attachCells n Y ι f) ∈ csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}} {x : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) | (x : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})} s hsBA) m ≫ HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap {x : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) | (x : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})} {x : ↥(csrOpenBall n Y ι f i) | (x : Work.RatHurewicz.attachCells n Y ι f) ∈ csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}} (csrRestrict q (csrOpenBall n Y ι f i)) (by intro x hx; exact hx)) m = 𝟙 _ := by
      rw [← HomologicalComplex.homologyMap_comp, hcomp, HomologicalComplex.homologyMap_id]
    have h3 := congrArg (fun φ => ModuleCat.Hom.hom φ y) h2
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply] using h3
  haveI : Epi (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap {x : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) | (x : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})} {x : ↥(csrOpenBall n Y ι f i) | (x : Work.RatHurewicz.attachCells n Y ι f) ∈ csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}} (csrRestrict q (csrOpenBall n Y ι f i)) (by intro x hx; exact hx)) m) :=
    (ModuleCat.epi_iff_surjective _).mpr hsurj
  rcases lt_trichotomy m (n+2) with hlt | heq | hgt
  · exact Work.StemsB.isIso_of_isZero_of_isZero
      (Work.Serre.Csr.csrSourceRat_isZero n Y ι f q hq i m hlt)
      (Work.Serre.Csr.csrTargetRat_isZero n Y ι f i m (by omega))
  · cases heq
    obtain ⟨eS⟩ := Work.Serre.Csr.csrSourceRat_iso_ratUnit n Y ι f q hq i
      (hacyc (csrCentre n Y ι f i)).2
    obtain ⟨eT⟩ := Work.Serre.Csr.csrTargetRat_iso_ratUnit n Y ι f i
    exact Work.Serre.Csr.isIso_of_epi_of_ratIso eS eT _ this
  · have hpos : 0 < m - (n+2) := Nat.sub_pos_of_lt hgt
    have hle : m - (n+2) ≤ N := by omega
    obtain ⟨eQ⟩ := Work.Serre.Csr.relChainsRHomologyIsoRat
      (TopCat.of ↥(q ⁻¹' (csrOpenBall n Y ι f i))) {x : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) | (x : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})} m
    obtain ⟨eZ⟩ := Work.Serre.Csr.csrSourceIntIso n Y ι f q hq i (m - (n+2))
    obtain ⟨eF⟩ := Work.Serre.Csr.absHomologyIsoRat
      (TopCat.of (Work.StemsB.fibre q (csrCentre n Y ι f i))) (m - (n+2))
    have hZ : ((Work.Cohomology.relChains (TopCat.of ↥(q ⁻¹' (csrOpenBall n Y ι f i))) {x : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) | (x : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})}).homology m) ≅ ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre q (csrCentre n Y ι f i)))).homology (m - (n+2))) :=
      (eqToIso (congrArg (fun k => (Work.Cohomology.relChains (TopCat.of ↥(q ⁻¹' (csrOpenBall n Y ι f i))) {x : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) | (x : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})}).homology k) (Nat.sub_add_cancel (by omega : n+2 ≤ m)))).symm ≪≫ eZ
    have hFrat : IsZero ((Work.Cohomology.singularChains ℚ (TopCat.of (Work.StemsB.fibre q (csrCentre n Y ι f i)))).homology (m - (n+2))) :=
      (hacyc (csrCentre n Y ι f i)).1 (m - (n+2)) hpos hle
    exact Work.StemsB.isIso_of_isZero_of_isZero
      (IsZero.of_iso hFrat (eQ ≪≫ Work.StemsB.IntRatF.mapIso hZ ≪≫ eF.symm))
      (Work.Serre.Csr.csrTargetRat_isZero n Y ι f i m (by omega))

end Work.Serre
