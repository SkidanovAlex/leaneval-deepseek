import Mathlib
import Submission.Work.PTGeometric.HOFChart

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.ThomBordism

noncomputable section

open Work.PTGeometric.HOF

/-- The `punctIso` linear equivalence agrees, as a linear map, with the excision `excM`. -/
theorem punctIso_toLinearMap_eq_excM (X : TopCat) (n : ℕ) (U : Set X) (hU : IsOpen U) (x : X)
    (hx : x ∈ U) (hxc : IsClosed ({x} : Set X)) :
    (punctIso X n U hU x hx hxc).toLinearMap = excM X n U ({x} : Set X) :=
  LinearMap.ext (fun z => by
    rw [show ((punctIso X n U hU x hx hxc).toLinearMap) z
        = (punctIso X n U hU x hx hxc) z from rfl]
    exact punctIso_apply X n U hU x hx hxc z)

/-- The Euclidean local generator is invariant under the cast of the base point. -/
theorem eucFam_cast {N : ℕ} (hN : 1 ≤ N) {y y' : Euc N} (h : y = y') :
    (h ▸ eucFam N hN y : Work.Orient.LocH (TopCat.of (Euc N)) N y') = eucFam N hN y' := by
  cases h
  rfl

/-- `RelHmapOf` towards a point commutes with the cast of that point. -/
theorem RelHmapOf_singleton_cast {Y : TopCat} {n : ℕ} {N : ℕ} {y y' : Euc N}
    (φ : Y ⟶ TopCat.of (Euc N)) (K : Set Y) (h : y = y')
    (h₁ : ∀ x, x ∉ K → φ x ∉ ({y} : Set (Euc N)))
    (h₂ : ∀ x, x ∉ K → φ x ∉ ({y'} : Set (Euc N)))
    (x : Work.Orient.RelH Y n K) :
    (h ▸ (RelHmapOf n φ K ({y} : Set (Euc N)) h₁ x)
      : Work.Orient.RelH (TopCat.of (Euc N)) n ({y'} : Set (Euc N)))
      = RelHmapOf n φ K ({y'} : Set (Euc N)) h₂ x := by
  cases h
  exact LinearMap.congr_fun (RelHmapOf_congr rfl h₁ h₂) x

/-- Casting along an equality of points is injective. -/
theorem eqRec_inj {α : Sort*} {β : α → Sort*} {a b : α} (h : a = b) {x y : β a}
    (H : (h ▸ x : β b) = h ▸ y) : x = y := by
  cases h
  exact H

theorem chartTr_relHmapOf {N : ℕ} {W W' : TopCat} [T1Space W] [T1Space W'] (hN : 1 ≤ N)
    (e : OpenPartialHomeomorph W (Work.PTGeometric.HOF.Euc N))
    (f : OpenPartialHomeomorph W' (Work.PTGeometric.HOF.Euc N))
    (Φ : C(W, W')) (w : W) (hw : w ∈ e.source)
    (hΦs : ∀ y, y ∈ e.source → Φ y ∈ f.source)
    (hΦ : ∀ y, y ∈ e.source → f (Φ y) = e y)
    (hinj : ∀ z : W, z ≠ w → Φ z ≠ Φ w) :
    Work.PTGeometric.HOF.RelHmapOf N (TopCat.ofHom Φ) ({w} : Set W) ({Φ w} : Set W')
        (fun z hz h => hz (by_contra (fun hzw => hinj z hzw h)))
        (Work.PTGeometric.HOF.chartTr e w hw (Work.PTGeometric.HOF.eucFam N hN (e w)))
      = Work.PTGeometric.HOF.chartTr f (Φ w) (hΦs w hw)
          (Work.PTGeometric.HOF.eucFam N hN (f (Φ w))) := by
  classical
  set hpair0 : ∀ z : W, z ∉ ({w} : Set W) → Φ z ∉ ({Φ w} : Set W') :=
    (fun z hz h => hz (by_contra (fun hzw => hinj z hzw h))) with hpair0def
  have hfy : f (Φ w) = e w := hΦ w hw
  set ve : Work.Orient.LocH (TopCat.of (Euc N)) N (e w) := eucFam N hN (e w) with hve
  set x0 : Work.Orient.LocH W N w := chartTr e w hw ve with hx0
  set q : Work.Orient.RelH (TopCat.of ↥e.source) N (punctSet W e.source w) :=
    ((punctIso W N e.source e.open_source w hw isClosed_singleton).symm.toLinearMap) x0 with hqdef
  have hq' : x0 = RelHmapOf N (Work.Cohomology.subtypeIncl W e.source) (punctSet W e.source w)
      ({w} : Set W) (fun z hz => hz) q :=
    (punctIso_excM_symm' W N e.source e.open_source w hw isClosed_singleton x0).symm
  -- the corestriction of `Φ` to `e.source → f.source`
  let Φs : TopCat.of ↥e.source ⟶ TopCat.of ↥f.source :=
    TopCat.ofHom ⟨fun y => ⟨Φ y, hΦs y y.2⟩,
      Continuous.subtype_mk (Φ.continuous.comp continuous_subtype_val) (fun y => hΦs y y.2)⟩
  have hΦs_coe (y : ↥e.source) : ((Φs y : ↥f.source) : W') = Φ y := rfl
  -- the two factorisations of the intertwining maps
  have hfac : Work.Cohomology.subtypeIncl W e.source ≫ TopCat.ofHom Φ
      = Φs ≫ Work.Cohomology.subtypeIncl W' f.source := by
    apply TopCat.ext
    intro y
    rfl
  have hfac2 : Φs ≫ eCore f ≫ Work.Cohomology.subtypeIncl (TopCat.of (Euc N)) f.target
      = eCore e ≫ Work.Cohomology.subtypeIncl (TopCat.of (Euc N)) e.target := by
    apply TopCat.ext
    intro y
    exact hΦ y y.2
  -- the pair conditions
  have hE_pair : ∀ z : ↥e.source, z ∉ punctSet W e.source w →
      (eCore e ≫ Work.Cohomology.subtypeIncl (TopCat.of (Euc N)) e.target) z ∉
        ({e w} : Set (Euc N)) := by
    intro z hz h
    refine hz ?_
    change (z : W) = w
    have h1 : e (z : W) = e w := (eCore_apply_coe e z).symm.trans h
    exact ((e.left_inv z.2).symm.trans (congrArg e.symm h1)).trans (e.left_inv hw)
  have hF_pair' : ∀ z : ↥e.source, z ∉ punctSet W e.source w →
      (eCore e ≫ Work.Cohomology.subtypeIncl (TopCat.of (Euc N)) e.target) z ∉
        ({f (Φ w)} : Set (Euc N)) := by
    intro z hz h
    refine hz ?_
    change (z : W) = w
    have h1 : e (z : W) = e w := ((eCore_apply_coe e z).symm.trans h).trans hfy
    exact ((e.left_inv z.2).symm.trans (congrArg e.symm h1)).trans (e.left_inv hw)
  have hA_pair2 : ∀ z : ↥e.source, z ∉ punctSet W e.source w →
      Φs z ∉ punctSet W' f.source (Φ w) := by
    intro z hz h
    refine hz ?_
    change (z : W) = w
    by_contra hne
    exact hinj (z : W) hne ((hΦs_coe z).symm.trans h)
  have hA_pair0 : ∀ z : ↥e.source, z ∉ punctSet W e.source w →
      (Work.Cohomology.subtypeIncl W e.source ≫ TopCat.ofHom Φ) z ∉ ({Φ w} : Set W') := by
    intro z hz h
    refine hz ?_
    change (z : W) = w
    by_contra hne
    exact hinj (z : W) hne h
  have hA_pair1 : ∀ z : ↥e.source, z ∉ punctSet W e.source w →
      (Φs ≫ Work.Cohomology.subtypeIncl W' f.source) z ∉ ({Φ w} : Set W') := by
    intro z hz h
    refine hz ?_
    change (z : W) = w
    by_contra hne
    exact hinj (z : W) hne h
  have hA_pair : ∀ x : ↥f.source, x ∉ punctSet W' f.source (Φ w) →
      (Work.Cohomology.subtypeIncl W' f.source) x ∉ ({Φ w} : Set W') := fun x hx => hx
  have hF_pair1 : ∀ z : ↥f.source, z ∉ punctSet W' f.source (Φ w) →
      (eCore f ≫ Work.Cohomology.subtypeIncl (TopCat.of (Euc N)) f.target) z ∉
        ({f (Φ w)} : Set (Euc N)) :=
    fun z hz => eCore_pair f (Φ w) (hΦs w hw) hz
  -- the e-side normal form
  have hE : chartInvCore e w hw x0
      = RelHmapOf N (eCore e ≫ Work.Cohomology.subtypeIncl (TopCat.of (Euc N)) e.target)
          (punctSet W e.source w) ({e w} : Set (Euc N)) hE_pair q := by
    rw [chartInvCore_apply, ← hqdef]
    rw [punctIso_toLinearMap_eq_excM (TopCat.of (Euc N)) N e.target e.open_target (e w)
      (e.map_source hw) isClosed_singleton]
    rw [show excM (TopCat.of (Euc N)) N e.target ({e w} : Set (Euc N))
        = RelHmapOf N (Work.Cohomology.subtypeIncl (TopCat.of (Euc N)) e.target)
            (punctSet (TopCat.of (Euc N)) e.target (e w)) ({e w} : Set (Euc N))
            (fun z hz => hz) from rfl]
    rw [← LinearMap.comp_apply, RelHmapOf_comp (f := eCore e)
      (g := Work.Cohomology.subtypeIncl (TopCat.of (Euc N)) e.target)
      (K := punctSet W e.source w) (K' := punctSet (TopCat.of (Euc N)) e.target (e w))
      (K'' := ({e w} : Set (Euc N))) (fun z hz => eCore_pair e w hw hz) (fun z hz => hz) hE_pair]
  have hE2 : chartInvCore e w hw x0 = ve := by
    rw [hx0]
    exact chartInvCore_chartTr e w hw ve
  -- the transferred class in normal form
  have hA : (RelHmapOf N (TopCat.ofHom Φ) ({w} : Set W) ({Φ w} : Set W') hpair0) x0
      = RelHmapOf N (Work.Cohomology.subtypeIncl W' f.source) (punctSet W' f.source (Φ w))
          ({Φ w} : Set W') hA_pair
          (RelHmapOf N Φs (punctSet W e.source w) (punctSet W' f.source (Φ w)) hA_pair2 q) := by
    rw [hq']
    rw [← LinearMap.comp_apply, RelHmapOf_comp (f := Work.Cohomology.subtypeIncl W e.source)
      (g := TopCat.ofHom Φ) (K := punctSet W e.source w) (K' := ({w} : Set W))
      (K'' := ({Φ w} : Set W')) (fun z hz => hz) hpair0 hA_pair0]
    rw [RelHmapOf_congr hfac hA_pair0 hA_pair1]
    rw [← RelHmapOf_comp (f := Φs) (g := Work.Cohomology.subtypeIncl W' f.source)
      (K := punctSet W e.source w) (K' := punctSet W' f.source (Φ w)) (K'' := ({Φ w} : Set W'))
      hA_pair2 hA_pair hA_pair1]
    rw [LinearMap.comp_apply]
  -- its image under the inverse of the `f`-chart transfer
  set Z : Work.Orient.RelH (TopCat.of ↥f.source) N (punctSet W' f.source (Φ w)) :=
    ((punctIso W' N f.source f.open_source (Φ w) (hΦs w hw) isClosed_singleton).symm.toLinearMap)
      ((RelHmapOf N (TopCat.ofHom Φ) ({w} : Set W) ({Φ w} : Set W') hpair0) x0) with hZdef
  have hZ : Z = RelHmapOf N Φs (punctSet W e.source w) (punctSet W' f.source (Φ w)) hA_pair2 q := by
    refine excM_injective W' N f.source f.open_source ({Φ w} : Set W')
      (Set.singleton_subset_iff.mpr (hΦs w hw)) isClosed_singleton ?_
    rw [show excM W' N f.source ({Φ w} : Set W') Z
        = (RelHmapOf N (TopCat.ofHom Φ) ({w} : Set W) ({Φ w} : Set W') hpair0) x0 from
      punctIso_excM_symm' W' N f.source f.open_source (Φ w) (hΦs w hw) isClosed_singleton _]
    rw [hA]
    rw [show excM W' N f.source ({Φ w} : Set W')
        = RelHmapOf N (Work.Cohomology.subtypeIncl W' f.source) (punctSet W' f.source (Φ w))
            ({Φ w} : Set W') (fun z hz => hz) from rfl]
  -- the `f`-side normal form
  have hF : chartInvCore f (Φ w) (hΦs w hw)
        ((RelHmapOf N (TopCat.ofHom Φ) ({w} : Set W) ({Φ w} : Set W') hpair0) x0)
      = RelHmapOf N (eCore e ≫ Work.Cohomology.subtypeIncl (TopCat.of (Euc N)) e.target)
          (punctSet W e.source w) ({f (Φ w)} : Set (Euc N)) hF_pair' q := by
    have hF_pair : ∀ z : ↥e.source, z ∉ punctSet W e.source w →
        (Φs ≫ eCore f ≫ Work.Cohomology.subtypeIncl (TopCat.of (Euc N)) f.target) z ∉
          ({f (Φ w)} : Set (Euc N)) := by
      intro z hz h
      refine hz ?_
      change (z : W) = w
      have h1 : f ((Φs z : ↥f.source) : W') = f (Φ w) := (eCore_apply_coe f (Φs z)).symm.trans h
      have h2 : ((Φs z : ↥f.source) : W') = Φ w := f.injOn (Φs z).2 (hΦs w hw) h1
      have h3 : Φ (z : W) = Φ w := (hΦs_coe z).symm.trans h2
      by_contra hne
      exact hinj (z : W) hne h3
    rw [chartInvCore_apply, ← hZdef]
    rw [hZ]
    rw [punctIso_toLinearMap_eq_excM (TopCat.of (Euc N)) N f.target f.open_target (f (Φ w))
      (f.map_source (hΦs w hw)) isClosed_singleton]
    rw [show excM (TopCat.of (Euc N)) N f.target ({f (Φ w)} : Set (Euc N))
        = RelHmapOf N (Work.Cohomology.subtypeIncl (TopCat.of (Euc N)) f.target)
            (punctSet (TopCat.of (Euc N)) f.target (f (Φ w))) ({f (Φ w)} : Set (Euc N))
            (fun z hz => hz) from rfl]
    rw [← LinearMap.comp_apply, RelHmapOf_comp (f := eCore f)
      (g := Work.Cohomology.subtypeIncl (TopCat.of (Euc N)) f.target)
      (K := punctSet W' f.source (Φ w)) (K' := punctSet (TopCat.of (Euc N)) f.target (f (Φ w)))
      (K'' := ({f (Φ w)} : Set (Euc N)))
      (fun z hz => eCore_pair f (Φ w) (hΦs w hw) hz) (fun z hz => hz) hF_pair1]
    rw [← LinearMap.comp_apply, RelHmapOf_comp (f := Φs)
      (g := eCore f ≫ Work.Cohomology.subtypeIncl (TopCat.of (Euc N)) f.target)
      (K := punctSet W e.source w) (K' := punctSet W' f.source (Φ w))
      (K'' := ({f (Φ w)} : Set (Euc N))) hA_pair2 hF_pair1 hF_pair]
    rw [RelHmapOf_congr hfac2 hF_pair hF_pair']
  -- the cast comparison
  have hcast : (hfy ▸ (chartInvCore f (Φ w) (hΦs w hw)
        ((RelHmapOf N (TopCat.ofHom Φ) ({w} : Set W) ({Φ w} : Set W') hpair0) x0))
      : Work.Orient.LocH (TopCat.of (Euc N)) N (e w)) = ve := by
    rw [hF]
    rw [RelHmapOf_singleton_cast (Y := TopCat.of ↥e.source) (n := N)
      (φ := eCore e ≫ Work.Cohomology.subtypeIncl (TopCat.of (Euc N)) e.target)
      (K := punctSet W e.source w) (y := f (Φ w)) (y' := e w) hfy hF_pair' hE_pair q]
    rw [← hE, hE2]
  have hve2 : (hfy ▸ (eucFam N hN (f (Φ w))) : Work.Orient.LocH (TopCat.of (Euc N)) N (e w))
      = ve := by
    rw [eucFam_cast hN hfy]
  have hsuff : chartInvCore f (Φ w) (hΦs w hw)
      ((RelHmapOf N (TopCat.ofHom Φ) ({w} : Set W) ({Φ w} : Set W') hpair0) x0)
      = eucFam N hN (f (Φ w)) :=
    eqRec_inj (β := fun t => Work.Orient.LocH (TopCat.of (Euc N)) N t) hfy (hcast.trans hve2.symm)
  exact (chartTr_chartInvCore f (Φ w) (hΦs w hw) _).symm.trans (congrArg _ hsuff)

end

end Work.ThomBordism
