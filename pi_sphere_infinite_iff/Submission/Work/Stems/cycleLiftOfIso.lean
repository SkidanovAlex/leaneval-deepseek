import Mathlib
import Submission.Work.RatHurewicz.CoherentLabelsDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Lifting a rational cycle along a rational homology isomorphism (local to area STEMS)

This file provides, in area STEMS' own namespace, the cycle-lifting statement

  * if `g : Y → Z` induces an isomorphism on `H_j(−;ℚ)`, then every rational `j`-cycle `z` of `Z`
    is the pushforward of a rational `j`-cycle `v` of `Y` **up to a boundary**: `g_# v = z + ∂b`.

The proof is the "up to boundaries" argument of `Work.StemsB.cycleLiftOfEpi` with the epimorphism
hypothesis replaced by the isomorphism hypothesis: no fibration hypothesis is needed for this
weakened conclusion, because the bounding chain of the base is *not* lifted.
-/

namespace Work.Stems

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- The composition law of `ModuleCat` morphisms, in elementwise form. -/
theorem comp_apply_aux {R : Type*} [Ring R] {M N P : ModuleCat R} (f : M ⟶ N) (g : N ⟶ P)
    (x : M) : (ModuleCat.Hom.hom (f ≫ g)) x = (ModuleCat.Hom.hom g) ((ModuleCat.Hom.hom f) x) := by
  simp

/-- The differential of a chain complex only depends on its two indices. -/
theorem d_congr_index (K : ChainComplex (ModuleCat ℚ) ℕ) {p q : ℕ} (h : p = q) {n : ℕ}
    (x : K.X n) (hx : (K.d n q).hom x = 0) : (K.d n p).hom x = 0 := by
  cases h
  exact hx

/-- The elementwise form of `HomologicalComplex.XIsoOfEq_hom_comp_d`. -/
theorem XIsoOfEq_hom_comp_d_apply (K : ChainComplex (ModuleCat ℚ) ℕ) {n : ℕ}
    (hprev : (ComplexShape.down ℕ).prev n = n + 1)
    (w : K.X ((ComplexShape.down ℕ).prev n)) :
    (K.d (n + 1) n).hom ((K.XIsoOfEq hprev).hom w)
      = (K.d ((ComplexShape.down ℕ).prev n) n).hom w := by
  have hh := congrArg (fun (g : K.X ((ComplexShape.down ℕ).prev n) ⟶ K.X n) =>
    (ConcreteCategory.hom g) w) (HomologicalComplex.XIsoOfEq_hom_comp_d K hprev n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh

/-- **A cycle of a chain complex of `ℚ`-modules whose homology class vanishes is a boundary.** -/
theorem chain_homologypi_eq_zero (K : ChainComplex (ModuleCat ℚ) ℕ) [∀ i, K.HasHomology i]
    (n : ℕ) (z : K.cycles n) (h : K.homologyπ n z = 0) :
    ∃ y : K.X (n + 1), (K.d (n + 1) n).hom y = (K.iCycles n).hom z := by
  have hprev : (ComplexShape.down ℕ).prev n = n + 1 := by
    rw [ComplexShape.prev_eq']
    rfl
  let z' : (K.sc n).cycles := z
  have hkey : ∃ w : (K.sc n).X₁, (K.sc n).f.hom w = (K.sc n).iCycles.hom z' := by
    have hzero : (K.sc n).homologyι ((K.sc n).homologyπ z') = 0 := by
      rw [show (K.sc n).homologyπ z' = 0 from h, map_zero]
    have hpop : (K.sc n).pOpcycles ((K.sc n).iCycles.hom z') = 0 := by
      have hh := congrArg (fun (g : (K.sc n).cycles ⟶ (K.sc n).opcycles) => g z')
        (ShortComplex.homology_π_ι (K.sc n))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh
      rw [← hh]
      exact hzero
    have hmem :=
      (ShortComplex.moduleCat_pOpcycles_eq_zero_iff (K.sc n) ((K.sc n).iCycles.hom z')).mp hpop
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hmem
    exact ⟨w, hw⟩
  obtain ⟨w, hw⟩ := hkey
  refine ⟨(K.XIsoOfEq hprev).hom w, ?_⟩
  rw [XIsoOfEq_hom_comp_d_apply K hprev w]
  exact hw

/-- **Lifting a rational cycle along a rational homology isomorphism, up to a boundary.** -/
theorem cycleLift_of_isIso {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    (g : C(Y, Z)) (j : ℕ)
    (hiso : CategoryTheory.IsIso (Work.Serre.ratHomologyMap g j))
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of Z)).X j)
    (hz : (Work.Cohomology.singularChains ℚ (TopCat.of Z)).d j (j - 1) z = 0) :
    ∃ (v : (Work.Cohomology.singularChains ℚ (TopCat.of Y)).X j)
      (b : (Work.Cohomology.singularChains ℚ (TopCat.of Z)).X (j + 1)),
      (Work.Cohomology.singularChains ℚ (TopCat.of Y)).d j (j - 1) v = 0 ∧
      (Work.Cohomology.chainMap ℚ (TopCat.of Y) (TopCat.of Z) (TopCat.ofHom g)).f j v
        = z + (Work.Cohomology.singularChains ℚ (TopCat.of Z)).d (j + 1) j b := by
  classical
  let KS := Work.Serre.ratChains (TopCat.of Y)
  let KZ := Work.Serre.ratChains (TopCat.of Z)
  let cm : KS ⟶ KZ := Work.Cohomology.chainMap ℚ (TopCat.of Y) (TopCat.of Z) (TopCat.ofHom g)
  have hnext : (ComplexShape.down ℕ).next j = j - 1 := by
    rcases j with _ | m
    · rw [ChainComplex.next_nat_zero]
    · rw [ChainComplex.next_nat_succ, Nat.add_sub_cancel]
  haveI hiso' : IsIso (HomologicalComplex.homologyMap cm j) := hiso
  have hsurj : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap cm j)) :=
    (ModuleCat.epi_iff_surjective _).mp (inferInstance : Epi (HomologicalComplex.homologyMap cm j))
  have hzp : (KZ.d j ((ComplexShape.down ℕ).next j)).hom z = 0 :=
    d_congr_index KZ hnext z hz
  have hkk : ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ (KZ.X j) z)
      ≫ KZ.d j ((ComplexShape.down ℕ).next j) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change (KZ.d j ((ComplexShape.down ℕ).next j)).hom
      ((LinearMap.toSpanSingleton ℚ (KZ.X j) z) 1) = 0
    rw [LinearMap.toSpanSingleton_apply, one_smul]
    exact hzp
  let zx : KZ.cycles j := (KZ.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ (KZ.X j) z))
    ((ComplexShape.down ℕ).next j) rfl hkk).hom 1
  have hzx : (KZ.iCycles j).hom zx = z := by
    have hlift := HomologicalComplex.liftCycles_i (K := KZ) (i := j) (A := ModuleCat.of ℚ ℚ)
      (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ (KZ.X j) z))
      ((ComplexShape.down ℕ).next j) rfl hkk
    have h2 := congrArg (fun (g : ModuleCat.of ℚ ℚ ⟶ KZ.X j) =>
      (ModuleCat.Hom.hom g) (1 : ℚ)) hlift
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    change (ModuleCat.Hom.hom (KZ.iCycles j))
      ((ModuleCat.Hom.hom (KZ.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ (KZ.X j) z))
        ((ComplexShape.down ℕ).next j) rfl hkk)) 1) = z
    rw [h2]
    change (LinearMap.toSpanSingleton ℚ (KZ.X j) z) 1 = z
    rw [LinearMap.toSpanSingleton_apply, one_smul]
  obtain ⟨y, hy⟩ := hsurj ((ModuleCat.Hom.hom (KZ.homologyπ j)) zx)
  have hsurj2 : Function.Surjective (ModuleCat.Hom.hom (KS.homologyπ j)) :=
    (ModuleCat.epi_iff_surjective _).mp (inferInstance : Epi (KS.homologyπ j))
  obtain ⟨wE, hwE⟩ := hsurj2 y
  have hnat : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap cm j))
        ((ModuleCat.Hom.hom (KS.homologyπ j)) wE)
      = (ModuleCat.Hom.hom (KZ.homologyπ j)) ((HomologicalComplex.cyclesMap cm j) wE) := by
    have hl := HomologicalComplex.homologyπ_naturality (φ := cm) (i := j)
    have happ := congrArg (fun (g : KS.cycles j ⟶ KZ.homology j) => (ModuleCat.Hom.hom g) wE) hl
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using happ
  have hzero : (ModuleCat.Hom.hom (KZ.homologyπ j))
      (((HomologicalComplex.cyclesMap cm j) wE) - zx) = 0 := by
    rw [map_sub, ← hnat, hwE, hy, sub_self]
  obtain ⟨e, he⟩ := chain_homologypi_eq_zero KZ j
    (((HomologicalComplex.cyclesMap cm j) wE) - zx) hzero
  have hcyc : (KS.d j (j - 1)).hom ((ModuleCat.Hom.hom (KS.iCycles j)) wE) = 0 := by
    have hg := HomologicalComplex.iCycles_d KS j ((ComplexShape.down ℕ).next j)
    have happ := congrArg (fun (g : KS.cycles j ⟶ KS.X ((ComplexShape.down ℕ).next j)) =>
      (ModuleCat.Hom.hom g) wE) hg
    rw [comp_apply_aux] at happ
    exact d_congr_index KS hnext.symm _ happ
  have hproj : (ModuleCat.Hom.hom (KZ.iCycles j)) ((HomologicalComplex.cyclesMap cm j) wE)
      = (ModuleCat.Hom.hom (cm.f j)) ((ModuleCat.Hom.hom (KS.iCycles j)) wE) := by
    have hcy := HomologicalComplex.cyclesMap_i cm j
    have happ := congrArg (fun (g : KS.cycles j ⟶ KZ.X j) => (ModuleCat.Hom.hom g) wE) hcy
    rw [comp_apply_aux] at happ
    rw [comp_apply_aux] at happ
    exact happ
  have hbound : (ModuleCat.Hom.hom (KZ.d (j + 1) j)) e
      = (ModuleCat.Hom.hom (cm.f j)) ((ModuleCat.Hom.hom (KS.iCycles j)) wE) - z := by
    rw [he, map_sub, hproj, hzx]
  refine ⟨(ModuleCat.Hom.hom (KS.iCycles j)) wE, e, hcyc, ?_⟩
  show (ModuleCat.Hom.hom (cm.f j)) ((ModuleCat.Hom.hom (KS.iCycles j)) wE)
    = z + (ModuleCat.Hom.hom (KZ.d (j + 1) j)) e
  rw [hbound]
  abel

/-! ## Bookkeeping lemmas about `chainMap`, shared by the two consumers of this module

These are copies of `Work.StemsB.chainMap_comp_eq` and `Work.StemsB.chainMap_d_apply`
(`Submission/Work/StemsB/cycleFiniteModel.lean`) and of
`Work.StemsB.exists_boundary_of_isZero_homology`
(`Submission/Work/StemsB/rangeModelRatAcyclic_of_fgCase.lean`), reproduced here because those two
modules do not build at present.  They are provided *upstream* so that the modules which use them
do not have to declare them twice. -/

/-- `chainMap` is functorial. -/
theorem chainMap_comp_eq {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) :
    Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Z) (TopCat.ofHom (g.comp f))
      = Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)
        ≫ Work.Cohomology.chainMap ℚ (TopCat.of Y) (TopCat.of Z) (TopCat.ofHom g) := by
  simp only [Work.Cohomology.chainMap]
  rw [show TopCat.ofHom (g.comp f) = TopCat.ofHom f ≫ TopCat.ofHom g from rfl]
  exact CategoryTheory.Functor.map_comp _ _ _

/-- `chainMap` commutes with the differential. -/
theorem chainMap_d_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (i j : ℕ) (x : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X i) :
    (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)).f j
      ((Work.Cohomology.singularChains ℚ (TopCat.of X)).d i j x)
    = (Work.Cohomology.singularChains ℚ (TopCat.of Y)).d i j
      ((Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)).f i x) := by
  have h := congrArg (fun (m : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X i ⟶
      (Work.Cohomology.singularChains ℚ (TopCat.of Y)).X j) => ModuleCat.Hom.hom m x)
    (HomologicalComplex.Hom.comm (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y)
      (TopCat.ofHom f)) i j)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

/-- A cycle in degree `j` is a boundary as soon as `H_j` vanishes. -/
theorem exists_boundary_of_isZero_homology (K : ChainComplex (ModuleCat ℚ) ℕ) (j : ℕ)
    (hprev : (ComplexShape.down ℕ).prev j = j + 1)
    (hnext : (ComplexShape.down ℕ).next j = j - 1)
    (h : IsZero (K.homology j)) (x : K.X j) (hx : K.d j (j - 1) x = 0) :
    ∃ u : K.X (j + 1), K.d (j + 1) j u = x := by
  haveI : K.HasHomology j := inferInstance
  have hex : K.ExactAt j := (HomologicalComplex.exactAt_iff_isZero_homology K j).mpr h
  have hex' : (K.sc' (j + 1) j (j - 1)).Exact :=
    (HomologicalComplex.exactAt_iff' K (j + 1) j (j - 1) hprev hnext).mp hex
  have hrange := (ShortComplex.moduleCat_exact_iff_range_eq_ker (K.sc' (j + 1) j (j - 1))).mp hex'
  have hxker : x ∈ LinearMap.ker (ModuleCat.Hom.hom (K.sc' (j + 1) j (j - 1)).g) := by
    show ModuleCat.Hom.hom (K.sc' (j + 1) j (j - 1)).g x = 0
    show K.d j (j - 1) x = 0
    exact hx
  rw [← hrange] at hxker
  obtain ⟨u, hu⟩ := hxker
  refine ⟨u, ?_⟩
  show ModuleCat.Hom.hom (K.sc' (j + 1) j (j - 1)).f u = x
  exact hu

/-- **The "compactness" input of the reduction of `RangeModelRatAcyclic` to its finitely generated
case.**  A rational `j`-cycle (`k < j ≤ 2k-1`) of a range model of `K(A,k)` is, up to a boundary,
the pushforward of a rational cycle of a *finite model*: a space which is `(k-1)`-connected with
finitely generated `π_k`.

This is the Prop `Work.StemsB.CycleFiniteModel`, restated in area STEMS' namespace so that the
reduction `RangeModelRatAcyclic ⟸ f.g. case` can be carried out here without importing
`Submission.Work.StemsB.rangeModelRatAcyclic_of_fgCase` (whose import closure contains the module
`Submission.Work.StemsB.cycleFiniteModel`, which does not build at present because the interface of
`Work.StemsB.cycleLift` was changed). -/
def CycleFiniteModelLocal : Prop :=
  ∀ (k j : ℕ) (hk : 2 ≤ k) (hj₁ : k < j) (hj₂ : j ≤ 2 * k - 1)
    (Z : Type) [TopologicalSpace Z] (z₀ : Z)
    (hZ : ∀ i : ℕ, i ≤ 2 * k - 1 → i ≠ k → Subsingleton (HomotopyGroup (Fin i) Z z₀))
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of Z)).X j)
    (hz : (Work.Cohomology.singularChains ℚ (TopCat.of Z)).d j (j - 1) z = 0),
    ∃ (W : Type) (_ : TopologicalSpace W) (w₀ : W) (φ : C(W, Z))
      (w : (Work.Cohomology.singularChains ℚ (TopCat.of W)).X j)
      (b : (Work.Cohomology.singularChains ℚ (TopCat.of Z)).X (j + 1)),
      (Work.Cohomology.singularChains ℚ (TopCat.of W)).d j (j - 1) w = 0 ∧
      (Work.Cohomology.chainMap ℚ (TopCat.of W) (TopCat.of Z) (TopCat.ofHom φ)).f j w
        = z + (Work.Cohomology.singularChains ℚ (TopCat.of Z)).d (j + 1) j b ∧
      (∀ i : ℕ, i < k → Subsingleton (HomotopyGroup (Fin i) W w₀)) ∧
      (letI : k.AtLeastTwo := ⟨hk⟩
       Module.Finite ℤ (Additive (HomotopyGroup (Fin k) W w₀)))

end

end Work.Stems
