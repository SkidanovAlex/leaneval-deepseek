import Mathlib
import Submission.Work.Serre.cylCMidDefs
import Submission.Work.Serre.csrPairFunctoriality
import Submission.Work.Serre.isIso_collapseMap
import Submission.Work.Serre.DiscPair.relPairFiveRat
import Submission.Work.Serre.coneFibreComparison
import Submission.Work.StemsB.relChainsRIsoOfHomeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The vanishing of `H_{r+1}(cyl q, CMid q b; ℚ)` from the pair comparison

Setting: `q : C(X,B)` a map, `b : B`, `M = cyl q` the mapping cylinder, `A = range (cylIncl q)`
the bottom copy of `X`, `P = (cylRetract q)⁻¹{b}` the fibre of the retraction over `b` (the cone on
the fibre `q⁻¹b`) and `Cm = CMid q b = A ∪ P`.

The target of this file:

`Epi (H_{r+1}(φ)) → IsIso (H_r(φ)) → IsZero (H_{r+1}(M, Cm; ℚ))`,  where
`φ = relPairMapRat q b : C_*(X, q⁻¹b) → C_*(B, {b})` is the map of pairs on relative rational
chains.

The proof is the cofibre (mapping-cone) computation for the map of pairs: `(M, Cm)` is the
homotopy cofibre of `(X, q⁻¹b) → (B, {b})`, so its relative homology fits the long exact sequence

`H_n(X,q⁻¹b) --φ_n--> H_n(B,{b}) --> H_n(M,Cm) --> H_{n-1}(X,q⁻¹b) --φ_{n-1}--> H_{n-1}(B,{b})`,

and over `ℚ` this splits as `H_n(M,Cm) ≅ coker(φ_n) ⊕ ker(φ_{n-1})`.  The two inputs are

* `collapseMap` — `H_k(C_*(Cm,P)) ≅ H_k(C_*(X,q⁻¹b))` (the cone attachment computes the relative
  homology), and
* `retractMap` — `H_k(C_*(M,P)) ≅ H_k(C_*(B,{b}))` (the retraction is a homotopy equivalence of
  pairs).
-/

set_option backward.isDefEq.respectTransparency false

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]

/-! ## The algebraic input: the third term of a short exact sequence

If `0 → X₁ → X₂ → X₃ → 0` is a short exact sequence of chain complexes of `ℚ`-modules and the map
`H_n(X₁) → H_n(X₂)` is onto while `H_{n-1}(X₁) → H_{n-1}(X₂)` is an isomorphism, then
`H_n(X₃) = 0`: the long exact sequence reads

`H_n(X₁) --α--> H_n(X₂) --β--> H_n(X₃) --δ--> H_{n-1}(X₁) --γ--> H_{n-1}(X₂)`,

`α` onto forces `β = 0`, hence `δ` injective; `γ` injective forces `δ = 0`; so `H_n(X₃) = 0`. -/
theorem isZero_homology_third_of_epi_isIso {S : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ)}
    (hS : S.ShortExact) (n : ℕ) (hn : 1 ≤ n)
    (hepi : CategoryTheory.Epi (HomologicalComplex.homologyMap S.f n))
    (hiso : CategoryTheory.IsIso (HomologicalComplex.homologyMap S.f (n - 1))) :
    IsZero (S.X₃.homology n) := by
  have hrel : (ComplexShape.down ℕ).Rel n (n - 1) := by
    simp [ComplexShape.down]; omega
  have h2 := (hS.homology_exact₂ n).moduleCat_range_eq_ker
  have h3 := (hS.homology_exact₃ n (n - 1) hrel).moduleCat_range_eq_ker
  have h1 := (hS.homology_exact₁ n (n - 1) hrel).moduleCat_range_eq_ker
  have hβker : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g n)).ker = ⊤ := by
    rw [← h2]
    exact LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective _).mp hepi)
  have hβhom : ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g n) = 0 :=
    LinearMap.ker_eq_top.mp hβker
  have hδker : (ModuleCat.Hom.hom (hS.δ n (n - 1) hrel)).ker = ⊥ := by
    rw [← h3, hβhom]
    simp
  have hδinj : Function.Injective (ModuleCat.Hom.hom (hS.δ n (n - 1) hrel)) :=
    LinearMap.ker_eq_bot.mp hδker
  haveI : IsIso (HomologicalComplex.homologyMap S.f (n - 1)) := hiso
  have hγinj : Function.Injective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.f (n - 1))) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hδzero : ModuleCat.Hom.hom (hS.δ n (n - 1) hrel) = 0 := by
    have hker : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.f (n - 1))).ker = ⊥ :=
      LinearMap.ker_eq_bot.mpr hγinj
    have hrange : (ModuleCat.Hom.hom (hS.δ n (n - 1) hrel)).range = ⊥ := by
      rw [h1, hker]
    exact LinearMap.range_eq_bot.mp hrange
  refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => ?_⟩
  have key : ∀ x : ↥(S.X₃.homology n), x = 0 := by
    intro x
    apply hδinj
    rw [hδzero]; rfl
  rw [key a, key b]

/-! ## The geometric inputs -/

/-- The retraction `C_*(cyl q, P) → C_*(B, {b})` is an isomorphism on rational homology:
`cylRetract q` is a homotopy equivalence (`cylHomotopyEquivExplicit`) and its restriction to the
fibre `P` is a homotopy equivalence because `P` is contractible
(`Work.Serre.DiscPair.cylRetractPreimageContractible`). -/
theorem isIso_retractMap (q : C(X, B)) (b : B) (k : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (retractMap q b) k) := by
  let hg : Set.MapsTo (cylRetract q) (fibreSet q b) ({b} : Set B) := fun _ hx => hx
  refine Work.Serre.DiscPair.relChainsRPairMap_homologyMap_isIso (fibreSet q b) ({b} : Set B)
    (cylRetract q) hg k ?_ ?_
  · intro n
    obtain ⟨E, hE⟩ := Work.Serre.cylHomotopyEquivExplicit q
    have h := Work.Serre.IsRatHomologyIso.of_homotopyEquiv E n
    rwa [hE] at h
  · intro n
    haveI : ContractibleSpace ↥(fibreSet q b) :=
      Work.Serre.DiscPair.cylRetractPreimageContractible q b
    let φ : C(↥(fibreSet q b), ↥({b} : Set B)) :=
      ⟨fun x => ⟨cylRetract q x.1, x.2⟩,
        Continuous.subtype_mk ((cylRetract q).continuous.comp continuous_subtype_val)
          (fun x => x.2)⟩
    let ψ : C(↥({b} : Set B), ↥(fibreSet q b)) :=
      ⟨fun _ => ⟨cylInr q b, rfl⟩, continuous_const⟩
    have hleft : (ψ.comp φ).Homotopic (ContinuousMap.id ↥(fibreSet q b)) :=
      homotopic_of_contractible _ _
    have hright : (φ.comp ψ).Homotopic (ContinuousMap.id ↥({b} : Set B)) := by
      have h : φ.comp ψ = ContinuousMap.id ↥({b} : Set B) :=
        ContinuousMap.ext (fun x => Subsingleton.elim _ _)
      rw [h]
    exact Work.Serre.IsRatHomologyIso.of_homotopyEquiv
      (ContinuousMap.HomotopyEquiv.mk φ ψ hleft hright) n

/-! ## The chain-level commuting square -/

/-- **The chain-level commuting square**: the collapse, the inclusion of the triple
`P ⊆ CMid q b ⊆ cyl q` and the retraction compose to the pair comparison map `relPairMapRat q b`. -/
theorem collapseMap_comp_retractMap (q : C(X, B)) (b : B) :
    collapseMap q b ≫ inclMap q b ≫ retractMap q b = relPairMapRat q b := by
  -- `inclMap` is the inclusion of pairs `(↥(CMid q b), P) → (cyl q, P)`
  have hIncl : inclMap q b
      = relChainsRPairMap {y : ↥(CMid q b) | (y : cyl q) ∈ fibreSet q b} (fibreSet q b)
          (⟨fun y => (y : cyl q), continuous_subtype_val⟩ : C(↥(CMid q b), cyl q))
          (by intro y hy; exact hy) := rfl
  rw [hIncl, collapseMap, retractMap]
  -- functoriality in the second leg
  rw [csrPairFunctoriality
        (⟨fun y => (y : cyl q), continuous_subtype_val⟩ : C(↥(CMid q b), cyl q))
        (cylRetract q) (by intro y hy; exact hy) (by intro x hx; exact hx)]
  -- functoriality in the first leg
  rw [csrPairFunctoriality (toCMid q b)
        ((cylRetract q).comp
          (⟨fun y => (y : cyl q), continuous_subtype_val⟩ : C(↥(CMid q b), cyl q)))
        (by intro x hx; exact hx) (by intro y hy; exact hy)]
  -- the composite of the underlying maps is `q`
  have hmap : ((cylRetract q).comp
        (⟨fun y => (y : cyl q), continuous_subtype_val⟩ : C(↥(CMid q b), cyl q))).comp
        (toCMid q b) = q := by
    ext x
    exact DFunLike.congr_fun (cylRetract_cylIncl q) x
  rw [show relChainsRPairMap (q ⁻¹' ({b} : Set B)) ({b} : Set B)
        (((cylRetract q).comp
          (⟨fun y => (y : cyl q), continuous_subtype_val⟩ : C(↥(CMid q b), cyl q))).comp
          (toCMid q b)) _
      = relChainsRPairMap (q ⁻¹' ({b} : Set B)) ({b} : Set B) q _ from
    relChainsRPairMap_congr hmap _ _]
  rfl

/-! ## The target -/

theorem isZero_homology_relChainsR_cylCMid_of_pairComparison {B : Type} [TopologicalSpace B]
    {X : Type} [TopologicalSpace X] (q : C(X, B)) (b : B) (r : ℕ)
    (hepi : CategoryTheory.Epi
      (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat q b) (r + 1)))
    (hiso : CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat q b) r)) :
    CategoryTheory.Limits.IsZero
      ((Work.StemsB.relChainsR ℚ (TopCat.of (Work.Serre.cyl q))
        (Work.Serre.CMid q b)).homology (r + 1)) := by
  classical
  have hS : (Work.Serre.RatTower.tripleShortR (TopCat.of (cyl q)) (fibreSet q b) (CMid q b)
      Set.subset_union_right).ShortExact :=
    Work.Serre.RatTower.tripleShortR_shortExact _ _ _ _
  -- the two comparison maps are homology isomorphisms
  haveI hcol : IsIso (HomologicalComplex.homologyMap (collapseMap q b) (r + 1)) :=
    isIso_collapseMap q b (r + 1)
  haveI hcol' : IsIso (HomologicalComplex.homologyMap (collapseMap q b) r) :=
    isIso_collapseMap q b r
  haveI hret : IsIso (HomologicalComplex.homologyMap (retractMap q b) (r + 1)) :=
    isIso_retractMap q b (r + 1)
  haveI hret' : IsIso (HomologicalComplex.homologyMap (retractMap q b) r) :=
    isIso_retractMap q b r
  -- the commuting square on homology
  have hsq : HomologicalComplex.homologyMap (collapseMap q b) (r + 1)
      ≫ HomologicalComplex.homologyMap (inclMap q b) (r + 1)
      ≫ HomologicalComplex.homologyMap (retractMap q b) (r + 1)
      = HomologicalComplex.homologyMap (relPairMapRat q b) (r + 1) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      collapseMap_comp_retractMap]
  have hsq' : HomologicalComplex.homologyMap (collapseMap q b) r
      ≫ HomologicalComplex.homologyMap (inclMap q b) r
      ≫ HomologicalComplex.homologyMap (retractMap q b) r
      = HomologicalComplex.homologyMap (relPairMapRat q b) r := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      collapseMap_comp_retractMap]
  -- transfer the hypotheses to `inclMap`
  have hSf_epi : CategoryTheory.Epi (HomologicalComplex.homologyMap (inclMap q b) (r + 1)) := by
    haveI hcomp : CategoryTheory.Epi (HomologicalComplex.homologyMap (collapseMap q b) (r + 1)
        ≫ HomologicalComplex.homologyMap (inclMap q b) (r + 1)
        ≫ HomologicalComplex.homologyMap (retractMap q b) (r + 1)) := by
      rw [hsq]; exact hepi
    haveI : CategoryTheory.Epi (HomologicalComplex.homologyMap (inclMap q b) (r + 1)
        ≫ HomologicalComplex.homologyMap (retractMap q b) (r + 1)) :=
      epi_of_epi (HomologicalComplex.homologyMap (collapseMap q b) (r + 1))
        (HomologicalComplex.homologyMap (inclMap q b) (r + 1)
          ≫ HomologicalComplex.homologyMap (retractMap q b) (r + 1))
    rw [show HomologicalComplex.homologyMap (inclMap q b) (r + 1)
        = (HomologicalComplex.homologyMap (inclMap q b) (r + 1)
          ≫ HomologicalComplex.homologyMap (retractMap q b) (r + 1))
          ≫ inv (HomologicalComplex.homologyMap (retractMap q b) (r + 1)) from by simp]
    exact inferInstance
  have hSf_iso : CategoryTheory.IsIso (HomologicalComplex.homologyMap (inclMap q b) r) := by
    haveI hcomp : CategoryTheory.IsIso (HomologicalComplex.homologyMap (collapseMap q b) r
        ≫ HomologicalComplex.homologyMap (inclMap q b) r
        ≫ HomologicalComplex.homologyMap (retractMap q b) r) := by
      rw [hsq']; exact hiso
    haveI hmid : CategoryTheory.IsIso (HomologicalComplex.homologyMap (inclMap q b) r
        ≫ HomologicalComplex.homologyMap (retractMap q b) r) :=
      IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap (collapseMap q b) r)
        (HomologicalComplex.homologyMap (inclMap q b) r
          ≫ HomologicalComplex.homologyMap (retractMap q b) r)
    exact IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap (inclMap q b) r)
      (HomologicalComplex.homologyMap (retractMap q b) r)
  exact isZero_homology_third_of_epi_isIso hS (r + 1) (by omega) hSf_epi hSf_iso

end

end Work.Serre
