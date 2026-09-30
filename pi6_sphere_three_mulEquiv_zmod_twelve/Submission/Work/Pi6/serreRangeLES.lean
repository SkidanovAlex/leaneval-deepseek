import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.SRANGE.Defs
import Submission.Work.Pi6.SRANGE.BaseChange
import Submission.Work.Pi6.SRANGE.RelChainsBaseChange
import Submission.Work.Pi6.SRANGE.PointHomology
import Submission.Work.Pi6.SRANGE.isIso_homologyMap_baseChangeMap
import Submission.Work.Cohomology.relChains_free
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.StemsB.serreStableExactTwo
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-! Area SRANGE: the Serre exact sequence in the stable range, with arbitrary coefficients.

The proof is the standard one, with two inputs:

* `Work.StemsB.serrePairComparisonTwo`: for a Serre fibration `p : E → B` with `B` `(b-1)`-connected
  (`b ≥ 2`) and fibre `F = p⁻¹(b₀)` homologically `(f-1)`-connected, the map of pairs
  `(E,F) → (B,b₀)` induces an isomorphism on integral relative homology in degrees `< b + f`
  (and an epimorphism at `b + f`);
* the technical coefficient-transfer chapter `Work.Pi6.SRANGE.*`: base change `ℤ → R` of the
  (free) relative chain complexes, which turns that integral statement into the corresponding
  statement with coefficients in an arbitrary commutative ring `R`.

The connecting map `bd i : H_{i+1}(B;R) → H_i(F;R)` is the composite of the identification
`H_{i+1}(B;R) ≅ H_{i+1}(B,{b₀};R)` (from the long exact sequence of the pair `(B,{b₀})`, which is
an isomorphism in positive degrees for a path connected base), the inverse of the (base-changed)
Serre comparison `H_{i+1}(E,F;R) ≅ H_{i+1}(B,{b₀};R)`, and the connecting homomorphism
`H_{i+1}(E,F;R) → H_i(F;R)` of the long exact sequence of the pair `(E,F)`.
-/

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 8000000

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6

noncomputable section

theorem serreRangeLES : Work.Pi6.SerreRangeLES := by
  intro R instR E B instE instB p e₀ b f hp hb hconn hfib0 hfibH
  obtain ⟨hcmp, -⟩ :=
    Work.StemsB.serrePairComparisonTwo p hp (p e₀) e₀ rfl b f hb hconn hfib0 hfibH
  haveI hpathB : PathConnectedSpace B :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero (p e₀) (hconn 0 (by omega))
  obtain ⟨e, he⟩ := Work.Pi6.SRANGE.BaseChange R
  obtain ⟨g, hg⟩ := Work.Pi6.SRANGE.RelChainsBaseChange R e he
  have hcompat := hg E B p (p e₀)
  have hTF : ∀ (X : TopCat) (A : Set X) (j : ℕ),
      Module.IsTorsionFree ℤ ((Work.Cohomology.relChains X A).X j) := by
    intro X A j
    haveI := Work.Cohomology.relChains_free X A j
    infer_instance
  have hiso : ∀ i : ℕ, i + 1 < b + f →
      IsIso (HomologicalComplex.homologyMap (Work.Pi6.SRANGE.relPairMapR R p (p e₀)) (i + 1)) := by
    intro i hi
    have hb1 : IsIso (HomologicalComplex.homologyMap
        (Work.Pi6.SRANGE.baseChangeMap R (Work.StemsB.relPairMap p (p e₀))) (i + 1)) :=
      Work.Pi6.SRANGE.isIso_homologyMap_baseChangeMap (R := R)
        (C := Work.Cohomology.relChains (TopCat.of E) (p ⁻¹' {p e₀}))
        (D := Work.Cohomology.relChains (TopCat.of B) ({p e₀} : Set B))
        (f := Work.StemsB.relPairMap p (p e₀)) (N := b + f)
        (fun j => hTF (TopCat.of E) (p ⁻¹' {p e₀}) j)
        (fun j => hTF (TopCat.of B) ({p e₀} : Set B) j)
        (fun j hj => hcmp j hj) (i + 1) hi
    have hsq : HomologicalComplex.homologyMap
          (CategoryTheory.CategoryStruct.comp (Work.Pi6.SRANGE.baseChangeMap R (Work.StemsB.relPairMap p (p e₀))) (g (TopCat.of B) ({p e₀} : Set B)).hom) (i+1)
        = HomologicalComplex.homologyMap
          (CategoryTheory.CategoryStruct.comp (g (TopCat.of E) (p ⁻¹' {p e₀})).hom (Work.Pi6.SRANGE.relPairMapR R p (p e₀))) (i+1) :=
      congrArg (fun (m : Work.Pi6.SRANGE.baseChange R (Work.Cohomology.relChains (TopCat.of E) (p ⁻¹' {p e₀}))
            ⟶ Work.StemsB.relChainsR R (TopCat.of B) ({p e₀} : Set B)) =>
          HomologicalComplex.homologyMap m (i+1)) hcompat
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq
    haveI hA : IsIso (HomologicalComplex.homologyMap
        (Work.Pi6.SRANGE.baseChangeMap R (Work.StemsB.relPairMap p (p e₀))) (i + 1)) := hb1
    haveI hC : IsIso (HomologicalComplex.homologyMap (g (TopCat.of B) ({p e₀} : Set B)).hom (i + 1)) :=
      (HomologicalComplex.homologyMapIso (g (TopCat.of B) ({p e₀} : Set B)) (i+1)).isIso_hom
    haveI hB : IsIso (HomologicalComplex.homologyMap (g (TopCat.of E) (p ⁻¹' {p e₀})).hom (i + 1)) :=
      (HomologicalComplex.homologyMapIso (g (TopCat.of E) (p ⁻¹' {p e₀})) (i+1)).isIso_hom
    have hcomp : IsIso (CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap (Work.Pi6.SRANGE.baseChangeMap R (Work.StemsB.relPairMap p (p e₀))) (i + 1))
        (HomologicalComplex.homologyMap (g (TopCat.of B) ({p e₀} : Set B)).hom (i + 1))) := inferInstance
    rw [hsq] at hcomp
    exact IsIso.of_isIso_comp_left
      (HomologicalComplex.homologyMap (g (TopCat.of E) (p ⁻¹' {p e₀})).hom (i + 1))
      (HomologicalComplex.homologyMap (Work.Pi6.SRANGE.relPairMapR R p (p e₀)) (i + 1))
  have hcan : ∀ n : ℕ, 1 ≤ n → IsIso (HomologicalComplex.homologyMap
      (cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of B) ({p e₀} : Set B))) n) :=
    fun n hn => Work.Pi6.SRANGE.PointHomology R (p e₀) n hn
  refine ⟨fun i => if h : i + 1 < b + f then
      (by
        haveI := hiso i h
        exact CategoryTheory.CategoryStruct.comp
          (HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of B) ({p e₀} : Set B))) (i+1))
          (CategoryTheory.CategoryStruct.comp
            (CategoryTheory.inv (HomologicalComplex.homologyMap (Work.Pi6.SRANGE.relPairMapR R p (p e₀)) (i+1)))
            (Work.StemsB.relChainsRδ R (TopCat.of E) (p ⁻¹' {p e₀}) i)))
      else 0, ?_⟩
  intro i hi
  simp only [dite_eq_left hi]
  have hles2 : Function.Exact
      (hmap R (Work.StemsB.fibreIncl p (p e₀)) (i+1)).hom
      (HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of E) (p ⁻¹' {p e₀}))) (i+1)).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (Work.StemsB.relChainsR_exact₂ R (TopCat.of E) (p ⁻¹' {p e₀}) (i+1))
  have hles3 : Function.Exact
      (HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of E) (p ⁻¹' {p e₀}))) (i+1)).hom
      (Work.StemsB.relChainsRδ R (TopCat.of E) (p ⁻¹' {p e₀}) i).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (Work.StemsB.relChainsR_exact₃ R (TopCat.of E) (p ⁻¹' {p e₀}) i)
  have hles1 : Function.Exact
      (Work.StemsB.relChainsRδ R (TopCat.of E) (p ⁻¹' {p e₀}) i).hom
      (hmap R (Work.StemsB.fibreIncl p (p e₀)) i).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (Work.StemsB.relChainsR_exact₁ R (TopCat.of E) (p ⁻¹' {p e₀}) i)
  have hnat : ∀ y, (HomologicalComplex.homologyMap (Work.Pi6.SRANGE.relPairMapR R p (p e₀)) (i+1)).hom
        ((HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of E) (p ⁻¹' {p e₀}))) (i+1)).hom y)
      = (HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of B) ({p e₀} : Set B))) (i+1)).hom
        ((hmap R p (i+1)).hom y) := by
    intro y
    have hsq := congrArg (fun m => HomologicalComplex.homologyMap m (i+1))
      (Work.Pi6.SRANGE.cokernel_π_relPairMapR R p (p e₀))
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq
    have h2 := congrArg (fun (m : Work.Pi6.HR R E (i+1)
        ⟶ (Work.StemsB.relChainsR R (TopCat.of B) ({p e₀} : Set B)).homology (i+1)) => m.hom y) hsq
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, Work.Pi6.hmap] using h2
  haveI hcanI : IsIso (HomologicalComplex.homologyMap
      (cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of B) ({p e₀} : Set B))) (i+1)) := hcan (i+1) (by omega)
  have hcaninj : Function.Injective (HomologicalComplex.homologyMap
      (cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of B) ({p e₀} : Set B))) (i+1)).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hcansurj : Function.Surjective (HomologicalComplex.homologyMap
      (cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of B) ({p e₀} : Set B))) (i+1)).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  haveI hginvI : IsIso (HomologicalComplex.homologyMap (Work.Pi6.SRANGE.relPairMapR R p (p e₀)) (i+1)) := hiso i hi
  have hginj : Function.Injective (HomologicalComplex.homologyMap
      (Work.Pi6.SRANGE.relPairMapR R p (p e₀)) (i+1)).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hgsurj : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Pi6.SRANGE.relPairMapR R p (p e₀)) (i+1)).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hcancel1 : ∀ w, (CategoryTheory.inv (HomologicalComplex.homologyMap
        (Work.Pi6.SRANGE.relPairMapR R p (p e₀)) (i+1))).hom
        ((HomologicalComplex.homologyMap (Work.Pi6.SRANGE.relPairMapR R p (p e₀)) (i+1)).hom w) = w := by
    intro w
    have h := congrArg (fun (m : (Work.StemsB.relChainsR R (TopCat.of E) (p ⁻¹' {p e₀})).homology (i+1)
          ⟶ (Work.StemsB.relChainsR R (TopCat.of E) (p ⁻¹' {p e₀})).homology (i+1)) => m.hom w)
      (IsIso.hom_inv_id (HomologicalComplex.homologyMap (Work.Pi6.SRANGE.relPairMapR R p (p e₀)) (i+1)))
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply] using h
  have hcancel2 : ∀ z, (HomologicalComplex.homologyMap
        (Work.Pi6.SRANGE.relPairMapR R p (p e₀)) (i+1)).hom
        ((CategoryTheory.inv (HomologicalComplex.homologyMap
          (Work.Pi6.SRANGE.relPairMapR R p (p e₀)) (i+1))).hom z) = z := by
    intro z
    have h := congrArg (fun (m : (Work.StemsB.relChainsR R (TopCat.of B) ({p e₀} : Set B)).homology (i+1)
          ⟶ (Work.StemsB.relChainsR R (TopCat.of B) ({p e₀} : Set B)).homology (i+1)) => m.hom z)
      (IsIso.inv_hom_id (HomologicalComplex.homologyMap (Work.Pi6.SRANGE.relPairMapR R p (p e₀)) (i+1)))
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply] using h
  refine ⟨?_, ?_, ?_⟩
  · -- (A) exactness at H_{i+1}(E;R)
    rw [Function.Exact]
    intro y
    rw [← hles2 y]
    constructor
    · intro hbeta
      have hzero : (HomologicalComplex.homologyMap (Work.Pi6.SRANGE.relPairMapR R p (p e₀)) (i+1)).hom
          ((HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of E) (p ⁻¹' {p e₀}))) (i+1)).hom y) = 0 := by
        rw [hnat y, hbeta, map_zero]
      exact hginj (by simpa using hzero)
    · intro hpi
      have hzero : (HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of B) ({p e₀} : Set B))) (i+1)).hom
          ((hmap R p (i+1)).hom y) = 0 := by
        rw [← hnat y, hpi, map_zero]
      exact hcaninj (by simpa using hzero)
  · -- (B) exactness at H_{i+1}(B;R)
    rw [Function.Exact]
    intro x
    show (Work.StemsB.relChainsRδ R (TopCat.of E) (p ⁻¹' {p e₀}) i).hom
        ((CategoryTheory.inv (HomologicalComplex.homologyMap (Work.Pi6.SRANGE.relPairMapR R p (p e₀)) (i+1))).hom
          ((HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of B) ({p e₀} : Set B))) (i+1)).hom x)) = 0
      ↔ x ∈ Set.range (hmap R p (i+1)).hom
    rw [hles3 ((CategoryTheory.inv (HomologicalComplex.homologyMap (Work.Pi6.SRANGE.relPairMapR R p (p e₀)) (i+1))).hom
      ((HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of B) ({p e₀} : Set B))) (i+1)).hom x))]
    constructor
    · intro hmem
      obtain ⟨z, hz⟩ := hmem
      refine ⟨z, ?_⟩
      have h1 : (HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of B) ({p e₀} : Set B))) (i+1)).hom
          ((hmap R p (i+1)).hom z)
          = (HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of B) ({p e₀} : Set B))) (i+1)).hom x := by
        rw [← hnat z, hz, hcancel2]
      exact hcaninj h1
    · intro hmem
      obtain ⟨z, hz⟩ := hmem
      refine ⟨z, ?_⟩
      rw [← hz, ← hnat z, hcancel1]
  · -- (C) exactness at H_i(F;R)
    rw [Function.Exact]
    intro x
    show (hmap R (Work.StemsB.fibreIncl p (p e₀)) i).hom x = 0
      ↔ x ∈ Set.range (fun y => (Work.StemsB.relChainsRδ R (TopCat.of E) (p ⁻¹' {p e₀}) i).hom
          ((CategoryTheory.inv (HomologicalComplex.homologyMap (Work.Pi6.SRANGE.relPairMapR R p (p e₀)) (i+1))).hom
            ((HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of B) ({p e₀} : Set B))) (i+1)).hom y)))
    rw [hles1 x]
    constructor
    · intro hmem
      obtain ⟨w, hw⟩ := hmem
      obtain ⟨y, hy⟩ := hcansurj ((HomologicalComplex.homologyMap (Work.Pi6.SRANGE.relPairMapR R p (p e₀)) (i+1)).hom w)
      refine ⟨y, ?_⟩
      show (Work.StemsB.relChainsRδ R (TopCat.of E) (p ⁻¹' {p e₀}) i).hom
          ((CategoryTheory.inv (HomologicalComplex.homologyMap (Work.Pi6.SRANGE.relPairMapR R p (p e₀)) (i+1))).hom
            ((HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of B) ({p e₀} : Set B))) (i+1)).hom y)) = x
      rw [hy, hcancel1 w, hw]
    · intro hmem
      obtain ⟨y, hy⟩ := hmem
      refine ⟨(CategoryTheory.inv (HomologicalComplex.homologyMap (Work.Pi6.SRANGE.relPairMapR R p (p e₀)) (i+1))).hom
        ((HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of B) ({p e₀} : Set B))) (i+1)).hom y), ?_⟩
      exact hy

end

end Work.Pi6
