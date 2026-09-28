import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_glue_defs
import Submission.Work.Cohomology.pdHom_iUnion_lift

/-!
# Killing a homology class of a finite stage inside an increasing union of open sets

Let `W : ℕ → Set M` be an increasing sequence of open subsets of `M`.  The singular chains of the
union `⋃ⱼ Wⱼ` are the directed union of the chains of the finite stages (this is
`Work.Cohomology.pdHom_iUnion_lift`), and consequently so is homology:

`H_m(⋃ⱼ Wⱼ) = colim_j H_m(Wⱼ)`.

This file proves the *injectivity* half of that statement, `pdHom_iUnion_kill`: a homology class
`yᵢ ∈ H_m(Wᵢ)` that dies in `H_m(⋃ⱼ Wⱼ)` is already killed at some finite stage `Wⱼ`, `j ≥ i`.

The argument is the classical chain-level compactness one, using the chain-level description of the
directed union supplied by `pdHom_iUnion_lift`:

* lift a representative cycle `z` of `yᵢ` to a cycle of `Wᵢ`;
* the image of `yᵢ` in the union is zero, so the image chain is a boundary `∂w` of the union;
* a chain of the union lands in a finite stage (`iSup_range_pdIncChain_eq_top`), and enlarging the
  stage so that it dominates `i` and using the injectivity of the inclusion of chains
  (`injective_chainMap_pdIncChain`) shows that the image chain of `z` is already a boundary in that
  stage;
* a chain that is a boundary represents the zero homology class.

The two chain-complex lemmas `pdHom_homologyπ_eq_zero_iff_sc` and
`pdHom_homologyπ_eq_zero_iff_d` are the bridge between the categorical `homologyπ` and the
chain-level statement "the cycle underlying the class is a boundary"; they are proved from the
explicit (module-theoretic) description of the homology of a short complex of `ℤ`-modules.

## Contents

* `pdHom_homologyπ_eq_zero_iff_sc` — the criterion in a short complex of `ℤ`-modules;
* `pdHom_homologyπ_eq_zero_iff_d` — the criterion for a chain complex indexed by `ℕ`;
* `pdHom_iUnion_kill` — the main statement.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- **Vanishing of `homologyπ` means "the cycle is a boundary".**

For a short complex `S` of `ℤ`-modules and a cycle `z ∈ S.cycles`, the homology class of `z` is
zero if and only if the image of `z` in `S.X₂` is in the image of `S.f`.

The proof uses the explicit description of the homology of a short complex of modules: the
monomorphism `homologyι : S.homology ⟶ S.opcycles` turns the vanishing into the vanishing in
`S.opcycles`, where it is exactly "in the range of `S.f`"
(`ShortComplex.moduleCat_pOpcycles_eq_zero_iff`). -/
theorem pdHom_homologyπ_eq_zero_iff_sc {S : ShortComplex (ModuleCat ℤ)} [S.HasHomology]
    (z : S.cycles) :
    S.homologyπ z = 0 ↔ ∃ w : S.X₁, S.f.hom w = S.iCycles z := by
  have h1 : S.homologyπ z = 0 ↔ S.homologyι (S.homologyπ z) = 0 :=
    ⟨fun h => by rw [h, map_zero], fun h =>
      (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance (by rw [h, map_zero])⟩
  rw [h1]
  have h2 : S.homologyι (S.homologyπ z) = S.pOpcycles (S.iCycles z) := by
    have h := congrArg (fun (g : S.cycles ⟶ S.opcycles) => g z) (S.homology_π_ι)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  rw [h2, S.moduleCat_pOpcycles_eq_zero_iff, LinearMap.mem_range]

/-- **Vanishing of `homologyπ` in a chain complex indexed by `ℕ`.**

For a chain complex `C` of `ℤ`-modules indexed by `ℕ`(with the shape of a chain complex, so that
the differentials are `C.d (m+1) m : C.X (m+1) ⟶ C.X m`) and a cycle `z ∈ C.cycles m`, the homology
class of `z` is zero if and only if `z` is a boundary, i.e. the image of `z` in `C.X m` is
`C.d (m+1) m w` for some `(m+1)`-chain `w`.

This is `pdHom_homologyπ_eq_zero_iff_sc` applied to the short complex `C.sc m`, transported across
`(ComplexShape.down ℕ).prev m = m + 1`. -/
theorem pdHom_homologyπ_eq_zero_iff_d {C : ChainComplex (ModuleCat ℤ) ℕ} [∀ i, C.HasHomology i]
    (m : ℕ) (z : C.cycles m) :
    C.homologyπ m z = 0 ↔ ∃ w : C.X (m+1), C.d (m+1) m w = C.iCycles m z := by
  have hrel : (ComplexShape.down ℕ).Rel (m+1) m := by rw [ComplexShape.down_Rel]
  have hprev : (ComplexShape.down ℕ).prev m = m + 1 := ComplexShape.prev_eq' _ hrel
  have key := pdHom_homologyπ_eq_zero_iff_sc (S := C.sc m) (z := z)
  have hR : (∃ w : (C.sc m).X₁, (C.sc m).f.hom w = (C.sc m).iCycles z)
      ↔ ∃ w : C.X (m+1), C.d (m+1) m w = C.iCycles m z := by
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨(C.XIsoOfEq hprev.symm).inv w, ?_⟩
      rw [← ModuleCat.comp_apply, HomologicalComplex.XIsoOfEq_inv_comp_d]
      exact hw
    · rintro ⟨w, hw⟩
      refine ⟨(C.XIsoOfEq hprev).inv w, ?_⟩
      change C.d ((ComplexShape.down ℕ).prev m) m ((C.XIsoOfEq hprev).inv w) = C.iCycles m z
      rw [← ModuleCat.comp_apply, HomologicalComplex.XIsoOfEq_inv_comp_d]
      exact hw
  exact (Iff.of_eq (show ((C.sc m).homologyπ z = 0) = (C.homologyπ m z = 0) from rfl)).symm.trans
    (key.trans hR)

/-- **Every homology class of a finite stage that dies in the union already dies at a finite stage.**

Let `W : ℕ → Set M` be increasing with each `W i` open, `i ≤ j`, and `yᵢ ∈ H_m(Wᵢ)` a homology class
whose image in `H_m(⋃ⱼ Wⱼ)` is zero.  Then there is `j ≥ i` such that the image of `yᵢ` in
`H_m(Wⱼ)` is already zero. -/
theorem pdHom_iUnion_kill {M : TopCat} (W : ℕ → Set M) (hWopen : ∀ i, IsOpen (W i))
    (hmono : Monotone W) (m i : ℕ)
    (yi : (Work.Cohomology.singularChains ℤ (TopCat.of (W i))).homology m)
    (hy : (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (W i))
      (TopCat.of (⋃ j, W j)) (Work.Cohomology.pdIncl (⋃ j, W j) (W i)
        (Set.subset_iUnion W i))) m) yi = 0) :
    ∃ (j : ℕ) (hij : i ≤ j),
      (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (W i))
        (TopCat.of (W j)) (Work.Cohomology.pdIncl (W j) (W i) (hmono hij))) m) yi = 0 := by
  classical
  -- ## Step 1: a cycle representative `zi` of the class `yi`
  obtain ⟨zi, hzi⟩ := (ModuleCat.epi_iff_surjective
    ((singularChains ℤ (TopCat.of (W i))).homologyπ m)).mp inferInstance yi
  -- ## Step 2: the image cycle in the union has vanishing homology class
  have hB : (singularChains ℤ (TopCat.of (⋃ j, W j))).homologyπ m
      (HomologicalComplex.cyclesMap (pdIncChain W i) m zi) = 0 := by
    have hnat := congrArg (fun (g : (singularChains ℤ (TopCat.of (W i))).cycles m ⟶
        (singularChains ℤ (TopCat.of (⋃ j, W j))).homology m) => g zi)
      (HomologicalComplex.homologyπ_naturality (pdIncChain W i) m)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
    rw [hzi, hy] at hnat
    exact hnat.symm
  -- ## Step 3: it is therefore a boundary of the union
  obtain ⟨wU, hwU⟩ := (pdHom_homologyπ_eq_zero_iff_d (C := singularChains ℤ (TopCat.of (⋃ j, W j))) m
    (HomologicalComplex.cyclesMap (pdIncChain W i) m zi)).mp hB
  have hD : (singularChains ℤ (TopCat.of (⋃ j, W j))).iCycles m
      (HomologicalComplex.cyclesMap (pdIncChain W i) m zi)
      = (pdIncChain W i).f m ((singularChains ℤ (TopCat.of (W i))).iCycles m zi) := by
    have h := congrArg (fun (g : (singularChains ℤ (TopCat.of (W i))).cycles m ⟶
        (singularChains ℤ (TopCat.of (⋃ j, W j))).X m) => g zi)
      (HomologicalComplex.cyclesMap_i (pdIncChain W i) m)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  rw [hD] at hwU
  -- ## Step 4: the bounding chain of the union lies in a finite stage `W j'` with `j' ≥ i`
  have hdir : Directed (· ≤ ·) (fun j => LinearMap.range ((pdIncChain W j).f (m+1)).hom) := by
    intro a b
    exact ⟨max a b, range_pdIncChain_le W hmono (le_max_left a b) (m+1),
      range_pdIncChain_le W hmono (le_max_right a b) (m+1)⟩
  have hmem : wU ∈ ⨆ j, LinearMap.range ((pdIncChain W j).f (m+1)).hom := by
    rw [iSup_range_pdIncChain_eq_top W hWopen hmono (m+1)]
    exact Submodule.mem_top
  rw [Submodule.mem_iSup_of_directed _ hdir] at hmem
  obtain ⟨j0, hj0⟩ := hmem
  set j' : ℕ := max i j0 with hj'def
  have hij' : i ≤ j' := by rw [hj'def]; exact le_max_left i j0
  have hj0j' : j0 ≤ j' := by rw [hj'def]; exact le_max_right i j0
  have hle : LinearMap.range ((pdIncChain W j0).f (m+1)).hom ≤
      LinearMap.range ((pdIncChain W j').f (m+1)).hom :=
    range_pdIncChain_le W hmono hj0j' (m+1)
  have hmem' : wU ∈ LinearMap.range ((pdIncChain W j').f (m+1)).hom := hle hj0
  rw [LinearMap.mem_range] at hmem'
  obtain ⟨w'', hw''⟩ := hmem'
  -- ## Step 5: the chain-level compatibilities
  have hchain : pdIncChain W i = chainMap ℤ (TopCat.of (W i)) (TopCat.of (W j'))
      (pdIncl (W j') (W i) (hmono hij')) ≫ pdIncChain W j' := by
    show chainMap ℤ (TopCat.of (W i)) (TopCat.of (⋃ k, W k))
        (pdIncl (⋃ k, W k) (W i) (Set.subset_iUnion W i))
        = chainMap ℤ (TopCat.of (W i)) (TopCat.of (W j')) (pdIncl (W j') (W i) (hmono hij'))
          ≫ chainMap ℤ (TopCat.of (W j')) (TopCat.of (⋃ k, W k))
              (pdIncl (⋃ k, W k) (W j') (Set.subset_iUnion W j'))
    have hcomp : pdIncl (W j') (W i) (hmono hij')
          ≫ pdIncl (⋃ k, W k) (W j') (Set.subset_iUnion W j')
        = pdIncl (⋃ k, W k) (W i) (Set.subset_iUnion W i) := by ext y; rfl
    rw [← hcomp, chainMap_comp']
  have hkey : (pdIncChain W j').f m ((chainMap ℤ (TopCat.of (W i)) (TopCat.of (W j'))
        (pdIncl (W j') (W i) (hmono hij'))).f m
          ((singularChains ℤ (TopCat.of (W i))).iCycles m zi))
      = (pdIncChain W i).f m ((singularChains ℤ (TopCat.of (W i))).iCycles m zi) := by
    conv_rhs => rw [hchain]
    rw [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  have hcomm : (singularChains ℤ (TopCat.of (⋃ k, W k))).d (m+1) m
        ((pdIncChain W j').f (m+1) w'') =
      (pdIncChain W j').f m ((singularChains ℤ (TopCat.of (W j'))).d (m+1) m w'') := by
    have h := congrArg (fun (g : (singularChains ℤ (TopCat.of (W j'))).X (m+1) ⟶
        (singularChains ℤ (TopCat.of (⋃ k, W k))).X m) => g w'')
      (HomologicalComplex.Hom.comm (pdIncChain W j') (m+1) m)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  have hcyc_j : (singularChains ℤ (TopCat.of (W j'))).iCycles m
      (HomologicalComplex.cyclesMap (chainMap ℤ (TopCat.of (W i)) (TopCat.of (W j'))
        (pdIncl (W j') (W i) (hmono hij'))) m zi)
      = (chainMap ℤ (TopCat.of (W i)) (TopCat.of (W j'))
        (pdIncl (W j') (W i) (hmono hij'))).f m
          ((singularChains ℤ (TopCat.of (W i))).iCycles m zi) := by
    have h := congrArg (fun (g : (singularChains ℤ (TopCat.of (W i))).cycles m ⟶
        (singularChains ℤ (TopCat.of (W j'))).X m) => g zi)
      (HomologicalComplex.cyclesMap_i (chainMap ℤ (TopCat.of (W i)) (TopCat.of (W j'))
        (pdIncl (W j') (W i) (hmono hij'))) m)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  -- ## Step 6: the same chain `w''` bounds the image of `z` in the stage `W j'`
  have hEdge : (singularChains ℤ (TopCat.of (W j'))).d (m+1) m w'' =
      (chainMap ℤ (TopCat.of (W i)) (TopCat.of (W j'))
        (pdIncl (W j') (W i) (hmono hij'))).f m
          ((singularChains ℤ (TopCat.of (W i))).iCycles m zi) := by
    apply injective_chainMap_pdIncChain W j' m
    rw [← hcomm, hw'', hwU, ← hkey]
  have hG : (singularChains ℤ (TopCat.of (W j'))).homologyπ m
      (HomologicalComplex.cyclesMap (chainMap ℤ (TopCat.of (W i)) (TopCat.of (W j'))
        (pdIncl (W j') (W i) (hmono hij'))) m zi) = 0 :=
    (pdHom_homologyπ_eq_zero_iff_d (C := singularChains ℤ (TopCat.of (W j'))) m _).mpr
      ⟨w'', by rw [hcyc_j, hEdge]⟩
  -- ## Step 7: conclude via the naturality square for `homologyπ`
  refine ⟨j', hij', ?_⟩
  have hnat2 := congrArg (fun (g : (singularChains ℤ (TopCat.of (W i))).cycles m ⟶
      (singularChains ℤ (TopCat.of (W j'))).homology m) => g zi)
    (HomologicalComplex.homologyπ_naturality (chainMap ℤ (TopCat.of (W i)) (TopCat.of (W j'))
      (pdIncl (W j') (W i) (hmono hij'))) m)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat2
  rw [hzi, hG] at hnat2
  exact hnat2

end

end Work.Cohomology
