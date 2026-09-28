import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_glue_defs

/-!
# Homology of an increasing union of open sets

Let `M` be a topological space and `W : ℕ → Set M` an increasing sequence of open subsets,
`W₀ ⊆ W₁ ⊆ ⋯ ⊆ ⋃ᵢ Wᵢ`.  This file proves `Work.Cohomology.pdHom_iUnion_lift`: every singular
homology class of the union `⋃ᵢ Wᵢ` comes from some finite stage,

`H_m(⋃ᵢ Wᵢ) = ⋃ᵢ (image of H_m(Wᵢ))`.

The proof is the classical compactness argument, made explicit:

* `exists_factor_iUnion` — a singular simplex of the union (a continuous map out of the compact
  `Δⁿ`) lands in some single `Wᵢ`, i.e. factors through the inclusion `Wᵢ ↪ ⋃ⱼ Wⱼ`;
* `gen_mem_range_pdIncChain`, `iSup_range_pdIncChain_eq_top` — consequently the chain module of the
  union is the directed union of the images of the chain modules of the `Wᵢ`;
* `range_pdIncChain_le` — the inclusions of chains are compatible with the monotonicity of `W`;
* `injective_chainMap_pdIncChain` — the inclusion `C_*(Wᵢ) ⟶ C_*(⋃ⱼ Wⱼ)` is degreewise injective.

The final step is the standard one: lift a cycle of the union to a chain of `Wᵢ` for some `i`
(possible by the chain-level statement), observe that this chain is a cycle because the inclusion is
degreewise injective, and read off the class.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Cohomology

noncomputable section

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Simplicial
open scoped Simplicial

/-- The chain map `C_*(Wᵢ) ⟶ C_*(⋃ⱼ Wⱼ)` induced by the inclusion of `Wᵢ` in the union. -/
abbrev pdIncChain {M : TopCat} (W : ℕ → Set M) (i : ℕ) :
    singularChains ℤ (TopCat.of (W i)) ⟶ singularChains ℤ (TopCat.of (⋃ j, W j)) :=
  chainMap ℤ (TopCat.of (W i)) (TopCat.of (⋃ j, W j))
    (pdIncl (⋃ j, W j) (W i) (Set.subset_iUnion W i))

/-! ## Simplices of the union factor through a finite stage -/

/-- **A singular simplex of an increasing union of open sets lands in one of the sets.**  The
preimages under the simplex of the (open) `Wᵢ` form an open cover of the compact `Δⁿ`; a finite
subcover together with monotonicity gives a single index. -/
theorem exists_factor_iUnion {M : TopCat} (W : ℕ → Set M) (hWopen : ∀ i, IsOpen (W i))
    (hmono : Monotone W) (n : ℕ) (σ : Simplex (TopCat.of (⋃ j, W j)) n) :
    ∃ (i : ℕ) (σ' : Simplex (TopCat.of (W i)) n),
      (TopCat.toSSet.map (pdIncl (⋃ j, W j) (W i) (Set.subset_iUnion W i))).app _ σ' = σ := by
  let f : C(stdSimplex ℝ (Fin (n+1)), (⋃ j, W j : Set M)) :=
    TopCat.toSSetObjEquivT (TopCat.of (⋃ j, W j)) (Opposite.op (SimplexCategory.mk n)) σ
  have hfcont : Continuous (fun z : stdSimplex ℝ (Fin (n+1)) => ((f z : (⋃ j, W j : Set M)) : M)) :=
    continuous_subtype_val.comp f.continuous
  let V : ℕ → Set (stdSimplex ℝ (Fin (n+1))) := fun i =>
    {z | ((f z : (⋃ j, W j : Set M)) : M) ∈ W i}
  have hVopen : ∀ i, IsOpen (V i) := fun i => (hWopen i).preimage hfcont
  have hVcover : (Set.univ : Set (stdSimplex ℝ (Fin (n+1)))) ⊆ ⋃ i, V i := by
    intro z _
    obtain ⟨i, hi⟩ : ∃ i, ((f z : (⋃ j, W j : Set M)) : M) ∈ W i :=
      Set.mem_iUnion.mp (f z).2
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨t, ht⟩ := (isCompact_univ (X := stdSimplex ℝ (Fin (n+1)))).elim_finite_subcover V hVopen hVcover
  have htne : t.Nonempty := by
    have h := ht (Set.mem_univ (stdSimplex.vertex (0 : Fin (n+1))))
    simp only [Set.mem_iUnion] at h
    obtain ⟨j, hj, _⟩ := h
    exact ⟨j, hj⟩
  let i₀ := t.max' htne
  have hsub : ∀ j ∈ t, V j ⊆ V i₀ := by
    intro j hj z hz
    exact hmono (Finset.le_max' t j hj) hz
  have hVi₀ : ∀ z, ((f z : (⋃ j, W j : Set M)) : M) ∈ W i₀ := by
    intro z
    have hz := ht (Set.mem_univ z)
    simp only [Set.mem_iUnion] at hz
    obtain ⟨j, hj, hzj⟩ := hz
    exact hsub j hj hzj
  refine ⟨i₀, ?_, ?_⟩
  · exact (TopCat.toSSetObjEquivT (TopCat.of (W i₀)) (Opposite.op (SimplexCategory.mk n))).symm
      ⟨fun z => ⟨((f z : (⋃ j, W j : Set M)) : M), hVi₀ z⟩,
       Continuous.subtype_mk hfcont (fun z => hVi₀ z)⟩
  · apply (TopCat.toSSetObjEquivT (TopCat.of (⋃ j, W j)) (Opposite.op (SimplexCategory.mk n))).injective
    ext z
    rw [toSSetObjEquiv_map_apply]
    rfl

/-! ## The chain modules of the union are the directed union of the images -/

/-- Every generator of the chains of the union lies in the image of the chains of some `Wᵢ`. -/
theorem gen_mem_range_pdIncChain {M : TopCat} (W : ℕ → Set M) (hWopen : ∀ i, IsOpen (W i))
    (hmono : Monotone W) (n : ℕ) (σ : Simplex (TopCat.of (⋃ j, W j)) n) :
    ∃ i, gen (TopCat.of (⋃ j, W j)) n σ ∈ LinearMap.range ((pdIncChain W i).f n).hom := by
  obtain ⟨i, σ', hσ'⟩ := exists_factor_iUnion W hWopen hmono n σ
  refine ⟨i, ?_⟩
  rw [LinearMap.mem_range]
  refine ⟨gen (TopCat.of (W i)) n σ', ?_⟩
  rw [← hσ']
  exact chainComplexMap_ι_apply
    (TopCat.toSSet.map (pdIncl (⋃ j, W j) (W i) (Set.subset_iUnion W i))) n σ' 1

/-- **The chains of the union are the directed union of the images of the chains of the `Wᵢ`.** -/
theorem iSup_range_pdIncChain_eq_top {M : TopCat} (W : ℕ → Set M) (hWopen : ∀ i, IsOpen (W i))
    (hmono : Monotone W) (n : ℕ) :
    (⨆ i, LinearMap.range ((pdIncChain W i).f n).hom) = ⊤ := by
  apply mem_of_gen (TopCat.of (⋃ j, W j)) n
  intro σ
  obtain ⟨i, hi⟩ := gen_mem_range_pdIncChain W hWopen hmono n σ
  exact le_iSup (fun i => LinearMap.range ((pdIncChain W i).f n).hom) i hi

/-- The images of the chain modules are compatible with the monotonicity of `W`. -/
theorem range_pdIncChain_le {M : TopCat} (W : ℕ → Set M) (hmono : Monotone W) {i j : ℕ}
    (hij : i ≤ j) (n : ℕ) :
    LinearMap.range ((pdIncChain W i).f n).hom ≤ LinearMap.range ((pdIncChain W j).f n).hom := by
  have hchain : pdIncChain W i
      = chainMap ℤ (TopCat.of (W i)) (TopCat.of (W j)) (pdIncl (W j) (W i) (hmono hij))
        ≫ pdIncChain W j := by
    show chainMap ℤ (TopCat.of (W i)) (TopCat.of (⋃ k, W k))
          (pdIncl (⋃ k, W k) (W i) (Set.subset_iUnion W i))
        = chainMap ℤ (TopCat.of (W i)) (TopCat.of (W j)) (pdIncl (W j) (W i) (hmono hij))
          ≫ chainMap ℤ (TopCat.of (W j)) (TopCat.of (⋃ k, W k))
              (pdIncl (⋃ k, W k) (W j) (Set.subset_iUnion W j))
    have hcomp : pdIncl (W j) (W i) (hmono hij)
          ≫ pdIncl (⋃ k, W k) (W j) (Set.subset_iUnion W j)
        = pdIncl (⋃ k, W k) (W i) (Set.subset_iUnion W i) := by ext y; rfl
    rw [← hcomp, chainMap_comp']
  rw [hchain, HomologicalComplex.comp_f, ModuleCat.hom_comp]
  exact LinearMap.range_comp_le_range _ _

/-- The inclusion of the chains of `Wᵢ` into the chains of the union is degreewise injective. -/
theorem injective_chainMap_pdIncChain {M : TopCat} (W : ℕ → Set M) (i n : ℕ) :
    Function.Injective (((pdIncChain W i).f n).hom) := by
  haveI : Mono (pdIncChain W i) := by
    haveI : Mono (pdIncl (⋃ j, W j) (W i) (Set.subset_iUnion W i)) := by
      rw [TopCat.mono_iff_injective]
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun x : (⋃ j, W j : Set M) => (x : M)) hab
    show Mono (chainMap ℤ (TopCat.of (W i)) (TopCat.of (⋃ j, W j))
      (pdIncl (⋃ j, W j) (W i) (Set.subset_iUnion W i)))
    exact Functor.map_mono
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
      (pdIncl (⋃ j, W j) (W i) (Set.subset_iUnion W i))
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

/-! ## The main statement -/

theorem pdHom_iUnion_lift {M : TopCat} (W : ℕ → Set M) (hWopen : ∀ i, IsOpen (W i))
    (hmono : Monotone W) (m : ℕ)
    (y : (Work.Cohomology.singularChains ℤ (TopCat.of (⋃ i, W i))).homology m) :
    ∃ (i : ℕ) (yi : (Work.Cohomology.singularChains ℤ (TopCat.of (W i))).homology m),
      (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (W i))
        (TopCat.of (⋃ j, W j)) (Work.Cohomology.pdIncl (⋃ j, W j) (W i)
          (Set.subset_iUnion W i))) m) yi = y := by
  classical
  -- The family of submodules consisting of the images of the chains of the `Wᵢ`.
  let Sfam : ℕ → Submodule ℤ ↥((singularChains ℤ (TopCat.of (⋃ j, W j))).X m) :=
    fun i => LinearMap.range ((pdIncChain W i).f m).hom
  have htop : (⨆ i, Sfam i) = ⊤ := iSup_range_pdIncChain_eq_top W hWopen hmono m
  have hdir : Directed (· ≤ ·) Sfam := by
    intro i j
    exact ⟨max i j, range_pdIncChain_le W hmono (le_max_left i j) m,
      range_pdIncChain_le W hmono (le_max_right i j) m⟩
  -- A cycle representing `y`.
  obtain ⟨zU, hzU⟩ := (ModuleCat.epi_iff_surjective
    ((singularChains ℤ (TopCat.of (⋃ j, W j))).homologyπ m)).mp inferInstance y
  have hmem : (HomologicalComplex.iCycles (singularChains ℤ (TopCat.of (⋃ j, W j))) m) zU
      ∈ ⨆ i, Sfam i := by rw [htop]; exact Submodule.mem_top
  rw [Submodule.mem_iSup_of_directed Sfam hdir] at hmem
  obtain ⟨i, hmem⟩ := hmem
  rw [LinearMap.mem_range] at hmem
  obtain ⟨zi, hzi⟩ := hmem
  -- `zi` is a cycle: the boundary maps to zero under the (injective) inclusion.
  have hcomm := HomologicalComplex.Hom.comm (pdIncChain W i) m ((ComplexShape.down ℕ).next m)
  have hcomm2 := congrArg (fun (g : (singularChains ℤ (TopCat.of (W i))).X m ⟶
      (singularChains ℤ (TopCat.of (⋃ j, W j))).X ((ComplexShape.down ℕ).next m)) => g.hom zi) hcomm
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm2
  have hd : (HomologicalComplex.iCycles (singularChains ℤ (TopCat.of (⋃ j, W j))) m) zU
      ∈ LinearMap.ker ((singularChains ℤ (TopCat.of (⋃ j, W j))).d m ((ComplexShape.down ℕ).next m)).hom := by
    rw [LinearMap.mem_ker]
    have h := congrArg (fun (g : (singularChains ℤ (TopCat.of (⋃ j, W j))).cycles m ⟶
        (singularChains ℤ (TopCat.of (⋃ j, W j))).X ((ComplexShape.down ℕ).next m)) => g.hom zU)
      (HomologicalComplex.iCycles_d (K := (singularChains ℤ (TopCat.of (⋃ j, W j))))
        (i := m) (j := (ComplexShape.down ℕ).next m))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h
  have hzicyc : ((singularChains ℤ (TopCat.of (W i))).d m ((ComplexShape.down ℕ).next m)).hom zi = 0 := by
    refine injective_chainMap_pdIncChain W i ((ComplexShape.down ℕ).next m) ?_
    rw [map_zero, ← hcomm2, hzi]
    exact hd
  let zi_cyc : (singularChains ℤ (TopCat.of (W i))).cycles m :=
    (singularChains ℤ (TopCat.of (W i))).cyclesMk zi ((ComplexShape.down ℕ).next m) rfl hzicyc
  have hzi_cyc_i : (HomologicalComplex.iCycles (singularChains ℤ (TopCat.of (W i))) m).hom zi_cyc = zi :=
    HomologicalComplex.i_cyclesMk (singularChains ℤ (TopCat.of (W i))) zi ((ComplexShape.down ℕ).next m) rfl hzicyc
  refine ⟨i, (singularChains ℤ (TopCat.of (W i))).homologyπ m zi_cyc, ?_⟩
  -- Naturality of `homologyπ` reduces the claim to an equality of cycles.
  have hnat := congrArg (fun (g : (singularChains ℤ (TopCat.of (W i))).cycles m ⟶
      (singularChains ℤ (TopCat.of (⋃ j, W j))).homology m) => g.hom zi_cyc)
    (HomologicalComplex.homologyπ_naturality (pdIncChain W i) m)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [← hzU, hnat]
  congr 1
  have hinj : Function.Injective
      (HomologicalComplex.iCycles (singularChains ℤ (TopCat.of (⋃ j, W j))) m).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  apply hinj
  have hci := congrArg (fun (g : (singularChains ℤ (TopCat.of (W i))).cycles m ⟶
      (singularChains ℤ (TopCat.of (⋃ j, W j))).X m) => g.hom zi_cyc)
    (HomologicalComplex.cyclesMap_i (pdIncChain W i) m)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hci
  rw [hci, hzi_cyc_i]
  exact hzi

end

end Work.Cohomology
