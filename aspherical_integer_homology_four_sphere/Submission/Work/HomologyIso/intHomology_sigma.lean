import Mathlib
import Submission.Work.Homology.Basic
import Submission.Work.Homology.Pairs
import Submission.Work.Homology.Point
import Submission.Work.Homology.RelChainMap
import Submission.Work.Homology.Corollaries
import Submission.Work.Homology.SingHomologyHomeomorph
import Submission.Work.Homology.HomologyBiprod
import Submission.Work.Homology.SingHomologyClopen
import Submission.Work.Homology.ContractibleHomology
import Submission.Work.Homology.BallHomology
import Submission.Work.Homology.StdSimplexHomology
import Submission.Work.Homology.HomotopyEquivHomology
import Submission.Work.Homology.DeformationRetractHomology
import Submission.Work.Homology.SimplexShim
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Homology.Spheres
import Submission.Work.Homology.MayerVietoris
import Submission.Work.Homology.FiniteBiprodHomology

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The integral homology of a finite disjoint union

This file proves `Work.HomologyIso.intHomology_sigma`: for a finite family `X : ι → Type` of
topological spaces, the singular chain complex of the topological sum `Σ i, X i` splits as the
direct sum of the singular chain complexes of the pieces `X i` (the summands form a finite family
of pairwise disjoint open sets covering the sum), and homology is additive over finite biproducts
of chain complexes (`Work.Homology.FiniteBiprodHomology`), which yields
`H_k(Σ i, X i) ≅ ⨁ i, H_k(X i)`.

The finite-cover splitting developed in §1–§5 is a direct generalisation of the binary clopen
splitting of `Work.Homology.SingHomologyClopen`: a singular simplex of the ambient space, being a
continuous map out of the (preconnected) standard simplex, lands in exactly one member of a finite
family of pairwise disjoint open sets, and the resulting degreewise projection is a two-sided
inverse of the sum of the inclusions.
-/

namespace Work.HomologyIso

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Opposite
open scoped Simplicial
open Work.Homology

noncomputable section

/-- Chain complexes of `ℤ`-modules have finite biproducts. -/
local instance instChainComplexFiniteBiproducts :
    HasFiniteBiproducts (ChainComplex (ModuleCat ℤ) ℕ) :=
  Abelian.hasFiniteBiproducts (C := ChainComplex (ModuleCat ℤ) ℕ)

open Classical
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. Degreewise isomorphisms give isomorphisms of chain complexes -/

/-- A morphism of chain complexes out of a finite biproduct of chain complexes is an
isomorphism as soon as it is an isomorphism in every degree. -/
theorem isIso_biproductDesc_of_isIso_components {ι : Type} [Fintype ι]
    (K : ι → ChainComplex (ModuleCat ℤ) ℕ) [HasBiproduct K]
    {Y : ChainComplex (ModuleCat ℤ) ℕ} (f : ∀ i, K i ⟶ Y)
    (h : ∀ n, IsIso (biproduct.desc fun i => (f i).f n)) : IsIso (biproduct.desc f) := by
  have hcomp : ∀ n, IsIso ((biproduct.desc f).f n) := by
    intro n
    have hPres : PreservesBiproduct K
        (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n) :=
      preservesBiproduct_of_preservesCoproduct _
    haveI := hPres
    haveI hI : IsIso (biproduct.desc fun i => (f i).f n) := h n
    have hδ : ((HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapBiproduct K).inv
        ≫ (biproduct.desc f).f n = biproduct.desc (fun i => (f i).f n) :=
      biproduct.mapBiproduct_inv_map_desc
        (F := HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n) (f := K) f
    exact IsIso.of_isIso_fac_left hδ
  haveI (n : ℕ) : IsIso ((biproduct.desc f).f n) := hcomp n
  exact HomologicalComplex.Hom.isIso_of_components _

/-! ## 2. Finite pairwise disjoint open covers -/

/-- A finite family of pairwise disjoint open subsets covering a topological space. -/
structure SigmaOpenCover {ι : Type} [Fintype ι] (X : TopCat) (V : ι → Set X) : Prop where
  /-- every member is open -/
  isOpen_mem : ∀ i, IsOpen (V i)
  /-- distinct members are disjoint -/
  disjoint_mem : ∀ i j, i ≠ j → Disjoint (V i) (V j)
  /-- the family covers the whole space -/
  cover_mem : ∀ x : X, ∃ i, x ∈ V i

/-- Each member of a finite disjoint open cover is clopen (unwrapped form). -/
theorem isClopen_of_sigmaOpenCover {ι : Type} [Fintype ι] {X : Type} [TopologicalSpace X]
    (V : ι → Set X) (hopen : ∀ i, IsOpen (V i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j)) (hcov : ∀ x : X, ∃ i, x ∈ V i) (i : ι) :
    IsClopen (V i) := by
  refine ⟨?_, hopen i⟩
  rw [← isOpen_compl_iff]
  have hcompl : (V i)ᶜ = ⋃ j : {j : ι // j ≠ i}, V j := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := hcov x
      exact Set.mem_iUnion.mpr ⟨⟨j, fun hji => hx (hji ▸ hj)⟩, hj⟩
    · intro hx hxi
      obtain ⟨⟨j, hji⟩, hj⟩ := Set.mem_iUnion.mp hx
      exact (Set.disjoint_left.mp (hdisj j i hji)) hj hxi
  rw [hcompl]
  exact isOpen_iUnion fun j => hopen j

/-- **Existence of the side.**  A continuous map from a preconnected space into `X` whose
image meets `V i₀` has image contained in `V i₀` (each `V i` is clopen). -/
theorem sigma_exists_forall_mem_of_preconnected {ι : Type} [Fintype ι] {X Z : Type}
    [TopologicalSpace X] [TopologicalSpace Z] [PreconnectedSpace Z]
    {V : ι → Set X} (hopen : ∀ i, IsOpen (V i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j)) (hcov : ∀ x : X, ∃ i, x ∈ V i)
    (f : C(Z, X)) (z₀ : Z) : ∃ i, ∀ z, f z ∈ V i := by
  obtain ⟨i₀, hi₀⟩ := hcov (f z₀)
  refine ⟨i₀, fun z => ?_⟩
  have hcl : IsClopen (f ⁻¹' V i₀) :=
    ⟨(isClopen_of_sigmaOpenCover V hopen hdisj hcov i₀).1.preimage f.continuous,
      (hopen i₀).preimage f.continuous⟩
  rcases isClopen_iff.mp hcl with h | h
  · have : z₀ ∉ f ⁻¹' V i₀ := by rw [h]; exact Set.notMem_empty z₀
    exact absurd (Set.mem_preimage.mpr hi₀) this
  · exact Set.mem_preimage.mp (h ▸ Set.mem_univ z)

/-- **Uniqueness of the side.** -/
theorem sigma_eq_of_forall_mem_of_disjoint {ι : Type} {X Z : Type} [TopologicalSpace X]
    [TopologicalSpace Z] [Nonempty Z] {V : ι → Set X}
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (f : C(Z, X)) {i j : ι} (hi : ∀ z, f z ∈ V i) (hj : ∀ z, f z ∈ V j) : i = j := by
  by_contra hij
  exact (Set.disjoint_left.mp (hdisj i j hij)) (hi (Classical.arbitrary Z))
    (hj (Classical.arbitrary Z))

/-! ## 3. The side of a singular simplex -/

/-- The standard topological `n`-simplex. -/
abbrev sigStdSimplex (n : ℕ) : Type := Convexity.StdSimplex ℝ (Fin (n + 1))

/-- The type of singular `n`-simplices of `X`. -/
abbrev sigSimplex (X : TopCat) (n : ℕ) : Type :=
  (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))

/-- The continuous map `|Δⁿ| → X` underlying a singular `n`-simplex of `X`. -/
abbrev sigMap (X : TopCat) (n : ℕ) (z : sigSimplex X n) : C(sigStdSimplex n, X) :=
  TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) z

/-- A singular simplex of `X` lands in some member of a finite disjoint open cover. -/
theorem sig_exists_forall_mem {ι : Type} [Fintype ι] {X : TopCat} {V : ι → Set X}
    (h : SigmaOpenCover X V) (n : ℕ) (z : sigSimplex X n) :
    ∃ i, ∀ t, sigMap X n z t ∈ V i :=
  sigma_exists_forall_mem_of_preconnected h.isOpen_mem h.disjoint_mem h.cover_mem
    (sigMap X n z) (Classical.arbitrary (sigStdSimplex n))

/-- The member of the cover in which a singular simplex lands. -/
def sigSide {ι : Type} [Fintype ι] {X : TopCat} {V : ι → Set X} (h : SigmaOpenCover X V)
    (n : ℕ) (z : sigSimplex X n) : ι :=
  Classical.choose (sig_exists_forall_mem h n z)

/-- The defining property of `sigSide`. -/
theorem sigSide_spec {ι : Type} [Fintype ι] {X : TopCat} {V : ι → Set X}
    (h : SigmaOpenCover X V) (n : ℕ) (z : sigSimplex X n) :
    ∀ t, sigMap X n z t ∈ V (sigSide h n z) :=
  Classical.choose_spec (sig_exists_forall_mem h n z)

/-- Uniqueness of the member of the cover in which a singular simplex lands. -/
theorem sigSide_eq {ι : Type} [Fintype ι] {X : TopCat} {V : ι → Set X}
    (h : SigmaOpenCover X V) (n : ℕ) (z : sigSimplex X n) {i : ι}
    (hi : ∀ t, sigMap X n z t ∈ V i) : sigSide h n z = i :=
  sigma_eq_of_forall_mem_of_disjoint h.disjoint_mem (sigMap X n z) (sigSide_spec h n z) hi

/-- A simplex that lies in `V i` has side `i`. -/
theorem sigSide_incl {ι : Type} [Fintype ι] {X : TopCat} {V : ι → Set X}
    (h : SigmaOpenCover X V) (n : ℕ) (i : ι) (z : sigSimplex (TopCat.of (V i)) n) :
    sigSide h n ((TopCat.toSSet.map (incl (V i))).app
      (Opposite.op (SimplexCategory.mk n)) z) = i := by
  refine sigSide_eq h n _ fun t => ?_
  exact (TopCat.toSSetObjEquiv (TopCat.of (V i)) (Opposite.op (SimplexCategory.mk n)) z t).2

/-- A simplex of `X` whose side is `i` factors through `V i`. -/
theorem incl_sigSide_map {ι : Type} [Fintype ι] {X : TopCat} {V : ι → Set X}
    (h : SigmaOpenCover X V) (n : ℕ) (z : sigSimplex X n) :
    (TopCat.toSSet.map (incl (V (sigSide h n z)))).app
        (Opposite.op (SimplexCategory.mk n))
        (liftSimplex z (sigSide_spec h n z)) = z :=
  toSSet_map_incl_liftSimplex z (sigSide_spec h n z)

/-! ## 4. The degreewise projection onto the chains of a member -/

/-- The generator of the `n`-chains of `X` corresponding to a singular simplex. -/
abbrev sigGen (R : ModuleCat ℤ) (X : TopCat) (n : ℕ) (z : sigSimplex X n) :
    R ⟶ (sChain R X).X n :=
  Sigma.ι (fun _ : sigSimplex X n => R) z

/-- The degreewise projection of the `n`-chains of `X` onto the `n`-chains of `V i`: a singular
simplex of `X` is sent to its unique lift to `V i` if it lands in `V i`, and to `0` otherwise. -/
def sigProj {ι : Type} [Fintype ι] (X : TopCat) (V : ι → Set X)
    (h : SigmaOpenCover X V) (R : ModuleCat ℤ) (n : ℕ) (i : ι) :
    (sChain R X).X n ⟶ (sChain R (TopCat.of (V i))).X n :=
  Sigma.desc fun z =>
    if hz : ∀ t, sigMap X n z t ∈ V i then
      Sigma.ι (fun _ : sigSimplex (TopCat.of (V i)) n => R)
        (liftSimplex (A := V i) z hz)
    else 0

/-- The effect of `sigProj` on the generator corresponding to a singular simplex. -/
theorem sigGen_comp_sigProj {ι : Type} [Fintype ι] (X : TopCat) (V : ι → Set X)
    (h : SigmaOpenCover X V) (R : ModuleCat ℤ) (n : ℕ) (i : ι) (z : sigSimplex X n) :
    sigGen R X n z ≫ sigProj X V h R n i
      = if hz : ∀ t, sigMap X n z t ∈ V i then
          sigGen R (TopCat.of (V i)) n (liftSimplex (A := V i) z hz) else 0 := by
  unfold sigProj
  rw [Sigma.ι_comp_desc]

/-- The projection `sigProj` is a left inverse of the inclusion of the chains of `V i`. -/
theorem sigProj_comp_incl {ι : Type} [Fintype ι] (X : TopCat) (V : ι → Set X)
    (h : SigmaOpenCover X V) (R : ModuleCat ℤ) (n : ℕ) (i : ι) :
    (sChainMap R (incl (V i))).f n ≫ sigProj X V h R n i
      = 𝟙 ((sChain R (TopCat.of (V i))).X n) := by
  apply SSet.chainComplex_hom_ext
  intro z
  rw [Category.comp_id]
  change sigGen R (TopCat.of (V i)) n z
      ≫ ((sChainMap R (incl (V i))).f n ≫ sigProj X V h R n i)
    = sigGen R (TopCat.of (V i)) n z
  rw [← Category.assoc, sChainMap_incl_ι, sigGen_comp_sigProj]
  have hz : ∀ t, sigMap X n ((TopCat.toSSet.map (incl (V i))).app
      (Opposite.op (SimplexCategory.mk n)) z) t ∈ V i :=
    fun t => (TopCat.toSSetObjEquiv (TopCat.of (V i)) (Opposite.op (SimplexCategory.mk n)) z t).2
  rw [dite_eq_left hz, liftSimplex_apply_incl]

/-- `sigProj _ _ j` kills the simplices that are not contained in `V j`. -/
theorem sigGen_comp_sigProj_eq_zero {ι : Type} [Fintype ι] (X : TopCat) (V : ι → Set X)
    (h : SigmaOpenCover X V) (R : ModuleCat ℤ) (n : ℕ) (j : ι) (z : sigSimplex X n)
    (hz : ¬ ∀ t, sigMap X n z t ∈ V j) :
    sigGen R X n z ≫ sigProj X V h R n j = 0 := by
  rw [sigGen_comp_sigProj, dite_eq_right hz]

/-- `sigProj _ _ j` kills the simplices that land in a different member `V i`. -/
theorem sigProj_comp_incl_zero {ι : Type} [Fintype ι] (X : TopCat) (V : ι → Set X)
    (h : SigmaOpenCover X V) (R : ModuleCat ℤ) (n : ℕ) {i j : ι} (hij : i ≠ j) :
    (sChainMap R (incl (V i))).f n ≫ sigProj X V h R n j = 0 := by
  apply SSet.chainComplex_hom_ext
  intro z
  change sigGen R (TopCat.of (V i)) n z
      ≫ ((sChainMap R (incl (V i))).f n ≫ sigProj X V h R n j)
    = sigGen R (TopCat.of (V i)) n z ≫ 0
  rw [comp_zero, ← Category.assoc, sChainMap_incl_ι]
  refine sigGen_comp_sigProj_eq_zero X V h R n j _ fun hall => ?_
  refine (Set.disjoint_left.mp (h.disjoint_mem i j hij))
    (show sigMap X n ((TopCat.toSSet.map (incl (V i))).app
      (Opposite.op (SimplexCategory.mk n)) z) (Classical.arbitrary (sigStdSimplex n)) ∈ V i from
      (TopCat.toSSetObjEquiv (TopCat.of (V i)) (Opposite.op (SimplexCategory.mk n)) z _).2)
    (hall _)

/-- The `sigProj` maps sum up to the identity on the chains of `X`. -/
theorem sum_sigProj_comp_incl {ι : Type} [Fintype ι] (X : TopCat) (V : ι → Set X)
    (h : SigmaOpenCover X V) (R : ModuleCat ℤ) (n : ℕ) :
    ∑ i, sigProj X V h R n i ≫ (sChainMap R (incl (V i))).f n
      = 𝟙 ((sChain R X).X n) := by
  apply SSet.chainComplex_hom_ext
  intro z
  rw [Preadditive.comp_sum, Category.comp_id]
  change ∑ i, sigGen R X n z
      ≫ (sigProj X V h R n i ≫ (sChainMap R (incl (V i))).f n) = sigGen R X n z
  have hterm : ∀ i, sigGen R X n z
      ≫ (sigProj X V h R n i ≫ (sChainMap R (incl (V i))).f n)
      = if hz : ∀ t, sigMap X n z t ∈ V i then sigGen R X n z else 0 := by
    intro i
    by_cases hz : ∀ t, sigMap X n z t ∈ V i
    · rw [dite_eq_left hz, ← Category.assoc, sigGen_comp_sigProj, dite_eq_left hz]
      rw [sChainMap_incl_ι, toSSet_map_incl_liftSimplex]
    · rw [dite_eq_right hz, ← Category.assoc, sigGen_comp_sigProj, dite_eq_right hz]
      simp
  have hside : ∀ i, sigGen R X n z
      ≫ (sigProj X V h R n i ≫ (sChainMap R (incl (V i))).f n)
      = if i = sigSide h n z then sigGen R X n z else 0 := by
    intro i
    rw [hterm i]
    by_cases hz : ∀ t, sigMap X n z t ∈ V i
    · rw [dite_eq_left hz, ite_eq_left (sigSide_eq h n z hz).symm]
    · rw [dite_eq_right hz, ite_eq_right]
      intro hEq
      exact hz (hEq ▸ sigSide_spec h n z)
  rw [Finset.sum_congr rfl fun i _ => hside i,
    Finset.sum_ite_eq' Finset.univ (sigSide h n z) fun _ => sigGen R X n z]
  simp

/-! ## 5. The degreewise and chain level splittings -/

/-- **The degreewise splitting.**  In each degree, the sum of the inclusions of the chain
complexes of the members of a finite disjoint open cover is an isomorphism. -/
theorem isIso_biproduct_desc_sigmaOpenCover {ι : Type} [Fintype ι] (X : TopCat)
    (V : ι → Set X) (h : SigmaOpenCover X V) (R : ModuleCat ℤ) (n : ℕ) :
    IsIso (biproduct.desc fun i => (sChainMap R (incl (V i))).f n) := by
  have hlift : biproduct.lift (fun i => sigProj X V h R n i)
      = ∑ j, sigProj X V h R n j
          ≫ biproduct.ι (fun i => (sChain R (TopCat.of (V i))).X n) j :=
    biproduct.lift_eq (g := fun i => sigProj X V h R n i)
  have hldesc : biproduct.lift (fun i => sigProj X V h R n i)
      ≫ biproduct.desc (fun i => (sChainMap R (incl (V i))).f n)
      = ∑ j, sigProj X V h R n j ≫ (sChainMap R (incl (V j))).f n :=
    biproduct.lift_desc (g := fun i => sigProj X V h R n i)
      (h := fun i => (sChainMap R (incl (V i))).f n)
  refine IsIso.mk ⟨biproduct.lift (fun i => sigProj X V h R n i), ?_, ?_⟩
  · apply biproduct.hom_ext'
    intro i
    rw [← Category.assoc, biproduct.ι_desc, Category.comp_id, hlift, Preadditive.comp_sum]
    have hterm : ∀ j, (sChainMap R (incl (V i))).f n ≫ sigProj X V h R n j
        ≫ biproduct.ι (fun i => (sChain R (TopCat.of (V i))).X n) j
        = if j = i then biproduct.ι (fun i => (sChain R (TopCat.of (V i))).X n) i else 0 := by
      intro j
      by_cases hij : j = i
      · subst hij
        rw [← Category.assoc, sigProj_comp_incl X V h R n j, Category.id_comp,
          ite_eq_left rfl]
      · have hz : (sChainMap R (incl (V i))).f n ≫ sigProj X V h R n j = 0 :=
          sigProj_comp_incl_zero (X := X) (V := V) (h := h) (R := R) (n := n)
            (i := i) (j := j) (fun hji => hij hji.symm)
        rw [← Category.assoc, hz, zero_comp, ite_eq_right hij]
    rw [Finset.sum_congr rfl fun j _ => hterm j,
      Finset.sum_ite_eq' Finset.univ i
        fun _ => biproduct.ι (fun i => (sChain R (TopCat.of (V i))).X n) i]
    simp
  · rw [hldesc, sum_sigProj_comp_incl X V h R n]

/-- **The chain level splitting.**  The singular chain complex of `X` is the direct sum of the
singular chain complexes of the members of a finite disjoint open cover. -/
theorem sChain_split_sigmaOpenCover {ι : Type} [Fintype ι] (X : TopCat) (V : ι → Set X)
    (h : SigmaOpenCover X V) (R : ModuleCat ℤ)
    [HasBiproduct (fun i => sChain R (TopCat.of (V i)))] :
    IsIso (biproduct.desc fun i => sChainMap R (incl (V i))) := by
  have hcomp : ∀ n, IsIso ((biproduct.desc (fun i => sChainMap R (incl (V i)))).f n) := by
    intro n
    have hPres : PreservesBiproduct (fun i => sChain R (TopCat.of (V i)))
        (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n) :=
      preservesBiproduct_of_preservesCoproduct _
    haveI := hPres
    haveI hI : IsIso (biproduct.desc fun i => (sChainMap R (incl (V i))).f n) :=
      isIso_biproduct_desc_sigmaOpenCover X V h R n
    have hδ : ((HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapBiproduct
          (fun i => sChain R (TopCat.of (V i)))).inv
        ≫ (biproduct.desc (fun i => sChainMap R (incl (V i)))).f n
        = biproduct.desc (fun i => (sChainMap R (incl (V i))).f n) :=
      biproduct.mapBiproduct_inv_map_desc
        (F := HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)
        (f := fun i => sChain R (TopCat.of (V i)))
        (g := fun i => sChainMap R (incl (V i)))
    exact IsIso.of_isIso_fac_left hδ
  haveI (n : ℕ) : IsIso ((biproduct.desc (fun i => sChainMap R (incl (V i)))).f n) := hcomp n
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **Splitting the singular chains of a space over a finite disjoint open cover.** -/
theorem sigmaOpenCoverChainSplit {ι : Type} [Fintype ι] (X : TopCat)
    (V : ι → Set X) (hopen : ∀ i, IsOpen (V i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j)) (hcov : ∀ x : X, ∃ i, x ∈ V i)
    (R : ModuleCat ℤ)
    [HasBiproduct (fun i => singChain R (TopCat.of (V i)))] :
    IsIso (biproduct.desc (fun i => singChainMap R (incl (V i)))) := by
  haveI : HasBiproduct (fun i => sChain R (TopCat.of (V i))) :=
    ‹HasBiproduct (fun i => singChain R (TopCat.of (V i)))›
  change IsIso (biproduct.desc fun i => sChainMap R (incl (V i)))
  exact sChain_split_sigmaOpenCover X V ⟨hopen, hdisj, hcov⟩ R

/-! ## 6. The summand cover of a topological sum, and the main theorem -/

/-- A homeomorphism of topological spaces induces an isomorphism of singular chain complexes. -/
def chainHomeomorphIso (R : ModuleCat ℤ) {α β : Type} [TopologicalSpace α]
    [TopologicalSpace β] (e : α ≃ₜ β) :
    singChain R (TopCat.of α) ≅ singChain R (TopCat.of β) where
  hom := singChainMap R (homeomorphTopCatHom e)
  inv := singChainMap R (homeomorphTopCatInv e)
  hom_inv_id := by rw [← singChainMap_comp, homeomorphTopCatHom_comp_inv, singChainMap_id]
  inv_hom_id := by rw [← singChainMap_comp, homeomorphTopCatInv_comp_hom, singChainMap_id]

/-- The `i`-th summand of the topological sum `Σ i, X i`, as a set. -/
abbrev sigmaPiece {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)] (i : ι) :
    Set (Σ i, X i) :=
  Set.range (@Sigma.mk ι X i)

/-- The `i`-th summand of a topological sum is homeomorphic to `X i`. -/
def sigmaPieceHomeomorph {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)] (i : ι) :
    X i ≃ₜ sigmaPiece X i :=
  (Topology.IsEmbedding.sigmaMk (σ := X) (i := i)).toHomeomorph

theorem isOpen_sigmaPiece {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)] (i : ι) :
    IsOpen (sigmaPiece X i) :=
  isOpen_range_sigmaMk (σ := X)

theorem disjoint_sigmaPiece {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)]
    {i j : ι} (hij : i ≠ j) : Disjoint (sigmaPiece X i) (sigmaPiece X j) := by
  rw [Set.disjoint_left]
  rintro a ⟨x, rfl⟩ ⟨y, hy⟩
  exact hij (Sigma.ext_iff.mp hy).1.symm

theorem exists_mem_sigmaPiece {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)] :
    ∀ x : (Σ i, X i), ∃ i, x ∈ sigmaPiece X i :=
  fun x => ⟨x.1, x.2, rfl⟩

/-- **Splitting the chains of a space over a finite disjoint open cover**, isomorphism form:
the singular chain complex of `X` is the direct sum of the singular chain complexes of the
members of a finite family of pairwise disjoint open sets covering `X`. -/
theorem sigmaOpenCoverChainIso {ι : Type} [Fintype ι] (X : TopCat) (V : ι → Set X)
    (hopen : ∀ i, IsOpen (V i)) (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (hcov : ∀ x : X, ∃ i, x ∈ V i) (R : ModuleCat ℤ)
    [HasBiproduct (fun i => singChain R (TopCat.of (V i)))] :
    Nonempty (biproduct (fun i => singChain R (TopCat.of (V i))) ≅ singChain R X) := by
  haveI := sigmaOpenCoverChainSplit X V hopen hdisj hcov R
  exact ⟨asIso (biproduct.desc fun i => singChainMap R (incl (V i)))⟩

open CategoryTheory CategoryTheory.Limits in
/-- **The integral homology of a finite disjoint union is the direct sum of the pieces.**

For a finite family `X : ι → Type` of topological spaces, the space `Σ i, X i` (with the sum
topology, i.e. the coproduct of the `X i` in `TopCat`) has
`H_k(Σ i, X i) ≅ ⨁ i, H_k(X i)`.

The binary case is `Work.Homology.SingHomologyCoproduct` (for `α ⊕ β`), and the clopen splitting
`Work.Homology.SingHomologyClopen` (`H_k X ≅ H_k A ⊞ H_k Aᶜ` for `A` clopen) is the tool for the
induction — each summand of a *finite* sum is clopen.  The homeomorphisms are those of
`Work.Homology.SingHomologyHomeomorph`. -/
theorem intHomology_sigma {ι : Type} [Fintype ι] (k : ℕ) (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] :
    Nonempty (LeanEval.Topology.intHomology k (TopCat.of (Σ i, X i)) ≅
      CategoryTheory.Limits.biproduct
        (fun i => LeanEval.Topology.intHomology k (TopCat.of (X i)))) := by
  classical
  -- The summands form a finite family of pairwise disjoint open sets covering the sum, so the
  -- chains of the sum are the direct sum of the chains of the summands.
  obtain ⟨eCover⟩ := sigmaOpenCoverChainIso (X := TopCat.of (Σ i, X i))
    (V := fun i => sigmaPiece X i) (isOpen_sigmaPiece X)
    (fun _ _ hij => disjoint_sigmaPiece X hij) (exists_mem_sigmaPiece X) ZMod
  -- The chains of the `i`-th summand are the chains of `X i`.
  have eChain : singChain ZMod (TopCat.of (Σ i, X i)) ≅
      biproduct (fun i => singChain ZMod (TopCat.of (X i))) :=
    eCover.symm ≪≫
      (biproduct.mapIso (fun i => chainHomeomorphIso ZMod (sigmaPieceHomeomorph X i))).symm
  -- Homology of a finite biproduct of chain complexes is the biproduct of the homologies.
  obtain ⟨hBip⟩ := FiniteBiprodHomology (fun i => singChain ZMod (TopCat.of (X i))) k
  exact ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k).mapIso eChain ≪≫ hBip⟩

end

end Work.HomologyIso
