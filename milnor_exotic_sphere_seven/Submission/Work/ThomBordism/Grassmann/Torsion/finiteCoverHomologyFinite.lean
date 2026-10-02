import Mathlib
import Submission.Work.ThomBordism.Grassmann.Torsion.mvFiniteness
import Submission.Work.ThomBordism.Grassmann.Torsion.mvFinitenessZero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

/-!
# Finite generation of singular homology for a finite open cover with finitely generated
intersections

The main result of this file is `finiteCoverHomologyFinite`: if `X` is covered by *finitely many*
open sets `U i` and every nonempty finite intersection `⋂ i ∈ S, U i` has finitely generated
singular homology in every degree (a single hypothesis `hfin`, for all nonempty `S : Finset ι`), then
`H_n(X; ℤ)` is finitely generated for every `n`.

This generalises `Work.ThomBordism.finiteGoodCoverHomology` (where all the intersections are
assumed contractible) to the case where the intersections are only assumed to have finitely
generated homology.  It is the tool by which finite generation of `H_*(Th γ)` is deduced from the
finitely many chart pieces of a Grassmannian.

## Strategy

The proof is the classical induction on the number of sets of the cover, using the Mayer–Vietoris
long exact sequence as in `finiteGoodCoverHomology`, but with the `map`-finiteness input replaced by
the hypotheses:

* the *subspace* `↥A` is covered by the `m` sets `{x : ↥A | (x : Z) ∈ U i}` and, along this cover,
  every nonempty finite intersection has finitely generated homology: such an intersection is
  homeomorphic (as a subspace of `↥A`) to the corresponding intersection of the `U i` in `Z`
  (`fgf_moduleFinite_subtype_inter` + `fgf_moduleFinite_of_homeomorph`), to which the hypothesis
  applies;
* the *intersection* `A ∩ V` is treated the same way, using the fact that
  `⋂ i ∈ β, (U i ∩ V) = ⋂ i : β ⊕ PUnit, U (Sum.elim i (fun _ => last))`.

The induction statement is phrased with the hypothesis in the "subtype/BiInter" form
`∀ β [Fintype β] (f : β → Fin m), Nonempty β → ...`, which is stable under restricting to
subspaces and under reindexing; the `Finset`-form hypothesis of the assignment is converted into it
at the very end (one `Finset.univ.image` computation) and then transported to `Fin (card ι)`.

## Main results

* `finiteHomology_of_fgFam` — the induction for a cover indexed by `Fin m`;
* `finiteCoverHomologyFinite` — the statement of the assignment, for a general finite index type.
-/

open CategoryTheory Limits

namespace Work.ThomBordism.Grassmann.Torsion

noncomputable section

/-! ## Elementary transport lemmas -/

/-- For `B ⊆ A ⊆ Z`, the subspace `{x : ↥A | (x : Z) ∈ B}` of `↥A` is homeomorphic to `↥B`
(both are the same set of points of `Z`, with the subspace topology). -/
def fgf_homeo_subtype_of_subtype {Z : Type*} [TopologicalSpace Z] {A B : Set Z} (hBA : B ⊆ A) :
    ↥{x : ↥A | (x : Z) ∈ B} ≃ₜ ↥B :=
  { toFun := fun x => ⟨(x : Z), x.2⟩
    invFun := fun y => ⟨⟨(y : Z), hBA y.2⟩, y.2⟩
    left_inv := fun x => by ext; rfl
    right_inv := fun y => by ext; rfl
    continuous_toFun :=
      Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun x => x.2)
    continuous_invFun :=
      Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val (fun y => hBA y.2))
        (fun y => y.2) }

/-- **Finite generation of singular homology is invariant under homeomorphism.**  A homeomorphism
of topological spaces induces an isomorphism of singular chain complexes (functoriality of the
singular chain complex functor), hence an isomorphism of homology. -/
theorem fgf_moduleFinite_of_homeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (k : ℕ)
    (h : Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology k)) :
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology k) := by
  let F : TopCat ⥤ ChainComplex (ModuleCat ℤ) ℕ :=
    (AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)
  have hiso : (Work.Cohomology.singularChains ℤ (TopCat.of X)).homology k ≅
      (Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology k :=
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k).mapIso
      (F.mapIso (TopCat.isoOfHomeo e))
  exact Work.ThomBordism.fgch_moduleFinite_of_iso hiso h

/-- **Finiteness descends to a subspace.**  Let `U : β → Set Z` be a family of subsets of `Z` whose
intersection `B = ⋂ i, U i` is contained in a set `A`.  If `H_k(↥B; ℤ)` is finitely generated, then
so is the homology in degree `k` of the corresponding family `i ↦ {x : ↥A | (x : Z) ∈ U i}` of
subsets of the subspace `↥A`: the two intersections are the same set of points, with the subspace
topology, so the spaces are homeomorphic (`fgf_homeo_subtype_of_subtype`). -/
theorem fgf_moduleFinite_subtype_inter {Z : TopCat} {β : Type} (U : β → Set Z)
    {A : Set Z} (hBA : (⋂ i, U i) ⊆ A) (k : ℕ)
    (h : Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(⋂ i, U i))).homology k)) :
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥(⋂ i, {x : ↥A | (x : Z) ∈ U i}))).homology k) := by
  have hset : (⋂ i, {x : ↥A | (x : Z) ∈ U i}) = {x : ↥A | (x : Z) ∈ ⋂ i, U i} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hset]
  exact fgf_moduleFinite_of_homeomorph (fgf_homeo_subtype_of_subtype hBA).symm k h

/-! ## The induction on the number of sets -/

/-- **The generalised Mayer–Vietoris finiteness theorem.**  If a topological space `Z` is covered by
the members of a finite family `U : Fin m → Set Z` of open sets, and *every* nonempty finite
intersection `⋂ i : β, U (f i)` has finitely generated singular homology in every degree, then
`H_k(Z; ℤ)` is finitely generated for every `k`.

The hypothesis is stated for an arbitrary finite index type `β` (with a `Nonempty` witness); this
"subtype form" is exactly the form stable under passing to a subspace and under reindexing. -/
theorem finiteHomology_of_fgFam : ∀ (m : ℕ) (Z : TopCat) (U : Fin m → Set Z),
    (∀ i, IsOpen (U i)) → (⋃ i, U i) = Set.univ →
    (∀ (β : Type) [Fintype β] (f : β → Fin m), Nonempty β → ∀ k,
      Module.Finite ℤ
        ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(⋂ i : β, U (f i)))).homology k)) →
    ∀ k, Module.Finite ℤ ((Work.Cohomology.singularChains ℤ Z).homology k) := by
  intro m
  induction m with
  | zero =>
    -- the space is empty, so all homology vanishes
    intro Z U _ hcov _ k
    haveI : IsEmpty ↥Z := by
      refine ⟨fun x => ?_⟩
      have hx : x ∈ (⋃ i : Fin 0, U i) := by rw [hcov]; exact Set.mem_univ x
      simpa using hx
    exact Work.ThomBordism.fgch_moduleFinite_of_isZero
      (Work.ThomBordism.fgch_isZero_homology_of_isEmpty Z k)
  | succ m ih =>
    intro Z U hU hcov hf k
    -- split off the last set: `Z = A ∪ V`
    set A : Set Z := ⋃ i : Fin m, U (Fin.castSucc i) with hA
    set V : Set Z := U (Fin.last m) with hV
    have hUeq : (⋃ i : Fin (m + 1), U i) = V ∪ A := by
      ext x
      constructor
      · intro hx
        rw [Set.mem_iUnion] at hx
        obtain ⟨i, hi⟩ := hx
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · exact Or.inr (Set.mem_iUnion.mpr ⟨j, hi⟩)
        · exact Or.inl hi
      · intro hx
        rcases hx with hx | hx
        · exact Set.mem_iUnion.mpr ⟨Fin.last m, hx⟩
        · rw [Set.mem_iUnion] at hx
          obtain ⟨j, hj⟩ := hx
          exact Set.mem_iUnion.mpr ⟨Fin.castSucc j, hj⟩
    have hcovAV : A ∪ V = Set.univ := by
      rw [Set.union_comm, ← hUeq]
      exact hcov
    have hAopen : IsOpen A := by rw [hA]; exact isOpen_iUnion fun i => hU _
    have hVopen : IsOpen V := by rw [hV]; exact hU (Fin.last m)
    -- finite generation on `V` (a single set, so the hypothesis applies directly)
    have hVfin : ∀ j, Module.Finite ℤ
        ((Work.Cohomology.singularChains ℤ (TopCat.of ↥V)).homology j) := by
      intro j
      have h1 := hf PUnit (fun _ : PUnit => Fin.last m) ⟨PUnit.unit⟩ j
      rw [Work.ThomBordism.fgch_iInter_punit (U (Fin.last m))] at h1
      exact h1
    -- finite generation on `A`, which carries the sub-cover `i ↦ U i ∩ A`
    have hAfin : ∀ j, Module.Finite ℤ
        ((Work.Cohomology.singularChains ℤ (TopCat.of ↥A)).homology j) :=
      ih (TopCat.of ↥A) (fun i : Fin m => {x : ↥A | (x : Z) ∈ U (Fin.castSucc i)})
        (fun i => (hU (Fin.castSucc i)).preimage continuous_subtype_val)
        (by
          ext x
          constructor
          · intro _; trivial
          · intro _
            have hx : ((x : ↥A) : Z) ∈ (⋃ i : Fin m, U (Fin.castSucc i)) := by
              rw [← hA]; exact x.2
            rw [Set.mem_iUnion] at hx
            obtain ⟨i, hi⟩ := hx
            exact Set.mem_iUnion.mpr ⟨i, hi⟩)
        (by
          intro β _ f hne j
          obtain ⟨b⟩ := hne
          have hBA : (⋂ i : β, U (Fin.castSucc (f i))) ⊆ A := by
            intro x hx
            rw [hA]
            exact Set.mem_iUnion.mpr ⟨f b, Set.mem_iInter.mp hx b⟩
          exact fgf_moduleFinite_subtype_inter (Z := Z)
            (U := fun i : β => U (Fin.castSucc (f i))) hBA j
            (hf β (fun i => Fin.castSucc (f i)) ⟨b⟩ j))
    -- finite generation on `A ∩ V`, which carries the sub-cover `i ↦ U i ∩ V`
    have hAVfin : ∀ j, Module.Finite ℤ
        ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(A ∩ V))).homology j) :=
      ih (TopCat.of ↥(A ∩ V))
        (fun i : Fin m => {x : ↥(A ∩ V) | (x : Z) ∈ U (Fin.castSucc i) ∩ V})
        (fun i => ((hU (Fin.castSucc i)).inter hVopen).preimage continuous_subtype_val)
        (by
          ext x
          constructor
          · intro _; trivial
          · intro _
            have hx : ((x : ↥(A ∩ V)) : Z) ∈ (⋃ i : Fin m, U (Fin.castSucc i)) := by
              rw [← hA]; exact x.2.1
            rw [Set.mem_iUnion] at hx
            obtain ⟨i, hi⟩ := hx
            exact Set.mem_iUnion.mpr ⟨i, ⟨hi, x.2.2⟩⟩)
        (by
          intro β _ f hne j
          obtain ⟨b⟩ := hne
          have hBA : (⋂ i : β, (U (Fin.castSucc (f i)) ∩ V)) ⊆ A ∩ V := by
            intro x hx
            refine ⟨?_, ?_⟩
            · rw [hA]
              exact Set.mem_iUnion.mpr ⟨f b, (Set.mem_iInter.mp hx b).1⟩
            · exact (Set.mem_iInter.mp hx b).2
          -- the intersection over `β` of the sets `U i ∩ V` is the intersection over `β ⊕ PUnit`
          have hEq : (⋂ i : β ⊕ PUnit, U (Sum.elim (fun i : β => Fin.castSucc (f i))
              (fun _ : PUnit => Fin.last m) i))
              = (⋂ i : β, (U (Fin.castSucc (f i)) ∩ V)) := by
            ext x
            simp only [Set.mem_iInter, Set.mem_inter_iff]
            constructor
            · intro h i
              exact ⟨h (Sum.inl i), h (Sum.inr PUnit.unit)⟩
            · intro h j
              rcases j with i | u
              · exact (h i).1
              · exact (h b).2
          have h1 := hf (β ⊕ PUnit)
            (Sum.elim (fun i : β => Fin.castSucc (f i)) (fun _ : PUnit => Fin.last m))
            ⟨Sum.inl b⟩ j
          rw [hEq] at h1
          exact fgf_moduleFinite_subtype_inter (Z := Z)
            (U := fun i : β => U (Fin.castSucc (f i)) ∩ V) hBA j h1)
    -- Mayer–Vietoris, separately in degree `0` (no `H_{-1}`) and in positive degrees
    rcases k with _ | k
    · exact mvFinitenessZero (X := Z) A V hAopen hVopen hcovAV (hAfin 0) (hVfin 0) (hAVfin 0)
    · exact moduleFinite_homology_of_mv (X := Z) A V hAopen hVopen hcovAV hAfin hVfin hAVfin
        (Nat.succ_le_succ (Nat.zero_le k))

/-! ## The statement of the assignment -/

/-- **A finite open cover whose nonempty finite intersections have finitely generated homology
produces finitely generated homology.**  For a finite open cover `U` of `X` such that the homology
of every nonempty finite intersection `⋂ i ∈ S, U i` is finitely generated in every degree,
`H_n(X; ℤ)` is finitely generated.

This is the "map" version of `finitedGoodCoverHomology`: the intersections need not be contractible,
only finitely generated in homology.  The proof converts the `Finset`-indexed hypothesis into the
subtype form used by `finiteHomology_of_fgFam`, reindexes the cover by `Fin (Fintype.card ι)`, and
applies the induction. -/
theorem finiteCoverHomologyFinite {X : TopCat} {ι : Type} [Fintype ι] (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcov : (⋃ i, U i) = Set.univ)
    (hfin : ∀ (S : Finset ι), S.Nonempty → ∀ n, Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(⋂ i ∈ S, U i))).homology n))
    (n : ℕ) : Module.Finite ℤ ((Work.Cohomology.singularChains ℤ X).homology n) := by
  classical
  -- Step 1: the `Finset`-indexed hypothesis implies the subtype-indexed form
  have hf : ∀ (β : Type) [Fintype β] (f : β → ι), Nonempty β → ∀ k,
      Module.Finite ℤ
        ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(⋂ i : β, U (f i)))).homology k) := by
    intro β _ f _ k
    have hset : (⋂ i : β, U (f i)) = ⋂ j ∈ (Finset.univ.image f : Finset ι), U j := by
      ext x
      simp only [Set.mem_iInter, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨fun h j hj => by obtain ⟨a, rfl⟩ := hj; exact h a,
        fun h i => h (f i) ⟨i, rfl⟩⟩
    rw [hset]
    exact hfin _ (Finset.image_nonempty.mpr Finset.univ_nonempty) k
  -- Step 2: reindex the cover by `Fin (Fintype.card ι)`
  let e := Fintype.equivFin ι
  have hU' : ∀ j : Fin (Fintype.card ι), IsOpen ((fun j => U (e.symm j)) j) := fun j => hU _
  have hcov' : (⋃ j : Fin (Fintype.card ι), U (e.symm j)) = Set.univ := by
    ext x
    constructor
    · intro _; trivial
    · intro _
      have hx : x ∈ (⋃ i, U i) := by rw [hcov]; trivial
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨e i, by simpa using hi⟩
  have hf' : ∀ (β : Type) [Fintype β] (f : β → Fin (Fintype.card ι)), Nonempty β → ∀ k,
      Module.Finite ℤ ((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥(⋂ i : β, (fun j => U (e.symm j)) (f i)))).homology k) :=
    fun β _ f hne k => hf β (fun i => e.symm (f i)) hne k
  -- Step 3: the induction on the number of sets
  exact finiteHomology_of_fgFam (Fintype.card ι) X (fun j => U (e.symm j)) hU' hcov' hf' n

end

end Work.ThomBordism.Grassmann.Torsion
