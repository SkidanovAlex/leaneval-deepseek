import Mathlib
import Submission.Work.LerayHirsch.LineSum
import Submission.Work.LerayHirsch.Splitting
import Submission.Work.LerayHirsch.SplitsOverProj
import Submission.Work.LerayHirsch.lerayHirsch_of_kunnethCP
import Submission.Work.LerayHirsch.CohMap_projMap_injective_of_LerayHirschFull
import Submission.Work.LerayHirsch.t2Space_projSpace
import Submission.Work.LerayHirsch.WhitneySumSnd
import Submission.Work.LerayHirsch.WhitneySumAssoc
import Submission.Work.Thom.BundleIso_comap_exists
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm
import Submission.Work.Whitney.chernClass_whitneySum_rank_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# The flag bundle: the iterated splitting principle

This module proves the **splitting principle in its sum form**
`Work.LerayHirsch.SplittingPrinciple`: for a complex gluing-data bundle `Z` of rank `m` over a
paracompact Hausdorff base `B`, there is a space `P` over `B` — the **flag bundle** of `Z`,
obtained by iterating the projectivisation of the tautological quotient — with

* `π^* : H^k(B;ℤ) → H^k(P;ℤ)` injective for every `k`, and
* `π^*Z ≅ L 0 ⊕ L 1 ⊕ … ⊕ L (m-1)` for complex **line** bundles `L i` over a single cover of `P`.

This is the iterated form of the splitting principle `Work.LerayHirsch.splitsOverProj_of_paracompact`
(item 3 of the deliverable of this chapter).  The induction is on the rank: over `P(E)` the
tautological sequence splits, `π^*E ≅ ℓ ⊕ Q` with `Q` of rank `m-1`
(`Work.LerayHirsch.splitsOverProj_of_paracompact`), and the induction hypothesis applied to `Q`
gives the flag bundle of `E`; the injectivity of the composite pullback is
`Work.Thom.CohMap_comp` together with `CohMap_projMap_injective_of_LerayHirschFull`.

## The conventions

* the iterated sum is `Work.LerayHirsch.lineSumCore m L` (`Submission/Work/LerayHirsch/LineSum.lean`),
  so the statement needs no dependent recursion over the successive intermediate bases;
* the cover of the flag bundle is written `(ι × Fin m) × ιL`: the pullback `π'^*ℓ` of the
  tautological line bundle lives over `ι × Fin m` and the lines of the induction hypothesis over
  `ιL`; the two are reindexed onto the product cover (`Work.Agree.reindexCore`), which is why the
  *last* summand of `lineSumCore (m) L'` is the tautological one (`Fin.snoc`).

## The two cases that are not the induction step

* rank `0`: `Work.LerayHirsch.splittingPrinciple_rank_zero`;
* rank `1`: handled directly (a line bundle is already a single summand), see the proof of
  `Work.LerayHirsch.splittingPrinciple_of_kunnethCP_aux`.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-! ## The statement -/

/-- **The witness of the splitting principle at a *fixed* space `P`**: a map `π : P → B`, a cover
`ιL` of `P`, and a family `L` of complex line bundles over that cover with `π^*E ≅ lineSumCore m L`
and `π^*` injective on cohomology in every degree. -/
structure FlagWitness {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {m : ℕ}
    (P : Type) [TopologicalSpace P] (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) where
  /-- the map from the flag bundle to the base -/
  π : C(P, B)
  /-- the cover of `P` on which the line bundles are presented -/
  ιL : Type
  /-- the cover is finite -/
  finL : Fintype ιL
  /-- the line bundles -/
  L : Fin m → VectorBundleCore ℂ P (EuclideanSpace ℂ (Fin 1)) ιL
  /-- the pullback along `π` is injective on cohomology in every degree -/
  inj : ∀ k : ℕ, Function.Injective (CohMap π ℤ k).hom
  /-- `π^*E` is the iterated direct sum of the line bundles -/
  iso : Nonempty (BundleIso (bundleComap Z π) (lineSumCore m L))

/-- **The splitting principle (sum form).**  There is a space `P` over `B` (the flag bundle of `E`)
— **paracompact and Hausdorff** whenever `B` is — together with a witness
`Work.LerayHirsch.FlagWitness P Z`: a map `π : P → B` with `π^*` injective on cohomology in every
degree, and an isomorphism of `π^*E` with an explicit iterated direct sum
`Work.LerayHirsch.lineSumCore m L` of complex line bundles over one common cover of `P`.

The paracompactness and Hausdorffness of `P` are *not* redundant: every construction over the flag
bundle (Chern classes of the splitting, the Whitney formula applied there, …) needs them, and they
are free in the induction because `P` is always either `B` or the projectivisation of a bundle over
a paracompact Hausdorff base.

The *tower* form of the same statement is `Work.LerayHirsch.SplittingPrincipleTower`
(`Submission/Work/LerayHirsch/Splitting.lean`). -/
def SplittingPrinciple (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] : Prop :=
  ∃ (P : Type) (tP : TopologicalSpace P) (_ : @ParacompactSpace P tP) (_ : @T2Space P tP),
    Nonempty (@FlagWitness B _ ι _ m P tP Z)

/-! ## Elementary facts about bundle isomorphisms -/

/-- Continuity of a map on an empty space. -/
theorem continuous_of_isEmpty {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [IsEmpty α]
    (f : α → β) : Continuous f := by
  rw [continuous_def]
  intro s _
  have h : f ⁻¹' s = ∅ := by
    ext x
    exact isEmptyElim x
  rw [h]
  exact isOpen_empty

/-- The total space of a bundle over an empty base is empty. -/
theorem isEmpty_totalSpace {B F : Type*} {E : B → Type*} [IsEmpty B] :
    IsEmpty (Bundle.TotalSpace F E) :=
  ⟨fun p => isEmptyElim p.proj⟩

/-- **Any two bundles over an empty base are isomorphic**: the fibrewise maps are vacuous and the
total spaces are empty. -/
theorem nonempty_bundleIso_of_isEmpty_base {P : Type} [TopologicalSpace P] [IsEmpty P]
    {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup F']
    [NormedSpace ℂ F'] {ι ι' : Type} (Z : VectorBundleCore ℂ P F ι)
    (Z' : VectorBundleCore ℂ P F' ι') : Nonempty (BundleIso Z Z') := by
  haveI : IsEmpty Z.TotalSpace := isEmpty_totalSpace
  haveI : IsEmpty Z'.TotalSpace := isEmpty_totalSpace
  exact ⟨{ hom := fun b => isEmptyElim b
           inv := fun b => isEmptyElim b
           left_inv := fun b => isEmptyElim b
           right_inv := fun b => isEmptyElim b
           continuous_hom := continuous_of_isEmpty _
           continuous_inv := continuous_of_isEmpty _ }⟩

/-- The total-space map of the zero fibrewise linear map is continuous. -/
theorem continuous_zero_totalSpaceMap {B : Type} [TopologicalSpace B] {F F' : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup F'] [NormedSpace ℂ F']
    {ι ι' : Type} (Z : VectorBundleCore ℂ B F ι) (Z' : VectorBundleCore ℂ B F' ι') :
    Continuous fun p : Z.TotalSpace =>
      (⟨p.1, (0 : F →L[ℂ] F') p.2⟩ : Z'.TotalSpace) := by
  refine continuous_totalSpaceMap_clm_gen (𝕜 := ℂ) Z Z' (ContinuousMap.id B) (fun _ => 0) ?_
  intro i₁ i₂
  have hfun : (fun b : B => Z'.coordChange (Z'.indexAt ((ContinuousMap.id B) b)) i₂
      ((ContinuousMap.id B) b) ∘SL (0 : F →L[ℂ] F') ∘SL Z.coordChange i₁ (Z.indexAt b) b)
      = (fun _ : B => (0 : F →L[ℂ] F')) := by
    funext b
    ext v
    simp
  rw [hfun]
  exact continuousOn_const

/-- **A bundle whose fibres are a subsingleton is isomorphic to the trivial bundle.**  Every
fibrewise linear map is `0`, and the constant fibrewise zero map has continuous induced map. -/
theorem nonempty_bundleIso_trivial_of_subsingleton {B : Type} [TopologicalSpace B] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [Subsingleton F] {ι : Type}
    (Z : VectorBundleCore ℂ B F ι) {ι' : Type} [Inhabited ι'] :
    Nonempty (BundleIso Z (trivialVectorBundleCore ℂ B F ι')) := by
  refine ⟨{ hom := fun _ => 0, inv := fun _ => 0,
            left_inv := fun b _ => by
              haveI : Subsingleton (Z.Fiber b) := ‹Subsingleton F›
              exact Subsingleton.elim _ _
            right_inv := fun b _ => by
              haveI : Subsingleton ((trivialVectorBundleCore ℂ B F ι').Fiber b) := ‹Subsingleton F›
              exact Subsingleton.elim _ _
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · simpa using continuous_zero_totalSpaceMap Z (trivialVectorBundleCore ℂ B F ι')
  · simpa using continuous_zero_totalSpaceMap (trivialVectorBundleCore ℂ B F ι') Z

/-- **Congruence of the iterated sum of line bundles**: isomorphisms of the summands induce an
isomorphism of the sums.  The two families may live over *different* covers `ι` and `ι'`. -/
theorem nonempty_bundleIso_lineSumCore_cover {P : Type} [TopologicalSpace P] {ι ι' : Type} (n : ℕ)
    (L : Fin n → VectorBundleCore ℂ P (EuclideanSpace ℂ (Fin 1)) ι)
    (L' : Fin n → VectorBundleCore ℂ P (EuclideanSpace ℂ (Fin 1)) ι')
    (h : ∀ i, Nonempty (BundleIso (L i) (L' i))) :
    Nonempty (BundleIso (lineSumCore n L) (lineSumCore n L')) := by
  induction n with
  | zero =>
      rw [lineSumCore_zero, lineSumCore_zero]
      exact ⟨BundleIso.refl _⟩
  | succ n ih =>
      rw [lineSumCore_succ, lineSumCore_succ]
      obtain ⟨e₁⟩ := ih (L ∘ Fin.castSucc) (L' ∘ Fin.castSucc) (fun i => h i.castSucc)
      obtain ⟨e₂⟩ := h (Fin.last n)
      obtain ⟨e₃⟩ := nonempty_bundleIso_whitneySum_first (lineSumCore n (L ∘ Fin.castSucc))
        (lineSumCore n (L' ∘ Fin.castSucc)) (L' (Fin.last n)) e₁
      obtain ⟨e₄⟩ := nonempty_bundleIso_whitneySum_snd (lineSumCore n (L ∘ Fin.castSucc))
        (L (Fin.last n)) (L' (Fin.last n)) e₂
      exact ⟨e₄.trans e₃⟩

/-- The special case of `Work.LerayHirsch.nonempty_bundleIso_lineSumCore_cover` in which the two
families live over the same cover. -/
theorem nonempty_bundleIso_lineSumCore {P : Type} [TopologicalSpace P] {ι : Type} (n : ℕ)
    (L L' : Fin n → VectorBundleCore ℂ P (EuclideanSpace ℂ (Fin 1)) ι)
    (h : ∀ i, Nonempty (BundleIso (L i) (L' i))) :
    Nonempty (BundleIso (lineSumCore n L) (lineSumCore n L')) :=
  nonempty_bundleIso_lineSumCore_cover n L L' h

/-! ## The base case of rank zero -/

/-- **The splitting principle in rank `0`**: an arbitrary rank-`0` bundle is already the (empty)
sum of line bundles over the base itself. -/
theorem splittingPrinciple_rank_zero {B : Type} [TopologicalSpace B] [ParacompactSpace B]
    [T2Space B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 0)) ι) : SplittingPrinciple Z := by
  refine ⟨B, inferInstance, inferInstance, inferInstance, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact ContinuousMap.id B
  · exact PUnit
  · exact inferInstance
  · exact Fin.elim0
  · intro k x y hxy
    rw [CohMap_id] at hxy
    simpa using hxy
  · rw [bundleComap_id, lineSumCore_zero]
    exact nonempty_bundleIso_trivial_of_subsingleton Z

/-! ## The induction -/

/-- **The splitting principle, by induction on the rank** (see
`Work.LerayHirsch.splittingPrinciple_of_kunnethCP` for the unconditional form).  The two inputs are
the Leray–Hirsch theorem `hK : Work.LerayHirsch.KunnethCP` (subproject KUNNETH) and the
paracompactness of the projectivisation `hPar` (proved in
`Submission/Work/LerayHirsch/paracompactSpace_projSpace.lean`; it is a hypothesis here only so that
this module does not depend on that one). -/
theorem splittingPrinciple_of_kunnethCP_aux (hK : KunnethCP)
    (hPar : ∀ {m : ℕ} {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
      {ι : Type} [Fintype ι] (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι),
      ParacompactSpace (ProjSpace Z)) (n : ℕ) :
    ∀ {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B] {ι : Type} [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ι), SplittingPrinciple Z := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n'
    · -- rank 0
      intro B _ _ _ ι _ Z
      exact splittingPrinciple_rank_zero Z
    · rcases n' with _ | k
      · -- rank 1
        intro B _htB _hparB _ht2B ι _hfinι Z
        refine ⟨B, inferInstance, inferInstance, inferInstance, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
        · exact ContinuousMap.id B
        · exact ι
        · exact inferInstance
        · exact fun _ => Z
        · intro j x y hxy
          rw [CohMap_id] at hxy
          simpa using hxy
        · rw [bundleComap_id, lineSumCore_succ]
          obtain ⟨e₁⟩ := Work.Whitney.nonempty_bundleIso_whitneySum_comm
            (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 0)) PUnit) Z
          obtain ⟨e₂⟩ := Work.Whitney.nonempty_bundleIso_sumCore_of_subsingleton (𝕜 := ℂ)
            (F₁ := EuclideanSpace ℂ (Fin 1)) (F₂ := EuclideanSpace ℂ (Fin 0))
            (F := EuclideanSpace ℂ (Fin (1 + 0))) (Work.Whitney.sumFibreC 1 0) Z
            (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 0)) PUnit)
          exact ⟨(e₁.trans e₂).symm⟩
      · -- rank k + 2
        intro B _htB _hparB _ht2B ι _hfinι Z
        have hih : ∀ {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
            {ι : Type} [Fintype ι] (Q : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (k + 1))) ι),
            SplittingPrinciple Q := ih (k + 1) (by omega)
        haveI hparZ : ParacompactSpace (ProjSpace Z) := hPar Z
        haveI ht2Z : T2Space (ProjSpace Z) := t2Space_projSpace Z
        obtain ⟨Q, ⟨eQ⟩⟩ := splitsOverProj_of_paracompact Z
        obtain ⟨P, tP, hparP, ht2P, ⟨W⟩⟩ := hih Q
        letI : TopologicalSpace P := tP
        letI : ParacompactSpace P := hparP
        letI : T2Space P := ht2P
        letI : Fintype W.ιL := W.finL
        -- injectivity of the composite pullback
        have hinjπ : ∀ j : ℕ, Function.Injective (CohMap ((projMap Z).comp W.π) ℤ j).hom := by
          intro j x y hxy
          rw [CohMap_comp W.π (projMap Z) ℤ j] at hxy
          simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hxy
          exact CohMap_projMap_injective_of_LerayHirschFull (m := (k + 1) + 1) (by omega) Z
            (lerayHirschFull_of_kunnethCP hK Z) j (W.inj j hxy)
        rcases isEmpty_or_nonempty P with hPempty | hPne
        · -- the flag bundle is the projectivisation of a bundle over an empty space
          haveI : IsEmpty P := hPempty
          refine ⟨P, tP, hparP, ht2P, ⟨(projMap Z).comp W.π, PUnit, inferInstance,
            (fun _ : Fin ((k + 1) + 1) =>
              trivialVectorBundleCore ℂ P (EuclideanSpace ℂ (Fin 1)) PUnit), hinjπ, ?_⟩⟩
          exact nonempty_bundleIso_of_isEmpty_base _ _
        · haveI : Nonempty P := hPne
          -- the two covers of the flag bundle
          have hσ₁ : ∀ p : P, ∃ x : (ι × Fin ((k + 1) + 1)) × W.ιL,
              p ∈ (bundleComap (tautLine Z) W.π).baseSet x.1 := by
            intro p
            refine ⟨((tautLine Z).indexAt (W.π p), (W.L ⟨0, by omega⟩).indexAt p), ?_⟩
            exact (tautLine Z).mem_baseSet_at (W.π p)
          have hσ₂ : ∀ i : Fin (k + 1), ∀ p : P, ∃ x : (ι × Fin ((k + 1) + 1)) × W.ιL,
              p ∈ (W.L i).baseSet x.2 := by
            intro i p
            refine ⟨((Z.indexAt ((projMap Z) (W.π p)), ⟨0, by omega⟩), (W.L i).indexAt p), ?_⟩
            exact (W.L i).mem_baseSet_at p
          let A' : VectorBundleCore ℂ P (EuclideanSpace ℂ (Fin 1))
              ((ι × Fin ((k + 1) + 1)) × W.ιL) :=
            Work.Agree.reindexCore (bundleComap (tautLine Z) W.π)
              (fun x : (ι × Fin ((k + 1) + 1)) × W.ιL => x.1) hσ₁
          let B' : Fin (k + 1) → VectorBundleCore ℂ P (EuclideanSpace ℂ (Fin 1))
              ((ι × Fin ((k + 1) + 1)) × W.ιL) :=
            fun i => Work.Agree.reindexCore (W.L i)
              (fun x : (ι × Fin ((k + 1) + 1)) × W.ιL => x.2) (hσ₂ i)
          have hA'def : A' = Work.Agree.reindexCore (bundleComap (tautLine Z) W.π)
              (fun x : (ι × Fin ((k + 1) + 1)) × W.ιL => x.1) hσ₁ := rfl
          have hB'def : B' = fun i : Fin (k + 1) =>
              Work.Agree.reindexCore (W.L i)
                (fun x : (ι × Fin ((k + 1) + 1)) × W.ιL => x.2) (hσ₂ i) := rfl
          let L' : Fin ((k + 1) + 1) → VectorBundleCore ℂ P (EuclideanSpace ℂ (Fin 1))
              ((ι × Fin ((k + 1) + 1)) × W.ιL) := Fin.snoc B' A'
          have hL'def : L' = Fin.snoc B' A' := rfl
          refine ⟨P, tP, hparP, ht2P, ⟨(projMap Z).comp W.π,
            (ι × Fin ((k + 1) + 1)) × W.ιL, inferInstance, L', hinjπ, ?_⟩⟩
          -- the iterated sum, unfolded
          have hunfold : lineSumCore ((k + 1) + 1) L' =
              Work.Whitney.whitneySum (lineSumCore (k + 1) B') A' := by
            rw [hL'def, lineSumCore_succ]
            simp only [Fin.snoc_comp_castSucc, Fin.snoc_last]
          -- the isomorphism of the summands
          obtain ⟨eVV'⟩ := nonempty_bundleIso_lineSumCore_cover (k + 1) W.L B'
            (fun i => ⟨(Work.Agree.nonempty_bundleIso_reindexCore_self (W.L i)
              (fun x : (ι × Fin ((k + 1) + 1)) × W.ιL => x.2) (hσ₂ i)).some.symm⟩)
          obtain ⟨eXA'⟩ := Work.Agree.nonempty_bundleIso_reindexCore_self
            (bundleComap (tautLine Z) W.π)
            (fun x : (ι × Fin ((k + 1) + 1)) × W.ιL => x.1) hσ₁
          -- reorder and reassemble the two summands
          have hstep : Nonempty (BundleIso
              (Work.Whitney.whitneySum (bundleComap (tautLine Z) W.π)
                (lineSumCore (k + 1) W.L))
              (Work.Whitney.whitneySum (lineSumCore (k + 1) B') A')) :=
            ⟨((Work.Whitney.nonempty_bundleIso_whitneySum_comm (bundleComap (tautLine Z) W.π)
                (lineSumCore (k + 1) W.L)).some.trans
              (((nonempty_bundleIso_whitneySum_first (lineSumCore (k + 1) W.L)
                  (lineSumCore (k + 1) B') (bundleComap (tautLine Z) W.π) eVV').some).trans
                ((nonempty_bundleIso_whitneySum_snd (lineSumCore (k + 1) B')
                  (bundleComap (tautLine Z) W.π) A' eXA'.symm).some)))⟩
          -- pull back the splitting of `Z` over `P(E)` along `π'`
          have hC : Nonempty (BundleIso (bundleComap Z ((projMap Z).comp W.π))
              (Work.Whitney.whitneySum (bundleComap (tautLine Z) W.π)
                (bundleComap Q W.π))) :=
            (bundleComap_comp Z (projMap Z) W.π) ▸
              ((Work.Whitney.whitneySum_bundleComap (tautLine Z) Q W.π) ▸
                (BundleIso_comap_exists (bundleComap Z (projMap Z))
                  (Work.Whitney.whitneySum (tautLine Z) Q) eQ W.π))
          have hD : Nonempty (BundleIso (bundleComap Z ((projMap Z).comp W.π))
              (Work.Whitney.whitneySum (bundleComap (tautLine Z) W.π)
                (lineSumCore (k + 1) W.L))) :=
            ⟨hC.some.trans ((nonempty_bundleIso_whitneySum_snd (bundleComap (tautLine Z) W.π)
              (bundleComap Q W.π) (lineSumCore (k + 1) W.L) W.iso.some).some)⟩
          exact hunfold.symm ▸ ⟨hD.some.trans hstep.some⟩

end

end Work.LerayHirsch
