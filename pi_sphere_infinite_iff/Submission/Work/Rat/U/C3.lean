import Mathlib
import Submission.Work.Serre.Models
import Submission.Work.Serre.serreRangeEMVanOne
import Submission.Work.Serre.serreRangeEMVanAll
import Submission.Work.Serre.ratSerrePairAssembly
import Submission.Work.Serre.ratPairInputs
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.Serre.hZeroOfPiZero
import Submission.Work.Serre.loopSpace_isEMSpace
import Submission.Work.Serre.isEMSpace_of_homotopyEquiv
import Submission.Work.Serre.subsingleton_pi0_loopSpace_of_pi1
import Submission.Work.Serre.ratAcyclic_of_finite_covering
import Submission.Work.Rat.U.C3One
import Submission.Work.Serre.cellStepSharp
import Submission.Work.Serre.ratTowerComparison
import Submission.Work.Serre.ratPullbackComparison
import Submission.Work.StemsB.RelChainsR
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.contractible_pathSpace
import Submission.Work.StemsB.isSerreFibration_evalOne

/-!
# C3 for finite coefficients — `Work.Serre.SerreC3Finite`

The target of this file, `Work.Serre.serreC3Finite`, is Serre's theorem in the case of a *finite*
coefficient group: for every finite abelian group `A`, every `n ≥ 1` and every model `X` of
`K(A,n)`, the reduced rational homology of `X` vanishes.

## Structure of the proof

Write `C3Finite n` for the statement at a fixed `n`.  Then

* `C3Finite (n+1)` follows from `C3Finite n` by the **path–loop fibration** of a model of
  `K(A,n+1)`: its total space `Work.StemsB.PathSpace X pt` is contractible
  (`Work.StemsB.contractible_pathSpace`), its fibre at the base point is the loop space
  `Path pt pt` (`Work.StemsB.fibreEvalOneHomeo`), which is a model of `K(A,n)`
  (`Work.Serre.loopSpace_isEMSpace`), hence rationally acyclic by `C3Finite n`.  The statement used
  is `ratAcyclic_of_acyclicFibration`: **a Serre fibration whose total space and whose fibre are
  rationally acyclic over a simply connected base forces the base to be rationally acyclic.**  This
  is blueprint E3(a) in the degenerate case where the fibre is rationally contractible; it is proved
  here from the stable-range Serre pair comparison `Work.Serre.ratSerrePairComparison_of_inputs`
  (the comparison `H_i(E, fibre) ≅ H_i(B, {b₀})` for `i < b + f`, where `f` bounds the *homological*
  acyclicity of the fibre).  In the case at hand the fibre is acyclic in **all** degrees, so the
  comparison is available in **all** degrees.

* The whole family therefore follows from the single case `n = 1`: `C3Finite 1` is the classical
  statement that a finite group has a rationally acyclic classifying space.  It is the one input
  that cannot be obtained from the loop induction, because there the fibre of the relevant
  fibration is *disconnected* and the mapping theorem does not apply.

## The inputs still to be supplied

* `Work.Serre.RatCellStepSharp` and `Work.Serre.RatTowerComparison` — the two analytic inputs of the
  stable-range pair comparison (being proved inside this chapter); they are carried here as
  hypotheses of `ratAcyclic_of_acyclicFibration`, so that this file records exactly what the
  assembly consumes.
* `Work.Serre.serreC3FiniteOne` — the base case `n = 1` (proved in a separate module and imported by
  `serreC3Finite`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre

noncomputable section

/-! ## The fibre is connected and `H₀` behaves -/

/-- **The inclusion of the fibre of a fibration is a homology isomorphism in degree `0`**, when both
`E` and the fibre are path connected.  Both `H₀`'s are one-dimensional and the induced map is the
composite of the two augmentations, both isomorphisms. -/
theorem isIso_relChainsRIncl_zero {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace E] (p : C(E, B)) (b₀ : B)
    [PathConnectedSpace (Work.StemsB.fibre p b₀)] :
    IsIso (HomologicalComplex.homologyMap
      (Work.StemsB.relChainsRIncl ℚ (TopCat.of E) (p ⁻¹' {b₀})) 0) := by
  haveI hFpc : PathConnectedSpace ↥(p ⁻¹' {b₀}) := ‹PathConnectedSpace (Work.StemsB.fibre p b₀)›
  exact hZeroOfPiZero (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(p ⁻¹' {b₀}), E)) (fun x => by
    refine ⟨fun a b _ => ?_, fun y => ⟨Classical.arbitrary _, ?_⟩⟩
    · haveI : Subsingleton (HomotopyGroup (Fin 0) ↥(p ⁻¹' {b₀}) x) :=
        subsingleton_pi0_of_pathConnectedSpace ↥(p ⁻¹' {b₀}) x
      exact Subsingleton.elim a b
    · haveI : Subsingleton (HomotopyGroup (Fin 0) E (Subtype.val x)) :=
        subsingleton_pi0_of_pathConnectedSpace E _
      exact Subsingleton.elim _ _)

/-- **The relative homology of a pair `(E, fibre)` vanishes in positive degrees** when `E` and the
fibre are path connected and rationally acyclic in positive degrees, so that the inclusion of the
fibre is a homology isomorphism in every degree. -/
theorem isZero_relChainsR_homology_of_acyclic {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] [PathConnectedSpace E] (p : C(E, B)) (b₀ : B)
    [PathConnectedSpace (Work.StemsB.fibre p b₀)]
    (hE : ∀ i : ℕ, 0 < i → IsZero (ratH (TopCat.of E) i))
    (hF : ∀ i : ℕ, 0 < i → IsZero (ratH (TopCat.of (Work.StemsB.fibre p b₀)) i)) :
    ∀ i : ℕ, 0 < i →
      IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' {b₀})).homology i) := by
  intro i hi
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  refine Work.StemsB.isZero_relChainsR_homology_succ_of_isIso ℚ (TopCat.of E) (p ⁻¹' {b₀}) k ?_ ?_
  · exact IsZero.isIso (hF (k + 1) (by omega)) (hE (k + 1) (by omega)) _
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      exact isIso_relChainsRIncl_zero p b₀
    · exact IsZero.isIso (hF k hk) (hE k hk) _

/-! ## The mapping theorem in the degenerate case -/

/-- **A Serre fibration with a rationally acyclic total space and a rationally acyclic fibre, over a
simply connected base, has a rationally acyclic base.**  This is blueprint E3(a) in the degenerate
case where the fibre is rationally contractible: the stable-range pair comparison
`H_i(E, p⁻¹{b₀}) ≅ H_i(B, {b₀})` (valid in degrees `< b + f`, and here for *every* `f` because the
fibre is acyclic in all degrees), together with the vanishing of the relative homology of the pair
`(E, p⁻¹{b₀})` (both terms acyclic) and the long exact sequence of the pair `(B, {b₀})`.

The two analytic inputs of the stable-range pair comparison are carried as hypotheses. -/
theorem ratAcyclic_of_acyclicFibration (hcell : RatCellStepSharp) (hpb : RatPullbackComparison)
    (htow : RatTowerComparison)
    {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (hp : Work.StemsB.IsSerreFibration p) (b₀ : B) (b : ℕ) (hb : 2 ≤ b)
    [PathConnectedSpace E] [PathConnectedSpace B]
    [PathConnectedSpace (Work.StemsB.fibre p b₀)]
    (hconn : ∀ i : ℕ, i < b → Subsingleton (HomotopyGroup (Fin i) B b₀))
    (hEac : ∀ i : ℕ, 0 < i → IsZero (ratH (TopCat.of E) i))
    (hFac : ∀ j : ℕ, 0 < j → IsZero (ratH (TopCat.of (Work.StemsB.fibre p b₀)) j)) :
    ∀ i : ℕ, 0 < i → IsZero (ratH (TopCat.of B) i) := by
  have hrel := isZero_relChainsR_homology_of_acyclic p b₀ hEac hFac
  intro i hi
  -- the pair comparison in degree `i`, with the fibre-acyclicity parameter `f = i`
  have hcmp := (ratSerrePairComparison_of_inputs hcell hpb htow p hp b₀ b i hb (by omega)
    (inferInstance) (inferInstance) hconn (inferInstance) (fun j hj _ => hFac j hj)).1 i
    (by omega)
  have hrelB : IsZero
      ((Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B)).homology i) :=
    IsZero.of_iso (hrel i hi) hcmp.some.symm
  -- the long exact sequence of the pair `(B, {b₀})`
  have hS := Work.StemsB.relChainsR_exact₂ ℚ (TopCat.of B) ({b₀} : Set B) i
  refine hS.isZero_X₂ ?_ ?_
  · exact IsZero.eq_zero_of_src
      (Work.Cohomology.homologyContractible_ring ℚ (X := TopCat.of ↥({b₀} : Set B)) i hi) _
  · exact IsZero.eq_zero_of_tgt hrelB _

/-- **`RatAcyclic` from the vanishing of the positive-degree rational homology** (path connectedness
supplies the degree-`0` statement). -/
theorem ratAcyclic_of_isZero_ratH (X : Type) [TopologicalSpace X] [PathConnectedSpace X]
    (h : ∀ i : ℕ, 0 < i → IsZero (ratH (TopCat.of X) i)) : RatAcyclic X := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine isIso_ratHomologyMap_toPoint_zero_of_subsingleton_pi0 X (Classical.arbitrary X) ?_
    exact subsingleton_pi0_of_pathConnectedSpace X _
  · exact IsZero.isIso (h n hn)
      (Work.Cohomology.homologyContractible_ring ℚ (X := TopCat.of PUnit) n hn) _

/-! ## The base case reduces to the existence of finite coverings -/

/-- **The base case `n = 1` follows from the existence of finite coverings with acyclic total
space.**  This is the transfer lemma `Work.Serre.ratAcyclic_of_finite_covering` applied to the
cover of `X`; it isolates what is still needed for every model of `K(A,1)`: a covering with
`|A|` sheets and a rationally acyclic (there: weakly contractible) total space — the universal
cover. -/
theorem ratAcyclic_of_exists_covering {A : Type} [AddCommGroup A] [Fintype A]
    (X : Type) [TopologicalSpace X] (pt : X)
    (hX : IsEMSpace A 1 (by norm_num : 0 < 1) X pt)
    (h : ∃ (Xt : Type) (_ : TopologicalSpace Xt) (q : C(Xt, X)), IsCoveringMap q ∧
      (∀ x : X, Nat.card ↥(q ⁻¹' {x}) = Fintype.card A) ∧ RatAcyclic Xt) :
    RatAcyclic X := by
  obtain ⟨Xt, tXt, q, hq, hcard, hac⟩ := h
  letI : TopologicalSpace Xt := tXt
  haveI : PathConnectedSpace X :=
    pathConnectedSpace_of_subsingleton_pi0 X pt (hX.2 0 (by norm_num))
  exact ratAcyclic_of_finite_covering q hq (Fintype.card A) Fintype.card_pos hcard hac

/-! ## The converse direction: an acyclic base has an acyclic fibre -/

/-- **A Serre fibration with a rationally acyclic total space and a rationally acyclic base, over a
simply connected base, has a rationally acyclic fibre.**  This is the converse of
`ratAcyclic_of_acyclicFibration`; it is proved by *bootstrapping* the stable-range pair comparison:
if the fibre is acyclic below `f`, the comparison identifies `H_{j+1}(E, fibre)` with
`H_{j+1}(B, b₀) = 0` for `j + 1 < b + f`, and the long exact sequence of `(E, fibre)` (with `E`
acyclic) converts this into the vanishing of `H_j(fibre)`.  Iterating grows the range by `b - 1 ≥ 1`
at every step.

Consequence: for the path-loop fibration of a model of `K(A,n+1)` the fibre is a model of `K(A,n)`,
so the statements `SerreC3Finite` at `n` and at `n+1` are *equivalent*. -/
theorem isZero_ratH_fibre_of_acyclicFibration (hcell : RatCellStepSharp)
    (hpb : RatPullbackComparison) (htow : RatTowerComparison)
    {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (hp : Work.StemsB.IsSerreFibration p) (b₀ : B) (b : ℕ) (hb : 2 ≤ b)
    [PathConnectedSpace E] [PathConnectedSpace B]
    [PathConnectedSpace (Work.StemsB.fibre p b₀)]
    (hconn : ∀ i : ℕ, i < b → Subsingleton (HomotopyGroup (Fin i) B b₀))
    (hEac : ∀ i : ℕ, 0 < i → IsZero (ratH (TopCat.of E) i))
    (hBac : ∀ i : ℕ, 0 < i → IsZero (ratH (TopCat.of B) i)) :
    ∀ j : ℕ, 0 < j → IsZero (ratH (TopCat.of (Work.StemsB.fibre p b₀)) j) := by
  -- the fibre-acyclicity range grows by `b - 1` at each application of the machine
  have hmain : ∀ k : ℕ, ∀ j : ℕ, 0 < j → j < 1 + k * (b - 1) →
      IsZero (ratH (TopCat.of (Work.StemsB.fibre p b₀)) j) := by
    intro k
    induction k with
    | zero => intro j hj hjlt; omega
    | succ k ih =>
      intro j hj hjlt
      have hf : 1 ≤ 1 + k * (b - 1) := by omega
      have hfib : ∀ i : ℕ, 0 < i → i < 1 + k * (b - 1) →
          IsZero (ratH (TopCat.of (Work.StemsB.fibre p b₀)) i) := fun i hi hil => ih i hi hil
      -- the range of the comparison: `j + 1 < b + (1 + k * (b-1))`
      have hexp : (k + 1) * (b - 1) = k * (b - 1) + (b - 1) := by rw [Nat.succ_mul]
      have hrange : j + 1 < b + (1 + k * (b - 1)) := by
        rw [hexp] at hjlt
        omega
      -- the pair comparison at parameter `f = 1 + k * (b-1)`
      have hcmp := (ratSerrePairComparison_of_inputs hcell hpb htow p hp b₀ b
        (1 + k * (b - 1)) hb hf (inferInstance) (inferInstance) hconn (inferInstance) hfib).1
        (j + 1) hrange
      -- `H_{j+1}(B, {b₀}) = 0` because `B` is acyclic
      have hBrel : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B)).homology
          (j + 1)) :=
        Work.StemsB.isZero_relChainsR_homology_succ_of_isIso ℚ (TopCat.of B) ({b₀} : Set B) j
          (IsZero.isIso (Work.Cohomology.homologyContractible_ring ℚ
              (X := TopCat.of ↥({b₀} : Set B)) (j + 1) (by omega)) (hBac (j + 1) (by omega)) _)
          (IsZero.isIso (Work.Cohomology.homologyContractible_ring ℚ
              (X := TopCat.of ↥({b₀} : Set B)) j hj) (hBac j hj) _)
      have hrel : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' {b₀})).homology
          (j + 1)) := IsZero.of_iso hBrel hcmp.some
      -- the long exact sequence of `(E, fibre)` turns this into `H_j(fibre) = 0`
      have hS := Work.StemsB.relChainsR_exact₁ ℚ (TopCat.of E) (p ⁻¹' {b₀}) j
      refine hS.isZero_X₂ ?_ ?_
      · exact IsZero.eq_zero_of_src hrel _
      · exact IsZero.eq_zero_of_tgt (hEac j hj) _
  intro j hj
  obtain ⟨k, hk⟩ : ∃ k, j < 1 + k * (b - 1) :=
    ⟨j, by nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ b)]⟩
  exact hmain k j hj hk

/-! ## The loop induction -/

/-- **`C3Finite` at `n+1` from `C3Finite` at `n`** (`n ≥ 1`), via the path–loop fibration of a model
of `K(A,n+1)`. -/
theorem ratAcyclic_of_model_succ (hcell : RatCellStepSharp) (hpb : RatPullbackComparison)
    (htow : RatTowerComparison)
    {A : Type} [AddCommGroup A] [Fintype A] {n : ℕ} (hn : 1 ≤ n)
    (ih : ∀ (X : Type) [TopologicalSpace X] (pt : X),
      IsEMSpace A n (by omega) X pt → RatAcyclic X)
    (X : Type) [TopologicalSpace X] (pt : X)
    (hX : IsEMSpace A (n + 1) (by omega : 0 < n + 1) X pt) : RatAcyclic X := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  haveI : Nonempty (Fin (n + 1)) := ⟨⟨0, by omega⟩⟩
  -- the space is path connected
  have hX0 : Subsingleton (HomotopyGroup (Fin 0) X pt) := hX.2 0 (by omega)
  haveI hXpc : PathConnectedSpace X := pathConnectedSpace_of_subsingleton_pi0 X pt hX0
  -- the path space is contractible, hence path connected and acyclic
  haveI hPc : ContractibleSpace (Work.StemsB.PathSpace X pt) :=
    Work.StemsB.contractible_pathSpace X pt
  haveI hPpc : PathConnectedSpace (Work.StemsB.PathSpace X pt) := inferInstance
  -- the loop space `Path pt pt` is a model of `K(A,n)`, hence acyclic by the induction hypothesis
  haveI : Subsingleton (HomotopyGroup (Fin 1) X pt) := hX.2 1 (by omega)
  haveI hLpc : PathConnectedSpace (Path pt pt) :=
    pathConnectedSpace_of_subsingleton_pi0 (Path pt pt) (Path.refl pt)
      (subsingleton_pi0_loopSpace_of_pi1 pt inferInstance)
  have hmodel : IsEMSpace A n (by omega) (Path pt pt) (Path.refl pt) :=
    loopSpace_isEMSpace (A := A) (n := n) (by omega) hX
  have hloop : RatAcyclic (Path pt pt) := ih (Path pt pt) (Path.refl pt) hmodel
  -- transport along the homeomorphism `fibre (evalOne X pt) pt ≃ Path pt pt`
  have hfib : RatAcyclic (Work.StemsB.fibre (Work.StemsB.evalOne X pt) pt) :=
    ratAcyclic_of_homotopyEquiv (Homeomorph.toHomotopyEquiv (Work.StemsB.fibreEvalOneHomeo X pt))
      hloop
  have hFpc : PathConnectedSpace (Work.StemsB.fibre (Work.StemsB.evalOne X pt) pt) := by
    refine ⟨⟨(Work.StemsB.fibreEvalOneHomeo X pt).symm (Path.refl pt)⟩, fun a b => ?_⟩
    obtain ⟨γ⟩ := hLpc.joined ((Work.StemsB.fibreEvalOneHomeo X pt) a)
      ((Work.StemsB.fibreEvalOneHomeo X pt) b)
    exact ⟨γ.map (Work.StemsB.fibreEvalOneHomeo X pt).symm.continuous⟩
  haveI := hFpc
  have hEac : ∀ i : ℕ, 0 < i → IsZero (ratH (TopCat.of (Work.StemsB.PathSpace X pt)) i) :=
    fun i hi => Work.Cohomology.homologyContractible_ring ℚ
      (X := TopCat.of (Work.StemsB.PathSpace X pt)) i hi
  have hFac : ∀ j : ℕ, 0 < j →
      IsZero (ratH (TopCat.of (Work.StemsB.fibre (Work.StemsB.evalOne X pt) pt)) j) :=
    fun j hj => hfib.isZero_ratH hj
  have hconn : ∀ i : ℕ, i < n + 1 → Subsingleton (HomotopyGroup (Fin i) X pt) :=
    fun i hi => hX.2 i (by omega)
  have hvanish := ratAcyclic_of_acyclicFibration hcell hpb htow (Work.StemsB.evalOne X pt)
    (Work.StemsB.isSerreFibration_evalOne X pt) pt (n + 1) (by omega) hconn hEac hFac
  exact ratAcyclic_of_isZero_ratH X hvanish

/-! ## The assembly -/

/-- **`SerreC3Finite`, given its base case `n = 1`.**  The base case is the statement that every
model of `K(A,1)`, `A` finite abelian, is rationally acyclic; the induction step is
`ratAcyclic_of_model_succ`. -/
theorem serreC3Finite_of_one (hcell : RatCellStepSharp) (hpb : RatPullbackComparison)
    (htow : RatTowerComparison)
    (h1 : ∀ (A : Type) [AddCommGroup A] [Fintype A] (X : Type) [TopologicalSpace X] (pt : X),
      IsEMSpace A 1 (by norm_num : 0 < 1) X pt → RatAcyclic X) :
    ∀ (k : ℕ) (hk : 1 ≤ k) (A : Type) [AddCommGroup A] [Fintype A]
      (X : Type) [TopologicalSpace X] (pt : X),
      IsEMSpace A k (by omega) X pt → RatAcyclic X := by
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ih hk A _ _ X _ pt hX
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · interval_cases k
    exact h1 A X pt hX
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    exact ratAcyclic_of_model_succ hcell hpb htow (by omega : 1 ≤ n)
      (fun Y _ q hY => ih n (by omega) (by omega) A Y q hY) X pt hX

/-- **C3 for finite coefficient groups** — the target of this file.

The proof is `serreC3Finite_of_one`, whose two inputs are

* the base case `n = 1`: `Work.Serre.serreC3FiniteOne` (`Submission/Work/Serre/serreC3FiniteOne.lean`),
  the classical statement that a finite group has a rationally acyclic classifying space, and
* the analytic inputs of the stable-range pair comparison used by
  `ratAcyclic_of_acyclicFibration`: `Work.Serre.RatCellStepSharp` and
  `Work.Serre.RatTowerComparison` (`Work.Serre.RatPullbackComparison` is already proved).

All of them are available (`Work.Serre.cellStepSharp` and `Work.Serre.ratTowerComparison` are
proved inside the SERRE chapter, `Work.Serre.ratPullbackComparison` is proved here,
`Work.Serre.serreC3FiniteOne` is the delegated base case), so the assembly below is unconditional.
-/
theorem serreC3Finite : Work.Serre.SerreC3Finite :=
  fun A _ _ k hk X _ pt hX =>
    serreC3Finite_of_one Work.Serre.cellStepSharp Work.Serre.ratPullbackComparison
      Work.Serre.ratTowerComparison Work.Serre.serreC3FiniteOne k hk A X pt hX

end

end Work.Serre
