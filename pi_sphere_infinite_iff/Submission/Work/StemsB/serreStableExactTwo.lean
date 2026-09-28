import Mathlib
import Submission.Work.Serre.SPC.Assembly
import Submission.Work.Serre.SPC.towerComparison
import Submission.Work.Serre.SPC.cellStepStrong
import Submission.Work.Serre.SPC.fibreTransport
import Submission.Work.Serre.ZeroCase.Basic
import Submission.Work.Serre.ZeroCase.Bridge
import Submission.Work.StemsB.SerreExact
import Submission.Work.StemsB.Fibrations

set_option synthInstance.maxHeartbeats 400000


/-!
# The Serre exact sequence in the stable range: the **corrected** hypothesis `2 ≤ b`

## Why the workspace's statement needs this correction

`Work.Serre.SerreStableExact` / `Work.Serre.SerreExactRangeCorrected`
(`Submission/Work/Serre/StableExact.lean`) carry the hypothesis `1 ≤ b`, i.e. they only ask the base
`B` to be path connected (their `b = 1` case is *not* assumed simply connected).  That case is
**false**:

> **Counterexample.**  Let `B = S¹`, `E = ℝ` and `p : ℝ → S¹` the universal cover (`e₀ = 0`,
> `b₀ = p 0`), and take `b = 1`, `f = 2`.  The hypotheses of the (corrected) statement hold: `p` is
> a Serre fibration (coverings are even Hurewicz fibrations), `π₀(S¹, b₀)` is trivial, and the fibre
> `p ⁻¹{b₀} = ℤ` is discrete, so `π_i(fibre, e₀) = 0` for every `i ≥ 1` (and `π₀` of a point is
> trivial), hence `∀ i < 2, Subsingleton (π_i(fibre,e₀))`.  The conclusion would be that
> `H_i(ℝ, ℤ) → H_i(S¹, {b₀})` is an isomorphism for `i < 3`; take `i = 1`.  From the long exact
> sequences of the pairs (both total spaces being contractible, `ℤ` discrete, `{b₀}` a point)
> `H_1(ℝ,ℤ) ≅ ker(⊕_{k∈ℤ} ℤ → ℤ)`, the kernel of the augmentation `Σ n_k [k] ↦ Σ n_k`, which is a
> **free abelian group of infinite rank**, while `H_1(S¹,{b₀}) ≅ ℤ`: the comparison map is
> surjective (`[k] - [0] ↦ k·generator`) but far from injective.  So the statement fails at `b = 1`,
> `f ≥ 1`.  (The case `f = 0` is fine: it is `Work.Serre.serreComparison_zero`, which only needs
> `1 ≤ b`.)

The mathematical reason: the classical Serre comparison is a statement about homology with **local
coefficients** `H_*(F)` over `B`; it reduces to ordinary homology only when the local system is
trivial, i.e. when the base is **simply connected** (`2 ≤ b`) — which is the hypothesis every
application actually uses.

## What this file provides

* `Work.StemsB.SerreStableExactTwo` and its proof `Work.StemsB.serreStableExactTwo` — the same
  statement as `Work.Serre.SerreStableExact` with `1 ≤ b` replaced by `2 ≤ b`;
* `Work.StemsB.SerreExactRangeCorrectedTwo` and `Work.StemsB.serreExactRangeCorrectedTwo` — the
  Hurewicz-fibration form, which is what this area's contract
  (`Submission/Work/StemsB/contractInputs.lean`) and area RATHUREWICZ's chain cite.

The proofs are the `2 ≤ b` branch of `Work.Serre.serrePairComparison` (`Submission/Work/Serre/
serrePairComparison.lean`) — the cell-attachment comparison over the CW model
`Work.Serre.CWModel.towerA`, with the clean inputs
`Work.Serre.SPC.towerComparison`, `Work.Serre.SPC.cellStepStrong`,
`Work.Serre.SPC.fibreTransport` and `Work.Serre.SPC.towerA_piMapN_bijective` — together with the
`f = 0` case `Work.Serre.serreComparison_zero`.  No `b = 1` model (`Work.Serre.ZeroCase.b1Comparison`,
`Work.Serre.SPC.b1Comparison`) is used, and neither is anything `sorry`-dependent.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.StemsB

noncomputable section

/-- **The `2 ≤ b` comparison**: for a Serre fibration over a **simply connected** base `B`
(`2 ≤ b`), the map of pairs `(E, p⁻¹b₀) → (B, {b₀})` is an isomorphism on integral homology in
degrees `< b + f` and an epimorphism in degree `b + f`. -/
theorem serrePairComparisonTwo {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B) (e₀ : E) (he₀ : p e₀ = b₀)
    (b f : ℕ) (hb2 : 2 ≤ b)
    (hconn : ∀ i < b, Subsingleton (HomotopyGroup (Fin i) B b₀))
    (hfib0 : Subsingleton (HomotopyGroup (Fin 0) (Work.StemsB.fibre p b₀) ⟨e₀, he₀⟩))
    (hfib : ∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p b₀))).homology j)) :
    (∀ i : ℕ, i < b + f → CategoryTheory.IsIso
        (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) i)) ∧
      Function.Surjective
        (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) (b + f)).hom := by
  classical
  have hB : PathConnectedSpace B :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero b₀ (hconn 0 (by omega))
  set K : ℕ := (b + f + 1) + 2 with hK
  set s := Work.Serre.CWModel.towerA B b₀ b hb2 hconn K with hs
  exact Work.Serre.SPC.serrePairComparison_of p hp b₀ s.g s.y₀ s.gbase b f s.conn hB
    (fun i hi x =>
      Work.Serre.SPC.towerA_piMapN_bijective b₀ b hb2 hconn (b + f + 1) i hi x)
    (Work.Serre.SPC.towerComparison p hp b₀ e₀ he₀ b f hb2 hconn hfib0 hfib
      Work.Serre.SPC.cellStepStrong Work.Serre.SPC.fibreTransport K)

/-- **K5 with the correct hypothesis**: `Work.Serre.SerreStableExact` with `1 ≤ b` replaced by
`2 ≤ b` (see the module docstring for the counterexample to the `b = 1` case). -/
def SerreStableExactTwo : Prop :=
  ∀ (E : Type) [TopologicalSpace E] (B : Type) [TopologicalSpace B] (p : C(E, B)),
    Work.StemsB.IsSerreFibration p → ∀ (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) (b f : ℕ),
      2 ≤ b →
      (∀ i < b, Subsingleton (HomotopyGroup (Fin i) B b₀)) →
      (∀ i < f, Subsingleton (HomotopyGroup (Fin i) (↥{x : E | p x = b₀}) ⟨e₀, he₀⟩)) →
      ∀ i : ℕ, i < b + f → IsIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) i)

/-- **The corrected Serre exact sequence in the stable range.** -/
theorem serreStableExactTwo : SerreStableExactTwo := by
  intro E _ B _ p hp e₀ b₀ he₀ b f hb2 hconn hfibπ i hi
  rcases Nat.eq_zero_or_pos f with hf0 | hfpos
  · subst hf0
    exact Work.Serre.serreComparison_zero p hp b₀ b (by omega) hconn i (by simpa using hi)
  · have hfib0 : Subsingleton (HomotopyGroup (Fin 0) (Work.StemsB.fibre p b₀) ⟨e₀, he₀⟩) :=
      hfibπ 0 (by omega)
    have hfibH : ∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero
        ((Work.Cohomology.singularChains ℤ
          (TopCat.of (Work.StemsB.fibre p b₀))).homology j) :=
      fun j hj hjl => Work.Serre.isZero_singularChains_homology_of_pi_subsingleton
        (X := Work.StemsB.fibre p b₀) ⟨e₀, he₀⟩ f (fun i hi' => hfibπ i hi') j hj hjl
    exact (serrePairComparisonTwo p hp b₀ e₀ he₀ b f hb2 hconn hfib0 hfibH).1 i hi

/-- The Hurewicz-fibration form of the corrected statement (the shape cited in
`Submission/Work/StemsB/contractInputs.lean` and by area RATHUREWICZ). -/
def SerreExactRangeCorrectedTwo : Prop :=
  ∀ (E : Type) [TopologicalSpace E] (B : Type) [TopologicalSpace B] (p : C(E, B)),
    Work.StemsB.IsHurewiczFibration p → ∀ (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) (b f : ℕ),
      2 ≤ b →
      (∀ i < b, Subsingleton (HomotopyGroup (Fin i) B b₀)) →
      (∀ i < f, Subsingleton (HomotopyGroup (Fin i) (↥{x : E | p x = b₀}) ⟨e₀, he₀⟩)) →
      ∀ i : ℕ, i < b + f → IsIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) i)

/-- **The corrected K5 (`SerreExactRangeCorrected` with `2 ≤ b`).** -/
theorem serreExactRangeCorrectedTwo : SerreExactRangeCorrectedTwo :=
  fun E _ B _ p hp e₀ b₀ he₀ b f hb2 hbconn hfconn i hi =>
    serreStableExactTwo E B p (Work.StemsB.IsHurewiczFibration.isSerreFibration hp)
      e₀ b₀ he₀ b f hb2 hbconn hfconn i hi

#print axioms Work.StemsB.serrePairComparisonTwo
#print axioms Work.StemsB.serreStableExactTwo
#print axioms Work.StemsB.serreExactRangeCorrectedTwo

end

end Work.StemsB
