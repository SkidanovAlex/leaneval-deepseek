import Mathlib
import Submission.Work.Stems.Engine.C2Range
import Submission.Work.Stems.Engine.DualVanishing
import Submission.Work.Stems.isEMSpace_loop
import Submission.Work.Stems.homotopyFibre_evalOne_equiv_loop
import Submission.Work.Stems.ratH_isEMSpace_self
import Submission.Work.StemsB.contractible_pathSpace
import Submission.Work.StemsB.isSerreFibration_evalOne
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.RatHurewicz.SimplyConnectedBridge
import Submission.Work.Serre.serreE0Range
import Submission.Work.Serre.gysinCupIsoReduction

/-!
# The even step of the `C2` layer from the **range-model** computation

`Submission/Work/Stems/EM_C2_RANGE_FINDING.md` records that the two range-form `C2` statements
(`Work.Stems.Engine.C2evenRange`, `Work.Stems.Engine.C2oddRange` of `C2Range.lean`) have no
producer *inside* the range-form engine: the even step needs the fibre `ΩL = K(ℤ,2j-1)` known as a
rational sphere, and the odd step's range is `2n-3`, so a mutual induction of the two losses fails.

The fix is to obtain the *odd* statement from a statement that is already a contract of the
workspace: `Work.RatHurewicz.RangeModelRatAcyclic` (`Submission/Work/RatHurewicz/S3Inputs.lean`)
says that a range model of `K(A,k)` through degree `2k-1` has vanishing rational homology above
`k`; for `A = ℤ` and `k` **odd** — where `K(ℤ,k)_ℚ = Λ(x_k)` — this, together with connectivity and
the first-degree Hurewicz theorem, gives exactly

`Work.Stems.Engine.OddSphereRange (fun n => 2 * n)`:  a model of `K(ℤ,n)`, `n` odd, is rationally
`Sⁿ` below degree `2n` (`Submission/Work/Stems/oddSphereRange_of_rangeAcyclic.lean`).

This file proves the **even step** from that input and the Gysin/periodicity statement
`Work.Serre.SerreE3b`, with the *exact* bound `4j - 1` of `C2evenRange`: the path–loop fibration
`ΩL → PL → L` has fibre `ΩL`, a `K(ℤ,2j-1)`-model known as a rational sphere through degree
`2(2j-1)-1 = 4j-3`, so `⌣e : H^m(L) ≅ H^{m+2j}(L)` is an isomorphism for `m ≤ 2j-2`.  Descending
the periodicity from `H^0(L) ≅ ℚ` kills every degree `< 4j-1` that is not divisible by `2j`
(degrees `< 2j` are killed by connectivity), and the field universal coefficient theorem
(`Engine/DualVanishing.lean`) transports the vanishing back to homology.

The resulting chain is `RangeModelRatAcyclic → OddSphereRange → C2evenRange → C2oddRange →
StableStemsTorsion`: it removes the `C2` layer from the list of independent gaps of area STEMS.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems

noncomputable section

/-- **The loop space of a `K(A,m)`-model is a `K(A,m-1)`-model**, for `m ≥ 2` (the index shape used
below; `Work.Stems.isEMSpace_loop` is stated for `k + 1`). -/
theorem isEMSpace_loop' {A : Type} [AddCommGroup A] {m : ℕ} (hm : 2 ≤ m) {X : Type}
    [TopologicalSpace X] (pt : X) (h : Work.Serre.IsEMSpace A m (by omega) X pt) :
    Work.Serre.IsEMSpace A (m - 1) (by omega) (Path pt pt) (Path.refl pt) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.sub_add_cancel (by omega : 1 ≤ m)).symm⟩
  exact Work.Stems.isEMSpace_loop (k := k) (by omega) pt h

end

end Work.Stems

namespace Work.Stems.Engine

noncomputable section

/-- **The even step of the `C2` layer**: a model of `K(ℤ,2j)` has the rational homology of
`ℂP^∞` rescaled by `2j` below degree `4j-1` (the bound of `Work.Stems.Engine.C2evenRange`). -/
theorem c2evenRange_of_oddSphereRange (hOdd : Work.Stems.Engine.OddSphereRange (fun n => 2 * n))
    (hE3b : Work.Serre.SerreE3b) : Work.Stems.Engine.C2evenRange := by
  intro j hj L _ l₀ hL
  -- connectivity and simple connectivity of `L`
  have h0L : Subsingleton (HomotopyGroup (Fin 0) L l₀) := hL.2 0 (by omega)
  have h1L : Subsingleton (HomotopyGroup (Fin 1) L l₀) := hL.2 1 (by omega)
  haveI hpcL : PathConnectedSpace L :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero l₀ h0L
  have hscL : SimplyConnectedSpace L :=
    Work.RatHurewicz.simplyConnectedSpace_of_subsingleton l₀ h0L h1L
  -- `H_d(L;ℚ) = 0` for `0 < d < 2j` (the model is `(2j-1)`-connected)
  have hLow : ∀ d : ℕ, 0 < d → d < 2 * j → IsZero (Work.Serre.ratH (TopCat.of L) d) := by
    intro d hd hd'
    have h := Work.Serre.serreE0Range L l₀ (2 * j - 1) (fun i hi => hL.2 i (by omega))
    exact h d hd (by omega)
  -- the fibre `ΩL = Path l₀ l₀` is a `K(ℤ,2j-1)`-model, known as a rational sphere below `2(2j-1)`
  have hFL : Work.Serre.IsEMSpace ℤ (2 * j - 1) (by omega) (Path l₀ l₀) (Path.refl l₀) :=
    Work.Stems.isEMSpace_loop' (m := 2 * j) (by omega) l₀ hL
  have hsphere : Work.Stems.Engine.RatSphereBelow (Path l₀ l₀) (2 * j - 1) (2 * (2 * j - 1)) :=
    hOdd (2 * j - 1) (by omega) ⟨j - 1, by omega⟩ (Path l₀ l₀) (Path.refl l₀) hFL
  -- transfer to the homotopy fibre of the path–loop fibration `evalOne : PL → L`
  obtain ⟨heq⟩ := Work.Stems.homotopyFibre_evalOne_equiv_loop L l₀
  have hFib : ∀ t : ℕ, 0 < t → t ≠ 2 * j - 1 → t ≤ 2 * (2 * j - 1) - 1 →
      IsZero (Work.Serre.ratH
        (TopCat.of (Work.RatHurewicz.homotopyFibre (Work.StemsB.evalOne L l₀)
          (Work.RatHurewicz.pathSpaceConst L l₀))) t) :=
    fun t ht htr htN =>
      Work.Stems.isZero_ratH_of_homotopyEquiv heq t (hsphere.2 t ht (by omega) htr)
  have hFibGen : Nonempty (Work.Serre.ratH
      (TopCat.of (Work.RatHurewicz.homotopyFibre (Work.StemsB.evalOne L l₀)
        (Work.RatHurewicz.pathSpaceConst L l₀))) (2 * j - 1) ≅ ModuleCat.of ℚ ℚ) :=
    Work.Stems.isoRat_of_homotopyEquiv heq (2 * j - 1) hsphere.1
  haveI : ContractibleSpace (Work.StemsB.PathSpace L l₀) := Work.StemsB.contractible_pathSpace L l₀
  have hacyc : Work.Serre.RatAcyclic (Work.StemsB.PathSpace L l₀) :=
    Work.Serre.ratAcyclic_of_contractible (Work.StemsB.PathSpace L l₀)
  -- the Gysin / periodicity isomorphism of `SerreE3b`
  have hgysin : ∀ m : ℕ, m + (2 * j - 1) + 1 ≤ 2 * (2 * j - 1) →
      ∃ e : Work.Serre.ratCoh (TopCat.of L) (2 * j - 1 + 1),
        IsIso (ModuleCat.ofHom (Work.Serre.cupWith (TopCat.of L) (2 * j - 1 + 1) e m)) := by
    intro m hm
    exact hE3b (Work.StemsB.PathSpace L l₀) L (Work.StemsB.evalOne L l₀)
      (Work.RatHurewicz.pathSpaceConst L l₀) (2 * j - 1) (2 * (2 * j - 1) - 1) (by omega)
      (Work.StemsB.isSerreFibration_evalOne L l₀) hscL hacyc hFib hFibGen m (by omega)
  -- one periodicity step in cohomology
  have hperStep : ∀ m : ℕ, m ≤ 2 * j - 2 → IsZero (Work.Serre.ratCoh (TopCat.of L) m) →
      IsZero (Work.Serre.ratCoh (TopCat.of L) (m + 2 * j)) := by
    intro m hm hzero
    obtain ⟨e, he⟩ := hgysin m (by omega)
    haveI := he
    have hdeg : m + ((2 * j - 1) + 1) = m + 2 * j := by omega
    have hiso : Work.Serre.ratCoh (TopCat.of L) (m + ((2 * j - 1) + 1)) ≅
        Work.Serre.ratCoh (TopCat.of L) (m + 2 * j) :=
      eqToIso (congrArg (Work.Serre.ratCoh (TopCat.of L)) hdeg)
    exact IsZero.of_iso hzero
      ((asIso (ModuleCat.ofHom (Work.Serre.cupWith (TopCat.of L) (2 * j - 1 + 1) e m))).trans
        hiso).symm
  -- descent: the cohomology of `L` vanishes below `4j-1` away from the multiples of `2j`
  have hcoh : ∀ d : ℕ, d < 4 * j - 1 → (∀ k : ℕ, d ≠ 2 * j * k) →
      IsZero (Work.Serre.ratCoh (TopCat.of L) d) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro hd hne
      rcases Nat.eq_zero_or_pos d with rfl | hpos
      · exact absurd rfl (hne 0)
      · rcases Nat.lt_or_ge d (2 * j) with hsmall | hbig
        · exact Work.Serre.isZero_ratCoh_of_isZero_ratH_dup (hLow d hpos hsmall)
        · have hd' : d - 2 * j < 4 * j - 1 := by omega
          have hne' : ∀ k : ℕ, d - 2 * j ≠ 2 * j * k := by
            intro k hk
            exact hne (k + 1) (by rw [Nat.mul_succ, ← hk]; omega)
          have hm' : d - 2 * j ≤ 2 * j - 2 := by omega
          have hsum : (d - 2 * j) + 2 * j = d := by omega
          exact hsum ▸ hperStep (d - 2 * j) hm' (ih (d - 2 * j) (by omega) hd' hne')
  refine ⟨?_, ?_⟩
  · intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simpa using Work.Serre.ratH_zero_of_pathConnected L
    · have hk1 : k = 1 := by
        by_contra hk1
        have h2 : 2 ≤ k := by omega
        have hle : 2 * j * 2 ≤ 2 * j * k := Nat.mul_le_mul_left (2 * j) h2
        omega
      subst hk1
      simpa using Work.Stems.ratH_isEMSpace_self (n := 2 * j) (by omega) l₀ hL
  · intro d hd hne
    exact Work.Stems.isZero_ratH_of_isZero_ratCoh (hcoh d (by omega) hne)

end

end Work.Stems.Engine
