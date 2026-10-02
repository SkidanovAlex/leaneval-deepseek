import Mathlib
import Submission.Work.Stems.Engine.C2FreeTop
import Submission.Work.Stems.Engine.C2EvenRange
import Submission.Work.Serre.Engine
import Submission.Work.Stems.Engine.DualVanishing
import Submission.Work.Serre.serreE0Range
import Submission.Work.Stems.homotopyFibre_evalOne_equiv_loop
import Submission.Work.Serre.ratCoh_ratH_iso_rat
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.RatHurewicz.SimplyConnectedBridge
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.StemsB.isSerreFibration_evalOne
import Submission.Work.StemsB.contractible_pathSpace

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The even step of the free-top `C2` interface, from the odd side

*(Area STEMS.  See `Submission/Work/Stems/C2ODD_PLAN.md` and `Engine/C2FreeTop.lean`.)*

`Work.Stems.Engine.C2evenFree c` (a range model of `K(ℤ,2j)` through `N` is rationally `ℂP^∞`
rescaled by `2j`, through degree `N - c·2j`) follows from `Work.Stems.Engine.C2oddFree c` (a range
model of `K(ℤ,2j-1)` — an **odd** level — is a rational `S^{2j-1}` through `N - c·(2j-1)`) and the
Gysin/periodicity statement `Work.Serre.SerreE3b`:

* the loop space `ΩX = Path pt pt` is a range model of `K(ℤ,2j-1)` through `N-1`
  (`Work.Stems.isEMSpaceUpTo_loop'`), hence rationally a rational sphere through
  `T := (N-1) - c·(2j-1)`;
* the path–loop fibration `ΩX ≃ hofib(evalOne) → PathSpace X pt → X` has rationally acyclic total
  space (it is contractible), so `SerreE3b` gives `⌣e : H^m(X;ℚ) ≅ H^{m+2j}(X;ℚ)` for every
  `m ≤ T - 2j`;
* descending along these periodicity isomorphisms from `H^0(X) ≅ ℚ` (and using the connectivity of
  `X` for degrees `< 2j`) gives the `ℚ[x_{2j}]` structure of `H^*(X;ℚ)` through degree `T`.

`T ≥ N - c·2j`, so the conclusion is at least as strong as `C2evenFree c` asks for.

This is `Work.Stems.c2evenFull` (the *unbounded* even step) with the range model's top carried
along.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems

noncomputable section

/-- **The even step of the free-top `C2` interface, from the odd side.** -/
theorem c2evenFree_of_c2oddFree (c : ℕ) (hE3b : Work.Serre.SerreE3b)
    (h : Work.Stems.Engine.C2oddFree c) : Work.Stems.Engine.C2evenFree c := by
  intro j hj N X tX pt hX
  letI : TopologicalSpace X := tX
  have h2j : 2 ≤ 2 * j := by omega
  set T : ℕ := (N - 1) - c * (2 * j - 1) with hT
  have hpi0 : Subsingleton (HomotopyGroup (Fin 0) X pt) := hX.2 0 (by omega) (Or.inl (by omega))
  have hpi1 : Subsingleton (HomotopyGroup (Fin 1) X pt) := hX.2 1 (by omega) (Or.inl (by omega))
  haveI hpcX : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero pt hpi0
  have hscX : SimplyConnectedSpace X :=
    Work.RatHurewicz.simplyConnectedSpace_of_subsingleton pt hpi0 hpi1
  -- the loop space
  have hLoop : Work.Serre.IsEMSpaceUpTo ℤ (2 * j - 1) (by omega) (N - 1)
      (Path pt pt) (Path.refl pt) :=
    Work.Stems.isEMSpaceUpTo_loop' (A := ℤ) (m := 2 * j) h2j pt hX
  have hodd : Odd (2 * j - 1) := ⟨j - 1, by omega⟩
  obtain ⟨hgen, hvan⟩ :=
    h (2 * j - 1) (by omega) hodd (N - 1) (Path pt pt) (Path.refl pt) hLoop
  -- the fibre of the path–loop fibration
  obtain ⟨heq⟩ := Work.Stems.homotopyFibre_evalOne_equiv_loop X pt
  have hFibIso : ∀ t : ℕ, 0 < t → t ≠ 2 * j - 1 → t ≤ T - 1 →
      IsZero (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre
        (Work.StemsB.evalOne X pt) (Work.RatHurewicz.pathSpaceConst X pt))) t) :=
    fun t ht hne hle =>
      Work.Stems.isZero_ratH_of_homotopyEquiv heq t (hvan t ht (by omega) hne)
  have hFibGen : Nonempty (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre
      (Work.StemsB.evalOne X pt) (Work.RatHurewicz.pathSpaceConst X pt)))
      (2 * j - 1) ≅ ModuleCat.of ℚ ℚ) :=
    Work.Stems.isoRat_of_homotopyEquiv heq (2 * j - 1) hgen
  haveI : ContractibleSpace (Work.StemsB.PathSpace X pt) := Work.StemsB.contractible_pathSpace X pt
  have hacyc : Work.Serre.RatAcyclic (Work.StemsB.PathSpace X pt) :=
    Work.Serre.ratAcyclic_of_contractible (Work.StemsB.PathSpace X pt)
  -- the periodicity `⌣e : H^m(X;ℚ) ≅ H^{m+2j}(X;ℚ)` for `m + 2j ≤ T`
  have hgysin : ∀ m : ℕ, m + 2 * j ≤ T →
      ∃ e : Work.Serre.ratCoh (TopCat.of X) (2 * j - 1 + 1),
        IsIso (ModuleCat.ofHom (Work.Serre.cupWith (TopCat.of X) (2 * j - 1 + 1) e m)) := by
    intro m hm
    exact hE3b (Work.StemsB.PathSpace X pt) X (Work.StemsB.evalOne X pt)
      (Work.RatHurewicz.pathSpaceConst X pt) (2 * j - 1) (T - 1) (by omega)
      (Work.StemsB.isSerreFibration_evalOne X pt) hscX hacyc
      (fun t ht htr hle => hFibIso t ht htr hle) hFibGen m (by omega)
  have hperIso : ∀ m : ℕ, m + 2 * j ≤ T →
      (Work.Serre.ratCoh (TopCat.of X) m ≅ Work.Serre.ratCoh (TopCat.of X) (m + 2 * j)) := by
    intro m hm
    let e := Classical.choose (hgysin m hm)
    have he : IsIso (ModuleCat.ofHom (Work.Serre.cupWith (TopCat.of X) (2 * j - 1 + 1) e m)) :=
      Classical.choose_spec (hgysin m hm)
    haveI := he
    have hdeg : m + (2 * j - 1 + 1) = m + 2 * j := by omega
    exact (asIso (ModuleCat.ofHom (Work.Serre.cupWith (TopCat.of X) (2 * j - 1 + 1) e m))).trans
      (eqToIso (congrArg (Work.Serre.ratCoh (TopCat.of X)) hdeg))
  have hperStep : ∀ m : ℕ, m + 2 * j ≤ T → IsZero (Work.Serre.ratCoh (TopCat.of X) m) →
      IsZero (Work.Serre.ratCoh (TopCat.of X) (m + 2 * j)) :=
    fun m hm h => IsZero.of_iso h (hperIso m hm).symm
  -- the arithmetic of the two tops
  have hkey : N - c * (2 * j) ≤ T + 1 := by
    have hc : c * (2 * j - 1) ≤ c * (2 * j) := Nat.mul_le_mul_left c (by omega)
    omega
  -- connectivity of `X`
  have hLow : ∀ d : ℕ, 0 < d → d < 2 * j → IsZero (Work.Serre.ratH (TopCat.of X) d) := by
    intro d hd hd'
    exact Work.Serre.serreE0Range X pt (2 * j - 1) (fun i _ => hX.2 i (by omega) (Or.inl (by omega)))
      d hd (by omega)
  -- the cohomology of `X` is `ℚ[x_{2j}]` through degree `T`
  have hcohZero : ∀ d : ℕ, d ≤ T → (∀ k : ℕ, d ≠ 2 * j * k) →
      IsZero (Work.Serre.ratCoh (TopCat.of X) d) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro hd hne
      rcases Nat.eq_zero_or_pos d with rfl | hpos
      · exact absurd rfl (hne 0)
      · rcases Nat.lt_or_ge d (2 * j) with hsmall | hbig
        · exact Work.Serre.isZero_ratCoh_of_isZero_ratH_dup (hLow d hpos hsmall)
        · have hne' : ∀ k : ℕ, d - 2 * j ≠ 2 * j * k := by
            intro k hk
            exact hne (k + 1) (by rw [Nat.mul_succ, ← hk]; omega)
          have hsum : d - 2 * j + 2 * j = d := by omega
          rw [← hsum]
          exact hperStep (d - 2 * j) (by omega) (ih (d - 2 * j) (by omega) (by omega) hne')
  have hcohGen : ∀ k : ℕ, 2 * j * k ≤ T →
      Nonempty (Work.Serre.ratCoh (TopCat.of X) (2 * j * k) ≅ ModuleCat.of ℚ ℚ) := by
    intro k
    induction k with
    | zero =>
      intro _
      have h0H : Nonempty (Work.Serre.ratH (TopCat.of X) 0 ≅ ModuleCat.of ℚ ℚ) :=
        Work.Serre.ratH_zero_of_pathConnected X
      have h0C := (Work.Serre.ratCoh_ratH_iso_rat (TopCat.of X) 0).mpr h0H
      simpa using h0C
    | succ k ih =>
      intro hk
      have hk' : 2 * j * k ≤ T := le_trans (Nat.mul_le_mul_left (2 * j) (by omega : k ≤ k + 1)) hk
      obtain ⟨e⟩ := ih hk'
      have hsum : 2 * j * (k + 1) = 2 * j * k + 2 * j := by ring
      exact ⟨eqToIso (congrArg (Work.Serre.ratCoh (TopCat.of X)) hsum) ≪≫
        (hperIso (2 * j * k) (by omega)).symm ≪≫ e⟩
  refine ⟨fun k hk => ?_, fun d hd hne => ?_⟩
  · have hle : 2 * j * k ≤ T := by omega
    exact (Work.Serre.ratCoh_ratH_iso_rat (TopCat.of X) (2 * j * k)).mp (hcohGen k hle)
  · exact Work.Stems.isZero_ratH_of_isZero_ratCoh (hcohZero d (by omega) hne)

end

end Work.Stems
