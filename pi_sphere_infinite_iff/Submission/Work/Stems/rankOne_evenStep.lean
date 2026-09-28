import Mathlib
import Submission.Work.Stems.RankOneClauses
import Submission.Work.Stems.rankOne_hurewicz_rank
import Submission.Work.Stems.c2EvenStepLocal
import Submission.Work.Stems.RankOne.loop_pi_subsingleton
import Submission.Work.Stems.RankOne.pi_one_loop_commutative
import Submission.Work.Stems.RankOne.periodic_ratH_structure

/-!
# The even step of the rank-one level clauses

`Work.Stems.EvenClauseR j N` (the rank-one even clause at level `j`, degree `2j`, top `N`,
`Submission/Work/Stems/RankOneClauses.lean`) is deduced here from the rank-one odd clause
`Work.Stems.OddClauseR (2j-1) M` at the lower level `2j-1` and Serre's Gysin/Euler-class statement
`Work.Serre.SerreE3b`.

The argument is the path--loop fibration `ΩX → PX → X`:

* `ΩX = Path pt pt` inherits the vanishing of the homotopy groups of `X` one degree down
  (`Work.Stems.RankOne.loop_pi_subsingleton`), and its `π₁` is abelian
  (`Work.Stems.RankOne.pi_one_loop_commutative`), so the odd clause applies to it at level `2j-1`
  and top `N-1`; the missing rank-one generator `H_{2j-1}(ΩX;ℚ) ≅ ℚ` is the loop-space Hurewicz
  input `Work.Stems.rankOne_hurewicz_rank`;
* since `PX` is contractible (hence rationally acyclic) and `X` is simply connected, `SerreE3b`
  turns those fibre facts into the periodicity `H^m(X;ℚ) ≅ H^{m+2j}(X;ℚ)` for `m + 2j ≤ N - 2j + 1`,
  i.e. cup product with the Euler class;
* the pure algebraic consequence of the periodicity plus the connectivity of `X` (E0) is
  `Work.Stems.RankOne.periodic_ratH_structure`, which is exactly the conclusion.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems

noncomputable section

theorem rankOne_evenStep (hE3b : Work.Serre.SerreE3b) (j : ℕ) (hj : 1 ≤ j)
    (hodd : ∀ M : ℕ, Work.Stems.OddClauseR (2 * j - 1) M) :
    ∀ N : ℕ, Work.Stems.EvenClauseR j N := by
  intro N h2jN X tX pt hX hgen
  letI : TopologicalSpace X := tX
  have h2j : 2 ≤ 2 * j := by omega
  set T : ℕ := N - 2 * j + 1 with hT
  -- π₀ and π₁ of `X`
  have hpi0 : Subsingleton (HomotopyGroup (Fin 0) X pt) := hX 0 (by omega) (by omega)
  have hpi1 : Subsingleton (HomotopyGroup (Fin 1) X pt) := hX 1 (by omega) (by omega)
  haveI hpcX : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero pt hpi0
  have hscX : SimplyConnectedSpace X :=
    Work.RatHurewicz.simplyConnectedSpace_of_subsingleton pt hpi0 hpi1
  -- the homotopy groups of the loop space
  have hloopPi : ∀ i : ℕ, i ≤ N - 1 → i ≠ 2 * j - 1 →
      Subsingleton (HomotopyGroup (Fin i) (Path pt pt) (Path.refl pt)) :=
    fun i hi hne =>
      Work.Stems.RankOne.loop_pi_subsingleton (X := X) (N := N) (d := 2 * j) pt h2j h2jN hX i hi hne
  -- the rank-one Hurewicz input: `H_{2j-1}(ΩX;ℚ) ≅ ℚ`
  have hgenLoop : Nonempty (Work.Serre.ratH (TopCat.of (Path pt pt)) (2 * j - 1) ≅
      ModuleCat.of ℚ ℚ) := by
    have hconn : ∀ i : ℕ, i < 2 * j → Subsingleton (HomotopyGroup (Fin i) X pt) :=
      fun i hi => hX i (by omega) (by omega)
    haveI : Nonempty (Fin (2 * j)) := ⟨⟨0, by omega⟩⟩
    exact (Work.Stems.rankOne_hurewicz_rank (k := 2 * j) h2j pt hconn hgen).2
  -- the odd clause applied to the loop space
  have hloopVanOdd : ∀ t : ℕ, 2 * j - 1 < t → t ≤ (N - 1) - (2 * j - 1) →
      IsZero (Work.Serre.ratH (TopCat.of (Path pt pt)) t) :=
    hodd (N - 1) (X := Path pt pt) (Path.refl pt)
      (fun _ => Work.Stems.RankOne.pi_one_loop_commutative pt) hloopPi hgenLoop
  -- the fibre of the path--loop fibration
  obtain ⟨heq⟩ := Work.Stems.homotopyFibre_evalOne_equiv_loop X pt
  have hloopVan : ∀ t : ℕ, 0 < t → t ≠ 2 * j - 1 → t ≤ T - 1 →
      IsZero (Work.Serre.ratH (TopCat.of (Path pt pt)) t) := by
    intro t ht hne hle
    rcases Nat.lt_or_ge t (2 * j - 1) with hlt | hge
    · -- below the hole degree: connectivity of the loop space (E0)
      have hE0 := Work.Serre.serreE0Range (Path pt pt) (Path.refl pt) t
        (fun i _ => hloopPi i (by omega) (by omega))
      exact hE0 t ht (by omega)
    · -- above it: the odd clause at level `2j-1`
      exact hloopVanOdd t (by omega) (by omega)
  have hFibIso : ∀ t : ℕ, 0 < t → t ≠ 2 * j - 1 → t ≤ T - 1 → IsZero (Work.Serre.ratH
      (TopCat.of (Work.RatHurewicz.homotopyFibre (Work.StemsB.evalOne X pt)
        (Work.RatHurewicz.pathSpaceConst X pt))) t) :=
    fun t ht hne hle => Work.Stems.isZero_ratH_of_homotopyEquiv heq t (hloopVan t ht hne hle)
  have hFibGen : Nonempty (Work.Serre.ratH
      (TopCat.of (Work.RatHurewicz.homotopyFibre (Work.StemsB.evalOne X pt)
        (Work.RatHurewicz.pathSpaceConst X pt))) (2 * j - 1) ≅ ModuleCat.of ℚ ℚ) :=
    Work.Stems.isoRat_of_homotopyEquiv heq (2 * j - 1) hgenLoop
  -- the path space is contractible, hence rationally acyclic
  haveI : ContractibleSpace (Work.StemsB.PathSpace X pt) := Work.StemsB.contractible_pathSpace X pt
  have hacyc : Work.Serre.RatAcyclic (Work.StemsB.PathSpace X pt) :=
    Work.Serre.ratAcyclic_of_contractible (Work.StemsB.PathSpace X pt)
  -- the Gysin periodicity `⌣e : H^m(X;ℚ) ≅ H^{m+2j}(X;ℚ)` for `m + 2j ≤ T`
  have hgysin : ∀ m : ℕ, m + 2 * j ≤ T →
      ∃ e : Work.Serre.ratCoh (TopCat.of X) (2 * j - 1 + 1),
        IsIso (ModuleCat.ofHom (Work.Serre.cupWith (TopCat.of X) (2 * j - 1 + 1) e m)) := by
    intro m hm
    exact hE3b (Work.StemsB.PathSpace X pt) X (Work.StemsB.evalOne X pt)
      (Work.RatHurewicz.pathSpaceConst X pt) (2 * j - 1) (T - 1) (by omega)
      (Work.StemsB.isSerreFibration_evalOne X pt) hscX hacyc
      (fun t ht htr hle => hFibIso t ht htr hle) hFibGen m (by omega)
  have hperIso : ∀ m : ℕ, m + 2 * j ≤ T →
      Nonempty (Work.Serre.ratCoh (TopCat.of X) m ≅ Work.Serre.ratCoh (TopCat.of X) (m + 2 * j)) := by
    intro m hm
    let e := Classical.choose (hgysin m hm)
    have he : IsIso (ModuleCat.ofHom (Work.Serre.cupWith (TopCat.of X) (2 * j - 1 + 1) e m)) :=
      Classical.choose_spec (hgysin m hm)
    haveI := he
    have hdeg : m + (2 * j - 1 + 1) = m + 2 * j := by omega
    exact ⟨(asIso (ModuleCat.ofHom (Work.Serre.cupWith (TopCat.of X) (2 * j - 1 + 1) e m))).trans
      (eqToIso (congrArg (Work.Serre.ratCoh (TopCat.of X)) hdeg))⟩
  -- connectivity of `X` (E0)
  have hLow : ∀ d : ℕ, 0 < d → d < 2 * j → IsZero (Work.Serre.ratH (TopCat.of X) d) := by
    intro d hd hd'
    exact Work.Serre.serreE0Range X pt (2 * j - 1) (fun i _ => hX i (by omega) (by omega))
      d hd (by omega)
  have h0 : Nonempty (Work.Serre.ratCoh (TopCat.of X) 0 ≅ ModuleCat.of ℚ ℚ) :=
    (Work.Serre.ratCoh_ratH_iso_rat (TopCat.of X) 0).mpr (Work.Serre.ratH_zero_of_pathConnected X)
  obtain ⟨hgenOut, hvanOut⟩ := Work.Stems.RankOne.periodic_ratH_structure (X := X) (d := 2 * j) (T := T)
    (by omega) hLow hperIso h0
  exact ⟨fun k hk => hgenOut k (by omega), fun e he hne => hvanOut e (by omega) hne⟩

end

end Work.Stems
