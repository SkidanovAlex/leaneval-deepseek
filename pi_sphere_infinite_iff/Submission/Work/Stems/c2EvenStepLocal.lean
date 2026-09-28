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
import Submission.Work.Stems.c2FreeClauses

/-!
# The even step of the free-top `C2` interface, level by level

*(Area STEMS.  `Submission/Work/Stems/c2FreeClauses.lean` defines the level clauses `EvenClause`
and `OddClause`; `c2evenFree_of_c2oddFree.lean` proves the same step for the *uniform* interfaces.)*

`Work.Stems.evenStepLocal` is `Work.Stems.c2evenFree_of_c2oddFree` with the hypothesis localised to
the single odd level `m = 2j-1` that the proof uses: the odd statement enters only through
`OddClause c (2j-1) (N-1)`, evaluated on the loop space `ΩX = Path pt pt`.  This is what lets the
mutual induction be run level by level (`Stems/c2FreeMain.lean`).  The body is the child proof of
`c2evenFree_of_c2oddFree` verbatim, with the single `obtain` that unpacks the (uniform) hypothesis
replaced by the level-local one.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems

noncomputable section

/-- **The even step, level-local.**  The odd clause at level `m = 2j-1` (any top) gives the even
clause at level `j` (any top). -/
theorem evenStepLocal (c : ℕ) (hE3b : Work.Serre.SerreE3b) (j : ℕ) (hj : 1 ≤ j) (m : ℕ)
    (hm : m = 2 * j - 1) (hodd : ∀ M : ℕ, OddClause c m (by omega) M) :
    ∀ N : ℕ, EvenClause c j hj N := by
  subst hm
  intro N X tX pt hX
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
  obtain ⟨hgen, hvan⟩ :=
    hodd (N - 1) (Path pt pt) (Path.refl pt) hLoop
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
