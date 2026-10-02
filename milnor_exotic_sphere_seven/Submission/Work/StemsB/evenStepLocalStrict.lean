import Mathlib
import Submission.Work.StemsB.gysinStrict
import Submission.Work.Stems.c2EvenStepLocal
import Submission.Work.Stems.c2FreeClauses

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The even step of the free-top `C2` layer, from the **strict** Gysin range

This is the port `Work.Stems.evenStepLocal → Work.StemsB.evenStepLocalStrict` promised by the
docstring of `Submission/Work/StemsB/gysinStrict.lean`: the even step of the free-top `C2` layer,
with the full-range hypothesis `Work.Serre.SerreE3b` replaced by the one-degree-of-slack statement
`Work.StemsB.SerreE3bStrict`.

The only change with respect to `Work.Stems.evenStepLocal` is the bookkeeping of the top degree.
There, `T := (N - 1) - c * (2j - 1)` is the largest degree in which the cohomology of the model is
computed; here we use `T := ((N - 1) - c * (2j - 1)) - 1`, one degree lower, which is exactly what
the strict range `m + r + 1 ≤ N` (rather than `≤ N + 1`) allows.  The degree loss is harmless
because the clause `EvenClause c j hj N` only asks about degrees `< N - c·(2j)`, and by
`Work.StemsB.slack_of_evenStepLocal` (the allowance `c ≥ 1` slack) every such degree is `≤ T`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.StemsB

noncomputable section

theorem evenStepLocalStrict (c : ℕ) (hc : 1 ≤ c) (hE3b : Work.StemsB.SerreE3bStrict) (j : ℕ)
    (hj : 1 ≤ j) (m : ℕ) (hm : m = 2 * j - 1)
    (hodd : ∀ M : ℕ, Work.Stems.OddClause c m (by omega) M) :
    ∀ N : ℕ, Work.Stems.EvenClause c j hj N := by
  subst hm
  intro N X tX pt hX
  letI : TopologicalSpace X := tX
  have h2j : 2 ≤ 2 * j := by omega
  set T : ℕ := ((N - 1) - c * (2 * j - 1)) - 1 with hT
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
  have hFibIso : ∀ t : ℕ, 0 < t → t ≠ 2 * j - 1 → t ≤ T →
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
  -- the periodicity `⌣e : H^m(X;ℚ) ≅ H^{m+2j}(X;ℚ)` for `m + 2j ≤ T` (strict range, top `T`)
  have hgysin : ∀ m : ℕ, m + 2 * j ≤ T →
      ∃ e : Work.Serre.ratCoh (TopCat.of X) (2 * j - 1 + 1),
        IsIso (ModuleCat.ofHom (Work.Serre.cupWith (TopCat.of X) (2 * j - 1 + 1) e m)) := by
    intro m hm
    exact hE3b (Work.StemsB.PathSpace X pt) X (Work.StemsB.evalOne X pt)
      (Work.RatHurewicz.pathSpaceConst X pt) (2 * j - 1) T (by omega)
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
  -- the slack: every degree asked for by the clause is `≤ T`
  have hslack : ∀ d : ℕ, d < N - c * (2 * j) → d ≤ T := by
    intro d hd
    have h1 := slack_of_evenStepLocal c j N d hc hj hd
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
  · exact (Work.Serre.ratCoh_ratH_iso_rat (TopCat.of X) (2 * j * k)).mp
      (hcohGen k (hslack (2 * j * k) hk))
  · exact Work.Stems.isZero_ratH_of_isZero_ratCoh (hcohZero d (hslack d hd) hne)


end

end Work.StemsB

