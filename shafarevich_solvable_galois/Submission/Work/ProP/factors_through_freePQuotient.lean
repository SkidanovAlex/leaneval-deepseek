import Mathlib
import Submission.Work.ProP.Defs
import Submission.Work.ProP.pCentralStep_eq_self_iff
import Submission.Work.Shrinking.map_pCentralSeries_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

/-- The descending `p`-central series of a finite `p`-group reaches the trivial subgroup.

By Nakayama (`Work.ProP.pCentralStep_eq_self_iff`, a finite `p`-group `Q` and a normal subgroup
`N ≤ Q` with `N^p ⁅N, Q⁆ = N` force `N = ⊥`), the series strictly decreases as long as it is
nonzero, so its order (as a natural number) strictly decreases; an infinite strictly decreasing
sequence of natural numbers is impossible. -/
theorem pCentralSeries_eventually_eq_bot_of_isPGroup (p : ℕ) [Fact p.Prime] (Q : Type*)
    [Group Q] [Finite Q] (hQ : IsPGroup p Q) : ∃ N, Work.Shrinking.pCentralSeries p Q N = ⊥ := by
  by_contra h
  push Not at h
  have hstep : ∀ n, Work.Shrinking.pCentralStep p (Work.Shrinking.pCentralSeries p Q n)
      ≠ Work.Shrinking.pCentralSeries p Q n := by
    intro n hne
    have hiff : Work.Shrinking.pCentralStep p (Work.Shrinking.pCentralSeries p Q n)
        = Work.Shrinking.pCentralSeries p Q n ↔ Work.Shrinking.pCentralSeries p Q n = ⊥ :=
      @pCentralStep_eq_self_iff p _ Q _ _ hQ (Work.Shrinking.pCentralSeries p Q n)
        (Work.Shrinking.pCentralSeries_normal p Q n)
    exact h n (hiff.mp hne)
  have hlt : ∀ n, Nat.card (Work.Shrinking.pCentralSeries p Q (n + 1))
      < Nat.card (Work.Shrinking.pCentralSeries p Q n) := by
    intro n
    have hle := Subgroup.card_le_of_le (Work.Shrinking.pCentralSeries_le_succ p Q n)
    have hne : Nat.card (Work.Shrinking.pCentralSeries p Q (n + 1))
        ≠ Nat.card (Work.Shrinking.pCentralSeries p Q n) := by
      intro heq
      have hsub : Work.Shrinking.pCentralSeries p Q (n + 1)
          = Work.Shrinking.pCentralSeries p Q n :=
        Subgroup.eq_of_le_of_card_ge (Work.Shrinking.pCentralSeries_le_succ p Q n)
          (le_of_eq heq.symm)
      exact hstep n hsub
    exact lt_of_le_of_ne hle hne
  have hineq : ∀ k, Nat.card (Work.Shrinking.pCentralSeries p Q k) + k
      ≤ Nat.card (Work.Shrinking.pCentralSeries p Q 0) := by
    intro k
    induction k with
    | zero => simp
    | succ m ih =>
      have := hlt m
      omega
  have hcontra := hineq (Nat.card (Work.Shrinking.pCentralSeries p Q 0) + 1)
  have hpos : 0 < Nat.card (Work.Shrinking.pCentralSeries p Q
      (Nat.card (Work.Shrinking.pCentralSeries p Q 0) + 1)) := Nat.card_pos
  omega

/-- Every homomorphism from the free group on `n` generators to a finite `p`-group kills some
term of the descending `p`-central series of the free group (cofinality of the filtration).

Apply the previous lemma to the image `φ.range`, a finite `p`-group: some term of *its*
`p`-central series is trivial.  The `p`-central series is functorial for surjective maps
(`Work.Shrinking.map_pCentralSeries_surjective`), and `φ.rangeRestrict : F^(n) ↠ φ.range` is
surjective, so the corresponding term of the free group maps to `⊥`, i.e. lies in the kernel. -/
theorem pCentralSeries_le_ker_of_freeGroup {p : ℕ} [Fact p.Prime] (n : ℕ) {P : Type*}
    [Group P] [Finite P] (hP : IsPGroup p P) (φ : FreeGroup (Fin n) →* P) :
    ∃ ν, Work.Shrinking.pCentralSeries p (FreeGroup (Fin n)) ν ≤ φ.ker := by
  obtain ⟨ν, hν⟩ :=
    pCentralSeries_eventually_eq_bot_of_isPGroup p ↥φ.range (hP.to_subgroup φ.range)
  refine ⟨ν, ?_⟩
  have hmap : (Work.Shrinking.pCentralSeries p (FreeGroup (Fin n)) ν).map φ.rangeRestrict
      = Work.Shrinking.pCentralSeries p ↥φ.range ν :=
    Work.Shrinking.map_pCentralSeries_surjective p φ.rangeRestrict
      φ.rangeRestrict_surjective ν
  rw [hν] at hmap
  have hle : Work.Shrinking.pCentralSeries p (FreeGroup (Fin n)) ν
      ≤ φ.rangeRestrict.ker := (Subgroup.map_eq_bot_iff _).mp hmap
  intro x hx
  rw [MonoidHom.mem_ker]
  have h1 : φ.rangeRestrict x = 1 := by
    rw [← MonoidHom.mem_ker]
    exact hle hx
  have h2 := congrArg (fun y : ↥φ.range => (y : P)) h1
  simpa [MonoidHom.coe_rangeRestrict] using h2

/-- Every homomorphism from the free group on `n` generators to a finite `p`-group factors
through one of the finite "generic kernel" quotients `F^(n)/F^(n)(ν)`.

Proof: choose `ν` with `pCentralSeries p (FreeGroup (Fin n)) ν ≤ φ.ker` and factor `φ` through
the quotient map using the universal property of the quotient group (`QuotientGroup.lift`,
`QuotientGroup.lift_mk'`).  If the cofinality result is not importable, prove it locally by
induction on `Nat.card P` through the centre (see `Work/ProP/exists_pCentralSeries_le_ker`). -/
theorem factors_through_freePQuotient {p : ℕ} [Fact p.Prime] (n : ℕ) {P : Type*} [Group P]
    [Finite P] (hP : IsPGroup p P) (φ : FreeGroup (Fin n) →* P) :
    ∃ (ν : ℕ) (f : FreePQuotient p n ν →* P), f.comp (freePQuotientMk p n ν) = φ := by
  obtain ⟨ν, hν⟩ := pCentralSeries_le_ker_of_freeGroup n hP φ
  refine ⟨ν, QuotientGroup.lift _ φ hν, ?_⟩
  refine MonoidHom.ext fun x => ?_
  show QuotientGroup.lift _ φ hν (QuotientGroup.mk' _ x) = φ x
  exact QuotientGroup.lift_mk' _ hν x

end Work.ProP
