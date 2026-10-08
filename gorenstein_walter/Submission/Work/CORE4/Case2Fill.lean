import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup

namespace Work.CORE4

/-- §4, p. 225: `F ≠ ⊥`, so `p := (|F|).minFac` is a prime dividing `|F|`, and `F` contains a
subgroup `P` of order `p` (Cauchy in the finite group `F`). -/
theorem Case2Fill :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
      (Nat.card ↥h.D.F).minFac.Prime ∧ (Nat.card ↥h.D.F).minFac ∣ Nat.card ↥h.D.F ∧
      ∃ P : Subgroup G, P ≤ h.D.F ∧ Nat.card ↥P = (Nat.card ↥h.D.F).minFac := by
  intro G _ _ B h
  -- `F ≠ ⊥` by §4 (1)–(5), hence `|F| ≥ 2` and `p = |F|.minFac` is a prime divisor of `|F|`.
  have hFne : h.D.F ≠ ⊥ := Work.GW2.Case2Pre.F_ne B h.D h.pre
  have hlt : 1 < Nat.card ↥h.D.F := (Subgroup.one_lt_card_iff_ne_bot h.D.F).mpr hFne
  have hprime : (Nat.card ↥h.D.F).minFac.Prime := Nat.minFac_prime hlt.ne'
  have hdvd : (Nat.card ↥h.D.F).minFac ∣ Nat.card ↥h.D.F := Nat.minFac_dvd _
  refine ⟨hprime, hdvd, ?_⟩
  -- Cauchy in the finite group `↥F`: an element of order `p`, whose cyclic span is our `P`.
  haveI : Fact (Nat.card ↥h.D.F).minFac.Prime := ⟨hprime⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' ((Nat.card ↥h.D.F).minFac) hdvd
  refine ⟨Subgroup.zpowers (x : G), Subgroup.zpowers_le.mpr x.2, ?_⟩
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]

end Work.CORE4
