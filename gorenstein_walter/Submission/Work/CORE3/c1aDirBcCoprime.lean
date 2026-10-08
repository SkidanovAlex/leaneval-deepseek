import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.DSTR.M110.PiCoreFacts
import Submission.Work.CORE3.exists_ne_one_mem_and_commute_of_prime_dvd_card_of_mem_normalizer

namespace Work.CORE3

open Subgroup

set_option linter.style.haveILetI false

/-- In the subcase `Ĥ = H`, no prime `r` dividing `|F_{3'}(U)|` divides the order of
`B = C_U(S)`.  Bender 1981 §3a: `B` is fixed-point-free on `F_{3'}(U)` (`Case1aBFpfProp`), so
if `r ∣ |B|` there is `1 ≠ b ∈ B` of order `r`; then `b ∈ U` acts by conjugation on the
`3'`-part `F_{3'}(U)` of the Fitting subgroup of `U`, and the fixed point set of this action
contains `1` and has cardinality congruent to `|F_{3'}(U)| ≡ 0` modulo `r` (fixed point
congruence for the `r`-group `⟨b⟩`), hence has at least `r > 1` elements: there is
`1 ≠ c ∈ F_{3'}(U)` commuting with `b`, contradicting the fixed-point-freeness of `B` on
`F_{3'}(U)` (`Case1aBFpfProp`). -/
theorem c1aDirBcCoprime (hBpf : Work.CORE3.Case1aBFpfProp) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G, Work.GW2.Case1 B → B.Hhat = B.H →
      ∀ r : ℕ, Nat.Prime r → r ∣ Nat.card (Work.GW2.fittingPiIn ({3}ᶜ) B.U) →
        ¬ r ∣ Nat.card (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) : Subgroup G) := by
  intro G _instG _finG hFT hCtx B hCase1 hHhat r hr hrdvd hdiv
  haveI : Fact r.Prime := ⟨hr⟩
  -- Cauchy: an element of order `r` in `B = C_U(S)`
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' r hdiv
  have hxmem : (x : G) ∈ B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) := x.2
  have hxU : (x : G) ∈ B.U := (Subgroup.mem_inf.mp hxmem).1
  have hxord' : orderOf ((x : G)) = r := (Subgroup.orderOf_coe x).trans hxord
  have hxne : (x : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxord'
    exact hr.ne_one hxord'.symm
  -- `F_{3'}(U)` is normalized by every element of `B.U`
  have hN : (x : G) ∈
      Subgroup.normalizer ((Work.GW2.fittingPiIn ({3}ᶜ) B.U : Subgroup G) : Set G) :=
    Work.DSTR.M110.le_normalizer_fittingPiIn G ({3}ᶜ) B.U hxU
  -- a nontrivial element of `F_{3'}(U)` commuting with `x`
  obtain ⟨c, hcF, hcne, hccomm⟩ :=
    exists_ne_one_mem_and_commute_of_prime_dvd_card_of_mem_normalizer
      (F := Work.GW2.fittingPiIn ({3}ᶜ) B.U) (b := (x : G)) hr hN hxord' hrdvd
  have hcC : c ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hccomm
  have hbot := hBpf G hFT hCtx B hCase1 hHhat (x : G) hxmem hxne
  have hcbot : c ∈ (⊥ : Subgroup G) := by
    rw [← hbot]
    exact Subgroup.mem_inf.mpr ⟨hcF, hcC⟩
  exact hcne (Subgroup.mem_bot.mp hcbot)

end Work.CORE3
