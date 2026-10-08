import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.EightIdxDefs

namespace Work.CORE4.N9InfC4Aux

/-- Pure `p`-group counting: if `A ≤ Q` with `|A| = p ^ 2` and `|Q : A| = p` (so `Q` is a finite
`p`-group of order `p ^ 3`), then the centre `Z(Q)` — here `Work.CORE4.centerIn Q`, the image of
`Subgroup.center ↥Q` under `Q.subtype` — has order `p`, provided `Z(Q) < A`. -/
theorem CenterCard {G : Type} [Group G] [Finite G] (p : ℕ) (hp : p.Prime)
    (Q A : Subgroup G) (hAQ : A ≤ Q) (hAcard : Nat.card ↥A = p ^ 2)
    (hrel : A.relIndex Q = p) (hZlt : Work.CORE4.centerIn Q < A) :
    Nat.card ↥(Work.CORE4.centerIn Q) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `Q` has order `p ^ 3`.
  have hAQ' : A ⊓ Q = A := inf_eq_left.mpr hAQ
  have hcardQ : Nat.card ↥Q = p ^ 3 := by
    have h := Subgroup.relIndex_mul_card A Q
    rw [hAQ', hAcard, hrel] at h
    rw [← h]; ring
  -- Hence `Q` is a nontrivial finite `p`-group, so its centre is nontrivial.
  have hQnt : Nontrivial ↥Q := by
    refine (Subgroup.nontrivial_iff_ne_bot Q).mpr ?_
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardQ
    have h2 : 2 ≤ p := hp.two_le
    nlinarith [hcardQ]
  haveI := hQnt
  have hQP : IsPGroup p ↥Q := by
    rw [IsPGroup.iff_card]
    exact ⟨3, hcardQ⟩
  have hZbot : (Subgroup.center ↥Q) ≠ ⊥ := by
    haveI : Group.IsNilpotent ↥Q := hQP.isNilpotent
    exact Group.IsNilpotent.center_ne_bot ↥Q
  -- Translate nontriviality of the centre to `centerIn Q`.
  have hZne : Work.CORE4.centerIn Q ≠ ⊥ := by
    intro hb
    apply hZbot
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ Work.CORE4.centerIn Q := Subgroup.mem_map_of_mem Q.subtype hx
    rw [hb] at hx'
    exact Subtype.ext (Subgroup.mem_bot.mp hx')
  -- `Z(Q) ≤ A`, so `|Z(Q)|` divides `p ^ 2` and is neither `1` nor `p ^ 2`.
  have hZle : Work.CORE4.centerIn Q ≤ A := le_of_lt hZlt
  have hZdiv : Nat.card ↥(Work.CORE4.centerIn Q) ∣ p ^ 2 := by
    rw [← hAcard]; exact Subgroup.card_dvd_of_le hZle
  have hZlt2 : Nat.card ↥(Work.CORE4.centerIn Q) ≠ p ^ 2 := by
    intro h
    refine (ne_of_lt hZlt) (Subgroup.eq_of_le_of_card_ge hZle ?_)
    rw [h, hAcard]
  have hk1 : Nat.card ↥(Work.CORE4.centerIn Q) ≠ 1 := by
    intro h1
    exact hZne (Subgroup.card_eq_one.mp h1)
  rcases (Nat.dvd_prime_pow hp).mp hZdiv with ⟨k, _hk, hkeq⟩
  have hk01 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk01 with rfl | rfl | rfl
  · rw [pow_zero] at hkeq; exact absurd hkeq hk1
  · rwa [pow_one] at hkeq
  · exact absurd hkeq hZlt2

end Work.CORE4.N9InfC4Aux
