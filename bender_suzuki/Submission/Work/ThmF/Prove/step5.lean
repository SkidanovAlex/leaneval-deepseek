import Mathlib
import Submission.Work.ThmF.ChV3.AppXI
import Submission.Work.ThmF.ChV3.NearField
import Submission.Work.ThmF.Prove.step4

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.step5` — Peterfalvi II, Ch. V §3, step (5)

Step (5) of the source (p. 248) reads

> **(5)** If `C_Q(P)` is non-abelian then `|C_Q(P)| = 8` and `Q₁ = 1`.

with inputs (2), (4), §1 Cor. of Prop. 2 and App. XI Prop. 2.  App. XI Prop. 2 is recorded as the
named input `ChV3.AppXIProp2`, which *is* exactly the first clause: in the standing context a
non-abelian `C_Q(P)` has order `8`.

The second clause `Q₁ = oddPart Q = ⊥` is then immediate from step (4)'s count
`|Q| = |C_Q(P)|^p` (hypothesis `h4`): once `|C_Q(P)| = 8`, we get `|Q| = 8^|P| = 2^(3|P|)`, a
power of `2`, so `Q` is a `2`-group and its odd part is trivial.  The auxiliary
`oddPart_eq_bot_of_card_eq_two_pow` records that elementary fact.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.Prove

/-- A finite group whose order is a power of `2` has trivial odd part: the generators of
`oddPart Q` are the elements of `Q` of odd order, but (by Lagrange) every element of `Q` has
order dividing `|Q| = 2^k`, hence 2-power order, so odd order forces order `1`. -/
private theorem oddPart_eq_bot_of_card_eq_two_pow {G : Type} [Group G] [Finite G]
    (Q : Subgroup G) {k : ℕ} (hQ : Nat.card Q = 2 ^ k) : Work.ThmF.oddPart Q = ⊥ := by
  rw [← le_bot_iff]
  show Subgroup.closure {x : G | x ∈ Q ∧ Odd (orderOf x)} ≤ ⊥
  rw [Subgroup.closure_le]
  rintro x ⟨hxQ, hxodd⟩
  -- `orderOf x` divides `|Q| = 2 ^ k`, but it is odd
  have hdvd : orderOf x ∣ 2 ^ k := by
    have h1 : orderOf (⟨x, hxQ⟩ : ↥Q) ∣ Nat.card ↥Q := orderOf_dvd_natCard _
    rw [hQ] at h1
    rwa [← Subgroup.orderOf_coe ⟨x, hxQ⟩] at h1
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    ((Nat.coprime_two_left.mpr hxodd).symm).pow_right k
  have hone : orderOf x = 1 := by
    refine Nat.dvd_one.mp (hcop.dvd_of_dvd_mul_right ?_)
    simpa using hdvd
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hone)

theorem step5 (hXI2 : Work.ThmF.ChV3.AppXIProp2) {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G} (hFT : Submission.Blueprint.FeitThompsonProp) (hTh : Submission.Blueprint.ThompsonFrobeniusProp) (hNF : Work.ThmF.ChV3.NearFieldAppXIProp) (hC4 : Submission.Blueprint.ChIIFourProp) (hnil : Group.IsNilpotent ↥Q) (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h4 : Nat.card Q = Nat.card ↥(Work.ThmF.ChV3.CQ Q P) ^ Nat.card P) : ¬ IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P) → Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = 8 ∧ Work.ThmF.oddPart Q = ⊥ := by
  intro hnc
  -- App. XI Prop. 2: a non-abelian `C_Q(P)` has order `8`
  have h8 : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = 8 := hXI2 c hnc
  refine ⟨h8, ?_⟩
  -- step (4): `|Q| = |C_Q(P)|^|P| = 8^|P| = 2^(3|P|)`, a power of `2`
  refine oddPart_eq_bot_of_card_eq_two_pow Q (k := 3 * Nat.card P) ?_
  rw [h4, h8, show (8 : ℕ) = 2 ^ 3 from by norm_num, ← pow_mul]

end Work.ThmF.Prove
