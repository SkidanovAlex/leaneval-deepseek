import Mathlib
import Submission.Work.ThmF.ChV3.Chain15

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.step9N6`

Peterfalvi II Ch. V §3, step (9), input **N6** (the arithmetic part of the reduction).

Write `p = |P|` (prime), `q = |C_Q(P)|`, `s = |Σ|` where `Σ = C_W(P)`.  The inputs are
`q + 1 = p^m` (`hcq` composed with `hpf`), step (3)'s output `h3` (every prime `ℓ ∣ |O_{2'}(Q)|`
satisfies `ℓ ≡ 2^i (mod 2^p − 1)` for some `i < p` and `ℓ ≠ p`), and step (8)'s output `h8`
(`s` is prime and `q + 1 ∈ {3^s, 5^s, 9^s}`).

Suppose `p ∣ s`.  Then `Σ ≠ ⊥`, so `h8` applies: `s` is prime, and since `p ∣ s` with both
prime we get `s = p`.  Hence `p^m ∈ {3^p, 5^p, 9^p}`.  Each of the three cases forces
`(p, m) ∈ {(3,3), (5,5), (3,6)}` and therefore
`q ∈ {26, 3124, 728}`; an odd prime (`13`, `11`, `13` respectively) divides `q`, hence divides
`|Q|` (as `C_Q(P) ≤ Q`) and so, by Cauchy, divides `|O_{2'}(Q)|`.  But `13 ≠ 2^i (mod 7)` for all
`i < 3` and `11 ≠ 2^i (mod 31)` for all `i < 5`, contradicting `h3`.
-/

set_option linter.style.haveILetI false

namespace Work.ThmF.Prove

/-- **Arithmetic core of step (9) N6.**  If `p` is prime, `q + 1 = p ^ m` with `m ≥ 1`, and
`p ^ m ∈ {3^p, 5^p, 9^p}`, then `q` is divisible by `13` or by `11`, and in the corresponding case
the prime does not satisfy `ℓ ≡ 2^i (mod 2^p − 1)` for any `i < p`. -/
theorem step9N6_arith {p q m : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (hq1 : q + 1 = p ^ m)
    (hcase : p ^ m = 3 ^ p ∨ p ^ m = 5 ^ p ∨ p ^ m = 9 ^ p) :
    (13 ∣ q ∧ ¬ (∃ i, i < p ∧ 13 ≡ 2 ^ i [MOD 2 ^ p - 1])) ∨
    (11 ∣ q ∧ ¬ (∃ i, i < p ∧ 11 ≡ 2 ^ i [MOD 2 ^ p - 1])) := by
  have hpdvd : p ∣ p ^ m := dvd_pow_self p (by omega)
  rcases hcase with h | h | h
  · -- `p^m = 3^p` forces `p = 3`, `m = 3`, `q = 26`
    have hp3 : p = 3 := by
      have h' : p ∣ 3 ^ p := h ▸ hpdvd
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h')
    subst hp3
    have hm3 : m = 3 := Nat.pow_right_injective (show (2:ℕ) ≤ 3 by norm_num) h
    left
    refine ⟨?_, ?_⟩
    · have : q + 1 = 27 := by rw [hq1, hm3]; norm_num
      omega
    · rintro ⟨i, hi, hc⟩
      interval_cases i <;> norm_num at hc
  · -- `p^m = 5^p` forces `p = 5`, `m = 5`, `q = 3124`
    have hp5 : p = 5 := by
      have h' : p ∣ 5 ^ p := h ▸ hpdvd
      exact (Nat.prime_dvd_prime_iff_eq hp (show Nat.Prime 5 by norm_num)).mp
        (hp.dvd_of_dvd_pow h')
    subst hp5
    have hm5 : m = 5 := Nat.pow_right_injective (show (2:ℕ) ≤ 5 by norm_num) h
    right
    refine ⟨?_, ?_⟩
    · have : q + 1 = 3125 := by rw [hq1, hm5]; norm_num
      omega
    · rintro ⟨i, hi, hc⟩
      interval_cases i <;> norm_num at hc
  · -- `p^m = 9^p` forces `p = 3`, `m = 6`, `q = 728`
    have hp3 : p = 3 := by
      have h9 : p ∣ 9 := hp.dvd_of_dvd_pow (h ▸ hpdvd)
      have h3 : p ∣ 3 := by
        have h9' : p ∣ (3:ℕ) ^ 2 := by simpa using h9
        exact hp.dvd_of_dvd_pow h9'
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    subst hp3
    have hm6 : m = 6 := by
      have h' : (3:ℕ)^m = 3^6 := by rw [h]; norm_num
      exact Nat.pow_right_injective (show (2:ℕ) ≤ 3 by norm_num) h'
    left
    refine ⟨?_, ?_⟩
    · have : q + 1 = 729 := by rw [hq1, hm6]; norm_num
      omega
    · rintro ⟨i, hi, hc⟩
      interval_cases i <;> norm_num at hc

/-- **An odd prime dividing `|C_Q(P)|` divides `|O_{2'}(Q)|`.**  `C_Q(P) ≤ Q`, so `ℓ ∣ |Q|`
(Lagrange); by Cauchy `Q` has an element `x` of order `ℓ`; being odd, `x` lies in `O_{2'}(Q)`,
and `|⟨x⟩| = ℓ`. -/
theorem step9N6_prime_dvd_oddPart {G : Type} [Group G] [Finite G] {Q P : Subgroup G} {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (h : ℓ ∣ Nat.card ↥(Work.ThmF.ChV3.CQ Q P)) :
    ℓ ∣ Nat.card ↥(Work.ThmF.oddPart Q) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hle : Work.ThmF.ChV3.CQ Q P ≤ Q := inf_le_left
  have hdvdQ : ℓ ∣ Nat.card Q := h.trans (Subgroup.card_dvd_of_le hle)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' ℓ hdvdQ
  have hodd : Odd (orderOf ((x : ↥Q) : G)) := by
    rw [Subgroup.orderOf_coe, hx]; exact hℓ.odd_of_ne_two hℓ2
  have hmem : ((x : ↥Q) : G) ∈ Work.ThmF.oddPart Q :=
    Work.ThmF.mem_oddPart_of_odd Q x.2 hodd
  have hzle : Subgroup.zpowers ((x : ↥Q) : G) ≤ Work.ThmF.oddPart Q :=
    Subgroup.zpowers_le.mpr hmem
  have hcard : Nat.card ↥(Subgroup.zpowers ((x : ↥Q) : G)) = ℓ := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  calc ℓ = Nat.card ↥(Subgroup.zpowers ((x : ↥Q) : G)) := hcard.symm
    _ ∣ Nat.card ↥(Work.ThmF.oddPart Q) := Subgroup.card_dvd_of_le hzle

theorem step9N6 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G} {m : ℕ}
    (hp : (Nat.card P).Prime)
    (h3 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card ↥(Work.ThmF.oddPart Q) →
      (∃ i < Nat.card P, ℓ ≡ 2 ^ i [MOD 2 ^ Nat.card P - 1]) ∧ ℓ ≠ Nat.card P)
    (h8 : Work.ThmF.ChV3.Sig H t P ≠ ⊥ → (Nat.card ↥(Work.ThmF.ChV3.Sig H t P)).Prime ∧
      (Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = 3 ^ Nat.card ↥(Work.ThmF.ChV3.Sig H t P) ∨
       Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = 5 ^ Nat.card ↥(Work.ThmF.ChV3.Sig H t P) ∨
       Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = 9 ^ Nat.card ↥(Work.ThmF.ChV3.Sig H t P)))
    (hm : 1 ≤ m) (hpf : Nat.card P = orderOf (s * t))
    (hcq : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = orderOf (s * t) ^ m) :
    ¬ Nat.card P ∣ Nat.card ↥(Work.ThmF.ChV3.Sig H t P) := by
  intro hdiv
  -- `q + 1 = p ^ m` with `p = |P|`, `q = |C_Q(P)|`
  have hq1 : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = (Nat.card P) ^ m := by
    rw [hcq, ← hpf]
  -- `p ∣ s` forces `Σ ≠ ⊥`
  have hsig : Work.ThmF.ChV3.Sig H t P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hdiv
    exact hp.not_dvd_one hdiv
  obtain ⟨hsprime, hcase⟩ := h8 hsig
  -- both `p` and `s` are prime and `p ∣ s`, so `s = p`
  have hsp : Nat.card ↥(Work.ThmF.ChV3.Sig H t P) = Nat.card P :=
    ((Nat.prime_dvd_prime_iff_eq hp hsprime).mp hdiv).symm
  -- hence `p ^ m ∈ {3^p, 5^p, 9^p}`
  have hpm : (Nat.card P) ^ m = 3 ^ Nat.card P ∨ (Nat.card P) ^ m = 5 ^ Nat.card P ∨
      (Nat.card P) ^ m = 9 ^ Nat.card P := by
    rcases hcase with h | h | h
    · left; rw [← hq1, h, hsp]
    · right; left; rw [← hq1, h, hsp]
    · right; right; rw [← hq1, h, hsp]
  rcases step9N6_arith hp hm hq1 hpm with ⟨h13dvd, h13not⟩ | ⟨h11dvd, h11not⟩
  · obtain ⟨⟨i, hi, hcong⟩, _⟩ :=
      h3 13 (by norm_num)
        (step9N6_prime_dvd_oddPart (by norm_num) (by norm_num) h13dvd)
    exact h13not ⟨i, hi, hcong⟩
  · obtain ⟨⟨i, hi, hcong⟩, _⟩ :=
      h3 11 (by norm_num)
        (step9N6_prime_dvd_oddPart (by norm_num) (by norm_num) h11dvd)
    exact h11not ⟨i, hi, hcong⟩

end Work.ThmF.Prove
