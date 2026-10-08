import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The structure of a non-abelian group of order `21`

`21 = 3 · 7`.  A group of order `21` that is not abelian necessarily has the shape
`C₇ ⋊ C₃`: the (unique) Sylow `7`-subgroup `S` is normal, a Sylow `3`-subgroup `X` is a
complement, it intersects the centralizer of `X` trivially, and `⁅X, S⁆ = S`.

The proof is elementary.  Take `S` of order `7` and `X` of order `3` (Sylow's first theorem).
The number of Sylow `7`-subgroups divides the index `3` of `S` and is `≡ 1 mod 7`, hence equals
`1`, so `S` is normal.  Its index is `3`, so `S` and `X` are complementary subgroups
(`|S| · |X| = 21 = |A|`) and in particular `S ⊓ X = ⊥` and `S ⊔ X = ⊤`.

Since `|S| = 7` is prime, any subgroup of `S` is trivial or all of `S`.  If `S` met the
centralizer of `X` non-trivially, or if `⁅X, S⁆ = ⊥`, then `S` and `X` would commute
elementwise; as `A = S ⊔ X` with `S, X` abelian (prime order) and `S` normal, `A` would be
abelian, contradicting the hypothesis.  Hence `S ⊓ C(X) = ⊥` and `⁅X, S⁆ ≠ ⊥`, and the latter is
a subgroup of the prime order group `S`, so `⁅X, S⁆ = S`.
-/

set_option linter.style.haveILetI false

open Pointwise

namespace Work.Hering.Step5

/-- If `S` is a normal subgroup, `S ⊔ X = ⊤`, `S` and `X` commute elementwise, and both `S`
and `X` are commutative, then `G` itself is commutative. -/
private theorem mul_comm_of_normal_sup {G : Type*} [Group G] {S X : Subgroup G}
    (hSn : S.Normal) (hsup : S ⊔ X = ⊤)
    (hc : ∀ x ∈ X, ∀ s ∈ S, x * s = s * x)
    (hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) :
    ∀ a b : G, a * b = b * a := by
  haveI := hSn
  intro a b
  -- every element of `G = S ⊔ X = S * X` is a product `s * x`
  have ha : a ∈ (↑S : Set G) * (↑X : Set G) := by
    have : a ∈ (↑(S ⊔ X) : Set G) := by rw [hsup]; trivial
    rwa [Subgroup.normal_mul] at this
  have hb : b ∈ (↑S : Set G) * (↑X : Set G) := by
    have : b ∈ (↑(S ⊔ X) : Set G) := by rw [hsup]; trivial
    rwa [Subgroup.normal_mul] at this
  obtain ⟨s1, hs1, x1, hx1, h1⟩ := Set.mem_mul.mp ha
  obtain ⟨s2, hs2, x2, hx2, h2⟩ := Set.mem_mul.mp hb
  rw [← h1, ← h2]
  calc s1 * x1 * (s2 * x2)
      = s1 * (x1 * s2) * x2 := by group
    _ = s1 * (s2 * x1) * x2 := by rw [hc x1 hx1 s2 hs2]
    _ = s1 * s2 * (x1 * x2) := by group
    _ = s2 * s1 * (x1 * x2) := by rw [hSc s1 hs1 s2 hs2]
    _ = s2 * s1 * (x2 * x1) := by rw [hXc x1 hx1 x2 hx2]
    _ = s2 * (s1 * x2) * x1 := by group
    _ = s2 * (x2 * s1) * x1 := by rw [hc x2 hx2 s1 hs1]
    _ = s2 * x2 * (s1 * x1) := by group

theorem order21_structure {A : Type*} [Group A] [Finite A] (hcard : Nat.card A = 21)
    (hnab : ∃ a b : A, a * b ≠ b * a) :
    ∃ S X : Subgroup A, S.Normal ∧ Nat.card S = 7 ∧ Nat.card X = 3 ∧
      S ⊓ X = ⊥ ∧ S ⊔ X = ⊤ ∧ S ⊓ Subgroup.centralizer (X : Set A) = ⊥ ∧ ⁅X, S⁆ = S := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  -- a subgroup `S₀` of order `7` and a subgroup `X₀` of order `3`
  obtain ⟨S₀, hS₀card⟩ : ∃ H : Subgroup A, Nat.card H = 7 := by
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (p := 7) (n := 1) (G := A)
      (by rw [hcard]; norm_num)
    exact ⟨H, by simpa using hH⟩
  obtain ⟨X₀, hX₀card⟩ : ∃ H : Subgroup A, Nat.card H = 3 := by
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (p := 3) (n := 1) (G := A)
      (by rw [hcard]; norm_num)
    exact ⟨H, by simpa using hH⟩
  -- `S₀` is a Sylow `7`-subgroup of index `3`
  have hS₀pg : IsPGroup 7 ↥S₀ := IsPGroup.of_card (n := 1) (p := 7) (by rw [hS₀card]; norm_num)
  have hS₀index : S₀.index = 3 := by
    have h := S₀.card_mul_index
    rw [hS₀card, hcard] at h
    omega
  let P : Sylow 7 A := hS₀pg.toSylow (by rw [hS₀index]; norm_num)
  have hPcoe : (P : Subgroup A) = S₀ := IsPGroup.toSylow_coe _ _
  have hPindex : (P : Subgroup A).index = 3 := by rw [hPcoe, hS₀index]
  -- there is exactly one Sylow `7`-subgroup, hence `S₀` is normal
  have hSylow_card : Nat.card (Sylow 7 A) = 1 := by
    have h1 : Nat.card (Sylow 7 A) ∣ 3 := by
      have := Sylow.card_dvd_index P
      rwa [hPindex] at this
    have h2 : Nat.card (Sylow 7 A) ≡ 1 [MOD 7] := card_sylow_modEq_one 7 A
    have hle : Nat.card (Sylow 7 A) ≤ 3 := Nat.le_of_dvd (by norm_num) h1
    exact Nat.ModEq.eq_of_lt_of_lt h2 (by omega) (by norm_num)
  haveI : Subsingleton (Sylow 7 A) := (Nat.card_eq_one_iff_unique.mp hSylow_card).1
  have hS₀normal : S₀.Normal := hPcoe ▸ Sylow.normal_of_subsingleton P
  haveI : S₀.Normal := hS₀normal
  -- `S₀` and `X₀` are commutative (they have prime order)
  have hS₀c : ∀ a ∈ S₀, ∀ b ∈ S₀, a * b = b * a := by
    haveI : IsCyclic ↥S₀ := isCyclic_of_prime_card hS₀card
    intro a ha b hb
    have := (IsMulCommutative.is_comm (M := ↥S₀)).comm (⟨a, ha⟩ : ↥S₀) (⟨b, hb⟩ : ↥S₀)
    simpa using this
  have hX₀c : ∀ a ∈ X₀, ∀ b ∈ X₀, a * b = b * a := by
    haveI : IsCyclic ↥X₀ := isCyclic_of_prime_card hX₀card
    intro a ha b hb
    have := (IsMulCommutative.is_comm (M := ↥X₀)).comm (⟨a, ha⟩ : ↥X₀) (⟨b, hb⟩ : ↥X₀)
    simpa using this
  -- `S₀` and `X₀` are complements
  have hcomp : S₀.IsComplement' X₀ :=
    Subgroup.isComplement'_of_coprime (by norm_num [hS₀card, hX₀card, hcard])
      (by norm_num [hS₀card, hX₀card])
  have hinfSX : S₀ ⊓ X₀ = ⊥ := hcomp.disjoint.eq_bot
  have hsupSX : S₀ ⊔ X₀ = ⊤ := hcomp.sup_eq_top
  -- if `S₀` and `X₀` commute elementwise then `A` is abelian, contradicting the hypothesis
  have hcontr : (∀ x ∈ X₀, ∀ s ∈ S₀, x * s = s * x) → False := by
    intro hc
    obtain ⟨a, b, hne⟩ := hnab
    exact hne (mul_comm_of_normal_sup hS₀normal hsupSX hc hS₀c hX₀c a b)
  -- `S₀ ⊓ C(X₀) = ⊥`, because any subgroup of the prime order group `S₀` is trivial or all of it
  have hCZ : S₀ ⊓ Subgroup.centralizer (X₀ : Set A) = ⊥ := by
    rcases Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 7)
        (Nat.card ↥(S₀ ⊓ Subgroup.centralizer (X₀ : Set A)))
        (by rw [← hS₀card]; exact Subgroup.card_dvd_of_le inf_le_left) with h1 | h7
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have hSleC : S₀ ≤ Subgroup.centralizer (X₀ : Set A) := by
        have heq : S₀ ⊓ Subgroup.centralizer (X₀ : Set A) = S₀ :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h7, hS₀card])
        rw [← heq]; exact inf_le_right
      exact hcontr (fun x hx s hs => (Subgroup.mem_centralizer_iff.mp (hSleC hs)) x hx)
  -- `⁅X₀, S₀⁆` is a nontrivial subgroup of the prime order group `S₀`, hence equals `S₀`
  have hcomm : ⁅X₀, S₀⁆ = S₀ := by
    have hle := Subgroup.commutator_le_right X₀ S₀
    rcases Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 7) (Nat.card ↥⁅X₀, S₀⁆)
        (by rw [← hS₀card]; exact Subgroup.card_dvd_of_le hle) with h1 | h7
    · exfalso
      have hbot : ⁅X₀, S₀⁆ = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      have hcle : X₀ ≤ Subgroup.centralizer (S₀ : Set A) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      exact hcontr (fun x hx s hs => (Subgroup.mem_centralizer_iff.mp (hcle hx) s hs).symm)
    · exact Subgroup.eq_of_le_of_card_ge hle (by rw [h7, hS₀card])
  exact ⟨S₀, X₀, hS₀normal, hS₀card, hX₀card, hinfSX, hsupSX, hCZ, hcomm⟩

end Work.Hering.Step5
