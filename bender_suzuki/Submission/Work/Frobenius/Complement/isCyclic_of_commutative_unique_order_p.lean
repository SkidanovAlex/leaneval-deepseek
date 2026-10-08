import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped IsMulCommutative

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Frobenius.Complement

/-- A finite commutative `p`-group with at most one subgroup of order `p` is cyclic.
Proved by strong induction on the group order, applied to the image `P` of the `p`-th power map. -/
private theorem isCyclic_aux (n : ℕ) :
    ∀ {G : Type*} [Group G] [Finite G] {p : ℕ}, p.Prime → IsMulCommutative G → IsPGroup p G →
      (∀ Q Q' : Subgroup G, Nat.card Q = p → Nat.card Q' = p → Q = Q') →
      Nat.card G = n → IsCyclic G := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ p hp hcomm hG huniq hcard
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : IsMulCommutative G := hcomm
    have hp2 : 2 ≤ p := hp.two_le
    by_cases hle : Nat.card G ≤ p
    · -- small order: the group is trivial or of order `p`
      by_cases h1 : Nat.card G = 1
      · haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
        exact isCyclic_of_subsingleton
      · have hcard_eq : Nat.card G = p := by
          rcases hG.card_eq_or_dvd with h | h
          · exact absurd h h1
          · have hpos : 0 < Nat.card G := Nat.card_pos_iff.mpr ⟨⟨(1 : G)⟩, inferInstance⟩
            exact le_antisymm hle (Nat.le_of_dvd hpos h)
        haveI : Nontrivial G := by
          rw [← not_subsingleton_iff_nontrivial]
          intro hs
          exact h1 (Nat.card_eq_one_iff_unique.mpr ⟨hs, ⟨1⟩⟩)
        obtain ⟨g, hg⟩ := exists_ne (1 : G)
        have hgord : orderOf g = p := by
          rcases (Nat.dvd_prime hp).mp (hcard_eq ▸ orderOf_dvd_natCard g) with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) hg
          · exact h
        exact isCyclic_of_orderOf_eq_card g (by rw [hgord, hcard_eq])
    · -- main case `p < Nat.card G`
      have hcardgt : p < Nat.card G := not_le.mp hle
      have hcard_ne1 : Nat.card G ≠ 1 := by omega
      have hp_dvd : p ∣ Nat.card G := by
        rcases hG.card_eq_or_dvd with h | h
        · exact absurd h hcard_ne1
        · exact h
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
      let P : G →* G := powMonoidHom p
      let K : Subgroup G := P.ker
      let R : Subgroup G := P.range
      have hP : ∀ x : G, P x = x ^ p := fun x => powMonoidHom_apply p x
      have hKmem : ∀ x : G, x ∈ K ↔ x ^ p = 1 := fun x => by
        rw [show K = P.ker from rfl, MonoidHom.mem_ker, hP x]
      have hRmem : ∀ y : G, y ∈ R ↔ ∃ x : G, x ^ p = y := fun y => by
        rw [show R = P.range from rfl, MonoidHom.mem_range]
        simp only [hP]
      set N : Subgroup G := Subgroup.zpowers z with hNdef
      have hN : Nat.card N = p := by
        rw [hNdef, Nat.card_zpowers, hz]
      -- the kernel of the `p`-th power map has order `p`
      have hNK : N ≤ K := by
        intro x hx
        rw [hKmem x, ← orderOf_dvd_iff_pow_eq_one]
        rw [hNdef] at hx
        exact hz ▸ orderOf_dvd_of_mem_zpowers hx
      have hKp : Nat.card K = p := by
        have hdvd : p ∣ Nat.card K := by
          rw [← hN]
          exact Subgroup.card_dvd_of_le hNK
        have hge : p ≤ Nat.card K := Nat.le_of_dvd Nat.card_pos hdvd
        have hle' : Nat.card K ≤ p := by
          by_contra hcon
          push Not at hcon
          have hNKne : N ≠ K := by
            intro heq
            rw [heq] at hN
            omega
          have hlt : N < K := lt_of_le_of_ne hNK hNKne
          obtain ⟨u, huK, huN⟩ := (SetLike.lt_iff_le_and_exists.mp hlt).2
          have hu_pow : u ^ p = 1 := (hKmem u).mp huK
          have hu_ne1 : u ≠ 1 := fun h => huN (by rw [h]; exact N.one_mem)
          have hzu : Nat.card (Subgroup.zpowers u) = p := by
            rw [Nat.card_zpowers, orderOf_eq_prime hu_pow hu_ne1]
          have := huniq (Subgroup.zpowers u) N hzu hN
          exact huN (this ▸ Subgroup.mem_zpowers u)
        exact le_antisymm hle' hge
      -- cardinality of the image
      have hquot : Nat.card (G ⧸ K) = Nat.card R :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange P).toEquiv
      have hGcard : Nat.card G = Nat.card R * p := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K, hquot, hKp]
      have hRgt1 : 1 < Nat.card R := by
        by_contra hcon
        push Not at hcon
        have hmul : Nat.card R * p ≤ p := by
          calc Nat.card R * p ≤ 1 * p := Nat.mul_le_mul_right p hcon
            _ = p := one_mul p
        omega
      have hRlt : Nat.card R < Nat.card G := by
        rw [hGcard]
        have h := Nat.mul_lt_mul_of_pos_left (n := 1) (m := p) (k := Nat.card R) (by omega) Nat.card_pos
        simpa using h
      -- the image inherits the uniqueness of the order-`p` subgroup
      have huniqR : ∀ Q Q' : Subgroup ↥R, Nat.card Q = p → Nat.card Q' = p → Q = Q' := by
        intro Q Q' hQ hQ'
        have hQm : Nat.card (Q.map R.subtype) = p := by
          rw [Subgroup.card_subtype]; exact hQ
        have hQm' : Nat.card (Q'.map R.subtype) = p := by
          rw [Subgroup.card_subtype]; exact hQ'
        exact Subgroup.map_injective (Subgroup.subtype_injective R) (huniq _ _ hQm hQm')
      -- induction hypothesis on the image
      have hRcyclic : IsCyclic ↥R :=
        ih (Nat.card R) (by rw [← hcard]; exact hRlt)
          (G := ↥R) (p := p) hp
          (⟨⟨fun a b => mul_comm a b⟩⟩ : IsMulCommutative ↥R)
          (hG.to_subgroup R) huniqR rfl
      -- a generator `g` of the image, and a preimage `x` with `x ^ p = g`
      obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top R).mp hRcyclic
      have hgcard : orderOf g = Nat.card R := by
        rw [← Nat.card_zpowers g, hg]
      have hgR : g ∈ R := hg ▸ Subgroup.mem_zpowers g
      obtain ⟨x, hx⟩ := (hRmem g).mp hgR
      have hg_ne1 : g ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hgcard
        omega
      have hx_ne1 : x ≠ 1 := by
        intro h
        exact hg_ne1 (by rw [← hx, h, one_pow])
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hG) x
      have hkpos : 1 ≤ k := by
        by_contra hk0
        have hk0' : k = 0 := by omega
        have : orderOf x = 1 := by rw [hk, hk0', pow_zero]
        exact hx_ne1 (orderOf_eq_one_iff.mp this)
      have hdiv : p ∣ orderOf x := by
        rw [hk]; exact dvd_pow_self p (by omega)
      have hgcd : (orderOf x).gcd p = p := by
        rw [hk]; exact Nat.gcd_eq_right (dvd_pow_self p (by omega))
      have hordg : orderOf g = orderOf x / p := by
        rw [← hx, orderOf_pow, hgcd]
      have hGord : Nat.card G = orderOf x := by
        rw [hGcard, ← hgcard, hordg]
        exact Nat.div_mul_cancel hdiv
      exact isCyclic_of_orderOf_eq_card x hGord.symm

lemma isCyclic_of_commutative_unique_order_p {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hcomm : IsMulCommutative G) (hG : IsPGroup p G) (N : Subgroup G) (hN : Nat.card N = p)
    (huniq : ∀ Q : Subgroup G, Nat.card Q = p → Q = N) : IsCyclic G :=
  isCyclic_aux (Nat.card G) hp hcomm hG
    (fun Q Q' hQ hQ' => (huniq Q hQ).trans (huniq Q' hQ').symm) rfl

end Work.Frobenius.Complement
