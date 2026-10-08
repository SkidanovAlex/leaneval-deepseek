import Mathlib

open scoped Pointwise

namespace Work.CORE4.L2PAux

/-- Suppose `Q` and `T` are complementary subgroups of a finite group `N`, with `|T| = p` a
prime, and `p ^ 2 ∤ |N|`. Then any subgroup `Z` of `N` of cardinality `p` is conjugate to `T`
by an element of `Q`.

The proof is Sylow's theorem: since `p ^ 2 ∤ |N|` and `|N| = |Q| · p`, both `T` and `Z` are
Sylow `p`-subgroups of `N`, hence are conjugate in `N`. Writing the conjugating element as
`q * t` with `q ∈ Q`, `t ∈ T` (using the complement decomposition), the factor `t` normalizes
`T`, so `Z` is already conjugate to `T` by `q ∈ Q`. -/
theorem exists_conjSub_of_isComplement {N : Type} [Group N] [Finite N] {p : ℕ} [Fact p.Prime]
    (Q T Z : Subgroup N) (hQ : Q.Normal) (hc : Q.IsComplement' T)
    (hTcard : Nat.card T = p) (hZcard : Nat.card Z = p) (hpdvd : ¬ p ^ 2 ∣ Nat.card N) :
    ∃ q ∈ Q, Z = Subgroup.map (MulAut.conj q).toMonoidHom T := by
  have _ : Q.Normal := hQ
  have hp : p.Prime := Fact.out
  -- `|N| = |Q| * p`
  have hNcard : Nat.card Q * p = Nat.card N := by rw [← hTcard]; exact hc.card_mul_card
  -- since `p ^ 2 ∤ |N| = |Q| * p`, we have `p ∤ |Q|`
  have hpndvdQ : ¬ p ∣ Nat.card Q := by
    intro h
    apply hpdvd
    rw [pow_two, ← hNcard]
    exact Nat.mul_dvd_mul h (dvd_refl p)
  -- the index of `T` (resp. `Z`) in `N` equals `|Q|`, hence is not divisible by `p`
  have hTindex : T.index = Nat.card Q := by
    have h1 : T.index * Nat.card T = Nat.card N := Subgroup.index_mul_card T
    rw [hTcard, ← hNcard] at h1
    exact Nat.mul_right_cancel hp.pos h1
  have hZindex : Z.index = Nat.card Q := by
    have h1 : Z.index * Nat.card Z = Nat.card N := Subgroup.index_mul_card Z
    rw [hZcard, ← hNcard] at h1
    exact Nat.mul_right_cancel hp.pos h1
  -- `T` and `Z` are Sylow `p`-subgroups of `N`
  have hTgrp : IsPGroup p ↥T := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hTcard)
  have hZgrp : IsPGroup p ↥Z := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hZcard)
  let sT : Sylow p N := hTgrp.toSylow (by rw [hTindex]; exact hpndvdQ)
  let sZ : Sylow p N := hZgrp.toSylow (by rw [hZindex]; exact hpndvdQ)
  have hsT : (sT : Subgroup N) = T := rfl
  have hsZ : (sZ : Subgroup N) = Z := rfl
  -- Sylow's theorem: the two Sylow subgroups are conjugate in `N`
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N sT sZ
  -- write the conjugating element `g = q * t` with `q ∈ Q`, `t ∈ T`
  obtain ⟨⟨⟨q, hq⟩, ⟨t, ht⟩⟩, hqt⟩ := hc.2 g
  change q * t = g at hqt
  -- `t ∈ T` normalizes `T`, hence fixes `sT`
  have ht_smul : t • sT = sT := by
    rw [Sylow.smul_eq_iff_mem_normalizer]
    exact Subgroup.le_normalizer ht
  -- therefore `q` alone conjugates `T` to `Z`
  have hq_smul : q • sT = sZ := by
    have h2 : (q * t) • sT = sZ := by rw [hqt]; exact hg
    rwa [mul_smul, ht_smul] at h2
  refine ⟨q, hq, ?_⟩
  have key : MulAut.conj q • (sT : Subgroup N) = Z := by
    rw [← Sylow.coe_subgroup_smul, hq_smul, hsZ]
  rw [← key, hsT]
  rfl

end Work.CORE4.L2PAux
