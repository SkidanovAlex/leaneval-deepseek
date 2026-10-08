import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.ZASS.dvd_card_sub_one_of_isConjInvariant
import Submission.Work.ZASS.two_mul_pow_ne_pow_add_one
import Submission.Work.Zassenhaus.Basic

namespace Work.ZASS

open Work.Zassenhaus

/-- Arithmetic step of Z4.  If `1 < n`, `n ∣ p ^ k` and `(p ^ k - 1) / 2 ∣ n - 1`
with `p` an odd prime and `1 ≤ k`, then `n = p ^ k`.

Write `n = p ^ m` with `m ≤ k`.  Since `(p ^ k - 1) / 2 ∣ p ^ m - 1`, writing the quotient as
`c` we get `p ^ m = (p ^ k - 1) / 2 * c + 1`; as `p ^ m ≤ p ^ k` this forces `c ≤ 2`.  For
`c = 1` we would get `2 * p ^ m = p ^ k + 1`, excluded by
`Work.ZASS.two_mul_pow_ne_pow_add_one`; hence `c = 2` and `p ^ m = p ^ k`. -/
theorem eq_pow_of_dvd_half_of_dvd_pow {p k n : ℕ} (hp : p.Prime) (hodd : Odd p) (hk : 1 ≤ k)
    (hdvd : n ∣ p ^ k) (hgt : 1 < n) (hhalf : (p ^ k - 1) / 2 ∣ n - 1) : n = p ^ k := by
  obtain ⟨m, hmk, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hgt
    · exact h
  have hpmle : p ^ m ≤ p ^ k := Nat.pow_le_pow_right hp.pos hmk
  -- `2 * ((p ^ k - 1) / 2) = p ^ k - 1`
  obtain ⟨j, hj⟩ := hodd.pow (n := k)
  have h2h : 2 * ((p ^ k - 1) / 2) = p ^ k - 1 := by
    have h1 : p ^ k - 1 = 2 * j := by omega
    rw [h1, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have hhpos : 0 < (p ^ k - 1) / 2 := by
    have hp3 : 3 ≤ p := by
      have hne : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hodd
      have hp2 : 2 ≤ p := hp.two_le
      omega
    have : 3 ≤ p ^ k := by
      calc 3 ≤ p := hp3
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
    omega
  obtain ⟨c, hc⟩ := hhalf
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, mul_zero] at hc; omega
    · exact h
  have hcle : c ≤ 2 := by
    have hle : (p ^ k - 1) / 2 * c ≤ (p ^ k - 1) / 2 * 2 := by
      rw [← hc, mul_comm ((p ^ k - 1) / 2) 2, h2h]
      omega
    exact Nat.le_of_mul_le_mul_left hle hhpos
  interval_cases c
  · exfalso
    have h1 : p ^ m = (p ^ k - 1) / 2 + 1 := by omega
    have hcontra : 2 * p ^ m = p ^ k + 1 := by
      rw [h1]
      have := h2h
      omega
    exact two_mul_pow_ne_pow_add_one hp hk m hcontra
  · have h2h' : (p ^ k - 1) / 2 * 2 = p ^ k - 1 := by rw [mul_comm]; exact h2h
    have : p ^ m - 1 = p ^ k - 1 := by rw [hc, h2h']
    omega

/-- **Z4 (blueprint §ZASS).** `U` has exponent `p`.  Assuming `U` abelian, the set
`Ω = {x ∈ U | x^p = 1}` is a subgroup of `U`; it is nontrivial (`U` is a nontrivial finite
`p`-group, so its center contains an element of order `p`), `H = G_{∞0}` normalizes `U` and
preserves `Ω`, and `ZASS/eq_top_of_isConjInvariant` (applied to `W = Ω`) gives `Ω = U`. -/
theorem exponent_dvd_p_of_zass {G X : Type} [Group G] [Finite G] [MulAction G X]
    {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hk : 1 ≤ k) {q : ℕ} (hq : q = p ^ k)
    {inf zero : X} {U : Subgroup G} (hUB : U ≤ Work.Zassenhaus.borel G inf)
    (hcardU : Nat.card U = p ^ k)
    (hcardH : Nat.card (Work.Zassenhaus.pairStab G inf zero) = (q - 1) / 2)
    (hN : (U.subgroupOf (Work.Zassenhaus.borel G inf)).Normal)
    (hcomm : IsMulCommutative U)
    (hfix : Work.ZASS.FixedPointFreeConj U (Work.Zassenhaus.pairStab G inf zero)) :
    ∀ u ∈ U, u ^ p = 1 := by
  haveI : IsMulCommutative U := hcomm
  set H : Subgroup G := Work.Zassenhaus.pairStab G inf zero with hHdef
  -- The `p`-torsion subgroup `Ω = {x ∈ U | x^p = 1}` (a subgroup because `U` is abelian).
  obtain ⟨Ω, hΩmem⟩ : ∃ Ω : Subgroup G, ∀ x : G, x ∈ Ω ↔ x ∈ U ∧ x ^ p = 1 :=
    ⟨{ carrier := {x : G | x ∈ U ∧ x ^ p = 1}
       mul_mem' := by
         rintro x y ⟨hxU, hxp⟩ ⟨hyU, hyp⟩
         refine ⟨U.mul_mem hxU hyU, ?_⟩
         have hc : Commute x y := by
           have h := IsMulCommutative.is_comm.comm (α := U) ⟨x, hxU⟩ ⟨y, hyU⟩
           exact Subtype.ext_iff.mp h
         rw [hc.mul_pow, hxp, hyp, mul_one]
       one_mem' := ⟨U.one_mem, one_pow p⟩
       inv_mem' := by
         rintro x ⟨hxU, hxp⟩
         exact ⟨U.inv_mem hxU, by rw [inv_pow, hxp, inv_one]⟩ },
     fun x => Iff.rfl⟩
  have hΩU : Ω ≤ U := fun x hx => ((hΩmem x).mp hx).1
  -- `H ≤ N(U)`: `U ⊴ B`, `H ≤ B`.
  have hHle : H ≤ Subgroup.normalizer (U : Set G) := by
    intro h hh
    have hhB : h ∈ Work.Zassenhaus.borel G inf :=
      Work.Zassenhaus.pairStab_le_borel inf zero (hHdef ▸ hh)
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact mem_conjBy_of_subgroupOf_normal hUB hN hhB hn
    · intro hn
      have hhB' : h⁻¹ ∈ Work.Zassenhaus.borel G inf :=
        (Work.Zassenhaus.borel G inf).inv_mem hhB
      have hconj := mem_conjBy_of_subgroupOf_normal hUB hN hhB' hn
      have hval : conjBy h⁻¹ (h * n * h⁻¹) = n := by
        simp only [conjBy]; group
      rwa [hval] at hconj
  -- `H` preserves `Ω`: conjugation preserves `x ^ p = 1`.
  have hΩinv : IsConjInvariant H Ω := by
    intro h hh w hw
    have hhB : h ∈ Work.Zassenhaus.borel G inf :=
      Work.Zassenhaus.pairStab_le_borel inf zero (hHdef ▸ hh)
    obtain ⟨hwU, hwp⟩ := (hΩmem w).mp hw
    refine (hΩmem (conjBy h w)).mpr
      ⟨mem_conjBy_of_subgroupOf_normal hUB hN hhB hwU, ?_⟩
    show (h * w * h⁻¹) ^ p = 1
    rw [conj_pow, hwp]
    simp
  -- `Ω` is nontrivial: Cauchy's theorem in the (`p`-)group `U`.
  have hΩne : Ω ≠ ⊥ := by
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    have hpdvd : p ∣ Nat.card U := by
      rw [hcardU]; exact dvd_pow_self p (by omega)
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpdvd
    have hgp : (g : G) ^ p = 1 := by
      rw [← Subgroup.coe_pow, show g ^ p = 1 from hg ▸ pow_orderOf_eq_one g, Subgroup.coe_one]
    have hgne : g ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hg
      exact (Fact.out (p := p.Prime)).ne_one hg.symm
    refine ⟨⟨(g : G), (hΩmem _).mpr ⟨g.2, hgp⟩⟩, ?_⟩
    intro hcon
    apply hgne
    have hval : (g : G) = 1 := by
      have := congrArg (Subtype.val : Ω → G) hcon
      simpa using this
    have ho1 : orderOf (g : G) = 1 := by rw [hval, orderOf_one]
    rw [Subgroup.orderOf_coe] at ho1
    exact orderOf_eq_one_iff.mp ho1
  -- The counting step, applied to `W = Ω`.
  have hcardH' : Nat.card H = (p ^ k - 1) / 2 := by rw [hHdef, hcardH, hq]
  have hdvd : (p ^ k - 1) / 2 ∣ Nat.card Ω - 1 :=
    dvd_card_sub_one_of_isConjInvariant hΩU hHle (hHdef ▸ hfix) hcardH' hΩne (hHdef ▸ hΩinv)
  have hcardΩdvd : Nat.card Ω ∣ p ^ k := by
    rw [← hcardU]; exact Subgroup.card_dvd_of_le hΩU
  have hΩgt : 1 < Nat.card Ω := by
    rw [Subgroup.ne_bot_iff_exists_ne_one] at hΩne
    obtain ⟨a, ha⟩ := hΩne
    exact Finite.one_lt_card_iff_nontrivial.mpr ⟨a, 1, ha⟩
  have hcardΩ : Nat.card Ω = p ^ k :=
    eq_pow_of_dvd_half_of_dvd_pow (Fact.out (p := p.Prime)) hp hk hcardΩdvd hΩgt hdvd
  have hEq : Ω = U := Subgroup.eq_of_le_of_card_ge hΩU (by rw [hcardU, hcardΩ])
  intro u hu
  exact ((hΩmem u).mp (hEq ▸ hu)).2

end Work.ZASS
