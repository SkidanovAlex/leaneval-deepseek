import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.ZASS.Leaf9
import Submission.Work.ZASS.Frobenius
import Submission.Work.ZASS.conjBy_mem_pairStab

namespace Work.ZASS

open Work.Zassenhaus (borel pairStab)

/-- `orderOf x = 2` is the same as `x ≠ 1` together with `x ^ 2 = 1`. -/
theorem orderOf_eq_two_iff' {G : Type*} [Group G] (x : G) :
    orderOf x = 2 ↔ x ≠ 1 ∧ x ^ 2 = 1 := by
  constructor
  · intro h
    refine ⟨?_, by rw [← h]; exact pow_orderOf_eq_one x⟩
    intro h1
    rw [h1, orderOf_one] at h
    exact absurd h (by norm_num)
  · rintro ⟨h1, h2⟩
    exact orderOf_eq_prime h2 h1

/-- **HB III XI 1.8(b)(c)** (= Isaacs Thm 6.3 / HB V 8.18), in the contract form
`Work.GW2.ZassCentralInvProp`. -/
theorem zassCentralInv : Work.GW2.ZassCentralInvProp := by
  intro G X _ _ _ _ p k hprime hp hq h hd inf zero hne U hU
  classical
  obtain ⟨hUB, hcardU, hN, hdec, hfree, hcomm, hexp⟩ := hU
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero] at hq; omega
    · exact hkpos
  have hcardH : Nat.card (pairStab G inf zero) = (p ^ k - 1) / 2 := by
    have h1 := h.2.2.2.2 inf zero hne
    have h2 : Nat.card (pairStab G inf zero) =
        Nat.card (MulAction.stabilizer G inf ⊓ MulAction.stabilizer G zero : Subgroup G) := by
      rw [pairStab, inf_comm]
    rw [h2]
    exact Nat.eq_div_of_mul_eq_right (by norm_num : (2 : ℕ) ≠ 0) h1
  have hnt : Nontrivial ↥U := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcardU]
    exact Nat.one_lt_pow (by rintro rfl; rw [pow_zero] at hq; omega) hprime.out.one_lt
  have heven : 2 ∣ Nat.card (pairStab G inf zero) := by
    rw [hcardH]; exact even_iff_two_dvd.mp hd
  obtain ⟨t, ht, htuniq⟩ :=
    unique_involution_of_even (inf := inf) (zero := zero) hUB hN hfree heven hnt
  have htG1 : (t : G) ≠ 1 := fun h1 => ht.1 (Subtype.ext h1)
  have htG2 : (t : G) ^ 2 = 1 := by
    have := congrArg (fun x : ↥(pairStab G inf zero) => (x : G)) ht.2
    simpa using this
  refine ⟨(t : G), t.2, (orderOf_eq_two_iff' (t : G)).mpr ⟨htG1, htG2⟩, ?_, ?_, ?_, ?_⟩
  · intro u hu
    have h1 := involution_inverts (inf := inf) (zero := zero) hUB hN hfree t ht.1 ht.2 ⟨u, hu⟩
    simpa [conjBy] using h1
  · intro t' ht'H ht'ord
    obtain ⟨ht'1, ht'2⟩ := (orderOf_eq_two_iff' t').mp ht'ord
    have h1 : (⟨t', ht'H⟩ : ↥(pairStab G inf zero)) ≠ 1 :=
      fun hh1 => ht'1 (congrArg Subtype.val hh1)
    have h2 : (⟨t', ht'H⟩ : ↥(pairStab G inf zero)) ^ 2 = 1 :=
      Subtype.ext (by simpa using ht'2)
    exact congrArg Subtype.val (htuniq ⟨t', ht'H⟩ ⟨h1, h2⟩)
  · intro hh hhH
    have hconj : conjBy hh (t : G) ∈ pairStab G inf zero :=
      (pairStab G inf zero).mul_mem ((pairStab G inf zero).mul_mem hhH t.2)
        ((pairStab G inf zero).inv_mem hhH)
    have hne1 : conjBy hh (t : G) ≠ 1 := by
      intro h1
      apply htG1
      have h2 := congrArg (fun x : G => hh⁻¹ * x * hh) h1
      simpa [conjBy, mul_assoc] using h2
    have hsq : (conjBy hh (t : G)) ^ 2 = 1 := by
      rw [conjBy, pow_two]
      calc (hh * (t : G) * hh⁻¹) * (hh * (t : G) * hh⁻¹)
          = hh * ((t : G) * (t : G)) * hh⁻¹ := by group
        _ = hh * 1 * hh⁻¹ := by rw [← pow_two, htG2]
        _ = 1 := by group
    have hne1' : (⟨conjBy hh (t : G), hconj⟩ : ↥(pairStab G inf zero)) ≠ 1 :=
      fun hh1 => hne1 (congrArg Subtype.val hh1)
    have hsq' : (⟨conjBy hh (t : G), hconj⟩ : ↥(pairStab G inf zero)) ^ 2 = 1 :=
      Subtype.ext (by simpa using hsq)
    have h3 : hh * (t : G) * hh⁻¹ = (t : G) :=
      congrArg Subtype.val (htuniq ⟨conjBy hh (t : G), hconj⟩ ⟨hne1', hsq'⟩)
    change hh * (t : G) * hh⁻¹ = (t : G) at h3
    calc hh * (t : G) = (hh * (t : G) * hh⁻¹) * hh := by group
      _ = (t : G) * hh := by rw [h3]
  · intro s' hsa hsb
    have hconj : conjBy s' (t : G) ∈ pairStab G inf zero := conjBy_mem_pairStab hsa hsb t.2
    have hne1 : conjBy s' (t : G) ≠ 1 := by
      intro h1
      apply htG1
      have h2 := congrArg (fun x : G => s'⁻¹ * x * s') h1
      simpa [conjBy, mul_assoc] using h2
    have hsq : (conjBy s' (t : G)) ^ 2 = 1 := by
      rw [conjBy, pow_two]
      calc (s' * (t : G) * s'⁻¹) * (s' * (t : G) * s'⁻¹)
          = s' * ((t : G) * (t : G)) * s'⁻¹ := by group
        _ = s' * 1 * s'⁻¹ := by rw [← pow_two, htG2]
        _ = 1 := by group
    have hne1' : (⟨conjBy s' (t : G), hconj⟩ : ↥(pairStab G inf zero)) ≠ 1 :=
      fun hh1 => hne1 (congrArg Subtype.val hh1)
    have hsq' : (⟨conjBy s' (t : G), hconj⟩ : ↥(pairStab G inf zero)) ^ 2 = 1 :=
      Subtype.ext (by simpa using hsq)
    have h3 : s' * (t : G) * s'⁻¹ = (t : G) :=
      congrArg Subtype.val (htuniq ⟨conjBy s' (t : G), hconj⟩ ⟨hne1', hsq'⟩)
    change s' * (t : G) * s'⁻¹ = (t : G) at h3
    calc s' * (t : G) = (s' * (t : G) * s'⁻¹) * s' := by group
      _ = (t : G) * s' := by rw [h3]

end Work.ZASS
