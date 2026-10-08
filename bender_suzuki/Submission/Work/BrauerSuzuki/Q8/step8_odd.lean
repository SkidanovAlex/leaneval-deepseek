import Mathlib
import Submission.Work.BrauerSuzuki.Q8.Ctx
import Submission.Work.BrauerSuzuki.Q8.Card
import Submission.Work.BrauerSuzuki.Q8.LamEta
import Submission.Work.BrauerSuzuki.Q8.Eta
import Submission.Work.BrauerSuzuki.Q8.Eta2
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.cfInner_int_vchar
import Submission.Work.CharCore.isVChar_mul

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Q8

/-- **Parity trick for a group of odd order.**  If `H` has odd order and `b : H → ℤ` is
symmetric under inversion (`b u⁻¹ = b u`), then the sum of `b` over `H` has the same parity as
`b 1`:  in `H ∖ {1}` the map `u ↦ u⁻¹` is a fixed-point-free involution, so its elements split
into inversion pairs and each pair contributes `b u + b u⁻¹ = 2 b u`.

Worked in `ZMod 2`, where the fixed-point-free involution makes the sum over `H ∖ {1}` vanish
(`Finset.sum_involution`). -/
private theorem odd_apply_one_of_odd_sum {H : Type*} [Group H] [Fintype H]
    (hodd : Odd (Fintype.card H)) (b : H → ℤ) (hb : ∀ u, b u⁻¹ = b u)
    (h : Odd (∑ u, b u)) : Odd (b 1) := by
  classical
  rw [← ZMod.intCast_eq_one_iff_odd] at h ⊢
  have hcast : ((∑ u, b u : ℤ) : ZMod 2) = ∑ u, (b u : ZMod 2) := by
    push_cast; rfl
  rw [hcast] at h
  have hz : ∑ u ∈ Finset.univ.erase 1, (b u : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun u _ => u⁻¹) ?_ ?_ ?_ ?_
    · intro aa _
      rw [hb aa, ← two_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul]
    · intro aa ha _ hcon
      have ha1 : aa ≠ 1 := (Finset.mem_erase.mp ha).1
      apply ha1
      have hsq : aa ^ 2 = 1 := by
        have hh : aa * aa = aa * aa⁻¹ := by rw [hcon]
        rw [pow_two, hh, mul_inv_cancel]
      have hd2 : orderOf aa ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
      have hdc : orderOf aa ∣ Fintype.card H := by
        rw [← Nat.card_eq_fintype_card]; exact orderOf_dvd_natCard aa
      have hg : Nat.gcd 2 (Fintype.card H) = 1 := hodd.coprime_two_left
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hg ▸ Nat.dvd_gcd hd2 hdc))
    · intro aa ha
      exact Finset.mem_erase.mpr ⟨inv_ne_one.mpr (Finset.mem_erase.mp ha).1, Finset.mem_univ _⟩
    · intro aa _; exact inv_inv aa
  have hsplit : (∑ u : H, (b u : ZMod 2)) = (b 1 : ZMod 2) := by
    rw [← Finset.sum_erase_add (Finset.univ) (fun u => (b u : ZMod 2)) (Finset.mem_univ 1), hz,
      zero_add]
  exact hsplit.symm.trans h

/-- Congruence mod `2` between the sum of an integer sequence and the sum of its squares. -/
private theorem odd_sum_sq_iff {ι : Type*} [Fintype ι] (a : ι → ℤ) :
    Odd (∑ i, a i ^ 2) ↔ Odd (∑ i, a i) := by
  have h2 : ((∑ i, a i ^ 2 : ℤ) : ZMod 2) = ((∑ i, a i : ℤ) : ZMod 2) := by
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact (show ∀ x : ZMod 2, x ^ 2 = x from by decide) (a i : ZMod 2)
  rw [← ZMod.intCast_eq_one_iff_odd (n := ∑ i, a i ^ 2),
      ← ZMod.intCast_eq_one_iff_odd (n := ∑ i, a i), h2]

open Classical in
theorem step8_odd {G : Type*} [Group G] [Fintype G] {x : G} {S : Sylow 2 G}
    (h : Work.BrauerSuzuki.Q8.Ctx G x S) (χ : G → ℂ) (ε : ℂ)
    (hIrr : χ ∈ Work.CharCore.Irr G) (hε : ε = 1 ∨ ε = -1)
    (hη : Work.CharCore.cfInner χ h.eta = ε)
    (hint : ∀ g : G, ∃ n : ℤ, χ g = (n : ℂ))
    (hconj : ∀ u : G, u ∈ Work.BrauerSuzuki.Q8.Hstar x → χ (x * u) = χ (x * u⁻¹))
    (h6 : Work.CharCore.cfInner χ h.eta =
      (Nat.card ↥(Work.BrauerSuzuki.Q8.Hstar x) : ℂ)⁻¹ *
        ∑ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), χ (x * (u : G)))
    (h6sq : Work.CharCore.cfInner (χ ^ 2) h.eta =
      (Nat.card ↥(Work.BrauerSuzuki.Q8.Hstar x) : ℂ)⁻¹ *
        ∑ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), (χ (x * (u : G))) ^ 2) :
    (∃ n : ℤ, χ x = (n : ℂ) ∧ Odd n) ∧
      (∃ m : ℤ, Work.CharCore.cfInner (χ ^ 2) h.eta = (m : ℂ) ∧ Odd m) := by
  classical
  set N : ℕ := Nat.card ↥(Work.BrauerSuzuki.Q8.Hstar x) with hNdef
  have hNodd : Odd N := by rw [hNdef]; exact h.odd_H
  let a : ↥(Work.BrauerSuzuki.Q8.Hstar x) → ℤ := fun u => (hint (x * (u : G))).choose
  have ha : ∀ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), χ (x * (u : G)) = (a u : ℂ) :=
    fun u => (hint (x * (u : G))).choose_spec
  let n : ℤ := (hint x).choose
  have hxn : χ x = (n : ℂ) := (hint x).choose_spec
  have hNne : (N : ℂ) ≠ 0 := by
    have hpos : 0 < N := by rw [hNdef]; exact Nat.card_pos
    exact_mod_cast hpos.ne'
  -- Step (6), evaluated: `∑_{u ∈ H*} χ (x u) = ε |H*|`.
  have hS : (∑ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), χ (x * (u : G))) = ε * (N : ℂ) := by
    have h6' := h6
    rw [hη] at h6'
    have h1 : (N : ℂ) * ε = ∑ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), χ (x * (u : G)) := by
      rw [h6', ← mul_assoc, mul_inv_cancel₀ hNne, one_mul]
    rw [mul_comm] at h1
    exact h1.symm
  have hAc : ((∑ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), a u : ℤ) : ℂ) = ε * ((N : ℤ) : ℂ) := by
    have h1 : ((∑ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), a u : ℤ) : ℂ) =
        ∑ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), (a u : ℂ) := by
      rw [Int.cast_sum]
    rw [h1, show (∑ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), (a u : ℂ)) =
        ∑ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), χ (x * (u : G)) from
        Finset.sum_congr rfl (fun u _ => (ha u).symm), hS, Int.cast_natCast]
  -- The integer sum `∑_{u ∈ H*} χ (x u)` is odd.
  have hAodd : Odd (∑ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), a u) := by
    rcases hε with h1 | h1
    · rw [h1, one_mul] at hAc
      have : (∑ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), a u) = (N : ℤ) := Int.cast_injective hAc
      rw [this]; exact_mod_cast hNodd
    · rw [h1] at hAc
      rw [neg_one_mul, ← Int.cast_neg] at hAc
      have : (∑ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), a u) = -(N : ℤ) := Int.cast_injective hAc
      rw [this]; exact (show Odd ((N : ℤ)) from by exact_mod_cast hNodd).neg
  have hNodd_fin : Odd (Fintype.card ↥(Work.BrauerSuzuki.Q8.Hstar x)) := by
    rw [← Nat.card_eq_fintype_card, ← hNdef]; exact hNodd
  -- Step (7)(b): `χ (x u) = χ (x u⁻¹)`, in integer form.
  have hb : ∀ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), a u⁻¹ = a u := by
    intro u
    refine Int.cast_injective (α := ℂ) ?_
    rw [← ha u⁻¹, ← ha u]
    have hcoe : ((u⁻¹ : ↥(Work.BrauerSuzuki.Q8.Hstar x)) : G) = (u : G)⁻¹ := rfl
    rw [hcoe]
    exact (hconj (u : G) u.2).symm
  have hC := odd_apply_one_of_odd_sum hNodd_fin a hb hAodd
  have ha1 : a (1 : ↥(Work.BrauerSuzuki.Q8.Hstar x)) = n := by
    refine Int.cast_injective (α := ℂ) ?_
    rw [← ha (1 : ↥(Work.BrauerSuzuki.Q8.Hstar x))]
    simp [hxn]
  -- Step (6) for `χ²`, plus integrality of `(χ², η)`.
  have hv2 : Work.CharCore.IsVChar (χ ^ 2) := by
    rw [pow_two]
    exact Work.CharCore.isVChar_mul (Work.CharCore.IsVChar.of_mem_Irr hIrr)
      (Work.CharCore.IsVChar.of_mem_Irr hIrr)
  obtain ⟨m, hm⟩ := Work.CharCore.cfInner_int_vchar hv2 h.isVChar_eta
  have hsq' : (m : ℂ) =
      (N : ℂ)⁻¹ * ∑ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), (χ (x * (u : G))) ^ 2 := by
    rw [← hm]; exact h6sq
  have hA2c : ((∑ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), (a u) ^ 2 : ℤ) : ℂ) =
      ∑ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), (χ (x * (u : G))) ^ 2 := by
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [ha u]
    push_cast
    ring
  have hNm : (N : ℤ) * m = ∑ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), (a u) ^ 2 := by
    refine Int.cast_injective (α := ℂ) ?_
    rw [Int.cast_mul, Int.cast_natCast]
    rw [hA2c, hsq', ← mul_assoc, mul_inv_cancel₀ hNne, one_mul]
  have hA2odd : Odd (∑ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), (a u) ^ 2) :=
    (odd_sum_sq_iff a).mpr hAodd
  have hmood : Odd m := by
    have hprod : Odd ((N : ℤ) * m) := hNm.symm ▸ hA2odd
    rw [← ZMod.intCast_eq_one_iff_odd] at hprod ⊢
    have hN2 : ((N : ℤ) : ZMod 2) = 1 := by
      rw [ZMod.intCast_eq_one_iff_odd]; exact_mod_cast hNodd
    rw [Int.cast_mul, hN2, one_mul] at hprod
    exact hprod
  exact ⟨⟨n, hxn, ha1 ▸ hC⟩, ⟨m, hm, hmood⟩⟩

end Work.BrauerSuzuki.Q8
