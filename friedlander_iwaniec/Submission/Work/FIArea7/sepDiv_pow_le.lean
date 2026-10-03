import Mathlib
import Submission.Work.FIArea7.SepDiv

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

/-- The `t`-th predecessor of an index. -/
private def wit {k : ℕ} (i : Fin k) (t : ℕ) : Fin k := ⟨i.val - t, by have := i.isLt; omega⟩

private lemma wit_val {k : ℕ} (i : Fin k) (t : ℕ) : (wit i t).val = i.val - t := rfl

private lemma wit_le {k : ℕ} (i : Fin k) (t : ℕ) : wit i t ≤ i := by
  simp [Fin.le_def, wit_val]

private lemma wit_mod {k : ℕ} (i : Fin k) (t q r : ℕ) (hq : i.val + 1 = q * r)
    (hq1 : 1 ≤ q) (ht1 : 1 ≤ t) (htr : t ≤ r - 1) :
    ((wit i t).val + 1) % r = r - t := by
  have hqr : r ≤ q * r := Nat.le_mul_of_pos_left r (by omega)
  have hle : (wit i t).val + 1 = q * r - t := by
    rw [wit_val]; omega
  rw [hle]
  have h2 : q * r - t = (r - t) + (q - 1) * r := by
    rw [Nat.sub_mul, one_mul]
    omega
  rw [h2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

private lemma dIdx_mem {r k : ℕ} {i : Fin k} :
    i ∈ dIdx r k ↔ i.val < r ∨ ((i.val + 1) % r = 0 ∧ 2 * r ≤ i.val + 1) := by
  simp [dIdx]

theorem sepDiv_pow_le (r k : ℕ) (p : Fin k → ℕ) (hk : 0 < k) (hr : 2 ≤ r)
    (hmono : StrictAnti p) (hprime : ∀ i, (p i).Prime) :
    (∏ i ∈ dIdx r k, p i) ^ r ≤ (∏ i, p i) * p ⟨0, hk⟩ ^ (r * (r - 1)) := by
  have hanti : Antitone p := hmono.antitone
  have hp0 : ∀ i : Fin k, p i ≤ p ⟨0, hk⟩ :=
    fun i => hanti (by rw [Fin.le_def]; exact Nat.zero_le _)
  have hp1 : ∀ i : Fin k, 1 ≤ p i := fun i => (hprime i).one_le
  set D1 : Finset (Fin k) := (dIdx r k).filter (fun i => i.val < r) with hD1
  set D2 : Finset (Fin k) := (dIdx r k).filter (fun i => ¬ i.val < r) with hD2
  set C : Finset (Fin k) := (Finset.univ : Finset (Fin k)) \ dIdx r k with hC
  have hD2facts : ∀ i ∈ D2, ∃ q : ℕ, i.val + 1 = q * r ∧ 2 ≤ q := by
    intro i hi
    rw [hD2] at hi
    obtain ⟨hd, hge_r⟩ := Finset.mem_filter.mp hi
    rw [dIdx_mem] at hd
    rcases hd with h | ⟨hmod, hge⟩
    · omega
    · have hdiv : r ∣ i.val + 1 := Nat.dvd_of_mod_eq_zero hmod
      refine ⟨(i.val + 1) / r, (Nat.div_mul_cancel hdiv).symm, ?_⟩
      have h2 : 2 * r ≤ ((i.val + 1) / r) * r := by
        rw [Nat.div_mul_cancel hdiv]; exact hge
      exact Nat.le_of_mul_le_mul_right h2 (by omega)
  have hsplit : ∏ i ∈ dIdx r k, p i ^ (r - 1)
      = (∏ i ∈ D1, p i ^ (r - 1)) * (∏ i ∈ D2, p i ^ (r - 1)) := by
    rw [hD1, hD2]
    exact (Finset.prod_filter_mul_prod_filter_not (dIdx r k) (fun i : Fin k => i.val < r)
      (fun i => p i ^ (r - 1))).symm
  have hD1card : D1.card ≤ r := by
    rw [hD1]
    have hinj : Function.Injective (fun i : Fin k => i.val) := fun a b h => Fin.ext h
    calc ((dIdx r k).filter (fun i : Fin k => i.val < r)).card
        = (((dIdx r k).filter (fun i : Fin k => i.val < r)).image
            (fun i : Fin k => i.val)).card := (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (Finset.range r).card := by
          apply Finset.card_le_card
          intro x hx
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
      _ = r := Finset.card_range r
  have hD1bound : ∏ i ∈ D1, p i ^ (r - 1) ≤ p ⟨0, hk⟩ ^ (r * (r - 1)) := by
    calc ∏ i ∈ D1, p i ^ (r - 1)
        ≤ ∏ i ∈ D1, p ⟨0, hk⟩ ^ (r - 1) := by
          apply Finset.prod_le_prod₀ (fun i _ => by positivity)
          intro i _
          exact Nat.pow_le_pow_left (hp0 i) (r - 1)
      _ = (p ⟨0, hk⟩ ^ (r - 1)) ^ D1.card := Finset.prod_const _
      _ = p ⟨0, hk⟩ ^ ((r - 1) * D1.card) := by rw [← pow_mul]
      _ ≤ p ⟨0, hk⟩ ^ ((r - 1) * r) :=
          Nat.pow_le_pow_right (hprime ⟨0, hk⟩).pos (Nat.mul_le_mul_left _ hD1card)
      _ = p ⟨0, hk⟩ ^ (r * (r - 1)) := by rw [Nat.mul_comm]
  have hstep1 : ∏ i ∈ D2, p i ^ (r - 1)
      ≤ ∏ i ∈ D2, ∏ t ∈ Finset.Icc 1 (r - 1), p (wit i t) := by
    apply Finset.prod_le_prod₀ (fun i _ => by positivity)
    intro i _
    calc p i ^ (r - 1) = ∏ _t ∈ Finset.Icc 1 (r - 1), p i := by
          have hc : (r - 1) + 1 - 1 = r - 1 := by omega
          rw [Finset.prod_const, Nat.card_Icc, hc]
      _ ≤ ∏ t ∈ Finset.Icc 1 (r - 1), p (wit i t) := by
          apply Finset.prod_le_prod₀ (fun t _ => by positivity)
          intro t _
          exact hanti (wit_le i t)
  have hstep2 : ∏ i ∈ D2, ∏ t ∈ Finset.Icc 1 (r - 1), p (wit i t)
      = ∏ s ∈ D2 ×ˢ (Finset.Icc 1 (r - 1)), p (wit s.1 s.2) := by
    rw [Finset.prod_product]
  have hWsub : (D2 ×ˢ (Finset.Icc 1 (r - 1))).image (fun s : Fin k × ℕ => wit s.1 s.2) ⊆ C := by
    intro u hu
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hs1, hs2⟩ := Finset.mem_product.mp hs
    obtain ⟨q, hq, hq2⟩ := hD2facts s.1 hs1
    have ht1 : 1 ≤ s.2 := (Finset.mem_Icc.mp hs2).1
    have htr : s.2 ≤ r - 1 := (Finset.mem_Icc.mp hs2).2
    rw [hC, Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hmem
    rw [dIdx_mem] at hmem
    have hmod := wit_mod s.1 s.2 q r hq (by omega) ht1 htr
    have hge : r ≤ (wit s.1 s.2).val := by
      have hge2 : 2 * r ≤ s.1.val + 1 := by rw [hq]; exact Nat.mul_le_mul_right r hq2
      rw [wit_val]; omega
    rcases hmem with h | ⟨h0, -⟩
    · omega
    · omega
  have hinj : Set.InjOn (fun s : Fin k × ℕ => wit s.1 s.2)
      ↑(D2 ×ˢ (Finset.Icc 1 (r - 1))) := by
    intro s hs s' hs' heq
    obtain ⟨hs1, hs2⟩ := Finset.mem_product.mp hs
    obtain ⟨hs1', hs2'⟩ := Finset.mem_product.mp hs'
    obtain ⟨q, hq, hq2⟩ := hD2facts s.1 hs1
    obtain ⟨q', hq', hq2'⟩ := hD2facts s'.1 hs1'
    have ht1 : 1 ≤ s.2 := (Finset.mem_Icc.mp hs2).1
    have htr : s.2 ≤ r - 1 := (Finset.mem_Icc.mp hs2).2
    have ht1' : 1 ≤ s'.2 := (Finset.mem_Icc.mp hs2').1
    have htr' : s'.2 ≤ r - 1 := (Finset.mem_Icc.mp hs2').2
    have hm1 := wit_mod s.1 s.2 q r hq (by omega) ht1 htr
    have hm2 := wit_mod s'.1 s'.2 q' r hq' (by omega) ht1' htr'
    have hvv : (wit s.1 s.2).val = (wit s'.1 s'.2).val := congrArg Fin.val heq
    have ht_eq : s.2 = s'.2 := by
      rw [hvv] at hm1
      omega
    have hi_eq : s.1 = s'.1 := by
      apply Fin.ext
      have hge2 : 2 * r ≤ s.1.val + 1 := by rw [hq]; exact Nat.mul_le_mul_right r hq2
      have hge2' : 2 * r ≤ s'.1.val + 1 := by rw [hq']; exact Nat.mul_le_mul_right r hq2'
      simp only [wit_val] at hvv
      omega
    exact Prod.ext hi_eq ht_eq
  have hstep3 : ∏ s ∈ D2 ×ˢ (Finset.Icc 1 (r - 1)), p (wit s.1 s.2) ≤ ∏ u ∈ C, p u := by
    rw [← Finset.prod_image hinj]
    exact Finset.prod_le_prod_of_subset_of_one_le₀ hWsub (fun u _ => by positivity)
      (fun u _ _ => hp1 u)
  have hD2bound : ∏ i ∈ D2, p i ^ (r - 1) ≤ ∏ i ∈ C, p i :=
    calc ∏ i ∈ D2, p i ^ (r - 1)
        ≤ ∏ i ∈ D2, ∏ t ∈ Finset.Icc 1 (r - 1), p (wit i t) := hstep1
      _ = ∏ s ∈ D2 ×ˢ (Finset.Icc 1 (r - 1)), p (wit s.1 s.2) := hstep2
      _ ≤ ∏ u ∈ C, p u := hstep3
  have hmain : (∏ i ∈ dIdx r k, p i) ^ (r - 1)
      ≤ p ⟨0, hk⟩ ^ (r * (r - 1)) * ∏ i ∈ C, p i := by
    calc (∏ i ∈ dIdx r k, p i) ^ (r - 1)
        = ∏ i ∈ dIdx r k, p i ^ (r - 1) := (Finset.prod_pow _ _ _).symm
      _ = (∏ i ∈ D1, p i ^ (r - 1)) * (∏ i ∈ D2, p i ^ (r - 1)) := hsplit
      _ ≤ p ⟨0, hk⟩ ^ (r * (r - 1)) * ∏ i ∈ C, p i :=
          mul_le_mul hD1bound hD2bound (by positivity) (by positivity)
  have hPC : (∏ i ∈ C, p i) * (∏ i ∈ dIdx r k, p i) = ∏ i, p i := by
    rw [hC]
    exact Finset.prod_sdiff (Finset.subset_univ _)
  have hpow : (∏ i ∈ dIdx r k, p i) ^ (r - 1) * ∏ i ∈ dIdx r k, p i
      = (∏ i ∈ dIdx r k, p i) ^ r := by
    have h1 : r - 1 + 1 = r := by omega
    calc (∏ i ∈ dIdx r k, p i) ^ (r - 1) * ∏ i ∈ dIdx r k, p i
        = (∏ i ∈ dIdx r k, p i) ^ (r - 1) * (∏ i ∈ dIdx r k, p i) ^ 1 := by rw [pow_one]
      _ = (∏ i ∈ dIdx r k, p i) ^ ((r - 1) + 1) :=
          (pow_add (∏ i ∈ dIdx r k, p i) (r - 1) 1).symm
      _ = (∏ i ∈ dIdx r k, p i) ^ r := by rw [h1]
  calc (∏ i ∈ dIdx r k, p i) ^ r
      = (∏ i ∈ dIdx r k, p i) ^ (r - 1) * ∏ i ∈ dIdx r k, p i := hpow.symm
    _ ≤ (p ⟨0, hk⟩ ^ (r * (r - 1)) * ∏ i ∈ C, p i) * ∏ i ∈ dIdx r k, p i :=
          mul_le_mul_left hmain (∏ i ∈ dIdx r k, p i)
    _ = p ⟨0, hk⟩ ^ (r * (r - 1)) * ((∏ i ∈ C, p i) * ∏ i ∈ dIdx r k, p i) :=
          mul_assoc _ _ _
    _ = p ⟨0, hk⟩ ^ (r * (r - 1)) * ∏ i, p i := by rw [hPC]
    _ = (∏ i, p i) * p ⟨0, hk⟩ ^ (r * (r - 1)) := mul_comm _ _

end Work.FIArea7
