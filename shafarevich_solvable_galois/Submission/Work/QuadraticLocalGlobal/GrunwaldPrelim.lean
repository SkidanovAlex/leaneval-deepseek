/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Preliminary lemmas for Grünwald's theorem in degree two

Small structural lemmas used in `Work.QuadraticLocalGlobal.grunwald_degree_two_with_sign`:

* `SameSquare` is an equivalence relation on nonzero `p`-adic numbers;
* divisibility/multiplicativity bookkeeping for `padicVal` and `legendreOf`;
* the `legendreOf` of an integral unit depends only on its residue class mod `p`;
* the `2`-adic square criterion in the `toZModPow 3` form;
* a Chinese-remainder statement for a finite family of pairwise coprime moduli, giving a
  *positive* integer with prescribed residues.
-/
import Mathlib
import Submission.Work.QuadraticLocalGlobal.Defs
import Submission.Work.QuadraticLocalGlobal.isSquare_padic_rat_iff
import Submission.Work.QuadraticLocalGlobal.isSquare_padic_two_rat_iff
import Submission.Work.QuadraticLocalGlobal.toZModPow_intCast
import Submission.Work.HilbertSymbol.legendreOf_intUnit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Classical

namespace Work.QuadraticLocalGlobal

open Work.HilbertSymbol

/-! ## `SameSquare` -/

theorem sameSquare_symm {p : ℕ} [Fact p.Prime] {d c : ℚ_[p]} (hd : d ≠ 0) (hc : c ≠ 0)
    (h : SameSquare d c) : SameSquare c d := by
  obtain ⟨z, hz⟩ := h
  have hz0 : z ≠ 0 := by
    intro h0
    exact hc (by rw [← hz, h0]; ring)
  refine ⟨z⁻¹, ?_⟩
  rw [← hz, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hz0, one_pow, one_mul]

theorem sameSquare_trans {p : ℕ} [Fact p.Prime] {d c e : ℚ_[p]}
    (h1 : SameSquare d c) (h2 : SameSquare c e) : SameSquare d e := by
  obtain ⟨z, hz⟩ := h1
  obtain ⟨w, hw⟩ := h2
  exact ⟨w * z, by rw [mul_pow, mul_assoc, hz, hw]⟩

/-! ## `padicVal` of inverses and quotients -/

theorem padicVal_inv (p : ℕ) [Fact p.Prime] (a : ℚˣ) : padicVal p a⁻¹ = -padicVal p a := by
  simp only [padicVal, Units.val_inv_eq_inv_val]
  rw [padicValRat.inv]

theorem padicVal_div (p : ℕ) [Fact p.Prime] (a b : ℚˣ) :
    padicVal p (a / b) = padicVal p a - padicVal p b := by
  rw [div_eq_mul_inv, padicVal_mul, padicVal_inv]
  ring

theorem padicVal_neg_one (p : ℕ) [Fact p.Prime] : padicVal p (-1 : ℚˣ) = 0 := by
  rw [show (-1 : ℚˣ) = -(1 : ℚˣ) by rfl, padicVal_neg, padicVal_one]

/-! ## `legendreOf` of inverses, quotients and integral units -/

theorem intUnitOf_mul_self_grunwald (n : ℤ) : intUnitOf n * intUnitOf n = 1 := by
  rw [intUnitOf]; split_ifs <;> simp

/-- Any value of `legendreOf` is a sign, hence idempotent. -/
theorem legendreOf_mul_self {p : ℕ} [Fact p.Prime] (a : ℚˣ) :
    legendreOf p a * legendreOf p a = 1 := by
  simp only [legendreOf, legendreUnit, quadCharUnit]
  exact intUnitOf_mul_self_grunwald _

theorem legendreOf_inv {p : ℕ} [Fact p.Prime] (a : ℚˣ) :
    legendreOf p a⁻¹ = legendreOf p a := by
  have h : legendreOf p a * legendreOf p a⁻¹ = 1 := by
    rw [← legendreOf_mul, mul_inv_cancel, legendreOf_one]
  have h1 : legendreOf p a⁻¹ = (legendreOf p a)⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [h1, inv_eq_of_mul_eq_one_right (legendreOf_mul_self (p := p) a)]

theorem legendreOf_div {p : ℕ} [Fact p.Prime] (a b : ℚˣ) :
    legendreOf p (a / b) = legendreOf p a * legendreOf p b := by
  rw [div_eq_mul_inv, legendreOf_mul, legendreOf_inv]

/-- For an odd prime `p`, the `legendreOf p` of an integral unit depends only on the residue
class of the integer modulo `p`. -/
theorem legendreOf_intUnit_eq_of_modEq {p : ℕ} [Fact p.Prime] {m m' : ℤ}
    (hm : m ≠ 0) (hm' : m' ≠ 0) (h : m ≡ m' [ZMOD p]) (hcop : ¬ (p : ℤ) ∣ m) :
    legendreOf p (intUnit m hm) = legendreOf p (intUnit m' hm') := by
  have hcop' : ¬ (p : ℤ) ∣ m' := by
    intro h'
    have hdvd : (p : ℤ) ∣ m' - m := Int.modEq_iff_dvd.mp h
    exact hcop (by simpa using dvd_sub h' hdvd)
  rw [legendreOf_intUnit hm hcop, legendreOf_intUnit hm' hcop']
  congr 1
  simp only [legendreSym]
  rw [show (m : ZMod p) = (m' : ZMod p) from (ZMod.intCast_eq_intCast_iff m m' p).mpr h]

/-! ## The `2`-adic square criterion in `toZModPow 3` form -/

theorem isSquare_padic_two_rat_iff' (x : ℚˣ) : IsSquare ((x : ℚ_[2])) ↔
    Even (padicVal 2 x) ∧ PadicInt.toZModPow 3 ((unitPart 2 x : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
  rw [isSquare_padic_two_rat_iff, ← toZModPow_three_eq_one_iff (unitPart 2 x)]

/-- For an odd integer `m`, the reduction mod `8` of the `2`-adic unit part of `m` is `m`. -/
theorem toZModPow_three_unitPart_two_intUnit {m : ℤ} (hm : m ≠ 0) (hodd : ¬ (2 : ℤ) ∣ m) :
    PadicInt.toZModPow 3 ((unitPart 2 (intUnit m hm) : ℤ_[2]ˣ) : ℤ_[2]) =
      ((m : ℤ) : ZMod (2 ^ 3)) := by
  rw [unitPart_intUnit_eq hm hodd, toZModPow_intCast]

/-! ## Chinese remainder for finitely many pairwise coprime moduli -/

/-- **Chinese remainder theorem**, integer form with positivity: for finitely many pairwise
coprime moduli `m i > 1` and arbitrary residues `r i : ℤ`, there is a *positive* integer `g`
with `g ≡ r i [ZMOD m i]` for every `i`. -/
theorem exists_pos_int_modEq_finset {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hm : ∀ i, 1 < m i) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j)) (r : ι → ℤ) :
    ∃ g : ℤ, 0 < g ∧ ∀ i, g ≡ r i [ZMOD (m i : ℤ)] := by
  classical
  set a : ι → ℕ := fun i => (r i % (m i : ℤ)).toNat with ha
  have ha_cast : ∀ i, (a i : ℤ) = r i % (m i : ℤ) := by
    intro i
    rw [ha]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by have := hm i; positivity))
  have hne : ∀ i ∈ (Finset.univ : Finset ι), m i ≠ 0 := by
    intro i _
    have := hm i
    omega
  have hpair : Set.Pairwise (↑(Finset.univ : Finset ι)) (Function.onFun Nat.Coprime m) := by
    intro i _ j _ hij
    exact hcop i j hij
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset a m (Finset.univ : Finset ι) hne hpair
  have hMpos : 0 < ∏ i, m i := Finset.prod_pos fun i _ => by have := hm i; omega
  refine ⟨(k : ℤ) + ((∏ i, m i : ℕ) : ℤ), ?_, fun i => ?_⟩
  · have hMi : (0 : ℤ) < ((∏ i, m i : ℕ) : ℤ) := by exact_mod_cast hMpos
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    linarith
  · have hkai : (k : ℤ) ≡ (a i : ℤ) [ZMOD (m i : ℤ)] :=
      Int.natCast_modEq_iff.mpr (hk i (Finset.mem_univ i))
    have hair : (a i : ℤ) ≡ r i [ZMOD (m i : ℤ)] := by
      rw [ha_cast i]; exact Int.mod_modEq (r i) (m i : ℤ)
    have hkr : (k : ℤ) ≡ r i [ZMOD (m i : ℤ)] := hkai.trans hair
    have hMg : (m i : ℤ) ∣ ((∏ i, m i : ℕ) : ℤ) := by
      exact_mod_cast Finset.dvd_prod_of_mem m (Finset.mem_univ i)
    have hgk : ((k : ℤ) + ((∏ i, m i : ℕ) : ℤ)) ≡ (k : ℤ) [ZMOD (m i : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      have : (k : ℤ) - ((k : ℤ) + ((∏ i, m i : ℕ) : ℤ)) = -((∏ i, m i : ℕ) : ℤ) := by ring
      rw [this]
      exact dvd_neg.mpr hMg
    exact hgk.trans hkr

end Work.QuadraticLocalGlobal
