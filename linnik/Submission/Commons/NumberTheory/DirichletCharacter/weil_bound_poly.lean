import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.irreducible_power_reduction
import Submission.Commons.NumberTheory.Stepanov.superelliptic_point_count
import Submission.Commons.NumberTheory.DirichletCharacter.weil_bound_of_point_count

namespace Commons.NumberTheory.DirichletCharacter

theorem weil_bound_poly (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (F : Polynomial (ZMod p)) (hF : F ≠ 0) (hd : 1 ≤ F.natDegree)
    (hnd : ∀ (c : ZMod p) (H : Polynomial (ZMod p)), F ≠ Polynomial.C c * H ^ orderOf χ) :
    ‖∑ x : ZMod p, χ (F.eval x)‖
      ≤ ((F.rootSet (AlgebraicClosure (ZMod p))).ncard : ℝ) * Real.sqrt (p : ℝ) := by
  have hm : 2 ≤ orderOf χ := by
    have h1 : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
    have h2 : 1 ≤ orderOf χ := orderOf_pos χ
    omega
  have hmne : orderOf χ ≠ 0 := by omega
  obtain ⟨e, G, c, he2, hedvd, hc0, hGmonic, hFG, hgcd, hIrr, hroot⟩ :=
    irreducible_power_reduction p (orderOf χ) hm F hF hd hnd
  have hgpos : 1 ≤ orderOf χ / e :=
    Nat.one_le_div_iff (by omega : 0 < e) |>.mpr (Nat.le_of_dvd (by omega : 0 < orderOf χ) hedvd)
  have hgne : orderOf χ / e ≠ 0 := by omega
  have hge : orderOf (χ ^ (orderOf χ / e)) = e := by
    rw [orderOf_pow, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hedvd)]
    exact Nat.div_div_self hedvd hmne
  have hχpow_ne : χ ^ (orderOf χ / e) ≠ 1 := by
    intro h; rw [h, orderOf_one] at hge; omega
  have hpt (x : ZMod p) : χ (F.eval x) = χ c * (χ ^ (orderOf χ / e)) (G.eval x) := by
    rw [hFG, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, map_mul, map_pow,
      MulChar.pow_apply' χ hgne]
  have hsum : (∑ x : ZMod p, χ (F.eval x))
      = χ c * ∑ x : ZMod p, (χ ^ (orderOf χ / e)) (G.eval x) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => hpt x)
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have horder_dvd : orderOf χ ∣ p - 1 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    ext a
    rw [MulChar.pow_apply']
    · rw [MulChar.one_apply (Units.isUnit a)]
      have hz : (a : ZMod p) ≠ 0 := Units.ne_zero a
      rw [← map_pow, ZMod.pow_card_sub_one_eq_one hz, map_one]
    · have : 2 ≤ p := (Fact.out : p.Prime).two_le
      omega
  have hedvd' : e ∣ Fintype.card (ZMod p) - 1 := by
    rw [hcard]; exact dvd_trans hedvd horder_dvd
  have hG0 : G ≠ 0 := hGmonic.ne_zero
  have hdG : 1 ≤ G.natDegree := by
    have hdeg : (Polynomial.C c * G ^ (orderOf χ / e)).natDegree
        = (orderOf χ / e) * G.natDegree := by
      rw [Polynomial.natDegree_C_mul hc0, Polynomial.natDegree_pow]
    have : 1 ≤ (Polynomial.C c * G ^ (orderOf χ / e)).natDegree := by rw [← hFG]; exact hd
    rw [hdeg] at this
    nlinarith [this, hgpos]
  have hpc : ∃ C : ℝ, 0 < C ∧ ∀ {F : Type} [Field F] [Fintype F], e ∣ Fintype.card F - 1 →
      ∀ (f : Polynomial F), f ≠ 0 → f.natDegree ≤ G.natDegree → f.Monic →
      Irreducible (Polynomial.X ^ e - Polynomial.C f) →
      (({p : F × F | p.2 ^ e = f.eval p.1}.ncard : ℝ) ≤
        (Fintype.card F : ℝ) + C * Real.sqrt ((Fintype.card F : ℕ) : ℝ)) :=
    Commons.NumberTheory.Stepanov.superelliptic_point_count e G.natDegree he2 hdG
  have hmagic := weil_bound_of_point_count e G.natDegree he2 hdG hpc
  obtain ⟨C, hCpos, hC⟩ := hmagic
  have key := hC (F := ZMod p) hedvd' (χ ^ (orderOf χ / e)) hχpow_ne hge G hG0 (le_refl _) hGmonic hIrr
  have hnormc : ‖χ c‖ = 1 := by
    have hpow1 : (χ c) ^ orderOf χ = 1 := by
      have h1 : (χ ^ orderOf χ) c = 1 := by
        rw [pow_orderOf_eq_one, MulChar.one_apply (isUnit_iff_ne_zero.mpr hc0)]
      rwa [MulChar.pow_apply' χ hmne] at h1
    have h2 : ‖χ c‖ ^ orderOf χ = 1 := by rw [← norm_pow, hpow1, norm_one]
    have h3 : ‖χ c‖ ≤ 1 := DirichletCharacter.norm_le_one χ c
    have hx1 : 1 ≤ ‖χ c‖ := by
      by_contra hlt
      push Not at hlt
      have hpow_lt : ‖χ c‖ ^ orderOf χ < 1 :=
        pow_lt_one₀ (norm_nonneg _) hlt hmne
      rw [h2] at hpow_lt
      exact lt_irrefl _ hpow_lt
    exact le_antisymm h3 hx1
  rw [hsum, norm_mul, hnormc, one_mul]
  calc ‖∑ x : ZMod p, (χ ^ (orderOf χ / e)) (G.eval x)‖
      ≤ ((G.rootSet (AlgebraicClosure (ZMod p))).ncard : ℝ) * Real.sqrt ((Fintype.card (ZMod p) : ℕ) : ℝ) := key
    _ = ((F.rootSet (AlgebraicClosure (ZMod p))).ncard : ℝ) * Real.sqrt (p : ℝ) := by
        rw [hroot, hcard]

end Commons.NumberTheory.DirichletCharacter
