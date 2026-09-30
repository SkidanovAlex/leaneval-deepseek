import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.N8.walk_products_close

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `walk_products_close_gen`: products of primes around a closed walk are close

Generalisation of `Work.N8.walk_products_close` where the geometric error bound
`100 * L` is replaced by an arbitrary `c * L` with `0 ≤ c`.

Along a closed walk `j ↦ j + 1 (mod m)` the vertices `x j ≥ D` satisfy the geometric
relation `x j ≈ (p₂ j / p₁ j) * x (j+1)` with error at most `c * L`, where the primes
`p₁ j, p₂ j` lie in `[P, 2P]`.  Multiplying all the relations around the cycle shows
that the ratio `∏ p₂ j / ∏ p₁ j` is within `1 - (1 + cL/D)^{-m} ≤ m * cL/D` of `1`;
combined with the constraints `P ≤ p₁ j` and `p₂ j ≤ 2P` this bounds the difference of
the two products, and the same two constraints give the trivial bound when `cL/D ≥ 1`.
-/

namespace Work.N8

open Finset

theorem walk_products_close_gen (m : ℕ) (hm : 1 ≤ m) (P L D c : ℝ) (hc : 0 ≤ c) (x : Fin m → ℝ)
    (p₁ p₂ : Fin m → ℕ)
    (hD : 0 < D) (hL : 0 < L) (hP : 1 ≤ P) (hx : ∀ j, D ≤ x j)
    (hp : ∀ j, Work.BMF.IsPrimeIn P (2 * P) (p₁ j) ∧ Work.BMF.IsPrimeIn P (2 * P) (p₂ j))
    (hgeo : ∀ j : Fin m, |x j - ((p₂ j : ℝ) / (p₁ j)) *
      x ⟨((j : ℕ) + 1) % m, Nat.mod_lt _ (by omega)⟩| ≤ c * L) :
    |(((Finset.univ.prod p₂ : ℕ)) : ℝ) - (((Finset.univ.prod p₁ : ℕ)) : ℝ)|
      ≤ (m : ℝ) * (2 * P) ^ m * (c * L / D) := by
  have hD0 : (0:ℝ) < D := hD
  have hP0 : (0:ℝ) < P := lt_of_lt_of_le zero_lt_one hP
  have hcL : (0:ℝ) ≤ c * L := mul_nonneg hc (le_of_lt hL)
  have hα0 : (0:ℝ) ≤ c * L / D := div_nonneg hcL (le_of_lt hD)
  have hxpos : ∀ j : Fin m, 0 < x j := fun j => lt_of_lt_of_le hD (hx j)
  have hxj : ∀ j : Fin m, x j ≠ 0 := fun j => ne_of_gt (hxpos j)
  have hp1ne : ∀ j : Fin m, (p₁ j : ℝ) ≠ 0 :=
    fun j => Nat.cast_ne_zero.mpr (ne_of_gt (hp j).1.1.pos)
  have hAcast : (((Finset.univ.prod p₂ : ℕ)) : ℝ) = ∏ j : Fin m, (p₂ j : ℝ) := by
    rw [Nat.cast_prod]
  have hBcast : (((Finset.univ.prod p₁ : ℕ)) : ℝ) = ∏ j : Fin m, (p₁ j : ℝ) := by
    rw [Nat.cast_prod]
  have hAbound : (((Finset.univ.prod p₂ : ℕ)) : ℝ) ≤ (2*P)^m := by
    rw [hAcast]
    calc ∏ j : Fin m, (p₂ j : ℝ) ≤ ∏ j : Fin m, (2*P) :=
          Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => (hp j).2.2.2)
      _ = (2*P)^m := by simp [Finset.prod_const, Fintype.card_fin]
  have hBbound : (((Finset.univ.prod p₁ : ℕ)) : ℝ) ≤ (2*P)^m := by
    rw [hBcast]
    calc ∏ j : Fin m, (p₁ j : ℝ) ≤ ∏ j : Fin m, (2*P) :=
          Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => (hp j).1.2.2)
      _ = (2*P)^m := by simp [Finset.prod_const, Fintype.card_fin]
  have hApos : (0:ℝ) < (((Finset.univ.prod p₂ : ℕ)) : ℝ) := by
    rw [hAcast]; exact Finset.prod_pos (fun j _ => Nat.cast_pos.mpr (hp j).2.1.pos)
  have hBpos : (0:ℝ) < (((Finset.univ.prod p₁ : ℕ)) : ℝ) := by
    rw [hBcast]; exact Finset.prod_pos (fun j _ => Nat.cast_pos.mpr (hp j).1.1.pos)
  by_cases hα1 : 1 ≤ c * L / D
  · have h2P : (0:ℝ) ≤ (2*P)^m := by positivity
    have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have hfin : |(((Finset.univ.prod p₂ : ℕ)) : ℝ) - (((Finset.univ.prod p₁ : ℕ)) : ℝ)| ≤ (2*P)^m := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [hAbound, hBbound, hApos, hBpos]
    have hstep : (1:ℝ) ≤ (m:ℝ) * (c*L/D) := by nlinarith [hm1, hα1]
    calc |(((Finset.univ.prod p₂ : ℕ)) : ℝ) - (((Finset.univ.prod p₁ : ℕ)) : ℝ)| ≤ (2*P)^m := hfin
      _ ≤ (m:ℝ) * (2*P)^m * (c*L/D) := by
          have := mul_le_mul_of_nonneg_left hstep h2P
          nlinarith [this]
  · have hαlt : c * L / D < 1 := lt_of_not_ge hα1
    let r : Fin m → ℝ := fun j => (p₂ j : ℝ) / (p₁ j : ℝ)
    let y : Fin m → ℝ := fun j => x j - r j * x ⟨((j:ℕ)+1) % m, Nat.mod_lt _ (by omega)⟩
    let w : Fin m → ℝ := fun j => y j / x j
    have hy : ∀ j : Fin m, |y j| ≤ c * L := fun j => hgeo j
    have hσprod : (∏ j : Fin m, x ⟨((j : ℕ) + 1) % m, Nat.mod_lt _ (by omega)⟩) = ∏ j : Fin m, x j :=
      walk_products_close_shift hm x
    have hr : ∀ j : Fin m, r j = (x j - y j) / x ⟨((j:ℕ)+1) % m, Nat.mod_lt _ (by omega)⟩ := by
      intro j
      rw [eq_div_iff (ne_of_gt (hxpos _))]
      dsimp only [y]
      ring
    have hnum : ∀ j : Fin m, x j - y j = x j * (1 - w j) := by
      intro j
      have h1 : x j * (1 - w j) = x j - y j := by
        dsimp only [w]
        rw [mul_sub, mul_one, mul_div_assoc', mul_div_cancel_left₀ (y j) (hxj j)]
      exact h1.symm
    have hxprod : (∏ j : Fin m, x j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hxj j)
    have hR : (∏ j : Fin m, r j) = ∏ j : Fin m, (1 - w j) := by
      calc ∏ j : Fin m, r j
          = ∏ j : Fin m, (x j - y j) / x ⟨((j:ℕ)+1) % m, Nat.mod_lt _ (by omega)⟩ :=
              Finset.prod_congr rfl (fun j _ => hr j)
        _ = (∏ j : Fin m, (x j - y j)) / (∏ j : Fin m, x ⟨((j:ℕ)+1) % m, Nat.mod_lt _ (by omega)⟩) :=
              Finset.prod_div_distrib _ _
        _ = (∏ j : Fin m, x j * (1 - w j)) / (∏ j : Fin m, x j) := by
              rw [Finset.prod_congr rfl (fun j _ => hnum j), hσprod]
        _ = ((∏ j : Fin m, x j) * (∏ j : Fin m, (1 - w j))) / (∏ j : Fin m, x j) := by
              rw [Finset.prod_mul_distrib]
        _ = ∏ j : Fin m, (1 - w j) := by
              rw [mul_div_cancel_left₀ _ hxprod]
    have hA_eq : (((Finset.univ.prod p₂ : ℕ)) : ℝ) =
        (∏ j : Fin m, r j) * (((Finset.univ.prod p₁ : ℕ)) : ℝ) := by
      rw [hAcast, hBcast]
      rw [show (∏ j : Fin m, (p₂ j : ℝ)) = ∏ j : Fin m, r j * (p₁ j : ℝ) from
        Finset.prod_congr rfl (fun j _ => by
          dsimp only [r]
          rw [div_mul_eq_mul_div, mul_div_cancel_right₀ _ (hp1ne j)])]
      rw [Finset.prod_mul_distrib]
    have hAW : (((Finset.univ.prod p₂ : ℕ)) : ℝ) =
        (((Finset.univ.prod p₁ : ℕ)) : ℝ) * ∏ j : Fin m, (1 - w j) := by
      rw [hA_eq, hR]; ring
    have hw_le : ∀ j : Fin m, |w j| ≤ c * L / D := by
      intro j
      dsimp only [w]
      rw [abs_div, abs_of_pos (hxpos j)]
      have h1 : |y j| / x j ≤ c * L / x j :=
        div_le_div_of_nonneg_right (hy j) (le_of_lt (hxpos j))
      have h2 : c * L / x j ≤ c * L / D :=
        div_le_div_of_nonneg_left hcL hD0 (hx j)
      linarith
    have hw_low : ∀ j : Fin m, 1 - c * L / D ≤ 1 - w j := fun j => by
      have := (abs_le.mp (hw_le j)).2; linarith
    have hw_up : ∀ j : Fin m, 1 - w j ≤ 1 + c * L / D := fun j => by
      have := (abs_le.mp (hw_le j)).1; linarith
    have hWlow : (1 - c*L/D)^m ≤ ∏ j : Fin m, (1 - w j) := by
      have h := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : Fin m => 1 - c*L/D)
          (g := fun j : Fin m => 1 - w j) (fun j _ => by linarith) (fun j _ => hw_low j)
      simpa [Finset.prod_const, Fintype.card_fin] using h
    have hWinc : 1 - (m:ℝ) * (c*L/D) ≤ ∏ j : Fin m, (1 - w j) := by
      have h := one_add_mul_le_pow (a := -(c*L/D)) (by linarith : -2 ≤ -(c*L/D)) m
      have hbase : (1:ℝ) + -(c*L/D) = 1 - c*L/D := by ring
      rw [hbase] at h
      have hlhs : (1:ℝ) + (m:ℝ) * (-(c*L/D)) = 1 - (m:ℝ) * (c*L/D) := by ring
      linarith [h, hlhs, hWlow]
    have hWinvg : ((1 + c*L/D)^m)⁻¹ ≤ (∏ j : Fin m, (1 - w j))⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      have h := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : Fin m => (1 + c*L/D)⁻¹)
          (g := fun j : Fin m => (1 - w j)⁻¹) (fun j _ => inv_nonneg.mpr (by linarith [hα0]))
          (fun j _ => by
            rw [inv_le_inv₀ (by linarith [hα0]) (by linarith [hw_low j])]
            exact hw_up j)
      simpa [Finset.prod_const, Fintype.card_fin] using h
    have hWInv : 1 - (m:ℝ) * (c*L/D) ≤ (∏ j : Fin m, (1 - w j))⁻¹ :=
      le_trans (walk_products_close_inv_pow_ge (c*L/D) hα0 m) hWinvg
    have hWeq : (∏ j : Fin m, (1 - w j)) =
        (((Finset.univ.prod p₂ : ℕ)) : ℝ) * (((Finset.univ.prod p₁ : ℕ)) : ℝ)⁻¹ := by
      rw [← div_eq_mul_inv, eq_div_iff (ne_of_gt hBpos), hAW]; ring
    rcases le_total (((Finset.univ.prod p₂ : ℕ)) : ℝ) (((Finset.univ.prod p₁ : ℕ)) : ℝ) with hAB | hBA
    · have hWle1 : (∏ j : Fin m, (1 - w j)) ≤ 1 := by
        rw [hWeq, ← mul_inv_cancel₀ (ne_of_gt hBpos)]
        exact mul_le_mul_of_nonneg_right hAB (inv_nonneg.mpr (le_of_lt hBpos))
      have habs : |(((Finset.univ.prod p₂ : ℕ)) : ℝ) - (((Finset.univ.prod p₁ : ℕ)) : ℝ)|
          = (((Finset.univ.prod p₁ : ℕ)) : ℝ) - (((Finset.univ.prod p₂ : ℕ)) : ℝ) := by
        rw [abs_of_nonpos (show (((Finset.univ.prod p₂ : ℕ)) : ℝ) - (((Finset.univ.prod p₁ : ℕ)) : ℝ) ≤ 0 by linarith)]
        ring
      have h1 : (((Finset.univ.prod p₁ : ℕ)) : ℝ) - (((Finset.univ.prod p₂ : ℕ)) : ℝ)
          = (((Finset.univ.prod p₁ : ℕ)) : ℝ) * (1 - ∏ j : Fin m, (1 - w j)) := by
        rw [hAW]; ring
      have hWmα : 1 - ∏ j : Fin m, (1 - w j) ≤ (m:ℝ) * (c*L/D) := by linarith [hWinc]
      calc |(((Finset.univ.prod p₂ : ℕ)) : ℝ) - (((Finset.univ.prod p₁ : ℕ)) : ℝ)|
          = (((Finset.univ.prod p₁ : ℕ)) : ℝ) * (1 - ∏ j : Fin m, (1 - w j)) := by rw [habs, h1]
        _ ≤ (2*P)^m * (1 - ∏ j : Fin m, (1 - w j)) :=
              mul_le_mul_of_nonneg_right hBbound (by linarith [hWle1])
        _ ≤ (2*P)^m * ((m:ℝ) * (c*L/D)) :=
              mul_le_mul_of_nonneg_left hWmα (by positivity)
        _ = (m:ℝ) * (2*P)^m * (c*L/D) := by ring
    · have hWge1 : 1 ≤ ∏ j : Fin m, (1 - w j) := by
        rw [hWeq, ← mul_inv_cancel₀ (ne_of_gt hBpos)]
        exact mul_le_mul_of_nonneg_right hBA (inv_nonneg.mpr (le_of_lt hBpos))
      have hWpos : 0 < ∏ j : Fin m, (1 - w j) := lt_of_lt_of_le zero_lt_one hWge1
      have hBeq : (((Finset.univ.prod p₁ : ℕ)) : ℝ) =
          (((Finset.univ.prod p₂ : ℕ)) : ℝ) * (∏ j : Fin m, (1 - w j))⁻¹ := by
        rw [hAW, mul_assoc, mul_inv_cancel₀ (ne_of_gt hWpos), mul_one]
      have habs : |(((Finset.univ.prod p₂ : ℕ)) : ℝ) - (((Finset.univ.prod p₁ : ℕ)) : ℝ)|
          = (((Finset.univ.prod p₂ : ℕ)) : ℝ) - (((Finset.univ.prod p₁ : ℕ)) : ℝ) :=
        abs_of_nonneg (by linarith)
      have h1 : (((Finset.univ.prod p₂ : ℕ)) : ℝ) - (((Finset.univ.prod p₁ : ℕ)) : ℝ)
          = (((Finset.univ.prod p₂ : ℕ)) : ℝ) * (1 - (∏ j : Fin m, (1 - w j))⁻¹) := by
        rw [hBeq]; ring
      have hWinv1 : (∏ j : Fin m, (1 - w j))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hWge1
      have hWmα : 1 - (∏ j : Fin m, (1 - w j))⁻¹ ≤ (m:ℝ) * (c*L/D) := by linarith [hWInv]
      calc |(((Finset.univ.prod p₂ : ℕ)) : ℝ) - (((Finset.univ.prod p₁ : ℕ)) : ℝ)|
          = (((Finset.univ.prod p₂ : ℕ)) : ℝ) * (1 - (∏ j : Fin m, (1 - w j))⁻¹) := by rw [habs, h1]
        _ ≤ (2*P)^m * (1 - (∏ j : Fin m, (1 - w j))⁻¹) :=
              mul_le_mul_of_nonneg_right hAbound (by linarith [hWinv1])
        _ ≤ (2*P)^m * ((m:ℝ) * (c*L/D)) :=
              mul_le_mul_of_nonneg_left hWmα (by positivity)
        _ = (m:ℝ) * (2*P)^m * (c*L/D) := by ring

end Work.N8
