import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.split_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

/-- Arithmetic core: for `r ≥ 2`, `d ≥ 1` and `σ_i ≥ 1/d`, the auxiliary degree
`D_j = ⌊D/(rdσ_j)⌋` (`Defs.pDj`) is at least `1`. -/
private lemma one_le_pDj_arith {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ i, 1 / (d : ℝ) ≤ σ i) (j : Fin r) : 1 ≤ pDj r d σ j := by
  have hr1 : 1 ≤ r := by omega
  have hrm : r - 1 + 1 = r := Nat.sub_add_cancel hr1
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show (0 : ℕ) < r by omega)
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show (0 : ℕ) < d by omega)
  have hσj : (0 : ℝ) < σ j := by
    have h1 : (0 : ℝ) < 1 / (d : ℝ) := one_div_pos.mpr hdR
    linarith [hσ j]
  -- power identities
  have hpr : (r : ℝ) ^ r = (r : ℝ) ^ (r - 1) * (r : ℝ) := by
    have h := pow_succ (r : ℝ) (r - 1)
    rwa [hrm] at h
  have hpd : (d : ℝ) ^ (r + 1) = (d : ℝ) ^ (r - 1) * (d : ℝ) * (d : ℝ) := by
    have h : (d : ℝ) ^ (r + 1) = (d : ℝ) ^ r * (d : ℝ) := pow_succ _ _
    have h2 : (d : ℝ) ^ r = (d : ℝ) ^ (r - 1) * (d : ℝ) := by
      have hh := pow_succ (d : ℝ) (r - 1)
      rwa [hrm] at hh
    rw [h2] at h
    rw [h]
  -- the complementary product and the logarithm, as local notations
  set Q : ℝ := ∏ i ∈ Finset.univ.erase j, σ i with hQ
  set L : ℝ := Real.log (2 * (r : ℝ) * (d : ℝ)) with hL
  have hprod : ∏ i : Fin r, σ i = σ j * Q := by
    have h := Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ j) σ
    rw [Finset.sdiff_singleton_eq_erase] at h
    simpa [hQ] using h
  have hcard : (Finset.univ.erase j).card = r - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  have hQlow : (1 / (d : ℝ)) ^ (r - 1) ≤ Q := by
    have h := prod_le_prod_of_nonneg (s := Finset.univ.erase j)
      (f := fun _ : Fin r => 1 / (d : ℝ)) (g := σ)
      (fun _ _ => le_of_lt (one_div_pos.mpr hdR)) (fun i _ => hσ i)
    rw [Finset.prod_const, hcard, ← hQ] at h
    exact h
  -- first factor
  have hfac1 : 1 ≤ 2 * (r : ℝ) ^ (r - 1) * (32 : ℝ) ^ (r + 1) * (d : ℝ) * L := by
    rw [hL]
    have hb : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    have h1 : (1 : ℝ) ≤ (r : ℝ) ^ (r - 1) := one_le_pow₀ hb
    have h2 : (1 : ℝ) ≤ (32 : ℝ) ^ (r + 1) := one_le_pow₀ (by norm_num)
    have h3 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have h4 : (4 / 3 : ℝ) ≤ Real.log (2 * (r : ℝ) * (d : ℝ)) := log_2rd_ge hr hd
    have hp1 : (1 : ℝ) ≤ 2 * (r : ℝ) ^ (r - 1) := by linarith
    have hp4 : (1 : ℝ) ≤ Real.log (2 * (r : ℝ) * (d : ℝ)) := by linarith
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hp1 h2) h3) hp4
  -- second factor
  have hfac2 : 1 ≤ (d : ℝ) ^ (r - 1) * Q := by
    have hd_inv : (d : ℝ) * (1 / (d : ℝ)) = 1 := by
      rw [mul_one_div, div_self (ne_of_gt hdR)]
    calc (1 : ℝ) = ((d : ℝ) * (1 / (d : ℝ))) ^ (r - 1) := by rw [hd_inv, one_pow]
      _ = (d : ℝ) ^ (r - 1) * (1 / (d : ℝ)) ^ (r - 1) := by rw [mul_pow]
      _ ≤ (d : ℝ) ^ (r - 1) * Q :=
            mul_le_mul_of_nonneg_left hQlow (pow_nonneg (le_of_lt hdR) _)
  -- the algebraic identity
  have hident : pD r d σ / ((r : ℝ) * (d : ℝ) * σ j)
      = 2 * (r : ℝ) ^ (r - 1) * (32 : ℝ) ^ (r + 1) * (d : ℝ) * L
          * ((d : ℝ) ^ (r - 1) * Q) := by
    rw [div_eq_iff (ne_of_gt (mul_pos (mul_pos hrR hdR) hσj))]
    rw [pD, hprod, ← hL]
    rw [mul_pow, hpr, hpd]
    ring
  rw [pDj]
  apply Nat.le_floor
  rw [hident]
  simpa using one_le_mul_of_one_le_of_one_le hfac1 hfac2

lemma one_le_pDj {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (j : Fin r) : 1 ≤ pDj r (dK K) σ j := by
  have hd : 1 ≤ dK K := Module.finrank_pos
  exact one_le_pDj_arith H.hr hd σ (fun i => sigma_ge H i) j

end Work.BW
