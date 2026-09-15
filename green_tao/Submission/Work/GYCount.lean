import Submission.Work.GYAvg

/-!
# The residue counting and the elementary error estimate of Green–Tao §9

This file discharges the two remaining hypotheses of `boxAvgGood_of_main`
(`Submission/Work/GYAvg.lean`): the residue-class counting `hcount` (from the commons
`card_box_residue_close`, already packaged as `countBox_two_sided`) and the elementary error
bound `herr`.  After this file the box-average statement `BoxAvgGood` (Green–Tao
Proposition 9.5) is reduced to the single analytic input `hmain` (Green–Tao (ddr)).
-/

open Finset
open scoped BigOperators

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace BoxAvg

variable {m t : ℕ}

open Commons.NumberTheory.Sieve

section Elems

/-- `∏(1 + y) ≤ 1 + 2 ∑ y` when `0 ≤ y` and `∑ y ≤ 1/2`. -/
lemma prod_one_add_le {ι : Type*} (s : Finset ι) {y : ι → ℝ} (hy : ∀ i ∈ s, 0 ≤ y i)
    (hsum : ∑ i ∈ s, y i ≤ 1 / 2) :
    ∏ i ∈ s, (1 + y i) ≤ 1 + 2 * ∑ i ∈ s, y i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hya : 0 ≤ y a := hy a (Finset.mem_insert_self a s)
    have hys : ∀ i ∈ s, 0 ≤ y i := fun i hi => hy i (Finset.mem_insert_of_mem hi)
    have hs : ∑ i ∈ s, y i ≤ 1 / 2 := by
      have h := hsum; rw [Finset.sum_insert ha] at h; linarith
    have ih' := ih hys hs
    have h1 : (1 + y a) * ∏ i ∈ s, (1 + y i) ≤ (1 + y a) * (1 + 2 * ∑ i ∈ s, y i) :=
      mul_le_mul_of_nonneg_left ih' (by linarith)
    have key : 2 * y a * ∑ i ∈ s, y i ≤ y a := by
      have h2 : 2 * ∑ i ∈ s, y i ≤ 1 := by linarith
      calc 2 * y a * ∑ i ∈ s, y i = (2 * ∑ i ∈ s, y i) * y a := by ring
        _ ≤ 1 * y a := mul_le_mul_of_nonneg_right h2 hya
        _ = y a := by ring
    have h2 : (1 + y a) * (1 + 2 * ∑ i ∈ s, y i) ≤ 1 + 2 * (y a + ∑ i ∈ s, y i) := by
      nlinarith [key]
    linarith

/-- `1 - ∑ y ≤ ∏ (1 - y)` for `0 ≤ y ≤ 1`. -/
lemma prod_one_sub_ge {ι : Type*} (s : Finset ι) {y : ι → ℝ}
    (hy0 : ∀ i ∈ s, 0 ≤ y i) (hy1 : ∀ i ∈ s, y i ≤ 1) :
    1 - ∑ i ∈ s, y i ≤ ∏ i ∈ s, (1 - y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have ha0 : 0 ≤ y a := hy0 a (Finset.mem_insert_self a s)
    have ha1 : y a ≤ 1 := hy1 a (Finset.mem_insert_self a s)
    have hs0 : ∀ i ∈ s, 0 ≤ y i := fun i hi => hy0 i (Finset.mem_insert_of_mem hi)
    have hs1 : ∀ i ∈ s, y i ≤ 1 := fun i hi => hy1 i (Finset.mem_insert_of_mem hi)
    have ih' := ih hs0 hs1
    have hsum0 : 0 ≤ ∑ i ∈ s, y i := Finset.sum_nonneg hs0
    have h1 : (1 - y a) * (1 - ∑ i ∈ s, y i) ≤ (1 - y a) * ∏ i ∈ s, (1 - y i) :=
      mul_le_mul_of_nonneg_left ih' (by linarith)
    have h2 : 1 - (y a + ∑ i ∈ s, y i) ≤ (1 - y a) * (1 - ∑ i ∈ s, y i) := by
      nlinarith [mul_nonneg ha0 hsum0]
    linarith

end Elems

section Efac

/-- The side product is non-negative when the sides are. -/
lemma sideProd_nonneg (l r : Fin t → ℤ) (h : ∀ j, 0 ≤ ((r j - l j : ℤ) : ℝ)) :
    0 ≤ sideProd l r := by
  rw [sideProd]
  exact Finset.prod_nonneg (fun j _ => h j)

/-- `rho` is non-negative. -/
lemma rho_nonneg (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (d e : Fin m → ℕ) :
    0 ≤ rho W A b d e := by
  have h1 : (0 : ℝ) ≤ ((Sfin W A b d e).card : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ ((Ddd d e : ℝ)) ^ t := pow_nonneg (Nat.cast_nonneg _) t
  rw [rho]
  exact mul_nonneg (inv_nonneg.mpr h2) h1

/-- `rho` is at most one. -/
lemma rho_le_one (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (d e : Fin m → ℕ)
    (hd : ∀ i, 1 ≤ d i) (he : ∀ i, 1 ≤ e i) :
    rho W A b d e ≤ 1 := by
  have hD : 0 < Ddd d e := Ddd_pos d e hd he
  have hcard : ((Sfin W A b d e).card : ℝ) ≤ ((Ddd d e : ℝ)) ^ t := by
    have h1 : (Sfin W A b d e).card ≤ (Ddd d e) ^ t := by
      calc (Sfin W A b d e).card ≤ Fintype.card (Fin t → Fin (Ddd d e)) := by
            rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
        _ = (Ddd d e) ^ t := by simp [Fintype.card_fun]
    exact_mod_cast h1
  rw [rho, inv_mul_le_iff₀ (by positivity : (0:ℝ) < ((Ddd d e : ℝ)) ^ t)]
  simpa using hcard

/-- Rewriting `Efac` as a difference of products of `1 ± D/N_j`. -/
lemma Efac_eq (d e : Fin m → ℕ) (l r : Fin t → ℤ)
    (hD : ((Ddd d e : ℝ)) ≠ 0) (hN : ∀ j, ((r j - l j : ℤ) : ℝ) ≠ 0) :
    Efac d e l r
      = (∏ j, (1 + (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ)))
        - (∏ j, (1 - (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ))) := by
  have h1 : ∀ j, ((r j - l j : ℤ) : ℝ) / (Ddd d e : ℝ) + 1
      = (1 + (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ))
        * (((r j - l j : ℤ) : ℝ) / (Ddd d e : ℝ)) := by
    intro j; have := hN j; field_simp
  have h2 : ∀ j, ((r j - l j : ℤ) : ℝ) / (Ddd d e : ℝ) - 1
      = (1 - (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ))
        * (((r j - l j : ℤ) : ℝ) / (Ddd d e : ℝ)) := by
    intro j; have := hN j; field_simp
  have hP : (∏ j, (((r j - l j : ℤ) : ℝ) / (Ddd d e : ℝ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => div_ne_zero (hN j) hD)
  rw [Efac, Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_congr rfl (fun j _ => h2 j),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib, sub_div,
    mul_div_cancel_right₀ _ hP, mul_div_cancel_right₀ _ hP]

/-- The key identity `sideProd · rho · Efac = rho · (∏(N+D) − ∏(N−D))`. -/
lemma side_mul_Efac (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (d e : Fin m → ℕ) (l r : Fin t → ℤ)
    (hD : ((Ddd d e : ℝ)) ≠ 0) (hN : ∀ j, ((r j - l j : ℤ) : ℝ) ≠ 0) :
    sideProd l r * rho W A b d e * Efac d e l r
      = rho W A b d e * ((∏ j, (((r j - l j : ℤ) : ℝ) + (Ddd d e : ℝ)))
          - (∏ j, (((r j - l j : ℤ) : ℝ) - (Ddd d e : ℝ)))) := by
  have h1 : ∀ j, (((r j - l j : ℤ) : ℝ)) * (1 + (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ))
      = ((r j - l j : ℤ) : ℝ) + (Ddd d e : ℝ) := by
    intro j; have := hN j; field_simp
  have h2 : ∀ j, (((r j - l j : ℤ) : ℝ)) * (1 - (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ))
      = ((r j - l j : ℤ) : ℝ) - (Ddd d e : ℝ) := by
    intro j; have := hN j; field_simp
  have key : (∏ j, (((r j - l j : ℤ) : ℝ)))
        * ((∏ j, (1 + (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ)))
            - (∏ j, (1 - (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ))))
      = (∏ j, (((r j - l j : ℤ) : ℝ) + (Ddd d e : ℝ)))
        - (∏ j, (((r j - l j : ℤ) : ℝ) - (Ddd d e : ℝ))) := by
    rw [mul_sub, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1
    · exact Finset.prod_congr rfl (fun j _ => h1 j)
    · exact Finset.prod_congr rfl (fun j _ => h2 j)
  rw [Efac_eq d e l r hD hN, sideProd]
  calc (∏ j, (((r j - l j : ℤ) : ℝ))) * rho W A b d e
        * ((∏ j, (1 + (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ)))
            - (∏ j, (1 - (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ))))
      = rho W A b d e * ((∏ j, (((r j - l j : ℤ) : ℝ)))
        * ((∏ j, (1 + (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ)))
            - (∏ j, (1 - (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ))))) := by ring
    _ = rho W A b d e * ((∏ j, (((r j - l j : ℤ) : ℝ) + (Ddd d e : ℝ)))
          - (∏ j, (((r j - l j : ℤ) : ℝ) - (Ddd d e : ℝ)))) := by rw [key]

end Efac

section Bound

/-- Under the box hypotheses every side length is positive. -/
lemma side_pos {l r : Fin t → ℤ} {d e : Fin m → ℕ} (hd : ∀ i, 1 ≤ d i) (he : ∀ i, 1 ≤ e i)
    (hN : ∀ j, (Ddd d e : ℤ) ≤ r j - l j) : ∀ j, 0 < ((r j - l j : ℤ) : ℝ) := by
  intro j
  have hD : 1 ≤ Ddd d e := by
    rw [Ddd]
    exact one_le_prod (fun i _ => by
      have := Nat.lcm_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one (hd i))
        (Nat.lt_of_lt_of_le Nat.zero_lt_one (he i))
      omega)
  have h1 : (0 : ℤ) < r j - l j := lt_of_lt_of_le (by omega) (hN j)
  exact_mod_cast h1

/-- `D = ∏ lcm(d_i,e_i) ≤ R^(2m)` for `d,e ∈ [1,R]^m`. -/
lemma Ddd_le {R : ℕ} (d e : Fin m → ℕ) (hd : ∀ i, 1 ≤ d i) (he : ∀ i, 1 ≤ e i)
    (hdR : ∀ i, d i ≤ R) (heR : ∀ i, e i ≤ R) :
    Ddd d e ≤ R ^ (2 * m) := by
  have hlcm : ∀ i, Nat.lcm (d i) (e i) ≤ R ^ 2 := by
    intro i
    calc Nat.lcm (d i) (e i) ≤ d i * e i :=
          Nat.lcm_le_mul (by have := hd i; omega) (by have := he i; omega)
      _ ≤ R * R := Nat.mul_le_mul (hdR i) (heR i)
      _ = R ^ 2 := by ring
  calc Ddd d e = ∏ _i : Fin m, Nat.lcm (d _i) (e _i) := rfl
    _ ≤ ∏ _i : Fin m, R ^ 2 := Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hlcm i)
    _ = (R ^ 2) ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = R ^ (2 * m) := by rw [← pow_mul]

/-- **The residue-class counting in the absolute-value form.** -/
theorem countBox_abs_bound (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (l r : Fin t → ℤ)
    (d e : Fin m → ℕ) (hd : ∀ i, 1 ≤ d i) (he : ∀ i, 1 ≤ e i)
    (hpos : ∀ x ∈ box l r, ∀ i, 0 < theta W A b x i)
    (hN : ∀ j, (Ddd d e : ℤ) ≤ r j - l j) :
    |((countBox W A b l r d e : ℕ) : ℝ) - sideProd l r * rho W A b d e|
      ≤ sideProd l r * rho W A b d e * Efac d e l r := by
  obtain ⟨hlo, hhi⟩ := countBox_two_sided W A b l r d e hd he hpos hN
  have hDpos : 0 < Ddd d e := Ddd_pos d e hd he
  have hDne : ((Ddd d e : ℝ)) ≠ 0 := ne_of_gt (by exact_mod_cast hDpos)
  have hNne : ∀ j, ((r j - l j : ℤ) : ℝ) ≠ 0 := fun j => ne_of_gt (side_pos hd he hN j)
  have hNpos : ∀ j, (0 : ℝ) ≤ ((r j - l j : ℤ) : ℝ) := fun j => (side_pos hd he hN j).le
  have hrho := rho_nonneg W A b d e
  have hDnn : (0:ℝ) ≤ (Ddd d e : ℝ) := by positivity
  have hNℝ : ∀ j, (Ddd d e : ℝ) ≤ ((r j - l j : ℤ) : ℝ) := fun j => by
    have h : ((Ddd d e : ℤ) : ℝ) ≤ ((r j - l j : ℤ) : ℝ) := by exact_mod_cast hN j
    simpa using h
  have hmono₁ : (∏ j, (((r j - l j : ℤ) : ℝ) - (Ddd d e : ℝ)))
      ≤ ∏ j, (((r j - l j : ℤ) : ℝ)) := by
    refine Finset.prod_le_prod (fun j _ => by linarith [hNℝ j]) (fun j _ => by linarith [hNℝ j])
  have hmono₂ : (∏ j, (((r j - l j : ℤ) : ℝ)))
      ≤ ∏ j, (((r j - l j : ℤ) : ℝ) + (Ddd d e : ℝ)) :=
    Finset.prod_le_prod (fun j _ => hNpos j) (fun j _ => by linarith [hDnn])
  have hside : sideProd l r * rho W A b d e * Efac d e l r
      = rho W A b d e * ((∏ j, (((r j - l j : ℤ) : ℝ) + (Ddd d e : ℝ)))
          - (∏ j, (((r j - l j : ℤ) : ℝ) - (Ddd d e : ℝ)))) :=
    side_mul_Efac W A b d e l r hDne hNne
  have hsp : sideProd l r * rho W A b d e = rho W A b d e * ∏ j, (((r j - l j : ℤ) : ℝ)) := by
    rw [sideProd]; ring
  rw [abs_le]
  constructor
  · rw [hside, hsp]
    nlinarith [hlo, hmono₁, hmono₂, hrho]
  · rw [hside, hsp]
    nlinarith [hhi, hmono₁, hmono₂, hrho]

end Bound

/-- The elementary real-arithmetic estimate of the box reduction. -/
lemma arith_err (k R t m : ℕ) (ε L c : ℝ) (hR : 3 ≤ R) (hm1 : 1 ≤ m)
    (hm : m ≤ k * 2 ^ (k-1)) (ht : t ≤ 3 * k) (hε : 0 < ε) (hL1 : 1 ≤ L) (hc1 : 1 ≤ c)
    (hsmall : 6 * (3 * (k:ℝ)) * L^(k*2^(k-1)) ≤ ε * (R:ℝ)^6) :
    (R:ℝ)^(2*m) * (L^(2*m) * 3 * (t:ℝ) * (1/(R:ℝ)^(8*m))) ≤ (ε/2) * (c*L)^m := by
  have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast (by omega : 1 ≤ R)
  have hRpos : (0:ℝ) < (R:ℝ) := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hstep : (R:ℝ)^(2*m) * (1/(R:ℝ)^(8*m)) = 1/(R:ℝ)^(6*m) := by
    have h1 : (R:ℝ)^(8*m) = (R:ℝ)^(2*m) * (R:ℝ)^(6*m) := by
      rw [← pow_add]; ring_nf
    rw [h1, one_div, one_div, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have hLHS : (R:ℝ)^(2*m) * (L^(2*m) * 3 * (t:ℝ) * (1/(R:ℝ)^(8*m)))
      = 3 * (t:ℝ) * L^(2*m) * (1/(R:ℝ)^(6*m)) := by
    rw [← hstep]; ring
  rw [hLHS]
  have hLM : L^(2*m) ≤ L^(k*2^(k-1)) * L^m := by
    have h1 : (2:ℕ)*m ≤ k*2^(k-1) + m := by omega
    calc L^(2*m) ≤ L^(k*2^(k-1) + m) := pow_le_pow_right₀ hL1 h1
      _ = L^(k*2^(k-1)) * L^m := pow_add _ _ _
  have hR6m : (1:ℝ)/(R:ℝ)^(6*m) ≤ 1/(R:ℝ)^6 := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ hR1 (by omega)
  have hR6pos : (0:ℝ) < (R:ℝ)^6 := by positivity
  have h3 : 3 * (t:ℝ) * L^(k*2^(k-1)) * (1/(R:ℝ)^6) ≤ ε/2 := by
    have ht3 : (t:ℝ) ≤ 3*(k:ℝ) := by
      have : (t:ℝ) ≤ (3*k : ℕ) := by exact_mod_cast ht
      simpa using this
    have hkey : 3 * (3*(k:ℝ)) * L^(k*2^(k-1)) / (R:ℝ)^6 ≤ ε/2 := by
      rw [div_le_iff₀ hR6pos]
      linarith [hsmall]
    have hLp : (0:ℝ) ≤ L^(k*2^(k-1)) := pow_nonneg hL0 _
    have : 3 * (t:ℝ) * L^(k*2^(k-1)) / (R:ℝ)^6
        ≤ 3 * (3*(k:ℝ)) * L^(k*2^(k-1)) / (R:ℝ)^6 := by
      apply div_le_div_of_nonneg_right _ hR6pos.le
      nlinarith [ht3, hLp]
    calc 3 * (t:ℝ) * L^(k*2^(k-1)) * (1/(R:ℝ)^6)
        = 3 * (t:ℝ) * L^(k*2^(k-1)) / (R:ℝ)^6 := by ring
      _ ≤ ε/2 := le_trans this hkey
  have hcm : (1:ℝ) ≤ c^m := one_le_pow₀ hc1
  have hε2 : (0:ℝ) ≤ ε/2 := by linarith
  calc 3 * (t:ℝ) * L^(2*m) * (1/(R:ℝ)^(6*m))
      ≤ 3 * (t:ℝ) * (L^(k*2^(k-1)) * L^m) * (1/(R:ℝ)^(6*m)) := by
        have h4 : (0:ℝ) ≤ 3 * (t:ℝ) * (1/(R:ℝ)^(6*m)) := by positivity
        nlinarith [hLM, h4]
    _ = (3 * (t:ℝ) * L^(k*2^(k-1)) * (1/(R:ℝ)^(6*m))) * L^m := by ring
    _ ≤ (ε/2) * L^m := by
        have h5 : 0 ≤ L^m := pow_nonneg hL0 m
        have h6 : 3 * (t:ℝ) * L^(k*2^(k-1)) * (1/(R:ℝ)^(6*m)) ≤ ε/2 :=
          le_trans (by
            have h7 : (0:ℝ) ≤ 3 * (t:ℝ) * L^(k*2^(k-1)) := by positivity
            nlinarith [hR6m, h7]) h3
        exact mul_le_mul_of_nonneg_right h6 h5
    _ ≤ (ε/2) * (c^m * L^m) := by
        have h8 : (ε/2) * 1 ≤ (ε/2) * c^m := mul_le_mul_of_nonneg_left hcm hε2
        nlinarith [h8, pow_nonneg hL0 m]
    _ = (ε/2) * (c*L)^m := by rw [mul_pow]

section Err

variable {R k W : ℕ}

/-- The error factor is bounded by three times the sum of the relative side errors. -/
lemma Efac_le (d e : Fin m → ℕ) (l r : Fin t → ℤ)
    (hD : 0 < Ddd d e) (hN : ∀ j, 0 < ((r j - l j : ℤ) : ℝ))
    (hDN : ∀ j, (Ddd d e : ℝ) ≤ ((r j - l j : ℤ) : ℝ))
    (hsum : ∑ j, (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ) ≤ 1 / 2) :
    Efac d e l r ≤ 3 * ∑ j, (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ) := by
  have hDne : ((Ddd d e : ℝ)) ≠ 0 := ne_of_gt (by exact_mod_cast hD)
  have hNne : ∀ j, ((r j - l j : ℤ) : ℝ) ≠ 0 := fun j => ne_of_gt (hN j)
  rw [Efac_eq d e l r hDne hNne]
  have hy0 : ∀ j ∈ (Finset.univ : Finset (Fin t)),
      0 ≤ (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ) :=
    fun j _ => div_nonneg (by positivity) (hN j).le
  have hy1 : ∀ j ∈ (Finset.univ : Finset (Fin t)),
      (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ) ≤ 1 := by
    intro j _
    exact (div_le_one (hN j)).mpr (hDN j)
  have hup := prod_one_add_le (Finset.univ : Finset (Fin t)) hy0 hsum
  have hlo := prod_one_sub_ge (Finset.univ : Finset (Fin t)) hy0 hy1
  linarith

/-- `D/N_j ≤ R^(-8m)` for `d, e ∈ [1,R]^m` and side length at least `R^(10m)`. -/
lemma Ddd_div_side_le {R m : ℕ} (d e : Fin m → ℕ) (l r : Fin t → ℤ) (hR : 3 ≤ R)
    (hd : ∀ i, 1 ≤ d i) (he : ∀ i, 1 ≤ e i) (hdR : ∀ i, d i ≤ R) (heR : ∀ i, e i ≤ R)
    (hside : ∀ j, (R : ℤ) ^ (10 * m) ≤ r j - l j) (j : Fin t) :
    (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ) ≤ 1 / (R : ℝ) ^ (8 * m) := by
  have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast (by omega : 1 ≤ R)
  have hDR : (Ddd d e : ℝ) ≤ (R:ℝ)^(2*m) := by
    have h : (Ddd d e : ℝ) ≤ ((R ^ (2*m) : ℕ) : ℝ) := by
      exact_mod_cast (Ddd_le d e hd he hdR heR)
    simpa using h
  have hsideR : (R:ℝ)^(10*m) ≤ ((r j - l j : ℤ) : ℝ) := by
    have h : (((R : ℤ) ^ (10*m) : ℤ) : ℝ) ≤ ((r j - l j : ℤ) : ℝ) := by
      exact_mod_cast (hside j)
    simpa using h
  have hmain : (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ) ≤ (R:ℝ)^(2*m) / (R:ℝ)^(10*m) :=
    div_le_div₀ (by positivity) hDR (by positivity) hsideR
  have hkey : (R:ℝ)^(2*m) / (R:ℝ)^(10*m) = 1/(R:ℝ)^(8*m) := by
    have h1 : (R:ℝ)^(10*m) = (R:ℝ)^(2*m) * (R:ℝ)^(8*m) := by
      rw [← pow_add]; ring_nf
    rw [h1]
    field_simp
  linarith [hkey ▸ hmain]

/-- `|coef| ≤ (log R)^(2m)` for `d,e ∈ [1,R]^m`. -/
lemma abs_coef_le {R : ℕ} (hR : 1 ≤ R) (d e : Fin m → ℕ)
    (hd : ∀ i, 1 ≤ d i) (hdR : ∀ i, d i ≤ R) (he : ∀ i, 1 ≤ e i) (heR : ∀ i, e i ≤ R) :
    |coef R d e| ≤ (Real.log (R : ℝ)) ^ (2 * m) := by
  have hRpos : (0:ℝ) < (R:ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hL0 : 0 ≤ Real.log (R:ℝ) := Real.log_nonneg (by exact_mod_cast hR)
  rw [coef, Finset.abs_prod]
  have hdpos : ∀ i, (0:ℝ) < (d i : ℝ) :=
    fun i => by exact_mod_cast (by have := hd i; omega : 0 < d i)
  have hepos : ∀ i, (0:ℝ) < (e i : ℝ) :=
    fun i => by exact_mod_cast (by have := he i; omega : 0 < e i)
  have hfac : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      |(((ArithmeticFunction.moebius (d i) : ℤ) : ℝ)
          * ((ArithmeticFunction.moebius (e i) : ℤ) : ℝ)
          * Real.log ((R : ℝ) / (d i : ℝ)) * Real.log ((R : ℝ) / (e i : ℝ)))|
        ≤ Real.log (R:ℝ) * Real.log (R:ℝ) := by
    intro i _
    have hμd : |(((ArithmeticFunction.moebius (d i) : ℤ) : ℝ))| ≤ 1 := by
      have h := ArithmeticFunction.abs_moebius_le_one (n := d i)
      exact_mod_cast h
    have hμe : |(((ArithmeticFunction.moebius (e i) : ℤ) : ℝ))| ≤ 1 := by
      have h := ArithmeticFunction.abs_moebius_le_one (n := e i)
      exact_mod_cast h
    have hgd : 1 ≤ (R:ℝ)/(d i : ℝ) := by
      rw [le_div_iff₀ (hdpos i)]
      have h : ((d i : ℕ) : ℝ) ≤ (R:ℝ) := by exact_mod_cast hdR i
      linarith
    have hle_d : (R:ℝ)/(d i : ℝ) ≤ (R:ℝ) := by
      rw [div_le_iff₀ (hdpos i)]
      have h : (1:ℝ) ≤ ((d i : ℕ) : ℝ) := by exact_mod_cast hd i
      nlinarith
    have hld : |Real.log ((R : ℝ) / (d i : ℝ))| ≤ Real.log (R:ℝ) := by
      rw [abs_of_nonneg (Real.log_nonneg hgd)]
      exact Real.log_le_log (div_pos hRpos (hdpos i)) hle_d
    have hge : 1 ≤ (R:ℝ)/(e i : ℝ) := by
      rw [le_div_iff₀ (hepos i)]
      have h : ((e i : ℕ) : ℝ) ≤ (R:ℝ) := by exact_mod_cast heR i
      linarith
    have hle_e : (R:ℝ)/(e i : ℝ) ≤ (R:ℝ) := by
      rw [div_le_iff₀ (hepos i)]
      have h : (1:ℝ) ≤ ((e i : ℕ) : ℝ) := by exact_mod_cast he i
      nlinarith
    have hle_ : |Real.log ((R : ℝ) / (e i : ℝ))| ≤ Real.log (R:ℝ) := by
      rw [abs_of_nonneg (Real.log_nonneg hge)]
      exact Real.log_le_log (div_pos hRpos (hepos i)) hle_e
    have key1 : |(((ArithmeticFunction.moebius (d i) : ℤ) : ℝ))|
        * |(((ArithmeticFunction.moebius (e i) : ℤ) : ℝ))| ≤ 1 * 1 :=
      mul_le_mul hμd hμe (abs_nonneg _) (by norm_num)
    have key2 : |Real.log ((R : ℝ) / (d i : ℝ))| * |Real.log ((R : ℝ) / (e i : ℝ))|
        ≤ Real.log (R:ℝ) * Real.log (R:ℝ) :=
      mul_le_mul hld hle_ (abs_nonneg _) hL0
    calc |(((ArithmeticFunction.moebius (d i) : ℤ) : ℝ)
          * ((ArithmeticFunction.moebius (e i) : ℤ) : ℝ)
          * Real.log ((R : ℝ) / (d i : ℝ)) * Real.log ((R : ℝ) / (e i : ℝ)))|
        = |(((ArithmeticFunction.moebius (d i) : ℤ) : ℝ))|
          * |(((ArithmeticFunction.moebius (e i) : ℤ) : ℝ))|
          * |Real.log ((R : ℝ) / (d i : ℝ))| * |Real.log ((R : ℝ) / (e i : ℝ))| := by
          rw [abs_mul, abs_mul, abs_mul]
      _ = (|(((ArithmeticFunction.moebius (d i) : ℤ) : ℝ))|
          * |(((ArithmeticFunction.moebius (e i) : ℤ) : ℝ))|)
          * (|Real.log ((R : ℝ) / (d i : ℝ))| * |Real.log ((R : ℝ) / (e i : ℝ))|) := by ring
      _ ≤ (1 * 1) * (Real.log (R:ℝ) * Real.log (R:ℝ)) :=
          mul_le_mul key1 key2 (by positivity) (by positivity)
      _ = Real.log (R:ℝ) * Real.log (R:ℝ) := by ring
  have hprodbound : (∏ i, |(((ArithmeticFunction.moebius (d i) : ℤ) : ℝ)
          * ((ArithmeticFunction.moebius (e i) : ℤ) : ℝ)
          * Real.log ((R : ℝ) / (d i : ℝ)) * Real.log ((R : ℝ) / (e i : ℝ)))|)
      ≤ (Real.log (R:ℝ)) ^ (2 * m) := by
    calc (∏ i, |(((ArithmeticFunction.moebius (d i) : ℤ) : ℝ)
          * ((ArithmeticFunction.moebius (e i) : ℤ) : ℝ)
          * Real.log ((R : ℝ) / (d i : ℝ)) * Real.log ((R : ℝ) / (e i : ℝ)))|)
        ≤ ∏ _i : Fin m, (Real.log (R:ℝ) * Real.log (R:ℝ)) :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hfac i (Finset.mem_univ i))
      _ = (Real.log (R:ℝ)) ^ (2 * m) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← sq, ← pow_mul]
  exact hprodbound

/-- The elementary error estimate of the box reduction. -/
theorem errBd_le (k R W : ℕ) (ε : ℝ) (hR : 3 ≤ R) (hRk : 3 * k ≤ R) (hW : 1 ≤ W)
    (hε : 0 < ε)
    (hsmall : 6 * (3 * (k : ℝ)) * (Real.log (R : ℝ)) ^ (k * 2 ^ (k - 1)) ≤ ε * (R : ℝ) ^ 6) :
    ∀ (m t : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (l r : Fin t → ℤ),
      1 ≤ m → m ≤ k * 2 ^ (k - 1) → 1 ≤ t → t ≤ 3 * k →
      (∀ j, (R : ℤ) ^ (10 * m) ≤ r j - l j) →
      (∀ x ∈ box l r, ∀ i, 0 < theta W A b x i) →
      errBd R W A b l r ≤ (ε / 2) * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ m := by
  intro m t A b l r hm1 hm ht1 ht2 hside hpos
  have hR1 : 1 ≤ R := by omega
  have hL1 : 1 ≤ Real.log (R:ℝ) := by
    have h3 : (1:ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      exact le_of_lt Real.exp_one_lt_three
    have hR3 : (3:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    exact le_trans h3 (Real.log_le_log (by norm_num) hR3)
  have hL0 : 0 ≤ Real.log (R:ℝ) := le_trans zero_le_one hL1
  have hφpos : 0 < (Nat.totient W : ℝ) := by
    have hW0 : 0 < W := by omega
    exact_mod_cast (Nat.totient_pos.mpr hW0)
  have hc1 : 1 ≤ (W:ℝ) / (Nat.totient W : ℝ) := by
    rw [le_div_iff₀ hφpos]
    have h := Nat.totient_le W
    have h' : ((Nat.totient W : ℕ) : ℝ) ≤ (W : ℝ) := by exact_mod_cast h
    linarith
  have ht3k : t ≤ 3 * k := by omega
  have hRpos : (0:ℝ) < (R:ℝ) := by exact_mod_cast (by omega : 0 < R)
  -- per-term bound
  have hterm : ∀ d ∈ P (m := m) R, ∀ e ∈ P (m := m) R,
      |coef R d e| * rho W A b d e * Efac d e l r
        ≤ (Real.log (R:ℝ))^(2*m) * 3 * (t:ℝ) * (1/(R:ℝ)^(8*m)) := by
    intro d hd e he
    simp only [P, Fintype.mem_piFinset] at hd he
    have hd1 : ∀ i, 1 ≤ d i := fun i => (Finset.mem_Icc.mp (hd i)).1
    have hdR : ∀ i, d i ≤ R := fun i => (Finset.mem_Icc.mp (hd i)).2
    have he1 : ∀ i, 1 ≤ e i := fun i => (Finset.mem_Icc.mp (he i)).1
    have heR : ∀ i, e i ≤ R := fun i => (Finset.mem_Icc.mp (he i)).2
    have hcoef := abs_coef_le hR1 d e hd1 hdR he1 heR
    have hrho := rho_le_one W A b d e hd1 he1
    have hDpos : 0 < Ddd d e := Ddd_pos d e hd1 he1
    have hNpos : ∀ j, 0 < ((r j - l j : ℤ) : ℝ) := by
      intro j
      have h1 : (0:ℤ) < (R:ℤ)^(10*m) := by
        have h2 : (1:ℤ) ≤ (R:ℤ)^(10*m) :=
          one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ R) : (1:ℤ) ≤ (R:ℤ))
        omega
      have : (0:ℤ) < r j - l j := lt_of_lt_of_le h1 (hside j)
      exact_mod_cast this
    have hdivle : ∀ j, (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ) ≤ 1/(R:ℝ)^(8*m) :=
      fun j => Ddd_div_side_le d e l r hR hd1 he1 hdR heR hside j
    have hsum : ∑ j : Fin t, (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ) ≤ 1/2 := by
      have h1 : ∑ j : Fin t, (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ)
          ≤ ∑ _j : Fin t, 1/(R:ℝ)^(8*m) := Finset.sum_le_sum (fun j _ => hdivle j)
      have h2 : ∑ _j : Fin t, 1/(R:ℝ)^(8*m) = (t:ℝ) * (1/(R:ℝ)^(8*m)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      have hR8 : (1:ℝ) ≤ (R:ℝ)^8 := one_le_pow₀ (by exact_mod_cast hR1 : (1:ℝ) ≤ R)
      have hRm : (1:ℝ) ≤ (R:ℝ)^(8*m) := by
        have h : (R:ℝ)^8 ≤ (R:ℝ)^(8*m) := pow_le_pow_right₀ (by exact_mod_cast hR1 : (1:ℝ) ≤ R)
          (by omega)
        linarith
      have htR : (t:ℝ) ≤ (R:ℝ) := by
        have : t ≤ R := by omega
        exact_mod_cast this
      have hRm7 : (2:ℝ) ≤ (R:ℝ)^7 := by
        have h : (3:ℝ)^7 ≤ (R:ℝ)^7 := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hR) 7
        norm_num at h ⊢
        linarith
      have hsplit : (R:ℝ)^(8*m) = (R:ℝ) * (R:ℝ)^(8*m - 1) := by
        have h : 1 ≤ 8*m := by omega
        conv_lhs => rw [show 8*m = (8*m - 1) + 1 by omega, pow_add]
        ring
      have hR8m1 : (R:ℝ)^7 ≤ (R:ℝ)^(8*m - 1) :=
        pow_le_pow_right₀ (by exact_mod_cast hR1 : (1:ℝ) ≤ R) (by omega)
      have h3 : (t:ℝ) * (1/(R:ℝ)^(8*m)) ≤ 1/2 := by
        have hA : (t:ℝ) * (1/(R:ℝ)^(8*m)) ≤ (R:ℝ) * (1/(R:ℝ)^(8*m)) :=
          mul_le_mul_of_nonneg_right htR (by positivity)
        have hB : (R:ℝ) * (1/(R:ℝ)^(8*m)) ≤ 1/2 := by
          rw [hsplit, mul_one_div, div_mul_eq_div_div, div_self (by positivity)]
          apply one_div_le_one_div_of_le (by norm_num)
          linarith
        linarith
      rw [h2] at h1
      linarith
    have hDN : ∀ j, (Ddd d e : ℝ) ≤ ((r j - l j : ℤ) : ℝ) := by
      intro j
      have h1 : (Ddd d e : ℝ) ≤ (R:ℝ)^(2*m) := by
        have h : (Ddd d e : ℝ) ≤ ((R ^ (2*m) : ℕ) : ℝ) := by
          exact_mod_cast (Ddd_le d e hd1 he1 hdR heR)
        simpa using h
      have h2 : (R:ℝ)^(2*m) ≤ (R:ℝ)^(10*m) :=
        pow_le_pow_right₀ (by exact_mod_cast hR1 : (1:ℝ) ≤ R) (by omega)
      have h3 : (R:ℝ)^(10*m) ≤ ((r j - l j : ℤ) : ℝ) := by
        have h : (((R : ℤ)^(10*m) : ℤ) : ℝ) ≤ ((r j - l j : ℤ) : ℝ) := by
          exact_mod_cast (hside j)
        simpa using h
      linarith
    have hEfac : Efac d e l r ≤ 3 * ∑ j : Fin t, (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ) :=
      Efac_le d e l r hDpos hNpos hDN hsum
    have hEfac2 : Efac d e l r ≤ 3 * (t:ℝ) * (1/(R:ℝ)^(8*m)) := by
      have h1 : 3 * ∑ j : Fin t, (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ)
          ≤ 3 * ((t:ℝ) * (1/(R:ℝ)^(8*m))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc ∑ j : Fin t, (Ddd d e : ℝ) / ((r j - l j : ℤ) : ℝ)
            ≤ ∑ _j : Fin t, 1/(R:ℝ)^(8*m) := Finset.sum_le_sum (fun j _ => hdivle j)
          _ = (t:ℝ) * (1/(R:ℝ)^(8*m)) := by
              rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      linarith
    have hcoef0 : 0 ≤ |coef R d e| := abs_nonneg _
    have hrho0 : 0 ≤ rho W A b d e := rho_nonneg W A b d e
    have hB0 : 0 ≤ 3 * (t:ℝ) * (1/(R:ℝ)^(8*m)) := by positivity
    calc |coef R d e| * rho W A b d e * Efac d e l r
        ≤ |coef R d e| * rho W A b d e * (3 * (t:ℝ) * (1/(R:ℝ)^(8*m))) :=
          mul_le_mul_of_nonneg_left hEfac2 (mul_nonneg hcoef0 hrho0)
      _ ≤ (Real.log (R:ℝ))^(2*m) * 1 * (3 * (t:ℝ) * (1/(R:ℝ)^(8*m))) := by
          have h1 : |coef R d e| * rho W A b d e ≤ (Real.log (R:ℝ))^(2*m) * 1 :=
            mul_le_mul hcoef hrho hrho0 (by positivity)
          exact mul_le_mul_of_nonneg_right h1 hB0
      _ = (Real.log (R:ℝ))^(2*m) * 3 * (t:ℝ) * (1/(R:ℝ)^(8*m)) := by ring
  have hcard : (((P (m := m) R).card : ℕ) : ℝ) = (R:ℝ)^m := by
    rw [P, Fintype.card_piFinset]
    simp [Nat.card_Icc]
  have hsumle : errBd R W A b l r
      ≤ (((P (m := m) R).card : ℕ) : ℝ)^2
        * ((Real.log (R:ℝ))^(2*m) * 3 * (t:ℝ) * (1/(R:ℝ)^(8*m))) := by
    rw [errBd]
    set C : ℝ := (Real.log (R:ℝ))^(2*m) * 3 * (t:ℝ) * (1/(R:ℝ)^(8*m)) with hC
    calc ∑ d ∈ P (m := m) R, ∑ e ∈ P (m := m) R,
            |coef R d e| * rho W A b d e * Efac d e l r
        ≤ ∑ d ∈ P (m := m) R, ∑ _e ∈ P (m := m) R, C :=
          Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => hterm d hd e he))
      _ = ∑ d ∈ P (m := m) R, (((P (m := m) R).card : ℕ) : ℝ) * C := by
          refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (((P (m := m) R).card : ℕ) : ℝ) * ((((P (m := m) R).card : ℕ) : ℝ) * C) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (((P (m := m) R).card : ℕ) : ℝ)^2 * C := by ring
  rw [hcard] at hsumle
  refine le_trans hsumle ?_
  have h1 : ((R:ℝ) ^ m)^2 * ((Real.log (R:ℝ))^(2*m) * 3 * (t:ℝ) * (1/(R:ℝ)^(8*m)))
      = (R:ℝ)^(2*m) * ((Real.log (R:ℝ))^(2*m) * 3 * (t:ℝ) * (1/(R:ℝ)^(8*m))) := by
    rw [← pow_mul]; ring_nf
  rw [h1]
  have h2 : ((W:ℝ) * Real.log (R:ℝ) / (Nat.totient W : ℝ))
      = ((W:ℝ) / (Nat.totient W : ℝ)) * Real.log (R:ℝ) := by ring
  rw [h2]
  exact arith_err k R t m ε (Real.log (R:ℝ)) ((W:ℝ) / (Nat.totient W : ℝ)) hR hm1 hm ht3k hε hL1 hc1
    hsmall

/-- **Green–Tao Proposition 9.5 reduced to the divisor-sum main term `hmain`** (Green–Tao
(ddr)).  The residue-class counting and the elementary error estimate are discharged here. -/
theorem boxAvgGood_of_hmain (k R W : ℕ) (ε : ℝ) (hR : 3 ≤ R) (hRk : 3 * k ≤ R) (hW : 1 ≤ W)
    (hε : 0 < ε)
    (hsmall : 6 * (3 * (k : ℝ)) * (Real.log (R : ℝ)) ^ (k * 2 ^ (k - 1)) ≤ ε * (R : ℝ) ^ 6)
    (hmain : ∀ (m t : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (l r : Fin t → ℤ),
      BoxData k R W m t A b l r →
      |mainSum R W A b - ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ m|
        ≤ (ε / 2) * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ m) :
    BoxAvgGood k R W ε := by
  refine boxAvgGood_of_main k R W ε (by omega) hε.le hmain ?_ ?_
  · intro m t A b l r hD d hd e he
    obtain ⟨hm1, hm, ht1, ht2, hne, hprop, _, hside, hpos⟩ := hD
    simp only [P, Fintype.mem_piFinset] at hd he
    have hd1 : ∀ i, 1 ≤ d i := fun i => (Finset.mem_Icc.mp (hd i)).1
    have hdR : ∀ i, d i ≤ R := fun i => (Finset.mem_Icc.mp (hd i)).2
    have he1 : ∀ i, 1 ≤ e i := fun i => (Finset.mem_Icc.mp (he i)).1
    have heR : ∀ i, e i ≤ R := fun i => (Finset.mem_Icc.mp (he i)).2
    have hN : ∀ j, (Ddd d e : ℤ) ≤ r j - l j := by
      intro j
      have h1 : (Ddd d e : ℤ) ≤ ((R : ℤ)) ^ (2 * m) := by
        have h := Ddd_le d e hd1 he1 hdR heR
        exact_mod_cast h
      have h2 : ((R : ℤ)) ^ (2 * m) ≤ ((R : ℤ)) ^ (10 * m) :=
        pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ R) : (1:ℤ) ≤ (R:ℤ)) (by omega)
      linarith [hside j]
    exact countBox_abs_bound W A b l r d e hd1 he1 hpos hN
  · intro m t A b l r hD
    obtain ⟨hm1, hm, ht1, ht2, _, _, _, hside, hpos⟩ := hD
    exact errBd_le k R W ε hR hRk hW hε hsmall m t A b l r hm1 hm ht1 (by omega) hside hpos

end Err

end BoxAvg
end GYMaj
