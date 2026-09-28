import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.FM4.xi_sum_vero
import Submission.Work.HP.DegSq.ball_sum_inv_pow
import Submission.Work.HP.veronese_enorm_lower

/-!
# `∑_{x ∈ Ξ_{d,n}(B)} ‖ν_{d,n}(x)‖^{-1} ≪ B` and `∑_{x ∈ Ξ_{d,n}(B)} ‖ν_{d,n}(x)‖^{-2} ≪ B^θ log B`

Browning--Le Boudec--Sawin need, for primitive integer vectors `x` of norm at most
`B^{1/(n+1-d)}` (the set `Xi d n B`),

* `Σ_x ‖ν_{d,n}(x)‖^{-1} ≪ B`  (this is the sub-critical case `d ≤ n`);
* `Σ_x ‖ν_{d,n}(x)‖^{-2} ≪ (1 + B^{(n+1-2d)/(n+1-d)}) (1 + log B)`, which is the critical
  estimate `Σ_{‖x‖ ≤ R} ‖x‖^{-2d} ≈ R^{n+1-2d}` (with a logarithm at the critical exponent)
  for the radius `R = B^{1/(n+1-d)}`.

Both follow from the two elementary inputs

* `veronese_enorm_lower`: `‖ν_{d,n}(x)‖ ≫ ‖x‖^d`, so the summand is `≪ ‖x‖^{-d}` resp.
  `≪ ‖x‖^{-2d}`;
* the dyadic shell estimates for lattice points in a Euclidean ball: `Work.HP.FM4.dyadic_sum_finset`
  (sharp, used in `Work.HP.FM4.xi_sum_vero` for the first bound) and
  `Work.HP.DegSq.ball_sum_inv_pow` (with the logarithm, used here for the second bound).

The only new content of this file is the second estimate and the packaging: the constants `C`
and `B₀` must be common to the two bounds, and the shell sum is stated for the ball of radius
`R = B^{1/(n+1-d)}`, so the exponent `R^{n+1-2d}` has to be rewritten as
`B^{(n+1-2d)/(n+1-d)}` (and, when `2d > n+1`, the natural subtraction truncates and the bound is
absorbed by the negative power of `B`).
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP

/-- `1/‖ν_{d,n}(x)‖² ≤ C/‖x‖^{2d}` for `x ≠ 0`, with `C` depending only on `d, n`. -/
lemma one_div_sq_veronese_le (d n : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Fin (n + 1) → ℤ, x ≠ 0 →
      1 / (eNorm (veronese d n x)) ^ 2 ≤ C * (1 / (eNorm x) ^ (2 * d)) := by
  obtain ⟨c, hc0, hc⟩ := veronese_enorm_lower d n hd
  refine ⟨(1 / c) ^ 2, by positivity, ?_⟩
  intro x hx
  have hxe : 0 < eNorm x := lt_of_lt_of_le one_pos (DegSq.one_le_eNorm hx)
  have ha : 0 < c * (eNorm x) ^ d := mul_pos hc0 (pow_pos hxe d)
  have hb : c * (eNorm x) ^ d ≤ eNorm (veronese d n x) := hc x
  have hle : (c * (eNorm x) ^ d) ^ 2 ≤ (eNorm (veronese d n x)) ^ 2 :=
    pow_le_pow_left₀ ha.le hb 2
  have h1 : 1 / (eNorm (veronese d n x)) ^ 2 ≤ 1 / (c * (eNorm x) ^ d) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) hle
  have hpow : (eNorm x) ^ (2 * d) = ((eNorm x) ^ d) ^ 2 := by
    rw [← pow_mul, mul_comm]
  have h2 : (1 : ℝ) / (c * (eNorm x) ^ d) ^ 2 = (1 / c) ^ 2 * (1 / (eNorm x) ^ (2 * d)) := by
    rw [hpow]
    field_simp
  rw [h2] at h1
  exact h1

theorem Xi_sum_inv_veronese (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ C B₀ : ℝ, 0 < C ∧ 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B →
      (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x)) ≤ C * B ∧
      (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x) ^ 2) ≤
        C * (1 + B ^ (((n : ℝ) + 1 - 2 * d) / ((n : ℝ) + 1 - d))) * (1 + Real.log B)
      := by
  obtain ⟨C₁, B₀₁, hC₁0, hB₀₁0, hfirst⟩ := FM4.xi_sum_vero d n hd hdn
  obtain ⟨K, hK0, hKbound⟩ := DegSq.ball_sum_inv_pow (n + 1)
  obtain ⟨Cv, hCv0, hCv⟩ := one_div_sq_veronese_le d n hd
  have hdnR : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
  refine ⟨max C₁ (Cv * K * 2), max B₀₁ 1,
    lt_of_lt_of_le hC₁0 (le_max_left _ _), lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro B hB
  have hB1 : (1 : ℝ) ≤ B := le_trans (le_max_right _ _) hB
  have hBfirst : B₀₁ ≤ B := le_trans (le_max_left _ _) hB
  constructor
  · calc (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x)) ≤ C₁ * B := hfirst B hBfirst
      _ ≤ max C₁ (Cv * K * 2) * B := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  · -- second estimate: reduce to lattice points in the ball of radius `R = B^{1/(n+1-d)}`
    set R : ℝ := B ^ (1 / ((n : ℝ) + 1 - d)) with hRdef
    have hden : 0 < (n : ℝ) + 1 - d := by linarith
    have hge1 : (1 : ℝ) ≤ (n : ℝ) + 1 - d := by linarith
    have hB0 : 0 < B := lt_of_lt_of_le one_pos hB1
    have hR1 : 1 ≤ R := Real.one_le_rpow hB1 (le_of_lt (one_div_pos.mpr hden))
    have hTfin : ({v : Fin (n + 1) → ℤ | v ≠ 0 ∧ eNorm v ≤ R} : Set (Fin (n + 1) → ℤ)).Finite :=
      (MDBasic.finite_eNorm_le R).subset (fun v hv => hv.2)
    have hXifin : (Xi d n B).Finite := (MDBasic.finite_eNorm_le R).subset (fun x hx => hx.2)
    have hsupp : (Xi d n B ∩
        Function.support (fun x : Fin (n + 1) → ℤ => 1 / (eNorm (veronese d n x)) ^ 2)).Finite :=
      hXifin.subset Set.inter_subset_left
    have hTf : (({v : Fin (n + 1) → ℤ | v ≠ 0 ∧ eNorm v ≤ R} : Set (Fin (n + 1) → ℤ)) ∩
        Function.support (fun x : Fin (n + 1) → ℤ => 1 / (eNorm x) ^ (2 * d))).Finite :=
      hTfin.subset Set.inter_subset_left
    have hstep1 : ∑ x ∈ hsupp.toFinset, 1 / (eNorm (veronese d n x)) ^ 2
        ≤ ∑ x ∈ hsupp.toFinset, Cv * (1 / (eNorm x) ^ (2 * d)) := by
      refine Finset.sum_le_sum (fun x hx => ?_)
      have hxXi : x ∈ Xi d n B := ((Set.Finite.mem_toFinset hsupp).1 hx).1
      simp only [Xi, Set.mem_ofPred_eq] at hxXi
      exact hCv x (FM4.isPrim_ne_zero hxXi.1)
    have hsub : hsupp.toFinset ⊆ hTfin.toFinset := by
      refine (Set.Finite.toFinset_subset_toFinset).2 ?_
      rintro x ⟨hx1, _hx2⟩
      have hxXi : x ∈ Xi d n B := hx1
      simp only [Xi, Set.mem_ofPred_eq] at hxXi
      exact ⟨FM4.isPrim_ne_zero hxXi.1, hxXi.2⟩
    have hstep3 : ∑ x ∈ hsupp.toFinset, 1 / (eNorm x) ^ (2 * d)
        ≤ ∑ x ∈ hTfin.toFinset, 1 / (eNorm x) ^ (2 * d) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun x _ _ => div_nonneg zero_le_one (pow_nonneg (FM4.eNorm_nonneg x) _))
    have hstep4 : (∑ x ∈ hTfin.toFinset, 1 / (eNorm x) ^ (2 * d))
        = ∑ᶠ x ∈ ({v : Fin (n + 1) → ℤ | v ≠ 0 ∧ eNorm v ≤ R} : Set (Fin (n + 1) → ℤ)),
            1 / (eNorm x) ^ (2 * d) := by
      have hsub' : hTf.toFinset ⊆ hTfin.toFinset := by
        rintro x hx
        have hx' : x ∈ ({v : Fin (n + 1) → ℤ | v ≠ 0 ∧ eNorm v ≤ R} : Set _) :=
          ((Set.Finite.mem_toFinset hTf).1 hx).1
        exact (Set.Finite.mem_toFinset hTfin).2 hx'
      have hzero : ∀ x ∈ hTfin.toFinset, x ∉ hTf.toFinset → 1 / (eNorm x) ^ (2 * d) = 0 := by
        intro x hxT hxnot
        by_contra hne
        exact hxnot ((Set.Finite.mem_toFinset hTf).2
          ⟨(Set.Finite.mem_toFinset hTfin).1 hxT, hne⟩)
      have hA : ∑ x ∈ hTf.toFinset, 1 / (eNorm x) ^ (2 * d)
          = ∑ x ∈ hTfin.toFinset, 1 / (eNorm x) ^ (2 * d) :=
        Finset.sum_subset hsub' hzero
      rw [← hA, finsum_mem_eq_sum (fun x : Fin (n + 1) → ℤ => 1 / (eNorm x) ^ (2 * d)) hTf]
    have hmain : (∑ᶠ x ∈ ({v : Fin (n + 1) → ℤ | v ≠ 0 ∧ eNorm v ≤ R} : Set (Fin (n + 1) → ℤ)),
            1 / (eNorm x) ^ (2 * d)) ≤ K * (1 + Real.log R) * (1 + R ^ ((n + 1) - 2 * d)) :=
      hKbound (2 * d) (by omega) R hR1
    have hlogR : Real.log R ≤ Real.log B := by
      rw [hRdef, Real.log_rpow hB0]
      refine mul_le_of_le_one_left (Real.log_nonneg hB1) ?_
      rw [div_le_one hden]
      exact hge1
    have hRpow : 1 + R ^ ((n + 1) - 2 * d) ≤
        2 * (1 + B ^ (((n : ℝ) + 1 - 2 * d) / ((n : ℝ) + 1 - d))) := by
      by_cases hcase : 2 * d ≤ n + 1
      · have heq : R ^ ((n + 1) - 2 * d)
            = B ^ (((n : ℝ) + 1 - 2 * d) / ((n : ℝ) + 1 - d)) := by
          rw [hRdef, ← Real.rpow_natCast _ ((n + 1) - 2 * d),
            ← Real.rpow_mul (le_of_lt hB0)]
          congr 1
          rw [Nat.cast_sub hcase]
          push_cast
          field_simp
        rw [heq]
        have hnn : 0 ≤ B ^ (((n : ℝ) + 1 - 2 * d) / ((n : ℝ) + 1 - d)) :=
          Real.rpow_nonneg (le_of_lt hB0) _
        linarith
      · push Not at hcase
        have hz : (n + 1) - 2 * d = 0 := Nat.sub_eq_zero_of_le (le_of_lt hcase)
        rw [hz, pow_zero]
        have hnn : 0 ≤ B ^ (((n : ℝ) + 1 - 2 * d) / ((n : ℝ) + 1 - d)) :=
          Real.rpow_nonneg (le_of_lt hB0) _
        linarith
    have hkey : Cv * (K * (1 + Real.log R) * (1 + R ^ ((n + 1) - 2 * d)))
        ≤ max C₁ (Cv * K * 2) * (1 + B ^ (((n : ℝ) + 1 - 2 * d) / ((n : ℝ) + 1 - d)))
            * (1 + Real.log B) := by
      have hCK : 0 ≤ Cv * K := by positivity
      have h1 : 1 + Real.log R ≤ 1 + Real.log B := by linarith
      have h3 : 0 ≤ 1 + Real.log B := by linarith [Real.log_nonneg hB1]
      have h0 : 0 ≤ 1 + R ^ ((n + 1) - 2 * d) := by positivity
      calc Cv * (K * (1 + Real.log R) * (1 + R ^ ((n + 1) - 2 * d)))
          = (Cv * K) * ((1 + Real.log R) * (1 + R ^ ((n + 1) - 2 * d))) := by ring
        _ ≤ (Cv * K) * ((1 + Real.log B)
              * (2 * (1 + B ^ (((n : ℝ) + 1 - 2 * d) / ((n : ℝ) + 1 - d))))) := by
            refine mul_le_mul_of_nonneg_left ?_ hCK
            exact mul_le_mul h1 hRpow h0 h3
        _ = (Cv * K * 2) * ((1 + B ^ (((n : ℝ) + 1 - 2 * d) / ((n : ℝ) + 1 - d)))
              * (1 + Real.log B)) := by ring
        _ ≤ (max C₁ (Cv * K * 2)) * ((1 + B ^ (((n : ℝ) + 1 - 2 * d) / ((n : ℝ) + 1 - d)))
              * (1 + Real.log B)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        _ = max C₁ (Cv * K * 2) * (1 + B ^ (((n : ℝ) + 1 - 2 * d) / ((n : ℝ) + 1 - d)))
              * (1 + Real.log B) := by ring
    rw [finsum_mem_eq_sum (fun x : Fin (n + 1) → ℤ => 1 / (eNorm (veronese d n x)) ^ 2) hsupp]
    refine le_trans ?_ hkey
    calc ∑ x ∈ hsupp.toFinset, 1 / (eNorm (veronese d n x)) ^ 2
        ≤ ∑ x ∈ hsupp.toFinset, Cv * (1 / (eNorm x) ^ (2 * d)) := hstep1
      _ = Cv * ∑ x ∈ hsupp.toFinset, 1 / (eNorm x) ^ (2 * d) := (Finset.mul_sum _ _ _).symm
      _ ≤ Cv * ∑ x ∈ hTfin.toFinset, 1 / (eNorm x) ^ (2 * d) :=
          mul_le_mul_of_nonneg_left hstep3 hCv0.le
      _ = Cv * ∑ᶠ x ∈ ({v : Fin (n + 1) → ℤ | v ≠ 0 ∧ eNorm v ≤ R} : Set (Fin (n + 1) → ℤ)),
            1 / (eNorm x) ^ (2 * d) := by rw [hstep4]
      _ ≤ Cv * (K * (1 + Real.log R) * (1 + R ^ ((n + 1) - 2 * d))) :=
          mul_le_mul_of_nonneg_left hmain hCv0.le

end Work.HP
