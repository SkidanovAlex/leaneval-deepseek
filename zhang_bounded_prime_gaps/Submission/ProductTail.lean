import Mathlib
import Submission.MaynardFunctionals

open scoped BigOperators Topology
open Filter

/-!
# The prime-product tail `∏_{p>w} (1 + O(p⁻²)) = 1 + o(1)` — finite form

P8 Lemma 4.1, between (39)/(40) and the ζ_WN identification: the cumulative
relative error of the per-prime local factors over all primes above `w` is
`1 + o(1)`, because `∏_{p>w}(1 + C/p²) ≤ exp(C·Σ_{p>w}1/p²) ≤ exp(C/w) → 1`.

This module proves the reusable FINITE form needed by the truncation.  For
any finite set `S` of naturals with all elements `> w ≥ 1` and per-element
relative errors `|x_p| ≤ C/p²` (of either sign),

    |∏_{p ∈ S} (1 + x_p) − 1| ≤ exp(C/w) − 1          (tailProduct_abs_sub_one_le)

and the k-coordinate composition (`e : Fin k → ℕ → ℝ`,
`|e_{j,p}| ≤ C/p²`) costs one coordinate factor:

    |∏_{p ∈ S} ∏_{j} (1 + e_{j,p}) − 1| ≤ exp(k·C/w) − 1
                                              (coordTailProduct_abs_sub_one_le)

so multiplying the `k` per-coordinate `(1 + O(p⁻²))` estimates over the tail
primes gives `1 + o(1)` as `w → ∞` (tendsto_exp_div_sub_one).

Key elementary ingredients (all kernel-verified, zero `sorry`):
`∏(1+x_i) ≤ exp(Σ x_i)` for `x_i ≥ 0`; the absolute-product bound
`|∏(1+x_p) − 1| ≤ ∏(1+|x_p|) − 1`; and the telescoping estimate
`Σ_{p∈S} 1/p² ≤ 1/w` for distinct naturals `p > w`
(`1/n² ≤ 1/((n−1)n)`, telescoping between `w+1` and `max S`).
-/

namespace Commons.NumberTheory.MaynardSieve

section Pointwise

lemma cast_pred (p : ℕ) (hp : 1 ≤ p) : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
  have h := Nat.cast_sub (R := ℝ) hp
  simpa using h

lemma inv_sq_le_pred_sub {p : ℕ} (hp : 2 ≤ p) :
    ((p : ℝ) ^ 2)⁻¹ ≤ ((p - 1 : ℕ) : ℝ)⁻¹ - (p : ℝ)⁻¹ := by
  have hpR : 2 ≤ (p : ℝ) := by exact_mod_cast hp
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := cast_pred p (by omega)
  have hpne : (p : ℝ) ≠ 0 := by positivity
  have hpm : (p : ℝ) - 1 ≠ 0 := by linarith
  have hle : (p : ℝ) * ((p : ℝ) - 1) ≤ (p : ℝ) ^ 2 := by nlinarith
  have h1 : ((p : ℝ) ^ 2)⁻¹ ≤ ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
    have hpp : 0 < (p : ℝ) ^ 2 := by positivity
    have hpm0 : 0 < (p : ℝ) * ((p : ℝ) - 1) := by
      exact mul_pos (by linarith : 0 < (p : ℝ)) (by linarith : 0 < (p : ℝ) - 1)
    exact (inv_le_inv₀ hpp hpm0).mpr hle
  have heq : ((p : ℝ) * ((p : ℝ) - 1))⁻¹ = ((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹ := by
    field_simp [hpne, hpm]
    ring
  calc
    ((p : ℝ) ^ 2)⁻¹ ≤ ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := h1
    _ = ((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹ := heq
    _ = ((p - 1 : ℕ) : ℝ)⁻¹ - (p : ℝ)⁻¹ := by rw [hcast]

lemma pred_sub_inv_nonneg {p : ℕ} (hp : 2 ≤ p) :
    0 ≤ ((p - 1 : ℕ) : ℝ)⁻¹ - (p : ℝ)⁻¹ := by
  have hpR : 2 ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1 : 1 ≤ p := by omega
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := cast_pred p hp1
  have hle : (p : ℝ)⁻¹ ≤ ((p - 1 : ℕ) : ℝ)⁻¹ := by
    rw [hcast]
    refine (inv_le_inv₀ ?_ ?_).mpr ?_
    · positivity
    · linarith
    · linarith
  linarith

lemma sum_pred_inv_sub_tele (w : ℕ) : ∀ M : ℕ, w ≤ M →
    (∑ n ∈ Finset.Icc (w + 1) M, (((n - 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹)) =
      (w : ℝ)⁻¹ - (M : ℝ)⁻¹ := by
  intro M
  induction M with
  | zero =>
      intro hw0
      have : w = 0 := by omega
      subst w
      simp
  | succ M ih =>
      intro hw
      by_cases hwM : w ≤ M
      · have hMnat : M + 1 - 1 = M := by omega
        calc
          (∑ n ∈ Finset.Icc (w + 1) (M + 1), (((n - 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹))
              = (∑ n ∈ Finset.Icc (w + 1) M, (((n - 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹)) +
                  (((M + 1 - 1 : ℕ) : ℝ)⁻¹ - ((M + 1 : ℕ) : ℝ)⁻¹) := by
                  simpa [hMnat] using (Finset.sum_Icc_succ_top (a := w + 1) (b := M)
                    (f := fun k : ℕ => (((k - 1 : ℕ) : ℝ)⁻¹ - (k : ℝ)⁻¹))
                    (by omega : w + 1 ≤ M + 1))
          _ = ((w : ℝ)⁻¹ - (M : ℝ)⁻¹) +
                  (((M + 1 - 1 : ℕ) : ℝ)⁻¹ - ((M + 1 : ℕ) : ℝ)⁻¹) := by
                  rw [ih hwM]
          _ = (w : ℝ)⁻¹ - ((M + 1 : ℕ) : ℝ)⁻¹ := by
                  rw [hMnat]
                  ring
      · have hwM1 : w = M + 1 := by omega
        subst w
        simp

theorem sum_inv_sq_le_inv {S : Finset ℕ} {w : ℕ} (hw : 1 ≤ w)
    (hS : ∀ p ∈ S, w < p) :
    (∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹) ≤ (w : ℝ)⁻¹ := by
  classical
  by_cases hSne : S.Nonempty
  · let M : ℕ := S.max' hSne
    have hMmem : M ∈ S := S.max'_mem hSne
    have hMgtw : w < M := hS M hMmem
    have hSM : S ⊆ Finset.Icc (w + 1) M := by
      intro p hp
      rw [Finset.mem_Icc]
      constructor
      · have hwp : w < p := hS p hp
        omega
      · exact Finset.le_max' S p hp
    have hMle : w ≤ M := by omega
    have hsum_le_tele : (∑ n ∈ Finset.Icc (w + 1) M,
          (((n - 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹)) = (w : ℝ)⁻¹ - (M : ℝ)⁻¹ :=
      sum_pred_inv_sub_tele w M hMle
    have hMge : 1 ≤ M := by omega
    calc
      (∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹)
          ≤ ∑ p ∈ S, (((p - 1 : ℕ) : ℝ)⁻¹ - (p : ℝ)⁻¹) := by
              refine Finset.sum_le_sum ?_
              intro p hp
              have hwp : w < p := hS p hp
              have hp2 : 2 ≤ p := by omega
              exact inv_sq_le_pred_sub hp2
      _ ≤ ∑ n ∈ Finset.Icc (w + 1) M, (((n - 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg hSM ?_
              intro n hn hnS
              have hnge : w + 1 ≤ n := (Finset.mem_Icc.mp hn).1
              have hn2 : 2 ≤ n := by omega
              exact pred_sub_inv_nonneg hn2
      _ = (w : ℝ)⁻¹ - (M : ℝ)⁻¹ := hsum_le_tele
      _ ≤ (w : ℝ)⁻¹ := by
              have hMR : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
              have hMpos : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr hMR.le
              linarith
  · have hSempty : S = ∅ := by
      ext p
      constructor
      · intro hp
        exact (hSne ⟨p, hp⟩).elim
      · intro hp
        simp at hp
    rw [hSempty]
    simp

end Pointwise

section ProductTools

lemma prod_one_add_le_exp {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∏ i ∈ s, (1 + x i)) ≤ Real.exp (∑ i ∈ s, x i) := by
  classical
  calc
    (∏ i ∈ s, (1 + x i)) ≤ ∏ i ∈ s, Real.exp (x i) := by
            refine Finset.prod_le_prod₀ ?_ ?_
            · intro i hi
              exact add_nonneg zero_le_one (hx i hi)
            · intro i hi
              simpa [add_comm] using (Real.add_one_le_exp (x i))
    _ = Real.exp (∑ i ∈ s, x i) := by rw [Real.exp_sum]

lemma abs_prod_one_add_sub_one_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    |∏ i ∈ s, (1 + x i) - 1| ≤ ∏ i ∈ s, (1 + |x i|) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      let P : ℝ := ∏ i ∈ s, (1 + x i)
      let Q : ℝ := ∏ i ∈ s, (1 + |x i|)
      have hPQ : |P| ≤ Q := by
        dsimp [P, Q]
        calc
          |∏ i ∈ s, (1 + x i)| = ∏ i ∈ s, |1 + x i| := by rw [Finset.abs_prod]
          _ ≤ ∏ i ∈ s, (1 + |x i|) := by
                  refine Finset.prod_le_prod₀ ?_ ?_
                  · intro i hi
                    exact abs_nonneg (1 + x i)
                  · intro i hi
                    simpa using (norm_add_le (1 : ℝ) (x i))
      have hih : |P - 1| ≤ Q - 1 := by
        dsimp [P, Q]
        simpa using ih
      calc
        |∏ i ∈ insert a s, (1 + x i) - 1|
            = |(1 + x a) * P - 1| := by
                simp [P, Finset.prod_insert ha]
        _ ≤ |(1 + x a) * P - P| + |P - 1| := by
                have hsplit : (1 + x a) * P - 1 = ((1 + x a) * P - P) + (P - 1) := by ring
                rw [hsplit]
                simpa using (norm_add_le ((1 + x a) * P - P) (P - 1))
        _ ≤ |x a| * Q + (Q - 1) := by
                have h1 : |(1 + x a) * P - P| ≤ |x a| * Q := by
                  calc
                    |(1 + x a) * P - P| = |x a * P| := by congr 1; ring
                    _ = |x a| * |P| := by rw [abs_mul]
                    _ ≤ |x a| * Q := mul_le_mul_of_nonneg_left hPQ (abs_nonneg (x a))
                exact add_le_add h1 hih
        _ = (1 + |x a|) * Q - 1 := by ring
        _ = ∏ i ∈ insert a s, (1 + |x i|) - 1 := by
                simp [Q, Finset.prod_insert ha]

end ProductTools

section TailProduct

theorem tailProduct_one_add_le (C : ℝ) (w : ℕ) (S : Finset ℕ) (hC : 0 ≤ C)
    (hw : 1 ≤ w) (hS : ∀ p ∈ S, w < p) :
    (∏ p ∈ S, (1 + C / (p : ℝ) ^ 2)) ≤ Real.exp (C / (w : ℝ)) := by
  classical
  calc
    (∏ p ∈ S, (1 + C / (p : ℝ) ^ 2))
        ≤ Real.exp (∑ p ∈ S, (C / (p : ℝ) ^ 2)) := by
            refine prod_one_add_le_exp S (fun p => C / (p : ℝ) ^ 2) ?_
            intro p hp
            have hwp : w < p := hS p hp
            exact div_nonneg hC (sq_nonneg (p : ℝ))
    _ = Real.exp (C * ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹) := by
            congr 1
            calc
              (∑ p ∈ S, C / (p : ℝ) ^ 2)
                  = ∑ p ∈ S, C * ((p : ℝ) ^ 2)⁻¹ := by
                      refine Finset.sum_congr rfl ?_
                      intro p hp
                      ring
              _ = C * ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ Real.exp (C / (w : ℝ)) := by
            have hsum : (∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹) ≤ (w : ℝ)⁻¹ :=
              sum_inv_sq_le_inv (S := S) (w := w) hw hS
            have hmul : C * (∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹) ≤ C * (w : ℝ)⁻¹ := by
              exact mul_le_mul_of_nonneg_left hsum hC
            have hmul2 : C * (w : ℝ)⁻¹ = C / (w : ℝ) := by ring
            rw [hmul2] at hmul
            exact Real.exp_le_exp.mpr hmul

theorem tailProduct_abs_sub_one_le (C : ℝ) (w : ℕ) (S : Finset ℕ) (x : ℕ → ℝ)
    (hC : 0 ≤ C) (hw : 1 ≤ w) (hS : ∀ p ∈ S, w < p)
    (hx : ∀ p ∈ S, |x p| ≤ C / (p : ℝ) ^ 2) :
    |∏ p ∈ S, (1 + x p) - 1| ≤ Real.exp (C / (w : ℝ)) - 1 := by
  classical
  calc
    |∏ p ∈ S, (1 + x p) - 1|
        ≤ ∏ p ∈ S, (1 + |x p|) - 1 := abs_prod_one_add_sub_one_le S x
    _ ≤ Real.exp (∑ p ∈ S, |x p|) - 1 := by
            have hprod : (∏ p ∈ S, (1 + |x p|)) ≤ Real.exp (∑ p ∈ S, |x p|) :=
              prod_one_add_le_exp S (fun p => |x p|) (fun p hp => abs_nonneg (x p))
            linarith
    _ ≤ Real.exp (C / (w : ℝ)) - 1 := by
            have hsum : (∑ p ∈ S, |x p|) ≤ C / (w : ℝ) := by
              calc
                (∑ p ∈ S, |x p|) ≤ ∑ p ∈ S, (C / (p : ℝ) ^ 2) := by
                        refine Finset.sum_le_sum ?_
                        intro p hp
                        exact hx p hp
                _ = C * ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ := by
                        calc
                          (∑ p ∈ S, C / (p : ℝ) ^ 2)
                              = ∑ p ∈ S, C * ((p : ℝ) ^ 2)⁻¹ := by
                                  refine Finset.sum_congr rfl ?_
                                  intro p hp
                                  ring
                          _ = C * ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
                _ ≤ C / (w : ℝ) := by
                        have hsum' : (∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹) ≤ (w : ℝ)⁻¹ :=
                          sum_inv_sq_le_inv (S := S) (w := w) hw hS
                        have hmul : C * (∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹) ≤ C * (w : ℝ)⁻¹ := by
                          exact mul_le_mul_of_nonneg_left hsum' hC
                        have hmul2 : C * (w : ℝ)⁻¹ = C / (w : ℝ) := by ring
                        rw [hmul2] at hmul
                        exact hmul
            have hexp : Real.exp (∑ p ∈ S, |x p|) ≤ Real.exp (C / (w : ℝ)) :=
              Real.exp_le_exp.mpr hsum
            linarith

theorem tendsto_exp_div_sub_one (C : ℝ) :
    Tendsto (fun w : ℕ => Real.exp (C / (w : ℝ)) - 1) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun w : ℕ => C / (w : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have hcon : Tendsto (fun w : ℕ => Real.exp (C / (w : ℝ))) atTop (𝓝 1) := by
    simpa [Function.comp_def] using (Real.continuous_exp.continuousAt.tendsto.comp hdiv)
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa using hcon.sub hc

/-- Per-coordinate per-prime relative error bound used by the composition:
`|∏_{j}(1+e_{j,p}) − 1| ≤ exp(k·C/p²) − 1` for `p ∈ S`. -/
theorem coordProd_per_prime_abs_le (C : ℝ) (p : ℕ) (k : ℕ) (e : Fin k → ℕ → ℝ)
    (he : ∀ j, |e j p| ≤ C / (p : ℝ) ^ 2) :
    |∏ j : Fin k, (1 + e j p) - 1| ≤
      Real.exp ((k : ℝ) * C / (p : ℝ) ^ 2) - 1 := by
  classical
  have h1 := abs_prod_one_add_sub_one_le (Finset.univ : Finset (Fin k)) (fun j => e j p)
  have h2 : (∏ j : Fin k, (1 + |e j p|)) ≤ Real.exp (∑ j : Fin k, |e j p|) :=
    prod_one_add_le_exp (Finset.univ : Finset (Fin k)) (fun j => |e j p|)
      (fun j hj => abs_nonneg (e j p))
  have hsum : (∑ j : Fin k, |e j p|) ≤ (k : ℝ) * C / (p : ℝ) ^ 2 := by
    calc
      (∑ j : Fin k, |e j p|) ≤ ∑ j : Fin k, (C / (p : ℝ) ^ 2) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            exact he j
      _ = (k : ℝ) * C / (p : ℝ) ^ 2 := by
            have hconst : (∑ _j : Fin k, (C / (p : ℝ) ^ 2)) = (k : ℝ) * C / (p : ℝ) ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
              simp [nsmul_eq_mul]
              ring
            exact hconst
  have h3 : Real.exp (∑ j : Fin k, |e j p|) ≤ Real.exp ((k : ℝ) * C / (p : ℝ) ^ 2) :=
    Real.exp_le_exp.mpr hsum
  calc
    |∏ j : Fin k, (1 + e j p) - 1|
        ≤ ∏ j : Fin k, (1 + |e j p|) - 1 := h1
    _ ≤ Real.exp (∑ j : Fin k, |e j p|) - 1 := by linarith
    _ ≤ Real.exp ((k : ℝ) * C / (p : ℝ) ^ 2) - 1 := by linarith

/-- **k-coordinate composition.**  Finite `S` of naturals all `> w ≥ 1`, with
per-coordinate per-prime relative errors `|e_{j,p}| ≤ C/p²`:
`|∏_{p∈S} ∏_{j:Fin k}(1+e_{j,p}) − 1| ≤ exp(k·C/w) − 1` — the product-tail
`1 + o(1)` for the k-fold local factors. -/
theorem coordTailProduct_abs_sub_one_le (C : ℝ) (w : ℕ) (S : Finset ℕ)
    (k : ℕ) (e : Fin k → ℕ → ℝ) (hC : 0 ≤ C) (hw : 1 ≤ w)
    (hS : ∀ p ∈ S, w < p) (he : ∀ j p, p ∈ S → |e j p| ≤ C / (p : ℝ) ^ 2) :
    |∏ p ∈ S, (∏ j : Fin k, (1 + e j p)) - 1| ≤
      Real.exp ((k : ℝ) * C / (w : ℝ)) - 1 := by
  classical
  have hη : ∀ p ∈ S,
      |∏ j : Fin k, (1 + e j p) - 1| ≤ Real.exp ((k : ℝ) * C / (p : ℝ) ^ 2) - 1 := by
    intro p hp
    exact coordProd_per_prime_abs_le C p k e (fun j => he j p hp)
  have hle1 : ∀ p ∈ S,
      (1 + |∏ j : Fin k, (1 + e j p) - 1|) ≤ Real.exp ((k : ℝ) * C / (p : ℝ) ^ 2) := by
    intro p hp
    linarith [hη p hp]
  have hprod : (∏ p ∈ S, (1 + |∏ j : Fin k, (1 + e j p) - 1|)) ≤
      ∏ p ∈ S, Real.exp ((k : ℝ) * C / (p : ℝ) ^ 2) := by
    refine Finset.prod_le_prod₀ ?_ ?_
    · intro p hp
      positivity
    · intro p hp
      exact hle1 p hp
  have hprod2 : (∏ p ∈ S, Real.exp ((k : ℝ) * C / (p : ℝ) ^ 2)) ≤
      Real.exp ((k : ℝ) * C / (w : ℝ)) := by
    calc
      (∏ p ∈ S, Real.exp ((k : ℝ) * C / (p : ℝ) ^ 2))
          = Real.exp (∑ p ∈ S, ((k : ℝ) * C / (p : ℝ) ^ 2)) := by rw [Real.exp_sum]
      _ ≤ Real.exp ((k : ℝ) * C / (w : ℝ)) := by
              apply Real.exp_le_exp.mpr
              have hkC : 0 ≤ (k : ℝ) * C := by positivity
              calc
                (∑ p ∈ S, ((k : ℝ) * C / (p : ℝ) ^ 2))
                    = (k : ℝ) * C * (∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹) := by
                        calc
                          (∑ p ∈ S, ((k : ℝ) * C / (p : ℝ) ^ 2))
                              = ∑ p ∈ S, ((k : ℝ) * C * ((p : ℝ) ^ 2)⁻¹) := by
                                  refine Finset.sum_congr rfl ?_
                                  intro p hp
                                  ring
                          _ = (k : ℝ) * C * (∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹) := by rw [Finset.mul_sum]
                _ ≤ (k : ℝ) * C / (w : ℝ) := by
                        have hsum' : (∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹) ≤ (w : ℝ)⁻¹ :=
                          sum_inv_sq_le_inv (S := S) (w := w) hw hS
                        have hmul : (k : ℝ) * C * (∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹) ≤
                            (k : ℝ) * C * (w : ℝ)⁻¹ := by
                          exact mul_le_mul_of_nonneg_left hsum' hkC
                        have hmul2 : (k : ℝ) * C * (w : ℝ)⁻¹ = (k : ℝ) * C / (w : ℝ) := by ring
                        rw [hmul2] at hmul
                        exact hmul
  calc
    |∏ p ∈ S, (∏ j : Fin k, (1 + e j p)) - 1|
        ≤ ∏ p ∈ S, (1 + |∏ j : Fin k, (1 + e j p) - 1|) - 1 := by
            simpa using (abs_prod_one_add_sub_one_le S (fun p => ∏ j : Fin k, (1 + e j p) - 1))
    _ ≤ ∏ p ∈ S, Real.exp ((k : ℝ) * C / (p : ℝ) ^ 2) - 1 := by
            linarith [hprod]
    _ ≤ Real.exp ((k : ℝ) * C / (w : ℝ)) - 1 := by
            linarith [hprod2]

end TailProduct

end Commons.NumberTheory.MaynardSieve
