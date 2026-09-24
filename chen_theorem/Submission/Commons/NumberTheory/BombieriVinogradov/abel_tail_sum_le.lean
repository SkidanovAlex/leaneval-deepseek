import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators
open Finset

/-- For `1 ≤ p`, `1/(p+1) ≤ log (p+1) - log p`. -/
lemma inv_succ_le_log_sub {p : ℝ} (hp : 1 ≤ p) :
    (1:ℝ) / (p + 1) ≤ Real.log (p+1) - Real.log p := by
  have hp0 : (0:ℝ) < p := by linarith
  have hx0 : (0:ℝ) < 1/(p+1) := by positivity
  have hle : (1:ℝ)/(p+1) ≤ 1/2 := by
    apply one_div_le_one_div_of_le (show (0:ℝ) < 2 by norm_num); linarith
  have hpos : (0:ℝ) < 1 - 1/(p+1) := by linarith
  have hlog := Real.log_le_sub_one_of_pos hpos
  have hlog2 : Real.log (1 - 1/(p+1)) ≤ -(1/(p+1)) := by linarith
  have hlog_eq : Real.log (1 - 1/(p+1)) = Real.log p - Real.log (p+1) := by
    have h : (1 - 1/(p+1)) = p/(p+1) := by field_simp; ring
    rw [h, Real.log_div (by linarith) (by linarith)]
  rw [hlog_eq] at hlog2
  linarith

/-- Telescoping bound: `∑_{p=R}^{N} 1/(p(p+1)) ≤ 1/R` for `R ≥ 1`. -/
lemma sum_Icc_inv_mul_succ_le_inv (R N : ℕ) (hR : 1 ≤ R) :
    (∑ p ∈ Finset.Icc R N, (1:ℝ) / ((p : ℝ) * ((p + 1 : ℕ) : ℝ))) ≤ 1/(R:ℝ) := by
  by_cases h : R ≤ N
  · have hterm : ∀ p ∈ Finset.Icc R N,
        (1:ℝ) / ((p : ℝ) * ((p + 1 : ℕ) : ℝ)) =
          (-(1:ℝ)/(((p+1:ℕ)):ℝ)) - (-(1:ℝ)/((p:ℝ))) := by
      intro p hp
      have hpR : R ≤ p := (Finset.mem_Icc.mp hp).1
      have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast (le_trans hR hpR)
      rw [Nat.cast_add, Nat.cast_one]
      have hp0 : ((p:ℝ)) ≠ 0 := by linarith
      have hp10 : ((p:ℝ) + 1) ≠ 0 := by linarith
      field_simp
      ring
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_Icc_sub h (fun n => -(1:ℝ)/(n:ℝ))]
    have hpos : (0:ℝ) ≤ 1/(((N+1:ℕ)):ℝ) := by positivity
    have hgoal : -(1:ℝ)/(((N+1:ℕ)):ℝ) - (-(1:ℝ)/(R:ℝ)) = 1/(R:ℝ) - 1/(((N+1:ℕ)):ℝ) := by ring
    rw [hgoal]
    linarith
  · rw [Finset.Icc_eq_empty h, Finset.sum_empty]
    positivity

/-- `∑_{p=R}^{N} 1/(p+1) ≤ log(N+1) - log R` for `1 ≤ R ≤ N+1`. -/
lemma sum_Icc_inv_succ_le_log (R N : ℕ) (hR : 1 ≤ R) (hN : R ≤ N + 1) :
    (∑ p ∈ Finset.Icc R N, (1:ℝ) / (((p + 1 : ℕ)) : ℝ)) ≤
      Real.log ((N:ℝ) + 1) - Real.log (R : ℝ) := by
  by_cases h : R ≤ N
  · have hterm : ∀ p ∈ Finset.Icc R N,
         (1:ℝ) / (((p+1:ℕ)):ℝ) ≤ Real.log (((p+1:ℕ)):ℝ) - Real.log ((p:ℝ)) := by
      intro p hp
      have hpR : R ≤ p := (Finset.mem_Icc.mp hp).1
      have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast (le_trans hR hpR)
      have := inv_succ_le_log_sub hp1
      simpa only [Nat.cast_add, Nat.cast_one] using this
    calc (∑ p ∈ Finset.Icc R N, (1:ℝ) / (((p+1:ℕ)):ℝ))
        ≤ ∑ p ∈ Finset.Icc R N, (Real.log (((p+1:ℕ)):ℝ) - Real.log ((p:ℝ))) :=
          Finset.sum_le_sum hterm
      _ = Real.log (((N+1:ℕ)):ℝ) - Real.log ((R:ℝ)) := Finset.sum_Icc_sub h (fun n => Real.log (n:ℝ))
      _ = Real.log ((N:ℝ) + 1) - Real.log (R : ℝ) := by simp only [Nat.cast_add, Nat.cast_one]
  · have hNR : N + 1 = R := by omega
    rw [Finset.Icc_eq_empty h, Finset.sum_empty]
    have hcast : (((N:ℝ)) + 1) = (R:ℝ) := by
      have : (((N+1:ℕ)):ℝ) = ((R:ℕ):ℝ) := by rw [hNR]
      push_cast at this; linarith
    rw [hcast]
    simp

/-- Reindexing `∑_{R<q≤Q} g(q-1)/q = ∑_{R≤p≤Q-1} g(p)/(p+1)` (`1 ≤ R`). -/
lemma sum_Ioc_pred_div (S : ℕ → ℝ) (R Q : ℕ) (hR : 1 ≤ R) :
    (∑ q ∈ Finset.Ioc R Q, S (q-1) / (q:ℝ)) = ∑ p ∈ Finset.Icc R (Q-1), S p / (((p+1:ℕ)):ℝ) := by
  have himg : Finset.Ioc R Q = (Finset.Icc R (Q-1)).image (fun p => p+1) := by
    ext q
    rw [Finset.mem_Ioc, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨q-1, ?_, ?_⟩
      · rw [Finset.mem_Icc]; omega
      · omega
    · rintro ⟨p, hp, hpq⟩
      rw [Finset.mem_Icc] at hp
      omega
  have hInj : Set.InjOn (fun p : ℕ => p+1) ↑(Finset.Icc R (Q-1)) := by
    intro a _ b _ hab
    have hab' : a + 1 = b + 1 := hab
    omega
  rw [himg, Finset.sum_image hInj]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Nat.add_sub_cancel]

/-- Summation-by-parts bound (Abel step). -/
lemma sum_Ioc_sub_div_le (S : ℕ → ℝ) (hS : ∀ n, 0 ≤ S n) (R Q : ℕ) (hR : 1 ≤ R) (hRQ : R ≤ Q) :
    (∑ q ∈ Finset.Ioc R Q, (S q - S (q - 1)) / (q : ℝ)) ≤
      S Q / (Q : ℝ) + ∑ p ∈ Finset.Icc R (Q - 1), S p / ((p : ℝ) * ((p + 1 : ℕ) : ℝ)) := by
  by_cases hQ : R + 1 ≤ Q
  · have hle : R ≤ Q - 1 := by omega
    have hQ1 : 1 ≤ Q := by omega
    have hpred : (∑ q ∈ Finset.Ioc R Q, S (q-1)/(q:ℝ)) =
        ∑ p ∈ Finset.Icc R (Q-1), S p/(((p+1:ℕ)):ℝ) := sum_Ioc_pred_div S R Q hR
    have hexp : (∑ q ∈ Finset.Ioc R Q, (S q - S (q - 1)) / (q : ℝ))
        = (∑ q ∈ Finset.Ioc R Q, S q/(q:ℝ)) - (∑ q ∈ Finset.Ioc R Q, S (q-1)/(q:ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      rw [sub_div]
    have hfirst : (∑ q ∈ Finset.Ioc R Q, S q/(q:ℝ))
        = S Q/(Q:ℝ) + ∑ q ∈ Finset.Ioc R (Q-1), S q/(q:ℝ) := by
      have h := Finset.sum_Ioc_succ_top (a := R) (b := Q-1) hle (fun q => S q/(q:ℝ))
      rw [Nat.sub_add_cancel hQ1] at h
      rw [h]; ring
    have hsecond : (∑ q ∈ Finset.Ioc R Q, S (q-1)/(q:ℝ))
        = S R/(((R+1:ℕ)):ℝ) + ∑ p ∈ Finset.Ioc R (Q-1), S p/(((p+1:ℕ)):ℝ) := by
      rw [hpred]
      have h := add_sum_Ioc_eq_sum_Icc (f := fun p => S p/(((p+1:ℕ)):ℝ)) hle
      rw [← h]
    have hAB : (∑ q ∈ Finset.Ioc R (Q-1), S q/(q:ℝ)) - (∑ p ∈ Finset.Ioc R (Q-1), S p/(((p+1:ℕ)):ℝ))
        = ∑ q ∈ Finset.Ioc R (Q-1), S q/((q:ℝ)*((q+1:ℕ):ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      have hqR : R ≤ q := (Finset.mem_Ioc.mp hq).1.le
      have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast le_trans hR hqR
      rw [Nat.cast_add, Nat.cast_one]
      have hq0 : ((q:ℝ)) ≠ 0 := by linarith
      have hq10 : ((q:ℝ)+1) ≠ 0 := by linarith
      field_simp
      ring
    have hCbound : (∑ q ∈ Finset.Ioc R (Q-1), S q/((q:ℝ)*((q+1:ℕ):ℝ)))
        ≤ ∑ p ∈ Finset.Icc R (Q-1), S p/((p:ℝ)*((p+1:ℕ):ℝ)) := by
      have h := add_sum_Ioc_eq_sum_Icc (f := fun p => S p/((p:ℝ)*((p+1:ℕ):ℝ))) hle
      rw [← h]
      have hnn : (0:ℝ) ≤ S R/((R:ℝ)*((R+1:ℕ):ℝ)) := by
        apply div_nonneg (hS R); positivity
      linarith
    calc (∑ q ∈ Finset.Ioc R Q, (S q - S (q - 1)) / (q : ℝ))
        = (S Q/(Q:ℝ) + ∑ q ∈ Finset.Ioc R (Q-1), S q/(q:ℝ))
            - (S R/(((R+1:ℕ)):ℝ) + ∑ p ∈ Finset.Ioc R (Q-1), S p/(((p+1:ℕ)):ℝ)) := by
          rw [hexp, hfirst, hsecond]
      _ = S Q/(Q:ℝ) - S R/(((R+1:ℕ)):ℝ)
            + ((∑ q ∈ Finset.Ioc R (Q-1), S q/(q:ℝ))
                - (∑ p ∈ Finset.Ioc R (Q-1), S p/(((p+1:ℕ)):ℝ))) := by ring
      _ = S Q/(Q:ℝ) - S R/(((R+1:ℕ)):ℝ)
            + ∑ q ∈ Finset.Ioc R (Q-1), S q/((q:ℝ)*((q+1:ℕ):ℝ)) := by rw [hAB]
      _ ≤ S Q/(Q:ℝ) + ∑ q ∈ Finset.Ioc R (Q-1), S q/((q:ℝ)*((q+1:ℕ):ℝ)) := by
          have hSR : (0:ℝ) ≤ S R/(((R+1:ℕ)):ℝ) := by
            apply div_nonneg (hS R); positivity
          linarith
      _ ≤ S Q/(Q:ℝ) + ∑ p ∈ Finset.Icc R (Q-1), S p/((p:ℝ)*((p+1:ℕ):ℝ)) := by linarith
  · have hQR : Q = R := by omega
    rw [hQR, Finset.Ioc_self, Finset.sum_empty]
    have hempty : Finset.Icc R (R-1) = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    have : (0:ℝ) ≤ S R/(R:ℝ) := div_nonneg (hS R) (by positivity)
    linarith

/-- **Abel summation step of the Bombieri–Vinogradov argument** (Vaughan §1, final step): if the
partial sums of `q ↦ q·f q` are bounded by `T t ≤ (x + x^{5/6} t + x^{1/2} t²)(log(xt+2))^5`
(which is what the Basic Mean Value bound supplies for
`f q = (φ q)⁻¹ Σ*_{χ primitive mod q} sup_{y ≤ x} ‖ψ(y,χ)‖`), then the tail sum satisfies
`Σ_{R<q≤Q} f q ≤ C (x/R + x^{5/6} log(2Q/R+2) + x^{1/2} Q)(log(xQ+2))^5`.

Proof: `Σ_{q∈(R,Q]} f q = Σ_{q∈(R,Q]}(qfq)/q` and summation by parts against the partial sums of
`q f q` (alternatively: `Σ_{q∈(t,2t]}f q ≤ t⁻¹ Σ_{q∈(t,2t]}q f q ≤ t⁻¹T(2t)`, dyadically in `t`). -/
theorem abel_tail_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℝ) (x Q R : ℕ) (T : ℕ → ℝ),
      0 < x → 1 ≤ R → R ≤ Q → (∀ q : ℕ, 0 ≤ f q) →
      (∀ t : ℕ, T t ≤ ((x : ℝ) + (x : ℝ) ^ (5 / 6 : ℝ) * (t : ℝ) +
            (x : ℝ) ^ (1 / 2 : ℝ) * (t : ℝ) ^ 2) *
          (Real.log ((x : ℝ) * (t : ℝ) + 2)) ^ 5) →
      (∀ t : ℕ, (∑ q ∈ Finset.Icc 1 t, (q : ℝ) * f q) ≤ T t) →
      (∑ q ∈ Finset.Ioc R Q, f q) ≤
        C * ((x : ℝ) / (R : ℝ) + (x : ℝ) ^ (5 / 6 : ℝ) *
              Real.log (2 * ((Q : ℝ) / (R : ℝ)) + 2) + (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ)) *
          (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ 5 := by
  refine ⟨2, by norm_num, ?_⟩
  intro f x Q R T hx hR hRQ hf hT hPS
  have hxpos : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx
  have hxnn : (0:ℝ) ≤ (x:ℝ) := le_of_lt hxpos
  have hQ1 : 1 ≤ Q := le_trans hR hRQ
  have hQ1R : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ1
  set L : ℝ := Real.log ((x:ℝ)*(Q:ℝ)+2) with hLdef
  set S : ℕ → ℝ := fun t => ∑ q ∈ Finset.Icc 1 t, (q:ℝ) * f q with hSdef
  have hSnn : ∀ n, 0 ≤ S n := by
    intro n
    simp only [hSdef]
    apply Finset.sum_nonneg
    intro q hq
    exact mul_nonneg (Nat.cast_nonneg q) (hf q)
  have hSle : ∀ t, S t ≤ ((x:ℝ) + (x:ℝ)^(5/6:ℝ)*(t:ℝ) + (x:ℝ)^(1/2:ℝ)*(t:ℝ)^2) *
      (Real.log ((x:ℝ)*(t:ℝ)+2))^5 := by
    intro t
    simp only [hSdef]
    exact le_trans (hPS t) (hT t)
  have hLnn : (0:ℝ) ≤ L := by
    rw [hLdef]; apply Real.log_nonneg; nlinarith
  have hL5nn : (0:ℝ) ≤ L^5 := by positivity
  -- equality: partial sum quotients
  have hfeq : (∑ q ∈ Finset.Ioc R Q, f q) = ∑ q ∈ Finset.Ioc R Q, (S q - S (q-1))/(q:ℝ) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqmem := Finset.mem_Ioc.mp hq
    have hq1 : 1 ≤ q := by omega
    have hs : S q = S (q-1) + (q:ℝ) * f q := by
      simp only [hSdef]
      have h := Finset.sum_Icc_succ_top (a := 1) (b := q-1) (by omega) (fun p => (p:ℝ) * f p)
      rw [Nat.sub_add_cancel hq1] at h
      exact h
    rw [hs]
    have hq0 : (q:ℝ) ≠ 0 := by
      have h1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
      linarith
    rw [add_sub_cancel_left, mul_div_cancel_left₀ (f q) hq0]
  -- S Q / Q bound
  have hSQ_bound : S Q/(Q:ℝ) ≤
      ((x:ℝ)/(Q:ℝ) + (x:ℝ)^(5/6:ℝ) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)) * L^5 := by
    have hQpos : (0:ℝ) < (Q:ℝ) := by exact_mod_cast hQ1
    have h1 : S Q ≤ ((x:ℝ) + (x:ℝ)^(5/6:ℝ)*(Q:ℝ) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)^2) * L^5 := by
      have hh := hSle Q
      rw [← hLdef] at hh
      exact hh
    calc S Q / (Q:ℝ)
        ≤ (((x:ℝ) + (x:ℝ)^(5/6:ℝ)*(Q:ℝ) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)^2) * L^5) / (Q:ℝ) :=
          div_le_div_of_nonneg_right h1 (le_of_lt hQpos)
      _ = ((x:ℝ)/(Q:ℝ) + (x:ℝ)^(5/6:ℝ) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)) * L^5 := by
          field_simp
  -- pointwise bound for the p-sum
  have hpt : ∀ p ∈ Finset.Icc R (Q-1),
      S p / ((p:ℝ)*((p+1:ℕ):ℝ)) ≤
        L^5 * ((x:ℝ)/((p:ℝ)*((p+1:ℕ):ℝ)) + (x:ℝ)^(5/6:ℝ)/(((p+1:ℕ)):ℝ) + (x:ℝ)^(1/2:ℝ)) := by
    intro p hp
    rw [Nat.cast_add, Nat.cast_one]
    have hpmem := Finset.mem_Icc.mp hp
    have hp1 : 1 ≤ p := le_trans hR hpmem.1
    have hpQ : p ≤ Q := by omega
    have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp1)
    have hpQn : (p:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hpQ
    have hx56nn : (0:ℝ) ≤ (x:ℝ)^(5/6:ℝ) := Real.rpow_nonneg hxnn _
    have hx12nn : (0:ℝ) ≤ (x:ℝ)^(1/2:ℝ) := Real.rpow_nonneg hxnn _
    have hden : (0:ℝ) < (p:ℝ)*((p:ℝ)+1) := by positivity
    have harg_pos : (0:ℝ) < (x:ℝ)*(p:ℝ)+2 := by
      have := mul_nonneg hxnn (le_of_lt hppos); linarith
    have harg_le : (x:ℝ)*(p:ℝ)+2 ≤ (x:ℝ)*(Q:ℝ)+2 := by
      have := mul_le_mul_of_nonneg_left hpQn hxnn; linarith
    have hlog_le : Real.log ((x:ℝ)*(p:ℝ)+2) ≤ L := by
      rw [hLdef]; exact Real.log_le_log harg_pos harg_le
    have hlog_nn : (0:ℝ) ≤ Real.log ((x:ℝ)*(p:ℝ)+2) := by
      apply Real.log_nonneg; nlinarith [mul_nonneg hxnn (le_of_lt hppos)]
    have hpow : (Real.log ((x:ℝ)*(p:ℝ)+2))^5 ≤ L^5 := pow_le_pow_left₀ hlog_nn hlog_le 5
    have hfac_nn : (0:ℝ) ≤ (x:ℝ) + (x:ℝ)^(5/6:ℝ)*(p:ℝ) + (x:ℝ)^(1/2:ℝ)*(p:ℝ)^2 := by
      have a1 := mul_nonneg hxnn (le_of_lt hppos)
      have a2 := mul_nonneg hx56nn (le_of_lt hppos)
      have a3 := mul_nonneg hx12nn (pow_nonneg (le_of_lt hppos) 2)
      linarith
    have hSp : S p ≤ ((x:ℝ) + (x:ℝ)^(5/6:ℝ)*(p:ℝ) + (x:ℝ)^(1/2:ℝ)*(p:ℝ)^2) * L^5 :=
      le_trans (hSle p) (mul_le_mul_of_nonneg_left hpow hfac_nn)
    have key : ((x:ℝ) + (x:ℝ)^(5/6:ℝ)*(p:ℝ) + (x:ℝ)^(1/2:ℝ)*(p:ℝ)^2) * L^5 / ((p:ℝ)*((p:ℝ)+1))
        ≤ L^5 * ((x:ℝ)/((p:ℝ)*((p:ℝ)+1)) + (x:ℝ)^(5/6:ℝ)/((p:ℝ)+1) + (x:ℝ)^(1/2:ℝ)) := by
      have e1 : ((x:ℝ) + (x:ℝ)^(5/6:ℝ)*(p:ℝ) + (x:ℝ)^(1/2:ℝ)*(p:ℝ)^2) / ((p:ℝ)*((p:ℝ)+1))
          = (x:ℝ)/((p:ℝ)*((p:ℝ)+1)) + (x:ℝ)^(5/6:ℝ)/((p:ℝ)+1)
              + (x:ℝ)^(1/2:ℝ)*(p:ℝ)/((p:ℝ)+1) := by
        have hp0 : (p:ℝ) ≠ 0 := by linarith
        have hp10 : (p:ℝ) + 1 ≠ 0 := by linarith
        field_simp
      have e2 : (x:ℝ)^(1/2:ℝ)*(p:ℝ)/((p:ℝ)+1) ≤ (x:ℝ)^(1/2:ℝ) := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < (p:ℝ)+1)]
        nlinarith [hx12nn, hppos]
      have e3 : ((x:ℝ) + (x:ℝ)^(5/6:ℝ)*(p:ℝ) + (x:ℝ)^(1/2:ℝ)*(p:ℝ)^2) * L^5 / ((p:ℝ)*((p:ℝ)+1))
          = L^5 * (((x:ℝ) + (x:ℝ)^(5/6:ℝ)*(p:ℝ) + (x:ℝ)^(1/2:ℝ)*(p:ℝ)^2) / ((p:ℝ)*((p:ℝ)+1))) := by
        rw [mul_comm ((x:ℝ) + (x:ℝ)^(5/6:ℝ)*(p:ℝ) + (x:ℝ)^(1/2:ℝ)*(p:ℝ)^2) (L^5), mul_div_assoc]
      rw [e3, e1]
      apply mul_le_mul_of_nonneg_left _ hL5nn
      linarith
    calc S p / ((p:ℝ)*((p:ℝ)+1))
        ≤ (((x:ℝ) + (x:ℝ)^(5/6:ℝ)*(p:ℝ) + (x:ℝ)^(1/2:ℝ)*(p:ℝ)^2) * L^5) / ((p:ℝ)*((p:ℝ)+1)) :=
          div_le_div_of_nonneg_right hSp (le_of_lt hden)
      _ ≤ L^5 * ((x:ℝ)/((p:ℝ)*((p:ℝ)+1)) + (x:ℝ)^(5/6:ℝ)/((p:ℝ)+1) + (x:ℝ)^(1/2:ℝ)) := key
  have hstep1 : (∑ p ∈ Finset.Icc R (Q-1), S p / ((p:ℝ)*((p+1:ℕ):ℝ)))
      ≤ ∑ p ∈ Finset.Icc R (Q-1),
          L^5 * ((x:ℝ)/((p:ℝ)*((p+1:ℕ):ℝ)) + (x:ℝ)^(5/6:ℝ)/(((p+1:ℕ)):ℝ) + (x:ℝ)^(1/2:ℝ)) :=
    Finset.sum_le_sum hpt
  have hinner : (∑ p ∈ Finset.Icc R (Q-1),
        ((x:ℝ)/((p:ℝ)*((p+1:ℕ):ℝ)) + (x:ℝ)^(5/6:ℝ)/(((p+1:ℕ)):ℝ) + (x:ℝ)^(1/2:ℝ)))
      ≤ (x:ℝ)/(R:ℝ) + (x:ℝ)^(5/6:ℝ)*(Real.log (Q:ℝ) - Real.log (R:ℝ)) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hA : (∑ p ∈ Finset.Icc R (Q-1), (x:ℝ)/((p:ℝ)*((p+1:ℕ):ℝ)))
        = (x:ℝ) * ∑ p ∈ Finset.Icc R (Q-1), (1:ℝ)/((p:ℝ)*((p+1:ℕ):ℝ)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp; ring
    have hB : (∑ p ∈ Finset.Icc R (Q-1), (x:ℝ)^(5/6:ℝ)/(((p+1:ℕ)):ℝ))
        = (x:ℝ)^(5/6:ℝ) * ∑ p ∈ Finset.Icc R (Q-1), (1:ℝ)/(((p+1:ℕ)):ℝ) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp; ring
    have hC : (∑ p ∈ Finset.Icc R (Q-1), (x:ℝ)^(1/2:ℝ))
        = ((Finset.Icc R (Q-1)).card : ℝ) * (x:ℝ)^(1/2:ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hA, hB, hC]
    have h1 : (∑ p ∈ Finset.Icc R (Q-1), (1:ℝ)/((p:ℝ)*((p+1:ℕ):ℝ))) ≤ 1/(R:ℝ) :=
      sum_Icc_inv_mul_succ_le_inv R (Q-1) hR
    have h2 : (∑ p ∈ Finset.Icc R (Q-1), (1:ℝ)/(((p+1:ℕ)):ℝ))
        ≤ Real.log (Q:ℝ) - Real.log (R:ℝ) := by
      have h := sum_Icc_inv_succ_le_log R (Q-1) hR (by omega : R ≤ (Q-1)+1)
      have heq : (((Q - 1 : ℕ) : ℝ) + 1) = ((Q:ℕ):ℝ) := by
        have hh : (((Q - 1 + 1 : ℕ)) : ℝ) = (Q:ℝ) := by rw [Nat.sub_add_cancel hQ1]
        rw [← hh]; push_cast; ring
      rwa [heq] at h
    have h3 : ((Finset.Icc R (Q-1)).card : ℝ) * (x:ℝ)^(1/2:ℝ) ≤ (x:ℝ)^(1/2:ℝ) * (Q:ℝ) := by
      have hcard : (Finset.Icc R (Q-1)).card = Q - R := by
        rw [Nat.card_Icc, Nat.sub_add_cancel hQ1]
      rw [hcard]
      have hle : ((Q - R : ℕ) : ℝ) ≤ (Q:ℝ) := by exact_mod_cast Nat.sub_le Q R
      have hx12 : (0:ℝ) ≤ (x:ℝ)^(1/2:ℝ) := Real.rpow_nonneg hxnn _
      nlinarith [hle, hx12]
    have e1' : (x:ℝ) * (∑ p ∈ Finset.Icc R (Q-1), (1:ℝ)/((p:ℝ)*((p+1:ℕ):ℝ))) ≤ (x:ℝ)/(R:ℝ) := by
      have := mul_le_mul_of_nonneg_left h1 hxnn
      rwa [mul_one_div] at this
    have e2' : (x:ℝ)^(5/6:ℝ) * (∑ p ∈ Finset.Icc R (Q-1), (1:ℝ)/(((p+1:ℕ)):ℝ))
        ≤ (x:ℝ)^(5/6:ℝ) * (Real.log (Q:ℝ) - Real.log (R:ℝ)) :=
      mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hxnn _)
    linarith
  have hpsum : (∑ p ∈ Finset.Icc R (Q-1), S p / ((p:ℝ)*((p+1:ℕ):ℝ)))
      ≤ L^5 * ((x:ℝ)/(R:ℝ) + (x:ℝ)^(5/6:ℝ)*(Real.log (Q:ℝ) - Real.log (R:ℝ)) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)) := by
    refine le_trans hstep1 ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hinner hL5nn
  -- final arithmetic
  have harith : ((x:ℝ)/(Q:ℝ) + (x:ℝ)^(5/6:ℝ) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)
        + ((x:ℝ)/(R:ℝ) + (x:ℝ)^(5/6:ℝ)*(Real.log (Q:ℝ) - Real.log (R:ℝ)) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)))
      ≤ 2 * ((x:ℝ)/(R:ℝ) + (x:ℝ)^(5/6:ℝ)*Real.log (2*((Q:ℝ)/(R:ℝ)) + 2) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)) := by
    have hRpos : (0:ℝ) < (R:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)
    have hRQ' : (R:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hRQ
    have hRpos' : (0:ℝ) < (R:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)
    have hi : (x:ℝ)/(Q:ℝ) ≤ (x:ℝ)/(R:ℝ) := div_le_div_of_nonneg_left hxnn hRpos hRQ'
    have hRne : (R:ℝ) ≠ 0 := ne_of_gt hRpos
    have hQne : (Q:ℝ) ≠ 0 := by positivity
    have hlog_ratio : Real.log ((Q:ℝ)/(R:ℝ)) = Real.log (Q:ℝ) - Real.log (R:ℝ) :=
      Real.log_div hQne hRne
    have hQRge : (1:ℝ) ≤ (Q:ℝ)/(R:ℝ) := by
      rw [le_div_iff₀ hRpos]; linarith
    have hL2_ge : (1:ℝ) ≤ Real.log (2*((Q:ℝ)/(R:ℝ)) + 2) := by
      have h4 : (4:ℝ) ≤ 2*((Q:ℝ)/(R:ℝ)) + 2 := by linarith
      have hlog4 : (1:ℝ) ≤ Real.log 4 := by
        rw [Real.le_log_iff_exp_le (by norm_num)]
        linarith [Real.exp_one_lt_three]
      exact le_trans hlog4 (Real.log_le_log (by norm_num) h4)
    have hlog_le : Real.log (Q:ℝ) - Real.log (R:ℝ) ≤ Real.log (2*((Q:ℝ)/(R:ℝ)) + 2) := by
      rw [← hlog_ratio]
      apply Real.log_le_log
      · positivity
      · nlinarith
    have h56 : (x:ℝ)^(5/6:ℝ) ≤ (x:ℝ)^(5/6:ℝ)*Real.log (2*((Q:ℝ)/(R:ℝ)) + 2) := by
      have := Real.rpow_nonneg hxnn (5/6:ℝ)
      nlinarith
    have h56b : (x:ℝ)^(5/6:ℝ)*(Real.log (Q:ℝ) - Real.log (R:ℝ))
        ≤ (x:ℝ)^(5/6:ℝ)*Real.log (2*((Q:ℝ)/(R:ℝ)) + 2) :=
      mul_le_mul_of_nonneg_left hlog_le (Real.rpow_nonneg hxnn _)
    linarith
  calc (∑ q ∈ Finset.Ioc R Q, f q)
      = (∑ q ∈ Finset.Ioc R Q, (S q - S (q-1))/(q:ℝ)) := hfeq
    _ ≤ S Q/(Q:ℝ) + ∑ p ∈ Finset.Icc R (Q-1), S p/((p:ℝ)*((p+1:ℕ):ℝ)) :=
        sum_Ioc_sub_div_le S hSnn R Q hR hRQ
    _ ≤ ((x:ℝ)/(Q:ℝ) + (x:ℝ)^(5/6:ℝ) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ))*L^5
          + L^5 * ((x:ℝ)/(R:ℝ) + (x:ℝ)^(5/6:ℝ)*(Real.log (Q:ℝ) - Real.log (R:ℝ))
              + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)) := by
        linarith [hSQ_bound, hpsum]
    _ = L^5 * ((x:ℝ)/(Q:ℝ) + (x:ℝ)^(5/6:ℝ) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)
          + ((x:ℝ)/(R:ℝ) + (x:ℝ)^(5/6:ℝ)*(Real.log (Q:ℝ) - Real.log (R:ℝ))
              + (x:ℝ)^(1/2:ℝ)*(Q:ℝ))) := by ring
    _ ≤ L^5 * (2 * ((x:ℝ)/(R:ℝ) + (x:ℝ)^(5/6:ℝ)*Real.log (2*((Q:ℝ)/(R:ℝ)) + 2)
            + (x:ℝ)^(1/2:ℝ)*(Q:ℝ))) := mul_le_mul_of_nonneg_left harith hL5nn
    _ = 2 * ((x:ℝ)/(R:ℝ) + (x:ℝ)^(5/6:ℝ)*Real.log (2*((Q:ℝ)/(R:ℝ)) + 2)
            + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)) * L^5 := by ring
    _ = 2 * ((x:ℝ)/(R:ℝ) + (x:ℝ)^(5/6:ℝ)*Real.log (2*((Q:ℝ)/(R:ℝ)) + 2)
            + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)) * (Real.log ((x:ℝ)*(Q:ℝ)+2))^5 := by rw [hLdef]

end Commons.NumberTheory.BombieriVinogradov