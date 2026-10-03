import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

namespace Commons.Analysis.HilbertMatrix
open scoped BigOperators ENNReal
open MeasureTheory

private lemma sum_range_rpow_neg_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (N : ℕ) :
    ∑ i ∈ Finset.range N, ((i:ℝ) + 1) ^ (-θ) ≤ (N:ℝ) ^ (1 - θ) / (1 - θ) := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    simp [Real.zero_rpow (show (1:ℝ) - θ ≠ 0 by linarith)]
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_add, Real.one_rpow]
  have hf0 : AntitoneOn (fun x : ℝ => x ^ (-θ)) (Set.Ioi 0) :=
    Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)
  have hf : AntitoneOn (fun x : ℝ => x ^ (-θ)) (Set.Icc 1 (1 + ↑M)) := by
    apply hf0.mono
    intro x hx
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Ioi]
    linarith [hx.1]
  have hint : ∑ i ∈ Finset.range M, ((1:ℝ) + (↑(i + 1) : ℝ)) ^ (-θ)
      ≤ ∫ (x:ℝ) in (1:ℝ)..(1 + ↑M), x ^ (-θ) := hf.sum_le_integral
  have hInt : ∫ (x:ℝ) in (1:ℝ)..(1 + ↑M), x ^ (-θ) = ((1 + (M:ℝ)) ^ (1 - θ) - 1) / (1 - θ) := by
    rw [integral_rpow (Or.inl (by linarith : (-1:ℝ) < -θ)),
        show (-θ) + 1 = 1 - θ by ring, Real.one_rpow]
  have hkey : (∑ k ∈ Finset.range M, ((↑(k + 1) : ℝ) + 1) ^ (-θ))
      = ∑ k ∈ Finset.range M, ((1:ℝ) + (↑(k + 1) : ℝ)) ^ (-θ) := by
    apply Finset.sum_congr rfl; intro k _
    rw [show ((↑(k + 1) : ℝ) + 1) = (1:ℝ) + (↑(k + 1) : ℝ) by ring]
  rw [hkey]
  have h1 : ∑ k ∈ Finset.range M, ((1:ℝ) + (↑(k + 1) : ℝ)) ^ (-θ)
      ≤ ((1 + (M:ℝ)) ^ (1 - θ) - 1) / (1 - θ) := by rw [← hInt]; exact hint
  have hMc : ((M+1 : ℕ) : ℝ) = 1 + (M:ℝ) := by push_cast; ring
  rw [hMc]
  refine le_trans (add_le_add_left h1 1) ?_
  have heq : ((1 + (M:ℝ)) ^ (1 - θ) - 1) / (1 - θ) + 1
      = ((1 + (M:ℝ)) ^ (1 - θ) - θ) / (1 - θ) := by
    rw [eq_div_iff (by linarith : (1:ℝ) - θ ≠ 0), add_mul, one_mul,
      div_mul_cancel₀ _ (by linarith : (1:ℝ) - θ ≠ 0)]
    ring
  rw [heq, div_le_div_iff_of_pos_right (by linarith : (0:ℝ) < 1 - θ)]
  linarith [hθ0]

private lemma summable_one_add_rpow_neg {r : ℝ} (hr : 1 < r) :
    Summable (fun n : ℕ => ((n:ℝ) + 1) ^ (-r)) := by
  have hmain : Summable (fun m : ℕ => ((m:ℝ) ^ r)⁻¹) :=
    (Real.summable_nat_rpow_inv (p := r)).2 hr
  have hshift : Summable (fun n : ℕ => ((((n+1 : ℕ)) : ℝ) ^ r)⁻¹) :=
    (summable_nat_add_iff (f := fun m : ℕ => ((m:ℝ) ^ r)⁻¹) 1).2 hmain
  refine hshift.congr fun n => ?_
  rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ ((n:ℝ) + 1))]
  push_cast
  ring_nf

private lemma weight_term_le {θ : ℝ} (y : ℕ) (k : ℕ) :
    ((k : ℝ) + (y : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) ^ θ)⁻¹
      ≤ ((k:ℝ)+1) ^ (-(1+θ)) := by
  have hk1 : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have h1 : ((k : ℝ) + (y : ℝ) + 1)⁻¹ ≤ ((k : ℝ) + 1)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2
      (by linarith [show (0:ℝ) ≤ (k:ℝ) by positivity])
  calc ((k : ℝ) + (y : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) ^ θ)⁻¹
      ≤ ((k : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) ^ θ)⁻¹ :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (((k : ℝ) + 1) ^ (1 + θ))⁻¹ := by rw [Real.rpow_add hk1, Real.rpow_one, mul_inv]
    _ = ((k:ℝ)+1) ^ (-(1+θ)) := by rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ (k:ℝ)+1)]

theorem weight_summable {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (y : ℕ) :
    Summable (fun k : ℕ => ((k : ℝ) + (y : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) ^ θ)⁻¹) := by
  refine Summable.of_nonneg_of_le (f := fun k : ℕ => ((k:ℝ)+1) ^ (-(1+θ)))
    (fun k => by positivity) (fun k => weight_term_le y k) ?_
  exact summable_one_add_rpow_neg (by linarith : (1:ℝ) < 1 + θ)

theorem weight_tsum_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (y : ℕ) :
    ∑' k : ℕ, ((k : ℝ) + (y : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) ^ θ)⁻¹
      ≤ (1/(θ*(1-θ))) * (((y : ℝ) + 1) ^ θ)⁻¹ := by
  have hf : Summable (fun k : ℕ => ((k : ℝ) + (y : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) ^ θ)⁻¹) :=
    weight_summable hθ0 hθ1 y
  have hA : ∑ i ∈ Finset.range (y+1), ((i:ℝ)+(y:ℝ)+1)⁻¹ * (((i:ℝ)+1)^θ)⁻¹
      ≤ (1/(1-θ)) * (((y:ℝ)+1)^θ)⁻¹ := by
    calc ∑ i ∈ Finset.range (y+1), ((i:ℝ)+(y:ℝ)+1)⁻¹ * (((i:ℝ)+1)^θ)⁻¹
        ≤ ∑ i ∈ Finset.range (y+1), ((y:ℝ)+1)⁻¹ * (((i:ℝ)+1)^θ)⁻¹ := by
          apply Finset.sum_le_sum; intro i hi
          have hi' : ((i:ℝ) + (y:ℝ) + 1)⁻¹ ≤ ((y:ℝ)+1)⁻¹ :=
            (inv_le_inv₀ (by positivity) (by positivity)).2
              (by linarith [show (0:ℝ) ≤ (i:ℝ) by positivity])
          exact mul_le_mul_of_nonneg_right hi' (by positivity)
      _ = ((y:ℝ)+1)⁻¹ * ∑ i ∈ Finset.range (y+1), (((i:ℝ)+1)^θ)⁻¹ := by
          rw [Finset.mul_sum]
      _ = ((y:ℝ)+1)⁻¹ * ∑ i ∈ Finset.range (y+1), ((i:ℝ)+1)^(-θ) := by
          congr 1; apply Finset.sum_congr rfl; intro i _
          rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ (i:ℝ)+1)]
      _ ≤ ((y:ℝ)+1)⁻¹ * (((y+1:ℕ):ℝ)^(1-θ)/(1-θ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact sum_range_rpow_neg_le hθ0 hθ1 (y+1)
      _ = (1/(1-θ)) * (((y:ℝ)+1)^θ)⁻¹ := by
          rw [show (((y+1:ℕ)):ℝ) = (y:ℝ)+1 by push_cast; ring]
          rw [← Real.rpow_neg (by positivity : (0:ℝ) ≤ (y:ℝ)+1) θ]
          rw [show ((y:ℝ)+1)^(-θ) = ((y:ℝ)+1)^(1-θ)/((y:ℝ)+1) by
                rw [show -θ = (1-θ)-1 by ring,
                    Real.rpow_sub (by positivity : (0:ℝ) < (y:ℝ)+1), Real.rpow_one]]
          field_simp
  have hg : Summable (fun i : ℕ => ((i:ℝ)+(y:ℝ)+2)^(-(1+θ))) := by
    refine Summable.of_nonneg_of_le (f := fun i : ℕ => ((i:ℝ)+1)^(-(1+θ)))
      (fun i => by positivity) (fun i => ?_)
      (summable_one_add_rpow_neg (by linarith : (1:ℝ) < 1 + θ))
    have hxy : (i:ℝ) + 1 ≤ (i:ℝ) + (y:ℝ) + 2 :=
      by linarith [show (0:ℝ) ≤ (y:ℝ) by positivity]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hxy (by linarith)
  have hpt : ∀ i : ℕ,
      ((↑(i + (y+1)) : ℝ) + (y:ℝ) + 1)⁻¹ * (((↑(i + (y+1)) : ℝ) + 1) ^ θ)⁻¹
        ≤ ((i:ℝ)+(y:ℝ)+2)^(-(1+θ)) := by
    intro i
    refine le_trans (weight_term_le y (i + (y+1))) (le_of_eq ?_)
    rw [show (↑(i + (y+1)) : ℝ) + 1 = (i:ℝ)+(y:ℝ)+2 by push_cast; ring]
  have hBs : Summable (fun i : ℕ =>
      ((↑(i + (y+1)) : ℝ) + (y:ℝ) + 1)⁻¹ * (((↑(i + (y+1)) : ℝ) + 1) ^ θ)⁻¹) :=
    Summable.of_nonneg_of_le (fun i => by positivity) hpt hg
  have hcomp := Summable.tsum_le_tsum hpt hBs hg
  have hint : ∑' i : ℕ, ((i:ℝ)+(y:ℝ)+2)^(-(1+θ)) ≤ (1/θ) * (((y:ℝ)+1)^θ)⁻¹ := by
    have hphi : AntitoneOn (fun x : ℝ => x^(-(1+θ))) (Set.Ici (((y+1:ℕ):ℝ))) := by
      apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -(1+θ) ≤ 0)).mono
      intro x hx; simp only [Set.mem_Ici] at hx; simp only [Set.mem_Ioi]
      exact lt_of_lt_of_le (by positivity) hx
    have hic : IntegrableOn (fun x : ℝ => x^(-(1+θ))) (Set.Ioi (((y+1:ℕ):ℝ))) :=
      integrableOn_Ioi_rpow_of_lt (by linarith : -(1+θ) < -1) (by positivity : (0:ℝ) < ((y+1:ℕ):ℝ))
    have hnn : ∀ t ∈ Set.Ioi (((y+1:ℕ):ℝ)), 0 ≤ t^(-(1+θ)) := by
      intro t ht
      exact Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le (by positivity : (0:ℝ) < ((y+1:ℕ):ℝ)) (le_of_lt (Set.mem_Ioi.mp ht)))) _
    have h4 := hphi.tsum_comp_add_le_integral (y+1) hic hnn
    have hI : ∫ x in Set.Ioi (((y+1:ℕ):ℝ)), x^(-(1+θ)) = (1/θ) * (((y:ℝ)+1)^θ)⁻¹ := by
      rw [integral_Ioi_rpow_of_lt (by linarith : -(1+θ) < -1) (by positivity : (0:ℝ) < ((y+1:ℕ):ℝ))]
      rw [show (-(1+θ)) + 1 = -θ by ring]
      rw [show (↑(y+1) : ℝ) = (y:ℝ)+1 by push_cast; ring]
      rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ (y:ℝ)+1)]
      field_simp
    have hsum_eq : (∑' n : ℕ, (↑(n + (y+1) + 1) : ℝ)^(-(1+θ)))
        = ∑' i : ℕ, ((i:ℝ)+(y:ℝ)+2)^(-(1+θ)) := by
      apply tsum_congr; intro n
      rw [show ((n + (y+1) + 1 : ℕ) : ℝ) = (n:ℝ)+(y:ℝ)+2 by push_cast; ring]
    rw [hsum_eq, hI] at h4
    exact h4
  rw [← Summable.sum_add_tsum_nat_add (y+1) hf]
  refine le_trans (add_le_add hA (le_trans hcomp hint)) ?_
  have hcoef : 1/(1-θ) + 1/θ = 1/(θ*(1-θ)) := by
    rw [div_add_div _ _ (by linarith : (1:ℝ)-θ ≠ 0) (by linarith : θ ≠ 0)]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have heq : (1/(1-θ)) * (((y:ℝ)+1)^θ)⁻¹ + (1/θ) * (((y:ℝ)+1)^θ)⁻¹
      = (1/(θ*(1-θ))) * (((y:ℝ)+1)^θ)⁻¹ := by rw [← add_mul, hcoef]
  rw [heq]

theorem weight_sum_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (s : Finset ℕ) (y : ℕ) :
    ∑ k ∈ s, ((k : ℝ) + (y : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) ^ θ)⁻¹
      ≤ (1/(θ*(1-θ))) * (((y : ℝ) + 1) ^ θ)⁻¹ := by
  refine le_trans (Summable.sum_le_tsum s (fun k _ => ?_) (weight_summable hθ0 hθ1 y)) (weight_tsum_le hθ0 hθ1 y)
  positivity

theorem hilbert_schur {p q : ℝ} (hpq : p.HolderConjugate q) {K : ℕ → ℕ → ℝ} {w : ℕ → ℝ}
    (hK : ∀ k y, 0 < K k y) (hw : ∀ n, 0 < w n) {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (h1 : ∀ y : ℕ, ∀ s : Finset ℕ, ∑ k ∈ s, K k y * (w k) ^ q ≤ c1 * (w y) ^ q)
    (h2 : ∀ k : ℕ, ∑' y : ℕ, K k y * (w y) ^ p ≤ c2 * (w k) ^ p)
    (h2s : ∀ k : ℕ, Summable (fun y : ℕ => K k y * (w y) ^ p)) :
    ∀ (a : ℕ → ℝ) (s : Finset ℕ), (∀ n, 0 ≤ a n) →
      ∑' y : ℕ, (∑ k ∈ s, a k * K k y) ^ p ≤ c1 ^ (p / q) * c2 * ∑ k ∈ s, (a k) ^ p := by
  intro a s ha
  have hp1 : 1 < p := (Real.holderConjugate_iff.mp hpq).1
  have hq1 : 1 < q := (Real.holderConjugate_iff.mp hpq.symm).1
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hq0 : 0 < q := lt_trans zero_lt_one hq1
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hpqsum : p⁻¹ + q⁻¹ = 1 := hpq.inv_add_inv_eq_one
  have hpq1 : (1:ℝ)/p + 1/q = 1 := by rw [one_div, one_div]; exact hpqsum
  have hc1nn : 0 ≤ c1 ^ (p / q) := Real.rpow_nonneg hc1 _
  have hpq_inv_mul : (1:ℝ)/p * p = 1 := by rw [one_div]; exact inv_mul_cancel₀ hpne
  have hqp_inv_mul : (1:ℝ)/q * q = 1 := by rw [one_div]; exact inv_mul_cancel₀ hqne
  have hqq_inv_mul : q * ((1:ℝ)/q) = 1 := by rw [one_div]; exact mul_inv_cancel₀ hqne
  have h1q_nonneg : (0:ℝ) ≤ 1/q := div_nonneg zero_le_one (le_of_lt hq0)
  have h1p_nonneg : (0:ℝ) ≤ 1/p := div_nonneg zero_le_one (le_of_lt hp0)
  have hTp : ∀ y : ℕ, (∑ k ∈ s, a k * K k y) ^ p
      ≤ c1 ^ (p / q) * (w y) ^ p * ∑ k ∈ s, (a k / w k) ^ p * K k y := by
    intro y
    have hdivnn : ∀ k, 0 ≤ a k / w k := fun k => div_nonneg (ha k) (le_of_lt (hw k))
    have hKpn : ∀ k, 0 ≤ (K k y) ^ (1/p) := fun k => Real.rpow_nonneg (le_of_lt (hK k y)) _
    have hKqn : ∀ k, 0 ≤ (K k y) ^ (1/q) := fun k => Real.rpow_nonneg (le_of_lt (hK k y)) _
    have hB : 0 ≤ ∑ k ∈ s, (a k / w k) ^ p * K k y :=
      Finset.sum_nonneg fun k _ => mul_nonneg (Real.rpow_nonneg (hdivnn k) _) (le_of_lt (hK k y))
    have hhol : ∑ k ∈ s, a k * K k y
        ≤ (∑ k ∈ s, (a k / w k) ^ p * K k y) ^ (1 / p)
          * (∑ k ∈ s, (w k) ^ q * K k y) ^ (1 / q) := by
      have hf : ∀ k ∈ s, 0 ≤ (a k / w k) * (K k y) ^ (1 / p) :=
        fun k _ => mul_nonneg (hdivnn k) (hKpn k)
      have hg : ∀ k ∈ s, 0 ≤ w k * (K k y) ^ (1 / q) :=
        fun k _ => mul_nonneg (le_of_lt (hw k)) (hKqn k)
      have h := Real.inner_le_Lp_mul_Lq_of_nonneg s hpq hf hg
      have e1 : ∑ k ∈ s, ((a k / w k) * (K k y) ^ (1 / p)) * (w k * (K k y) ^ (1 / q))
          = ∑ k ∈ s, a k * K k y := by
        apply Finset.sum_congr rfl; intro k hk
        have hW : w k ≠ 0 := ne_of_gt (hw k)
        have hKw : 0 < K k y := hK k y
        calc ((a k / w k) * (K k y) ^ (1 / p)) * (w k * (K k y) ^ (1 / q))
            = (a k / w k * w k) * ((K k y) ^ (1 / p) * (K k y) ^ (1 / q)) := by ring
          _ = a k * ((K k y) ^ (1 / p) * (K k y) ^ (1 / q)) := by rw [div_mul_cancel₀ _ hW]
          _ = a k * K k y := by
              rw [← Real.rpow_add hKw (1 / p) (1 / q), hpq1, Real.rpow_one]
      have e2 : ∑ k ∈ s, ((a k / w k) * (K k y) ^ (1 / p)) ^ p
          = ∑ k ∈ s, (a k / w k) ^ p * K k y := by
        apply Finset.sum_congr rfl; intro k hk
        have hKw : 0 < K k y := hK k y
        calc ((a k / w k) * (K k y) ^ (1 / p)) ^ p
            = (a k / w k) ^ p * ((K k y) ^ (1 / p)) ^ p :=
              Real.mul_rpow (hdivnn k) (hKpn k)
          _ = (a k / w k) ^ p * K k y := by
              rw [← Real.rpow_mul (le_of_lt hKw) (1 / p) p, hpq_inv_mul, Real.rpow_one]
      have e3 : ∑ k ∈ s, (w k * (K k y) ^ (1 / q)) ^ q
          = ∑ k ∈ s, (w k) ^ q * K k y := by
        apply Finset.sum_congr rfl; intro k hk
        have hKw : 0 < K k y := hK k y
        calc (w k * (K k y) ^ (1 / q)) ^ q
            = (w k) ^ q * ((K k y) ^ (1 / q)) ^ q :=
              Real.mul_rpow (le_of_lt (hw k)) (hKqn k)
          _ = (w k) ^ q * K k y := by
              rw [← Real.rpow_mul (le_of_lt hKw) (1 / q) q, hqp_inv_mul, Real.rpow_one]
      rw [e1, e2, e3] at h
      exact h
    have hwq : (∑ k ∈ s, (w k) ^ q * K k y) ^ (1 / q) ≤ c1 ^ (1 / q) * w y := by
      have hsq : (∑ k ∈ s, (w k) ^ q * K k y) = ∑ k ∈ s, K k y * (w k)^q := by
        apply Finset.sum_congr rfl; intro k hk; ring
      rw [hsq]
      calc (∑ k ∈ s, K k y * (w k) ^ q) ^ (1 / q)
          ≤ (c1 * (w y) ^ q) ^ (1 / q) :=
            Real.rpow_le_rpow
              (Finset.sum_nonneg fun k _ => mul_nonneg (le_of_lt (hK k y)) (Real.rpow_nonneg (le_of_lt (hw k)) _))
              (h1 y s) h1q_nonneg
        _ = c1 ^ (1 / q) * w y := by
            rw [Real.mul_rpow hc1 (Real.rpow_nonneg (le_of_lt (hw y)) _),
                ← Real.rpow_mul (le_of_lt (hw y)) q (1 / q), hqq_inv_mul, Real.rpow_one]
    calc (∑ k ∈ s, a k * K k y) ^ p
        ≤ ((∑ k ∈ s, (a k / w k) ^ p * K k y) ^ (1 / p) * (c1 ^ (1 / q) * w y)) ^ p := by
          apply Real.rpow_le_rpow
            (Finset.sum_nonneg fun k _ => mul_nonneg (ha k) (le_of_lt (hK k y)))
          · exact le_trans hhol (mul_le_mul_of_nonneg_left hwq (Real.rpow_nonneg hB _))
          · exact le_of_lt hp0
      _ = c1 ^ (p / q) * (w y) ^ p * ∑ k ∈ s, (a k / w k) ^ p * K k y := by
          rw [Real.mul_rpow (Real.rpow_nonneg hB _)
                (mul_nonneg (Real.rpow_nonneg hc1 _) (le_of_lt (hw y))),
              Real.mul_rpow (Real.rpow_nonneg hc1 _) (le_of_lt (hw y)),
              ← Real.rpow_mul hB (1 / p) p, hpq_inv_mul, Real.rpow_one,
              ← Real.rpow_mul hc1 (1 / q) p, show (1:ℝ)/q * p = p / q by ring]
          ring
  have hDsum : Summable (fun y : ℕ => c1 ^ (p / q) * (w y) ^ p * ∑ k ∈ s, (a k / w k) ^ p * K k y) := by
    have hinner : Summable (fun y : ℕ => ∑ k ∈ s, (a k / w k) ^ p * (K k y * (w y) ^ p)) :=
      summable_sum (fun k hk => (h2s k).mul_left ((a k / w k) ^ p))
    refine (hinner.mul_left (c1 ^ (p/q))).congr (fun y => ?_)
    show c1 ^ (p/q) * (∑ k ∈ s, (a k/w k)^p * (K k y*(w y)^p))
        = c1 ^ (p/q) * (w y)^p * ∑ k ∈ s, (a k/w k)^p * K k y
    have hsum : (∑ k ∈ s, (a k/w k)^p * (K k y*(w y)^p))
        = (w y)^p * ∑ k ∈ s, (a k/w k)^p * K k y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k hk; ring
    rw [hsum]; ring
  have hTs : Summable (fun y : ℕ => (∑ k ∈ s, a k * K k y) ^ p) :=
    Summable.of_nonneg_of_le
      (fun y => Real.rpow_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg (ha k) (le_of_lt (hK k y))) p)
      hTp hDsum
  have hstep1 := Summable.tsum_le_tsum hTp hTs hDsum
  calc ∑' y : ℕ, (∑ k ∈ s, a k * K k y) ^ p
      ≤ ∑' y : ℕ, c1 ^ (p / q) * (w y) ^ p * ∑ k ∈ s, (a k / w k) ^ p * K k y := hstep1
    _ = c1 ^ (p/q) * ∑ k ∈ s, (a k/w k)^p * ∑' y, K k y * (w y)^p := by
        have hcongr : (fun y => c1^(p/q)*(w y)^p*∑ k∈s, (a k/w k)^p*K k y)
            = fun y => c1^(p/q) * ∑ k∈s, (a k/w k)^p * (K k y*(w y)^p) := by
          funext y; rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k hk; ring
        rw [hcongr, tsum_mul_left]
        congr 1
        rw [Summable.tsum_finsetSum (fun k hk => (h2s k).mul_left ((a k/w k)^p))]
        apply Finset.sum_congr rfl; intro k hk
        rw [tsum_mul_left]
    _ ≤ c1 ^ (p/q) * ∑ k ∈ s, (a k/w k)^p * (c2 * (w k)^p) := by
        apply mul_le_mul_of_nonneg_left _ hc1nn
        apply Finset.sum_le_sum; intro k hk
        exact mul_le_mul_of_nonneg_left (h2 k) (Real.rpow_nonneg (div_nonneg (ha k) (le_of_lt (hw k))) _)
    _ = c1 ^ (p / q) * c2 * ∑ k ∈ s, (a k) ^ p := by
        have hsum2 : ∑ k∈s, (a k/w k)^p * (c2*(w k)^p) = c2 * ∑ k∈s, (a k)^p := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k hk
          have h1 : (a k/w k)^p * (w k)^p = (a k)^p := by
            rw [← Real.mul_rpow (div_nonneg (ha k) (le_of_lt (hw k))) (le_of_lt (hw k)),
                div_mul_cancel₀ _ (ne_of_gt (hw k))]
          rw [show (a k/w k)^p * (c2*(w k)^p) = c2 * ((a k/w k)^p * (w k)^p) by ring, h1]
        rw [hsum2]; ring


variable {s : Finset ℕ}

/-- **Hilbert's inequality**: for `p > 1` the Hilbert matrix `1/(k+y+1)` is bounded on `ℓ^p(ℕ)`.
Proof: Schur test with weight `w k = (k+1)^{-1/p}`; the weighted sums
`∑_k 1/((k+y+1)(k+1)^γ) ≤ A (y+1)^γ` for `0 < γ < 1` follow from the antitone integral test
(`AntitoneOn.tsum_le_integral`). -/
theorem lp_bound {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℝ), (∀ n, 0 ≤ a n) →
      (∃ s : Finset ℕ, ∀ n, n ∉ s → a n = 0) →
      (∑' y : ℕ, (∑ k ∈ s, a k / ((k : ℝ) + (y : ℝ) + 1)) ^ p)
        ≤ C ^ p * ∑ k ∈ s, (a k) ^ p := by
  set q : ℝ := Real.conjExponent p with hqdef
  set α : ℝ := (2*(p+q))⁻¹ with hαdef
  set θ1 : ℝ := p / (2*(p+q)) with hθ1def
  set θ2 : ℝ := q / (2*(p+q)) with hθ2def
  set w : ℕ → ℝ := fun k => ((k:ℝ)+1)^(-α) with hwdef
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpq : p.HolderConjugate q := by rw [hqdef]; exact Real.HolderConjugate.conjExponent hp
  have hq1 : 1 < q := (Real.holderConjugate_iff.mp hpq.symm).1
  have hq0 : 0 < q := lt_trans zero_lt_one hq1
  have hpqsum : p⁻¹ + q⁻¹ = 1 := hpq.inv_add_inv_eq_one
  have hsum_pos : 0 < 2 * (p + q) := by linarith
  have hθ1pos : 0 < θ1 := by rw [hθ1def]; positivity
  have hθ2pos : 0 < θ2 := by rw [hθ2def]; positivity
  have hθ1lt : θ1 < 1 := by rw [hθ1def, div_lt_one hsum_pos]; linarith
  have hθ2lt : θ2 < 1 := by rw [hθ2def, div_lt_one hsum_pos]; linarith
  have hc1pos : 0 < 1/(θ2*(1-θ2)) := one_div_pos.mpr (mul_pos hθ2pos (by linarith))
  have hc2pos : 0 < 1/(θ1*(1-θ1)) := one_div_pos.mpr (mul_pos hθ1pos (by linarith))
  have hαq : α * q = θ2 := by rw [hαdef, hθ2def]; field_simp
  have hαp : α * p = θ1 := by rw [hαdef, hθ1def]; field_simp
  have hwpos : ∀ n, 0 < w n := by intro n; rw [hwdef]; exact Real.rpow_pos_of_pos (by positivity) _
  have hwq : ∀ k, (w k) ^ q = (((k:ℝ)+1) ^ θ2)⁻¹ := by
    intro k
    rw [hwdef, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (k:ℝ)+1) (-α) q,
        show (-α)*q = -θ2 by rw [neg_mul, hαq], Real.rpow_neg (by positivity : (0:ℝ) ≤ (k:ℝ)+1)]
  have hwp : ∀ k, (w k) ^ p = (((k:ℝ)+1) ^ θ1)⁻¹ := by
    intro k
    rw [hwdef, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (k:ℝ)+1) (-α) p,
        show (-α)*p = -θ1 by rw [neg_mul, hαp], Real.rpow_neg (by positivity : (0:ℝ) ≤ (k:ℝ)+1)]
  have h1 : ∀ y : ℕ, ∀ s : Finset ℕ, ∑ k ∈ s, ((k:ℝ)+(y:ℝ)+1)⁻¹ * (w k) ^ q
      ≤ (1/(θ2*(1-θ2))) * (w y) ^ q := by
    intro y s
    calc ∑ k ∈ s, ((k:ℝ)+(y:ℝ)+1)⁻¹ * (w k) ^ q
        = ∑ k ∈ s, ((k:ℝ)+(y:ℝ)+1)⁻¹ * (((k:ℝ)+1) ^ θ2)⁻¹ := by
          apply Finset.sum_congr rfl; intro k _; rw [hwq k]
      _ ≤ (1/(θ2*(1-θ2))) * (((y:ℝ)+1) ^ θ2)⁻¹ := weight_sum_le hθ2pos hθ2lt s y
      _ = (1/(θ2*(1-θ2))) * (w y) ^ q := by rw [hwq y]
  have h2 : ∀ k : ℕ, ∑' y : ℕ, ((k:ℝ)+(y:ℝ)+1)⁻¹ * (w y) ^ p
      ≤ (1/(θ1*(1-θ1))) * (w k) ^ p := by
    intro k
    have hcongr : (fun y : ℕ => ((k:ℝ)+(y:ℝ)+1)⁻¹ * (w y) ^ p)
        = fun y : ℕ => ((y:ℝ)+(k:ℝ)+1)⁻¹ * (((y:ℝ)+1) ^ θ1)⁻¹ := by
      funext y; rw [hwp y]; congr 1; ring
    rw [hcongr]
    calc ∑' y : ℕ, ((y:ℝ)+(k:ℝ)+1)⁻¹ * (((y:ℝ)+1) ^ θ1)⁻¹
        ≤ (1/(θ1*(1-θ1))) * (((k:ℝ)+1) ^ θ1)⁻¹ := weight_tsum_le hθ1pos hθ1lt k
      _ = (1/(θ1*(1-θ1))) * (w k) ^ p := by rw [hwp k]
  have h2s : ∀ k : ℕ, Summable (fun y : ℕ => ((k:ℝ)+(y:ℝ)+1)⁻¹ * (w y) ^ p) := by
    intro k
    have hcongr : (fun y : ℕ => ((k:ℝ)+(y:ℝ)+1)⁻¹ * (w y) ^ p)
        = fun y : ℕ => ((y:ℝ)+(k:ℝ)+1)⁻¹ * (((y:ℝ)+1) ^ θ1)⁻¹ := by
      funext y; rw [hwp y]; congr 1; ring
    rw [hcongr]
    exact weight_summable hθ1pos hθ1lt k
  have hmain : ∀ (a : ℕ → ℝ) (s : Finset ℕ), (∀ n, 0 ≤ a n) →
      ∑' y : ℕ, (∑ k ∈ s, a k * ((k:ℝ)+(y:ℝ)+1)⁻¹) ^ p
        ≤ (1/(θ2*(1-θ2))) ^ (p/q) * (1/(θ1*(1-θ1))) * ∑ k ∈ s, (a k) ^ p :=
    hilbert_schur (K := fun k y : ℕ => ((k:ℝ)+(y:ℝ)+1)⁻¹) (w := w) hpq
      (fun k y => by positivity) hwpos (by positivity) (by positivity) h1 h2 h2s
  set B : ℝ := (1/(θ2*(1-θ2))) ^ (p/q) * (1/(θ1*(1-θ1))) with hBdef
  have hBpos : 0 < B := by
    rw [hBdef]
    exact mul_pos (Real.rpow_pos_of_pos hc1pos _) hc2pos
  set C : ℝ := B ^ (1/p) with hCdef
  have hCpos : 0 < C := by rw [hCdef]; exact Real.rpow_pos_of_pos hBpos _
  have hCpow : C ^ p = B := by
    rw [hCdef, ← Real.rpow_mul (le_of_lt hBpos) (1/p) p,
        show (1:ℝ)/p * p = 1 by rw [one_div]; exact inv_mul_cancel₀ (ne_of_gt hp0), Real.rpow_one]
  refine ⟨C, hCpos, ?_⟩
  intro a ha hs
  have hb := hmain a s ha
  calc ∑' y : ℕ, (∑ k ∈ s, a k / ((k : ℝ) + (y : ℝ) + 1)) ^ p
      = ∑' y : ℕ, (∑ k ∈ s, a k * ((k:ℝ)+(y:ℝ)+1)⁻¹) ^ p := by simp_rw [div_eq_mul_inv]
    _ ≤ (1/(θ2*(1-θ2))) ^ (p/q) * (1/(θ1*(1-θ1))) * ∑ k ∈ s, (a k) ^ p := hb
    _ = C ^ p * ∑ k ∈ s, (a k) ^ p := by rw [hCpow]

end Commons.Analysis.HilbertMatrix