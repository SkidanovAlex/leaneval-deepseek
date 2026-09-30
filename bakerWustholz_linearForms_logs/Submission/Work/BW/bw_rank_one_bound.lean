import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.liouville_logForm
import Submission.Work.BW.bw_arith_rank1
import Submission.Work.BW.log_norm_ratCast_ge
import Submission.Work.BW.log_norm_factor_ge
import Submission.Work.BW.log_norm_lamP_ge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

/-- The modified height is at least `1/d`. -/
lemma one_div_finrank_le_modifiedHeight_bw {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (β : K) :
    1 / (Module.finrank ℚ K : ℝ) ≤ BakerWustholz.modifiedHeight φ β := by
  simp only [BakerWustholz.modifiedHeight]
  exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- BW §11, the case of minimal rank `r = 1` (p. 36). If `b` lies in the span of a single row `L`
of an integer matrix and `BH` holds at rank `1`, then `Λ = q·2^v·λ₁` with `|q| ≥ 1/(d 2^v σ₁)`, and
Liouville's estimate applied to the single logarithm `λ₁` of `α'₁` bounds `log|Λ|` below by
`-C(n,d)·max(log B, 1/d)·∏h'(α)`. -/
theorem bw_rank_one_bound {K : Type*} [Field K] [NumberField K] {n : ℕ} (φ : K →+* ℂ)
    (α : Fin n → K) (b : Fin n → ℤ) {B : ℕ} (hB : 2 ≤ B) (hΛ : lam φ α b ≠ 0)
    (v : ℕ) (L : Fin 1 → Fin n → ℤ) (α' : Fin 1 → K) (σ : Fin 1 → ℝ) (c : ℝ) (hc : 1 < c)
    (hBH : BH φ α b v c 1 L α' σ) :
    Real.log ‖lam φ α b‖ ≥
      -(BakerWustholz.C n (Module.finrank ℚ K) * max (Real.log B) (1 / (Module.finrank ℚ K : ℝ))
          * ∏ i, BakerWustholz.modifiedHeight φ (α i)) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    exact absurd (by simp [lam]) hΛ
  have hn1 : 1 ≤ n := hnpos
  obtain ⟨_hlin, hspan, hα', _hkc, hσpos, hσb1, hσb2, hσprod⟩ := hBH
  -- degree
  have hd1 : 1 ≤ Module.finrank ℚ K := by
    have h : 0 < Module.finrank ℚ K := Module.finrank_pos
    omega
  have hdR : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
  set Θ : ℂ := lamP φ α v L 0 with hΘdef
  -- (1) `b` is a rational multiple of the single row `L 0`
  have hrange : Set.range (fun j : Fin 1 => fun i : Fin n => ((L j i : ℤ) : ℚ))
      = {(fun i : Fin n => ((L 0 i : ℤ) : ℚ))} := by
    ext x
    constructor
    · rintro ⟨j, hj⟩
      rw [Set.mem_singleton_iff, ← hj]
      congr 1
      exact Subsingleton.elim j 0
    · rintro hx
      exact ⟨0, hx.symm⟩
  have hspan' : (fun i : Fin n => ((b i : ℤ) : ℚ)) ∈
      Submodule.span ℚ {(fun i : Fin n => ((L 0 i : ℤ) : ℚ))} := by
    rw [← hrange]; exact hspan
  obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.mp hspan'
  have hqrel : ∀ i, (b i : ℚ) = q * (L 0 i : ℚ) := by
    intro i
    have h := congrFun hq i
    simp only [Pi.smul_apply, smul_eq_mul] at h
    simpa using h.symm
  have hbiC : ∀ i, (b i : ℂ) = (q : ℂ) * ((L 0 i : ℤ) : ℂ) := by
    intro i
    have : ((b i : ℚ) : ℂ) = (q : ℂ) * ((L 0 i : ℚ) : ℂ) := by
      rw [hqrel i]; push_cast; ring
    simpa using this
  -- (2) `Λ = q · 2^v · Θ`
  have hS : (∑ i, ((L 0 i : ℤ) : ℂ) * Complex.log (φ (α i)))
      = (2 : ℂ) ^ v * Θ := by
    have h2v : ((2 : ℂ) ^ v) ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [hΘdef, lamP]
    rw [← mul_assoc, mul_inv_cancel₀ h2v, one_mul]
  have hlam_factor : lam φ α b = (q : ℂ) * (2 : ℂ) ^ v * Θ := by
    simp only [lam]
    calc ∑ i, (b i : ℂ) * Complex.log (φ (α i))
        = ∑ i, ((q : ℂ) * ((L 0 i : ℤ) : ℂ)) * Complex.log (φ (α i)) :=
          Finset.sum_congr rfl fun i _ => by rw [hbiC i]
      _ = (q : ℂ) * ∑ i, ((L 0 i : ℤ) : ℂ) * Complex.log (φ (α i)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = (q : ℂ) * (2 : ℂ) ^ v * Θ := by rw [hS]; ring
  -- (3) nonzero-ness
  have hb : ∃ i, b i ≠ 0 := by
    by_contra h
    push Not at h
    exact hΛ (by simp [lam, h])
  obtain ⟨i₀, hi₀⟩ := hb
  have hqne : q ≠ 0 := by
    intro hq0
    refine hi₀ ?_
    have h := hqrel i₀
    rw [hq0, zero_mul] at h
    exact_mod_cast h
  have hΘne : Θ ≠ 0 := by
    intro hΘ0
    exact hΛ (by rw [hlam_factor, hΘ0, mul_zero])
  -- (4) lower bound for `‖q‖`
  have hLbound : ∑ i, |((L 0 i : ℤ) : ℝ)| * (1 / (Module.finrank ℚ K : ℝ)) ≤ 2 ^ v * σ 0 := by
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) (hσb2 0)
    exact mul_le_mul_of_nonneg_left (one_div_finrank_le_modifiedHeight_bw φ (α i)) (abs_nonneg _)
  have hq_ge : Real.log ‖(q : ℂ)‖ ≥
      -((v : ℝ) * Real.log 2 + Real.log (σ 0) + Real.log (Module.finrank ℚ K : ℝ)) :=
    log_norm_ratCast_ge hd1 q (σ 0) (hσpos 0) hqrel ⟨i₀, hi₀⟩ hLbound
  -- (5) lower bound for `‖Θ‖`
  have hΘ_ge : Real.log ‖Θ‖ ≥
      -((Module.finrank ℚ K : ℝ) * (σ 0) + (Module.finrank ℚ K : ℝ) * Real.log 2) :=
    log_norm_lamP_ge φ (α' 0) Θ (σ 0)
      (by rw [hΘdef]; exact (hα' 0).2) (hα' 0).1 hΘne (by rw [hΘdef]; exact hσb1 0)
  -- (6) assemble
  have hmain := log_norm_factor_ge hqne hΘne hq_ge hΘ_ge
  rw [← hlam_factor] at hmain
  -- (7) arithmetic
  have hPpos : 0 < ∏ i, BakerWustholz.modifiedHeight φ (α i) :=
    Finset.prod_pos fun i _ =>
      lt_of_lt_of_le (div_pos one_pos hdR) (one_div_finrank_le_modifiedHeight_bw φ (α i))
  have hPn : ((Module.finrank ℚ K : ℝ)) ^ (-(n : ℤ))
      ≤ ∏ i, BakerWustholz.modifiedHeight φ (α i) := by
    have hbase : (∏ _i : Fin n, (1 / (Module.finrank ℚ K : ℝ)))
        ≤ ∏ i, BakerWustholz.modifiedHeight φ (α i) :=
      Finset.prod_le_prod₀ (fun i _ => le_of_lt (div_pos one_pos hdR))
        (fun i _ => one_div_finrank_le_modifiedHeight_bw φ (α i))
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_div, inv_pow] at hbase
    rw [zpow_neg, zpow_natCast]
    exact hbase
  have hσle : σ 0 ≤ kappa n (Module.finrank ℚ K) 1 v c
      * ∏ i, BakerWustholz.modifiedHeight φ (α i) := by
    simpa [Fin.prod_univ_one] using hσprod
  have harith := bw_arith_rank1 n (Module.finrank ℚ K) v c (σ 0)
    (∏ i, BakerWustholz.modifiedHeight φ (α i)) B hn1 hd1 hc hPpos hPn hB hσle (hσpos 0)
  linarith [hmain, harith]

end Work.BW
