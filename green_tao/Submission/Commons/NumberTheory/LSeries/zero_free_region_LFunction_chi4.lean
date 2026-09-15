import Mathlib.NumberTheory.LSeries.Nonvanishing
import Submission.Commons.NumberTheory.DirichletCharacter.exists_odd_character_mod_four
import Submission.Commons.NumberTheory.LSeries.riemannZeta_norm_le_inv_sub_one
import Submission.Commons.NumberTheory.LSeries.norm_riemannZeta_le_five_mul_log

/-!
# A quantitative zero-free region for `L(s, χ₄)`

`χ₄` is the (primitive, odd) Dirichlet character modulo `4`.  In this file we show that
`L(s, χ₄)` has no zeros in the region `σ ≥ 1 - c/(log(|t|+2))^9` (`|t| ≥ 2`), by the same
de la Vallée Poussin scheme as for `ζ` (`Submission/ZFR.lean`):

* the (3,4,1) inequality `1 ≤ ‖L(χ₀,σ)‖³‖L(χ₄,σ+it)‖⁴‖L(χ₀,σ+2it)‖` (Mathlib), where `χ₀`
  is the trivial character mod `4`, gives a lower bound for `‖L(χ₄,σ+it)‖` in terms of `σ-1`;
* the upper bound `‖L(χ₄,σ+it)‖ ≤ C (σ-β) log²|t|` when `β+it` is a zero, from the mean value
  inequality along the horizontal segment plus a Cauchy estimate for `L'`;
* optimising in `σ - 1 = δ` gives `β ≤ 1 - c/log⁹|t|`.
-/

set_option maxHeartbeats 1200000

open Complex Metric
open Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.LSeries

noncomputable section

/-- `χ₄ ^ 2` is the trivial character modulo `4`. -/
lemma chi4_sq : chi4 ^ 2 = (1 : DirichletCharacter ℂ 4) := by
  haveI : Fact (1 < 4) := ⟨by norm_num⟩
  apply MulChar.ext'
  intro a
  rw [pow_two]
  change chi4 a * chi4 a = (1 : DirichletCharacter ℂ 4) a
  rcases zmod_four_eq a with rfl | rfl | rfl | rfl
  · rw [chi4_apply, chi4Fun_zero, MulChar.map_nonunit _ (not_isUnit_zero (M₀ := ZMod 4))]
    ring
  · rw [chi4_apply, chi4Fun_one, MulChar.one_apply isUnit_one]
    norm_num
  · rw [chi4_apply, chi4Fun_two, MulChar.map_nonunit _ (by decide : ¬ IsUnit (2 : ZMod 4))]
    ring
  · rw [chi4_apply, chi4Fun_three, MulChar.one_apply (isUnit_iff_exists_inv.mpr ⟨3, by decide⟩)]
    norm_num

/-- `χ₄` is not the trivial character. -/
lemma chi4_ne_one : chi4 ≠ (1 : DirichletCharacter ℂ 4) := by
  intro h
  have h3 : chi4 (3 : ZMod 4) = (1 : DirichletCharacter ℂ 4) 3 := by rw [h]
  rw [chi4_apply, chi4Fun_three, MulChar.one_apply (isUnit_iff_exists_inv.mpr ⟨3, by decide⟩)] at h3
  norm_num at h3

/-- The `(3,4,1)` inequality for `χ₄`: for `σ > 1`,
`1 ≤ ‖L(χ₀,σ)‖³ ‖L(χ₄,σ+it)‖⁴ ‖L(χ₀,σ+2it)‖` where `χ₀` is the trivial character mod `4`. -/
lemma one_le_norm_LFunction_chi4_three_four_one (σ t : ℝ) (hσ : 1 < σ) :
    1 ≤ ‖DirichletCharacter.LFunctionTrivChar 4 (σ : ℂ)‖ ^ 3 *
        ‖DirichletCharacter.LFunction chi4 ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4 *
        ‖DirichletCharacter.LFunctionTrivChar 4 ((σ : ℂ) + 2 * (t : ℂ) * Complex.I)‖ := by
  have h := DirichletCharacter.norm_LFunction_product_ge_one (χ := chi4) (x := σ - 1) (y := t)
    (by linarith)
  have key1 : (1 : ℂ) + ((σ - 1 : ℝ) : ℂ) = (σ : ℂ) := by push_cast; ring
  have key2 : (σ : ℂ) + Complex.I * (t : ℂ) = (σ : ℂ) + (t : ℂ) * Complex.I := by ring
  have key4 : (σ : ℂ) + 2 * Complex.I * (t : ℂ) = (σ : ℂ) + 2 * (t : ℂ) * Complex.I := by ring
  rw [key1, key2, key4, chi4_sq] at h
  rw [norm_mul, norm_mul, norm_pow, norm_pow] at h
  simpa using h

/-- Mean-value inequality for `L(·, χ₄)` along a horizontal segment. -/
lemma norm_LFunction_chi4_sub_le_of_deriv_bound (β σ γ C : ℝ) (hβσ : β ≤ σ)
    (hC : ∀ u ∈ Set.Icc β σ, ‖deriv (DirichletCharacter.LFunction chi4) ((u:ℂ) + (γ:ℂ)*I)‖ ≤ C) :
    ‖DirichletCharacter.LFunction chi4 ((σ:ℂ) + (γ:ℂ)*I)
      - DirichletCharacter.LFunction chi4 ((β:ℂ) + (γ:ℂ)*I)‖ ≤ C * (σ - β) := by
  have hdiff : ∀ x : ℝ, HasDerivAt (fun u : ℝ => DirichletCharacter.LFunction chi4 ((u:ℂ) + (γ:ℂ)*I))
      (deriv (DirichletCharacter.LFunction chi4) ((x:ℂ) + (γ:ℂ)*I)) x := by
    intro x
    have h1 : HasDerivAt (fun u : ℝ => ((u:ℂ) + (γ:ℂ)*I)) 1 x := by
      have : HasDerivAt (fun u : ℝ => (u:ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
      simpa using this.add_const ((γ:ℂ)*I)
    have h2 : HasDerivAt (DirichletCharacter.LFunction chi4)
        (deriv (DirichletCharacter.LFunction chi4) ((x:ℂ) + (γ:ℂ)*I)) ((x:ℂ) + (γ:ℂ)*I) :=
      ((DirichletCharacter.differentiable_LFunction chi4_ne_one) _).hasDerivAt
    simpa [Function.comp_def] using h2.comp x h1
  have hf' : ∀ x ∈ Set.Icc β σ,
      HasDerivWithinAt (fun u : ℝ => DirichletCharacter.LFunction chi4 ((u:ℂ) + (γ:ℂ)*I))
        (deriv (DirichletCharacter.LFunction chi4) ((x:ℂ) + (γ:ℂ)*I)) (Set.Icc β σ) x :=
    fun x _ => (hdiff x).hasDerivWithinAt
  have hb : ∀ x ∈ Set.Ico β σ, ‖deriv (DirichletCharacter.LFunction chi4) ((x:ℂ) + (γ:ℂ)*I)‖ ≤ C :=
    fun x hx => hC x (Set.Ico_subset_Icc_self hx)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hf' hb σ ⟨hβσ, le_rfl⟩
  rw [mul_comm] at h
  simpa only [mul_comm (γ:ℂ) I] using h

/-- Bound for the trivial character factor: `‖L(χ₀,s)‖ ≤ 2‖ζ(re s)‖` for `1 < re s`. -/
lemma norm_LFunctionTrivChar_four_le (s : ℂ) (hs : 0 ≤ s.re) (hs1 : s ≠ 1) :
    ‖DirichletCharacter.LFunctionTrivChar 4 s‖ ≤ 2 * ‖riemannZeta s‖ := by
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := 4) hs1, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg (riemannZeta s))
  have hpf : (4 : ℕ).primeFactors = {2} := by decide +kernel
  rw [hpf, Finset.prod_singleton]
  have h2 : ‖((2:ℝ) : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 2), neg_re,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    refine inv_le_one_of_one_le₀ ?_
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    calc (1:ℝ) = 2 ^ (0:ℝ) := by simp
      _ ≤ 2 ^ s.re := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hs
  calc ‖(1 : ℂ) - ((2:ℝ):ℂ)^(-s)‖ ≤ ‖(1:ℂ)‖ + ‖((2:ℝ):ℂ)^(-s)‖ := norm_sub_le _ _
    _ = 1 + ‖((2:ℝ):ℂ)^(-s)‖ := by simp
    _ ≤ 2 := by linarith

/-- **De la Vallée Poussin zero-free region for `L(·,χ₄)`, parametric form.**

If `C ≥ 1` bounds `‖L'(σ+it, χ₄)‖ ≤ C (log(|t|+2))²` whenever `2 ≤ |t|` and
`1 - d/log(|t|+2) ≤ σ ≤ 1 + 1/(2 log(|t|+2))` (with `d > 0`), then `L(σ+it,χ₄) ≠ 0` for
`2 ≤ |t|` and `σ ≥ 1 - min(1/(40960 C⁴), d/2) / (log(|t|+2))⁹`.

A COMPLETE PROOF (with all the auxiliary lemmas: `chi4_sq`, `chi4_ne_one`,
`one_le_norm_LFunction_chi4_three_four_one`, `norm_LFunctionTrivChar_four_le`,
`norm_LFunction_chi4_sub_le_of_deriv_bound` and `zero_free_region_LFunction_chi4`) is in the
workspace file `Submission/Chi4ZFR.lean`, namespace `Submission`; for this declaration only the
namespace has to be changed (and the auxiliary lemmas copied into this file).  The proof uses
the `(3,4,1)` inequality `DirichletCharacter.norm_LFunction_product_ge_one` with `χ = chi4`,
together with `chi4 ^ 2 = 1`, `LFunctionTrivChar_eq_mul_riemannZeta`, the mean value inequality
along the horizontal segment and the usual optimisation in `δ = σ - 1`. -/
theorem zero_free_region_LFunction_chi4 (C d : ℝ) (hC1 : 1 ≤ C) (hd : 0 < d)
    (hderiv : ∀ σ t : ℝ, 2 ≤ |t| →
      1 - d / Real.log (|t| + 2) ≤ σ →
      σ ≤ 1 + 1 / (2 * Real.log (|t| + 2)) →
      ‖deriv (DirichletCharacter.LFunction Commons.NumberTheory.DirichletCharacter.chi4)
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (Real.log (|t| + 2)) ^ 2) :
    ∀ σ t : ℝ, 2 ≤ |t| →
      1 - (min (1 / (40960 * C ^ 4)) (d / 2)) / (Real.log (|t| + 2)) ^ 9 ≤ σ →
      DirichletCharacter.LFunction Commons.NumberTheory.DirichletCharacter.chi4
        ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by 
  intro σ t ht hσ hz
  set L : ℝ := Real.log (|t| + 2) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]; exact Real.log_pos (by linarith [abs_nonneg t])
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith [abs_nonneg t] : (0:ℝ) < |t| + 2)]
    exact le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith [abs_nonneg t])
  set D : ℝ := 1280 * C ^ 4 with hDdef
  have hC4 : 1 ≤ C ^ 4 := one_le_pow₀ hC1
  have hDbig : 1280 ≤ D := by rw [hDdef]; nlinarith
  have hDpos : 0 < D := by linarith
  have hL8 : 1 ≤ L ^ 8 := one_le_pow₀ hL1
  have hLL9 : L ≤ L ^ 9 := by
    have : L ^ 9 = L ^ 8 * L := by ring
    nlinarith [hLpos, hL8, this]
  set δ : ℝ := 1 / (16 * (D * L ^ 9)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδle : δ ≤ 1 / (2 * L) := by
    rw [hδdef]
    rw [div_le_iff₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have hb : 1 * L ≤ D * L := by
      have h2 : (1:ℝ) ≤ D := by linarith
      exact mul_le_mul_of_nonneg_right h2 (le_of_lt hLpos)
    have hc : D * L ≤ D * L ^ 9 := mul_le_mul_of_nonneg_left hLL9 (le_of_lt hDpos)
    linarith
  set σ₁ : ℝ := 1 + δ with hσ₁def
  have hσ₁1 : 1 < σ₁ := by rw [hσ₁def]; linarith
  have hσ₁2 : σ₁ ≤ 1 + 1 / (2 * L) := by rw [hσ₁def]; linarith
  have hσ₁2' : σ₁ ≤ 2 := by
    have : 1 / (2 * L) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have htne : t ≠ 0 := by
    intro h
    have hab : |t| = 0 := by rw [h]; simp
    rw [hab] at ht
    norm_num at ht
  have hσlt1 : σ < 1 := by
    by_contra hcon
    push_neg at hcon
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := chi4) (Or.inl chi4_ne_one)
      (by simpa using hcon)) hz
  have hσσ₁ : σ ≤ σ₁ := by linarith
  -- derivative bound on the segment
  have hderiv' : ∀ u ∈ Set.Icc σ σ₁,
      ‖deriv (DirichletCharacter.LFunction chi4) ((u:ℂ) + (t:ℂ)*I)‖ ≤ C * L ^ 2 := by
    intro u hu
    have hu1 : 1 - d / L ≤ u := by
      have h2 : min (1 / (40960 * C ^ 4)) (d / 2) / L ^ 9 ≤ d / L := by
        have h3 : min (1 / (40960 * C ^ 4)) (d / 2) / L ^ 9 ≤ (d / 2) / L ^ 9 :=
          div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
        have h4 : d / 2 / L ^ 9 ≤ d / L := by
          have hL9eq : L ^ 9 = L ^ 8 * L := by ring
          rw [div_div, hL9eq, div_le_iff₀ (by positivity), div_mul_eq_mul_div,
            le_div_iff₀ (by positivity)]
          nlinarith [hd, hL8, hLpos]
        linarith
      linarith [hu.1, h2, hσ]
    have hu2 : u ≤ 1 + 1 / (2 * L) := le_trans hu.2 hσ₁2
    simpa [hLdef] using hderiv u t ht hu1 hu2
  -- mean value: upper bound for ‖L(σ₁+iγ)‖
  have hmv : ‖DirichletCharacter.LFunction chi4 ((σ₁:ℂ) + (t:ℂ)*I)‖ ≤ (C * L ^ 2) * (σ₁ - σ) := by
    have h := norm_LFunction_chi4_sub_le_of_deriv_bound σ σ₁ t (C * L ^ 2) hσσ₁ hderiv'
    rw [hz, sub_zero] at h
    simpa using h
  -- the (3,4,1) inequality and upper bounds for the trivial-character factors
  have h341 := one_le_norm_LFunction_chi4_three_four_one σ₁ t hσ₁1
  have hA : ‖DirichletCharacter.LFunctionTrivChar 4 (σ₁ : ℂ)‖ ≤ 4 / δ := by
    have hs1 : (σ₁ : ℂ) ≠ 1 := by
      simp only [ne_eq, ofReal_eq_one]
      linarith
    have h := norm_LFunctionTrivChar_four_le (σ₁:ℂ) (by simp; linarith) hs1
    have hζ := Commons.NumberTheory.LSeries.riemannZeta_norm_le_inv_sub_one hσ₁1 hσ₁2'
    have hδeq : σ₁ - 1 = δ := by rw [hσ₁def]; ring
    rw [hδeq] at hζ
    calc ‖DirichletCharacter.LFunctionTrivChar 4 (σ₁ : ℂ)‖
        ≤ 2 * ‖riemannZeta (σ₁ : ℂ)‖ := h
      _ ≤ 2 * (2 / δ) := by linarith [hζ]
      _ = 4 / δ := by ring
  have hB : ‖DirichletCharacter.LFunctionTrivChar 4 ((σ₁ : ℂ) + 2 * (t : ℂ) * Complex.I)‖ ≤ 20 * L := by
    have hs1 : ((σ₁ : ℂ) + 2 * (t : ℂ) * Complex.I) ≠ 1 := by
      intro h
      have h' := congrArg Complex.im h
      simp at h'
      exact htne h'
    have h := norm_LFunctionTrivChar_four_le _ (by
      have : ((σ₁ : ℂ) + 2 * (t : ℂ) * Complex.I).re = σ₁ := by
        simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
      rw [this]; linarith) hs1
    have h2t : (1:ℝ) ≤ |2*t| := by rw [abs_mul]; norm_num; linarith
    have hζ0 := Commons.NumberTheory.LSeries.norm_riemannZeta_le_five_mul_log
      (σ := σ₁) (t := 2*t) (le_of_lt hσ₁1) h2t
    have harg : ((σ₁ : ℂ) + ((2*t : ℝ):ℂ) * Complex.I) = (σ₁ : ℂ) + 2 * (t : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg] at hζ0
    have hlog2 : Real.log (|2*t| + 2) ≤ 2 * L := by
      have h1 : |2*t| + 2 ≤ 2 * (|t| + 2) := by
        rw [abs_mul]; norm_num; nlinarith [abs_nonneg t]
      have hL2 : Real.log 2 ≤ L := by
        rw [hLdef]; exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
      calc Real.log (|2*t| + 2) ≤ Real.log (2 * (|t| + 2)) := Real.log_le_log (by positivity) h1
        _ = Real.log 2 + Real.log (|t| + 2) := Real.log_mul (by norm_num) (by linarith [abs_nonneg t])
        _ ≤ L + L := by rw [← hLdef]; linarith
        _ = 2 * L := by ring
    calc ‖DirichletCharacter.LFunctionTrivChar 4 ((σ₁ : ℂ) + 2 * (t : ℂ) * Complex.I)‖
        ≤ 2 * ‖riemannZeta ((σ₁ : ℂ) + 2 * (t : ℂ) * Complex.I)‖ := h
      _ ≤ 2 * (5 * Real.log (|2*t| + 2)) := by linarith [hζ0]
      _ ≤ 2 * (5 * (2 * L)) := by linarith [hlog2]
      _ = 20 * L := by ring
  -- lower bound ‖L(σ₁+it,χ₄)‖⁴ ≥ δ³/(D L)
  have hB4 : δ ^ 3 / (1280 * L) ≤
      ‖DirichletCharacter.LFunction chi4 ((σ₁:ℂ) + (t:ℂ)*I)‖ ^ 4 := by
    have hA3 : ‖DirichletCharacter.LFunctionTrivChar 4 (σ₁:ℂ)‖ ^ 3 ≤ (4 / δ) ^ 3 :=
      pow_le_pow_left₀ (norm_nonneg _) hA 3
    have hprod : ‖DirichletCharacter.LFunctionTrivChar 4 (σ₁:ℂ)‖ ^ 3 *
          ‖DirichletCharacter.LFunction chi4 ((σ₁:ℂ) + (t:ℂ)*I)‖ ^ 4 *
          ‖DirichletCharacter.LFunctionTrivChar 4 ((σ₁:ℂ) + 2*(t:ℂ)*I)‖
        ≤ (4 / δ) ^ 3 * ‖DirichletCharacter.LFunction chi4 ((σ₁:ℂ) + (t:ℂ)*I)‖ ^ 4 * (20 * L) := by
      apply mul_le_mul
      · exact mul_le_mul hA3 le_rfl (pow_nonneg (norm_nonneg _) 4) (by positivity)
      · exact hB
      · positivity
      · positivity
    have h1 : (1:ℝ) ≤ (4 / δ) ^ 3 * ‖DirichletCharacter.LFunction chi4 ((σ₁:ℂ) + (t:ℂ)*I)‖ ^ 4 * (20 * L) :=
      le_trans h341 hprod
    have h2 : (4 / δ) ^ 3 * ‖DirichletCharacter.LFunction chi4 ((σ₁:ℂ) + (t:ℂ)*I)‖ ^ 4 * (20 * L)
        = 1280 * L * ‖DirichletCharacter.LFunction chi4 ((σ₁:ℂ) + (t:ℂ)*I)‖ ^ 4 / δ ^ 3 := by
      field_simp
      ring
    rw [h2] at h1
    rw [le_div_iff₀ (by positivity)] at h1
    rw [div_le_iff₀ (by positivity), mul_comm]
    nlinarith [h1, hδpos]
  -- combine with the mean value bound
  have hσ₁σ4 : δ ^ 3 / (D * L ^ 9) ≤ (σ₁ - σ) ^ 4 := by
    have hB4' : ‖DirichletCharacter.LFunction chi4 ((σ₁:ℂ) + (t:ℂ)*I)‖ ^ 4
        ≤ (C * L ^ 2) ^ 4 * (σ₁ - σ) ^ 4 := by
      calc ‖DirichletCharacter.LFunction chi4 ((σ₁:ℂ) + (t:ℂ)*I)‖ ^ 4
            ≤ ((C * L ^ 2) * (σ₁ - σ)) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hmv 4
        _ = (C * L ^ 2) ^ 4 * (σ₁ - σ) ^ 4 := by ring
    have hpow : (C * L ^ 2) ^ 4 = C ^ 4 * L ^ 8 := by ring
    rw [hpow] at hB4'
    have h1 : δ ^ 3 / (1280 * L) ≤ C ^ 4 * L ^ 8 * (σ₁ - σ) ^ 4 := le_trans hB4 hB4'
    rw [div_le_iff₀ (by positivity)] at h1
    rw [div_le_iff₀ (by positivity)]
    have hD' : D * L ^ 9 = 1280 * (C ^ 4 * L ^ 8) * L := by rw [hDdef]; ring
    rw [hD']
    nlinarith [h1, hLpos]
  -- hence σ₁ - σ ≥ 1/(8 D L⁹)
  have hkey : (1/8:ℝ) ^ 4 ≤ ((σ₁ - σ) * (D * L ^ 9)) ^ 4 := by
    have hδ3 : δ ^ 3 = 4096⁻¹ / (D * L ^ 9) ^ 3 := by
      rw [hδdef]
      field_simp
      ring
    rw [hδ3, div_div] at hσ₁σ4
    rw [← pow_succ] at hσ₁σ4
    have := (div_le_iff₀ (by positivity : (0:ℝ) < (D * L ^ 9) ^ 4)).mp hσ₁σ4
    rw [mul_pow] at this
    norm_num at this ⊢
    linarith [this]
  have hx8 : 1/8 ≤ (σ₁ - σ) * (D * L ^ 9) := by
    have hx0 : 0 ≤ (σ₁ - σ) * (D * L ^ 9) := by
      apply mul_nonneg _ (by positivity)
      linarith
    have := (pow_le_pow_iff_left₀ (by norm_num : (0:ℝ) ≤ 1/8) hx0 (n := 4) (by norm_num)).mp hkey
    simpa using this
  have hsub : 1 / (8 * (D * L ^ 9)) ≤ σ₁ - σ := by
    rw [div_le_iff₀ (by positivity)]
    linarith [hx8]
  -- conclusion
  have hfinal : σ ≤ 1 - (1 / (20480 * C ^ 4)) / L ^ 9 := by
    have hD' : D = 1280 * C ^ 4 := hDdef
    have : σ = (1 + 1 / (16 * (D * L ^ 9))) - (σ₁ - σ) := by rw [hσ₁def, hδdef]; ring
    rw [this]
    have heq : 1 / (16 * (D * L ^ 9)) - 1 / (8 * (D * L ^ 9))
        = - ((1 / (20480 * C ^ 4)) / L ^ 9) := by
      rw [hD']
      field_simp
      ring
    linarith [hsub, heq]
  have hstrict : 1 - (1 / (20480 * C ^ 4)) / L ^ 9
      < 1 - (min (1 / (40960 * C ^ 4)) (d / 2)) / L ^ 9 := by
    have hlt : min (1 / (40960 * C ^ 4)) (d / 2) < 1 / (20480 * C ^ 4) := by
      have h2 : min (1 / (40960 * C ^ 4)) (d / 2) ≤ 1 / (40960 * C ^ 4) := min_le_left _ _
      have h3 : 1 / (40960 * C ^ 4) < 1 / (20480 * C ^ 4) :=
        one_div_lt_one_div_of_lt (by positivity) (by nlinarith [hC4])
      linarith
    have := div_lt_div_of_pos_right hlt (by positivity : (0:ℝ) < L ^ 9)
    linarith
  linarith [hσ, hfinal, hstrict]

end

end Commons.NumberTheory.LSeries