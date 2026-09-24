import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.R_l2

/-!
# GM Lemma 8.2 on an arbitrary interval `[1/C, C]`

`Rfun W v = Σ_{t ∈ W} |v|^{it}` and `T = M N = N^{6/5}`.  This file proves
`Work.GM.S3.R_l2_interval`: for every `C ≥ 1` and every `ε > 0` there are `C' > 0` and `N₀` such
that for `N ≥ N₀`, for every `W ⊆ [0, M N]` that is `(M N)^ε`-separated,
`∫_{1/C}^{C} ‖Rfun W v‖² dv ≤ C' * N^ε * |W|`.

The proof is the one of `Work.GM.S3.R_l2` with `[1,2]` replaced by `[1/C, C]`: expand the square,
integrate termwise using `‖∫_{1/C}^{C} v^{iΔ} dv‖ ≤ 2(C + 1/C)/(1+|Δ|)`, and sum the resulting
`1/(1+|t-t'|)` with the separated reciprocal-sum lemma of `R_l2`.
-/

open Finset
open scoped BigOperators

namespace Work.GM.S3

/-- **The pair integral on `[1/C, C]`.** For `C ≥ 1` and real `Δ`,
`‖∫_{1/C}^{C} v^{iΔ} dv‖ ≤ 2(C + 1/C)/(1+|Δ|)`.

For `Δ ≠ 0` the antiderivative `v^{1+iΔ}/(1+iΔ)` gives the value
`(C^{1+iΔ} - (1/C)^{1+iΔ})/(1+iΔ)`, whose numerator has modulus `≤ C + 1/C`, while
`1 + |Δ| ≤ 2‖1 + iΔ‖`; for `Δ = 0` the integral is `C - 1/C ≤ 2(C + 1/C)`. -/
theorem pair_integral_bound_interval {C : ℝ} (hC : 1 ≤ C) (Δ : ℝ) :
    ‖∫ v in (1 / C)..C, ((v : ℂ) ^ (Complex.I * (Δ : ℂ)))‖
      ≤ 2 * (C + 1 / C) / (1 + |Δ|) := by
  have hCpos : 0 < C := by linarith
  have hICpos : 0 < 1 / C := div_pos one_pos hCpos
  have hICnonneg : 0 ≤ C + 1 / C := le_of_lt (add_pos hCpos hICpos)
  have hden : 0 < 1 + |Δ| := by positivity
  by_cases hΔ : Δ = 0
  · subst hΔ
    have hzero : ∀ v : ℝ, ((v:ℂ)^(Complex.I * ((0:ℝ):ℂ))) = 1 := by
      intro v; rw [Complex.ofReal_zero, mul_zero, Complex.cpow_zero]
    rw [intervalIntegral.integral_congr (fun v _ => hzero v)]
    rw [intervalIntegral.integral_const]
    have hCle : 0 ≤ C - 1/C := by
      have h1 : 1/C ≤ C := by
        rw [div_le_iff₀ hCpos]; nlinarith
      linarith
    have hsmul : ‖(C - 1/C) • (1:ℂ)‖ = |C - 1/C| := by
      rw [norm_smul, Real.norm_eq_abs, norm_one, mul_one]
    rw [hsmul, abs_of_nonneg hCle]
    rw [show (1 + |(0:ℝ)|) = 1 by norm_num, div_one]
    linarith
  · set c : ℂ := 1 + Complex.I * (Δ:ℂ) with hc_def
    have hc_re : c.re = 1 := by rw [hc_def]; simp [Complex.add_re]
    have hc_im : c.im = Δ := by rw [hc_def]; simp [Complex.add_im]
    have hc_ne : c ≠ 0 := by
      intro h
      have h2 : c.im = (0:ℂ).im := by rw [h]
      rw [hc_im] at h2
      simp at h2
      exact hΔ h2
    have huIcc : ∀ v ∈ Set.uIcc (1/C) C, (0:ℝ) < v := by
      intro v hv
      rcases Set.mem_uIcc.mp hv with ⟨h1,_⟩ | ⟨h1,_⟩
      · exact lt_of_lt_of_le hICpos h1
      · exact lt_of_lt_of_le hCpos h1
    have hderiv : ∀ v ∈ Set.uIcc (1/C) C,
        HasDerivAt (fun v : ℝ => (v:ℂ)^c / c) ((v:ℂ)^(Complex.I * (Δ:ℂ))) v := by
      intro v hv
      have hv1 : (0:ℝ) < v := huIcc v hv
      have hbase : (v:ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hv1
      have h1 : HasDerivAt (fun v : ℝ => (v:ℂ)) 1 v := by
        simpa using HasDerivAt.ofReal_comp (hasDerivAt_id v)
      have hg : HasDerivAt (fun z : ℂ => z^c) (c * (v:ℂ)^(c-1)) (v:ℂ) :=
        (Complex.hasStrictDerivAt_cpow_const hbase).hasDerivAt
      have h2 : HasDerivAt (fun v : ℝ => (v:ℂ)^c) ((c * (v:ℂ)^(c-1)) * 1) v := hg.comp v h1
      have h3 := h2.div_const c
      have hgoal : (c * (v:ℂ)^(c-1)) * 1 / c = (v:ℂ)^(Complex.I * (Δ:ℂ)) := by
        rw [mul_one, mul_div_cancel_left₀ _ hc_ne]
        have hc1 : c - 1 = Complex.I * (Δ:ℂ) := by rw [hc_def]; ring
        rw [hc1]
      rwa [hgoal] at h3
    have hint : IntervalIntegrable (fun v : ℝ => (v:ℂ)^(Complex.I*(Δ:ℂ)))
        MeasureTheory.volume (1/C) C := by
      apply ContinuousOn.intervalIntegrable
      exact ContinuousOn.cpow_const (f := fun v : ℝ => (v:ℂ)) Complex.continuous_ofReal.continuousOn
        (fun v hv => Complex.ofReal_mem_slitPlane.mpr (huIcc v hv))
    have hmain : ∫ v in (1/C)..C, (v:ℂ)^(Complex.I*(Δ:ℂ))
        = (((C:ℝ):ℂ)^c - (((1/C:ℝ):ℂ))^c)/c := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, ← sub_div]
    rw [hmain]
    have hnormC : ‖((C:ℝ):ℂ)^c‖ = C := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hCpos, hc_re, Real.rpow_one]
    have hnormIC : ‖(((1/C:ℝ)):ℂ)^c‖ = 1/C := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hICpos, hc_re, Real.rpow_one]
    have hnormc1 : (1:ℝ) ≤ ‖c‖ := by
      have h' := Complex.abs_re_le_norm c
      rwa [hc_re, abs_one] at h'
    have hnormcD : |Δ| ≤ ‖c‖ := by
      have h' := Complex.abs_im_le_norm c
      rwa [hc_im] at h'
    have hpos : 0 < ‖c‖ := lt_of_lt_of_le zero_lt_one hnormc1
    have hnum : ‖((C:ℝ):ℂ)^c - (((1/C:ℝ)):ℂ)^c‖ ≤ C + 1/C := by
      calc ‖((C:ℝ):ℂ)^c - (((1/C:ℝ)):ℂ)^c‖
          ≤ ‖((C:ℝ):ℂ)^c‖ + ‖(((1/C:ℝ)):ℂ)^c‖ := norm_sub_le _ _
        _ = C + 1/C := by rw [hnormC, hnormIC]
    calc ‖((((C:ℝ):ℂ)^c - (((1/C:ℝ)):ℂ)^c)/c)‖
        = ‖((C:ℝ):ℂ)^c - (((1/C:ℝ)):ℂ)^c‖/‖c‖ := norm_div _ _
      _ ≤ (C + 1/C)/‖c‖ := div_le_div_of_nonneg_right hnum (le_of_lt hpos)
      _ ≤ 2*(C+1/C)/(1+|Δ|) := by
            rw [div_le_div_iff₀ hpos hden]
            have h : 1 + |Δ| ≤ 2 * ‖c‖ := by linarith
            calc (C + 1/C) * (1 + |Δ|) ≤ (C + 1/C) * (2 * ‖c‖) :=
                  mul_le_mul_of_nonneg_left h hICnonneg
              _ = 2 * (C + 1/C) * ‖c‖ := by ring

/-- **GM (7.2) expansion on `[a,b]`** (`0 < a`, so the integrand is smooth there):
`∫_a^b ‖Rfun W v‖² dv = Re Σ_{t,t' ∈ W} ∫_a^b v^{i(t-t')} dv`. -/
theorem R_l2_expansion_interval (W : Finset ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ v in a..b, ‖Submission.GM.Rfun W v‖ ^ 2
      = Complex.re (∑ t ∈ W, ∑ t' ∈ W,
          ∫ v in a..b, ((v : ℂ) ^ (Complex.I * ((t - t') : ℂ)))) := by
  have hpt : ∀ v ∈ Set.uIcc a b,
      ((‖Submission.GM.Rfun W v‖ ^ 2 : ℝ) : ℂ)
        = ∑ t ∈ W, ∑ t' ∈ W, (v : ℂ) ^ (Complex.I * ((t - (t':ℝ)) : ℂ)) := by
    intro v hv
    have hv1 : (0:ℝ) < v := by
      rcases Set.mem_uIcc.mp hv with ⟨h1,_⟩ | ⟨h1,_⟩
      · exact lt_of_lt_of_le ha h1
      · exact lt_of_lt_of_le hb h1
    have hvne : ((v:ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt hv1
    have habs : (|v| : ℝ) = v := abs_of_pos hv1
    have hnorm : ∀ s : ℝ, ‖((v:ℂ)) ^ (Complex.I * (s:ℂ))‖ = 1 := by
      intro s; rw [Complex.norm_cpow_eq_rpow_re_of_pos hv1]; simp
    have hconj : star (Submission.GM.Rfun W v)
        = ∑ t' ∈ W, (v:ℂ) ^ (-(Complex.I * ((t':ℝ):ℂ))) := by
      rw [Submission.GM.Rfun, star_sum]
      refine Finset.sum_congr rfl fun t' ht' => ?_
      rw [habs, Complex.star_def, ← Complex.inv_eq_conj (hnorm t'), ← Complex.cpow_neg]
    calc ((‖Submission.GM.Rfun W v‖ ^ 2 : ℝ) : ℂ)
        = Submission.GM.Rfun W v * star (Submission.GM.Rfun W v) := by
          rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      _ = (∑ t ∈ W, ((v:ℂ)) ^ (Complex.I * (t:ℂ))) *
            (∑ t' ∈ W, (v:ℂ) ^ (-(Complex.I * ((t':ℝ):ℂ)))) := by
          rw [hconj]
          congr 1
          rw [Submission.GM.Rfun]
          refine Finset.sum_congr rfl fun t ht => ?_
          rw [habs]
      _ = ∑ t ∈ W, ∑ t' ∈ W, ((v:ℂ)) ^ (Complex.I * (t:ℂ)) *
            ((v:ℂ)) ^ (-(Complex.I * ((t':ℝ):ℂ))) :=
          Finset.sum_mul_sum W W _ _
      _ = ∑ t ∈ W, ∑ t' ∈ W, ((v:ℂ)) ^ (Complex.I * ((t - t') : ℂ)) := by
          refine Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun t' ht' => ?_
          rw [← Complex.cpow_add _ _ hvne]
          congr 1
          ring
  have hcontOn : ∀ (Δ : ℂ), ContinuousOn
      (fun v : ℝ => ((v:ℂ) ^ (Complex.I * Δ))) (Set.uIcc a b) := by
    intro Δ
    exact ContinuousOn.cpow_const (f := fun v : ℝ => (v:ℂ)) Complex.continuous_ofReal.continuousOn
      (fun v hv => Complex.ofReal_mem_slitPlane.mpr (by
        rcases Set.mem_uIcc.mp hv with ⟨h1,_⟩ | ⟨h1,_⟩
        · exact lt_of_lt_of_le ha h1
        · exact lt_of_lt_of_le hb h1))
  have hcont : ∀ (Δ : ℂ), IntervalIntegrable
      (fun v : ℝ => ((v:ℂ) ^ (Complex.I * Δ))) MeasureTheory.volume a b :=
    fun Δ => (hcontOn Δ).intervalIntegrable
  have h1 : ∫ v in a..b, ((‖Submission.GM.Rfun W v‖ ^ 2 : ℝ) : ℂ)
      = ∫ v in a..b, ∑ t ∈ W, ∑ t' ∈ W, (v:ℂ) ^ (Complex.I * ((t - t') : ℂ)) :=
    intervalIntegral.integral_congr hpt
  rw [intervalIntegral.integral_ofReal] at h1
  have h2 : ∫ v in a..b, ∑ t ∈ W, ∑ t' ∈ W, (v:ℂ) ^ (Complex.I * ((t - t') : ℂ))
      = ∑ t ∈ W, ∑ t' ∈ W, ∫ v in a..b, (v:ℂ) ^ (Complex.I * ((t - t') : ℂ)) := by
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun t ht => ?_
      rw [intervalIntegral.integral_finsetSum]
      intro t' ht'
      exact hcont ((t - t') : ℂ)
    · intro t ht
      exact (continuousOn_finsetSum W (fun t' ht' => hcontOn ((t - t') : ℂ))).intervalIntegrable
  have h3 := congrArg Complex.re h1
  simp only [Complex.ofReal_re] at h3
  rw [h2] at h3
  exact h3

/-- The elementary estimate `18 + 12 log(N^{6/5}+2) ≤ (18 + 24·3^{ε/2}/ε) N^ε` for `N ≥ 1`. -/
private lemma log_bound_interval (ε : ℝ) (hε : 0 < ε) (N : ℕ) (hN : 1 ≤ N) :
    18 + 12 * Real.log ((N:ℝ) ^ (6/5:ℝ) + 2)
      ≤ (18 + 24 * 3 ^ (ε/2) / ε) * (N:ℝ) ^ ε := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le zero_lt_one hN1
  set x : ℝ := (N:ℝ) with hx
  have hx1 : 1 ≤ x := hN1
  have hxpos : 0 < x := hNpos
  have hP1 : (1:ℝ) ≤ x ^ ε := Real.one_le_rpow hx1 (le_of_lt hε)
  have hxT1 : (1:ℝ) ≤ x ^ (6/5:ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hlog : Real.log (x ^ (6/5:ℝ) + 2)
      ≤ 2 * (x ^ (6/5:ℝ) + 2) ^ (ε/2) / ε := by
    have h := Real.log_le_rpow_div (x := x ^ (6/5:ℝ) + 2) (ε := ε/2)
      (by positivity) (by linarith)
    have h2 : (x ^ (6/5:ℝ) + 2) ^ (ε/2) / (ε/2)
        = 2 * (x ^ (6/5:ℝ) + 2) ^ (ε/2) / ε := by
      field_simp
    linarith [h, h2.symm.le, h2.le]
  have hstep : (x ^ (6/5:ℝ) + 2) ^ (ε/2) ≤ 3 ^ (ε/2) * x ^ ε := by
    have hle : x ^ (6/5:ℝ) + 2 ≤ 3 * x ^ (6/5:ℝ) := by linarith
    have h1 : (x ^ (6/5:ℝ) + 2) ^ (ε/2) ≤ (3 * x ^ (6/5:ℝ)) ^ (ε/2) :=
      Real.rpow_le_rpow (by positivity) hle (by positivity)
    have h2 : (3 * x ^ (6/5:ℝ)) ^ (ε/2) = 3 ^ (ε/2) * x ^ (3*ε/5) := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      congr 1
      rw [← Real.rpow_mul (le_of_lt hxpos)]
      congr 1
      ring
    have h3 : x ^ (3*ε/5) ≤ x ^ ε := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h4 : (0:ℝ) ≤ 3 ^ (ε/2) := by positivity
    calc (x ^ (6/5:ℝ) + 2) ^ (ε/2) ≤ (3 * x ^ (6/5:ℝ)) ^ (ε/2) := h1
      _ = 3 ^ (ε/2) * x ^ (3*ε/5) := h2
      _ ≤ 3 ^ (ε/2) * x ^ ε := by exact mul_le_mul_of_nonneg_left h3 h4
  have hL : 12 * Real.log (x ^ (6/5:ℝ) + 2) ≤ 24 * 3 ^ (ε/2) * x ^ ε / ε := by
    have h3 : 2 * (x ^ (6/5:ℝ) + 2) ^ (ε/2) / ε ≤ 2 * (3 ^ (ε/2) * x ^ ε) / ε := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hε)
      linarith
    have h4 : 12 * (2 * (3 ^ (ε/2) * x ^ ε) / ε) = 24 * 3 ^ (ε/2) * x ^ ε / ε := by ring
    linarith [hlog, hstep, h3, h4.le, h4.ge]
  have hgoal : 18 + 12 * Real.log (x ^ (6/5:ℝ) + 2)
      ≤ (18 + 24 * 3 ^ (ε/2) / ε) * x ^ ε := by
    have h5 : 24 * 3 ^ (ε/2) * x ^ ε / ε = (24 * 3 ^ (ε/2) / ε) * x ^ ε := by ring
    have h6 : (18 + 24 * 3 ^ (ε/2) / ε) * x ^ ε
        = 18 * x ^ ε + (24 * 3 ^ (ε/2) / ε) * x ^ ε := by ring
    rw [h5] at hL
    rw [h6]
    nlinarith [hL, hP1]
  rwa [hx] at hgoal

/-- **GM Lemma 8.2 on an arbitrary fixed interval `[1/C, C]`.**

The assembly of §10 integrates `|R|²` against the bump `ψ₂`, whose support is `[1/4,4]` rather than
`[1,2]`; the `L²` bound is needed on that interval.  The statement is `Work.GM.S3.R_l2` with
`[1,2]` replaced by `[1/C, C]` (the constant `C'` may depend on `C`, and `C` is quantified before
`C'`):

for every `C ≥ 1` and every `ε > 0` there are `C' > 0`, `N₀` such that for every `N ≥ N₀` and every
`W ⊆ [0, M N]` that is `(M N)^ε`-separated,

`∫_{1/C}^{C} ‖R(v)‖² dv ≤ C' * N^ε * |W|`.

Proof: identical to `Work.GM.S3.R_l2` (which is the special case `C = 2`): expand the square and use
`∫_{1/C}^{C} v^{i τ} dv ≪_C 1/(1+|τ|)`, with separation `(M N)^ε` killing the off-diagonal terms. -/
theorem R_l2_interval :
    ∀ C : ℝ, 1 ≤ C → ∀ ε : ℝ, 0 < ε → ∃ C' : ℝ, 0 < C' ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
      ∫ v in (1 / C)..C, ‖Submission.GM.Rfun W v‖ ^ 2 ≤ C' * (N : ℝ) ^ ε * (W.card : ℝ) := by
  intro C hC ε hε
  refine ⟨2 * (C + 1/C) * ((18 + 24 * 3 ^ (ε/2) / ε) / 6), ?_, 1, ?_⟩
  · have hCpos : 0 < C := by linarith
    have hICpos : 0 < 1 / C := div_pos one_pos hCpos
    have h1 : 0 < 2 * (C + 1/C) := by
      have : 0 < C + 1/C := add_pos hCpos hICpos
      linarith
    have h2 : 0 < (18 + 24 * 3 ^ (ε/2) / ε) / 6 := by
      have h3 : 0 < (3:ℝ) ^ (ε/2) := by positivity
      have h4 : 0 < 24 * 3 ^ (ε/2) / ε := div_pos (by positivity) hε
      have h5 : 0 < 18 + 24 * 3 ^ (ε/2) / ε := by linarith
      exact div_pos h5 (by norm_num)
    exact mul_pos h1 h2
  · intro N hN W hsub hsep
    have hCpos : 0 < C := by linarith
    have hICpos : 0 < 1 / C := div_pos one_pos hCpos
    have hKpos : 0 < 2 * (C + 1/C) := by
      have : 0 < C + 1/C := add_pos hCpos hICpos
      linarith
    have hKnonneg : 0 ≤ 2 * (C + 1/C) := le_of_lt hKpos
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hT1 : (1:ℝ) ≤ Submission.LargeValues.M N := Submission.LargeValues.M_ge_one hN
    have hTpos : (0:ℝ) < Submission.LargeValues.M N := Submission.LargeValues.M_pos hN
    have hδ1 : (1:ℝ) ≤ (Submission.LargeValues.M N) ^ ε := Real.one_le_rpow hT1 (le_of_lt hε)
    have hδpos : (0:ℝ) < (Submission.LargeValues.M N) ^ ε :=
      Real.rpow_pos_of_pos hTpos ε
    have hcard0 : (0:ℝ) ≤ (W.card : ℝ) := by positivity
    have hstep1 : ∫ v in (1/C)..C, ‖Submission.GM.Rfun W v‖ ^ 2
        ≤ (2 * (C + 1/C)) * (∑ t ∈ W, ∑ t' ∈ W, 1 / (1 + |t - t'|)) := by
      rw [R_l2_expansion_interval W (1/C) C hICpos hCpos]
      calc Complex.re (∑ t ∈ W, ∑ t' ∈ W,
              ∫ v in (1/C)..C, (v:ℂ)^(Complex.I*((t - t') : ℂ)))
          = ∑ t ∈ W, ∑ t' ∈ W,
              Complex.re (∫ v in (1/C)..C, (v:ℂ)^(Complex.I*((t - t') : ℂ))) := by
            rw [Complex.re_sum]
            refine Finset.sum_congr rfl fun t ht => ?_
            rw [Complex.re_sum]
        _ ≤ ∑ t ∈ W, ∑ t' ∈ W,
              ‖∫ v in (1/C)..C, (v:ℂ)^(Complex.I*((t - t') : ℂ))‖ :=
            Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun t' ht' => Complex.re_le_norm _
        _ ≤ ∑ t ∈ W, ∑ t' ∈ W, 2 * (C + 1/C) / (1 + |t - t'|) :=
            Finset.sum_le_sum fun t ht =>
              Finset.sum_le_sum fun t' ht' =>
                (by simpa [Complex.ofReal_sub] using pair_integral_bound_interval hC (t - t'))
        _ = (2 * (C + 1/C)) * ∑ t ∈ W, ∑ t' ∈ W, 1 / (1 + |t - t'|) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun t ht => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun t' ht' => ?_
            ring
    have hstep2 : (∑ t ∈ W, ∑ t' ∈ W, 1 / (1 + |t - t'|))
        ≤ (W.card : ℝ) * (1 + 2 * (1 + Real.log (Submission.LargeValues.M N /
            (Submission.LargeValues.M N) ^ ε + 2)) / (Submission.LargeValues.M N) ^ ε) :=
      sep_recip_sum W ((Submission.LargeValues.M N) ^ ε) (Submission.LargeValues.M N) hδpos hsub
        (fun t ht s hs hts => hsep t ht s hs hts)
    have hstep3 : 1 + 2 * (1 + Real.log (Submission.LargeValues.M N /
            (Submission.LargeValues.M N) ^ ε + 2)) / (Submission.LargeValues.M N) ^ ε
        ≤ 1 + 2 * (1 + Real.log (Submission.LargeValues.M N + 2)) := by
      have hT0 : (0:ℝ) ≤ Submission.LargeValues.M N := le_of_lt hTpos
      have hdiv : Submission.LargeValues.M N / (Submission.LargeValues.M N) ^ ε
          ≤ Submission.LargeValues.M N := by
        rw [div_le_iff₀ hδpos]
        nlinarith [hT0, hδ1]
      have hlog : Real.log (Submission.LargeValues.M N / (Submission.LargeValues.M N) ^ ε + 2)
          ≤ Real.log (Submission.LargeValues.M N + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have hb : (0:ℝ) ≤ 1 + Real.log (Submission.LargeValues.M N + 2) := by
        have h2 : (0:ℝ) ≤ Real.log (Submission.LargeValues.M N + 2) :=
          Real.log_nonneg (by linarith)
        linarith
      have h1 : 2 * (1 + Real.log (Submission.LargeValues.M N /
          (Submission.LargeValues.M N) ^ ε + 2)) / (Submission.LargeValues.M N) ^ ε
          ≤ 2 * (1 + Real.log (Submission.LargeValues.M N + 2)) := by
        rw [div_le_iff₀ hδpos]
        nlinarith [hlog, hb, hδ1]
      linarith
    have hstep4 : 1 + 2 * (1 + Real.log (Submission.LargeValues.M N + 2))
        = 3 + 2 * Real.log (Submission.LargeValues.M N + 2) := by ring
    have hnum : 3 + 2 * Real.log (Submission.LargeValues.M N + 2)
        ≤ ((18 + 24 * 3 ^ (ε/2) / ε) / 6) * (N:ℝ)^ε := by
      have h' : 3 + 2 * Real.log ((N:ℝ)^(6/5:ℝ) + 2)
          ≤ ((18 + 24 * 3 ^ (ε/2) / ε) / 6) * (N:ℝ)^ε := by
        have h := log_bound_interval ε hε N hN
        rw [show ((18 + 24 * 3 ^ (ε/2) / ε) / 6) * (N:ℝ)^ε
              = (18 + 24 * 3 ^ (ε/2) / ε) * (N:ℝ)^ε / 6 by ring]
        linarith
      exact h'
    calc ∫ v in (1/C)..C, ‖Submission.GM.Rfun W v‖ ^ 2
        ≤ (2 * (C + 1/C)) * (∑ t ∈ W, ∑ t' ∈ W, 1 / (1 + |t - t'|)) := hstep1
      _ ≤ (2 * (C + 1/C)) * ((W.card : ℝ) * (1 + 2 * (1 + Real.log (Submission.LargeValues.M N /
            (Submission.LargeValues.M N) ^ ε + 2)) / (Submission.LargeValues.M N) ^ ε)) :=
            mul_le_mul_of_nonneg_left hstep2 hKnonneg
      _ ≤ (2 * (C + 1/C)) * ((W.card : ℝ) *
            (1 + 2 * (1 + Real.log (Submission.LargeValues.M N + 2)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep3 hcard0) hKnonneg
      _ = (2 * (C + 1/C)) * ((W.card : ℝ) *
            (3 + 2 * Real.log (Submission.LargeValues.M N + 2))) := by rw [hstep4]
      _ ≤ (2 * (C + 1/C)) * ((W.card : ℝ) *
            (((18 + 24 * 3 ^ (ε/2) / ε) / 6) * (N:ℝ)^ε)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnum hcard0) hKnonneg
      _ = (2 * (C + 1/C) * ((18 + 24 * 3 ^ (ε/2) / ε) / 6)) * (N:ℝ)^ε * (W.card : ℝ) := by ring

end Work.GM.S3
