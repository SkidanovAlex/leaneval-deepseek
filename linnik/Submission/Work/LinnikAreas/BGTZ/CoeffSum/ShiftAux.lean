/-
# The critical-line contour-shift lemmas used by `CoeffSumLower`

Self-contained copies (from the shared file `Work/LinnikAreas/BGTZ/SelbergSieveAux.lean`) of the
elementary facts about the smoothed sum `Ssm`, the critical-line shift identity
`SsmC_sub_res_eq_critIntegral`, the monotonicity step `Ssm_rpow_le_sum` and the lower bound
`Ssm_ge_res_sub_J`.  They live in their own namespace
`Work.LinnikAreas.BGTZ.CoeffSum` so that they never clash with the originals.
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_conj
import Submission.Work.LinnikAreas.LFunction_eq_zero_of_zeroMult
import Submission.Work.Sieve.triPerron_shift_half
import Submission.Work.Sieve.triPerron_formula

open DirichletCharacter Complex
open scoped Classical BigOperators

set_option maxHeartbeats 4000000

noncomputable section

namespace Work.LinnikAreas.BGTZ.CoeffSum

open Work.LinnikAreas


/-- For a Dirichlet character with `χ ^ 2 = 1` the value `L(1,χ)` is real. -/
lemma im_LFunction_one_eq_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχ2 : χ ^ 2 = 1) : (DirichletCharacter.LFunction χ (1 : ℂ)).im = 0 := by
  have hinv : χ⁻¹ = χ := by
    have h2 : χ * χ = 1 := by simpa [pow_two] using hχ2
    have h3 : χ⁻¹ * (χ * χ) = χ⁻¹ * 1 := by rw [h2]
    rw [← mul_assoc, inv_mul_cancel, one_mul, mul_one] at h3
    exact h3.symm
  have hconj := Commons.NumberTheory.DirichletCharacter.LFunction_conj χ hχ (1 : ℂ)
  rw [hinv] at hconj
  have hfix : DirichletCharacter.LFunction χ (1 : ℂ)
      = (starRingEnd ℂ) (DirichletCharacter.LFunction χ (1 : ℂ)) := by
    rw [hconj]
    simp
  have h := congrArg Complex.im hfix
  simp only [Complex.conj_im] at h
  linarith

/-! ## Elementary facts about the smoothed sum `Ssm`

These are copies of `SsmC_re`, `Ssm_eq_re_SsmC` and `Ssm_ge_one` from
`Submission/Work/LinnikAreas/L_one_lower_relation.lean`, reproduced here because that module is
not part of the import closure of the present file. -/

/-- Real form of `SsmC`. -/
lemma SsmC_re' {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (β x : ℝ) :
    (Work.LinnikAreas.SsmC ψ β x).re
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, lamR ψ n * (n : ℝ) ^ (-β) * (1 - (n : ℝ) / x) := by
  rw [Work.LinnikAreas.SsmC, Complex.re_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [lamR_apply]
  have h1 : (n : ℂ) ^ (-(β : ℂ)) = (((n : ℝ) ^ (-β) : ℝ) : ℂ) := by
    have hb : (-(β : ℂ)) = ((-β : ℝ) : ℂ) := by simp
    rw [hb, ← Complex.ofReal_natCast n, ← Complex.ofReal_cpow (Nat.cast_nonneg n) (-β)]
  have h2 : (1 - (n : ℂ) / (x : ℂ)) = (((1 - (n : ℝ) / x) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_div, ← Complex.ofReal_one,
      ← Complex.ofReal_sub]
  rw [h1, h2, mul_assoc, ← Complex.ofReal_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- `Ssm` is the real part of `SsmC`. -/
lemma Ssm_eq_re_SsmC' {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (β x : ℝ) :
    Work.LinnikAreas.Ssm ψ β x = (Work.LinnikAreas.SsmC ψ β x).re := by
  rw [Work.LinnikAreas.Ssm_apply, SsmC_re']

/-- `Ssm ψ β x ≥ 1 - 1/x` for a real character `ψ`. -/
lemma Ssm_ge_one' {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ^ 2 = 1) (β : ℝ)
    {x : ℝ} (hx : 1 ≤ x) : 1 - 1 / x ≤ Work.LinnikAreas.Ssm ψ β x := by
  have hpos := (lamRealNonneg ψ hψ).2.1
  have hfloor : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hmem : 1 ∈ Finset.Icc 1 ⌊x⌋₊ := Finset.mem_Icc.mpr ⟨le_rfl, hfloor⟩
  have hnonneg : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊,
      0 ≤ lamR ψ n * (n : ℝ) ^ (-β) * (1 - (n : ℝ) / x) := by
    intro n hn
    have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
      (Nat.floor_le (by linarith))
    have h1 : 0 ≤ (n : ℝ) ^ (-β) := Real.rpow_nonneg (by positivity) _
    have h2 : 0 ≤ 1 - (n : ℝ) / x := by
      rw [sub_nonneg, div_le_one (by linarith)]
      exact hnx
    have h3 : 0 ≤ lamR ψ n := by rw [lamR_apply]; exact hpos n
    positivity
  have hsingle := Finset.single_le_sum hnonneg hmem
  have hone : lamR ψ 1 * (((1 : ℕ) : ℝ)) ^ (-β) * (1 - (((1 : ℕ) : ℝ)) / x) = 1 - 1 / x := by
    rw [lamR_apply, lam_one_eq_one]
    norm_num
  rw [← hone, Ssm_eq_re_SsmC', SsmC_re']
  exact hsingle

/-- The real part of the residue term `triPerronRes` of the critical-line shift. -/
lemma triPerronRes_re {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) {β x : ℝ} (hx : 0 ≤ x) :
    (Work.LinnikAreas.triPerronRes ψ β x).re
      = (DirichletCharacter.LFunction ψ 1).re * (x ^ (1 - β) / ((1 - β) * (2 - β))) := by
  have hpow : (((x : ℂ)) ^ (((1 - β : ℝ)) : ℂ))
      = ((x ^ (1 - β) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cpow hx (1 - β)]
  have hmain : Work.LinnikAreas.triPerronRes ψ β x
      = DirichletCharacter.LFunction ψ 1 * (((x ^ (1 - β) / ((1 - β) * (2 - β)) : ℝ)) : ℂ) := by
    rw [Work.LinnikAreas.triPerronRes,
      show ((((2 - β : ℝ)) : ℂ)) = ((2 - β : ℝ) : ℂ) from rfl, hpow]
    push_cast
    ring
  rw [hmain, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- **The critical-line shift identity for the triangle-kernel Perron integral.**

With the Perron error tending to `0` (`hperr`) and the two horizontal segments of the rectangle
`[1/2-β, 1] × [-T,T]` tending to `0` (`hH`) as `T → ∞`, the difference between the smoothed sum
`SsmC ψ β x` and the residue `triPerronRes ψ β x` is exactly the integral of `triFun` along the
critical line `Re s = 1/2 - β`. -/
theorem SsmC_sub_res_eq_critIntegral {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1)
    (hψ2 : ψ ^ 2 = 1) {β x : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1) (hx : 1 < x)
    (hxnn : ∀ n : ℕ, (n : ℝ) ≠ x) (hL0 : DirichletCharacter.LFunction ψ (β : ℂ) = 0)
    (hint : MeasureTheory.Integrable
      (fun y : ℝ => Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)))
    (hperr : Filter.Tendsto (fun T : ℝ => Work.LinnikAreas.perrErr ψ β x T) Filter.atTop (nhds 0))
    (hH : Filter.Tendsto (fun T : ℝ => (1 / (2 * Real.pi * Complex.I)) *
        ((∫ u in ((1 / 2 - β : ℝ))..1, Work.LinnikAreas.triFun ψ β x ((u : ℂ) + T * Complex.I))
         - (∫ u in ((1 / 2 - β : ℝ))..1, Work.LinnikAreas.triFun ψ β x ((u : ℂ) - T * Complex.I))))
        Filter.atTop (nhds 0)) :
    Work.LinnikAreas.SsmC ψ β x - Work.LinnikAreas.triPerronRes ψ β x
      = (1 / (2 * Real.pi)) *
        (∫ y : ℝ, Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)) := by
  obtain ⟨K, hKpos, hK⟩ := Work.Sieve.triPerron_formula
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  -- the Perron error for each truncation height
  have hper_all : ∀ T : ℝ, 0 < T → ∃ e : ℂ, ‖e‖ ≤ K * (x * Work.LinnikAreas.perrErr ψ β x T) ∧
      (1 / (2 * Real.pi)) *
          (∫ y in (-T)..T, Work.LinnikAreas.triFun ψ β x (1 + (y : ℂ) * Complex.I))
        = Work.LinnikAreas.SsmC ψ β x + e := fun T hT => hK ψ hψ hψ2 hβ hβ1 hx hT hxnn
  -- the Perron error, as a function of the truncation height
  set e : ℝ → ℂ := fun T =>
    if hT : 0 < T then Classical.choose (hper_all T hT) else 0 with hedef
  have he : ∀ T (hT : 0 < T),
      ‖e T‖ ≤ K * (x * Work.LinnikAreas.perrErr ψ β x T) := by
    intro T hT
    have h := (Classical.choose_spec (hper_all T hT)).1
    simpa only [hedef, dif_pos hT] using h
  have heq : ∀ T (hT : 0 < T),
      (1 / (2 * Real.pi)) *
          (∫ y in (-T)..T, Work.LinnikAreas.triFun ψ β x (1 + (y : ℂ) * Complex.I))
        = Work.LinnikAreas.SsmC ψ β x + e T := by
    intro T hT
    have h := (Classical.choose_spec (hper_all T hT)).2
    simpa only [hedef, dif_pos hT] using h
  -- the Perron error tends to zero
  have hbfun : Filter.Tendsto (fun T : ℝ => K * (x * Work.LinnikAreas.perrErr ψ β x T))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun T : ℝ => (K * x) * Work.LinnikAreas.perrErr ψ β x T)
        Filter.atTop (nhds ((K * x) * 0)) := Filter.Tendsto.const_mul (K * x) hperr
    simpa [mul_assoc] using h1
  have he0 : Filter.Tendsto e Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [(Metric.tendsto_nhds.mp hbfun) ε hε,
      Filter.eventually_gt_atTop (0 : ℝ)] with T hdist hT
    rw [dist_zero_right] at hdist ⊢
    have h1 : ‖e T‖ ≤ K * (x * Work.LinnikAreas.perrErr ψ β x T) := he T hT
    have h2 : K * (x * Work.LinnikAreas.perrErr ψ β x T)
        ≤ |K * (x * Work.LinnikAreas.perrErr ψ β x T)| := le_abs_self _
    rw [Real.norm_eq_abs] at hdist
    linarith
  -- the shifted-line integral tends to the full critical-line integral
  have hmono : Monotone (fun T : ℝ => Set.Ioc (-T) T) :=
    fun a b hab => Set.Ioc_subset_Ioc (neg_le_neg hab) hab
  have hUnion : (⋃ T : ℝ, Set.Ioc (-T) T) = Set.univ := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_univ, iff_true]
    exact ⟨|y| + 1, by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  have hS : Filter.Tendsto (fun T : ℝ => (1 / (2 * Real.pi)) *
      (∫ y in (-T)..T, Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)))
      Filter.atTop (nhds ((1 / (2 * Real.pi)) *
        (∫ y : ℝ, Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)))) := by
    have hmain := MeasureTheory.tendsto_setIntegral_of_monotone (μ := MeasureTheory.volume)
      (f := fun y : ℝ => Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))
      (s := fun T : ℝ => Set.Ioc (-T) T) (fun T => measurableSet_Ioc) hmono hint.integrableOn
    rw [hUnion, MeasureTheory.setIntegral_univ] at hmain
    have hscale : Filter.Tendsto (fun z : ℂ => (1 / (2 * Real.pi)) * z)
        (nhds (∫ y : ℝ, Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)))
        (nhds ((1 / (2 * Real.pi)) *
          (∫ y : ℝ, Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)))) :=
      (continuous_const.mul continuous_id).tendsto _
    refine Filter.Tendsto.congr' ?_ (hscale.comp hmain)
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
    simp only [Function.comp_apply]
    rw [intervalIntegral.integral_of_le (a := -T) (b := T) (by linarith : -T ≤ T)]
  -- combine
  have hkey : ∀ T : ℝ, 0 < T →
      Work.LinnikAreas.SsmC ψ β x - Work.LinnikAreas.triPerronRes ψ β x
        = (1 / (2 * Real.pi)) *
            (∫ y in (-T)..T, Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))
          + (1 / (2 * Real.pi * Complex.I)) *
              ((∫ u in ((1 / 2 - β : ℝ))..1, Work.LinnikAreas.triFun ψ β x ((u : ℂ) + T * Complex.I))
               - (∫ u in ((1 / 2 - β : ℝ))..1,
                    Work.LinnikAreas.triFun ψ β x ((u : ℂ) - T * Complex.I)))
          - e T := by
    intro T hT
    have hs := Work.Sieve.triPerron_shift_half ψ hψ hβ hβ1 hx0 hT hL0
    have hp := heq T hT
    rw [hp] at hs
    linear_combination hs
  have hlim : Filter.Tendsto (fun T : ℝ =>
      (1 / (2 * Real.pi)) *
          (∫ y in (-T)..T, Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))
      + (1 / (2 * Real.pi * Complex.I)) *
          ((∫ u in ((1 / 2 - β : ℝ))..1, Work.LinnikAreas.triFun ψ β x ((u : ℂ) + T * Complex.I))
           - (∫ u in ((1 / 2 - β : ℝ))..1,
                Work.LinnikAreas.triFun ψ β x ((u : ℂ) - T * Complex.I)))
      - e T)
      Filter.atTop (nhds ((1 / (2 * Real.pi)) *
        (∫ y : ℝ, Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)))) := by
    have := (hS.add hH).sub he0
    simpa using this
  have hEq : (fun T : ℝ =>
      (1 / (2 * Real.pi)) *
          (∫ y in (-T)..T, Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))
      + (1 / (2 * Real.pi * Complex.I)) *
          ((∫ u in ((1 / 2 - β : ℝ))..1, Work.LinnikAreas.triFun ψ β x ((u : ℂ) + T * Complex.I))
           - (∫ u in ((1 / 2 - β : ℝ))..1,
                Work.LinnikAreas.triFun ψ β x ((u : ℂ) - T * Complex.I)))
      - e T)
      =ᶠ[Filter.atTop]
      (fun _ => Work.LinnikAreas.SsmC ψ β x - Work.LinnikAreas.triPerronRes ψ β x) :=
    (Filter.eventually_gt_atTop (0 : ℝ)).mono (fun T hT => (hkey T hT).symm)
  have hlim' : Filter.Tendsto (fun T : ℝ =>
      (1 / (2 * Real.pi)) *
          (∫ y in (-T)..T, Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))
      + (1 / (2 * Real.pi * Complex.I)) *
          ((∫ u in ((1 / 2 - β : ℝ))..1, Work.LinnikAreas.triFun ψ β x ((u : ℂ) + T * Complex.I))
           - (∫ u in ((1 / 2 - β : ℝ))..1,
                Work.LinnikAreas.triFun ψ β x ((u : ℂ) - T * Complex.I)))
      - e T)
      Filter.atTop (nhds (Work.LinnikAreas.SsmC ψ β x - Work.LinnikAreas.triPerronRes ψ β x)) :=
    Filter.Tendsto.congr' hEq.symm tendsto_const_nhds
  exact tendsto_nhds_unique hlim' hlim

/-- `aCoeff` is the real form of the coefficients `λ(n) = Σ_{d | n} χ(d)`. -/
lemma aCoeff_eq_lamR {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (n : ℕ) :
    aCoeff ψ n = lamR ψ n := by
  rw [aCoeff, lamR_apply, lam, Complex.re_sum]

/-- **The monotonicity step of BGTZ Lemma 4.2.**  For a real character `ψ`, `β ≤ 1` and `x ≥ 1`
with `⌊x⌋₊ = R`,

`x^{β-1} · Σ_{n ≤ x} a(n) n^{-β}(1 - n/x) ≤ Σ_{n ≤ R} a(n)/n`.

Indeed each summand of the left side is at most `a(n)/n`, because `a(n) ≥ 0`, `1 - n/x ≤ 1` and
`x^{β-1} n^{-β} ≤ n^{-1}` (the latter is `x^{β-1} ≤ n^{β-1}`, which follows from `n ≤ x` and
`β - 1 ≤ 0`). -/
lemma Ssm_rpow_le_sum {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ2 : ψ ^ 2 = 1)
    {β x : ℝ} (hβ : β ≤ 1) (hx : 1 ≤ x) {R : ℕ} (hxR : ⌊x⌋₊ = R) :
    x ^ (β - 1) * Work.LinnikAreas.Ssm ψ β x
      ≤ ∑ n ∈ Finset.Icc 1 R, aCoeff ψ n / (n : ℝ) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hpos := (lamRealNonneg ψ hψ2).2.1
  have hfloor : ⌊x⌋₊ = R := hxR
  rw [Ssm_eq_re_SsmC', SsmC_re', Finset.mul_sum, hfloor]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnR : n ≤ ⌊x⌋₊ := by rw [hfloor]; exact (Finset.mem_Icc.mp hn).2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hnR) (Nat.floor_le (le_of_lt hx0))
  have h1 : 0 ≤ lamR ψ n := hpos n
  have h3 : 0 ≤ 1 - (n : ℝ) / x := by
    rw [sub_nonneg, div_le_one hx0]; exact hnx
  rw [aCoeff_eq_lamR]
  have hkey : x ^ (β - 1) * (n : ℝ) ^ (-β) * (1 - (n : ℝ) / x) ≤ (n : ℝ)⁻¹ := by
    have hstep1 : x ^ (β - 1) * (n : ℝ) ^ (-β) ≤ (n : ℝ)⁻¹ := by
      have hexp : 0 ≤ 1 - β := by linarith
      have hnlx : (n : ℝ) ^ (1 - β) ≤ x ^ (1 - β) :=
        Real.rpow_le_rpow (le_of_lt hn0) hnx hexp
      have hxn : x ^ (β - 1) ≤ (n : ℝ) ^ (β - 1) := by
        have h1 : x ^ (β - 1) = (x ^ (1 - β))⁻¹ := by
          rw [show β - 1 = -(1 - β) by ring, Real.rpow_neg (le_of_lt hx0)]
        have h2 : (n : ℝ) ^ (β - 1) = ((n : ℝ) ^ (1 - β))⁻¹ := by
          rw [show β - 1 = -(1 - β) by ring, Real.rpow_neg (le_of_lt hn0)]
        rw [h1, h2]
        simpa [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hn0 (1 - β)) hnlx
      calc x ^ (β - 1) * (n : ℝ) ^ (-β) ≤ (n : ℝ) ^ (β - 1) * (n : ℝ) ^ (-β) :=
            mul_le_mul_of_nonneg_right hxn (Real.rpow_nonneg (le_of_lt hn0) _)
        _ = (n : ℝ)⁻¹ := by
            rw [← Real.rpow_add hn0 (β - 1) (-β),
              show β - 1 + -β = -1 by ring, Real.rpow_neg_one]
    calc x ^ (β - 1) * (n : ℝ) ^ (-β) * (1 - (n : ℝ) / x)
        ≤ x ^ (β - 1) * (n : ℝ) ^ (-β) * 1 :=
          mul_le_mul_of_nonneg_left (by
            have := div_nonneg (Nat.cast_nonneg n) (le_of_lt hx0); linarith) (by positivity)
      _ = x ^ (β - 1) * (n : ℝ) ^ (-β) := by ring
      _ ≤ (n : ℝ)⁻¹ := hstep1
  have hgoal : x ^ (β - 1) * (lamR ψ n * (n : ℝ) ^ (-β) * (1 - (n : ℝ) / x))
      ≤ lamR ψ n * (n : ℝ)⁻¹ := by
    rw [show x ^ (β - 1) * (lamR ψ n * (n : ℝ) ^ (-β) * (1 - (n : ℝ) / x))
        = lamR ψ n * (x ^ (β - 1) * (n : ℝ) ^ (-β) * (1 - (n : ℝ) / x)) by ring]
    exact mul_le_mul_of_nonneg_left hkey h1
  rwa [div_eq_mul_inv]

/-- **The lower bound for `Ssm` from the critical-line shift.**  If the critical-line integral
is bounded by `K`, then the smoothed sum is at least the residue term minus `K`. -/
theorem Ssm_ge_res_sub_J {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1)
    (hψ2 : ψ ^ 2 = 1) {β x K : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1) (hx : 1 < x)
    (hxnn : ∀ n : ℕ, (n : ℝ) ≠ x) (hL0 : DirichletCharacter.LFunction ψ (β : ℂ) = 0)
    (hint : MeasureTheory.Integrable
      (fun y : ℝ => Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)))
    (hperr : Filter.Tendsto (fun T : ℝ => Work.LinnikAreas.perrErr ψ β x T) Filter.atTop (nhds 0))
    (hH : Filter.Tendsto (fun T : ℝ => (1 / (2 * Real.pi * Complex.I)) *
        ((∫ u in ((1 / 2 - β : ℝ))..1, Work.LinnikAreas.triFun ψ β x ((u : ℂ) + T * Complex.I))
         - (∫ u in ((1 / 2 - β : ℝ))..1, Work.LinnikAreas.triFun ψ β x ((u : ℂ) - T * Complex.I))))
        Filter.atTop (nhds 0))
    (hJ : ‖(1 / (2 * Real.pi)) *
        (∫ y : ℝ, Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))‖ ≤ K) :
    (DirichletCharacter.LFunction ψ 1).re * (x ^ (1 - β) / ((1 - β) * (2 - β)))
        - K ≤ Work.LinnikAreas.Ssm ψ β x := by
  have hx0 : 0 ≤ x := le_of_lt (lt_trans zero_lt_one hx)
  have hid := SsmC_sub_res_eq_critIntegral ψ hψ hψ2 hβ hβ1 hx hxnn hL0 hint hperr hH
  have hre : (Work.LinnikAreas.SsmC ψ β x).re
      = (Work.LinnikAreas.triPerronRes ψ β x).re
        + ((1 / (2 * Real.pi)) *
            (∫ y : ℝ, Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))).re := by
    have hsplit : Work.LinnikAreas.SsmC ψ β x
        = Work.LinnikAreas.triPerronRes ψ β x
          + (1 / (2 * Real.pi)) *
              (∫ y : ℝ, Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)) := by
      rw [← hid]; ring
    rw [hsplit, Complex.add_re]
  have hneg : -‖(1 / (2 * Real.pi)) *
      (∫ y : ℝ, Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))‖
      ≤ ((1 / (2 * Real.pi)) *
          (∫ y : ℝ, Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))).re := by
    have h := Complex.abs_re_le_norm ((1 / (2 * Real.pi)) *
      (∫ y : ℝ, Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)))
    rw [abs_le] at h
    linarith [h.1]
  rw [Ssm_eq_re_SsmC', hre, triPerronRes_re ψ hx0]
  linarith

end Work.LinnikAreas.BGTZ.CoeffSum
