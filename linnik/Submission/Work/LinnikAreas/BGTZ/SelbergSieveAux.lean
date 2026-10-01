/-
# Auxiliary lemmas for `Work.LinnikAreas.BGTZ.SelbergSieveMain2` (BGTZ Lemma 4.2)

The proof of BGTZ Lemma 4.2 (= the file `SelbergSieveMain2`) runs as follows.

* **Monotonicity.**  Since `a(n) ≥ 0` and `1 - β₁ > 0`,
  `Σ_{n ≤ R} a(n)/n ≥ R^{β₁-1} Σ_{n ≤ R} a(n) n^{-β₁} ≥ R^{β₁-1} Σ_{n ≤ R} a(n)n^{-β₁}(1 - n/R)`.

* **The contour shift on the critical line** (`SsmC_sub_res_eq_critIntegral`).  Combining the
  truncated Perron formula for the triangle kernel (`Work.Sieve.triPerron_formula`, which writes
  `Σ_{n ≤ x}λ(n)n^{-β}(1-n/x)` as the vertical integral of `triFun` over `Re s = 1` plus a small
  Perron error) with the rectangle Cauchy identity `Work.Sieve.triPerron_shift_half` (which shifts
  that integral to the line `Re s = 1/2 - β`, picking up the residue `triPerronRes` at
  `s = 1 - β` and leaving the horizontal segments), and letting the truncation height `T → ∞`,
  the Perron error and the horizontal segments disappear and one obtains the identity
  `SsmC ψ β x - triPerronRes ψ β x = (1/2π) ∫_ℝ triFun ψ β x (1/2 - β + iy) dy`.

* **The two estimates of the critical-line integral.**  With the convexity strip bound for
  imprimitive characters (`critLine_integral_convex`) the integral is `≪ q^{1/3} log(2q+2)
  x^{1/2-β}`, and with Hypothesis A (`critLine_integral_hypA`) it is
  `≪ A q^θ exp((log q)^{3/4}) x^{1/2-β}`.  The first gives the Hecke-type lower bound
  `‖L(1,χ)‖ ≫ 1-β` for the (possibly imprimitive) exceptional character `χ`; the second gives the
  lower bound for `Σ_{n ≤ x} a(n)/n` that the Sieve consumes.
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

namespace Work.LinnikAreas.BGTZ

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

/-- **Assembly of BGTZ Lemma 4.2 from its two analytic inputs.**

`hratio` is the Hecke-type lower bound for the real part of `L(1,χ)` at an exceptional zero
(proved from the same critical-line shift plus the *convexity* bound for the critical-line
integral), and `hJ` is the bound for the critical-line integral coming from Hypothesis A.
`hperr`/`hH` are the two vanishing statements used in the contour shift.
-/
theorem selbergSieveMain2_of_bounds
    (c : ℝ) (hc : 0 < c)
    (hratio : ∀ (q : ℕ) [NeZero q], 400000 < q → ∀ (χ : DirichletCharacter ℂ q),
      χ ^ 2 = 1 → χ ≠ 1 → ∀ {β : ℝ}, β < 1 → Work.LinnikContract.zeroMult χ (β : ℂ) ≠ 0 →
      1 - 1 / (10 * Real.log q) < β →
        c * (1 - β) ≤ (DirichletCharacter.LFunction χ (1 : ℂ)).re)
    (CJ : ℝ) (hCJ : 0 < CJ)
    (hJ : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → 3 ≤ q →
      ∀ {A θ β x : ℝ}, HypA A θ → 3 / 4 ≤ β → β < 1 → 1 ≤ x →
      MeasureTheory.Integrable
          (fun y : ℝ => triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)) ∧
      ‖(1 / (2 * Real.pi)) *
          (∫ y : ℝ, triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))‖
        ≤ CJ * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * x ^ (1 / 2 - β))
    (hperr : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 →
      ∀ {β x : ℝ}, 0 < β → 0 < x → (∀ n : ℕ, (n : ℝ) ≠ x) →
      Filter.Tendsto (fun T : ℝ => perrErr χ β x T) Filter.atTop (nhds 0))
    (hH : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {β x : ℝ}, 1 / 2 < β → β < 1 → 0 < x →
      Filter.Tendsto (fun T : ℝ => (1 / (2 * Real.pi * Complex.I)) *
        ((∫ u in ((1 / 2 - β : ℝ))..1, triFun χ β x ((u : ℂ) + T * Complex.I))
         - (∫ u in ((1 / 2 - β : ℝ))..1, triFun χ β x ((u : ℂ) - T * Complex.I))))
        Filter.atTop (nhds 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 400000 < q → ∀ (χ₁ : DirichletCharacter ℂ q),
      χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ∀ {β₁ : ℝ}, β₁ < 1 → Work.LinnikContract.zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
      1 - 1 / (10 * Real.log q) < β₁ → ∀ {A θ : ℝ}, HypA A θ →
      ∀ {R : ℝ}, 200 ≤ R →
      ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖ / ((1 - β₁) * (2 - β₁))
        * (1 - C * A * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
            * (q : ℝ) ^ θ / R ^ (1 / 2 : ℝ))
        ≤ ∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aCoeff χ₁ n / (n : ℝ) := by
  refine ⟨max 1 (3 * CJ / c + 1), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro q _inst hq χ₁ hχ2 hχne β₁ hβ1 hzm hβ' A θ hA R hR
  have hApos : 0 < A := hA.1
  have hθpos : 0 < θ := hA.2.1
  have hq3 : 3 ≤ q := by omega
  have hCpos : (0 : ℝ) < max 1 (3 * CJ / c + 1) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hClo : 3 * CJ / c + 1 ≤ max 1 (3 * CJ / c + 1) := le_max_right _ _
  -- `1 ≤ log q`
  have hlogq1 : (1 : ℝ) ≤ Real.log (q : ℝ) := by
    have h4 : (400000 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have h3 : Real.exp 1 < 400000 := by
      have h := Real.exp_one_lt_d9
      linarith
    exact (Real.le_log_iff_exp_le (by positivity)).mpr (by linarith)
  have hlogqpos : 0 < Real.log (q : ℝ) := by linarith
  -- consequences of the Siegel-range hypothesis
  have h1mβ : 1 - β₁ < 1 / (10 * Real.log q) := by linarith
  have hβ10 : (1 - β₁) * Real.log q < 1 / 10 := by
    have h := mul_lt_mul_of_pos_right h1mβ hlogqpos
    have h2 : (1 / (10 * Real.log q)) * Real.log q = 1 / 10 := by
      field_simp
    linarith [h, h2]
  have hβpos : 0 < β₁ := by
    have h2 : 1 / (10 * Real.log q) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    linarith
  have hβ34 : (3 : ℝ) / 4 ≤ β₁ := by
    have h2 : 1 / (10 * Real.log q) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hβhalf : 1 / 2 < β₁ := by linarith
  -- the sum is nonnegative
  have hSumNonneg : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aCoeff χ₁ n / (n : ℝ) := by
    apply Finset.sum_nonneg
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have h1 : 0 ≤ aCoeff χ₁ n := by
      rw [aCoeff_eq_lamR]; exact (lamRealNonneg χ₁ hχ2).2.1 n
    have h2 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    positivity
  set δ : ℝ := max 1 (3 * CJ / c + 1) * A * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
      * (q : ℝ) ^ θ / R ^ (1 / 2 : ℝ) with hδdef
  by_cases hcase : (1 : ℝ) ≤ δ
  · have hfac : 1 - δ ≤ 0 := by linarith
    have hX : 0 ≤ ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖ / ((1 - β₁) * (2 - β₁)) := by
      apply div_nonneg (norm_nonneg _)
      nlinarith
    exact le_trans (mul_nonpos_of_nonneg_of_nonpos hX hfac) hSumNonneg
  · push_neg at hcase
    -- the point `x = ⌊R⌋ + 1/2`
    set x : ℝ := (⌊R⌋₊ : ℝ) + 1 / 2 with hxdef
    have hfloor200 : (200 : ℝ) ≤ (⌊R⌋₊ : ℝ) :=
      by exact_mod_cast (Nat.le_floor (by exact_mod_cast hR) : 200 ≤ ⌊R⌋₊)
    have hx200 : (200 : ℝ) ≤ x := by rw [hxdef]; push_cast; linarith
    have hx1 : 1 < x := by linarith
    have hx0 : 0 < x := by linarith
    have hxnn : ∀ n : ℕ, (n : ℝ) ≠ x := by
      intro n hn
      have h2 : (2 : ℝ) * (n : ℝ) = 2 * (⌊R⌋₊ : ℝ) + 1 := by
        rw [hn, hxdef]; ring
      have h3 : ((2 * n : ℕ) : ℝ) = ((2 * ⌊R⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      have h4 : 2 * n = 2 * ⌊R⌋₊ + 1 := by exact_mod_cast h3
      omega
    have hxfloor : ⌊x⌋₊ = ⌊R⌋₊ := by
      rw [hxdef]
      apply le_antisymm
      · have h : ((⌊R⌋₊ : ℝ) + 1 / 2) < ((⌊R⌋₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
        have h2 : ⌊(⌊R⌋₊ : ℝ) + 1 / 2⌋₊ < ⌊R⌋₊ + 1 :=
          (Nat.floor_lt (a := (⌊R⌋₊ : ℝ) + 1 / 2) (by positivity)).mpr h
        omega
      · exact Nat.le_floor (by push_cast; linarith)
    -- the critical-line integral bound at `x`
    have hJb := hJ q χ₁ hχne hq3 hA hβ34 hβ1 (le_of_lt hx1)
    have hL0 : DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 :=
      LFunction_eq_zero_of_zeroMult χ₁ hχne hβpos hβ1 hzm
    have hlow := Ssm_ge_res_sub_J χ₁ hχne hχ2 hβhalf hβ1 hx1 hxnn hL0 hJb.1
      (hperr q χ₁ hχ2 hβpos hx0 hxnn) (hH q χ₁ hχne hβhalf hβ1 hx0) hJb.2
    have hmono := Ssm_rpow_le_sum χ₁ hχ2 (le_of_lt hβ1) (le_of_lt hx1) hxfloor
    -- multiply by `x^{β₁-1} ≥ 0` and identify the two powers
    have hxpow : (0 : ℝ) ≤ x ^ (β₁ - 1) := Real.rpow_nonneg (le_of_lt hx0) _
    have hstep1 : x ^ (β₁ - 1) * ((DirichletCharacter.LFunction χ₁ (1 : ℂ)).re *
        (x ^ (1 - β₁) / ((1 - β₁) * (2 - β₁)))
        - CJ * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * x ^ (1 / 2 - β₁))
        ≤ ∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aCoeff χ₁ n / (n : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_left hlow hxpow) hmono
    have hxprod : x ^ (β₁ - 1) * x ^ (1 - β₁) = 1 := by
      rw [← Real.rpow_add hx0, show β₁ - 1 + (1 - β₁) = 0 by ring, Real.rpow_zero]
    have hxhalf : x ^ (β₁ - 1) * x ^ (1 / 2 - β₁) = x ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hx0, show β₁ - 1 + (1 / 2 - β₁) = -(1 / 2) by ring]
    have hsimp : x ^ (β₁ - 1) * ((DirichletCharacter.LFunction χ₁ (1 : ℂ)).re *
        (x ^ (1 - β₁) / ((1 - β₁) * (2 - β₁)))
        - CJ * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * x ^ (1 / 2 - β₁))
        = (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re / ((1 - β₁) * (2 - β₁))
          - CJ * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * x ^ (-(1 / 2 : ℝ)) := by
      rw [mul_sub]
      congr 1
      · calc x ^ (β₁ - 1) * ((DirichletCharacter.LFunction χ₁ (1 : ℂ)).re *
            (x ^ (1 - β₁) / ((1 - β₁) * (2 - β₁))))
            = (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re *
                (x ^ (β₁ - 1) * (x ^ (1 - β₁) / ((1 - β₁) * (2 - β₁)))) := by ring
          _ = (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re *
                ((x ^ (β₁ - 1) * x ^ (1 - β₁)) / ((1 - β₁) * (2 - β₁))) := by
                rw [mul_div_assoc']
          _ = (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re * (1 / ((1 - β₁) * (2 - β₁))) := by
                rw [hxprod]
          _ = (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re / ((1 - β₁) * (2 - β₁)) := by ring
      · calc x ^ (β₁ - 1) * (CJ * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
              * x ^ (1 / 2 - β₁))
            = CJ * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
                * (x ^ (β₁ - 1) * x ^ (1 / 2 - β₁)) := by ring
          _ = CJ * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
                * x ^ (-(1 / 2 : ℝ)) := by rw [hxhalf]
    have hstep2 : (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re / ((1 - β₁) * (2 - β₁))
        - CJ * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * x ^ (-(1 / 2 : ℝ))
        ≤ ∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aCoeff χ₁ n / (n : ℝ) := by
      rw [← hsimp]; exact hstep1
    -- replace `x^{-1/2}` by `√2 R^{-1/2}`
    have hRpos : 0 < R := by linarith
    have hRx2 : R ≤ 2 * x := by
      have hlt : R < (⌊R⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one R
      rw [hxdef]; linarith
    have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by
      rw [show (3 / 2 : ℝ) = Real.sqrt ((3 / 2) ^ 2) by
        rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hxinv : x ^ (-(1 / 2 : ℝ)) ≤ Real.sqrt 2 * R ^ (-(1 / 2 : ℝ)) := by
      have h5 : x ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt x := by
        rw [Real.rpow_neg (le_of_lt hx0), Real.sqrt_eq_rpow, inv_eq_one_div]
      have h6 : R ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt R := by
        rw [Real.rpow_neg (le_of_lt hRpos), Real.sqrt_eq_rpow, inv_eq_one_div]
      rw [h5, h6, show Real.sqrt 2 * (1 / Real.sqrt R) = Real.sqrt 2 / Real.sqrt R by ring,
        div_le_div_iff₀ (Real.sqrt_pos.mpr hx0) (Real.sqrt_pos.mpr hRpos)]
      rw [one_mul]
      calc Real.sqrt R ≤ Real.sqrt (2 * x) := Real.sqrt_le_sqrt hRx2
        _ = Real.sqrt 2 * Real.sqrt x := Real.sqrt_mul (by norm_num) x
    have hstep3 : (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re / ((1 - β₁) * (2 - β₁))
        - Real.sqrt 2 * CJ * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
            * R ^ (-(1 / 2 : ℝ))
        ≤ ∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aCoeff χ₁ n / (n : ℝ) := by
      refine le_trans ?_ hstep2
      have hnn : (0 : ℝ) ≤ CJ * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) := by
        have h1 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
        positivity
      have h2 := mul_le_mul_of_nonneg_left hxinv hnn
      have h3 : (CJ * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))) *
          (Real.sqrt 2 * R ^ (-(1 / 2 : ℝ)))
          = Real.sqrt 2 * CJ * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
              * R ^ (-(1 / 2 : ℝ)) := by ring
      have h4 : CJ * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
          * x ^ (-(1 / 2 : ℝ))
          ≤ Real.sqrt 2 * CJ * A * (q : ℝ) ^ θ
              * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * R ^ (-(1 / 2 : ℝ)) := by
        rw [← h3]; exact h2
      linarith [h4]
    -- the Hecke-type lower bound for `Re L(1,χ₁)`
    have hratio' := hratio q hq χ₁ hχ2 hχne hβ1 hzm hβ'
    have h1mβpos : 0 < 1 - β₁ := by linarith
    have hLpos : 0 < (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re :=
      lt_of_lt_of_le (mul_pos hc h1mβpos) hratio'
    have hM : c / 2 ≤ (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re / ((1 - β₁) * (2 - β₁)) := by
      have hden : 0 < (1 - β₁) * (2 - β₁) := by nlinarith
      rw [le_div_iff₀ hden]
      have h1 : c / 2 * ((1 - β₁) * (2 - β₁)) ≤ c * (1 - β₁) := by
        have h3 : (0 : ℝ) ≤ 1 - β₁ := by linarith
        have h5 : (1 - β₁) * (2 - β₁) ≤ (1 - β₁) * 2 :=
          mul_le_mul_of_nonneg_left (by linarith) h3
        have h6 : c / 2 * ((1 - β₁) * (2 - β₁)) ≤ c / 2 * ((1 - β₁) * 2) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
        have h7 : c / 2 * ((1 - β₁) * 2) = c * (1 - β₁) := by ring
        linarith [h6, h7]
      exact le_trans h1 hratio'
    have him := im_LFunction_one_eq_zero χ₁ hχne hχ2
    have hnorm : ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖
        = (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re := by
      have hz : DirichletCharacter.LFunction χ₁ (1 : ℂ)
          = (((DirichletCharacter.LFunction χ₁ (1 : ℂ)).re : ℝ) : ℂ) := by
        apply Complex.ext
        · rw [Complex.ofReal_re]
        · rw [Complex.ofReal_im, him]
      rw [hz, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hLpos.le,
        Complex.ofReal_re]
    -- the error term is dominated by `M · δ`
    have hMC : Real.sqrt 2 * CJ
        ≤ (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re / ((1 - β₁) * (2 - β₁))
            * max 1 (3 * CJ / c + 1) := by
      have hCge : 3 * CJ / c ≤ max 1 (3 * CJ / c + 1) := by
        have := le_max_right (1 : ℝ) (3 * CJ / c + 1); linarith
      have hM0 : 0 ≤ (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re / ((1 - β₁) * (2 - β₁)) :=
        le_of_lt (lt_of_lt_of_le (by positivity : (0 : ℝ) < c / 2) hM)
      have h1 : (c / 2) * (3 * CJ / c) = 3 * CJ / 2 := by field_simp
      have h2 : 3 * CJ / 2 ≤ (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re
            / ((1 - β₁) * (2 - β₁)) * max 1 (3 * CJ / c + 1) := by
        calc 3 * CJ / 2 = (c / 2) * (3 * CJ / c) := h1.symm
          _ ≤ (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re / ((1 - β₁) * (2 - β₁))
                * (3 * CJ / c) := mul_le_mul_of_nonneg_right hM (by positivity)
          _ ≤ (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re / ((1 - β₁) * (2 - β₁))
                * max 1 (3 * CJ / c + 1) := mul_le_mul_of_nonneg_left hCge hM0
      have h3 : Real.sqrt 2 * CJ ≤ 3 * CJ / 2 := by nlinarith [hsqrt2, hCJ]
      exact le_trans h3 h2
    have herr : Real.sqrt 2 * CJ * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
        * R ^ (-(1 / 2 : ℝ))
        ≤ ((DirichletCharacter.LFunction χ₁ (1 : ℂ)).re / ((1 - β₁) * (2 - β₁))) * δ := by
      rw [hδdef]
      have hkey : (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re / ((1 - β₁) * (2 - β₁))
            * (max 1 (3 * CJ / c + 1) * A * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
              * (q : ℝ) ^ θ / R ^ (1 / 2 : ℝ))
          = ((DirichletCharacter.LFunction χ₁ (1 : ℂ)).re / ((1 - β₁) * (2 - β₁))
              * max 1 (3 * CJ / c + 1)) * (A * (q : ℝ) ^ θ
              * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * (R ^ (1 / 2 : ℝ))⁻¹) := by
        rw [div_eq_mul_inv]; ring
      rw [hkey, Real.rpow_neg (le_of_lt hRpos)]
      have hfac : (0 : ℝ) ≤ A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
          * (R ^ (1 / 2 : ℝ))⁻¹ := by
        have h1 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
        positivity
      have hres := mul_le_mul_of_nonneg_right hMC hfac
      calc Real.sqrt 2 * CJ * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
              * (R ^ (1 / 2 : ℝ))⁻¹
          = Real.sqrt 2 * CJ * (A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
              * (R ^ (1 / 2 : ℝ))⁻¹) := by ring
        _ ≤ ((DirichletCharacter.LFunction χ₁ (1 : ℂ)).re / ((1 - β₁) * (2 - β₁))
              * max 1 (3 * CJ / c + 1)) * (A * (q : ℝ) ^ θ
              * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * (R ^ (1 / 2 : ℝ))⁻¹) := hres
    -- conclude
    rw [hnorm]
    have hfinal : (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re / ((1 - β₁) * (2 - β₁))
        * (1 - δ)
        ≤ (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re / ((1 - β₁) * (2 - β₁))
          - Real.sqrt 2 * CJ * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
              * R ^ (-(1 / 2 : ℝ)) := by
      nlinarith [herr]
    exact le_trans hfinal hstep3

end Work.LinnikAreas.BGTZ
