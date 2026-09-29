import Mathlib
import Submission.Work.TMComp.MAnalytic.amoM_strip
import Submission.Work.TMComp.MAnalytic.section_unique_real

/-!
# The Cayley transform of AJ's `m`-function on a strip

Avila--Jitomirskaya, *The Ten Martini Problem*, Ann. of Math. 170 (2009).

For `Im z ≥ 4` and a strip half-width `σ > 0` satisfying
`2λ sinh (2πσ) ≤ Im z / 2 - 2 / Im z` (a width exists for every `λ > 0`, `Im z ≥ 4`, see
`strip_sigma_exists`), the `m`-function `amoM α lam z ·` has a one-periodic analytic
companion on the strip `{|Im x| < σ}` taking values in the open unit disc: its **Cayley
transform**

`x ↦ (amoM α lam z x - i) / (amoM α lam z x + i)`.

Such a bounded `1`-periodic holomorphic function is what makes it possible to use Fourier
analysis / Nevanlinna-type arguments along vertical strips (the Cayley transform of an
`ℍ`-valued function is `𝔻`-valued, so all the bounds become uniform).

The construction goes through the analytic section `M` of the (complexified) section
equation produced by `amoM_strip`:

* `amoM α lam z x = M x` for real `x` (the `limUnder` in the definition of `amoM` is the
  genuine limit supplied by `amoM_strip`);
* `M` is `1`-periodic **on the strip** (`section_periodic_strip`): the only step is the
  identity theorem, since `M` and `x ↦ M (x+1)` are both analytic on the (convex, hence
  preconnected) strip and agree on the real line, where periodicity follows from
  `backIterC` being `1`-periodic in its argument);
* `Im (M x) > 0` on the strip (`section_im_pos`), so the Cayley transform has modulus `< 1`
  (`norm_cayley_lt_one`);
* to make the Cayley transform `1`-periodic *everywhere* (the statement asks for all
  `x : ℂ`, not only inside the strip) we declare it to be `0` outside the strip: the
  Cayley transform of `M` is only meaningful inside the strip, and the strip is invariant
  under `x ↦ x + 1`.

Todo: the statement `amoM_strip_cayley` below is exactly the lemma requested by the
Ten Martini project.
-/

set_option autoImplicit false

open Filter
open Work.TMContract

namespace Work.TMComp.MAnalytic

noncomputable section

lemma tmC_add_one (lam : ℝ) (E : ℂ) (x : ℝ) : tmC lam E (x + 1) = tmC lam E x := by
  have h : Real.cos (2 * Real.pi * (x + 1)) = Real.cos (2 * Real.pi * x) := by
    rw [show 2 * Real.pi * (x + 1) = 2 * Real.pi * x + 2 * Real.pi by ring, Real.cos_add_two_pi]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tmC, h]

lemma backIterC_add_one (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    backIterC α lam E n (x + 1) = backIterC α lam E n x := by
  induction n with
  | zero => simp [backIterC]
  | succ n ih =>
    rw [backIterC, ih, backIterC]
    rw [show x + 1 - ((n : ℝ) + 1) * α = (x - ((n : ℝ) + 1) * α) + 1 by ring, tmC_add_one]

lemma section_periodic_real {α lam : ℝ} {z : ℂ} {M : ℂ → ℂ}
    (hM : ∀ y : ℝ, Tendsto (fun n : ℕ => mob (backIterC α lam z n y) Complex.I) atTop
      (nhds (M (y : ℂ)))) :
    ∀ y : ℝ, M ((y : ℂ) + 1) = M (y : ℂ) := by
  intro y
  have hseq : (fun n : ℕ => mob (backIterC α lam z n y) Complex.I)
      = (fun n : ℕ => mob (backIterC α lam z n (y + 1)) Complex.I) := by
    funext n
    rw [backIterC_add_one]
  have h1 : Tendsto (fun n : ℕ => mob (backIterC α lam z n y) Complex.I) atTop
      (nhds (M (((y + 1 : ℝ)) : ℂ))) := by
    rw [hseq]
    exact hM (y + 1)
  have h2 := tendsto_nhds_unique h1 (hM y)
  rwa [Complex.ofReal_add, Complex.ofReal_one] at h2

lemma eqOn_of_eqOn_real_of_strip {σ : ℝ} (hσ : 0 < σ) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {x : ℂ | |x.im| < σ})
    (hg : AnalyticOnNhd ℂ g {x : ℂ | |x.im| < σ})
    (h : ∀ t : ℝ, f (t : ℂ) = g (t : ℂ)) :
    ∀ x : ℂ, |x.im| < σ → f x = g x := by
  have hpre : IsPreconnected {x : ℂ | |x.im| < σ} := by
    have hset : {x : ℂ | |x.im| < σ} = {x : ℂ | x.im < σ} ∩ {x : ℂ | -σ < x.im} := by
      ext x
      show |x.im| < σ ↔ x.im < σ ∧ -σ < x.im
      rw [abs_lt]
      tauto
    rw [hset]
    exact ((convex_halfSpace_im_lt σ).inter (convex_halfSpace_im_gt (-σ))).isPreconnected
  have h0 : (0 : ℂ) ∈ {x : ℂ | |x.im| < σ} := by
    show |(0 : ℂ).im| < σ
    simpa using hσ
  have hcl : (0 : ℂ) ∈ closure ({z : ℂ | f z = g z} \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨(((ε / 2 : ℝ)) : ℂ), ⟨h (ε / 2), ?_⟩, ?_⟩
    · intro hz
      have hre := congrArg Complex.re hz
      simp only [Complex.ofReal_re, Complex.zero_re] at hre
      linarith
    · rw [dist_eq_norm, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0:ℝ) < ε / 2)]
      linarith
  exact AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure hf hg hpre h0 hcl

lemma section_periodic_strip {α lam σ : ℝ} (hσ : 0 < σ) {z : ℂ} {M : ℂ → ℂ}
    (hMan : AnalyticOnNhd ℂ M {x : ℂ | |x.im| < σ})
    (hM : ∀ y : ℝ, Tendsto (fun n : ℕ => mob (backIterC α lam z n y) Complex.I) atTop
      (nhds (M (y : ℂ)))) :
    ∀ x : ℂ, |x.im| < σ → M (x + 1) = M x := by
  have han : AnalyticOnNhd ℂ (fun x : ℂ => M (x + 1)) {x : ℂ | |x.im| < σ} := by
    intro x hx
    have hx1 : |(x + 1).im| < σ := by simpa using hx
    have h1 : AnalyticAt ℂ (fun y : ℂ => y + 1) x :=
      (analyticAt_id.add analyticAt_const : AnalyticAt ℂ (fun y : ℂ => y + 1) x)
    have h2 : AnalyticAt ℂ M (x + 1) := hMan (x + 1) hx1
    exact AnalyticAt.comp (f := fun y : ℂ => y + 1) h2 h1
  exact eqOn_of_eqOn_real_of_strip hσ han hMan (section_periodic_real hM)

lemma neg_inv_im_lower {w : ℂ} (hw : w ≠ 0) : -(1 / ‖w‖) ≤ -(1 / w).im := by
  have hnsq : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
  have him : -‖w‖ ≤ w.im := by
    have h := Complex.abs_im_le_norm w
    rw [abs_le] at h
    exact h.1
  have hval : -(1 / w).im = w.im / Complex.normSq w := by
    rw [one_div, Complex.inv_im]
    ring
  rw [hval, le_div_iff₀ hnsq, Complex.normSq_eq_norm_sq]
  have h1 : -(1 / ‖w‖) * ‖w‖ ^ 2 = -‖w‖ := by
    have hw0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    field_simp
  rw [h1]
  exact him

lemma section_im_pos {α lam σ : ℝ} (hlam : 0 ≤ lam) {z : ℂ} (hz : 4 ≤ z.im) (_hσ : 0 < σ)
    (hσz : 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ z.im / 2 - 2 / z.im) {M : ℂ → ℂ}
    (hM : ∀ x : ℂ, |x.im| < σ →
      M x = (z - 2 * lam * Complex.cos (2 * Real.pi * (x - α))) - 1 / M (x - α))
    (hbd : ∀ x : ℂ, |x.im| < σ → z.im / 2 ≤ ‖M x‖) :
    ∀ x : ℂ, |x.im| < σ → 0 < (M x).im := by
  have hzpos : (0:ℝ) < z.im := by linarith
  intro x hx
  have hx' : |(x - α).im| < σ := by simpa using hx
  have hlow : z.im / 2 ≤ ‖M (x - α)‖ := hbd (x - α) hx'
  have hne : M (x - α) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlow
    linarith
  have hδ : z.im - 2 * lam * Real.sinh (2 * Real.pi * σ)
      ≤ (z - 2 * lam * Complex.cos (2 * Real.pi * (x - α))).im := by
    have h := stripA_im_lower α hlam z hx
    rw [stripA_eq] at h
    convert h using 1
    push_cast
    ring
  have hstep : (M x).im = (z - 2 * lam * Complex.cos (2 * Real.pi * (x - α))).im
      - (1 / M (x - α)).im := by
    rw [hM x hx, Complex.sub_im]
  have hinv := neg_inv_im_lower hne
  have h2 : 1 / ‖M (x - α)‖ ≤ 2 / z.im := by
    have h3 : 1 / ‖M (x - α)‖ ≤ 1 / (z.im / 2) := one_div_le_one_div_of_le (by linarith) hlow
    have h4 : 1 / (z.im / 2) = 2 / z.im := by rw [one_div, inv_div]
    linarith
  have h3 : z.im - 2 * lam * Real.sinh (2 * Real.pi * σ) - 2 / z.im ≤ (M x).im := by
    linarith [hstep, hδ, hinv, h2]
  have h4 : z.im / 2 ≤ z.im - 2 * lam * Real.sinh (2 * Real.pi * σ) - 2 / z.im := by
    linarith
  linarith

lemma norm_cayley_lt_one {w : ℂ} (hw : 0 < w.im) : ‖(w - Complex.I) / (w + Complex.I)‖ < 1 := by
  have hden : w + Complex.I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at him
    linarith
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hden)]
  have h1 : ‖w - Complex.I‖ ^ 2 = w.re ^ 2 + (w.im - 1) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im, sub_zero]
    ring
  have h2 : ‖w + Complex.I‖ ^ 2 = w.re ^ 2 + (w.im + 1) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, add_zero]
    ring
  nlinarith [norm_nonneg (w - Complex.I), norm_nonneg (w + Complex.I), h1, h2, hw]

theorem amoM_strip_cayley {α lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : 4 ≤ z.im) {σ : ℝ}
    (hσ : 0 < σ) (hσz : 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ z.im / 2 - 2 / z.im) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G {x : ℂ | |x.im| < σ} ∧
      (∀ x : ℂ, |x.im| < σ → ‖G x‖ < 1) ∧
      (∀ x : ℂ, G (x + 1) = G x) ∧
      (∀ x : ℝ, G (x : ℂ) = (Work.TMContract.amoM α lam z x - Complex.I) /
        (Work.TMContract.amoM α lam z x + Complex.I)) := by
  have hlam0 : (0:ℝ) ≤ lam := le_of_lt hlam
  obtain ⟨M, hMan, hMbd, hMeq, hMlim⟩ := amoM_strip hlam hz hσ hσz
  have hMper : ∀ x : ℂ, |x.im| < σ → M (x + 1) = M x := section_periodic_strip hσ hMan hMlim
  have hMim : ∀ x : ℂ, |x.im| < σ → 0 < (M x).im :=
    section_im_pos hlam0 hz hσ hσz hMeq (fun x hx => (hMbd x hx).1)
  have hamoM : ∀ y : ℝ, Work.TMContract.amoM α lam z y = M (y : ℂ) :=
    fun y => (hMlim y).limUnder_eq
  have hUopen : IsOpen {y : ℂ | |y.im| < σ} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  refine ⟨(fun x : ℂ => if |x.im| < σ then (M x - Complex.I) / (M x + Complex.I) else 0),
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hMx_ne : M x + Complex.I ≠ 0 := by
      have h1 : z.im / 2 ≤ ‖M x‖ := (hMbd x hx).1
      have hb : ‖(M x + Complex.I) - Complex.I‖ ≤ ‖M x + Complex.I‖ + ‖Complex.I‖ :=
        norm_sub_le _ _
      have heq : (M x + Complex.I) - Complex.I = M x := by ring
      rw [heq, Complex.norm_I] at hb
      intro h0
      rw [h0, norm_zero] at hb
      linarith
    have hcay : AnalyticAt ℂ (fun w : ℂ => (w - Complex.I) / (w + Complex.I)) (M x) :=
      AnalyticAt.div (analyticAt_id.sub analyticAt_const)
        (analyticAt_id.add analyticAt_const) hMx_ne
    have hat : AnalyticAt ℂ (fun y : ℂ => (M y - Complex.I) / (M y + Complex.I)) x :=
      AnalyticAt.comp (f := M) (g := fun w : ℂ => (w - Complex.I) / (w + Complex.I))
        hcay (hMan x hx)
    refine hat.congr ?_
    filter_upwards [hUopen.mem_nhds hx] with y hy
    simp only [if_pos hy]
  · intro x hx
    change ‖(if |x.im| < σ then (M x - Complex.I) / (M x + Complex.I) else 0)‖ < 1
    rw [if_pos hx]
    exact norm_cayley_lt_one (hMim x hx)
  · intro x
    change (if |(x + 1).im| < σ then (M (x + 1) - Complex.I) / (M (x + 1) + Complex.I) else 0)
      = (if |x.im| < σ then (M x - Complex.I) / (M x + Complex.I) else 0)
    have him : (x + 1).im = x.im := by simp
    rw [him]
    by_cases hx : |x.im| < σ
    · rw [if_pos hx, if_pos hx, hMper x hx]
    · rw [if_neg hx, if_neg hx]
  · intro x
    change (if |((x : ℂ)).im| < σ then (M (x : ℂ) - Complex.I) / (M (x : ℂ) + Complex.I) else 0)
      = (Work.TMContract.amoM α lam z x - Complex.I)
        / (Work.TMContract.amoM α lam z x + Complex.I)
    have hx : |((x : ℂ)).im| < σ := by simpa using hσ
    rw [if_pos hx, hamoM x]

end

end Work.TMComp.MAnalytic
