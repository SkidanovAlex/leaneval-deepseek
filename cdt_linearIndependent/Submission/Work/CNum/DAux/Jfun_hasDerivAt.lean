import Mathlib
import Submission.Work.CNum.Jfun_defs
import Submission.Work.CNum.arc_bounds
import Submission.Work.CNum.LL_derivs
import Submission.Work.CNum.tD_bounds
import Submission.Work.CNum.sum_bndJ
import Submission.Work.CNum.Jfun_chord

/-! # CNum.DAux: the first derivative of `Jfun` on the arc `(-3.905, -2.385)`

`Jfun ψ = log ‖h(c₂ + ρ₂ e^{iψ})‖ = log 256 + log ‖wf ψ‖ + Σ'_m tt m ψ` with
`wf ψ = c₂ + ρ₂ e^{iψ}`.  Differentiating term by term (majorant `u1J`, base point `-π`)
gives the first derivative `LLD ψ + Σ'_k tD (k+1) ψ` for every `ψ` on the arc.

The auxiliary lemmas below (`jh_*`) are public copies of the private computations of
`Submission/Work/CNum/Jfun_chord.lean`.
-/

namespace Work.CNum.DAux

open Complex Metric Filter Topology
open scoped BigOperators RealInnerProductSpace
open ComplexConjugate

/-! ## 1. The constants -/

private lemma cenC2_eq_jh : cenC2 = 629 / 572 := by
  norm_num [cenC2, aR, bR, kR, cR]

private lemma rho2sq_eq_jh : rho2sq = 13225 / 20449 := by
  norm_num [rho2sq, cenC2, c0R, bR, aR, kR, cR]

private lemma sqrt_rho2sq_eq_jh : Real.sqrt rho2sq = 115 / 143 := by
  rw [rho2sq_eq_jh, Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
  norm_num

/-! ## 2. `Jfun` as a function of `wf` -/

/-- `Jfun` in terms of the curve `wf` and the summands `tt`. -/
theorem jh_Jfun_eq (ψ : ℝ) :
    Jfun ψ = Real.log 256 + Real.log ‖wf ψ‖ + ∑' n : ℕ, tt (n + 1) ψ := by
  simp only [Jfun, wf, tt, cJ, uJ, cenC2_eq_jh, sqrt_rho2sq_eq_jh]

/-! ## 3. Derivatives of the curve `w` -/

/-- `wf` is differentiable with derivative `tanf`. -/
theorem jh_hasDerivAt_wf (ψ : ℝ) : HasDerivAt wf (tanf ψ) ψ := by
  have hid : HasDerivAt (fun ψ : ℝ => (ψ : ℂ)) 1 ψ := by
    simpa using (hasDerivAt_id ψ).ofReal_comp
  have h2 : HasDerivAt (fun ψ : ℝ => Complex.I * (ψ : ℂ)) (Complex.I * 1) ψ :=
    hid.const_mul Complex.I
  have h3 : HasDerivAt (fun ψ : ℝ => Complex.exp (Complex.I * (ψ : ℂ)))
      (Complex.exp (Complex.I * (ψ : ℂ)) * (Complex.I * 1)) ψ := h2.cexp
  have h4 : HasDerivAt (fun ψ : ℝ => (uJ : ℂ) * Complex.exp (Complex.I * (ψ : ℂ)))
      ((uJ : ℂ) * (Complex.exp (Complex.I * (ψ : ℂ)) * (Complex.I * 1))) ψ :=
    h3.const_mul (uJ : ℂ)
  have h5 : HasDerivAt (fun ψ : ℝ => (cJ : ℂ) + (uJ : ℂ) * Complex.exp (Complex.I * (ψ : ℂ)))
      ((uJ : ℂ) * (Complex.exp (Complex.I * (ψ : ℂ)) * (Complex.I * 1))) ψ :=
    h4.const_add (cJ : ℂ)
  have h6 : HasDerivAt wf ((uJ : ℂ) * (Complex.exp (Complex.I * (ψ : ℂ)) * (Complex.I * 1))) ψ :=
    h5
  convert h6 using 1
  simp only [tanf, wf]
  ring

/-- `tanf` is differentiable with derivative `tanf2`. -/
theorem jh_hasDerivAt_tanf (ψ : ℝ) : HasDerivAt tanf (tanf2 ψ) ψ := by
  have h1 : HasDerivAt (fun ψ => wf ψ - (cJ : ℂ)) (tanf ψ) ψ :=
    (jh_hasDerivAt_wf ψ).sub_const (cJ : ℂ)
  have h2 : HasDerivAt (fun ψ => Complex.I * (wf ψ - (cJ : ℂ))) (Complex.I * tanf ψ) ψ :=
    h1.const_mul Complex.I
  have h3 : HasDerivAt tanf (Complex.I * tanf ψ) ψ := h2
  convert h3 using 1
  rw [show Complex.I * tanf ψ = Complex.I * (Complex.I * (wf ψ - (cJ : ℂ))) from rfl,
    show tanf2 ψ = -(wf ψ - (cJ : ℂ)) from rfl, ← mul_assoc, Complex.I_mul_I]
  ring

/-! ## 4. Generic derivative lemmas for the summands -/

/-- Real part of a complex-valued `HasDerivAt`. -/
theorem jh_hasDerivAt_re_of_complex {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y : ℝ => (f y).re) f'.re x := by
  have h1 : HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℝ f') x := h.hasFDerivAt
  have h2 := (Complex.reCLM.hasFDerivAt (x := f x)).comp x h1
  have h3 := h2.hasDerivAt
  convert h3 using 1 <;> try rfl
  simp [ContinuousLinearMap.comp_apply]

/-- `1 + (wf ψ)^m ≠ 0` for `m ≥ 1` and `‖wf ψ‖ < 1`. -/
theorem jh_wf_ne_one (m : ℕ) (hm : 1 ≤ m) {ψ : ℝ} (h : ‖wf ψ‖ < 1) : 1 + (wf ψ)^m ≠ 0 := by
  intro hc
  have h1 : (1 + (wf ψ)^m).re = 0 := by rw [hc]; simp
  have h3 : ‖wf ψ ^ m‖ ≤ ‖wf ψ‖ ^ m := by rw [norm_pow]
  have h4 : ‖wf ψ‖ ^ m < 1 := pow_lt_one₀ (norm_nonneg _) h (by omega)
  have h5 : -1 < (wf ψ ^ m).re := by
    have h6 : -(‖wf ψ ^ m‖) ≤ (wf ψ ^ m).re := by
      have h7 := Complex.abs_re_le_norm (wf ψ ^ m)
      rw [abs_le] at h7
      exact h7.1
    linarith
  rw [Complex.add_re, Complex.one_re] at h1
  linarith

/-- The real part of a quotient, written with `normSq`. -/
theorem jh_re_div_eq_mul_conj_div_normSq (w u : ℂ) (hu : u ≠ 0) :
    Complex.re (w / u) = (w * conj u).re / Complex.normSq u := by
  have hn : Complex.normSq u ≠ 0 := fun h => hu (Complex.normSq_eq_zero.mp h)
  rw [Complex.div_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  field_simp [hn]
  ring

/-- The real derivative of `log ‖F‖` along a complex curve. -/
theorem jh_hasDerivAt_log_norm {F : ℝ → ℂ} {x : ℝ} {w : ℂ}
    (hF : HasDerivAt F w x) (h0 : F x ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log ‖F t‖) (Complex.re (w / F x)) x := by
  have hident : (fun t : ℝ => Real.log ‖F t‖)
      = fun t => (1 / 2 : ℝ) * Real.log (Complex.normSq (F t)) := by
    funext t
    have hs : Real.log ‖F t‖ = Real.log (Complex.normSq (F t)) / 2 := by
      rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg (F t))]
    rw [hs]
    ring
  have hnsq : HasDerivAt (fun t : ℝ => Complex.normSq (F t)) (2 * ⟪F x, w⟫) x := by
    simpa [Complex.normSq_eq_norm_sq] using
      (hF.norm_sq : HasDerivAt (fun t : ℝ => ‖F t‖ ^ 2) (2 * ⟪F x, w⟫) x)
  have hnsq0 : Complex.normSq (F x) ≠ 0 := ne_of_gt (Complex.normSq_pos.2 h0)
  have hlog : HasDerivAt (fun t : ℝ => Real.log (Complex.normSq (F t)))
      ((2 * ⟪F x, w⟫) / Complex.normSq (F x)) x := hnsq.log hnsq0
  have hhalf : HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * Real.log (Complex.normSq (F t)))
      ((1 / 2 : ℝ) * ((2 * ⟪F x, w⟫) / Complex.normSq (F x))) x := hlog.const_mul (1 / 2 : ℝ)
  have hval : (1 / 2 : ℝ) * ((2 * ⟪F x, w⟫) / Complex.normSq (F x))
      = ⟪F x, w⟫ / Complex.normSq (F x) := by ring
  convert hhalf using 1
  rw [hval, Complex.inner, ← jh_re_div_eq_mul_conj_div_normSq w (F x) h0]

/-- First derivative of the `m`-th summand. -/
theorem jh_hasDerivAt_tt (m : ℕ) (hm : 1 ≤ m) {ψ : ℝ} (h : ‖wf ψ‖ < 1) :
    HasDerivAt (tt m) (tD m ψ) ψ := by
  have hF : HasDerivAt (fun y : ℝ => 1 + (wf y)^m) ((m : ℂ) * (wf ψ)^(m-1) * tanf ψ) ψ :=
    ((jh_hasDerivAt_wf ψ).pow m).const_add 1
  have h0 : (fun y : ℝ => 1 + (wf y)^m) ψ ≠ 0 := jh_wf_ne_one m hm h
  have hlog := jh_hasDerivAt_log_norm hF h0
  have h24 := hlog.const_mul (24 : ℝ)
  have h6 : tt m = fun y : ℝ => 24 * Real.log ‖1 + (wf y)^m‖ := rfl
  rw [h6]
  convert h24 using 1 <;> try rfl

/-! ## 5. The base point `ψ = -π` -/

theorem jh_wf_neg_pi : wf (-Real.pi) = (((13 : ℝ) / 44 : ℝ) : ℂ) := by
  have h1 : Complex.exp (Complex.I * ((-Real.pi : ℝ) : ℂ)) = -1 := by
    rw [show Complex.I * ((-Real.pi : ℝ) : ℂ) = -((Real.pi : ℂ) * Complex.I) from by push_cast; ring]
    rw [Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
  rw [wf, h1]
  push_cast
  norm_num [cJ, uJ]

theorem jh_norm_wf_neg_pi : ‖wf (-Real.pi)‖ ≤ rJ := by
  rw [jh_wf_neg_pi, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs,
    abs_of_nonneg (by norm_num)]
  norm_num [rJ]

theorem jh_summable_tt_base : Summable (fun k : ℕ => tt (k + 1) (-Real.pi)) := by
  have hb : ∀ k : ℕ, tt (k+1) (-Real.pi) = 24 * Real.log (1 + (13/44 : ℝ)^(k+1)) := by
    intro k
    simp only [tt]
    rw [jh_wf_neg_pi]
    rw [show (1 : ℂ) + ((((13:ℝ)/44 : ℝ) : ℂ))^(k+1) = ((1 + (13/44 : ℝ)^(k+1) : ℝ) : ℂ) from by
      push_cast; ring]
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs,
      abs_of_nonneg (by positivity)]
  rw [show (fun k : ℕ => tt (k+1) (-Real.pi))
      = fun k : ℕ => 24 * Real.log (1 + (13/44 : ℝ)^(k+1)) from funext hb]
  have h2 : Summable (fun k : ℕ => 24 * ((13:ℝ)/44)^(k+1)) := by
    have h3 := (summable_geometric_of_norm_lt_one (show ‖((13:ℝ)/44)‖ < 1 by norm_num)).mul_left
      (24 * ((13:ℝ)/44))
    refine h3.congr (fun k => ?_)
    rw [pow_succ]; ring
  refine Summable.of_norm_bounded h2 (fun k => ?_)
  have hp : (0:ℝ) ≤ (13/44)^(k+1) := pow_nonneg (by norm_num) _
  have hlog : 0 ≤ Real.log (1 + (13/44 : ℝ)^(k+1)) := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hlog)]
  have hx : 0 < 1 + (13/44 : ℝ)^(k+1) := by positivity
  have hle := Real.log_le_sub_one_of_pos hx
  linarith

/-! ## 6. Term-by-term differentiation of the series on the arc -/

/-- On the arc `(-3.905, -2.385)` the series `Σ_k tt (k+1)` is term-by-term differentiable
with derivative `Σ_k tD (k+1)`. -/
theorem jh_hder_sum :
    ∀ y ∈ Set.Ioo (-3.905 : ℝ) (-2.385 : ℝ),
      HasDerivAt (fun z : ℝ => ∑' k : ℕ, tt (k + 1) z) (∑' k : ℕ, tD (k + 1) y) y := by
  have hu1 : Summable (fun k : ℕ => u1J (k + 1)) := u1J_summable
  have ht_open : IsOpen (Set.Ioo (-3.905 : ℝ) (-2.385 : ℝ)) := isOpen_Ioo
  have ht_pre : IsPreconnected (Set.Ioo (-3.905 : ℝ) (-2.385 : ℝ)) :=
    (convex_Ioo _ _).isPreconnected
  have hmem : (-Real.pi) ∈ Set.Ioo (-3.905 : ℝ) (-2.385 : ℝ) :=
    ⟨by linarith [Real.pi_lt_d20], by linarith [Real.pi_gt_three]⟩
  have hrJ1 : rJ < 1 := by norm_num [rJ]
  intro y hy
  refine hasDerivAt_tsum_of_isPreconnected (u := fun k : ℕ => u1J (k + 1)) hu1 ht_open ht_pre
    ?_ ?_ hmem jh_summable_tt_base hy
  · intro k z hz
    exact jh_hasDerivAt_tt (k + 1) (by omega)
      (lt_of_le_of_lt (arc_bounds (ψ := z) hz).2 hrJ1)
  · intro k z hz
    exact (tD_bounds (ψ := z) (arc_bounds (ψ := z) hz).2).2.1 (k + 1) (by omega)

/-! ## 7. The first derivative of `Jfun` on the arc -/

/-- First-derivative (chord) fact for `Jfun` on the arc `(-3.905, -2.385)`.
Hint: `Submission/Work/CNum/Jfun_chord.lean` proves a private theorem `Jfun_chord_aux`
whose internals (`hasDerivAt_wf`, `hasDerivAt_tanf`, `wf_ne_one`,
`hasDerivAt_log_norm_of_hasDerivAt`, `hasDerivAt_tt`, `hasDerivAt_tD`, `wf_neg_pi`,
`norm_wf_neg_pi`, `summable_tt_base`, and `hder_sum`) contain exactly this computation
(differentiating the series `Σ tt (k+1)` term-by-term with majorant `u1J` and base point `-π`
via `hasDerivAt_tsum_of_isPreconnected`).  Copy those private lemmas under new public names
and assemble with `Jfun_eq`, `LL_eq_log`, `hasDerivAt_LL`, `arc_bounds`, `tD_bounds`. -/
theorem Jfun_hasDerivAt {ψ : ℝ} (hψ : ψ ∈ Set.Ioo (-3.905 : ℝ) (-2.385 : ℝ)) :
    HasDerivAt Work.CNum.Jfun (Work.CNum.LLD ψ + ∑' k : ℕ, Work.CNum.tD (k + 1) ψ) ψ := by
  have hder := jh_hder_sum ψ hψ
  have hLL := hasDerivAt_LL ψ
  have h1 : HasDerivAt (fun y : ℝ => LL y + ∑' k : ℕ, tt (k + 1) y)
      (LLD ψ + ∑' k : ℕ, tD (k + 1) ψ) ψ := hLL.add hder
  have h2 : HasDerivAt (fun y : ℝ => Real.log 256 + (LL y + ∑' k : ℕ, tt (k + 1) y))
      (LLD ψ + ∑' k : ℕ, tD (k + 1) ψ) ψ := h1.const_add (Real.log 256)
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hψ] with y hy
  rw [jh_Jfun_eq y, LL_eq_log y]
  ring

end Work.CNum.DAux
