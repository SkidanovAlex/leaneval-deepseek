import Mathlib
import Submission.Work.CNum.Basic
import Submission.Work.CNum.Jfun_defs
import Submission.Work.CNum.arc_bounds
import Submission.Work.CNum.LL_derivs
import Submission.Work.CNum.tD_bounds
import Submission.Work.CNum.sum_bndJ
import Submission.Work.CNum.chord_Icc

/-! # CNum: the chord bound for `Jfun`

`Jfun ψ = log ‖h(c₂ + ρ₂ e^{iψ})‖` is the value of `log ‖h‖` on the circle `C₂`
(`h = hauptH` the hauptmodul).  This file proves the *chord bound*

`Jfun ψ ≤ max (Jfun a) (Jfun b) + 1000 (b - a)²`   for `ψ ∈ [a,b]`, `-3.9 ≤ a ≤ b ≤ -2.39`,

which lets one bound `Jfun` on an interval from its two endpoint values.  It is the
`C₂`-analogue of `Hfun_chord`.

The proof follows the same plan as `Hfun_chord`: write `Jfun = log 256 + log ‖w ψ‖ + Σ'_m t_m`
with `w ψ = c₂ + ρ₂ e^{iψ}`, and show that the second derivative of the sum is bounded below
by `-8000` on the arc.  The summands `t_m = 24 log ‖1 + (w ψ)ᵐ‖` and their first and second
derivatives are handled by the chain rule on the complex curve `w`; on the arc `‖w ψ‖ ≤ rJ`
with `rJ = 79/100 < 1`, which makes all series absolutely convergent with summable bounding
sequences `u1J`, `bndJ`.  The constant is very generous: the true `inf` of the second
derivative is about `-34.7`.
-/

namespace Work.CNum

open Complex Metric Filter Topology
open scoped BigOperators RealInnerProductSpace
open ComplexConjugate

/-! ## 1. The constants -/

private lemma cenC2_eq : cenC2 = 629 / 572 := by
  norm_num [cenC2, aR, bR, kR, cR]

private lemma rho2sq_eq : rho2sq = 13225 / 20449 := by
  norm_num [rho2sq, cenC2, c0R, bR, aR, kR, cR]

private lemma sqrt_rho2sq_eq : Real.sqrt rho2sq = 115 / 143 := by
  rw [rho2sq_eq, Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
  norm_num

/-! ## 2. `Jfun` as a function of `w ψ = c₂ + ρ₂ e^{iψ}` -/

private lemma Jfun_eq (ψ : ℝ) :
    Jfun ψ = Real.log 256 + Real.log ‖wf ψ‖ + ∑' n : ℕ, tt (n + 1) ψ := by
  simp only [Jfun, wf, tt, cJ, uJ, cenC2_eq, sqrt_rho2sq_eq]

private lemma wf_eq (ψ : ℝ) :
    wf ψ = ((cJ + uJ * Real.cos ψ : ℝ) : ℂ) + ((uJ * Real.sin ψ : ℝ) : ℂ) * Complex.I := by
  simp only [wf]
  rw [show Complex.I * (ψ : ℂ) = (ψ : ℂ) * Complex.I from mul_comm _ _]
  rw [Complex.exp_ofReal_mul_I]
  push_cast
  ring

private lemma wf_re (ψ : ℝ) : (wf ψ).re = cJ + uJ * Real.cos ψ := by
  rw [wf_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

private lemma wf_im (ψ : ℝ) : (wf ψ).im = uJ * Real.sin ψ := by
  rw [wf_eq]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, mul_zero, add_zero, sub_zero]
  ring

private lemma norm_wf_sq (ψ : ℝ) : ‖wf ψ‖ ^ 2 = KK ψ := by
  rw [← Complex.normSq_eq_norm_sq, normSq_wf]

private lemma log_norm_wf (ψ : ℝ) : Real.log ‖wf ψ‖ = LL ψ := by
  have h1 : ‖wf ψ‖ = Real.sqrt (KK ψ) := by
    rw [← norm_wf_sq ψ, Real.sqrt_sq (norm_nonneg _)]
  rw [LL, h1, Real.log_sqrt (le_of_lt (KK_pos ψ))]
  ring

/-! ## 3. Derivatives of the curve `w` -/

private lemma hasDerivAt_wf (ψ : ℝ) : HasDerivAt wf (tanf ψ) ψ := by
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

private lemma hasDerivAt_tanf (ψ : ℝ) : HasDerivAt tanf (tanf2 ψ) ψ := by
  have h1 : HasDerivAt (fun ψ => wf ψ - (cJ : ℂ)) (tanf ψ) ψ :=
    (hasDerivAt_wf ψ).sub_const (cJ : ℂ)
  have h2 : HasDerivAt (fun ψ => Complex.I * (wf ψ - (cJ : ℂ))) (Complex.I * tanf ψ) ψ :=
    h1.const_mul Complex.I
  have h3 : HasDerivAt tanf (Complex.I * tanf ψ) ψ := h2
  convert h3 using 1
  rw [show Complex.I * tanf ψ = Complex.I * (Complex.I * (wf ψ - (cJ : ℂ))) from rfl,
    show tanf2 ψ = -(wf ψ - (cJ : ℂ)) from rfl, ← mul_assoc, Complex.I_mul_I]
  ring

/-! ## 4. The generic derivative lemmas for the summands -/

private lemma HasDerivAt.re_of_complex {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y : ℝ => (f y).re) f'.re x := by
  have h1 : HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℝ f') x := h.hasFDerivAt
  have h2 := (Complex.reCLM.hasFDerivAt (x := f x)).comp x h1
  have h3 := h2.hasDerivAt
  convert h3 using 1 <;> try rfl
  simp [ContinuousLinearMap.comp_apply]

private lemma wf_ne_one (m : ℕ) (hm : 1 ≤ m) {ψ : ℝ} (h : ‖wf ψ‖ < 1) : 1 + (wf ψ)^m ≠ 0 := by
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

/-- The real derivative of `log ‖F‖` along a complex curve, via `normSq`. -/
private lemma re_div_eq_mul_conj_div_normSq (w u : ℂ) (hu : u ≠ 0) :
    Complex.re (w / u) = (w * conj u).re / Complex.normSq u := by
  have hn : Complex.normSq u ≠ 0 := fun h => hu (Complex.normSq_eq_zero.mp h)
  rw [Complex.div_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  field_simp [hn]
  ring

private lemma hasDerivAt_log_norm_of_hasDerivAt {F : ℝ → ℂ} {x : ℝ} {w : ℂ}
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
  rw [hval, Complex.inner, ← re_div_eq_mul_conj_div_normSq w (F x) h0]

/-- First derivative of the `m`-th summand. -/
private lemma hasDerivAt_tt (m : ℕ) (hm : 1 ≤ m) {ψ : ℝ} (h : ‖wf ψ‖ < 1) :
    HasDerivAt (tt m) (tD m ψ) ψ := by
  have hF : HasDerivAt (fun y : ℝ => 1 + (wf y)^m) ((m : ℂ) * (wf ψ)^(m-1) * tanf ψ) ψ :=
    ((hasDerivAt_wf ψ).pow m).const_add 1
  have h0 : (fun y : ℝ => 1 + (wf y)^m) ψ ≠ 0 := wf_ne_one m hm h
  have hlog := hasDerivAt_log_norm_of_hasDerivAt hF h0
  have h24 := hlog.const_mul (24 : ℝ)
  have h6 : tt m = fun y : ℝ => 24 * Real.log ‖1 + (wf y)^m‖ := rfl
  rw [h6]
  convert h24 using 1 <;> try rfl

/-- The value identity `tD2 m ψ = 24 Re (Φ' ψ)` for the quotient rule. -/
private lemma val_identity (m : ℕ) (hm : 1 ≤ m) {ψ : ℝ} (hD : 1 + (wf ψ)^m ≠ 0) :
    (((m:ℂ) * (((m-1:ℕ):ℂ) * (wf ψ)^(m-2) * tanf ψ) * tanf ψ + ((m:ℂ) * (wf ψ)^(m-1)) * tanf2 ψ)
        * (1 + (wf ψ)^m) - ((m:ℂ) * (wf ψ)^(m-1) * tanf ψ) * ((m:ℂ) * (wf ψ)^(m-1) * tanf ψ))
      / (1 + (wf ψ)^m)^2
    = ((m:ℂ) * ((m:ℂ) - 1) * (wf ψ)^(m-2) * (tanf ψ)^2 / (1 + (wf ψ)^m)
        + (m:ℂ) * (wf ψ)^(m-1) * tanf2 ψ / (1 + (wf ψ)^m)
        - (m:ℂ)^2 * (wf ψ)^(2*m-2) * (tanf ψ)^2 / (1 + (wf ψ)^m)^2) := by
  have hc1 : ((m - 1 : ℕ) : ℂ) = (m : ℂ) - 1 := by
    rw [Nat.cast_sub hm]; norm_num
  rw [hc1, show 2*m-2 = (m-1)+(m-1) from by omega, pow_add]
  field_simp

/-- Second derivative of the `m`-th summand. -/
private lemma hasDerivAt_tD (m : ℕ) (hm : 1 ≤ m) {ψ : ℝ} (h : ‖wf ψ‖ < 1) :
    HasDerivAt (tD m) (tD2 m ψ) ψ := by
  have hD0 : 1 + (wf ψ)^m ≠ 0 := wf_ne_one m hm h
  have hm1 : m - 1 - 1 = m - 2 := by omega
  have hp : HasDerivAt (fun y : ℝ => (wf y)^(m-1)) (((m-1:ℕ):ℂ) * (wf ψ)^(m-2) * tanf ψ) ψ := by
    have hh := (hasDerivAt_wf ψ).pow (m-1)
    convert hh using 1 <;> try rfl
  have hN : HasDerivAt (fun y : ℝ => (m:ℂ) * (wf y)^(m-1) * tanf y)
      (((m:ℂ) * (((m-1:ℕ):ℂ) * (wf ψ)^(m-2) * tanf ψ)) * tanf ψ
        + ((m:ℂ) * (wf ψ)^(m-1)) * tanf2 ψ) ψ := by
    have h1 : HasDerivAt (fun y : ℝ => (m:ℂ) * (wf y)^(m-1))
        ((m:ℂ) * (((m-1:ℕ):ℂ) * (wf ψ)^(m-2) * tanf ψ)) ψ :=
      hp.const_mul (m:ℂ)
    exact h1.mul (hasDerivAt_tanf ψ)
  have hDen : HasDerivAt (fun y : ℝ => 1 + (wf y)^m) ((m:ℂ) * (wf ψ)^(m-1) * tanf ψ) ψ :=
    ((hasDerivAt_wf ψ).pow m).const_add 1
  have hdiv := hN.div hDen hD0
  have hre := HasDerivAt.re_of_complex hdiv
  have h24 := hre.const_mul (24:ℝ)
  have hval : tD2 m ψ = (24:ℝ) * Complex.re
      ((((m:ℂ) * (((m-1:ℕ):ℂ) * (wf ψ)^(m-2) * tanf ψ) * tanf ψ + ((m:ℂ) * (wf ψ)^(m-1)) * tanf2 ψ)
          * (1 + (wf ψ)^m) - ((m:ℂ) * (wf ψ)^(m-1) * tanf ψ) * ((m:ℂ) * (wf ψ)^(m-1) * tanf ψ))
        / (1 + (wf ψ)^m)^2) := by
    rw [val_identity m hm hD0]
    have htD2 : tD2 m ψ = 24 * (((m:ℂ) * ((m:ℂ) - 1) * (wf ψ)^(m-2) * (tanf ψ)^2 / (1 + (wf ψ)^m)
        + (m:ℂ) * (wf ψ)^(m-1) * tanf2 ψ / (1 + (wf ψ)^m)
        - (m:ℂ)^2 * (wf ψ)^(2*m-2) * (tanf ψ)^2 / (1 + (wf ψ)^m)^2)).re := rfl
    rw [htD2]
  rw [← hval] at h24
  convert h24 using 1 <;> try rfl

/-! ## 5. The base point `ψ = -π` -/

private lemma wf_neg_pi : wf (-Real.pi) = (((13 : ℝ) / 44 : ℝ) : ℂ) := by
  have h1 : Complex.exp (Complex.I * ((-Real.pi : ℝ) : ℂ)) = -1 := by
    rw [show Complex.I * ((-Real.pi : ℝ) : ℂ) = -((Real.pi : ℂ) * Complex.I) from by push_cast; ring]
    rw [Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
  rw [wf, h1]
  push_cast
  norm_num [cJ, uJ]

private lemma norm_wf_neg_pi : ‖wf (-Real.pi)‖ ≤ rJ := by
  rw [wf_neg_pi, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs,
    abs_of_nonneg (by norm_num)]
  norm_num [rJ]

private lemma summable_tt_base : Summable (fun k : ℕ => tt (k + 1) (-Real.pi)) := by
  have hb : ∀ k : ℕ, tt (k+1) (-Real.pi) = 24 * Real.log (1 + (13/44 : ℝ)^(k+1)) := by
    intro k
    simp only [tt]
    rw [wf_neg_pi]
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

private lemma summable_tD_base (hu1 : Summable (fun k : ℕ => u1J (k+1)))
    (hb : ∀ m : ℕ, 1 ≤ m → ‖tD m (-Real.pi)‖ ≤ u1J m) :
    Summable (fun k : ℕ => tD (k+1) (-Real.pi)) :=
  Summable.of_norm_bounded hu1 (fun k => hb (k+1) (by omega))



/-! ## 6. Assembly: `Jfun'` and `Jfun''` and the chord bound -/

private theorem Jfun_chord_aux
    (harc : ∀ ψ ∈ Set.Ioo (-3.905 : ℝ) (-2.385 : ℝ), Real.cos ψ ≤ -7/10 ∧ ‖wf ψ‖ ≤ rJ)
    (hLL : ∀ ψ ∈ Set.Ioo (-3.905 : ℝ) (-2.385 : ℝ),
      LL ψ = Real.log ‖wf ψ‖ ∧ HasDerivAt LL (LLD ψ) ψ ∧ HasDerivAt LLD (LLDD ψ) ψ ∧
        -2 ≤ LLDD ψ)
    (htD : ∀ ψ, ‖wf ψ‖ ≤ rJ → Summable (fun m : ℕ => u1J (m + 1)) ∧
      (∀ m : ℕ, 1 ≤ m → ‖tD m ψ‖ ≤ u1J m) ∧ (∀ m : ℕ, 1 ≤ m → ‖tD2 m ψ‖ ≤ bndJ m) ∧
      (∀ m : ℕ, 1 ≤ m → -tD2 m ψ ≤ bndJ m))
    (hsum : Summable (fun m : ℕ => bndJ (m + 1)) ∧ (∑' m : ℕ, bndJ (m + 1)) ≤ 6500)
    (hchord : ∀ {a b : ℝ} (hab : a ≤ b) {g g' g'' : ℝ → ℝ},
      (∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x) → (∀ x ∈ Set.Icc a b, HasDerivAt g' (g'' x) x) →
      (∀ x ∈ Set.Icc a b, -8000 ≤ g'' x) →
      ∀ φ ∈ Set.Icc a b, g φ ≤ max (g a) (g b) + 1000 * (b - a) ^ 2)
    {a b : ℝ} (hab : a ≤ b) (ha : -3.9 ≤ a) (hb : b ≤ -2.39) :
    ∀ ψ ∈ Set.Icc a b, Jfun ψ ≤ max (Jfun a) (Jfun b) + 1000 * (b - a) ^ 2 := by
  have hu1 : Summable (fun k : ℕ => u1J (k + 1)) := (htD (-Real.pi) norm_wf_neg_pi).1
  have hbase2 : Summable (fun k : ℕ => tD (k + 1) (-Real.pi)) :=
    summable_tD_base hu1 (fun m _ => (htD (-Real.pi) norm_wf_neg_pi).2.1 m (by omega))
  have ht_open : IsOpen (Set.Ioo (-3.905 : ℝ) (-2.385 : ℝ)) := isOpen_Ioo
  have ht_pre : IsPreconnected (Set.Ioo (-3.905 : ℝ) (-2.385 : ℝ)) := (convex_Ioo _ _).isPreconnected
  have hmem : (-Real.pi) ∈ Set.Ioo (-3.905 : ℝ) (-2.385 : ℝ) :=
    ⟨by linarith [Real.pi_lt_d20], by linarith [Real.pi_gt_three]⟩
  have hrJ1 : rJ < 1 := by norm_num [rJ]
  have hder_sum : ∀ y ∈ Set.Ioo (-3.905 : ℝ) (-2.385 : ℝ),
      HasDerivAt (fun z : ℝ => ∑' k : ℕ, tt (k + 1) z) (∑' k : ℕ, tD (k + 1) y) y := by
    intro y hy
    refine hasDerivAt_tsum_of_isPreconnected (u := fun k : ℕ => u1J (k + 1)) hu1 ht_open ht_pre
      ?_ ?_ hmem summable_tt_base hy
    · intro k z hz
      exact hasDerivAt_tt (k + 1) (by omega) (lt_of_le_of_lt (harc z hz).2 hrJ1)
    · intro k z hz
      exact (htD z (harc z hz).2).2.1 (k + 1) (by omega)
  have hder_sum2 : ∀ y ∈ Set.Ioo (-3.905 : ℝ) (-2.385 : ℝ),
      HasDerivAt (fun z : ℝ => ∑' k : ℕ, tD (k + 1) z) (∑' k : ℕ, tD2 (k + 1) y) y := by
    intro y hy
    refine hasDerivAt_tsum_of_isPreconnected (u := fun k : ℕ => bndJ (k + 1)) hsum.1 ht_open ht_pre
      ?_ ?_ hmem hbase2 hy
    · intro k z hz
      exact hasDerivAt_tD (k + 1) (by omega) (lt_of_le_of_lt (harc z hz).2 hrJ1)
    · intro k z hz
      exact (htD z (harc z hz).2).2.2.1 (k + 1) (by omega)
  have hmem_ab : ∀ x ∈ Set.Icc a b, x ∈ Set.Ioo (-3.905 : ℝ) (-2.385 : ℝ) := by
    intro x hx
    exact ⟨by linarith [hx.1, ha], by linarith [hx.2, hb]⟩
  have hJfun_eq : ∀ y ∈ Set.Ioo (-3.905 : ℝ) (-2.385 : ℝ),
      Jfun y = Real.log 256 + LL y + ∑' k : ℕ, tt (k + 1) y := by
    intro y hy
    rw [Jfun_eq, (hLL y hy).1]
  refine hchord (g := Jfun) (g' := fun x : ℝ => LLD x + ∑' k : ℕ, tD (k + 1) x)
    (g'' := fun x : ℝ => LLDD x + ∑' k : ℕ, tD2 (k + 1) x) hab ?_ ?_ ?_
  · intro x hx
    have hxt := hmem_ab x hx
    have h2 : HasDerivAt (fun y : ℝ => LL y + ∑' k : ℕ, tt (k + 1) y)
        (LLD x + ∑' k : ℕ, tD (k + 1) x) x :=
      (hLL x hxt).2.1.add (hder_sum x hxt)
    have h1 : HasDerivAt (fun y : ℝ => Real.log 256 + (LL y + ∑' k : ℕ, tt (k + 1) y))
        (LLD x + ∑' k : ℕ, tD (k + 1) x) x := h2.const_add (Real.log 256)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hxt] with y hy
    rw [hJfun_eq y hy, add_assoc]
  · intro x hx
    exact (hLL x (hmem_ab x hx)).2.2.1.add (hder_sum2 x (hmem_ab x hx))
  · intro x hx
    have hxt := hmem_ab x hx
    have hbounded : -(∑' k : ℕ, tD2 (k + 1) x) ≤ 6500 := by
      have hsum_neg : Summable (fun k : ℕ => -tD2 (k + 1) x) := by
        refine Summable.of_norm_bounded hsum.1 (fun k => ?_)
        have hk := (htD x (harc x hxt).2).2.2.1 (k + 1) (by omega)
        rw [Real.norm_eq_abs, abs_neg]
        exact hk
      have hle := Summable.tsum_le_tsum
        (fun k => (htD x (harc x hxt).2).2.2.2 (k + 1) (by omega)) hsum_neg hsum.1
      rw [tsum_neg] at hle
      linarith [hsum.2]
    have h2 := (hLL x hxt).2.2.2
    linarith

/-! ## 7. The chord bound for `Jfun` -/

theorem Jfun_chord {a b : ℝ} (hab : a ≤ b) (ha : -3.9 ≤ a) (hb : b ≤ -2.39) :
    ∀ ψ ∈ Set.Icc a b, Jfun ψ ≤ max (Jfun a) (Jfun b) + 1000 * (b - a) ^ 2 :=
  Jfun_chord_aux (fun ψ hψ => arc_bounds (ψ := ψ) hψ) (fun ψ hψ => LL_derivs (ψ := ψ) hψ)
    (fun ψ hψ => tD_bounds (ψ := ψ) hψ) sum_bndJ chord_Icc hab ha hb

end Work.CNum
