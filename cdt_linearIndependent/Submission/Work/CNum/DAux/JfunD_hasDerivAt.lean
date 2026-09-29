import Mathlib
import Submission.Work.CNum.Jfun_defs
import Submission.Work.CNum.arc_bounds
import Submission.Work.CNum.LL_derivs
import Submission.Work.CNum.tD_bounds
import Submission.Work.CNum.sum_bndJ
import Submission.Work.CNum.Jfun_chord

/-! # CNum/DAux: second derivative of the series part of `Jfun`

This file exposes, under public names, the derivative computations that
`Submission/Work/CNum/Jfun_chord.lean` uses privately (they are the `C₂`-analogue
of the summand computations of `Hfun_chord`: chain rule along the complex curve
`w ψ = c₂ + ρ₂ e^{iψ}`, termwise differentiation of `Σ'ₖ tD (k+1)` with majorant
`bndJ (k+1)` and base point `-π`), and assembles from them

`HasDerivAt (LLD + Σ'ₖ tD (k+1)) (LLDD ψ + Σ'ₖ tD2 (k+1) ψ) ψ`

for `ψ` in the arc `(-3.905, -2.385)`.
-/

namespace Work.CNum.DAux

open Complex Metric Filter Topology
open scoped BigOperators
open ComplexConjugate

/-! ## Chains rule for the curve `w` -/

lemma hasDerivAt_wf_pub (ψ : ℝ) : HasDerivAt wf (tanf ψ) ψ := by
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

lemma hasDerivAt_tanf_pub (ψ : ℝ) : HasDerivAt tanf (tanf2 ψ) ψ := by
  have h1 : HasDerivAt (fun ψ => wf ψ - (cJ : ℂ)) (tanf ψ) ψ :=
    (hasDerivAt_wf_pub ψ).sub_const (cJ : ℂ)
  have h2 : HasDerivAt (fun ψ => Complex.I * (wf ψ - (cJ : ℂ))) (Complex.I * tanf ψ) ψ :=
    h1.const_mul Complex.I
  have h3 : HasDerivAt tanf (Complex.I * tanf ψ) ψ := h2
  convert h3 using 1
  rw [show Complex.I * tanf ψ = Complex.I * (Complex.I * (wf ψ - (cJ : ℂ))) from rfl,
    show tanf2 ψ = -(wf ψ - (cJ : ℂ)) from rfl, ← mul_assoc, Complex.I_mul_I]
  ring

/-! ## The real part of a complex derivative -/

lemma hasDerivAt_re_of_complex {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y : ℝ => (f y).re) f'.re x := by
  have h1 : HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℝ f') x := h.hasFDerivAt
  have h2 := (Complex.reCLM.hasFDerivAt (x := f x)).comp x h1
  have h3 := h2.hasDerivAt
  convert h3 using 1 <;> try rfl
  simp [ContinuousLinearMap.comp_apply]

/-! ## Non-vanishing of the denominator -/

lemma wf_ne_one' (m : ℕ) (hm : 1 ≤ m) {ψ : ℝ} (h : ‖wf ψ‖ < 1) : 1 + (wf ψ)^m ≠ 0 := by
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

/-! ## The quotient rule value identity -/

lemma val_identity' (m : ℕ) (hm : 1 ≤ m) {ψ : ℝ} (hD : 1 + (wf ψ)^m ≠ 0) :
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

/-! ## Derivative of the summand `tD` -/

lemma hasDerivAt_tD_pub (m : ℕ) (hm : 1 ≤ m) {ψ : ℝ} (h : ‖wf ψ‖ < 1) :
    HasDerivAt (tD m) (tD2 m ψ) ψ := by
  have hD0 : 1 + (wf ψ)^m ≠ 0 := wf_ne_one' m hm h
  have hm1 : m - 1 - 1 = m - 2 := by omega
  have hp : HasDerivAt (fun y : ℝ => (wf y)^(m-1)) (((m-1:ℕ):ℂ) * (wf ψ)^(m-2) * tanf ψ) ψ := by
    have hh := (hasDerivAt_wf_pub ψ).pow (m-1)
    convert hh using 1 <;> try rfl
  have hN : HasDerivAt (fun y : ℝ => (m:ℂ) * (wf y)^(m-1) * tanf y)
      (((m:ℂ) * (((m-1:ℕ):ℂ) * (wf ψ)^(m-2) * tanf ψ)) * tanf ψ
        + ((m:ℂ) * (wf ψ)^(m-1)) * tanf2 ψ) ψ := by
    have h1 : HasDerivAt (fun y : ℝ => (m:ℂ) * (wf y)^(m-1))
        ((m:ℂ) * (((m-1:ℕ):ℂ) * (wf ψ)^(m-2) * tanf ψ)) ψ :=
      hp.const_mul (m:ℂ)
    exact h1.mul (hasDerivAt_tanf_pub ψ)
  have hDen : HasDerivAt (fun y : ℝ => 1 + (wf y)^m) ((m:ℂ) * (wf ψ)^(m-1) * tanf ψ) ψ :=
    ((hasDerivAt_wf_pub ψ).pow m).const_add 1
  have hdiv := hN.div hDen hD0
  have hre := hasDerivAt_re_of_complex hdiv
  have h24 := hre.const_mul (24:ℝ)
  have hval : tD2 m ψ = (24:ℝ) * Complex.re
      ((((m:ℂ) * (((m-1:ℕ):ℂ) * (wf ψ)^(m-2) * tanf ψ) * tanf ψ + ((m:ℂ) * (wf ψ)^(m-1)) * tanf2 ψ)
          * (1 + (wf ψ)^m) - ((m:ℂ) * (wf ψ)^(m-1) * tanf ψ) * ((m:ℂ) * (wf ψ)^(m-1) * tanf ψ))
        / (1 + (wf ψ)^m)^2) := by
    rw [val_identity' m hm hD0]
    have htD2 : tD2 m ψ = 24 * (((m:ℂ) * ((m:ℂ) - 1) * (wf ψ)^(m-2) * (tanf ψ)^2 / (1 + (wf ψ)^m)
        + (m:ℂ) * (wf ψ)^(m-1) * tanf2 ψ / (1 + (wf ψ)^m)
        - (m:ℂ)^2 * (wf ψ)^(2*m-2) * (tanf ψ)^2 / (1 + (wf ψ)^m)^2)).re := rfl
    rw [htD2]
  rw [← hval] at h24
  convert h24 using 1 <;> try rfl

/-! ## The base point `ψ = -π` -/

lemma wf_neg_pi' : wf (-Real.pi) = (((13 : ℝ) / 44 : ℝ) : ℂ) := by
  have h1 : Complex.exp (Complex.I * ((-Real.pi : ℝ) : ℂ)) = -1 := by
    rw [show Complex.I * ((-Real.pi : ℝ) : ℂ) = -((Real.pi : ℂ) * Complex.I) from by push_cast; ring]
    rw [Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
  rw [wf, h1]
  push_cast
  norm_num [cJ, uJ]

lemma norm_wf_neg_pi' : ‖wf (-Real.pi)‖ ≤ rJ := by
  rw [wf_neg_pi', Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs,
    abs_of_nonneg (by norm_num)]
  norm_num [rJ]

lemma summable_tD_base' (hu1 : Summable (fun k : ℕ => u1J (k+1)))
    (hb : ∀ m : ℕ, 1 ≤ m → ‖tD m (-Real.pi)‖ ≤ u1J m) :
    Summable (fun k : ℕ => tD (k+1) (-Real.pi)) :=
  Summable.of_norm_bounded hu1 (fun k => hb (k+1) (by omega))

/-- Second-derivative of the series part of `Jfun` on the arc `(-3.905, -2.385)`:
if `LLD + Σ' k, tD (k+1)` is the first derivative of `Jfun`, then its derivative is
`LLDD ψ + Σ' k, tD2 (k+1) ψ`.
Hint: this is exactly the statement `hder_sum2` proved inside the private theorem
`Jfun_chord_aux` of `Submission/Work/CNum/Jfun_chord.lean`, combined with
`hasDerivAt_LLD` from `Submission/Work/CNum/LL_derivs.lean` via `HasDerivAt.add`
(and `HasDerivAt.const_add`); the private lemmas `hasDerivAt_tD`, `hasDerivAt_wf`,
`hasDerivAt_tanf`, `wf_neg_pi`, `norm_wf_neg_pi`, `summable_tD_base`, `summable_tt_base`
in that file contain the needed computations (copy them under new public names). -/
theorem JfunD_hasDerivAt {ψ : ℝ} (hψ : ψ ∈ Set.Ioo (-3.905 : ℝ) (-2.385 : ℝ)) :
    HasDerivAt (fun x : ℝ => Work.CNum.LLD x + ∑' k : ℕ, Work.CNum.tD (k + 1) x)
      (Work.CNum.LLDD ψ + ∑' k : ℕ, Work.CNum.tD2 (k + 1) ψ) ψ := by
  have ht_open : IsOpen (Set.Ioo (-3.905 : ℝ) (-2.385 : ℝ)) := isOpen_Ioo
  have ht_pre : IsPreconnected (Set.Ioo (-3.905 : ℝ) (-2.385 : ℝ)) :=
    (convex_Ioo _ _).isPreconnected
  have hmem : (-Real.pi) ∈ Set.Ioo (-3.905 : ℝ) (-2.385 : ℝ) :=
    ⟨by linarith [Real.pi_lt_d20], by linarith [Real.pi_gt_three]⟩
  have hrJ1 : rJ < 1 := by norm_num [rJ]
  have hbase2 : Summable (fun k : ℕ => tD (k+1) (-Real.pi)) :=
    summable_tD_base' u1J_summable
      (fun m _ => (tD_bounds norm_wf_neg_pi').2.1 m (by omega))
  have hder_sum2 : HasDerivAt (fun z : ℝ => ∑' k : ℕ, tD (k + 1) z)
      (∑' k : ℕ, tD2 (k + 1) ψ) ψ := by
    refine hasDerivAt_tsum_of_isPreconnected (u := fun k : ℕ => bndJ (k + 1)) sum_bndJ.1
      ht_open ht_pre ?_ ?_ hmem hbase2 hψ
    · intro k z hz
      exact hasDerivAt_tD_pub (k + 1) (by omega) (lt_of_le_of_lt (arc_bounds hz).2 hrJ1)
    · intro k z hz
      exact (tD_bounds (arc_bounds hz).2).2.2.1 (k + 1) (by omega)
  exact (hasDerivAt_LLD ψ).add hder_sum2

end Work.CNum.DAux
