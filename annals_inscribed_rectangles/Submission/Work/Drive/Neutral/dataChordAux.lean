import Mathlib
import Submission.Work.Drive.Neutral.StripDiskAux

/-!
# Auxiliary lemmas for the chord data of the configuration strip

`Work.Drive.Neutral.curvePtAt γ x s = symmC (γ (toCirc (x * exp (s * I))))` is the complexified curve
point at the circle parameter of `x * exp (s * I)`; `dataChord`/`dataMid` are its differences and
midpoints.  This file collects the small lemmas needed to see that these are `C^∞` functions of
`(x, s)` on `{x ≠ 0}`, and to factor `dataChord` as `s • W` with `W` smooth and even in `s`.

The two ingredients are:

* `toCirc (x * exp (s * I)) = toCirc x * Circle.exp s`, so that the whole `(x, s)`-dependence of
  `curvePtAt` is the `(x, s)`-dependence of `toCirc x * Circle.exp s`;
* a **local argument**: `Circle.exp ((Complex.log x).im) = toCirc x` for every `x ≠ 0`, and
  `Circle.exp ((Complex.log (-x)).im + π) = toCirc x`, which are smooth on the two charts
  `Complex.slitPlane` and `{x | -x ∈ Complex.slitPlane}` covering `ℂ \ {0}` (`slitPlane_or_neg`).
-/

namespace Work.Drive.Neutral

open Manifold
open scoped Manifold ContDiff

noncomputable section

variable {γ : Circle → ℝ × ℝ}

/-! ## `symmC` is additive -/

lemma symmC_add (u v : ℝ × ℝ) : symmC (u + v) = symmC u + symmC v := by
  refine Complex.ext ?_ ?_ <;> simp [symmC]

lemma symmC_sub (u v : ℝ × ℝ) : symmC (u - v) = symmC u - symmC v := by
  refine Complex.ext ?_ ?_ <;> simp [symmC]

/-! ## `toCirc` -/

lemma toCirc_coe (y : ℂ) (hy : y ≠ 0) : ((toCirc y hy : Circle) : ℂ) = y / (‖y‖ : ℂ) := rfl

lemma toCirc_eq_exp_arg (y : ℂ) (hy : y ≠ 0) : toCirc y hy = Circle.exp (Complex.arg y) := by
  refine Subtype.ext ?_
  rw [toCirc_coe, Circle.coe_exp]
  have hnorm : ((‖y‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr hy
  rw [div_eq_iff hnorm, mul_comm]
  exact (Complex.norm_mul_exp_arg_mul_I y).symm

lemma toCirc_mul (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    toCirc (a * b) (mul_ne_zero ha hb) = toCirc a ha * toCirc b hb := by
  refine Subtype.ext ?_
  rw [Circle.coe_mul, toCirc_coe, toCirc_coe, toCirc_coe, Complex.norm_mul, Complex.ofReal_mul]
  field_simp

lemma toCirc_exp (s : ℝ) :
    toCirc (Complex.exp (s * Complex.I)) (Complex.exp_ne_zero _) = Circle.exp s := by
  refine Subtype.ext ?_
  rw [toCirc_coe, Circle.coe_exp, Complex.norm_exp_ofReal_mul_I, Complex.ofReal_one, div_one]

/-- If `Circle.exp θ` is the unit point `x / ‖x‖` then `curvePtAt γ x s` is the curve point at
`θ + s`. -/
lemma curvePtAt_eq_exp (γ : Circle → ℝ × ℝ) (x : ℂ) (hx : x ≠ 0) {θ : ℝ}
    (hθ : (Circle.exp θ : ℂ) = x / (‖x‖ : ℂ)) (s : ℝ) :
    curvePtAt γ x s = symmC (curve γ (θ + sClamp s)) := by
  have hA : toCirc (x * Complex.exp ((sClamp s) * Complex.I))
        (mul_ne_zero hx (Complex.exp_ne_zero _))
      = Circle.exp (θ + sClamp s) := by
    rw [toCirc_mul _ _ hx (Complex.exp_ne_zero _), toCirc_exp]
    have : toCirc x hx = Circle.exp θ := Subtype.ext (by rw [toCirc_coe]; exact hθ.symm)
    rw [this, ← Circle.exp_add]
  rw [curvePtAt, dif_neg hx, hA]
  rfl

/-- The chord vector in terms of a local argument `θ`. -/
lemma dataChord_eq_exp (γ : Circle → ℝ × ℝ) (x : ℂ) (hx : x ≠ 0) {θ : ℝ}
    (hθ : (Circle.exp θ : ℂ) = x / (‖x‖ : ℂ)) (s : ℝ) :
    dataChord γ x s = symmC (curve γ (θ + sClamp s) - curve γ (θ - sClamp s)) := by
  have h1 := curvePtAt_eq_exp γ x hx hθ s
  have h2 := curvePtAt_eq_exp γ x hx hθ (-s)
  rw [dataChord, endPlus, endMinus, h1, h2, sClamp_odd,
    show θ + -sClamp s = θ - sClamp s by ring, ← symmC_sub]

/-- The chord midpoint in terms of a local argument `θ`. -/
lemma dataMid_eq_exp (γ : Circle → ℝ × ℝ) (x : ℂ) (hx : x ≠ 0) {θ : ℝ}
    (hθ : (Circle.exp θ : ℂ) = x / (‖x‖ : ℂ)) (s : ℝ) :
    dataMid γ x s = symmC ((1 / 2 : ℝ) • (curve γ (θ + sClamp s) + curve γ (θ - sClamp s))) := by
  have h1 := curvePtAt_eq_exp γ x hx hθ s
  have h2 := curvePtAt_eq_exp γ x hx hθ (-s)
  rw [dataMid, endPlus, endMinus, h1, h2, sClamp_odd,
    show θ + -sClamp s = θ - sClamp s by ring]
  rw [show (symmC (curve γ (θ + sClamp s)) + symmC (curve γ (θ - sClamp s))) / 2
      = (↑(1 / 2 : ℝ) : ℂ) * (symmC (curve γ (θ + sClamp s)) + symmC (curve γ (θ - sClamp s))) by
    rw [div_eq_mul_inv, show (↑(1 / 2 : ℝ) : ℂ) = (2 : ℂ)⁻¹ by norm_num, mul_comm]]
  rw [← symmC_add, ← symmC_smul]

/-! ## The two local arguments -/

/-- First local argument: the imaginary part of the principal logarithm agrees with
`Circle.exp _ = x / ‖x‖` in the sense of the coercion to `ℂ`. -/
lemma exp_log_im (x : ℂ) (hx : x ≠ 0) :
    (Circle.exp ((Complex.log x).im) : ℂ) = x / (‖x‖ : ℂ) := by
  rw [Circle.coe_exp, Complex.log_im]
  rw [eq_div_iff (by rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr hx), mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I x

/-- Second local argument: on the complement of `slitPlane` the angle is `-π` there, and one
shifts by `π`. -/
lemma exp_log_neg_im (x : ℂ) (hx : x ≠ 0) :
    (Circle.exp ((Complex.log (-x)).im + Real.pi) : ℂ) = x / (‖x‖ : ℂ) := by
  have hnx : -x ≠ 0 := neg_ne_zero.mpr hx
  have h1 : (Circle.exp ((Complex.log (-x)).im) : ℂ) = (-x) / (‖-x‖ : ℂ) := exp_log_im (-x) hnx
  have hpi : ((Circle.exp Real.pi : Circle) : ℂ) = -1 := by
    rw [Circle.coe_exp, Complex.exp_pi_mul_I]
  have hexp : ((Circle.exp ((Complex.log (-x)).im + Real.pi) : Circle) : ℂ)
      = ((Circle.exp ((Complex.log (-x)).im) : Circle) : ℂ) * -1 := by
    rw [Circle.exp_add, Circle.coe_mul, hpi]
  rw [hexp, h1, norm_neg, mul_neg_one, ← neg_div, neg_neg]

lemma hlog_slit : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Complex.log Complex.slitPlane :=
  Complex.isOpen_slitPlane.contDiffOn_iff.mpr
    (fun x hx => (Complex.contDiffAt_log hx).restrict_scalars ℝ)

lemma contDiffOn_log_im : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : ℂ => (Complex.log x).im) Complex.slitPlane := by
  have h : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => z.im) Set.univ :=
    Complex.imCLM.contDiff.contDiffOn
  exact h.comp hlog_slit (fun x hx => trivial)

lemma contDiffOn_log_neg_im : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : ℂ => (Complex.log (-x)).im + Real.pi) {x : ℂ | -x ∈ Complex.slitPlane} := by
  have h : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℂ => (Complex.log (-x)).im)
      {x : ℂ | -x ∈ Complex.slitPlane} :=
    contDiffOn_log_im.comp contDiff_neg.contDiffOn (fun x hx => hx)
  exact h.add contDiffOn_const

lemma ne_zero_of_mem_slitPlane {x : ℂ} (hx : x ∈ Complex.slitPlane) : x ≠ 0 := by
  intro h
  rw [h, Complex.mem_slitPlane_iff] at hx
  rcases hx with h' | h'
  · exact lt_irrefl 0 h'
  · exact h' rfl

/-- Variant of `ne_zero_of_mem_slitPlane` for the second chart. -/
lemma ne_zero_of_neg_mem_slitPlane {x : ℂ} (hx : -x ∈ Complex.slitPlane) : x ≠ 0 :=
  neg_ne_zero.mp (ne_zero_of_mem_slitPlane hx)

/-- Every nonzero complex number lies in `slitPlane` or in its negative. -/
lemma slitPlane_or_neg (x : ℂ) (hx : x ≠ 0) :
    x ∈ Complex.slitPlane ∨ -x ∈ Complex.slitPlane := by
  by_cases h : 0 < x.re
  · exact Or.inl ((Complex.mem_slitPlane_iff).mpr (Or.inl h))
  · by_cases h2 : x.im ≠ 0
    · exact Or.inl ((Complex.mem_slitPlane_iff).mpr (Or.inr h2))
    · refine Or.inr ((Complex.mem_slitPlane_iff).mpr (Or.inl ?_))
      rw [Complex.neg_re]
      have h2' : x.im = 0 := not_ne_iff.mp h2
      have h4 : x.re ≠ 0 := by
        intro hz
        exact hx (Complex.ext (by rw [hz, Complex.zero_re]) (by rw [h2', Complex.zero_im]))
      have h5 : x.re < 0 := lt_of_le_of_ne (not_lt.mp h) h4
      linarith

lemma sClamp_zero : sClamp 0 = 0 := by
  rw [sClamp, sSig]
  norm_num

/-! ## The glueing factor `argGlue x = (1 - x.re / ‖x‖) / 2` -/

/-- The smooth glueing factor: it is `0` on the positive real axis and `1` on the negative one
(away from `0`). -/
def argGlue (x : ℂ) : ℝ := (1 - x.re / ‖x‖) / 2

lemma contDiffOn_argGlue : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) argGlue {x : ℂ | x ≠ 0} := by
  have hden : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℂ => ‖x‖) {x : ℂ | x ≠ 0} :=
    ContDiffOn.norm ℝ (contDiff_id.contDiffOn (s := {x : ℂ | x ≠ 0})) (fun x hx => hx)
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℂ => x.re / ‖x‖) {x : ℂ | x ≠ 0} :=
    (Complex.reCLM.contDiff.contDiffOn (s := {x : ℂ | x ≠ 0})).div hden
      (fun x hx => norm_ne_zero_iff.mpr hx)
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℂ => 1 - x.re / ‖x‖) {x : ℂ | x ≠ 0} := contDiffOn_const.sub h1
  exact ContDiffOn.congr (h2.div_const 2) (fun x hx => rfl)

lemma re_eq_norm_iff (x : ℂ) : x.re = ‖x‖ ↔ 0 ≤ x.re ∧ x.im = 0 := by
  constructor
  · intro h
    refine ⟨by rw [h]; exact norm_nonneg x, ?_⟩
    have hsq : ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [← h] at hsq
    have : x.im ^ 2 = 0 := by linarith
    exact sq_eq_zero_iff.mp this
  · rintro ⟨hre, him⟩
    have hx : x = ((x.re : ℝ) : ℂ) := Complex.ext rfl (by simp [him])
    rw [hx]
    simp [abs_of_nonneg hre]

/-- `argGlue` is nonzero exactly where the second chart is available. -/
lemma argGlue_ne_zero_imp (x : ℂ) (hx : x ≠ 0) (h : argGlue x ≠ 0) :
    -x ∈ Complex.slitPlane := by
  have hnorm : (‖x‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hx
  have hre : x.re ≠ ‖x‖ := by
    intro hc
    apply h
    rw [argGlue, hc, div_self hnorm, sub_self, zero_div]
  have hnot : ¬(0 ≤ x.re ∧ x.im = 0) := fun hc => hre ((re_eq_norm_iff x).mpr hc)
  rw [Complex.mem_slitPlane_iff, Complex.neg_re, Complex.neg_im]
  by_cases h1 : x.re < 0
  · exact Or.inl (by linarith)
  · refine Or.inr ?_
    have h2 : x.im ≠ 0 := fun him => hnot ⟨not_lt.mp h1, him⟩
    simpa using h2

/-- `1 - argGlue` is nonzero exactly where the first chart is available. -/
lemma one_sub_argGlue_ne_zero_imp (x : ℂ) (hx : x ≠ 0) (h : 1 - argGlue x ≠ 0) :
    x ∈ Complex.slitPlane := by
  have hnorm : (‖x‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hx
  have hk : argGlue x ≠ 1 := by intro hc; exact h (by rw [hc]; ring)
  have hre : x.re ≠ -‖x‖ := by
    intro hc
    apply hk
    rw [argGlue, hc, neg_div, div_self hnorm]
    norm_num
  have hnot : ¬(0 ≤ (-x).re ∧ (-x).im = 0) := fun hc => hre (by
    have h := (re_eq_norm_iff (-x)).mpr hc
    rw [Complex.neg_re, norm_neg] at h
    exact neg_eq_iff_eq_neg.mp h)
  rw [Complex.mem_slitPlane_iff]
  by_cases h1 : x.re > 0
  · exact Or.inl h1
  · refine Or.inr ?_
    intro him
    apply hnot
    constructor
    · rw [Complex.neg_re]; linarith [not_lt.mp h1]
    · simp [Complex.neg_im, him]

/-! ## Local smoothness of the chord data -/

lemma contDiffOn_dataChord_slit (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℝ => dataChord γ p.1 p.2)
      (Complex.slitPlane ×ˢ Set.univ) := by
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => symmC (curve γ t)) :=
    contDiff_symmC.comp (contDiff_curve_top hγ)
  have hθ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℝ => (Complex.log p.1).im)
      (Complex.slitPlane ×ˢ Set.univ) :=
    contDiffOn_log_im.comp contDiffOn_fst (fun p hp => hp.1)
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℝ => sClamp p.2)
      (Complex.slitPlane ×ˢ Set.univ) := (contDiff_sClamp.comp contDiff_snd).contDiffOn
  have hplus := hF.comp_contDiffOn (hθ.add hs)
  have hminus := hF.comp_contDiffOn (hθ.sub hs)
  refine ContDiffOn.congr (hplus.sub hminus) (fun p hp => ?_)
  obtain ⟨hx, _⟩ := hp
  rw [dataChord_eq_exp γ p.1 (ne_zero_of_mem_slitPlane hx) (exp_log_im p.1 (ne_zero_of_mem_slitPlane hx)) p.2,
    symmC_sub]
  rfl

lemma contDiffOn_dataMid_slit (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℝ => dataMid γ p.1 p.2)
      (Complex.slitPlane ×ˢ Set.univ) := by
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => symmC (curve γ t)) :=
    contDiff_symmC.comp (contDiff_curve_top hγ)
  have hθ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℝ => (Complex.log p.1).im)
      (Complex.slitPlane ×ˢ Set.univ) :=
    contDiffOn_log_im.comp contDiffOn_fst (fun p hp => hp.1)
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℝ => sClamp p.2)
      (Complex.slitPlane ×ˢ Set.univ) := (contDiff_sClamp.comp contDiff_snd).contDiffOn
  have hplus := hF.comp_contDiffOn (hθ.add hs)
  have hminus := hF.comp_contDiffOn (hθ.sub hs)
  have hhalf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℂ × ℝ => (1 / 2 : ℝ) • (symmC (curve γ ((Complex.log p.1).im + sClamp p.2))
        + symmC (curve γ ((Complex.log p.1).im - sClamp p.2)))) (Complex.slitPlane ×ˢ Set.univ) :=
    ContDiffOn.const_smul (1 / 2 : ℝ) (hplus.add hminus)
  refine ContDiffOn.congr hhalf (fun p hp => ?_)
  obtain ⟨hx, _⟩ := hp
  rw [dataMid_eq_exp γ p.1 (ne_zero_of_mem_slitPlane hx)
    (exp_log_im p.1 (ne_zero_of_mem_slitPlane hx)) p.2, symmC_smul, symmC_add, Complex.real_smul]
  -- (the rewrite above closes the goal)

lemma contDiffOn_dataChord_negSlit (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℝ => dataChord γ p.1 p.2)
      {p : ℂ × ℝ | -p.1 ∈ Complex.slitPlane} := by
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => symmC (curve γ t)) :=
    contDiff_symmC.comp (contDiff_curve_top hγ)
  have hθ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℂ × ℝ => (Complex.log (-p.1)).im + Real.pi)
      {p : ℂ × ℝ | -p.1 ∈ Complex.slitPlane} :=
    contDiffOn_log_neg_im.comp contDiffOn_fst (fun p hp => hp)
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℝ => sClamp p.2)
      {p : ℂ × ℝ | -p.1 ∈ Complex.slitPlane} := (contDiff_sClamp.comp contDiff_snd).contDiffOn
  have hplus := hF.comp_contDiffOn (hθ.add hs)
  have hminus := hF.comp_contDiffOn (hθ.sub hs)
  refine ContDiffOn.congr (hplus.sub hminus) (fun p hp => ?_)
  have hx : p.1 ≠ 0 := ne_zero_of_neg_mem_slitPlane hp
  rw [dataChord_eq_exp γ p.1 hx (exp_log_neg_im p.1 hx) p.2, symmC_sub]
  rfl

lemma contDiffOn_dataMid_negSlit (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℝ => dataMid γ p.1 p.2)
      {p : ℂ × ℝ | -p.1 ∈ Complex.slitPlane} := by
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => symmC (curve γ t)) :=
    contDiff_symmC.comp (contDiff_curve_top hγ)
  have hθ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℂ × ℝ => (Complex.log (-p.1)).im + Real.pi)
      {p : ℂ × ℝ | -p.1 ∈ Complex.slitPlane} :=
    contDiffOn_log_neg_im.comp contDiffOn_fst (fun p hp => hp)
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℝ => sClamp p.2)
      {p : ℂ × ℝ | -p.1 ∈ Complex.slitPlane} := (contDiff_sClamp.comp contDiff_snd).contDiffOn
  have hplus := hF.comp_contDiffOn (hθ.add hs)
  have hminus := hF.comp_contDiffOn (hθ.sub hs)
  have hhalf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℂ × ℝ => (1 / 2 : ℝ) • (symmC (curve γ ((Complex.log (-p.1)).im + Real.pi + sClamp p.2))
        + symmC (curve γ ((Complex.log (-p.1)).im + Real.pi - sClamp p.2))))
      {p : ℂ × ℝ | -p.1 ∈ Complex.slitPlane} :=
    ContDiffOn.const_smul (1 / 2 : ℝ) (hplus.add hminus)
  refine ContDiffOn.congr hhalf (fun p hp => ?_)
  have hx : p.1 ≠ 0 := ne_zero_of_neg_mem_slitPlane hp
  rw [dataMid_eq_exp γ p.1 hx (exp_log_neg_im p.1 hx) p.2, symmC_smul, symmC_add, Complex.real_smul]
  -- (the rewrite above closes the goal)

end

end Work.Drive.Neutral
