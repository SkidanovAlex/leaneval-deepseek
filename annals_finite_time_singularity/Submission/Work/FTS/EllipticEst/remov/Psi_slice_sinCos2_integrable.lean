import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular slices of a weak-class datum are `L¹` against `sin θ cos²θ`

For a datum of Elgindi's weak elliptic hypothesis class `EllWeakPos α k F Ψ` (`k ≥ 1`) and every
`z > 0`, the angular slice `θ ↦ Ψ z θ` is integrable against the angular weight `sin θ cos²θ`:

  `∫_{Iθ} |Ψ z θ| sin θ cos²θ dθ < ∞`.

The mathematical content is a one-dimensional bootstrap from the *only* `θ`-derivative control
that the hypothesis class provides, namely the honesty (`ℋ^k`-membership) of `∂_θθΨ`:

* `ℋ^k`-membership of `∂_θθΨ` gives `(∂_θθΨ)² sin(2θ)^{-η} ∈ L¹(Iθ)` (the `i = 0` summand of the
  `ℋ^k`-integrand is `(∂_θθΨ · w/sin(2θ)^{η/2})²`, and the weight is separated by a constant);
* the interval `Iθ` is bounded, so `f'' ∈ L¹(Iθ)` (Cauchy–Schwarz against `1`);
* a `C²` function on `(0, π/2)` with `f'' ∈ L¹` is bounded on `(0, π/2)` (two applications of the
  fundamental theorem of calculus).  The Dirichlet data `Ψ z 0 = Ψ z (π/2) = 0` extend the bound
  to the closed interval, and a bounded function is integrable against the bounded weight
  `sin θ cos²θ` on the finite interval `Iθ`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## Elementary angular facts -/

/-- `sin (2θ)` is nonnegative on the closed angular interval. -/
private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin (2θ)` is positive on the open angular interval. -/
private lemma sin_two_pos_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private lemma measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc

/-! ## A `C²` slice with integrable second derivative is bounded -/

/-- Fundamental theorem of calculus bound: the integral of `g` over a subinterval of `Iθ` is
bounded by the integral of `|g|` over the whole of `Iθ`. -/
private lemma intervalIntegral_abs_le_setIntegral {g : ℝ → ℝ}
    (hg : IntervalIntegrable (fun x => |g x|) volume 0 (π / 2)) {a b : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ π / 2) (hb : 0 ≤ b) (hb' : b ≤ π / 2) :
    |∫ x in a..b, g x| ≤ ∫ x in Work.Spaces.Iθ, |g x| := by
  have hle : (0 : ℝ) ≤ π / 2 := by linarith [Real.pi_pos]
  have hIeq : (∫ x in (0 : ℝ)..(π / 2), |g x|) = ∫ x in Work.Spaces.Iθ, |g x| := by
    rw [intervalIntegral.integral_of_le hle, Work.Spaces.Iθ,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rcases le_total a b with hab | hba
  · have h1 : |∫ x in a..b, g x| ≤ ∫ x in a..b, |g x| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    have h2 : (∫ x in a..b, |g x|) ≤ ∫ x in Work.Spaces.Iθ, |g x| := by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval ha hab hb'
        (Eventually.of_forall (fun x => abs_nonneg _)) hg
    linarith
  · have hsym : (∫ x in a..b, g x) = -(∫ x in b..a, g x) := intervalIntegral.integral_symm b a
    have h1 : |∫ x in b..a, g x| ≤ ∫ x in b..a, |g x| :=
      intervalIntegral.abs_integral_le_integral_abs hba
    have h2 : (∫ x in b..a, |g x|) ≤ ∫ x in Work.Spaces.Iθ, |g x| := by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval hb hba ha'
        (Eventually.of_forall (fun x => abs_nonneg _)) hg
    rw [hsym, abs_neg]
    linarith

/-- **A `C²` function on the open angular interval whose second derivative is integrable is
bounded.**

`f'' ∈ L¹(0, π/2)` is integrated twice by the fundamental theorem of calculus: `f'` is the sum of
its value at the midpoint `π/4` and `∫ f''`, hence bounded by `|f'(π/4)| + ∫_{Iθ}|f''|`, and then
`f` is bounded by `|f(π/4)| + (π/2)·(|f'(π/4)| + ∫_{Iθ}|f''|)`. -/
private lemma bdd_of_integrableOn_abs_second_deriv {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (π / 2)))
    (hg : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (π / 2)))
    (hint : MeasureTheory.IntegrableOn (fun θ : ℝ => |deriv (deriv f) θ|) Work.Spaces.Iθ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ C := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hle_half : (0 : ℝ) ≤ π / 2 := by linarith
  set θ₀ : ℝ := π / 4 with hθ₀def
  have hθ₀mem : θ₀ ∈ Set.Ioo (0 : ℝ) (π / 2) :=
    ⟨by rw [hθ₀def]; linarith, by rw [hθ₀def]; linarith⟩
  -- the second derivative is interval integrable over `Iθ`
  have hgi : IntervalIntegrable (fun x => |deriv (deriv f) x|) volume 0 (π / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle_half]
    exact hint
  -- the total mass of `|f''|`
  set M : ℝ := ∫ x in Work.Spaces.Iθ, |deriv (deriv f) x| with hMdef
  have hMnn : 0 ≤ M := integral_nonneg fun x => abs_nonneg (deriv (deriv f) x)
  -- the subinterval `uIcc θ₀ θ` lies inside the open angular interval
  have hsub : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), Set.uIcc θ₀ θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
    intro θ hθ x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hθ₀mem.1 h1, lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hθ₀mem.2⟩
  -- (1) the first derivative is bounded
  have hbound_deriv : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |deriv f θ| ≤ |deriv f θ₀| + M := by
    intro θ hθ
    have hFTC : (∫ x in θ₀..θ, deriv (deriv f) x) = deriv f θ - deriv f θ₀ :=
      intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hg.mono (hsub θ hθ))
    have hstep : |deriv f θ - deriv f θ₀| ≤ M := by
      rw [← hFTC]
      exact intervalIntegral_abs_le_setIntegral hgi (le_of_lt hθ₀mem.1) (le_of_lt hθ₀mem.2)
        (le_of_lt hθ.1) (le_of_lt hθ.2)
    calc |deriv f θ| = |deriv f θ₀ + (deriv f θ - deriv f θ₀)| := by ring_nf
      _ ≤ |deriv f θ₀| + |deriv f θ - deriv f θ₀| := abs_add_le _ _
      _ ≤ |deriv f θ₀| + M := by linarith
  -- (2) the function itself is bounded
  have hbound_f : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |f θ| ≤ |f θ₀| + (|deriv f θ₀| + M) * (π / 2) := by
    intro θ hθ
    have hFTC : (∫ x in θ₀..θ, deriv f x) = f θ - f θ₀ :=
      intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hf.mono (hsub θ hθ))
    have hc0 : 0 ≤ |deriv f θ₀| + M := by positivity
    have huo : Set.uIoc θ₀ θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
      intro x hx
      rw [Set.uIoc, Set.mem_Ioc] at hx
      obtain ⟨hx1, hx2⟩ := hx
      exact ⟨lt_trans (lt_min hθ₀mem.1 hθ.1) hx1,
        lt_of_le_of_lt hx2 (max_lt hθ₀mem.2 hθ.2)⟩
    have hnb : ‖∫ x in θ₀..θ, deriv f x‖ ≤ (|deriv f θ₀| + M) * |θ - θ₀| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (fun x hx => by
          rw [Real.norm_eq_abs]
          exact hbound_deriv x (huo hx))
    have hdist : |θ - θ₀| ≤ π / 2 := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith [hθ.2, hθ₀mem.1], by linarith [hθ₀mem.2, hθ.1]⟩
    have hstep : ‖∫ x in θ₀..θ, deriv f x‖ ≤ (|deriv f θ₀| + M) * (π / 2) :=
      le_trans hnb (mul_le_mul_of_nonneg_left hdist hc0)
    rw [Real.norm_eq_abs] at hstep
    calc |f θ| = |f θ₀ + (f θ - f θ₀)| := by ring_nf
      _ ≤ |f θ₀| + |f θ - f θ₀| := abs_add_le _ _
      _ = |f θ₀| + |∫ x in θ₀..θ, deriv f x| := by rw [hFTC]
      _ ≤ |f θ₀| + (|deriv f θ₀| + M) * (π / 2) := by linarith
  exact ⟨|f θ₀| + (|deriv f θ₀| + M) * (π / 2),
    by positivity, fun θ hθ => hbound_f θ hθ⟩

/-! ## The weighted square of `∂_θθΨ` is integrable -/

/-- The `i = 0` summand of the `ℋ^k`-integrand of `f` is the weighted square of `f` up to the
constant `(w z)²` on the slice. -/
private lemma weighted_sq_conv {w f s η : ℝ} (hw : w ≠ 0) (hs : 0 < s) :
    (w ^ 2)⁻¹ * (f * (w / s ^ (η / 2))) ^ 2 = f ^ 2 * s ^ (-η) := by
  have hsnn : 0 ≤ s := le_of_lt hs
  have hpow : (s ^ (η / 2)) ^ 2 = s ^ η := by
    rw [← Real.rpow_natCast (s ^ (η / 2)) 2, ← Real.rpow_mul hsnn]
    congr 1
    ring
  have h2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw
  have hsη : s ^ η ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hs η)
  rw [mul_pow, div_pow, hpow, div_eq_mul_inv, Real.rpow_neg hsnn]
  field_simp

/-- **The weighted square of the second angular derivative is integrable on every slice.**

The hypothesis `EllWeakPos α k F Ψ` contains the honesty of `∂_θθΨ` in `ℋ^k`; the `i = 0` summand
of its `ℋ^k`-integrand is `(∂_θθΨ · w/sin(2θ)^{η/2})²`, which differs from
`(∂_θθΨ)² sin(2θ)^{-η}` by the constant `(w z)²` on the slice `z`. -/
private lemma pthIter2_weighted_sq_integrable {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  intro z hz
  have hso : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth).pth.pth
  -- the `ℋ^k`-integrand of `∂_θθΨ` is integrable on the slice
  have hslice : MeasureTheory.Integrable (fun θ : ℝ =>
      Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 Ψ) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    h.memB.1 z (by rw [Work.Spaces.Iz]; exact le_of_lt hz)
  -- hence so is the `i = 0` summand
  have hsummand : MeasureTheory.Integrable (fun θ : ℝ =>
      (Work.Spaces.pthIter 2 Ψ z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' hslice ?_ ?_
    · have hcont : ContinuousOn (fun p : ℝ × ℝ =>
          Work.Spaces.pthIter 2 Ψ p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)))
          Work.FTS.EllipticEst.Q0 :=
        hso.continuousOn.mul Work.FTS.EllipticEst.continuousOn_wdivsin_Q0
      exact (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz).pow 2
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Iθ]
      exact Eventually.of_forall fun θ _ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.pthIter 2 Ψ) z θ 0 (Nat.zero_le k)
  -- separate the constant `(w z)²` from the weight
  refine (hsummand.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  exact weighted_sq_conv (by rw [Work.Spaces.w]; positivity) (sin_two_pos_of_Ioo hθ)

/-! ## An `L²`-function on the finite interval `Iθ` is `L¹` -/

/-- **On the bounded interval `Iθ`, a square-integrable function is integrable.**

With the weight `sin(2θ)^{-η} ≥ 1` (for `η ≥ 0`, away from the two endpoints) the weighted square
integral dominates `∫ f²`, and `|f| ≤ (f² + 1)/2` gives `∫|f| < ∞`. -/
private lemma abs_integrableOn_of_weighted_sq {η : ℝ} (hη : 0 ≤ η) {f : ℝ → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => |f θ|) Work.Spaces.Iθ := by
  -- the unweighted square is integrable
  have hsqi : MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' h (hf.pow 2) ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hspos : 0 < Real.sin (2 * θ) := sin_two_pos_of_Ioo hθ
    have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hsηpos : 0 < (Real.sin (2 * θ)) ^ η := Real.rpow_pos_of_pos hspos η
    have hsηle : (Real.sin (2 * θ)) ^ η ≤ 1 :=
      Real.rpow_le_one (le_of_lt hspos) hsin1 hη
    have hw : 1 ≤ (Real.sin (2 * θ)) ^ (-η) := by
      rw [Real.rpow_neg (le_of_lt hspos), inv_eq_one_div, le_div_iff₀ hsηpos]
      simpa using hsηle
    exact le_mul_of_one_le_right (sq_nonneg _) hw
  -- `|f| ≤ (f² + 1)/2`
  have hvol : (MeasureTheory.volume : Measure ℝ) Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hdom : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (1 / 2) * (f θ) ^ 2 + (1 / 2) * 1) Work.Spaces.Iθ :=
    (hsqi.const_mul (1 / 2)).add
      ((MeasureTheory.integrableOn_const (C := (1 : ℝ)) hvol).const_mul (1 / 2))
  refine (MeasureTheory.Integrable.mono' hdom hf ?_).abs
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Iθ (fun θ _ => ?_)
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|f θ| - 1), sq_abs (f θ), abs_nonneg (f θ)]

/-! ## The main theorem -/

theorem Psi_slice_sinCos2_integrable {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 1 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => |Ψ z θ| * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  intro z hz
  have hso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- the second angular derivative of the slice is a.e. strongly measurable
  have hpth2_aesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.pthIter 2 Ψ z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 Ψ p.1 p.2) (hso.pth.pth).continuousOn hz
  -- the second derivative of the slice is integrable
  have hL1 : MeasureTheory.IntegrableOn (fun θ : ℝ => |Work.Spaces.pthIter 2 Ψ z θ|)
      Work.Spaces.Iθ :=
    abs_integrableOn_of_weighted_sq Work.Spaces.eta_nonneg hpth2_aesm
      (pthIter2_weighted_sq_integrable h z hz)
  -- rewrite in terms of `deriv (deriv ·)`
  have hderiv_eq : ∀ θ : ℝ,
      deriv (deriv (fun t : ℝ => Ψ z t)) θ = Work.Spaces.pthIter 2 Ψ z θ := by
    intro θ
    simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  have hL1' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => |deriv (deriv (fun t : ℝ => Ψ z t)) θ|) Work.Spaces.Iθ :=
    hL1.congr_fun (fun θ _ => by rw [hderiv_eq θ]) measurableSet_Iθ
  -- the slice is `C¹` together with its derivative
  have hf1 : ContDiffOn ℝ 1 (fun θ : ℝ => Ψ z θ) (Set.Ioo 0 (π / 2)) :=
    (hso.curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
  have hg1 : ContDiffOn ℝ 1 (deriv (fun θ : ℝ => Ψ z θ)) (Set.Ioo 0 (π / 2)) := by
    have h' : ContDiffOn ℝ 1 (fun θ : ℝ => Work.Spaces.pth Ψ z θ)
        (Set.Ioo 0 (π / 2)) :=
      ((hso.pth).curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
    simpa only [Work.Spaces.pth] using h'
  obtain ⟨C, hCnn, hC⟩ :=
    bdd_of_integrableOn_abs_second_deriv hf1 hg1 hL1'
  -- the Dirichlet data extend the bound to the closed interval
  have hbdd : ∀ θ ∈ Work.Spaces.Iθ, |Ψ z θ| ≤ C := by
    intro θ hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · rw [← h0, h.zero z, abs_zero]; exact hCnn
    rcases eq_or_lt_of_le hθ.2 with hpi | hpi
    · rw [hpi, h.pi_half z, abs_zero]; exact hCnn
    · exact hC θ ⟨h0, hpi⟩
  -- a bounded function is integrable against the bounded weight
  have hvol : (MeasureTheory.volume : Measure ℝ) Work.Spaces.Iθ < ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  refine MeasureTheory.Integrable.mono'
    (MeasureTheory.integrableOn_const (C := C) (ne_of_lt hvol)) ?_ ?_
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => |Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2)
        Work.FTS.EllipticEst.Q0 :=
      hso.continuousOn.abs.mul
        (Continuous.continuousOn (by simp only [Work.Elliptic.sinCos2]; fun_prop :
          Continuous (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)))
    exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Iθ (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_abs]
    have h1 : |Work.Elliptic.sinCos2 θ| ≤ 1 :=
      Work.FTS.EllipticEst.abs_sinCos2_le_one hθ
    have h2 : |Ψ z θ| ≤ C := hbdd θ hθ
    nlinarith [abs_nonneg (Ψ z θ), hCnn]

end Work.FTS.EllipticEst.remov
