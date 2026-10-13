/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise slice bound `σ cos θ (v''² + v'²) ≤ C·(weighted norms)`

Target: `Work.FTS.EllipticEst.remov.slice_bd_ptwise`.

With `v = u / cos θ` on the slice, `σ = sin(2θ)^{2-γ}` (`1 ≤ γ ≤ 3/2`), `Lzero1 u = g` and
`Iθ = [0, π/2]`, the bound

  `σ θ · cos θ · (v''(θ)² + v'(θ)²) ≤ C (∫(g')²σ + ∫(u'')²sEta + ∫(u')² + ∫u² + ∫g²σ)`

is proved for `θ ∈ [π/4, π/2]`.  This is the *boundary-term control* of Elgindi's `§H2` Step 5
in the one-dimensional slice form: the weight `σ cos θ` vanishes at the endpoint `π/2`, and the
pointwise values of `v'` and `v''` there are controlled by the weighted `L²` data.

## Structure of the argument

The two auxiliary quantities

* `Ψ₁ := cos³θ · v'`,
* `Ψ₂ := cos⁴θ · v''`

satisfy (on `(0,π/2)`)

* `(Ψ₁)' = -(4u+g)·cos²θ`,
* `(Ψ₂)' = -cos³θ·g' - cos⁴θ·v' + 4 sinθcos³θ·v`.

The point of the normalisation by `cos³`, resp. `cos⁴`, is that `Ψ₁` (resp. `Ψ₂`) has a finite
*vanishing* limit at `π/2`: the pointwise values of `Ψ₁` and `Ψ₂` at `θ` are bounded by the
tail integrals of their derivatives (see `abs_le_tail_integral_of_primitive` and
`abs_le_tail_integral_of_double_primitive`), which are controlled by the weighted data via
Cauchy–Schwarz against `σ`, the elementary weight bounds of `slice_bd_weights` and the
pointwise bounds `|u'| ≲ √(∫(u'')²sEta) + √(∫(u')²)`, `|u| ≤ (π/2-θ)|u'|`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.remov.cosBarIdents
import Submission.Work.FTS.EllipticEst.remov.slice_v_identities
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_v_ident
import Submission.Work.FTS.EllipticEst.remov.abs_le_tail_of_bounded_double_primitive
import Submission.Work.FTS.EllipticEst.remov.slice_bd_sup_bounds
import Submission.Work.FTS.EllipticEst.remov.slice_bd_tail_g
import Submission.Work.FTS.EllipticEst.remov.slice_bd_tail_gprime

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ### Elementary facts on the open slice -/

/-- `cos` is positive on the open slice. -/
private lemma cos_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩

/-- `cos` does not vanish on the open slice. -/
private lemma cos_ne_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos θ ≠ 0 :=
  ne_of_gt (cos_pos_of_mem_Ioo hθ)

/-- `v = u/cos θ` is `C³` on the open slice. -/
private lemma slice_contDiffOn (u : ℝ → ℝ) (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 3 (fun t => u t / Real.cos t) (Set.Ioo 0 (Real.pi / 2)) :=
  hu.div Real.contDiff_cos.contDiffOn (fun t ht => cos_ne_of_mem_Ioo ht)

/-- `v` is differentiable at every point of the open slice. -/
private lemma hasDerivAt_slice (u : ℝ → ℝ) (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      HasDerivAt (fun t => u t / Real.cos t) (deriv (fun t => u t / Real.cos t) θ) θ := by
  intro θ hθ
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  exact (((slice_contDiffOn u hu).contDiffAt hIoo).differentiableAt (by norm_num)).hasDerivAt

/-- The second derivative of `v` exists at every point of the open slice. -/
private lemma hasDerivAt_deriv_slice (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      HasDerivAt (fun t => deriv (fun s => u s / Real.cos s) t)
        (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) θ := by
  intro θ hθ
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hC1 : DifferentiableAt ℝ (deriv (fun t => u t / Real.cos t)) θ := by
    have h := contDiffAt_iteratedDeriv (f := fun t => u t / Real.cos t) (x := θ)
      (n := 3) (k := 1) ((slice_contDiffOn u hu).contDiffAt hIoo) (by norm_num)
    rw [iteratedDeriv_one] at h
    exact h.differentiableAt (by norm_num)
  exact hC1.hasDerivAt

/-- The third derivative of `v` exists at every point of the open slice. -/
private lemma hasDerivAt_deriv_deriv_slice (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      HasDerivAt (fun t => deriv (fun s => deriv (fun r => u r / Real.cos r) s) t)
        (deriv (fun t => deriv (fun s => deriv (fun r => u r / Real.cos r) s) t) θ) θ := by
  intro θ hθ
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hC1 : DifferentiableAt ℝ
      (deriv (fun t => deriv (fun s => u s / Real.cos s) t)) θ := by
    have h := contDiffAt_iteratedDeriv (f := fun t => u t / Real.cos t) (x := θ)
      (n := 3) (k := 2) ((slice_contDiffOn u hu).contDiffAt hIoo) (by norm_num)
    rw [itd_two] at h
    exact h.differentiableAt (by norm_num)
  exact hC1.hasDerivAt

/-! ### The two derivative identities -/

/-- `Ψ₁' = -(4u+g)·cos²θ`, where `Ψ₁ = cos³θ·v'`. -/
private lemma Psi1_hasDerivAt (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      HasDerivAt (fun t => (Real.cos t) ^ 3 * deriv (fun s => u s / Real.cos s) t)
        (-(4 * u θ + g θ) * (Real.cos θ) ^ 2) θ := by
  intro θ hθ
  have hc : HasDerivAt (fun t => (Real.cos t) ^ 3)
      (3 * (Real.cos θ) ^ 2 * (-Real.sin θ)) θ := by
    exact (Real.hasDerivAt_cos θ).pow 3
  have hprod := hc.mul (hasDerivAt_deriv_slice u hu θ hθ)
  convert hprod using 1
  obtain ⟨hL, -⟩ := slice_v_identities u hu θ hθ
  have hC : Real.cos θ ≠ 0 := cos_ne_of_mem_Ioo hθ
  have hu_eq : u θ = Real.cos θ * (u θ / Real.cos θ) := by field_simp
  rw [← hg θ hθ, hL]
  linear_combination (-4 * (Real.cos θ) ^ 2) * hu_eq

/-- `Ψ₂' = -cos³θ·g' - cos⁴θ·v' + 4 sinθcos³θ·v`, where `Ψ₂ = cos⁴θ·v''`. -/
private lemma Psi2_hasDerivAt (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      HasDerivAt (fun t => (Real.cos t) ^ 4 * deriv (fun s => deriv (fun r => u r / Real.cos r) s) t)
        (-(Real.cos θ) ^ 3 * deriv g θ - (Real.cos θ) ^ 4 * deriv (fun t => u t / Real.cos t) θ
          + 4 * Real.sin θ * (Real.cos θ) ^ 3 * (u θ / Real.cos θ)) θ := by
  intro θ hθ
  have hc : HasDerivAt (fun t => (Real.cos t) ^ 4)
      (4 * (Real.cos θ) ^ 3 * (-Real.sin θ)) θ := by
    exact (Real.hasDerivAt_cos θ).pow 4
  have hprod := hc.mul (hasDerivAt_deriv_deriv_slice u hu θ hθ)
  convert hprod using 1
  have hg' := slice_gprime_v_ident u g hu hg θ hθ
  rw [hg']
  ring

/-! ### Elementary helpers for the tail estimates -/

/-- `cos θ ≤ π/2 - θ` for `θ ∈ [0, π/2]`. -/
private lemma cos_le_pi_div_two_sub {θ : ℝ} (h0 : 0 ≤ θ) (h2 : θ ≤ Real.pi / 2) :
    Real.cos θ ≤ Real.pi / 2 - θ := by
  have h : Real.cos θ = Real.sin (Real.pi / 2 - θ) := by
    have h1 := Real.cos_pi_div_two_sub (Real.pi / 2 - θ)
    rwa [show Real.pi / 2 - (Real.pi / 2 - θ) = θ by ring] at h1
  rw [h]
  exact Real.sin_le (by linarith)

/-- `sin (2θ) ≥ 0` for `θ ∈ [0, π/2]`. -/
private lemma sin_two_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h2 : θ ≤ Real.pi / 2) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])

/-- The weight `sEta = sin(2θ)^{-η}` is nonnegative on the slice. -/
private lemma sEta_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h2 : θ ≤ Real.pi / 2) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg (sin_two_nonneg h0 h2) _

/-- The weight `σ = sin(2θ)^{2-γ}` is nonnegative on the slice. -/
private lemma sigma_nonneg (γ : ℝ) {θ : ℝ} (h0 : 0 ≤ θ) (h2 : θ ≤ Real.pi / 2) :
    0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
  Real.rpow_nonneg (sin_two_nonneg h0 h2) _

/-- The restriction to `Ioc a b` is the restriction to `Ioo a b` (they differ by a point). -/
private lemma restrict_Ioc_eq_restrict_Ioo (a b : ℝ) :
    MeasureTheory.volume.restrict (Set.Ioc a b) = MeasureTheory.volume.restrict (Set.Ioo a b) :=
  MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Ioc (a := a) (b := b)).symm

/-- A function bounded on a finite-measure set is integrable there. -/
private lemma integrableOn_of_bound {s : Set ℝ} (hsm : MeasurableSet s)
    (hfin : MeasureTheory.volume s ≠ ⊤) {f : ℝ → ℝ} {M : ℝ}
    (hfm : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict s))
    (h : ∀ t ∈ s, |f t| ≤ M) : MeasureTheory.IntegrableOn f s :=
  MeasureTheory.Integrable.mono'
    (MeasureTheory.integrableOn_const (C := M) (by simpa using hfin)) hfm
    (by
      rw [MeasureTheory.ae_restrict_iff' hsm]
      exact Filter.Eventually.of_forall fun t ht => by
        simpa only [Real.norm_eq_abs] using h t ht)

/-- Cauchy–Schwarz for set integrals, in square-root form. -/
private lemma cs_sqrt_le {F H : ℝ → ℝ} {s : Set ℝ} (hsm : MeasurableSet s)
    (hF : MeasureTheory.MemLp F 2 (MeasureTheory.volume.restrict s))
    (hH : MeasureTheory.MemLp H 2 (MeasureTheory.volume.restrict s)) :
    |∫ x in s, F x * H x|
      ≤ Real.sqrt (∫ x in s, F x ^ 2) * Real.sqrt (∫ x in s, H x ^ 2) := by
  have h := Work.Spaces.cs_integral hF hH
  have hFnn : 0 ≤ ∫ x in s, F x ^ 2 :=
    MeasureTheory.setIntegral_nonneg hsm fun x _ => sq_nonneg _
  have h1 : |∫ x in s, F x * H x| = Real.sqrt ((∫ x in s, F x * H x) ^ 2) :=
    (Real.sqrt_sq_eq_abs _).symm
  rw [h1]
  calc Real.sqrt ((∫ x in s, F x * H x) ^ 2)
      ≤ Real.sqrt ((∫ x in s, F x ^ 2) * (∫ x in s, H x ^ 2)) := Real.sqrt_le_sqrt h
    _ = Real.sqrt (∫ x in s, F x ^ 2) * Real.sqrt (∫ x in s, H x ^ 2) := Real.sqrt_mul hFnn _

/-- `(x+y)² ≤ 2(x²+y²)`. -/
private lemma two_sq_le (x y : ℝ) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (x - y)]

/-- `(a+b+c+d)² ≤ 4(a²+b²+c²+d²)`. -/
private lemma four_sq_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  have h1 := two_sq_le (a + b) (c + d)
  have h2 := two_sq_le a b
  have h3 := two_sq_le c d
  nlinarith [h1, h2, h3]

/-- The integral of a constant over `Ioc a b`. -/
private lemma setIntegral_Ioc_const {a b c : ℝ} (hab : a ≤ b) :
    ∫ _ in Set.Ioc a b, c = c * (b - a) := by
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
    Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
  ring

/-- The integral of a constant over `Ioo a b`. -/
private lemma setIntegral_Ioo_const {a b c : ℝ} (hab : a ≤ b) :
    ∫ _ in Set.Ioo a b, c = c * (b - a) := by
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
    Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
  ring

/-- A pointwise bound on `Ioc a b` gives an integral bound. -/
private lemma setIntegral_Ioc_le_of_le {a b M : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn f (Set.Ioc a b))
    (hg : MeasureTheory.IntegrableOn (fun _ : ℝ => M) (Set.Ioc a b))
    (h : ∀ t ∈ Set.Ioc a b, f t ≤ M) :
    ∫ t in Set.Ioc a b, f t ≤ M * (b - a) := by
  have h1 := MeasureTheory.setIntegral_mono_on hf hg measurableSet_Ioc h
  rwa [setIntegral_Ioc_const hab] at h1

/-! ### Tail estimates -/

/-- Convert integrability from the open tail to the half-open tail. -/
private lemma integrableOn_Ioc_of_Ioo {f : ℝ → ℝ} {a b : ℝ}
    (h : MeasureTheory.IntegrableOn f (Set.Ioo a b)) : MeasureTheory.IntegrableOn f (Set.Ioc a b) := by
  rw [MeasureTheory.IntegrableOn,
    ← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Ioc (a := a) (b := b))]
  exact h

/-- The two tails have the same integral. -/
private lemma setIntegral_Ioc_eq_Ioo {f : ℝ → ℝ} {a b : ℝ} :
    (∫ t in Set.Ioc a b, f t) = ∫ t in Set.Ioo a b, f t := by
  rw [← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Ioc (a := a) (b := b))]

/-- `x ≤ x ^ (2 - γ)` for `x ∈ (0, 1]` and `1 ≤ γ`. -/
private lemma rpow_two_sub_ge_self {γ x : ℝ} (hγ1 : 1 ≤ γ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    x ≤ x ^ (2 - γ) := by
  have hsplit : x ^ (2 - γ) * x ^ (γ - 1) = x := by
    rw [← Real.rpow_add hx0, show 2 - γ + (γ - 1) = 1 by ring, Real.rpow_one]
  have hle : x ^ (γ - 1) ≤ 1 := Real.rpow_le_one hx0.le hx1 (by linarith)
  have hpos : 0 < x ^ (2 - γ) := Real.rpow_pos_of_pos hx0 _
  have h2 : x ^ (2 - γ) * x ^ (γ - 1) ≤ x ^ (2 - γ) * 1 :=
    mul_le_mul_of_nonneg_left hle hpos.le
  rw [mul_one] at h2
  linarith [hsplit, h2]

/-- `σ t ≥ 1/2` for `t ∈ [π/8, π/4]`. -/
private lemma sigma_ge_half {γ : ℝ} (hγ1 : 1 ≤ γ) {t : ℝ} (h0 : Real.pi / 8 ≤ t)
    (h2 : t ≤ Real.pi / 4) :
    (1 : ℝ) / 2 ≤ (Real.sin (2 * t)) ^ (2 - γ) := by
  have hsin : (1 : ℝ) / 2 ≤ Real.sin (2 * t) := by
    have h1 : 2 / Real.pi * (2 * t) ≤ Real.sin (2 * t) :=
      Real.mul_le_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have h2' : (1 : ℝ) / 2 ≤ 2 / Real.pi * (2 * t) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
      nlinarith [h0, Real.pi_pos]
    linarith
  have hsin1 : Real.sin (2 * t) ≤ 1 := Real.sin_le_one _
  exact le_trans hsin (rpow_two_sub_ge_self hγ1 (lt_of_lt_of_le (by norm_num) hsin) hsin1)

/-- AM–GM: `|g| cos² ≤ (g²σ)/2 + (cos⁴/σ)/2` when `σ > 0`. -/
private lemma abs_g_mul_cos_sq_le {γ : ℝ} {g : ℝ → ℝ} {t : ℝ}
    (hσ : 0 < Real.rpow (Real.sin (2 * t)) (2 - γ)) :
    |g t| * (Real.cos t) ^ 2
      ≤ (1 / 2) * ((g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
        + (1 / 2) * ((Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ)) := by
  set a : ℝ := Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t| with ha
  set b : ℝ := (Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) with hb
  have hs : Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hσ)
  have hsq : (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))) ^ 2 = Real.rpow (Real.sin (2 * t)) (2 - γ) :=
    Real.sq_sqrt hσ.le
  have hab : a * b = |g t| * (Real.cos t) ^ 2 := by
    rw [ha, hb]; field_simp
  have ha2 : a ^ 2 = (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ) := by
    rw [ha, mul_pow, hsq, sq_abs]; ring
  have hb2 : b ^ 2 = (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ) := by
    rw [hb, div_pow, hsq]; ring
  have h2ab : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  rw [hab, ha2, hb2] at h2ab
  linarith

/-- AM–GM: `cos³ |g'| ≤ ((g')²σ)/2 + (cos⁶/σ)/2` when `σ > 0`. -/
private lemma abs_g'_mul_cos_cu_le {γ : ℝ} {g : ℝ → ℝ} {t : ℝ}
    (hσ : 0 < Real.rpow (Real.sin (2 * t)) (2 - γ)) :
    (Real.cos t) ^ 3 * |deriv g t|
      ≤ (1 / 2) * ((deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
        + (1 / 2) * ((Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ)) := by
  set a : ℝ := Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |deriv g t| with ha
  set b : ℝ := (Real.cos t) ^ 3 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) with hb
  have hs : Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hσ)
  have hsq : (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))) ^ 2 = Real.rpow (Real.sin (2 * t)) (2 - γ) :=
    Real.sq_sqrt hσ.le
  have hab : a * b = (Real.cos t) ^ 3 * |deriv g t| := by
    rw [ha, hb]; field_simp
  have ha2 : a ^ 2 = (deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ) := by
    rw [ha, mul_pow, hsq, sq_abs]; ring
  have hb2 : b ^ 2 = (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ) := by
    rw [hb, div_pow, hsq]; ring
  have h2ab : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  rw [hab, ha2, hb2] at h2ab
  linarith

/-- `σ > 0` on `(0, π/2)`. -/
private lemma sigma_pos_of_mem {γ : ℝ} {t : ℝ} (h0 : 0 < t) (h2 : t < Real.pi / 2) :
    0 < (Real.sin (2 * t)) ^ (2 - γ) := by
  refine Real.rpow_pos_of_pos ?_ _
  rw [Real.sin_two_mul]
  exact mul_pos (mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])))
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩)

/-- `g` is a.e.-strongly measurable on `Ioo T T'` for `0 < T`, `T' ≤ π/2`. -/
private lemma ae_measurable_g {u g : ℝ → ℝ} (hcont : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    {T T' : ℝ} (hT : 0 < T) (hT' : T' ≤ Real.pi / 2) :
    MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict (Set.Ioo T T')) := by
  have hum : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume.restrict (Set.Ioo T T')) :=
    ContinuousOn.aestronglyMeasurable
      (hcont.mono (fun x hx => ⟨le_trans hT.le hx.1.le, le_trans hx.2.le hT'⟩)) measurableSet_Ioo
  have h1 : MeasureTheory.AEStronglyMeasurable (fun θ => deriv (deriv u) θ)
      (MeasureTheory.volume.restrict (Set.Ioo T T')) :=
    (measurable_deriv fun θ => deriv u θ).aestronglyMeasurable
  have h2 : MeasureTheory.AEStronglyMeasurable (fun θ => deriv (fun t => Real.tan t * u t) θ)
      (MeasureTheory.volume.restrict (Set.Ioo T T')) :=
    (measurable_deriv fun t => Real.tan t * u t).aestronglyMeasurable
  have h3 : MeasureTheory.AEStronglyMeasurable (fun θ => 6 * u θ)
      (MeasureTheory.volume.restrict (Set.Ioo T T')) := hum.const_mul 6
  have hL : MeasureTheory.AEStronglyMeasurable (Work.FTS.EllipticEst.Lzero1 u)
      (MeasureTheory.volume.restrict (Set.Ioo T T')) := by
    have h := (h1.neg.add h2).sub h3
    refine h.congr ?_
    filter_upwards with x
    simp only [Work.FTS.EllipticEst.Lzero1, Pi.neg_apply, Pi.add_apply, Pi.sub_apply]
  refine hL.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
  exact hg t ⟨lt_trans hT ht.1, lt_of_lt_of_le ht.2 hT'⟩

/-! ### Trigonometric and exponent helpers -/

/-- `(2/π)(π/2 - t) ≤ cos t` on `[0, π/2]`. -/
private lemma two_div_pi_mul_le_cos {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ Real.pi / 2) :
    (2 / Real.pi) * (Real.pi / 2 - t) ≤ Real.cos t := by
  rw [← Real.sin_pi_div_two_sub t]
  exact Real.mul_le_sin (by linarith) (by linarith [h0, Real.pi_pos])

/-- `cos t ≤ sin (2t)` on `[π/4, π/2]`. -/
private lemma cos_le_sin_two {t : ℝ} (h0 : Real.pi / 4 ≤ t) (h2 : t ≤ Real.pi / 2) :
    Real.cos t ≤ Real.sin (2 * t) := by
  have hcos0 : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h2⟩
  have hhalf : (1 : ℝ) / 2 ≤ Real.sin t := by
    have hmem1 : Real.pi / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hmem2 : t ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [Real.pi_pos], h2⟩
    have h := Real.strictMonoOn_sin.monotoneOn hmem1 hmem2 h0
    rw [Real.sin_pi_div_four] at h
    have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  calc Real.cos t ≤ 1 * Real.cos t := by rw [one_mul]
    _ ≤ (2 * Real.sin t) * Real.cos t := mul_le_mul_of_nonneg_right (by linarith) hcos0
    _ = Real.sin (2 * t) := by rw [Real.sin_two_mul]

/-! ### Exponent arithmetic for `Real.rpow` -/

private lemma rpow_add_one_mul (x : ℝ) (hx : 0 < x) (n : ℝ) : x ^ n * x = x ^ (n + 1) := by
  have h := Real.rpow_add hx n 1
  rw [Real.rpow_one] at h
  exact h.symm

private lemma mul_rpow_one (x : ℝ) (hx : 0 < x) (n : ℝ) : x * x ^ n = x ^ (1 + n) := by
  have h := Real.rpow_add hx 1 n
  rw [Real.rpow_one] at h
  exact h.symm

private lemma rpow_three_mul (x : ℝ) (hx : 0 < x) : x ^ (3 : ℝ) * x = x ^ (4 : ℝ) := by
  have h := rpow_add_one_mul x hx 3
  rw [show (3 : ℝ) + 1 = (4 : ℝ) by norm_num] at h
  exact h

private lemma rpow_five_mul (x : ℝ) (hx : 0 < x) : x ^ (5 : ℝ) * x = x ^ (6 : ℝ) := by
  have h := rpow_add_one_mul x hx 5
  rw [show (5 : ℝ) + 1 = (6 : ℝ) by norm_num] at h
  exact h

private lemma mul_rpow_four (x : ℝ) (hx : 0 < x) : x * x ^ (4 : ℝ) = x ^ (5 : ℝ) := by
  have h := mul_rpow_one x hx 4
  rw [show (1 : ℝ) + 4 = (5 : ℝ) by norm_num] at h
  exact h

private lemma mul_rpow_gamma {γ x : ℝ} (hx : 0 < x) :
    x * x ^ ((3 + γ) / 2) = x ^ ((5 + γ) / 2) := by
  have h := mul_rpow_one x hx ((3 + γ) / 2)
  rw [show (1 : ℝ) + (3 + γ) / 2 = (5 + γ) / 2 by ring] at h
  exact h

private lemma rpow_half_gamma_mul {γ x : ℝ} (hx : 0 < x) :
    x ^ ((5 + γ) / 2) * x = x ^ ((7 + γ) / 2) := by
  have h := rpow_add_one_mul x hx ((5 + γ) / 2)
  rw [show (5 + γ) / 2 + 1 = (7 + γ) / 2 by ring] at h
  exact h

private lemma rpow_nat_three (x : ℝ) : x ^ (3 : ℝ) = x ^ (3 : ℕ) := by
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num]
  exact Real.rpow_natCast x 3

private lemma rpow_nat_four (x : ℝ) : x ^ (4 : ℝ) = x ^ (4 : ℕ) := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num]
  exact Real.rpow_natCast x 4

private lemma cos_times_Psi1_bound {Kq GG Cw γ x : ℝ} (hx : 0 < x) :
    x * (4 * Kq * x ^ (4 : ℝ) + Real.sqrt (Cw * GG) * x ^ ((3 + γ) / 2))
      = 4 * Kq * x ^ (5 : ℝ) + Real.sqrt (Cw * GG) * x ^ ((5 + γ) / 2) := by
  rw [mul_add]
  congr 1
  · rw [show x * (4 * Kq * x ^ (4 : ℝ)) = 4 * Kq * (x * x ^ (4 : ℝ)) by ring,
      mul_rpow_four x hx]
  · rw [show x * (Real.sqrt (Cw * GG) * x ^ ((3 + γ) / 2))
        = Real.sqrt (Cw * GG) * (x * x ^ ((3 + γ) / 2)) by ring,
      mul_rpow_gamma (γ := γ) hx]

/-- `cos t ^ n / σ ≤ 2` on `[π/8, π/2)` for `n ≥ 2`, where `σ = sin(2t)^{2-γ}`, `γ ≥ 1`. -/
private lemma cos_pow_div_sigma_le_two {γ : ℝ} (hγ1 : 1 ≤ γ) {t : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (h0 : Real.pi / 8 ≤ t) (h2 : t < Real.pi / 2) :
    (Real.cos t) ^ n / Real.rpow (Real.sin (2 * t)) (2 - γ) ≤ 2 := by
  have ht0 : 0 < t := by linarith [h0, Real.pi_pos]
  have hcospos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩
  have hσpos : 0 < Real.rpow (Real.sin (2 * t)) (2 - γ) := sigma_pos_of_mem ht0 h2
  rcases le_or_gt t (Real.pi / 4) with hle | hgt
  · have hσhalf : (1 : ℝ) / 2 ≤ Real.rpow (Real.sin (2 * t)) (2 - γ) :=
      sigma_ge_half hγ1 h0 hle
    have hn1 : (Real.cos t) ^ n ≤ 1 := pow_le_one₀ hcospos.le (Real.cos_le_one t)
    rw [div_le_iff₀ hσpos]
    linarith
  · have hsin1 : Real.sin (2 * t) ≤ 1 := Real.sin_le_one _
    have hsin0 : 0 ≤ Real.sin (2 * t) := sin_two_nonneg (le_of_lt ht0) (le_of_lt h2)
    have hcossin : Real.cos t ≤ Real.sin (2 * t) := cos_le_sin_two (le_of_lt hgt) (le_of_lt h2)
    have hsinpos : 0 < Real.sin (2 * t) := lt_of_lt_of_le hcospos hcossin
    have hnum : (Real.cos t) ^ n ≤ (Real.sin (2 * t)) ^ n :=
      pow_le_pow_left₀ hcospos.le hcossin n
    have hstep := div_le_div_of_nonneg_right hnum hσpos.le
    have hpow : (Real.sin (2 * t)) ^ n / Real.rpow (Real.sin (2 * t)) (2 - γ)
        = Real.rpow (Real.sin (2 * t)) ((n : ℝ) - (2 - γ)) := by
      have hden : Real.rpow (Real.sin (2 * t)) (2 - γ) = (Real.sin (2 * t)) ^ (2 - γ) := rfl
      have hden2 : Real.rpow (Real.sin (2 * t)) ((n : ℝ) - (2 - γ))
          = (Real.sin (2 * t)) ^ ((n : ℝ) - (2 - γ)) := rfl
      rw [hden, hden2, ← Real.rpow_natCast (Real.sin (2 * t)) n, ← Real.rpow_sub hsinpos]
    rw [hpow] at hstep
    have hone : Real.rpow (Real.sin (2 * t)) ((n : ℝ) - (2 - γ)) ≤ 1 :=
      Real.rpow_le_one hsin0 hsin1 (by
        have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith)
    linarith

/-- `(cos t)^4 / σ t ≤ 2` on `(π/8, π/2)`. -/
private lemma cos4_div_sigma_le_two {γ : ℝ} (hγ1 : 1 ≤ γ) {t : ℝ}
    (h0 : Real.pi / 8 ≤ t) (h2 : t < Real.pi / 2) :
    (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ) ≤ 2 :=
  cos_pow_div_sigma_le_two hγ1 (by norm_num) h0 h2

/-- `(cos t)^6 / σ t ≤ 2` on `(π/8, π/2)`. -/
private lemma cos6_div_sigma_le_two {γ : ℝ} (hγ1 : 1 ≤ γ) {t : ℝ}
    (h0 : Real.pi / 8 ≤ t) (h2 : t < Real.pi / 2) :
    (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ) ≤ 2 :=
  cos_pow_div_sigma_le_two hγ1 (by norm_num) h0 h2

/-- `|f|` is a.e.-strongly measurable whenever `f` is. -/
private lemma aestronglyMeasurable_abs_real {f : ℝ → ℝ} {μ : MeasureTheory.Measure ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f μ) :
    MeasureTheory.AEStronglyMeasurable (fun x => |f x|) μ := by
  simpa only [Real.norm_eq_abs] using hf.norm

/-- `v = u / cos θ` is a.e.-strongly measurable on any measurable subset of the open slice. -/
private lemma aesm_div_cos {u : ℝ → ℝ} {s : Set ℝ}
    (hcont : ContinuousOn u (Set.Icc 0 (Real.pi / 2))) (hsm : MeasurableSet s)
    (hs : s ⊆ Set.Ioo 0 (Real.pi / 2)) :
    MeasureTheory.AEStronglyMeasurable (fun t => u t / Real.cos t)
      (MeasureTheory.volume.restrict s) :=
  (ContinuousOn.div (hcont.mono (fun x hx => ⟨(hs hx).1.le, (hs hx).2.le⟩))
    Real.continuous_cos.continuousOn (fun x hx => cos_ne_of_mem_Ioo (hs hx))).aestronglyMeasurable hsm

/-! ### Integrability of the `g`-tails on `(π/8, π/2)` -/

/-- `|g| cos²` is integrable on `(π/8, π/2)` when `g²σ` is. -/
private lemma integrable_abs_g_cos_sq {γ : ℝ} (hγ1 : 1 ≤ γ) {g : ℝ → ℝ}
    (hm : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 8) (Real.pi / 2))))
    (hG : MeasureTheory.IntegrableOn
      (fun t => (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
      (Set.Ioo (Real.pi / 8) (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun t => |g t| * (Real.cos t) ^ 2)
      (Set.Ioo (Real.pi / 8) (Real.pi / 2)) := by
  have hfin : MeasureTheory.volume (Set.Ioo (Real.pi / 8) (Real.pi / 2)) ≠ ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hdom : MeasureTheory.IntegrableOn
      (fun t => (1 / 2) * ((g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)) + 1)
      (Set.Ioo (Real.pi / 8) (Real.pi / 2)) :=
    (hG.const_mul (1 / 2)).add (MeasureTheory.integrableOn_const (C := (1 : ℝ)) hfin)
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · exact (aestronglyMeasurable_abs_real hm).mul
      ((Real.continuous_cos.pow 2).aestronglyMeasurable)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    have hσ : 0 < Real.rpow (Real.sin (2 * t)) (2 - γ) :=
      sigma_pos_of_mem (by linarith [ht.1, Real.pi_pos]) ht.2
    have h1 := abs_g_mul_cos_sq_le (γ := γ) (g := g) (t := t) hσ
    have h2 : (1 / 2) * ((Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ)) ≤ 1 := by
      have h := cos4_div_sigma_le_two hγ1 (le_of_lt ht.1) ht.2
      linarith
    have hnn : 0 ≤ |g t| * (Real.cos t) ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    linarith

/-- `cos³ |g'|` is integrable on `(π/8, π/2)` when `(g')²σ` is. -/
private lemma integrable_cos3_abs_gprime {γ : ℝ} (hγ1 : 1 ≤ γ) {g : ℝ → ℝ}
    (hm : MeasureTheory.AEStronglyMeasurable (deriv g)
      (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 8) (Real.pi / 2))))
    (hG : MeasureTheory.IntegrableOn
      (fun t => (deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
      (Set.Ioo (Real.pi / 8) (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun t => (Real.cos t) ^ 3 * |deriv g t|)
      (Set.Ioo (Real.pi / 8) (Real.pi / 2)) := by
  have hfin : MeasureTheory.volume (Set.Ioo (Real.pi / 8) (Real.pi / 2)) ≠ ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hdom : MeasureTheory.IntegrableOn
      (fun t => (1 / 2) * ((deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)) + 1)
      (Set.Ioo (Real.pi / 8) (Real.pi / 2)) :=
    (hG.const_mul (1 / 2)).add (MeasureTheory.integrableOn_const (C := (1 : ℝ)) hfin)
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · exact ((Real.continuous_cos.pow 3).aestronglyMeasurable).mul
      (aestronglyMeasurable_abs_real hm)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    have hσ : 0 < Real.rpow (Real.sin (2 * t)) (2 - γ) :=
      sigma_pos_of_mem (by linarith [ht.1, Real.pi_pos]) ht.2
    have h1 := abs_g'_mul_cos_cu_le (γ := γ) (g := g) (t := t) hσ
    have h2 : (1 / 2) * ((Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ)) ≤ 1 := by
      have h := cos6_div_sigma_le_two hγ1 (le_of_lt ht.1) ht.2
      linarith
    have hc0 : 0 ≤ Real.cos t :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2.le⟩
    have hnn : 0 ≤ (Real.cos t) ^ 3 * |deriv g t| :=
      mul_nonneg (pow_nonneg hc0 3) (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    linarith

/-! ### The `u`-part of the tail -/

/-- The elementary pointwise bound `|u t| cos²t ≤ Kq (π/2-t)³` for `t ∈ Iθ`. -/
private lemma abs_u_cos_sq_le {Kq : ℝ} (hKq : 0 ≤ Kq) {u : ℝ → ℝ}
    (hub : ∀ η ∈ Work.Spaces.Iθ, |u η| ≤ (Real.pi / 2 - η) * Kq) :
    ∀ t ∈ Work.Spaces.Iθ, |u t| * (Real.cos t) ^ 2 ≤ Kq * (Real.pi / 2 - t) ^ (3 : ℝ) := by
  intro t ht
  have h1 := hub t ht
  have hcos : Real.cos t ≤ Real.pi / 2 - t := cos_le_pi_div_two_sub ht.1 ht.2
  have hcos0 : 0 ≤ Real.cos t :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  calc |u t| * (Real.cos t) ^ 2 ≤ ((Real.pi / 2 - t) * Kq) * (Real.pi / 2 - t) ^ 2 :=
        mul_le_mul h1 (pow_le_pow_left₀ hcos0 hcos 2) (sq_nonneg _)
          (mul_nonneg (by linarith [ht.2, Real.pi_pos]) hKq)
    _ = Kq * (Real.pi / 2 - t) ^ (3 : ℝ) := by
        rw [show ((Real.pi / 2 - t) * Kq) * (Real.pi / 2 - t) ^ 2
            = Kq * (Real.pi / 2 - t) ^ (3 : ℕ) by ring,
          show (Real.pi / 2 - t) ^ (3 : ℕ) = (Real.pi / 2 - t) ^ (3 : ℝ) from
            (Real.rpow_natCast (Real.pi / 2 - t) 3).symm]

/-- The value bound for the `u`-part of the tail. -/
private lemma tail_u_cos_sq_le {Kq ν : ℝ} (hKq : 0 ≤ Kq)
    (hν0 : Real.pi / 8 ≤ ν) (hν1 : ν < Real.pi / 2) {u : ℝ → ℝ}
    (hub : ∀ η ∈ Work.Spaces.Iθ, |u η| ≤ (Real.pi / 2 - η) * Kq) :
    (∫ t in Set.Ioc ν (Real.pi / 2), |u t| * (Real.cos t) ^ 2)
      ≤ Kq * (Real.pi / 2 - ν) ^ (4 : ℝ) := by
  have hεpos : 0 < Real.pi / 2 - ν := by linarith [hν1]
  have hbdd : ∀ t ∈ Set.Ioc ν (Real.pi / 2),
      |u t| * (Real.cos t) ^ 2 ≤ Kq * (Real.pi / 2 - ν) ^ (3 : ℝ) := by
    intro t ht
    have ht0 : 0 < t := lt_trans (by linarith [hν0, Real.pi_pos]) ht.1
    have h1 := abs_u_cos_sq_le hKq hub t ⟨ht0.le, ht.2⟩
    have hδ0 : 0 ≤ Real.pi / 2 - t := by linarith [ht.2]
    have hδ : Real.pi / 2 - t ≤ Real.pi / 2 - ν := by linarith [ht.1]
    calc |u t| * (Real.cos t) ^ 2 ≤ Kq * (Real.pi / 2 - t) ^ (3 : ℝ) := h1
      _ ≤ Kq * (Real.pi / 2 - ν) ^ (3 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ0 hδ (by norm_num)) hKq
  have hconst : MeasureTheory.IntegrableOn
      (fun _ : ℝ => Kq * (Real.pi / 2 - ν) ^ (3 : ℝ)) (Set.Ioc ν (Real.pi / 2)) :=
    MeasureTheory.integrableOn_const (C := Kq * (Real.pi / 2 - ν) ^ (3 : ℝ)) (by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top)
  have hmono : (∫ t in Set.Ioc ν (Real.pi / 2), |u t| * (Real.cos t) ^ 2)
      ≤ ∫ t in Set.Ioc ν (Real.pi / 2), Kq * (Real.pi / 2 - ν) ^ (3 : ℝ) :=
    MeasureTheory.integral_mono_of_nonneg
      (f := fun t => |u t| * (Real.cos t) ^ 2)
      (g := fun _ : ℝ => Kq * (Real.pi / 2 - ν) ^ (3 : ℝ))
      (Filter.Eventually.of_forall fun t => by positivity) hconst
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        exact hbdd t ht)
  rw [setIntegral_Ioc_const (by linarith : ν ≤ Real.pi / 2)] at hmono
  have hconv : Kq * (Real.pi / 2 - ν) ^ (3 : ℝ) * (Real.pi / 2 - ν)
      = Kq * (Real.pi / 2 - ν) ^ (4 : ℝ) := by
    rw [mul_assoc Kq ((Real.pi / 2 - ν) ^ (3 : ℝ)) (Real.pi / 2 - ν),
      rpow_three_mul (Real.pi / 2 - ν) hεpos]
  rw [hconv] at hmono
  exact hmono

/-- The pointwise domination of `abs (-(4u+g)cos²)` by a constant plus `|g|cos²`. -/
private lemma abs_q_le {Kq δ t : ℝ} (hKq : 0 ≤ Kq) (hδt : δ ≤ t) (ht0 : 0 < t)
    (ht2 : t ≤ Real.pi / 2) {u g : ℝ → ℝ}
    (hub : ∀ η ∈ Work.Spaces.Iθ, |u η| ≤ (Real.pi / 2 - η) * Kq) :
    |-(4 * u t + g t) * (Real.cos t) ^ 2|
      ≤ 4 * (Kq * (Real.pi / 2 - δ) ^ (3 : ℝ)) + |g t| * (Real.cos t) ^ 2 := by
  have htI : t ∈ Work.Spaces.Iθ := ⟨ht0.le, ht2⟩
  have hcos0 : 0 ≤ Real.cos t :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], ht2⟩
  have h1 : |u t| * (Real.cos t) ^ 2 ≤ Kq * (Real.pi / 2 - t) ^ (3 : ℝ) :=
    abs_u_cos_sq_le hKq hub t htI
  have hδ0 : 0 ≤ Real.pi / 2 - t := by linarith [ht2]
  have hδν : Real.pi / 2 - t ≤ Real.pi / 2 - δ := by linarith [hδt]
  have h2 : Kq * (Real.pi / 2 - t) ^ (3 : ℝ) ≤ Kq * (Real.pi / 2 - δ) ^ (3 : ℝ) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ0 hδν (by norm_num)) hKq
  have h3 : |-(4 * u t + g t) * (Real.cos t) ^ 2|
      = |4 * u t + g t| * (Real.cos t) ^ 2 := by
    rw [abs_mul, abs_neg, abs_of_nonneg (pow_nonneg hcos0 2)]
  have h4 : |4 * u t + g t| ≤ 4 * |u t| + |g t| := by
    calc |4 * u t + g t| ≤ |4 * u t| + |g t| := abs_add_le _ _
      _ = 4 * |u t| + |g t| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  have h5 : (4 * |u t| + |g t|) * (Real.cos t) ^ 2
      = 4 * (|u t| * (Real.cos t) ^ 2) + |g t| * (Real.cos t) ^ 2 := by ring
  have h6 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 4)
  calc |-(4 * u t + g t) * (Real.cos t) ^ 2|
      = |4 * u t + g t| * (Real.cos t) ^ 2 := h3
    _ ≤ (4 * |u t| + |g t|) * (Real.cos t) ^ 2 :=
        mul_le_mul_of_nonneg_right h4 (pow_nonneg hcos0 2)
    _ = 4 * (|u t| * (Real.cos t) ^ 2) + |g t| * (Real.cos t) ^ 2 := h5
    _ ≤ 4 * (Kq * (Real.pi / 2 - δ) ^ (3 : ℝ)) + |g t| * (Real.cos t) ^ 2 := by
        linarith [h6, h2]

/-! ### The two tail bounds for `Ψ₁ = cos³θ·v'` and `Ψ₂ = cos⁴θ·v''` -/

/-! ### The weight bounds used by the final estimate

`σ θ = sin(2θ)^{2-γ}` is comparable to `cos θ^{2-γ}` on `[π/4, π/2)`, so `σ/cos^k` grows at
most like `ε^{-(k-2+γ)}` (`ε = π/2 - θ`) and `∫_θ^{π/2} cos^k/σ ≤ ε^{k-1+γ}`; the positive powers
`ε^{3-γ}`, `ε^{5-γ}` are bounded.  These are exactly the bounds consumed by the two tail
estimates above and by the final arithmetic. -/

/-- `(2/π)^{-a} = (π/2)^{a}`. -/
private lemma two_div_pi_rpow_neg (a : ℝ) : (2 / Real.pi) ^ (-a) = (Real.pi / 2) ^ a := by
  have hπ : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have h : (2 : ℝ) / Real.pi = (Real.pi / 2)⁻¹ := by rw [inv_div]
  rw [h, Real.inv_rpow hπ.le, Real.rpow_neg hπ.le a, inv_inv]

/-- **Weight bounds on the right half of the slice.** -/
private lemma weights_local (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
      (2 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.cos θ
      ∧ Real.cos θ ≤ Real.pi / 2 - θ
      ∧ (Real.sin (2 * θ)) ^ (2 - γ) / (Real.cos θ) ^ 5
          ≤ C * (Real.pi / 2 - θ) ^ (-(3 + γ))
      ∧ (Real.sin (2 * θ)) ^ (2 - γ) / (Real.cos θ) ^ 7
          ≤ C * (Real.pi / 2 - θ) ^ (-(5 + γ))
      ∧ (Real.pi / 2 - θ) ^ (3 - γ) ≤ C
      ∧ (Real.pi / 2 - θ) ^ (5 - γ) ≤ C
      ∧ (∫ t in θ..(Real.pi / 2), (Real.cos t) ^ 4 / (Real.sin (2 * t)) ^ (2 - γ)
            ≤ C * (Real.pi / 2 - θ) ^ (3 + γ))
      ∧ (∫ t in θ..(Real.pi / 2), (Real.cos t) ^ 6 / (Real.sin (2 * t)) ^ (2 - γ)
            ≤ C * (Real.pi / 2 - θ) ^ (5 + γ)) := by
  have hπ2 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hπ4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hCnonneg : (0 : ℝ) ≤ 4 * (Real.pi / 2) ^ (3 + γ) + 4 * (Real.pi / 2) ^ (5 + γ) := by
    have h1 : 0 ≤ (Real.pi / 2) ^ (3 + γ) := Real.rpow_nonneg hπ2.le _
    have h2 : 0 ≤ (Real.pi / 2) ^ (5 + γ) := Real.rpow_nonneg hπ2.le _
    linarith
  refine ⟨4 * (Real.pi / 2) ^ (3 + γ) + 4 * (Real.pi / 2) ^ (5 + γ) + 1,
    by linarith [hCnonneg], ?_⟩
  intro θ hθ
  have hθ0 : 0 ≤ θ := by linarith [hθ.1, Real.pi_pos]
  have hθlt : θ < Real.pi / 2 := hθ.2
  have hεpos : 0 < Real.pi / 2 - θ := by linarith
  have hcospos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθlt⟩
  have hcosnn : 0 ≤ Real.cos θ := hcospos.le
  have hsinθ : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos])
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hεle : Real.pi / 2 - θ ≤ Real.pi / 4 := by linarith [hθ.1]
  have hε1 : Real.pi / 2 - θ ≤ 1 := by linarith [hεle, Real.pi_lt_four]
  have hC1 : 1 ≤ 4 * (Real.pi / 2) ^ (3 + γ) + 4 * (Real.pi / 2) ^ (5 + γ) + 1 := by
    linarith
  -- (1), (2): `cos θ` squeezed by `(2/π)ε` and `ε`
  have hcosge : (2 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.cos θ :=
    two_div_pi_mul_le_cos hθ0 hθlt.le
  have hcosle : Real.cos θ ≤ Real.pi / 2 - θ := cos_le_pi_div_two_sub hθ0 hθlt.le
  -- `σ θ ≤ 4 cos θ^{2-γ}`
  have hσle : (Real.sin (2 * θ)) ^ (2 - γ) ≤ 4 * (Real.cos θ) ^ (2 - γ) := by
    have h1 : (Real.sin (2 * θ)) ^ (2 - γ) ≤ (2 * Real.cos θ) ^ (2 - γ) := by
      refine Real.rpow_le_rpow (sin_two_nonneg hθ0 hθlt.le) ?_ (by linarith)
      rw [Real.sin_two_mul]
      nlinarith [hsin1, hcosnn]
    have h2 : (2 * Real.cos θ) ^ (2 - γ) = (2 : ℝ) ^ (2 - γ) * (Real.cos θ) ^ (2 - γ) :=
      Real.mul_rpow (by norm_num) hcosnn
    have h3 : (2 : ℝ) ^ (2 - γ) ≤ 4 := by
      have h4 : (2 : ℝ) ^ (2 - γ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith : 2 - γ ≤ 2)
      have h5 : (2 : ℝ) ^ (2 : ℝ) = 4 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        norm_num
      linarith
    calc (Real.sin (2 * θ)) ^ (2 - γ) ≤ (2 * Real.cos θ) ^ (2 - γ) := h1
      _ = (2 : ℝ) ^ (2 - γ) * (Real.cos θ) ^ (2 - γ) := h2
      _ ≤ 4 * (Real.cos θ) ^ (2 - γ) :=
          mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hcosnn _)
  -- (3), (4): `σ/cos^k`
  have hcos_k : ∀ k : ℕ, 2 ≤ k → (Real.sin (2 * θ)) ^ (2 - γ) / (Real.cos θ) ^ k
      ≤ 4 * (Real.pi / 2) ^ ((k : ℝ) - 2 + γ) * (Real.pi / 2 - θ) ^ (-((k : ℝ) - 2 + γ)) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    have h1 : (Real.sin (2 * θ)) ^ (2 - γ) / (Real.cos θ) ^ k
        ≤ 4 * (Real.cos θ) ^ (2 - γ) / (Real.cos θ) ^ k :=
      div_le_div_of_nonneg_right hσle (pow_nonneg hcosnn k)
    have h2 : 4 * (Real.cos θ) ^ (2 - γ) / (Real.cos θ) ^ k
        = 4 * (Real.cos θ) ^ ((2 - γ) - k) := by
      rw [show (4 : ℝ) * (Real.cos θ) ^ (2 - γ) / (Real.cos θ) ^ k
          = 4 * ((Real.cos θ) ^ (2 - γ) / (Real.cos θ) ^ k) by ring,
        ← Real.rpow_natCast (Real.cos θ) k, ← Real.rpow_sub hcospos]
    have h3 : (Real.cos θ) ^ ((2 - γ) - k)
        ≤ ((2 / Real.pi) * (Real.pi / 2 - θ)) ^ ((2 - γ) - k) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hcosge (by linarith [hγ1, hk1])
    have h4 : ((2 / Real.pi) * (Real.pi / 2 - θ)) ^ ((2 - γ) - k)
        = (Real.pi / 2) ^ ((k : ℝ) - 2 + γ) * (Real.pi / 2 - θ) ^ (-((k : ℝ) - 2 + γ)) := by
      rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 / Real.pi) hεpos.le,
        show (2 - γ - (k : ℝ)) = -((k : ℝ) - 2 + γ) by ring,
        two_div_pi_rpow_neg ((k : ℝ) - 2 + γ)]
    calc (Real.sin (2 * θ)) ^ (2 - γ) / (Real.cos θ) ^ k
        ≤ 4 * (Real.cos θ) ^ (2 - γ) / (Real.cos θ) ^ k := h1
      _ = 4 * (Real.cos θ) ^ ((2 - γ) - k) := h2
      _ ≤ 4 * ((2 / Real.pi) * (Real.pi / 2 - θ)) ^ ((2 - γ) - k) :=
          mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = 4 * ((Real.pi / 2) ^ ((k : ℝ) - 2 + γ)
            * (Real.pi / 2 - θ) ^ (-((k : ℝ) - 2 + γ))) := by rw [h4]
      _ = 4 * (Real.pi / 2) ^ ((k : ℝ) - 2 + γ)
            * (Real.pi / 2 - θ) ^ (-((k : ℝ) - 2 + γ)) := by ring
  have hσ5 : (Real.sin (2 * θ)) ^ (2 - γ) / (Real.cos θ) ^ 5
      ≤ (4 * (Real.pi / 2) ^ (3 + γ) + 4 * (Real.pi / 2) ^ (5 + γ) + 1)
        * (Real.pi / 2 - θ) ^ (-(3 + γ)) := by
    have h := hcos_k 5 (by norm_num)
    have h5 : ((5 : ℕ) : ℝ) - 2 + γ = 3 + γ := by ring
    rw [h5] at h
    have hA : 0 ≤ (Real.pi / 2) ^ (5 + γ) := Real.rpow_nonneg hπ2.le _
    have hB : 0 ≤ (Real.pi / 2) ^ (3 + γ) := Real.rpow_nonneg hπ2.le _
    have hle : 4 * (Real.pi / 2) ^ (3 + γ)
        ≤ 4 * (Real.pi / 2) ^ (3 + γ) + 4 * (Real.pi / 2) ^ (5 + γ) + 1 := by linarith
    exact le_trans h (mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hεpos.le _))
  have hσ7 : (Real.sin (2 * θ)) ^ (2 - γ) / (Real.cos θ) ^ 7
      ≤ (4 * (Real.pi / 2) ^ (3 + γ) + 4 * (Real.pi / 2) ^ (5 + γ) + 1)
        * (Real.pi / 2 - θ) ^ (-(5 + γ)) := by
    have h := hcos_k 7 (by norm_num)
    have h7 : ((7 : ℕ) : ℝ) - 2 + γ = 5 + γ := by ring
    rw [h7] at h
    have hA : 0 ≤ (Real.pi / 2) ^ (5 + γ) := Real.rpow_nonneg hπ2.le _
    have hB : 0 ≤ (Real.pi / 2) ^ (3 + γ) := Real.rpow_nonneg hπ2.le _
    have hle : 4 * (Real.pi / 2) ^ (5 + γ)
        ≤ 4 * (Real.pi / 2) ^ (3 + γ) + 4 * (Real.pi / 2) ^ (5 + γ) + 1 := by linarith
    exact le_trans h (mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hεpos.le _))
  -- (5), (6): the positive powers of `ε` are bounded
  have hε3 : (Real.pi / 2 - θ) ^ (3 - γ) ≤ 4 * (Real.pi / 2) ^ (3 + γ)
      + 4 * (Real.pi / 2) ^ (5 + γ) + 1 :=
    le_trans (Real.rpow_le_one hεpos.le hε1 (by linarith)) hC1
  have hε5 : (Real.pi / 2 - θ) ^ (5 - γ) ≤ 4 * (Real.pi / 2) ^ (3 + γ)
      + 4 * (Real.pi / 2) ^ (5 + γ) + 1 :=
    le_trans (Real.rpow_le_one hεpos.le hε1 (by linarith)) hC1
  -- pointwise bound on the tail: `cos^k t / σ t ≤ ε^{k-2+γ}` for `t ∈ (θ, π/2]`
  have hpt : ∀ t ∈ Set.Ioc θ (Real.pi / 2), ∀ k : ℕ, 2 ≤ k →
      (Real.cos t) ^ k / (Real.sin (2 * t)) ^ (2 - γ)
        ≤ (Real.pi / 2 - θ) ^ ((k : ℝ) - 2 + γ) := by
    intro t ht k hk
    have ht0 : 0 ≤ t := by linarith [hθ.1, ht.1, Real.pi_pos]
    have htlt : t ≤ Real.pi / 2 := ht.2
    have hcost : Real.cos t ≤ Real.pi / 2 - t := cos_le_pi_div_two_sub ht0 htlt
    have hcosnn' : 0 ≤ Real.cos t :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, ht.1, Real.pi_pos], htlt⟩
    have hnum : (Real.cos t) ^ k ≤ (Real.pi / 2 - t) ^ k :=
      pow_le_pow_left₀ hcosnn' hcost k
    rcases lt_or_eq_of_le htlt with hlt | heq
    · have hεtpos : 0 < Real.pi / 2 - t := by linarith
      have hσpos : 0 < (Real.sin (2 * t)) ^ (2 - γ) :=
        sigma_pos_of_mem (by linarith [ht.1, hθ.1, Real.pi_pos]) hlt
      have hsin : 4 * (Real.pi / 2 - t) / Real.pi ≤ Real.sin (2 * t) := by
        have h2 := Real.mul_le_sin (show (0 : ℝ) ≤ 2 * (Real.pi / 2 - t) by linarith)
          (show 2 * (Real.pi / 2 - t) ≤ Real.pi / 2 by linarith [hθ.1, ht.1])
        have h3 : Real.sin (2 * t) = Real.sin (2 * (Real.pi / 2 - t)) := by
          rw [show 2 * (Real.pi / 2 - t) = Real.pi - 2 * t by ring, Real.sin_pi_sub]
        rw [h3]
        calc 4 * (Real.pi / 2 - t) / Real.pi = 2 / Real.pi * (2 * (Real.pi / 2 - t)) := by ring
          _ ≤ Real.sin (2 * (Real.pi / 2 - t)) := h2
      have hσge : (4 * (Real.pi / 2 - t) / Real.pi) ^ (2 - γ)
          ≤ (Real.sin (2 * t)) ^ (2 - γ) :=
        Real.rpow_le_rpow (by positivity) hsin (by linarith)
      have hDmul : (4 * (Real.pi / 2 - t) / Real.pi) ^ (2 - γ)
          = (4 / Real.pi) ^ (2 - γ) * (Real.pi / 2 - t) ^ (2 - γ) := by
        rw [show 4 * (Real.pi / 2 - t) / Real.pi = (4 / Real.pi) * (Real.pi / 2 - t) by ring,
          Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 / Real.pi) hεtpos.le]
      have hD1 : (1 : ℝ) ≤ (4 / Real.pi) ^ (2 - γ) := by
        refine Real.one_le_rpow ?_ ?_
        · rw [le_div_iff₀ Real.pi_pos]
          linarith [Real.pi_lt_four]
        · linarith
      have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hεtle : (Real.pi / 2 - t) ^ ((k : ℝ) - 2 + γ)
          ≤ (Real.pi / 2 - θ) ^ ((k : ℝ) - 2 + γ) :=
        Real.rpow_le_rpow hεtpos.le (by linarith [ht.1]) (by linarith [hγ1, hk2])
      have hpk : (Real.pi / 2 - t) ^ ((k : ℝ) - 2 + γ)
            * (Real.pi / 2 - t) ^ (2 - γ) = (Real.pi / 2 - t) ^ k := by
        rw [← Real.rpow_add hεtpos]
        have hexp : ((k : ℝ) - 2 + γ) + (2 - γ) = (k : ℝ) := by ring
        rw [hexp]
        exact Real.rpow_natCast (Real.pi / 2 - t) k
      have hA : (Real.pi / 2 - t) ^ k
          ≤ (Real.pi / 2 - θ) ^ ((k : ℝ) - 2 + γ) * (Real.sin (2 * t)) ^ (2 - γ) := by
        have hstep1 : (Real.pi / 2 - t) ^ k
            ≤ (Real.pi / 2 - θ) ^ ((k : ℝ) - 2 + γ) * (Real.pi / 2 - t) ^ (2 - γ) := by
          rw [← hpk]
          exact mul_le_mul_of_nonneg_right hεtle (Real.rpow_nonneg hεtpos.le _)
        have hstep2 : (Real.pi / 2 - θ) ^ ((k : ℝ) - 2 + γ) * (Real.pi / 2 - t) ^ (2 - γ)
            ≤ (Real.pi / 2 - θ) ^ ((k : ℝ) - 2 + γ) * (4 / Real.pi) ^ (2 - γ)
              * (Real.pi / 2 - t) ^ (2 - γ) := by
          have h : (1 : ℝ) * (Real.pi / 2 - t) ^ (2 - γ)
              ≤ (4 / Real.pi) ^ (2 - γ) * (Real.pi / 2 - t) ^ (2 - γ) :=
            mul_le_mul_of_nonneg_right hD1 (Real.rpow_nonneg hεtpos.le (2 - γ))
          calc (Real.pi / 2 - θ) ^ ((k : ℝ) - 2 + γ) * (Real.pi / 2 - t) ^ (2 - γ)
              = (Real.pi / 2 - θ) ^ ((k : ℝ) - 2 + γ)
                  * (1 * (Real.pi / 2 - t) ^ (2 - γ)) := by ring
            _ ≤ (Real.pi / 2 - θ) ^ ((k : ℝ) - 2 + γ)
                  * ((4 / Real.pi) ^ (2 - γ) * (Real.pi / 2 - t) ^ (2 - γ)) :=
                mul_le_mul_of_nonneg_left h
                  (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Real.pi / 2 - θ) _)
            _ = (Real.pi / 2 - θ) ^ ((k : ℝ) - 2 + γ) * (4 / Real.pi) ^ (2 - γ)
                  * (Real.pi / 2 - t) ^ (2 - γ) := by ring
        have hstep3 : (Real.pi / 2 - θ) ^ ((k : ℝ) - 2 + γ) * (4 / Real.pi) ^ (2 - γ)
              * (Real.pi / 2 - t) ^ (2 - γ)
            ≤ (Real.pi / 2 - θ) ^ ((k : ℝ) - 2 + γ) * (Real.sin (2 * t)) ^ (2 - γ) := by
          have hle : (4 / Real.pi) ^ (2 - γ) * (Real.pi / 2 - t) ^ (2 - γ)
              ≤ (Real.sin (2 * t)) ^ (2 - γ) := by
            rw [← hDmul]
            exact hσge
          have h : (4 / Real.pi) ^ (2 - γ) * (Real.pi / 2 - t) ^ (2 - γ)
                * (Real.pi / 2 - θ) ^ ((k : ℝ) - 2 + γ)
              ≤ (Real.sin (2 * t)) ^ (2 - γ) * (Real.pi / 2 - θ) ^ ((k : ℝ) - 2 + γ) :=
            mul_le_mul_of_nonneg_right hle
              (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Real.pi / 2 - θ) ((k : ℝ) - 2 + γ))
          linarith [h]
        linarith [hstep1, hstep2, hstep3]
      rw [div_le_iff₀ hσpos]
      exact le_trans hnum hA
    · rw [heq, Real.cos_pi_div_two, zero_pow (by omega : k ≠ 0)]
      rw [show Real.sin (2 * (Real.pi / 2)) = 0 by
        rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]]
      rw [Real.zero_rpow (by linarith : (2 : ℝ) - γ ≠ 0), zero_div]
      exact Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Real.pi / 2 - θ) _
  -- (7), (8): the two weighted tails
  have hint1 : (∫ t in θ..(Real.pi / 2), (Real.cos t) ^ 4 / (Real.sin (2 * t)) ^ (2 - γ))
      ≤ (4 * (Real.pi / 2) ^ (3 + γ) + 4 * (Real.pi / 2) ^ (5 + γ) + 1)
        * (Real.pi / 2 - θ) ^ (3 + γ) := by
    rw [intervalIntegral.integral_of_le (by linarith : θ ≤ Real.pi / 2)]
    have hconst : MeasureTheory.IntegrableOn
        (fun _ : ℝ => (Real.pi / 2 - θ) ^ (2 + γ)) (Set.Ioc θ (Real.pi / 2)) :=
      MeasureTheory.integrableOn_const (C := (Real.pi / 2 - θ) ^ (2 + γ)) (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top)
    have hmono : (∫ t in Set.Ioc θ (Real.pi / 2),
          (Real.cos t) ^ 4 / (Real.sin (2 * t)) ^ (2 - γ))
        ≤ ∫ t in Set.Ioc θ (Real.pi / 2), (Real.pi / 2 - θ) ^ (2 + γ) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ hconst ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        exact div_nonneg (pow_nonneg (Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [hθ.1, ht.1, Real.pi_pos], ht.2⟩) 4)
          (Real.rpow_nonneg (sin_two_nonneg (by linarith [hθ.1, ht.1, Real.pi_pos]) ht.2) _)
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        have h := hpt t ht 4 (by norm_num)
        have h4 : ((4 : ℕ) : ℝ) - 2 + γ = 2 + γ := by ring
        rwa [h4] at h
    rw [setIntegral_Ioc_const (by linarith : θ ≤ Real.pi / 2)] at hmono
    have hpow : (Real.pi / 2 - θ) ^ (2 + γ) * (Real.pi / 2 - θ) = (Real.pi / 2 - θ) ^ (3 + γ) := by
      have h1 : (Real.pi / 2 - θ) ^ (2 + γ) * (Real.pi / 2 - θ) ^ (1 : ℝ)
          = (Real.pi / 2 - θ) ^ (3 + γ) := by
        rw [← Real.rpow_add hεpos]
        congr 1
        ring
      rwa [Real.rpow_one] at h1
    rw [hpow] at hmono
    have hnn : 0 ≤ (Real.pi / 2 - θ) ^ (3 + γ) := Real.rpow_nonneg hεpos.le _
    exact le_trans hmono (by
      have := mul_le_mul_of_nonneg_right hC1 hnn
      linarith [this])
  have hint2 : (∫ t in θ..(Real.pi / 2), (Real.cos t) ^ 6 / (Real.sin (2 * t)) ^ (2 - γ))
      ≤ (4 * (Real.pi / 2) ^ (3 + γ) + 4 * (Real.pi / 2) ^ (5 + γ) + 1)
        * (Real.pi / 2 - θ) ^ (5 + γ) := by
    rw [intervalIntegral.integral_of_le (by linarith : θ ≤ Real.pi / 2)]
    have hconst : MeasureTheory.IntegrableOn
        (fun _ : ℝ => (Real.pi / 2 - θ) ^ (4 + γ)) (Set.Ioc θ (Real.pi / 2)) :=
      MeasureTheory.integrableOn_const (C := (Real.pi / 2 - θ) ^ (4 + γ)) (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top)
    have hmono : (∫ t in Set.Ioc θ (Real.pi / 2),
          (Real.cos t) ^ 6 / (Real.sin (2 * t)) ^ (2 - γ))
        ≤ ∫ t in Set.Ioc θ (Real.pi / 2), (Real.pi / 2 - θ) ^ (4 + γ) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ hconst ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        exact div_nonneg (pow_nonneg (Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [hθ.1, ht.1, Real.pi_pos], ht.2⟩) 6)
          (Real.rpow_nonneg (sin_two_nonneg (by linarith [hθ.1, ht.1, Real.pi_pos]) ht.2) _)
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        have h := hpt t ht 6 (by norm_num)
        have h6 : ((6 : ℕ) : ℝ) - 2 + γ = 4 + γ := by ring
        rwa [h6] at h
    rw [setIntegral_Ioc_const (by linarith : θ ≤ Real.pi / 2)] at hmono
    have hpow : (Real.pi / 2 - θ) ^ (4 + γ) * (Real.pi / 2 - θ) = (Real.pi / 2 - θ) ^ (5 + γ) := by
      have h1 : (Real.pi / 2 - θ) ^ (4 + γ) * (Real.pi / 2 - θ) ^ (1 : ℝ)
          = (Real.pi / 2 - θ) ^ (5 + γ) := by
        rw [← Real.rpow_add hεpos]
        congr 1
        ring
      rwa [Real.rpow_one] at h1
    rw [hpow] at hmono
    have hnn : 0 ≤ (Real.pi / 2 - θ) ^ (5 + γ) := Real.rpow_nonneg hεpos.le _
    exact le_trans hmono (by
      have := mul_le_mul_of_nonneg_right hC1 hnn
      linarith [this])
  exact ⟨hcosge, hcosle, hσ5, hσ7, hε3, hε5, hint1, hint2⟩

/-! ### A self-contained tail bound for a bounded primitive

The two lemmas below replace the imported `abs_le_tail_of_bounded_primitive` (whose module
pulls in an unfinished dependency).  `abs_sub_le_tail_local` is the fundamental-theorem-of-
calculus bound on the increment of a primitive, and `abs_le_tail_local` is the contrapositive
argument: a bounded primitive whose derivative is `Q/cos^p` forces `Q` to be dominated by the
tail integral of its own derivative. -/

/-- For `e < 0`, `R ≥ 0` and `c > 0` there is `δ ∈ (0, c)` with `δ ^ e > R`. -/
private lemma exists_rpow_neg_gt {e R c : ℝ} (he : e < 0) (hR : 0 ≤ R) (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ δ < c ∧ R < δ ^ e := by
  have hpos : 0 < R + 2 := by linarith
  have hne : e ≠ 0 := ne_of_lt he
  have hDpos : 0 < (R + 2) ^ (1 / e) := Real.rpow_pos_of_pos hpos _
  have hbig : R < ((R + 2) ^ (1 / e)) ^ e := by
    have hmul : ((R + 2) ^ (1 / e)) ^ e = R + 2 := by
      rw [← Real.rpow_mul hpos.le (1 / e) e, one_div, inv_mul_cancel₀ hne, Real.rpow_one]
    rw [hmul]; linarith
  refine ⟨min ((R + 2) ^ (1 / e)) (c / 2), lt_min hDpos (by linarith), ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  · have hle : min ((R + 2) ^ (1 / e)) (c / 2) ≤ (R + 2) ^ (1 / e) := min_le_left _ _
    have h4 : ((R + 2) ^ (1 / e)) ^ e ≤ (min ((R + 2) ^ (1 / e)) (c / 2)) ^ e :=
      Real.rpow_le_rpow_of_nonpos (lt_min hDpos (by linarith)) hle (le_of_lt he)
    linarith

/-- The fundamental-theorem-of-calculus bound on the increment of a primitive. -/
private lemma abs_sub_le_tail_local {T b : ℝ} (hTb : T < b) {Q q : ℝ → ℝ}
    (hQ : ∀ t ∈ Set.Ioo T b, HasDerivAt Q (q t) t)
    (hq : MeasureTheory.IntegrableOn (fun t => |q t|) (Set.Ioc T b))
    {θ u : ℝ} (hθ : θ ∈ Set.Ioo T b) (hu : u ∈ Set.Ioo T b) (hθu : θ ≤ u) :
    |Q u - Q θ| ≤ ∫ t in Set.Ioc θ b, |q t| := by
  have hsub : Set.Ioc θ u ⊆ Set.Ioo T b := fun x hx =>
    ⟨lt_trans hθ.1 hx.1, lt_of_le_of_lt hx.2 hu.2⟩
  have haesm : MeasureTheory.AEStronglyMeasurable q
      (MeasureTheory.volume.restrict (Set.Ioc θ u)) := by
    refine (aestronglyMeasurable_deriv Q MeasureTheory.volume).restrict.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => ?_)
    exact (hQ x (hsub hx)).deriv
  have hqabs : MeasureTheory.IntegrableOn (fun t => |q t|) (Set.Ioc θ u) :=
    hq.mono_set (fun x hx => ⟨lt_trans hθ.1 hx.1, le_trans hx.2 (le_of_lt hu.2)⟩)
  have hqint : MeasureTheory.IntegrableOn q (Set.Ioc θ u) := by
    rw [MeasureTheory.IntegrableOn] at hqabs ⊢
    exact MeasureTheory.Integrable.mono' hqabs haesm
      (Filter.Eventually.of_forall (fun a => by simp [Real.norm_eq_abs]))
  have hintq : IntervalIntegrable q MeasureTheory.volume θ u := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hθu]
    exact hqint
  have hderiv : ∀ x ∈ Set.uIcc θ u, HasDerivAt Q (q x) x := by
    intro x hx
    rw [Set.uIcc_of_le hθu] at hx
    exact hQ x ⟨lt_of_lt_of_le hθ.1 hx.1, lt_of_le_of_lt hx.2 hu.2⟩
  have hftc : ∫ x in θ..u, q x = Q u - Q θ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintq
  have hb : |∫ x in θ..u, q x| ≤ ∫ x in θ..u, |q x| :=
    intervalIntegral.abs_integral_le_integral_abs hθu
  rw [hftc] at hb
  have htail : ∫ x in θ..u, |q x| ≤ ∫ x in Set.Ioc θ b, |q x| := by
    rw [intervalIntegral.integral_of_le hθu]
    exact MeasureTheory.setIntegral_mono_set
      (hq.mono_set (fun x hx => ⟨lt_trans hθ.1 hx.1, hx.2⟩))
      (Filter.Eventually.of_forall (fun x => abs_nonneg (q x)))
      (Filter.Eventually.of_forall (fun x hx => ⟨hx.1, le_trans hx.2 (le_of_lt hu.2)⟩))
  linarith

/-- `Φ u = (b - u) ^ (1 - p) / (p - 1)` has derivative `(b - u) ^ (-p)`. -/
private lemma hasDerivAt_Phi {b p u : ℝ} (hp : 1 < p) (hu : u < b) :
    HasDerivAt (fun u : ℝ => (b - u) ^ (1 - p) / (p - 1)) ((b - u) ^ (-p)) u := by
  have hbu : 0 < b - u := sub_pos.mpr hu
  have hp1 : p - 1 ≠ 0 := by linarith
  have h1 : HasDerivAt (fun u : ℝ => b - u) (-1) u :=
    (hasDerivAt_id u).const_sub b
  have h2 : HasDerivAt (fun y : ℝ => (b - y) ^ (1 - p))
      ((-1) * (1 - p) * (b - u) ^ (1 - p - 1)) u :=
    h1.rpow_const (Or.inl hbu.ne')
  have h3 : (-1 : ℝ) * (1 - p) * (b - u) ^ (1 - p - 1) = (b - u) ^ (-p) * (p - 1) := by
    rw [show (1 : ℝ) - p - 1 = -p by ring]
    ring
  rw [h3] at h2
  have h4 := h2.div_const (p - 1)
  rwa [mul_div_cancel_right₀ _ hp1] at h4

/-- **A bounded primitive forces the boundary value of its "good quotient" to vanish.**

Let `T < b`, `p > 1`, `Q, q, F, f` with `Q' = q` and `F' = f` on `(T,b)`, `f = Q / cos^p` there
and `|F| ≤ K` on `[T,b)`, and suppose `cos t > 0`, `cos t ≤ b - t` on `[T,b)`.  Then for every
`θ ∈ (T,b)`, `|Q θ| ≤ ∫_{t ∈ (θ,b]} |q t|`.

Proof (contrapositive).  If `A := ∫_{(θ,b]}|q| < |Q θ|` then `Q` keeps the sign `s` of `Q θ`
on `(θ,b)` and `s Q ≥ μ := |Q θ| - A > 0` there, so `s F' ≥ μ / cos^p ≥ μ (b-t)^{-p}`.  With
`Φ(t) := (b-t)^{1-p}/(p-1)` (so `Φ' = (b-t)^{-p}`) the function `s F - μ Φ` is monotone on
`[θ,u]` for every `u ∈ (θ,b)`, hence `s F t ≥ G θ + μ Φ t → ∞` as `t → b⁻`, contradicting
`|F| ≤ K`. -/
private lemma abs_le_tail_local {T b K p : ℝ} (hTb : T < b) (hp : 1 < p)
    (hcos_pos : ∀ t ∈ Set.Ico T b, 0 < Real.cos t)
    (hcos_le : ∀ t ∈ Set.Ico T b, Real.cos t ≤ b - t)
    {Q q F f : ℝ → ℝ}
    (hQ : ∀ t ∈ Set.Ioo T b, HasDerivAt Q (q t) t)
    (hF : ∀ t ∈ Set.Ioo T b, HasDerivAt F (f t) t)
    (hq : MeasureTheory.IntegrableOn (fun t => |q t|) (Set.Ioc T b))
    (hfp : ∀ t ∈ Set.Ioo T b, f t = Q t / (Real.cos t) ^ p)
    (hFbd : ∀ t ∈ Set.Ico T b, |F t| ≤ K) :
    ∀ θ ∈ Set.Ioo T b, |Q θ| ≤ ∫ t in Set.Ioc θ b, |q t| := by
  intro θ hθ
  by_contra hcon
  rw [not_le] at hcon
  set A : ℝ := ∫ t in Set.Ioc θ b, |q t| with hA
  have hA0 : 0 ≤ A := MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun x _ => abs_nonneg _)
  have hQθpos : 0 < |Q θ| := lt_of_le_of_lt hA0 hcon
  have hQθne : Q θ ≠ 0 := fun h => by rw [h] at hQθpos; simp at hQθpos
  set μ : ℝ := |Q θ| - A with hμ
  have hμpos : 0 < μ := by rw [hμ]; linarith
  set s : ℝ := if 0 < Q θ then 1 else -1 with hsdef
  have hsval : s = 1 ∨ s = -1 := by rw [hsdef]; split_ifs <;> simp
  have hsabs : |s| = 1 := by rcases hsval with h | h <;> rw [h] <;> norm_num
  have hsQ : s * Q θ = |Q θ| := by
    rw [hsdef]; split_ifs with h
    · rw [one_mul, abs_of_pos h]
    · have hle : Q θ ≤ 0 := not_lt.mp h
      have hlt : Q θ < 0 := lt_of_le_of_ne hle hQθne
      rw [neg_one_mul, abs_of_neg hlt]
  -- `Q` keeps the sign `s` and `s Q ≥ μ` on `(θ,b)`
  have hQlower : ∀ t ∈ Set.Ioo θ b, μ ≤ s * Q t := by
    intro t ht
    have htTb : t ∈ Set.Ioo T b := ⟨lt_trans hθ.1 ht.1, ht.2⟩
    have hQu : |Q t - Q θ| ≤ A := by
      have h := abs_sub_le_tail_local hTb hQ hq hθ htTb (le_of_lt ht.1)
      rw [hA]; exact h
    have hkey : s * (Q θ - Q t) ≤ |Q t - Q θ| := by
      have h1 : s * (Q θ - Q t) ≤ |s * (Q θ - Q t)| := le_abs_self _
      have h2 : |s * (Q θ - Q t)| = |Q t - Q θ| := by
        rw [abs_mul, hsabs, one_mul, abs_sub_comm]
      linarith [h1, h2]
    have h3 : s * Q t = s * Q θ - s * (Q θ - Q t) := by ring
    rw [h3, hsQ, hμ]
    linarith
  -- the comparison function `Φ`
  set Φ : ℝ → ℝ := fun u => (b - u) ^ (1 - p) / (p - 1) with hΦdef
  have hΦderiv : ∀ u ∈ Set.Ioo θ b, HasDerivAt Φ ((b - u) ^ (-p)) u := by
    intro u hu
    rw [hΦdef]
    exact hasDerivAt_Phi hp hu.2
  set G : ℝ → ℝ := fun u => s * F u - μ * Φ u with hGdef
  have hGderiv : ∀ u ∈ Set.Ioo θ b, HasDerivAt G (s * f u - μ * (b - u) ^ (-p)) u := by
    intro u hu
    rw [hGdef]
    exact ((hF u ⟨lt_trans hθ.1 hu.1, hu.2⟩).const_mul s).sub ((hΦderiv u hu).const_mul μ)
  -- `G` increases on `[θ,u]` for every `u ∈ (θ,b)`
  have hGmono : ∀ u ∈ Set.Ioo θ b, G θ ≤ G u := by
    intro u hu
    have hcont : ContinuousOn G (Set.Icc θ u) := by
      refine ContinuousOn.sub ?_ ?_
      · exact ContinuousOn.const_mul
          (fun x hx => ((hF x ⟨lt_of_lt_of_le hθ.1 hx.1, lt_of_le_of_lt hx.2 hu.2⟩).continuousAt).continuousWithinAt)
          s
      · refine ContinuousOn.const_mul ?_ μ
        intro x hx
        have hxb : x < b := lt_of_le_of_lt hx.2 hu.2
        exact ((hasDerivAt_Phi hp hxb).continuousAt).continuousWithinAt
    have hdiff : DifferentiableOn ℝ G (interior (Set.Icc θ u)) := by
      rw [interior_Icc]
      intro x hx
      exact (hGderiv x ⟨hx.1, lt_trans hx.2 hu.2⟩).differentiableAt.differentiableWithinAt
    have hnonneg : ∀ x ∈ interior (Set.Icc θ u), 0 ≤ deriv G x := by
      rw [interior_Icc]
      intro x hx
      have hxIob : x ∈ Set.Ioo θ b := ⟨hx.1, lt_trans hx.2 hu.2⟩
      have hxTb : x ∈ Set.Ioo T b := ⟨lt_trans hθ.1 hx.1, hxIob.2⟩
      have hcosx : 0 < Real.cos x := hcos_pos x ⟨le_of_lt hxTb.1, hxTb.2⟩
      have hcosle : Real.cos x ≤ b - x := hcos_le x ⟨le_of_lt hxTb.1, hxTb.2⟩
      have hbx : 0 < b - x := sub_pos.mpr hxTb.2
      rw [(hGderiv x hxIob).deriv]
      have hQl := hQlower x hxIob
      have h1 : μ / (Real.cos x) ^ p ≤ s * Q x / (Real.cos x) ^ p :=
        div_le_div_of_nonneg_right hQl (Real.rpow_nonneg hcosx.le p)
      have hsf : s * f x = s * Q x / (Real.cos x) ^ p := by
        rw [hfp x hxTb]; ring
      have h6 : (b - x) ^ (-p) ≤ (Real.cos x) ^ (-p) :=
        Real.rpow_le_rpow_of_nonpos hcosx hcosle (by linarith)
      have h7 : (Real.cos x) ^ (-p) = 1 / (Real.cos x) ^ p := by
        rw [Real.rpow_neg hcosx.le p, one_div]
      have h8 : μ * (b - x) ^ (-p) ≤ μ / (Real.cos x) ^ p := by
        rw [h7] at h6
        calc μ * (b - x) ^ (-p) ≤ μ * (1 / (Real.cos x) ^ p) :=
              mul_le_mul_of_nonneg_left h6 hμpos.le
          _ = μ / (Real.cos x) ^ p := by ring
      rw [hsf]
      linarith [h1, h8]
    exact monotoneOn_of_deriv_nonneg (convex_Icc θ u) hcont hdiff hnonneg
      ⟨le_rfl, le_of_lt hu.1⟩ ⟨le_of_lt hu.1, le_rfl⟩ (le_of_lt hu.1)
  -- choose the point `b - δ`
  have hc : 0 < b - θ := sub_pos.mpr hθ.2
  set R : ℝ := max ((p - 1) * (K - G θ) / μ) 0 + 1 with hRdef
  have hR0 : 0 ≤ R := by
    have h := le_max_right ((p - 1) * (K - G θ) / μ) 0
    rw [hRdef]; linarith
  obtain ⟨δ, hδpos, hδc, hδR⟩ := exists_rpow_neg_gt (e := 1 - p) (by linarith) hR0 hc
  have hu : b - δ ∈ Set.Ioo θ b :=
    ⟨by linarith, by linarith⟩
  have hGθu : G θ ≤ G (b - δ) := hGmono (b - δ) hu
  have hsFu : s * F (b - δ)
      = G (b - δ) + μ * ((b - (b - δ)) ^ (1 - p) / (p - 1)) := by
    rw [hGdef, hΦdef]; ring
  have hsFle : s * F (b - δ) ≤ K := by
    have h1 : s * F (b - δ) ≤ |s * F (b - δ)| := le_abs_self _
    have h2 : |F (b - δ)| ≤ K :=
      hFbd (b - δ) ⟨le_of_lt (lt_trans hθ.1 hu.1), hu.2⟩
    rw [abs_mul, hsabs, one_mul] at h1
    linarith
  have hbig : K < G θ + μ * ((b - (b - δ)) ^ (1 - p) / (p - 1)) := by
    have hp1 : 0 < p - 1 := by linarith
    have h2 : (p - 1) * (K - G θ) / μ < R := by
      have h := le_max_left ((p - 1) * (K - G θ) / μ) 0
      rw [hRdef]; linarith
    have h4 : (p - 1) * (K - G θ) / μ < δ ^ (1 - p) := lt_trans h2 hδR
    have h5 : (p - 1) * (K - G θ) < δ ^ (1 - p) * μ := by
      rw [div_lt_iff₀ hμpos] at h4
      linarith
    have h6 : (p - 1) * (K - G θ) / (p - 1) < δ ^ (1 - p) * μ / (p - 1) :=
      div_lt_div_of_pos_right h5 hp1
    rw [mul_div_cancel_left₀ _ hp1.ne'] at h6
    have h7 : μ * ((b - (b - δ)) ^ (1 - p) / (p - 1)) = δ ^ (1 - p) * μ / (p - 1) := by
      rw [show b - (b - δ) = δ by ring]; ring
    rw [h7]
    linarith
  linarith [hsFu, hGθu, hbig, hsFle]

/-- **Tail bound for `Ψ₁`.** -/
private lemma Psi1_tail_le {γ Cw Kq GG : ℝ} (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    (hCw : 0 ≤ Cw) (hKq : 0 ≤ Kq) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    (hG2 : MeasureTheory.IntegrableOn
      (fun θ => (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (hGG : (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) ≤ GG)
    (hub : ∀ η ∈ Work.Spaces.Iθ, |u η| ≤ (Real.pi / 2 - η) * Kq)
    (hI4 : ∀ ν ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
      (∫ t in ν..(Real.pi / 2), (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ))
        ≤ Cw * (Real.pi / 2 - ν) ^ (3 + γ)) :
    (∀ ν ∈ Set.Ioo (Real.pi / 8) (Real.pi / 2),
        |(Real.cos ν) ^ 3 * deriv (fun s => u s / Real.cos s) ν|
          ≤ ∫ t in Set.Ioc (Real.pi / 8) (Real.pi / 2),
              |-(4 * u t + g t) * (Real.cos t) ^ 2|)
      ∧ (∀ ν ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
        |(Real.cos ν) ^ 3 * deriv (fun s => u s / Real.cos s) ν|
          ≤ 4 * Kq * (Real.pi / 2 - ν) ^ (4 : ℝ)
            + Real.sqrt (Cw * GG) * (Real.pi / 2 - ν) ^ ((3 + γ) / 2)) := by
  have hm_g : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 8) (Real.pi / 2))) :=
    ae_measurable_g hcont hg (by linarith [Real.pi_pos]) le_rfl
  have hm_u : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 8) (Real.pi / 2))) :=
    ContinuousOn.aestronglyMeasurable
      (hcont.mono (fun x hx => ⟨le_of_lt (by linarith [hx.1, Real.pi_pos]), hx.2.le⟩))
      measurableSet_Ioo
  have hG8 : MeasureTheory.IntegrableOn
      (fun t => (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
      (Set.Ioo (Real.pi / 8) (Real.pi / 2)) :=
    hG2.mono_set (fun x hx => ⟨le_of_lt (by linarith [hx.1, Real.pi_pos]), hx.2.le⟩)
  -- integrability of `abs q` for `q = -(4u+g)cos²` on `(π/8, π/2)`
  have hqint_oo : MeasureTheory.IntegrableOn
      (fun t => |-(4 * u t + g t) * (Real.cos t) ^ 2|)
      (Set.Ioo (Real.pi / 8) (Real.pi / 2)) := by
    have hbig : MeasureTheory.IntegrableOn
        (fun t => 4 * (Kq * (Real.pi / 2 - Real.pi / 8) ^ (3 : ℝ)) + |g t| * (Real.cos t) ^ 2)
        (Set.Ioo (Real.pi / 8) (Real.pi / 2)) :=
      (MeasureTheory.integrableOn_const (C := 4 * (Kq * (Real.pi / 2 - Real.pi / 8) ^ (3 : ℝ)))
        (by
          rw [Real.volume_Ioo]
          exact ENNReal.ofReal_ne_top)).add
        (integrable_abs_g_cos_sq hγ1 hm_g hG8)
    refine MeasureTheory.Integrable.mono' hbig ?_ ?_
    · have hq : MeasureTheory.AEStronglyMeasurable
          (fun t => -(4 * u t + g t) * (Real.cos t) ^ 2)
          (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 8) (Real.pi / 2))) :=
        (((hm_u.const_mul 4).add hm_g).neg).mul
          ((Real.continuous_cos.pow 2).aestronglyMeasurable)
      simpa only [Real.norm_eq_abs] using hq.norm
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : 0 < t := by linarith [ht.1, Real.pi_pos]
      have hb : |-(4 * u t + g t) * (Real.cos t) ^ 2|
          ≤ 4 * (Kq * (Real.pi / 2 - Real.pi / 8) ^ (3 : ℝ)) + |g t| * (Real.cos t) ^ 2 :=
        abs_q_le (Kq := Kq) (δ := Real.pi / 8) (t := t) hKq (le_of_lt ht.1) ht0 ht.2.le hub
      simpa only [Real.norm_eq_abs, abs_abs] using hb
  have hqint : MeasureTheory.IntegrableOn
      (fun t => |-(4 * u t + g t) * (Real.cos t) ^ 2|) (Set.Ioc (Real.pi / 8) (Real.pi / 2)) :=
    integrableOn_Ioc_of_Ioo hqint_oo
  -- the primitive-lemma input
  have hkey : ∀ ν ∈ Set.Ioo (Real.pi / 8) (Real.pi / 2),
      |(Real.cos ν) ^ 3 * deriv (fun s => u s / Real.cos s) ν|
        ≤ ∫ t in Set.Ioc ν (Real.pi / 2), |-(4 * u t + g t) * (Real.cos t) ^ 2| := by
    intro ν hν
    refine abs_le_tail_local (T := Real.pi / 8) (b := Real.pi / 2)
      (K := (Real.pi / 2) * Kq) (p := 3)
      (Q := fun s => (Real.cos s) ^ 3 * deriv (fun r => u r / Real.cos r) s)
      (q := fun t => -(4 * u t + g t) * (Real.cos t) ^ 2)
      (F := fun t => u t / Real.cos t) (f := deriv (fun r => u r / Real.cos r))
      (by linarith [Real.pi_pos]) (by norm_num)
      (fun t ht => Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
      (fun t ht => cos_le_pi_div_two_sub (by linarith [ht.1, Real.pi_pos]) ht.2.le)
      (fun t ht => Psi1_hasDerivAt u g hu hg t ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
      (fun t ht => hasDerivAt_slice u hu t ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
      hqint
      (fun t ht => by
        have hc : (Real.cos t) ^ 3 ≠ 0 :=
          pow_ne_zero 3 (cos_ne_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
        rw [rpow_nat_three (Real.cos t), eq_div_iff hc]
        ring)
      (fun t ht => by
        have ht0 : 0 < t := by linarith [ht.1, Real.pi_pos]
        have hcospos : 0 < Real.cos t :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
        have hcosge : (2 / Real.pi) * (Real.pi / 2 - t) ≤ Real.cos t :=
          two_div_pi_mul_le_cos ht0.le ht.2.le
        have h1 := hub t ⟨ht0.le, ht.2.le⟩
        have hεt : 0 < Real.pi / 2 - t := by linarith [ht.2]
        rw [abs_div, abs_of_pos hcospos]
        have h2 : ((Real.pi / 2 - t) * Kq) / ((2 / Real.pi) * (Real.pi / 2 - t))
            = (Real.pi / 2) * Kq := by
          have hA : Real.pi / 2 - t ≠ 0 := ne_of_gt hεt
          rw [mul_comm (Real.pi / 2 - t) Kq, mul_div_mul_right Kq (2 / Real.pi) hA]
          have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
          field_simp
          try ring
        calc |u t| / Real.cos t ≤ ((Real.pi / 2 - t) * Kq) / Real.cos t :=
              div_le_div_of_nonneg_right h1 hcospos.le
          _ ≤ ((Real.pi / 2 - t) * Kq) / ((2 / Real.pi) * (Real.pi / 2 - t)) :=
              div_le_div_of_nonneg_left (mul_nonneg hεt.le hKq)
                (mul_pos (div_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) hεt) hcosge
          _ = (Real.pi / 2) * Kq := h2)
      ν hν
  refine ⟨?_, ?_⟩
  · intro ν hν
    refine le_trans (hkey ν hν) ?_
    refine MeasureTheory.setIntegral_mono_set hqint
      (Filter.Eventually.of_forall fun t => abs_nonneg _) ?_
    exact Filter.Eventually.of_forall fun t ht =>
      ⟨lt_of_lt_of_le (show Real.pi / 8 < ν by linarith [hν.1, Real.pi_pos]) (le_of_lt ht.1),
        ht.2⟩
  · intro ν hν
    have hν8 : Real.pi / 8 ≤ ν := by linarith [hν.1, Real.pi_pos]
    have hνlt : ν < Real.pi / 2 := hν.2
    have hεpos : 0 < Real.pi / 2 - ν := by linarith [hν.2]
    have hνIoo : ν ∈ Set.Ioo (Real.pi / 8) (Real.pi / 2) :=
      ⟨by linarith [hν.1, Real.pi_pos], hν.2⟩
    have hGν : MeasureTheory.IntegrableOn
        (fun t => (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)) (Set.Ioo ν (Real.pi / 2)) :=
      hG2.mono_set (fun x hx =>
        ⟨le_of_lt (by linarith [hν.1, hx.1, Real.pi_pos]), hx.2.le⟩)
    have hm_gν : MeasureTheory.AEStronglyMeasurable g
        (MeasureTheory.volume.restrict (Set.Ioo ν (Real.pi / 2))) :=
      ae_measurable_g hcont hg (by linarith [hν.1, Real.pi_pos]) le_rfl
    have hTailG := slice_bd_tail_g γ hγ1 hγ2 (g := g) (Cw := Cw) (ν := ν) hCw hν hm_gν hGν
      (hI4 ν hν)
    have hgIoc : MeasureTheory.IntegrableOn (fun t => |g t| * (Real.cos t) ^ 2)
        (Set.Ioc ν (Real.pi / 2)) := integrableOn_Ioc_of_Ioo hTailG.1
    have hu_bd : (∫ t in Set.Ioc ν (Real.pi / 2), |u t| * (Real.cos t) ^ 2)
        ≤ Kq * (Real.pi / 2 - ν) ^ (4 : ℝ) :=
      tail_u_cos_sq_le hKq hν8 hνlt hub
    have hg_bd : (∫ t in Set.Ioc ν (Real.pi / 2), |g t| * (Real.cos t) ^ 2)
        ≤ Real.sqrt (Cw * GG) * (Real.pi / 2 - ν) ^ ((3 + γ) / 2) := by
      rw [setIntegral_Ioc_eq_Ioo]
      calc (∫ t in Set.Ioo ν (Real.pi / 2), |g t| * (Real.cos t) ^ 2)
          ≤ Real.sqrt (Cw * (∫ t in Set.Ioo ν (Real.pi / 2),
                (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)))
              * (Real.pi / 2 - ν) ^ ((3 + γ) / 2) := hTailG.2
        _ ≤ Real.sqrt (Cw * GG) * (Real.pi / 2 - ν) ^ ((3 + γ) / 2) := by
            have hle : (∫ t in Set.Ioo ν (Real.pi / 2),
                  (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)) ≤ GG :=
              le_trans (MeasureTheory.setIntegral_mono_set hG2
                (by
                  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
                  exact mul_nonneg (sq_nonneg _) (sigma_nonneg γ ht.1 ht.2))
                (Filter.Eventually.of_forall fun t ht =>
                  ⟨le_of_lt (by linarith [hν.1, ht.1, Real.pi_pos]), ht.2.le⟩)) hGG
            exact mul_le_mul_of_nonneg_right
              (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle hCw))
              (Real.rpow_nonneg (by linarith) _)
    have hle1 : (∫ t in Set.Ioc ν (Real.pi / 2), |-(4 * u t + g t) * (Real.cos t) ^ 2|)
        ≤ 4 * Kq * (Real.pi / 2 - ν) ^ (4 : ℝ)
          + Real.sqrt (Cw * GG) * (Real.pi / 2 - ν) ^ ((3 + γ) / 2) := by
      have hRHS : MeasureTheory.IntegrableOn
          (fun t => 4 * (Kq * (Real.pi / 2 - ν) ^ (3 : ℝ)) + |g t| * (Real.cos t) ^ 2)
          (Set.Ioc ν (Real.pi / 2)) :=
        (MeasureTheory.integrableOn_const (C := 4 * (Kq * (Real.pi / 2 - ν) ^ (3 : ℝ)))
          (by
            rw [Real.volume_Ioc]
            exact ENNReal.ofReal_ne_top)).add hgIoc
      have hstep : (∫ t in Set.Ioc ν (Real.pi / 2), |-(4 * u t + g t) * (Real.cos t) ^ 2|)
          ≤ ∫ t in Set.Ioc ν (Real.pi / 2),
              (4 * (Kq * (Real.pi / 2 - ν) ^ (3 : ℝ)) + |g t| * (Real.cos t) ^ 2) :=
        MeasureTheory.integral_mono_of_nonneg
          (f := fun t => |-(4 * u t + g t) * (Real.cos t) ^ 2|)
          (g := fun t => 4 * (Kq * (Real.pi / 2 - ν) ^ (3 : ℝ)) + |g t| * (Real.cos t) ^ 2)
          (Filter.Eventually.of_forall fun t => abs_nonneg _) hRHS
          (by
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
            have ht0 : 0 < t := by linarith [hν.1, ht.1, Real.pi_pos]
            exact abs_q_le (Kq := Kq) (δ := ν) (t := t) hKq (le_of_lt ht.1) ht0 ht.2 hub)
      have hconst : MeasureTheory.IntegrableOn
          (fun _ : ℝ => 4 * (Kq * (Real.pi / 2 - ν) ^ (3 : ℝ))) (Set.Ioc ν (Real.pi / 2)) :=
        MeasureTheory.integrableOn_const (C := 4 * (Kq * (Real.pi / 2 - ν) ^ (3 : ℝ))) (by
          rw [Real.volume_Ioc]
          exact ENNReal.ofReal_ne_top)
      rw [MeasureTheory.integral_add hconst hgIoc,
        setIntegral_Ioc_const (by linarith : ν ≤ Real.pi / 2)] at hstep
      have hconv : 4 * (Kq * (Real.pi / 2 - ν) ^ (3 : ℝ)) * (Real.pi / 2 - ν)
          = 4 * Kq * (Real.pi / 2 - ν) ^ (4 : ℝ) := by
        rw [mul_assoc 4 (Kq * (Real.pi / 2 - ν) ^ (3 : ℝ)) (Real.pi / 2 - ν),
          mul_assoc Kq ((Real.pi / 2 - ν) ^ (3 : ℝ)) (Real.pi / 2 - ν),
          rpow_three_mul (Real.pi / 2 - ν) hεpos]
        ring
      rw [hconv] at hstep
      linarith [hstep, hg_bd]
    exact le_trans (hkey ν hνIoo) hle1

/-- **Tail bound for `Ψ₂`.** -/
private lemma Psi2_tail_le {γ Cw Kq GG DD Qb : ℝ} (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    (hCw : 0 ≤ Cw) (hKq : 0 ≤ Kq) (hQb : 0 ≤ Qb) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    (hD : MeasureTheory.IntegrableOn
      (fun θ => (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (hDD : (∫ θ in Work.Spaces.Iθ,
        (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) ≤ DD)
    (hub : ∀ η ∈ Work.Spaces.Iθ, |u η| ≤ (Real.pi / 2 - η) * Kq)
    (hPsi1bd : ∀ t ∈ Set.Ioo (Real.pi / 8) (Real.pi / 2),
      |(Real.cos t) ^ 3 * deriv (fun s => u s / Real.cos s) t| ≤ Qb)
    (hPsi1sharp : ∀ t ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
      |(Real.cos t) ^ 3 * deriv (fun s => u s / Real.cos s) t|
        ≤ 4 * Kq * (Real.pi / 2 - t) ^ (4 : ℝ)
          + Real.sqrt (Cw * GG) * (Real.pi / 2 - t) ^ ((3 + γ) / 2))
    (hI6 : ∀ ν ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
      (∫ t in ν..(Real.pi / 2), (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ))
        ≤ Cw * (Real.pi / 2 - ν) ^ (5 + γ)) :
    ∀ ν ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
      |(Real.cos ν) ^ 4 * deriv (fun s => deriv (fun r => u r / Real.cos r) s) ν|
        ≤ Real.sqrt (Cw * DD) * (Real.pi / 2 - ν) ^ ((5 + γ) / 2)
          + 4 * Kq * (Real.pi / 2 - ν) ^ (6 : ℝ)
          + Real.sqrt (Cw * GG) * (Real.pi / 2 - ν) ^ ((7 + γ) / 2)
          + 2 * Real.pi * Kq * (Real.pi / 2 - ν) ^ (4 : ℝ) := by
  intro ν hν
  have hν8 : Real.pi / 8 ≤ ν := by linarith [hν.1, Real.pi_pos]
  have hνlt : ν < Real.pi / 2 := hν.2
  have hεpos : 0 < Real.pi / 2 - ν := by linarith [hν.2]
  have hm_u : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 8) (Real.pi / 2))) :=
    ContinuousOn.aestronglyMeasurable
      (hcont.mono (fun x hx => ⟨le_of_lt (by linarith [hx.1, Real.pi_pos]), hx.2.le⟩))
      measurableSet_Ioo
  have hD8 : MeasureTheory.IntegrableOn
      (fun t => (deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
      (Set.Ioo (Real.pi / 8) (Real.pi / 2)) :=
    hD.mono_set (fun x hx => ⟨le_of_lt (by linarith [hx.1, Real.pi_pos]), hx.2.le⟩)
  have hv_meas : MeasureTheory.AEStronglyMeasurable
      (fun t => deriv (fun s => u s / Real.cos s) t)
      (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 8) (Real.pi / 2))) :=
    (measurable_deriv fun t => u t / Real.cos t).aestronglyMeasurable
  -- ### integrability of `abs q₂` on `(π/8, π/2)`
  have hq2int_oo : MeasureTheory.IntegrableOn
      (fun t => abs (-((Real.cos t) ^ 3 * deriv g t) - (Real.cos t) ^ 4
          * deriv (fun s => u s / Real.cos s) t
          + 4 * Real.sin t * (Real.cos t) ^ 3 * (u t / Real.cos t)))
      (Set.Ioo (Real.pi / 8) (Real.pi / 2)) := by
    have h1 : MeasureTheory.IntegrableOn (fun t => (Real.cos t) ^ 3 * |deriv g t|)
        (Set.Ioo (Real.pi / 8) (Real.pi / 2)) :=
      integrable_cos3_abs_gprime hγ1
        ((measurable_deriv g).aestronglyMeasurable) hD8
    have h2 : MeasureTheory.IntegrableOn (fun t => (Real.cos t) ^ 4
        * |deriv (fun s => u s / Real.cos s) t|) (Set.Ioo (Real.pi / 8) (Real.pi / 2)) := by
      refine integrableOn_of_bound (s := Set.Ioo (Real.pi / 8) (Real.pi / 2)) measurableSet_Ioo
        (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (M := Qb) ?_ ?_
      · exact ((Real.continuous_cos.pow 4).aestronglyMeasurable).mul
          (aestronglyMeasurable_abs_real hv_meas)
      · intro t ht
        have hcos0 : 0 ≤ Real.cos t :=
          Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2.le⟩
        have hnn : 0 ≤ (Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t| :=
          mul_nonneg (pow_nonneg hcos0 4) (abs_nonneg _)
        rw [abs_of_nonneg hnn]
        have heq : (Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t|
            = Real.cos t * |(Real.cos t) ^ 3 * deriv (fun s => u s / Real.cos s) t| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg hcos0 3)]
          ring
        rw [heq]
        calc Real.cos t * |(Real.cos t) ^ 3 * deriv (fun s => u s / Real.cos s) t|
            ≤ Real.cos t * Qb := mul_le_mul_of_nonneg_left (hPsi1bd t ht) hcos0
          _ ≤ 1 * Qb := mul_le_mul_of_nonneg_right (Real.cos_le_one t) hQb
          _ = Qb := one_mul Qb
    have h3 : MeasureTheory.IntegrableOn
        (fun t => 4 * ((Real.cos t) ^ 3 * |u t / Real.cos t|))
        (Set.Ioo (Real.pi / 8) (Real.pi / 2)) := by
      refine integrableOn_of_bound (s := Set.Ioo (Real.pi / 8) (Real.pi / 2)) measurableSet_Ioo
        (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (M := 2 * Real.pi * Kq) ?_ ?_
      · have hc3 : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => (Real.cos t) ^ 3)
            (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 8) (Real.pi / 2))) :=
          (Real.continuous_cos.pow 3).aestronglyMeasurable
        have hv : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => u t / Real.cos t)
            (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 8) (Real.pi / 2))) :=
          aesm_div_cos hcont measurableSet_Ioo
            (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
        exact ((hc3.mul (aestronglyMeasurable_abs_real hv)).const_mul 4)
      · intro t ht
        have ht0 : 0 < t := by linarith [ht.1, Real.pi_pos]
        have hcospos : 0 < Real.cos t :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
        have hnn : 0 ≤ 4 * ((Real.cos t) ^ 3 * |u t / Real.cos t|) :=
          mul_nonneg (by norm_num)
            (mul_nonneg (pow_nonneg hcospos.le 3) (abs_nonneg _))
        rw [abs_of_nonneg hnn]
        have hcosge : (2 / Real.pi) * (Real.pi / 2 - t) ≤ Real.cos t :=
          two_div_pi_mul_le_cos ht0.le ht.2.le
        have h1b := hub t ⟨ht0.le, ht.2.le⟩
        have hεt : 0 < Real.pi / 2 - t := by linarith [ht.2]
        rw [abs_div, abs_of_pos hcospos]
        have hvb : |u t| / Real.cos t ≤ (Real.pi / 2) * Kq := by
          have h2b : ((Real.pi / 2 - t) * Kq) / ((2 / Real.pi) * (Real.pi / 2 - t))
              = (Real.pi / 2) * Kq := by
            have hA : Real.pi / 2 - t ≠ 0 := ne_of_gt hεt
            rw [mul_comm (Real.pi / 2 - t) Kq, mul_div_mul_right Kq (2 / Real.pi) hA]
            have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
            field_simp
            try ring
          calc |u t| / Real.cos t ≤ ((Real.pi / 2 - t) * Kq) / Real.cos t :=
                div_le_div_of_nonneg_right h1b hcospos.le
            _ ≤ ((Real.pi / 2 - t) * Kq) / ((2 / Real.pi) * (Real.pi / 2 - t)) :=
                div_le_div_of_nonneg_left (mul_nonneg hεt.le hKq)
                  (mul_pos (div_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) hεt) hcosge
            _ = (Real.pi / 2) * Kq := h2b
        have hcos3le : (Real.cos t) ^ 3 ≤ 1 := pow_le_one₀ hcospos.le (Real.cos_le_one t)
        calc 4 * ((Real.cos t) ^ 3 * (|u t| / Real.cos t))
            ≤ 4 * (1 * ((Real.pi / 2) * Kq)) := by
              have hpi2 : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
              have h := mul_le_mul hcos3le hvb (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
              exact mul_le_mul_of_nonneg_left h (by norm_num)
          _ = 2 * Real.pi * Kq := by ring
    have hsum : MeasureTheory.IntegrableOn
        (fun t => (Real.cos t) ^ 3 * |deriv g t|
          + ((Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t|
            + 4 * ((Real.cos t) ^ 3 * |u t / Real.cos t|)))
        (Set.Ioo (Real.pi / 8) (Real.pi / 2)) :=
      h1.add (h2.add h3)
    refine MeasureTheory.Integrable.mono' hsum ?_ ?_
    · have hc3 : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => (Real.cos t) ^ 3)
          (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 8) (Real.pi / 2))) :=
        (Real.continuous_cos.pow 3).aestronglyMeasurable
      have hc4 : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => (Real.cos t) ^ 4)
          (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 8) (Real.pi / 2))) :=
        (Real.continuous_cos.pow 4).aestronglyMeasurable
      have h4 : MeasureTheory.AEStronglyMeasurable (fun _ : ℝ => (4 : ℝ))
          (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 8) (Real.pi / 2))) :=
        aestronglyMeasurable_const
      have hdv : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => deriv g t)
          (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 8) (Real.pi / 2))) :=
        (measurable_deriv g).aestronglyMeasurable
      have hvc : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => u t / Real.cos t)
          (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 8) (Real.pi / 2))) :=
        aesm_div_cos hcont measurableSet_Ioo
          (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
      have hm_1 : MeasureTheory.AEStronglyMeasurable
          (fun t : ℝ => (Real.cos t) ^ 3 * deriv g t)
          (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 8) (Real.pi / 2))) :=
        hc3.mul hdv
      have hm_2 : MeasureTheory.AEStronglyMeasurable
          (fun t : ℝ => (Real.cos t) ^ 4 * deriv (fun s => u s / Real.cos s) t)
          (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 8) (Real.pi / 2))) :=
        hc4.mul hv_meas
      have hm_3 : MeasureTheory.AEStronglyMeasurable
          (fun t : ℝ => 4 * Real.sin t * (Real.cos t) ^ 3 * (u t / Real.cos t))
          (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 8) (Real.pi / 2))) :=
        ((h4.mul Real.continuous_sin.aestronglyMeasurable).mul hc3).mul hvc
      have hq2 : MeasureTheory.AEStronglyMeasurable
          (fun t : ℝ => -((Real.cos t) ^ 3 * deriv g t) - (Real.cos t) ^ 4
            * deriv (fun s => u s / Real.cos s) t
            + 4 * Real.sin t * (Real.cos t) ^ 3 * (u t / Real.cos t))
          (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 8) (Real.pi / 2))) :=
        (hm_1.neg.sub hm_2).add hm_3
      simpa only [Real.norm_eq_abs] using hq2.norm
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      have hcos0 : 0 ≤ Real.cos t :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2.le⟩
      have hsin1 : |Real.sin t| ≤ 1 := Real.abs_sin_le_one t
      have e1 : abs (-((Real.cos t) ^ 3 * deriv g t) - (Real.cos t) ^ 4
            * deriv (fun s => u s / Real.cos s) t
            + 4 * Real.sin t * (Real.cos t) ^ 3 * (u t / Real.cos t))
          ≤ abs (-((Real.cos t) ^ 3 * deriv g t) - (Real.cos t) ^ 4
              * deriv (fun s => u s / Real.cos s) t)
            + |4 * Real.sin t * (Real.cos t) ^ 3 * (u t / Real.cos t)| := abs_add_le _ _
      have e2 : abs (-((Real.cos t) ^ 3 * deriv g t) - (Real.cos t) ^ 4
            * deriv (fun s => u s / Real.cos s) t)
          ≤ (Real.cos t) ^ 3 * |deriv g t|
            + (Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t| := by
        have h1 : abs (-((Real.cos t) ^ 3 * deriv g t) - (Real.cos t) ^ 4
              * deriv (fun s => u s / Real.cos s) t)
            = abs (((Real.cos t) ^ 3 * deriv g t)
                + (Real.cos t) ^ 4 * deriv (fun s => u s / Real.cos s) t) := by
          rw [show -((Real.cos t) ^ 3 * deriv g t) - (Real.cos t) ^ 4
                * deriv (fun s => u s / Real.cos s) t
              = -(((Real.cos t) ^ 3 * deriv g t)
                + (Real.cos t) ^ 4 * deriv (fun s => u s / Real.cos s) t) by ring,
            abs_neg]
        rw [h1]
        calc abs (((Real.cos t) ^ 3 * deriv g t)
              + (Real.cos t) ^ 4 * deriv (fun s => u s / Real.cos s) t)
            ≤ |(Real.cos t) ^ 3 * deriv g t|
              + |(Real.cos t) ^ 4 * deriv (fun s => u s / Real.cos s) t| := abs_add_le _ _
          _ = (Real.cos t) ^ 3 * |deriv g t|
              + (Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hcos0 3),
                abs_of_nonneg (pow_nonneg hcos0 4)]
      have e3 : |4 * Real.sin t * (Real.cos t) ^ 3 * (u t / Real.cos t)|
          ≤ 4 * ((Real.cos t) ^ 3 * |u t / Real.cos t|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
          abs_of_nonneg (pow_nonneg hcos0 3)]
        have h := mul_le_mul_of_nonneg_right hsin1
          (by positivity : (0 : ℝ) ≤ 4 * (Real.cos t) ^ 3 * |u t / Real.cos t|)
        linarith [h]
      have htri : abs (-((Real.cos t) ^ 3 * deriv g t) - (Real.cos t) ^ 4
            * deriv (fun s => u s / Real.cos s) t
            + 4 * Real.sin t * (Real.cos t) ^ 3 * (u t / Real.cos t))
          ≤ (Real.cos t) ^ 3 * |deriv g t|
            + ((Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t|
              + 4 * ((Real.cos t) ^ 3 * |u t / Real.cos t|)) :=
        le_trans e1 (le_trans (add_le_add e2 e3) (le_of_eq (by ring)))
      simpa only [Real.norm_eq_abs, abs_abs] using htri
  have hq2int : MeasureTheory.IntegrableOn
      (fun t => abs (-((Real.cos t) ^ 3 * deriv g t) - (Real.cos t) ^ 4
          * deriv (fun s => u s / Real.cos s) t
          + 4 * Real.sin t * (Real.cos t) ^ 3 * (u t / Real.cos t)))
      (Set.Ioc (Real.pi / 8) (Real.pi / 2)) :=
    integrableOn_Ioc_of_Ioo hq2int_oo
  -- ### the primitive lemma
  have hkey : |(Real.cos ν) ^ 4 * deriv (fun s => deriv (fun r => u r / Real.cos r) s) ν|
      ≤ ∫ t in Set.Ioc ν (Real.pi / 2),
          abs (-((Real.cos t) ^ 3 * deriv g t) - (Real.cos t) ^ 4
            * deriv (fun s => u s / Real.cos s) t
            + 4 * Real.sin t * (Real.cos t) ^ 3 * (u t / Real.cos t)) := by
    refine abs_le_tail_of_bounded_double_primitive (T := Real.pi / 8) (b := Real.pi / 2)
      (K := (Real.pi / 2) * Kq) (p := 4)
      (Q := fun s => (Real.cos s) ^ 4
        * deriv (fun r => deriv (fun q => u q / Real.cos q) r) s)
      (q := fun t => -((Real.cos t) ^ 3 * deriv g t) - (Real.cos t) ^ 4
            * deriv (fun s => u s / Real.cos s) t
            + 4 * Real.sin t * (Real.cos t) ^ 3 * (u t / Real.cos t))
      (F := fun t => u t / Real.cos t)
      (by linarith [Real.pi_pos]) (by norm_num)
      (fun t ht => Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
      (fun t ht => cos_le_pi_div_two_sub (by linarith [ht.1, Real.pi_pos]) ht.2.le)
      (fun t ht => (Psi2_hasDerivAt u g hu hg t
        ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩).congr_deriv (by ring))
      hq2int
      (fun t ht => hasDerivAt_slice u hu t ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
      (fun t ht => hasDerivAt_deriv_slice u hu t ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
      (fun t ht => by
        have hc : (Real.cos t) ^ 4 ≠ 0 :=
          pow_ne_zero 4 (cos_ne_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
        rw [rpow_nat_four (Real.cos t), eq_div_iff hc]
        ring)
      (fun t ht => by
        have ht0 : 0 < t := by linarith [ht.1, Real.pi_pos]
        have hcospos : 0 < Real.cos t :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
        have hcosge : (2 / Real.pi) * (Real.pi / 2 - t) ≤ Real.cos t :=
          two_div_pi_mul_le_cos ht0.le ht.2.le
        have h1 := hub t ⟨ht0.le, ht.2.le⟩
        have hεt : 0 < Real.pi / 2 - t := by linarith [ht.2]
        rw [abs_div, abs_of_pos hcospos]
        have h2 : ((Real.pi / 2 - t) * Kq) / ((2 / Real.pi) * (Real.pi / 2 - t))
            = (Real.pi / 2) * Kq := by
          have hA : Real.pi / 2 - t ≠ 0 := ne_of_gt hεt
          rw [mul_comm (Real.pi / 2 - t) Kq,
            mul_div_mul_right Kq (2 / Real.pi) hA]
          have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
          field_simp
          try ring
        calc |u t| / Real.cos t ≤ ((Real.pi / 2 - t) * Kq) / Real.cos t :=
              div_le_div_of_nonneg_right h1 hcospos.le
          _ ≤ ((Real.pi / 2 - t) * Kq) / ((2 / Real.pi) * (Real.pi / 2 - t)) :=
              div_le_div_of_nonneg_left (mul_nonneg hεt.le hKq)
                (mul_pos (div_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) hεt) hcosge
          _ = (Real.pi / 2) * Kq := h2)
      ν ⟨by linarith [hν.1, Real.pi_pos], hν.2⟩
  -- ### decomposition of the tail integral, over the open tail `(ν, π/2)`
  have hGν : MeasureTheory.IntegrableOn
      (fun t => (deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)) (Set.Ioo ν (Real.pi / 2)) :=
    hD.mono_set (fun x hx => ⟨le_of_lt (by linarith [hν.1, hx.1, Real.pi_pos]), hx.2.le⟩)
  have hm_gν : MeasureTheory.AEStronglyMeasurable (deriv g)
      (MeasureTheory.volume.restrict (Set.Ioo ν (Real.pi / 2))) :=
    (measurable_deriv g).aestronglyMeasurable
  have hTailG := slice_bd_tail_gprime γ hγ1 hγ2 (g := g) (Cw := Cw) (ν := ν) hCw hν hm_gν hGν
    (hI6 ν hν)
  have hgpIoo : MeasureTheory.IntegrableOn (fun t => (Real.cos t) ^ 3 * |deriv g t|)
      (Set.Ioo ν (Real.pi / 2)) := hTailG.1
  have hv1Ioo : MeasureTheory.IntegrableOn
      (fun t => (Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t|)
      (Set.Ioo ν (Real.pi / 2)) := by
    refine integrableOn_of_bound (s := Set.Ioo ν (Real.pi / 2)) measurableSet_Ioo (by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (M := Qb) ?_ ?_
    · exact ((Real.continuous_cos.pow 4).aestronglyMeasurable).mul
        (aestronglyMeasurable_abs_real
          (measurable_deriv fun t => u t / Real.cos t).aestronglyMeasurable)
    · intro t ht
      have hcos0 : 0 ≤ Real.cos t :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hν.1, ht.1, Real.pi_pos], ht.2.le⟩
      have hnn : 0 ≤ (Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t| :=
        mul_nonneg (pow_nonneg hcos0 4) (abs_nonneg _)
      rw [abs_of_nonneg hnn]
      have heq : (Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t|
          = Real.cos t * |(Real.cos t) ^ 3 * deriv (fun s => u s / Real.cos s) t| := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hcos0 3)]
        ring
      rw [heq]
      calc Real.cos t * |(Real.cos t) ^ 3 * deriv (fun s => u s / Real.cos s) t|
          ≤ Real.cos t * Qb := mul_le_mul_of_nonneg_left
            (hPsi1bd t ⟨by linarith [hν.1, ht.1, Real.pi_pos], ht.2⟩) hcos0
        _ ≤ 1 * Qb := mul_le_mul_of_nonneg_right (Real.cos_le_one t) hQb
        _ = Qb := one_mul Qb
  have hvIoo : MeasureTheory.IntegrableOn
      (fun t => 4 * ((Real.cos t) ^ 3 * |u t / Real.cos t|))
      (Set.Ioo ν (Real.pi / 2)) := by
    refine integrableOn_of_bound (s := Set.Ioo ν (Real.pi / 2)) measurableSet_Ioo (by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (M := 2 * Real.pi * Kq) ?_ ?_
    · have hc3 : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => (Real.cos t) ^ 3)
          (MeasureTheory.volume.restrict (Set.Ioo ν (Real.pi / 2))) :=
        (Real.continuous_cos.pow 3).aestronglyMeasurable
      have hvc : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => u t / Real.cos t)
          (MeasureTheory.volume.restrict (Set.Ioo ν (Real.pi / 2))) :=
        aesm_div_cos hcont measurableSet_Ioo
          (fun x hx => ⟨by linarith [hν.1, hx.1, Real.pi_pos], hx.2⟩)
      exact ((hc3.mul (aestronglyMeasurable_abs_real hvc)).const_mul 4)
    · intro t ht
      have ht0 : 0 < t := by linarith [hν.1, ht.1, Real.pi_pos]
      have hcospos : 0 < Real.cos t :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hν.1, ht.1, Real.pi_pos], ht.2⟩
      have hnn : 0 ≤ 4 * ((Real.cos t) ^ 3 * |u t / Real.cos t|) :=
        mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg hcospos.le 3) (abs_nonneg _))
      rw [abs_of_nonneg hnn]
      have hcosge : (2 / Real.pi) * (Real.pi / 2 - t) ≤ Real.cos t :=
        two_div_pi_mul_le_cos ht0.le ht.2.le
      have h1 := hub t ⟨ht0.le, ht.2.le⟩
      have hεt : 0 < Real.pi / 2 - t := by linarith [ht.2]
      rw [abs_div, abs_of_pos hcospos]
      have h2 : ((Real.pi / 2 - t) * Kq) / ((2 / Real.pi) * (Real.pi / 2 - t))
          = (Real.pi / 2) * Kq := by
        have hA : Real.pi / 2 - t ≠ 0 := ne_of_gt hεt
        rw [mul_comm (Real.pi / 2 - t) Kq, mul_div_mul_right Kq (2 / Real.pi) hA]
        have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
        field_simp
        try ring
      have hvb : |u t| / Real.cos t ≤ (Real.pi / 2) * Kq :=
        calc |u t| / Real.cos t ≤ ((Real.pi / 2 - t) * Kq) / Real.cos t :=
              div_le_div_of_nonneg_right h1 hcospos.le
          _ ≤ ((Real.pi / 2 - t) * Kq) / ((2 / Real.pi) * (Real.pi / 2 - t)) :=
              div_le_div_of_nonneg_left (mul_nonneg hεt.le hKq)
                (mul_pos (div_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) hεt) hcosge
          _ = (Real.pi / 2) * Kq := h2
      have hcos3le : (Real.cos t) ^ 3 ≤ 1 := pow_le_one₀ hcospos.le (Real.cos_le_one t)
      calc 4 * ((Real.cos t) ^ 3 * (|u t| / Real.cos t))
          ≤ 4 * (1 * ((Real.pi / 2) * Kq)) := by
            have hpi2 : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
            have h := mul_le_mul hcos3le hvb (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
            exact mul_le_mul_of_nonneg_left h (by norm_num)
        _ = 2 * Real.pi * Kq := by ring
  have hsumIoo : MeasureTheory.IntegrableOn
      (fun t => (Real.cos t) ^ 3 * |deriv g t|
        + ((Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t|
          + 4 * ((Real.cos t) ^ 3 * |u t / Real.cos t|))) (Set.Ioo ν (Real.pi / 2)) :=
    hgpIoo.add (hv1Ioo.add hvIoo)
  have hstep1 : (∫ t in Set.Ioo ν (Real.pi / 2),
        abs (-((Real.cos t) ^ 3 * deriv g t) - (Real.cos t) ^ 4
          * deriv (fun s => u s / Real.cos s) t
          + 4 * Real.sin t * (Real.cos t) ^ 3 * (u t / Real.cos t)))
      ≤ ∫ t in Set.Ioo ν (Real.pi / 2),
        ((Real.cos t) ^ 3 * |deriv g t|
          + ((Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t|
            + 4 * ((Real.cos t) ^ 3 * |u t / Real.cos t|))) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hsumIoo ?_
    · exact Filter.Eventually.of_forall fun t => abs_nonneg _
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      have hcos0 : 0 ≤ Real.cos t :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hν.1, ht.1, Real.pi_pos], ht.2.le⟩
      have hsin1 : |Real.sin t| ≤ 1 := Real.abs_sin_le_one t
      have e1 : abs (-((Real.cos t) ^ 3 * deriv g t) - (Real.cos t) ^ 4
            * deriv (fun s => u s / Real.cos s) t
            + 4 * Real.sin t * (Real.cos t) ^ 3 * (u t / Real.cos t))
          ≤ abs (-((Real.cos t) ^ 3 * deriv g t) - (Real.cos t) ^ 4
              * deriv (fun s => u s / Real.cos s) t)
            + |4 * Real.sin t * (Real.cos t) ^ 3 * (u t / Real.cos t)| := abs_add_le _ _
      have e2 : abs (-((Real.cos t) ^ 3 * deriv g t) - (Real.cos t) ^ 4
            * deriv (fun s => u s / Real.cos s) t)
          ≤ (Real.cos t) ^ 3 * |deriv g t|
            + (Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t| := by
        have h1 : abs (-((Real.cos t) ^ 3 * deriv g t) - (Real.cos t) ^ 4
              * deriv (fun s => u s / Real.cos s) t)
            = abs (((Real.cos t) ^ 3 * deriv g t)
                + (Real.cos t) ^ 4 * deriv (fun s => u s / Real.cos s) t) := by
          rw [show -((Real.cos t) ^ 3 * deriv g t) - (Real.cos t) ^ 4
                * deriv (fun s => u s / Real.cos s) t
              = -(((Real.cos t) ^ 3 * deriv g t)
                + (Real.cos t) ^ 4 * deriv (fun s => u s / Real.cos s) t) by ring,
            abs_neg]
        rw [h1]
        calc abs (((Real.cos t) ^ 3 * deriv g t)
              + (Real.cos t) ^ 4 * deriv (fun s => u s / Real.cos s) t)
            ≤ |(Real.cos t) ^ 3 * deriv g t|
              + |(Real.cos t) ^ 4 * deriv (fun s => u s / Real.cos s) t| := abs_add_le _ _
          _ = (Real.cos t) ^ 3 * |deriv g t|
              + (Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hcos0 3),
                abs_of_nonneg (pow_nonneg hcos0 4)]
      have e3 : |4 * Real.sin t * (Real.cos t) ^ 3 * (u t / Real.cos t)|
          ≤ 4 * ((Real.cos t) ^ 3 * |u t / Real.cos t|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
          abs_of_nonneg (pow_nonneg hcos0 3)]
        have h := mul_le_mul_of_nonneg_right hsin1
          (by positivity : (0 : ℝ) ≤ 4 * (Real.cos t) ^ 3 * |u t / Real.cos t|)
        linarith [h]
      have hfin : abs (-((Real.cos t) ^ 3 * deriv g t) - (Real.cos t) ^ 4
            * deriv (fun s => u s / Real.cos s) t
            + 4 * Real.sin t * (Real.cos t) ^ 3 * (u t / Real.cos t))
          ≤ (Real.cos t) ^ 3 * |deriv g t|
            + ((Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t|
              + 4 * ((Real.cos t) ^ 3 * |u t / Real.cos t|)) :=
        le_trans e1 (le_trans (add_le_add e2 e3) (le_of_eq (by ring)))
      simpa only [Real.norm_eq_abs, abs_abs] using hfin
  -- ### the three terms, over the open tail
  have hGp_bd : (∫ t in Set.Ioo ν (Real.pi / 2), (Real.cos t) ^ 3 * |deriv g t|)
      ≤ Real.sqrt (Cw * DD) * (Real.pi / 2 - ν) ^ ((5 + γ) / 2) := by
    calc (∫ t in Set.Ioo ν (Real.pi / 2), (Real.cos t) ^ 3 * |deriv g t|)
        ≤ Real.sqrt (Cw * (∫ t in Set.Ioo ν (Real.pi / 2),
              (deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)))
            * (Real.pi / 2 - ν) ^ ((5 + γ) / 2) := hTailG.2
      _ ≤ Real.sqrt (Cw * DD) * (Real.pi / 2 - ν) ^ ((5 + γ) / 2) := by
          have hle : (∫ t in Set.Ioo ν (Real.pi / 2),
                (deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)) ≤ DD :=
            le_trans (MeasureTheory.setIntegral_mono_set hD
              (by
                filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
                exact mul_nonneg (sq_nonneg _) (sigma_nonneg γ ht.1 ht.2))
              (Filter.Eventually.of_forall fun t ht =>
                ⟨le_of_lt (by linarith [hν.1, ht.1, Real.pi_pos]), ht.2.le⟩)) hDD
          exact mul_le_mul_of_nonneg_right
            (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle hCw))
            (Real.rpow_nonneg (by linarith) _)
  have hv1_bd : (∫ t in Set.Ioo ν (Real.pi / 2),
        (Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t|)
      ≤ 4 * Kq * (Real.pi / 2 - ν) ^ (6 : ℝ)
        + Real.sqrt (Cw * GG) * (Real.pi / 2 - ν) ^ ((7 + γ) / 2) := by
    have hbdd : ∀ t ∈ Set.Ioo ν (Real.pi / 2),
        (Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t|
          ≤ 4 * Kq * (Real.pi / 2 - ν) ^ (5 : ℝ)
            + Real.sqrt (Cw * GG) * (Real.pi / 2 - ν) ^ ((5 + γ) / 2) := by
      intro t ht
      have ht0 : 0 < t := by linarith [hν.1, ht.1, Real.pi_pos]
      have hcos0 : 0 ≤ Real.cos t :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hν.1, ht.1, Real.pi_pos], ht.2.le⟩
      have hcosle : Real.cos t ≤ Real.pi / 2 - t := cos_le_pi_div_two_sub ht0.le ht.2.le
      have hxpos : 0 < Real.pi / 2 - t := by linarith [ht.2]
      have hx0 : 0 ≤ Real.pi / 2 - t := hxpos.le
      have hxε : Real.pi / 2 - t ≤ Real.pi / 2 - ν := by linarith [ht.1]
      have hIt : t ∈ Set.Ico (Real.pi / 4) (Real.pi / 2) :=
        ⟨by linarith [hν.1, ht.1], ht.2⟩
      have heq : (Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t|
          = Real.cos t * |(Real.cos t) ^ 3 * deriv (fun s => u s / Real.cos s) t| := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hcos0 3)]
        ring
      have h1 : Real.cos t * |(Real.cos t) ^ 3 * deriv (fun s => u s / Real.cos s) t|
          ≤ (Real.pi / 2 - t) * (4 * Kq * (Real.pi / 2 - t) ^ (4 : ℝ)
              + Real.sqrt (Cw * GG) * (Real.pi / 2 - t) ^ ((3 + γ) / 2)) :=
        mul_le_mul hcosle (hPsi1sharp t hIt)
          (abs_nonneg ((Real.cos t) ^ 3 * deriv (fun s => u s / Real.cos s) t)) hx0
      rw [cos_times_Psi1_bound (Kq := Kq) (GG := GG) (Cw := Cw) (γ := γ) hxpos] at h1
      have ha : 4 * Kq * (Real.pi / 2 - t) ^ (5 : ℝ)
          ≤ 4 * Kq * (Real.pi / 2 - ν) ^ (5 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0 hxε (by norm_num))
          (by linarith [hKq])
      have hb : Real.sqrt (Cw * GG) * (Real.pi / 2 - t) ^ ((5 + γ) / 2)
          ≤ Real.sqrt (Cw * GG) * (Real.pi / 2 - ν) ^ ((5 + γ) / 2) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0 hxε (by linarith [hγ1]))
          (Real.sqrt_nonneg _)
      linarith [h1, ha, hb]
    have hconst : MeasureTheory.IntegrableOn
        (fun _ : ℝ => 4 * Kq * (Real.pi / 2 - ν) ^ (5 : ℝ)
            + Real.sqrt (Cw * GG) * (Real.pi / 2 - ν) ^ ((5 + γ) / 2))
        (Set.Ioo ν (Real.pi / 2)) :=
      MeasureTheory.integrableOn_const
        (C := 4 * Kq * (Real.pi / 2 - ν) ^ (5 : ℝ)
            + Real.sqrt (Cw * GG) * (Real.pi / 2 - ν) ^ ((5 + γ) / 2)) (by
          rw [Real.volume_Ioo]
          exact ENNReal.ofReal_ne_top)
    have hmono : (∫ t in Set.Ioo ν (Real.pi / 2),
          (Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t|)
        ≤ ∫ t in Set.Ioo ν (Real.pi / 2),
            (4 * Kq * (Real.pi / 2 - ν) ^ (5 : ℝ)
              + Real.sqrt (Cw * GG) * (Real.pi / 2 - ν) ^ ((5 + γ) / 2)) :=
      MeasureTheory.integral_mono_of_nonneg
        (f := fun t => (Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t|)
        (g := fun _ : ℝ => 4 * Kq * (Real.pi / 2 - ν) ^ (5 : ℝ)
              + Real.sqrt (Cw * GG) * (Real.pi / 2 - ν) ^ ((5 + γ) / 2))
        (Filter.Eventually.of_forall fun t => by positivity) hconst
        (by
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
          exact hbdd t ht)
    rw [setIntegral_Ioo_const (by linarith : ν ≤ Real.pi / 2)] at hmono
    have hsplit : (4 * Kq * (Real.pi / 2 - ν) ^ (5 : ℝ)
          + Real.sqrt (Cw * GG) * (Real.pi / 2 - ν) ^ ((5 + γ) / 2)) * (Real.pi / 2 - ν)
        = 4 * Kq * (Real.pi / 2 - ν) ^ (6 : ℝ)
          + Real.sqrt (Cw * GG) * (Real.pi / 2 - ν) ^ ((7 + γ) / 2) := by
      rw [add_mul, mul_assoc (4 * Kq) ((Real.pi / 2 - ν) ^ (5 : ℝ)) (Real.pi / 2 - ν),
        rpow_five_mul (Real.pi / 2 - ν) hεpos,
        mul_assoc (Real.sqrt (Cw * GG)) ((Real.pi / 2 - ν) ^ ((5 + γ) / 2))
          (Real.pi / 2 - ν),
        rpow_half_gamma_mul (x := Real.pi / 2 - ν) (γ := γ) hεpos]
    rw [hsplit] at hmono
    exact hmono
  have hv_bd : (∫ t in Set.Ioo ν (Real.pi / 2),
        4 * ((Real.cos t) ^ 3 * |u t / Real.cos t|))
      ≤ 2 * Real.pi * Kq * (Real.pi / 2 - ν) ^ (4 : ℝ) := by
    have hbdd : ∀ t ∈ Set.Ioo ν (Real.pi / 2),
        4 * ((Real.cos t) ^ 3 * |u t / Real.cos t|)
          ≤ 2 * Real.pi * Kq * (Real.pi / 2 - ν) ^ (3 : ℝ) := by
      intro t ht
      have ht0 : 0 < t := by linarith [hν.1, ht.1, Real.pi_pos]
      have hcospos : 0 < Real.cos t :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hν.1, ht.1, Real.pi_pos], ht.2⟩
      have hcosge : (2 / Real.pi) * (Real.pi / 2 - t) ≤ Real.cos t :=
        two_div_pi_mul_le_cos ht0.le ht.2.le
      have hcosle : Real.cos t ≤ Real.pi / 2 - t := cos_le_pi_div_two_sub ht0.le ht.2.le
      have h1 := hub t ⟨ht0.le, ht.2.le⟩
      have hεt : 0 < Real.pi / 2 - t := by linarith [ht.2]
      rw [abs_div, abs_of_pos hcospos]
      have h2 : ((Real.pi / 2 - t) * Kq) / ((2 / Real.pi) * (Real.pi / 2 - t))
          = (Real.pi / 2) * Kq := by
        have hA : Real.pi / 2 - t ≠ 0 := ne_of_gt hεt
        rw [mul_comm (Real.pi / 2 - t) Kq, mul_div_mul_right Kq (2 / Real.pi) hA]
        have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
        field_simp
        try ring
      have hvb : |u t| / Real.cos t ≤ (Real.pi / 2) * Kq :=
        calc |u t| / Real.cos t ≤ ((Real.pi / 2 - t) * Kq) / Real.cos t :=
              div_le_div_of_nonneg_right h1 hcospos.le
          _ ≤ ((Real.pi / 2 - t) * Kq) / ((2 / Real.pi) * (Real.pi / 2 - t)) :=
              div_le_div_of_nonneg_left (mul_nonneg hεt.le hKq)
                (mul_pos (div_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) hεt) hcosge
          _ = (Real.pi / 2) * Kq := h2
      have hx0 : 0 ≤ Real.pi / 2 - t := hεt.le
      have hxε : Real.pi / 2 - t ≤ Real.pi / 2 - ν := by linarith [ht.1]
      have hcos3le : (Real.cos t) ^ 3 ≤ (Real.pi / 2 - t) ^ (3 : ℝ) := by
        have h3 := pow_le_pow_left₀ hcospos.le hcosle 3
        rwa [show (Real.pi / 2 - t) ^ (3 : ℕ) = (Real.pi / 2 - t) ^ (3 : ℝ) from
          (Real.rpow_natCast (Real.pi / 2 - t) 3).symm] at h3
      calc 4 * ((Real.cos t) ^ 3 * (|u t| / Real.cos t))
          ≤ 4 * ((Real.pi / 2 - t) ^ (3 : ℝ) * ((Real.pi / 2) * Kq)) := by
            have hpi2 : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
            have h := mul_le_mul hcos3le hvb (by positivity) (Real.rpow_nonneg hx0 3)
            exact mul_le_mul_of_nonneg_left h (by norm_num)
        _ ≤ 4 * ((Real.pi / 2 - ν) ^ (3 : ℝ) * ((Real.pi / 2) * Kq)) := by
            have hpi2 : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
            have h : (Real.pi / 2 - t) ^ (3 : ℝ) * ((Real.pi / 2) * Kq)
                ≤ (Real.pi / 2 - ν) ^ (3 : ℝ) * ((Real.pi / 2) * Kq) :=
              mul_le_mul_of_nonneg_right
                (Real.rpow_le_rpow hx0 hxε (show (0 : ℝ) ≤ 3 by norm_num))
                (mul_nonneg hpi2 hKq)
            exact mul_le_mul_of_nonneg_left h (by norm_num)
        _ = 2 * Real.pi * Kq * (Real.pi / 2 - ν) ^ (3 : ℝ) := by ring
    have hconst : MeasureTheory.IntegrableOn
        (fun _ : ℝ => 2 * Real.pi * Kq * (Real.pi / 2 - ν) ^ (3 : ℝ))
        (Set.Ioo ν (Real.pi / 2)) :=
      MeasureTheory.integrableOn_const
        (C := 2 * Real.pi * Kq * (Real.pi / 2 - ν) ^ (3 : ℝ)) (by
          rw [Real.volume_Ioo]
          exact ENNReal.ofReal_ne_top)
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (f := fun t => 4 * ((Real.cos t) ^ 3 * |u t / Real.cos t|))
      (g := fun _ : ℝ => 2 * Real.pi * Kq * (Real.pi / 2 - ν) ^ (3 : ℝ))
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
        have ht0 : 0 < t := by linarith [hν.1, ht.1, Real.pi_pos]
        have hc : 0 < Real.cos t :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [hν.1, ht.1, Real.pi_pos], ht.2⟩
        exact mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg hc.le 3) (abs_nonneg _)))
      hconst
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
        exact hbdd t ht)
    rw [setIntegral_Ioo_const (by linarith : ν ≤ Real.pi / 2)] at hmono
    have hsplit : (2 * Real.pi * Kq * (Real.pi / 2 - ν) ^ (3 : ℝ)) * (Real.pi / 2 - ν)
        = 2 * Real.pi * Kq * (Real.pi / 2 - ν) ^ (4 : ℝ) := by
      rw [mul_assoc (2 * Real.pi * Kq) ((Real.pi / 2 - ν) ^ (3 : ℝ)) (Real.pi / 2 - ν),
        rpow_three_mul (Real.pi / 2 - ν) hεpos]
    rw [hsplit] at hmono
    exact hmono
  -- ### assembly
  have hdecomp : (∫ t in Set.Ioo ν (Real.pi / 2),
        ((Real.cos t) ^ 3 * |deriv g t|
          + ((Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t|
            + 4 * ((Real.cos t) ^ 3 * |u t / Real.cos t|))))
      = (∫ t in Set.Ioo ν (Real.pi / 2), (Real.cos t) ^ 3 * |deriv g t|)
        + ((∫ t in Set.Ioo ν (Real.pi / 2),
              (Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t|)
          + ∫ t in Set.Ioo ν (Real.pi / 2), 4 * ((Real.cos t) ^ 3 * |u t / Real.cos t|)) := by
    have hA : (∫ t in Set.Ioo ν (Real.pi / 2),
          ((Real.cos t) ^ 3 * |deriv g t|
            + ((Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t|
              + 4 * ((Real.cos t) ^ 3 * |u t / Real.cos t|))))
        = (∫ t in Set.Ioo ν (Real.pi / 2), (Real.cos t) ^ 3 * |deriv g t|)
          + (∫ t in Set.Ioo ν (Real.pi / 2),
              ((Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t|
                + 4 * ((Real.cos t) ^ 3 * |u t / Real.cos t|))) :=
      MeasureTheory.integral_add hgpIoo (hv1Ioo.add hvIoo)
    have hB : (∫ t in Set.Ioo ν (Real.pi / 2),
              ((Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t|
                + 4 * ((Real.cos t) ^ 3 * |u t / Real.cos t|)))
        = (∫ t in Set.Ioo ν (Real.pi / 2),
              (Real.cos t) ^ 4 * |deriv (fun s => u s / Real.cos s) t|)
          + ∫ t in Set.Ioo ν (Real.pi / 2), 4 * ((Real.cos t) ^ 3 * |u t / Real.cos t|) :=
      MeasureTheory.integral_add hv1Ioo hvIoo
    rw [hA, hB]
  rw [hdecomp] at hstep1
  have hIocEq : (∫ t in Set.Ioc ν (Real.pi / 2),
        abs (-((Real.cos t) ^ 3 * deriv g t) - (Real.cos t) ^ 4
          * deriv (fun s => u s / Real.cos s) t
          + 4 * Real.sin t * (Real.cos t) ^ 3 * (u t / Real.cos t)))
      = ∫ t in Set.Ioo ν (Real.pi / 2),
        abs (-((Real.cos t) ^ 3 * deriv g t) - (Real.cos t) ^ 4
          * deriv (fun s => u s / Real.cos s) t
          + 4 * Real.sin t * (Real.cos t) ^ 3 * (u t / Real.cos t)) :=
    setIntegral_Ioc_eq_Ioo
  rw [hIocEq] at hkey
  linarith [hkey, hstep1, hGp_bd, hv1_bd, hv_bd]

private lemma final_arith {Cw Cs GG DD B2 A1 A0 Kq P1 P2 ε γ : ℝ}
    (hCw : 0 ≤ Cw) (hCs : 0 ≤ Cs) (hGG : 0 ≤ GG) (hDD : 0 ≤ DD) (hB2 : 0 ≤ B2)
    (hA1 : 0 ≤ A1) (hA0 : 0 ≤ A0) (hKq : 0 ≤ Kq)
    (hKq2 : Kq ^ 2 ≤ 2 * Cs ^ 2 * (B2 + A1))
    (he1 : Cw * ε ^ (-(3 + γ)) * P1 ^ 2 ≤ 32 * Cw ^ 2 * Kq ^ 2 + 2 * Cw ^ 2 * GG)
    (he2 : Cw * ε ^ (-(5 + γ)) * P2 ^ 2 ≤ 4 * Cw ^ 2 * DD + 64 * Cw ^ 2 * Kq ^ 2
      + 4 * Cw ^ 2 * GG + 16 * Real.pi ^ 2 * Cw ^ 2 * Kq ^ 2)
    (hpi2 : Real.pi ^ 2 ≤ 16) :
    Cw * ε ^ (-(3 + γ)) * P1 ^ 2 + Cw * ε ^ (-(5 + γ)) * P2 ^ 2
      ≤ 1000000 * (Cw ^ 2 + 1) * (Cs ^ 2 + 1) * (DD + B2 + A1 + A0 + GG) := by
  have hKnn : 0 ≤ (Cw ^ 2 + 1) * (Cs ^ 2 + 1) := by positivity
  have hsum : 0 ≤ DD + B2 + A1 + A0 + GG := by linarith
  have hBs : 0 ≤ B2 + A1 := by linarith
  have hcs : Cw ^ 2 * Cs ^ 2 ≤ (Cw ^ 2 + 1) * (Cs ^ 2 + 1) := by
    nlinarith [sq_nonneg Cw, sq_nonneg Cs]
  have hcw : Cw ^ 2 ≤ (Cw ^ 2 + 1) * (Cs ^ 2 + 1) := by
    nlinarith [sq_nonneg Cw, sq_nonneg Cs]
  have hpi3 : 16 * Real.pi ^ 2 * Cw ^ 2 * Kq ^ 2 ≤ 256 * Cw ^ 2 * Kq ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hpi2 (by positivity : (0 : ℝ) ≤ Cw ^ 2 * Kq ^ 2)
    linarith [h]
  have h1 : Cw * ε ^ (-(3 + γ)) * P1 ^ 2 + Cw * ε ^ (-(5 + γ)) * P2 ^ 2
      ≤ 400 * Cw ^ 2 * Kq ^ 2 + 6 * Cw ^ 2 * GG + 4 * Cw ^ 2 * DD := by
    nlinarith [he1, he2, hpi3, hCw, sq_nonneg Cw, sq_nonneg Kq]
  have h2 : 400 * Cw ^ 2 * Kq ^ 2 ≤ 800 * ((Cw ^ 2 + 1) * (Cs ^ 2 + 1)) * (B2 + A1) := by
    have ha : Cw ^ 2 * Kq ^ 2 ≤ Cw ^ 2 * (2 * Cs ^ 2 * (B2 + A1)) :=
      mul_le_mul_of_nonneg_left hKq2 (by positivity)
    have hb : Cw ^ 2 * (2 * Cs ^ 2 * (B2 + A1)) = 2 * (Cw ^ 2 * Cs ^ 2) * (B2 + A1) := by ring
    have hc : 2 * (Cw ^ 2 * Cs ^ 2) * (B2 + A1)
        ≤ 2 * ((Cw ^ 2 + 1) * (Cs ^ 2 + 1)) * (B2 + A1) := by
      have hd := mul_le_mul_of_nonneg_right hcs hBs
      linarith [hd]
    linarith [ha, hb, hc]
  have h3 : 6 * (Cw ^ 2 * GG) ≤ 6 * ((Cw ^ 2 + 1) * (Cs ^ 2 + 1)) * GG := by
    have hd := mul_le_mul_of_nonneg_right hcw hGG
    linarith [hd]
  have h4 : 4 * (Cw ^ 2 * DD) ≤ 4 * ((Cw ^ 2 + 1) * (Cs ^ 2 + 1)) * DD := by
    have hd := mul_le_mul_of_nonneg_right hcw hDD
    linarith [hd]
  have h5 : 800 * ((Cw ^ 2 + 1) * (Cs ^ 2 + 1)) * (B2 + A1)
        + 6 * ((Cw ^ 2 + 1) * (Cs ^ 2 + 1)) * GG + 4 * ((Cw ^ 2 + 1) * (Cs ^ 2 + 1)) * DD
      ≤ 1000000 * ((Cw ^ 2 + 1) * (Cs ^ 2 + 1)) * (DD + B2 + A1 + A0 + GG) := by
    have hB2' : B2 + A1 ≤ DD + B2 + A1 + A0 + GG := by linarith
    have hGG' : GG ≤ DD + B2 + A1 + A0 + GG := by linarith
    have hDD' : DD ≤ DD + B2 + A1 + A0 + GG := by linarith
    have hb1 := mul_le_mul_of_nonneg_left hB2' (by positivity : (0 : ℝ) ≤ 800 * ((Cw ^ 2 + 1) * (Cs ^ 2 + 1)))
    have hb2 := mul_le_mul_of_nonneg_left hGG' (by positivity : (0 : ℝ) ≤ 6 * ((Cw ^ 2 + 1) * (Cs ^ 2 + 1)))
    have hb3 := mul_le_mul_of_nonneg_left hDD' (by positivity : (0 : ℝ) ≤ 4 * ((Cw ^ 2 + 1) * (Cs ^ 2 + 1)))
    have hcoe : (810 : ℝ) * ((Cw ^ 2 + 1) * (Cs ^ 2 + 1)) * (DD + B2 + A1 + A0 + GG)
        ≤ 1000000 * ((Cw ^ 2 + 1) * (Cs ^ 2 + 1)) * (DD + B2 + A1 + A0 + GG) := by
      have h6 : (810 : ℝ) * ((Cw ^ 2 + 1) * (Cs ^ 2 + 1))
          ≤ 1000000 * ((Cw ^ 2 + 1) * (Cs ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_right (by norm_num) hKnn
      exact mul_le_mul_of_nonneg_right h6 hsum
    linarith [hb1, hb2, hb3, hcoe]
  linarith [h1, h2, h3, h4, h5]

/-- `Kq ^ 2 ≤ 2 Cs ^ 2 (B2 + A1)` for `Kq = Cs (√B2 + √A1)`. -/
private lemma Kq_sq_le {Cs B2 A1 Kq : ℝ} (hCs : 0 ≤ Cs) (hB2 : 0 ≤ B2) (hA1 : 0 ≤ A1)
    (hKq : Kq = Cs * (Real.sqrt B2 + Real.sqrt A1)) :
    Kq ^ 2 ≤ 2 * Cs ^ 2 * (B2 + A1) := by
  rw [hKq]
  have h := two_sq_le (Real.sqrt B2) (Real.sqrt A1)
  have hB := Real.sq_sqrt hB2
  have hA := Real.sq_sqrt hA1
  nlinarith [h, hB, hA, sq_nonneg Cs, hCs]

/-- `π ^ 2 ≤ 16`. -/
private lemma pi_sq_le_sixteen : Real.pi ^ 2 ≤ 16 := by
  nlinarith [Real.pi_lt_four, Real.pi_pos]

private lemma est1 (γ Cw Kq GG ε P1 : ℝ) (hCw : 0 ≤ Cw) (hKq : 0 ≤ Kq) (hGG : 0 ≤ GG)
    (hε : 0 < ε) (hε5 : ε ^ (5 - γ) ≤ Cw)
    (hP1 : P1 ^ 2 ≤ 2 * (16 * Kq ^ 2 * (ε ^ (4 : ℝ) * ε ^ (4 : ℝ))
        + (Cw * GG) * (ε ^ ((3 + γ) / 2) * ε ^ ((3 + γ) / 2))))
    (hcomb1 : ε ^ (-(3 + γ)) * (ε ^ (4 : ℝ) * ε ^ (4 : ℝ)) = ε ^ (5 - γ))
    (hcomb2 : ε ^ (-(3 + γ)) * (ε ^ ((3 + γ) / 2) * ε ^ ((3 + γ) / 2)) = 1) :
    Cw * ε ^ (-(3 + γ)) * P1 ^ 2 ≤ 32 * Cw ^ 2 * Kq ^ 2 + 2 * Cw ^ 2 * GG := by
  have h2 : ε ^ (-(3 + γ)) * (2 * (16 * Kq ^ 2 * (ε ^ (4 : ℝ) * ε ^ (4 : ℝ))
      + (Cw * GG) * (ε ^ ((3 + γ) / 2) * ε ^ ((3 + γ) / 2))))
      = 2 * (16 * Kq ^ 2 * (ε ^ (-(3 + γ)) * (ε ^ (4 : ℝ) * ε ^ (4 : ℝ)))
          + Cw * GG * (ε ^ (-(3 + γ)) * (ε ^ ((3 + γ) / 2) * ε ^ ((3 + γ) / 2)))) := by ring
  have h1 := mul_le_mul_of_nonneg_left hP1 (Real.rpow_nonneg hε.le (-(3 + γ)))
  rw [h2, hcomb1, hcomb2] at h1
  simp only [mul_one] at h1
  have h3 := mul_le_mul_of_nonneg_left h1 hCw
  have h4 : Cw * (2 * (16 * Kq ^ 2 * ε ^ (5 - γ) + Cw * GG))
      ≤ 32 * Cw ^ 2 * Kq ^ 2 + 2 * Cw ^ 2 * GG := by
    have ha : Kq ^ 2 * ε ^ (5 - γ) ≤ Kq ^ 2 * Cw := mul_le_mul_of_nonneg_left hε5 (sq_nonneg Kq)
    nlinarith [ha, hCw, hGG, hKq, sq_nonneg Kq]
  linarith [h3, h4]

/-- The second term of the final estimate. -/
private lemma est2 (γ Cw Kq GG DD ε P2 : ℝ) (hCw : 0 ≤ Cw) (hKq : 0 ≤ Kq) (hGG : 0 ≤ GG)
    (hDD : 0 ≤ DD) (hε : 0 < ε) (hε3 : ε ^ (3 - γ) ≤ Cw) (hε7 : ε ^ (7 - γ) ≤ Cw)
    (hε2 : ε ^ (2 : ℝ) ≤ 1)
    (hP2 : P2 ^ 2 ≤ 4 * (Cw * DD * (ε ^ ((5 + γ) / 2) * ε ^ ((5 + γ) / 2))
        + 16 * Kq ^ 2 * (ε ^ (6 : ℝ) * ε ^ (6 : ℝ))
        + Cw * GG * (ε ^ ((7 + γ) / 2) * ε ^ ((7 + γ) / 2))
        + 4 * (Real.pi * Kq) ^ 2 * (ε ^ (4 : ℝ) * ε ^ (4 : ℝ))))
    (hcomb3 : ε ^ (-(5 + γ)) * (ε ^ ((5 + γ) / 2) * ε ^ ((5 + γ) / 2)) = 1)
    (hcomb4 : ε ^ (-(5 + γ)) * (ε ^ (6 : ℝ) * ε ^ (6 : ℝ)) = ε ^ (7 - γ))
    (hcomb5 : ε ^ (-(5 + γ)) * (ε ^ ((7 + γ) / 2) * ε ^ ((7 + γ) / 2)) = ε ^ (2 : ℝ))
    (hcomb6 : ε ^ (-(5 + γ)) * (ε ^ (4 : ℝ) * ε ^ (4 : ℝ)) = ε ^ (3 - γ)) :
    Cw * ε ^ (-(5 + γ)) * P2 ^ 2 ≤ 4 * Cw ^ 2 * DD + 64 * Cw ^ 2 * Kq ^ 2 + 4 * Cw ^ 2 * GG
      + 16 * Real.pi ^ 2 * Cw ^ 2 * Kq ^ 2 := by
  have h2 : ε ^ (-(5 + γ)) * (4 * (Cw * DD * (ε ^ ((5 + γ) / 2) * ε ^ ((5 + γ) / 2))
      + 16 * Kq ^ 2 * (ε ^ (6 : ℝ) * ε ^ (6 : ℝ))
      + Cw * GG * (ε ^ ((7 + γ) / 2) * ε ^ ((7 + γ) / 2))
      + 4 * (Real.pi * Kq) ^ 2 * (ε ^ (4 : ℝ) * ε ^ (4 : ℝ))))
      = 4 * (Cw * DD * (ε ^ (-(5 + γ)) * (ε ^ ((5 + γ) / 2) * ε ^ ((5 + γ) / 2)))
          + 16 * Kq ^ 2 * (ε ^ (-(5 + γ)) * (ε ^ (6 : ℝ) * ε ^ (6 : ℝ)))
          + Cw * GG * (ε ^ (-(5 + γ)) * (ε ^ ((7 + γ) / 2) * ε ^ ((7 + γ) / 2)))
          + 4 * (Real.pi * Kq) ^ 2 * (ε ^ (-(5 + γ)) * (ε ^ (4 : ℝ) * ε ^ (4 : ℝ)))) := by ring
  have h1 := mul_le_mul_of_nonneg_left hP2 (Real.rpow_nonneg hε.le (-(5 + γ)))
  rw [h2, hcomb3, hcomb4, hcomb5, hcomb6] at h1
  simp only [mul_one] at h1
  have h3 := mul_le_mul_of_nonneg_left h1 hCw
  have h4 : Cw * (4 * (Cw * DD + 16 * Kq ^ 2 * ε ^ (7 - γ) + Cw * GG * ε ^ (2 : ℝ)
        + 4 * (Real.pi * Kq) ^ 2 * ε ^ (3 - γ)))
      ≤ 4 * Cw ^ 2 * DD + 64 * Cw ^ 2 * Kq ^ 2 + 4 * Cw ^ 2 * GG
        + 16 * Real.pi ^ 2 * Cw ^ 2 * Kq ^ 2 := by
    have hb : 16 * Kq ^ 2 * ε ^ (7 - γ) ≤ 16 * Kq ^ 2 * Cw :=
      mul_le_mul_of_nonneg_left hε7 (by positivity)
    have hc : Cw * GG * ε ^ (2 : ℝ) ≤ Cw * GG * 1 :=
      mul_le_mul_of_nonneg_left hε2 (by positivity)
    have hd : 4 * (Real.pi * Kq) ^ 2 * ε ^ (3 - γ) ≤ 4 * (Real.pi * Kq) ^ 2 * Cw :=
      mul_le_mul_of_nonneg_left hε3 (by positivity)
    have hb' : Cw * (16 * Kq ^ 2 * ε ^ (7 - γ)) ≤ Cw * (16 * Kq ^ 2 * Cw) :=
      mul_le_mul_of_nonneg_left hb hCw
    have hc' : Cw * (Cw * GG * ε ^ (2 : ℝ)) ≤ Cw * (Cw * GG * 1) :=
      mul_le_mul_of_nonneg_left hc hCw
    have hd' : Cw * (4 * (Real.pi * Kq) ^ 2 * ε ^ (3 - γ))
        ≤ Cw * (4 * (Real.pi * Kq) ^ 2 * Cw) :=
      mul_le_mul_of_nonneg_left hd hCw
    nlinarith [hb', hc', hd', hCw, hGG, hDD, sq_nonneg Kq, sq_nonneg (Real.pi * Kq),
      Real.pi_pos]
  linarith [h3, h4]

theorem slice_bd_ptwise (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u g : ℝ → ℝ),
      ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
      ∀ θ ∈ Set.Icc (Real.pi / 4) (Real.pi / 2),
        Real.rpow (Real.sin (2 * θ)) (2 - γ) * Real.cos θ *
          ((deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2
            + (deriv (fun t => u t / Real.cos t) θ) ^ 2)
        ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
            + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
            + (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))) := by
  obtain ⟨Cw, hCwpos, hw⟩ := weights_local γ hγ1 hγ2
  obtain ⟨Cs, hCspos, hsup⟩ := slice_bd_sup_bounds
  have hCwnn : 0 ≤ Cw := hCwpos.le
  have hCsnn : 0 ≤ Cs := hCspos.le
  refine ⟨1000000 * (Cw ^ 2 + 1) * (Cs ^ 2 + 1), by positivity, ?_⟩
  intro u g hu hcont hu0 hupi hg hA2 hA1 hA0 hD hG2 hY2 θ hθ
  -- ### abbreviations
  set B2 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    with hB2def
  set A1 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 with hA1def
  set A0 : ℝ := ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 with hA0def
  set GG : ℝ := ∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
    with hGGdef
  set DD : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
    with hDDdef
  have hB2nn : 0 ≤ B2 := by
    rw [hB2def]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun x hx =>
      mul_nonneg (sq_nonneg _) (sEta_nonneg hx.1 hx.2)
  have hA1nn : 0 ≤ A1 := by
    rw [hA1def]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun x _ => sq_nonneg _
  have hA0nn : 0 ≤ A0 := by
    rw [hA0def]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun x _ => sq_nonneg _
  have hGGnn : 0 ≤ GG := by
    rw [hGGdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun x hx =>
      mul_nonneg (sq_nonneg _) (sigma_nonneg γ hx.1 hx.2)
  have hDDnn : 0 ≤ DD := by
    rw [hDDdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun x hx =>
      mul_nonneg (sq_nonneg _) (sigma_nonneg γ hx.1 hx.2)
  -- ### the two pointwise bounds from the weighted `L²` data
  have hs := hsup u hu hcont hupi hA2 hA1
  have hKu : ∀ η ∈ Work.Spaces.Iθ, |deriv u η| ≤ Cs * (Real.sqrt B2 + Real.sqrt A1) := by
    intro η hη
    have h1 := hs.1 η hη
    rw [hB2def, hA1def]
    exact h1
  have hu_bound : ∀ η ∈ Work.Spaces.Iθ,
      |u η| ≤ (Real.pi / 2 - η) * Cs * (Real.sqrt B2 + Real.sqrt A1) := by
    intro η hη
    have h2 := hs.2 η hη
    rw [hB2def, hA1def]
    exact h2
  have hKqnn : 0 ≤ Cs * (Real.sqrt B2 + Real.sqrt A1) :=
    mul_nonneg hCsnn (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rcases eq_or_lt_of_le hθ.2 with hpi | hlt
  · -- trivial case `θ = π/2`
    rw [hpi]
    have hzero : Real.rpow (Real.sin (2 * (Real.pi / 2))) (2 - γ) = 0 := by
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      exact Real.zero_rpow (by linarith)
    rw [hzero, Real.cos_pi_div_two, zero_mul, zero_mul]
    exact mul_nonneg (by positivity)
      (by linarith [hA0nn, hB2nn, hA1nn, hGGnn, hDDnn])
  · -- main case `θ < π/2`
    have hεpos : 0 < Real.pi / 2 - θ := by linarith
    obtain ⟨hcosge, hcosle, hσc5, hσc7, hε3, hε5, -, -⟩ := hw θ ⟨hθ.1, hlt⟩
    -- the two `Ψ`-bounds
    set Kq0 : ℝ := Cs * (Real.sqrt B2 + Real.sqrt A1) with hKq0def
    have hKq0nn : 0 ≤ Kq0 := by rw [hKq0def]; exact hKqnn
    have hu_bd : ∀ η ∈ Work.Spaces.Iθ, |u η| ≤ (Real.pi / 2 - η) * Kq0 := by
      intro η hη
      have h := hu_bound η hη
      rw [hKq0def]
      simpa only [mul_assoc] using h
    have hI4fun : ∀ ν ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
        (∫ t in ν..(Real.pi / 2), (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ))
          ≤ Cw * (Real.pi / 2 - ν) ^ (3 + γ) := by
      intro ν hν
      obtain ⟨-, -, -, -, -, -, hI4ν, -⟩ := hw ν hν
      exact hI4ν
    have hI6fun : ∀ ν ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
        (∫ t in ν..(Real.pi / 2), (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ))
          ≤ Cw * (Real.pi / 2 - ν) ^ (5 + γ) := by
      intro ν hν
      obtain ⟨-, -, -, -, -, -, -, hI6ν⟩ := hw ν hν
      exact hI6ν
    obtain ⟨hPsi1bd, hPsi1sharp⟩ := Psi1_tail_le (γ := γ) (Cw := Cw) (Kq := Kq0) (GG := GG)
      hγ1 hγ2 hCwnn hKq0nn hu hcont hg hG2 hGGdef.ge hu_bd hI4fun
    have htail1 : |(Real.cos θ) ^ 3 * deriv (fun s => u s / Real.cos s) θ|
        ≤ 4 * (Cs * (Real.sqrt B2 + Real.sqrt A1)) * (Real.pi / 2 - θ) ^ (4 : ℝ)
          + Real.sqrt (Cw * GG) * (Real.pi / 2 - θ) ^ ((3 + γ) / 2) := by
      have h := hPsi1sharp θ ⟨hθ.1, hlt⟩
      rw [hKq0def] at h
      exact h
    have htail2 : |(Real.cos θ) ^ 4 * deriv (fun s => deriv (fun r => u r / Real.cos r) s) θ|
        ≤ Real.sqrt (Cw * DD) * (Real.pi / 2 - θ) ^ ((5 + γ) / 2)
          + 4 * (Cs * (Real.sqrt B2 + Real.sqrt A1)) * (Real.pi / 2 - θ) ^ (6 : ℝ)
          + Real.sqrt (Cw * GG) * (Real.pi / 2 - θ) ^ ((7 + γ) / 2)
          + 2 * Real.pi * (Cs * (Real.sqrt B2 + Real.sqrt A1)) * (Real.pi / 2 - θ) ^ (4 : ℝ) := by
      have hQb0 : 0 ≤ ∫ s in Set.Ioc (Real.pi / 8) (Real.pi / 2),
          |-(4 * u s + g s) * (Real.cos s) ^ 2| :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun s _ => abs_nonneg _
      have h := Psi2_tail_le (γ := γ) (Cw := Cw) (Kq := Kq0) (GG := GG) (DD := DD)
        (Qb := ∫ s in Set.Ioc (Real.pi / 8) (Real.pi / 2),
            |-(4 * u s + g s) * (Real.cos s) ^ 2|)
        hγ1 hγ2 hCwnn hKq0nn hQb0 hu hcont hg hD hDDdef.ge hu_bd hPsi1bd
        (fun t ht => by
          have h2 := hPsi1sharp t ht
          rw [hKq0def] at h2
          exact h2)
        hI6fun θ ⟨hθ.1, hlt⟩
      rw [hKq0def] at h
      exact h
    -- ### assembly
    set ε : ℝ := Real.pi / 2 - θ with hεdef
    set Kq : ℝ := Cs * (Real.sqrt B2 + Real.sqrt A1) with hKqdef
    have hεpos' : 0 < ε := by rw [hεdef]; exact hεpos
    have hKqnn' : 0 ≤ Kq := by rw [hKqdef]; exact hKqnn
    have hcospos : 0 < Real.cos θ := cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hlt⟩
    have hcosne : Real.cos θ ≠ 0 := ne_of_gt hcospos
    -- rewrite `v'` and `v''` through `Ψ₁`, `Ψ₂`
    have hv1 : deriv (fun t => u t / Real.cos t) θ
        = ((Real.cos θ) ^ 3 * deriv (fun s => u s / Real.cos s) θ) / (Real.cos θ) ^ 3 := by
      field_simp
    have hv2 : deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
        = ((Real.cos θ) ^ 4 * deriv (fun s => deriv (fun r => u r / Real.cos r) s) θ)
            / (Real.cos θ) ^ 4 := by
      field_simp
    rw [hv1, hv2, mul_add]
    set P1 : ℝ := (Real.cos θ) ^ 3 * deriv (fun s => u s / Real.cos s) θ with hP1def
    set P2 : ℝ := (Real.cos θ) ^ 4 * deriv (fun s => deriv (fun r => u r / Real.cos r) s) θ
      with hP2def
    have hP1b : |P1| ≤ 4 * Kq * ε ^ (4 : ℝ) + Real.sqrt (Cw * GG) * ε ^ ((3 + γ) / 2) := by
      rw [hP1def, hKqdef, hεdef]
      exact htail1
    have hP2b : |P2| ≤ Real.sqrt (Cw * DD) * ε ^ ((5 + γ) / 2) + 4 * Kq * ε ^ (6 : ℝ)
        + Real.sqrt (Cw * GG) * ε ^ ((7 + γ) / 2) + 2 * Real.pi * Kq * ε ^ (4 : ℝ) := by
      rw [hP2def, hKqdef, hεdef]
      exact htail2
    have key1 : Real.rpow (Real.sin (2 * θ)) (2 - γ) * Real.cos θ * (P1 / (Real.cos θ) ^ 3) ^ 2
        = (Real.rpow (Real.sin (2 * θ)) (2 - γ) / (Real.cos θ) ^ 5) * P1 ^ 2 := by
      field_simp
    have key2 : Real.rpow (Real.sin (2 * θ)) (2 - γ) * Real.cos θ * (P2 / (Real.cos θ) ^ 4) ^ 2
        = (Real.rpow (Real.sin (2 * θ)) (2 - γ) / (Real.cos θ) ^ 7) * P2 ^ 2 := by
      field_simp
    rw [key1, key2]
    have hEE : ε ^ (4 : ℝ) * ε ^ (4 : ℝ) = ε ^ (4 : ℝ) * ε ^ (4 : ℝ) := rfl
    have hA1' : (4 * Kq * ε ^ (4 : ℝ)) ^ 2 = 16 * Kq ^ 2 * (ε ^ (4 : ℝ) * ε ^ (4 : ℝ)) := by
      ring
    have hB1' : (Real.sqrt (Cw * GG) * ε ^ ((3 + γ) / 2)) ^ 2
        = Cw * GG * (ε ^ ((3 + γ) / 2) * ε ^ ((3 + γ) / 2)) := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Cw * GG), pow_two]
    have hP1sq : P1 ^ 2 ≤ 2 * (16 * Kq ^ 2 * (ε ^ (4 : ℝ) * ε ^ (4 : ℝ))
        + (Cw * GG) * (ε ^ ((3 + γ) / 2) * ε ^ ((3 + γ) / 2))) := by
      have hraw : P1 ^ 2 ≤ 2 * ((4 * Kq * ε ^ (4 : ℝ)) ^ 2
          + (Real.sqrt (Cw * GG) * ε ^ ((3 + γ) / 2)) ^ 2) := by
        calc P1 ^ 2 = |P1| ^ 2 := (sq_abs P1).symm
          _ ≤ (4 * Kq * ε ^ (4 : ℝ) + Real.sqrt (Cw * GG) * ε ^ ((3 + γ) / 2)) ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg P1) hP1b 2
          _ ≤ 2 * ((4 * Kq * ε ^ (4 : ℝ)) ^ 2
                + (Real.sqrt (Cw * GG) * ε ^ ((3 + γ) / 2)) ^ 2) := two_sq_le _ _
      rw [hA1', hB1'] at hraw
      exact hraw
    have hA2' : (Real.sqrt (Cw * DD) * ε ^ ((5 + γ) / 2)) ^ 2
        = Cw * DD * (ε ^ ((5 + γ) / 2) * ε ^ ((5 + γ) / 2)) := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Cw * DD), pow_two]
    have hB2' : (4 * Kq * ε ^ (6 : ℝ)) ^ 2 = 16 * Kq ^ 2 * (ε ^ (6 : ℝ) * ε ^ (6 : ℝ)) := by
      ring
    have hC2' : (Real.sqrt (Cw * GG) * ε ^ ((7 + γ) / 2)) ^ 2
        = Cw * GG * (ε ^ ((7 + γ) / 2) * ε ^ ((7 + γ) / 2)) := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Cw * GG), pow_two]
    have hD2' : (2 * Real.pi * Kq * ε ^ (4 : ℝ)) ^ 2
        = 4 * (Real.pi * Kq) ^ 2 * (ε ^ (4 : ℝ) * ε ^ (4 : ℝ)) := by
      ring
    have hP2sq : P2 ^ 2 ≤ 4 * (Cw * DD * (ε ^ ((5 + γ) / 2) * ε ^ ((5 + γ) / 2))
        + 16 * Kq ^ 2 * (ε ^ (6 : ℝ) * ε ^ (6 : ℝ))
        + Cw * GG * (ε ^ ((7 + γ) / 2) * ε ^ ((7 + γ) / 2))
        + 4 * (Real.pi * Kq) ^ 2 * (ε ^ (4 : ℝ) * ε ^ (4 : ℝ))) := by
      have hraw : P2 ^ 2 ≤ 4 * ((Real.sqrt (Cw * DD) * ε ^ ((5 + γ) / 2)) ^ 2
          + (4 * Kq * ε ^ (6 : ℝ)) ^ 2 + (Real.sqrt (Cw * GG) * ε ^ ((7 + γ) / 2)) ^ 2
          + (2 * Real.pi * Kq * ε ^ (4 : ℝ)) ^ 2) := by
        calc P2 ^ 2 = |P2| ^ 2 := (sq_abs P2).symm
          _ ≤ (Real.sqrt (Cw * DD) * ε ^ ((5 + γ) / 2) + 4 * Kq * ε ^ (6 : ℝ)
                + Real.sqrt (Cw * GG) * ε ^ ((7 + γ) / 2) + 2 * Real.pi * Kq * ε ^ (4 : ℝ)) ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg P2) hP2b 2
          _ ≤ 4 * ((Real.sqrt (Cw * DD) * ε ^ ((5 + γ) / 2)) ^ 2
                + (4 * Kq * ε ^ (6 : ℝ)) ^ 2 + (Real.sqrt (Cw * GG) * ε ^ ((7 + γ) / 2)) ^ 2
                + (2 * Real.pi * Kq * ε ^ (4 : ℝ)) ^ 2) := four_sq_le _ _ _ _
      rw [hA2', hB2', hC2', hD2'] at hraw
      exact hraw
    have hεle1 : ε ≤ 1 := by rw [hεdef]; linarith [hθ.1, Real.pi_lt_four]
    have hε2 : ε ^ (2 : ℝ) ≤ 1 := Real.rpow_le_one hεpos'.le hεle1 (by norm_num)
    have hcomb1 : ε ^ (-(3 + γ)) * (ε ^ (4 : ℝ) * ε ^ (4 : ℝ)) = ε ^ (5 - γ) := by
      rw [← Real.rpow_add hεpos', ← Real.rpow_add hεpos']
      congr 1
      ring
    have hcomb2 : ε ^ (-(3 + γ)) * (ε ^ ((3 + γ) / 2) * ε ^ ((3 + γ) / 2)) = 1 := by
      have h0 : ε ^ (-(3 + γ)) * (ε ^ ((3 + γ) / 2) * ε ^ ((3 + γ) / 2)) = ε ^ (0 : ℝ) := by
        rw [← Real.rpow_add hεpos', ← Real.rpow_add hεpos']
        congr 1
        ring
      rw [h0, Real.rpow_zero]
    have hcomb3 : ε ^ (-(5 + γ)) * (ε ^ ((5 + γ) / 2) * ε ^ ((5 + γ) / 2)) = 1 := by
      have h0 : ε ^ (-(5 + γ)) * (ε ^ ((5 + γ) / 2) * ε ^ ((5 + γ) / 2)) = ε ^ (0 : ℝ) := by
        rw [← Real.rpow_add hεpos', ← Real.rpow_add hεpos']
        congr 1
        ring
      rw [h0, Real.rpow_zero]
    have hcomb4 : ε ^ (-(5 + γ)) * (ε ^ (6 : ℝ) * ε ^ (6 : ℝ)) = ε ^ (7 - γ) := by
      rw [← Real.rpow_add hεpos', ← Real.rpow_add hεpos']
      congr 1
      ring
    have hcomb5 : ε ^ (-(5 + γ)) * (ε ^ ((7 + γ) / 2) * ε ^ ((7 + γ) / 2)) = ε ^ (2 : ℝ) := by
      rw [← Real.rpow_add hεpos', ← Real.rpow_add hεpos']
      congr 1
      ring
    have hcomb6 : ε ^ (-(5 + γ)) * (ε ^ (4 : ℝ) * ε ^ (4 : ℝ)) = ε ^ (3 - γ) := by
      rw [← Real.rpow_add hεpos', ← Real.rpow_add hεpos']
      congr 1
      ring
    have hε7 : ε ^ (7 - γ) ≤ Cw := by
      have h : ε ^ (7 - γ) = ε ^ (5 - γ) * ε ^ (2 : ℝ) := by
        rw [← Real.rpow_add hεpos']
        congr 1
        ring
      rw [h]
      have hb := mul_le_mul hε5 hε2 (by positivity) hCwnn
      simpa using hb
    have he1 : Cw * ε ^ (-(3 + γ)) * P1 ^ 2 ≤ 32 * Cw ^ 2 * Kq ^ 2 + 2 * Cw ^ 2 * GG :=
      est1 γ Cw Kq GG ε P1 hCwnn hKqnn' hGGnn hεpos' hε5 hP1sq hcomb1 hcomb2
    have he2 : Cw * ε ^ (-(5 + γ)) * P2 ^ 2
        ≤ 4 * Cw ^ 2 * DD + 64 * Cw ^ 2 * Kq ^ 2 + 4 * Cw ^ 2 * GG
          + 16 * Real.pi ^ 2 * Cw ^ 2 * Kq ^ 2 :=
      est2 γ Cw Kq GG DD ε P2 hCwnn hKqnn' hGGnn hDDnn hεpos' hε3 hε7 hε2 hP2sq hcomb3 hcomb4 hcomb5 hcomb6
    have hKq2 : Kq ^ 2 ≤ 2 * Cs ^ 2 * (B2 + A1) :=
      Kq_sq_le hCsnn hB2nn hA1nn hKqdef
    have hpi2 : Real.pi ^ 2 ≤ 16 := pi_sq_le_sixteen
    have hfinal1 : Real.rpow (Real.sin (2 * θ)) (2 - γ) / (Real.cos θ) ^ 7 * P2 ^ 2
          + Real.rpow (Real.sin (2 * θ)) (2 - γ) / (Real.cos θ) ^ 5 * P1 ^ 2
        ≤ Cw * ε ^ (-(5 + γ)) * P2 ^ 2 + Cw * ε ^ (-(3 + γ)) * P1 ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_right hσc7 (sq_nonneg _))
        (mul_le_mul_of_nonneg_right hσc5 (sq_nonneg _))
    have hfinal2 := final_arith hCwnn hCsnn hGGnn hDDnn hB2nn hA1nn hA0nn hKqnn' hKq2 he1 he2 hpi2
    exact le_trans hfinal1 (by simpa only [add_comm] using hfinal2)

end Work.FTS.EllipticEst.remov
