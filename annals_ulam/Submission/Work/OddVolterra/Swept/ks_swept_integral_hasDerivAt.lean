import Mathlib
import Submission.Work.OddVolterra.Swept.ksSmooth
import Submission.Work.OddVolterra.Swept.ksBounds
import Submission.Work.OddVolterra.Swept.SweptCore

/-!
# Differentiation of the swept `ks`-integral

For `p = n + 1/2` and `j ≤ n`, the function `x' ↦ ∫_σ in x'..b, ks A p j x' σ` has derivative
`∫_σ in x..b, ks A p (j+1) x σ` at `x`.

The proof goes through the `v`-form `Gfun` of the kernel (`σ = u + (b-u)v²`): on the compact box
`[0,1] × [x-η, x+η]` the integrand `Gfun n A b j u v` and all its `u`-derivatives are smooth, so
differentiation under the integral sign is the standard parametric-integral lemma with a constant
bound.  The resulting integrand `2v·Dkt n A b j x (v²)` differs from `Gfun n A b (j+1) x v` by the
total `v`-derivative `Hkt n A b j x v` of `(1-v²)kt_j(x,(b-x)v²)`, which integrates to zero.
-/

noncomputable section

set_option maxHeartbeats 16000000

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Swept

open Work.OddVolterra
open Filter

/-! ## The working region -/

/-- The region of `u`-values on which the `v`-form is used: `u` is within `δ/2` of `s` and below
`b`, so that the whole segment `σ ∈ [u,b]` lies in the smoothness region. -/
def Vset (s b δ : ℝ) : Set ℝ := Set.Ioo (s - δ / 2) (s + δ / 2) ∩ Set.Iio b

theorem isOpen_Vset (s b δ : ℝ) : IsOpen (Vset s b δ) := isOpen_Ioo.inter isOpen_Iio

theorem lt_b_of_mem_Vset {s b δ u : ℝ} (hu : u ∈ Vset s b δ) : u < b := hu.2

theorem mem_Rset_of_mem_Vset {s b δ : ℝ} (hsb : s < b) (hδ : 0 < δ) {u : ℝ}
    (hu : u ∈ Vset s b δ) {w : ℝ} (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    (u, u + (b - u) * w) ∈ Rset s b δ := by
  obtain ⟨⟨h1, h2⟩, hub⟩ := hu
  have hb : u < b := hub
  show u ∈ Set.Ioo (s - δ) (s + δ) ∧ u + (b - u) * w ∈ Set.Ioo (s - δ) (b + δ)
  refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
  · have h : 0 ≤ (b - u) * w := mul_nonneg (by linarith) hw
    linarith
  · have h : (b - u) * w ≤ b - u := mul_le_of_le_one_right (by linarith) hw1
    linarith

theorem mem_Os_of_mem_Vset {s b δ : ℝ} (hsb : s < b) (hδ : 0 < δ) {u : ℝ}
    (hu : u ∈ Vset s b δ) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : (u, v) ∈ Os s b δ := by
  obtain ⟨⟨h1, h2⟩, hub⟩ := hu
  have hb : u < b := hub
  have h3 : 0 ≤ (b - u) * v ^ 2 := mul_nonneg (by linarith) (sq_nonneg v)
  have h4 : (b - u) * v ^ 2 ≤ b - u := mul_le_of_le_one_right (by linarith) (by nlinarith)
  show u ∈ Set.Ioo (s - δ) (s + δ) ∧ u < b ∧ u + (b - u) * v ^ 2 ∈ Set.Ioo (s - δ) (b + δ)
  exact ⟨⟨by linarith, by linarith⟩, hub, by linarith, by linarith⟩

/-! ## Smoothness of the `v`-form -/

/-- The `v`-form is smooth at the points of `Os`. -/
theorem contDiffAt_Gfun_smooth {n j : ℕ} {s b δ : ℝ} {A : ℝ → ℝ → ℝ}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) (Rset s b δ)) {q : ℝ × ℝ}
    (hq : q ∈ Os s b δ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => Gfun n A b j q.1 q.2) q := by
  have hq1 : b - q.1 ≠ 0 := ne_of_gt (sub_pos.mpr hq.2.1)
  have hmem : (q.1, q.1 + (b - q.1) * q.2 ^ 2) ∈ Rset s b δ := ⟨hq.1, hq.2.2⟩
  have hcurve : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => (q.1, q.1 + (b - q.1) * q.2 ^ 2)) q := by fun_prop
  simp only [Gfun]
  refine ContDiffAt.sum fun i hi => ?_
  have h_a : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => (b - q.1) ^ (pk n - (i:ℝ) + 1)) q := by
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => x ^ (pk n - (i:ℝ) + 1)) (b - q.1) :=
      Real.contDiffAt_rpow_const_of_ne hq1
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => b - q.1) q := by fun_prop
    simpa [Function.comp_def] using h1.comp q h2
  have h_v : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => q.2 ^ (2 * n + 2 - 2 * i)) q := by fun_prop
  have h_p : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => pder A (j - i) q.1 (q.1 + (b - q.1) * q.2 ^ 2)) q := by
    have h1 := (Smooth.contDiffOn_uncurried_pder_smooth (isOpen_Ioo.prod isOpen_Ioo) hA (j - i)).contDiffAt
      ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hmem)
    have h3 := h1.comp q hcurve
    simpa [Function.comp_def] using h3
  refine ContDiffAt.mul (ContDiffAt.mul (ContDiffAt.mul ?_ h_a) h_v) h_p
  exact contDiffAt_const

theorem contDiffOn_Gfun {n j : ℕ} {s b δ : ℝ} {A : ℝ → ℝ → ℝ}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) (Rset s b δ)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => Gfun n A b j q.1 q.2) (Os s b δ) := by
  intro q hq
  rw [contDiffWithinAt_iff_contDiffAt (isOpen_Os s b δ |>.mem_nhds hq)]
  exact contDiffAt_Gfun_smooth hA hq


/-- `∂_u` of `(b-u) kt_j(u,(b-u)w)`, written out. -/
def Dkt (n : ℕ) (A : ℝ → ℝ → ℝ) (b : ℝ) (j : ℕ) (u w : ℝ) : ℝ :=
  - kt A (pk n) j u ((b - u) * w)
    + (b - u) * (kt A (pk n) (j + 1) u ((b - u) * w)
        + (1 - w) * tkt A (pk n) j u ((b - u) * w))

/-- the total `v`-derivative of `(1-v²) kt_j(u,(b-u)v²)`, written out. -/
def Hkt (n : ℕ) (A : ℝ → ℝ → ℝ) (b : ℝ) (j : ℕ) (u v : ℝ) : ℝ :=
  2 * v * (- kt A (pk n) j u ((b - u) * v ^ 2)
    + (b - u) * (1 - v ^ 2) * tkt A (pk n) j u ((b - u) * v ^ 2))

/-- The `u`-derivative of `(b-u) kt_j(u,(b-u)w)`. -/
theorem hasDerivAt_Psi {n j : ℕ} {s b δ u w : ℝ} {A : ℝ → ℝ → ℝ} (hsb : s < b) (hδ : 0 < δ)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) (Rset s b δ))
    (hu : u ∈ Vset s b δ) (hw0 : 0 < w) (hw1 : w ≤ 1) :
    HasDerivAt (fun x : ℝ => (b - x) * kt A (pk n) j x ((b - x) * w)) (Dkt n A b j u w) u := by
  have hub : u < b := lt_b_of_mem_Vset hu
  have hτ : 0 < (b - u) * w := mul_pos (sub_pos.mpr hub) hw0
  have huw := mem_Rset_of_mem_Vset hsb hδ hu (le_of_lt hw0) hw1
  have hK := Smooth.hasFDerivAt_uncurried_kt_smooth (p := pk n) (j := j) (O := Rset s b δ)
    (isOpen_Ioo.prod isOpen_Ioo) hA huw hτ
  have hcurve : HasDerivAt (fun x : ℝ => (x, (b - x) * w)) ((1:ℝ), -w) u := by
    refine (hasDerivAt_id u).prodMk ?_
    have h := ((hasDerivAt_id u).const_sub b).mul_const w
    simpa using h
  have hcomp := hK.comp_hasDerivAt u hcurve
  have hval : ((ks A (pk n) (j+1) u (u + (b-u)*w) + tkt A (pk n) j u ((b-u)*w)) •
        ContinuousLinearMap.fst ℝ ℝ ℝ +
        (tkt A (pk n) j u ((b-u)*w)) • ContinuousLinearMap.snd ℝ ℝ ℝ) ((1:ℝ), -w)
      = kt A (pk n) (j+1) u ((b-u)*w) + (1-w) * tkt A (pk n) j u ((b-u)*w) := by
    simp [smul_eq_mul]
    rw [kt_eq_ks]
    ring
  have hcomp' : HasDerivAt (fun x : ℝ => kt A (pk n) j x ((b - x) * w))
      (kt A (pk n) (j+1) u ((b-u)*w) + (1-w) * tkt A (pk n) j u ((b-u)*w)) u := by
    have := hcomp.congr_deriv hval
    simpa [Function.comp_def] using this
  have hb : HasDerivAt (fun x : ℝ => b - x) (-1) u := (hasDerivAt_id u).const_sub b
  have hprod := hb.mul hcomp'
  refine hprod.congr_deriv ?_
  simp only [Dkt]
  ring

/-- The `u`-derivative of the `v`-form. -/
theorem hasDerivAt_Gfun {n j : ℕ} {s b δ : ℝ} {A : ℝ → ℝ → ℝ} (hsb : s < b) (hδ : 0 < δ)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) (Rset s b δ))
    {u v : ℝ} (hu : u ∈ Vset s b δ) (hv0 : 0 < v) (hv1 : v ≤ 1) (hj : j ≤ n+1) :
    HasDerivAt (fun x : ℝ => Gfun n A b j x v) (2 * v * Dkt n A b j u (v ^ 2)) u := by
  have hv2pos : 0 < v ^ 2 := pow_pos hv0 2
  have hv21 : v ^ 2 ≤ 1 := by nlinarith
  have hpsi := hasDerivAt_Psi (n := n) (j := j) hsb hδ hA hu hv2pos hv21
  have hmul := hpsi.const_mul (2 * v)
  refine hmul.congr_of_eventuallyEq ?_
  filter_upwards [IsOpen.mem_nhds isOpen_Iio (lt_b_of_mem_Vset hu)] with x hx
  rw [Gfun_eq_kt (A := A) (sub_pos.mpr hx) hv0 hj]
  ring

/-- The total `v`-derivative of `(1-v²) kt_j(u,(b-u)v²)`. -/
theorem hasDerivAt_Hh {n j : ℕ} {s b δ : ℝ} {A : ℝ → ℝ → ℝ} (hsb : s < b) (hδ : 0 < δ)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) (Rset s b δ))
    {u v : ℝ} (hu : u ∈ Vset s b δ) (hv0 : 0 < v) (hv1 : v ≤ 1) :
    HasDerivAt (fun y : ℝ => (1 - y ^ 2) * kt A (pk n) j u ((b - u) * y ^ 2))
      (Hkt n A b j u v) v := by
  have hub : u < b := lt_b_of_mem_Vset hu
  have hv2pos : 0 < v ^ 2 := pow_pos hv0 2
  have hv21 : v ^ 2 ≤ 1 := by nlinarith
  have huτ : (u, u + (b - u) * v ^ 2) ∈ Rset s b δ :=
    mem_Rset_of_mem_Vset hsb hδ hu (le_of_lt hv2pos) hv21
  have hτ : 0 < (b - u) * v ^ 2 := mul_pos (sub_pos.mpr hub) hv2pos
  have hK := Smooth.hasFDerivAt_uncurried_kt_smooth (p := pk n) (j := j) (O := Rset s b δ)
    (isOpen_Ioo.prod isOpen_Ioo) hA huτ hτ
  have hcurve : HasDerivAt (fun y : ℝ => (u, (b - u) * y ^ 2)) ((0:ℝ), 2 * (b - u) * v) v := by
    refine (hasDerivAt_const v u).prodMk ?_
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * v) v := by
      simpa using hasDerivAt_pow 2 v
    have h2 := h1.const_mul (b - u)
    refine h2.congr_deriv ?_
    ring
  have hcomp := hK.comp_hasDerivAt v hcurve
  have hval : ((ks A (pk n) (j+1) u (u + (b-u)*v^2) + tkt A (pk n) j u ((b-u)*v^2)) •
        ContinuousLinearMap.fst ℝ ℝ ℝ +
        (tkt A (pk n) j u ((b-u)*v^2)) • ContinuousLinearMap.snd ℝ ℝ ℝ) ((0:ℝ), 2*(b-u)*v)
      = 2 * (b - u) * v * tkt A (pk n) j u ((b-u)*v^2) := by
    simp [smul_eq_mul]
    ring
  have hcomp' : HasDerivAt (fun y : ℝ => kt A (pk n) j u ((b - u) * y ^ 2))
      (2 * (b - u) * v * tkt A (pk n) j u ((b-u)*v^2)) v := by
    have := hcomp.congr_deriv hval
    simpa [Function.comp_def] using this
  have h1 : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2*v)) v := by
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * v) v := by
      simpa using hasDerivAt_pow 2 v
    have h3 := (hasDerivAt_const v (1:ℝ)).sub h2
    refine (h3.congr_deriv (by ring)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => ?_)
    simp [Pi.sub_apply]
  have hprod := h1.mul hcomp'
  refine hprod.congr_deriv ?_
  simp only [Hkt]
  ring
/-- The derivative of the `v`-form in the `u`-variable, in terms of `Dkt`. -/
theorem deriv_Gfun_eq {n j : ℕ} {s b δ : ℝ} {A : ℝ → ℝ → ℝ} (hsb : s < b) (hδ : 0 < δ)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) (Rset s b δ))
    {u v : ℝ} (hu : u ∈ Vset s b δ) (hv0 : 0 < v) (hv1 : v ≤ 1) (hj : j ≤ n+1) :
    Gdu n A b j (u, v) = 2 * v * Dkt n A b j u (v ^ 2) := by
  have hOs : (u, v) ∈ Os s b δ := mem_Os_of_mem_Vset hsb hδ hu (le_of_lt hv0) hv1
  have hfd := (contDiffAt_Gfun_smooth (n := n) (j := j) hA hOs).differentiableAt (by simp)
  have hcurve : HasDerivAt (fun x : ℝ => (x, v)) ((1:ℝ),(0:ℝ)) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u v)
  have hcomp := hfd.hasFDerivAt.comp_hasDerivAt u hcurve
  have hcomp' : HasDerivAt (fun x : ℝ => Gfun n A b j x v)
      ((fderiv ℝ (fun q : ℝ × ℝ => Gfun n A b j q.1 q.2) (u,v)) ((1:ℝ),(0:ℝ))) u := by
    simpa [Function.comp_def] using hcomp
  exact hcomp'.unique (hasDerivAt_Gfun hsb hδ hA hu hv0 hv1 hj)

/-- The leftover total derivative identity. -/
theorem Hkt_eq {n j : ℕ} {b u v : ℝ} {A : ℝ → ℝ → ℝ} (hub : u < b) (hv0 : 0 < v)
    (hj : j ≤ n) :
    Hkt n A b j u v = 2 * v * Dkt n A b j u (v ^ 2) - Gfun n A b (j+1) u v := by
  rw [Hkt, Dkt, Gfun_eq_kt (A := A) (b := b) (u := u) (v := v) (sub_pos.mpr hub) hv0 (by omega)]
  ring


/-! ## Continuity of the slices of the `v`-form and of its `u`-derivative -/

theorem continuousOn_gfun_slice {n j : ℕ} {s b δ : ℝ} {A : ℝ → ℝ → ℝ} (hsb : s < b) (hδ : 0 < δ)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) (Rset s b δ))
    {u : ℝ} (hu : u ∈ Vset s b δ) :
    ContinuousOn (fun v : ℝ => Gfun n A b j u v) (Set.Icc (0:ℝ) 1) :=
  (contDiffOn_Gfun (n := n) (j := j) hA).continuousOn.comp
    ((continuous_const.prodMk continuous_id).continuousOn)
    (fun v hv => mem_Os_of_mem_Vset hsb hδ hu hv.1 hv.2)

theorem continuousOn_gdu_slice {n j : ℕ} {s b δ : ℝ} {A : ℝ → ℝ → ℝ} (hsb : s < b) (hδ : 0 < δ)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) (Rset s b δ))
    {u : ℝ} (hu : u ∈ Vset s b δ) :
    ContinuousOn (fun v : ℝ => Gdu n A b j (u, v)) (Set.Icc (0:ℝ) 1) := by
  have hfd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (fun q : ℝ × ℝ => Gfun n A b j q.1 q.2))
      (Os s b δ) :=
    (contDiffOn_Gfun (n := n) (j := j) hA).fderiv_of_isOpen (isOpen_Os s b δ) (by simp)
  have hcurve : ContinuousOn (fun v : ℝ => (u, v)) (Set.Icc (0:ℝ) 1) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hmem : Set.MapsTo (fun v : ℝ => (u, v)) (Set.Icc (0:ℝ) 1) (Os s b δ) :=
    fun v hv => mem_Os_of_mem_Vset hsb hδ hu hv.1 hv.2
  exact (hfd.continuousOn.comp hcurve hmem).clm_apply continuousOn_const

/-- A uniform bound for the `u`-derivative of the `v`-form on a compact box of `u`-values. -/
theorem exists_bound_gdu_Icc {n j : ℕ} {s b δ u₀ u₁ : ℝ} {A : ℝ → ℝ → ℝ}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) (Rset s b δ)) (hδ : 0 < δ)
    (h1 : s - δ < u₀) (h2 : u₁ < s + δ) (h3 : u₁ < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Icc u₀ u₁, ∀ v ∈ Set.Icc (0:ℝ) 1,
      ‖Gdu n A b j (u, v)‖ ≤ C := by
  have hcont : ContinuousOn (fun q : ℝ × ℝ => Gdu n A b j q) (Os s b δ) := by
    have h1' : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (fun q : ℝ × ℝ => Gfun n A b j q.1 q.2))
        (Os s b δ) :=
      (contDiffOn_Gfun (n := n) (j := j) hA).fderiv_of_isOpen (isOpen_Os s b δ) (by simp)
    exact (h1'.continuousOn).clm_apply continuousOn_const
  have hKO : (Set.Icc u₀ u₁ ×ˢ Set.Icc (0:ℝ) 1) ⊆ Os s b δ := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    simp only [Set.mem_Icc, Prod.fst, Prod.snd] at hu hv
    have hmn : 0 ≤ (b - u) * v ^ 2 := mul_nonneg (by linarith [hu.2]) (sq_nonneg v)
    have hmx : (b - u) * v ^ 2 ≤ b - u :=
      mul_le_of_le_one_right (by linarith [hu.2]) (by nlinarith [hv.2])
    show u ∈ Set.Ioo (s - δ) (s + δ) ∧ u < b ∧ u + (b - u) * v ^ 2 ∈ Set.Ioo (s - δ) (b + δ)
    exact ⟨⟨by linarith [hu.1], by linarith [hu.2]⟩, by linarith [hu.2],
      by linarith, by linarith⟩
  obtain ⟨C0, hC0⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hcont.mono hKO)
  exact ⟨max C0 0, le_max_right _ _, fun u hu v hv =>
    le_trans (hC0 (u, v) ⟨hu, hv⟩) (le_max_left _ _)⟩

/-- **The leftover total derivative integrates to zero.** -/
theorem integral_Hkt_eq_zero {n j : ℕ} {s b δ : ℝ} {A : ℝ → ℝ → ℝ} (hsb : s < b) (hδ : 0 < δ)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) (Rset s b δ))
    {u : ℝ} (hu : u ∈ Vset s b δ) (hjp : (j : ℝ) < pk n) :
    ∫ v in (0:ℝ)..1, Hkt n A b j u v = 0 := by
  have hjn : j ≤ n := by
    have h : (j : ℝ) < (n : ℝ) + 1 / 2 := by simpa [pk] using hjp
    have h' : (j : ℝ) < (n : ℝ) + 1 := by linarith
    have h'' : j < n + 1 := by exact_mod_cast h'
    exact Nat.lt_succ_iff.mp h''
  have hhub : u < b := lt_b_of_mem_Vset hu
  have huu : (u, u) ∈ Rset s b δ := by
    have h := mem_Rset_of_mem_Vset (w := 0) hsb hδ hu le_rfl (by norm_num)
    simpa using h
  -- integrability of `Hkt`, through its a.e. expression as a difference of continuous functions
  have hint : IntervalIntegrable (fun v : ℝ => Hkt n A b j u v) volume (0:ℝ) 1 := by
    refine IntervalIntegrable.congr_ae
      (ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ 1)
        ((continuousOn_gdu_slice (n := n) (j := j) hsb hδ hA hu).sub
          (continuousOn_gfun_slice (n := n) (j := j + 1) hsb hδ hA hu))) ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with v hv
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hv
    show Gdu n A b j (u, v) - Gfun n A b (j + 1) u v = Hkt n A b j u v
    rw [deriv_Gfun_eq (n := n) (j := j) (s := s) (b := b) (δ := δ) hsb hδ hA
        (u := u) (v := v) hu hv.1 hv.2 (by omega),
      Hkt_eq (A := A) (n := n) (j := j) (b := b) (u := u) (v := v) hhub hv.1 hjn]
  -- derivative on the open interval
  have hderiv : ∀ v ∈ Set.Ioo (0:ℝ) 1,
      HasDerivAt (fun y : ℝ => (1 - y ^ 2) * kt A (pk n) j u ((b - u) * y ^ 2))
        (Hkt n A b j u v) v :=
    fun v hv => hasDerivAt_Hh (n := n) (j := j) hsb hδ hA hu hv.1 (le_of_lt hv.2)
  -- the one-sided limits
  have hfa : Tendsto (fun v : ℝ => (1 - v ^ 2) * kt A (pk n) j u ((b - u) * v ^ 2))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hk := Smooth.tendsto_kt_zero_smooth (p := pk n) (j := j) (O := Rset s b δ)
      (isOpen_Ioo.prod isOpen_Ioo) hA hjp huu
    have hsq : Tendsto (fun v : ℝ => (b - u) * v ^ 2) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
      have hbu : 0 < b - u := sub_pos.mpr hhub
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h : Tendsto (fun v : ℝ => (b - u) * v ^ 2) (𝓝 (0:ℝ)) (𝓝 ((b - u) * (0:ℝ) ^ 2)) :=
          ((continuous_const.mul (continuous_id.pow 2)).continuousAt).tendsto
        rw [show (b - u) * (0:ℝ) ^ 2 = 0 by ring] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with v hv
        exact mul_pos hbu (pow_pos hv 2)
    have hkt := hk.comp hsq
    have h1 : Tendsto (fun v : ℝ => 1 - v ^ 2) (𝓝[>] (0:ℝ)) (𝓝 (1:ℝ)) := by
      have h : Tendsto (fun v : ℝ => 1 - v ^ 2) (𝓝 (0:ℝ)) (𝓝 (1 - (0:ℝ) ^ 2)) :=
        (((continuous_const.sub (continuous_id.pow 2))).continuousAt).tendsto
      rw [show 1 - (0:ℝ) ^ 2 = 1 by ring] at h
      exact h.mono_left nhdsWithin_le_nhds
    simpa using h1.mul hkt
  have hfb : Tendsto (fun v : ℝ => (1 - v ^ 2) * kt A (pk n) j u ((b - u) * v ^ 2))
      (𝓝[<] (1:ℝ)) (𝓝 ((1 - (1:ℝ) ^ 2) * kt A (pk n) j u ((b - u) * (1:ℝ) ^ 2))) := by
    have hh := hasDerivAt_Hh (n := n) (j := j) hsb hδ hA hu (v := 1) (by norm_num) le_rfl
    exact hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0:ℝ)) (b := (1:ℝ))
    (f := fun y : ℝ => (1 - y ^ 2) * kt A (pk n) j u ((b - u) * y ^ 2))
    (f' := fun y : ℝ => Hkt n A b j u y)
    (fa := 0) (fb := (1 - (1:ℝ) ^ 2) * kt A (pk n) j u ((b - u) * (1:ℝ) ^ 2))
    (by norm_num) hderiv hint hfa hfb
  rw [hmain]
  ring

/-! ## The derivative of the swept integral -/

theorem ks_swept_integral_hasDerivAt {n : ℕ} {b s δ : ℝ} (hsb : s < b) (hδ : 0 < δ)
    {A : ℝ → ℝ → ℝ}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2)
      (Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (b + δ)))
    {j : ℕ} (hj : j ≤ n) {x : ℝ} (hx : x ∈ Set.Ioo (s - δ / 2) (s + δ / 2)) (hxb : x < b) :
    HasDerivAt (fun x' : ℝ => ∫ σ in x'..b, Work.OddVolterra.ks A ((n : ℝ) + 1 / 2) j x' σ)
      (∫ σ in x..b, Work.OddVolterra.ks A ((n : ℝ) + 1 / 2) (j + 1) x σ) x := by
  have hpk : pk n = (n : ℝ) + 1 / 2 := rfl
  have hjn1 : j ≤ n + 1 := by omega
  have hjn : (j : ℝ) < pk n := by
    rw [hpk]
    have h : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
    linarith
  have hxV : x ∈ Vset s b δ := ⟨hx, hxb⟩
  -- the auxiliary neighbourhood of `x` on which everything is differentiable
  set η : ℝ := min ((x - (s - δ / 2)) / 2) (min (((s + δ / 2) - x) / 2) ((b - x) / 2)) with hηdef
  have hηpos : 0 < η := lt_min (by linarith [hx.1]) (lt_min (by linarith [hx.2]) (by linarith [hxb]))
  have hη1 : s - δ / 2 < x - η := by
    have h : η ≤ (x - (s - δ / 2)) / 2 := min_le_left _ _
    linarith
  have hη2 : x + η < s + δ / 2 := by
    have h1 : η ≤ min (((s + δ / 2) - x) / 2) ((b - x) / 2) := min_le_right _ _
    have h2 : η ≤ ((s + δ / 2) - x) / 2 := le_trans h1 (min_le_left _ _)
    linarith
  have hη3 : x + η < b := by
    have h1 : η ≤ min (((s + δ / 2) - x) / 2) ((b - x) / 2) := min_le_right _ _
    have h2 : η ≤ (b - x) / 2 := le_trans h1 (min_le_right _ _)
    linarith
  set W : Set ℝ := Set.Ioo (x - η) (x + η) with hWdef
  have hW_nhds : W ∈ 𝓝 x := isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hWV : ∀ u ∈ W, u ∈ Vset s b δ := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    show u < b
    linarith
  have hWVc : ∀ u ∈ Set.Icc (x - η) (x + η), u ∈ Vset s b δ := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    show u < b
    linarith
  -- the constant bound for the `u`-derivative
  obtain ⟨C, hC0, hCbd⟩ := exists_bound_gdu_Icc (n := n) (j := j) (u₀ := x - η) (u₁ := x + η)
    (hA := hA) hδ (by linarith) (by linarith) hη3
  have hUsub : Set.uIoc (0:ℝ) 1 ⊆ Set.Icc (0:ℝ) 1 := by
    intro v hv
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hv
    exact ⟨le_of_lt hv.1, hv.2⟩
  have hF_meas : ∀ᶠ u in 𝓝 x, AEStronglyMeasurable (fun v : ℝ => Gfun n A b j u v)
      (volume.restrict (Ι (0:ℝ) 1)) := by
    filter_upwards [hW_nhds] with u hu
    exact ((continuousOn_gfun_slice (n := n) (j := j) hsb hδ hA (hWV u hu)).mono hUsub).aestronglyMeasurable
      measurableSet_uIoc
  have hF_int : IntervalIntegrable (fun v : ℝ => Gfun n A b j x v) volume (0:ℝ) 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ 1)
      (continuousOn_gfun_slice (n := n) (j := j) hsb hδ hA hxV)
  have hF'_meas : AEStronglyMeasurable (fun v : ℝ => Gdu n A b j (x, v))
      (volume.restrict (Ι (0:ℝ) 1)) :=
    ((continuousOn_gdu_slice (n := n) (j := j) hsb hδ hA hxV).mono hUsub).aestronglyMeasurable
      measurableSet_uIoc
  have hbound : ∀ᵐ v ∂volume, v ∈ Ι (0:ℝ) 1 →
      ∀ u ∈ W, ‖Gdu n A b j (u, v)‖ ≤ (fun _ : ℝ => C) v := by
    filter_upwards with v hv u hu
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hv
    exact hCbd u ⟨le_of_lt hu.1, le_of_lt hu.2⟩ v ⟨le_of_lt hv.1, hv.2⟩
  have hdiff : ∀ᵐ v ∂volume, v ∈ Ι (0:ℝ) 1 → ∀ u ∈ W,
      HasDerivAt (fun u' : ℝ => Gfun n A b j u' v) (Gdu n A b j (u, v)) u := by
    filter_upwards with v hv u hu
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hv
    have hOs : (u, v) ∈ Os s b δ := mem_Os_of_mem_Vset hsb hδ (hWV u hu) (le_of_lt hv.1) hv.2
    have hfd := (contDiffAt_Gfun_smooth (n := n) (j := j) (s := s) (b := b) (δ := δ) hA hOs).differentiableAt
      (by simp)
    have hcurve : HasDerivAt (fun x' : ℝ => (x', v)) ((1:ℝ),(0:ℝ)) u :=
      (hasDerivAt_id u).prodMk (hasDerivAt_const u v)
    have hcomp := hfd.hasFDerivAt.comp_hasDerivAt u hcurve
    simpa [Function.comp_def, Gdu] using hcomp
  obtain ⟨hGdu_int, hderiv⟩ :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := (0:ℝ)) (b := (1:ℝ)) (bound := fun _ : ℝ => C) (x₀ := x)
      (s := W) (F := fun u v => Gfun n A b j u v)
      (F' := fun u v => Gdu n A b j (u, v))
      hW_nhds hF_meas hF_int hF'_meas hbound intervalIntegrable_const hdiff
  -- the value of the `u`-derivative integral
  have hIntG : IntervalIntegrable (fun v : ℝ => Gfun n A b (j + 1) x v) volume (0:ℝ) 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ 1)
      (continuousOn_gfun_slice (n := n) (j := j + 1) hsb hδ hA hxV)
  have hae : (fun v : ℝ => Gdu n A b j (x, v))
      =ᵐ[volume.restrict (Ι (0:ℝ) 1)]
        (fun v : ℝ => Gfun n A b (j + 1) x v + Hkt n A b j x v) := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with v hv
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hv
    have h1 := deriv_Gfun_eq (n := n) (j := j) (s := s) (b := b) (δ := δ) hsb hδ hA
      (u := x) (v := v) hxV hv.1 hv.2 hjn1
    have h2 := Hkt_eq (A := A) (n := n) (j := j) (b := b) (u := x) (v := v) hxb hv.1 hj
    show Gdu n A b j (x, v) = Gfun n A b (j + 1) x v + Hkt n A b j x v
    rw [h1, h2]
    ring
  have hHkt_int : IntervalIntegrable (fun v : ℝ => Hkt n A b j x v) volume (0:ℝ) 1 := by
    refine IntervalIntegrable.congr_ae
      (ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ 1)
        ((continuousOn_gdu_slice (n := n) (j := j) hsb hδ hA hxV).sub
          (continuousOn_gfun_slice (n := n) (j := j + 1) hsb hδ hA hxV))) ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with v hv
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hv
    show Gdu n A b j (x, v) - Gfun n A b (j + 1) x v = Hkt n A b j x v
    rw [deriv_Gfun_eq (n := n) (j := j) (s := s) (b := b) (δ := δ) hsb hδ hA
        (u := x) (v := v) hxV hv.1 hv.2 hjn1,
      Hkt_eq (A := A) (n := n) (j := j) (b := b) (u := x) (v := v) hxb hv.1 hj]
  have hval : ∫ v in (0:ℝ)..1, Gdu n A b j (x, v) = ∫ σ in x..b, ks A (pk n) (j + 1) x σ := by
    rw [intervalIntegral.integral_congr_ae_restrict hae, intervalIntegral.integral_add hIntG hHkt_int,
      integral_Gfun_eq_integral_ks (A := A) (b := b) (u := x) (j := j + 1) hxb (by omega),
      integral_Hkt_eq_zero (n := n) (j := j) (s := s) (b := b) (δ := δ) (A := A) hsb hδ hA hxV hjn]
    ring
  -- transfer to the function of the statement
  have heq : (fun x' : ℝ => ∫ σ in x'..b, ks A (pk n) j x' σ)
      =ᶠ[𝓝 x] (fun u : ℝ => ∫ v in (0:ℝ)..1, Gfun n A b j u v) := by
    filter_upwards [hW_nhds] with u hu
    exact (integral_Gfun_eq_integral_ks (A := A) (b := b) (u := u) (j := j)
      (lt_b_of_mem_Vset (hWV u hu)) hjn1).symm
  have hmain : HasDerivAt
      (fun x' : ℝ => ∫ σ in x'..b, ks A ((n : ℝ) + 1 / 2) j x' σ)
      (∫ σ in x..b, ks A ((n : ℝ) + 1 / 2) (j + 1) x σ) x :=
    (hderiv.congr_deriv hval).congr_of_eventuallyEq heq
  exact hmain

end Work.OddVolterra.Swept
