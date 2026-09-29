import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17.logP_local_defs
import Submission.Work.C17.logP_local_plan
import Submission.Work.C17f.xs_factor_data
import Submission.Work.C17f.differentiableOn_of_hasSum_powSeries
import Submission.Work.C17f.Pfun_solves_M
import Submission.Work.C17f.frobenius_double_exponent_zero

namespace Work.C17

open Polynomial Filter
open scoped BigOperators Topology

noncomputable section

/-- For `3 ≤ a < b` the cusp `x_s` lies in `(0,1)`.  (Local copy of
`Work.C17.xs_pos_and_sq_lt_one`, kept here to avoid a heavy import.) -/
private lemma xs_pos_and_sq_lt_one' (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a < b) :
    0 < xs a b ∧ xs a b * xs a b < 1 := by
  have haR : (1 : ℝ) ≤ (a : ℝ) := by
    have h : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by
    have h : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  set A : ℝ := (a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1) with hA
  set B : ℝ := (b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1) with hB
  have hsqa : Real.sqrt ((a : ℝ) ^ 2 - 1) ^ 2 = (a : ℝ) ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hsqb : Real.sqrt ((b : ℝ) ^ 2 - 1) ^ 2 = (b : ℝ) ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hApos : 0 < A := by
    rw [hA]
    have hs := Real.sqrt_nonneg ((a : ℝ) ^ 2 - 1)
    have ha0 : (0 : ℝ) < (a : ℝ) := by linarith
    linarith
  have hBpos : 0 < B := by
    rw [hB]
    have hs := Real.sqrt_nonneg ((b : ℝ) ^ 2 - 1)
    have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
    linarith
  have hBβ : B * ((b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1)) = 1 := by
    rw [hB]; nlinarith
  have hxs_eq : xs a b = A * ((b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1)) := by
    rw [xs, ← hA]
  have hβb : (b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1) = 1 / B := by
    rw [eq_div_iff (ne_of_gt hBpos)]
    rw [mul_comm]; exact hBβ
  have hxsB : xs a b = A / B := by rw [hxs_eq, hβb]; ring
  have hAltB : A < B := by
    rw [hA, hB]
    have hs : Real.sqrt ((a : ℝ) ^ 2 - 1) < Real.sqrt ((b : ℝ) ^ 2 - 1) := by
      apply Real.sqrt_lt_sqrt
      · nlinarith
      · nlinarith
    linarith
  have hxs_lt1 : xs a b < 1 := by
    rw [hxsB, div_lt_one hBpos]; exact hAltB
  have hxs_pos : 0 < xs a b := by rw [hxsB]; positivity
  exact ⟨hxs_pos, by nlinarith [hxs_pos, hxs_lt1]⟩

/-- `dslope` at a point different from the base point, as a quotient. -/
private lemma dslope_eq_div (f : ℂ → ℂ) {a b : ℂ} (h : b ≠ a) :
    dslope f a b = (f b - f a) / (b - a) := by
  rw [dslope_of_ne f h, slope_def_field]

/-- Derivative of `z ↦ log (s - z)` at a point of the slit plane. -/
private lemma hasDerivAt_log_sub {s z : ℂ} (h : s - z ∈ Complex.slitPlane) :
    HasDerivAt (fun x : ℂ => Complex.log (s - x)) (1 / (z - s)) z := by
  have h1 : HasDerivAt (fun x : ℂ => s - x) (-1) z := (hasDerivAt_id z).const_sub s
  have h2 := (Complex.hasDerivAt_log h).comp z h1
  have h3 : 1 / (z - s) = (s - z)⁻¹ * (-1) := by
    rw [show z - s = -(s - z) by ring, div_eq_mul_inv, inv_neg]
    ring
  exact h2.congr_deriv h3.symm

/-- The local structure of a solution of a Fuchsian equation with a double exponent `0`. -/
private theorem local_structure_core {s : ℂ} {δ : ℝ}
    (hδ : 0 < δ)
    {y1 φ : ℂ → ℂ} {P2 P1 P0 G : ℂ → ℂ} {Ω : Set ℂ} {q : ℂ → ℂ}
    (hy1d : DifferentiableOn ℂ y1 (Metric.ball s δ))
    (hy1ne : ∀ z ∈ Metric.ball s δ, y1 z ≠ 0)
    (hy1ode : ∀ z ∈ Metric.ball s δ,
      P2 z * deriv (deriv y1) z + P1 z * deriv y1 z + P0 z * y1 z = 0)
    (hP2fac : ∀ z ∈ Metric.ball s δ, P2 z = (z - s) * q z)
    (hqd : DifferentiableOn ℂ q (Metric.ball s δ))
    (hqne : ∀ z ∈ Metric.ball s δ, q z ≠ 0)
    (hres : P1 s = q s)
    (hP1d : DifferentiableOn ℂ P1 (Metric.ball s δ))
    (hP0d : DifferentiableOn ℂ P0 (Metric.ball s δ))
    (hGd : DifferentiableOn ℂ G (Metric.ball s δ))
    (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω) (hΩsub : Ω ⊆ Metric.ball s δ)
    (hsΩ : s ∉ Ω)
    (hslit : ∀ z ∈ Ω, s - z ∈ Complex.slitPlane)
    (hφd : DifferentiableOn ℂ φ Ω)
    (hφode : ∀ z ∈ Ω, P2 z * deriv (deriv φ) z + P1 z * deriv φ z + P0 z * φ z = G z) :
    ∃ (κ : ℂ) (W0 : ℂ → ℂ), DifferentiableOn ℂ W0 (Metric.ball s δ) ∧
      ∀ z ∈ Ω, φ z = κ * y1 z * Complex.log (s - z) + y1 z * W0 z := by
  classical
  have hball : Metric.ball s δ ∈ 𝓝 s := Metric.ball_mem_nhds s hδ
  have hballo : IsOpen (Metric.ball s δ) := Metric.isOpen_ball
  have hdy1d : DifferentiableOn ℂ (deriv y1) (Metric.ball s δ) := hy1d.deriv hballo
  -- ## 1. the analytic quotient `A1 = (P1 - q)/((z-s)q)`
  set A1 : ℂ → ℂ := fun z => (dslope P1 s z - dslope q s z) / q z with hA1def
  have hdsP1 : DifferentiableOn ℂ (dslope P1 s) (Metric.ball s δ) :=
    (Complex.differentiableOn_dslope (f := P1) (s := Metric.ball s δ) (c := s) hball).mpr hP1d
  have hdsq : DifferentiableOn ℂ (dslope q s) (Metric.ball s δ) :=
    (Complex.differentiableOn_dslope (f := q) (s := Metric.ball s δ) (c := s) hball).mpr hqd
  have hA1d : DifferentiableOn ℂ A1 (Metric.ball s δ) := by
    rw [hA1def]
    exact (hdsP1.sub hdsq).div hqd hqne
  have hA1eq : ∀ z ∈ Metric.ball s δ, z ≠ s → 1 / (z - s) + A1 z = P1 z / P2 z := by
    intro z hz hzs
    have hP2z : P2 z ≠ 0 := by
      rw [hP2fac z hz]
      exact mul_ne_zero (sub_ne_zero.mpr hzs) (hqne z hz)
    have h1 : dslope P1 s z = (P1 z - P1 s) / (z - s) := dslope_eq_div P1 hzs
    have h2 : dslope q s z = (q z - q s) / (z - s) := dslope_eq_div q hzs
    have hqz : q z ≠ 0 := hqne z hz
    rw [hA1def]
    change 1 / (z - s) + (dslope P1 s z - dslope q s z) / q z = P1 z / P2 z
    rw [h1, h2, hP2fac z hz, hres]
    field_simp
    ring
  -- ## 2. an antiderivative of `A1`, and the functions `A0`, `A`, `g`, `ζh`
  obtain ⟨Qant, hQant0, hQant⟩ : ∃ Qant : ℂ → ℂ, Qant s = 0 ∧
      ∀ z ∈ Metric.ball s δ, HasDerivAt Qant (A1 z) z := by
    obtain ⟨Q, hQ0, hQ⟩ := (hA1d.isExactOn_ball).with_val_at s 0
    exact ⟨Q, hQ0, hQ⟩
  have hQantd : DifferentiableOn ℂ Qant (Metric.ball s δ) :=
    fun z hz => (hQant z hz).differentiableAt.differentiableWithinAt
  set A0 : ℂ → ℂ := fun z => 2 * deriv y1 z / y1 z + A1 z with hA0def
  set A : ℂ → ℂ := fun z => 1 / (z - s) + A0 z with hAdef
  set g : ℂ → ℂ := fun z => -(Complex.exp (-(Qant z)) / (y1 z) ^ 2) with hgdef
  have hgd : DifferentiableOn ℂ g (Metric.ball s δ) := by
    rw [hgdef]
    refine DifferentiableOn.neg ?_
    refine DifferentiableOn.div ((hQantd.neg).cexp) (hy1d.pow 2) ?_
    intro z hz
    exact pow_ne_zero 2 (hy1ne z hz)
  have hgne : ∀ z ∈ Metric.ball s δ, g z ≠ 0 := by
    intro z hz
    rw [hgdef]
    refine neg_ne_zero.mpr (div_ne_zero (Complex.exp_ne_zero _) ?_)
    exact pow_ne_zero 2 (hy1ne z hz)
  have hpow_d : ∀ z ∈ Metric.ball s δ, HasDerivAt (fun x : ℂ => y1 x ^ 2)
      (2 * y1 z * deriv y1 z) z := by
    intro z hz
    have hy1d_at : HasDerivAt y1 (deriv y1 z) z :=
      (hy1d.differentiableAt (hballo.mem_nhds hz)).hasDerivAt
    have h := hy1d_at.pow 2
    have h2 : (y1 ^ 2 : ℂ → ℂ) = fun x => y1 x ^ 2 := by ext x; simp
    rw [h2] at h
    simpa using h
  have hg_deriv : ∀ z ∈ Metric.ball s δ, deriv g z = -(A0 z) * g z := by
    intro z hz
    have hy1z : y1 z ≠ 0 := hy1ne z hz
    have h1 : HasDerivAt (fun x : ℂ => Complex.exp (-(Qant x)) / (y1 x) ^ 2)
        ((Complex.exp (-(Qant z)) * (-(A1 z)) * (y1 z) ^ 2 - Complex.exp (-(Qant z))
          * (2 * y1 z * deriv y1 z)) / ((y1 z) ^ 2) ^ 2) z := by
      refine ((hQant z hz).neg.cexp).div (hpow_d z hz) ?_
      exact pow_ne_zero 2 hy1z
    have h2 : HasDerivAt g
        (-(((Complex.exp (-(Qant z)) * (-(A1 z)) * (y1 z) ^ 2 - Complex.exp (-(Qant z))
          * (2 * y1 z * deriv y1 z)) / ((y1 z) ^ 2) ^ 2))) z := by
      rw [hgdef]; exact h1.neg
    rw [h2.deriv]
    rw [hA0def, hA1def, hgdef]
    field_simp
    ring
  set ζh : ℂ → ℂ := fun z => g z / (z - s) with hζhdef
  have hζh_deriv : ∀ z ∈ Metric.ball s δ, z ≠ s → HasDerivAt ζh (-(A z) * ζh z) z := by
    intro z hz hzs
    have h1 : HasDerivAt (fun x : ℂ => g x / (x - s))
        ((deriv g z * (z - s) - g z * 1) / (z - s) ^ 2) z := by
      refine ((hgd.differentiableAt (hballo.mem_nhds hz)).hasDerivAt).div ?_ ?_
      · exact (hasDerivAt_id z).sub_const s
      · exact sub_ne_zero.mpr hzs
    have h2 : HasDerivAt ζh ((deriv g z * (z - s) - g z * 1) / (z - s) ^ 2) z := by
      rw [hζhdef]; exact h1
    refine h2.congr_deriv ?_
    rw [hg_deriv z hz, hζhdef, hAdef, hA0def, hA1def]
    field_simp
    ring
  -- ## 3. the particular solution: `Ψ`, its primitive `ℓ`, and `ζp`
  have hΨd : DifferentiableOn ℂ (fun z => G z / (q z * y1 z * g z)) (Metric.ball s δ) :=
    hGd.div ((hqd.mul hy1d).mul hgd)
      (fun z hz => mul_ne_zero (mul_ne_zero (hqne z hz) (hy1ne z hz)) (hgne z hz))
  obtain ⟨ℓ, hℓ0, hℓ⟩ : ∃ ℓ : ℂ → ℂ, ℓ s = 0 ∧
      ∀ z ∈ Metric.ball s δ, HasDerivAt ℓ (G z / (q z * y1 z * g z)) z := by
    obtain ⟨L, hL0, hL⟩ := (hΨd.isExactOn_ball).with_val_at s 0
    exact ⟨L, hL0, hL⟩
  have hℓd : DifferentiableOn ℂ ℓ (Metric.ball s δ) :=
    fun z hz => (hℓ z hz).differentiableAt.differentiableWithinAt
  set ζp : ℂ → ℂ := fun z => g z * dslope ℓ s z with hζpdef
  have hdsℓ : DifferentiableOn ℂ (dslope ℓ s) (Metric.ball s δ) :=
    (Complex.differentiableOn_dslope (f := ℓ) (s := Metric.ball s δ) (c := s) hball).mpr hℓd
  have hζpd : DifferentiableOn ℂ ζp (Metric.ball s δ) := by
    rw [hζpdef]; exact hgd.mul hdsℓ
  have hdsl_ne : ∀ z : ℂ, z ≠ s → dslope ℓ s z = ℓ z / (z - s) := by
    intro z hzs
    rw [dslope_eq_div ℓ hzs, hℓ0, sub_zero]
  have hζp_deriv : ∀ z ∈ Metric.ball s δ, z ≠ s →
      HasDerivAt ζp (-(A z) * ζp z + G z / (P2 z * y1 z)) z := by
    intro z hz hzs
    have hy1z : y1 z ≠ 0 := hy1ne z hz
    have hgz : g z ≠ 0 := hgne z hz
    have hqz : q z ≠ 0 := hqne z hz
    have hP2z : P2 z ≠ 0 := by
      rw [hP2fac z hz]; exact mul_ne_zero (sub_ne_zero.mpr hzs) hqz
    have hdℓz : dslope ℓ s z = ℓ z / (z - s) := hdsl_ne z hzs
    have hnhds : {x : ℂ | x ≠ s} ∈ 𝓝 z :=
      (isOpen_compl_singleton).mem_nhds (by simpa using hzs)
    have hEq : ζp =ᶠ[𝓝 z] fun x : ℂ => g x * (ℓ x / (x - s)) := by
      filter_upwards [hnhds] with x hx
      show g x * dslope ℓ s x = g x * (ℓ x / (x - s))
      rw [hdsl_ne x hx]
    have hdiv : HasDerivAt (fun x : ℂ => ℓ x / (x - s))
        ((G z / (q z * y1 z * g z) * (z - s) - ℓ z * 1) / (z - s) ^ 2) z := by
      refine ((hℓ z hz).div ((hasDerivAt_id z).sub_const s) (sub_ne_zero.mpr hzs)).congr_deriv ?_
      norm_num
    have h1 : HasDerivAt (fun x : ℂ => g x * (ℓ x / (x - s)))
        (deriv g z * (ℓ z / (z - s))
          + g z * ((G z / (q z * y1 z * g z) * (z - s) - ℓ z * 1) / (z - s) ^ 2)) z :=
      ((hgd.differentiableAt (hballo.mem_nhds hz)).hasDerivAt).mul hdiv
    have h2 : HasDerivAt ζp (deriv g z * (ℓ z / (z - s))
        + g z * ((G z / (q z * y1 z * g z) * (z - s) - ℓ z * 1) / (z - s) ^ 2)) z :=
      h1.congr_of_eventuallyEq hEq
    refine h2.congr_deriv ?_
    rw [hg_deriv z hz, hAdef, hA0def, hA1def, hζpdef]
    simp only []
    rw [hdℓz, hP2fac z hz]
    have hgz2 : g z ≠ 0 := hgz
    field_simp
    ring
  -- ## 4. the solution `φ` and the first-order equation for `v = (φ/y1)'`
  set w : ℂ → ℂ := fun z => φ z / y1 z with hwdef
  set Wr : ℂ → ℂ := fun z => y1 z * deriv φ z - deriv y1 z * φ z with hWrdef
  set v : ℂ → ℂ := fun z => Wr z / (y1 z) ^ 2 with hvdef
  have hφd' : DifferentiableOn ℂ (deriv φ) Ω := hφd.deriv hΩo
  have hw_deriv : ∀ z ∈ Ω, HasDerivAt w (v z) z := by
    intro z hz
    have hzB : z ∈ Metric.ball s δ := hΩsub hz
    have hy1z : y1 z ≠ 0 := hy1ne z hzB
    have h1 : HasDerivAt (fun x : ℂ => φ x / y1 x)
        ((deriv φ z * y1 z - φ z * deriv y1 z) / (y1 z) ^ 2) z :=
      ((hφd.differentiableAt (hΩo.mem_nhds hz)).hasDerivAt).div
        ((hy1d.differentiableAt (hballo.mem_nhds hzB)).hasDerivAt) hy1z
    have h2 : HasDerivAt w ((deriv φ z * y1 z - φ z * deriv y1 z) / (y1 z) ^ 2) z := by
      rw [hwdef]; exact h1
    refine h2.congr_deriv ?_
    rw [hvdef, hWrdef]
    ring
  have hv_ode : ∀ z ∈ Ω, HasDerivAt v (-(A z) * v z + G z / (P2 z * y1 z)) z := by
    intro z hz
    have hzB : z ∈ Metric.ball s δ := hΩsub hz
    have hzs : z ≠ s := fun h => hsΩ (h ▸ hz)
    have hy1z : y1 z ≠ 0 := hy1ne z hzB
    have hqz : q z ≠ 0 := hqne z hzB
    have hP2z : P2 z ≠ 0 := by
      rw [hP2fac z hzB]; exact mul_ne_zero (sub_ne_zero.mpr hzs) hqz
    have hWr_deriv : HasDerivAt Wr (y1 z * deriv (deriv φ) z - deriv (deriv y1) z * φ z) z := by
      rw [hWrdef]
      have h1 : HasDerivAt (fun x : ℂ => y1 x * deriv φ x)
          (deriv y1 z * deriv φ z + y1 z * deriv (deriv φ) z) z :=
        ((hy1d.differentiableAt (hballo.mem_nhds hzB)).hasDerivAt).mul
          ((hφd'.differentiableAt (hΩo.mem_nhds hz)).hasDerivAt)
      have h2 : HasDerivAt (fun x : ℂ => deriv y1 x * φ x)
          (deriv (deriv y1) z * φ z + deriv y1 z * deriv φ z) z :=
        ((hdy1d.differentiableAt (hballo.mem_nhds hzB)).hasDerivAt).mul
          ((hφd.differentiableAt (hΩo.mem_nhds hz)).hasDerivAt)
      exact (h1.sub h2).congr_deriv (by ring)
    have hWr_ode : HasDerivAt Wr ((y1 z * G z - P1 z * Wr z) / P2 z) z := by
      refine hWr_deriv.congr_deriv ?_
      have e1 : P2 z * deriv (deriv φ) z = G z - P1 z * deriv φ z - P0 z * φ z := by
        linear_combination hφode z hz
      have e2 : P2 z * deriv (deriv y1) z = -(P1 z * deriv y1 z) - P0 z * y1 z := by
        linear_combination hy1ode z hzB
      have key : P2 z * (y1 z * deriv (deriv φ) z - deriv (deriv y1) z * φ z)
          = y1 z * G z - P1 z * Wr z := by
        rw [hWrdef]; linear_combination (y1 z) * e1 - (φ z) * e2
      rw [eq_div_iff hP2z]
      linear_combination key
    have hv' : HasDerivAt v ((((y1 z * G z - P1 z * Wr z) / P2 z) * (y1 z) ^ 2
        - Wr z * (2 * y1 z * deriv y1 z)) / (((y1 z) ^ 2) ^ 2)) z := by
      rw [hvdef]
      exact hWr_ode.div (hpow_d z hzB) (pow_ne_zero 2 hy1z)
    refine hv'.congr_deriv ?_
    have hA1z : A1 z = P1 z / P2 z - 1 / (z - s) := by
      linear_combination hA1eq z hzB hzs
    rw [hvdef, hWrdef, hAdef, hA0def]
    simp only []
    rw [hA1z, hP2fac z hzB]
    field_simp
    ring
  -- ## 5. the general solution of the first-order equation
  set u : ℂ → ℂ := fun z => (v z - ζp z) / ζh z with hudef
  have hζhne : ∀ z ∈ Ω, ζh z ≠ 0 := by
    intro z hz
    have hzB : z ∈ Metric.ball s δ := hΩsub hz
    have hzs : z ≠ s := fun h => hsΩ (h ▸ hz)
    rw [hζhdef]
    exact div_ne_zero (hgne z hzB) (sub_ne_zero.mpr hzs)
  have hwd : DifferentiableOn ℂ w Ω :=
    fun z hz => (hw_deriv z hz).differentiableAt.differentiableWithinAt
  have hvd : DifferentiableOn ℂ v Ω :=
    (hwd.deriv hΩo).congr (fun z hz => ((hw_deriv z hz).deriv).symm)
  have hζhd : DifferentiableOn ℂ ζh Ω := by
    rw [hζhdef]
    refine (hgd.mono hΩsub).div (by fun_prop) ?_
    intro z hz
    exact sub_ne_zero.mpr (fun h => hsΩ (h ▸ hz))
  have hud : DifferentiableOn ℂ u Ω := by
    rw [hudef]
    refine (hvd.sub (hζpd.mono hΩsub)).div hζhd ?_
    intro z hz
    exact hζhne z hz
  have huderiv : Set.EqOn (deriv u) 0 Ω := by
    intro z hz
    have hzB : z ∈ Metric.ball s δ := hΩsub hz
    have hzs : z ≠ s := fun h => hsΩ (h ▸ hz)
    have hv' := hv_ode z hz
    have hζp' := hζp_deriv z hzB hzs
    have hζh' := hζh_deriv z hzB hzs
    have hsub : HasDerivAt (fun x : ℂ => v x - ζp x) (-(A z) * (v z - ζp z)) z :=
      (hv'.sub hζp').congr_deriv (by ring)
    have h1 : HasDerivAt ((fun x : ℂ => v x - ζp x) / ζh) 0 z := by
      refine (hsub.div hζh' (hζhne z hz)).congr_deriv ?_
      have hζhz : ζh z ≠ 0 := hζhne z hz
      field_simp
      ring
    have h2 : HasDerivAt u 0 z := by rw [hudef]; exact h1
    exact h2.deriv
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ z ∈ Ω, v z = ζp z + c * ζh z := by
    by_cases hne : Ω.Nonempty
    · refine ⟨u hne.choose, fun z hz => ?_⟩
      have hzu : (v z - ζp z) / ζh z = u hne.choose := by
        have h := IsOpen.is_const_of_deriv_eq_zero hΩo hΩc hud huderiv hz hne.choose_spec
        simpa only [hudef] using h
      rw [div_eq_iff (hζhne z hz)] at hzu
      rw [← hzu]
      ring
    · exact ⟨0, fun z hz => absurd ⟨z, hz⟩ hne⟩
  -- ## 6. the last steps: `κ`, `L`, the primitive `W₁` and the constant
  have hLd : DifferentiableOn ℂ (fun z => g z * (ℓ z + c)) (Metric.ball s δ) :=
    hgd.mul (hℓd.add_const c)
  have hdsLd : DifferentiableOn ℂ (dslope (fun z => g z * (ℓ z + c)) s) (Metric.ball s δ) :=
    (Complex.differentiableOn_dslope (f := fun z => g z * (ℓ z + c)) (s := Metric.ball s δ)
      (c := s) hball).mpr hLd
  obtain ⟨W1, hW1⟩ : ∃ W1 : ℂ → ℂ,
      ∀ z ∈ Metric.ball s δ, HasDerivAt W1 (dslope (fun z => g z * (ℓ z + c)) s z) z :=
    (hdsLd.isExactOn_ball)
  have hW1d : DifferentiableOn ℂ W1 (Metric.ball s δ) :=
    fun z hz => (hW1 z hz).differentiableAt.differentiableWithinAt
  have hw_deriv2 : ∀ z ∈ Ω, HasDerivAt w ((fun x => g x * (ℓ x + c)) z / (z - s)) z := by
    intro z hz
    have hzB : z ∈ Metric.ball s δ := hΩsub hz
    have hzs : z ≠ s := fun h => hsΩ (h ▸ hz)
    have hdℓz : dslope ℓ s z = ℓ z / (z - s) := hdsl_ne z hzs
    have h1 := hw_deriv z hz
    rw [hc z hz] at h1
    refine h1.congr_deriv ?_
    rw [hζpdef, hζhdef]
    simp only []
    rw [hdℓz]
    try field_simp
    try ring
  set κ : ℂ := (fun x => g x * (ℓ x + c)) s with hκdef
  have hF_deriv : ∀ z ∈ Ω,
      HasDerivAt (fun x => w x - κ * Complex.log (s - x) - W1 x) 0 z := by
    intro z hz
    have hzs : z ≠ s := fun h => hsΩ (h ▸ hz)
    have h1 := hw_deriv2 z hz
    have h2 : HasDerivAt (fun x : ℂ => Complex.log (s - x)) (1 / (z - s)) z :=
      hasDerivAt_log_sub (hslit z hz)
    have h3 : HasDerivAt (fun x : ℂ => κ * Complex.log (s - x)) (κ * (1 / (z - s))) z :=
      h2.const_mul κ
    have h4 : HasDerivAt W1 (dslope (fun x => g x * (ℓ x + c)) s z) z :=
      hW1 z (hΩsub hz)
    refine ((h1.sub h3).sub h4).congr_deriv ?_
    rw [hκdef, dslope_eq_div (fun x => g x * (ℓ x + c)) hzs]
    field_simp
    ring
  obtain ⟨C, hC⟩ : ∃ C : ℂ, ∀ z ∈ Ω, w z - κ * Complex.log (s - z) - W1 z = C := by
    by_cases hne : Ω.Nonempty
    · refine ⟨w hne.choose - κ * Complex.log (s - hne.choose) - W1 hne.choose, fun z hz => ?_⟩
      exact IsOpen.is_const_of_deriv_eq_zero hΩo hΩc
        (fun z hz => (hF_deriv z hz).differentiableAt.differentiableWithinAt)
        (fun z hz => (hF_deriv z hz).deriv) hz hne.choose_spec
    · exact ⟨0, fun z hz => absurd ⟨z, hz⟩ hne⟩
  refine ⟨κ, fun z => W1 z + C, hW1d.add_const C, fun z hz => ?_⟩
  have hy1z : y1 z ≠ 0 := hy1ne z (hΩsub hz)
  have h := hC z hz
  rw [hwdef] at h
  simp only [] at h
  show φ z = κ * y1 z * Complex.log (s - z) + y1 z * (W1 z + C)
  field_simp
  field_simp at h
  linear_combination h

/-- **The local structure of the unlikely series `Pfun` at its cusp `x_s`.**
There are `δ > 0`, `κ ≠ 0`, a solution `y₁` of the homogeneous equation `M(y₁) = 0` on
`ball x_s δ` with `y₁ x_s ≠ 0`, and a holomorphic `hh` on `ball x_s δ`, such that
`Pfun = κ·y₁·log(x_s − ·) + hh` on `ball x_s δ ∩ ball 0 x_s`. -/
theorem logP_local_structure (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a < b)
    (ra rb rab r0 : ℤ)
    (hQ4 : (Q4x a b).eval₂ (algebraMap ℚ ℂ) ((xs a b : ℝ) : ℂ) = 0)
    (hconv : ∀ z : ℂ, ‖z‖ < xs a b →
      HasSum (fun n : ℕ => ((PowerSeries.coeff n (Submission.CDT.logP a b ra rb rab r0) : ℚ) : ℂ) * z ^ n)
        (Pfun a b ra rb rab r0 z))
    (hnot : ¬ ∃ (g : ℂ → ℂ) (δ : ℝ), 0 < δ ∧
      DifferentiableOn ℂ g (Metric.ball ((xs a b : ℝ) : ℂ) δ) ∧
      ∀ z ∈ Metric.ball ((xs a b : ℝ) : ℂ) δ ∩ Metric.ball (0 : ℂ) (xs a b),
        g z = Pfun a b ra rb rab r0 z) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ (κ : ℂ) (y1 hh : ℂ → ℂ), κ ≠ 0 ∧
      y1 (((xs a b : ℝ) : ℂ)) ≠ 0 ∧
      DifferentiableOn ℂ y1 (Metric.ball ((xs a b : ℝ) : ℂ) δ) ∧
      DifferentiableOn ℂ hh (Metric.ball ((xs a b : ℝ) : ℂ) δ) ∧
      (∀ z ∈ Metric.ball ((xs a b : ℝ) : ℂ) δ,
        (P2x a b).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv y1) z
          + (P1x a b).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z
          + (P0x a b).eval₂ (algebraMap ℚ ℂ) z * y1 z = 0) ∧
      (∀ z ∈ Metric.ball ((xs a b : ℝ) : ℂ) δ ∩ Metric.ball (0 : ℂ) (xs a b),
        Pfun a b ra rb rab r0 z = κ * y1 z * Complex.log (((xs a b : ℝ) : ℂ) - z) + hh z) := by
  classical
  obtain ⟨hxs_pos, hxs_sq_lt_one⟩ := xs_pos_and_sq_lt_one' a b ha hb hab
  obtain ⟨hP2fac, hQ2ne, hP1Q2, _hSdiv⟩ := Work.C17f.xs_factor_data a b ha hb hab hQ4
  set s : ℂ := ((xs a b : ℝ) : ℂ) with hsdef
  have hsnorm : ‖s‖ = xs a b := by
    rw [hsdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxs_pos]
  -- ## the function-level factorisation data at `x_s`
  have hP2fun : ∀ z : ℂ, (P2x a b).eval₂ (algebraMap ℚ ℂ) z = (z - s) * (Q2x a b).eval z := by
    intro z
    have h := congrArg (fun p : Polynomial ℂ => p.eval z) hP2fac
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval₂_eq_eval_map] at h ⊢
    simp only [xsC, ← hsdef] at h
    exact h
  have hres : (P1x a b).eval₂ (algebraMap ℚ ℂ) s = (Q2x a b).eval s := by
    simpa only [xsC, ← hsdef] using hP1Q2
  -- ## the homogeneous solution `y₁` (Fuchs/Frobenius at the double exponent `0`)
  obtain ⟨δ₁, hδ₁, y1, hy1d₁, hy1s, hy1ode₁⟩ :
      ∃ δ : ℝ, 0 < δ ∧ ∃ y : ℂ → ℂ,
        DifferentiableOn ℂ y (Metric.ball s δ) ∧ y s = 1 ∧
        ∀ z ∈ Metric.ball s δ, (P2x a b).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv y) z
          + (P1x a b).eval₂ (algebraMap ℚ ℂ) z * deriv y z
          + (P0x a b).eval₂ (algebraMap ℚ ℂ) z * y z = 0 := by
    refine Work.C17f.frobenius_double_exponent_zero
      (P2 := fun z => (P2x a b).eval₂ (algebraMap ℚ ℂ) z)
      (P1 := fun z => (P1x a b).eval₂ (algebraMap ℚ ℂ) z)
      (P0 := fun z => (P0x a b).eval₂ (algebraMap ℚ ℂ) z)
      (q := fun z => (Q2x a b).eval z) (s := s) 1 ?_ ?_ ?_ ?_ ?_ ?_
    · exact hP2fun
    · exact AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) (Q2x a b) s (Set.mem_univ s)
    · simpa only [xsC, ← hsdef] using hQ2ne
    · simpa only [Polynomial.eval₂_eq_eval_map] using
        (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) ((P1x a b).map (algebraMap ℚ ℂ))
          s (Set.mem_univ s))
    · exact hres
    · simpa only [Polynomial.eval₂_eq_eval_map] using
        (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) ((P0x a b).map (algebraMap ℚ ℂ))
          s (Set.mem_univ s))
  -- ## shrink the radius so that `y₁` and `q` do not vanish
  obtain ⟨δ₂, hδ₂, hy1ne₂⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∀ z ∈ Metric.ball s δ, y1 z ≠ 0 := by
    have hcont : ContinuousAt y1 s :=
      (hy1d₁.differentiableAt (Metric.ball_mem_nhds s hδ₁)).continuousAt
    have hnhds : {z : ℂ | y1 z ≠ 0} ∈ 𝓝 s :=
      hcont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds (by simp [hy1s]))
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hnhds
    exact ⟨ε, hε, fun z hz => hsub hz⟩
  obtain ⟨δ₃, hδ₃, hQ2ne₃⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∀ z ∈ Metric.ball s δ, (Q2x a b).eval z ≠ 0 := by
    have hcont : ContinuousAt (fun z : ℂ => (Q2x a b).eval z) s :=
      (Polynomial.continuous (Q2x a b)).continuousAt
    have hnhds : {z : ℂ | (Q2x a b).eval z ≠ 0} ∈ 𝓝 s :=
      hcont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds (by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        simpa only [xsC, ← hsdef] using hQ2ne))
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hnhds
    exact ⟨ε, hε, fun z hz => hsub hz⟩
  set δ : ℝ := min δ₁ (min δ₂ δ₃) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min hδ₁ (lt_min hδ₂ hδ₃)
  have hδ1 : δ ≤ δ₁ := by rw [hδdef]; exact min_le_left _ _
  have hδ2 : δ ≤ δ₂ := by rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ3 : δ ≤ δ₃ := by rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hy1d : DifferentiableOn ℂ y1 (Metric.ball s δ) :=
    hy1d₁.mono (Metric.ball_subset_ball hδ1)
  have hy1ne : ∀ z ∈ Metric.ball s δ, y1 z ≠ 0 :=
    fun z hz => hy1ne₂ z (Metric.ball_subset_ball hδ2 hz)
  have hqne : ∀ z ∈ Metric.ball s δ, (Q2x a b).eval z ≠ 0 :=
    fun z hz => hQ2ne₃ z (Metric.ball_subset_ball hδ3 hz)
  have hy1ode : ∀ z ∈ Metric.ball s δ, (P2x a b).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv y1) z
      + (P1x a b).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z
      + (P0x a b).eval₂ (algebraMap ℚ ℂ) z * y1 z = 0 :=
    fun z hz => hy1ode₁ z (Metric.ball_subset_ball hδ1 hz)
  -- ## `Pfun` solves the inhomogeneous equation on its disc
  have hφd₀ : DifferentiableOn ℂ (Pfun a b ra rb rab r0) (Metric.ball 0 (xs a b)) :=
    Work.C17f.differentiableOn_of_hasSum_powSeries
      (c := fun n => ((PowerSeries.coeff n (Submission.CDT.logP a b ra rb rab r0) : ℚ) : ℂ))
      (r := xs a b) (F := Pfun a b ra rb rab r0) (fun z hz => hconv z hz)
  have hφode₀ : ∀ z : ℂ, ‖z‖ < xs a b →
      (P2x a b).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv (Pfun a b ra rb rab r0)) z
        + (P1x a b).eval₂ (algebraMap ℚ ℂ) z * deriv (Pfun a b ra rb rab r0) z
        + (P0x a b).eval₂ (algebraMap ℚ ℂ) z * Pfun a b ra rb rab r0 z
      = (rhoMx a b ra rb rab).eval₂ (algebraMap ℚ ℂ) z :=
    Work.C17f.Pfun_solves_M a b ra rb rab r0 hconv
  -- ## the region `Ω = ball x_s δ ∩ ball 0 x_s`
  set Ω : Set ℂ := Metric.ball s δ ∩ Metric.ball 0 (xs a b) with hΩdef
  have hΩo : IsOpen Ω := Metric.isOpen_ball.inter Metric.isOpen_ball
  have hΩc : IsPreconnected Ω :=
    ((convex_ball s δ).inter (convex_ball 0 (xs a b))).isPreconnected
  have hΩsub : Ω ⊆ Metric.ball s δ := Set.inter_subset_left
  have hsΩ : s ∉ Ω := by
    intro h
    have h1 : ‖s‖ < xs a b := by
      have := h.2
      rwa [Metric.mem_ball, dist_zero_right] at this
    rw [hsnorm] at h1
    exact lt_irrefl _ h1
  have hslit : ∀ z ∈ Ω, s - z ∈ Complex.slitPlane := by
    intro z hz
    have hz2 : ‖z‖ < xs a b := by
      have := hz.2
      rwa [Metric.mem_ball, dist_zero_right] at this
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have hre : (s - z).re = xs a b - z.re := by
      rw [hsdef, Complex.sub_re, Complex.ofReal_re]
    rw [hre]
    have := Complex.re_le_norm z
    linarith
  have hφd : DifferentiableOn ℂ (Pfun a b ra rb rab r0) Ω := hφd₀.mono Set.inter_subset_right
  have hφode : ∀ z ∈ Ω, (P2x a b).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv (Pfun a b ra rb rab r0)) z
      + (P1x a b).eval₂ (algebraMap ℚ ℂ) z * deriv (Pfun a b ra rb rab r0) z
      + (P0x a b).eval₂ (algebraMap ℚ ℂ) z * Pfun a b ra rb rab r0 z
      = (rhoMx a b ra rb rab).eval₂ (algebraMap ℚ ℂ) z := by
    intro z hz
    refine hφode₀ z ?_
    have := hz.2
    rwa [Metric.mem_ball, dist_zero_right] at this
  -- ## the analytic data on the ball
  have hpoly : ∀ (p : Polynomial ℂ), DifferentiableOn ℂ (fun z : ℂ => p.eval z) (Metric.ball s δ) :=
    fun p z _ => (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) p z
      (Set.mem_univ z)).differentiableWithinAt
  have hqd : DifferentiableOn ℂ (fun z : ℂ => (Q2x a b).eval z) (Metric.ball s δ) :=
    hpoly (Q2x a b)
  have hP1d : DifferentiableOn ℂ (fun z : ℂ => (P1x a b).eval₂ (algebraMap ℚ ℂ) z)
      (Metric.ball s δ) := by
    simpa only [Polynomial.eval₂_eq_eval_map] using hpoly ((P1x a b).map (algebraMap ℚ ℂ))
  have hP0d : DifferentiableOn ℂ (fun z : ℂ => (P0x a b).eval₂ (algebraMap ℚ ℂ) z)
      (Metric.ball s δ) := by
    simpa only [Polynomial.eval₂_eq_eval_map] using hpoly ((P0x a b).map (algebraMap ℚ ℂ))
  have hGd : DifferentiableOn ℂ (fun z : ℂ => (rhoMx a b ra rb rab).eval₂ (algebraMap ℚ ℂ) z)
      (Metric.ball s δ) := by
    simpa only [Polynomial.eval₂_eq_eval_map] using
      hpoly ((rhoMx a b ra rb rab).map (algebraMap ℚ ℂ))
  -- ## the core
  obtain ⟨κ, W0, hW0d, hW0eq⟩ := local_structure_core (s := s) (δ := δ) hδpos
    (y1 := y1) (φ := Pfun a b ra rb rab r0)
    (P2 := fun z => (P2x a b).eval₂ (algebraMap ℚ ℂ) z)
    (P1 := fun z => (P1x a b).eval₂ (algebraMap ℚ ℂ) z)
    (P0 := fun z => (P0x a b).eval₂ (algebraMap ℚ ℂ) z)
    (G := fun z => (rhoMx a b ra rb rab).eval₂ (algebraMap ℚ ℂ) z)
    (q := fun z => (Q2x a b).eval z)
    hy1d hy1ne hy1ode (fun z _ => hP2fun z) hqd hqne hres hP1d hP0d hGd hΩo hΩc hΩsub hsΩ hslit hφd hφode
  refine ⟨δ, hδpos, κ, y1, fun z => y1 z * W0 z, ?_, ?_, hy1d, ?_, hy1ode, ?_⟩
  · -- `κ ≠ 0`: otherwise `Pfun` would extend holomorphically across `x_s`
    intro hκ
    refine hnot ⟨fun z => y1 z * W0 z, δ, hδpos, hy1d.mul hW0d, ?_⟩
    intro z hz
    have h := hW0eq z hz
    rw [hκ, zero_mul, zero_mul, zero_add] at h
    exact h.symm
  · -- `y₁ x_s ≠ 0`
    rw [hy1s]
    norm_num
  · exact hy1d.mul hW0d
  · intro z hz
    exact hW0eq z hz

end

end Work.C17
