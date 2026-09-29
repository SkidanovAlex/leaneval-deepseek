import Mathlib
import Submission.Work.A14D.local_core_pub

/-!
# Frobenius at a double indicial exponent `0` with a simple-pole source

Same setting as `Work.A14D.local_structure_core`, but for the inhomogeneous equation
`P2 φ'' + P1 φ' + P0 φ = A/(s-z) + G`.  The pole term resonating with the double exponent
produces a *double* logarithm whose top coefficient is forced.

The proof follows the same reduction of order as `local_structure_core`; the extra source
contributes a term of the first-order equation solved by `vp`, and the final assembly uses
primitives on the ball together with the fact that `A / (2 (y1 s * q s)) = -A * h s * g s / 2`
where `h = y1 · exp Q / q` and `g = -exp(-Q)/y1²`.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

noncomputable section

/-- Frobenius at a regular singular point with double indicial exponent `0`, for a source with a
*simple pole* `A/(s-z)`.  If `P2 z = (z-s) * q z` with `q s ≠ 0`, `P1 s = q s` (the two indicial
exponents are `0,0`), `y1` is a non-vanishing holomorphic solution of the homogeneous equation on
`ball s δ`, and `φ` solves `P2 φ'' + P1 φ' + P0 φ = A/(s-z) + G` on an open preconnected
`Ω ⊆ ball s δ` with `s ∉ Ω` and `s - z ∈ slitPlane` on `Ω`, then `φ` has a *double logarithm* with
top coefficient `-A/(2 (y1 s * q s))`:
`φ = e0 + e1·log(s-z) - (A/(2 (y1 s * q s))) · y1 · (log(s-z))^2`
with `e0, e1` holomorphic on the whole ball `ball s δ`. -/
theorem frobenius_double_exponent_simple_pole {s : ℂ} {δ : ℝ} (hδ : 0 < δ)
    {y1 φ : ℂ → ℂ} {P2 P1 P0 G : ℂ → ℂ} {Ω : Set ℂ} {q : ℂ → ℂ} {A : ℂ}
    (hy1d : DifferentiableOn ℂ y1 (Metric.ball s δ))
    (hy1ne : ∀ z ∈ Metric.ball s δ, y1 z ≠ 0)
    (hy1s : y1 s ≠ 0)
    (hy1ode : ∀ z ∈ Metric.ball s δ,
      P2 z * deriv (deriv y1) z + P1 z * deriv y1 z + P0 z * y1 z = 0)
    (hP2fac : ∀ z ∈ Metric.ball s δ, P2 z = (z - s) * q z)
    (hqd : DifferentiableOn ℂ q (Metric.ball s δ))
    (hqne : ∀ z ∈ Metric.ball s δ, q z ≠ 0)
    (hqs : q s ≠ 0)
    (hres : P1 s = q s)
    (hP1d : DifferentiableOn ℂ P1 (Metric.ball s δ))
    (hP0d : DifferentiableOn ℂ P0 (Metric.ball s δ))
    (hGd : DifferentiableOn ℂ G (Metric.ball s δ))
    (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω) (hΩsub : Ω ⊆ Metric.ball s δ)
    (hsΩ : s ∉ Ω)
    (hslit : ∀ z ∈ Ω, s - z ∈ Complex.slitPlane)
    (hφd : DifferentiableOn ℂ φ Ω)
    (hφode : ∀ z ∈ Ω,
      P2 z * deriv (deriv φ) z + P1 z * deriv φ z + P0 z * φ z = A / (s - z) + G z) :
    ∃ e0 e1 : ℂ → ℂ, DifferentiableOn ℂ e0 (Metric.ball s δ) ∧
      DifferentiableOn ℂ e1 (Metric.ball s δ) ∧
      ∀ z ∈ Ω, φ z = e0 z + e1 z * Complex.log (s - z)
        - (A / (2 * (y1 s * q s))) * y1 z * (Complex.log (s - z)) ^ 2 := by
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
  -- ## 2. an antiderivative of `A1`, and the functions `A0`, `Af`, `g`, `ζh`
  obtain ⟨Qant, hQant0, hQant⟩ : ∃ Qant : ℂ → ℂ, Qant s = 0 ∧
      ∀ z ∈ Metric.ball s δ, HasDerivAt Qant (A1 z) z := by
    obtain ⟨Q, hQ0, hQ⟩ := (hA1d.isExactOn_ball).with_val_at s 0
    exact ⟨Q, hQ0, hQ⟩
  have hQantd : DifferentiableOn ℂ Qant (Metric.ball s δ) :=
    fun z hz => (hQant z hz).differentiableAt.differentiableWithinAt
  set A0 : ℂ → ℂ := fun z => 2 * deriv y1 z / y1 z + A1 z with hA0def
  set Af : ℂ → ℂ := fun z => 1 / (z - s) + A0 z with hAfdef
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
  have hζh_deriv : ∀ z ∈ Metric.ball s δ, z ≠ s → HasDerivAt ζh (-(Af z) * ζh z) z := by
    intro z hz hzs
    have h1 : HasDerivAt (fun x : ℂ => g x / (x - s))
        ((deriv g z * (z - s) - g z * 1) / (z - s) ^ 2) z := by
      refine ((hgd.differentiableAt (hballo.mem_nhds hz)).hasDerivAt).div ?_ ?_
      · exact (hasDerivAt_id z).sub_const s
      · exact sub_ne_zero.mpr hzs
    have h2 : HasDerivAt ζh ((deriv g z * (z - s) - g z * 1) / (z - s) ^ 2) z := by
      rw [hζhdef]; exact h1
    refine h2.congr_deriv ?_
    rw [hg_deriv z hz, hζhdef, hAfdef, hA0def, hA1def]
    field_simp
    ring
  -- ## 2b. the function `h = y1·exp Q/q`, the constant `c'`, the primitive `M0`
  set hh : ℂ → ℂ := fun z => y1 z * Complex.exp (Qant z) / q z with hhhdef
  have hhd : DifferentiableOn ℂ hh (Metric.ball s δ) := by
    rw [hhhdef]
    exact (hy1d.mul hQantd.cexp).div hqd hqne
  have hhs : hh s = y1 s / q s := by
    simp only [hhhdef, hQant0, Complex.exp_zero]
    ring
  have hgh : ∀ z ∈ Metric.ball s δ, g z * hh z = -1 / (q z * y1 z) := by
    intro z hz
    have hy1z : y1 z ≠ 0 := hy1ne z hz
    have hqz : q z ≠ 0 := hqne z hz
    simp only [hgdef, hhhdef]
    field_simp
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have hgs : g s = -1 / (y1 s) ^ 2 := by
    simp only [hgdef, hQant0, neg_zero, Complex.exp_zero]
    ring
  set c' : ℂ := -(A / (2 * (y1 s * q s))) with hc'def
  have h2c : A * hh s * g s = 2 * c' := by
    rw [hhs, hgs, hc'def]
    field_simp
    try ring
  have hdshh : DifferentiableOn ℂ (dslope hh s) (Metric.ball s δ) :=
    (Complex.differentiableOn_dslope (f := hh) (s := Metric.ball s δ) (c := s) hball).mpr hhd
  set φ2 : ℂ → ℂ := fun z => A * dslope hh s z with hφ2def
  have hφ2d : DifferentiableOn ℂ φ2 (Metric.ball s δ) := by
    rw [hφ2def]
    exact (differentiableOn_const (A : ℂ)).mul hdshh
  obtain ⟨M0, hM0s, hM0⟩ : ∃ M0 : ℂ → ℂ, M0 s = 0 ∧
      ∀ z ∈ Metric.ball s δ, HasDerivAt M0 (φ2 z) z := by
    obtain ⟨M, hMv, hM⟩ := (hφ2d.isExactOn_ball).with_val_at s 0
    exact ⟨M, hMv, hM⟩
  have hM0d : DifferentiableOn ℂ M0 (Metric.ball s δ) :=
    fun z hz => (hM0 z hz).differentiableAt.differentiableWithinAt
  -- ## 3. the primitive `ℓ` of the `G`-part
  have hΨd : DifferentiableOn ℂ (fun z => G z / (q z * y1 z * g z)) (Metric.ball s δ) :=
    hGd.div ((hqd.mul hy1d).mul hgd)
      (fun z hz => mul_ne_zero (mul_ne_zero (hqne z hz) (hy1ne z hz)) (hgne z hz))
  obtain ⟨ℓ, hℓ0, hℓ⟩ : ∃ ℓ : ℂ → ℂ, ℓ s = 0 ∧
      ∀ z ∈ Metric.ball s δ, HasDerivAt ℓ (G z / (q z * y1 z * g z)) z := by
    obtain ⟨L, hL0, hL⟩ := (hΨd.isExactOn_ball).with_val_at s 0
    exact ⟨L, hL0, hL⟩
  have hℓd : DifferentiableOn ℂ ℓ (Metric.ball s δ) :=
    fun z hz => (hℓ z hz).differentiableAt.differentiableWithinAt
  -- ## 4. the reduction `v = Wr/y1²` and its first-order equation
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
  have hv_ode : ∀ z ∈ Ω,
      HasDerivAt v (-(Af z) * v z + (A / (s - z) + G z) / (P2 z * y1 z)) z := by
    intro z hz
    have hzB : z ∈ Metric.ball s δ := hΩsub hz
    have hzs : z ≠ s := fun h => hsΩ (h ▸ hz)
    have hsz : s - z ≠ 0 := sub_ne_zero.mpr (fun h => hzs h.symm)
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
    have hWr_ode : HasDerivAt Wr ((y1 z * (A / (s - z) + G z) - P1 z * Wr z) / P2 z) z := by
      refine hWr_deriv.congr_deriv ?_
      have e1 : P2 z * deriv (deriv φ) z
          = (A / (s - z) + G z) - P1 z * deriv φ z - P0 z * φ z := by
        linear_combination hφode z hz
      have e2 : P2 z * deriv (deriv y1) z = -(P1 z * deriv y1 z) - P0 z * y1 z := by
        linear_combination hy1ode z hzB
      have key : P2 z * (y1 z * deriv (deriv φ) z - deriv (deriv y1) z * φ z)
          = y1 z * (A / (s - z) + G z) - P1 z * Wr z := by
        rw [hWrdef]; linear_combination (y1 z) * e1 - (φ z) * e2
      rw [eq_div_iff hP2z]
      linear_combination key
    have hv' : HasDerivAt v ((((y1 z * (A / (s - z) + G z) - P1 z * Wr z) / P2 z) * (y1 z) ^ 2
        - Wr z * (2 * y1 z * deriv y1 z)) / (((y1 z) ^ 2) ^ 2)) z := by
      rw [hvdef]
      exact hWr_ode.div (hpow_d z hzB) (pow_ne_zero 2 hy1z)
    refine hv'.congr_deriv ?_
    have hA1z : A1 z = P1 z / P2 z - 1 / (z - s) := by
      linear_combination hA1eq z hzB hzs
    rw [hvdef, hWrdef, hAfdef, hA0def]
    simp only []
    rw [hA1z, hP2fac z hzB]
    field_simp
    ring
  -- ## 5. a particular solution `vp` of this first-order equation, and `u = (v - vp)/ζh`
  set vp : ℂ → ℂ := fun z => ζh z * (ℓ z + M0 z + A * hh s * Complex.log (s - z)) with hvpdef
  have hvp_deriv : ∀ z ∈ Ω,
      HasDerivAt vp (-(Af z) * vp z + (A / (s - z) + G z) / (P2 z * y1 z)) z := by
    intro z hz
    have hzB : z ∈ Metric.ball s δ := hΩsub hz
    have hzs : z ≠ s := fun h => hsΩ (h ▸ hz)
    have hsz : s - z ≠ 0 := sub_ne_zero.mpr (fun h => hzs h.symm)
    have hy1z : y1 z ≠ 0 := hy1ne z hzB
    have hqz : q z ≠ 0 := hqne z hzB
    have hgz : g z ≠ 0 := hgne z hzB
    have hP2z : P2 z ≠ 0 := by
      rw [hP2fac z hzB]; exact mul_ne_zero (sub_ne_zero.mpr hzs) hqz
    have hsum : HasDerivAt (fun x : ℂ => ℓ x + M0 x + A * hh s * Complex.log (s - x))
        (G z / (q z * y1 z * g z) + φ2 z + A * hh s * (1 / (z - s))) z :=
      ((hℓ z hzB).add (hM0 z hzB)).add
        ((hasDerivAt_log_sub (hslit z hz)).const_mul (A * hh s))
    have hmain : HasDerivAt vp (-(Af z) * vp z
        + ζh z * (G z / (q z * y1 z * g z) + φ2 z + A * hh s * (1 / (z - s)))) z := by
      have hmul := (hζh_deriv z hzB hzs).mul hsum
      refine hmul.congr_deriv ?_
      rw [hvpdef]
      ring
    refine hmain.congr_deriv ?_
    have hGpart : ζh z * (G z / (q z * y1 z * g z)) = G z / ((z - s) * q z * y1 z) := by
      simp only [hζhdef]; field_simp; try ring
    have hPpart : ζh z * (φ2 z + A * hh s * (1 / (z - s)))
        = A / ((s - z) * ((z - s) * q z * y1 z)) := by
      have key : ζh z * (φ2 z + A * hh s * (1 / (z - s))) = A / (z - s) ^ 2 * (g z * hh z) := by
        simp only [hζhdef, hφ2def]
        rw [dslope_eq_div hh hzs]
        field_simp
        try ring
      rw [key, hgh z hzB]
      field_simp
      try ring
    rw [show ζh z * (G z / (q z * y1 z * g z) + φ2 z + A * hh s * (1 / (z - s)))
        = ζh z * (G z / (q z * y1 z * g z))
          + ζh z * (φ2 z + A * hh s * (1 / (z - s))) from by ring,
      hGpart, hPpart, hP2fac z hzB]
    field_simp
    try ring
  set u : ℂ → ℂ := fun z => (v z - vp z) / ζh z with hudef
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
  have hlogd : DifferentiableOn ℂ (fun z => Complex.log (s - z)) Ω :=
    fun z hz => (hasDerivAt_log_sub (hslit z hz)).differentiableAt.differentiableWithinAt
  have hvpd : DifferentiableOn ℂ vp Ω := by
    rw [hvpdef]
    exact hζhd.mul (((hℓd.mono hΩsub).add (hM0d.mono hΩsub)).add
      ((differentiableOn_const (A * hh s)).mul hlogd))
  have hud : DifferentiableOn ℂ u Ω := by
    rw [hudef]
    exact (hvd.sub hvpd).div hζhd hζhne
  have huderiv : Set.EqOn (deriv u) 0 Ω := by
    intro z hz
    have hzB : z ∈ Metric.ball s δ := hΩsub hz
    have hzs : z ≠ s := fun h => hsΩ (h ▸ hz)
    have hv' := hv_ode z hz
    have hvp' := hvp_deriv z hz
    have hζh' := hζh_deriv z hzB hzs
    have hsub : HasDerivAt (fun x : ℂ => v x - vp x) (-(Af z) * (v z - vp z)) z :=
      (hv'.sub hvp').congr_deriv (by ring)
    have h1 : HasDerivAt ((fun x : ℂ => v x - vp x) / ζh) 0 z := by
      refine (hsub.div hζh' (hζhne z hz)).congr_deriv ?_
      have hζhz : ζh z ≠ 0 := hζhne z hz
      field_simp
      ring
    have h2 : HasDerivAt u 0 z := by rw [hudef]; exact h1
    exact h2.deriv
  obtain ⟨C, hC⟩ : ∃ C : ℂ, ∀ z ∈ Ω, v z = vp z + C * ζh z := by
    by_cases hne : Ω.Nonempty
    · refine ⟨u hne.choose, fun z hz => ?_⟩
      have hzu : (v z - vp z) / ζh z = u hne.choose := by
        have h := IsOpen.is_const_of_deriv_eq_zero hΩo hΩc hud huderiv hz hne.choose_spec
        simpa only [hudef] using h
      rw [div_eq_iff (hζhne z hz)] at hzu
      rw [← hzu]; ring
    · exact ⟨0, fun z hz => absurd ⟨z, hz⟩ hne⟩
  -- ## 6. the holomorphic correction functions on the ball
  set Gc : ℂ → ℂ := fun z => g z * (ℓ z + M0 z + C) with hGcdef
  have hGcd : DifferentiableOn ℂ Gc (Metric.ball s δ) := by
    rw [hGcdef]
    exact hgd.mul ((hℓd.add hM0d).add_const C)
  have hw_deriv2 : ∀ z ∈ Ω, HasDerivAt w
      ((Gc z + A * hh s * g z * Complex.log (s - z)) / (z - s)) z := by
    intro z hz
    have hzB : z ∈ Metric.ball s δ := hΩsub hz
    have hzs : z ≠ s := fun h => hsΩ (h ▸ hz)
    have hzsub : z - s ≠ 0 := sub_ne_zero.mpr hzs
    have h1 := hw_deriv z hz
    rw [hC z hz, hvpdef] at h1
    refine h1.congr_deriv ?_
    simp only [hGcdef, hζhdef]
    field_simp
    try ring
  set φ1 : ℂ → ℂ := fun z => A * hh s * dslope g s z with hφ1def
  have hdsg : DifferentiableOn ℂ (dslope g s) (Metric.ball s δ) :=
    (Complex.differentiableOn_dslope (f := g) (s := Metric.ball s δ) (c := s) hball).mpr hgd
  have hφ1d : DifferentiableOn ℂ φ1 (Metric.ball s δ) := by
    rw [hφ1def]
    exact (differentiableOn_const (A * hh s)).mul hdsg
  obtain ⟨Be, hBes, hBe⟩ : ∃ Be : ℂ → ℂ, Be s = Gc s ∧
      ∀ z ∈ Metric.ball s δ, HasDerivAt Be (φ1 z) z := by
    obtain ⟨B, hBv, hB⟩ := (hφ1d.isExactOn_ball).with_val_at s (Gc s)
    exact ⟨B, hBv, hB⟩
  have hBed : DifferentiableOn ℂ Be (Metric.ball s δ) :=
    fun z hz => (hBe z hz).differentiableAt.differentiableWithinAt
  set ψ : ℂ → ℂ := fun z => dslope Gc s z - dslope Be s z with hψdef
  have hψd : DifferentiableOn ℂ ψ (Metric.ball s δ) := by
    rw [hψdef]
    exact ((Complex.differentiableOn_dslope (f := Gc) (s := Metric.ball s δ) (c := s)
        hball).mpr hGcd).sub
      ((Complex.differentiableOn_dslope (f := Be) (s := Metric.ball s δ) (c := s)
        hball).mpr hBed)
  obtain ⟨Ae, hAes, hAe⟩ : ∃ Ae : ℂ → ℂ, Ae s = 0 ∧
      ∀ z ∈ Metric.ball s δ, HasDerivAt Ae (ψ z) z := by
    obtain ⟨A', hAv, hA⟩ := (hψd.isExactOn_ball).with_val_at s 0
    exact ⟨A', hAv, hA⟩
  have hAed : DifferentiableOn ℂ Ae (Metric.ball s δ) :=
    fun z hz => (hAe z hz).differentiableAt.differentiableWithinAt
  have hF_deriv : ∀ z ∈ Ω, HasDerivAt
      (fun x => w x - c' * (Complex.log (s - x)) ^ 2 - Be x * Complex.log (s - x) - Ae x) 0 z := by
    intro z hz
    have hzB : z ∈ Metric.ball s δ := hΩsub hz
    have hzs : z ≠ s := fun h => hsΩ (h ▸ hz)
    have hsz : s - z ≠ 0 := sub_ne_zero.mpr (fun h => hzs h.symm)
    have hzsub : z - s ≠ 0 := sub_ne_zero.mpr hzs
    have hL : HasDerivAt (fun x : ℂ => Complex.log (s - x)) (1 / (z - s)) z :=
      hasDerivAt_log_sub (hslit z hz)
    have hL2 : HasDerivAt (fun x : ℂ => (Complex.log (s - x)) ^ 2)
        (2 * Complex.log (s - z) * (1 / (z - s))) z := by
      have h := hL.pow 2
      have h2 : ((fun x : ℂ => Complex.log (s - x)) ^ 2 : ℂ → ℂ)
          = fun x => (Complex.log (s - x)) ^ 2 := by ext x; simp
      rw [h2] at h
      simpa using h
    have hc2 : HasDerivAt (fun x : ℂ => c' * (Complex.log (s - x)) ^ 2)
        (c' * (2 * Complex.log (s - z) * (1 / (z - s)))) z := hL2.const_mul c'
    have hBL : HasDerivAt (fun x : ℂ => Be x * Complex.log (s - x))
        (φ1 z * Complex.log (s - z) + Be z * (1 / (z - s))) z := (hBe z hzB).mul hL
    have hA' : (z - s) * ψ z = Gc z - Be z := by
      simp only [hψdef]
      rw [dslope_eq_div Gc hzs, dslope_eq_div Be hzs, hBes]
      field_simp
      try ring
    have hB' : (z - s) * φ1 z = A * hh s * g z - 2 * c' := by
      simp only [hφ1def]
      rw [dslope_eq_div g hzs, ← h2c]
      field_simp
      try ring
    have hkey : (Gc z + A * hh s * g z * Complex.log (s - z)) / (z - s)
        = ψ z + φ1 z * Complex.log (s - z) + Be z / (z - s)
          + (2 * c' * Complex.log (s - z)) / (z - s) := by
      have hψeq : ψ z = (Gc z - Be z) / (z - s) := by
        rw [eq_div_iff hzsub, mul_comm (ψ z) (z - s)]; exact hA'
      have hφeq : φ1 z = (A * hh s * g z - 2 * c') / (z - s) := by
        rw [eq_div_iff hzsub, mul_comm (φ1 z) (z - s)]; exact hB'
      rw [hψeq, hφeq, div_mul_eq_mul_div]
      field_simp
      try ring
    have hwv := hw_deriv2 z hz
    have hAev := hAe z hzB
    refine (((hwv.sub hc2).sub hBL).sub hAev).congr_deriv ?_
    rw [hkey]
    field_simp
    try ring
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℂ, ∀ z ∈ Ω,
      w z - c' * (Complex.log (s - z)) ^ 2 - Be z * Complex.log (s - z) - Ae z = C0 := by
    by_cases hne : Ω.Nonempty
    · refine ⟨w hne.choose - c' * (Complex.log (s - hne.choose)) ^ 2
        - Be hne.choose * Complex.log (s - hne.choose) - Ae hne.choose, fun z hz => ?_⟩
      exact IsOpen.is_const_of_deriv_eq_zero hΩo hΩc
        (fun z hz => (hF_deriv z hz).differentiableAt.differentiableWithinAt)
        (fun z hz => (hF_deriv z hz).deriv) hz hne.choose_spec
    · exact ⟨0, fun z hz => absurd ⟨z, hz⟩ hne⟩
  refine ⟨fun z => y1 z * (Ae z + C0), fun z => y1 z * Be z, ?_, ?_, ?_⟩
  · exact hy1d.mul (hAed.add_const C0)
  · exact hy1d.mul hBed
  · intro z hz
    have hy1z : y1 z ≠ 0 := hy1ne z (hΩsub hz)
    have h := hC0 z hz
    rw [hwdef] at h
    simp only [] at h
    have hfin : φ z = y1 z * (Ae z + C0) + y1 z * Be z * Complex.log (s - z)
        + c' * y1 z * (Complex.log (s - z)) ^ 2 := by
      have h3 : φ z / y1 z = c' * (Complex.log (s - z)) ^ 2 + Be z * Complex.log (s - z)
          + Ae z + C0 := by linear_combination h
      calc φ z = y1 z * (φ z / y1 z) := by field_simp
        _ = y1 z * (c' * (Complex.log (s - z)) ^ 2 + Be z * Complex.log (s - z)
              + Ae z + C0) := by rw [h3]
        _ = y1 z * (Ae z + C0) + y1 z * Be z * Complex.log (s - z)
              + c' * y1 z * (Complex.log (s - z)) ^ 2 := by ring
    rw [hfin, hc'def]
    ring

end

end Work.A14D
