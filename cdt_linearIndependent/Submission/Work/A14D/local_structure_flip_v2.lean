import Mathlib

/-!  This is a copy of `Submission/Work/A14D/local_structure_flip.lean` in which the import of
`Submission.Work.A14D.local_core_pub` is replaced by an inlined `dslope_eq_div`: that module
defines `Work.A14D.hasDerivAt_log_sub`, which clashes with the same name in
`Submission.Work.A14D.setup`, so no module can import both.  Helper names are suffixed `_v2` so
that this module is separate from the original. -/

/-!  # The local structure of a solution of `P2 y'' + P1 y' + P0 y = 0` at a double
indicial exponent `0` (`local_structure_flip`)

This is the "flipped" companion of `Work.A14D.local_structure_core`: the branch of the logarithm
used is `log (z - s)` (with `z - s` in the slit plane) rather than `log (s - z)`.  The argument is
the same reduction of order; the only change is the derivative of the logarithm.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

noncomputable section

/-- `dslope` at a point different from the base point, as a quotient (local copy). -/
lemma dslope_eq_div_v2 (f : ℂ → ℂ) {a b : ℂ} (h : b ≠ a) :
    dslope f a b = (f b - f a) / (b - a) := by
  rw [dslope_of_ne f h, slope_def_field]

/-- Derivative of `z ↦ log (z - s)` at a point of the slit plane. -/
lemma hasDerivAt_log_sub_flip_v2 {s z : ℂ} (h : z - s ∈ Complex.slitPlane) :
    HasDerivAt (fun x : ℂ => Complex.log (x - s)) (1 / (z - s)) z := by
  have h1 : HasDerivAt (fun x : ℂ => x - s) 1 z := (hasDerivAt_id z).sub_const s
  have h2 := (Complex.hasDerivAt_log h).comp z h1
  have h3 : 1 / (z - s) = (z - s)⁻¹ * 1 := by ring
  exact h2.congr_deriv h3.symm

theorem local_structure_flip_v2 {s : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {y1 F : ℂ → ℂ} {P2 P1 P0 q : ℂ → ℂ} {Ω : Set ℂ}
    (hy1d : DifferentiableOn ℂ y1 (Metric.ball s ρ))
    (hy1ne : ∀ z ∈ Metric.ball s ρ, y1 z ≠ 0)
    (hy1ode : ∀ z ∈ Metric.ball s ρ,
      P2 z * deriv (deriv y1) z + P1 z * deriv y1 z + P0 z * y1 z = 0)
    (hP2d : DifferentiableOn ℂ P2 (Metric.ball s ρ))
    (hP1eq : ∀ z ∈ Metric.ball s ρ, P1 z = deriv P2 z)
    (hP2fac : ∀ z ∈ Metric.ball s ρ, P2 z = (z - s) * q z)
    (hqd : DifferentiableOn ℂ q (Metric.ball s ρ))
    (hqne : ∀ z ∈ Metric.ball s ρ, q z ≠ 0)
    (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω) (hΩsub : Ω ⊆ Metric.ball s ρ) (hsΩ : s ∉ Ω)
    (hslit : ∀ z ∈ Ω, z - s ∈ Complex.slitPlane)
    (hFd : DifferentiableOn ℂ F Ω)
    (hFode : ∀ z ∈ Ω, P2 z * deriv (deriv F) z + P1 z * deriv F z + P0 z * F z = 0) :
    ∃ κ : ℂ, ∃ hh : ℂ → ℂ, DifferentiableOn ℂ hh (Metric.ball s ρ) ∧
      ∀ z ∈ Ω, F z = κ * y1 z * Complex.log (z - s) + hh z := by
  classical
  have hball : Metric.ball s ρ ∈ 𝓝 s := Metric.ball_mem_nhds s hρ
  have hballo : IsOpen (Metric.ball s ρ) := Metric.isOpen_ball
  have hsmem : s ∈ Metric.ball s ρ := Metric.mem_ball_self hρ
  -- `P1 = P2'` is holomorphic on the ball
  have hP1d : DifferentiableOn ℂ P1 (Metric.ball s ρ) :=
    (hP2d.deriv hballo).congr fun z hz => hP1eq z hz
  -- the residue condition `P1 s = q s` of the double indicial exponent
  have hres : P1 s = q s := by
    have hev : P2 =ᶠ[𝓝 s] fun z => (z - s) * q z :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds s hρ) fun z hz => hP2fac z hz
    have hd : deriv (fun z : ℂ => (z - s) * q z) s = q s := by
      have h2 : HasDerivAt (fun z : ℂ => z - s) 1 s := (hasDerivAt_id s).sub_const s
      have h3 : HasDerivAt q (deriv q s) s :=
        (hqd.differentiableAt (hballo.mem_nhds hsmem)).hasDerivAt
      have h4 : HasDerivAt ((fun z : ℂ => z - s) * q) (1 * q s + (s - s) * deriv q s) s :=
        h2.mul h3
      have h5 : (1 : ℂ) * q s + (s - s) * deriv q s = q s := by ring
      rw [h5] at h4
      exact h4.deriv
    rw [hP1eq s hsmem, hev.deriv_eq, hd]
  -- the (trivial) inhomogeneity
  set G : ℂ → ℂ := fun _ => 0 with hGdef
  have hGd : DifferentiableOn ℂ G (Metric.ball s ρ) := by
    rw [hGdef]; exact differentiableOn_const 0
  have hFode0 : ∀ z ∈ Ω, P2 z * deriv (deriv F) z + P1 z * deriv F z + P0 z * F z = G z := by
    intro z hz
    rw [hGdef]
    exact hFode z hz

  have hdy1d : DifferentiableOn ℂ (deriv y1) (Metric.ball s ρ) := hy1d.deriv hballo
  -- ## 1. the analytic quotient `A1 = (P1 - q)/((z-s)q)`
  set A1 : ℂ → ℂ := fun z => (dslope P1 s z - dslope q s z) / q z with hA1def
  have hdsP1 : DifferentiableOn ℂ (dslope P1 s) (Metric.ball s ρ) :=
    (Complex.differentiableOn_dslope (f := P1) (s := Metric.ball s ρ) (c := s) hball).mpr hP1d
  have hdsq : DifferentiableOn ℂ (dslope q s) (Metric.ball s ρ) :=
    (Complex.differentiableOn_dslope (f := q) (s := Metric.ball s ρ) (c := s) hball).mpr hqd
  have hA1d : DifferentiableOn ℂ A1 (Metric.ball s ρ) := by
    rw [hA1def]
    exact (hdsP1.sub hdsq).div hqd hqne
  have hA1eq : ∀ z ∈ Metric.ball s ρ, z ≠ s → 1 / (z - s) + A1 z = P1 z / P2 z := by
    intro z hz hzs
    have hP2z : P2 z ≠ 0 := by
      rw [hP2fac z hz]
      exact mul_ne_zero (sub_ne_zero.mpr hzs) (hqne z hz)
    have h1 : dslope P1 s z = (P1 z - P1 s) / (z - s) := dslope_eq_div_v2 P1 hzs
    have h2 : dslope q s z = (q z - q s) / (z - s) := dslope_eq_div_v2 q hzs
    have hqz : q z ≠ 0 := hqne z hz
    rw [hA1def]
    change 1 / (z - s) + (dslope P1 s z - dslope q s z) / q z = P1 z / P2 z
    rw [h1, h2, hP2fac z hz, hres]
    field_simp
    ring
  -- ## 2. an antiderivative of `A1`, and the functions `A0`, `A`, `g`, `ζh`
  obtain ⟨Qant, hQant0, hQant⟩ : ∃ Qant : ℂ → ℂ, Qant s = 0 ∧
      ∀ z ∈ Metric.ball s ρ, HasDerivAt Qant (A1 z) z := by
    obtain ⟨Q, hQ0, hQ⟩ := (hA1d.isExactOn_ball).with_val_at s 0
    exact ⟨Q, hQ0, hQ⟩
  have hQantd : DifferentiableOn ℂ Qant (Metric.ball s ρ) :=
    fun z hz => (hQant z hz).differentiableAt.differentiableWithinAt
  set A0 : ℂ → ℂ := fun z => 2 * deriv y1 z / y1 z + A1 z with hA0def
  set A : ℂ → ℂ := fun z => 1 / (z - s) + A0 z with hAdef
  set g : ℂ → ℂ := fun z => -(Complex.exp (-(Qant z)) / (y1 z) ^ 2) with hgdef
  have hgd : DifferentiableOn ℂ g (Metric.ball s ρ) := by
    rw [hgdef]
    refine DifferentiableOn.neg ?_
    refine DifferentiableOn.div ((hQantd.neg).cexp) (hy1d.pow 2) ?_
    intro z hz
    exact pow_ne_zero 2 (hy1ne z hz)
  have hgne : ∀ z ∈ Metric.ball s ρ, g z ≠ 0 := by
    intro z hz
    rw [hgdef]
    refine neg_ne_zero.mpr (div_ne_zero (Complex.exp_ne_zero _) ?_)
    exact pow_ne_zero 2 (hy1ne z hz)
  have hpow_d : ∀ z ∈ Metric.ball s ρ, HasDerivAt (fun x : ℂ => y1 x ^ 2)
      (2 * y1 z * deriv y1 z) z := by
    intro z hz
    have hy1d_at : HasDerivAt y1 (deriv y1 z) z :=
      (hy1d.differentiableAt (hballo.mem_nhds hz)).hasDerivAt
    have h := hy1d_at.pow 2
    have h2 : (y1 ^ 2 : ℂ → ℂ) = fun x => y1 x ^ 2 := by ext x; simp
    rw [h2] at h
    simpa using h
  have hg_deriv : ∀ z ∈ Metric.ball s ρ, deriv g z = -(A0 z) * g z := by
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
  have hζh_deriv : ∀ z ∈ Metric.ball s ρ, z ≠ s → HasDerivAt ζh (-(A z) * ζh z) z := by
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
  have hΨd : DifferentiableOn ℂ (fun z => G z / (q z * y1 z * g z)) (Metric.ball s ρ) :=
    hGd.div ((hqd.mul hy1d).mul hgd)
      (fun z hz => mul_ne_zero (mul_ne_zero (hqne z hz) (hy1ne z hz)) (hgne z hz))
  obtain ⟨ℓ, hℓ0, hℓ⟩ : ∃ ℓ : ℂ → ℂ, ℓ s = 0 ∧
      ∀ z ∈ Metric.ball s ρ, HasDerivAt ℓ (G z / (q z * y1 z * g z)) z := by
    obtain ⟨L, hL0, hL⟩ := (hΨd.isExactOn_ball).with_val_at s 0
    exact ⟨L, hL0, hL⟩
  have hℓd : DifferentiableOn ℂ ℓ (Metric.ball s ρ) :=
    fun z hz => (hℓ z hz).differentiableAt.differentiableWithinAt
  set ζp : ℂ → ℂ := fun z => g z * dslope ℓ s z with hζpdef
  have hdsℓ : DifferentiableOn ℂ (dslope ℓ s) (Metric.ball s ρ) :=
    (Complex.differentiableOn_dslope (f := ℓ) (s := Metric.ball s ρ) (c := s) hball).mpr hℓd
  have hζpd : DifferentiableOn ℂ ζp (Metric.ball s ρ) := by
    rw [hζpdef]; exact hgd.mul hdsℓ
  have hdsl_ne : ∀ z : ℂ, z ≠ s → dslope ℓ s z = ℓ z / (z - s) := by
    intro z hzs
    rw [dslope_eq_div_v2 ℓ hzs, hℓ0, sub_zero]
  have hζp_deriv : ∀ z ∈ Metric.ball s ρ, z ≠ s →
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
  -- ## 4. the solution `F` and the first-order equation for `v = (F/y1)'`
  set w : ℂ → ℂ := fun z => F z / y1 z with hwdef
  set Wr : ℂ → ℂ := fun z => y1 z * deriv F z - deriv y1 z * F z with hWrdef
  set v : ℂ → ℂ := fun z => Wr z / (y1 z) ^ 2 with hvdef
  have hFd' : DifferentiableOn ℂ (deriv F) Ω := hFd.deriv hΩo
  have hw_deriv : ∀ z ∈ Ω, HasDerivAt w (v z) z := by
    intro z hz
    have hzB : z ∈ Metric.ball s ρ := hΩsub hz
    have hy1z : y1 z ≠ 0 := hy1ne z hzB
    have h1 : HasDerivAt (fun x : ℂ => F x / y1 x)
        ((deriv F z * y1 z - F z * deriv y1 z) / (y1 z) ^ 2) z :=
      ((hFd.differentiableAt (hΩo.mem_nhds hz)).hasDerivAt).div
        ((hy1d.differentiableAt (hballo.mem_nhds hzB)).hasDerivAt) hy1z
    have h2 : HasDerivAt w ((deriv F z * y1 z - F z * deriv y1 z) / (y1 z) ^ 2) z := by
      rw [hwdef]; exact h1
    refine h2.congr_deriv ?_
    rw [hvdef, hWrdef]
    ring
  have hv_ode : ∀ z ∈ Ω, HasDerivAt v (-(A z) * v z + G z / (P2 z * y1 z)) z := by
    intro z hz
    have hzB : z ∈ Metric.ball s ρ := hΩsub hz
    have hzs : z ≠ s := fun h => hsΩ (h ▸ hz)
    have hy1z : y1 z ≠ 0 := hy1ne z hzB
    have hqz : q z ≠ 0 := hqne z hzB
    have hP2z : P2 z ≠ 0 := by
      rw [hP2fac z hzB]; exact mul_ne_zero (sub_ne_zero.mpr hzs) hqz
    have hWr_deriv : HasDerivAt Wr (y1 z * deriv (deriv F) z - deriv (deriv y1) z * F z) z := by
      rw [hWrdef]
      have h1 : HasDerivAt (fun x : ℂ => y1 x * deriv F x)
          (deriv y1 z * deriv F z + y1 z * deriv (deriv F) z) z :=
        ((hy1d.differentiableAt (hballo.mem_nhds hzB)).hasDerivAt).mul
          ((hFd'.differentiableAt (hΩo.mem_nhds hz)).hasDerivAt)
      have h2 : HasDerivAt (fun x : ℂ => deriv y1 x * F x)
          (deriv (deriv y1) z * F z + deriv y1 z * deriv F z) z :=
        ((hdy1d.differentiableAt (hballo.mem_nhds hzB)).hasDerivAt).mul
          ((hFd.differentiableAt (hΩo.mem_nhds hz)).hasDerivAt)
      exact (h1.sub h2).congr_deriv (by ring)
    have hWr_ode : HasDerivAt Wr ((y1 z * G z - P1 z * Wr z) / P2 z) z := by
      refine hWr_deriv.congr_deriv ?_
      have e1 : P2 z * deriv (deriv F) z = G z - P1 z * deriv F z - P0 z * F z := by
        linear_combination hFode0 z hz
      have e2 : P2 z * deriv (deriv y1) z = -(P1 z * deriv y1 z) - P0 z * y1 z := by
        linear_combination hy1ode z hzB
      have key : P2 z * (y1 z * deriv (deriv F) z - deriv (deriv y1) z * F z)
          = y1 z * G z - P1 z * Wr z := by
        rw [hWrdef]; linear_combination (y1 z) * e1 - (F z) * e2
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
    have hzB : z ∈ Metric.ball s ρ := hΩsub hz
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
    have hzB : z ∈ Metric.ball s ρ := hΩsub hz
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
  have hLd : DifferentiableOn ℂ (fun z => g z * (ℓ z + c)) (Metric.ball s ρ) :=
    hgd.mul (hℓd.add_const c)
  have hdsLd : DifferentiableOn ℂ (dslope (fun z => g z * (ℓ z + c)) s) (Metric.ball s ρ) :=
    (Complex.differentiableOn_dslope (f := fun z => g z * (ℓ z + c)) (s := Metric.ball s ρ)
      (c := s) hball).mpr hLd
  obtain ⟨W1, hW1⟩ : ∃ W1 : ℂ → ℂ,
      ∀ z ∈ Metric.ball s ρ, HasDerivAt W1 (dslope (fun z => g z * (ℓ z + c)) s z) z :=
    (hdsLd.isExactOn_ball)
  have hW1d : DifferentiableOn ℂ W1 (Metric.ball s ρ) :=
    fun z hz => (hW1 z hz).differentiableAt.differentiableWithinAt
  have hw_deriv2 : ∀ z ∈ Ω, HasDerivAt w ((fun x => g x * (ℓ x + c)) z / (z - s)) z := by
    intro z hz
    have hzB : z ∈ Metric.ball s ρ := hΩsub hz
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
      HasDerivAt (fun x => w x - κ * Complex.log (x - s) - W1 x) 0 z := by
    intro z hz
    have hzs : z ≠ s := fun h => hsΩ (h ▸ hz)
    have h1 := hw_deriv2 z hz
    have h2 : HasDerivAt (fun x : ℂ => Complex.log (x - s)) (1 / (z - s)) z :=
      hasDerivAt_log_sub_flip_v2 (hslit z hz)
    have h3 : HasDerivAt (fun x : ℂ => κ * Complex.log (x - s)) (κ * (1 / (z - s))) z :=
      h2.const_mul κ
    have h4 : HasDerivAt W1 (dslope (fun x => g x * (ℓ x + c)) s z) z :=
      hW1 z (hΩsub hz)
    refine ((h1.sub h3).sub h4).congr_deriv ?_
    rw [hκdef, dslope_eq_div_v2 (fun x => g x * (ℓ x + c)) hzs]
    field_simp
    ring
  obtain ⟨C, hC⟩ : ∃ C : ℂ, ∀ z ∈ Ω, w z - κ * Complex.log (z - s) - W1 z = C := by
    by_cases hne : Ω.Nonempty
    · refine ⟨w hne.choose - κ * Complex.log (hne.choose - s) - W1 hne.choose, fun z hz => ?_⟩
      exact IsOpen.is_const_of_deriv_eq_zero hΩo hΩc
        (fun z hz => (hF_deriv z hz).differentiableAt.differentiableWithinAt)
        (fun z hz => (hF_deriv z hz).deriv) hz hne.choose_spec
    · exact ⟨0, fun z hz => absurd ⟨z, hz⟩ hne⟩
  refine ⟨κ, fun z => y1 z * (W1 z + C), hy1d.mul (hW1d.add_const C), fun z hz => ?_⟩
  have hy1z : y1 z ≠ 0 := hy1ne z (hΩsub hz)
  have h := hC z hz
  rw [hwdef] at h
  simp only [] at h
  show F z = κ * y1 z * Complex.log (z - s) + y1 z * (W1 z + C)
  field_simp
  field_simp at h
  linear_combination h


end

end Work.A14D
