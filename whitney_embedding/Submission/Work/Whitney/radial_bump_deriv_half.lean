import Mathlib

/-!
# A smooth radial cut-off on `ℝ^N` with derivative bound `1/2`

For `q : EuclideanSpace ℝ (Fin N)` and radii `0 ≤ ρ < δ`, `0 < lam ≤ (δ - ρ)/4` we build a
`C^∞` function `χ : ℝ^N → ℝ` with `0 ≤ χ ≤ lam`, `χ = lam` on the closed ball of radius
`max ρ lam` around `q`, `χ = 0` outside the closed ball of radius `δ`, and
`‖fderiv ℝ χ y‖ ≤ 1/2` everywhere.

## The analytic core

The only non-elementary ingredient is a `C^∞` *flat step*: a smooth function `ψ` equal to `1`
on `(-∞, 0]`, to `0` on `[1, ∞)`, with values in `[0,1]` and `|deriv ψ| ≤ 5/4`.

It is produced as the difference of two translates of a primitive: let
`b t = smoothTransition (4 * t)` (so `b = 0` for `t ≤ 0` and `b = 1` for `t ≥ 1/4`),
let `F u = ∫ t in 0..u, b t`, and put

`ψ t = 1 - F ((5/4) * t) + F ((5/4) * t - 1)`.

Since `F a - F (a-1) = ∫ t in (a-1)..a, b t ∈ [0,1]`, the range is `[0,1]`; the function
equals `1` for `t ≤ 0` (both arguments of `F` are `≤ 0`) and `0` for `t ≥ 1` (both arguments are
`≥ 1/4`, where `b = 1`, so the difference of the two primitives is `1`). Finally
`deriv ψ t = (5/4) * (b ((5/4) * t - 1) - b ((5/4) * t))`, whose absolute value is at most
`5/4` because `b` takes values in `[0,1]`.

The radial cut-off is `χ y = lam * ψ ((‖y - q‖ - R0) / L)` with `R0 = max ρ lam` and
`L = δ - R0 > 0`.  The only geometric input is `3 * lam ≤ L`, which follows from the
hypothesis `lam ≤ (δ - ρ)/4` in both cases `ρ ≤ lam` and `lam ≤ ρ`.
-/

namespace Work.Whitney

open MeasureTheory Filter Metric
open scoped Topology ContDiff

/-- The primitive `u ↦ ∫ t in 0..u, b t` of a `C^∞` function `b : ℝ → ℝ` is `C^∞`, and it
has derivative `b` everywhere. -/
lemma contDiff_primitive {b : ℝ → ℝ}
    (hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => ∫ t in (0 : ℝ)..u, b t) ∧
      ∀ u, HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, b t) (b u) u := by
  have hbcont : Continuous b := hb.continuous
  have hderiv : ∀ u, HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, b t) (b u) u := fun u =>
    intervalIntegral.integral_hasDerivAt_right (hbcont.intervalIntegrable 0 u)
      (hbcont.stronglyMeasurableAtFilter volume (𝓝 u)) hbcont.continuousAt
  exact ⟨contDiff_infty_iff_deriv.mpr ⟨fun u => (hderiv u).differentiableAt, by
    have : deriv (fun u => ∫ t in (0 : ℝ)..u, b t) = b := funext fun u => (hderiv u).deriv
    rw [this]; exact hb⟩, hderiv⟩

/-- There exists a `C^∞` flat step function `ψ : ℝ → ℝ` with `ψ = 1` on `(-∞, 0]`,
`ψ = 0` on `[1, ∞)`, `0 ≤ ψ ≤ 1` and `|deriv ψ| ≤ 5/4`. -/
lemma exists_flat_step_deriv :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧ (∀ u, 0 ≤ ψ u) ∧ (∀ u, ψ u ≤ 1) ∧
      (∀ u, u ≤ 0 → ψ u = 1) ∧ (∀ u, 1 ≤ u → ψ u = 0) ∧ (∀ u, |deriv ψ u| ≤ 5/4) := by
  set b : ℝ → ℝ := fun t => Real.smoothTransition (4 * t) with hbdef
  have hbc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b := by rw [hbdef]; fun_prop
  have hbcont : Continuous b := hbc.continuous
  have hb0 : ∀ t, 0 ≤ b t := fun t => by rw [hbdef]; exact Real.smoothTransition.nonneg _
  have hb1 : ∀ t, b t ≤ 1 := fun t => by rw [hbdef]; exact Real.smoothTransition.le_one _
  have hbz : ∀ t, t ≤ 0 → b t = 0 := fun t ht => by
    rw [hbdef]; exact Real.smoothTransition.zero_of_nonpos (by linarith)
  have hbo : ∀ t, 1/4 ≤ t → b t = 1 := fun t ht => by
    rw [hbdef]; exact Real.smoothTransition.one_of_one_le (by linarith)
  obtain ⟨hFc, hFderiv⟩ := contDiff_primitive hbc
  set F : ℝ → ℝ := fun u => ∫ t in (0 : ℝ)..u, b t with hFdef
  have hFderiv' : ∀ u, HasDerivAt F (b u) u := fun u => by rw [hFdef]; exact hFderiv u
  have hFc' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := by rw [hFdef]; exact hFc
  have hFint : ∀ a c, IntervalIntegrable b volume a c := fun a c => hbcont.intervalIntegrable a c
  have hFzero : ∀ u, u ≤ 0 → F u = 0 := by
    intro u hu
    show ∫ t in (0:ℝ)..u, b t = 0
    have hc : ∫ t in (0:ℝ)..u, b t = ∫ t in (0:ℝ)..u, (0:ℝ) :=
      intervalIntegral.integral_congr (g := fun _ : ℝ => (0:ℝ)) (fun t ht => by
        rw [Set.uIcc_of_ge hu] at ht; exact hbz t ht.2)
    rw [hc, intervalIntegral.integral_const]; simp
  have hadj : ∀ a, F a - F (a - 1) = ∫ t in (a-1)..a, b t := by
    intro a
    have h := intervalIntegral.integral_add_adjacent_intervals (a := (0:ℝ)) (b := a-1) (c := a)
      (hFint 0 (a-1)) (hFint (a-1) a)
    show (∫ t in (0:ℝ)..a, b t) - (∫ t in (0:ℝ)..(a-1), b t) = ∫ t in (a-1)..a, b t
    linarith [h]
  have hbound : ∀ a, 0 ≤ F a - F (a-1) ∧ F a - F (a-1) ≤ 1 := by
    intro a
    constructor
    · rw [hadj a]; exact intervalIntegral.integral_nonneg (by linarith) (fun t _ => hb0 t)
    · rw [hadj a]
      have hle : ∫ t in (a-1)..a, b t ≤ ∫ t in (a-1)..a, (1:ℝ) :=
        intervalIntegral.integral_mono (by linarith) (hFint (a-1) a) intervalIntegrable_const
          (fun t => hb1 t)
      rw [intervalIntegral.integral_const] at hle
      simpa using hle
  refine ⟨fun t => 1 - F ((5:ℝ)/4 * t) + F ((5:ℝ)/4 * t - 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => F ((5:ℝ)/4 * t)) :=
      hFc'.comp (by fun_prop)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => F ((5:ℝ)/4 * t - 1)) :=
      hFc'.comp (by fun_prop)
    exact (contDiff_const.sub h1).add h2
  · intro u
    show 0 ≤ 1 - F ((5:ℝ)/4 * u) + F ((5:ℝ)/4 * u - 1)
    have := (hbound ((5:ℝ)/4 * u)).2
    linarith
  · intro u
    show 1 - F ((5:ℝ)/4 * u) + F ((5:ℝ)/4 * u - 1) ≤ 1
    have := (hbound ((5:ℝ)/4 * u)).1
    linarith
  · intro u hu
    show 1 - F ((5:ℝ)/4 * u) + F ((5:ℝ)/4 * u - 1) = 1
    have h1 : F ((5:ℝ)/4 * u) = 0 := hFzero _ (by linarith)
    have h2 : F ((5:ℝ)/4 * u - 1) = 0 := hFzero _ (by linarith)
    rw [h1, h2]; ring
  · intro u hu
    show 1 - F ((5:ℝ)/4 * u) + F ((5:ℝ)/4 * u - 1) = 0
    have h1 : F ((5:ℝ)/4 * u) - F ((5:ℝ)/4 * u - 1) = 1 := by
      rw [hadj ((5:ℝ)/4 * u)]
      have hc : ∫ t in ((5:ℝ)/4*u-1)..((5:ℝ)/4*u), b t
          = ∫ t in ((5:ℝ)/4*u-1)..((5:ℝ)/4*u), (1:ℝ) :=
        intervalIntegral.integral_congr (g := fun _ : ℝ => (1:ℝ)) (fun t ht => by
          rw [Set.uIcc_of_le (by linarith : (5:ℝ)/4*u-1 ≤ (5:ℝ)/4*u)] at ht
          exact hbo t (by linarith [ht.1]))
      rw [hc, intervalIntegral.integral_const]; simp
    linarith
  · intro u
    have hinner : HasDerivAt (fun t : ℝ => (5:ℝ)/4 * t) (5/4) u := by
      simpa using (hasDerivAt_id u).const_mul ((5:ℝ)/4)
    have hg1 : HasDerivAt (F ∘ fun t : ℝ => (5:ℝ)/4 * t) (b ((5:ℝ)/4 * u) * (5/4)) u :=
      (hFderiv' ((5:ℝ)/4 * u)).comp u hinner
    have hg2 : HasDerivAt (F ∘ fun t : ℝ => (5:ℝ)/4 * t - 1)
        (b ((5:ℝ)/4 * u - 1) * (5/4)) u :=
      (hFderiv' ((5:ℝ)/4 * u - 1)).comp u (hinner.sub_const 1)
    have htot : HasDerivAt (fun t : ℝ => 1 - F ((5:ℝ)/4 * t) + F ((5:ℝ)/4 * t - 1))
        (b ((5:ℝ)/4 * u - 1) * (5/4) - b ((5:ℝ)/4 * u) * (5/4)) u := by
      have h := ((hasDerivAt_const u (1:ℝ)).sub hg1).add hg2
      have hv : (0 - b ((5:ℝ)/4 * u) * (5/4)) + b ((5:ℝ)/4 * u - 1) * (5/4)
          = b ((5:ℝ)/4 * u - 1) * (5/4) - b ((5:ℝ)/4 * u) * (5/4) := by ring
      rw [hv] at h
      exact h
    rw [htot.deriv]
    rw [abs_le]
    constructor
    · nlinarith [hb0 ((5:ℝ)/4*u), hb1 ((5:ℝ)/4*u), hb0 ((5:ℝ)/4*u-1), hb1 ((5:ℝ)/4*u-1)]
    · nlinarith [hb0 ((5:ℝ)/4*u), hb1 ((5:ℝ)/4*u), hb0 ((5:ℝ)/4*u-1), hb1 ((5:ℝ)/4*u-1)]

theorem radial_bump_deriv_half {N : ℕ} (q : EuclideanSpace ℝ (Fin N)) {ρ δ lam : ℝ}
    (hρ : 0 ≤ ρ) (hρδ : ρ < δ) (hlam : 0 < lam) (hlamδ : lam ≤ (δ - ρ) / 4) :
    ∃ χ : EuclideanSpace ℝ (Fin N) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ (∀ y, 0 ≤ χ y) ∧ (∀ y, χ y ≤ lam) ∧
      (∀ y, ‖y - q‖ ≤ ρ → χ y = lam) ∧ (∀ y, ‖y - q‖ ≤ lam → χ y = lam) ∧
      (∀ y, δ ≤ ‖y - q‖ → χ y = 0) ∧ (∀ y, ‖fderiv ℝ χ y‖ ≤ 1 / 2) := by
  obtain ⟨ψ, hψc, hψ0, hψ1, hψtop, hψbot, hψd⟩ := exists_flat_step_deriv
  have hδpos : 0 < δ := lt_of_le_of_lt hρ hρδ
  have hRdef : max ρ lam < δ := max_lt hρδ (by have h := hlamδ; nlinarith [hρ, hδpos, hlam])
  set R0 : ℝ := max ρ lam with hR0def
  have hR0ρ : ρ ≤ R0 := le_max_left _ _
  have hR0lam : lam ≤ R0 := le_max_right _ _
  have hR0pos : 0 < R0 := lt_of_lt_of_le hlam hR0lam
  have hR0δ : R0 < δ := hRdef
  set L : ℝ := δ - R0 with hLdef
  have hLpos : 0 < L := sub_pos.mpr hR0δ
  have hL3 : 3 * lam ≤ L := by
    rcases le_total ρ lam with h | h
    · have hδ4 : 4 * lam ≤ δ := by
        have hle : lam ≤ δ / 4 := le_trans hlamδ (by nlinarith [hρ])
        linarith
      rw [hLdef, hR0def, max_eq_right h]; linarith
    · rw [hLdef, hR0def, max_eq_left h]
      have h4 : 4 * lam ≤ δ - ρ := by linarith [hlamδ]
      linarith
  have hψdiff : Differentiable ℝ ψ := hψc.differentiable (by simp)
  have hψlip : LipschitzWith (NNReal.mk (5/4) (by norm_num)) ψ :=
    lipschitzWith_of_nnnorm_deriv_le hψdiff (fun x => by
      rw [← NNReal.coe_le_coe, NNReal.coe_mk, coe_nnnorm, Real.norm_eq_abs]; exact hψd x)
  have hK : (0:ℝ) ≤ lam * (5/4) / L := div_nonneg (mul_nonneg hlam.le (by norm_num)) hLpos.le
  let χ : EuclideanSpace ℝ (Fin N) → ℝ := fun y => lam * ψ ((‖y - q‖ - R0) / L)
  have hχc : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) χ := by
    change ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin N) => lam * ψ ((‖y - q‖ - R0) / L))
    rw [contDiff_iff_contDiffAt]
    intro y
    rcases lt_or_ge (‖y - q‖) R0 with hy | hy
    · have hnhd : {z : EuclideanSpace ℝ (Fin N) | ‖z - q‖ < R0} ∈ 𝓝 y :=
        (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const))
          continuous_const).mem_nhds hy
      have heq : (fun z : EuclideanSpace ℝ (Fin N) => lam * ψ ((‖z - q‖ - R0) / L))
          =ᶠ[𝓝 y] (fun _ => lam) := by
        filter_upwards [hnhd] with z hz
        have hz0 : (‖z - q‖ - R0) / L ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hLpos.le
        rw [hψtop _ hz0, mul_one]
      exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const heq
    · have hyne : (fun z : EuclideanSpace ℝ (Fin N) => z - q) y ≠ 0 := by
        show y - q ≠ 0
        intro h; rw [h, norm_zero] at hy; linarith [hR0pos]
      have hnorm : ContDiffAt ℝ ((⊤:ℕ∞):WithTop ℕ∞)
          (fun z : EuclideanSpace ℝ (Fin N) => ‖z - q‖) y :=
        ContDiffAt.norm ℝ (contDiffAt_id.sub contDiffAt_const) hyne
      have harg : ContDiffAt ℝ ((⊤:ℕ∞):WithTop ℕ∞)
          (fun z : EuclideanSpace ℝ (Fin N) => (‖z - q‖ - R0) / L) y :=
        (hnorm.sub contDiffAt_const).div_const L
      exact (contDiffAt_const (c := lam)).mul (hψc.contDiffAt.comp y harg)
  have hχlip : LipschitzWith (NNReal.mk (lam * (5/4) / L) hK) χ := by
    change LipschitzWith (NNReal.mk (lam * (5/4) / L) hK)
      (fun y : EuclideanSpace ℝ (Fin N) => lam * ψ ((‖y - q‖ - R0) / L))
    refine LipschitzWith.of_dist_le_mul (fun y₁ y₂ => ?_)
    have h1 : |ψ ((‖y₁ - q‖ - R0) / L) - ψ ((‖y₂ - q‖ - R0) / L)|
        ≤ (5/4) * |(‖y₁ - q‖ - R0) / L - (‖y₂ - q‖ - R0) / L| := by
      have := hψlip.dist_le_mul ((‖y₁ - q‖ - R0) / L) ((‖y₂ - q‖ - R0) / L)
      rw [Real.dist_eq, Real.dist_eq, NNReal.coe_mk] at this
      exact this
    have h2 : |(‖y₁ - q‖ - R0) / L - (‖y₂ - q‖ - R0) / L| ≤ ‖y₁ - y₂‖ / L := by
      rw [div_sub_div_same, abs_div, abs_of_pos hLpos]
      gcongr
      calc |‖y₁ - q‖ - R0 - (‖y₂ - q‖ - R0)| = |‖y₁ - q‖ - ‖y₂ - q‖| := by ring_nf
        _ ≤ ‖(y₁ - q) - (y₂ - q)‖ := abs_norm_sub_norm_le _ _
        _ = ‖y₁ - y₂‖ := by rw [sub_sub_sub_cancel_right]
    calc dist (lam * ψ ((‖y₁ - q‖ - R0) / L)) (lam * ψ ((‖y₂ - q‖ - R0) / L))
        = |lam * ψ ((‖y₁ - q‖ - R0) / L) - lam * ψ ((‖y₂ - q‖ - R0) / L)| := Real.dist_eq _ _
      _ = lam * |ψ ((‖y₁ - q‖ - R0) / L) - ψ ((‖y₂ - q‖ - R0) / L)| := by
          rw [← mul_sub, abs_mul, abs_of_pos hlam]
      _ ≤ lam * ((5/4) * |(‖y₁ - q‖ - R0) / L - (‖y₂ - q‖ - R0) / L|) := by gcongr
      _ ≤ lam * ((5/4) * (‖y₁ - y₂‖ / L)) := by gcongr
      _ = (lam * (5/4) / L) * ‖y₁ - y₂‖ := by ring
      _ = ↑(NNReal.mk (lam * (5/4) / L) hK) * dist y₁ y₂ := by rw [NNReal.coe_mk, dist_eq_norm]
  have hχderiv : ∀ y : EuclideanSpace ℝ (Fin N), ‖fderiv ℝ χ y‖ ≤ 1 / 2 := by
    intro y
    have hle := (hχc.differentiable (by simp) y).hasFDerivAt.le_of_lipschitz hχlip
    have hKle : lam * (5/4) / L ≤ 1/2 := by
      rw [div_le_iff₀ hLpos]
      nlinarith [hlam, hLpos, hL3]
    calc ‖fderiv ℝ χ y‖ ≤ ↑(NNReal.mk (lam * (5/4) / L) hK) := hle
      _ = lam * (5/4) / L := NNReal.coe_mk _ _
      _ ≤ 1/2 := hKle
  refine ⟨χ, hχc, ?_, ?_, ?_, ?_, ?_, hχderiv⟩
  · intro y; change 0 ≤ lam * ψ ((‖y - q‖ - R0) / L)
    exact mul_nonneg hlam.le (hψ0 _)
  · intro y; change lam * ψ ((‖y - q‖ - R0) / L) ≤ lam
    have := hψ1 ((‖y - q‖ - R0) / L); nlinarith [hlam]
  · intro y hy; change lam * ψ ((‖y - q‖ - R0) / L) = lam
    have hz0 : (‖y - q‖ - R0) / L ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hLpos.le
    rw [hψtop _ hz0, mul_one]
  · intro y hy; change lam * ψ ((‖y - q‖ - R0) / L) = lam
    have hz0 : (‖y - q‖ - R0) / L ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hLpos.le
    rw [hψtop _ hz0, mul_one]
  · intro y hy; change lam * ψ ((‖y - q‖ - R0) / L) = 0
    have hz1 : 1 ≤ (‖y - q‖ - R0) / L := by rw [le_div_iff₀ hLpos]; linarith
    rw [hψbot _ hz1, mul_zero]

end Work.Whitney
