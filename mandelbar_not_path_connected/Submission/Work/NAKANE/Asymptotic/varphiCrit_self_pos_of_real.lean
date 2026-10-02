import Mathlib
import Submission.Work.NAKANE.Defs
import Submission.Work.NAKANE.Asymptotic.bottcher_real_pos
import Submission.Work.NAKANE.BottcherFar.jointVarphi_eq_jointBottcher_of_far
import Submission.Work.ParamRays.RealSlice

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE.Asymptotic

open Filter
open scoped Topology ComplexConjugate

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The real orbit of `t ↦ t² + c` and the monotonicity of the Green function

The Green function of the tricorn `T_c` is the limit of `2^{-n} log⁺ ‖T_c^n z‖`
(`Work.Escape.tendsto_greenIter`).  For real `c, x` the orbit of `x` is the real orbit of
`t ↦ t² + c` (`Work.Bottcher.Core.Tantibar_iterate_ofReal`), and that real map is increasing on
`[0, ∞)`.  Hence `G_c` is increasing in the point variable on `[c, ∞)`, and therefore the whole
half line `[c, ∞)` lies in the critical domain `critDomain c = {G_c > G_c 0}` as soon as
`c ∈ critDomain c`. -/

/-- The real orbit `t ↦ t² + c` of a non-negative point stays non-negative. -/
theorem tOrbit_nonneg {c x : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ Work.Bottcher.Core.tOrbit c x n := by
  induction n with
  | zero => simpa [Work.Bottcher.Core.tOrbit] using hx
  | succ n ih =>
      rw [Work.Bottcher.Core.tOrbit_succ]
      nlinarith [sq_nonneg (Work.Bottcher.Core.tOrbit c x n)]

/-- The real orbit of `t ↦ t² + c` is increasing in the initial point. -/
theorem tOrbit_mono {c x y : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ) :
    Work.Bottcher.Core.tOrbit c x n ≤ Work.Bottcher.Core.tOrbit c y n := by
  induction n with
  | zero => simpa [Work.Bottcher.Core.tOrbit] using hxy
  | succ n ih =>
      rw [Work.Bottcher.Core.tOrbit_succ, Work.Bottcher.Core.tOrbit_succ]
      have hxn : 0 ≤ Work.Bottcher.Core.tOrbit c x n := tOrbit_nonneg hc hx n
      have hyn : 0 ≤ Work.Bottcher.Core.tOrbit c y n := tOrbit_nonneg hc (le_trans hx hxy) n
      nlinarith

/-- **Monotonicity of the Green function along the real axis.**  For real `c ≥ 0` and
`c ≤ x ≤ y` one has `G_c x ≤ G_c y`. -/
theorem green_ofReal_mono {c x y : ℝ} (hc : 0 ≤ c) (hx : c ≤ x) (hxy : x ≤ y) :
    Work.Bottcher.green (c : ℂ) (x : ℂ) ≤ Work.Bottcher.green (c : ℂ) (y : ℂ) := by
  have hx0 : 0 ≤ x := le_trans hc hx
  have hmono : ∀ n, Work.Escape.greenIter (Tantibar (c : ℂ)) 2 (x : ℂ) n
      ≤ Work.Escape.greenIter (Tantibar (c : ℂ)) 2 (y : ℂ) n := by
    intro n
    have h1 : 0 ≤ Work.Bottcher.Core.tOrbit c x n := tOrbit_nonneg hc hx0 n
    have h2 : Work.Bottcher.Core.tOrbit c x n ≤ Work.Bottcher.Core.tOrbit c y n :=
      tOrbit_mono hc hx0 hxy n
    rw [Work.Escape.greenIter_def, Work.Escape.greenIter_def,
      Work.Bottcher.Core.Tantibar_iterate_ofReal, Work.Bottcher.Core.Tantibar_iterate_ofReal,
      show ‖((Work.Bottcher.Core.tOrbit c x n : ℝ) : ℂ)‖ = Work.Bottcher.Core.tOrbit c x n
        from by simp [abs_of_nonneg h1],
      show ‖((Work.Bottcher.Core.tOrbit c y n : ℝ) : ℂ)‖ = Work.Bottcher.Core.tOrbit c y n
        from by simp [abs_of_nonneg (le_trans h1 h2)]]
    exact mul_le_mul_of_nonneg_left (Work.Escape.logPos_mono h2) (by positivity)
  have h1 := Work.Escape.tendsto_greenIter (Tantibar (c : ℂ)) 2 ‖(c : ℂ)‖
    (Work.Escape.monicGrowth_Tantibar (c : ℂ)) le_rfl (x : ℂ)
  have h2 := Work.Escape.tendsto_greenIter (Tantibar (c : ℂ)) 2 ‖(c : ℂ)‖
    (Work.Escape.monicGrowth_Tantibar (c : ℂ)) le_rfl (y : ℂ)
  exact le_of_tendsto_of_tendsto h1 h2 (Filter.Eventually.of_forall hmono)

/-- **The half line `[c, ∞)` lies in the critical domain.**  For real `c > 1/4` and real
`x ≥ c` one has `(x : ℂ) ∈ critDomain c`, i.e. `G_c x > G_c 0`.

Indeed `c > 1/4` gives `(c : ℂ) ∉ Mb`, hence `G_c 0 < G_c c`; and `G_c c ≤ G_c x` by
`green_ofReal_mono`. -/
theorem mem_critDomain_ofReal_of_le {c x : ℝ} (hc : 1 / 4 < c) (hx : c ≤ x) :
    (x : ℂ) ∈ Work.ParamRays.critDomain (c : ℂ) := by
  have hcpos : 0 < c := by linarith
  have hcMb : (c : ℂ) ∉ Work.ParamRays.Mb :=
    Work.ParamRays.real_not_mem_Mb_of_one_fourth_lt hc
  have hself : (c : ℂ) ∈ Work.ParamRays.critDomain (c : ℂ) :=
    Work.ParamRays.self_mem_critDomain hcMb
  rw [Work.ParamRays.mem_critDomain] at hself ⊢
  have hmono : Work.ParamRays.greenFun (c : ℂ) (c : ℂ)
      ≤ Work.ParamRays.greenFun (c : ℂ) (x : ℂ) := by
    rw [← Work.Bottcher.Contraction.green_eq_greenFun (c : ℂ) (c : ℂ),
      ← Work.Bottcher.Contraction.green_eq_greenFun (c : ℂ) (x : ℂ)]
    exact green_ofReal_mono hcpos.le le_rfl hx
  linarith

/-! ## `varphiCrit` is real on the real axis -/

/-- Complex conjugation fixes the real numbers, so it transports the canonical critical Böttcher
coordinate of `T_c` for real `c` to itself; by uniqueness they agree, and at a real point `x` of
the critical domain this says that `varphiCrit c x` is fixed by conjugation. -/
theorem varphiCrit_ofReal_conj {c x : ℝ}
    (hx : (x : ℂ) ∈ Work.ParamRays.critDomain (c : ℂ)) :
    (starRingEnd ℂ) (Work.Bottcher.varphiCrit (c : ℂ) (x : ℂ))
      = Work.Bottcher.varphiCrit (c : ℂ) (x : ℂ) := by
  have hψ : Work.ParamRays.IsCritBottcher ((starRingEnd ℂ) (c : ℂ))
      (fun w : ℂ => (starRingEnd ℂ) (Work.Bottcher.varphiCrit (c : ℂ) ((starRingEnd ℂ) w))) :=
    Work.ParamRaysCrit.CritTransport.isCritBottcher_conj
      (Work.Bottcher.isCritBottcher_varphiCrit (c : ℂ))
  rw [Complex.conj_ofReal] at hψ
  have huniq := Work.Bottcher.varphiCrit_unique hψ hx
  rw [Complex.conj_ofReal] at huniq
  exact huniq.symm

/-- A complex number fixed by conjugation is the real number of its real part. -/
theorem complex_eq_ofReal_re_of_conj {z : ℂ} (h : (starRingEnd ℂ) z = z) :
    z = (z.re : ℂ) := by
  have hz : z.im = 0 := Complex.conj_eq_iff_im.mp h
  exact Complex.ext rfl (by simp [hz])

/-! ## Sign constancy on a half line -/

/-- A continuous real function on `[a, ∞)` which never vanishes and is positive at a point of
`[a, ∞)` is positive on all of `[a, ∞)`.

Reason: `[a, ∞)` is preconnected, hence order-convex, so a point of the half line between a
non-positive and a positive value of `g` would have to be a zero of `g`. -/
theorem pos_of_continuousOn_Ici_of_pos {a : ℝ} {g : ℝ → ℝ}
    (hcont : ContinuousOn g (Set.Ici a)) (hne : ∀ x ∈ Set.Ici a, g x ≠ 0)
    {x₀ : ℝ} (hx₀ : a ≤ x₀) (hpos : 0 < g x₀) {x : ℝ} (hx : a ≤ x) : 0 < g x := by
  by_contra h
  have hle : g x ≤ 0 := le_of_not_gt h
  have himg : IsPreconnected (g '' Set.Ici a) := isPreconnected_Ici.image g hcont
  have h0 : (0 : ℝ) ∈ g '' Set.Ici a :=
    himg.ordConnected.out (Set.mem_image_of_mem g hx) (Set.mem_image_of_mem g hx₀)
      ⟨hle, hpos.le⟩
  obtain ⟨z, hz, hgz⟩ := h0
  exact hne z hz hgz

/-- **The critical Böttcher coordinate is positive on the positive real axis, past the cusp.**
For real `c > 1/4` there is a positive real `r` with `varphiCrit (c:ℂ) (c:ℂ) = (r : ℂ)`.

This *unconditionally* determines the sign of the constant in the uniform asymptotic
`Φ c / c → 1`: the ratio `Φ c / bottcher c c` is a fourth root of unity which is constant for
`‖c‖ ≥ 8`, hence equal to `1` as soon as one real parameter gives the sign `+1` (there
`bottcher c c > 0` by `Work.NAKANE.Asymptotic.bottcher_real_pos`).
(The statement is *not* the existing `Work.ParamRays.Phi_real_pos_of_one_fourth_lt`: that one takes
`NakaneInput` as a hypothesis, which is what must be proved here.)

Route.

1. `c > 1/4` gives `c ∉ Mb` (`Work.ParamRays.real_not_mem_Mb_of_one_fourth_lt`), hence
   `G_c(0) > 0` (`Work.ParamRays.paramPotential_pos`), and `G_c(c) = 2 G_c(0)`
   (`Work.Bottcher.Green.green_comm` with `Work.Bottcher.Tantibar_zero`), and
   `c ∈ critDomain c` (`Work.ParamRays.self_mem_critDomain`).
2. **Monotonicity.** For `c ≤ x ≤ y` and all `n`, `(Tantibar c)^[n] x ≤ (Tantibar c)^[n] y` (the map
   `u ↦ u^2 + c` is increasing on `[0,∞)` and maps `[c,∞)` into itself); hence `green c x ≤ green c y`
   (limits of `2^{-n} log⁺`).  So for `x ≥ c`, `green c x ≥ green c c = 2 * green c 0 > green c 0`,
   i.e. `[c,∞) ⊆ critDomain c`.
3. **Realness.** For real `c`, `Tantibar c` commutes with `conj`, so
   `Work.ParamRaysCrit.CritTransport.isCritBottcher_conj` (or the `Work.Bottcher` copy) plus
   `varphiCrit_unique` gives `varphiCrit (c:ℂ) (conj z) = conj (varphiCrit (c:ℂ) z)`; at real `z`
   this makes `varphiCrit c z` real.
4. **Sign constancy.** On the preconnected `[c,∞) ⊆ critDomain c` the function
   `x ↦ (varphiCrit c x).re` is continuous (`Work.Bottcher.varphiCrit_continuousOn`) and never `0`
   (realness plus `Work.Bottcher.varphiCrit_ne_zero`), so its sign is constant; cf.
   `Work.ParamRays.pos_of_continuousOn_Ioi_of_eventually_pos` in
   `Submission/Work/ParamRays/Phi_real_pos_of_one_fourth_lt.lean`.
5. **The sign is `+1`.** For a real `x > farRadius c` one has
   `varphiCrit c x = bottcher c x`
   (`Work.NAKANE.BottcherFar.jointVarphi_eq_jointBottcher_of_far`) and `bottcher c x > 0`
   (`Work.NAKANE.Asymptotic.bottcher_real_pos`).  Hence the sign is `+1` on `[c,∞)`, so
   `varphiCrit c c` is positive. -/
theorem varphiCrit_self_pos_of_real {c : ℝ} (hc : 1 / 4 < c) :
    ∃ r : ℝ, 0 < r ∧ Work.Bottcher.varphiCrit (c : ℂ) (c : ℂ) = (r : ℂ) := by
  have hcpos : 0 < c := by linarith
  -- A real point beyond the far radius, where `varphiCrit` is given by the product formula.
  set x₀ : ℝ := max c (Work.NAKANE.farRadius ‖(c : ℂ)‖ + 1) with hx₀def
  have hcx₀ : c ≤ x₀ := le_max_left _ _
  have hRx₀ : Work.NAKANE.farRadius ‖(c : ℂ)‖ < x₀ := by
    have h : Work.NAKANE.farRadius ‖(c : ℂ)‖ + 1 ≤ x₀ := le_max_right _ _
    linarith
  have hx₀pos : 0 < x₀ := lt_of_lt_of_le hcpos hcx₀
  -- The half line `[c, ∞)` is contained in the critical domain.
  have hmem : ∀ x ∈ Set.Ici c, (x : ℂ) ∈ Work.ParamRays.critDomain (c : ℂ) :=
    fun x hx => mem_critDomain_ofReal_of_le hc hx
  -- Continuity of the real part of `varphiCrit c` along the real axis.
  have hcont : ContinuousOn (fun x : ℝ => (Work.Bottcher.varphiCrit (c : ℂ) (x : ℂ)).re)
      (Set.Ici c) :=
    Complex.continuous_re.comp_continuousOn
      ((Work.Bottcher.varphiCrit_continuousOn (c : ℂ)).comp Complex.continuous_ofReal.continuousOn
        hmem)
  -- Realness, so that non-vanishing transfers from `varphiCrit` to its real part.
  have hne : ∀ x ∈ Set.Ici c, (Work.Bottcher.varphiCrit (c : ℂ) (x : ℂ)).re ≠ 0 := by
    intro x hx hzero
    have hreal := varphiCrit_ofReal_conj (hmem x hx)
    have hz : Work.Bottcher.varphiCrit (c : ℂ) (x : ℂ)
        = (((Work.Bottcher.varphiCrit (c : ℂ) (x : ℂ)).re : ℝ) : ℂ) :=
      complex_eq_ofReal_re_of_conj hreal
    have hzero' : Work.Bottcher.varphiCrit (c : ℂ) (x : ℂ) = 0 := by
      rw [hz, hzero]
      simp
    exact Work.Bottcher.varphiCrit_ne_zero (hmem x hx) hzero'
  -- At a far real point the value is the (positive real) product formula.
  have hpos₀ : 0 < (Work.Bottcher.varphiCrit (c : ℂ) (x₀ : ℂ)).re := by
    have hRnorm : Work.NAKANE.farRadius ‖(c : ℂ)‖ < ‖(x₀ : ℂ)‖ := by
      rw [show ‖(x₀ : ℂ)‖ = |x₀| from by simp, abs_of_pos hx₀pos]
      exact hRx₀
    have hfar := Work.NAKANE.BottcherFar.jointVarphi_eq_jointBottcher_of_far
      (c := (c : ℂ)) (z := (x₀ : ℂ)) hRnorm
    rw [Work.NAKANE.jointVarphi_apply, Work.NAKANE.jointBottcher_apply] at hfar
    obtain ⟨r, hrpos, hr⟩ := Work.NAKANE.Asymptotic.bottcher_real_pos hcpos hx₀pos
    rw [hfar, hr, Complex.ofReal_re]
    exact hrpos
  -- The sign is constant on `[c, ∞)`, hence `+1` at `c`.
  have hposc : 0 < (Work.Bottcher.varphiCrit (c : ℂ) (c : ℂ)).re :=
    pos_of_continuousOn_Ici_of_pos hcont hne hcx₀ hpos₀ (le_refl c)
  have hrealc := varphiCrit_ofReal_conj (hmem c (le_refl c))
  exact ⟨(Work.Bottcher.varphiCrit (c : ℂ) (c : ℂ)).re, hposc,
    complex_eq_ofReal_re_of_conj hrealc⟩

end Work.NAKANE.Asymptotic
