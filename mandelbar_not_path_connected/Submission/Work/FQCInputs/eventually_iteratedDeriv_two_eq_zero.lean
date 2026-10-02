/-
# `Work.FQCInputs.eventually_iteratedDeriv_two_eq_zero`

The local Hurwitz (minimum-modulus) step of the continuation route to the simplicity of the
transported parabolic point (S5 of `Submission/Work/NOTES_LEAD_mandelbar_simple.md` §3.6).

Let `P : ℝ → ℂ → ℂ` be a family of polynomial functions, jointly continuous in `(t, z)`, and let
`w : ℝ → ℂ` be continuous at `t₀`.  Assume that for every `t`, `w t` is a root of `P t` of order at
least two (`P t (w t) = 0`, `deriv (P t) (w t) = 0`), and that near `t₀` the *only* root of `P t`
in the closed ball `closedBall (w t₀) ε` is `w t` (`hiso`).  If the second derivative vanishes at
`t₀` (`hN`), then it vanishes for all `t` near `t₀`.

This is the statement that the set `{t | iteratedDeriv 2 (P t) (w t) = 0}` is *open*: the
multiplicity of an isolated zero of a polynomial is locally constant along a continuous family.

The proof writes `P t z = (z - w t)² · H_t z` with `H_t` the polynomial
`divX (divX (taylor (w t) (p t)))` evaluated at `z - w t` (so that `H_t` is entire and
`2 * H_t (w t) = iteratedDeriv 2 (P t) (w t)`), and applies the maximum modulus principle to
`1 / H_t` on `ball (w t₀) ε`.  The only subtlety is that the ball is *not* centred at `w t`, so the
lower bound on `H_t` on the frontier uses `‖z - w t‖ ≤ 3ε/2` (valid because `‖w t - w t₀‖ ≤ ε/2`).
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FQCInputs

open Polynomial Metric Filter Set
open scoped Topology

/-- **The polynomial factorisation** underlying the Hurwitz step.

Let `p : ℂ[X]` have a zero of order at least two at `W` (`p.eval W = 0` and
`(p.derivative).eval W = 0`), and put `Q := divX (divX (taylor W p))`.  Then

* `p.eval (W + u) = u^2 * Q.eval u` for all `u` (so `Q` is the polynomial `p(W+u)/u²`), and
* `2 * Q.eval 0 = iteratedDeriv 2 (fun z => p.eval z) W`, i.e. `Q.eval 0` is half the second
  derivative of the polynomial function at `W`.

`divX` shifts the coefficients (`(divX q).coeff n = q.coeff (n+1)`) and `taylor W p = p.comp (X + W)`
is the Taylor shift. -/
private lemma poly_factor (p : Polynomial ℂ) (W : ℂ) (h0 : p.eval W = 0)
    (h1 : p.derivative.eval W = 0) :
    (∀ u : ℂ, p.eval (W + u) = u^2 * (divX (divX (taylor W p))).eval u) ∧
    2 * (divX (divX (taylor W p))).eval 0 = iteratedDeriv 2 (fun z => p.eval z) W := by
  constructor
  · intro u
    set s := taylor W p with hs
    have hs0 : s.eval 0 = 0 := by rw [hs, taylor_eval]; simpa using h0
    have hsc0 : s.coeff 0 = 0 := by rw [coeff_zero_eq_eval_zero]; exact hs0
    have hs1 : (divX s).eval 0 = 0 := by
      rw [← coeff_zero_eq_eval_zero, coeff_divX]
      rw [show s.coeff 1 = p.derivative.eval W from by rw [hs, taylor_coeff, hasseDeriv_one]]
      exact h1
    have hs1c0 : (divX s).coeff 0 = 0 := by rw [coeff_zero_eq_eval_zero]; exact hs1
    have key1 : u * (divX s).eval u = s.eval u := by
      have := congrArg (fun q : Polynomial ℂ => q.eval u) (X_mul_divX_add s)
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
        at this
      rw [hsc0, add_zero] at this
      exact this
    have key2 : u * (divX (divX s)).eval u = (divX s).eval u := by
      have := congrArg (fun q : Polynomial ℂ => q.eval u) (X_mul_divX_add (divX s))
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
        at this
      rw [hs1c0, add_zero] at this
      exact this
    calc p.eval (W + u) = s.eval u := by rw [hs, taylor_eval, add_comm]
      _ = u * (divX s).eval u := key1.symm
      _ = u * (u * (divX (divX s)).eval u) := by rw [key2]
      _ = u^2 * (divX (divX s)).eval u := by ring
  · set s := taylor W p with hs
    have hQ0 : (divX (divX s)).eval 0 = s.coeff 2 := by
      rw [← coeff_zero_eq_eval_zero, coeff_divX, coeff_divX]
    have hs2 : s.coeff 2 = (hasseDeriv 2 p).eval W := by rw [hs, taylor_coeff]
    have hfact : (2:ℂ) * (hasseDeriv 2 p).eval W = ((derivative^[2]) p).eval W := by
      have h := congrArg (fun (f : Polynomial ℂ → Polynomial ℂ) => f p)
        (Polynomial.factorial_smul_hasseDeriv (R := ℂ) 2)
      simp only [Nat.factorial_two] at h
      rw [← h]
      simp [Polynomial.eval_mul]
    have hder : ((derivative^[2]) p).eval W = iteratedDeriv 2 (fun z => p.eval z) W := by
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
      have h1 : deriv (fun z : ℂ => p.eval z) = fun z => p.derivative.eval z := by
        funext z; exact Polynomial.deriv p
      rw [h1, Polynomial.deriv]
      rfl
    rw [hQ0, hs2, hfact, hder]

/-- **The single-`t` Hurwitz step.**  If `p` has a double zero at `W` which is the only zero in
`closedBall w₀ ε`, `W` is within `ε/2` of the centre `w₀`, `p` is bounded below by `m/2` on the
sphere `sphere w₀ ε`, and the second derivative at `W` is smaller than `4m/(9ε²)`, then it vanishes.

The maximum modulus principle applied to `1 / H` on `ball w₀ ε` (where `p z = (z - W)² H z`) turns
the vanishing of the second derivative at `W` into a lower bound `4m/(9ε²)` on its modulus. -/
private lemma key_step {p : Polynomial ℂ} {W w₀ : ℂ} {ε m : ℝ}
    (hε : 0 < ε) (hm : 0 < m)
    (hp0 : p.eval W = 0) (hp1 : p.derivative.eval W = 0)
    (hiso : ∀ z ∈ Metric.closedBall w₀ ε, p.eval z = 0 → z = W)
    (hclose : ‖W - w₀‖ ≤ ε/2)
    (hunif : ∀ z ∈ Metric.sphere w₀ ε, m/2 ≤ ‖p.eval z‖)
    (hsmall : ‖iteratedDeriv 2 (fun z => p.eval z) W‖ < 4*m/(9*ε^2)) :
    iteratedDeriv 2 (fun z => p.eval z) W = 0 := by
  obtain ⟨hfactor, hsecond⟩ := poly_factor p W hp0 hp1
  let H : ℂ → ℂ := fun z => (divX (divX (taylor W p))).eval (z - W)
  have hH_def : ∀ z : ℂ, H z = (divX (divX (taylor W p))).eval (z - W) := fun z => rfl
  have hPz : ∀ z : ℂ, p.eval z = (z - W)^2 * H z := by
    intro z
    have h1 := hfactor (z - W)
    have hW : W + (z - W) = z := by ring
    rw [hW] at h1
    rw [hH_def z]
    exact h1
  have hHW : H W = (divX (divX (taylor W p))).eval 0 := by rw [hH_def W, sub_self]
  have hHval : 2 * H W = iteratedDeriv 2 (fun z => p.eval z) W := by
    rw [hHW]; exact hsecond
  by_contra hne
  have hHWne : H W ≠ 0 := by
    intro h
    apply hne
    rw [← hHval, h, mul_zero]
  have hH_ne : ∀ z ∈ Metric.closedBall w₀ ε, H z ≠ 0 := by
    intro z hz hz0
    have hpe : p.eval z = 0 := by rw [hPz z, hz0, mul_zero]
    have hzW : z = W := hiso z hz hpe
    refine hHWne ?_
    rw [← hzW]; exact hz0
  have hH_diff : Differentiable ℂ H := by
    have hHeq : H = fun z : ℂ => (divX (divX (taylor W p))).eval (z - W) := by
      funext z; rw [hH_def]
    rw [hHeq]
    exact (Polynomial.differentiable (divX (divX (taylor W p)))).comp
      (differentiable_id.sub_const W)
  have hdinv : DiffContOnCl ℂ H⁻¹ (Metric.ball w₀ ε) := by
    refine (hH_diff.diffContOnCl).inv ?_
    intro z hz
    rw [closure_ball w₀ hε.ne'] at hz
    exact hH_ne z hz
  have hC : ∀ z ∈ frontier (Metric.ball w₀ ε), ‖H⁻¹ z‖ ≤ 9*ε^2/(2*m) := by
    intro z hz
    rw [frontier_ball w₀ hε.ne'] at hz
    have hzW : z ≠ W := by
      intro h
      rw [h] at hz
      have hd := Metric.mem_sphere.mp hz
      rw [dist_eq_norm] at hd
      linarith [hclose, hε]
    have hdenpos : 0 < ‖z - W‖^2 := by
      have : z - W ≠ 0 := sub_ne_zero.mpr hzW
      positivity
    have hHz : ‖H z‖ = ‖p.eval z‖ / ‖z - W‖^2 := by
      rw [hPz z, norm_mul, norm_pow]
      rw [mul_div_cancel_left₀ _ (ne_of_gt hdenpos)]
    have hzw₀ : ‖z - w₀‖ = ε := by
      have := Metric.mem_sphere.mp hz
      rwa [dist_eq_norm] at this
    have hzW_le : ‖z - W‖ ≤ 3*ε/2 := by
      have h1 : z - W = (z - w₀) + (w₀ - W) := by ring
      rw [h1]
      refine (norm_add_le _ _).trans ?_
      rw [hzw₀, norm_sub_rev]
      linarith [hclose]
    have hden_le : ‖z - W‖^2 ≤ (3*ε/2)^2 := by nlinarith [hzW_le, norm_nonneg (z - W)]
    have hHz_ge : 2*m/(9*ε^2) ≤ ‖H z‖ := by
      rw [hHz]
      have h1 : 2*m/(9*ε^2) = (m/2)/((3*ε/2)^2) := by field_simp; ring
      rw [h1, div_le_div_iff₀ (by positivity : (0:ℝ) < (3*ε/2)^2) hdenpos]
      have hs1 : (m/2) * ‖z - W‖^2 ≤ ‖p.eval z‖ * ‖z - W‖^2 :=
        mul_le_mul_of_nonneg_right (hunif z hz) (le_of_lt hdenpos)
      have hs2 : ‖p.eval z‖ * ‖z - W‖^2 ≤ ‖p.eval z‖ * (3*ε/2)^2 :=
        mul_le_mul_of_nonneg_left hden_le (norm_nonneg _)
      linarith
    have hHz_pos : 0 < ‖H z‖ := lt_of_lt_of_le (by positivity) hHz_ge
    have hc : 9*ε^2/(2*m) = (2*m/(9*ε^2))⁻¹ := by rw [inv_div]
    rw [show H⁻¹ z = (H z)⁻¹ from rfl, norm_inv, hc]
    exact (inv_le_inv₀ hHz_pos (by positivity)).mpr hHz_ge
  have hzW_ball : W ∈ closure (Metric.ball w₀ ε) := by
    rw [closure_ball w₀ hε.ne', Metric.mem_closedBall, dist_eq_norm]
    linarith [hclose]
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le
    (isBounded_ball (x := w₀) (r := ε)) hdinv hC hzW_ball
  have hHW_ge : 2*m/(9*ε^2) ≤ ‖H W‖ := by
    have hHW_pos : 0 < ‖H W‖ := norm_pos_iff.mpr hHWne
    have hc : 9*ε^2/(2*m) = (2*m/(9*ε^2))⁻¹ := by rw [inv_div]
    rw [show H⁻¹ W = (H W)⁻¹ from rfl, norm_inv, hc] at hmax
    exact (inv_le_inv₀ hHW_pos (by positivity)).mp hmax
  have hkey : 4*m/(9*ε^2) = 2 * (2*m/(9*ε^2)) := by ring
  have : 4*m/(9*ε^2) ≤ ‖iteratedDeriv 2 (fun z => p.eval z) W‖ := by
    rw [← hHval, norm_mul]
    have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
    rw [h2]
    linarith [hHW_ge, hkey]
  linarith [this, hsmall]

theorem eventually_iteratedDeriv_two_eq_zero {P : ℝ → ℂ → ℂ} {w : ℝ → ℂ} {t₀ ε : ℝ}
    (hε : 0 < ε) (hpoly : ∀ t, ∃ p : Polynomial ℂ, P t = fun z => p.eval z)
    (hcont : Continuous fun q : ℝ × ℂ => P q.1 q.2) (hw : ContinuousAt w t₀)
    (h2cont : ContinuousAt (fun t => iteratedDeriv 2 (P t) (w t)) t₀)
    (h0 : ∀ t, P t (w t) = 0) (h1 : ∀ t, deriv (P t) (w t) = 0)
    (hiso : ∀ᶠ t in nhds t₀, ∀ z ∈ Metric.closedBall (w t₀) ε, P t z = 0 → z = w t)
    (hN : iteratedDeriv 2 (P t₀) (w t₀) = 0) :
    ∀ᶠ t in nhds t₀, iteratedDeriv 2 (P t) (w t) = 0 := by
  let pt : ℝ → Polynomial ℂ := fun t => Classical.choose (hpoly t)
  have hpt : ∀ t, P t = fun z => (pt t).eval z := fun t => Classical.choose_spec (hpoly t)
  have hiso0 : ∀ z ∈ Metric.closedBall (w t₀) ε, P t₀ z = 0 → z = w t₀ := hiso.self_of_nhds
  have hcontP0 : Continuous fun z : ℂ => P t₀ z := by
    rw [hpt t₀]; exact Polynomial.continuous (pt t₀)
  -- the minimum of `‖P t₀‖` on the sphere `sphere (w t₀) ε`
  obtain ⟨z_m, hz_m_sphere, hz_m_min⟩ :=
    (isCompact_sphere (w t₀) ε).exists_isMinOn
      ⟨w t₀ + (ε : ℂ), by
        rw [Metric.mem_sphere, dist_eq_norm]
        simp [Complex.norm_real, abs_of_pos hε]⟩
      hcontP0.norm.continuousOn
  have hm_min : ∀ z ∈ Metric.sphere (w t₀) ε, ‖P t₀ z_m‖ ≤ ‖P t₀ z‖ :=
    isMinOn_iff.mp hz_m_min
  have hz_m_closed : z_m ∈ Metric.closedBall (w t₀) ε := sphere_subset_closedBall hz_m_sphere
  have hm_pos : 0 < ‖P t₀ z_m‖ := by
    refine norm_pos_iff.mpr ?_
    intro h
    have hzW : z_m = w t₀ := hiso0 z_m hz_m_closed h
    have hdist := Metric.mem_sphere.mp hz_m_sphere
    rw [hzW, dist_self] at hdist
    exact absurd hdist.symm hε.ne'
  have hκ : 0 < 4*‖P t₀ z_m‖/(9*ε^2) := by positivity
  have htend : Tendsto (fun t => iteratedDeriv 2 (P t) (w t)) (nhds t₀) (nhds 0) := by
    rw [← hN]; exact h2cont
  have hev2 : ∀ᶠ t in nhds t₀, ‖iteratedDeriv 2 (P t) (w t)‖ < 4*‖P t₀ z_m‖/(9*ε^2) := by
    have := (Metric.tendsto_nhds.mp htend) _ hκ
    simpa [dist_eq_norm] using this
  have hev_unif : ∀ᶠ t in nhds t₀,
      ∀ z ∈ Metric.sphere (w t₀) ε, ‖P t z - P t₀ z‖ < ‖P t₀ z_m‖/2 := by
    refine IsCompact.eventually_forall_of_forall_eventually (isCompact_sphere (w t₀) ε) ?_
    intro y hy
    have hcf : ContinuousAt (fun z : ℝ × ℂ => P z.1 z.2 - P t₀ z.2) (t₀, y) :=
      (hcont.sub (hcontP0.comp continuous_snd)).continuousAt
    have hm2 : (0:ℝ) < ‖P t₀ z_m‖/2 := by linarith
    have hgoal := (Metric.tendsto_nhds.mp hcf) _ hm2
    simpa [dist_eq_norm] using hgoal
  have hev_w : ∀ᶠ t in nhds t₀, ‖w t - w t₀‖ ≤ ε/2 := by
    have := (Metric.tendsto_nhds.mp hw) (ε/2) (by linarith)
    filter_upwards [this] with t ht
    rw [dist_eq_norm] at ht
    exact le_of_lt ht
  have hev_all : ∀ᶠ t in nhds t₀,
      (∀ z ∈ Metric.closedBall (w t₀) ε, P t z = 0 → z = w t) ∧
      ‖w t - w t₀‖ ≤ ε/2 ∧
      (∀ z ∈ Metric.sphere (w t₀) ε, ‖P t z - P t₀ z‖ < ‖P t₀ z_m‖/2) ∧
      ‖iteratedDeriv 2 (P t) (w t)‖ < 4*‖P t₀ z_m‖/(9*ε^2) := by
    filter_upwards [hiso, hev_w, hev_unif, hev2] with t h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  filter_upwards [hev_all] with t ht
  obtain ⟨hiso_t, hwt_le, hunif_t, hsmall_t⟩ := ht
  have hp0 : (pt t).eval (w t) = 0 := by
    have := h0 t; rw [hpt t] at this; simpa using this
  have hp1 : (pt t).derivative.eval (w t) = 0 := by
    have := h1 t; rw [hpt t, Polynomial.deriv] at this; simpa using this
  have hiso_t' : ∀ z ∈ Metric.closedBall (w t₀) ε, (pt t).eval z = 0 → z = w t := by
    intro z hz hz0
    exact hiso_t z hz (by rw [hpt t]; exact hz0)
  have hunif_t' : ∀ z ∈ Metric.sphere (w t₀) ε, ‖P t₀ z_m‖/2 ≤ ‖(pt t).eval z‖ := by
    intro z hz
    have h1 : ‖P t₀ z_m‖ ≤ ‖P t₀ z‖ := hm_min z hz
    have h2 : ‖P t z - P t₀ z‖ < ‖P t₀ z_m‖/2 := hunif_t z hz
    have h3 : P t z = (pt t).eval z := by rw [hpt t]
    have htri : ‖P t₀ z‖ - ‖P t z - P t₀ z‖ ≤ ‖P t z‖ := by
      have h := abs_norm_sub_norm_le (P t z) (P t₀ z)
      rw [abs_le] at h
      linarith [h.1]
    rw [h3] at h2 htri
    linarith
  have hsmall_t' : ‖iteratedDeriv 2 (fun z => (pt t).eval z) (w t)‖
      < 4*‖P t₀ z_m‖/(9*ε^2) := by rw [← hpt t]; exact hsmall_t
  have hres := key_step hε hm_pos hp0 hp1 hiso_t' hwt_le hunif_t' hsmall_t'
  rw [hpt t]; exact hres

end Work.FQCInputs
