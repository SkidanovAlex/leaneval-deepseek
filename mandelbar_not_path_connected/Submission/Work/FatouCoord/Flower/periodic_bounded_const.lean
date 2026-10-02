import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology

namespace Work.FatouCoord.Flower

/-- A holomorphic function on a left half-plane that is `1`-periodic there and bounded is
constant.

The proof shows that the derivative vanishes.  For `w` in the half-plane `{w | w.re < -R}` the
periodicity relation `P (w + 1) = P w` gives `deriv P (w + 1) = deriv P w`, so
`deriv P w = deriv P (w - n)` for every `n`.  Cauchy's estimate on the disc of radius `n` centred
at `w - n` (which lies in the half-plane, since `(w - n).re + n = w.re < -R`) bounds
`‖deriv P (w - n)‖` by `B / n`.  Letting `n → ∞` gives `deriv P w = 0`, and a function with zero
derivative on the (convex, hence connected) half-plane is constant. -/
theorem periodic_bounded_const {P : ℂ → ℂ} {R B : ℝ}
    (hd : DifferentiableOn ℂ P {w : ℂ | w.re < -R})
    (hper : ∀ w : ℂ, w.re < -R → P (w + 1) = P w)
    (hb : ∀ w : ℂ, w.re < -R → ‖P w‖ ≤ B) :
    ∃ c : ℂ, ∀ w : ℂ, w.re < -R → P w = c := by
  have hs_open : IsOpen {w : ℂ | w.re < -R} :=
    isOpen_lt Complex.continuous_re continuous_const
  have hs_pre : IsPreconnected {w : ℂ | w.re < -R} :=
    (convex_halfSpace_re_lt (-R)).isPreconnected
  -- Step 1: the derivative inherits the periodicity.
  have hderiv_per : ∀ u : ℂ, u.re < -R → deriv P (u + 1) = deriv P u := by
    intro u hu
    have heq : (fun v : ℂ => P v) =ᶠ[𝓝 u] (fun v : ℂ => P (v + 1)) := by
      filter_upwards [hs_open.mem_nhds hu] with v hv
      exact (hper v hv).symm
    have h := heq.deriv_eq
    rw [deriv_comp_add_const] at h
    exact h.symm
  -- It suffices to show the derivative vanishes on the half-plane.
  refine IsOpen.exists_is_const_of_deriv_eq_zero hs_open hs_pre hd ?_
  intro w hw
  have hw' : w.re < -R := hw
  -- Step 2: `deriv P w = deriv P (w - n)` for every `n`.
  have hshift : ∀ n : ℕ, deriv P w = deriv P (w - (n : ℂ)) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [ih]
      have hk : (w - ((k : ℂ) + 1)).re < -R := by
        have h1 : (w - ((k : ℂ) + 1)).re = w.re - ((k : ℝ) + 1) := by
          simp [Complex.sub_re, Complex.add_re]
        rw [h1]
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      have h := hderiv_per (w - ((k : ℂ) + 1)) hk
      have e : w - ((k : ℂ) + 1) + 1 = w - (k : ℂ) := by ring
      rw [e] at h
      simpa [Nat.cast_succ] using h
  -- Step 3: Cauchy's estimate at the shifted point.
  have hbound : ∀ n : ℕ, 1 ≤ n → ‖deriv P w‖ ≤ B / (n : ℝ) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hsub : Metric.closedBall (w - (n : ℂ)) (n : ℝ) ⊆ {w : ℂ | w.re < -R} := by
      intro z hz
      change z.re < -R
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have h2 : (z - (w - (n : ℂ))).re ≤ (n : ℝ) := le_trans (Complex.re_le_norm _) hz
      have hsplit : z.re = (w - (n : ℂ)).re + (z - (w - (n : ℂ))).re := by
        have h : z = (w - (n : ℂ)) + (z - (w - (n : ℂ))) := by ring
        conv_lhs => rw [h]
        exact Complex.add_re _ _
      have hwr : (w - (n : ℂ)).re = w.re - (n : ℝ) := by simp [Complex.sub_re]
      rw [hsplit, hwr]
      linarith only [h2, hw']
    have hdc : DiffContOnCl ℂ P (Metric.ball (w - (n : ℂ)) (n : ℝ)) :=
      DiffContOnCl.mk_ball (hd.mono (Metric.ball_subset_closedBall.trans hsub))
        ((hd.mono hsub).continuousOn)
    have hC : ∀ z ∈ Metric.sphere (w - (n : ℂ)) (n : ℝ), ‖P z‖ ≤ B := by
      intro z hz
      exact hb z (hsub (Metric.sphere_subset_closedBall hz))
    have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hnpos hdc hC
    rw [hshift n]
    exact hcauchy
  -- Step 4: let `n → ∞`.
  have hev : ∀ᶠ n : ℕ in Filter.atTop, ‖deriv P w‖ ≤ B / (n : ℝ) :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => hbound n hn⟩
  have hle : ‖deriv P w‖ ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds
      (tendsto_const_div_atTop_nhds_zero_nat B) hev
  exact norm_le_zero_iff.mp hle

end Work.FatouCoord.Flower
