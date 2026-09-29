import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.setup
import Submission.Work.A14D.log_growth_contra

/-!
# A14D — `logCoeff_growth_contra`

A holomorphic function `D` on the disc `ball (1/9) δ` can never agree with `c · y9 · log (· − 1/9)`
on the slit disc `slitDisk δ`, when `c ≠ 0` and `y9` is holomorphic on the disc with
`y9 (1/9) ≠ 0`.

The mechanism is the branch point of the principal logarithm at `1/9`: the relation shows that
`log (z − 1/9)` equals the *holomorphic* quotient `D z / (c · y9 z)` near `1/9`, hence is bounded
there; but along the vertical ray `z = 1/9 + t·i` (`t → 0⁺`), which lies in the slit disc, we have
`Re (log (z − 1/9)) = Real.log t → −∞`.  Two limits of the same quantity, one finite and one
`atBot`, contradict each other.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

theorem logCoeff_growth_contra {δ : ℝ} (hδ : 0 < δ) {y9 D : ℂ → ℂ} {c : ℂ}
    (hy9 : DifferentiableOn ℂ y9 (Metric.ball Work.A14D.ninth δ)) (hy9ne : y9 Work.A14D.ninth ≠ 0)
    (hD : DifferentiableOn ℂ D (Metric.ball Work.A14D.ninth δ)) (hc : c ≠ 0)
    (hid : ∀ z ∈ Work.A14D.slitDisk δ, c * y9 z * Complex.log (z - Work.A14D.ninth) = D z) : False := by
  -- `y9` and `D` are continuous at `1/9`, and `y9` is non-vanishing nearby.
  have hδmem : Metric.ball ninth δ ∈ 𝓝 ninth := Metric.ball_mem_nhds _ hδ
  have hy9c : ContinuousAt y9 ninth := hy9.continuousOn.continuousAt hδmem
  have hDc : ContinuousAt D ninth := hD.continuousOn.continuousAt hδmem
  have hy9ev : ∀ᶠ z in 𝓝 ninth, y9 z ≠ 0 :=
    hy9c.eventually (isOpen_ne.mem_nhds hy9ne)
  obtain ⟨ε₁, hε₁pos, hε₁sub⟩ := Metric.mem_nhds_iff.mp hy9ev
  set ε₂ : ℝ := min ε₁ δ with hε₂def
  have hε₂pos : 0 < ε₂ := lt_min hε₁pos hδ
  have hε₂δ : ε₂ ≤ δ := min_le_right _ _
  have hε₂ε₁ : ε₂ ≤ ε₁ := min_le_left _ _
  -- The vertical ray `zf t = 1/9 + t·i`, approaching `1/9` as `t → 0⁺`.
  set zf : ℝ → ℂ := fun t => ninth + (t : ℂ) * Complex.I with hzf
  have hzfcont : ContinuousAt zf 0 := by
    rw [hzf]
    exact continuousAt_const.add (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
  have hzftend : Tendsto zf (𝓝[>] (0 : ℝ)) (𝓝 ninth) := by
    have h : Tendsto zf (𝓝 (0 : ℝ)) (𝓝 ninth) := by
      have h2 := hzfcont.tendsto
      rwa [show zf 0 = ninth by simp [hzf]] at h2
    exact h.mono_left nhdsWithin_le_nhds
  -- The quotient `D / (c · y9)` is continuous at `1/9` …
  have hgat : ContinuousAt (fun z => D z / (c * y9 z)) ninth :=
    hDc.div (hy9c.const_mul c) (mul_ne_zero hc hy9ne)
  have hglim : Tendsto (fun t => (D (zf t) / (c * y9 (zf t))).re)
      (𝓝[>] (0 : ℝ)) (𝓝 ((D ninth / (c * y9 ninth)).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp (hgat.tendsto.comp hzftend)
  have hevε₂ : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < ε₂ := by
    have hlt : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), t < ε₂ :=
      IsOpen.mem_nhds isOpen_Iio (by show (0 : ℝ) < ε₂; exact hε₂pos)
    exact hlt.filter_mono nhdsWithin_le_nhds
  -- … and on the small vertical ray it equals `Real.log t`.
  have heq : (fun t : ℝ => (D (zf t) / (c * y9 (zf t))).re) =ᶠ[𝓝[>] (0 : ℝ)] Real.log := by
    filter_upwards [self_mem_nhdsWithin, hevε₂] with t ht htε
    have ht0 : 0 < t := ht
    have hsub : zf t - ninth = ((t : ℂ)) * Complex.I := by rw [hzf]; ring
    have hnorm : ‖zf t - ninth‖ = t := by
      rw [hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht0]
    have hzt_ball9δ : zf t ∈ Metric.ball ninth δ := by
      rw [Metric.mem_ball, Complex.dist_eq, hnorm]
      exact lt_of_lt_of_le htε hε₂δ
    have hzt_ball9ε₁ : zf t ∈ Metric.ball ninth ε₁ := by
      rw [Metric.mem_ball, Complex.dist_eq, hnorm]
      exact lt_of_lt_of_le htε hε₂ε₁
    have hyt : y9 (zf t) ≠ 0 := hε₁sub hzt_ball9ε₁
    have hzt_slit : zf t ∈ slitDisk δ := by
      refine ⟨hzt_ball9δ, ?_⟩
      left
      have him : (zf t).im = t := by rw [hzf]; simp [ninth]
      rw [him]; exact ne_of_gt ht0
    have hlogdiv : Complex.log (zf t - ninth) = D (zf t) / (c * y9 (zf t)) := by
      have h := hid (zf t) hzt_slit
      rw [eq_div_iff (mul_ne_zero hc hyt)]
      linear_combination h
    rw [← hlogdiv, Complex.log_re, hnorm]
  -- Hence `Real.log t` tends both to the finite value `(D 1/9 / (c · y9 1/9)).re` and to `atBot`.
  have hloglim : Tendsto (fun t : ℝ => Real.log t) (𝓝[>] (0 : ℝ))
      (𝓝 ((D ninth / (c * y9 ninth)).re)) :=
    (Filter.tendsto_congr' heq).mp hglim
  have hlatbot : Tendsto (fun t : ℝ => Real.log t) (𝓝[>] (0 : ℝ)) atBot :=
    Real.tendsto_log_nhdsGT_zero
  have hlne : NeBot (𝓝[>] (0 : ℝ)) := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioi]
    exact Set.mem_Ici.mpr le_rfl
  have hfalse : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), False := by
    have hA : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        Real.log t ≤ (D ninth / (c * y9 ninth)).re - 1 :=
      (tendsto_atBot.mp hlatbot) _
    have hB : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        (D ninth / (c * y9 ninth)).re - 1 < Real.log t :=
      hloglim.eventually (Ioi_mem_nhds (by linarith))
    filter_upwards [hA, hB] with t h1 h2
    linarith
  exact hlne.ne (eventually_false_iff_eq_bot.mp hfalse)

end Work.A14D
