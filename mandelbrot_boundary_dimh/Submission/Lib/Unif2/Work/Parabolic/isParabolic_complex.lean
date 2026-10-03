import Mathlib
import Submission.Lib.Unif2.Work.Parabolic.Deps
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.harmonic_eqOn_ball_of_isMaxOn

/-!
# The complex plane is parabolic

`Work.Parabolic.isParabolic_complex : IsParabolic ℂ`, i.e. the plane carries no Green function.

## The mathematics

The naive argument ("invert at the pole and let the radius shrink") needs one genuine analytic
input, namely the *minimum principle*: a non-negative harmonic function on a disc which vanishes at
one point vanishes identically.  Accordingly the proof is:

* Suppose `E : ℂ → ℝ` is Green data at `z₀`: `E > 0` off `z₀`, harmonic off `z₀`, and every
  superlevel set `{z | ε ≤ E z}` (`ε > 0`) has compact closure.
* Invert: put `F w = E (z₀ + w⁻¹)` for `w ≠ 0`.  Since `z₀ + w⁻¹ ≠ z₀`, `F > 0` on `ℂ \ {0}`, and
  `F` is harmonic on `ℂ \ {0}` (composition of the harmonic `E` with the analytic map
  `w ↦ z₀ + w⁻¹`, away from its pole).
* Since `closure {z | ε ≤ E z}` is bounded, `F w < ε` for `0 < ‖w‖ < δ(ε)`: for such `w` one has
  `‖z₀ + w⁻¹‖ ≥ 1/‖w‖ - ‖z₀‖ > R_ε`.  Taking `ε = 1` shows that `F` is bounded near `0`, so
  `F` extends across `0` to a function `h` harmonic on a disc `ball 0 δ₁`
  (`Work.Potential.punctured_ball_harmonic_extension`).
* The extension satisfies `h 0 = 0`: `h 0 ≥ 0` because `h = F > 0` on a punctured neighbourhood of
  `0`, and `h 0 ≤ ε` for every `ε > 0` because `F < ε` on a punctured neighbourhood of `0`.
* But then `h ≥ 0` on the disc with `h 0 = 0`, so `-h` is harmonic on the disc with an interior
  maximum at `0`; the strong maximum principle
  (`Commons.Analysis.Complex.Harmonic.harmonic_eqOn_ball_of_isMaxOn`) forces `h ≡ 0` on the disc,
  contradicting `h = F > 0` off `0`.

Nothing here uses the challenge hypothesis `H¹(X,ℝ) = 0`, the chart transport, or the logarithmic
pole: parabolicity of `ℂ` is a pure potential-theoretic fact.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set

namespace Work.Parabolic

/-- On `ℂ` (where the preferred chart at every point is the identity), the manifold-level notion
`Submission.HarmonicOnX` is planar harmonicity. -/
theorem harmonicAt_of_harmonicOnX_complex {E : ℂ → ℝ} {z₀ z : ℂ}
    (h : Submission.HarmonicOnX E (Set.univ \ {z₀})) (hz : z ≠ z₀) :
    InnerProductSpace.HarmonicAt E z := by
  have h' := h z ⟨Set.mem_univ z, hz⟩
  rw [Submission.HarmonicOnXAt] at h'
  rw [chartAt_self_eq] at h'
  simpa using h'

/-- **No Green function on `ℂ`.**  A strictly positive harmonic function on `ℂ \ {z₀}` whose
superlevel sets are relatively compact cannot exist: after inversion at the pole such a function
would be a positive harmonic function on a punctured disc, bounded above near the puncture, whose
harmonic extension vanishes at the puncture — and the strong minimum principle then kills it. -/
theorem not_isGreenFunctionAt_complex (z₀ : ℂ) (E : ℂ → ℝ)
    (hpos : ∀ z : ℂ, z ≠ z₀ → 0 < E z)
    (hharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hcomp : ∀ ε : ℝ, 0 < ε → IsCompact (closure {z : ℂ | ε ≤ E z})) : False := by
  -- The inverted function.
  set F : ℂ → ℝ := fun w => E (z₀ + w⁻¹) with hFdef
  have hne_of : ∀ w : ℂ, w ≠ 0 → z₀ + w⁻¹ ≠ z₀ := by
    intro w hw h
    have h0 : w⁻¹ = 0 := by
      have h' : z₀ + w⁻¹ = z₀ + 0 := by simpa using h
      exact add_left_cancel h'
    exact inv_ne_zero hw h0
  have hFpos : ∀ w : ℂ, w ≠ 0 → 0 < F w := by
    intro w hw
    show 0 < E (z₀ + w⁻¹)
    exact hpos _ (hne_of w hw)
  have hharmE : ∀ z : ℂ, z ≠ z₀ → InnerProductSpace.HarmonicAt E z :=
    fun z hz => harmonicAt_of_harmonicOnX_complex hharm hz
  have hFharm : ∀ w : ℂ, w ≠ 0 → InnerProductSpace.HarmonicAt F w := by
    intro w hw
    have hf : AnalyticAt ℂ (fun w : ℂ => z₀ + w⁻¹) w :=
      (analyticAt_const (v := z₀)).add (analyticAt_id.inv hw)
    have h := Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic hf
      (hharmE _ (hne_of w hw))
    simpa using h
  -- `F` is small near `0`, because the superlevel sets of `E` are bounded.
  have hFsmall : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ w : ℂ, w ≠ 0 → ‖w‖ < δ → F w < ε := by
    intro ε hε
    obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).mp (hcomp ε hε).isBounded
    set R : ℝ := max R₀ 1 with hRdef
    have hR₀R : R₀ ≤ R := le_max_left _ _
    have hSpos : 0 < R + ‖z₀‖ + 1 := by
      have h1 : (1 : ℝ) ≤ R := le_max_right _ _
      have h2 : (0 : ℝ) ≤ ‖z₀‖ := norm_nonneg z₀
      linarith
    refine ⟨1 / (R + ‖z₀‖ + 1), one_div_pos.mpr hSpos, ?_⟩
    intro w hw hwlt
    have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hlt : R + ‖z₀‖ + 1 < ‖w‖⁻¹ := by
      have h := one_div_lt_one_div_of_lt hwn hwlt
      rw [one_div_one_div] at h
      rw [one_div] at h
      exact h
    have hnorm : R < ‖z₀ + w⁻¹‖ := by
      have h1 : ‖w⁻¹‖ - ‖z₀‖ ≤ ‖z₀ + w⁻¹‖ := by
        have h2 := (abs_le.mp (abs_norm_sub_norm_le w⁻¹ (-z₀))).2
        simpa [add_comm] using h2
      rw [norm_inv] at h1
      linarith
    have hnotin : z₀ + w⁻¹ ∉ closure {z : ℂ | ε ≤ E z} := by
      intro hmem
      have hmem' : z₀ + w⁻¹ ∈ Metric.ball (0 : ℂ) R :=
        Metric.ball_subset_ball hR₀R (hR₀ hmem)
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hmem'
      exact absurd hmem' (not_lt.mpr hnorm.le)
    show E (z₀ + w⁻¹) < ε
    by_contra hcon
    exact hnotin (subset_closure (by simpa using not_lt.mp hcon))
  -- Harmonic extension of `F` across the origin.
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hFsmall 1 one_pos
  obtain ⟨h, hharmh, hheq⟩ :=
    Work.Potential.punctured_ball_harmonic_extension (a := 0) (ρ := δ₁) (M := 1) hδ₁pos
      (fun z _ hz => hFharm z hz)
      (fun z hzB hz => by
        rw [abs_of_pos (hFpos z hz)]
        exact le_of_lt (hδ₁ z hz (by simpa using hzB)))
  have hOnNhd : InnerProductSpace.HarmonicOnNhd h (Metric.ball (0 : ℂ) δ₁) :=
    fun z hz => hharmh z (by simpa using hz)
  have hcontAt : ContinuousAt h 0 :=
    (InnerProductSpace.HarmonicOnNhd.continuousOn hOnNhd).continuousAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ₁pos))
  have htend : Filter.Tendsto h (𝓝[≠] (0 : ℂ)) (𝓝 (h 0)) :=
    hcontAt.tendsto.mono_left inf_le_left
  -- The value of the extension at the origin, from both sides.
  have h0_le : h 0 ≤ 0 := by
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    obtain ⟨δ, hδpos, hδ⟩ := hFsmall ε hε
    have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), h z ≤ ε := by
      have hballEv : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ Metric.ball (0 : ℂ) (min δ δ₁) :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (Metric.ball_mem_nhds (0 : ℂ) (lt_min hδpos hδ₁pos))
      filter_upwards [hballEv, self_mem_nhdsWithin] with z hzB hz
      have hz1 : ‖z - 0‖ < δ₁ := by
        have h := hzB
        rw [Metric.mem_ball, dist_eq_norm] at h
        exact lt_of_lt_of_le h (min_le_right _ _)
      have hz2 : ‖z - 0‖ < δ := by
        have h := hzB
        rw [Metric.mem_ball, dist_eq_norm] at h
        exact lt_of_lt_of_le h (min_le_left _ _)
      rw [hheq z hz1 hz]
      exact (hδ z hz (by simpa using hz2)).le
    exact le_of_tendsto htend (by simpa using hev)
  have h0_ge : 0 ≤ h 0 := by
    have hballEv : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ Metric.ball (0 : ℂ) δ₁ :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hδ₁pos)
    have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (0 : ℝ) ≤ h z := by
      filter_upwards [hballEv, self_mem_nhdsWithin] with z hzB hz
      have hz1 : ‖z - 0‖ < δ₁ := by
        have h := hzB
        rw [Metric.mem_ball, dist_eq_norm] at h
        exact h
      rw [hheq z hz1 hz]
      exact (hFpos z hz).le
    exact ge_of_tendsto htend hev
  have h0 : h 0 = 0 := le_antisymm h0_le h0_ge
  -- `-h` has an interior maximum at `0`, so `h ≡ 0` on the disc.
  have hmin : ∀ z ∈ Metric.ball (0 : ℂ) δ₁,
      (fun z : ℂ => -h z) z ≤ (fun z : ℂ => -h z) 0 := by
    intro z hz
    have hzle : 0 ≤ h z := by
      by_cases hz0 : z = 0
      · rw [hz0, h0]
      · have hz1 : ‖z - 0‖ < δ₁ := by
          have h := hz
          rw [Metric.mem_ball, dist_eq_norm] at h
          exact h
        rw [hheq z hz1 hz0]
        exact (hFpos z hz0).le
    show -h z ≤ -h 0
    rw [h0, neg_zero]
    exact neg_nonpos.mpr hzle
  have hconst :=
    Commons.Analysis.Complex.Harmonic.harmonic_eqOn_ball_of_isMaxOn hδ₁pos hOnNhd.neg hmin
  -- Evaluate at a nonzero point of the disc.
  obtain ⟨w, hwne, hwnorm⟩ : ∃ w : ℂ, w ≠ 0 ∧ ‖w - 0‖ < δ₁ := by
    refine ⟨(δ₁ / 2 : ℝ), ?_, ?_⟩
    · simp only [Complex.ofReal_eq_zero, ne_eq]
      linarith
    · rw [sub_zero]
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0 : ℝ) < δ₁ / 2)]
      linarith
  have hwball : w ∈ Metric.ball (0 : ℂ) δ₁ := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hwnorm
  have hw0 : -h w = -h 0 := by simpa using hconst w hwball
  have hwz : h w = 0 := by
    rw [h0, neg_zero] at hw0
    exact neg_eq_zero.mp hw0
  have hwF : h w = F w := hheq w hwnorm hwne
  rw [hwF] at hwz
  exact absurd hwz (ne_of_gt (hFpos w hwne))

/-- **The complex plane is parabolic**: it carries no Green function.  This is the prototype
member of the parabolic case, and it shows that `IsParabolic` is not vacuous.

Proof.  Suppose `E` is Green data at `z₀ ∈ ℂ`; thus `E > 0` on `ℂ \ {z₀}`, `E` is harmonic there,
and for every `ε > 0` the set `{z | ε ≤ E z}` is contained in a compact — hence bounded — set.
Invert: put `F w = E (z₀ + 1/w)` for `w ≠ 0`, which is harmonic on `ℂ \ {0}` (composition of the
harmonic `E` with the analytic map `w ↦ z₀ + 1/w`, away from its pole) and strictly positive.  For
`ε > 0` choose `R` with `{z | ε ≤ E z} ⊆ Metric.ball 0 R`; then for `0 < ‖w‖ < 1/(R + ‖z₀‖)` one
has `‖z₀ + 1/w‖ ≥ 1/‖w‖ - ‖z₀‖ > R`, hence `F w = E (z₀ + 1/w) < ε`.  So `F` is bounded above off
`0` and hence extends to a harmonic function `h` on a disc around `0`
(`Work.Potential.punctured_ball_harmonic_extension`).  Passing to the limit along `𝓝[≠] 0`, the two
bounds above give `h 0 = 0`; then `h ≥ 0` on the disc with `h 0 = 0`, so `-h` is harmonic with an
interior maximum at `0` and the strong maximum principle
(`Commons.Analysis.Complex.Harmonic.harmonic_eqOn_ball_of_isMaxOn`) forces `h ≡ 0` there,
contradicting `h = F > 0` at any nonzero point of the disc. -/
theorem isParabolic_complex : Work.Parabolic.IsParabolic ℂ := by
  rintro ⟨z₀, E, hpos, hharm, hcomp⟩
  exact not_isGreenFunctionAt_complex z₀ E hpos hharm hcomp

end Work.Parabolic
