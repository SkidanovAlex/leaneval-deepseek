import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.germ_expansion
import Submission.Work.Horn.petal_components_upper_local
import Submission.Work.Horn.exists_basin_component_in_outer

namespace Work.Horn

/-- `pushdown Ẽ_{f₀}` is holomorphic on a full disc around `0`: on the punctured disc this is
`pushdown_differentiableOn_punctured` (the principal lift of `ζ → 0` lands in the upper end where
`Ẽ` is defined and holomorphic by `ParabData.ends_sub`), and at `0` it is
`pushdown_hasDerivAt_zero` (normalisation (4.1.5)). -/
theorem pushdown_differentiableOn_ball {f₀ : ℂ → ℂ} {D₀ : Set ℂ}
    (d : MandelDim.ParabData f₀ D₀) :
    DifferentiableOn ℂ (MandelDim.pushdown d.E) (Metric.ball 0 (Real.exp (-(2 * Real.pi * d.η₀)))) := by
  intro ζ hζ
  rcases eq_or_ne ζ 0 with h0 | h0
  · subst h0
    exact ((pushdown_hasDerivAt_zero f₀ D₀ d).differentiableAt).differentiableWithinAt
  · have hs : (Metric.ball 0 (Real.exp (-(2 * Real.pi * d.η₀))) \ {0}) ∈ nhds ζ :=
      (Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hζ, h0⟩
    exact (((pushdown_differentiableOn_punctured f₀ D₀ d) ζ ⟨hζ, h0⟩).differentiableAt hs)
      |>.differentiableWithinAt

/-- **Taylor expansion of the pushed-down horn map at `0`.**  The germ `g = pushdown Ẽ_{f₀}` is
holomorphic near `0` with `g 0 = 0`, `g'(0) = 1` and `g ≠ id` near `0` (the last is
`pushdown_not_eventually_id`, i.e. the exclusion of the flat/identity germ, which rests on
Proposition 5.3's infinite-fibre statement).  Hence `g` has a first non-trivial Taylor term beyond
the linear one: `g ζ = ζ + a ζ^{q+1} + o(ζ^{q+1})` with `q ≥ 1` and `a ≠ 0`.  This is the
hypothesis `Lemma 5.4`/`Prop 5.3` of Shishikura needs in order to read off the number `q` of
petals. -/
theorem germ_expansion_pushdown {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl) :
    ∃ (q : ℕ) (a : ℂ), 1 ≤ q ∧ a ≠ 0 ∧
      Filter.Tendsto (fun z : ℂ => (MandelDim.pushdown d.E z - z - a * z ^ (q + 1)) / z ^ (q + 1))
        (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  -- the unique critical point of the given immediate basin, giving the `IsF0Setup` package
  obtain ⟨c, hsetup⟩ := isF0Setup_of_immediateBasin hF0 d hB hBne
  obtain ⟨q, hq, a, ha, ht⟩ :=
    germ_expansion (Real.exp_pos _) (pushdown_differentiableOn_ball d)
      (Work.Horn.MandelDim.pushdown_zero d.E) (Work.Horn.MandelDim.deriv_pushdown_E d)
      (pushdown_not_eventually_id d hsetup)
  exact ⟨q, a, hq, ha, ht⟩

end Work.Horn
