import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Weyl.Levels.tendsto_slice_quotient

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Weyl.Levels

open Filter Set
open scoped Topology

/-!
# The two-sided limit of `Φ̂(w,θ,τ)/cos θ` at `θ = -π/2`

The odd extension `Φ̂` of `Φ` in the angle variable satisfies
`Φ̂(w,θ,τ) = -Φ(w,-θ,τ)` for `θ < 0`, so at `θ = -π/2` the quotient
`Φ̂(w,θ,τ)/cos θ` is, after the substitution `s = -θ`, the slice difference quotient
`-(Φ(w,s,τ) - Φ(w,π/2,τ))/(s - π/2)` (here `Φ(w,π/2,τ) = 0` by hypothesis `hπ`) times
`(s - π/2)/cos s`.  The first factor tends to `∂_θΦ(w₀,π/2,τ)` by the (proved)
mean-value-theorem lemma `tendsto_slice_quotient`, the second to `1/cos'(π/2) = -1`
(reciprocal slope of `cos` at `π/2`), and the two signs give the claimed value.
-/

/-- `(θ - π/2)/cos θ → -1` as `θ → π/2`: the reciprocal of the slope of `cos` at `π/2`. -/
theorem tendsto_sub_div_cos_at_pi_div_two_aux :
    Filter.Tendsto (fun θ : ℝ => (θ - Real.pi / 2) / Real.cos θ)
      (𝓝[≠] (Real.pi / 2)) (𝓝 (-1)) := by
  have hcos : HasDerivAt Real.cos (-Real.sin (Real.pi / 2)) (Real.pi / 2) :=
    Real.hasDerivAt_cos (Real.pi / 2)
  have hne : (-Real.sin (Real.pi / 2) : ℝ) ≠ 0 := by
    rw [Real.sin_pi_div_two]; norm_num
  have hinv := hcos.tendsto_slope.inv₀ hne
  have hval : ((-Real.sin (Real.pi / 2) : ℝ))⁻¹ = -1 := by
    rw [Real.sin_pi_div_two]; norm_num
  have hfun : (fun y : ℝ => (slope Real.cos (Real.pi / 2) y)⁻¹)
      = (fun θ : ℝ => (θ - Real.pi / 2) / Real.cos θ) := by
    funext y
    rw [slope_def_field, Real.cos_pi_div_two, sub_zero, inv_div]
  rw [hfun, hval] at hinv
  exact hinv

/-- Elementary cancellation of the two factors introduced by the change of variable. -/
private lemma neg_div_mul_div_cancel (X a c : ℝ) (ha : a ≠ 0) :
    -(X / a) * (a / c) = (-X) / c := by
  field_simp

theorem tendsto_PhiOdd_div_cos_at_neg_pi_div_two {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0)
    {w₀ : ℝ} (hw₀ : 0 < w₀) :
    Filter.Tendsto (fun p : ℝ × ℝ => Work.FTS.BSIdent.PhiOdd Φ p.1 p.2 τ / Real.cos p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ -Real.pi / 2 < p.2 ∧ p.2 < 0}] (w₀, -(Real.pi / 2)))
      (𝓝 (deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2))) := by
  set S : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 < p.1 ∧ -Real.pi / 2 < p.2 ∧ p.2 < 0} with hSdef
  set x : ℝ × ℝ := (w₀, -(Real.pi / 2)) with hxdef
  set δ : ℝ := min 1 w₀ with hδdef
  have hδpos : 0 < δ := lt_min one_pos hw₀
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδw : δ ≤ w₀ := min_le_right _ _
  -- ## The hypotheses of the slice lemma in the box `|w - w₀| < δ`, `|θ - π/2| < δ`
  have hsmbox : ∀ w θ, |w - w₀| < δ → |θ - Real.pi / 2| < δ →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ) := by
    intro w θ hw hθ
    refine hsm w θ ?_ ?_ ?_
    · have h := (abs_lt.mp hw).1; linarith
    · have h := (abs_lt.mp hθ).1; linarith [Real.pi_pos]
    · have h := (abs_lt.mp hθ).2; linarith
  have hzbox : ∀ w, |w - w₀| < δ → Φ w (Real.pi / 2) τ = 0 := by
    intro w hw
    apply hπ
    have h := (abs_lt.mp hw).1
    linarith
  have hslice := tendsto_slice_quotient (f := fun w θ => Φ w θ τ) hδpos hsmbox hzbox
  -- ## The box `|p.1 - w₀| < δ ∧ |p.2 + π/2| < δ` is a neighbourhood of `x`
  have hU : {p : ℝ × ℝ | |p.1 - w₀| < δ ∧ |p.2 + Real.pi / 2| < δ} ∈ 𝓝 x := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x hδpos) ?_
    intro p hp
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff] at hp
    simpa [hxdef] using hp
  -- ## Change of variable `(p₁,p₂) ↦ (p₁,-p₂)`
  have hu : Tendsto (fun p : ℝ × ℝ => ((p.1, -p.2) : ℝ × ℝ)) (𝓝[S] x)
      (𝓝[{q : ℝ × ℝ | |q.1 - w₀| < δ ∧ |q.2 - Real.pi / 2| < δ ∧ q.2 ≠ Real.pi / 2}]
        (w₀, Real.pi / 2)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : ContinuousAt (fun p : ℝ × ℝ => ((p.1, -p.2) : ℝ × ℝ)) x := by
        fun_prop
      have hxy : (x.1, -x.2) = (w₀, Real.pi / 2) := by simp [hxdef]
      have ht := hcont.tendsto
      rw [hxy] at ht
      exact ht.mono_left nhdsWithin_le_nhds
    · filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with p hbox hpS
      have hp2 : 0 < p.1 ∧ -Real.pi / 2 < p.2 ∧ p.2 < 0 := by simpa [hSdef] using hpS
      refine ⟨hbox.1, ?_, ?_⟩
      · have h2 : -p.2 - Real.pi / 2 = -(p.2 + Real.pi / 2) := by ring
        rw [h2, abs_neg]
        exact hbox.2
      · intro hc
        linarith [hp2.2.1]
  -- ## The slice quotient (in the variable `s = -p₂`)
  have hκ : Tendsto (fun p : ℝ × ℝ => Φ p.1 (-p.2) τ / (-p.2 - Real.pi / 2))
      (𝓝[S] x) (𝓝 (deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2))) := by
    refine (hslice.comp hu).congr' ?_
    filter_upwards with p
    simp [Function.comp_apply]
  -- ## The `cos` quotient
  have hβ : Tendsto (fun p : ℝ × ℝ => (-p.2 - Real.pi / 2) / Real.cos p.2)
      (𝓝[S] x) (𝓝 (-1)) := by
    have hneg : Tendsto (fun p : ℝ × ℝ => -p.2) (𝓝[S] x) (𝓝[≠] (Real.pi / 2)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have hcont : ContinuousAt (fun p : ℝ × ℝ => -p.2) x := by fun_prop
        have hxy : -x.2 = Real.pi / 2 := by simp [hxdef]
        have ht := hcont.tendsto
        rw [hxy] at ht
        exact ht.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with p hpS
        have hp2 : 0 < p.1 ∧ -Real.pi / 2 < p.2 ∧ p.2 < 0 := by simpa [hSdef] using hpS
        intro hc
        rw [Set.mem_singleton_iff] at hc
        linarith [hp2.2.1]
    refine ((tendsto_sub_div_cos_at_pi_div_two_aux).comp hneg).congr' ?_
    filter_upwards with p
    simp [Function.comp_apply, Real.cos_neg]
  -- ## Assembly
  have hprod : Tendsto (fun p : ℝ × ℝ =>
      -(Φ p.1 (-p.2) τ / (-p.2 - Real.pi / 2)) * ((-p.2 - Real.pi / 2) / Real.cos p.2))
      (𝓝[S] x) (𝓝 (deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2))) := by
    have h := hκ.neg.mul hβ
    have hval : -(deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2)) * -1
        = deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2) := by ring
    rwa [hval] at h
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with p hpS
  have hp2 : 0 < p.1 ∧ -Real.pi / 2 < p.2 ∧ p.2 < 0 := by simpa [hSdef] using hpS
  have hodd : Work.FTS.BSIdent.PhiOdd Φ p.1 p.2 τ = -(Φ p.1 (-p.2) τ) :=
    Work.FTS.BSIdent.PhiOdd_of_neg (by linarith [hp2.2.2])
  have ha : -p.2 - Real.pi / 2 ≠ 0 := by linarith [hp2.2.1]
  rw [hodd]
  exact neg_div_mul_div_cancel _ _ _ ha

end Work.FTS.BSIdent.Weyl.Levels
