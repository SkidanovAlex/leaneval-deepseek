import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.FireFix.Clauses.psiField_contDiffAt_two
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.MeridianDyn.ResidDyn
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.Physical.BiotSavart.isOdd_physVel_of_swirlShape
import Submission.Work.FTS.PressureOn.PoissonAux.kernelIntegral
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS_BSIdentP.Slim.TendstoSliceQuotient
import Submission.Work.FTS_EllLimOK.EGap.integrableOn_PhiD
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.BSIdent.Cyl.DecayAux.Wrapper =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pointwise bounds for `∂_z psiCore` and `∂_r psiCore` on the open quadrant
-/

noncomputable section

open scoped Topology

namespace Work.FTS.BSIdent.Cyl

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The bound on `∂_z ψ` on the open quadrant.** -/
theorem abs_pdZ_psiCore_le {G : ℝ → ℝ → ℝ} {p c b C₀ q lam r z : ℝ}
    (hC₀ : 0 ≤ C₀) (hq : 2 < q) (hlam : 0 < lam) (hp : 0 < p) (hb : 0 < b)
    (hr : 0 < r) (hz : 0 < z) (hpl : 3 ≤ p * lam)
    (hG : Work.Cyl.DiffAt2 G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))
    (hval : |G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z) ^ q * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam))
    (hwd : |Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z) ^ q
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam - 1))
    (hth : |Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z) ^ (q - 1)
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam)) :
    |Work.Cyl.pdZ (psiCore p c b G) r z|
      ≤ decayKzr p c C₀ q lam b / (1 + Work.Cyl.rhoP r z) := by
  rw [pdZ_psiCore_eq hG hr]
  refine abs_combination_bound (X := p * z * (Work.Cyl.rhoP r z ^ p / b)) (Y := r) (zc := z)
    hC₀ hq hlam hp hb hr hz hpl ?_ ?_ ?_ hval hwd hth
  · exact abs_snd_le_rhoP r z
  · rw [abs_mul, abs_mul, abs_of_nonneg hp.le,
      abs_of_nonneg (div_nonneg (Real.rpow_nonneg (Work.Cyl.rhoP_nonneg r z) p) hb.le)]
    have h1 : (0 : ℝ) ≤ Work.Cyl.rhoP r z ^ p / b :=
      div_nonneg (Real.rpow_nonneg (Work.Cyl.rhoP_nonneg r z) p) hb.le
    have h2 : p * |z| ≤ p * Work.Cyl.rhoP r z :=
      mul_le_mul_of_nonneg_left (abs_snd_le_rhoP r z) hp.le
    exact mul_le_mul_of_nonneg_right h2 h1
  · rw [abs_of_nonneg hr.le]; exact le_rhoP r z hr.le

/-- **The bound on `∂_r ψ` on the open quadrant.** -/
theorem abs_pdR_psiCore_le {G : ℝ → ℝ → ℝ} {p c b C₀ q lam r z : ℝ}
    (hC₀ : 0 ≤ C₀) (hq : 2 < q) (hlam : 0 < lam) (hp : 0 < p) (hb : 0 < b)
    (hr : 0 < r) (hz : 0 < z) (hpl : 3 ≤ p * lam)
    (hG : Work.Cyl.DiffAt2 G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))
    (hval : |G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z) ^ q * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam))
    (hwd : |Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z) ^ q
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam - 1))
    (hth : |Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z) ^ (q - 1)
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam)) :
    |Work.Cyl.pdR (psiCore p c b G) r z|
      ≤ decayKzr p c C₀ q lam b / (1 + Work.Cyl.rhoP r z) := by
  rw [pdR_psiCore_eq hG hr]
  refine abs_combination_bound (X := p * r * (Work.Cyl.rhoP r z ^ p / b)) (Y := -z) (zc := r)
    hC₀ hq hlam hp hb hr hz hpl ?_ ?_ ?_ hval hwd hth
  · rw [abs_of_nonneg hr.le]; exact le_rhoP r z hr.le
  · rw [abs_mul, abs_mul, abs_of_nonneg hp.le, abs_of_nonneg hr.le,
      abs_of_nonneg (div_nonneg (Real.rpow_nonneg (Work.Cyl.rhoP_nonneg r z) p) hb.le)]
    have h1 : (0 : ℝ) ≤ Work.Cyl.rhoP r z ^ p / b :=
      div_nonneg (Real.rpow_nonneg (Work.Cyl.rhoP_nonneg r z) p) hb.le
    have h2 : p * r ≤ p * Work.Cyl.rhoP r z :=
      mul_le_mul_of_nonneg_left (le_rhoP r z hr.le) hp.le
    exact mul_le_mul_of_nonneg_right h2 h1
  · rw [abs_neg]; exact abs_snd_le_rhoP r z

end Work.FTS.BSIdent.Cyl
end
end
-- ===== merged: Submission.Work.FTS.BSIdent.Weyl.Levels.abs_div_psiCore_le_one =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Weyl.Levels

theorem abs_div_psiCore_le_one {G : ℝ → ℝ → ℝ} {p c b C₀ lam r z : ℝ}
    (hC₀ : 0 ≤ C₀) (hlam : 0 < lam) (hp : 0 < p) (hb : 0 < b)
    (hr : 0 < r) (hz : 0 < z) (hpl : 2 ≤ p * lam)
    (hval : |G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z)
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam)) :
    |Work.FTS.BSIdent.Cyl.psiCore p c b G r z / r|
      ≤ Work.FTS.BSIdent.Weyl.Levels.decayKqOne c C₀ lam b / (1 + Work.Cyl.rhoP r z) := by
  -- Unfold the core `ψ = ρ² c G(w, θ)` and abbreviate the four recurring quantities.
  simp only [Work.FTS.BSIdent.Cyl.psiCore]
  set ρ := Work.Cyl.rhoP r z with hρ
  set θ := Work.Cyl.thetaP r z with hθ
  set w := ρ ^ p / b with hw
  set R := (1 + w) ^ (-lam) with hR
  have hρpos : 0 < ρ := by rw [hρ]; exact Work.Cyl.rhoP_pos hr z
  have hρnn : 0 ≤ ρ := hρpos.le
  have hθpos : 0 < θ := by rw [hθ]; exact Work.FTS.BSIdent.Cyl.thetaP_pos_of_pos hr hz
  have hwpos : 0 < w := by rw [hw]; exact div_pos (Real.rpow_pos_of_pos hρpos p) hb
  have hRnn : 0 ≤ R := by
    rw [hR]; exact (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < 1 + w) _).le
  -- `cos θ = r/ρ` is the sharp form of the distance of `θ` to `π/2`.
  have hcos : Real.cos θ = r / ρ := by rw [hθ, hρ]; exact Work.Cyl.cos_thetaP hr z
  -- The rate hypothesis, in the abbreviations.
  have hG : |G w θ| ≤ C₀ * (Real.pi / 2 - θ) * R := hval
  -- Jordan's inequality turns the profile rate `(π/2 - θ)` into `(π/2) cos θ = (π/2) r/ρ`.
  have hSle : Real.pi / 2 - θ ≤ Real.pi / 2 * Real.cos θ := by
    have hθabs : |θ| ≤ Real.pi / 2 :=
      le_of_lt (by rw [hθ]; exact Work.FTS.BSIdent.Cyl.abs_thetaP_lt r z)
    have h := Work.FTS.BSIdent.Cyl.DecayAux.pi_div_two_sub_abs_le_cos hθabs
    rw [abs_of_nonneg hθpos.le] at h
    exact h
  -- … so that `ρ² (π/2 - θ)/r ≤ (π/2) ρ`.
  have hSbound : ρ ^ 2 * (Real.pi / 2 - θ) / r ≤ Real.pi / 2 * ρ := by
    have h1 : ρ ^ 2 * (Real.pi / 2 - θ) ≤ ρ ^ 2 * (Real.pi / 2 * Real.cos θ) :=
      mul_le_mul_of_nonneg_left hSle (sq_nonneg ρ)
    have h2 : ρ ^ 2 * (Real.pi / 2 * Real.cos θ) = Real.pi / 2 * ρ * r := by
      rw [hcos]; field_simp
    rw [h2] at h1
    rw [div_le_iff₀ hr]
    exact h1
  have step1 : |ρ ^ 2 * c * G w θ / r|
      ≤ |c| * C₀ * (ρ ^ 2 * (Real.pi / 2 - θ) / r) * R := by
    have h1 : (0 : ℝ) ≤ ρ ^ 2 * |c| := mul_nonneg (sq_nonneg ρ) (abs_nonneg c)
    have h2 : ρ ^ 2 * |c| * |G w θ| / r
        ≤ ρ ^ 2 * |c| * (C₀ * (Real.pi / 2 - θ) * R) / r :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hG h1) hr.le
    calc |ρ ^ 2 * c * G w θ / r|
        = ρ ^ 2 * |c| * |G w θ| / r := by
          rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ρ), abs_of_nonneg hr.le]
      _ ≤ ρ ^ 2 * |c| * (C₀ * (Real.pi / 2 - θ) * R) / r := h2
      _ = |c| * C₀ * (ρ ^ 2 * (Real.pi / 2 - θ) / r) * R := by ring
  have step2 : |c| * C₀ * (ρ ^ 2 * (Real.pi / 2 - θ) / r) * R
      ≤ |c| * C₀ * (Real.pi / 2) * ρ * R := by
    have h4 : (0 : ℝ) ≤ |c| * C₀ * R :=
      mul_nonneg (mul_nonneg (abs_nonneg c) hC₀) hRnn
    have h5 := mul_le_mul_of_nonneg_left hSbound h4
    calc |c| * C₀ * (ρ ^ 2 * (Real.pi / 2 - θ) / r) * R
        = (|c| * C₀ * R) * (ρ ^ 2 * (Real.pi / 2 - θ) / r) := by ring
      _ ≤ (|c| * C₀ * R) * (Real.pi / 2 * ρ) := h5
      _ = |c| * C₀ * (Real.pi / 2) * ρ * R := by ring
  have step3 : |c| * C₀ * (Real.pi / 2) * ρ * R
      ≤ decayKqOne c C₀ lam b / (1 + ρ) := by
    have hρR : ρ * R ≤ 2 * max 1 (b ^ lam) / (1 + ρ) := by
      have h := rho_mul_rpow_weight_le_two hp hlam hb hρnn hpl
      rw [← hw, ← hR] at h
      exact h
    have h4 : (0 : ℝ) ≤ |c| * C₀ * (Real.pi / 2) :=
      mul_nonneg (mul_nonneg (abs_nonneg c) hC₀) (by linarith [Real.pi_pos])
    calc |c| * C₀ * (Real.pi / 2) * ρ * R
        = (|c| * C₀ * (Real.pi / 2)) * (ρ * R) := by ring
      _ ≤ (|c| * C₀ * (Real.pi / 2)) * (2 * max 1 (b ^ lam) / (1 + ρ)) :=
          mul_le_mul_of_nonneg_left hρR h4
      _ = decayKqOne c C₀ lam b / (1 + ρ) := by rw [decayKqOne]; ring
  calc |ρ ^ 2 * c * G w θ / r|
      ≤ |c| * C₀ * (ρ ^ 2 * (Real.pi / 2 - θ) / r) * R := step1
    _ ≤ |c| * C₀ * (Real.pi / 2) * ρ * R := step2
    _ ≤ decayKqOne c C₀ lam b / (1 + ρ) := step3

end Work.FTS.BSIdent.Weyl.Levels
end
-- ===== merged: Submission.Work.FTS.BSIdent.Weyl.Levels.tendsto_PhiOdd_div_cos_at_neg_pi_div_two =====
section

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
end
-- ===== merged: Submission.Work.FTS.BSIdent.Weyl.Levels.tendsto_PhiOdd_div_cos_at_pi_div_two =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Weyl.Levels

open Filter Set
open scoped Topology

/-!
# The boundary value `Φ̂/cos` at `θ = π/2`

Near `θ = π/2` the stream function `Φ` vanishes (`Φ w (π/2) τ = 0`), so the quotient
`Φ̂(w,θ,τ)/cos θ` has a finite limit there, namely `-∂_θ Φ(w₀,π/2,τ)`: indeed, writing
`θ = π/2 - δ` with `δ → 0⁺`, `cos θ = sin δ` and `Φ(w,θ) = -δ ∂_θΦ(w,π/2) + o(δ)`.

The proof is the product rule for limits applied to the two factors
`Φ(w,θ)/(θ - π/2) → ∂_θΦ(w₀,π/2)` (the slice difference quotient, `tendsto_slice_quotient`)
and `(θ - π/2)/cos θ → 1/∂_θ(cos)(π/2) = -1`, combined with `Φ̂ = Φ` on the sector
`{p.2 > 0}`.
-/

/-- Near `(w₀, π/2)`, the sector `{0 < p.1 ∧ 0 < p.2 ∧ p.2 < π/2}` is contained in the box
`{|p.1 - w₀| < δ} ∩ {|p.2 - π/2| < δ}` (and there `p.2 ≠ π/2`).  This is the filter transfer
that lets the slice-quotient lemmas be applied on the sector. -/
private lemma sector_le_box (w₀ δ : ℝ) (hδ : 0 < δ) :
    𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2) ≤
      𝓝[{p : ℝ × ℝ | |p.1 - w₀| < δ ∧ |p.2 - Real.pi / 2| < δ ∧ p.2 ≠ Real.pi / 2}]
        (w₀, Real.pi / 2) := by
  set T : Set (ℝ × ℝ) := {p | |p.1 - w₀| < δ ∧ |p.2 - Real.pi / 2| < δ} with hT
  have hTmem : T ∈ 𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}]
      (w₀, Real.pi / 2) :=
    nhdsWithin_le_nhds (Filter.mem_of_superset (Metric.ball_mem_nhds (w₀, Real.pi / 2) hδ)
      (by
        intro p hp
        rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff] at hp
        exact hp))
  calc 𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2)
      = 𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2} ∩ T] (w₀, Real.pi / 2) :=
        (nhdsWithin_inter_of_mem' hTmem).symm
    _ ≤ 𝓝[{p : ℝ × ℝ | |p.1 - w₀| < δ ∧ |p.2 - Real.pi / 2| < δ ∧ p.2 ≠ Real.pi / 2}]
          (w₀, Real.pi / 2) :=
        nhdsWithin_mono _ fun p hp => ⟨hp.2.1, hp.2.2, ne_of_lt hp.1.2.2⟩

theorem tendsto_PhiOdd_div_cos_at_pi_div_two {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0)
    {w₀ : ℝ} (hw₀ : 0 < w₀) :
    Filter.Tendsto (fun p : ℝ × ℝ => Work.FTS.BSIdent.PhiOdd Φ p.1 p.2 τ / Real.cos p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
      (𝓝 (-(deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2)))) := by
  -- a positive radius, small enough that the box stays in `w > -1` and in `w > 0`
  obtain ⟨δ, hδpos, hδ1, hδw⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ ≤ w₀ :=
    ⟨min 1 w₀, lt_min one_pos hw₀, min_le_left _ _, min_le_right _ _⟩
  -- the `C²` hypothesis and the vanishing, on the box of half-width `δ`
  have hsm' : ∀ w θ : ℝ, |w - w₀| < δ → |θ - Real.pi / 2| < δ →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ) := by
    intro w θ hw hθ
    rw [abs_lt] at hw hθ
    exact hsm w θ (by linarith [hw.1, hδw])
      (by linarith [hθ.1, hδ1, Real.pi_pos]) (by linarith [hθ.2, hδ1])
  have hz' : ∀ w : ℝ, |w - w₀| < δ → Φ w (Real.pi / 2) τ = 0 := by
    intro w hw
    rw [abs_lt] at hw
    exact hπ w (by linarith [hw.1, hδw])
  -- (1) the `θ`-difference quotient of `Φ` tends to `∂_θΦ (w₀, π/2)`
  have hslope : Filter.Tendsto (fun p : ℝ × ℝ => Φ p.1 p.2 τ / (p.2 - Real.pi / 2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
      (𝓝 (deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2))) :=
    (tendsto_slice_quotient (f := fun w θ : ℝ => Φ w θ τ) (w₀ := w₀) (θ₀ := Real.pi / 2)
      (δ := δ) hδpos hsm' hz').mono_left (sector_le_box w₀ δ hδpos)
  -- (2) the quotient `(θ - π/2) / cos θ` tends to `-1`
  have hcosq : Filter.Tendsto (fun p : ℝ × ℝ => (p.2 - Real.pi / 2) / Real.cos p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
      (𝓝 (-1)) := by
    have hsmc : ∀ w θ : ℝ, |w - w₀| < Real.pi / 2 + 1 → |θ - Real.pi / 2| < Real.pi / 2 + 1 →
        ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Real.cos p.2) (w, θ) :=
      fun _ _ _ _ => ContDiffAt.cos contDiffAt_snd
    have hzc : ∀ w : ℝ, |w - w₀| < Real.pi / 2 + 1 → Real.cos (Real.pi / 2) = 0 :=
      fun _ _ => Real.cos_pi_div_two
    have h1 : Filter.Tendsto (fun p : ℝ × ℝ => Real.cos p.2 / (p.2 - Real.pi / 2))
        (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
        (𝓝 (-1)) := by
      have h0 := (tendsto_slice_quotient (f := fun _ θ : ℝ => Real.cos θ) (w₀ := w₀)
        (θ₀ := Real.pi / 2) (δ := Real.pi / 2 + 1) (by linarith [Real.pi_pos]) hsmc
        hzc).mono_left (sector_le_box w₀ (Real.pi / 2 + 1) (by linarith [Real.pi_pos]))
      simpa [Real.deriv_cos, Real.sin_pi_div_two] using h0
    have h2 : Filter.Tendsto (fun p : ℝ × ℝ => (Real.cos p.2 / (p.2 - Real.pi / 2))⁻¹)
        (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
        (𝓝 (-1)) := by
      have h0 := h1.inv₀ (by norm_num : (-1 : ℝ) ≠ 0)
      simpa using h0
    exact h2.congr' (Eventually.of_forall fun p => inv_div _ _)
  -- (3) the product is the quotient of the statement
  have hprod : Filter.Tendsto
      (fun p : ℝ × ℝ =>
        (Φ p.1 p.2 τ / (p.2 - Real.pi / 2)) * ((p.2 - Real.pi / 2) / Real.cos p.2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
      (𝓝 (deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2) * (-1))) :=
    hslope.mul hcosq
  have key : Filter.Tendsto
      (fun p : ℝ × ℝ => Work.FTS.BSIdent.PhiOdd Φ p.1 p.2 τ / Real.cos p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
      (𝓝 (deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2) * (-1))) :=
    hprod.congr' (by
      filter_upwards [self_mem_nhdsWithin] with p hp
      rw [Work.FTS.BSIdent.PhiOdd_of_nonneg (Φ := Φ) (z := p.1) (θ := p.2) (τ := τ)
        (le_of_lt hp.2.1)]
      have h1 : p.2 - Real.pi / 2 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hp.2.2)
      have h2 : Real.cos p.2 ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hp.2.2⟩)
      have h3 : p.2 * 2 - Real.pi ≠ 0 := fun hcon => h1 (by linarith)
      field_simp)
  simpa [mul_neg, mul_one] using key

end Work.FTS.BSIdent.Weyl.Levels
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.PhysVortAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter Topology
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix.Clauses

/-- `ℝ³`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- **If the Fréchet derivative of `F` is bounded almost everywhere by a locally integrable
function, then `x ↦ fderiv ℝ F x` is locally integrable.**  (Measurability of `fderiv` is free:
`measurable_fderiv`.) -/
theorem locallyIntegrable_fderiv_of_ae_bound {F : R3 → R3} {Ψ : R3 → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrable Ψ MeasureTheory.volume)
    (hbd : ∀ᵐ x ∂MeasureTheory.volume, ‖fderiv ℝ F x‖ ≤ Ψ x) :
    MeasureTheory.LocallyIntegrable (fun x : R3 => fderiv ℝ F x) MeasureTheory.volume := by
  rw [MeasureTheory.locallyIntegrable_iff]
  intro K hK
  refine MeasureTheory.Integrable.mono' (hΨ.integrableOn_isCompact hK) ?_ ?_
  · exact (measurable_fderiv ℝ F).aestronglyMeasurable.restrict
  · filter_upwards [MeasureTheory.ae_restrict_of_ae hbd] with x hx using hx

/-- The coordinate hyperplane `{x | x i = 0}` in `ℝ³` is null. -/
theorem volume_coord_eq_zero (i : Fin 3) : MeasureTheory.volume {x : R3 | x i = 0} = 0 := by
  have hker : {x : R3 | x i = 0}
      = ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i : R3 →L[ℝ] ℝ) : R3 →ₗ[ℝ] ℝ).ker := by
    ext x
    simp [LinearMap.mem_ker]
  rw [hker]
  refine Measure.addHaar_submodule MeasureTheory.volume _ (fun htop => ?_)
  have hzero : ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i : R3 →L[ℝ] ℝ) : R3 →ₗ[ℝ] ℝ) = 0 :=
    LinearMap.ker_eq_top.mp htop
  have h1 := congrArg (fun (L : R3 →ₗ[ℝ] ℝ) => L (FiniteTimeSingularity.e i)) hzero
  simp only [LinearMap.zero_apply] at h1
  have hproj :
      (((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i : R3 →L[ℝ] ℝ) : R3 →ₗ[ℝ] ℝ)
        (FiniteTimeSingularity.e i)) = 1 := by
    simp [EuclideanSpace.proj, FiniteTimeSingularity.e]
  rw [hproj] at h1
  exact one_ne_zero h1

/-- The axis `{x : ℝ³ | r(x) = 0}` is null. -/
theorem volume_radial_eq_zero : MeasureTheory.volume {x : R3 | Work.Cyl.radial x = 0} = 0 := by
  have hsub : {x : R3 | Work.Cyl.radial x = 0} ⊆ {x : R3 | x 0 = 0} ∪ {x : R3 | x 1 = 0} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [Work.Cyl.radial_eq_zero_iff] at hx
    exact Or.inl hx.1
  exact measure_mono_null hsub
    (measure_union_null (volume_coord_eq_zero 0) (volume_coord_eq_zero 1))

/-- The equatorial plane `{x : ℝ³ | x₃ = 0}` is null. -/
theorem volume_axial_eq_zero : MeasureTheory.volume {x : R3 | Work.Cyl.axial x = 0} = 0 := by
  have hsub : {x : R3 | Work.Cyl.axial x = 0} ⊆ {x : R3 | x 2 = 0} := by
    intro x hx
    simpa [Work.Cyl.axial] using hx
  exact measure_mono_null hsub (volume_coord_eq_zero 2)

/-! ## 3. The local section of `x ↦ (ρ(x)^{3α}/B, θ(x))`

For `x` off the axis, the point

  `sect x (z,θ) = (Bz)^{1/(3α)} • (cos θ • e_R(x) + sin θ • e_z)`

lies in the meridian half-plane spanned by `e_R(x)` and `e_z` and has self-similar variable `z` and
angle `θ`; it provides the local right inverse needed to transfer the differentiability of a
composite `x ↦ P (ρ(x)^{3α}/B) (θ(x))` back to the two-variable function `P`. -/

/-- The local section of `(ρ,θ)` through `x` (in the meridian half-plane of `x`). -/
noncomputable def sect (α B : ℝ) (x : R3) (p : ℝ × ℝ) : R3 :=
  (B * p.1) ^ (1 / (3 * α)) • (Real.cos p.2 • Work.Cyl.eR x + Real.sin p.2 • Work.Cyl.eZ)

lemma sect_diff {α B : ℝ} (hα : 0 < α) (hB : 0 < B) (x : R3) {z θ : ℝ}
    (hz : 0 < z) : DifferentiableAt ℝ (sect α B x) (z, θ) := by
  have hBz : B * z ≠ 0 := by positivity
  have h1 : DifferentiableAt ℝ (fun p : ℝ × ℝ => (B * p.1) ^ (1 / (3 * α))) (z, θ) := by
    have h2 : DifferentiableAt ℝ (fun p : ℝ × ℝ => B * p.1) (z, θ) := by fun_prop
    exact h2.rpow_const (Or.inl hBz)
  have h3 : DifferentiableAt ℝ (fun p : ℝ × ℝ =>
      Real.cos p.2 • Work.Cyl.eR x + Real.sin p.2 • Work.Cyl.eZ) (z, θ) := by fun_prop
  exact h1.smul h3

lemma sect_rho {α B : ℝ} (hα : 0 < α) (hB : 0 < B) (x : R3)
    (hr : 0 < Work.Cyl.radial x) {z θ : ℝ} (hz : 0 < z) (hθ : |θ| < Real.pi / 2) :
    Work.Cyl.rho (sect α B x (z, θ)) = (B * z) ^ (1 / (3 * α)) :=
  (rho_theta_sect x hr (Real.rpow_pos_of_pos (by positivity) _) hθ).1

lemma sect_theta {α B : ℝ} (hα : 0 < α) (hB : 0 < B) (x : R3)
    (hr : 0 < Work.Cyl.radial x) {z θ : ℝ} (hz : 0 < z) (hθ : |θ| < Real.pi / 2) :
    Work.Cyl.theta (sect α B x (z, θ)) = θ :=
  (rho_theta_sect x hr (Real.rpow_pos_of_pos (by positivity) _) hθ).2

/-- `ρ(x) = ρP(r(x), x₃)`. -/
lemma rho_eq_rhoP (x : R3) :
    Work.Cyl.rho x = Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) := by
  rw [Work.Cyl.rhoP, Work.Cyl.rho]
  congr 1
  rw [← Work.Cyl.radial_sq]

/-- `cos θ(x) = r(x)/ρ(x)` off the axis. -/
lemma cos_theta_eq (x : R3) (hr : 0 < Work.Cyl.radial x) :
    Real.cos (Work.Cyl.theta x) = Work.Cyl.radial x / Work.Cyl.rho x := by
  have hθ : Work.Cyl.theta x = Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x) := rfl
  rw [hθ, Work.Cyl.cos_thetaP hr (Work.Cyl.axial x), rho_eq_rhoP x]

/-- `sin θ(x) = x₃/ρ(x)` off the axis. -/
lemma sin_theta_eq (x : R3) (hr : 0 < Work.Cyl.radial x) :
    Real.sin (Work.Cyl.theta x) = Work.Cyl.axial x / Work.Cyl.rho x := by
  have hθ : Work.Cyl.theta x = Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x) := rfl
  rw [hθ, Work.Cyl.sin_thetaP hr (Work.Cyl.axial x), rho_eq_rhoP x]

/-- The section through `x` is a right inverse at `x` itself. -/
lemma sect_self {α B : ℝ} (hα : 0 < α) (hB : 0 < B) (x : R3)
    (hr : 0 < Work.Cyl.radial x) :
    sect α B x (Work.Cyl.rho x ^ (3 * α) / B, Work.Cyl.theta x) = x := by
  have hr0 : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
  have h1 : (B * (Work.Cyl.rho x ^ (3 * α) / B)) ^ (1 / (3 * α)) = Work.Cyl.rho x := by
    rw [mul_div_cancel₀ _ (ne_of_gt hB), ← Real.rpow_mul (Work.Cyl.rho_nonneg x)]
    have hexp : (3 * α) * (1 / (3 * α)) = 1 := by field_simp
    rw [hexp, Real.rpow_one]
  have h2 : Work.Cyl.radial x • Work.Cyl.eR x = Work.Cyl.radialVec x := by
    rw [Work.Cyl.eR, smul_smul, mul_one_div, div_self hr0, one_smul]
  have h3 : Work.Cyl.radialVec x + Work.Cyl.axial x • Work.Cyl.eZ = x := by
    refine Work.Cyl.ext_coord ?_ ?_ ?_ <;>
      simp [Work.Cyl.radialVec, Work.Cyl.eZ, Work.Cyl.axial, FiniteTimeSingularity.e]
  have hρpos : 0 < Work.Cyl.rho x := lt_of_lt_of_le hr (Work.Cyl.radial_le_rho x)
  have hρne : Work.Cyl.rho x ≠ 0 := ne_of_gt hρpos
  have h4 : Work.Cyl.rho x * (Work.Cyl.radial x / Work.Cyl.rho x) = Work.Cyl.radial x := by
    rw [mul_comm, div_mul_cancel₀ _ hρne]
  have h5 : Work.Cyl.rho x * (Work.Cyl.axial x / Work.Cyl.rho x) = Work.Cyl.axial x := by
    rw [mul_comm, div_mul_cancel₀ _ hρne]
  rw [sect, h1, cos_theta_eq x hr, sin_theta_eq x hr, smul_add, smul_smul, smul_smul, h4, h5, h2]
  exact h3

/-- **Differentiability of a two-variable function from that of its composition with
`x ↦ (ρ(x)^{3α}/B, θ(x))`.**  Since the latter has the local section `sect x` (through `x`), the
composition is differentiable at `x` exactly when the two-variable function is differentiable at
the image point. -/
lemma diffAt2_of_comp_sect {α B : ℝ} {P : ℝ → ℝ → ℝ} (hα : 0 < α) (hB : 0 < B)
    (x : R3) (hr : 0 < Work.Cyl.radial x)
    (hG : DifferentiableAt ℝ (fun y : R3 => P (Work.Cyl.rho y ^ (3 * α) / B) (Work.Cyl.theta y))
      x) :
    Work.Cyl.DiffAt2 P (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x) := by
  set z₀ : ℝ := Work.Cyl.rho x ^ (3 * α) / B with hz₀
  set θ₀ : ℝ := Work.Cyl.theta x with hθ₀
  have hρpos : 0 < Work.Cyl.rho x := lt_of_lt_of_le hr (Work.Cyl.radial_le_rho x)
  have hz0pos : 0 < z₀ := by
    rw [hz₀]
    exact div_pos (Real.rpow_pos_of_pos hρpos _) hB
  have hθ₀mem : |θ₀| < Real.pi / 2 := by
    rw [hθ₀, Work.Cyl.theta]
    exact abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  have hsect : DifferentiableAt ℝ (sect α B x) (z₀, θ₀) := sect_diff hα hB x hz0pos
  have hsectx : sect α B x (z₀, θ₀) = x := by rw [hz₀, hθ₀]; exact sect_self hα hB x hr
  have hGs : DifferentiableAt ℝ
      (fun y : R3 => P (Work.Cyl.rho y ^ (3 * α) / B) (Work.Cyl.theta y)) (sect α B x (z₀, θ₀)) := by
    rw [hsectx]; exact hG
  have hcomp : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => (fun y : R3 => P (Work.Cyl.rho y ^ (3 * α) / B) (Work.Cyl.theta y))
        (sect α B x p)) (z₀, θ₀) :=
    hGs.comp (z₀, θ₀) hsect
  refine hcomp.congr_of_eventuallyEq ?_
  have hnb : {p : ℝ × ℝ | 0 < p.1 ∧ |p.2| < Real.pi / 2} ∈ 𝓝 (z₀, θ₀) := by
    refine IsOpen.mem_nhds ?_ ⟨hz0pos, hθ₀mem⟩
    exact (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)
  filter_upwards [hnb] with p hp
  obtain ⟨hpz, hpθ⟩ := hp
  show P p.1 p.2 = P (Work.Cyl.rho (sect α B x p) ^ (3 * α) / B)
    (Work.Cyl.theta (sect α B x p))
  rw [sect_rho hα hB x hr hpz hpθ, sect_theta hα hB x hr hpz hpθ]
  congr 1
  rw [← Real.rpow_mul (show (0 : ℝ) ≤ B * p.1 by positivity)]
  have hexp : (1 / (3 * α)) * (3 * α) = 1 := by field_simp
  rw [hexp, Real.rpow_one]
  field_simp

/-! ## 4. The pointwise majorant of the vorticity's derivative

`psiBound α A B g τ N Npz L z θ` is the function of the self-similar variables `(z,θ)` that
dominates the Fréchet derivative of the vorticity slice `physVort α A B g · τ` at every point with
self-similar variable `z` and angle `θ`, for a profile whose perturbation is bounded by `N` with
`z`-derivative bounded by `Npz` and supported in `z ≤ L`.  It is a sum of the three elementary
pieces of the bound

  `‖∂_x ω‖ ≤ |A(τ)⁻¹| · ( M_F · 2/r + 2·(∂_ρ F̃ + ∂_θ F̃ / ρ) )`,

with `F̃(ρ,θ) = F(ρ^{3α}/B, θ)`, `M_F = 20·3α + N`, `ρ = (Bz)^{1/(3α)}` and `r = ρ cos θ`. -/
noncomputable def psiBound (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ)
    (τ N Npz L : ℝ) (z θ : ℝ) : ℝ :=
  if z ≤ L then
    |(A τ)⁻¹| * ((20 * (3 * α) + N) * (2 / ((B τ * z) ^ (1 / (3 * α)) * Real.cos θ))
      + 2 * (((3 * α) / (B τ)) * (B τ * z) ^ ((3 * α - 1) / (3 * α)) * (60 * α + Npz)
        + (200 * α ^ 2 * (Real.sin (abs θ)) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1)
            + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z (abs θ)|)
          / (B τ * z) ^ (1 / (3 * α))))
  else 0

lemma psiBound_nonneg (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ N Npz L z θ : ℝ)
    {Bpos : 0 < B τ} (hN : 0 ≤ N) (hNpz : 0 ≤ Npz) (hα : 0 < α) (hz : 0 ≤ z)
    (hθ : |θ| ≤ Real.pi / 2) :
    0 ≤ psiBound α A B g τ N Npz L z θ := by
  have hρ : 0 ≤ (B τ * z) ^ (1 / (3 * α)) := Real.rpow_nonneg (by positivity) _
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨(abs_le.mp hθ).1, (abs_le.mp hθ).2⟩
  have hsin : 0 ≤ Real.sin (abs θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith [hθ, Real.pi_pos])
  have hAθ : 0 ≤ 200 * α ^ 2 * (Real.sin (abs θ)) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg α))
      (Real.rpow_nonneg hsin _)) (Real.rpow_nonneg hcos _)
  have hX : 0 ≤ (20 * (3 * α) + N) * (2 / ((B τ * z) ^ (1 / (3 * α)) * Real.cos θ)) :=
    mul_nonneg (by linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 20) hα.le])
      (div_nonneg (by norm_num) (mul_nonneg hρ hcos))
  have hY : 0 ≤ ((3 * α) / (B τ)) * (B τ * z) ^ ((3 * α - 1) / (3 * α)) * (60 * α + Npz) :=
    mul_nonneg (mul_nonneg (div_nonneg (by linarith [hα.le]) Bpos.le)
      (Real.rpow_nonneg (by positivity) _)) (by linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 60) hα.le])
  have hZ : 0 ≤ (200 * α ^ 2 * (Real.sin (abs θ)) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1)
      + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z (abs θ)|)
      / (B τ * z) ^ (1 / (3 * α)) :=
    div_nonneg (by linarith [hAθ, abs_nonneg (Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z (abs θ))]) hρ
  unfold psiBound
  split_ifs with h
  · exact mul_nonneg (abs_nonneg _) (by linarith)
  · exact le_refl 0

/-- **The `z`-derivative of the profile is bounded** by `60α + Npz`. -/
lemma abs_pz_profile_le {α S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {Npz : ℝ}
    {g : ℝ → ℝ → ℝ → ℝ} (hNpz : ∀ z θ τ', 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ' ∈ Set.Icc 0 S →
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ') z θ| ≤ Npz)
    (hcont : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1
      (fun q : ℝ × ℝ => g q.1 θ q.2) (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |deriv (fun z' => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z' θ) z| ≤ 60 * α + Npz := by
  have hθ0 : 0 ≤ θ := hθ.1
  have hfun : (fun z' => Work.ConstructionInstance.profile (3 * α)
      (Work.FTS.Regularity.gSlice g τ) z' θ)
      = fun z' => Work.Construction.Fstar (3 * α) z' θ + g z' θ τ := by
    funext z'
    exact Work.ConstructionInstance.profile_of_nonneg hθ0
  rw [hfun]
  have hdiffFM : DifferentiableAt ℝ (fun z' : ℝ => Work.FM.Fstar z') z := by
    have hnum : DifferentiableAt ℝ (fun z' : ℝ => 2 * z') z := by fun_prop
    have hden : DifferentiableAt ℝ (fun z' : ℝ => (1 + z') ^ 2) z := by fun_prop
    have hne : (1 + z) ^ 2 ≠ 0 := by
      have h1 : (1 : ℝ) + z ≠ 0 := by positivity
      exact pow_ne_zero 2 h1
    have h := hnum.div hden hne
    have hfun : (fun z' : ℝ => Work.FM.Fstar z')
        = (fun z' => 2 * z') * (fun z' => (1 + z') ^ 2)⁻¹ := by
      funext z'; simp [Work.FM.Fstar, div_eq_mul_inv]
    rwa [hfun]
  have hdiff1 : DifferentiableAt ℝ (fun z' => Work.Construction.Fstar (3 * α) z' θ) z := by
    have hconst : (fun z' : ℝ => Work.Construction.Fstar (3 * α) z' θ)
        = fun z' => (3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α))
            * Work.FM.Fstar z' := rfl
    rw [hconst]
    exact hdiffFM.const_mul _
  have hdiff2 : DifferentiableAt ℝ (fun z' => g z' θ τ) z := by
    have hmem : (z, τ) ∈ Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (S + 1) := by
      refine ⟨?_, ?_⟩
      · show (-1 : ℝ) < z; linarith
      · show τ ∈ Set.Ioo (-1 : ℝ) (S + 1)
        exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hopen : Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (S + 1) ∈ 𝓝 (z, τ) :=
      (isOpen_Ioi.prod isOpen_Ioo).mem_nhds hmem
    have hd := (hcont θ hθ).differentiableOn (one_ne_zero)
    have hd' : DifferentiableAt ℝ (fun q : ℝ × ℝ => g q.1 θ q.2) (z, τ) :=
      hd.differentiableAt hopen
    exact hd'.comp z (by fun_prop : DifferentiableAt ℝ (fun z' : ℝ => (z', τ)) z)
  have hsum : (fun z' => Work.Construction.Fstar (3 * α) z' θ + g z' θ τ)
      = (fun z' => Work.Construction.Fstar (3 * α) z' θ) + (fun z' => g z' θ τ) := rfl
  rw [hsum, deriv_add hdiff1 hdiff2]
  have h1 := (Work.FTS.FireFix.Clauses.Fstar_bounds hα hα13).2.1 z θ hz hθ
  have h2 : |deriv (fun z' => g z' θ τ) z| ≤ Npz := by
    have heq : deriv (fun z' => g z' θ τ) z = Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ := rfl
    rw [heq]
    exact hNpz z θ τ hz hθ hτ
  calc |deriv (fun z' => Work.Construction.Fstar (3 * α) z' θ) z + deriv (fun z' => g z' θ τ) z|
      ≤ |deriv (fun z' => Work.Construction.Fstar (3 * α) z' θ) z|
        + |deriv (fun z' => g z' θ τ) z| := abs_add_le _ _
    _ ≤ 60 * α + Npz := by linarith


/-! ## 5. The positive branch of the profile and its angular derivative bound -/

/-- The positive branch `F_* + g` of the profile (which is the profile itself for `θ ≥ 0`). -/
noncomputable def Ppos (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ z θ : ℝ) : ℝ :=
  Work.Construction.Fstar (3 * α) z θ + g z θ τ

lemma profile_eq_Ppos {α : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {τ z θ : ℝ} (hθ : 0 ≤ θ) :
    Work.ConstructionInstance.profile (3 * α) (Work.FTS.Regularity.gSlice g τ) z θ
      = Ppos α g τ z θ :=
  Work.ConstructionInstance.profile_of_nonneg hθ

lemma profile_eq_neg_Ppos {α : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {τ z θ : ℝ} (hθ : ¬ 0 ≤ θ) :
    Work.ConstructionInstance.profile (3 * α) (Work.FTS.Regularity.gSlice g τ) z θ
      = - Ppos α g τ z (-θ) :=
  Work.ConstructionInstance.profile_of_neg hθ

/-- Differentiability of `θ' ↦ F_*(z,θ')` on the open angular interval. -/
lemma differentiableAt_fstar_slice {α : ℝ} (hα : 0 < α) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    DifferentiableAt ℝ (fun θ' => Work.Construction.Fstar (3 * α) z θ') θ := by
  have hbase : 0 < Real.sin θ * Real.cos θ ^ 2 := by
    have h1 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have hGam : DifferentiableAt ℝ (fun θ' : ℝ => (Real.sin θ' * Real.cos θ' ^ 2) ^ α) θ := by
    have h1 : DifferentiableAt ℝ (fun θ' : ℝ => Real.sin θ' * Real.cos θ' ^ 2) θ := by fun_prop
    exact h1.rpow_const (Or.inl (ne_of_gt hbase))
  have hconst : (fun θ' : ℝ => Work.Construction.Fstar (3 * α) z θ')
      = fun θ' => (Work.FM.Fstar z * ((3 * α) / Work.Spaces.c (3 * α)))
          * (Real.sin θ' * Real.cos θ' ^ 2) ^ α := by
    funext θ'
    rw [Work.Construction.Fstar, Work.Spaces.Gam, show 3 * α / 3 = α from by ring]
    ring
  rw [hconst]
  exact hGam.const_mul _

/-- **The angular derivative of the positive branch**, bounded by the singular weight
`200α² sin^{α-1}θ cos^{2α-1}θ` plus the (uncontrolled) angular derivative of `g`. -/
lemma abs_pdz_posbranch_le {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {g : ℝ → ℝ → ℝ → ℝ} {τ z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hd : DifferentiableAt ℝ (fun θ' => Ppos α g τ z θ') θ) :
    |deriv (fun θ' => Ppos α g τ z θ') θ|
      ≤ 200 * α ^ 2 * (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1)
        + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z θ| := by
  have hFd := differentiableAt_fstar_slice (z := z) hα hθ
  have hgd : DifferentiableAt ℝ (fun θ' => g z θ' τ) θ := by
    have hsub : DifferentiableAt ℝ
        ((fun θ' => Ppos α g τ z θ') - (fun θ' => Work.Construction.Fstar (3 * α) z θ')) θ :=
      hd.sub hFd
    refine hsub.congr_of_eventuallyEq ?_
    filter_upwards with θ'
    simp [Ppos]
  have hFsum : (fun θ' => Ppos α g τ z θ')
      = (fun θ' => Work.Construction.Fstar (3 * α) z θ') + (fun θ' => g z θ' τ) := rfl
  rw [hFsum, deriv_add hFd hgd]
  have h1 : |deriv (fun θ' => Work.Construction.Fstar (3 * α) z θ') θ|
      ≤ 200 * α ^ 2 * (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1) :=
    (Work.FTS.FireFix.Clauses.Fstar_bounds hα hα13).2.2 z θ hz ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have h2 : deriv (fun θ' => g z θ' τ) θ
      = Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z θ := rfl
  rw [h2]
  calc |deriv (fun θ' => Work.Construction.Fstar (3 * α) z θ') θ
        + Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z θ|
      ≤ |deriv (fun θ' => Work.Construction.Fstar (3 * α) z θ') θ|
        + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z θ| := abs_add_le _ _
    _ ≤ 200 * α ^ 2 * (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1)
        + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z θ| := by linarith [h1]

end Work.FTS.FireFix.Clauses
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.Support.timeDeriv_physOmega_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Clauses.Support

theorem timeDeriv_physOmega_eq {α : ℝ} (hα : 0 < α)
    {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : Work.FTS.Physical.PhysClock}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' α S A B g)
    (x : EuclideanSpace ℝ (Fin 3)) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) C.T) :
    FiniteTimeSingularity.timeDeriv
        (fun y s => - Work.FTS.Physical.physOmega α A B g C y s) x t
      = - ((C.A (Work.FTS.Physical.clockInv C t))⁻¹ •
            FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x
              (Work.FTS.Physical.clockInv C t)) := by
  -- the fake-time coordinate of `t` is nonnegative, so it lies in the strip `[0, τ(t)+1]`
  have hpos : 0 ≤ Work.FTS.Physical.clockInv C t := Work.FTS.Physical.clockInv_nonneg C ht
  obtain ⟨hder, _⟩ :=
    Work.FTS.FireFix.Prime.physVort_hasDerivAt_and_bound (α := α)
      (S := Work.FTS.Physical.clockInv C t + 1) (A := A) (B := B) (g := g)
      (hreg _ (by linarith : (0 : ℝ) < Work.FTS.Physical.clockInv C t + 1))
  have hv := hder x _ ⟨hpos, by linarith⟩
  -- the extended inverse clock is differentiable at every `t ∈ [0, C.T)`, including `t = 0`
  have hc : HasDerivAt (Work.FTS.Physical.clockInv C)
      ((C.A (Work.FTS.Physical.clockInv C t))⁻¹) t := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      simpa using Work.FTS.Physical.clockInv_hasDerivAt_zero C
    · exact Work.FTS.Physical.clockInv_hasDerivAt C ⟨h, ht.2⟩
  -- chain rule, then negation
  have hgs : HasDerivAt
      (fun s : ℝ => Work.FTS.Regularity.physVort α A B g x (Work.FTS.Physical.clockInv C s))
      ((C.A (Work.FTS.Physical.clockInv C t))⁻¹ •
        FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x
          (Work.FTS.Physical.clockInv C t)) t := by
    simpa [Function.comp_def] using hv.scomp t hc
  have hneg := hgs.neg
  -- `physOmega`/`timeDeriv` unfold definitionally to the composite above
  change deriv (fun s : ℝ =>
      - (Work.FTS.Regularity.physVort α A B g x (Work.FTS.Physical.clockInv C s))) t
    = - ((C.A (Work.FTS.Physical.clockInv C t))⁻¹ •
        FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x
          (Work.FTS.Physical.clockInv C t))
  exact hneg.deriv

end Work.FTS.FireFix.Clauses.Support
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.integrableOn_psi_weight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.FireFix.Clauses.integrableOn_psi_weight`

Integrability, over the half-strip `(0,inf) x (-pi/2, pi/2)`, of the psi-weight integrand of the
reconstruction (with the cutoff `1_{q.1 <= L}`): the `Ca`-term, the `Cb`-term, the angular
`sin^{a-1}cos^{2a-1}` term and the `|d_theta g|` term, all times `q.1^{1/a-1} cos q.2`.

The `|d_theta g|` term is handled by an `L^2` Cauchy-Schwarz/AM-GM against the two weighted pieces
`(D_theta g)^2 sin(2theta)^{-gamma}` and `cos^2 theta sin(2theta)^{gamma-2}`; the first is
integrable by `HkMem (3a) 4` (the `H^4` field of `RegPkg'`), the second by elementary calculus.
The pointwise bookkeeping lives in `Work.FTS.FireFix.Clauses.psiWpsiLeWmaj`, the auxiliary
integrability statements in `Clauses/PsiWt/`.
-/

open MeasureTheory Set Filter Topology

namespace Work.FTS.FireFix.Clauses

set_option maxHeartbeats 1000000
theorem integrableOn_psi_weight {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S)
    {Ca Cb Cc L : ℝ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc) (hL : 0 ≤ L) :
    MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
      (if q.1 ≤ L then
        Ca / ((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2)
        + Cb * (B τ * q.1) ^ ((3 * α - 1) / (3 * α))
        + Cc * (200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1) * (Real.cos q.2) ^ (2 * α - 1)
            + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2)|)
          / ((B τ * q.1) ^ (1 / (3 * α)))
      else 0) * q.1 ^ (1 / α - 1) * Real.cos q.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  change MeasureTheory.IntegrableOn (psiWpsi α Ca Cb Cc L B g τ)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))
  have hssmeas : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  have hα : 0 < α := h.hα
  have hα13 : α ≤ 1 / 3 := h.hα13
  have hb : 0 < B τ := h.hB τ hτ
  have hγ1 : 1 < Work.Spaces.gam (Work.FTS.Regularity.pExp α) :=
    Work.Spaces.one_lt_gam (Work.FTS.Regularity.pExp_pos hα)
  have hγ2 : Work.Spaces.gam (Work.FTS.Regularity.pExp α) ≤ 2 := by
    rw [Work.Spaces.gam, Work.FTS.Regularity.pExp]; linarith
  have hI1 : MeasureTheory.IntegrableOn (psiWq1 L)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
    PsiWt.integrableOn_indic_Iic hL
  have hI2 : MeasureTheory.IntegrableOn (psiWq2 α L)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
    PsiWt.integrableOn_sin_rpow_mul_cos_rpow hα hα13 hL
  have hI3 : MeasureTheory.IntegrableOn (psiWq3 α (Work.FTS.Regularity.gSlice g τ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
    PsiWt.integrableOn_Dth_sq_sin_rpow h hτ
  have hI4 : MeasureTheory.IntegrableOn
      (psiWq4 (Work.Spaces.gam (Work.FTS.Regularity.pExp α)) L)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
    PsiWt.integrableOn_cos_sq_sin_rpow hγ1 hγ2 hL
  have hMaj : MeasureTheory.IntegrableOn (psiWmaj α Ca Cb Cc L B g τ)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
    have hM1 : MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
        (Ca * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1))
          + Cb * (B τ) ^ (1 - 1 / (3 * α)) * (L ^ (2 / (3 * α)))) * psiWq1 L q)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
      psiIntegrableOnConstMul hI1
    have hM2 : MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
        (Cc * 200 * α ^ 2 * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)))
          * psiWq2 α L q)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
      psiIntegrableOnConstMul hI2
    have hM3 : MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
        (Cc * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) / 2)
          * psiWq3 α (Work.FTS.Regularity.gSlice g τ) q)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
      psiIntegrableOnConstMul hI3
    have hM4 : MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
        (Cc * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) / 2)
          * psiWq4 (Work.Spaces.gam (Work.FTS.Regularity.pExp α)) L q)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
      psiIntegrableOnConstMul hI4
    unfold psiWmaj
    exact ((hM1.add hM2).add hM3).add hM4
  have hmeas : AEStronglyMeasurable (psiWpsi α Ca Cb Cc L B g τ)
      (MeasureTheory.volume.restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) := by
    have hp : AEStronglyMeasurable (fun q : ℝ × ℝ =>
        |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2)|)
        (MeasureTheory.volume.restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) :=
      continuous_abs.comp_aestronglyMeasurable (PsiWt.aesm_pth_abs h hτ)
    have hX : AEStronglyMeasurable (fun q : ℝ × ℝ => (B τ * q.1) ^ (1 / (3 * α)))
        (MeasureTheory.volume.restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) :=
      ((psiMeasurableRpowConst _).comp
        (measurable_const.mul measurable_fst)).aestronglyMeasurable
    have hY : AEStronglyMeasurable (fun q : ℝ × ℝ =>
        (B τ * q.1) ^ ((3 * α - 1) / (3 * α)))
        (MeasureTheory.volume.restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) :=
      ((psiMeasurableRpowConst _).comp
        (measurable_const.mul measurable_fst)).aestronglyMeasurable
    have hc : AEStronglyMeasurable (fun q : ℝ × ℝ => Real.cos q.2)
        (MeasureTheory.volume.restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) :=
      (Real.measurable_cos.comp measurable_snd).aestronglyMeasurable
    have hsa : AEStronglyMeasurable (fun q : ℝ × ℝ => (Real.sin (abs q.2)) ^ (α - 1))
        (MeasureTheory.volume.restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) :=
      ((psiMeasurableRpowConst _).comp
        (Real.measurable_sin.comp measurable_snd.abs)).aestronglyMeasurable
    have hc2 : AEStronglyMeasurable (fun q : ℝ × ℝ => (Real.cos q.2) ^ (2 * α - 1))
        (MeasureTheory.volume.restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) :=
      ((psiMeasurableRpowConst _).comp
        (Real.measurable_cos.comp measurable_snd)).aestronglyMeasurable
    have he : AEStronglyMeasurable (fun q : ℝ × ℝ => q.1 ^ (1 / α - 1))
        (MeasureTheory.volume.restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) :=
      ((psiMeasurableRpowConst _).comp measurable_fst).aestronglyMeasurable
    have hinner : AEStronglyMeasurable (psiWinner α Ca Cb Cc B g τ)
        (MeasureTheory.volume.restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) := by
      have hXm : Measurable (fun q : ℝ × ℝ => (B τ * q.1) ^ (1 / (3 * α))) :=
        (psiMeasurableRpowConst _).comp (measurable_const.mul measurable_fst)
      have hYm : Measurable (fun q : ℝ × ℝ =>
          (B τ * q.1) ^ ((3 * α - 1) / (3 * α))) :=
        (psiMeasurableRpowConst _).comp (measurable_const.mul measurable_fst)
      have hcm : Measurable (fun q : ℝ × ℝ => Real.cos q.2) :=
        Real.measurable_cos.comp measurable_snd
      have hsam : Measurable (fun q : ℝ × ℝ => (Real.sin (abs q.2)) ^ (α - 1)) :=
        (psiMeasurableRpowConst _).comp (Real.measurable_sin.comp measurable_snd.abs)
      have hc2m : Measurable (fun q : ℝ × ℝ => (Real.cos q.2) ^ (2 * α - 1)) :=
        (psiMeasurableRpowConst _).comp (Real.measurable_cos.comp measurable_snd)
      have hMm : Measurable (fun q : ℝ × ℝ =>
          Ca / ((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2)
          + Cb * (B τ * q.1) ^ ((3 * α - 1) / (3 * α))
          + Cc * (200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1)
              * (Real.cos q.2) ^ (2 * α - 1))
            / ((B τ * q.1) ^ (1 / (3 * α)))) :=
        (((measurable_const : Measurable (fun _ : ℝ × ℝ => Ca)).div
            (hXm.mul hcm)).add
          ((measurable_const : Measurable (fun _ : ℝ × ℝ => Cb)).mul hYm)).add
          (((measurable_const : Measurable (fun _ : ℝ × ℝ => Cc)).mul
            (((measurable_const : Measurable (fun _ : ℝ × ℝ => 200 * α ^ 2)).mul hsam).mul
              hc2m)).div hXm)
      have hBm : Measurable (fun q : ℝ × ℝ => Cc / ((B τ * q.1) ^ (1 / (3 * α)))) :=
        (measurable_const : Measurable (fun _ : ℝ × ℝ => Cc)).div hXm
      refine (hMm.aestronglyMeasurable.add (hBm.aestronglyMeasurable.mul hp)).congr
        (Filter.Eventually.of_forall (fun q => ?_))
      simp only [Pi.add_apply, Pi.mul_apply]
      unfold psiWinner
      ring
    have hite : AEStronglyMeasurable
        (fun q : ℝ × ℝ => if q.1 ≤ L then psiWinner α Ca Cb Cc B g τ q else 0)
        (MeasureTheory.volume.restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) := by
      have hs : MeasurableSet {q : ℝ × ℝ | q.1 ≤ L} :=
        measurableSet_le measurable_fst measurable_const
      convert hinner.indicator hs using 1
      funext q
      by_cases hq : q.1 ≤ L
      · rw [Set.indicator_of_mem (show q ∈ {q : ℝ × ℝ | q.1 ≤ L} from hq), if_pos hq]
      · rw [Set.indicator_of_notMem (show q ∉ {q : ℝ × ℝ | q.1 ≤ L} from hq), if_neg hq]
    exact (hite.mul he).mul hc
  have hnull : (MeasureTheory.volume.restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)))
        {q : ℝ × ℝ | q.2 = 0} = 0 := by
    rw [MeasureTheory.Measure.restrict_apply' hssmeas]
    refine MeasureTheory.measure_mono_null (t := Set.univ ×ˢ ({0} : Set ℝ)) ?_ ?_
    · rintro q ⟨hq, -⟩
      exact ⟨Set.mem_univ q.1, hq⟩
    · rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
        MeasureTheory.Measure.prod_prod]
      simp [Real.volume_univ, Real.volume_singleton]
  have hbd : ∀ᵐ q ∂(MeasureTheory.volume.restrict
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))),
      ‖psiWpsi α Ca Cb Cc L B g τ q‖ ≤ psiWmaj α Ca Cb Cc L B g τ q := by
    have h1 : ∀ᵐ q ∂(MeasureTheory.volume.restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))),
        (‖psiWpsi α Ca Cb Cc L B g τ q‖ ≤ psiWmaj α Ca Cb Cc L B g τ q) ∨ q.2 = 0 :=
      MeasureTheory.ae_restrict_of_forall_mem hssmeas (fun q hq => by
        have hq1 : 0 < q.1 := hq.1
        have hq2 : q.2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := hq.2
        by_cases h0 : q.2 = 0
        · exact Or.inr h0
        · exact Or.inl (psiWpsiLeWmaj h hτ hCa hCb hCc hL hq1 hq2 h0))
    have h2 : ∀ᵐ q ∂(MeasureTheory.volume.restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))), q.2 ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      rw [show {q : ℝ × ℝ | ¬q.2 ≠ 0} = {q : ℝ × ℝ | q.2 = 0} from by ext q; simp]
      exact hnull
    exact (h1.and h2).mono (fun q hq => hq.1.resolve_right hq.2)
  exact hMaj.mono' hmeas hbd

end Work.FTS.FireFix.Clauses
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.physOmega_hasDerivWithinAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS.FireFix.Clauses

/-- **The time-derivative clause.**  For every `x : ℝ³` and every `t ∈ [0, C.T)`, the negated
physical vorticity `s ↦ −physOmega α A B g C x s` has, within `[t, ∞)`, the derivative equal to
its own time derivative `∂ₜ(−physOmega α A B g C)(x,t)`.

Both sides are the chain-rule value: the two-sided derivative of `τ ↦ physVort α A B g x τ` at
`τ = clockInv C t`, composed with the derivative `(C.A (clockInv C t))⁻¹` of the extended inverse
clock. -/
theorem physOmega_hasDerivWithinAt {α : ℝ} (hα : 0 < α)
    {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : Work.FTS.Physical.PhysClock}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' α S A B g) :
    ∀ x : EuclideanSpace ℝ (Fin 3), ∀ t ∈ Set.Ico (0 : ℝ) C.T,
      HasDerivWithinAt (fun s : ℝ => - (Work.FTS.Physical.physOmega α A B g C x s))
        (FiniteTimeSingularity.timeDeriv
          (fun y s => - (Work.FTS.Physical.physOmega α A B g C y s)) x t)
        (Set.Ici t) t := by
  intro x t ht
  -- the fake-time coordinate `τ₀ = clockInv C t` is nonnegative, hence lies in a strip `[0,S]`
  have hpos : 0 ≤ Work.FTS.Physical.clockInv C t := Work.FTS.Physical.clockInv_nonneg C ht
  obtain ⟨hder, _⟩ :=
    Work.FTS.FireFix.Prime.physVort_hasDerivAt_and_bound
      (hreg _ (by linarith : 0 < Work.FTS.Physical.clockInv C t + 1))
  have hv := hder x _ ⟨hpos, by linarith⟩
  -- the extended inverse clock is differentiable at every `t ∈ [0, C.T)`, including `t = 0`
  have hc : HasDerivAt (Work.FTS.Physical.clockInv C)
      ((C.A (Work.FTS.Physical.clockInv C t))⁻¹) t := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      simpa using Work.FTS.Physical.clockInv_hasDerivAt_zero C
    · exact Work.FTS.Physical.clockInv_hasDerivAt C ⟨h, ht.2⟩
  -- chain rule, then negation
  have hgs : HasDerivAt
      (fun s : ℝ => Work.FTS.Regularity.physVort α A B g x (Work.FTS.Physical.clockInv C s))
      ((C.A (Work.FTS.Physical.clockInv C t))⁻¹ •
        FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x
          (Work.FTS.Physical.clockInv C t)) t := by
    simpa [Function.comp_def] using hv.scomp t hc
  have hneg : HasDerivAt
      (fun s : ℝ => - (Work.FTS.Regularity.physVort α A B g x (Work.FTS.Physical.clockInv C s)))
      (-((C.A (Work.FTS.Physical.clockInv C t))⁻¹ •
        FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x
          (Work.FTS.Physical.clockInv C t))) t :=
    hgs.neg
  -- `physOmega` and `timeDeriv` unfold definitionally to the composite above
  show HasDerivWithinAt
      (fun s : ℝ => - (Work.FTS.Regularity.physVort α A B g x (Work.FTS.Physical.clockInv C s)))
      (deriv (fun s : ℝ => -
        (Work.FTS.Regularity.physVort α A B g x (Work.FTS.Physical.clockInv C s))) t)
      (Set.Ici t) t
  exact hneg.differentiableAt.hasDerivAt.hasDerivWithinAt

end Work.FTS.FireFix.Clauses
end
-- ===== merged: Submission.Work.FTS.FireFix.PhysFields =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix

open Work.FTS.Regularity (pExp gSlice physVort)
open Work.FTS.BSSwirl (swirlField)
open Work.FTS.Physical (PhysClock)

/-! ## The `(ρ,θ)`-dictionary at a point -/

theorem rhoP_radial_axial (x : R3) :
    Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) = Work.Cyl.rho x := by
  rw [Work.Cyl.rhoP, Work.Cyl.rho, Work.Cyl.radial_sq]

theorem thetaP_radial_axial (x : R3) :
    Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x) = Work.Cyl.theta x := rfl

/-! ## The swirl scalar of the (negated) physical vorticity -/

/-- **The swirl scalar of the negated physical vorticity slice.**  For a fake time `τ`, the slice
`x ↦ −physOmega α A B g C x t` (with `τ = clockInv C t`) is the swirl field of

  `negSwirlScalar α τ A B g ρ θ = −((A τ)⁻¹ · profile (3α) (g·τ) (ρ^{3α}/B τ) θ)`,

in the `(ρ,θ)` coordinates of the cylinder. -/
noncomputable def negSwirlScalar (α τ : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (ρ θ : ℝ) : ℝ :=
  -((A τ)⁻¹ * Work.ConstructionInstance.profile (pExp α) (gSlice g τ)
      (ρ ^ pExp α / B τ) θ)

/-- The pointwise form of the swirl representation, in the meridian coordinates `(ρ(x),θ(x))`. -/
theorem neg_physOmega_slice_eq {α : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : PhysClock}
    (x : R3) (t : ℝ) :
    - Work.FTS.Physical.physOmega α A B g C x t
      = negSwirlScalar α (Work.FTS.Physical.clockInv C t) A B g
          (Work.Cyl.rho x) (Work.Cyl.theta x) • Work.Cyl.eTheta x := by
  rw [Work.FTS.Physical.physOmega_apply, Work.FTS.Regularity.physVort_apply,
    Work.ConstructionInstance.omegaSz_apply, negSwirlScalar, neg_smul, smul_smul]

/-- The slice `x ↦ −physOmega α A B g C x t` is the swirl field of `negSwirlScalar`, in the
`(radial, axial)` coordinates in which `Work.FTS.BSSwirl.BiotSavartSwirl` is stated. -/
theorem neg_physOmega_swirlShape {α : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : PhysClock}
    (t : ℝ) :
    (fun x : R3 => - Work.FTS.Physical.physOmega α A B g C x t)
      = swirlField (fun r a => negSwirlScalar α (Work.FTS.Physical.clockInv C t) A B g
          (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a)) := by
  funext x
  rw [Work.FTS.BSSwirl.swirlField_apply, rhoP_radial_axial, thetaP_radial_axial]
  exact neg_physOmega_slice_eq x t

/-- **The swirl scalar is odd in the angle**: `negSwirlScalar α τ A B g ρ (−θ) = −…`.  This is the
oddness of the profile `profile (3α) (g·τ)` (the odd extension of `F_* + g`), which holds because
the perturbation vanishes at `θ = 0` (`VanishTheta`). -/
theorem negSwirlScalar_odd {α τ : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (hα : α ≠ 0) (hvt : ∀ z : ℝ, gSlice g τ z 0 = 0) (ρ θ : ℝ) :
    negSwirlScalar α τ A B g ρ (-θ) = - negSwirlScalar α τ A B g ρ θ := by
  have hp : pExp α ≠ 0 := by
    rw [pExp]
    intro h
    exact hα (by linarith)
  rw [negSwirlScalar, negSwirlScalar, Work.ConstructionInstance.profile_odd hp hvt]
  ring

/-! ## Oddness of the reconstructed velocity -/

/-- **Oddness of the reconstructed velocity at every physical time** (for the signed vorticity
`ω = −physOmega`).  The slice of `ω` is a swirl field whose angular scalar is odd in the angle, so
`Work.FTS.Physical.isOdd_physVel_of_swirlShape` gives the oddness of `u = physVel ω`. -/
theorem neg_physOmega_isOdd {α : ℝ≥0} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : PhysClock}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' (α : ℝ) S A B g)
    {t : ℝ} (ht : t ∈ Set.Ico 0 C.T) :
    IsOdd ((Work.FTS.Physical.physVel
      (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s)) · t) := by
  have hTpos : 0 < C.T := Work.FTS.Physical.Clock.T_pos C
  set S : ℝ := (t + C.T) / 2 with hSdef
  have hS : S ∈ Set.Ioo (0 : ℝ) C.T :=
    ⟨by rw [hSdef]; linarith [ht.1, ht.2], by rw [hSdef]; linarith [ht.2]⟩
  have htSle : t ≤ S := by rw [hSdef]; linarith [ht.2]
  set Sel : ℝ := Work.FTS.Physical.clockInv C S with hSeldef
  have hSelpos : 0 < Sel := by
    rw [hSeldef]; exact Work.FTS.Physical.clockInv_pos_of_pos C hS
  have hsel : Work.FTS.RegPkgGal.RegPkg' (α : ℝ) Sel A B g := hreg Sel hSelpos
  have hτmem : Work.FTS.Physical.clockInv C t ∈ Set.Icc (0 : ℝ) Sel := by
    refine ⟨Work.FTS.Physical.clockInv_nonneg C ht, ?_⟩
    rw [hSeldef]
    exact Work.FTS.Physical.clockInv_mono C ht ⟨hS.1.le, hS.2⟩ htSle
  have hvt : ∀ z : ℝ, gSlice g (Work.FTS.Physical.clockInv C t) z 0 = 0 :=
    fun z => (hsel.hvt _ hτmem).1 z
  refine Work.FTS.Physical.isOdd_physVel_of_swirlShape
    (W := negSwirlScalar (α : ℝ) (Work.FTS.Physical.clockInv C t) A B g) ?_ ?_
  · intro x
    exact neg_physOmega_slice_eq x t
  · refine negSwirlScalar_odd ?_ hvt
    have hαpos : 0 < (α : ℝ) := (hreg 1 one_pos).hα
    intro h0
    rw [h0] at hαpos
    exact lt_irrefl 0 hαpos

/-! ## The curl and divergence clauses -/

/-- **The curl and divergence clauses of the reconstruction** (design §1, item 7a): for the swirl
Biot–Savart law `hBS`, the Biot–Savart field of the negated physical vorticity inverts its curl and
is divergence-free at every physical time.

Proof: on the strip `[0,S]`, `S = (t + C.T)/2`, the per-strip bundle supplies both the `HolderWith`
datum and the support of the slice; the slice *is* a swirl field (`neg_physOmega_swirlShape`), so
`BiotSavartSwirl` applies. -/
theorem neg_physOmega_curl_div {α : ℝ≥0} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : PhysClock}
    (hBS : Work.FTS.BSSwirl.BiotSavartSwirl)
    (hbun : ∀ S' ∈ Set.Ioo 0 C.T, ∃ R : ℝ,
      Work.CoreResiduals.BSAdmissibleStripFull α
        (fun x t => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x t) R S') :
    (∀ t ∈ Set.Ico 0 C.T, ∀ x : R3,
        vorticity (fun y => Work.FTS.Physical.physVel
          (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s) y t) x
          = - Work.FTS.Physical.physOmega (α : ℝ) A B g C x t) ∧
      (∀ t ∈ Set.Ico 0 C.T, div (fun y => Work.FTS.Physical.physVel
        (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s) y t) = 0) := by
  constructor
  · intro t ht x
    set S : ℝ := (t + C.T) / 2 with hSdef
    have hS : S ∈ Set.Ioo (0 : ℝ) C.T :=
      ⟨by rw [hSdef]; linarith [ht.1, ht.2], by rw [hSdef]; linarith [ht.2]⟩
    have htS : t ∈ Set.Icc (0 : ℝ) S := ⟨ht.1, by rw [hSdef]; linarith [ht.2]⟩
    obtain ⟨R, hb⟩ := hbun S hS
    obtain ⟨⟨hR, hsupp, ⟨M, hM⟩, ⟨H, hH⟩, ⟨N, hN⟩, hmeas⟩, -, -⟩ := hb
    have hholder : HolderWith H α (swirlField (fun r a =>
        negSwirlScalar (α : ℝ) (Work.FTS.Physical.clockInv C t) A B g
          (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a))) := by
      rw [← neg_physOmega_swirlShape (α := (α : ℝ)) (A := A) (B := B) (g := g) (C := C) t]
      exact hH t htS
    have hsupp' : ∀ y : R3, swirlField (fun r a =>
        negSwirlScalar (α : ℝ) (Work.FTS.Physical.clockInv C t) A B g
          (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a)) y ≠ 0 → ‖y‖ ≤ R := by
      intro y hy
      rw [← neg_physOmega_swirlShape (α := (α : ℝ)) (A := A) (B := B) (g := g) (C := C) t]
        at hy
      have h := hsupp t htS y hy
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    obtain ⟨hc, -⟩ := hBS (fun r a => negSwirlScalar (α : ℝ) (Work.FTS.Physical.clockInv C t)
      A B g (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a)) H α R hα hα1 hholder hsupp'
    have hfun : (fun y : R3 => Work.FTS.Physical.physVel
        (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s) y t)
        = Work.LWP.biotSavart (swirlField (fun r a => negSwirlScalar (α : ℝ)
            (Work.FTS.Physical.clockInv C t) A B g (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a))) := by
      funext y
      simp only [Work.FTS.Physical.physVel_apply,
        neg_physOmega_swirlShape (α := (α : ℝ)) (A := A) (B := B) (g := g) (C := C) t]
    rw [hfun]
    have hx : - Work.FTS.Physical.physOmega (α : ℝ) A B g C x t
        = swirlField (fun r a => negSwirlScalar (α : ℝ) (Work.FTS.Physical.clockInv C t)
            A B g (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a)) x :=
      congrFun (neg_physOmega_swirlShape (α := (α : ℝ)) (A := A) (B := B) (g := g) (C := C) t) x
    rw [hx]
    exact hc x
  · intro t ht
    set S : ℝ := (t + C.T) / 2 with hSdef
    have hS : S ∈ Set.Ioo (0 : ℝ) C.T :=
      ⟨by rw [hSdef]; linarith [ht.1, ht.2], by rw [hSdef]; linarith [ht.2]⟩
    have htS : t ∈ Set.Icc (0 : ℝ) S := ⟨ht.1, by rw [hSdef]; linarith [ht.2]⟩
    obtain ⟨R, hb⟩ := hbun S hS
    obtain ⟨⟨hR, hsupp, ⟨M, hM⟩, ⟨H, hH⟩, ⟨N, hN⟩, hmeas⟩, -, -⟩ := hb
    have hholder : HolderWith H α (swirlField (fun r a =>
        negSwirlScalar (α : ℝ) (Work.FTS.Physical.clockInv C t) A B g
          (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a))) := by
      rw [← neg_physOmega_swirlShape (α := (α : ℝ)) (A := A) (B := B) (g := g) (C := C) t]
      exact hH t htS
    have hsupp' : ∀ y : R3, swirlField (fun r a =>
        negSwirlScalar (α : ℝ) (Work.FTS.Physical.clockInv C t) A B g
          (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a)) y ≠ 0 → ‖y‖ ≤ R := by
      intro y hy
      rw [← neg_physOmega_swirlShape (α := (α : ℝ)) (A := A) (B := B) (g := g) (C := C) t]
        at hy
      have h := hsupp t htS y hy
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    obtain ⟨-, hd⟩ := hBS (fun r a => negSwirlScalar (α : ℝ) (Work.FTS.Physical.clockInv C t)
      A B g (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a)) H α R hα hα1 hholder hsupp'
    have hfun : (fun y : R3 => Work.FTS.Physical.physVel
        (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s) y t)
        = Work.LWP.biotSavart (swirlField (fun r a => negSwirlScalar (α : ℝ)
            (Work.FTS.Physical.clockInv C t) A B g (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a))) := by
      funext y
      simp only [Work.FTS.Physical.physVel_apply,
        neg_physOmega_swirlShape (α := (α : ℝ)) (A := A) (B := B) (g := g) (C := C) t]
    rw [hfun]
    funext x
    exact hd x

/-- **The `C^{1,α}` datum of the reconstruction** (for `ω = −physOmega`): the restriction of the
joint `C^{1,α}` strip statement of the space–time Schauder estimate to the time slice `t = 0`. -/
theorem neg_physOmega_datum_holder {α : ℝ≥0} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : PhysClock}
    (hbun : ∀ S' ∈ Set.Ioo 0 C.T, ∃ R : ℝ,
      Work.CoreResiduals.BSAdmissibleStripFull α
        (fun x t => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x t) R S') :
    IsContDiffHolder ℝ α ((Work.FTS.Physical.physVel
      (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s)) · 0) := by
  have hTpos : 0 < C.T := Work.FTS.Physical.Clock.T_pos C
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S ∈ Set.Ioo (0 : ℝ) C.T :=
    ⟨C.T / 2, ⟨by linarith, by linarith⟩⟩
  obtain ⟨R, hb⟩ := hbun S hS
  have hstrip := Work.FTS.Physical.isContDiffHolderOn_physVel (α := α) hα hα1 hS.1 hb
  have hslice := Prime.isContDiffHolder_slice (S := S) (τ := 0)
    ⟨le_rfl, hS.1.le⟩ α hstrip
  simpa only [Function.uncurry, Work.FTS.Physical.physVel_apply] using hslice

end Work.FTS.FireFix
end
-- ===== merged: Submission.Work.FTS_BSIdentP.Slim.AbsDivPsiCoreLeOne =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdentP.Levels

open Work.FTS.BSIdent

theorem abs_div_psiCore_le_one {G : ℝ → ℝ → ℝ} {p c b C₀ lam r z : ℝ}
    (hC₀ : 0 ≤ C₀) (hlam : 0 < lam) (hp : 0 < p) (hb : 0 < b)
    (hr : 0 < r) (hz : 0 < z) (hpl : 2 ≤ p * lam)
    (hval : |G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z)
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam)) :
    |Work.FTS.BSIdent.Cyl.psiCore p c b G r z / r|
      ≤ Work.FTS.BSIdentP.Levels.decayKqOne c C₀ lam b / (1 + Work.Cyl.rhoP r z) := by
  -- Unfold the core `ψ = ρ² c G(w, θ)` and abbreviate the four recurring quantities.
  simp only [Work.FTS.BSIdent.Cyl.psiCore]
  set ρ := Work.Cyl.rhoP r z with hρ
  set θ := Work.Cyl.thetaP r z with hθ
  set w := ρ ^ p / b with hw
  set R := (1 + w) ^ (-lam) with hR
  have hρpos : 0 < ρ := by rw [hρ]; exact Work.Cyl.rhoP_pos hr z
  have hρnn : 0 ≤ ρ := hρpos.le
  have hθpos : 0 < θ := by rw [hθ]; exact Work.FTS.BSIdent.Cyl.thetaP_pos_of_pos hr hz
  have hwpos : 0 < w := by rw [hw]; exact div_pos (Real.rpow_pos_of_pos hρpos p) hb
  have hRnn : 0 ≤ R := by
    rw [hR]; exact (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < 1 + w) _).le
  -- `cos θ = r/ρ` is the sharp form of the distance of `θ` to `π/2`.
  have hcos : Real.cos θ = r / ρ := by rw [hθ, hρ]; exact Work.Cyl.cos_thetaP hr z
  -- The rate hypothesis, in the abbreviations.
  have hG : |G w θ| ≤ C₀ * (Real.pi / 2 - θ) * R := hval
  -- Jordan's inequality turns the profile rate `(π/2 - θ)` into `(π/2) cos θ = (π/2) r/ρ`.
  have hSle : Real.pi / 2 - θ ≤ Real.pi / 2 * Real.cos θ := by
    have hθabs : |θ| ≤ Real.pi / 2 :=
      le_of_lt (by rw [hθ]; exact Work.FTS.BSIdent.Cyl.abs_thetaP_lt r z)
    have h := Work.FTS.BSIdent.Cyl.DecayAux.pi_div_two_sub_abs_le_cos hθabs
    rw [abs_of_nonneg hθpos.le] at h
    exact h
  -- … so that `ρ² (π/2 - θ)/r ≤ (π/2) ρ`.
  have hSbound : ρ ^ 2 * (Real.pi / 2 - θ) / r ≤ Real.pi / 2 * ρ := by
    have h1 : ρ ^ 2 * (Real.pi / 2 - θ) ≤ ρ ^ 2 * (Real.pi / 2 * Real.cos θ) :=
      mul_le_mul_of_nonneg_left hSle (sq_nonneg ρ)
    have h2 : ρ ^ 2 * (Real.pi / 2 * Real.cos θ) = Real.pi / 2 * ρ * r := by
      rw [hcos]; field_simp
    rw [h2] at h1
    rw [div_le_iff₀ hr]
    exact h1
  have step1 : |ρ ^ 2 * c * G w θ / r|
      ≤ |c| * C₀ * (ρ ^ 2 * (Real.pi / 2 - θ) / r) * R := by
    have h1 : (0 : ℝ) ≤ ρ ^ 2 * |c| := mul_nonneg (sq_nonneg ρ) (abs_nonneg c)
    have h2 : ρ ^ 2 * |c| * |G w θ| / r
        ≤ ρ ^ 2 * |c| * (C₀ * (Real.pi / 2 - θ) * R) / r :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hG h1) hr.le
    calc |ρ ^ 2 * c * G w θ / r|
        = ρ ^ 2 * |c| * |G w θ| / r := by
          rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ρ), abs_of_nonneg hr.le]
      _ ≤ ρ ^ 2 * |c| * (C₀ * (Real.pi / 2 - θ) * R) / r := h2
      _ = |c| * C₀ * (ρ ^ 2 * (Real.pi / 2 - θ) / r) * R := by ring
  have step2 : |c| * C₀ * (ρ ^ 2 * (Real.pi / 2 - θ) / r) * R
      ≤ |c| * C₀ * (Real.pi / 2) * ρ * R := by
    have h4 : (0 : ℝ) ≤ |c| * C₀ * R :=
      mul_nonneg (mul_nonneg (abs_nonneg c) hC₀) hRnn
    have h5 := mul_le_mul_of_nonneg_left hSbound h4
    calc |c| * C₀ * (ρ ^ 2 * (Real.pi / 2 - θ) / r) * R
        = (|c| * C₀ * R) * (ρ ^ 2 * (Real.pi / 2 - θ) / r) := by ring
      _ ≤ (|c| * C₀ * R) * (Real.pi / 2 * ρ) := h5
      _ = |c| * C₀ * (Real.pi / 2) * ρ * R := by ring
  have step3 : |c| * C₀ * (Real.pi / 2) * ρ * R
      ≤ decayKqOne c C₀ lam b / (1 + ρ) := by
    have hρR : ρ * R ≤ 2 * max 1 (b ^ lam) / (1 + ρ) := by
      have h := rho_mul_rpow_weight_le_two hp hlam hb hρnn hpl
      rw [← hw, ← hR] at h
      exact h
    have h4 : (0 : ℝ) ≤ |c| * C₀ * (Real.pi / 2) :=
      mul_nonneg (mul_nonneg (abs_nonneg c) hC₀) (by linarith [Real.pi_pos])
    calc |c| * C₀ * (Real.pi / 2) * ρ * R
        = (|c| * C₀ * (Real.pi / 2)) * (ρ * R) := by ring
      _ ≤ (|c| * C₀ * (Real.pi / 2)) * (2 * max 1 (b ^ lam) / (1 + ρ)) :=
          mul_le_mul_of_nonneg_left hρR h4
      _ = decayKqOne c C₀ lam b / (1 + ρ) := by rw [decayKqOne]; ring
  calc |ρ ^ 2 * c * G w θ / r|
      ≤ |c| * C₀ * (ρ ^ 2 * (Real.pi / 2 - θ) / r) * R := step1
    _ ≤ |c| * C₀ * (Real.pi / 2) * ρ * R := step2
    _ ≤ decayKqOne c C₀ lam b / (1 + ρ) := step3

end Work.FTS.BSIdentP.Levels
end
-- ===== merged: Submission.Work.FTS_BSIdentP.Slim.TendstoPhiOddNegPi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdentP.Levels

open Work.FTS.BSIdent

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
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
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

end Work.FTS.BSIdentP.Levels
end
