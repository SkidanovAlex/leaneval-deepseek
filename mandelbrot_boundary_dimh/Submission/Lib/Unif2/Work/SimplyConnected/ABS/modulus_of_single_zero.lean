import Mathlib
import Submission.Lib.Unif2.ModulusAbsorb
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs
import Submission.Lib.Unif2.SweepMember
import Submission.Lib.Unif2.Work.Potential.removable_singularity_of_bounded_near
import Submission.Lib.Unif2.Work.Potential.removable_singularity_bounded_harmonic

/-!
# The holomorphic modulus from a holomorphic function with a single simple zero

`Submission.exists_holomorphic_modulus` (`Submission/ModulusAbsorb.lean`) constructs the holomorphic
modulus `Φ` of a potential `E` from

* a holomorphic `g` with a single simple zero at the pole `z₀`,
* the **harmonicity of `E + log ‖g‖` on all of `X`** -- an input there, not a consequence.

This file supplies that missing input.  Because the logarithmic pole of `E` at `x₀` is exactly
cancelled by the simple zero of `g`, the function `u := E + log ‖g‖` is harmonic on `X ∖ {x₀}` and
bounded near `x₀`, so it extends to a harmonic function on `X`
(`Work.Potential.removable_singularity_of_bounded_near`).  This is
`harmonicOnX_add_log_norm_of_singleZero` below.

Since `E + log ‖g‖` has a *removable* singularity at `x₀`, its value at `x₀` in Lean (`Real.log 0 = 0`)
need not agree with its limit there, so the extension is not the literal function.  The second
statement `exists_modulus_of_harmonic_add_log_norm` is therefore the form of
`Submission.exists_holomorphic_modulus` in which the harmonicity is supplied through the extension.

Combining the two gives `exists_modulus_of_singleSimpleZero`: from a holomorphic `g` with a single
*simple* zero at `x₀` and no other zeros, and `Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)`
(used to produce the global harmonic conjugate), there is `Φ` holomorphic on `X` with `Φ x₀ = 0`, a
simple zero at `x₀` and `‖Φ x‖ = exp (-(E x))` for `x ≠ x₀`.

The zero-fibre target `Work.SimplyConnected.ABS.extremal_maximizer_zero_fiber` consumes this in the
form `extremal_maximizer_zero_fiber_of_singleZeroFunction`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Filter Set
open Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Boundedness of `E + log ‖g‖` near the pole.**

If `E` has a unit logarithmic pole at `x₀` (`HasLogPoleOn`) and `g` is holomorphic with a *simple*
zero there (given in the preferred chart as `g ∘ c.symm = (w - a) * H w` with `H` analytic and
`H a ≠ 0`), then `E + log ‖g‖` is bounded in a punctured neighbourhood of `x₀`: the two logarithmic
singularities cancel. -/
theorem bounded_near_pole_add_log_norm {x₀ : X} {E : X → ℝ} {g : X → ℂ}
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {x₀}) x₀ E)
    (hgsimple : ∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ x₀) x₀) ∧ H ((chartAt ℂ x₀) x₀) ≠ 0 ∧
      Filter.EventuallyEq (nhds ((chartAt ℂ x₀) x₀)) (g ∘ (chartAt ℂ x₀).symm)
        (fun w : ℂ => (w - (chartAt ℂ x₀) x₀) * H w)) :
    ∃ M : ℝ, ∃ W : Set X, W ∈ 𝓝 x₀ ∧ ∀ x ∈ W, x ≠ x₀ → |E x + Real.log ‖g x‖| ≤ M := by
  classical
  have hsrc : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
  -- ## the data of the pole and of the simple zero
  obtain ⟨C, V, hVnhds, hVbnd⟩ := hpole
  obtain ⟨H, hHana, hHne, hHeq⟩ := hgsimple
  have hHa : 0 < ‖H ((chartAt ℂ x₀) x₀)‖ := norm_pos_iff.mpr hHne
  have hHcont : ContinuousAt (fun w : ℂ => ‖H w‖) ((chartAt ℂ x₀) x₀) := hHana.continuousAt.norm
  -- a neighbourhood of the pole on which `log ‖H ·‖` is bounded
  have hlt₁ : ∀ᶠ w in nhds ((chartAt ℂ x₀) x₀),
      ‖H ((chartAt ℂ x₀) x₀)‖ / 2 < ‖H w‖ :=
    hHcont.eventually (isOpen_Ioi.mem_nhds (x := ‖H ((chartAt ℂ x₀) x₀)‖)
      (by simp only [Set.mem_Ioi]; linarith [hHa]))
  have hlt₂ : ∀ᶠ w in nhds ((chartAt ℂ x₀) x₀),
      ‖H w‖ < 2 * ‖H ((chartAt ℂ x₀) x₀)‖ :=
    hHcont.eventually (isOpen_Iio.mem_nhds (x := ‖H ((chartAt ℂ x₀) x₀)‖)
      (by simp only [Set.mem_Iio]; linarith [hHa]))
  have hpre : ∀ᶠ w in nhds ((chartAt ℂ x₀) x₀),
      ‖H ((chartAt ℂ x₀) x₀)‖ / 2 < ‖H w‖ ∧
      ‖H w‖ < 2 * ‖H ((chartAt ℂ x₀) x₀)‖ ∧
      g ((chartAt ℂ x₀).symm w) = (w - (chartAt ℂ x₀) x₀) * H w :=
    hlt₁.and (hlt₂.and hHeq)
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := Metric.eventually_nhds_iff.mp hpre
  -- a radius inside the chart target
  obtain ⟨r, hrpos, hrsub⟩ : ∃ r : ℝ, 0 < r ∧
      Metric.ball ((chartAt ℂ x₀) x₀) r ⊆ (chartAt ℂ x₀).target :=
    Metric.mem_nhds_iff.mp ((chartAt ℂ x₀).open_target.mem_nhds
      ((chartAt ℂ x₀).map_source hsrc))
  set ρ : ℝ := min ε₀ r with hρdef
  have hρpos : 0 < ρ := lt_min hε₀pos hrpos
  have hρε : ρ ≤ ε₀ := min_le_left _ _
  have hρr : ρ ≤ r := min_le_right _ _
  have hballtgt : Metric.ball ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target :=
    (Metric.ball_subset_ball hρr).trans hrsub

  -- ## boundedness of `u` near `x₀`
  refine ⟨C + (|Real.log (‖H ((chartAt ℂ x₀) x₀)‖ / 2)| +
        |Real.log (2 * ‖H ((chartAt ℂ x₀) x₀)‖)|),
      (chartAt ℂ x₀).symm '' Metric.ball ((chartAt ℂ x₀) x₀) ρ ∩ V, ?_, ?_⟩
  · -- the neighbourhood
    refine Filter.inter_mem ?_ hVnhds
    have himg : IsOpen ((chartAt ℂ x₀).symm '' Metric.ball ((chartAt ℂ x₀) x₀) ρ) :=
      (chartAt ℂ x₀).isOpen_image_symm_of_subset_target Metric.isOpen_ball hballtgt
    exact himg.mem_nhds ⟨_, Metric.mem_ball_self hρpos, (chartAt ℂ x₀).left_inv hsrc⟩
  · -- the bound
    intro x hx hxne
    obtain ⟨⟨w, hw, rfl⟩, hxV⟩ := hx
    have hwdist : dist w ((chartAt ℂ x₀) x₀) < ε₀ :=
      lt_of_lt_of_le (by simpa [Metric.mem_ball] using hw) hρε
    obtain ⟨h1, h2, h3⟩ := hε₀ (y := w) hwdist
    have hne : (chartAt ℂ x₀).symm w ≠ x₀ := hxne
    have hwa : w ≠ (chartAt ℂ x₀) x₀ := by
      intro h
      exact hne (by rw [h, (chartAt ℂ x₀).left_inv hsrc])
    have hwtgt : w ∈ (chartAt ℂ x₀).target := hballtgt hw
    have hcw : (chartAt ℂ x₀) ((chartAt ℂ x₀).symm w) = w := (chartAt ℂ x₀).right_inv hwtgt
    -- the pole estimate for `E`
    have hpole2 : |E ((chartAt ℂ x₀).symm w) + Real.log ‖w - (chartAt ℂ x₀) x₀‖| ≤ C := by
      have h0 := hVbnd ((chartAt ℂ x₀).symm w) hxV ⟨Set.mem_univ _, hne⟩ hne
      rwa [hcw] at h0
    -- `log ‖g‖ = log ‖w - a‖ + log ‖H w‖`
    have hHpos : 0 < ‖H w‖ := lt_of_lt_of_le (half_pos hHa) h1.le
    have hgl : Real.log ‖g ((chartAt ℂ x₀).symm w)‖
        = Real.log ‖w - (chartAt ℂ x₀) x₀‖ + Real.log ‖H w‖ := by
      have hnorm : ‖g ((chartAt ℂ x₀).symm w)‖ = ‖w - (chartAt ℂ x₀) x₀‖ * ‖H w‖ := by
        rw [h3, norm_mul]
      conv_lhs => rw [hnorm]
      exact Real.log_mul (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hwa)) (ne_of_gt hHpos)
    have hHbound : |Real.log ‖H w‖|
        ≤ |Real.log (‖H ((chartAt ℂ x₀) x₀)‖ / 2)| +
          |Real.log (2 * ‖H ((chartAt ℂ x₀) x₀)‖)| := by
      have hlog1 : Real.log (‖H ((chartAt ℂ x₀) x₀)‖ / 2) ≤ Real.log ‖H w‖ :=
        Real.log_le_log (half_pos hHa) h1.le
      have hlog2 : Real.log ‖H w‖ ≤ Real.log (2 * ‖H ((chartAt ℂ x₀) x₀)‖) :=
        Real.log_le_log hHpos h2.le
      have hA : -(|Real.log (‖H ((chartAt ℂ x₀) x₀)‖ / 2)| +
          |Real.log (2 * ‖H ((chartAt ℂ x₀) x₀)‖)|) ≤ Real.log ‖H w‖ := by
        linarith [neg_abs_le (Real.log (‖H ((chartAt ℂ x₀) x₀)‖ / 2)), hlog1,
          abs_nonneg (Real.log (2 * ‖H ((chartAt ℂ x₀) x₀)‖))]
      have hB : Real.log ‖H w‖ ≤ |Real.log (‖H ((chartAt ℂ x₀) x₀)‖ / 2)| +
          |Real.log (2 * ‖H ((chartAt ℂ x₀) x₀)‖)| := by
        linarith [le_abs_self (Real.log (2 * ‖H ((chartAt ℂ x₀) x₀)‖)), hlog2,
          abs_nonneg (Real.log (‖H ((chartAt ℂ x₀) x₀)‖ / 2))]
      exact abs_le.mpr ⟨hA, hB⟩
    rw [hgl]
    have hsplit : E ((chartAt ℂ x₀).symm w)
        + (Real.log ‖w - (chartAt ℂ x₀) x₀‖ + Real.log ‖H w‖)
        = (E ((chartAt ℂ x₀).symm w) + Real.log ‖w - (chartAt ℂ x₀) x₀‖) + Real.log ‖H w‖ := by
      ring
    rw [hsplit]
    linarith [abs_add_le (E ((chartAt ℂ x₀).symm w) + Real.log ‖w - (chartAt ℂ x₀) x₀‖)
        (Real.log ‖H w‖), hHbound, (abs_le.mp hpole2).1, (abs_le.mp hpole2).2]

theorem harmonicOnX_add_log_norm_of_singleZero {x₀ : X} {E : X → ℝ} {g : X → ℂ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {x₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {x₀}) x₀ E)
    (hg : Submission.HolomorphicOnX g Set.univ) (hgne : ∀ x : X, x ≠ x₀ → g x ≠ 0)
    (hgsimple : ∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ x₀) x₀) ∧ H ((chartAt ℂ x₀) x₀) ≠ 0 ∧
      Filter.EventuallyEq (nhds ((chartAt ℂ x₀) x₀)) (g ∘ (chartAt ℂ x₀).symm)
        (fun w : ℂ => (w - (chartAt ℂ x₀) x₀) * H w)) :
    ∃ U : X → ℝ, Submission.HarmonicOnX U Set.univ ∧
      ∀ x : X, x ≠ x₀ → U x = E x + Real.log ‖g x‖ := by
  classical
  have hu : Submission.HarmonicOnX (fun x : X => E x + Real.log ‖g x‖) (Set.univ \ {x₀}) := by
    intro x hx
    have h1 : Submission.HarmonicOnXAt E x := hEharm x hx
    have h2 : Submission.HarmonicOnXAt (fun y : X => Real.log ‖g y‖) x :=
      Submission.harmonicOnXAt_log_norm (hg x (Set.mem_univ x)) (hgne x hx.2)
    exact h1.add h2
  obtain ⟨M, W, hW, hbnd⟩ := bounded_near_pole_add_log_norm hpole hgsimple
  exact Work.Potential.removable_singularity_of_bounded_near hu ⟨M, W, hW, hbnd⟩

/-- **The holomorphic modulus from a harmonic extension of `E + log ‖g‖`.**

This is `Submission.exists_holomorphic_modulus` with the harmonicity of the *literal* function
`E + log ‖g‖` replaced by a harmonic function `K` on `X` agreeing with it off the pole.  This is the
form in which `harmonicOnX_add_log_norm_of_singleZero` delivers the input: the literal function has
a removable singularity at the pole, and its value there in Lean (`Real.log 0 = 0`) need not agree
with its limit. -/
theorem exists_modulus_of_harmonic_add_log_norm {x₀ z₀ : X} {E : X → ℝ} {g : X → ℂ} {K : X → ℝ}
    (hg : Submission.HolomorphicOnX g Set.univ) (hg_ne : ∀ x : X, x ≠ z₀ → g x ≠ 0)
    (hK : Submission.HarmonicOnX K Set.univ)
    (hKeq : ∀ x : X, x ≠ z₀ → K x = E x + Real.log ‖g x‖)
    (hgpole : Submission.HasLogPoleAt z₀ g)
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)] :
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧ Submission.HasLogPoleAt z₀ Φ ∧
      ∀ x : X, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)) := by
  classical
  obtain ⟨F, hFhol, hFre⟩ := Submission.exists_holomorphicOnX_re_of_harmonic x₀ hK
  have hFana : AnalyticAt ℂ (F ∘ (chartAt ℂ z₀).symm) ((chartAt ℂ z₀) z₀) :=
    hFhol z₀ (Set.mem_univ z₀)
  have hpole2 : Submission.HasLogPoleAt z₀ (fun x => g x * Complex.exp (-(F x))) := by
    obtain ⟨H, hHana, hHne, hev⟩ := hgpole
    have hexpana : AnalyticAt ℂ
        (fun w : ℂ => Complex.exp (-(F ((chartAt ℂ z₀).symm w)))) ((chartAt ℂ z₀) z₀) :=
      (hFana.neg).cexp
    refine ⟨fun w : ℂ => H w * Complex.exp (-(F ((chartAt ℂ z₀).symm w))), ?_, ?_, ?_⟩
    · exact hHana.mul hexpana
    · exact mul_ne_zero hHne (Complex.exp_ne_zero _)
    · filter_upwards [hev] with w hw
      show g ((chartAt ℂ z₀).symm w) * Complex.exp (-(F ((chartAt ℂ z₀).symm w)))
        = (w - (chartAt ℂ z₀) z₀) * (H w * Complex.exp (-(F ((chartAt ℂ z₀).symm w))))
      simp only [Function.comp_apply] at hw
      rw [hw]
      ring
  refine ⟨fun x => g x * Complex.exp (-(F x)), ?_, hpole2, ?_⟩
  · refine Submission.HolomorphicOnX.mul hg ?_
    intro x _
    exact Submission.HolomorphicOnXAt.cexp_neg (hFhol x (Set.mem_univ x))
  · intro x hx
    have hgx : g x ≠ 0 := hg_ne x hx
    have hgp : 0 < ‖g x‖ := norm_pos_iff.mpr hgx
    have hnorm : ‖Complex.exp (-(F x))‖ = Real.exp (-(K x)) := by
      rw [Complex.norm_exp, Complex.neg_re, hFre x]
    have hexp : Real.exp (-(K x)) = Real.exp (-(E x)) / ‖g x‖ := by
      have h1 : -(K x) = -(E x) + -(Real.log ‖g x‖) := by rw [hKeq x hx]; ring
      rw [h1, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hgp, div_eq_mul_inv]
    rw [norm_mul, hnorm, hexp]
    field_simp

/-- **The holomorphic modulus from a holomorphic function with a single simple zero.**

If `E` is harmonic on `X ∖ {x₀}` with a unit logarithmic pole at `x₀`, if `g` is holomorphic on `X`
with a single *simple* zero at `x₀` (`Submission.HasLogPoleAt x₀ g`) and no other zeros, and if the fundamental
group of `X` has no non-trivial homomorphism to `ℝ`, then `E` has a holomorphic modulus `Φ`:
holomorphic on `X`, with a simple zero at `x₀` and `‖Φ x‖ = exp (-(E x))` off `x₀`. -/
theorem exists_modulus_of_singleSimpleZero {x₀ : X} {E : X → ℝ} {g : X → ℂ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {x₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {x₀}) x₀ E)
    (hg : Submission.HolomorphicOnX g Set.univ) (hgne : ∀ x : X, x ≠ x₀ → g x ≠ 0)
    (hgsimple : ∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ x₀) x₀) ∧ H ((chartAt ℂ x₀) x₀) ≠ 0 ∧
      Filter.EventuallyEq (nhds ((chartAt ℂ x₀) x₀)) (g ∘ (chartAt ℂ x₀).symm)
        (fun w : ℂ => (w - (chartAt ℂ x₀) x₀) * H w))
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)] :
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧ Φ x₀ = 0 ∧
      (∀ x : X, x ≠ x₀ → ‖Φ x‖ = Real.exp (-(E x))) ∧
      (∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ x₀) x₀) ∧ H ((chartAt ℂ x₀) x₀) ≠ 0 ∧
        Filter.EventuallyEq (nhds ((chartAt ℂ x₀) x₀)) (Φ ∘ (chartAt ℂ x₀).symm)
          (fun w : ℂ => (w - (chartAt ℂ x₀) x₀) * H w)) := by
  classical
  obtain ⟨K, hKharm, hKeq⟩ :=
    harmonicOnX_add_log_norm_of_singleZero (x₀ := x₀) hEharm hpole hg hgne hgsimple
  obtain ⟨Φ, hΦhol, hΦpole, hΦmod⟩ :=
    exists_modulus_of_harmonic_add_log_norm (x₀ := x₀) (z₀ := x₀) hg hgne hKharm hKeq hgsimple
  exact ⟨Φ, hΦhol, Submission.phi_zero_of_logPole hΦhol hΦpole, hΦmod, hΦpole⟩

end Work.SimplyConnected.ABS
