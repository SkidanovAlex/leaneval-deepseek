/-
# `Work.SeedExist.Sides.notMem_interior_of_flower`

**A point of the dynamical plane that carries a Leau–Fatou flower of the second return map
`F c = (T_c)^[10] = (Tsq c)^[5]` is never an interior point of the filled Julia set `K c`.**

Equivalently: the characteristic parabolic point of a root-parabolic parameter lies on the
frontier of `K c`, hence on the Julia set.  This is the dynamical-plane input used by the seed
construction (`Work.SeedExist`): it is what rules out the degenerate case in which the
characteristic point of the wake portrait would sit inside the filled Julia set.

## The mathematics

Let `S = Tsq c = (T_c)^[2]` be the holomorphic quartic second iterate of the antiholomorphic
quadratic `T_c`, so that `F c = S^[5]`.  Suppose `z₁ ∈ interior (K c)`.

1. **The iterates of `S` form a normal family near `z₁`.**  On the open set `interior (K c)`
   every orbit is bounded, and a single escape radius `R` (from `Work.Normal.escapeRadius`)
   bounds *all* the iterates on every point of `K c`; Montel's locally bounded principle
   (`Work.Normal.montel_locallyBounded`) therefore makes the family of iterates
   `{S^[n]}` normal on `interior (K c)`.

2. **A subsequence of the return-map iterates `F^[n] = S^[5n]` converges locally uniformly.**
   The flower supplies an open petal `Pa` accumulating at `z₁` on which the `F`-orbits converge
   to `z₁` (`fl.tendsto_Pa`); the `∞`-alternative of normality is impossible because `z₁` is
   fixed by `F`.  So a subsequence `F^[φ n]` tends locally uniformly on a ball `B (z₁) r` to a
   holomorphic limit `g`.

3. **The limit is the constant `z₁`.**  On `Pa ∩ B` the values `F^[φ n]` converge to `z₁`, so
   `g = z₁` on the (nonempty, open) set `Pa ∩ B`; the identity theorem
   (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) makes `g` constant on the ball `B`.
   Hence `deriv g z₁ = 0`.

4. **But the derivatives cannot converge to `0`.**  Weierstrass' theorem
   (`TendstoLocallyUniformlyOn.deriv`) gives convergence of the derivatives on `B`; while
   `HasDerivAt.iterate` computes `deriv (F^[n]) z₁ = (deriv F z₁)^n`, and the multiplier of the
   second return map at the parabolic point has modulus `1`
   (`Work.FQC.norm_deriv_eq_one_of_flower_data`, which extracts `‖deriv F z₁‖ = 1` from the
   flower data: the petal `Pa` forbids an attracting point, the repelling coordinate `Ψ` forbids
   a repelling one).  So every `deriv (F^[φ n]) z₁` has modulus `1`, contradicting convergence
   to `0`.

No hypothesis beyond the flower and the fixed-point equation is used; in particular the statement
does not require the ray-landing data of the seed.
-/
import Mathlib
import Submission.Work.SeedExist.Setup
import Submission.Work.Normal.All
import Submission.Work.ELPull.tantibar_openMap
import Submission.Work.ELRig.Defs
import Submission.Work.FQC.transfer_parabolic_aux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function Set Metric
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Work.SeedExist.Sides

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## Elementary bridges between the tricorn vocabulary and the normal-family chapter -/

/-- The holomorphic second iterate `Work.Landing.Tsq c` of the tricorn is `TantibarSq c`. -/
theorem tsq_eq_tantibarSq (c : ℂ) : Work.Landing.Tsq c = Work.Normal.TantibarSq c := rfl

/-- **The iterates of the second return map are the `5`-th iterates of the quartic.**
`Work.EL.F c = (Tsq c)^[5]`, so `(F c)^[n] = (Tsq c)^[5 * n]`. -/
theorem F_iterate_eq_TantibarSq (c : ℂ) (n : ℕ) :
    (Work.EL.F c)^[n] = (Work.Normal.TantibarSq c)^[5 * n] := by
  have h : Work.EL.F c = (Work.Normal.TantibarSq c)^[5] := rfl
  rw [h, ← Function.iterate_mul]

/-- `Work.EL.F c` is holomorphic (it is a polynomial of degree `4 ^ 5`). -/
theorem differentiable_F (c : ℂ) : Differentiable ℂ (Work.EL.F c) := by
  rw [Work.EL.F]
  unfold Work.Landing.Tsq
  fun_prop

/-- `Work.Normal.TantibarSq c` is holomorphic. -/
theorem differentiable_tantibarSq (c : ℂ) : Differentiable ℂ (Work.Normal.TantibarSq c) := by
  rw [show Work.Normal.TantibarSq c = Work.Landing.Tsq c from rfl]
  unfold Work.Landing.Tsq
  fun_prop

/-- **A bounded `T_c`-orbit has bounded `TantibarSq c`-orbit** (the even sub-orbit of a bounded
orbit is bounded), in the form needed to apply the escape radius of the quartic. -/
theorem exists_bound_iterate_tantibarSq {c z : ℂ} (h : Work.ParamRays.BoundedOrbit c z) :
    ∃ M : ℝ, ∀ n : ℕ, ‖(Work.Normal.TantibarSq c)^[n] z‖ ≤ M := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M, fun n => ?_⟩
  have h2 := Work.Normal.tantibar_iterate_even c n
  rw [← congrFun h2 z]
  exact hM (2 * n)

/-! ## The petal accumulates at the parabolic point -/

/-- **The attracting petal accumulates at `z₁`.**  Any point of the petal has an `F`-orbit that
stays in the petal, avoids `z₁` and converges to `z₁`; hence there are points of `Pa` at
arbitrarily small positive distance from `z₁`.

(The petal is nonempty by the flower's `Ψ_ends` field: the far ends of the repelling
half-planes lie in `Pa`.) -/
theorem exists_mem_Pa_norm_sub_lt {c z₁ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.EL.F c) ((Tantibar c)^[5]) z₁) :
    ∀ ε : ℝ, 0 < ε → ∃ y ∈ fl.Pa, 0 < ‖y - z₁‖ ∧ ‖y - z₁‖ < ε := by
  intro ε hε
  obtain ⟨R₀, hR₀⟩ := fl.Ψ_ends
  set w : ℂ := ⟨-R₀ - 1, |R₀| + 1⟩ with hw
  have hwre : w.re < -R₀ := by simp [hw]
  have him : w.im = |R₀| + 1 := by simp [hw]
  have hwim : R₀ < |w.im| := by
    have h1 : (0 : ℝ) ≤ |R₀| + 1 := by positivity
    rw [him, abs_of_nonneg h1]
    linarith [le_abs_self R₀]
  have hyPa : fl.Ψ w ∈ fl.Pa := hR₀ w hwre hwim
  have htend : Tendsto (fun n : ℕ => (Work.EL.F c)^[n] (fl.Ψ w)) atTop (nhds z₁) :=
    fl.tendsto_Pa _ hyPa
  have hev : ∀ᶠ n : ℕ in atTop, ‖(Work.EL.F c)^[n] (fl.Ψ w) - z₁‖ < ε := by
    have h1 : Tendsto (fun n : ℕ => (Work.EL.F c)^[n] (fl.Ψ w) - z₁) atTop (nhds (z₁ - z₁)) :=
      htend.sub tendsto_const_nhds
    have h2 : Tendsto (fun n : ℕ => ‖(Work.EL.F c)^[n] (fl.Ψ w) - z₁‖) atTop (nhds 0) := by
      simpa using h1.norm
    filter_upwards [h2.eventually (Iio_mem_nhds hε)] with n hn
    exact hn
  obtain ⟨n, hn⟩ := hev.exists
  have hmem : (Work.EL.F c)^[n] (fl.Ψ w) ∈ fl.Pa := fl.mapsTo_Pa.iterate n hyPa
  refine ⟨(Work.EL.F c)^[n] (fl.Ψ w), hmem, ?_, hn⟩
  rw [norm_pos_iff, sub_ne_zero]
  intro hcon
  rw [hcon] at hmem
  exact fl.z₀_not_mem hmem

/-! ## The multiplier of the second return map at the parabolic point has modulus `1` -/

/-- **`‖deriv (F c) z₁‖ = 1`.**  This is the topological characterisation of a parabolic germ
already available in the workspace (`Work.FQC.norm_deriv_eq_one_of_flower_data`): the petal
`Pa` rules out an attracting point (its orbits converge to `z₁` although the petal misses `z₁`),
and the repelling coordinate `Ψ`, whose backward iterates accumulate at `z₁` while their
forward iterates stay put, rules out a repelling one. -/
theorem norm_deriv_F_eq_one_of_flower {c z₁ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.EL.F c) ((Tantibar c)^[5]) z₁)
    (hfix : Work.EL.F c z₁ = z₁) :
    ‖deriv (Work.EL.F c) z₁‖ = 1 :=
  Work.FQC.norm_deriv_eq_one_of_flower_data hfix (differentiable_F c).differentiableAt
    fl.z₀_not_mem fl.mapsTo_Pa fl.tendsto_Pa (exists_mem_Pa_norm_sub_lt fl)
    fl.Ψ_shift fl.Ψ_small

/-! ## The main theorem -/

theorem notMem_interior_of_flower {c z₁ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) z₁)
    (hfix : Work.EL.F c z₁ = z₁) :
    z₁ ∉ interior (Work.EL.K c) := by
  intro hzint
  -- the escape radius of the quartic, and the resulting uniform bound on `K c`
  obtain ⟨R, hR2, hRdouble, hKeq, -, -, -, -⟩ :=
    Work.Normal.escapeRadius (d := 4) (f := Work.Normal.TantibarSq c) (by norm_num)
      (Work.Normal.isPolynomialMapOfDegree_tantibarSq c)
  -- **(1)** Montel: the iterates of the quartic are normal on `interior (K c)`
  have hnorm : Work.Normal.IsNormalFamily (Work.Normal.iterateFamily (Work.Normal.TantibarSq c))
      (interior (Work.EL.K c)) := by
    refine Work.Normal.montel_locallyBounded isOpen_interior ?_ ?_
    · rintro f ⟨n, rfl⟩
      exact ((differentiable_tantibarSq c).iterate n).differentiableOn
    · intro K' hK'sub hK'c
      refine ⟨max R 0, ?_⟩
      rintro f ⟨n, rfl⟩ z hz
      have hzK : Work.ParamRays.BoundedOrbit c z :=
        interior_subset (s := Work.EL.K c) (hK'sub hz)
      obtain ⟨M, hM⟩ := exists_bound_iterate_tantibarSq hzK
      have hzFJ : z ∈ Work.Normal.FilledJuliaSet (Work.Normal.TantibarSq c) := ⟨M, hM⟩
      rw [hKeq] at hzFJ
      exact le_trans (hzFJ n) (le_max_left _ _)
  obtain ⟨r, hr0, hrU⟩ := Metric.isOpen_iff.mp isOpen_interior z₁ hzint
  have hnorm_ball : Work.Normal.IsNormalFamily (Work.Normal.iterateFamily (Work.Normal.TantibarSq c))
      (Metric.ball z₁ r) := hnorm.mono hrU
  have hz₁ball : z₁ ∈ Metric.ball z₁ r := Metric.mem_ball_self hr0
  have hmem_iter : ∀ n : ℕ,
      (Work.EL.F c)^[n] ∈ Work.Normal.iterateFamily (Work.Normal.TantibarSq c) :=
    fun n => ⟨5 * n, (F_iterate_eq_TantibarSq c n).symm⟩
  -- **(2)** extract a locally uniformly convergent subsequence of the return-map iterates
  obtain ⟨φ, hφ, hlim | hlim⟩ := hnorm_ball (fun n => (Work.EL.F c)^[n]) hmem_iter
  · -- **(3) and (4)** a holomorphic limit is impossible
    obtain ⟨g, hg⟩ := hlim
    have hgdiff : DifferentiableOn ℂ g (Metric.ball z₁ r) :=
      hg.differentiableOn
        (Eventually.of_forall fun n => ((differentiable_F c).iterate (φ n)).differentiableOn)
        isOpen_ball
    have hgan : AnalyticOnNhd ℂ g (Metric.ball z₁ r) := hgdiff.analyticOnNhd isOpen_ball
    -- the limit equals `z₁` on `Pa ∩ ball`
    have hg_eq : ∀ z ∈ Metric.ball z₁ r ∩ fl.Pa, g z = z₁ := by
      rintro z ⟨hzball, hzPa⟩
      have h1 : Tendsto (fun n => (Work.EL.F c)^[φ n] z) atTop (nhds (g z)) := hg.tendsto_at hzball
      have h2 : Tendsto (fun n => (Work.EL.F c)^[φ n] z) atTop (nhds z₁) :=
        (fl.tendsto_Pa z hzPa).comp hφ.tendsto_atTop
      exact tendsto_nhds_unique h1 h2
    obtain ⟨y, hyPa, hyne, hyr⟩ := exists_mem_Pa_norm_sub_lt fl r hr0
    have hyball : y ∈ Metric.ball z₁ r := by
      rw [Metric.mem_ball, dist_eq_norm]; exact hyr
    -- the identity theorem on the ball
    have hO : Metric.ball z₁ r ∩ fl.Pa ∈ 𝓝 y :=
      (isOpen_ball.inter fl.isOpen_Pa).mem_nhds ⟨hyball, hyPa⟩
    have hev : g =ᶠ[𝓝 y] (fun _ : ℂ => z₁) :=
      Filter.eventuallyEq_of_mem hO fun z hz => hg_eq z hz
    have heqOn : EqOn g (fun _ : ℂ => z₁) (Metric.ball z₁ r) :=
      hgan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
        (convex_ball z₁ r).isPreconnected hyball hev
    have hderiv_g : deriv g z₁ = 0 := by
      have hev2 : g =ᶠ[𝓝 z₁] (fun _ : ℂ => z₁) :=
        Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds z₁ hr0) fun z hz => heqOn hz
      rw [hev2.deriv_eq, deriv_const]
    -- the derivatives of the subsequence all have modulus `1`
    have hderivF1 : ‖deriv (Work.EL.F c) z₁‖ = 1 := norm_deriv_F_eq_one_of_flower fl hfix
    have hmod : ∀ n : ℕ, ‖deriv ((Work.EL.F c)^[φ n]) z₁‖ = 1 := by
      intro n
      have hdF : HasDerivAt (Work.EL.F c) (deriv (Work.EL.F c) z₁) z₁ :=
        (differentiable_F c).differentiableAt.hasDerivAt
      have h1 : HasDerivAt ((Work.EL.F c)^[φ n]) ((deriv (Work.EL.F c) z₁) ^ (φ n)) z₁ :=
        HasDerivAt.iterate z₁ hdF hfix (φ n)
      rw [h1.deriv, norm_pow, hderivF1, one_pow]
    -- Weierstrass: the derivatives converge to the derivative of the limit
    have hconv : TendstoLocallyUniformlyOn (fun n => deriv ((Work.EL.F c)^[φ n])) (deriv g) atTop
        (Metric.ball z₁ r) :=
      hg.deriv
        (Eventually.of_forall fun n => ((differentiable_F c).iterate (φ n)).differentiableOn)
        isOpen_ball
    have h0 : Tendsto (fun n => deriv ((Work.EL.F c)^[φ n]) z₁) atTop (nhds 0) := by
      have h3 := hconv.tendsto_at hz₁ball
      simpa [hderiv_g] using h3
    obtain ⟨n, hn⟩ := (h0.eventually (Metric.ball_mem_nhds (0 : ℂ) one_pos)).exists
    have hlt : ‖deriv ((Work.EL.F c)^[φ n]) z₁‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hn
    rw [hmod n] at hlt
    exact lt_irrefl 1 hlt
  · -- the `∞`-alternative is impossible because `z₁` is fixed by `F`
    obtain ⟨N, hN⟩ :=
      hlim {z₁} (by intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; exact hz₁ball)
        isCompact_singleton (‖z₁‖ + 1)
    have h1 := hN N le_rfl z₁ (Set.mem_singleton z₁)
    dsimp only at h1
    rw [Function.iterate_fixed hfix (φ N)] at h1
    linarith

end Work.SeedExist.Sides
