/-
Copyright: subproject `Submission/Work/FBif/` of `mandelbar_not_path_connected`.

# `Work.FBif` — the gluing datum, constructed (FBif, part 3d)

This module *constructs* the gluing datum `Work.FBif.GluingDatum` for the C¹ gluing of the
perturbation `f_ε = perturb c q ε` with the model `T_c`, thereby removing the last hypothesis of
the area: the gluing construction stops being an assumption and becomes a theorem.

The route is exactly the one described in `FBif/Glue.lean`:

* `F = glueMap c q ε (cutoff c)` is the C¹ interpolation of the perturbation with `T_c` outside
  the ball of radius `farRad c`, built from the smooth radial cutoff `cutoff c`;
* `μ = glueMu F (farRad c)` is the invariant Beltrami coefficient obtained by pulling back `0`
  along the orbits until they hit the far ball;
* the estimates of `FBif/glueMap_estimates.lean` provide the escape of the outer region, the
  vanishing of `∂F` inside the inner ball and outside the cut ball, and the bound
  `‖∂F‖ ≤ κ ‖∂̄F‖` with `κ = ε Q K_χ / innerRad`; hence (`FBif/norm_glueMu_le.lean`)
  `‖μ‖ ≤ κ` and (`FBif/badSet_locallyFinite.lean`) the bad set of `F` is discrete;
* `Work.FBif.glueMu_invariant` gives the invariance `μ = pullRev μ F`, and MRMT `M1`
  (`FBif/principal_decay_bound.lean`) gives the quantitative decay of `principal μ` with
  constant `≤ 4 κ (farRad c + 1)² ≤ ε`;
* the orbit neighbourhood `FBif/exists_orbit_in_ball.lean` gives the fifth-iterate agreement with
  the perturbation near the parabolic point.

The perturbation coefficient `q` is rescaled by a constant `lam > 0` chosen in the proof; the
rescaled coefficient is `fun z => lam * q z`.  Since `perturb c (lam • q) ε = perturb c q (lam ε)`
and `GoodPerturbation`/`HSEstimate` are invariant under positive rescaling
(`FBif/goodPerturbation_const_mul.lean`, `FBif/hsEstimate_const_mul.lean`), the assembly
`Work.FBif.bifSide` in `FBif/Main.lean` may use the rescaled perturbation.
-/
import Mathlib
import Submission.Work.FBif.Glue
import Submission.Work.FBif.cutoff_props
import Submission.Work.FBif.escR_props
import Submission.Work.FBif.radius_numerics
import Submission.Work.FBif.antipoly_wirtinger
import Submission.Work.FBif.glue_derivs
import Submission.Work.FBif.continuous_deriv_glueMap
import Submission.Work.FBif.norm_glueMap_sub_le
import Submission.Work.FBif.glueMap_estimates
import Submission.Work.FBif.pullRev_le
import Submission.Work.FBif.measurable_glueMu
import Submission.Work.FBif.glueMu_invariant
import Submission.Work.FBif.norm_glueMu_le
import Submission.Work.FBif.support_glueMu_subset
import Submission.Work.FBif.badSet_locallyFinite
import Submission.Work.FBif.natDegree_ge_three
import Submission.Work.FBif.deriv_linear_ne_zero
import Submission.Work.FBif.exists_bound_on_closedBall
import Submission.Work.FBif.exists_orbit_in_ball
import Submission.Work.FBif.goodPerturbation_const_mul
import Submission.Work.FBif.principal_decay_bound
import Submission.Work.FBif.glue_constants
import Submission.Work.FBif.MRMTInput

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function MeasureTheory
open scoped Topology ENNReal

set_option maxHeartbeats 4000000

noncomputable section

namespace Work.FBif

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The far radius of the datum -/

theorem datumRad_spec (c : ℂ) :
    datumRad c = max (2 * (farRad c + 1)) 1 ∧ 0 < datumRad c ∧
      farRad c ≤ datumRad c ∧ cutRad c < datumRad c := by
  obtain ⟨hfar0, hinner0, hcut0, hlt_inner_cut, hlt_cut_far, hescR_inner, hinner_sq, hcut_sq⟩ :=
    radius_numerics c
  have h1 : (1 : ℝ) ≤ 2 * (farRad c + 1) := by linarith
  have hD : datumRad c = 2 * (farRad c + 1) := rfl
  have hmax : max (2 * (farRad c + 1)) 1 = 2 * (farRad c + 1) := max_eq_left h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hD, hmax]
  · rw [hD]; linarith
  · rw [hD]; linarith
  · rw [hD]; linarith

/-! ## The gluing datum -/

/-- **The gluing datum exists**, after rescaling the perturbation coefficient.

For every perturbation `q` of HS type there is a positive rescaling `lam` such that, for all
sufficiently small `ε > 0`, the glued map `glueMap c (lam • q) ε (cutoff c)` with its invariant
coefficient `glueMu` is a `GluingDatum` — provided the parabolic point is of exact period `5`
(the hypotheses `hper`, `hne` are supplied by `Work.EL.RootParabolic`). -/
theorem exists_gluingDatum_scaled (c z₁ : ℂ) (q : ℂ → ℂ) (hgood : GoodPerturbation c z₁ q)
    (hper : (Tantibar c)^[5] z₁ = z₁)
    (hne : ∀ k ∈ Finset.Ioo 0 5, (Tantibar c)^[k] z₁ ≠ z₁) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ δ' > 0, ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Nonempty (GluingDatum c z₁ (fun z => (lam : ℂ) * q z) δ' (datumRad c) ε) := by
  classical
  have hgood0 : GoodPerturbation c z₁ q := hgood
  obtain ⟨P, hqP, hdiv, hdiv4, hqz4⟩ := hgood0
  have hq_cont : Continuous q := Antipoly.continuous ⟨P, hqP⟩
  obtain ⟨hχcd, hχ1, hχ0, hχb, hdzinc, hdzoutc, Kχ, hKχ0, hKχ⟩ := cutoff_props c
  have hKχ' : ∀ z : ℂ, ‖Work.MRMT.dz (realCoe (cutoff c)) z‖ ≤ Kχ := fun z => (hKχ z).1
  obtain ⟨hfar0, hinner0, hcut0, hlt_inner_cut, hlt_cut_far, hescR_inner, hinner_sq, hcut_sq⟩ :=
    radius_numerics c
  obtain ⟨hdatum_eq, hdatum_pos, hfar_le_datum, hcut_lt_datum⟩ := datumRad_spec c
  -- bounds for the perturbation
  have hdzbarq_cont : Continuous (fun z : ℂ => Work.MRMT.dzbar q z) := by
    have h : (fun z : ℂ => Work.MRMT.dzbar q z) = fun z : ℂ => P.derivative.eval (star z) :=
      funext (antipoly_wirtinger hqP).2.2
    rw [h]
    exact (Polynomial.continuous P.derivative).comp continuous_star
  obtain ⟨Q₀, hQ₀0, hQ₀⟩ := exists_bound_on_closedBall hq_cont (cutRad c)
  obtain ⟨Q₁, hQ₁0, hQ₁⟩ := exists_bound_on_closedBall hdzbarq_cont (cutRad c)
  -- the rescaling and the small parameters
  obtain ⟨lam, hlam0, hQ_le_one, hQK_small, hX, ε₀, hε₀, hfacts⟩ :=
    glue_constants c hQ₀0 hQ₁0 hKχ0
  -- the rescaled coefficient
  have hq'_good : GoodPerturbation c z₁ (fun z => (lam : ℂ) * q z) :=
    goodPerturbation_const_mul hgood (ne_of_gt hlam0)
  have hq'_anti : Antipoly (fun z => (lam : ℂ) * q z) := hq'_good.anti
  have hq'_cont : Continuous (fun z => (lam : ℂ) * q z) := continuous_const.mul hq_cont
  obtain ⟨P', hq'P', hdiv', hdiv4', hqz4'⟩ := hq'_good
  have hP'0 : ¬ (P' = 0) := by
    intro h0
    have : (fun z => (lam : ℂ) * q z) (cyclePt c z₁ 4) = 0 := by
      rw [hq'P']; simp [h0]
    exact hqz4' this
  have hnorm_lam : ‖(lam : ℂ)‖ = lam := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0]
  have hQ : ∀ z : ℂ, ‖z‖ ≤ cutRad c → ‖(fun w => (lam : ℂ) * q w) z‖ ≤ lam * Q₀ := by
    intro z hz
    show ‖(lam : ℂ) * q z‖ ≤ lam * Q₀
    rw [norm_mul, hnorm_lam]
    exact mul_le_mul_of_nonneg_left (hQ₀ z hz) hlam0.le
  have hQ' : ∀ z : ℂ, ‖z‖ ≤ cutRad c →
      ‖Work.MRMT.dzbar (fun w => (lam : ℂ) * q w) z‖ ≤ lam * Q₁ := by
    intro z hz
    have hP'' : ∀ w : ℂ,
        (fun w => (lam : ℂ) * q w) w = (Polynomial.C (lam : ℂ) * P).eval (star w) := by
      intro w
      show (lam : ℂ) * q w = (Polynomial.eval (star w)) (Polynomial.C (lam : ℂ) * P)
      rw [Polynomial.eval_mul, Polynomial.eval_C, hqP w]
    have h1 : (Polynomial.C (lam : ℂ) * P).derivative
        = Polynomial.C (lam : ℂ) * P.derivative := Polynomial.derivative_C_mul (lam : ℂ) P
    rw [(antipoly_wirtinger hP'').2.2 z, h1, Polynomial.eval_mul, Polynomial.eval_C, norm_mul,
      hnorm_lam]
    rw [← (antipoly_wirtinger hqP).2.2 z]
    exact mul_le_mul_of_nonneg_left (hQ₁ z hz) hlam0.le
  -- the orbit neighbourhood
  obtain ⟨δ₀, hδ₀pos, εorb, hεorbpos, horb⟩ :=
    exists_orbit_in_ball c z₁ hper hq'_cont hescR_inner
  refine ⟨lam, hlam0, δ₀, hδ₀pos, min ε₀ εorb, lt_min hε₀ hεorbpos, ?_⟩
  intro ε hε0 hεlt
  have hεε₀ : ε < ε₀ := lt_of_lt_of_le hεlt (min_le_left _ _)
  have hε_orb : ε < εorb := lt_of_lt_of_le hεlt (min_le_right _ _)
  obtain ⟨h1, h2, hsmall, hκ_le_eps, hκ_half, hCd_bound⟩ := hfacts ε hε0 hεε₀
  obtain ⟨hesc, hW, hdzin', hdzout', hratio⟩ :=
    glueMap_estimates c hq'_anti hε0.le hQ hKχ' hQ' h1 h2
  have hFcd : ContDiff ℝ 1 (glueMap c (fun z => (lam : ℂ) * q z) ε (cutoff c)) :=
    (glue_derivs c hq'P' ε hχcd).1
  obtain ⟨hFcont, hdzFcont, hdzbFcont⟩ := continuous_deriv_glueMap c hq'_anti hχcd
  -- the coefficient
  have hκ0 : 0 ≤ ε * (lam * Q₀) * Kχ / innerRad c := by positivity
  have hμbound : ∀ z : ℂ,
      ‖glueMu (glueMap c (fun z => (lam : ℂ) * q z) ε (cutoff c)) (farRad c) z‖ ≤
        ε * (lam * Q₀) * Kχ / innerRad c :=
    norm_glueMu_le hdzout' hdzin' hesc hratio hκ0
  -- admissibility
  have hsupp : Function.support
      (glueMu (glueMap c (fun z => (lam : ℂ) * q z) ε (cutoff c)) (farRad c)) ⊆
        Metric.closedBall 0 (datumRad c) :=
    fun z hz => Metric.closedBall_subset_closedBall hfar_le_datum (support_glueMu_subset hW hz)
  have hmeas : Measurable
      (glueMu (glueMap c (fun z => (lam : ℂ) * q z) ε (cutoff c)) (farRad c)) :=
    (measurable_glueMu hFcont.measurable hdzFcont.measurable hdzbFcont.measurable (farRad c)).2
  have hbdd : Bornology.IsBounded (Function.support
      (glueMu (glueMap c (fun z => (lam : ℂ) * q z) ε (cutoff c)) (farRad c))) :=
    Metric.isBounded_closedBall.subset (support_glueMu_subset hW)
  have haeb : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      ‖glueMu (glueMap c (fun z => (lam : ℂ) * q z) ε (cutoff c)) (farRad c) z‖ ≤
        ε * (lam * Q₀) * Kχ / innerRad c :=
    Filter.Eventually.of_forall hμbound
  have hadm : Work.MRMT.Found.Admissible
      (glueMu (glueMap c (fun z => (lam : ℂ) * q z) ε (cutoff c)) (farRad c)) :=
    ⟨hmeas.aestronglyMeasurable, ⟨ε * (lam * Q₀) * Kχ / innerRad c, by linarith [hκ_half], haeb⟩,
      hbdd⟩
  -- the quantitative normalisation of the principal solution
  obtain ⟨Cd, hCd0, hCd_le, hCd_dec⟩ :=
    principal_decay_bound hadm hκ0 (by linarith [hκ_half])
      (support_glueMu_subset hW) haeb
  have hCd_le_eps : Cd ≤ ε := by
    have h4 : 4 * (ε * (lam * Q₀) * Kχ / innerRad c) * (farRad c + 1) ^ 2 = 4 *
        (ε * (lam * Q₀) * Kχ / innerRad c) * (farRad c + 1) ^ 2 := rfl
    linarith [hCd_le, hCd_bound]
  -- the invariance
  have hinv : ∀ z : ℂ, glueMu (glueMap c (fun z => (lam : ℂ) * q z) ε (cutoff c)) (farRad c) z
      = Work.MRMT.Found.pullRev
          (glueMu (glueMap c (fun z => (lam : ℂ) * q z) ε (cutoff c)) (farRad c))
          (glueMap c (fun z => (lam : ℂ) * q z) ε (cutoff c)) z := by
    refine glueMu_invariant (fun z hz => hdzin' z (by
      have hz' : z ∈ Metric.ball 0 (innerRad c) := nonEsc_subset_ball hesc hz
      simpa [Metric.mem_ball, dist_eq_norm] using hz')) (fun z hz => hdzout' z (by
        exact lt_of_lt_of_le hlt_cut_far hz)) hW
  -- the exceptional set
  have hQ0ne : ¬ (Polynomial.C 2 * Polynomial.X + Polynomial.C (ε : ℂ) * P'.derivative = 0) :=
    deriv_linear_ne_zero (natDegree_ge_three hP'0 hper hne hdiv') (by
      intro h0
      exact hε0.ne' (by simpa using h0))
  have hS : ∀ z : ℂ, Filter.Eventually
      (fun w : ℂ => w ∉ badSet (glueMap c (fun z => (lam : ℂ) * q z) ε (cutoff c)))
      (nhdsWithin z {z}ᶜ) :=
    badSet_locallyFinite c hq'P' hε0 hQ0ne hQ hKχ' hQ' hsmall
  have hrev : ∀ z ∉ badSet (glueMap c (fun z => (lam : ℂ) * q z) ε (cutoff c)),
      ‖Work.MRMT.dz (glueMap c (fun z => (lam : ℂ) * q z) ε (cutoff c)) z‖ <
        ‖Work.MRMT.dzbar (glueMap c (fun z => (lam : ℂ) * q z) ε (cutoff c)) z‖ :=
    badSet_hrev
  -- the asymptotic agreement with the model
  have hasymp : ∀ z : ℂ, datumRad c ≤ ‖z‖ →
      glueMap c (fun z => (lam : ℂ) * q z) ε (cutoff c) z = Tantibar c z :=
    fun z hz => glueMap_eq_tantibar hχ0 (le_trans hcut_lt_datum.le hz)
  -- the fifth-iterate agreement near the parabolic point
  have hagree : ∀ z : ℂ, ‖z - z₁‖ ≤ δ₀ →
      ((glueMap c (fun z => (lam : ℂ) * q z) ε (cutoff c))^[5]) z
        = ((perturb c (fun z => (lam : ℂ) * q z) ε)^[5]) z := by
    intro z hz
    have hiter : ∀ k : ℕ, k ≤ 5 →
        ((glueMap c (fun z => (lam : ℂ) * q z) ε (cutoff c))^[k]) z
          = ((perturb c (fun z => (lam : ℂ) * q z) ε)^[k]) z := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
        congr 1
        exact glueMap_eq_perturb hχ1 (by
          have hb := horb ε hε0 hε_orb z hz k (by omega)
          simpa using hb)
    exact hiter 5 le_rfl
  exact ⟨{ F := glueMap c (fun z => (lam : ℂ) * q z) ε (cutoff c)
           μ := glueMu (glueMap c (fun z => (lam : ℂ) * q z) ε (cutoff c)) (farRad c)
           adm := hadm
           hR := hdatum_pos
           supp := hsupp
           small := ⟨ε * (lam * Q₀) * Kχ / innerRad c, hκ0, hκ_le_eps, haeb⟩
           decay := ⟨Cd, hCd0, hCd_le_eps, fun z hz => by
             rw [hdatum_eq] at hz
             exact hCd_dec z hz⟩
           contDiff := hFcd
           S := badSet (glueMap c (fun z => (lam : ℂ) * q z) ε (cutoff c))
           hS := hS
           hrev := hrev
           hinv := Filter.Eventually.of_forall hinv
           asymp := hasymp
           agree5 := hagree }⟩

end Work.FBif

end
