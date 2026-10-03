import Mathlib
import Submission.Lib.Unif2.Work.Parabolic.All
import Submission.Lib.Unif2.Work.Modulus.Main
import Submission.Lib.Unif2.Work.UnitGreen.Defs
import Submission.Lib.Unif2.Helpers
import Submission.Lib.Unif2.Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic
import Submission.Lib.Unif2.Commons.Analysis.Complex.UpperHalfPlane.halfPlane_disc_diffeomorph

/-!
# A chart with room around a compact set, whose chart representative is a local biholomorphism

This module isolates the *exact* geometric input of `Work.SimplyConnected.ABS.regularPiece_core`
(and of `Work.SimplyConnected.ABS.exists_isRegularPiece_superset`), in the sharpest form the region
argument can consume:

> for every compact `K` in a simply connected non-compact Riemann surface `X` there are an open
> partial homeomorphism `φ : X → ℂ`, `c : ℂ` and `ρ > 0` with `K ⊆ φ.source`,
> `φ '' K ⊆ ball c ρ`, `closedBall c ρ ⊆ φ.target`, and — the point which distinguishes this from
> `Work.SimplyConnected.ABS.planarity_around_compact` — the chart representatives
> `φ ∘ (chartAt ℂ p).symm` are **analytic with non-vanishing derivative** at `(chartAt ℂ p) p`.

Why the extra clause is needed: the sector condition `HasSectorBoundary U p` at a frontier point of
`U = φ.symm '' ball c ρ` is *not* a consequence of `U` being a chart ball with room; it needs the
local geometry of `U` in the *atlas* chart at `p`, which is governed by the chart representative
`φ ∘ (chartAt ℂ p).symm`.  With the clause above, `U` locally is a strictly regular level set of a
holomorphic function (non-zero derivative), which is the quadratic-Taylor situation handled by
`Work.SimplyConnected.ABS.sectorComplement_of_quadraticRemainder`; the endgame
`Work.SimplyConnected.ABS.exists_regularPiece_of_chart_with_room` (in `regularPiece_core.lean`)
turns this into the full conclusion of `regularPiece_core`.

## Status

* the **hyperbolic case** (X carries a unit-pole Green function) is **proved** here: the workspace's
  modulus assembly plus `Work.Parabolic.uniformization_of_greenFunctionAt` give `X ≅ ℂ` or `X ≅ ℍ`,
  and in both cases the chart representative of the diffeomorphism is analytic with non-vanishing
  derivative (a diffeomorphism of complex manifolds, composed with the inclusion of the disc);
* the **parabolic case** (no Green function) is left as the single `sorry` of this module.  It is
  exactly the ABS/Mori input: by `Work.Parabolic.plane_of_no_greenFunction` it is enough to exhibit an
  injective holomorphic `X → ℂ` (Anghel--Bruin--Stan Theorem 1 / Mori's normal form theorem), i.e.
  the planarity of `X`.  Nothing in the workspace proves it; every route is recorded in
  `NOTES_sector_general_position_DONE.md`, `NOTES_engulfing_route_analysis.md` and the docstring of
  `regularPiece_core.lean`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology
open Set Metric

set_option linter.unusedSectionVars false

noncomputable section

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- A charted space with a nontrivial chart has at least two points (local form of
`Submission.exists_ne_of_chartedSpace`). -/
theorem exists_ne_of_chartedSpace' (z : X) : ∃ y : X, y ≠ z := by
  have hz : (chartAt ℂ z) z ∈ (chartAt ℂ z).target :=
    (chartAt ℂ z).map_source (mem_chart_source ℂ z)
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp (chartAt ℂ z).open_target _ hz
  set v : ℂ := (chartAt ℂ z) z + ((r / 2 : ℝ) : ℂ) with hv
  have hvmem : v ∈ (chartAt ℂ z).target := hrsub (by
    rw [hv, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < r / 2 by linarith)]
    linarith)
  have hne : v ≠ (chartAt ℂ z) z := by
    intro h
    have h2 : ((r / 2 : ℝ) : ℂ) = 0 := by
      have := congrArg (fun w : ℂ => w - (chartAt ℂ z) z) h
      simpa [hv] using this
    have : (r / 2 : ℝ) = 0 := Complex.ofReal_eq_zero.mp h2
    linarith
  refine ⟨(chartAt ℂ z).symm v, fun h => hne ?_⟩
  calc v = (chartAt ℂ z) ((chartAt ℂ z).symm v) := ((chartAt ℂ z).right_inv hvmem).symm
    _ = (chartAt ℂ z) z := by rw [h]

/-- **The local-biholomorphism clause for an injective smooth map `X → ℂ`.**  If `E : X → ℂ` is a
smooth injective map and `φ` is an open partial homeomorphism (`φ.source = univ`) which agrees with
`E`, then the chart representatives of `φ` are analytic with non-vanishing derivative. -/
theorem locallyBiholomorphic_of_injective_smooth {E : X → ℂ}
    (hEcd : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞ E)
    (hEinj : Function.Injective E)
    {φ : OpenPartialHomeomorph X ℂ} (hφsrc : φ.source = Set.univ) (hφE : ∀ x : X, φ x = E x) :
    (∀ p : X, AnalyticAt ℂ (fun w => φ ((chartAt ℂ p).symm w)) ((chartAt ℂ p) p)) ∧
      (∀ p : X, deriv (fun w => φ ((chartAt ℂ p).symm w)) ((chartAt ℂ p) p) ≠ 0) := by
  have hEq : ∀ p : X, (fun w => φ ((chartAt ℂ p).symm w))
      = fun w => E ((chartAt ℂ p).symm w) := by
    intro p
    funext w
    rw [hφE]
  have hAnal : ∀ p : X, AnalyticAt ℂ (fun w => E ((chartAt ℂ p).symm w)) ((chartAt ℂ p) p) := by
    intro p
    have h := Work.Parabolic.analyticAt_chart_representation_infty (X := X) (Y := ℂ) (Φ := E)
      hEcd p
    have h' : (fun z => (chartAt ℂ (E p)) (E ((chartAt ℂ p).symm z)))
        = fun z => E ((chartAt ℂ p).symm z) := by
      funext z
      simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq]
    rwa [h'] at h
  constructor
  · intro p
    rw [hEq p]
    exact hAnal p
  · intro p
    rw [hEq p]
    exact Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic (X := X) (Φ := E) hEinj
      (fun x => hAnal x) (exists_ne_of_chartedSpace' p)

/-- A compact subset of `ℂ` lies in an open ball of positive radius. -/
theorem exists_ball_superset_of_isCompact' {K : Set ℂ} (hK : IsCompact K) :
    ∃ c : ℂ, ∃ ρ : ℝ, 0 < ρ ∧ K ⊆ Metric.ball c ρ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, 1, one_pos, by simp⟩
  · obtain ⟨z₀, hz₀⟩ := hne
    obtain ⟨R, hR⟩ := hK.isBounded.subset_ball z₀
    have hRpos : 0 < R := by
      have h : z₀ ∈ Metric.ball z₀ R := hR hz₀
      rwa [Metric.mem_ball, dist_self] at h
    exact ⟨z₀, R, hRpos, hR⟩

/-- A compact subset of a round ball is contained in a strictly smaller round ball. -/
theorem exists_ball_of_isCompact_subset_ball' {K : Set ℂ} (hK : IsCompact K) {R₁ : ℝ}
    (hR₁ : 0 < R₁) (hK₁ : K ⊆ Metric.ball (0 : ℂ) R₁) :
    ∃ R : ℝ, 0 < R ∧ R < R₁ ∧ K ⊆ Metric.ball (0 : ℂ) R := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨R₁ / 2, by linarith, by linarith, by simp⟩
  · obtain ⟨z₀, hz₀K, hz₀max⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
    have hz₀lt : ‖z₀‖ < R₁ := by
      have h := hK₁ hz₀K
      simpa [dist_eq_norm] using h
    refine ⟨(‖z₀‖ + R₁) / 2, by linarith [norm_nonneg z₀], by linarith, fun z hz => ?_⟩
    have h1 : ‖z‖ ≤ ‖z₀‖ := hz₀max hz
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    linarith

/-- **The clause from a diffeomorphism to `ℂ`.** -/
theorem exists_chart_with_room_locallyBiholomorphic_of_diffeomorph_plane
    (e : X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) (K : Set X)
    (hK : IsCompact K) :
    ∃ (φ : OpenPartialHomeomorph X ℂ) (c : ℂ) (ρ : ℝ), 0 < ρ ∧ K ⊆ φ.source ∧
      φ '' K ⊆ Metric.ball c ρ ∧ Metric.closedBall c ρ ⊆ φ.target ∧
      (∀ p ∈ φ.source, AnalyticAt ℂ (fun w => φ ((chartAt ℂ p).symm w)) ((chartAt ℂ p) p)) ∧
      (∀ p ∈ φ.source, deriv (fun w => φ ((chartAt ℂ p).symm w)) ((chartAt ℂ p) p) ≠ 0) := by
  classical
  obtain ⟨c, ρ, hρ, hball⟩ := exists_ball_superset_of_isCompact' (hK.image e.continuous)
  have hsrc : e.toHomeomorph.toOpenPartialHomeomorph.source = Set.univ :=
    Homeomorph.toOpenPartialHomeomorph_source e.toHomeomorph
  have hφE : ∀ x : X, e.toHomeomorph.toOpenPartialHomeomorph x = e x := fun x => rfl
  obtain ⟨han, hder⟩ := locallyBiholomorphic_of_injective_smooth (E := (e : X → ℂ))
    e.contMDiff e.injective hsrc hφE
  refine ⟨e.toHomeomorph.toOpenPartialHomeomorph, c, ρ, hρ, ?_, ?_, ?_,
    fun p _ => han p, fun p _ => hder p⟩
  · rw [hsrc]; exact subset_univ K
  · rintro z ⟨x, hx, rfl⟩
    exact hball ⟨x, hx, rfl⟩
  · rw [Homeomorph.toOpenPartialHomeomorph_target e.toHomeomorph]
    exact subset_univ _

/-- **The clause from a diffeomorphism to the open unit disc.** -/
theorem exists_chart_with_room_locallyBiholomorphic_of_diffeomorph_disc
    (e : X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ Submission.Helpers.DiscOpen)
    (K : Set X) (hK : IsCompact K) :
    ∃ (φ : OpenPartialHomeomorph X ℂ) (c : ℂ) (ρ : ℝ), 0 < ρ ∧ K ⊆ φ.source ∧
      φ '' K ⊆ Metric.ball c ρ ∧ Metric.closedBall c ρ ⊆ φ.target ∧
      (∀ p ∈ φ.source, AnalyticAt ℂ (fun w => φ ((chartAt ℂ p).symm w)) ((chartAt ℂ p) p)) ∧
      (∀ p ∈ φ.source, deriv (fun w => φ ((chartAt ℂ p).symm w)) ((chartAt ℂ p) p) ≠ 0) := by
  classical
  haveI : Nonempty ↥Submission.Helpers.DiscOpen :=
    ⟨⟨0, by simp [Submission.Helpers.DiscOpen]⟩⟩
  set E : X → ℂ := fun x => (e x : ℂ) with hEdef
  set φ : OpenPartialHomeomorph X ℂ :=
    e.toHomeomorph.toOpenPartialHomeomorph.trans
      (Submission.Helpers.DiscOpen.openPartialHomeomorphSubtypeCoe inferInstance) with hφdef
  have hsrc : φ.source = Set.univ := by
    rw [hφdef, OpenPartialHomeomorph.trans_source]
    simp [Homeomorph.toOpenPartialHomeomorph_source,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source]
  have htrg : φ.target = (Submission.Helpers.DiscOpen : Set ℂ) := by
    rw [hφdef, OpenPartialHomeomorph.trans_target]
    simp [Homeomorph.toOpenPartialHomeomorph_target,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
  have hφE : ∀ x : X, φ x = E x := by
    intro x
    rw [hφdef, OpenPartialHomeomorph.trans_apply, Homeomorph.toOpenPartialHomeomorph_apply]
    simp [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe, hEdef]
  have hEcd : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞ E :=
    contMDiff_subtype_val.comp e.contMDiff
  have hEinj : Function.Injective E := fun x y hxy => e.injective (Subtype.ext hxy)
  have hEsub : E '' K ⊆ Metric.ball (0 : ℂ) 1 := by
    rintro z ⟨x, -, rfl⟩
    exact (e x).2
  obtain ⟨ρ, hρ, hρ1, hball⟩ :=
    exists_ball_of_isCompact_subset_ball' (hK.image hEcd.continuous) (by norm_num) hEsub
  obtain ⟨han, hder⟩ := locallyBiholomorphic_of_injective_smooth (E := E) hEcd hEinj hsrc hφE
  refine ⟨φ, 0, ρ, hρ, ?_, ?_, ?_, fun p _ => han p, fun p _ => hder p⟩
  · rw [hsrc]; exact subset_univ K
  · rintro z ⟨x, hx, rfl⟩
    exact hball ⟨x, hx, rfl⟩
  · rw [htrg]
    exact Metric.closedBall_subset_ball hρ1

/-- **The clause in the hyperbolic case.**  A unit-pole Green function on `X` gives, through the
modulus assembly and `Work.Parabolic.uniformization_of_greenFunctionAt`, a diffeomorphism of `X` onto
`ℂ` or onto `ℍ`; the two preceding lemmas then produce the chart with room. -/
theorem exists_chart_with_room_locallyBiholomorphic_of_unitGreenFunction [SimplyConnectedSpace X]
    (hX : ¬ CompactSpace X)
    (h : ∃ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (K : Set X) (hK : IsCompact K) :
    ∃ (φ : OpenPartialHomeomorph X ℂ) (c : ℂ) (ρ : ℝ), 0 < ρ ∧ K ⊆ φ.source ∧
      φ '' K ⊆ Metric.ball c ρ ∧ Metric.closedBall c ρ ⊆ φ.target ∧
      (∀ p ∈ φ.source, AnalyticAt ℂ (fun w => φ ((chartAt ℂ p).symm w)) ((chartAt ℂ p) p)) ∧
      (∀ p ∈ φ.source, deriv (fun w => φ ((chartAt ℂ p).symm w)) ((chartAt ℂ p) p) ≠ 0) := by
  obtain ⟨z₀, E, hE⟩ := h
  obtain ⟨Φ, hhol, hpole, hmod⟩ :=
    Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction_of_simplyConnected (X := X)
      (z₀ := z₀) hE
  rcases Work.Parabolic.uniformization_of_greenFunctionAt (X := X) hX hE.isGreenFunctionAt
    hhol hmod hpole with h | h
  · obtain ⟨e⟩ := h
    exact exists_chart_with_room_locallyBiholomorphic_of_diffeomorph_plane e K hK
  · obtain ⟨e⟩ := h
    obtain ⟨d⟩ := Commons.Analysis.Complex.UpperHalfPlane.halfPlane_disc_diffeomorph
    exact exists_chart_with_room_locallyBiholomorphic_of_diffeomorph_disc (e.trans d) K hK

end Work.SimplyConnected.ABS
