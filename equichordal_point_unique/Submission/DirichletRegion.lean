import Submission.UnifDeps
import Submission.PerronOn
import Submission.HarmonicReplacement
import Submission.SubharmonicAlgebra

/-!
# The Dirichlet problem on an open set, and the harmonic measure

Hubbard's Perron theorem (`Submission.IsPerronOn.upperEnvelope_harmonic`) applies to a family of
subharmonic functions which is closed under harmonic replacement in small discs around every point
of an open set `U`.  This module applies it to the two basic families of the theory of §1.4–§1.5:

* `Submission.dirichletFamily Ω f M` — the Perron family of the Dirichlet problem on an open set
  `Ω` with data `f` *outside* `Ω` and upper bound `M`.  The upper envelope
  `upperEnvelope (dirichletFamily Ω f M)` is harmonic on `Ω`, is bounded by `f` outside `Ω` and by
  `M`, and dominates every subharmonic function which satisfies the same two bounds.

* `Submission.harmonicMeasureFamily Ω` — the special case `f = 0`, `M = 1`; the envelope
  `harmonicMeasure Ω` is the *harmonic measure* of the ideal boundary of `Ω`: it is harmonic on `Ω`,
  takes values in `[0,1]`, vanishes outside `Ω`, and is monotone with respect to `Ω`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The glued function of two equal constants is that constant. -/
theorem gluedBall_const (a : ℂ) (ρ M : ℝ) :
    gluedBall (fun _ : ℂ => M) (fun _ : ℂ => M) a ρ = fun _ : ℂ => M := by
  funext w
  rw [gluedBall_apply]
  by_cases hw : w ∈ Metric.ball a ρ
  · rw [if_pos hw]
  · rw [if_neg hw]

/-! ## The Dirichlet family of an open set -/

/-- The Perron family of the Dirichlet problem on `Ω` with data `f` outside `Ω` and upper bound
`M`: subharmonic functions on `X` which are `≤ f` off `Ω` and `≤ M` everywhere. -/
def dirichletFamily (Ω : Set X) (f : X → ℝ) (M : ℝ) : Set (X → ℝ) :=
  {v | SubharmonicOnX v univ ∧ (∀ x : X, x ∉ Ω → v x ≤ f x) ∧ ∀ x : X, v x ≤ M}

theorem dirichletFamily_subharmonic {Ω : Set X} {f : X → ℝ} {M : ℝ} {v : X → ℝ}
    (hv : v ∈ dirichletFamily Ω f M) : SubharmonicOnX v univ := hv.1

theorem dirichletFamily_le_off {Ω : Set X} {f : X → ℝ} {M : ℝ} {v : X → ℝ}
    (hv : v ∈ dirichletFamily Ω f M) {x : X} (hx : x ∉ Ω) : v x ≤ f x := hv.2.1 x hx

theorem dirichletFamily_le_bound {Ω : Set X} {f : X → ℝ} {M : ℝ} {v : X → ℝ}
    (hv : v ∈ dirichletFamily Ω f M) (x : X) : v x ≤ M := hv.2.2 x

/-- **The Dirichlet family is a Perron family with restricted replacement** on `Ω`, provided it is
nonempty. -/
theorem dirichletFamily_isPerronOn {Ω : Set X} (hΩ : IsOpen Ω) {f : X → ℝ} {M : ℝ}
    (hne : (dirichletFamily Ω f M).Nonempty) :
    IsPerronOn (dirichletFamily Ω f M) (fun _ => M) Ω := by
  refine ⟨hne, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have hv' := dirichletFamily_subharmonic hv
    exact hv'.mono (Set.subset_univ Ω) (hv'.1.mono (Set.subset_univ Ω))
  · intro v hv x _
    exact dirichletFamily_le_bound hv x
  · intro v hv w hw
    exact ⟨(dirichletFamily_subharmonic hv).sup (dirichletFamily_subharmonic hw),
      fun x hx => max_le (dirichletFamily_le_off hv hx) (dirichletFamily_le_off hw hx),
      fun x => max_le (dirichletFamily_le_bound hv x) (dirichletFamily_le_bound hw x)⟩
  · intro z hz
    -- a radius around `z` whose chart ball lies in `Ω` and in the chart target
    have hsrc : z ∈ (chartAt ℂ z).source := mem_chart_source ℂ z
    have hmemtgt : (chartAt ℂ z) z ∈ (chartAt ℂ z).target := (chartAt ℂ z).map_source hsrc
    have hsymm : (chartAt ℂ z).symm ((chartAt ℂ z) z) = z := (chartAt ℂ z).left_inv hsrc
    obtain ⟨ε₁, hε₁, hε₁sub⟩ :=
      Metric.mem_nhds_iff.mp ((chartAt ℂ z).open_target.mem_nhds hmemtgt)
    obtain ⟨ε₂, hε₂, hε₂Ω⟩ := Metric.mem_nhds_iff.mp
      (((chartAt ℂ z).continuousAt_symm hmemtgt).preimage_mem_nhds
        (hΩ.mem_nhds (by rw [hsymm]; exact hz)))
    refine ⟨min (ε₁ / 2) (ε₂ / 2), lt_min (half_pos hε₁) (half_pos hε₂), ?_⟩
    intro v hv ρ hρ hρle hsub u hu hglued
    have hρ1 : ρ < ε₁ := by
      linarith [hρle, min_le_left (ε₁ / 2) (ε₂ / 2), hε₁]
    have hρ2 : ρ < ε₂ := by
      linarith [hρle, min_le_right (ε₁ / 2) (ε₂ / 2), hε₂]
    have hle2 : Metric.closedBall ((chartAt ℂ z) z) ρ ⊆ Metric.ball ((chartAt ℂ z) z) ε₂ :=
      Metric.closedBall_subset_ball hρ2
    have hΩball : chartBall (chartAt ℂ z) ((chartAt ℂ z) z) ρ ⊆ Ω := by
      rintro y ⟨hy1, hy2⟩
      have h1 : (chartAt ℂ z) y ∈ Metric.ball ((chartAt ℂ z) z) ε₂ :=
        hle2 (Metric.ball_subset_closedBall hy2)
      have h2 := hε₂Ω h1
      rw [Set.mem_preimage] at h2
      rwa [(chartAt ℂ z).left_inv hy1] at h2
    refine ⟨replaceOnDisc_subharmonic hρ hsub (dirichletFamily_subharmonic hv) hu hglued, ?_, ?_⟩
    · -- the bound `≤ f` off `Ω` is vacuous: the chart ball lies in `Ω`
      intro x hx
      by_cases hxb : x ∈ chartBall (chartAt ℂ z) ((chartAt ℂ z) z) ρ
      · exact absurd (hΩball hxb) hx
      · rw [replaceOnDisc_of_not_mem_chartBall hxb]
        exact dirichletFamily_le_off hv hx
    · -- the bound `≤ M`
      intro x
      by_cases hxb : x ∈ chartBall (chartAt ℂ z) ((chartAt ℂ z) z) ρ
      · have hxball : (chartAt ℂ z) x ∈ Metric.ball ((chartAt ℂ z) z) ρ := hxb.2
        have hcontM : ContinuousOn
            (gluedBall (fun _ : ℂ => M) (fun _ : ℂ => M) ((chartAt ℂ z) z) ρ)
            (Metric.closedBall ((chartAt ℂ z) z) ρ) := by
          rw [gluedBall_const]
          exact continuousOn_const
        have hle := harmonic_le_of_gluedBall_le hρ hu
          (fun w _ => InnerProductSpace.harmonicAt_const M) hglued hcontM
          (fun w _ => dirichletFamily_le_bound hv ((chartAt ℂ z).symm w))
        rw [replaceOnDisc_of_mem_chartBall hxb]
        exact hle _ (by simpa [Metric.mem_ball, dist_eq_norm] using hxball)
      · rw [replaceOnDisc_of_not_mem_chartBall hxb]
        exact dirichletFamily_le_bound hv x

/-! ## The Perron solution of the Dirichlet problem on an open set -/

/-- The upper envelope of the Dirichlet family: the Perron solution of the Dirichlet problem on `Ω`
with data `f` outside `Ω` and bound `M`. -/
def dirichletOnRegion (Ω : Set X) (f : X → ℝ) (M : ℝ) : X → ℝ :=
  upperEnvelope (dirichletFamily Ω f M)

/-- **The Dirichlet problem on an open set.**  The Perron solution is harmonic on `Ω`. -/
theorem harmonicOnX_dirichletOnRegion {Ω : Set X} (hΩ : IsOpen Ω) {f : X → ℝ} {M : ℝ}
    (hne : (dirichletFamily Ω f M).Nonempty) :
    HarmonicOnX (dirichletOnRegion Ω f M) Ω :=
  IsPerronOn.upperEnvelope_harmonic hΩ (dirichletFamily_isPerronOn hΩ hne)

theorem dirichletOnRegion_le_off {Ω : Set X} {f : X → ℝ} {M : ℝ}
    (hne : (dirichletFamily Ω f M).Nonempty) {x : X} (hx : x ∉ Ω) :
    dirichletOnRegion Ω f M x ≤ f x := by
  rw [dirichletOnRegion, upperEnvelope]
  exact csSup_le (hne.image _) (by rintro y ⟨v, hv, rfl⟩; exact dirichletFamily_le_off hv hx)

theorem dirichletOnRegion_le_bound {Ω : Set X} {f : X → ℝ} {M : ℝ}
    (hne : (dirichletFamily Ω f M).Nonempty) (x : X) : dirichletOnRegion Ω f M x ≤ M := by
  rw [dirichletOnRegion, upperEnvelope]
  exact csSup_le (hne.image _) (by rintro y ⟨v, hv, rfl⟩; exact dirichletFamily_le_bound hv x)

/-- **Maximality of the Perron solution**: it dominates every subharmonic function with the same
bounds. -/
theorem le_dirichletOnRegion {Ω : Set X} (hΩ : IsOpen Ω) {f : X → ℝ} {M : ℝ}
    (hne : (dirichletFamily Ω f M).Nonempty) {v : X → ℝ} (hv : v ∈ dirichletFamily Ω f M) :
    ∀ x ∈ Ω, v x ≤ dirichletOnRegion Ω f M x :=
  fun x hx => IsPerronOn.mem_le_upperEnvelope (dirichletFamily_isPerronOn hΩ hne) hv hx

/-- Monotonicity of the upper envelope in the family. -/
theorem upperEnvelope_mono {F G : Set (X → ℝ)} (hFG : F ⊆ G) {x : X} (hne : F.Nonempty)
    (hbdd : BddAbove (G.image (fun f : X → ℝ => f x))) :
    upperEnvelope F x ≤ upperEnvelope G x := by
  rw [upperEnvelope, upperEnvelope]
  refine csSup_le (hne.image _) ?_
  rintro y ⟨v, hv, rfl⟩
  exact le_csSup hbdd ⟨v, hFG hv, rfl⟩

/-! ## The harmonic measure of an open set -/

/-- The harmonic measure family of `Ω`: subharmonic functions which are `≤ 0` outside `Ω` and
`≤ 1` everywhere. -/
def harmonicMeasureFamily (Ω : Set X) : Set (X → ℝ) :=
  dirichletFamily Ω (fun _ => 0) 1

theorem harmonicMeasureFamily_nonempty (Ω : Set X) :
    (harmonicMeasureFamily Ω).Nonempty :=
  ⟨fun _ => 0, subharmonicOnX_const 0, fun x _ => le_rfl, fun x => zero_le_one⟩

/-- The harmonic measure of the ideal boundary of `Ω` (as seen from `Ω`). -/
def harmonicMeasure (Ω : Set X) : X → ℝ :=
  upperEnvelope (harmonicMeasureFamily Ω)

/-- The harmonic measure is bounded above by `1`. -/
theorem harmonicMeasure_le_one (Ω : Set X) (x : X) : harmonicMeasure Ω x ≤ 1 := by
  rw [harmonicMeasure, upperEnvelope]
  exact csSup_le ((harmonicMeasureFamily_nonempty Ω).image _)
    (by rintro y ⟨v, hv, rfl⟩; exact hv.2.2 x)

/-- The harmonic measure is nonnegative. -/
theorem harmonicMeasure_nonneg (Ω : Set X) (x : X) : 0 ≤ harmonicMeasure Ω x := by
  rw [harmonicMeasure, upperEnvelope]
  refine le_csSup ⟨1, by rintro y ⟨v, hv, rfl⟩; exact hv.2.2 x⟩ ?_
  exact ⟨fun _ => 0, ⟨subharmonicOnX_const 0, (fun y _ => le_rfl), (fun y => zero_le_one)⟩, rfl⟩

/-- The harmonic measure vanishes outside `Ω`. -/
theorem harmonicMeasure_eq_zero_of_not_mem {Ω : Set X} {x : X} (hx : x ∉ Ω) :
    harmonicMeasure Ω x = 0 :=
  le_antisymm
    (by
      rw [harmonicMeasure, upperEnvelope]
      exact csSup_le ((harmonicMeasureFamily_nonempty Ω).image _)
        (by rintro y ⟨v, hv, rfl⟩; exact hv.2.1 x hx))
    (harmonicMeasure_nonneg Ω x)

/-- **The harmonic measure is harmonic on `Ω`.** -/
theorem harmonicOnX_harmonicMeasure {Ω : Set X} (hΩ : IsOpen Ω) :
    HarmonicOnX (harmonicMeasure Ω) Ω :=
  IsPerronOn.upperEnvelope_harmonic hΩ (dirichletFamily_isPerronOn hΩ
    (harmonicMeasureFamily_nonempty Ω))

/-- **Monotonicity of the harmonic measure**: enlarging `Ω` can only increase the harmonic
measure. -/
theorem harmonicMeasure_mono {Ω Ω' : Set X} (hsub : Ω ⊆ Ω') {x : X} (hx : x ∈ Ω') :
    harmonicMeasure Ω x ≤ harmonicMeasure Ω' x := by
  have hfam : harmonicMeasureFamily Ω ⊆ harmonicMeasureFamily Ω' := by
    rintro v ⟨hv1, hv2, hv3⟩
    exact ⟨hv1, fun y hy => hv2 y (fun hy' => hy (hsub hy')), hv3⟩
  refine upperEnvelope_mono hfam (harmonicMeasureFamily_nonempty Ω) ?_
  exact ⟨1, by rintro y ⟨v, hv, rfl⟩; exact hv.2.2 x⟩

end Submission
