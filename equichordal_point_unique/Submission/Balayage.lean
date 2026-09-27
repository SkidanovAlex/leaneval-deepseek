import Submission.UnifDeps
import Submission.PerronOn
import Submission.DirichletRegion
import Submission.MaxPrincipleX

/-!
# Balayage: the hitting probability of a chart disc

For a chart disc `D = chartBall c a ρ` on the Riemann surface `X` we build, by Perron's theorem,
the **hitting probability** of `D`: the largest harmonic function `≤ 1` which is `≥ 1` on `D` and
which is `≤ 1` with "boundary value `0` at the ideal boundary".

Concretely the Perron family is

`hittingFamily c a ρ = {v : X → ℝ | v subharmonic on X, v ≤ -1 on D, v ≤ 0 on X}`,

whose upper envelope `balayage c a ρ` is a nonpositive subharmonic function: it equals `-1` on `D`
and is harmonic outside the closed disc.  The hitting probability is
`hittingProbability c a ρ = -balayage c a ρ`; it satisfies `0 ≤ h ≤ 1`, `h = 1` on `D`, and it is
harmonic on `X ∖ closure D`.

This is the first step of the construction of the Green function of `X` with a pole `x₀`: for the
chart discs `D_ρ` centred at `x₀` the functions `(-log ρ) · hittingProbability D_ρ` are the
"normalised" versions of the Green function (which they converge to as `ρ → 0`).
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

/-- The balayage family of the chart disc `chartBall c a ρ`: subharmonic functions which are `≤ -1`
on the disc and `≤ 0` everywhere. -/
def hittingFamily (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) : Set (X → ℝ) :=
  {v | SubharmonicOnX v univ ∧ (∀ x ∈ chartBall c a ρ, v x ≤ -1) ∧ ∀ x, v x ≤ 0}

theorem hittingFamily_nonempty (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) :
    (hittingFamily c a ρ).Nonempty :=
  ⟨fun _ => -1, subharmonicOnX_const (-1), (fun x _ => le_rfl), (fun x => by norm_num)⟩

/-- The **balayage** of the chart disc `chartBall c a ρ`: the upper envelope of `hittingFamily`,
a nonpositive function equal to `-1` on the disc and harmonic outside the closed disc. -/
def balayage (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) : X → ℝ :=
  upperEnvelope (hittingFamily c a ρ)

/-- The **hitting probability** of the chart disc `chartBall c a ρ`: the probability that a
"Brownian particle" starting at `x` hits the disc before reaching the ideal boundary of `X`. -/
def hittingProbability (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) : X → ℝ :=
  fun x => -balayage c a ρ x

theorem balayage_le_zero (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) (x : X) :
    balayage c a ρ x ≤ 0 := by
  rw [balayage, upperEnvelope]
  exact csSup_le ((hittingFamily_nonempty c a ρ).image _)
    (by rintro y ⟨v, hv, rfl⟩; exact hv.2.2 x)

theorem balayage_le_neg_one (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) {x : X}
    (hx : x ∈ chartBall c a ρ) : balayage c a ρ x ≤ -1 := by
  rw [balayage, upperEnvelope]
  exact csSup_le ((hittingFamily_nonempty c a ρ).image _)
    (by rintro y ⟨v, hv, rfl⟩; exact hv.2.1 x hx)

theorem neg_one_le_balayage (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) (x : X) :
    -1 ≤ balayage c a ρ x := by
  rw [balayage, upperEnvelope]
  refine le_csSup ⟨0, by rintro y ⟨v, hv, rfl⟩; exact hv.2.2 x⟩ ?_
  exact ⟨fun _ => -1, ⟨subharmonicOnX_const (-1), (fun y _ => le_rfl), (fun y => by norm_num)⟩, rfl⟩

/-- The balayage is a valid Perron family with restricted replacement outside the closed disc, hence
the balayage is harmonic off the closed disc. -/
theorem isPerronOn_hittingFamily {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall a ρ ⊆ c.target) :
    IsPerronOn (hittingFamily c a ρ) (fun _ => 0) ((chartClosedBall c a ρ)ᶜ) := by
  have hclosed : IsClosed (chartClosedBall c a ρ) := isClosed_chartClosedBall hsub
  refine ⟨hittingFamily_nonempty c a ρ, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact (hv.1).mono (Set.subset_univ _) ((hv.1).1.mono (Set.subset_univ _))
  · intro v hv x _
    exact hv.2.2 x
  · intro v hv w hw
    exact ⟨(hv.1).sup (hw.1),
      fun x hx => max_le (hv.2.1 x hx) (hw.2.1 x hx),
      fun x => max_le (hv.2.2 x) (hw.2.2 x)⟩
  · -- replacement in a small disc around a point outside the closed disc
    intro z hz
    have hznot : z ∉ chartClosedBall c a ρ := hz
    have hsrc : z ∈ (chartAt ℂ z).source := mem_chart_source ℂ z
    have hmemtgt : (chartAt ℂ z) z ∈ (chartAt ℂ z).target := (chartAt ℂ z).map_source hsrc
    have hsymm : (chartAt ℂ z).symm ((chartAt ℂ z) z) = z := (chartAt ℂ z).left_inv hsrc
    -- a neighbourhood of `z` disjoint from the closed chart ball
    have hcompl : (chartClosedBall c a ρ)ᶜ ∈ nhds z := hclosed.isOpen_compl.mem_nhds hznot
    have hcompl' : (chartClosedBall c a ρ)ᶜ ∈ nhds ((chartAt ℂ z).symm ((chartAt ℂ z) z)) := by
      rw [hsymm]; exact hcompl
    obtain ⟨ε₁, hε₁, hε₁sub⟩ := Metric.mem_nhds_iff.mp
      (((chartAt ℂ z).continuousAt_symm hmemtgt).preimage_mem_nhds hcompl')
    obtain ⟨ε₂, hε₂, hε₂tgt⟩ :=
      Metric.mem_nhds_iff.mp ((chartAt ℂ z).open_target.mem_nhds hmemtgt)
    refine ⟨min (ε₁ / 2) (ε₂ / 2), lt_min (half_pos hε₁) (half_pos hε₂), ?_⟩
    intro v hv σ hσ hσle hsub u hu hglued
    have hσ1 : σ < ε₁ := by linarith [hσle, min_le_left (ε₁ / 2) (ε₂ / 2), hε₁]
    have hσ2 : σ < ε₂ := by linarith [hσle, min_le_right (ε₁ / 2) (ε₂ / 2), hε₂]
    -- the chart disc is disjoint from `chartBall c a ρ`
    have hdisj : ∀ y ∈ chartBall (chartAt ℂ z) ((chartAt ℂ z) z) σ,
        y ∉ chartBall c a ρ := by
      intro y hy hy'
      have hy1 : (chartAt ℂ z) y ∈ Metric.ball ((chartAt ℂ z) z) ε₁ :=
        (Metric.closedBall_subset_ball hσ1) (Metric.ball_subset_closedBall hy.2)
      have hy2 := hε₁sub hy1
      rw [Set.mem_preimage] at hy2
      rw [(chartAt ℂ z).left_inv hy.1] at hy2
      exact hy2 (chartBall_subset_chartClosedBall c a ρ hy')
    have hcont0 : ContinuousOn
        (gluedBall (fun _ : ℂ => (0 : ℝ)) (fun _ : ℂ => (0 : ℝ)) ((chartAt ℂ z) z) σ)
        (Metric.closedBall ((chartAt ℂ z) z) σ) := by
      rw [gluedBall_const]
      exact continuousOn_const
    have hle0 : ∀ w ∈ Metric.sphere ((chartAt ℂ z) z) σ,
        (fun w => v ((chartAt ℂ z).symm w)) w ≤ (fun _ : ℂ => (0 : ℝ)) w :=
      fun w _ => hv.2.2 _
    have hrep_le : ∀ w : ℂ, ‖w - (chartAt ℂ z) z‖ < σ →
        u w ≤ 0 :=
      harmonic_le_of_gluedBall_le hσ hu (fun w _ => InnerProductSpace.harmonicAt_const 0)
        hglued hcont0 hle0
    refine ⟨replaceOnDisc_subharmonic hσ hsub hv.1 hu hglued, ?_, ?_⟩
    · -- the constraint `≤ -1` on the chart ball is untouched
      intro x hx
      by_cases hxb : x ∈ chartBall (chartAt ℂ z) ((chartAt ℂ z) z) σ
      · exact absurd hx (hdisj x hxb)
      · rw [replaceOnDisc_of_not_mem_chartBall hxb]
        exact hv.2.1 x hx
    · -- the constraint `≤ 0`
      intro x
      by_cases hxb : x ∈ chartBall (chartAt ℂ z) ((chartAt ℂ z) z) σ
      · have hxball : (chartAt ℂ z) x ∈ Metric.ball ((chartAt ℂ z) z) σ := hxb.2
        rw [replaceOnDisc_of_mem_chartBall hxb]
        exact hrep_le _ (by simpa [Metric.mem_ball, dist_eq_norm] using hxball)
      · rw [replaceOnDisc_of_not_mem_chartBall hxb]
        exact hv.2.2 x

/-- The balayage is harmonic outside the closed chart disc. -/
theorem harmonicOnX_balayage {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall a ρ ⊆ c.target) :
    HarmonicOnX (balayage c a ρ) ((chartClosedBall c a ρ)ᶜ) :=
  IsPerronOn.upperEnvelope_harmonic (isClosed_chartClosedBall hsub).isOpen_compl
    (isPerronOn_hittingFamily hρ hsub)

/-- The hitting probability is harmonic outside the closed chart disc. -/
theorem harmonicOnX_hittingProbability {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hsub : Metric.closedBall a ρ ⊆ c.target) :
    HarmonicOnX (hittingProbability c a ρ) ((chartClosedBall c a ρ)ᶜ) :=
  (harmonicOnX_balayage hρ hsub).neg

theorem hittingProbability_nonneg (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) (x : X) :
    0 ≤ hittingProbability c a ρ x :=
  neg_nonneg.mpr (balayage_le_zero c a ρ x)

theorem hittingProbability_le_one (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) (x : X) :
    hittingProbability c a ρ x ≤ 1 := by
  have h := neg_le_neg (neg_one_le_balayage c a ρ x)
  simpa [hittingProbability] using h

theorem hittingProbability_eq_one (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) {x : X}
    (hx : x ∈ chartBall c a ρ) : hittingProbability c a ρ x = 1 := by
  refine le_antisymm (hittingProbability_le_one c a ρ x) ?_
  have h := neg_le_neg (balayage_le_neg_one c a ρ hx)
  simpa [hittingProbability] using h

/-- **Monotonicity in the disc**: a bigger disc is hit with larger probability. -/
theorem hittingProbability_mono_radius (c : OpenPartialHomeomorph X ℂ) {a : ℂ} {ρ ρ' : ℝ}
    (hρ : ρ ≤ ρ') (x : X) : hittingProbability c a ρ x ≤ hittingProbability c a ρ' x := by
  have hfam : hittingFamily c a ρ' ⊆ hittingFamily c a ρ := by
    rintro v ⟨hv1, hv2, hv3⟩
    exact ⟨hv1, fun y hy => hv2 y ⟨hy.1, Metric.ball_subset_ball hρ hy.2⟩, hv3⟩
  refine neg_le_neg ?_
  exact upperEnvelope_mono hfam (hittingFamily_nonempty c a ρ')
    ⟨0, by rintro y ⟨v, hv, rfl⟩; exact hv.2.2 x⟩

section Members

variable {X : Type*} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- Every member of the hitting family is strictly negative outside the closed chart disc: if it
vanished there, the maximum principle would make it constant `0`, contradicting its bound `-1` on
the (nonempty) chart disc. -/
theorem hittingFamily_neg_of_not_mem {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall a ρ ⊆ c.target) {v : X → ℝ} (hv : v ∈ hittingFamily c a ρ) {x : X}
    (hx : x ∉ chartClosedBall c a ρ) : v x < 0 := by
  rcases lt_or_eq_of_le (hv.2.2 x) with h | h
  · exact h
  · exfalso
    have hmax : ∀ y : X, v y ≤ v x := by
      intro y
      rw [h]
      exact hv.2.2 y
    have hconst := SubharmonicOnX.eq_of_isMaxOn hv.1 hmax
    have hmem : c.symm a ∈ chartBall c a ρ := by
      refine ⟨c.map_target (hsub (Metric.mem_closedBall_self hρ.le)), ?_⟩
      show c (c.symm a) ∈ Metric.ball a ρ
      rw [c.right_inv (hsub (Metric.mem_closedBall_self hρ.le))]
      exact Metric.mem_ball_self hρ
    have h1 := hv.2.1 _ hmem
    rw [hconst _] at h1
    linarith

end Members

end Submission
