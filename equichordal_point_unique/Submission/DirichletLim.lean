import Submission.UnifDeps
import Submission.PerronOn
import Submission.DirichletRegionOn

/-!
# The classical region-Perrron family: limsup boundary data

`Submission.dirichletFamilyOn Ω f M` prescribes the Dirichlet data *pointwise outside* `Ω`
(`v x ≤ f x` for `x ∉ Ω`).  As explained in `Submission/ROADMAP.md` (SESSION 17, correction (A))
this is **not** the classical Perron family: the pointwise condition cannot control the behaviour of
`v` as one approaches the boundary *from inside* `Ω` (the Poisson kernel of a point mass, extended
by `0` outside the closed disc, is a member but has infinite limsup at that boundary point).  The
classical family prescribes limsup boundary data:

`limFamily U f M = {v | v subharmonic on U, v ≤ M, and limsup_{z→ζ, z∈U} v z ≤ f ζ for
every ζ ∈ frontier U}`.

This module proves that `limFamily U f M` is a Perron family (`IsPerronOn`, so that the upper
envelope is harmonic on `U`) and records the elementary consequences.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

section Def

variable [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The region-Perrron family with limsup boundary data.** -/
def limFamily (U : Set X) (f : X → ℝ) (M : ℝ) : Set (X → ℝ) :=
  {v | SubharmonicOnX v U ∧ (∀ x : X, v x ≤ M) ∧
    ∀ ζ ∈ frontier U, ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝[U] ζ, v z ≤ f ζ + ε}

theorem limFamily_subharmonic {U : Set X} {f : X → ℝ} {M : ℝ} {v : X → ℝ}
    (hv : v ∈ limFamily U f M) : SubharmonicOnX v U := hv.1

theorem limFamily_bound {U : Set X} {f : X → ℝ} {M : ℝ} {v : X → ℝ}
    (hv : v ∈ limFamily U f M) (x : X) : v x ≤ M := hv.2.1 x

theorem limFamily_limsup {U : Set X} {f : X → ℝ} {M : ℝ} {v : X → ℝ}
    (hv : v ∈ limFamily U f M) {ζ : X} (hζ : ζ ∈ frontier U) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝[U] ζ, v z ≤ f ζ + ε := hv.2.2 ζ hζ ε hε

end Def

section Perron

variable [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The limsup region-Perrron family is a Perron family** (with restricted harmonic replacement):
the replacement only changes the function inside a small chart disc whose closure stays in `U`, so
near every boundary point of `U` the replacement agrees with the original member. -/
theorem limFamily_isPerronOn {U : Set X} (hU : IsOpen U) {f : X → ℝ} {M : ℝ}
    (hne : (limFamily U f M).Nonempty) : IsPerronOn (limFamily U f M) (fun _ => M) U := by
  refine ⟨hne, fun v hv => limFamily_subharmonic hv, fun v hv x _ => limFamily_bound hv x, ?_, ?_⟩
  · intro v hv w hw
    refine ⟨(limFamily_subharmonic hv).sup (limFamily_subharmonic hw),
      fun x => max_le (limFamily_bound hv x) (limFamily_bound hw x), ?_⟩
    intro ζ hζ ε hε
    filter_upwards [limFamily_limsup hv hζ hε, limFamily_limsup hw hζ hε] with z h1 h2
    exact max_le h1 h2
  · intro z hz
    have hsrc : z ∈ (chartAt ℂ z).source := mem_chart_source ℂ z
    have hzt : (chartAt ℂ z) z ∈ (chartAt ℂ z).target := (chartAt ℂ z).map_source hsrc
    have hsymm : (chartAt ℂ z).symm ((chartAt ℂ z) z) = z := (chartAt ℂ z).left_inv hsrc
    obtain ⟨ε₁, hε₁, hε₁U⟩ := Metric.mem_nhds_iff.mp (by
      have h2 : U ∈ 𝓝 ((chartAt ℂ z).symm ((chartAt ℂ z) z)) := by
        rw [hsymm]
        exact hU.mem_nhds hz
      exact ((chartAt ℂ z).continuousAt_symm hzt).preimage_mem_nhds h2)
    obtain ⟨ε₂, hε₂, hε₂t⟩ := Metric.mem_nhds_iff.mp ((chartAt ℂ z).open_target.mem_nhds hzt)
    refine ⟨min (ε₁ / 2) (ε₂ / 2), lt_min (half_pos hε₁) (half_pos hε₂), ?_⟩
    intro v hv ρ hρ hρε hsub u hu hglue
    have hρ₁ : ρ < ε₁ := by linarith [hρε, min_le_left (ε₁ / 2) (ε₂ / 2), hε₁]
    have hρ₂ : ρ < ε₂ := by linarith [hρε, min_le_right (ε₁ / 2) (ε₂ / 2), hε₂]
    have hsubU : Metric.closedBall ((chartAt ℂ z) z) ρ ⊆ (chartAt ℂ z).target := hsub
    have hUcl : chartClosedBall (chartAt ℂ z) ((chartAt ℂ z) z) ρ ⊆ U := by
      rintro y ⟨hy1, hy2⟩
      have h1 : (chartAt ℂ z) y ∈ Metric.ball ((chartAt ℂ z) z) ε₁ :=
        (Metric.closedBall_subset_ball hρ₁) hy2
      have h2 := hε₁U h1
      rw [Set.mem_preimage] at h2
      rwa [(chartAt ℂ z).left_inv hy1] at h2
    have hΔU : (chartAt ℂ z).symm '' Metric.closedBall ((chartAt ℂ z) z) ρ ⊆ U := by
      rw [← chartClosedBall_eq_image hsubU]
      exact hUcl
    have hballU : chartBall (chartAt ℂ z) ((chartAt ℂ z) z) ρ ⊆ U :=
      (chartBall_subset_chartClosedBall _ _ _).trans hUcl
    refine ⟨replaceOnDisc_subharmonicOn hU hρ hsubU hΔU (limFamily_subharmonic hv) hu hglue,
      ?_, ?_⟩
    · intro x
      by_cases hxb : x ∈ chartBall (chartAt ℂ z) ((chartAt ℂ z) z) ρ
      · have hxball : (chartAt ℂ z) x ∈ Metric.ball ((chartAt ℂ z) z) ρ := hxb.2
        have hcontM : ContinuousOn
            (gluedBall (fun _ : ℂ => M) (fun _ : ℂ => M) ((chartAt ℂ z) z) ρ)
            (Metric.closedBall ((chartAt ℂ z) z) ρ) := by
          rw [gluedBall_const]
          exact continuousOn_const
        have hle := harmonic_le_of_gluedBall_le hρ hu
          (fun w _ => InnerProductSpace.harmonicAt_const M) hglue hcontM
          (fun w _ => limFamily_bound hv _)
        rw [replaceOnDisc_of_mem_chartBall hxb]
        exact hle _ (by simpa [Metric.mem_ball, dist_eq_norm] using hxball)
      · rw [replaceOnDisc_of_not_mem_chartBall hxb]
        exact limFamily_bound hv x
    · intro ζ hζ ε hε
      have hζnotU : ζ ∉ U := by
        rw [← hU.interior_eq]
        exact hζ.2
      have hζc : ζ ∉ chartClosedBall (chartAt ℂ z) ((chartAt ℂ z) z) ρ := fun h =>
        hζnotU (hUcl h)
      have hnb : (chartBall (chartAt ℂ z) ((chartAt ℂ z) z) ρ)ᶜ ∈ 𝓝 ζ := by
        refine Filter.mem_of_superset
          ((isClosed_chartClosedBall hsubU).isOpen_compl.mem_nhds hζc) ?_
        intro x hx
        exact fun hc => hx (chartBall_subset_chartClosedBall _ _ _ hc)
      have hnb' : (chartBall (chartAt ℂ z) ((chartAt ℂ z) z) ρ)ᶜ ∈ 𝓝[U] ζ := by
        rw [nhdsWithin]
        exact Filter.mem_inf_of_left hnb
      filter_upwards [hnb', limFamily_limsup hv hζ hε] with x hxnot hxle
      rw [replaceOnDisc_of_not_mem_chartBall hxnot]
      exact hxle

/-- The Perron solution of the Dirichlet problem with limsup boundary data. -/
def limEnvelope (U : Set X) (f : X → ℝ) (M : ℝ) : X → ℝ :=
  upperEnvelope (limFamily U f M)

/-- **Perron's theorem in the limsup formulation**: the envelope is harmonic on `U`. -/
theorem harmonicOnX_limEnvelope {U : Set X} (hU : IsOpen U) {f : X → ℝ} {M : ℝ}
    (hne : (limFamily U f M).Nonempty) : HarmonicOnX (limEnvelope U f M) U :=
  IsPerronOn.upperEnvelope_harmonic hU (limFamily_isPerronOn hU hne)

/-- **Maximality**: every member dominates nothing — rather, every member is dominated by the
envelope. -/
theorem limFamily_le_limEnvelope {U : Set X} (hU : IsOpen U) {f : X → ℝ} {M : ℝ}
    (hne : (limFamily U f M).Nonempty) {v : X → ℝ} (hv : v ∈ limFamily U f M) :
    ∀ x ∈ U, v x ≤ limEnvelope U f M x :=
  fun x hx => IsPerronOn.mem_le_upperEnvelope (limFamily_isPerronOn hU hne) hv hx

end Perron

end Submission
