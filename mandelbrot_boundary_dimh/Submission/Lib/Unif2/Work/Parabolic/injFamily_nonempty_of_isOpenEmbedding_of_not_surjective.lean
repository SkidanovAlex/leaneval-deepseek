import Mathlib
import Submission.Lib.Unif2.Work.Parabolic.Deps

/-!
# The injective extremal family is non-empty when `X` embeds into `ℂ` as a proper
simply connected planar domain

If a Riemann surface `X` admits a holomorphic **open embedding** `φ : X → ℂ` whose image is
*simply connected* and *proper* (i.e. `φ` is not surjective), then `X` is biholomorphic to the
unit disc: the image `φ '' X` is an open, simply connected, proper subset of `ℂ`, and the
Riemann-mapping step
`Commons.Analysis.Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero` supplies an injective
holomorphic map `f` from it into the unit disc with non-vanishing derivative.  Composing with a
Möbius automorphism of the disc that kills `f (φ x₀)` produces a member of the injective extremal
family `Submission.injFamily x₀`.

This is the parabolic chapter's "`X` cannot be simultaneously parabolic and a proper planar
domain" input: the parabolic branch is where such a `φ` is surjective iff ... .  In fact the
conclusion here is exactly `Case A` of the uniformization endgame
(`Submission.uniformization_of_injective_into_disc`).

The proof is the argument of `Submission.uniformization_of_injective_to_simplyConnected`, stopped
one step earlier: there one concludes the uniformization disjunction; here we produce the witness
in `injFamily`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set
open Classical

namespace Work.Parabolic

theorem injFamily_nonempty_of_isOpenEmbedding_of_not_surjective {X : Type*} [TopologicalSpace X]
    [T2Space X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x₀ : X} {φ : X → ℂ}
    (hφ : Submission.HolomorphicOnX φ Set.univ) (hemb : Topology.IsOpenEmbedding φ)
    (hUc : IsSimplyConnected (Set.range φ)) (hnot : ¬ Function.Surjective φ) :
    (Submission.injFamily x₀).Nonempty := by
  have hUo : IsOpen (Set.range φ) := hemb.isOpen_range
  have hUne : Set.range φ ≠ Set.univ := by
    intro h
    apply hnot
    intro y
    have : y ∈ Set.range φ := by rw [h]; exact Set.mem_univ y
    exact this
  -- the Riemann mapping step: an injective holomorphic map from the image into `𝔻`
  obtain ⟨f, hfmap, hfinj, hfderiv⟩ :=
    Commons.Analysis.Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero hUo hUc hUne
  have hmem : ∀ x : X, φ x ∈ Set.range φ := fun x => Set.mem_range_self x
  have hmt : ∀ x : X, f (φ x) ∈ Metric.ball (0 : ℂ) 1 := fun x => hfmap (hmem x)
  have hfbnd : ∀ x : X, ‖f (φ x)‖ ≤ 1 := fun x => by
    have h := hmt x
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
    exact le_of_lt h
  have ha : ‖f (φ x₀)‖ < 1 := by
    have h := hmt x₀
    rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at h
  set g : X → ℂ := fun x => Submission.mobiusA (f (φ x₀)) (f (φ x)) with hg
  have hgval : ∀ x : X, g x = Submission.mobiusA (f (φ x₀)) (f (φ x)) := fun x => rfl
  -- holomorphy of the composite
  have hhol : Submission.HolomorphicOnX g Set.univ := by
    intro x _
    have h1 : AnalyticAt ℂ (φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hφ x (mem_univ x)
    have hev : ∀ᶠ z in 𝓝 (φ x), DifferentiableAt ℂ f z := by
      filter_upwards [hUo.mem_nhds (hmem x)] with z hz
      exact differentiableAt_of_deriv_ne_zero (hfderiv z hz)
    have hfana : AnalyticAt ℂ f (φ x) :=
      Complex.analyticAt_iff_eventually_differentiableAt.mpr hev
    have hmob : AnalyticAt ℂ (Submission.mobiusA (f (φ x₀))) (f (φ x)) :=
      Submission.analyticAt_mobiusA _ (Submission.mobiusA_denom_ne_zero ha (hfbnd x))
    have hφval : (φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = φ x := by
      simp only [Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    have hgc : AnalyticAt ℂ (fun w : ℂ => Submission.mobiusA (f (φ x₀)) (f w))
        ((φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) := by
      rw [hφval]
      exact hmob.comp hfana
    exact hgc.comp h1
  -- injectivity of the composite
  have hginj : Function.Injective g := by
    intro x y hxy
    refine hemb.injective (hfinj (hmem x) (hmem y) ?_)
    refine Submission.mobiusA_injOn ha (hfbnd x) (hfbnd y) ?_
    simpa only [hgval] using hxy
  have hgnorm : ∀ x : X, ‖g x‖ ≤ 1 := fun x => by
    rw [hgval x]
    exact Submission.norm_mobiusA_le ha (hfbnd x)
  have hg0 : g x₀ = 0 := by
    rw [hgval x₀]
    exact Submission.mobiusA_self _
  exact ⟨g, ⟨⟨hhol, hgnorm, hg0⟩, hginj⟩⟩

end Work.Parabolic
