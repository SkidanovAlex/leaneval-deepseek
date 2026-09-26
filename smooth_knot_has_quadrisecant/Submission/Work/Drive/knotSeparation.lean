import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.spatial_le_slope_mul_dist

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-!
# Separation of a knot from itself

A smooth (hence continuous, periodic, injective-on-a-period) knot `r` cannot
come arbitrarily close to itself at parameters that are uniformly far apart on
the parameter circle: for every `η > 0` there is `ρ > 0` such that

  `η ≤ dist s x  →  ρ ≤ ‖r s - r x‖`.

This is the quantitative form of "a continuous injective map on a compact
space is a closed embedding", applied to the induced map `knotMap r` on the
compact circle `AddCircle period`.

The topological input is proved once, in complete generality, as
`exists_pos_le_dist_of_continuous_injective`.
-/

/-- **Uniform separation.** A continuous injective map from a compact metric
space into a metric space is uniformly separated: for every `ε > 0` the values
at `ε`-separated pairs of points stay a positive distance apart.

This is the quantitative form of "a continuous injective map on a compact
space is a closed embedding".  The proof is the standard one: the set of
`ε`-separated pairs is compact, the continuous function
`(a, b) ↦ dist (f a) (f b)` is strictly positive on it, and
`IsCompact.exists_forall_le'` upgrades pointwise positivity to a uniform lower
bound. -/
theorem exists_pos_le_dist_of_continuous_injective
    {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
    (f : X → Y) (hf : Continuous f) (hinj : Function.Injective f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b : X, ε ≤ dist a b → δ ≤ dist (f a) (f b) := by
  have hS : IsCompact {p : X × X | ε ≤ dist p.1 p.2} :=
    (isClosed_le continuous_const continuous_dist).isCompact
  have hcont : ContinuousOn (fun p : X × X => dist (f p.1) (f p.2))
      {p : X × X | ε ≤ dist p.1 p.2} :=
    ((hf.comp continuous_fst).dist (hf.comp continuous_snd)).continuousOn
  have hgt : ∀ p ∈ {p : X × X | ε ≤ dist p.1 p.2}, (0 : ℝ) < dist (f p.1) (f p.2) := by
    intro p hp
    rcases p with ⟨a, b⟩
    have hp' : ε ≤ dist a b := hp
    have hne : a ≠ b := by
      intro h
      have h0 : dist a b = 0 := by rw [h, dist_self]
      linarith
    exact dist_pos.mpr fun h => hne (hinj h)
  obtain ⟨δ, hδpos, hδle⟩ := hS.exists_forall_le' hcont hgt
  exact ⟨δ, hδpos, fun a b hab => hδle (a, b) hab⟩

/-- **Knot separation from itself.** For a smooth knot `r` and every `η > 0`
there is `ρ > 0` such that parameters which are `η`-separated on the parameter
circle give points at distance at least `ρ`.

This is `exists_pos_le_dist_of_continuous_injective` applied to the induced
continuous injective map `knotMap r` on the compact circle
`AddCircle period`, using that `knotMap r` agrees with `r` at the class of
every real number (`knotMap_coe_of_periodic`). -/
theorem knotSeparation {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space} (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r) {η : ℝ} (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s x : ℝ,
      η ≤ dist (s : AddCircle LeanEval.KnotTheory.Quadrisecant.period)
        (x : AddCircle LeanEval.KnotTheory.Quadrisecant.period) →
      ρ ≤ ‖r s - r x‖ := by
  obtain ⟨ρ, hρpos, hρ⟩ :=
    exists_pos_le_dist_of_continuous_injective (knotMap r)
      hr.knotMap_continuous (knotMap_injective hr) hη
  refine ⟨ρ, hρpos, fun s x hsx => ?_⟩
  have h := hρ (s : AddCircle period) (x : AddCircle period) hsx
  rw [knotMap_coe_of_periodic hr.periodic s, knotMap_coe_of_periodic hr.periodic x,
    dist_eq_norm] at h
  exact h

end Work.Drive
