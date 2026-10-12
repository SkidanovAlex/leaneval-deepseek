import ChallengeDeps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Layer 0: measure theory of `BoseGases.box`.

The box `box N L = {x : (Fin N → ℝ³) | ∀ i k, x i k ∈ Icc 0 L}` is a measurable set of
finite volume.  Here `ℝ³ = EuclideanSpace ℝ (Fin 3) = PiLp 2 (fun _ : Fin 3 ↦ ℝ)`.
-/

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The `(i,k)`-coordinate projection `x ↦ (x i).ofLp k` is measurable. -/
lemma coord_measurable (N : ℕ) (i : Fin N) (k : Fin 3) :
    Measurable fun (x : Fin N → ℝ³) => (x i).ofLp k := by
  have h1 : Measurable (fun (x : Fin N → ℝ³) => x i) := measurable_pi_apply i
  have h2 : Measurable (fun (y : ℝ³) => y.ofLp k) := by
    exact (measurable_pi_apply k).comp (WithLp.measurable_ofLp 2 (Fin 3 → ℝ))
  exact h2.comp h1

/-- The box is a measurable set. -/
lemma box_measurable (N : ℕ) (L : ℝ) : MeasurableSet (box N L) := by
  rw [show box N L =
      {x : Fin N → ℝ³ | ∀ i k, (x i).ofLp k ∈ Set.Icc 0 L} by
        ext x
        simp [box]]
  rw [show {x : Fin N → ℝ³ | ∀ i k, (x i).ofLp k ∈ Set.Icc 0 L} =
      (⋂ i : Fin N, ⋂ k : Fin 3,
        (fun x : Fin N → ℝ³ => (x i).ofLp k) ⁻¹' Set.Icc 0 L) by
        ext x
        simp]
  exact MeasurableSet.iInter (fun i =>
    MeasurableSet.iInter (fun k =>
      (coord_measurable N i k) measurableSet_Icc))

/-- The box is contained in the product of coordinate intervals (restated via the
`PiLp` coordinate projection). -/
lemma mem_box_iff (N : ℕ) (L : ℝ) (x : Fin N → ℝ³) :
    x ∈ box N L ↔ ∀ i k, (x i).ofLp k ∈ Set.Icc 0 L := by
  simp [box]

end BoseGases

end Submission
