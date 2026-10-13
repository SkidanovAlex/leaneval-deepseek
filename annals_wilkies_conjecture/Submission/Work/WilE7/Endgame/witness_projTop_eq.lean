import Mathlib
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes

namespace Work.WilE7.Endgame

theorem witness_projTop_eq {n m : ℕ} {C : Set (Fin n → ℝ)}
    (ℓ : (Fin n → ℝ) → ℝ) (hℓ : ContinuousOn ℓ C)
    {x : ℕ → Fin n → ℝ} {x₀ : Fin n → ℝ} (hxC : ∀ t, x t ∈ C)
    (hxtend : Filter.Tendsto x Filter.atTop (nhds x₀)) (hx₀ : x₀ ∈ C)
    {z : ℕ → Fin (0 + (n + (m + 1))) → ℝ} {w : Fin (n + (m + 1)) → ℝ}
    (hztend : Filter.Tendsto (fun t => Work.WilE7.MainDesign.absPt (z t)) Filter.atTop (nhds w))
    (hzproj : ∀ t, Work.WilE7.CoreStep.projTop n m (Work.WilE7.MainDesign.absPt (z t))
      = Fin.snoc (x t) (ℓ (x t))) :
    Work.WilE7.CoreStep.projTop n m w = Fin.snoc x₀ (ℓ x₀) := by
  -- `projTop` is continuous, so it passes to the limit of `absPt (z t)`.
  have hproj : Filter.Tendsto (fun t => Work.WilE7.CoreStep.projTop n m
      (Work.WilE7.MainDesign.absPt (z t))) Filter.atTop
      (nhds (Work.WilE7.CoreStep.projTop n m w)) :=
    ((Work.WilE7.CoreStep.continuous_projTop n m).tendsto w).comp hztend
  -- `x t` converges to `x₀` and stays inside `C`, so it converges in the trace filter.
  have hxtendC : Filter.Tendsto x Filter.atTop (nhdsWithin x₀ C) :=
    tendsto_nhdsWithin_iff.mpr ⟨hxtend, Filter.Eventually.of_forall hxC⟩
  -- hence `ℓ (x t) → ℓ x₀` by continuity of `ℓ` on `C`.
  have hℓx : Filter.Tendsto (fun t => ℓ (x t)) Filter.atTop (nhds (ℓ x₀)) :=
    ((hℓ.continuousWithinAt hx₀).tendsto).comp hxtendC
  -- coordinatewise, `Fin.snoc (x t) (ℓ (x t)) → Fin.snoc x₀ (ℓ x₀)`.
  have hsnoc : Filter.Tendsto (fun t => Fin.snoc (x t) (ℓ (x t))) Filter.atTop
      (nhds (Fin.snoc x₀ (ℓ x₀) : Fin (n+1) → ℝ)) := by
    rw [tendsto_pi_nhds]
    intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa only [Fin.snoc_last] using hℓx
    · intro j
      simpa only [Fin.snoc_castSucc] using (tendsto_pi_nhds.mp hxtend) j
  -- the two limits of the same sequence coincide.
  have hproj' : Filter.Tendsto (fun t => Work.WilE7.CoreStep.projTop n m
      (Work.WilE7.MainDesign.absPt (z t))) Filter.atTop (nhds (Fin.snoc x₀ (ℓ x₀))) := by
    rw [show (fun t => Work.WilE7.CoreStep.projTop n m (Work.WilE7.MainDesign.absPt (z t)))
        = fun t => Fin.snoc (x t) (ℓ (x t)) from funext hzproj]
    exact hsnoc
  exact tendsto_nhds_unique hproj hproj'

end Work.WilE7.Endgame
