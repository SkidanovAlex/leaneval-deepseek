import Submission.Work.PTGeometric.Source

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# PTGEOMETRIC: the source homotopy on the model annulus `SourceModel n`

`Work.PTGeometric.exists_annulusStationaryHomotopy` produces the descended, stationary homotopy on
`S^n × I`; the last-mile interface lives on the annulus `Work.PTGeometric.SourceModel n = S^n × [1,2]`
(whose compact `T2` smooth structure over the half-space is `Work.PTGeometric.nonempty_halfBallSource`).
This file transports the homotopy along the reparametrisation `(s,τ) ↦ (s, τ - 1)`, keeping the two
properties the construction uses: agreement with the `0`-end value on the whole collar `[1,3/2]`, and
the value `y₀` at the far end.

## Main results

* `Work.PTGeometric.exists_sourceModelHomotopy`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology unitInterval
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

/-- **The source homotopy on the model annulus.**  From a continuous homotopy on `S^n × I` which is
constant in the interval variable on `[0,1/2]` and equal to `y₀` at the far end, there is a continuous
homotopy on `SourceModel n = S^n × [1,2]` which agrees with the `0`-end slice `Hbar (·,0)` on the
collar `[1,3/2]` and is `y₀` at `τ = 2`. -/
theorem exists_sourceModelHomotopy {n : ℕ} {T : Type} [TopologicalSpace T] {y₀ : T}
    (Hbar : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × Set.Icc (0 : ℝ) 1, T))
    (hstat : ∀ (s : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      (t : Set.Icc (0 : ℝ) 1), (t : ℝ) ≤ 1 / 2 → Hbar (s, t) = Hbar (s, 0))
    (h1 : ∀ s : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, Hbar (s, 1) = y₀) :
    ∃ Hbar' : C(SourceModel n, T),
      (∀ (s : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (τ : Set.Icc (1 : ℝ) 2),
        (τ : ℝ) ≤ 3 / 2 → Hbar' (s, τ) = Hbar (s, 0)) ∧
      (∀ s : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
        Hbar' (s, ⟨2, by norm_num⟩) = y₀) := by
  have hmem : ∀ τ : Set.Icc (1 : ℝ) 2, ((τ : ℝ) - 1) ∈ Set.Icc (0 : ℝ) 1 := by
    intro τ
    exact ⟨by have := τ.2.1; linarith, by have := τ.2.2; linarith⟩
  let g : Set.Icc (1 : ℝ) 2 → Set.Icc (0 : ℝ) 1 := fun τ => ⟨(τ : ℝ) - 1, hmem τ⟩
  have hg : ∀ τ : Set.Icc (1 : ℝ) 2, ((g τ : Set.Icc (0 : ℝ) 1) : ℝ) = (τ : ℝ) - 1 :=
    fun _ => rfl
  have hcontg : Continuous g :=
    Continuous.subtype_mk
      ((continuous_subtype_val.comp continuous_id).sub continuous_const) _
  refine ⟨⟨fun x => Hbar (x.1, g x.2), ?_⟩, ?_, ?_⟩
  · exact Hbar.continuous.comp (Continuous.prodMk continuous_fst (hcontg.comp continuous_snd))
  · intro s τ hτ
    exact hstat s (g τ) (by rw [hg τ]; linarith)
  · intro s
    have heq : g (⟨2, by norm_num⟩ : Set.Icc (1 : ℝ) 2) = 1 := by
      apply Subtype.ext
      show (2 : ℝ) - 1 = 1
      norm_num
    exact (congrArg (fun t => Hbar (s, t)) heq).trans (h1 s)

end

end Work.PTGeometric
