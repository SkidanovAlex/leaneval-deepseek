import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndex
import Submission.Work.Smooth.SphereJordan.planeIndexGeom

/-!
# Homotopy invariance of the index of a closed plane curve

The index `loopIndex` of `Submission.Work.Smooth.SphereJordan.planeIndex` is a homotopy invariant of
closed curves in the punctured plane `ℂ \ {0}`.  This file proves this in the form needed for the
Jordan separation theory: if `H : [0,1] × [0,1] → ℂ` is a nowhere vanishing homotopy all of whose
"slices" `t ↦ H (t, s)` are closed loops, then the indices of the two end loops agree:

`loopIndex_eq_of_homotopy`.

The proof rests on the local constancy of the index in the homotopy parameter.  For a fixed `s₀`
the slice `t ↦ H (t, s₀)` is a closed curve in the punctured plane, so by compactness of
`[0,1]` its modulus has a positive lower bound `m`; by uniform continuity of `H` on the compact
square there is `δ > 0` such that `‖H (t, s) - H (t, s₀)‖ < m` whenever `dist s s₀ < δ` and for
*every* `t`.  Then `H (t, s) / H (t, s₀)` lies in the ball of radius `1` about `1`, hence in the
slit plane, and `Work.Smooth.SphereJordan.loopIndex_eq_of_pointwise_div_mem_slitPlane` gives
`loopIndex (H (·, s)) = loopIndex (H (·, s₀))`.  Thus `s ↦ loopIndex (H (·, s))` is locally
constant on the connected space `[0,1]`, hence constant.
-/

set_option linter.unusedVariables false

noncomputable section

open Set

namespace Work.Smooth.SphereJordan

/-- **Local constancy of the index along a nowhere vanishing homotopy of closed loops.** -/
theorem isLocallyConstant_loopIndex_of_homotopy (H : C(unitInterval × unitInterval, ℂ))
    (hHne : ∀ p, H p ≠ 0) (hHloop : ∀ s, H (0, s) = H (1, s)) :
    IsLocallyConstant (fun s : unitInterval =>
      loopIndex (H.comp (ContinuousMap.prodMk (ContinuousMap.id unitInterval)
        (ContinuousMap.const unitInterval s)))) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro s₀
  -- A positive lower bound for `‖H (·, s₀)‖`.
  have hf : Continuous fun t : unitInterval => ‖H (t, s₀)‖ := by fun_prop
  obtain ⟨t₀, -, hmin⟩ :=
    IsCompact.exists_isMinOn (isCompact_univ) (Set.univ_nonempty) hf.continuousOn
  set m : ℝ := ‖H (t₀, s₀)‖ with hm
  have hmpos : 0 < m := by rw [hm]; exact norm_pos_iff.mpr (hHne (t₀, s₀))
  have hmle : ∀ t, m ≤ ‖H (t, s₀)‖ := by
    intro t; rw [hm]; exact hmin (Set.mem_univ t)
  -- Uniform continuity of `H` on the compact square.
  have hu : UniformContinuous H := CompactSpace.uniformContinuous_of_continuous H.continuous
  rw [Metric.uniformContinuous_iff] at hu
  obtain ⟨δ, hδpos, hδ⟩ := hu m hmpos
  refine ⟨Metric.ball s₀ δ, Metric.isOpen_ball, Metric.mem_ball_self hδpos, ?_⟩
  intro s hs
  rw [Metric.mem_ball] at hs
  have hdiv : ∀ t : unitInterval,
      (H.comp (ContinuousMap.prodMk (ContinuousMap.id unitInterval)
        (ContinuousMap.const unitInterval s))) t
      / (H.comp (ContinuousMap.prodMk (ContinuousMap.id unitInterval)
        (ContinuousMap.const unitInterval s₀))) t ∈ Complex.slitPlane := by
    intro t
    -- Uniform smallness of the displacement.
    have hd : ‖H (t, s) - H (t, s₀)‖ < m := by
      have hdist : dist (t, s) (t, s₀) < δ := by
        rw [Prod.dist_eq]
        simp only [dist_self]
        rw [max_eq_right (dist_nonneg)]
        exact hs
      have := hδ hdist
      rwa [dist_eq_norm] at this
    -- The quotient stays in the ball of radius `1` about `1`.
    have hb : H (t, s₀) ≠ 0 := hHne (t, s₀)
    have hw : ‖H (t, s) / H (t, s₀) - 1‖ < 1 := by
      rw [show H (t, s) / H (t, s₀) - 1 = (H (t, s) - H (t, s₀)) / H (t, s₀) by field_simp]
      rw [norm_div]
      have h1 : ‖H (t, s) - H (t, s₀)‖ / ‖H (t, s₀)‖ ≤ ‖H (t, s) - H (t, s₀)‖ / m :=
        div_le_div_of_nonneg_left (norm_nonneg _) hmpos (hmle t)
      have h2 : ‖H (t, s) - H (t, s₀)‖ / m < 1 := (div_lt_one hmpos).mpr hd
      linarith
    have := Complex.mem_slitPlane_of_norm_lt_one (z := H (t, s) / H (t, s₀) - 1) hw
    simpa using this
  exact loopIndex_eq_of_pointwise_div_mem_slitPlane _ _
    (fun t => hHne (t, s)) (fun t => hHne (t, s₀)) (by simp [hHloop s]) (by simp [hHloop s₀]) hdiv

theorem loopIndex_eq_of_homotopy {c₀ c₁ : C(unitInterval, ℂ)} (h₀ : ∀ t, c₀ t ≠ 0)
    (h₁ : ∀ t, c₁ t ≠ 0) (H : C(unitInterval × unitInterval, ℂ)) (hHne : ∀ p, H p ≠ 0)
    (hH0 : ∀ t, H (t, 0) = c₀ t) (hH1 : ∀ t, H (t, 1) = c₁ t)
    (hHloop : ∀ s, H (0, s) = H (1, s)) : loopIndex c₀ = loopIndex c₁ := by
  have hlc := isLocallyConstant_loopIndex_of_homotopy H hHne hHloop
  have hg0 : H.comp (ContinuousMap.prodMk (ContinuousMap.id unitInterval)
        (ContinuousMap.const unitInterval (0 : unitInterval))) = c₀ :=
    ContinuousMap.ext (fun t => hH0 t)
  have hg1 : H.comp (ContinuousMap.prodMk (ContinuousMap.id unitInterval)
        (ContinuousMap.const unitInterval (1 : unitInterval))) = c₁ :=
    ContinuousMap.ext (fun t => hH1 t)
  have h01 := hlc.apply_eq_of_preconnectedSpace (0 : unitInterval) (1 : unitInterval)
  rw [hg0, hg1] at h01
  exact h01

end Work.Smooth.SphereJordan
