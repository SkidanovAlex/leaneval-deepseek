import Submission.Work.BoxShrink.PinchOff.PairingData
import Submission.Work.SurgeryInvariance.Defs

/-!
# A nonzero functional killing every realised winding: rank at most one

The two-gate form of the pinch (`winding_psi_eq_zero_of_two_component_inter_of_weakPartition`)
produces, for the two closed halves and a suitable functional `ψ` of the parameter plane, the
statement *every winding vector realised in `UpperSide ∪ LowerSide = Ω` is killed by `ψ`*.  This
module turns that curve-level statement into the dimension bound `finrank W(Ω) ≤ 1` that the
residual `DropCase` needs.

* `finrank_le_one_of_inf_span_le_bot` — a submodule of `ℚ²` whose only multiples in a line are zero
  has dimension at most one (`ℚ²` being two-dimensional);
* `finrank_windingSpan_le_one_of_forall_psi_eq_zero` — the same for a winding span: if a *nonzero*
  linear functional `ψ : ℝ² → ℝ` kills the winding of every closed curve of a region `X`, then
  `finrank W(X) ≤ 1`.  The proof is the span argument: the set of rational points on which
  `ψ ∘ (the cast to ℝ²)` vanishes is a `ℚ`-submodule containing every realised winding, and one of
  the two rational basis vectors `(1,0)`, `(0,1)` is not killed by `ψ`, giving the line whose
  multiples in `W(X)` vanish.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **A submodule of `ℚ²` with no multiples in a line has dimension at most one.** -/
theorem finrank_le_one_of_inf_span_le_bot {W : Submodule ℚ (ℚ × ℚ)} {v : ℚ × ℚ}
    (hv : v ≠ 0) (h : W ⊓ Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤ ⊥) :
    Module.finrank ℚ ↥W ≤ 1 := by
  have hv1 : Module.finrank ℚ ↥(Submodule.span ℚ ({v} : Set (ℚ × ℚ))) = 1 :=
    finrank_span_singleton hv
  have hbot : W ⊓ Submodule.span ℚ ({v} : Set (ℚ × ℚ)) = ⊥ := le_bot_iff.mp h
  have hfr := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span ℚ ({v} : Set (ℚ × ℚ)))
  rw [hbot, finrank_bot, hv1] at hfr
  have hle : Module.finrank ℚ ↥(W ⊔ Submodule.span ℚ ({v} : Set (ℚ × ℚ))) ≤ 2 := by
    have h2 := Submodule.finrank_mono (le_top : W ⊔ Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤ ⊤)
    rwa [finrank_top, Module.finrank_prod, Module.finrank_self] at h2
  omega

/-- A functional on `ℝ²` is determined by its values on the two rational basis vectors: if it kills
both, it is zero. -/
theorem eq_zero_of_apply_one_zero_and_zero_one {ψ : (ℝ × ℝ) →ₗ[ℝ] ℝ}
    (h1 : ψ ((1 : ℝ), (0 : ℝ)) = 0) (h2 : ψ ((0 : ℝ), (1 : ℝ)) = 0) : ψ = 0 := by
  refine LinearMap.ext fun v => ?_
  have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hv, map_add, map_smul, map_smul, h1, h2]
  simp

/-- **A nonzero functional killing every realised winding vector bounds the winding span by one.** -/
theorem finrank_windingSpan_le_one_of_forall_psi_eq_zero
    {P : Work.CoreTopology.ParamTorus} {X : Set R3} {ψ : (ℝ × ℝ) →ₗ[ℝ] ℝ} (hψ : ψ ≠ 0)
    (h : ∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ X) →
      ψ (((Work.SurgeryInvariance.windingOf P γ).1 : ℝ),
         ((Work.SurgeryInvariance.windingOf P γ).2 : ℝ)) = 0) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P X) ≤ 1 := by
  classical
  -- the composite of `ψ` with the realification, a `ℚ`-linear map on `ℚ²`
  let toR : (ℚ × ℚ) →ₗ[ℚ] (ℝ × ℝ) :=
    { toFun := fun v : ℚ × ℚ => ((v.1 : ℝ), (v.2 : ℝ))
      map_add' := by intro a b; ext <;> simp [Rat.cast_add]
      map_smul' := by intro c v; ext <;> simp [Rat.cast_mul, Rat.smul_def] }
  let φ : (ℚ × ℚ) →ₗ[ℚ] ℝ := (ψ.restrictScalars ℚ).comp toR
  have hφ1 : φ ((1 : ℚ), (0 : ℚ)) = ψ ((1 : ℝ), (0 : ℝ)) := by simp [φ, toR]
  have hφ0 : φ ((0 : ℚ), (1 : ℚ)) = ψ ((0 : ℝ), (1 : ℝ)) := by simp [φ, toR]
  have hφv : ∀ v : ℚ × ℚ, φ v = ψ ((v.1 : ℝ), (v.2 : ℝ)) := by intro v; simp [φ, toR]
  -- every vector of the span lies in the kernel of `φ`
  have hspan : Work.SurgeryInvariance.WindingSpan P X ≤ LinearMap.ker φ := by
    rw [Work.SurgeryInvariance.WindingSpan]
    refine Submodule.span_le.mpr ?_
    rintro v ⟨γ, hγ, rfl⟩
    refine (LinearMap.mem_ker).mpr ?_
    rw [hφv]
    have h' := h γ hγ
    push_cast
    exact h'
  -- one of the two rational basis vectors is not killed
  have hv₀ : ψ ((1 : ℝ), (0 : ℝ)) ≠ 0 ∨ ψ ((0 : ℝ), (1 : ℝ)) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hψ (eq_zero_of_apply_one_zero_and_zero_one hcon.1 hcon.2)
  rcases hv₀ with h1 | h1
  · -- the line `ℚ ∙ (1,0)`
    refine finrank_le_one_of_inf_span_le_bot (W := Work.SurgeryInvariance.WindingSpan P X)
      (v := ((1 : ℚ), (0 : ℚ))) (by norm_num) ?_
    rw [le_bot_iff, Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨hvW, hvc⟩ := Submodule.mem_inf.mp hv
    rw [Submodule.mem_span_singleton] at hvc
    obtain ⟨c, hc⟩ := hvc
    rw [← hc] at hvW ⊢
    have hker : ((c : ℚ) • ((1 : ℚ), (0 : ℚ))) ∈ LinearMap.ker φ := hspan hvW
    have hzero : c • φ ((1 : ℚ), (0 : ℚ)) = 0 := by
      rw [← map_smul]
      exact (LinearMap.mem_ker).mpr hker
    rw [hφ1] at hzero
    rcases smul_eq_zero.mp hzero with hc0 | hc0
    · have : c = 0 := hc0
      rw [this]
      simp
    · exact absurd hc0 h1
  · -- the line `ℚ ∙ (0,1)`
    refine finrank_le_one_of_inf_span_le_bot (W := Work.SurgeryInvariance.WindingSpan P X)
      (v := ((0 : ℚ), (1 : ℚ))) (by norm_num) ?_
    rw [le_bot_iff, Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨hvW, hvc⟩ := Submodule.mem_inf.mp hv
    rw [Submodule.mem_span_singleton] at hvc
    obtain ⟨c, hc⟩ := hvc
    rw [← hc] at hvW ⊢
    have hker : ((c : ℚ) • ((0 : ℚ), (1 : ℚ))) ∈ LinearMap.ker φ := hspan hvW
    have hzero : c • φ ((0 : ℚ), (1 : ℚ)) = 0 := by
      rw [← map_smul]
      exact (LinearMap.mem_ker).mpr hker
    rw [hφ0] at hzero
    rcases smul_eq_zero.mp hzero with hc0 | hc0
    · have : c = 0 := hc0
      rw [this]
      simp
    · exact absurd hc0 h1

end

end Work.BoxShrink.PinchOff
