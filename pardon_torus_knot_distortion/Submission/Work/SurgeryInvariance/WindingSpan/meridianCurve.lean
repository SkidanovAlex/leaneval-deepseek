import Mathlib
import Submission.Work.SurgeryInvariance.Defs

/-!
# The winding span of a meridian circle

The winding span `WindingSpan P X` of a region `X ⊆ ℝ³` is the `ℚ`-span in `ℚ² = H₁(T²; ℚ)` of
the winding vectors of the closed curves of `F = P.carrier` whose image lies in `X`.

Here we compute it for `X` the meridian circle `{θ = const}` of a parametrised torus `P`, i.e.
the image of `φ ↦ P.psi θ φ`: it is the line spanned by `(0, 1)`.

* The meridian circle itself (`meridianCurve P θ`) is a closed curve of `P` whose winding vector
  is `(0, 1)` (`meridianLift_winding`), which gives `span {(0, 1)} ≤ WindingSpan …`.
* Conversely every closed curve lying in the meridian circle has vanishing longitude winding
  number: along any lift `(Θ, Φ)` of the curve the function `Θ - θ` is continuous and takes
  values in the discrete set `2πℤ`, hence is constant, so `Θ` does not advance over one period.
  Hence every winding vector met is a multiple of `(0, 1)`, which gives the reverse inclusion.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.SurgeryInvariance.WindingSpan

noncomputable section

/-- **A closed curve of the torus lying in a meridian circle has vanishing longitude winding
number.**  Along any lift `(Θ, Φ)` of the curve, `Θ t - θ` is a continuous function of `t`
taking values in the discrete set `2πℤ` (`LiftOf.continuous_int_multiple_const`), hence
constant; so `Θ` does not advance over one period and the first winding number is `0`. -/
theorem windingOf_fst_eq_zero_of_mem_meridian (P : Work.CoreTopology.ParamTorus) (θ : ℝ)
    (γ : Work.CoreTopology.ClosedCurve P)
    (hγ : ∀ t : ℝ, γ t ∈ Set.range fun φ : ℝ => P.psi θ φ) :
    (Work.SurgeryInvariance.windingOf P γ).1 = 0 := by
  let L : Work.CoreTopology.LiftOf P γ :=
    Classical.choice (Work.TorusCover.ParamTorus_exists_liftOf P γ)
  -- the longitude parameter of the lift stays in the lattice `θ + 2πℤ`
  have hmem : ∀ t : ℝ, ∃ k : ℤ, L.Θ t - θ = k * (2 * Real.pi) := by
    intro t
    obtain ⟨φ, hφ⟩ := hγ t
    have heq : P.psi (L.Θ t) (L.Φ t) = P.psi θ φ := (L.lifts t).trans hφ.symm
    obtain ⟨⟨k, hk⟩, _⟩ := (P.inj_mod (L.Θ t) (L.Φ t) θ φ).mp heq
    exact ⟨k, by linarith⟩
  have hcont : Continuous fun t : ℝ => L.Θ t - θ := L.contΘ.sub continuous_const
  obtain ⟨k₀, hk₀⟩ := Work.CoreTopology.LiftOf.continuous_int_multiple_const
    (fun t : ℝ => L.Θ t - θ) hcont hmem
  have hspec := L.winding_spec.1
  have hmul : ((L.winding).1 : ℝ) * (2 * Real.pi) = 0 := by
    have h2π := hk₀ (2 * Real.pi)
    have h0 := hk₀ 0
    linarith
  have hw : (L.winding).1 = 0 := by
    rcases mul_eq_zero.mp hmul with h | h
    · exact_mod_cast h
    · exact absurd h (ne_of_gt (by positivity))
  calc (Work.SurgeryInvariance.windingOf P γ).1
      = (L.winding).1 := by rw [Work.SurgeryInvariance.windingOf_eq P γ L]
    _ = 0 := hw

theorem meridianCurve (P : Work.CoreTopology.ParamTorus) (θ : ℝ) :
    Work.SurgeryInvariance.WindingSpan P (Set.range fun φ : ℝ => P.psi θ φ) =
      Submodule.span ℚ {((0 : ℚ), (1 : ℚ))} := by
  apply le_antisymm
  · -- every winding vector realised in the meridian circle lies in `span {(0, 1)}`
    show Submodule.span ℚ
        (Work.SurgeryInvariance.windingVectors P (Set.range fun φ : ℝ => P.psi θ φ)) ≤ _
    rw [Submodule.span_le]
    rintro v ⟨γ, hγ, hv⟩
    have h1 : (Work.SurgeryInvariance.windingOf P γ).1 = 0 :=
      windingOf_fst_eq_zero_of_mem_meridian P θ γ hγ
    rw [← hv]
    have hp : ((((Work.SurgeryInvariance.windingOf P γ).1 : ℤ) : ℚ),
        (((Work.SurgeryInvariance.windingOf P γ).2 : ℤ) : ℚ)) =
        ((((Work.SurgeryInvariance.windingOf P γ).2 : ℤ) : ℚ)) • ((0 : ℚ), (1 : ℚ)) := by
      rw [h1]
      ext <;> simp
    rw [hp]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · -- the meridian circle itself realises `(0, 1)`
    rw [Submodule.span_le]
    rintro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    apply Submodule.subset_span
    refine ⟨Work.CoreTopology.meridianCurve P θ, fun t => ⟨t, rfl⟩, ?_⟩
    have hw : Work.SurgeryInvariance.windingOf P (Work.CoreTopology.meridianCurve P θ) =
        ((0 : ℤ), (1 : ℤ)) :=
      (Work.SurgeryInvariance.windingOf_eq P _
        (Work.CoreTopology.meridianLift P θ)).trans (Work.CoreTopology.meridianLift_winding P θ)
    rw [hw]
    norm_num

end

end Work.SurgeryInvariance.WindingSpan
