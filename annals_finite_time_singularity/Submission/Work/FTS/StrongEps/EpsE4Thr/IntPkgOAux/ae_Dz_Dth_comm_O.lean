import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux

/-- **Clairaut for the curvilinear operators, a.e. on the closed quadrant.**

For any `f` of class `SmoothOpen` (`C^∞` on the *open* quadrant `(0,∞) × (0,π/2)`),
the operators `D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ` commute at almost every point of
`Iz × Iθ` with respect to the product of the restricted Lebesgue measures.

The proof is the pointwise Clairaut identity `Work.Spaces.Dz_Dth_comm` applied at the a.e.
*interior* points: the `x`-measure of `{0}` is zero, so a.e. `z ∈ Iz` satisfies `z > 0`, and
a.e. `θ ∈ Iθ` avoids `{0, π/2}`; at such an interior point `(z,θ) ∈ Q0` the uncurried `f` is
`C²` (`SmoothOpen.forall 2` plus `IsOpen.mem_nhds` of the open quadrant `Q0`), which is
exactly the hypothesis of Clairaut–Schwarz. -/
theorem ae_Dz_Dth_comm_O {f : Work.FTS.Galerkin.Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      Work.Spaces.Dz (Work.Spaces.Dth f) p.1 p.2
        = Work.Spaces.Dth (Work.Spaces.Dz f) p.1 p.2 := by
  -- a.e. `z ∈ Iz` and a.e. `z ≠ 0`, whence a.e. `z > 0`
  have hzmem : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      z ∈ Work.Spaces.Iz := MeasureTheory.ae_restrict_mem measurableSet_Ici
  have hzne : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have hset : {z : ℝ | ¬ z ≠ 0} = {0} := by ext z; simp
    rw [hset]
    exact Set.Finite.measure_zero (Set.finite_singleton 0) _
  have hzpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    filter_upwards [hzmem, hzne] with z hz hne
    exact lt_of_le_of_ne hz (Ne.symm hne)
  -- a.e. `θ ∈ Iθ` with `θ ≠ 0`, `θ ≠ π/2`
  have hθmem : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Work.Spaces.Iθ := MeasureTheory.ae_restrict_mem measurableSet_Icc
  have hθne0 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have hset : {θ : ℝ | ¬ θ ≠ 0} = {0} := by ext θ; simp
    rw [hset]
    exact Set.Finite.measure_zero (Set.finite_singleton 0) _
  have hθneπ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ≠ Real.pi / 2 := by
    rw [MeasureTheory.ae_iff]
    have hset : {θ : ℝ | ¬ θ ≠ Real.pi / 2} = {Real.pi / 2} := by ext θ; simp
    rw [hset]
    exact Set.Finite.measure_zero (Set.finite_singleton _) _
  -- a.e. point of the product lies in the open quadrant
  have hQ : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p ∈ Work.FTS.EllipticEst.Q0 := by
    refine (MeasureTheory.Measure.ae_prod_iff_ae_ae
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (p := fun p : ℝ × ℝ => p ∈ Work.FTS.EllipticEst.Q0)
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet).mpr ?_
    filter_upwards [hzpos] with z hz
    filter_upwards [hθmem, hθne0, hθneπ] with θ hθ h0 hp
    exact Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨hz, lt_of_le_of_ne hθ.1 (Ne.symm h0), lt_of_le_of_ne hθ.2 hp⟩
  filter_upwards [hQ] with p hp
  exact Work.Spaces.Dz_Dth_comm ((hs.forall 2).contDiffAt
    (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp))

end Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux
