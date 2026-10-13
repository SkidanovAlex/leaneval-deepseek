import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.TraceEngine

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Two angular derivatives -/

/-- `∂_θ sin²(2θ) = 4 sin(2θ) cos(2θ)`. -/
theorem hasDerivAt_sinSq (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2)
      (4 * Real.sin (2 * θ) * Real.cos (2 * θ)) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (2 * Real.cos (2 * θ)) θ := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
    have hfunc : (Real.sin ∘ fun x : ℝ => 2 * x) = fun θ : ℝ => Real.sin (2 * θ) := by
      funext x; rfl
    rw [hfunc] at h
    have hderiv : Real.cos (2 * θ) * (2 * 1) = 2 * Real.cos (2 * θ) := by ring
    rw [hderiv] at h
    exact h
  have h2 : HasDerivAt ((fun θ : ℝ => Real.sin (2 * θ)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (2 * Real.cos (2 * θ))) θ := h1.pow 2
  have h3 : (2 : ℝ) * (Real.sin (2 * θ)) ^ (2 - 1) * (2 * Real.cos (2 * θ))
      = 4 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    ring
  rw [h3] at h2
  have hfun : ((fun θ : ℝ => Real.sin (2 * θ)) ^ 2)
      = fun θ : ℝ => (Real.sin (2 * θ)) ^ 2 := by
    funext x; rfl
  rw [hfun] at h2
  exact h2

/-- `∂_θ sin(4θ) = 4 cos(4θ)`. -/
theorem hasDerivAt_sinFour (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => Real.sin (4 * θ)) (4 * Real.cos (4 * θ)) θ := by
  have h := (Real.hasDerivAt_sin (4 * θ)).comp θ ((hasDerivAt_id θ).const_mul (4 : ℝ))
  have hfunc : (Real.sin ∘ fun x : ℝ => 4 * x) = fun θ : ℝ => Real.sin (4 * θ) := by
    funext x; rfl
  rw [hfunc] at h
  have hderiv : Real.cos (4 * θ) * (4 * 1) = 4 * Real.cos (4 * θ) := by ring
  rw [hderiv] at h
  exact h

/-! ## Clairaut on the open quadrant -/

/-- On the open quadrant, `∂_θ(D_zG) = D_z(∂_θG)`. -/
theorem pth_Dz_eq_Dz_pth {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pth (Work.Spaces.Dz G) z θ = Work.Spaces.Dz (Work.Spaces.pth G) z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.mem_Q0).mpr ⟨hz, hθ.1, hθ.2⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry G) (z, θ) :=
    (hG.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).of_le
      (by simp [Work.Stability.smoothOrder])
  have h1 : Work.Spaces.pth (Work.Spaces.Dz G) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz G) z θ := by
    show deriv (fun θ' : ℝ => z * Work.Spaces.pz G z θ') θ
      = z * Work.Spaces.pth (Work.Spaces.pz G) z θ
    rw [deriv_const_mul_field]
    rfl
  have h2 : Work.Spaces.Dz (Work.Spaces.pth G) z θ
      = z * Work.Spaces.pz (Work.Spaces.pth G) z θ := rfl
  rw [h1, h2, Work.Spaces.pz_pth_comm (f := G) hcd]

/-- The two slot-1 integrands agree a.e. on `Iz ×ˢ Iθ`. -/
theorem ae_pth_sq_eq {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)]
    (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.pth (Work.Spaces.Dz G) p.1 p.2) ^ 2) := by
  change ∀ᵐ p ∂(MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)),
    (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2) ^ 2) p
      = (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.pth (Work.Spaces.Dz G) p.1 p.2) ^ 2) p
  rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
    (measurableSet_Ici.prod measurableSet_Icc)]
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ))
    ∪ ((Set.univ : Set ℝ) ×ˢ ({(0 : ℝ), Real.pi / 2} : Set ℝ))) ?_ ?_
  · intro p hp
    obtain ⟨hpS, hpne⟩ := not_imp.mp hp
    obtain ⟨hz, hθ⟩ := Set.mem_prod.mp hpS
    by_cases hz0 : p.1 = 0
    · exact Or.inl ⟨hz0, Set.mem_univ _⟩
    · by_cases hθ0 : p.2 = 0
      · exact Or.inr ⟨Set.mem_univ _, Or.inl hθ0⟩
      · by_cases hθ1 : p.2 = Real.pi / 2
        · exact Or.inr ⟨Set.mem_univ _, Or.inr hθ1⟩
        · exfalso
          have hzpos : 0 < p.1 := lt_of_le_of_ne hz (Ne.symm hz0)
          have hθpos : 0 < p.2 := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
          have hθlt : p.2 < Real.pi / 2 := lt_of_le_of_ne hθ.2 hθ1
          have heq : Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2
              = Work.Spaces.pth (Work.Spaces.Dz G) p.1 p.2 :=
            (pth_Dz_eq_Dz_pth hG hzpos ⟨hθpos, hθlt⟩).symm
          exact hpne (by
            show (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
                * (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2) ^ 2
              = (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
                * (Work.Spaces.pth (Work.Spaces.Dz G) p.1 p.2) ^ 2
            rw [heq])
  · have h1 : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
        (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
      rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, MeasureTheory.Measure.prod_prod,
        MeasureTheory.measure_singleton, zero_mul]
    have hs : (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ({(0 : ℝ), Real.pi / 2} : Set ℝ) = 0 := by
      rw [show ({(0 : ℝ), Real.pi / 2} : Set ℝ) = {0} ∪ {Real.pi / 2} from by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
      exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
        (MeasureTheory.measure_singleton (Real.pi / 2))
    have h2 : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
        ((Set.univ : Set ℝ) ×ˢ ({(0 : ℝ), Real.pi / 2} : Set ℝ)) = 0 := by
      rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, MeasureTheory.Measure.prod_prod, hs,
        mul_zero]
    refine le_antisymm ?_ bot_le
    calc (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
          ((({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ))
            ∪ ((Set.univ : Set ℝ) ×ˢ ({(0 : ℝ), Real.pi / 2} : Set ℝ)))
        ≤ _ + _ := MeasureTheory.measure_union_le _ _
      _ = 0 := by rw [h1, h2, add_zero]

end Work.FTS.EllSol.PkgK5.TraceEngine
