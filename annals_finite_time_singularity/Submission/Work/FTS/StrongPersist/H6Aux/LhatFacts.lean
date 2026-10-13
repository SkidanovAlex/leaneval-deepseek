/-
# `Work.FTS.StrongPersist.H6Aux.LhatFacts` — membership and norm bounds for `Lhat`

The commutator induction needs, at every level `n`:
* the *membership* `HkMem α m (Lhat g)` from the order-`(m+1)` honesty of `g` (to feed the
  additivity clause of the pairing), and
* the *norm* comparison `HkSq α m (Lhat g) ≤ C · HkSq α (m+1) g`.

Both follow from the pointwise integrand domination `Lhat_integrand_le` (the order-`m`
integrand of `Lhat g` is bounded by a constant times the order-`(m+1)` integrand of `g`),
extended to the closed quadrant `Iz × Iθ` (where both integrands vanish at the boundary lines
`z = 0` and `sin(2θ) = 0`) and integrated with `HkMem_of_majorant`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Aux.Facts
import Submission.Work.FTS.StrongPersist.H6Aux.Lhat_integrand_le
import Submission.Work.FTS.LocData.HkMem_of_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **Extension of a pointwise integrand bound to the closed quadrant.**  Both integrands
vanish on the two boundary lines `z = 0` and `sin(2θ) = 0`, so a bound valid on the open
quadrant extends to `Iz × Iθ` as soon as the constant is nonnegative. -/
theorem HkIntegrand_le_Izθ_of_Ioo {α : ℝ} (hα : 0 < α) {m l : ℕ} {X Y : Fn} {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.HkIntegrand α m X z θ ≤ C * Work.Spaces.HkIntegrand α l Y z θ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α m X z θ ≤ C * Work.Spaces.HkIntegrand α l Y z θ := by
  intro z hz θ hθ
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · rw [← hz0, Work.FTS.LocData.HkIntegrand_zero_fst]
    exact mul_nonneg hC (Work.Spaces.HkIntegrand_nonneg α l Y 0 θ)
  · by_cases hsin : Real.sin (2 * θ) = 0
    · rw [Work.FTS.StrongPersist.HkIntegrand_eq_zero_of_sin_zero (α := α) hα (k := m) hsin]
      exact mul_nonneg hC (Work.Spaces.HkIntegrand_nonneg α l Y z θ)
    · have hsinpos : 0 < Real.sin (2 * θ) :=
        lt_of_le_of_ne (Work.Elliptic.sin_two_nonneg_of_mem hθ) (Ne.symm hsin)
      have hθIoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        Work.FTS.CoercivityFix.Coer1.mem_Ioo_of_mem_Iθ_of_sin_pos hθ hsinpos
      exact h z hzpos θ hθIoo

/-- **The pointwise integrand domination for `Lhat`**, on the closed quadrant. -/
theorem Lhat_HkIntegrand_le (α : ℝ) (hα : 0 < α) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α m (Work.FTS.CoercivityFix.Lhat g) z θ
          ≤ C * Work.Spaces.HkIntegrand α (m + 1) g z θ := by
  obtain ⟨C, hC, h⟩ := Lhat_integrand_le α hα m
  exact ⟨C, hC, fun g hs => HkIntegrand_le_Izθ_of_Ioo (α := α) (m := m) (l := m + 1)
    (X := Work.FTS.CoercivityFix.Lhat g) (Y := g) (C := C) hα hC.le (h g hs)⟩

/-- **`ℋ^m`-membership of `Lhat g`** from the order-`(m+1)` honesty of `g`. -/
theorem Lhat_mem (α : ℝ) (hα : 0 < α) (m : ℕ) {g : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen g) (hm : Work.Spaces.HkMem α (m + 1) g) :
    Work.Spaces.HkMem α m (Work.FTS.CoercivityFix.Lhat g) := by
  obtain ⟨C, hC, h⟩ := Lhat_HkIntegrand_le α hα m
  refine Work.FTS.LocData.HkMem_of_majorant α m
    (f := Work.FTS.CoercivityFix.Lhat g)
    (M := fun z θ => C * Work.Spaces.HkIntegrand α (m + 1) g z θ)
    ((q0Sm_Lhat hs m).continuousOn_HkIntegrand α) ?_ ?_ ?_
  · intro z hz
    exact (hm.1 z hz).const_mul C
  · have hI2 : MeasureTheory.IntegrableOn (fun z => C * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α (m + 1) g z θ)) Work.Spaces.Iz := hm.2.const_mul C
    refine hI2.congr (Filter.Eventually.of_forall fun z => ?_)
    exact (MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iθ) C
      (fun θ => Work.Spaces.HkIntegrand α (m + 1) g z θ)).symm
  · intro z hz θ hθ
    exact h g hs z hz θ hθ

/-- **The integrated form**: `|Lhat g|²_{ℋ^m} ≤ C·|g|²_{ℋ^{m+1}}`. -/
theorem HkSq_Lhat_le (α : ℝ) (hα : 0 < α) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α (m + 1) g →
        Work.Spaces.HkSq α m (Work.FTS.CoercivityFix.Lhat g)
          ≤ C * Work.Spaces.HkSq α (m + 1) g := by
  obtain ⟨C, hC, h⟩ := Lhat_HkIntegrand_le α hα m
  refine ⟨C, hC, fun g hs hm => ?_⟩
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  have hout : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m
          (Work.FTS.CoercivityFix.Lhat g) z θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m + 1) g z θ) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    have hinner : (∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α (m + 1) g z θ)
        = C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m + 1) g z θ) :=
      MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iθ) C _
    rw [← hinner]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α m
        (Work.FTS.CoercivityFix.Lhat g) z θ) ((hm.1 z hz).const_mul C) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    exact h g hs z hz θ hθ
  refine le_trans (MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α m (Work.FTS.CoercivityFix.Lhat g) z θ)
    (hm.2.const_mul C) hout) ?_
  exact le_of_eq (MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iz) C
    (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m + 1) g z θ))

end Work.FTS.StrongPersist.H6Aux
