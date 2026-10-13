import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Radial.radGreenIntended
import Submission.Work.EllipticEst.ModalSolution.RGW.Defs
import Submission.Work.FTS.H2.ModalSolR.contOn_primitive_Ioc
import Submission.Work.FTS.H2.ModalSolR.contOn_tailIoi
import Submission.Work.FTS.H2.ModalSolR.integrableOn_Ioi_mul_rpow_neg
import Submission.Work.FTS.H2.ModalSolR.integrableOn_Ioc_mul_rpow_sub_one

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR

/-- **Continuity of the modal radial Green function on `(0,∞)`.**

`radGreen α m c` is the explicit Green's function of the mode-`m` Euler equation, i.e. the
combination `K·(z^{s⁻}·A(z) + z^{s⁺}·B(z))` of the primitive
`A z = ∫_0^z c t · t^{(2m+5)/α-1} dt` and the tail integral
`B z = ∫_z^∞ c t · t^{-2m/α-1} dt`, with `s⁻ = -(2m+5)/α`, `s⁺ = 2m/α` and
`K = 1/(α(4m+5))`.  Both integrands are integrable — the head weight obeys
`(2m+5)/α - 1 ≥ 4 > -1` because `α ≤ 1`, and the tail weight `-2m/α-1 ≤ -1` with the integral
taken over `(z,∞)`, `z > 0` — so the two integrals are honest and continuous, by
`contOn_primitive_Ioc` and `contOn_tailIoi`, and the prefactors `z^{s±}` are continuous on
`(0,∞)`. -/
theorem radGreenContinuousOn {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    ContinuousOn (Work.FTS.PhiStar.Radial.radGreen α m c) (Set.Ioi 0) := by
  -- The head exponent `(2m+5)/α` is `≥ 1`, the tail exponent `2m/α` is `≥ 0`.
  have hβ1 : (1 : ℝ) ≤ (2 * (m : ℝ) + 5) / α := by
    rw [le_div_iff₀ hα]
    have h5 : (1 : ℝ) ≤ 2 * (m : ℝ) + 5 := by
      have := Nat.cast_nonneg (α := ℝ) m
      linarith
    linarith
  have hβ2 : (0 : ℝ) ≤ 2 * (m : ℝ) / α :=
    div_nonneg (by positivity) (le_of_lt hα)
  -- Integrability of the two integrands, on `(0,z]` resp. `(z,∞)`.
  have hint1 : ∀ z ∈ Set.Ioi 0, MeasureTheory.IntegrableOn
      (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioc 0 z) :=
    fun z hz => integrableOn_Ioc_mul_rpow_sub_one (β := (2 * (m : ℝ) + 5) / α) hc hcm hβ1 hz
  have hint2 : ∀ z ∈ Set.Ioi 0, MeasureTheory.IntegrableOn
      (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi z) :=
    fun z hz => integrableOn_Ioi_mul_rpow_neg (β := 2 * (m : ℝ) / α) hc hcm hβ2 hz
  -- Continuity of the two integral pieces.
  have hw1 : ContinuousOn (fun t : ℝ => t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioi 0) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
  have hw2 : ContinuousOn (fun t : ℝ => t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 0) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
  have hA : ContinuousOn (fun z => ∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioi 0) :=
    contOn_primitive_Ioc (w := fun t : ℝ => t ^ ((2 * (m : ℝ) + 5) / α - 1)) hc hcm hw1 hint1
  have hB : ContinuousOn (fun z => ∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 0) :=
    contOn_tailIoi (w := fun t : ℝ => t ^ (-(2 * (m : ℝ) / α) - 1)) hc hcm hw2 hint2
  -- Continuity of the two power prefactors.
  have hpowN : ContinuousOn (fun z : ℝ => z ^ (-(2 * (m : ℝ) + 5) / α)) (Set.Ioi 0) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
  have hpowP : ContinuousOn (fun z : ℝ => z ^ (2 * (m : ℝ) / α)) (Set.Ioi 0) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
  -- Assembly: the value of `radGreen` is *definitionally* this combination.
  have hinner : ContinuousOn (fun z : ℝ =>
      z ^ (-(2 * (m : ℝ) + 5) / α) * (∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
        + z ^ (2 * (m : ℝ) / α) * (∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1)))
      (Set.Ioi 0) :=
    (hpowN.mul hA).add (hpowP.mul hB)
  refine (hinner.const_mul (1 / (α * (4 * (m : ℝ) + 5)))).congr (fun z _ => ?_)
  rfl

end Work.FTS.H2.ModalSolR
