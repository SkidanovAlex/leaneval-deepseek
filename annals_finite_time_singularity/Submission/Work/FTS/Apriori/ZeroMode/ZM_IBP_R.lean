import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Submission.Work.FTS.Apriori.ZeroMode.L12_ZMDefs
import Submission.Work.FM.Core2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Apriori.ZeroMode

open scoped Real Topology
open MeasureTheory Set Filter

theorem ZM_IBP_R {α : ℝ} {f : ℝ → ℝ → ℝ} (H : Work.FTS.Apriori.ZeroMode.L12Hyp α f)
    (hu : ContinuousOn (Work.FTS.Apriori.ZeroMode.uOf f) (Set.Ioi 0)) :
    ∀ ε ρ : ℝ, 0 < ε → ε < ρ →
      ∫ r in Set.Ioc ε ρ, Work.FTS.Apriori.ZeroMode.ROf f r / (1 + r) ^ 2
        = -(Work.FTS.Apriori.ZeroMode.ROf f ρ / (1 + ρ))
          + Work.FTS.Apriori.ZeroMode.ROf f ε / (1 + ε)
          - ∫ r in Set.Ioc ε ρ, Work.FTS.Apriori.ZeroMode.uOf f r / (1 + r) := by
  intro ε ρ hε hερ
  have hερle : ε ≤ ρ := le_of_lt hερ
  -- `ROf f r = ∫_r^∞ uOf f s ds` is a primitive of `-uOf f` (`hasDerivAt_L12`), so the
  -- identity is integration by parts with the antiderivative `r ↦ -1/(1+r)` of `(1+r)⁻²`.
  -- First rewrite the two set integrals over `Ioc ε ρ` as interval integrals `ε..ρ`.
  have hIoc1 : (∫ r in ε..ρ, Work.FTS.Apriori.ZeroMode.ROf f r / (1 + r) ^ 2)
      = ∫ r in Set.Ioc ε ρ, Work.FTS.Apriori.ZeroMode.ROf f r / (1 + r) ^ 2 :=
    intervalIntegral.integral_of_le hερle
  have hIoc2 : (∫ r in ε..ρ, Work.FTS.Apriori.ZeroMode.uOf f r / (1 + r))
      = ∫ r in Set.Ioc ε ρ, Work.FTS.Apriori.ZeroMode.uOf f r / (1 + r) :=
    intervalIntegral.integral_of_le hερle
  rw [← hIoc1, ← hIoc2]
  -- the integration interval lies in `(0,∞)`
  have hsub : Set.uIcc ε ρ ⊆ Set.Ioi (0 : ℝ) := by
    rw [Set.uIcc_of_le hερle]
    intro x hx
    exact Set.mem_Ioi.mpr (lt_of_lt_of_le hε hx.1)
  -- the density is integrable on `(0,∞)` (hypothesis `hintL2` of `L12Hyp`)
  have hint : IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 0) := by
    simpa only [Work.Construction.L12dens] using H.hintL2
  have hudens : ContinuousOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 0) := hu
  -- `ROf f` has derivative `-(uOf f)`
  have hderiv_u : ∀ x ∈ Set.uIcc ε ρ, HasDerivAt (Work.FTS.Apriori.ZeroMode.ROf f)
      (-(Work.FTS.Apriori.ZeroMode.uOf f x)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hsub hx
    have hcont : ContinuousAt (Work.FM.L12dens Work.Spaces.K f) x :=
      hudens.continuousAt (isOpen_Ioi.mem_nhds hx0)
    exact Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := f) (a := 0) (ρ := x)
      hint hcont hx0
  -- `r ↦ -1/(1+r)` has derivative `(1+r)⁻²`
  have hderiv_v : ∀ x ∈ Set.uIcc ε ρ,
      HasDerivAt (fun r : ℝ => -1 / (1 + r)) (1 / (1 + x) ^ 2) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hsub hx
    have hne : (1 + x : ℝ) ≠ 0 := by positivity
    have hlin : HasDerivAt (fun r : ℝ => 1 + r) 1 x := by
      simpa using (hasDerivAt_id x).const_add (1 : ℝ)
    have h := (hasDerivAt_const x (-1 : ℝ)).div hlin hne
    have hd : ((0 : ℝ) * (1 + x) - -1 * 1) / (1 + x) ^ 2 = 1 / (1 + x) ^ 2 := by
      congr 1; ring
    rw [hd] at h
    exact h
  have hInt_u : IntervalIntegrable (fun x : ℝ => -(Work.FTS.Apriori.ZeroMode.uOf f x))
      volume ε ρ :=
    (hu.neg.mono hsub).intervalIntegrable
  have hInt_v : IntervalIntegrable (fun x : ℝ => 1 / (1 + x) ^ 2) volume ε ρ := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · fun_prop
    · intro x hx
      have hx0 : (0 : ℝ) < x := hsub hx
      positivity
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := ε) (b := ρ)
    (u := Work.FTS.Apriori.ZeroMode.ROf f)
    (u' := fun x : ℝ => -(Work.FTS.Apriori.ZeroMode.uOf f x))
    (v := fun r : ℝ => -1 / (1 + r))
    (v' := fun x : ℝ => 1 / (1 + x) ^ 2)
    hderiv_u hderiv_v hInt_u hInt_v
  rw [show (∫ r in ε..ρ, Work.FTS.Apriori.ZeroMode.ROf f r / (1 + r) ^ 2)
      = ∫ r in ε..ρ, Work.FTS.Apriori.ZeroMode.ROf f r * (1 / (1 + r) ^ 2) from
    intervalIntegral.integral_congr (fun x _ => by rw [div_eq_mul_one_div])]
  rw [hibp]
  rw [show (∫ x in ε..ρ, (-(Work.FTS.Apriori.ZeroMode.uOf f x)) * (-1 / (1 + x)))
      = ∫ x in ε..ρ, Work.FTS.Apriori.ZeroMode.uOf f x / (1 + x) from
    intervalIntegral.integral_congr (fun x _ => by ring_nf)]
  ring_nf

end Work.FTS.Apriori.ZeroMode
