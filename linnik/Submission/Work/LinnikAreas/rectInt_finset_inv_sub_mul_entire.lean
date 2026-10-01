import Mathlib
import Submission.Work.LinnikAreas.ZetaTentPrelude

namespace Work.LinnikAreas

open Complex MeasureTheory intervalIntegral Filter
open scoped Real Topology BigOperators

/-- The function `z ↦ (z - u)⁻¹` is complex-differentiable on any set avoiding `u`. -/
private lemma differentiableOn_inv_sub (u : ℂ) {s : Set ℂ} (hs : ∀ x ∈ s, x ≠ u) :
    DifferentiableOn ℂ (fun z => (z - u)⁻¹) s := by
  have h : DifferentiableOn ℂ (fun z : ℂ => z - u) s := differentiableOn_id.sub_const u
  exact h.inv (fun x hx hx0 => hs x hx (sub_eq_zero.mp hx0))

/-- Residue on the rectangle of `s ↦ (s - u)⁻¹ · G s` for an entire `G` and a pole `u`
strictly inside the rectangle: the integral equals `G u · 2πi`. -/
private lemma rectInt_inv_sub_mul_entire_inside {z w u : ℂ} {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huin : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im) :
    Commons.NumberTheory.DirichletCharacter.rectInt z w (fun s => (s - u)⁻¹ * G s) =
      G u * (2 * (Real.pi : ℂ) * Complex.I) := by
  have hds : Differentiable ℂ (dslope G u) :=
    Commons.NumberTheory.DirichletCharacter.dslope_differentiable_of_differentiable hG u
  have hpt : ∀ s ∈ Commons.NumberTheory.DirichletCharacter.rectBoundary z w,
      (s - u)⁻¹ * G s = dslope G u s + G u * (s - u)⁻¹ := by
    intro s hs
    have hsune : s ≠ u :=
      Commons.NumberTheory.DirichletCharacter.ne_of_mem_rectBoundary_of_inside huin hs
    rw [dslope_of_ne G hsune, slope_def_module]
    simp only [smul_eq_mul]
    ring
  have hcont1 : ∀ s ∈ Commons.NumberTheory.DirichletCharacter.rectBoundary z w,
      ContinuousAt (fun s : ℂ => dslope G u s) s := fun s _ => (hds s).continuousAt
  have hcont2 : ∀ s ∈ Commons.NumberTheory.DirichletCharacter.rectBoundary z w,
      ContinuousAt (fun s : ℂ => G u * (s - u)⁻¹) s := by
    intro s hs
    have hsu : s - u ≠ 0 := sub_ne_zero.mpr
      (Commons.NumberTheory.DirichletCharacter.ne_of_mem_rectBoundary_of_inside huin hs)
    exact ContinuousAt.mul continuousAt_const
      (ContinuousAt.inv₀ (continuousAt_id.sub continuousAt_const) hsu)
  rw [Commons.NumberTheory.DirichletCharacter.rectInt_congr_boundary' hpt]
  have a1 := Commons.NumberTheory.DirichletCharacter.intervalIntegrable_of_boundary_continuousAt
    hcont1
  have a2 := Commons.NumberTheory.DirichletCharacter.intervalIntegrable_of_boundary_continuousAt
    hcont2
  rw [Commons.NumberTheory.DirichletCharacter.rectInt_add''
      a1.1 a2.1 a1.2.1 a2.2.1 a1.2.2.1 a2.2.2.1 a1.2.2.2 a2.2.2.2,
    Commons.NumberTheory.DirichletCharacter.rectInt_entire_eq_zero hds, zero_add]
  rw [show (fun s : ℂ => G u * (s - u)⁻¹) = (fun s : ℂ => G u / (s - u)) by
        funext s; rw [div_eq_mul_inv]]
  rw [Commons.NumberTheory.DirichletCharacter.rectInt_const_div_sub_inside (G u) hzre hzim huin]

/-- The rectangle integral of `s ↦ (s - u)⁻¹ · G s` vanishes when the pole `u` lies
strictly outside the closed rectangle and `G` is entire. -/
private lemma rectInt_inv_sub_mul_entire_outside {z w u : ℂ} {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (huout : u ∉ Commons.NumberTheory.DirichletCharacter.rectSet z w) :
    Commons.NumberTheory.DirichletCharacter.rectInt z w (fun s => (s - u)⁻¹ * G s) = 0 := by
  apply Commons.NumberTheory.DirichletCharacter.rectInt_eq_zero_of_differentiableOn
  refine DifferentiableOn.mul ?_ hG.differentiableOn
  exact differentiableOn_inv_sub u (fun x hx h => huout (h ▸ hx))

theorem rectInt_finset_inv_sub_mul_entire {z w : ℂ} {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hzre : z.re < w.re) (hzim : z.im < w.im) (S : Finset ℂ) (c : ℂ → ℂ)
    (hnb : ∀ u ∈ S, u ∉ Commons.NumberTheory.DirichletCharacter.rectBoundary z w) :
    Commons.NumberTheory.DirichletCharacter.rectInt z w
        (fun s => (∑ u ∈ S, c u * (s - u)⁻¹) * G s) =
      ∑ u ∈ S, c u * (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then
        G u * (2 * (Real.pi : ℂ) * Complex.I) else 0) := by
  have hsplit : Commons.NumberTheory.DirichletCharacter.rectInt z w
        (fun s => (∑ u ∈ S, c u * (s - u)⁻¹) * G s)
      = Commons.NumberTheory.DirichletCharacter.rectInt z w
        (fun s => ∑ u ∈ S, c u * ((s - u)⁻¹ * G s)) := by
    apply Commons.NumberTheory.DirichletCharacter.rectInt_congr_boundary'
    intro s hs
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun u hu => by ring)
  rw [hsplit]
  have hcont : ∀ u ∈ S, ∀ s ∈ Commons.NumberTheory.DirichletCharacter.rectBoundary z w,
      ContinuousAt (fun s : ℂ => c u * ((s - u)⁻¹ * G s)) s := by
    intro u hu s hs
    have hsu : s - u ≠ 0 := sub_ne_zero.mpr (fun h => hnb u hu (h ▸ hs))
    exact ContinuousAt.mul continuousAt_const
      (ContinuousAt.mul (ContinuousAt.inv₀ (continuousAt_id.sub continuousAt_const) hsu)
        (hG s).continuousAt)
  rw [Commons.NumberTheory.DirichletCharacter.rectInt_finset_sum_of_boundary S hcont]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  rw [Commons.NumberTheory.DirichletCharacter.rectInt_const_mul' (c u)
    (fun s => (s - u)⁻¹ * G s)]
  by_cases huin : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im
  · rw [if_pos huin, rectInt_inv_sub_mul_entire_inside hG hzre hzim huin]
  · rw [if_neg huin, rectInt_inv_sub_mul_entire_outside hG
      (Commons.NumberTheory.DirichletCharacter.notMem_rectSet_of_outside hzre hzim
        (Commons.NumberTheory.DirichletCharacter.outside_of_not_inside hzre hzim huin
          (hnb u hu))),
      mul_zero]

end Work.LinnikAreas
