import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Filter

/-- Integration by parts for the power-weighted square on `(ε, x₁]` with `0 < ε < x₁`: if `v` is
`C^∞` on `(0, x₁]`, then with `D := derivWithin v (Set.Ioc 0 x₁)` (which is the honest `deriv v`
at every interior point)

  `(p+1) ∫_ε^{x₁} x^p v² = x₁^{p+1} v(x₁)² - ε^{p+1} v(ε)² - 2 ∫_ε^{x₁} x^{p+1} v D`,

the identity obtained by integrating `(x^{p+1} v²)' = (p+1)x^p v² + 2x^{p+1} v D` over the
interval. -/
lemma powerIbp (p x₁ ε : ℝ) (hε : 0 < ε) (hεx : ε < x₁) (v : ℝ → ℝ)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (Set.Ioc 0 x₁)) :
    (p + 1) * (∫ x in ε..x₁, x ^ p * (v x) ^ 2)
      = x₁ ^ (p + 1) * (v x₁) ^ 2 - ε ^ (p + 1) * (v ε) ^ 2
        - 2 * (∫ x in ε..x₁, x ^ (p + 1) * (v x * derivWithin v (Set.Ioc 0 x₁) x)) := by
  have hle : ε ≤ x₁ := le_of_lt hεx
  set s := Set.Ioc (0 : ℝ) x₁ with hs
  set D : ℝ → ℝ := fun x => derivWithin v s x with hD
  set F : ℝ → ℝ := fun x => x ^ (p + 1) * (v x) ^ 2 with hF
  set f' : ℝ → ℝ := fun x => (p + 1) * (x ^ p * (v x) ^ 2)
    + 2 * (x ^ (p + 1) * (v x * D x)) with hf'
  have hDs : ContinuousOn D s := by
    rw [hD]
    exact hv.continuousOn_derivWithin (uniqueDiffOn_Ioc 0 x₁) (by simp)
  have hvcont : ContinuousOn v s := hv.continuousOn
  have hpowp : ContinuousOn (fun x : ℝ => x ^ p) s :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))
  have hpowp1 : ContinuousOn (fun x : ℝ => x ^ (p + 1)) s :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))
  have hf'cont : ContinuousOn f' s := by
    rw [hf']
    exact ((hpowp.mul (hvcont.pow 2)).const_mul (p + 1)).add
      ((hpowp1.mul (hvcont.mul hDs)).const_mul 2)
  have hIcc_sub : Set.Icc ε x₁ ⊆ s := fun x hx => ⟨lt_of_lt_of_le hε hx.1, hx.2⟩
  have hf'contIcc : ContinuousOn f' (Set.Icc ε x₁) := hf'cont.mono hIcc_sub
  have hint : IntervalIntegrable f' volume ε x₁ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hle]
    exact hf'contIcc
  have hFcont : ContinuousOn F (Set.Icc ε x₁) := by
    rw [hF]
    exact (hpowp1.mono hIcc_sub).mul ((hvcont.mono hIcc_sub).pow 2)
  have hderiv : ∀ x ∈ Set.Ioo ε x₁, HasDerivAt F (f' x) x := by
    intro x hx
    have hxpos : 0 < x := lt_trans hε hx.1
    have hxlt : x < x₁ := hx.2
    have hxs : x ∈ s := ⟨hxpos, le_of_lt hxlt⟩
    have hmem : s ∈ nhds x :=
      mem_of_superset (Ioo_mem_nhds hxpos hxlt)
        (fun y (hy : y ∈ Set.Ioo (0 : ℝ) x₁) => ⟨hy.1, le_of_lt hy.2⟩)
    have hDx : D x = deriv v x := by
      rw [hD]
      exact derivWithin_of_mem_nhds hmem
    have hvderiv : HasDerivAt v (deriv v x) x :=
      (((hv.contDiffWithinAt hxs).differentiableWithinAt (by simp)).differentiableAt hmem).hasDerivAt
    have h1 : HasDerivAt (fun y : ℝ => y ^ (p + 1)) ((p + 1) * x ^ p) x := by
      simpa using Real.hasDerivAt_rpow_const (x := x) (p := p + 1) (Or.inl (ne_of_gt hxpos))
    have h2 : HasDerivAt (fun y : ℝ => (v y) ^ 2) (2 * v x * deriv v x) x := by
      convert hvderiv.pow 2 using 1; ring
    have hmul : HasDerivAt (fun y : ℝ => y ^ (p + 1) * (v y) ^ 2)
        (((p + 1) * x ^ p) * (v x) ^ 2 + x ^ (p + 1) * (2 * v x * deriv v x)) x := by
      convert h1.mul h2 using 1
    rw [hF]
    have hfx : f' x = ((p + 1) * x ^ p) * (v x) ^ 2 + x ^ (p + 1) * (2 * v x * deriv v x) := by
      show (p + 1) * (x ^ p * (v x) ^ 2) + 2 * (x ^ (p + 1) * (v x * D x)) = _
      rw [hDx]; ring
    rw [hfx]
    exact hmul
  have hFTC : ∫ y in ε..x₁, f' y = F x₁ - F ε :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hFcont hderiv hint
  have hg1cont : ContinuousOn (fun y : ℝ => (p + 1) * (y ^ p * (v y) ^ 2)) (Set.Icc ε x₁) :=
    ((hpowp.mul (hvcont.pow 2)).const_mul (p + 1)).mono hIcc_sub
  have hg2cont : ContinuousOn (fun y : ℝ => 2 * (y ^ (p + 1) * (v y * D y))) (Set.Icc ε x₁) :=
    ((hpowp1.mul (hvcont.mul hDs)).const_mul 2).mono hIcc_sub
  have hg1int : IntervalIntegrable (fun y : ℝ => (p + 1) * (y ^ p * (v y) ^ 2)) volume ε x₁ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hle]
    exact hg1cont
  have hg2int : IntervalIntegrable (fun y : ℝ => 2 * (y ^ (p + 1) * (v y * D y))) volume ε x₁ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hle]
    exact hg2cont
  have hexp : (∫ y in ε..x₁, f' y)
      = (p + 1) * (∫ y in ε..x₁, y ^ p * (v y) ^ 2)
        + 2 * (∫ y in ε..x₁, y ^ (p + 1) * (v y * D y)) := by
    rw [hf']
    rw [intervalIntegral.integral_add hg1int hg2int]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have key : (p + 1) * (∫ y in ε..x₁, y ^ p * (v y) ^ 2)
      + 2 * (∫ y in ε..x₁, y ^ (p + 1) * (v y * D y))
      = x₁ ^ (p + 1) * (v x₁) ^ 2 - ε ^ (p + 1) * (v ε) ^ 2 := by
    rw [← hexp, hFTC]
  have hDfun : ∀ y, D y = derivWithin v (Set.Ioc 0 x₁) y := by
    intro y; rw [hD]
  have hIntD : (∫ y in ε..x₁, y ^ (p + 1) * (v y * D y))
      = ∫ y in ε..x₁, y ^ (p + 1) * (v y * derivWithin v (Set.Ioc 0 x₁) y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    simp only [hDfun]
  have key2 : (p + 1) * (∫ y in ε..x₁, y ^ p * (v y) ^ 2)
      + 2 * (∫ y in ε..x₁, y ^ (p + 1) * (v y * derivWithin v (Set.Ioc 0 x₁) y))
      = x₁ ^ (p + 1) * (v x₁) ^ 2 - ε ^ (p + 1) * (v ε) ^ 2 := by
    rw [← hIntD]; exact key
  linarith [key2]

end Work.FTS.H2.DivQ
