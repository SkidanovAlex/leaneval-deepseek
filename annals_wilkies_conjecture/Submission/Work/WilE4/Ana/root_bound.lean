import Mathlib

namespace Work.WilE4.Ana

theorem root_bound {p : Polynomial ℝ} (hp : p ≠ 0) {y : ℝ} (hy : p.IsRoot y) :
    |y| ≤ 1 + (∑ i ∈ Finset.range p.natDegree, |p.coeff i|) / |p.leadingCoeff| := by
  -- Cauchy's bound (Mathlib) controls `‖y‖₊` by `p.cauchyBound`, whose numerator is the
  -- *max* of the coefficient norms; it is at most their *sum*, which is the bound we want.
  have hlt := Polynomial.IsRoot.norm_lt_cauchyBound hp hy
  have hsup : (Finset.range p.natDegree).sup (fun i => ‖p.coeff i‖₊) ≤
      ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖₊ :=
    Finset.sup_le (fun i hi =>
      Finset.single_le_sum (f := fun i => ‖p.coeff i‖₊) (fun j _ => zero_le) hi)
  have hmain : Polynomial.cauchyBound p ≤
      1 + (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖₊) / ‖p.leadingCoeff‖₊ := by
    calc Polynomial.cauchyBound p
        = (Finset.range p.natDegree).sup (fun i => ‖p.coeff i‖₊) / ‖p.leadingCoeff‖₊ + 1 := rfl
      _ ≤ (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖₊) / ‖p.leadingCoeff‖₊ + 1 :=
          add_le_add_left
            (div_le_div_of_nonneg_right hsup (zero_le : (0 : NNReal) ≤ ‖p.leadingCoeff‖₊)) 1
      _ = 1 + (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖₊) / ‖p.leadingCoeff‖₊ := by rw [add_comm]
  have hle : ‖y‖₊ ≤ 1 + (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖₊) / ‖p.leadingCoeff‖₊ :=
    hlt.le.trans hmain
  have hcoe := NNReal.coe_le_coe.mpr hle
  simpa using hcoe

end Work.WilE4.Ana
