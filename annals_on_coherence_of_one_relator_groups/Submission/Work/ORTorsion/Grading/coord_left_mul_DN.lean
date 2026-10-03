import Mathlib
import Submission.Work.ORTorsion.Defs

set_option autoImplicit false

open Work.ORTorsion
open Work.ORTorsion.LaurentBase

namespace Work.ORTorsion.Grading

/-!
# Left `D(N)`-linearity of the coordinate maps

For the Laurent datum `Lb` attached to a surjection `φ : H ↠ ℤ` with kernel `N` and subalgebra
`R = Σ_{h ∈ H} D(N) h`, the degree-`j` coordinate map `coord j : R → D(N)` is left `D(N)`-linear:
for `a ∈ D(N)` and `y ∈ R`, the degree-`j` coordinate of the product `a · y` is `a` times the
degree-`j` coordinate of `y`.

The proof writes `y = ∑ i ∈ S, (coord i y) · u ^ i` using the reconstruction field `coord_expand`,
moves the left factor `a` inside the sum (`Finset.mul_sum`), uses that left multiplication by
`a ∈ D(N)` commutes with the right shift `· u ^ i` (so that
`a · (coord i y · u ^ i) = (a · coord i y) · u ^ i`), and reads off the degree-`j` part with
`coord_base`.
-/

/-- **Left `D(N)`-linearity of the coordinate maps.**  For `a ∈ D(N)`, the degree-`j` coordinate
of the product `a · y` in `R ⊆ U` is `a` times the degree-`j` coordinate of `y`. -/
theorem coord_left_mul_DN {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Algebra K U] (L : TorsionData K G U) {H : Subgroup G} {φ : H →* Multiplicative ℤ}
    (Lb : LaurentBase K U G L.gen L.D H φ) (a : ↥(L.D Lb.N)) (j : ℤ) (y : ↥Lb.R) :
    Lb.coord j (⟨(a : U), Lb.DN_le_R a.2⟩ * y) = a * Lb.coord j y := by
  obtain ⟨S, hS⟩ := Lb.coord_expand y
  have hmul : (⟨(a : U), Lb.DN_le_R a.2⟩ : ↥Lb.R) * y
      = ∑ i ∈ S, Lb.rightMulU i (⟨((a * Lb.coord i y : ↥(L.D Lb.N)) : U),
          Lb.DN_le_R (a * Lb.coord i y).2⟩ : ↥Lb.R) := by
    conv_lhs => rw [← hS, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Lb.rightMulU_coe]
    rw [mul_assoc]
  have hsum : Lb.coord j (⟨(a : U), Lb.DN_le_R a.2⟩ * y)
      = ∑ i ∈ S, (if j = i then a * Lb.coord i y else 0) := by
    rw [hmul, map_sum]
    exact Finset.sum_congr rfl (fun i _ => Lb.coord_base j i (a * Lb.coord i y))
  rw [hsum, Finset.sum_ite_eq]
  by_cases hj : j ∈ S
  · rw [if_pos hj]
  · rw [if_neg hj]
    have hz : Lb.coord j y = 0 := by
      have h1 : Lb.coord j y
          = ∑ i ∈ S, Lb.coord j (Lb.rightMulU i
              (⟨(Lb.coord i y : U), Lb.DN_le_R (Lb.coord i y).2⟩ : ↥Lb.R)) := by
        conv_lhs => rw [← hS, map_sum]
      calc Lb.coord j y
          = ∑ i ∈ S, Lb.coord j (Lb.rightMulU i
              (⟨(Lb.coord i y : U), Lb.DN_le_R (Lb.coord i y).2⟩ : ↥Lb.R)) := h1
        _ = ∑ i ∈ S, (if j = i then Lb.coord i y else 0) :=
              Finset.sum_congr rfl (fun i _ => Lb.coord_base j i (Lb.coord i y))
        _ = (if j ∈ S then Lb.coord j y else 0) :=
              Finset.sum_ite_eq S j (fun i => Lb.coord i y)
        _ = 0 := by rw [if_neg hj]
    rw [hz, mul_zero]

end Work.ORTorsion.Grading
