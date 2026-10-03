import Mathlib
import Submission.Work.ORHughesFree.Prop51.ConclB
import Submission.Work.ORHughesFree.SkewLaurentSeries.isDivisionRing_skewLaurentSeries

namespace Work.ORHughesFree.Prop51

open Work.ORHughesFree

/-- **`⋄` of `laurentEmbed f` is `laurentEmbed` of the inverse of `f`.**  Let
`x = laurentEmbed f ∈ D_{H,P}` where `f` is a unit of `D_{N,P}((t;τ))` with inverse `u`.  Then `x`
is a unit of `P` with inverse `laurentEmbed u`, so its `⋄`-inverse inside `D_{H,P}` is
`laurentEmbed u` again: `ratOp_of_isUnit` computes `⋄` on the units of `D_{H,P}`, and the inverse
is unique.

(Step 1 of the proof of the `⋄` case of [JZLA20, Proposition 5.1], see `conclB_ratOp`.  The
element `laurentEmbed u` is exhibited as an element of `D_{H,P}` only indirectly, through
`DH_inv_closed` applied to the unit `x` of `P`.) -/
theorem ratOp_eq_laurentEmbed_inv {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Work.ORHughesFree.Prop51Data Γ P DN)
    {x : P} (hx : x ∈ d.DH) {f u : Work.ORHughesFree.SkewLaurentSeries ↥DN}
    (hf : d.laurentEmbed f = x) (hu : f * u = 1) (hu' : u * f = 1) :
    ((d.rDH.ratOp ⟨x, hx⟩ : ↥d.DH) : P) = d.laurentEmbed u := by
  -- `x` is a unit of `P`, with inverse `laurentEmbed u`.
  have hxu : x * d.laurentEmbed u = 1 := by rw [← hf, ← map_mul, hu, map_one]
  have hux : d.laurentEmbed u * x = 1 := by rw [← hf, ← map_mul, hu', map_one]
  have hunitP : IsUnit x := ⟨⟨x, d.laurentEmbed u, hxu, hux⟩, rfl⟩
  -- `D_{H,P}` is a division closure, so it contains a right inverse `y` of `x`.
  obtain ⟨y, hy, hxy⟩ := d.DH_inv_closed x hx hunitP
  -- ... which, by uniqueness of inverses in `P`, is `laurentEmbed u`.
  have hyz : y = d.laurentEmbed u := by
    calc y = 1 * y := (one_mul y).symm
      _ = (d.laurentEmbed u * x) * y := by rw [hux]
      _ = d.laurentEmbed u * (x * y) := mul_assoc _ _ _
      _ = d.laurentEmbed u * 1 := by rw [hxy]
      _ = d.laurentEmbed u := mul_one _
  have hyx : y * x = 1 := by rw [hyz, hux]
  -- hence `⟨x, hx⟩` is a unit of `D_{H,P}`, and `ratOp` is inversion on units.
  have hunitDH : IsUnit (⟨x, hx⟩ : ↥d.DH) :=
    ⟨⟨⟨x, hx⟩, ⟨y, hy⟩, Subtype.ext hxy, Subtype.ext hyx⟩, rfl⟩
  have hrat : (⟨x, hx⟩ : ↥d.DH) * d.rDH.ratOp ⟨x, hx⟩ = 1 := d.ratOp_of_isUnit _ hunitDH
  have heq : d.rDH.ratOp ⟨x, hx⟩ = (⟨y, hy⟩ : ↥d.DH) :=
    IsUnit.mul_left_cancel hunitDH (hrat.trans (Subtype.ext hxy).symm)
  rw [heq]
  exact hyz

end Work.ORHughesFree.Prop51
