import Mathlib

namespace Work.WilkiesH.NT

/-- The multiplicative height of a tuple `x : ι → K` over a number field is bounded above by
the product of the multiplicative heights of its coordinates.

The proof uses the "Segre embedding": `mulHeight₁ y = mulHeight ![y, 1]`, and the multiset
`∏ i, mulHeight₁ (x i)` is the `Height.mulHeight` of the multiplication table
`I ↦ ∏ i, ![x i, 1] (I i)` on `ι → Fin 2` (`Height.mulHeight_fun_prod_eq`).
The tuple `x` is the restriction of that table to the coordinates `I` that are `0` at exactly
one place, so the inequality is monotonicity of `Height.mulHeight` under composition
(`Height.mulHeight_comp_le`). -/
theorem mulHeight_le_prod_mulHeight1 {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    (x : ι → K) : Height.mulHeight x ≤ ∏ i, Height.mulHeight₁ (x i) := by
  classical
  -- `x` is the restriction of the multiplication table `I ↦ ∏ i, ![x i, 1] (I i)` along the
  -- embedding `i ↦ (fun j ↦ if j = i then 0 else 1)`.
  have key : (fun I : ι → Fin 2 => ∏ i, ![x i, (1 : K)] (I i)) ∘
      (fun i : ι => fun j : ι => if j = i then (0 : Fin 2) else 1) = x := by
    ext i
    simp only [Function.comp_apply]
    rw [Finset.prod_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  calc Height.mulHeight x
      = Height.mulHeight ((fun I : ι → Fin 2 => ∏ i, ![x i, (1 : K)] (I i)) ∘
          (fun i : ι => fun j : ι => if j = i then (0 : Fin 2) else 1)) := by rw [key]
    _ ≤ Height.mulHeight (fun I : ι → Fin 2 => ∏ i, ![x i, (1 : K)] (I i)) :=
        Height.mulHeight_comp_le _ _
    _ = ∏ i, Height.mulHeight ![x i, (1 : K)] :=
        Height.mulHeight_fun_prod_eq (x := fun i : ι => ![x i, (1 : K)]) (fun i => by simp)
    _ = ∏ i, Height.mulHeight₁ (x i) := by simp only [Height.mulHeight₁_eq_mulHeight]

end Work.WilkiesH.NT
