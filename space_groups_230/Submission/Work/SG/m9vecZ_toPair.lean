import Mathlib
import Submission.Work.SG.SGprelude

namespace Work.SG

/-- Restatement aid: when the parameter type of the map `n ↦ n / d` is left implicit,
Lean elaborates `l.map fun n => (n : ℚ) / (d : ℚ)` (for `l : List ℤ`) through a `do`-block
form; this identifies it with the explicitly typed variant. -/
private lemma map_div_coe (l : List ℤ) (d : ℕ) :
    (l.map fun n => (n : ℚ) / (d : ℚ)) = l.map (fun n : ℤ => (n : ℚ) / (d : ℚ)) := by
  rw [List.bind_eq_flatMap]
  change List.map (fun n : ℚ => n / (d : ℚ))
      (List.flatMap (fun a : ℤ => [(a : ℚ)]) l) = List.map (fun n : ℤ => (n : ℚ) / (d : ℚ)) l
  rw [← List.map_eq_flatMap, List.map_map]
  rfl

/-- The integer and rational flat matrix–vector products agree up to the common
denominator `d`, with the scaling map written with an explicit domain. -/
private lemma m9vec_map_div_annot (a v : List ℤ) (d : ℕ) :
    m9vec a (v.map (fun n : ℤ => (n : ℚ) / (d : ℚ))) =
      (m9vecZ a v).map (fun n : ℤ => (n : ℚ) / (d : ℚ)) := by
  -- `getD` of the scaled list is the scaled `getD`.
  have hget : ∀ (k : ℕ),
      (v.map (fun n : ℤ => (n : ℚ) / (d : ℚ))).getD k 0 = ((v.getD k 0 : ℤ) : ℚ) / (d : ℚ) := by
    intro k
    have h := List.getD_map v (0 : ℤ) (n := k) (f := fun n : ℤ => (n : ℚ) / (d : ℚ))
    rw [show (((0 : ℤ) : ℚ) / (d : ℚ)) = (0 : ℚ) from by norm_num] at h
    exact h
  have h3 : (List.range 3) = [0, 1, 2] := rfl
  -- Expand both sides into explicit length-three vectors and the three coordinate
  -- equations, then finish by casting and ring arithmetic.
  simp only [m9vec, m9vecZ, h3, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hget,
    List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> (push_cast; ring)

/-- The integer matrix-vector product matches the rational one at a common denominator. -/
theorem m9vecZ_toPair (a v : List ℤ) (d : ℕ) :
    m9vec a (v.map fun n => (n : ℚ) / (d : ℚ)) =
      (m9vecZ a v).map fun n => (n : ℚ) / (d : ℚ) := by
  simpa only [map_div_coe] using m9vec_map_div_annot a v d

end Work.SG
