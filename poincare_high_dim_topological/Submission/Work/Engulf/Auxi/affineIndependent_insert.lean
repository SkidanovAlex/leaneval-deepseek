import Mathlib
import Submission.Work.PL.Defs

namespace Work.Engulf.Aux

/-- A simplex together with an apex outside its affine span is affinely independent: if the finite
vertex set `u` is affinely independent and `a` is outside `affineSpan ℝ u`, then `insert a u` is
affinely independent. (Used to check the `indep` field of the cone complex.) -/
theorem affineIndependent_insert {N : ℕ} {u : Finset (PL.E N)} {a : PL.E N}
    (hu : AffineIndependent ℝ (fun v : u => (v : PL.E N)))
    (ha : a ∉ affineSpan ℝ (u : Set (PL.E N))) :
    AffineIndependent ℝ (fun v : (insert a u : Finset (PL.E N)) => (v : PL.E N)) := by
  have hau : a ∉ u := by
    intro h
    exact ha (subset_affineSpan ℝ (u : Set (PL.E N)) (by simpa using h))
  let i : (insert a u : Finset (PL.E N)) := ⟨a, Finset.mem_insert_self a u⟩
  let e : u ≃ { y : (insert a u : Finset (PL.E N)) // y ≠ i } :=
    { toFun := fun t => ⟨⟨t.1, Finset.mem_insert_of_mem t.2⟩,
        fun h => hau (by
          have h' : (t : PL.E N) = a := by simpa [i] using Subtype.ext_iff.mp h
          exact h' ▸ t.2)⟩
      invFun := fun y => ⟨y.1.1, by
        rcases Finset.mem_insert.mp y.1.2 with h | h
        · exact absurd (Subtype.ext h) y.2
        · exact h⟩
      left_inv := fun t => by ext; rfl
      right_inv := fun y => by ext; rfl }
  have h1 : AffineIndependent ℝ
      (fun x : { y : (insert a u : Finset (PL.E N)) // y ≠ i } => (x : PL.E N)) :=
    (affineIndependent_equiv e
      (p := fun x : { y : (insert a u : Finset (PL.E N)) // y ≠ i } => (x : PL.E N))).mp hu
  have hset : (fun v : (insert a u : Finset (PL.E N)) => (v : PL.E N)) '' {x | x ≠ i}
      = (u : Set (PL.E N)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases Finset.mem_insert.mp x.2 with h | h
      · exact absurd (Subtype.ext h) hx
      · exact h
    · intro hy
      exact ⟨⟨y, Finset.mem_insert_of_mem hy⟩, fun h => hau (by
        have h' : y = a := by simpa [i] using Subtype.ext_iff.mp h
        exact h' ▸ hy), rfl⟩
  refine AffineIndependent.affineIndependent_of_notMem_span (k := ℝ) (i := i) h1 ?_
  rw [hset]
  simpa using ha

end Work.Engulf.Aux
