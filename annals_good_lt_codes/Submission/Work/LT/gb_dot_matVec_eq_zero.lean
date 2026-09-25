import Mathlib
import Submission.Work.LT.gb_rank_defs

namespace Work.LT

/-- Membership in `(GB.dotForm D).orthogonal C` unwound for the dot product: if `u ⊥ C` then
`GB.dot u c = 0` for every `c ∈ C`. -/
lemma gb_dot_eq_zero_of_mem_orthogonal {D : ℕ} {C : Submodule (ZMod 2) (Fin D → ZMod 2)}
    {u : Fin D → ZMod 2} (hu : u ∈ (GB.dotForm D).orthogonal C) :
    ∀ c ∈ C, GB.dot u c = 0 := by
  intro c hc
  have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hu) c hc
  rw [GB.dotForm_apply, GB.dot_comm] at h
  exact h

/-- Column-wise part of the pairing: if every column of `a` lies in `CA` and `u ⊥ CA`, then
`u` pairs to zero with `a * w`. -/
lemma gb_dot_matVec_colwise_eq_zero {D : ℕ} {CA : Submodule (ZMod 2) (Fin D → ZMod 2)}
    {a : Fin D × Fin D → ZMod 2} (ha : GB.IsColwise CA a) {u : Fin D → ZMod 2}
    (hu : ∀ c ∈ CA, GB.dot u c = 0) (w : Fin D → ZMod 2) :
    GB.dot u (GB.matVec a w) = 0 := by
  have ha' : ∀ j, GB.dot u (GB.col a j) = 0 := fun j => hu _ (ha j)
  simp only [GB.dot, GB.matVec, GB.col] at ha' ⊢
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have h1 : (∑ i, u i * (a (i, j) * w j)) = (∑ i, u i * a (i, j)) * w j := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h1, ha' j, zero_mul]

/-- Row-wise part of the pairing: if every row of `b` lies in `CB` and `v ⊥ CB`, then
`u` pairs to zero with `b * v`. -/
lemma gb_dot_matVec_rowwise_eq_zero {D : ℕ} {CB : Submodule (ZMod 2) (Fin D → ZMod 2)}
    {b : Fin D × Fin D → ZMod 2} (hb : GB.IsRowwise CB b) {u v : Fin D → ZMod 2}
    (hv : ∀ c ∈ CB, GB.dot v c = 0) :
    GB.dot u (GB.matVec b v) = 0 := by
  have hb' : ∀ i, GB.dot v (GB.row b i) = 0 := fun i => hv _ (hb i)
  simp only [GB.dot, GB.matVec, GB.row] at hb' ⊢
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have h : (∑ j, b (i, j) * v j) = ∑ j, v j * b (i, j) :=
    Finset.sum_congr rfl (fun j _ => by ring)
  rw [h, hb' i, mul_zero]

/-- Additivity of the pairing `x ↦ GB.dot u (GB.matVec x w)` in the matrix variable. -/
lemma gb_dot_matVec_add {D : ℕ} (u : Fin D → ZMod 2) (a b : Fin D × Fin D → ZMod 2)
    (w : Fin D → ZMod 2) :
    GB.dot u (GB.matVec (a + b) w) = GB.dot u (GB.matVec a w) + GB.dot u (GB.matVec b w) := by
  simp only [GB.dot, GB.matVec, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]

/-- (file `Submission/Work/LT/gb_dot_matVec_eq_zero.lean`, inside `namespace Work.LT` / `namespace GB`, importing `Submission.Work.LT.gb_rank_defs`) Pairing computation behind Kalachev--Panteleev Lemma 8.  Let `x = a + b` where every column of `a` lies in the code `CA` and every row of `b` lies in the code `CB` (i.e. `x ∈ CA ⊞ CB`).  If `u ⊥ CA` and `v ⊥ CB` (orthogonality with respect to the dot product: `u ∈ (GB.dotForm D).orthogonal CA`, `v ∈ (GB.dotForm D).orthogonal CB`), then `u` is orthogonal to `x * v`. -/
lemma gb_dot_matVec_eq_zero {D : ℕ} {CA CB : Submodule (ZMod 2) (Fin D → ZMod 2)}
    {x a b : Fin D × Fin D → ZMod 2} (hx : x = a + b)
    (ha : GB.IsColwise CA a) (hb : GB.IsRowwise CB b)
    {u v : Fin D → ZMod 2} (hu : u ∈ (GB.dotForm D).orthogonal CA)
    (hv : v ∈ (GB.dotForm D).orthogonal CB) :
    GB.dot u (GB.matVec x v) = 0 := by
  subst hx
  rw [gb_dot_matVec_add u a b v,
    gb_dot_matVec_colwise_eq_zero ha (gb_dot_eq_zero_of_mem_orthogonal hu) v,
    gb_dot_matVec_rowwise_eq_zero hb (gb_dot_eq_zero_of_mem_orthogonal hv), add_zero]

end Work.LT
