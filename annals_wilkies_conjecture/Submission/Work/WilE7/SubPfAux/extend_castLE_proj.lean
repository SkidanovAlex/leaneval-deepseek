import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE8.Basic
import Submission.Work.WilE8.Extend
import Submission.Work.WilE8.Extend.semipf_set_extend

namespace Work.WilE7.SubPfAux

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-!
# Extending along `Fin.castLE` and projecting

`Work.WilE8.SemiPf.extend e X` views the semi-Pfaffian set `X ⊆ ℝ^k` as a set in `ℝ^{k'}`: by
`semipf_set_extend`, its points are the points of the closed cube `[-1,1]^{k'}` whose first `k`
coordinates (pulled back along the injection `e`) lie in `X`.

For the coordinate injection `e = Fin.castLE (m ≤ M) : Fin (n+m) → Fin (n+M)` the projection to
the first `n` coordinates therefore does not see the extension: the first `n` coordinates of a
point of the extended set are exactly the image of the first `n` coordinates of a point of `X`.
That is the statement below; the two inclusions are witnessed by zero-padding a point of `X`
(`padZ`) and by truncating a point of the extension (`takeZ`).
-/

/-! ## `takeZ` and `padZ` against `Fin.castLE` -/

/-- `takeZ` is the pullback along `Fin.castLE`. -/
private theorem takeZ_eq_castLE {k K : ℕ} (hm : k ≤ K) (y : Fin K → ℝ) :
    Work.WilE7.takeZ hm y = fun i => y (Fin.castLE hm i) := rfl

/-- Truncating a zero-padding gives back the original point. -/
private theorem takeZ_padZ {k K : ℕ} (hm : k ≤ K) (x : Fin k → ℝ) :
    Work.WilE7.takeZ hm (Work.WilE7.padZ K x) = x := by
  funext i
  rw [takeZ_eq_castLE]
  show (if h : ((Fin.castLE hm i : Fin K) : ℕ) < k then
      x ⟨((Fin.castLE hm i : Fin K) : ℕ), h⟩ else 0) = x i
  rw [dite_eq_left (by rw [Fin.val_castLE]; exact i.isLt)]
  exact congrArg x (Fin.ext (by rw [Fin.val_castLE]))

/-- Zero-padding stays inside the closed cube. -/
private theorem padZ_mem_cubeC {k K : ℕ} {x : Fin k → ℝ} (hx : x ∈ cubeC k) :
    Work.WilE7.padZ K x ∈ cubeC K := by
  intro i
  show |(if h : (i : ℕ) < k then x ⟨(i : ℕ), h⟩ else 0)| ≤ 1
  split_ifs with h
  · exact hx ⟨(i : ℕ), h⟩
  · simp

/-- Zero-padding does not change the first `n` coordinates, `m ≤ M`. -/
private theorem projFirst_padZ {n m M : ℕ} (x : Fin (n + m) → ℝ) :
    projFirst n M (Work.WilE7.padZ (n + M) x) = projFirst n m x := by
  funext i
  show Work.WilE7.padZ (n + M) x (Fin.castAdd M i) = x (Fin.castAdd m i)
  show (if h : ((Fin.castAdd M i : Fin (n + M)) : ℕ) < n + m then
      x ⟨((Fin.castAdd M i : Fin (n + M)) : ℕ), h⟩ else 0) = x (Fin.castAdd m i)
  rw [dite_eq_left (by rw [Fin.val_castAdd]; exact lt_of_lt_of_le i.isLt (Nat.le_add_right n m))]
  exact congrArg x (Fin.ext (by rw [Fin.val_castAdd, Fin.val_castAdd]))

/-- The projection to the first `n` coordinates commutes with the truncation along `Fin.castLE`. -/
private theorem projFirst_takeZ {n m M : ℕ} (hm : m ≤ M) (y : Fin (n + M) → ℝ) :
    projFirst n M y = projFirst n m (Work.WilE7.takeZ (Nat.add_le_add_left hm n) y) := by
  funext i
  show y (Fin.castAdd M i) = y (Fin.castLE (Nat.add_le_add_left hm n) (Fin.castAdd m i))
  exact congrArg y (Fin.ext (by rw [Fin.val_castAdd, Fin.val_castLE, Fin.val_castAdd]))

/-! ## The main statement -/

theorem extend_castLE_proj {n m M : ℕ} (hm : m ≤ M)
    (X : WilkiesDesign.E.SemiPf (n + m)) :
    WilkiesDesign.E.projFirst n M ''
        (Work.WilE8.SemiPf.extend (Fin.castLE (Nat.add_le_add_left hm n)) X).set =
      WilkiesDesign.E.projFirst n m '' X.set := by
  -- The set of the extended semi-Pfaffian set, in terms of truncation.
  have hset := Work.WilE8.Extend.semipf_set_extend (k := n + m) (k' := n + M)
    (e := Fin.castLE (Nat.add_le_add_left hm n))
    (Fin.castLE_injective (Nat.add_le_add_left hm n)) X
  rw [hset]
  refine Set.Subset.antisymm ?_ ?_
  · -- A point of the extended set projects to the projection of its truncation.
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨_, hxX⟩ := hx
    exact ⟨Work.WilE7.takeZ (Nat.add_le_add_left hm n) x, hxX, (projFirst_takeZ hm x).symm⟩
  · -- Conversely, a point of `X` zero-extends to a point of the extended set with the same
    -- first `n` coordinates.
    rintro z ⟨y, hyX, rfl⟩
    refine ⟨Work.WilE7.padZ (n + M) y, ⟨?_, ?_⟩, projFirst_padZ y⟩
    · exact padZ_mem_cubeC ((Work.WilE8.SemiPf.set_subset_cube X) hyX)
    · show Work.WilE7.takeZ (Nat.add_le_add_left hm n) (Work.WilE7.padZ (n + M) y) ∈ X.set
      rw [takeZ_padZ]
      exact hyX

end Work.WilE7.SubPfAux
