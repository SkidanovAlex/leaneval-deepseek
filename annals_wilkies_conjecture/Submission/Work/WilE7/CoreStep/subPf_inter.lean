import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.fiberProduct_semiPf
import Submission.Work.WilE7.pad_set
import Submission.Work.WilE7.prod_semiPf
import Submission.Work.WilE7.SemiPfInter
import Submission.Work.WilE7.PadDefs
import Submission.Work.WilE8.Extend
import Submission.Work.WilE8.Extend.semipf_set_extend
import Submission.Work.WilE7.CoreStep.glue_append

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.CoreStep

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-!
# `SubPf` is closed under finite intersections

`WilkiesDesign.E.SubPf n Y` means that `Y ⊆ ℝⁿ` is the projection of a restricted semi-Pfaffian
(EA) set, `Y = projFirst n m '' X.set` for some `X : SemiPf (n+m)`.  The intersection `Y ∩ Z`
is *not* obtained by intersecting representatives inside `ℝⁿ`: the two witnesses live in
`ℝ^{n+m₁}` and `ℝ^{n+m₂}` and their fibres have to be kept apart.  The correct object is the
fibre product

  `W = {z : ℝ^{n+(m₁+m₂)} | (x, y₁) ∈ X₁.set ∧ (x, y₂) ∈ X₂.set}`,

where `z` is split as `x` (first `n` coordinates), `y₁` (next `m₁`), `y₂` (last `m₂`); then
`projFirst n (m₁+m₂) '' W = Y ∩ Z`.  And `W` is the intersection of two semi-Pfaffian sets in
`ℝ^{n+(m₁+m₂)}`:

* `SemiPf.extend (Fin.castLE ·) X₁`, which reads the first `n+m₁` coordinates as a point of `X₁`;
* `SemiPf.extend (midInj n m₁ m₂) X₂`, which reads the coordinates `0,…,n-1` together with the
  last `m₂` coordinates as a point of `X₂` (`midInj` is the injection skipping the middle `m₁`
  block).

The two are intersected with `Work.WilE7.interSet`, whose point set is `interSet_set`.  The only
non-trivial combinatorial input is the gluing of a point of `X₁.set` and a point of `X₂.set`
with a common first `n` coordinates into a single point of `ℝ^{n+(m₁+m₂)}`, which is
`Work.WilE7.CoreStep.glue_append`.
-/

/-! ## Splitting a point along `projFirst`/`projSnd` -/

/-- A point of `ℝ^{n+m}` is the concatenation of its first `n` and last `m` coordinates. -/
theorem append_projFirst_projSnd {n m : ℕ} (p : Fin (n + m) → ℝ) :
    Fin.append (projFirst n m p) (projSnd n m p) = p :=
  Fin.append_castAdd_natAdd

/-! ## Truncating the ambient coordinates -/

/-- The first `n` coordinates of a point restricted along `Fin.castLE` only see the first `n`
coordinates of the point. -/
theorem projFirst_castLE_comp {n m M : ℕ} (h : n + m ≤ n + M) (z : Fin (n + M) → ℝ) :
    projFirst n m (fun i : Fin (n + m) => z (Fin.castLE h i)) = projFirst n M z := by
  funext i
  show z (Fin.castLE h (Fin.castAdd m i)) = z (Fin.castAdd M i)
  refine congrArg z (Fin.ext ?_)
  rw [Fin.val_castLE, Fin.val_castAdd, Fin.val_castAdd]

/-- The first `n` coordinates of a point restricted along `midInj` only see the first `n`
coordinates of the point. -/
theorem projFirst_midInj_comp {n m1 m2 : ℕ} (z : Fin (n + (m1 + m2)) → ℝ) :
    projFirst n m2 (fun i : Fin (n + m2) => z (midInj n m1 m2 i)) =
      projFirst n (m1 + m2) z := by
  funext i
  show z (midInj n m1 m2 (Fin.castAdd m2 i)) = z (Fin.castAdd (m1 + m2) i)
  rw [midInj_castAdd]

/-! ## The fibre product of two sub-Pfaffian sets -/

/-- **The point set of the fibre product.**  Extending `X₁ : SemiPf (n+m₁)` along `Fin.castLE` and
`X₂ : SemiPf (n+m₂)` along `midInj n m₁ m₂` and intersecting gives a semi-Pfaffian set in
`ℝ^{n+(m₁+m₂)}` whose first `n` coordinates run exactly over
`projFirst n m₁ '' X₁.set ∩ projFirst n m₂ '' X₂.set`. -/
theorem projFirst_inter_extend {n m1 m2 : ℕ} (X1 : SemiPf (n + m1)) (X2 : SemiPf (n + m2)) :
    projFirst n (m1 + m2) ''
        (interSet
          (Work.WilE8.SemiPf.extend (Fin.castLE (Nat.add_le_add_left (Nat.le_add_right m1 m2) n))
            X1)
          (Work.WilE8.SemiPf.extend (midInj n m1 m2) X2)).set =
      projFirst n m1 '' X1.set ∩ projFirst n m2 '' X2.set := by
  have h1 : n + m1 ≤ n + (m1 + m2) := Nat.add_le_add_left (Nat.le_add_right m1 m2) n
  rw [interSet_set,
    Work.WilE8.Extend.semipf_set_extend (Fin.castLE_injective h1) X1,
    Work.WilE8.Extend.semipf_set_extend (midInj_injective n m1 m2) X2]
  refine Set.Subset.antisymm ?_ ?_
  · -- a point of the fibre product projects into the two projections
    rintro x ⟨z, ⟨hzA, hzB⟩, rfl⟩
    obtain ⟨-, hu1⟩ := hzA
    obtain ⟨-, hu2⟩ := hzB
    exact ⟨⟨_, hu1, projFirst_castLE_comp h1 z⟩, ⟨_, hu2, projFirst_midInj_comp z⟩⟩
  · -- conversely, two witnesses with common first `n` coordinates glue to a point
    rintro x ⟨⟨p, hpX1, hpx⟩, ⟨q, hqX2, hqx⟩⟩
    have hp : Fin.append x (projSnd n m1 p) = p := by
      rw [← hpx]
      exact append_projFirst_projSnd p
    have hq : Fin.append x (projSnd n m2 q) = q := by
      rw [← hqx]
      exact append_projFirst_projSnd q
    obtain ⟨z, hz1, hz2, hzproj, hzcube⟩ :=
      glue_append x (projSnd n m1 p) (projSnd n m2 q)
    -- `z` lies in the cube, because both witnesses do
    have hzc : z ∈ cubeC (n + (m1 + m2)) := by
      refine hzcube ?_ ?_
      · rw [hp]
        exact Work.WilE8.SemiPf.set_subset_cube X1 hpX1
      · rw [hq]
        exact Work.WilE8.SemiPf.set_subset_cube X2 hqX2
    -- `z` reads back the two witnesses along the two injections
    have hzu1 : (fun i : Fin (n + m1) => z (Fin.castLE h1 i)) ∈ X1.set := by
      have hfun : (fun i : Fin (n + m1) => z (Fin.castLE h1 i)) =
          Fin.append x (projSnd n m1 p) := funext hz1
      rw [hfun, hp]
      exact hpX1
    have hzu2 : (fun i : Fin (n + m2) => z (midInj n m1 m2 i)) ∈ X2.set := by
      have hfun : (fun i : Fin (n + m2) => z (midInj n m1 m2 i)) =
          Fin.append x (projSnd n m2 q) := funext hz2
      rw [hfun, hq]
      exact hqX2
    exact ⟨z, ⟨⟨hzc, hzu1⟩, ⟨hzc, hzu2⟩⟩, hzproj⟩

/-! ## The closure statement -/

theorem subPf_inter {n : ℕ} {Y Z : Set (Fin n → ℝ)}
    (hY : WilkiesDesign.E.SubPf n Y) (hZ : WilkiesDesign.E.SubPf n Z) :
    WilkiesDesign.E.SubPf n (Y ∩ Z) := by
  obtain ⟨m1, X1, hY⟩ := hY
  obtain ⟨m2, X2, hZ⟩ := hZ
  refine ⟨m1 + m2,
    interSet
      (Work.WilE8.SemiPf.extend (Fin.castLE (Nat.add_le_add_left (Nat.le_add_right m1 m2) n)) X1)
      (Work.WilE8.SemiPf.extend (midInj n m1 m2) X2), ?_⟩
  rw [projFirst_inter_extend, ← hY, ← hZ]

end Work.WilE7.CoreStep
