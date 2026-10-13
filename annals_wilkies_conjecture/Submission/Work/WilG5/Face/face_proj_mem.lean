import Mathlib
import Submission.Work.WilG5.Face.Defs

namespace Work.WilG5.Face

/-- The face of an `Ω`-set is an `Ω`-set, with the format/degree shifts `ffs`/`dfs`.

`faceProj i c X = coordImage (delSplit i) (X ∩ {x | x i = c})` is obtained by intersecting
`X` with a coordinate hyperplane (degree `1`, format `n`) and then pushing forward along the
coordinate-deleting map `delSplit i : Fin (n-1) → Fin n`, which by `coordImage_mem` costs
format `64 * (n + (n-1)) + 64` and degree `32 * (n + (n-1)) + 32` — exactly `ffs F n` and
`dfs n`. -/
theorem face_proj_mem {S : WilkiesDesign.SOMin} {n F D : ℕ} {X : Set (Fin n → ℝ)}
    (h : X ∈ S.Ω F D n) (i : Fin n) (c : ℝ) :
    Work.WilG5.Face.faceProj i c X ∈ S.Ω (Work.WilG5.Face.ffs F n)
      (D + Work.WilG5.Face.dfs n) (n - 1) := by
  show coordImage (delSplit i) (X ∩ {x : Fin n → ℝ | x i = c}) ∈
    S.Ω (ffs F n) (D + dfs n) (n - 1)
  -- both pieces at the common format `max F n`
  have hX : X ∈ S.Ω (max F n) D n := mem_mono h _ _ (le_max_left _ _) (le_refl _)
  have hH : {x : Fin n → ℝ | x i = c} ∈ S.Ω (max F n) 1 n :=
    mem_mono (coordEq_mem (S := S) i c) _ _ (le_max_right _ _) (le_refl _)
  -- the intersection
  have hJ : X ∩ {x : Fin n → ℝ | x i = c} ∈ S.Ω (max F n + 1) (D + 1) n := by
    have hI := S.inter (fun k : Fin 2 => if k = 0 then D else 1)
      (fun k : Fin 2 => if k = 0 then X else {x : Fin n → ℝ | x i = c})
      (by
        intro k
        fin_cases k
        · simpa using hX
        · simpa using hH)
    have hsum : (∑ k : Fin 2, (if k = 0 then D else 1)) = D + 1 := by
      simp [Fin.sum_univ_two]
    rw [hsum] at hI
    have hset : (⋂ k : Fin 2, (if k = 0 then X else {x : Fin n → ℝ | x i = c})) =
        X ∩ {x : Fin n → ℝ | x i = c} := by
      ext z
      simp [Fin.forall_fin_two]
    rwa [hset] at hI
  -- push forward along the coordinate-deleting map
  have h2 := coordImage_mem (S := S) (F := max F n + 1) (D := D + 1) (ι := delSplit i) hJ
  refine mem_mono h2 (ffs F n) (D + dfs n) ?_ ?_ <;> simp only [ffs, dfs] <;> omega

end Work.WilG5.Face
