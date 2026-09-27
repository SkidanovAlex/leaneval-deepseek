import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.ClutchGeom
import Submission.Work.KT.whitehead_diag
import Submission.Work.KT.elem_lift

namespace Work.KT

open Matrix

/-- If every member of a list `L` of matrices over the boundary sphere is an elementary matrix
(`1 + single i j a`, `i ≠ j`), then `L` is the boundary restriction of the product of a list of
units over the ball: replace each elementary matrix by a Tietze lift `E` (`elem_lift`) and multiply. -/
private lemma list_lift (V : Type) [NormedAddCommGroup V] {n : ℕ}
    (L : List (Matrix (Fin n) (Fin n) C(Sph V, ℂ)))
    (hL : ∀ M ∈ L, ∃ (i j : Fin n) (a : C(Sph V, ℂ)), i ≠ j ∧ M = 1 + Matrix.single i j a) :
    ∃ U : (Matrix (Fin n) (Fin n) C(Ball V, ℂ))ˣ,
      RingHom.mapMatrix (restRho V) (↑U : Matrix (Fin n) (Fin n) C(Ball V, ℂ)) = L.prod := by
  induction L with
  | nil => exact ⟨1, by simp⟩
  | cons M L ih =>
      obtain ⟨i, j, a, hij, rfl⟩ := hL M (by simp)
      obtain ⟨E, hE⟩ := elem_lift V i j hij a
      obtain ⟨U, hU⟩ := ih (by intro K hK; exact hL K (by simp [hK]))
      refine ⟨E * U, ?_⟩
      rw [Units.val_mul, map_mul, hE, hU, List.prod_cons]

/-- Every unit `γ` of `m × m` matrices over the boundary sphere `C(Sph V, ℂ)` extends to a unit of
`2m × 2m` matrices over the ball whose boundary restriction is `diag(γ, γ⁻¹)`: `diag(γ,γ⁻¹)` is a
product of elementary matrices (Whitehead) and each of those lifts over the ball (Tietze). -/
theorem lift_diag_unit (V : Type) [NormedAddCommGroup V] {m : ℕ}
    (G : (Matrix (Fin m) (Fin m) C(Sph V, ℂ))ˣ) :
    ∃ H : (Matrix (Fin (m + m)) (Fin (m + m)) C(Ball V, ℂ))ˣ,
      RingHom.mapMatrix (restRho V) (↑H : Matrix (Fin (m + m)) (Fin (m + m)) C(Ball V, ℂ)) =
        Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (↑G : Matrix (Fin m) (Fin m) C(Sph V, ℂ)) 0 0
            (↑(G⁻¹) : Matrix (Fin m) (Fin m) C(Sph V, ℂ))) := by
  -- Whitehead: the block diagonal `diag(γ, γ⁻¹)` is a product of elementary matrices over the sphere.
  obtain ⟨L, hLmem, hLprod⟩ := whitehead_diag
    (↑G : Matrix (Fin m) (Fin m) C(Sph V, ℂ))
    (↑(G⁻¹) : Matrix (Fin m) (Fin m) C(Sph V, ℂ))
    (Units.inv_mul G) (Units.mul_inv G)
  -- Tietze: lift each elementary factor to a unit over the ball and multiply.
  obtain ⟨U, hU⟩ := list_lift V L hLmem
  exact ⟨U, by rw [hU, hLprod]⟩

end Work.KT
