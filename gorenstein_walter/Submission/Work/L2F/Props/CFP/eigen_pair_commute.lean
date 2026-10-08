import Mathlib

namespace Work.L2F.Props.CFP

theorem eigen_pair_commute (F : Type*) [Field F] (X Y : Matrix (Fin 2) (Fin 2) F)
    (v u : Fin 2 → F) (c c2 d d2 : F)
    (hsp : Submodule.span F ({v, u} : Set (Fin 2 → F)) = ⊤)
    (hXv : Matrix.mulVec X v = c • v) (hXu : Matrix.mulVec X u = c2 • u)
    (hYv : Matrix.mulVec Y v = d • v) (hYu : Matrix.mulVec Y u = d2 • u) :
    X * Y = Y * X := by
  have hXv' : (Matrix.toLin' X) v = c • v := by
    rw [Matrix.toLin'_apply]; exact hXv
  have hXu' : (Matrix.toLin' X) u = c2 • u := by
    rw [Matrix.toLin'_apply]; exact hXu
  have hYv' : (Matrix.toLin' Y) v = d • v := by
    rw [Matrix.toLin'_apply]; exact hYv
  have hYu' : (Matrix.toLin' Y) u = d2 • u := by
    rw [Matrix.toLin'_apply]; exact hYu
  have hcomm : (Matrix.toLin' X).comp (Matrix.toLin' Y)
      = (Matrix.toLin' Y).comp (Matrix.toLin' X) := by
    apply LinearMap.ext_on hsp
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw
    · rw [hw]
      show Matrix.toLin' X (Matrix.toLin' Y v) = Matrix.toLin' Y (Matrix.toLin' X v)
      rw [hYv', hXv', map_smul, map_smul, hXv', hYv', smul_smul, smul_smul, mul_comm]
    · rw [hw]
      show Matrix.toLin' X (Matrix.toLin' Y u) = Matrix.toLin' Y (Matrix.toLin' X u)
      rw [hYu', hXu', map_smul, map_smul, hXu', hYu', smul_smul, smul_smul, mul_comm]
  have h2 : Matrix.toLin' (X * Y) = Matrix.toLin' (Y * X) := by
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
    exact hcomm
  exact Matrix.toLin'.injective h2

end Work.L2F.Props.CFP
