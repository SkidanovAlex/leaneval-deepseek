import Mathlib
import Submission.Work.LT.gb_ext_defs

/-!
# Row-wise preservation under `GB.matExt`

`GB.matExt A B u (GB.opVec T) b` has, in row `i`,

`∑ i' ∈ A, u i' i • T.toLin (GB.row b i')`,

a linear combination of the images under `T` of the rows of `b`.  Hence if every row of `b` lies
in a code `C` and `T` is a `B`-extension operator preserving `C`, then every row of the resulting
matrix lies in `C`: `GB.IsRowwise C (GB.matExt A B u (GB.opVec T) b)`.
-/

namespace Work.LT

namespace GB

variable {D : ℕ} {C : Submodule (ZMod 2) (Fin D → ZMod 2)} {B : Finset (Fin D)}

/-- The `l`-th coordinate of `T v` is the pairing of `v` with the `l`-th coordinates of the
vectors `opVec T j` for `j ∈ B`. -/
lemma ExtOp.toLin_apply (T : GB.ExtOp C B) (v : Fin D → ZMod 2) (l : Fin D) :
    T.toLin v l = ∑ j ∈ B, v j * GB.opVec T j l := by
  conv_lhs => rw [T.vanish v, GB.projA_eq_sum]
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul, GB.opVec_apply]
  simp [Pi.smul_apply, smul_eq_mul]

end GB

theorem gb_matExt_rowwise {D : ℕ} {C : Submodule (ZMod 2) (Fin D → ZMod 2)} (A B : Finset (Fin D))
    (T : GB.ExtOp C B) (u : Fin D → (Fin D → ZMod 2)) (b : Fin D × Fin D → ZMod 2)
    (hb : GB.IsRowwise C b) : GB.IsRowwise C (GB.matExt A B u (GB.opVec T) b) := by
  intro i
  have hz : (∑ i' ∈ A, u i' i • GB.row b i') ∈ C :=
    C.sum_mem (fun i' _ => C.smul_mem (u i' i) (hb i'))
  have hval : ∀ j, (∑ i' ∈ A, u i' i • GB.row b i') j = ∑ i' ∈ A, u i' i * b (i', j) := by
    intro j
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i' hi'
    simp [GB.row, Pi.smul_apply, smul_eq_mul]
  have hkey : GB.row (GB.matExt A B u (GB.opVec T) b) i
      = T.toLin (∑ i' ∈ A, u i' i • GB.row b i') := by
    funext l
    have hlhs : GB.row (GB.matExt A B u (GB.opVec T) b) i l
        = ∑ i' ∈ A, ∑ j ∈ B, b (i', j) * u i' i * GB.opVec T j l := by
      simp only [GB.row, GB.matExt_apply]
    rw [hlhs, GB.ExtOp.toLin_apply]
    simp only [hval, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i' hi'
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hkey]
  exact T.preserves _ hz

end Work.LT
