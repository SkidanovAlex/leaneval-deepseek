import Mathlib
import Submission.Work.Whitney.LocalModel
import Submission.Work.Whitney.TransverseAux
import Submission.Work.Whitney.model_immersion

/-!
# The derivative of Whitney's local model at `e₀`

We compute `fderiv ℝ (model n) (e0 n)`: it is the linear map
`v ↦ (v, sheetE0 n v)`, i.e. the linear inclusion `inclModel` on the first block and the
"sheet" map `sheetE0 n` on the second block.  This is used to identify the `coprod` of the two
derivatives of the model at its double point with the endomorphism `C n` and hence to prove that
the self-intersection is transverse.

The files `Work.Whitney.model_immersion` (coordinate-wise derivatives of the model) and
`Work.Whitney.TransverseAux` (the definition of `sheetE0`) are imported.  The identity
`uu n (e0 n) = 2` is reproved locally as `uu_e0'` because the module containing the global
`uu_e0` would clash with `model_immersion` on the name `uu_pos`.
-/

namespace Work.Whitney

open scoped BigOperators

/-- `uu n (e0 n) = 2`. -/
lemma uu_e0' (n : ℕ) [NeZero n] : uu n (e0 n) = 2 := by
  unfold uu e0
  rw [Finset.prod_eq_single (0 : Fin n)]
  · norm_num
  · intro b _ hb; rw [Pi.single_eq_of_ne hb]; ring
  · intro h; exact absurd (Finset.mem_univ 0) h

/-- Coordinate description of the sheet map `sheetE0 n`. -/
lemma sheetE0_apply (n : ℕ) [NeZero n] (v : Fin n → ℝ) (i : Fin n) :
    sheetE0 n v i = if i = 0 then -(1/2) * v i else (1/2) * v i := by
  simp only [sheetE0, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply]
  split_ifs <;> ring

/-- `fderiv ℝ (uu n) (e0 n) v = 2 * v 0`. -/
lemma fderiv_uu_e0_apply (n : ℕ) [NeZero n] (v : Fin n → ℝ) :
    fderiv ℝ (uu n) (e0 n) v = 2 * v 0 := by
  have hsingle : ∀ j : Fin n, j ≠ 0 → (e0 n) j = 0 := by
    intro j hj; unfold e0; rw [Pi.single_eq_of_ne hj]
  have hsingle0 : (e0 n) 0 = 1 := by unfold e0; rw [Pi.single_eq_same]
  have hprod : (∏ j ∈ Finset.univ.erase (0 : Fin n), (1 + (e0 n) j ^ 2)) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    rw [Finset.mem_erase] at hj
    rw [hsingle j hj.1]; ring
  rw [fderiv_uu_apply, Finset.sum_eq_single (0 : Fin n)]
  · rw [hprod, hsingle0]; ring
  · intro b _ hb
    rw [hsingle b hb]; ring
  · intro h; exact absurd (Finset.mem_univ 0) h

/-- **The derivative of Whitney's local model at `e₀`** is `v ↦ (v, sheetE0 n v)`. -/
theorem model_fderiv_e0 (n : ℕ) [NeZero n] :
    ∀ v : Fin n → ℝ,
      fderiv ℝ (Work.Whitney.model n) (Work.Whitney.e0 n) v =
        (v, Work.Whitney.sheetE0 n v) := by
  intro v
  have hfst : (fderiv ℝ (model n) (e0 n) v).1 = v := by
    funext i
    rw [← fderiv_model_fst_apply_eq n (e0 n) v i]
    by_cases hi : i = 0
    · subst hi
      rw [fderiv_model_fst_zero_apply n (e0 n) v, fderiv_uu_e0_apply, uu_e0']
      simp only [e0, Pi.single_eq_same]
      ring
    · rw [fderiv_model_fst_apply_ne n hi (e0 n) v]
  have hsnd : (fderiv ℝ (model n) (e0 n) v).2 = sheetE0 n v := by
    funext i
    rw [← fderiv_model_snd_apply_eq n (e0 n) v i]
    by_cases hi : i = 0
    · subst hi
      rw [fderiv_model_snd_zero_apply n (e0 n) v, fderiv_uu_e0_apply, uu_e0', sheetE0_apply]
      simp only [↓reduceIte]
      ring
    · rw [fderiv_model_snd_apply_ne n hi (e0 n) v, fderiv_uu_e0_apply, uu_e0', sheetE0_apply]
      simp only [e0, Pi.single_eq_of_ne hi, Pi.single_eq_same, hi, ↓reduceIte]
      ring
  exact Prod.ext hfst hsnd

end Work.Whitney
