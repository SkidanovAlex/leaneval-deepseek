import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.numaux.rk_orthLatDefs
import Submission.Work.HP.numaux.castL_mem_spread_iff
import Submission.Work.HP.numaux.rk_satLat
import Submission.Work.HP.numaux.doubleOrth_eq_satLat

/-!
# A vector orthogonal to a rational basis of the orthogonal lattice lies in the lattice

Let `Λ ⊆ ℤ^ι` be a primitive (saturated) integral lattice with `rk (orthLat Λ) = m`, let
`a : Fin m → ℤ^ι` be a `ℤ`-linearly independent family of vectors of the orthogonal lattice
`orthLat Λ`, and let `w : ℤ^ι` be orthogonal to every `a j`.  Then `w ∈ Λ`.

The point is that `a` is a `ℚ`-basis of the rational spread of `orthLat Λ` (independence over
`ℤ` upgrades to independence over `ℚ` for the torsion-free module `ℤ^ι`, and the cardinality
`m` equals the rank).  Hence `w`, being orthogonal to a spanning set of `orthLat Λ`, lies in
the double orthogonal complement `orthLat (orthLat Λ)`, which is the saturation of `Λ`
(`Work.HP.numaux.doubleOrth_eq_satLat`); primitivity then gives `w ∈ Λ`.

The auxiliary lemmas local to this file are placed in the nested namespace `MSL` so that the
module can be imported alongside the sibling files that state the same facts publicly.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace Work.HP.numaux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace MSL

/-- The standard pairing on `ℤ^ι` is the restriction of the standard bilinear form on `ℚ^ι`
along the coordinatewise inclusion. -/
lemma stdB_castL (v w : ι → ℤ) : stdB (ι := ι) (castL v) (castL w) = (dotI v w : ℚ) := by
  simp only [stdB_apply, dotI, castL_apply, Int.cast_sum, Int.cast_mul]

end MSL

theorem mem_satLat_of_dot_eq_zero {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Submodule ℤ (ι → ℤ))
    (hΛ : IsPrimLat Λ) {m : ℕ} (hm : rk (orthLat Λ) = m) {a : Fin m → (ι → ℤ)}
    (ha : ∀ j, a j ∈ orthLat Λ) (hind : LinearIndependent ℤ a) (w : ι → ℤ)
    (hw : ∀ j, dotI w (a j) = 0) : w ∈ Λ := by
  -- `a` is linearly independent over `ℚ` after the coordinatewise inclusion into `ℚ^ι`.
  have hindQ : LinearIndependent ℚ (fun j : Fin m => castL (a j)) := by
    have h := (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℚ) (v := a)).mpr hind
    change LinearIndependent ℚ (fun j : Fin m => (⇑(algebraMap ℤ ℚ)) ∘ a j)
    exact h
  -- The `a j` rationally span the whole spread of `orthLat Λ`.
  have hspan : Submodule.span ℚ (Set.range (fun j : Fin m => castL (a j)))
      = spread (orthLat Λ) := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro x ⟨j, rfl⟩
      exact castL_mem_spread (ha j)
    · have h1 : Module.finrank ℚ
          ↥(Submodule.span ℚ (Set.range (fun j : Fin m => castL (a j)))) = m := by
        rw [finrank_span_eq_card hindQ, Fintype.card_fin]
      have h2 : Module.finrank ℚ ↥(spread (orthLat Λ)) = m := by
        rw [← finrank_eq_finrank_spread (orthLat Λ)]
        exact hm
      rw [h1, h2]
  -- Every generator is annihilated by the functional `stdB · (castL w)`.
  have hgen : ∀ j : Fin m, stdB (ι := ι) (castL (a j)) (castL w) = 0 := by
    intro j
    rw [MSL.stdB_castL, dotI_comm, hw j, Int.cast_zero]
  -- Hence `w` lies in the double orthogonal complement of `Λ`.
  have hw_orth : w ∈ orthLat (orthLat Λ) := by
    rw [mem_orthLat]
    intro u hu
    have hu_span : castL u ∈ Submodule.span ℚ (Set.range (fun j : Fin m => castL (a j))) := by
      rw [hspan]
      exact castL_mem_spread hu
    have hzero : stdB (ι := ι) (castL u) (castL w) = 0 :=
      Submodule.span_induction (p := fun x _ => stdB (ι := ι) x (castL w) = 0)
        (fun x hx => by obtain ⟨j, rfl⟩ := hx; exact hgen j)
        (by simp)
        (fun x y _ _ hx hy => by rw [map_add, LinearMap.add_apply, hx, hy, add_zero])
        (fun c x _ hx => by rw [map_smul, LinearMap.smul_apply, hx, smul_zero])
        hu_span
    have hz : (dotI u w : ℚ) = 0 := by rw [← MSL.stdB_castL u w]; exact hzero
    have hzu : dotI u w = 0 := by exact_mod_cast hz
    rw [dotI_comm]
    exact hzu
  -- The double orthogonal complement is the saturation, which is `Λ` by primitivity.
  have hsat : w ∈ satLat Λ := by
    rwa [doubleOrth_eq_satLat Λ] at hw_orth
  rwa [satLat_eq_of_isPrimLat hΛ] at hsat

end Work.HP.numaux
