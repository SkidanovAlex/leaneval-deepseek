import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.numaux.rk_orthLatDefs
import Submission.Work.HP.numaux.rk_orthLat
import Submission.Work.HP.numaux.castL_mem_spread_iff

/-!
# `Work.EEupper.memSatLatDotB`

An integer vector `w` orthogonal to a full-rank family `a_1, …, a_m` of vectors of the
*primitive* orthogonal lattice `orthLat Λ` (with `m = rk (orthLat Λ)`) already lies in `Λ`.

The point is that `a_1, …, a_m` span a sublattice `A ≤ orthLat Λ` of the same rank
`m = rk (orthLat Λ)`; hence, *after spreading out to `ℚ`*, `A` spans the same rational
subspace as `orthLat Λ`, and every `b ∈ orthLat Λ` is a rational combination of the `a_j`.
Since `w` is orthogonal to each `a_j`, the image of `w` is orthogonal to the rational
orthogonal complement of `spread Λ`, hence lies in `spread Λ`, i.e. `w ∈ satLat Λ = Λ`.

The `ℚ`-spreading machinery (`spread`, `castL`, `stdB`, `spread_finrank`, `stdB_castL`,
`spread_orthLat_eq_orthogonal`) lives in
`Submission.Work.HP.numaux.rk_orthLatDefs` / `Submission.Work.HP.numaux.rk_orthLat`, and
`castL_mem_spread_iff` (integer points of `spread L` are `satLat L`) in
`Submission.Work.HP.numaux.castL_mem_spread_iff`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.EEupper

open Work.HP

/-- The standard bilinear form on `ℚ^ι` is symmetric and nondegenerate, so taking the rational
orthogonal complement twice is the identity. -/
lemma stdB_orthogonal_orthogonal_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Submodule ℚ (ι → ℚ)) :
    (Work.HP.numaux.stdB (ι := ι)).orthogonal
      ((Work.HP.numaux.stdB (ι := ι)).orthogonal V) = V :=
  LinearMap.BilinForm.orthogonal_orthogonal (Work.HP.numaux.stdB_nondegenerate (ι := ι))
    (fun x y h => by rw [Work.HP.numaux.stdB_comm y x]; exact h) V

theorem memSatLatDotB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ (ι → ℤ)) (hΛ : Work.HP.IsPrimLat Λ)
    {m : ℕ} (hm : Work.HP.rk (Work.HP.orthLat Λ) = m) {a : Fin m → (ι → ℤ)}
    (ha : ∀ j, a j ∈ Work.HP.orthLat Λ) (hind : LinearIndependent ℤ a) (w : ι → ℤ)
    (hw : ∀ j, Work.HP.dotI w (a j) = 0) : w ∈ Λ := by
  classical
  -- The lattice spanned by the family `a`.
  set A : Submodule ℤ (ι → ℤ) := Submodule.span ℤ (Set.range a) with hA
  -- It sits inside `orthLat Λ` and has the full rank `m` of `orthLat Λ`.
  have hAle : A ≤ Work.HP.orthLat Λ := by
    rw [hA]
    exact Submodule.span_le.mpr (fun x hx => by obtain ⟨j, rfl⟩ := hx; exact ha j)
  have hfinA : Module.finrank ℤ A = m := by
    rw [hA, finrank_span_eq_card hind]
    simp
  -- Spreading out to `ℚ`, the two lattices span the same rational subspace.
  have hspread_le : Work.HP.numaux.spread A ≤ Work.HP.numaux.spread (Work.HP.orthLat Λ) := by
    unfold Work.HP.numaux.spread
    exact Submodule.span_mono (Submodule.map_mono hAle)
  have hdim : Module.finrank ℚ (Work.HP.numaux.spread A) =
      Module.finrank ℚ (Work.HP.numaux.spread (Work.HP.orthLat Λ)) := by
    have hm' : Module.finrank ℤ ↥(Work.HP.orthLat Λ) = m := hm
    rw [Work.HP.numaux.spread_finrank A, Work.HP.numaux.spread_finrank (Work.HP.orthLat Λ),
      hfinA, hm']
  have hspread_eq : Work.HP.numaux.spread A = Work.HP.numaux.spread (Work.HP.orthLat Λ) :=
    Submodule.eq_of_le_of_finrank_eq hspread_le hdim
  -- `w` is orthogonal to `A`.
  have hdotA : ∀ x ∈ A, Work.HP.dotI w x = 0 := by
    intro x hx
    rw [hA] at hx
    refine Submodule.span_induction (p := fun x _ => Work.HP.dotI w x = 0) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨j, rfl⟩
      exact hw j
    · simp only [Work.HP.dotI, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    · intro y z _ _ ihy ihz
      rw [Work.HP.dotI_add_right, ihy, ihz, add_zero]
    · intro c y _ ihy
      rw [Work.HP.dotI_smul_right, ihy, mul_zero]
  -- Hence the image of `w` is orthogonal to the rational spread of `A`.
  have hmapker : ((A.map (Work.HP.numaux.castL (ι := ι)) : Submodule ℤ (ι → ℚ)) : Set (ι → ℚ)) ⊆
      ((LinearMap.ker ((Work.HP.numaux.stdB (ι := ι)) (Work.HP.numaux.castL w)) :
        Submodule ℚ (ι → ℚ)) : Set (ι → ℚ)) := by
    rintro n ⟨x, hx, rfl⟩
    change (Work.HP.numaux.stdB (ι := ι)) (Work.HP.numaux.castL w) (Work.HP.numaux.castL x) = 0
    rw [Work.HP.numaux.stdB_castL, hdotA x hx, Int.cast_zero]
  have hker : Work.HP.numaux.spread A ≤
      LinearMap.ker ((Work.HP.numaux.stdB (ι := ι)) (Work.HP.numaux.castL w)) := by
    unfold Work.HP.numaux.spread
    exact Submodule.span_le.mpr hmapker
  -- So the image of `w` is orthogonal to `spread (orthLat Λ) = orthogonal (spread Λ)`.
  have hcast : Work.HP.numaux.castL w ∈ Work.HP.numaux.spread Λ := by
    have h1 : Work.HP.numaux.castL w ∈
        (Work.HP.numaux.stdB (ι := ι)).orthogonal (Work.HP.numaux.spread A) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      rw [Work.HP.numaux.stdB_comm]
      exact hker hn
    rw [hspread_eq, Work.HP.numaux.spread_orthLat_eq_orthogonal Λ,
      stdB_orthogonal_orthogonal_aux (Work.HP.numaux.spread Λ)] at h1
    exact h1
  -- Integer vectors of `spread Λ` form the saturation, which is `Λ` by primitivity.
  have hsat : w ∈ Work.HP.satLat Λ := (Work.HP.numaux.castL_mem_spread_iff Λ w).mp hcast
  rw [Work.HP.satLat_eq_of_isPrimLat hΛ] at hsat
  exact hsat

end Work.EEupper
