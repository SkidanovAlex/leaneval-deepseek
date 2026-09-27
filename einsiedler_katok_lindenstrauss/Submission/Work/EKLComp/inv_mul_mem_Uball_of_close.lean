import Mathlib
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLComp.abs_mul_entry_le
import Submission.Work.EKLComp.inv_entries_le_of_mem_Ucl
import Submission.Work.EKLProd.inv_entries_bound

/-!
# `Work.EKLComp.inv_mul_mem_Uball_of_close`

A `Ucl U r`-element `v₂` and a `U`-element `v₁` whose entries differ from those of `v₂` by at
most `η` in absolute value satisfy `v₂⁻¹ v₁ ∈ Uball U e` whenever `6 (1+r)^2 η < e`.

Writing `(v₂⁻¹ v₁) - 1 = v₂⁻¹ (v₁ - v₂)` (the entries of the inverse of a special linear group
element are its adjugate, i.e. its `2 × 2` minors) and using

* `Work.EKLComp.inv_entries_le_of_mem_Ucl` — the entries of `v₂⁻¹` are bounded by `2 (1+r)^2`,
* `Work.EKLComp.abs_mul_entry_le` — an entrywise product bound `|(A B) i j| ≤ 3 C η`,

every entry of `v₂⁻¹ v₁ - 1` is bounded by `3 · 2 (1+r)^2 · η = 6 (1+r)^2 η < e`.  Membership in
`U` is the subgroup closure `v₂⁻¹ v₁ ∈ U`.
-/

namespace Work.EKLComp

open Work.EKLContract

theorem inv_mul_mem_Uball_of_close {U : Subgroup Work.EKLContract.SL3} {r η e : ℝ} (hr : 0 < r)
    (hη0 : 0 ≤ η) (hη : 6 * (1 + r) ^ 2 * η < e)
    {v₁ v₂ : Work.EKLContract.SL3} (hv₁ : v₁ ∈ U) (hv₂ : v₂ ∈ Work.EKLComp.Ucl U r)
    (hclose : ∀ i j, |(v₁ : Matrix (Fin 3) (Fin 3) ℝ) i j - (v₂ : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ η) :
    v₂⁻¹ * v₁ ∈ Work.EKLComp.Uball U e := by
  -- entries of `v₂⁻¹` are bounded by `2 (1+r)^2`
  have hinvE : ∀ i j, |((v₂⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j|
      ≤ 2 * (1 + r) ^ 2 := fun i j => inv_entries_le_of_mem_Ucl hr hv₂ i j
  -- `(v₂⁻¹ v₁) - 1 = v₂⁻¹ (v₁ - v₂)` on the level of matrices
  have hmat : ((v₂⁻¹ * v₁ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)
      - (1 : Matrix (Fin 3) (Fin 3) ℝ)
      = ((v₂⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)
        * (((v₁ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)
            - ((v₂ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) := by
    have h21 : ((v₂⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)
        * ((v₂ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    rw [Matrix.SpecialLinearGroup.coe_mul, mul_sub, h21]
  refine ⟨mul_mem (inv_mem hv₂.1) hv₁, fun i j => ?_⟩
  have hprod : ((v₂⁻¹ * v₁ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
      = (((v₂⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)
        * (((v₁ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)
            - ((v₂ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ))) i j := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) hmat
    simpa [Matrix.sub_apply, Matrix.mul_apply] using h
  rw [hprod]
  have hb := Work.EKLComp.abs_mul_entry_le
    (A := ((v₂⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ))
    (B := (((v₁ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)
      - ((v₂ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)))
    (C := 2 * (1 + r) ^ 2) (η := η) (by positivity) hη0 hinvE
    (fun i j => by simpa [Matrix.sub_apply] using hclose i j) i j
  linarith [hη, hb]

end Work.EKLComp
