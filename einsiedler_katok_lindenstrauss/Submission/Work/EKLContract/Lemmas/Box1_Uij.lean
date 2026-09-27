import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Diag

namespace Work.EKLContract.Lemmas

open Work.EKLContract

/-- Membership in the root group `U_ij`: it is exactly the range of the one-parameter
subgroup `s ↦ u_ij(s)`, because that range already is a subgroup
(`u_ij(0) = 1`, `u_ij(s+t) = u_ij(s) u_ij(t)`, `u_ij(s)⁻¹ = u_ij(-s)`). -/
private theorem mem_Uij_iff {i j : Fin 3} (h : i ≠ j) (g : SL3) :
    g ∈ Uij h ↔ ∃ s : ℝ, g = uij h s := by
  constructor
  · intro hg
    let S : Subgroup SL3 :=
      { carrier := Set.range fun s : ℝ => uij h s
        one_mem' := ⟨0, by simp [uij, Matrix.SpecialLinearGroup.transvection_coeff_zero]⟩
        mul_mem' := by
          rintro a b ⟨s, rfl⟩ ⟨t, rfl⟩
          exact ⟨s + t, by simp [uij, Matrix.SpecialLinearGroup.transvection_add]⟩
        inv_mem' := by
          rintro a ⟨s, rfl⟩
          exact ⟨-s, by simp [uij, Matrix.SpecialLinearGroup.transvection_inv]⟩ }
    have hle : Uij h ≤ S := (Subgroup.closure_le S).2 (fun x hx => hx)
    obtain ⟨s, hs⟩ := hle hg
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, rfl⟩
    exact Subgroup.subset_closure (Set.mem_range_self s)

/-- The entries of the shear `u_ij(s) = 1 + s E_ij`: `1` on the diagonal, `s` at position
`(i,j)`, and `0` elsewhere. -/
theorem uij_apply {i j : Fin 3} (h : i ≠ j) (s : ℝ) (k l : Fin 3) :
    (uij h s : Matrix (Fin 3) (Fin 3) ℝ) k l =
      if k = l then 1 else if k = i ∧ l = j then s else 0 := by
  rw [uij, Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs with h1 h2 h3
  · exfalso; simp_all
  · ring
  · ring
  · exfalso; simp_all
  · exfalso; simp_all
  · ring

/-- The `(i,j)` entry of `u_ij(s)` is `s`. -/
theorem uij_apply_self {i j : Fin 3} (h : i ≠ j) (s : ℝ) :
    (uij h s : Matrix (Fin 3) (Fin 3) ℝ) i j = s := by
  rw [uij_apply h s i j, if_neg h, if_pos ⟨rfl, rfl⟩]

/-- The `(i,j)` entry of the identity is `0` when `i ≠ j`. -/
theorem one_apply_ne {i j : Fin 3} (h : i ≠ j) :
    (1 : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := by
  rw [Matrix.one_apply, if_neg h]

theorem Box1_Uij {i j : Fin 3} (h : i ≠ j) : Work.EKLContract.Box1 (Work.EKLContract.Uij h) = Work.EKLContract.ballU h 1 := by
  ext g
  simp only [Box1, ballU, Set.mem_ofPred_eq, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨hgU, hbox⟩
    obtain ⟨s, rfl⟩ := (mem_Uij_iff h g).1 hgU
    refine ⟨s, ?_, rfl⟩
    have h1 : (uij h s : Matrix (Fin 3) (Fin 3) ℝ) i j = s := uij_apply_self h s
    have h2 : (1 : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := one_apply_ne h
    have h3 := hbox i j
    rw [h1, h2, sub_zero] at h3
    exact abs_le.mp h3
  · rintro ⟨s, hs, rfl⟩
    refine ⟨Subgroup.subset_closure (Set.mem_range_self s), ?_⟩
    intro k l
    rw [uij_apply h s k l, Matrix.one_apply]
    by_cases hkl : k = l
    · subst hkl; simp
    · rw [if_neg hkl, if_neg hkl]
      by_cases hij : k = i ∧ l = j
      · obtain ⟨rfl, rfl⟩ := hij
        simpa using abs_le.mpr ⟨hs.1, hs.2⟩
      · simp [hij]

end Work.EKLContract.Lemmas
