/-
# Cramér's rule form of the Dirichlet Green's function

The Dirichlet Green's function `G α lam θ E x₁ x₂ x y` of the almost Mathieu operator is
the `(x - x₁, y - x₁)` entry of the inverse of `dirMat` on `[x₁, x₂]`, hence by Cramér's
rule the ratio of a cofactor (a minor of a tridiagonal matrix, evaluated in
`det_minor_A`/`det_minor_B`) and the determinant (`det_triD`).
-/
import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.triCont

noncomputable section

namespace Work.TMC16Core.Basic

open Work.TMC16Core

/-- Shifting the phase by `c α` shifts the site index by `c`. -/
theorem amoPot_shift (α lam ψ : ℝ) (c : ℕ) (n : ℤ) :
    amoPot α lam (ψ + (c : ℝ) * α) n = amoPot α lam ψ (n + c) := by
  simp only [amoPot]
  rw [show (((n + ((c : ℕ) : ℤ)) : ℤ) : ℝ) = (n : ℝ) + (c : ℝ) by push_cast; ring]
  ring

theorem det_minor_row0 (d : ℕ → ℂ) (n : ℕ) (j : Fin (n + 1)) :
    ((triD d (n + 1)).submatrix (j.succAbove) Fin.succ).det
      = cont (seqShift d (j.val + 1)) (n - j.val) := by
  revert d j
  induction n with
  | zero =>
      intro d j
      have hjn : j = 0 := Fin.ext (by omega)
      subst hjn
      simp
  | succ n ih =>
      intro d j
      by_cases h0 : j = 0
      · subst h0
        rw [Fin.succAbove_zero, triD_tail, det_triD]
        rw [show (((0 : Fin (n + 2)) : ℕ)) = 0 from Fin.val_zero (n + 2),
          Nat.zero_add, Nat.sub_zero]
      · have hj0 : 0 < (j : ℕ) := by
          rcases Nat.eq_zero_or_pos (j : ℕ) with h | h
          · exact absurd (Fin.ext (by simpa using h)) h0
          · exact h
        obtain ⟨j', hj'v⟩ : ∃ j' : Fin (n + 1), (j' : ℕ) + 1 = (j : ℕ) :=
          ⟨⟨(j : ℕ) - 1, by omega⟩, by simp only [Fin.val_mk]; omega⟩
        have hrow0 : ((triD d (n + 2)).submatrix (j.succAbove) Fin.succ) 0 0 = 1 := by
          have h1 : j.succAbove 0 = 0 := by
            rw [Fin.succAbove_of_castSucc_lt j (0 : Fin (n + 1))
              (by simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_zero]; omega)]
            exact Fin.ext (by simp)
          rw [Matrix.submatrix_apply, h1, Fin.succ_zero_eq_one]
          exact triD_succ d (n + 2) (by simp)
        have hrow : ∀ k : Fin (n + 1), k ≠ 0 →
            ((triD d (n + 2)).submatrix (j.succAbove) Fin.succ) 0 k = 0 := by
          intro k hk
          have hk0 : (k : ℕ) ≠ 0 := by
            intro h
            exact hk (Fin.ext (by simpa using h))
          have h1 : j.succAbove 0 = 0 := by
            rw [Fin.succAbove_of_castSucc_lt j (0 : Fin (n + 1))
              (by simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_zero]; omega)]
            exact Fin.ext (by simp)
          have hne : (0 : Fin (n + 2)) ≠ Fin.succ k := by
            intro hh
            have hh' := congrArg (fun t : Fin (n + 2) => (t : ℕ)) hh
            simp only [Fin.val_succ, Fin.val_zero] at hh'
            omega
          have hdisj : ¬ (((0 : Fin (n + 2)) : ℕ) + 1 = ((Fin.succ k : Fin (n + 2)) : ℕ)
              ∨ ((Fin.succ k : Fin (n + 2)) : ℕ) + 1 = ((0 : Fin (n + 2)) : ℕ)) := by
            simp only [Fin.val_succ, Fin.val_zero]
            omega
          rw [Matrix.submatrix_apply, h1]
          exact triD_zero d (n + 2) hne hdisj
        have hcomp : (j.succAbove) ∘ (Fin.succ : Fin n → Fin (n + 1))
            = (Fin.succ : Fin (n + 1) → Fin (n + 2)) ∘ (j'.succAbove) := by
          funext t
          apply Fin.ext
          have ht : ((t : ℕ) + 1) = (t.succ : Fin (n + 1)) := by simp
          simp only [Function.comp_apply, Fin.succAbove]
          split_ifs <;>
            simp only [Fin.val_castSucc, Fin.val_succ, Fin.lt_def, Fin.val_zero] at * <;>
            omega
        rw [det_of_first_row _ hrow0 hrow, Matrix.submatrix_submatrix, hcomp,
          ← Matrix.submatrix_submatrix, triD_tail, ih (seqShift d 1) j', seqShift_seqShift]
        have h1 : 1 + ((j' : ℕ) + 1) = ((j : ℕ) + 1) := by omega
        have h2 : n - (j' : ℕ) = n + 1 - (j : ℕ) := by omega
        rw [h1, h2]

theorem det_minor_last (d : ℕ → ℂ) (n : ℕ) (j : Fin (n + 1)) :
    ((triD d (n + 1)).submatrix Fin.castSucc (j.succAbove)).det = cont d j.val := by
  revert d j
  induction n with
  | zero =>
      intro d j
      have hjn : j = 0 := Fin.ext (by omega)
      subst hjn
      simp
  | succ n ih =>
      intro d j
      by_cases hlast : j = Fin.last (n + 1)
      · subst hlast
        rw [Fin.succAbove_last, triD_head, det_triD]
        congr 1
      · have hjle : (j : ℕ) ≤ n := by
          by_contra h
          exact hlast (Fin.ext (by simp only [Fin.val_last]; omega))
        obtain ⟨j', hj'v⟩ : ∃ j' : Fin (n + 1), (j' : ℕ) = (j : ℕ) :=
          ⟨⟨(j : ℕ), by omega⟩, rfl⟩
        have hcol0 : ((triD d (n + 2)).submatrix Fin.castSucc (j.succAbove))
            (Fin.last n) (Fin.last n) = 1 := by
          have h1 : j.succAbove (Fin.last n) = Fin.last (n + 1) := by
            rw [Fin.succAbove_of_le_castSucc j (Fin.last n)
              (by simp only [Fin.le_def, Fin.val_castSucc, Fin.val_last]; omega)]
            exact Fin.ext (by simp only [Fin.val_succ, Fin.val_last])
          rw [Matrix.submatrix_apply, h1]
          exact triD_succ d (n + 2) (by simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last])
        have hcol : ∀ i : Fin (n + 1), i ≠ Fin.last n →
            ((triD d (n + 2)).submatrix Fin.castSucc (j.succAbove)) i (Fin.last n) = 0 := by
          intro i hi
          have hi' : (i : ℕ) < n := by
            rcases Nat.lt_or_ge (i : ℕ) n with h | h
            · exact h
            · exact absurd (Fin.ext (by simp only [Fin.val_last]; omega)) hi
          have h1 : j.succAbove (Fin.last n) = Fin.last (n + 1) := by
            rw [Fin.succAbove_of_le_castSucc j (Fin.last n)
              (by simp only [Fin.le_def, Fin.val_castSucc, Fin.val_last]; omega)]
            exact Fin.ext (by simp only [Fin.val_succ, Fin.val_last])
          have hne : Fin.castSucc i ≠ Fin.last (n + 1) := by
            intro hh
            have hh' := congrArg (fun t : Fin (n + 2) => (t : ℕ)) hh
            simp only [Fin.val_castSucc, Fin.val_last] at hh'
            omega
          have hdisj : ¬ (((Fin.castSucc i : Fin (n + 2)) : ℕ) + 1
                = ((Fin.last (n + 1) : Fin (n + 2)) : ℕ)
              ∨ ((Fin.last (n + 1) : Fin (n + 2)) : ℕ) + 1
                = ((Fin.castSucc i : Fin (n + 2)) : ℕ)) := by
            simp only [Fin.val_castSucc, Fin.val_last]
            omega
          rw [Matrix.submatrix_apply, h1]
          exact triD_zero d (n + 2) hne hdisj
        have hcomp : (j.succAbove) ∘ (Fin.castSucc : Fin n → Fin (n + 1))
            = (Fin.castSucc : Fin (n + 1) → Fin (n + 2)) ∘ (j'.succAbove) := by
          funext t
          apply Fin.ext
          simp only [Function.comp_apply, Fin.succAbove]
          split_ifs <;>
            simp only [Fin.val_castSucc, Fin.val_succ, Fin.lt_def, Fin.val_zero] at * <;>
            omega
        rw [det_of_last_col _ hcol0 hcol, Matrix.submatrix_submatrix, hcomp,
          ← Matrix.submatrix_submatrix, triD_head, ih d j', hj'v]

theorem cramer (α lam : ℝ) (θ : ℝ) (E : ℂ) (x₁ x₂ y : ℤ) (h1 : x₁ ≤ y) (h2 : y ≤ x₂) :
    ‖Work.TMC16Core.G α lam θ E x₁ x₂ x₁ y‖ =
        ‖Work.TMC16Core.pd α lam (θ + ((y : ℝ) + 1) * α) E ((x₂ - y).toNat + 1) /
         Work.TMC16Core.pd α lam (θ + (x₁ : ℝ) * α) E ((x₂ - x₁ + 1).toNat + 1)‖ ∧
      ‖Work.TMC16Core.G α lam θ E x₁ x₂ y x₂‖ =
        ‖Work.TMC16Core.pd α lam (θ + (x₁ : ℝ) * α) E ((y - x₁).toNat + 1) /
         Work.TMC16Core.pd α lam (θ + (x₁ : ℝ) * α) E ((x₂ - x₁ + 1).toNat + 1)‖ := by
  simp only [G, Int.sub_self, Int.toNat_zero]
  set Q : ℕ := (x₂ - x₁).toNat with hQdef
  set J : ℕ := (y - x₁).toNat with hJdef
  set P : ℕ := (x₂ - y).toNat with hPdef
  set φ : ℝ := θ + (x₁ : ℝ) * α with hφdef
  let d : ℕ → ℂ := fun i => ((amoPot α lam φ (i : ℤ) : ℝ) : ℂ) - E
  have hQz : (Q : ℤ) = x₂ - x₁ := by rw [hQdef]; exact Int.toNat_of_nonneg (by omega)
  have hJz : (J : ℤ) = y - x₁ := by rw [hJdef]; exact Int.toNat_of_nonneg (by omega)
  have hPz : (P : ℤ) = x₂ - y := by rw [hPdef]; exact Int.toNat_of_nonneg (by omega)
  have hQJ : Q - J = P := by
    have h : (Q : ℤ) = J + P := by omega
    have h' : Q = J + P := by exact_mod_cast h
    omega
  have hsize : (x₂ - x₁ + 1).toNat = Q + 1 := by
    have h1' : ((x₂ - x₁ + 1).toNat : ℤ) = x₂ - x₁ + 1 := Int.toNat_of_nonneg (by omega)
    have h2' : ((Q + 1 : ℕ) : ℤ) = x₂ - x₁ + 1 := by
      push_cast
      rw [hQz]
    omega
  have hJQ : J < Q + 1 := by omega
  rw [hsize]
  -- the determinant of `dirMat` and the two minors
  have hDetEq : (triD d (Q + 1)).det = (-1 : ℂ) ^ (Q + 1) * pd α lam φ E (Q + 1 + 1) := by
    rw [det_triD d (Q + 1)]
    have h1 : d = fun (i : ℕ) => - (E - ((amoPot α lam φ (i : ℤ) : ℝ) : ℂ)) := by
      funext i
      show ((amoPot α lam φ (i : ℤ) : ℝ) : ℂ) - E
        = - (E - ((amoPot α lam φ (i : ℤ) : ℝ) : ℂ))
      ring
    rw [h1, cont_neg]
    congr 1
    exact (pd_eq_cont α lam φ E (Q + 1)).symm
  have hNormDet : ‖(triD d (Q + 1)).det‖ = ‖pd α lam φ E (Q + 1 + 1)‖ := by
    rw [hDetEq, norm_mul, norm_pow]
    simp
  have hMinorA : ((triD d (Q + 1)).submatrix ((⟨J, hJQ⟩ : Fin (Q + 1)).succAbove) Fin.succ).det
      = cont (seqShift d (J + 1)) (Q - J) := det_minor_row0 d Q ⟨J, hJQ⟩
  have hshift : φ + ((J + 1 : ℕ) : ℝ) * α = θ + ((y : ℝ) + 1) * α := by
    have hJzR : (J : ℝ) = (y : ℝ) - (x₁ : ℝ) := by exact_mod_cast hJz
    rw [hφdef]
    push_cast
    rw [hJzR]
    ring
  have hseq : seqShift d (J + 1)
      = fun (i : ℕ) => - (E - ((amoPot α lam (θ + ((y : ℝ) + 1) * α) (i : ℤ) : ℝ) : ℂ)) := by
    funext i
    show ((amoPot α lam φ ((i + (J + 1) : ℕ) : ℤ) : ℝ) : ℂ) - E
      = - (E - ((amoPot α lam (θ + ((y : ℝ) + 1) * α) (i : ℤ) : ℝ) : ℂ))
    have h1 : amoPot α lam φ (((i + (J + 1) : ℕ) : ℤ))
        = amoPot α lam (θ + ((y : ℝ) + 1) * α) (i : ℤ) := by
      rw [show (((i + (J + 1) : ℕ) : ℤ)) = (i : ℤ) + ((J + 1 : ℕ) : ℤ) by push_cast; ring]
      rw [← amoPot_shift α lam φ (J + 1) (i : ℤ), hshift]
    rw [h1]
    ring
  have hMinorNorm : ‖((triD d (Q + 1)).submatrix ((⟨J, hJQ⟩ : Fin (Q + 1)).succAbove) Fin.succ).det‖
      = ‖pd α lam (θ + ((y : ℝ) + 1) * α) E (P + 1)‖ := by
    rw [hMinorA, hQJ, hseq, cont_neg, ← pd_eq_cont α lam (θ + ((y : ℝ) + 1) * α) E P]
    rw [norm_mul, norm_pow]
    simp
  have hMinorB : ((triD d (Q + 1)).submatrix Fin.castSucc ((⟨J, hJQ⟩ : Fin (Q + 1)).succAbove)).det
      = cont d J := det_minor_last d Q ⟨J, hJQ⟩
  have hMinorBNorm : ‖((triD d (Q + 1)).submatrix Fin.castSucc ((⟨J, hJQ⟩ : Fin (Q + 1)).succAbove)).det‖
      = ‖pd α lam φ E (J + 1)‖ := by
    rw [hMinorB]
    have h1 : d = fun (i : ℕ) => - (E - ((amoPot α lam φ (i : ℤ) : ℝ) : ℂ)) := by
      funext i
      show ((amoPot α lam φ (i : ℤ) : ℝ) : ℂ) - E
        = - (E - ((amoPot α lam φ (i : ℤ) : ℝ) : ℂ))
      ring
    rw [h1, cont_neg, ← pd_eq_cont α lam φ E J]
    rw [norm_mul, norm_pow]
    simp
  -- the two Green's function entries
  have hconj1 : ‖greenEntry α lam φ E (Q + 1) 0 J‖
      = ‖pd α lam (θ + ((y : ℝ) + 1) * α) E (P + 1) / pd α lam φ E (Q + 1 + 1)‖ := by
    have hG1 : greenEntry α lam φ E (Q + 1) 0 J
        = (triD d (Q + 1))⁻¹ (0 : Fin (Q + 1)) ⟨J, hJQ⟩ := by
      rw [greenEntry]
      rw [dif_pos (show 0 < Q + 1 ∧ J < Q + 1 from ⟨by omega, hJQ⟩), dirMat_eq_triD]
      rw [show (⟨0, (show 0 < Q + 1 by omega)⟩ : Fin (Q + 1)) = 0 from Fin.ext (by simp),
        show (⟨J, (show J < Q + 1 by omega)⟩ : Fin (Q + 1)) = ⟨J, hJQ⟩ from Fin.ext rfl]
    have hInv1 : (triD d (Q + 1))⁻¹ (0 : Fin (Q + 1)) ⟨J, hJQ⟩
        = Ring.inverse (triD d (Q + 1)).det
          * (triD d (Q + 1)).adjugate (0 : Fin (Q + 1)) (⟨J, hJQ⟩ : Fin (Q + 1)) := by
      rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
    have hadj1 : (triD d (Q + 1)).adjugate (0 : Fin (Q + 1)) (⟨J, hJQ⟩ : Fin (Q + 1))
        = (-1 : ℂ) ^ J
          * ((triD d (Q + 1)).submatrix ((⟨J, hJQ⟩ : Fin (Q + 1)).succAbove) Fin.succ).det := by
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_zero]
      simp
    rw [hG1, hInv1, hadj1, norm_mul, Ring.inverse_eq_inv, norm_inv, norm_mul, norm_pow]
    simp only [norm_neg, norm_one, one_pow, one_mul]
    rw [hMinorNorm, hNormDet, mul_comm, norm_div, div_eq_mul_inv]
  have hconj2 : ‖greenEntry α lam φ E (Q + 1) J Q‖
      = ‖pd α lam φ E (J + 1) / pd α lam φ E (Q + 1 + 1)‖ := by
    have hG2 : greenEntry α lam φ E (Q + 1) J Q
        = (triD d (Q + 1))⁻¹ (⟨J, hJQ⟩ : Fin (Q + 1)) (Fin.last Q) := by
      rw [greenEntry]
      rw [dif_pos (show J < Q + 1 ∧ Q < Q + 1 from ⟨hJQ, by omega⟩), dirMat_eq_triD]
      rw [show (⟨J, (show J < Q + 1 by omega)⟩ : Fin (Q + 1)) = ⟨J, hJQ⟩ from Fin.ext rfl,
        show (⟨Q, (show Q < Q + 1 by omega)⟩ : Fin (Q + 1)) = Fin.last Q from Fin.ext rfl]
    have hInv2 : (triD d (Q + 1))⁻¹ (⟨J, hJQ⟩ : Fin (Q + 1)) (Fin.last Q)
        = Ring.inverse (triD d (Q + 1)).det
          * (triD d (Q + 1)).adjugate (⟨J, hJQ⟩ : Fin (Q + 1)) (Fin.last Q) := by
      rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
    have hadj2 : (triD d (Q + 1)).adjugate (⟨J, hJQ⟩ : Fin (Q + 1)) (Fin.last Q)
        = (-1 : ℂ) ^ (Q + J)
          * ((triD d (Q + 1)).submatrix Fin.castSucc ((⟨J, hJQ⟩ : Fin (Q + 1)).succAbove)).det := by
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
      simp
    rw [hG2, hInv2, hadj2, norm_mul, Ring.inverse_eq_inv, norm_inv, norm_mul, norm_pow]
    simp only [norm_neg, norm_one, one_pow, one_mul]
    rw [hMinorBNorm, hNormDet, mul_comm, norm_div, div_eq_mul_inv]
  exact ⟨hconj1, hconj2⟩

end Work.TMC16Core.Basic

end
