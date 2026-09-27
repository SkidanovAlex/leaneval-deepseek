import Mathlib
import Submission.Work.KT.Psi.psi3blk
import Submission.Work.KT.PsiC.cls_cyclic
import Submission.Work.KT.PsiC.CycProj

/-!
# `Work.KT.Psi.psi3pre` — the orbit/spectral facts for `ψ³`-additivity

`uPerm` commutes with the constant-word projectors and with every orbit sum `orb3 (eBlk w)`; the
four projectors `e000`, `e111`, `orb3 (e001)`, `orb3 (e011)` are orthogonal idempotents summing to
`1`; and `Cp` (the spectral projector of `uPerm`) commutes with everything commuting with `uPerm`.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

variable {A : Type} [Ring A]

theorem rotW_w000 : rotW w000 = w000 := rfl
theorem rotW_w111 : rotW w111 = w111 := rfl

theorem ne_rotW_w001 : w001 ≠ rotW w001 := by decide
theorem ne_rotW_w011 : w011 ≠ rotW w011 := by decide
theorem ne_rotW2_w001 : w001 ≠ rotW (rotW w001) := by decide
theorem ne_rotW2_w011 : w011 ≠ rotW (rotW w011) := by decide

theorem uPerm_mul_eBlk {m n : ℕ} (hA : ∀ x y : A, x * y = y * x)
    (w : (Fin 2 × Fin 2) × Fin 2) :
    uPerm A (Fin m ⊕ Fin n) * eBlk (A := A) (m := m) (n := n) w =
      eBlk (rotW w) * uPerm A (Fin m ⊕ Fin n) := by
  have h := uPerm_eBlk_conj (A := A) (m := m) (n := n) hA w
  calc uPerm A (Fin m ⊕ Fin n) * eBlk w
      = uPerm A (Fin m ⊕ Fin n) * eBlk w *
          (uPerm A (Fin m ⊕ Fin n) * uPerm A (Fin m ⊕ Fin n) * uPerm A (Fin m ⊕ Fin n)) := by
        rw [uPerm_cube, Matrix.mul_one]
    _ = (uPerm A (Fin m ⊕ Fin n) * eBlk w *
          (uPerm A (Fin m ⊕ Fin n) * uPerm A (Fin m ⊕ Fin n))) * uPerm A (Fin m ⊕ Fin n) := by
        noncomm_ring
    _ = eBlk (rotW w) * uPerm A (Fin m ⊕ Fin n) := by rw [h]

theorem uPerm_sq_mul_eBlk {m n : ℕ} (hA : ∀ x y : A, x * y = y * x)
    (w : (Fin 2 × Fin 2) × Fin 2) :
    (uPerm A (Fin m ⊕ Fin n) * uPerm A (Fin m ⊕ Fin n)) * eBlk (A := A) (m := m) (n := n) w =
      eBlk (rotW (rotW w)) * (uPerm A (Fin m ⊕ Fin n) * uPerm A (Fin m ⊕ Fin n)) := by
  have h := uPerm_sq_eBlk_conj (A := A) (m := m) (n := n) hA w
  calc (uPerm A (Fin m ⊕ Fin n) * uPerm A (Fin m ⊕ Fin n)) * eBlk w
      = (uPerm A (Fin m ⊕ Fin n) * uPerm A (Fin m ⊕ Fin n)) * eBlk w *
          (uPerm A (Fin m ⊕ Fin n) * uPerm A (Fin m ⊕ Fin n) * uPerm A (Fin m ⊕ Fin n)) := by
        rw [uPerm_cube, Matrix.mul_one]
    _ = ((uPerm A (Fin m ⊕ Fin n) * uPerm A (Fin m ⊕ Fin n)) * eBlk w *
          uPerm A (Fin m ⊕ Fin n)) * (uPerm A (Fin m ⊕ Fin n) * uPerm A (Fin m ⊕ Fin n)) := by
        noncomm_ring
    _ = eBlk (rotW (rotW w)) * (uPerm A (Fin m ⊕ Fin n) * uPerm A (Fin m ⊕ Fin n)) := by rw [h]

theorem eBlk_mul_uPerm_mul_eBlk {m n : ℕ} (hA : ∀ x y : A, x * y = y * x)
    {w : (Fin 2 × Fin 2) × Fin 2} (h : w ≠ rotW w) :
    eBlk (A := A) (m := m) (n := n) w * uPerm A (Fin m ⊕ Fin n) * eBlk w = 0 := by
  rw [mul_assoc, uPerm_mul_eBlk (A := A) hA w, ← mul_assoc, eBlk_orth (A := A) hA h,
    Matrix.zero_mul]

theorem eBlk_mul_uPerm_sq_mul_eBlk {m n : ℕ} (hA : ∀ x y : A, x * y = y * x)
    {w : (Fin 2 × Fin 2) × Fin 2} (h : w ≠ rotW (rotW w)) :
    eBlk (A := A) (m := m) (n := n) w *
      (uPerm A (Fin m ⊕ Fin n) * uPerm A (Fin m ⊕ Fin n)) * eBlk w = 0 := by
  rw [mul_assoc, uPerm_sq_mul_eBlk (A := A) hA w, ← mul_assoc, eBlk_orth (A := A) hA h,
    Matrix.zero_mul]

theorem uPerm_comm_eBlk_w000 {m n : ℕ} (hA : ∀ x y : A, x * y = y * x) :
    uPerm A (Fin m ⊕ Fin n) * eBlk (A := A) (m := m) (n := n) w000 =
      eBlk w000 * uPerm A (Fin m ⊕ Fin n) := by
  rw [uPerm_mul_eBlk (A := A) hA w000, rotW_w000]

theorem uPerm_comm_eBlk_w111 {m n : ℕ} (hA : ∀ x y : A, x * y = y * x) :
    uPerm A (Fin m ⊕ Fin n) * eBlk (A := A) (m := m) (n := n) w111 =
      eBlk w111 * uPerm A (Fin m ⊕ Fin n) := by
  rw [uPerm_mul_eBlk (A := A) hA w111, rotW_w111]

theorem uPerm_comm_orb3 {m n : ℕ} (e : Matrix (SQ (Fin m ⊕ Fin n)) (SQ (Fin m ⊕ Fin n)) A) :
    uPerm A (Fin m ⊕ Fin n) * orb3 (Fin m ⊕ Fin n) e =
      orb3 (Fin m ⊕ Fin n) e * uPerm A (Fin m ⊕ Fin n) := by
  have hu : uPerm A (Fin m ⊕ Fin n) * uPerm A (Fin m ⊕ Fin n) * uPerm A (Fin m ⊕ Fin n) = 1 :=
    uPerm_cube (Fin m ⊕ Fin n)
  rw [orb3]
  set u := uPerm A (Fin m ⊕ Fin n) with hu'
  have hu3 : u * u * u = 1 := by rw [hu']; exact hu
  have hu4 : u * (u * u) = 1 := by rw [← mul_assoc]; exact hu3
  noncomm_ring [hu3, hu4]
  rw [show u * (u * (u * (e * u))) = e * u from by
    rw [← mul_assoc, ← mul_assoc, hu3, one_mul]]

theorem orb3_eBlk_idem {m n : ℕ} (hA : ∀ x y : A, x * y = y * x)
    {w : (Fin 2 × Fin 2) × Fin 2} (h : w ≠ rotW w) (h2 : w ≠ rotW (rotW w)) :
    orb3 (Fin m ⊕ Fin n) (eBlk (A := A) (m := m) (n := n) w) *
      orb3 (Fin m ⊕ Fin n) (eBlk w) = orb3 (Fin m ⊕ Fin n) (eBlk w) := by
  have hh := PsiC.orbit_idem (R := Matrix (SQ (Fin m ⊕ Fin n)) (SQ (Fin m ⊕ Fin n)) A)
    (e := eBlk (A := A) (m := m) (n := n) w) (u := uPerm A (Fin m ⊕ Fin n))
    (eBlk_idem (A := A) hA w) (uPerm_cube (Fin m ⊕ Fin n))
    (eBlk_mul_uPerm_mul_eBlk (A := A) hA h) (eBlk_mul_uPerm_sq_mul_eBlk (A := A) hA h2)
  show orb3 (Fin m ⊕ Fin n) (eBlk (A := A) (m := m) (n := n) w) *
      orb3 (Fin m ⊕ Fin n) (eBlk w) = orb3 (Fin m ⊕ Fin n) (eBlk w)
  simp only [orb3]
  exact hh

theorem eBlk_mul_orb3_eq_zero {m n : ℕ} (hA : ∀ x y : A, x * y = y * x)
    {w w' : (Fin 2 × Fin 2) × Fin 2} (h1 : w ≠ w') (h2 : w ≠ rotW w')
    (h3 : w ≠ rotW (rotW w')) :
    eBlk (A := A) (m := m) (n := n) w * orb3 (Fin m ⊕ Fin n) (eBlk w') = 0 := by
  rw [orb3_eBlk (A := A) hA w']
  simp only [mul_add, eBlk_orth (A := A) hA h1, eBlk_orth (A := A) hA h2,
    eBlk_orth (A := A) hA h3, Matrix.mul_zero, add_zero]

theorem orb3_mul_eBlk_eq_zero {m n : ℕ} (hA : ∀ x y : A, x * y = y * x)
    {w w' : (Fin 2 × Fin 2) × Fin 2} (h1 : w' ≠ w) (h2 : rotW w' ≠ w)
    (h3 : rotW (rotW w') ≠ w) :
    orb3 (Fin m ⊕ Fin n) (eBlk (A := A) (m := m) (n := n) w') * eBlk w = 0 := by
  rw [orb3_eBlk (A := A) hA w']
  simp only [add_mul, eBlk_orth (A := A) hA h1, eBlk_orth (A := A) hA h2,
    eBlk_orth (A := A) hA h3, Matrix.zero_mul, add_zero]

theorem partition {m n : ℕ} (hA : ∀ x y : A, x * y = y * x) :
    eBlk (A := A) (m := m) (n := n) w000 + eBlk w111 +
      orb3 (Fin m ⊕ Fin n) (eBlk w001) + orb3 (Fin m ⊕ Fin n) (eBlk w011) = 1 := by
  rw [orb3_eBlk (A := A) hA w001, orb3_eBlk (A := A) hA w011, ← eBlk_sum (A := A) hA]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, w000, w111, w001, w011, rotW]
  abel

end

end Work.KT.Psi
