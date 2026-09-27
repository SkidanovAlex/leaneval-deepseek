import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.psi3sum_Setup
import Submission.Work.KT.Psi.psi3blk
import Submission.Work.KT.Psi.psi3pre
import Submission.Work.KT.Psi.clsM_idem_add
import Submission.Work.KT.Psi.clsM_orb3
import Submission.Work.KT.Psi.clsM_sumBlk_cubePartP
import Submission.Work.KT.Psi.clsM_sumBlkP_cubePart
import Submission.Work.KT.Psi.clsM_sumBlkQ_cubePart

namespace Work.KT.Psi

open Matrix

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]

/-! ## Elementary ring lemmas -/

/-- A product of two commuting idempotents is idempotent. -/
theorem idem_mul_of_comm {M : Type} [Ring M] {X Y : M} (hX : X * X = X) (hY : Y * Y = Y)
    (h : X * Y = Y * X) : (X * Y) * (X * Y) = X * Y := by
  calc (X * Y) * (X * Y) = X * (Y * X) * Y := by noncomm_ring
    _ = X * (X * Y) * Y := by rw [← h]
    _ = (X * X) * (Y * Y) := by noncomm_ring
    _ = X * Y := by rw [hX, hY]

/-- A sum of two orthogonal idempotents is idempotent. -/
theorem idem_add_of_orth {M : Type} [Ring M] {E F : M} (hE : E * E = E) (hF : F * F = F)
    (hEF : E * F = 0) (hFE : F * E = 0) : (E + F) * (E + F) = E + F := by
  rw [add_mul, mul_add, mul_add, hE, hEF, hFE, hF]
  abel

/-- A product of two orthogonal `Y`-multiples is zero. -/
theorem mul_orth_of_orth {M : Type} [Ring M] {Y q r : M} (hYq : Y * q = q * Y)
    (hYr : Y * r = r * Y) (hY : Y * Y = Y) (h : q * r = 0) : (Y * q) * (Y * r) = 0 := by
  calc (Y * q) * (Y * r) = Y * (q * Y) * r := by noncomm_ring
    _ = Y * (Y * q) * r := by rw [hYq]
    _ = (Y * Y) * (q * r) := by noncomm_ring
    _ = 0 := by rw [hY, h, mul_zero]

/-- General form of the `Cp`-commutation: a matrix commuting with `uPerm` commutes with `Cp`. -/
theorem comm_Cp_of_comm_uPerm (hA : ∀ x y : A, x * y = y * x) {S : Type} [Fintype S]
    [DecidableEq S] {X : Matrix (SQ S) (SQ S) A} (hX : X * uPerm A S = uPerm A S * X) (lam : ℂ) :
    X * Cp S lam = Cp S lam * X := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  have hX' : X * Equiv.Perm.permMatrix A (cyc3 S) = Equiv.Perm.permMatrix A (cyc3 S) * X := hX
  have hX2 : X * (Equiv.Perm.permMatrix A (cyc3 S) * Equiv.Perm.permMatrix A (cyc3 S))
      = (Equiv.Perm.permMatrix A (cyc3 S) * Equiv.Perm.permMatrix A (cyc3 S)) * X := by
    calc X * (Equiv.Perm.permMatrix A (cyc3 S) * Equiv.Perm.permMatrix A (cyc3 S))
        = (X * Equiv.Perm.permMatrix A (cyc3 S)) * Equiv.Perm.permMatrix A (cyc3 S) := by
          rw [← mul_assoc]
      _ = (Equiv.Perm.permMatrix A (cyc3 S) * X) * Equiv.Perm.permMatrix A (cyc3 S) := by
          rw [hX']
      _ = Equiv.Perm.permMatrix A (cyc3 S)
            * (X * Equiv.Perm.permMatrix A (cyc3 S)) := by rw [mul_assoc]
      _ = Equiv.Perm.permMatrix A (cyc3 S) * (Equiv.Perm.permMatrix A (cyc3 S) * X) := by
          rw [hX']
      _ = (Equiv.Perm.permMatrix A (cyc3 S) * Equiv.Perm.permMatrix A (cyc3 S)) * X := by
          rw [← mul_assoc]
  unfold Cp
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_add,
    Matrix.add_mul]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, hX', hX2]

/-- `Cp` is a projection when `lam³ = 1`. -/
theorem Cp_idem {S : Type} [Fintype S] [DecidableEq S] (lam : ℂ) (hlam : lam ^ 3 = 1) :
    Cp (A := A) S lam * Cp S lam = Cp S lam := by
  rw [show Cp (A := A) S lam = PsiC.cycProj (A := A) (cyc3 S) lam from rfl]
  exact PsiC.cycProj_idem (A := A) (cyc3 S) lam (cyc3_cube S) hlam

/-- A ring element commuting with `u` and `e` commutes with the orbit sum `orb3 e`. -/
theorem comm_orb3_gen {M : Type} [Ring M] {X e u : M} (hXu : X * u = u * X)
    (hXe : X * e = e * X) :
    X * (e + u * e * (u * u) + (u * u) * e * u) =
      (e + u * e * (u * u) + (u * u) * e * u) * X := by
  have hXu2 : X * (u * u) = (u * u) * X := by
    calc X * (u * u) = (X * u) * u := by rw [← mul_assoc]
      _ = (u * X) * u := by rw [hXu]
      _ = u * (X * u) := by rw [mul_assoc]
      _ = u * (u * X) := by rw [hXu]
      _ = (u * u) * X := by rw [← mul_assoc]
  have h1 : X * (u * e * (u * u)) = (u * e * (u * u)) * X := by
    calc X * (u * e * (u * u)) = (X * u) * e * (u * u) := by noncomm_ring
      _ = (u * X) * e * (u * u) := by rw [hXu]
      _ = (u * (X * e)) * (u * u) := by noncomm_ring
      _ = (u * (e * X)) * (u * u) := by rw [hXe]
      _ = (u * e) * (X * (u * u)) := by noncomm_ring
      _ = (u * e) * ((u * u) * X) := by rw [hXu2]
      _ = (u * e * (u * u)) * X := by noncomm_ring
  have h2 : X * ((u * u) * e * u) = ((u * u) * e * u) * X := by
    calc X * ((u * u) * e * u) = (X * (u * u)) * e * u := by noncomm_ring
      _ = ((u * u) * X) * e * u := by rw [hXu2]
      _ = ((u * u) * (X * e)) * u := by noncomm_ring
      _ = ((u * u) * (e * X)) * u := by rw [hXe]
      _ = (u * u) * e * (X * u) := by noncomm_ring
      _ = (u * u) * e * (u * X) := by rw [hXu]
      _ = ((u * u) * e * u) * X := by noncomm_ring
  rw [mul_add, mul_add, add_mul, add_mul, hXe, h1, h2] <;> abel

/-! ## The block splitting -/

/-- **The four-block decomposition of `(p ⊕ q)^{⊗3}`.**  For `lam³ = 1` the class of the triple
tensor power of `p ⊕ q` cut down by the spectral projector of the cyclic permutation is the sum of
the two "pure" blocks (`cubePart lam p`, `cubePart lam q`) and the two free-orbit contributions
(each of which, by `clsM_orb3`, is independent of `lam`). -/
theorem psi3_split_key (hA : ∀ x y : A, x * y = y * x) {p q : Mat A} (hp : p.IsIdem)
    (hq : q.IsIdem) (lam : ℂ) (hlam : lam ^ 3 = 1) :
    clsM (SQ (Fin p.1 ⊕ Fin q.1))
        (kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
      = cls (cubePart lam p) + cls (cubePart lam q)
        + clsM (SQ (Fin p.1 ⊕ Fin q.1))
            (kron3g (sumBlk (A := A) p q) * eBlk (m := p.1) (n := q.1) w001)
        + clsM (SQ (Fin p.1 ⊕ Fin q.1))
            (kron3g (sumBlk (A := A) p q) * eBlk (m := p.1) (n := q.1) w011) := by
  have hXidem : kron3g (sumBlk (A := A) p q) * kron3g (sumBlk p q) = kron3g (sumBlk p q) :=
    kron3g_sumBlk_idem (A := A) hA hp hq
  have hXU : kron3g (sumBlk (A := A) p q) * uPerm A (Fin p.1 ⊕ Fin q.1)
      = uPerm A (Fin p.1 ⊕ Fin q.1) * kron3g (sumBlk p q) :=
    kron3g_sumBlk_comm_uPerm (A := A) hA
  have hClidem : Cp (Fin p.1 ⊕ Fin q.1) lam * Cp (Fin p.1 ⊕ Fin q.1) lam
      = Cp (Fin p.1 ⊕ Fin q.1) lam := Cp_idem (A := A) (S := Fin p.1 ⊕ Fin q.1) lam hlam
  have hXCl : kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam
      = Cp (Fin p.1 ⊕ Fin q.1) lam * kron3g (sumBlk p q) :=
    comm_Cp_of_comm_uPerm hA hXU lam
  have hYidem : (kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
      * (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
      = kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam :=
    idem_mul_of_comm hXidem hClidem hXCl
  have hq1idem : eBlk (A := A) (m := p.1) (n := q.1) w000 * eBlk w000 = eBlk w000 :=
    eBlk_idem (A := A) hA w000
  have hq2idem : eBlk (A := A) (m := p.1) (n := q.1) w111 * eBlk w111 = eBlk w111 :=
    eBlk_idem (A := A) hA w111
  have hq3idem : orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (A := A) (m := p.1) (n := q.1) w001)
      * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001) = orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001) :=
    orb3_eBlk_idem (A := A) hA ne_rotW_w001 ne_rotW2_w001
  have hq4idem : orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (A := A) (m := p.1) (n := q.1) w011)
      * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011) = orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011) :=
    orb3_eBlk_idem (A := A) hA ne_rotW_w011 ne_rotW2_w011
  have hXq1 : kron3g (sumBlk (A := A) p q) * eBlk (m := p.1) (n := q.1) w000
      = eBlk w000 * kron3g (sumBlk p q) := kron3g_sumBlk_comm_eBlk (A := A) hA w000
  have hXq2 : kron3g (sumBlk (A := A) p q) * eBlk (m := p.1) (n := q.1) w111
      = eBlk w111 * kron3g (sumBlk p q) := kron3g_sumBlk_comm_eBlk (A := A) hA w111
  have hXq3 : kron3g (sumBlk (A := A) p q)
        * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (m := p.1) (n := q.1) w001)
      = orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001) * kron3g (sumBlk p q) := by
    rw [orb3, comm_orb3_gen hXU (kron3g_sumBlk_comm_eBlk (A := A) hA w001)]
  have hXq4 : kron3g (sumBlk (A := A) p q)
        * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (m := p.1) (n := q.1) w011)
      = orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011) * kron3g (sumBlk p q) := by
    rw [orb3, comm_orb3_gen hXU (kron3g_sumBlk_comm_eBlk (A := A) hA w011)]
  have hClq1 : Cp (Fin p.1 ⊕ Fin q.1) lam * eBlk (m := p.1) (n := q.1) w000
      = eBlk w000 * Cp (Fin p.1 ⊕ Fin q.1) lam :=
    (comm_Cp_of_comm_uPerm hA (hX := (uPerm_comm_eBlk_w000 (A := A) hA).symm) lam).symm
  have hClq2 : Cp (Fin p.1 ⊕ Fin q.1) lam * eBlk (m := p.1) (n := q.1) w111
      = eBlk w111 * Cp (Fin p.1 ⊕ Fin q.1) lam :=
    (comm_Cp_of_comm_uPerm hA (hX := (uPerm_comm_eBlk_w111 (A := A) hA).symm) lam).symm
  have hClq3 : Cp (Fin p.1 ⊕ Fin q.1) lam * orb3 (Fin p.1 ⊕ Fin q.1)
        (eBlk (m := p.1) (n := q.1) w001)
      = orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001) * Cp (Fin p.1 ⊕ Fin q.1) lam :=
    (comm_Cp_of_comm_uPerm hA
      (hX := (uPerm_comm_orb3 (eBlk (A := A) (m := p.1) (n := q.1) w001)).symm) lam).symm
  have hClq4 : Cp (Fin p.1 ⊕ Fin q.1) lam * orb3 (Fin p.1 ⊕ Fin q.1)
        (eBlk (m := p.1) (n := q.1) w011)
      = orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011) * Cp (Fin p.1 ⊕ Fin q.1) lam :=
    (comm_Cp_of_comm_uPerm hA
      (hX := (uPerm_comm_orb3 (eBlk (A := A) (m := p.1) (n := q.1) w011)).symm) lam).symm
  have hYq1 : (kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
      * eBlk (m := p.1) (n := q.1) w000
      = eBlk w000 * (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) := by
    calc (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w000
        = kron3g (sumBlk p q) * (Cp (Fin p.1 ⊕ Fin q.1) lam * eBlk w000) := by rw [mul_assoc]
      _ = kron3g (sumBlk p q) * (eBlk w000 * Cp (Fin p.1 ⊕ Fin q.1) lam) := by rw [hClq1]
      _ = (kron3g (sumBlk p q) * eBlk w000) * Cp (Fin p.1 ⊕ Fin q.1) lam := by rw [← mul_assoc]
      _ = (eBlk w000 * kron3g (sumBlk p q)) * Cp (Fin p.1 ⊕ Fin q.1) lam := by rw [hXq1]
      _ = eBlk w000 * (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) := by rw [mul_assoc]
  have hYq2 : (kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
      * eBlk (m := p.1) (n := q.1) w111
      = eBlk w111 * (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) := by
    calc (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w111
        = kron3g (sumBlk p q) * (Cp (Fin p.1 ⊕ Fin q.1) lam * eBlk w111) := by rw [mul_assoc]
      _ = kron3g (sumBlk p q) * (eBlk w111 * Cp (Fin p.1 ⊕ Fin q.1) lam) := by rw [hClq2]
      _ = (kron3g (sumBlk p q) * eBlk w111) * Cp (Fin p.1 ⊕ Fin q.1) lam := by rw [← mul_assoc]
      _ = (eBlk w111 * kron3g (sumBlk p q)) * Cp (Fin p.1 ⊕ Fin q.1) lam := by rw [hXq2]
      _ = eBlk w111 * (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) := by rw [mul_assoc]
  have hYq3 : (kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
      * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (m := p.1) (n := q.1) w001)
      = orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001)
        * (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) := by
    calc (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
          * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001)
        = kron3g (sumBlk p q) * (Cp (Fin p.1 ⊕ Fin q.1) lam
            * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001)) := by rw [mul_assoc]
      _ = kron3g (sumBlk p q) * (orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001)
            * Cp (Fin p.1 ⊕ Fin q.1) lam) := by rw [hClq3]
      _ = (kron3g (sumBlk p q) * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001))
            * Cp (Fin p.1 ⊕ Fin q.1) lam := by rw [← mul_assoc]
      _ = (orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001) * kron3g (sumBlk p q))
            * Cp (Fin p.1 ⊕ Fin q.1) lam := by rw [hXq3]
      _ = orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001)
            * (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) := by rw [mul_assoc]
  have hYq4 : (kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
      * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (m := p.1) (n := q.1) w011)
      = orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011)
        * (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) := by
    calc (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
          * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011)
        = kron3g (sumBlk p q) * (Cp (Fin p.1 ⊕ Fin q.1) lam
            * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011)) := by rw [mul_assoc]
      _ = kron3g (sumBlk p q) * (orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011)
            * Cp (Fin p.1 ⊕ Fin q.1) lam) := by rw [hClq4]
      _ = (kron3g (sumBlk p q) * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011))
            * Cp (Fin p.1 ⊕ Fin q.1) lam := by rw [← mul_assoc]
      _ = (orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011) * kron3g (sumBlk p q))
            * Cp (Fin p.1 ⊕ Fin q.1) lam := by rw [hXq4]
      _ = orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011)
            * (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) := by rw [mul_assoc]
  -- orthogonality of the four projections
  have h12 : eBlk (A := A) (m := p.1) (n := q.1) w000 * eBlk w111 = 0 :=
    eBlk_orth (A := A) hA (by decide : w000 ≠ w111)
  have h21 : eBlk (A := A) (m := p.1) (n := q.1) w111 * eBlk w000 = 0 :=
    eBlk_orth (A := A) hA (by decide : w111 ≠ w000)
  have h13 : eBlk (A := A) (m := p.1) (n := q.1) w000
      * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001) = 0 :=
    eBlk_mul_orb3_eq_zero (A := A) hA (by decide : w000 ≠ w001)
      (by decide : w000 ≠ rotW w001) (by decide : w000 ≠ rotW (rotW w001))
  have h31 : orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (A := A) (m := p.1) (n := q.1) w001)
      * eBlk w000 = 0 :=
    orb3_mul_eBlk_eq_zero (A := A) hA (by decide : w001 ≠ w000)
      (by decide : rotW w001 ≠ w000) (by decide : rotW (rotW w001) ≠ w000)
  have h14 : eBlk (A := A) (m := p.1) (n := q.1) w000
      * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011) = 0 :=
    eBlk_mul_orb3_eq_zero (A := A) hA (by decide : w000 ≠ w011)
      (by decide : w000 ≠ rotW w011) (by decide : w000 ≠ rotW (rotW w011))
  have h41 : orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (A := A) (m := p.1) (n := q.1) w011)
      * eBlk w000 = 0 :=
    orb3_mul_eBlk_eq_zero (A := A) hA (by decide : w011 ≠ w000)
      (by decide : rotW w011 ≠ w000) (by decide : rotW (rotW w011) ≠ w000)
  have h23 : eBlk (A := A) (m := p.1) (n := q.1) w111
      * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001) = 0 :=
    eBlk_mul_orb3_eq_zero (A := A) hA (by decide : w111 ≠ w001)
      (by decide : w111 ≠ rotW w001) (by decide : w111 ≠ rotW (rotW w001))
  have h32 : orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (A := A) (m := p.1) (n := q.1) w001)
      * eBlk w111 = 0 :=
    orb3_mul_eBlk_eq_zero (A := A) hA (by decide : w001 ≠ w111)
      (by decide : rotW w001 ≠ w111) (by decide : rotW (rotW w001) ≠ w111)
  have h24 : eBlk (A := A) (m := p.1) (n := q.1) w111
      * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011) = 0 :=
    eBlk_mul_orb3_eq_zero (A := A) hA (by decide : w111 ≠ w011)
      (by decide : w111 ≠ rotW w011) (by decide : w111 ≠ rotW (rotW w011))
  have h42 : orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (A := A) (m := p.1) (n := q.1) w011)
      * eBlk w111 = 0 :=
    orb3_mul_eBlk_eq_zero (A := A) hA (by decide : w011 ≠ w111)
      (by decide : rotW w011 ≠ w111) (by decide : rotW (rotW w011) ≠ w111)
  have hpart : eBlk (A := A) (m := p.1) (n := q.1) w000 + eBlk w111
      + orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001)
      + orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011) = 1 := partition (A := A) hA
  -- the remaining orthogonality relations, involving the `orb3`-orbits
  have h34 : orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (A := A) (m := p.1) (n := q.1) w001)
      * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011) = 0 := by
    have hq4 : orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (A := A) (m := p.1) (n := q.1) w011)
        = 1 - eBlk (m := p.1) (n := q.1) w000 - eBlk w111
          - orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001) := by
      rw [← hpart]; abel
    rw [hq4, mul_sub, mul_sub, mul_sub, h31, h32, mul_one, hq3idem]
    abel
  have h43 : orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (A := A) (m := p.1) (n := q.1) w011)
      * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001) = 0 := by
    have hq4 : orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (A := A) (m := p.1) (n := q.1) w011)
        = 1 - eBlk (m := p.1) (n := q.1) w000 - eBlk w111
          - orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001) := by
      rw [← hpart]; abel
    rw [hq4, sub_mul, sub_mul, sub_mul, h13, h23, one_mul, hq3idem]
    abel
  -- idempotency and orthogonality of the four pieces
  have hA1idem : ((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
        * eBlk (m := p.1) (n := q.1) w000)
      * ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w000)
      = (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w000 :=
    idem_mul_of_comm hYidem hq1idem hYq1
  have hA2idem : ((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
        * eBlk (m := p.1) (n := q.1) w111)
      * ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w111)
      = (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w111 :=
    idem_mul_of_comm hYidem hq2idem hYq2
  have hA3idem : ((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
        * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (m := p.1) (n := q.1) w001))
      * ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001))
      = (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
        * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001) :=
    idem_mul_of_comm hYidem hq3idem hYq3
  have hA4idem : ((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
        * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (m := p.1) (n := q.1) w011))
      * ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011))
      = (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
        * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011) :=
    idem_mul_of_comm hYidem hq4idem hYq4
  have hA12 : ((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
        * eBlk (m := p.1) (n := q.1) w000)
      * ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w111) = 0 :=
    mul_orth_of_orth hYq1 hYq2 hYidem h12
  have hA21 : ((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
        * eBlk (m := p.1) (n := q.1) w111)
      * ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w000) = 0 :=
    mul_orth_of_orth hYq2 hYq1 hYidem h21
  have hA34 : ((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
        * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (m := p.1) (n := q.1) w001))
      * ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011))
      = 0 := mul_orth_of_orth hYq3 hYq4 hYidem h34
  have hA43 : ((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
        * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (m := p.1) (n := q.1) w011))
      * ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001))
      = 0 := mul_orth_of_orth hYq4 hYq3 hYidem h43
  have hA13 : ((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
        * eBlk (m := p.1) (n := q.1) w000)
      * ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
          * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001)) = 0 := mul_orth_of_orth hYq1 hYq3 hYidem h13
  have hA31 : ((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
        * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (m := p.1) (n := q.1) w001))
      * ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w000) = 0 :=
    mul_orth_of_orth hYq3 hYq1 hYidem h31
  have hA14 : ((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
        * eBlk (m := p.1) (n := q.1) w000)
      * ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
          * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011)) = 0 := mul_orth_of_orth hYq1 hYq4 hYidem h14
  have hA41 : ((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
        * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (m := p.1) (n := q.1) w011))
      * ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w000) = 0 :=
    mul_orth_of_orth hYq4 hYq1 hYidem h41
  have hA23 : ((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
        * eBlk (m := p.1) (n := q.1) w111)
      * ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
          * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001)) = 0 := mul_orth_of_orth hYq2 hYq3 hYidem h23
  have hA32 : ((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
        * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (m := p.1) (n := q.1) w001))
      * ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w111) = 0 :=
    mul_orth_of_orth hYq3 hYq2 hYidem h32
  have hA24 : ((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
        * eBlk (m := p.1) (n := q.1) w111)
      * ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
          * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011)) = 0 := mul_orth_of_orth hYq2 hYq4 hYidem h24
  have hA42 : ((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
        * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (m := p.1) (n := q.1) w011))
      * ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w111) = 0 :=
    mul_orth_of_orth hYq4 hYq2 hYidem h42
  -- the pure blocks
  have hpure1 : (kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
      * eBlk (m := p.1) (n := q.1) w000 = kron3g (sumBlkP p q) * Cp (Fin p.1 ⊕ Fin q.1) lam := by
    calc (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w000
        = kron3g (sumBlk p q) * (Cp (Fin p.1 ⊕ Fin q.1) lam * eBlk w000) := by rw [mul_assoc]
      _ = kron3g (sumBlk p q) * (eBlk w000 * Cp (Fin p.1 ⊕ Fin q.1) lam) := by rw [hClq1]
      _ = (kron3g (sumBlk p q) * eBlk w000) * Cp (Fin p.1 ⊕ Fin q.1) lam := by rw [← mul_assoc]
      _ = kron3g (sumBlkP p q) * Cp (Fin p.1 ⊕ Fin q.1) lam := by
            rw [kron3g_sumBlk_mul_eBlk_w000 (A := A) hA]
  have hpure2 : (kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
      * eBlk (m := p.1) (n := q.1) w111 = kron3g (sumBlkQ p q) * Cp (Fin p.1 ⊕ Fin q.1) lam := by
    calc (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w111
        = kron3g (sumBlk p q) * (Cp (Fin p.1 ⊕ Fin q.1) lam * eBlk w111) := by rw [mul_assoc]
      _ = kron3g (sumBlk p q) * (eBlk w111 * Cp (Fin p.1 ⊕ Fin q.1) lam) := by rw [hClq2]
      _ = (kron3g (sumBlk p q) * eBlk w111) * Cp (Fin p.1 ⊕ Fin q.1) lam := by rw [← mul_assoc]
      _ = kron3g (sumBlkQ p q) * Cp (Fin p.1 ⊕ Fin q.1) lam := by
            rw [kron3g_sumBlk_mul_eBlk_w111 (A := A) hA]
  have hpure1cls : clsM (SQ (Fin p.1 ⊕ Fin q.1))
      ((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk (m := p.1) (n := q.1) w000)
      = cls (cubePart lam p) := by
    rw [hpure1]
    exact clsM_sumBlkP_cubePart (A := A) p q lam
  have hpure2cls : clsM (SQ (Fin p.1 ⊕ Fin q.1))
      ((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk (m := p.1) (n := q.1) w111)
      = cls (cubePart lam q) := by
    rw [hpure2]
    exact clsM_sumBlkQ_cubePart (A := A) p q lam
  -- the mixed blocks
  have hmix3 : clsM (SQ (Fin p.1 ⊕ Fin q.1))
      ((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
        * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (m := p.1) (n := q.1) w001))
      = clsM (SQ (Fin p.1 ⊕ Fin q.1))
          (kron3g (sumBlk p q) * eBlk (m := p.1) (n := q.1) w001) :=
    clsM_orb3 (A := A) (kron3g (sumBlk p q)) (eBlk (m := p.1) (n := q.1) w001) hXidem
      (eBlk_idem (A := A) hA w001) (uPerm_cube (Fin p.1 ⊕ Fin q.1))
      (kron3g_sumBlk_comm_eBlk (A := A) hA w001) hXU
      (eBlk_mul_uPerm_mul_eBlk (A := A) hA ne_rotW_w001)
      (eBlk_mul_uPerm_sq_mul_eBlk (A := A) hA ne_rotW2_w001) lam hlam
  have hmix4 : clsM (SQ (Fin p.1 ⊕ Fin q.1))
      ((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
        * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk (m := p.1) (n := q.1) w011))
      = clsM (SQ (Fin p.1 ⊕ Fin q.1))
          (kron3g (sumBlk p q) * eBlk (m := p.1) (n := q.1) w011) :=
    clsM_orb3 (A := A) (kron3g (sumBlk p q)) (eBlk (m := p.1) (n := q.1) w011) hXidem
      (eBlk_idem (A := A) hA w011) (uPerm_cube (Fin p.1 ⊕ Fin q.1))
      (kron3g_sumBlk_comm_eBlk (A := A) hA w011) hXU
      (eBlk_mul_uPerm_mul_eBlk (A := A) hA ne_rotW_w011)
      (eBlk_mul_uPerm_sq_mul_eBlk (A := A) hA ne_rotW2_w011) lam hlam
  -- assemble
  have hE1 : (((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w000)
        + (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w111)
      * (((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w000)
        + (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w111)
      = ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w000)
        + (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w111 :=
    idem_add_of_orth hA1idem hA2idem hA12 hA21
  have hE2 : (((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
          * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001))
        + (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011))
      * (((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001))
        + (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011))
      = ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001))
        + (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011) :=
    idem_add_of_orth hA3idem hA4idem hA34 hA43
  have hEF : (((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w000)
        + (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w111)
      * (((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001))
        + (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011))
      = 0 := by
    rw [add_mul, mul_add, mul_add, hA13, hA14, hA23, hA24]
    abel
  have hFE : (((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
          * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001))
        + (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011))
      * (((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w000)
        + (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w111)
      = 0 := by
    rw [add_mul, mul_add, mul_add, hA31, hA32, hA41, hA42]
    abel
  have hsum : (((kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w000)
        + (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w111)
      + (((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001))
        + (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011))
      = kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam := by
    have hq : (eBlk (A := A) (m := p.1) (n := q.1) w000 + eBlk w111)
        + (orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001)
          + orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011)) = 1 := by
      rw [← hpart]; abel
    rw [← mul_add, ← mul_add, ← mul_add, hq, mul_one]
  have final : clsM (SQ (Fin p.1 ⊕ Fin q.1))
        (kron3g (sumBlk (A := A) p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)
      = clsM (SQ (Fin p.1 ⊕ Fin q.1)) ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w000)
        + clsM (SQ (Fin p.1 ⊕ Fin q.1)) ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * eBlk w111)
        + clsM (SQ (Fin p.1 ⊕ Fin q.1))
            ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w001))
        + clsM (SQ (Fin p.1 ⊕ Fin q.1))
            ((kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) * orb3 (Fin p.1 ⊕ Fin q.1) (eBlk w011)) := by
    conv_lhs => rw [← hsum]
    rw [clsM_idem_add _ _ hE1 hE2 hEF hFE, clsM_idem_add _ _ hA1idem hA2idem hA12 hA21,
      clsM_idem_add _ _ hA3idem hA4idem hA34 hA43]
    abel
  rw [final, hpure1cls, hpure2cls, hmix3, hmix4]

end

/-- **Additivity of `ψ³` on `K₀`.** -/
theorem psi3Cls_sum {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    {p q : Mat A} (hp : p.IsIdem) (hq : q.IsIdem) :
    psi3Cls (p.sum q) = psi3Cls p + psi3Cls q := by
  rw [psi3Cls, psi3Cls, psi3Cls, if_pos (Mat.isIdem_sum hp hq), if_pos hp, if_pos hq]
  have h1 : cls (cubePart 1 (p.sum q)) = cls (cubePart 1 p) + cls (cubePart 1 q)
      + (clsM (SQ (Fin p.1 ⊕ Fin q.1))
            (kron3g (sumBlk (A := A) p q) * eBlk (m := p.1) (n := q.1) w001)
          + clsM (SQ (Fin p.1 ⊕ Fin q.1))
            (kron3g (sumBlk p q) * eBlk (m := p.1) (n := q.1) w011)) := by
    rw [show cls (cubePart 1 (p.sum q))
          = clsM (SQ (Fin (p.1 + q.1))) (cubePartP 1 (p.sum q)) from
        (clsM_I3_cubePartP 1 (p.sum q)).symm,
      ← clsM_sumBlk_cubePartP (A := A) p q 1]
    rw [psi3_split_key (A := A) hA hp hq 1 (by norm_num)]
    abel
  have h2 : cls (cubePart omega (p.sum q)) = cls (cubePart omega p) + cls (cubePart omega q)
      + (clsM (SQ (Fin p.1 ⊕ Fin q.1))
            (kron3g (sumBlk (A := A) p q) * eBlk (m := p.1) (n := q.1) w001)
          + clsM (SQ (Fin p.1 ⊕ Fin q.1))
            (kron3g (sumBlk p q) * eBlk (m := p.1) (n := q.1) w011)) := by
    rw [show cls (cubePart omega (p.sum q))
          = clsM (SQ (Fin (p.1 + q.1))) (cubePartP omega (p.sum q)) from
        (clsM_I3_cubePartP omega (p.sum q)).symm,
      ← clsM_sumBlk_cubePartP (A := A) p q omega]
    rw [psi3_split_key (A := A) hA hp hq omega omega_pow_three]
    abel
  rw [h1, h2]
  abel

end Work.KT.Psi
