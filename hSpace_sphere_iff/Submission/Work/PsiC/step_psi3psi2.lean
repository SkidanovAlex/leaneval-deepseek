import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.PsiC.BFrame
import Submission.Work.KT.Psi.clsM_idem_add
import Submission.Work.PsiC.DepsDefs
import Submission.Work.PsiC.Deps_idem
import Submission.Work.PsiC.IdemMul3
import Submission.Work.PsiC.PB_comm_frame
import Submission.Work.PsiC.gamB_decomp
import Submission.Work.PsiC.bridge_cube_sq2

/-!
# `Work.PsiC.step_psi3psi2`

`ψ³ψ²` on a generator: the class of `cubePart λ (sq2Part ε p)` is the "leading" class
`Tcls p (λ²ε)` minus the "rest" class `Dcls p ε`.

The bridge `bridge_cube_sq2` computes the left hand side as the class of `PB p · E_ε · Q_λ` in
the six-fold tensor frame `IB p.1`, where

* `E_ε = Eeps ε` is the joint `ε`-eigenspace projector of the three pair swaps `sg0,sg1,sg2`,
* `Q_λ = cycProj (cB) λ` is the `λ`-eigenspace projector of the cyclic permutation `cB` of the
  three pairs.

`gamB_decomp` and `Deps_idem` express the right hand side as
`clsM (PB p · Q_λ · E_ε) + clsM (PB p · Q_λ · D_ε) - clsM (PB p · Edel ε (-ε) (-ε))`,
where `D_ε = Deps ε = h_ε(sB) - E_ε`.  The remaining input is the orbit computation
`clsM (PB p · Q_λ · D_ε) = clsM (PB p · Edel ε (-ε) (-ε))`: `D_ε` is the sum of the three
`Edel`-projectors obtained from `Edel ε (-ε) (-ε)` by the cyclic permutation `cB` of the three
pairs, so the free-orbit lemma `Work.KT.PsiC.clsM_orbit` applies with `g = cB.permMatrix`,
`F = Edel ε (-ε) (-ε)`, `k = 3`, and `λ` a cube root of unity.
-/

set_option linter.unusedSectionVars false

namespace Work.PsiC

open Matrix Work.KT Work.KT.Psi Work.KT.PsiC

noncomputable section

namespace StepPsi3Psi2Aux

variable {A : Type} [Ring A] [Algebra ℂ A]

/-! ## 1.  The joint spectral decomposition of a product of three involutions -/

/-- The two eigenspace projectors of an involution add up to `1`. -/
theorem hps_add_neg {R : Type} [Ring R] [Algebra ℂ R] (ε : ℂ) (x : R) :
    DepsAux.hps ε x + DepsAux.hps (-ε) x = 1 := by
  have h1 : ε • x + (-ε) • x = 0 := by rw [neg_smul, add_neg_cancel]
  have h2 : (1 + ε • x) + (1 + (-ε) • x) = (2 : ℂ) • (1 : R) := by
    rw [show (1 + ε • x) + (1 + (-ε) • x) = ((1 : R) + 1) + (ε • x + (-ε) • x) by abel,
      h1, add_zero]
    rw [← two_mul (1 : R), Algebra.smul_def, map_ofNat, mul_one]
  rw [DepsAux.hps, DepsAux.hps, ← smul_add, h2, smul_smul,
    show ((1 : ℂ) / 2) * 2 = 1 by norm_num, one_smul]

/-- An involution is the sum of its two eigenspaces, weighted by their eigenvalues. -/
theorem hps_eq_smul_sub {R : Type} [Ring R] [Algebra ℂ R] (ε : ℂ) (heps : ε ^ 2 = 1)
    (x : R) (hx : x * x = 1) :
    x = ε • (DepsAux.hps ε x - DepsAux.hps (-ε) x) := by
  have hne : (-ε) ^ 2 = 1 := by rw [neg_sq, heps]
  have h1 := DepsAux.x_mul_hps ε heps x hx
  have h2 := DepsAux.x_mul_hps (-ε) hne x hx
  calc x = x * 1 := (mul_one x).symm
    _ = x * (DepsAux.hps ε x + DepsAux.hps (-ε) x) := by rw [hps_add_neg]
    _ = x * DepsAux.hps ε x + x * DepsAux.hps (-ε) x := by rw [mul_add]
    _ = ε • DepsAux.hps ε x + (-ε) • DepsAux.hps (-ε) x := by rw [h1, h2]
    _ = ε • (DepsAux.hps ε x - DepsAux.hps (-ε) x) := by
        rw [smul_sub, neg_smul, sub_eq_add_neg]

/-- The two eigenspace projectors of an involution are orthogonal. -/
theorem hps_orth {R : Type} [Ring R] [Algebra ℂ R] (ε : ℂ) (heps : ε ^ 2 = 1)
    (x : R) (hx : x * x = 1) :
    DepsAux.hps ε x * DepsAux.hps (-ε) x = 0 := by
  have h3 : DepsAux.hps (-ε) x = 1 - DepsAux.hps ε x := by rw [← hps_add_neg ε x]; abel
  rw [h3, mul_sub, mul_one, DepsAux.hps_idem ε heps x hx, sub_self]

/-- **The `hps` decomposition.**  For three involutions `x, y, z` and `ε² = 1`, the
`ε`-projector of the product splits into the four joint eigenspace projectors whose eigenvalue
product is `ε`.  No commutativity is needed. -/
theorem hps_split3 {R : Type} [Ring R] [Algebra ℂ R] (ε : ℂ) (heps : ε ^ 2 = 1)
    (x y z : R) (hx : x * x = 1) (hy : y * y = 1) (hz : z * z = 1) :
    DepsAux.hps ε (x * y * z) =
      DepsAux.hps ε x * DepsAux.hps ε y * DepsAux.hps ε z +
      (DepsAux.hps ε x * DepsAux.hps (-ε) y * DepsAux.hps (-ε) z +
       DepsAux.hps (-ε) x * DepsAux.hps ε y * DepsAux.hps (-ε) z +
       DepsAux.hps (-ε) x * DepsAux.hps (-ε) y * DepsAux.hps ε z) := by
  have hee : ε * ε = 1 := by rw [← pow_two]; exact heps
  have hss : ∀ W : R, ε • (ε • W) = W := by
    intro W; rw [smul_smul, hee, one_smul]
  set P := DepsAux.hps ε x with hP
  set P' := DepsAux.hps (-ε) x with hP'
  set Q := DepsAux.hps ε y with hQ
  set Q' := DepsAux.hps (-ε) y with hQ'
  set Rr := DepsAux.hps ε z with hRr
  set Rr' := DepsAux.hps (-ε) z with hRr'
  have hx' : x = ε • (P - P') := by rw [hP, hP']; exact hps_eq_smul_sub ε heps x hx
  have hy' : y = ε • (Q - Q') := by rw [hQ, hQ']; exact hps_eq_smul_sub ε heps y hy
  have hz' : z = ε • (Rr - Rr') := by rw [hRr, hRr']; exact hps_eq_smul_sub ε heps z hz
  have hone : (P + P') * (Q + Q') * (Rr + Rr') = 1 := by
    rw [hP, hP', hQ, hQ', hRr, hRr', hps_add_neg ε x, hps_add_neg ε y, hps_add_neg ε z,
      mul_one, mul_one]
  have hkey : (1 : R) + (P - P') * (Q - Q') * (Rr - Rr') =
      (P * Q * Rr + (P * Q' * Rr' + P' * Q * Rr' + P' * Q' * Rr)) +
        (P * Q * Rr + (P * Q' * Rr' + P' * Q * Rr' + P' * Q' * Rr)) := by
    rw [← hone]
    noncomm_ring
  have harg : (ε • (P - P')) * (ε • (Q - Q')) * (ε • (Rr - Rr')) =
      ε • ((P - P') * (Q - Q') * (Rr - Rr')) := by
    rw [smul_mul_smul, smul_mul_smul]
    congr 1
    rw [hee, one_mul]
  rw [hx', hy', hz', harg]
  rw [DepsAux.hps, hss]
  rw [hkey, DepsAux.two_smulC, smul_smul,
    show ((1 : ℂ) / 2) * 2 = 1 by norm_num, one_smul]

/-! ## 2.  The frame: `sB` as a product of the pair swaps -/

theorem sB_permMatrix (n : ℕ) :
    (sB n).permMatrix A = (sg0 n).permMatrix A * (sg1 n).permMatrix A *
      (sg2 n).permMatrix A := by
  have k01 : (sg0 n).permMatrix A * (sg1 n).permMatrix A =
      (sg1 n).permMatrix A * (sg0 n).permMatrix A := by
    rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul, sg_comm01]
  have k02 : (sg0 n).permMatrix A * (sg2 n).permMatrix A =
      (sg2 n).permMatrix A * (sg0 n).permMatrix A := by
    rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul, sg_comm02]
  have k12 : (sg1 n).permMatrix A * (sg2 n).permMatrix A =
      (sg2 n).permMatrix A * (sg1 n).permMatrix A := by
    rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul, sg_comm12]
  rw [sB, Matrix.permMatrix_mul, Matrix.permMatrix_mul]
  calc (sg2 n).permMatrix A * ((sg1 n).permMatrix A * (sg0 n).permMatrix A)
      = ((sg2 n).permMatrix A * (sg1 n).permMatrix A) * (sg0 n).permMatrix A := by
        noncomm_ring
    _ = ((sg1 n).permMatrix A * (sg2 n).permMatrix A) * (sg0 n).permMatrix A := by rw [← k12]
    _ = (sg1 n).permMatrix A * ((sg2 n).permMatrix A * (sg0 n).permMatrix A) := by
        noncomm_ring
    _ = (sg1 n).permMatrix A * ((sg0 n).permMatrix A * (sg2 n).permMatrix A) := by rw [← k02]
    _ = ((sg1 n).permMatrix A * (sg0 n).permMatrix A) * (sg2 n).permMatrix A := by
        noncomm_ring
    _ = ((sg0 n).permMatrix A * (sg1 n).permMatrix A) * (sg2 n).permMatrix A := by rw [← k01]

/-- **`Deps` is the sum of the three `(ε,-ε,-ε)`-type projectors.** -/
theorem Deps_eq_sum (n : ℕ) (eps : ℂ) (heps : eps ^ 2 = 1) :
    Deps (A := A) eps n = Edel (A := A) eps (-eps) (-eps) n +
      Edel (A := A) (-eps) eps (-eps) n + Edel (A := A) (-eps) (-eps) eps n := by
  have h0 : (sg0 n).permMatrix A * (sg0 n).permMatrix A = 1 := by
    rw [← Matrix.permMatrix_mul, sg0_mul_self, Matrix.permMatrix_one]
  have h1 : (sg1 n).permMatrix A * (sg1 n).permMatrix A = 1 := by
    rw [← Matrix.permMatrix_mul, sg1_mul_self, Matrix.permMatrix_one]
  have h2 : (sg2 n).permMatrix A * (sg2 n).permMatrix A = 1 := by
    rw [← Matrix.permMatrix_mul, sg2_mul_self, Matrix.permMatrix_one]
  have hsB := sB_permMatrix (A := A) n
  have h := hps_split3 (R := Matrix (IB n) (IB n) A) eps heps
    ((sg0 n).permMatrix A) ((sg1 n).permMatrix A) ((sg2 n).permMatrix A) h0 h1 h2
  rw [hps_eq_halfProj eps (sg0 n), hps_eq_halfProj eps (sg1 n), hps_eq_halfProj eps (sg2 n),
      hps_eq_halfProj (-eps) (sg0 n), hps_eq_halfProj (-eps) (sg1 n),
      hps_eq_halfProj (-eps) (sg2 n), ← hsB, hps_eq_halfProj eps (sB n)] at h
  rw [show Deps (A := A) eps n = halfProj eps (sB n) - Eeps eps n from rfl, h]
  exact add_sub_cancel_left _ _

/-! ## 3.  Conjugation by the pair cycle `cB` -/

/-- `(cB n)⁻¹ = cB n * cB n`. -/
theorem cB_inv_eq_sq (n : ℕ) : (cB n)⁻¹ = cB n * cB n := by
  have h := cB_cube n
  rw [mul_assoc] at h
  exact inv_eq_of_mul_eq_one_right h

theorem cB_mul_self_eq_inv (n : ℕ) :
    (cB n).permMatrix A * (cB n).permMatrix A = ((cB n)⁻¹).permMatrix A := by
  rw [← Matrix.permMatrix_mul, cB_inv_eq_sq]

theorem cB_permMatrix_mul_inv (n : ℕ) :
    (cB n).permMatrix A * ((cB n)⁻¹).permMatrix A = 1 := by
  rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

theorem cB_inv_permMatrix_mul (n : ℕ) :
    ((cB n)⁻¹).permMatrix A * (cB n).permMatrix A = 1 := by
  rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

theorem cB_inv_mul_self (n : ℕ) :
    ((cB n)⁻¹).permMatrix A * ((cB n)⁻¹).permMatrix A = (cB n).permMatrix A := by
  have h : (cB n)⁻¹ * (cB n)⁻¹ = cB n := by
    rw [cB_inv_eq_sq n]
    calc (cB n * cB n) * (cB n * cB n) = ((cB n * cB n) * cB n) * cB n := by rw [← mul_assoc]
      _ = 1 * cB n := by rw [show (cB n * cB n) * cB n = 1 from cB_cube n]
      _ = cB n := one_mul _
  rw [← Matrix.permMatrix_mul, h]

theorem cB_inv_sg0_cB (n : ℕ) : (cB n)⁻¹ * sg0 n * cB n = sg2 n := by
  apply Equiv.ext; intro x; rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨e,f⟩⟩
  simp only [Equiv.Perm.mul_apply, cB_apply, sg0_apply, sg2_apply, GamBDecomp.cB_symm_apply]

theorem cB_inv_sg1_cB (n : ℕ) : (cB n)⁻¹ * sg1 n * cB n = sg0 n := by
  apply Equiv.ext; intro x; rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨e,f⟩⟩
  simp only [Equiv.Perm.mul_apply, cB_apply, sg0_apply, sg1_apply, GamBDecomp.cB_symm_apply]

theorem cB_inv_sg2_cB (n : ℕ) : (cB n)⁻¹ * sg2 n * cB n = sg1 n := by
  apply Equiv.ext; intro x; rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨e,f⟩⟩
  simp only [Equiv.Perm.mul_apply, cB_apply, sg1_apply, sg2_apply, GamBDecomp.cB_symm_apply]

theorem cB_conj_halfProj_sg0 (hA : ∀ x y : A, x * y = y * x) (n : ℕ) (δ : ℂ) :
    (cB n).permMatrix A * halfProj δ (sg0 n) * ((cB n)⁻¹).permMatrix A =
      halfProj δ (sg2 n) := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  have hpm : (cB n).permMatrix A * (sg0 n).permMatrix A * ((cB n)⁻¹).permMatrix A =
      (sg2 n).permMatrix A := by
    rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul, ← mul_assoc, cB_inv_sg0_cB]
  rw [halfProj, halfProj, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul, hpm,
    cB_permMatrix_mul_inv]

theorem cB_conj_halfProj_sg1 (hA : ∀ x y : A, x * y = y * x) (n : ℕ) (δ : ℂ) :
    (cB n).permMatrix A * halfProj δ (sg1 n) * ((cB n)⁻¹).permMatrix A =
      halfProj δ (sg0 n) := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  have hpm : (cB n).permMatrix A * (sg1 n).permMatrix A * ((cB n)⁻¹).permMatrix A =
      (sg0 n).permMatrix A := by
    rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul, ← mul_assoc, cB_inv_sg1_cB]
  rw [halfProj, halfProj, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul, hpm,
    cB_permMatrix_mul_inv]

theorem cB_conj_halfProj_sg2 (hA : ∀ x y : A, x * y = y * x) (n : ℕ) (δ : ℂ) :
    (cB n).permMatrix A * halfProj δ (sg2 n) * ((cB n)⁻¹).permMatrix A =
      halfProj δ (sg1 n) := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  have hpm : (cB n).permMatrix A * (sg2 n).permMatrix A * ((cB n)⁻¹).permMatrix A =
      (sg1 n).permMatrix A := by
    rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul, ← mul_assoc, cB_inv_sg2_cB]
  rw [halfProj, halfProj, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul, hpm,
    cB_permMatrix_mul_inv]

theorem halfProj_sg01_comm (hA : ∀ x y : A, x * y = y * x) (n : ℕ) (δ η : ℂ) :
    halfProj (A := A) δ (sg0 n) * halfProj (A := A) η (sg1 n) =
      halfProj (A := A) η (sg1 n) * halfProj (A := A) δ (sg0 n) := by
  have h : (sg0 n).permMatrix A * (sg1 n).permMatrix A =
      (sg1 n).permMatrix A * (sg0 n).permMatrix A := by
    rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul, sg_comm01]
  have h1 : (sg0 n).permMatrix A * halfProj η (sg1 n) =
      halfProj η (sg1 n) * (sg0 n).permMatrix A :=
    halfProj_comm_of hA (sg1 n) η ((sg0 n).permMatrix A) h
  exact (halfProj_comm_of hA (sg0 n) δ (halfProj η (sg1 n)) h1.symm).symm

theorem halfProj_sg02_comm (hA : ∀ x y : A, x * y = y * x) (n : ℕ) (δ η : ℂ) :
    halfProj (A := A) δ (sg0 n) * halfProj (A := A) η (sg2 n) =
      halfProj (A := A) η (sg2 n) * halfProj (A := A) δ (sg0 n) := by
  have h : (sg0 n).permMatrix A * (sg2 n).permMatrix A =
      (sg2 n).permMatrix A * (sg0 n).permMatrix A := by
    rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul, sg_comm02]
  have h1 : (sg0 n).permMatrix A * halfProj η (sg2 n) =
      halfProj η (sg2 n) * (sg0 n).permMatrix A :=
    halfProj_comm_of hA (sg2 n) η ((sg0 n).permMatrix A) h
  exact (halfProj_comm_of hA (sg0 n) δ (halfProj η (sg2 n)) h1.symm).symm

theorem halfProj_sg12_comm (hA : ∀ x y : A, x * y = y * x) (n : ℕ) (δ η : ℂ) :
    halfProj (A := A) δ (sg1 n) * halfProj (A := A) η (sg2 n) =
      halfProj (A := A) η (sg2 n) * halfProj (A := A) δ (sg1 n) := by
  have h : (sg1 n).permMatrix A * (sg2 n).permMatrix A =
      (sg2 n).permMatrix A * (sg1 n).permMatrix A := by
    rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul, sg_comm12]
  have h1 : (sg1 n).permMatrix A * halfProj η (sg2 n) =
      halfProj η (sg2 n) * (sg1 n).permMatrix A :=
    halfProj_comm_of hA (sg2 n) η ((sg1 n).permMatrix A) h
  exact (halfProj_comm_of hA (sg1 n) δ (halfProj η (sg2 n)) h1.symm).symm

/-- Multiplication of conjugates: `g (a b) g⁻¹ = (g a g⁻¹)(g b g⁻¹)`. -/
theorem conj_mul_g {n : ℕ} (g gi a b : Matrix (IB n) (IB n) A) (h : gi * g = 1) :
    g * (a * b) * gi = (g * a * gi) * (g * b * gi) := by
  rw [show (g * a * gi) * (g * b * gi) = g * a * (gi * g) * b * gi by noncomm_ring, h,
    mul_one]
  noncomm_ring

/-- **Conjugation by `cB` cycles the pair swaps**: `cB · Edel a b c · cB⁻¹ = Edel b c a`. -/
theorem cB_conj_Edel (hA : ∀ x y : A, x * y = y * x) (n : ℕ) (a b c : ℂ) :
    (cB n).permMatrix A * Edel a b c n * ((cB n)⁻¹).permMatrix A = Edel b c a n := by
  have h02 : halfProj b (sg0 n) * halfProj a (sg2 n) =
      halfProj a (sg2 n) * halfProj b (sg0 n) := halfProj_sg02_comm hA n b a
  have h12 : halfProj a (sg2 n) * halfProj c (sg1 n) =
      halfProj c (sg1 n) * halfProj a (sg2 n) := (halfProj_sg12_comm hA n c a).symm
  rw [Edel, conj_mul_g _ _ _ _ (cB_inv_permMatrix_mul (A := A) n),
    conj_mul_g _ _ _ _ (cB_inv_permMatrix_mul (A := A) n),
    cB_conj_halfProj_sg0 hA, cB_conj_halfProj_sg1 hA, cB_conj_halfProj_sg2 hA]
  rw [show halfProj a (sg2 n) * halfProj b (sg0 n) * halfProj c (sg1 n) =
      (halfProj b (sg0 n) * halfProj a (sg2 n)) * halfProj c (sg1 n) from by rw [h02],
    show (halfProj b (sg0 n) * halfProj a (sg2 n)) * halfProj c (sg1 n) =
      halfProj b (sg0 n) * (halfProj a (sg2 n) * halfProj c (sg1 n)) from by noncomm_ring,
    h12,
    show halfProj b (sg0 n) * (halfProj c (sg1 n) * halfProj a (sg2 n)) =
      halfProj b (sg0 n) * halfProj c (sg1 n) * halfProj a (sg2 n) from by noncomm_ring]
  rfl

/-- `cB` commutes with the joint projector `Eeps ε`. -/
theorem cB_comm_Eeps (hA : ∀ x y : A, x * y = y * x) (n : ℕ) (eps : ℂ) :
    (cB n).permMatrix A * Eeps eps n = Eeps eps n * (cB n).permMatrix A := by
  have h : (cB n).permMatrix A * Eeps eps n * ((cB n)⁻¹).permMatrix A = Eeps eps n := by
    rw [show Eeps eps n = Edel eps eps eps n from rfl, cB_conj_Edel hA]
  have h2 : ((cB n).permMatrix A * Eeps eps n * ((cB n)⁻¹).permMatrix A) *
      (cB n).permMatrix A = Eeps eps n * (cB n).permMatrix A := by rw [h]
  rwa [Matrix.mul_assoc, cB_inv_permMatrix_mul, Matrix.mul_one] at h2

/-- `cB` commutes with the product `sB` of the pair swaps. -/
theorem cB_permMatrix_comm_sB (n : ℕ) :
    (cB n).permMatrix A * (sB n).permMatrix A = (sB n).permMatrix A * (cB n).permMatrix A := by
  have h := congrArg (fun σ : Equiv.Perm (IB n) => σ.permMatrix A) (cB_comm_sB n)
  rw [Matrix.permMatrix_mul, Matrix.permMatrix_mul] at h
  exact h.symm

/-! ## 4.  Orthogonality of the `Edel` projectors with different sign patterns -/

/-- The `(ε,b,c)` and `(-ε,b',c')` joint projectors are orthogonal. -/
theorem Edel_mul_Edel_sg0 (hA : ∀ x y : A, x * y = y * x) (n : ℕ) (eps b c b' c' : ℂ)
    (heps : eps ^ 2 = 1) :
    Edel (A := A) eps b c n * Edel (A := A) (-eps) b' c' n = 0 := by
  have h02 : halfProj (A := A) c (sg2 n) * halfProj (A := A) (-eps) (sg0 n) =
      halfProj (A := A) (-eps) (sg0 n) * halfProj (A := A) c (sg2 n) :=
    (halfProj_sg02_comm hA n (-eps) c).symm
  have h01 : halfProj (A := A) b (sg1 n) * halfProj (A := A) (-eps) (sg0 n) =
      halfProj (A := A) (-eps) (sg0 n) * halfProj (A := A) b (sg1 n) :=
    (halfProj_sg01_comm hA n (-eps) b).symm
  have horth : halfProj (A := A) eps (sg0 n) * halfProj (A := A) (-eps) (sg0 n) = 0 :=
    halfProj_orth (sg0 n) eps (sg0_mul_self n) heps
  have hstart : Edel (A := A) eps b c n * Edel (A := A) (-eps) b' c' n =
      halfProj eps (sg0 n) * halfProj b (sg1 n) * halfProj c (sg2 n) *
        halfProj (-eps) (sg0 n) * halfProj b' (sg1 n) * halfProj c' (sg2 n) := by
    rw [Edel, Edel]
    noncomm_ring
  rw [hstart]
  rw [show halfProj eps (sg0 n) * halfProj b (sg1 n) * halfProj c (sg2 n) *
        halfProj (-eps) (sg0 n) * halfProj b' (sg1 n) * halfProj c' (sg2 n) =
      (halfProj eps (sg0 n) * halfProj b (sg1 n) *
        (halfProj c (sg2 n) * halfProj (-eps) (sg0 n))) * halfProj b' (sg1 n) *
        halfProj c' (sg2 n) from by noncomm_ring,
    h02,
    show (halfProj eps (sg0 n) * halfProj b (sg1 n) *
        (halfProj (-eps) (sg0 n) * halfProj c (sg2 n))) * halfProj b' (sg1 n) *
        halfProj c' (sg2 n) =
      (halfProj eps (sg0 n) * (halfProj b (sg1 n) * halfProj (-eps) (sg0 n)) *
        halfProj c (sg2 n)) * halfProj b' (sg1 n) * halfProj c' (sg2 n) from by noncomm_ring,
    h01,
    show (halfProj eps (sg0 n) * (halfProj (-eps) (sg0 n) * halfProj b (sg1 n)) *
        halfProj c (sg2 n)) * halfProj b' (sg1 n) * halfProj c' (sg2 n) =
      ((halfProj eps (sg0 n) * halfProj (-eps) (sg0 n)) * halfProj b (sg1 n) *
        halfProj c (sg2 n)) * halfProj b' (sg1 n) * halfProj c' (sg2 n) from by noncomm_ring]
  rw [horth]
  simp only [zero_mul]

/-- The `(a,ε,c)` and `(a',-ε,c')` joint projectors are orthogonal. -/
theorem Edel_mul_Edel_sg1 (hA : ∀ x y : A, x * y = y * x) (n : ℕ) (eps a c a' c' : ℂ)
    (heps : eps ^ 2 = 1) :
    Edel (A := A) a eps c n * Edel (A := A) a' (-eps) c' n = 0 := by
  have h20 : halfProj (A := A) c (sg2 n) * halfProj (A := A) a' (sg0 n) =
      halfProj (A := A) a' (sg0 n) * halfProj (A := A) c (sg2 n) :=
    (halfProj_sg02_comm hA n a' c).symm
  have h10 : halfProj (A := A) eps (sg1 n) * halfProj (A := A) a' (sg0 n) =
      halfProj (A := A) a' (sg0 n) * halfProj (A := A) eps (sg1 n) :=
    (halfProj_sg01_comm hA n a' eps).symm
  have h21 : halfProj (A := A) c (sg2 n) * halfProj (A := A) (-eps) (sg1 n) =
      halfProj (A := A) (-eps) (sg1 n) * halfProj (A := A) c (sg2 n) :=
    (halfProj_sg12_comm hA n (-eps) c).symm
  have horth : halfProj (A := A) eps (sg1 n) * halfProj (A := A) (-eps) (sg1 n) = 0 :=
    halfProj_orth (sg1 n) eps (sg1_mul_self n) heps
  have hstart : Edel (A := A) a eps c n * Edel (A := A) a' (-eps) c' n =
      halfProj a (sg0 n) * halfProj eps (sg1 n) * halfProj c (sg2 n) *
        halfProj a' (sg0 n) * halfProj (-eps) (sg1 n) * halfProj c' (sg2 n) := by
    rw [Edel, Edel]
    noncomm_ring
  rw [hstart]
  rw [show halfProj a (sg0 n) * halfProj eps (sg1 n) * halfProj c (sg2 n) *
        halfProj a' (sg0 n) * halfProj (-eps) (sg1 n) * halfProj c' (sg2 n) =
      (halfProj a (sg0 n) * halfProj eps (sg1 n) *
        (halfProj c (sg2 n) * halfProj a' (sg0 n))) * halfProj (-eps) (sg1 n) *
        halfProj c' (sg2 n) from by noncomm_ring,
    h20,
    show (halfProj a (sg0 n) * halfProj eps (sg1 n) *
        (halfProj a' (sg0 n) * halfProj c (sg2 n))) * halfProj (-eps) (sg1 n) *
        halfProj c' (sg2 n) =
      (halfProj a (sg0 n) * (halfProj eps (sg1 n) * halfProj a' (sg0 n)) *
        halfProj c (sg2 n)) * halfProj (-eps) (sg1 n) * halfProj c' (sg2 n) from by
        noncomm_ring,
    h10,
    show (halfProj a (sg0 n) * (halfProj a' (sg0 n) * halfProj eps (sg1 n)) *
        halfProj c (sg2 n)) * halfProj (-eps) (sg1 n) * halfProj c' (sg2 n) =
      ((halfProj a (sg0 n) * halfProj a' (sg0 n)) * halfProj eps (sg1 n) *
        halfProj c (sg2 n)) * halfProj (-eps) (sg1 n) * halfProj c' (sg2 n) from by
        noncomm_ring,
    show ((halfProj a (sg0 n) * halfProj a' (sg0 n)) * halfProj eps (sg1 n) *
        halfProj c (sg2 n)) * halfProj (-eps) (sg1 n) * halfProj c' (sg2 n) =
      (halfProj a (sg0 n) * halfProj a' (sg0 n)) * halfProj eps (sg1 n) *
        (halfProj c (sg2 n) * halfProj (-eps) (sg1 n)) * halfProj c' (sg2 n) from by
        noncomm_ring,
    h21,
    show (halfProj a (sg0 n) * halfProj a' (sg0 n)) * halfProj eps (sg1 n) *
        (halfProj (-eps) (sg1 n) * halfProj c (sg2 n)) * halfProj c' (sg2 n) =
      ((halfProj a (sg0 n) * halfProj a' (sg0 n)) *
        (halfProj eps (sg1 n) * halfProj (-eps) (sg1 n)) * halfProj c (sg2 n)) *
        halfProj c' (sg2 n) from by noncomm_ring]
  rw [horth]
  simp only [mul_zero, zero_mul]

/-! ## 5.  The orbit sum of `Edel ε (-ε) (-ε)` -/

theorem orbSum_three {ι : Type} [Fintype ι] [DecidableEq ι] (g F : Matrix ι ι A)
    (hg : g ^ 3 = 1) :
    orbSum g F 3 = F + g * F * g ^ 2 + g ^ 2 * F * g := by
  simp only [orbSum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_mul,
    pow_one, hg, mul_one, Nat.reduceSub]

theorem cB_permMatrix_pow3 (n : ℕ) : ((cB n).permMatrix A) ^ 3 = 1 :=
  permMatrix_cube (cB n) (cB_cube n)

/-- **The orbit sum of the `(ε,-ε,-ε)` projector is `Deps ε`.** -/
theorem orbSum_Edel_eq_Deps (hA : ∀ x y : A, x * y = y * x) (n : ℕ) (eps : ℂ)
    (heps : eps ^ 2 = 1) :
    orbSum ((cB n).permMatrix A) (Edel (A := A) eps (-eps) (-eps) n) 3 = Deps (A := A) eps n := by
  have hg : ((cB n).permMatrix A) ^ 3 = 1 := cB_permMatrix_pow3 n
  have h1 : (cB n).permMatrix A * Edel (A := A) eps (-eps) (-eps) n * (cB n).permMatrix A ^ 2 =
      Edel (A := A) (-eps) (-eps) eps n := by
    rw [pow_two, cB_mul_self_eq_inv, cB_conj_Edel hA]
  have h2 : (cB n).permMatrix A ^ 2 * Edel (A := A) eps (-eps) (-eps) n * (cB n).permMatrix A =
      Edel (A := A) (-eps) eps (-eps) n := by
    have hexp : (cB n).permMatrix A ^ 2 * Edel (A := A) eps (-eps) (-eps) n *
          (cB n).permMatrix A
        = (cB n).permMatrix A *
            ((cB n).permMatrix A * Edel (A := A) eps (-eps) (-eps) n *
              ((cB n)⁻¹).permMatrix A) * ((cB n)⁻¹).permMatrix A := by
      rw [pow_two]
      rw [show (cB n).permMatrix A *
            ((cB n).permMatrix A * Edel eps (-eps) (-eps) n * ((cB n)⁻¹).permMatrix A) *
            ((cB n)⁻¹).permMatrix A =
          ((cB n).permMatrix A * (cB n).permMatrix A) * Edel eps (-eps) (-eps) n *
            (((cB n)⁻¹).permMatrix A * ((cB n)⁻¹).permMatrix A) from by noncomm_ring,
        cB_inv_mul_self]
    rw [hexp, cB_conj_Edel hA, cB_conj_Edel hA]
  rw [orbSum_three _ _ hg, Deps_eq_sum (A := A) n eps heps, h1, h2]
  abel

/-! ## 6.  The orbit step -/

/-- The `Edel ε (-ε) (-ε)` projector is idempotent. -/
theorem Edel_idem (hA : ∀ x y : A, x * y = y * x) (n : ℕ) (eps : ℂ) (heps : eps ^ 2 = 1) :
    Edel (A := A) eps (-eps) (-eps) n * Edel (A := A) eps (-eps) (-eps) n =
      Edel (A := A) eps (-eps) (-eps) n := by
  have hne : (-eps) ^ 2 = 1 := by rw [neg_sq, heps]
  have i0 : halfProj (A := A) eps (sg0 n) * halfProj (A := A) eps (sg0 n) =
      halfProj (A := A) eps (sg0 n) :=
    halfProj_idem (sg0 n) eps (sg0_mul_self n) heps
  have i1 : halfProj (A := A) (-eps) (sg1 n) * halfProj (A := A) (-eps) (sg1 n) =
      halfProj (A := A) (-eps) (sg1 n) :=
    halfProj_idem (sg1 n) (-eps) (sg1_mul_self n) hne
  have i2 : halfProj (A := A) (-eps) (sg2 n) * halfProj (A := A) (-eps) (sg2 n) =
      halfProj (A := A) (-eps) (sg2 n) :=
    halfProj_idem (sg2 n) (-eps) (sg2_mul_self n) hne
  have c01 : halfProj (A := A) eps (sg0 n) * halfProj (A := A) (-eps) (sg1 n) =
      halfProj (A := A) (-eps) (sg1 n) * halfProj (A := A) eps (sg0 n) :=
    halfProj_sg01_comm hA n eps (-eps)
  have c02 : halfProj (A := A) (-eps) (sg2 n) * halfProj (A := A) eps (sg0 n) =
      halfProj (A := A) eps (sg0 n) * halfProj (A := A) (-eps) (sg2 n) :=
    (halfProj_sg02_comm hA n eps (-eps)).symm
  have c12 : halfProj (A := A) (-eps) (sg2 n) * halfProj (A := A) (-eps) (sg1 n) =
      halfProj (A := A) (-eps) (sg1 n) * halfProj (A := A) (-eps) (sg2 n) :=
    (halfProj_sg12_comm hA n (-eps) (-eps)).symm
  rw [Edel]
  exact DepsAux.idem_mul_of_comm (DepsAux.idem_mul_of_comm i0 i1 c01) i2
    (comm_mul_of_comm (halfProj (A := A) (-eps) (sg2 n)) (halfProj (A := A) eps (sg0 n))
      (halfProj (A := A) (-eps) (sg1 n)) c02 c12).symm

/-- **The orbit step.**  For an idempotent `P` commuting with `cB.permMatrix` and with
`Edel ε (-ε) (-ε)`, the class of `P · Deps ε · Q_λ` is that of `P · Edel ε (-ε) (-ε)`. -/
theorem Deps_orbit (A : Type) [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    {n : ℕ} (eps lam : ℂ) (heps : eps ^ 2 = 1) (hlam : lam ^ 3 = 1)
    (P : Matrix (IB n) (IB n) A) (hP : P * P = P)
    (hPg : P * (cB n).permMatrix A = (cB n).permMatrix A * P)
    (hPF : P * Edel eps (-eps) (-eps) n = Edel eps (-eps) (-eps) n * P) :
    clsM (IB n) (P * Deps eps n * cycProj (cB n) lam) =
      clsM (IB n) (P * Edel eps (-eps) (-eps) n) := by
  have hF : Edel eps (-eps) (-eps) n * Edel eps (-eps) (-eps) n = Edel eps (-eps) (-eps) n :=
    Edel_idem hA n eps heps
  have hg : ((cB n).permMatrix A) ^ 3 = 1 := cB_permMatrix_pow3 n
  have hspec : orbitSpec lam ((cB n).permMatrix A) 3 = cycProj (cB n) lam :=
    (cycProj_eq_orbitSpec (cB n) lam).symm
  have hE1 : (cB n).permMatrix A * Edel (A := A) eps (-eps) (-eps) n * (cB n).permMatrix A ^ 2 =
      Edel (A := A) (-eps) (-eps) eps n := by
    rw [pow_two, cB_mul_self_eq_inv, cB_conj_Edel hA]
  have hE2 : (cB n).permMatrix A ^ 2 * Edel (A := A) eps (-eps) (-eps) n *
      (cB n).permMatrix A = Edel (A := A) (-eps) eps (-eps) n := by
    have hexp : (cB n).permMatrix A ^ 2 * Edel (A := A) eps (-eps) (-eps) n *
          (cB n).permMatrix A
        = (cB n).permMatrix A *
            ((cB n).permMatrix A * Edel (A := A) eps (-eps) (-eps) n *
              ((cB n)⁻¹).permMatrix A) * ((cB n)⁻¹).permMatrix A := by
      rw [pow_two]
      rw [show (cB n).permMatrix A *
            ((cB n).permMatrix A * Edel eps (-eps) (-eps) n * ((cB n)⁻¹).permMatrix A) *
            ((cB n)⁻¹).permMatrix A =
          ((cB n).permMatrix A * (cB n).permMatrix A) * Edel eps (-eps) (-eps) n *
            (((cB n)⁻¹).permMatrix A * ((cB n)⁻¹).permMatrix A) from by noncomm_ring,
        cB_inv_mul_self]
    rw [hexp, cB_conj_Edel hA, cB_conj_Edel hA]
  have hL0 : (cB n).permMatrix A ^ 0 * Edel (A := A) eps (-eps) (-eps) n *
        (cB n).permMatrix A ^ (3 - 0) = Edel (A := A) eps (-eps) (-eps) n := by
    rw [pow_zero, show (3 : ℕ) - 0 = 3 from rfl, hg, one_mul, mul_one]
  have hL1 : (cB n).permMatrix A ^ 1 * Edel (A := A) eps (-eps) (-eps) n *
        (cB n).permMatrix A ^ (3 - 1) = Edel (A := A) (-eps) (-eps) eps n := by
    rw [pow_one, show (3 : ℕ) - 1 = 2 from rfl, hE1]
  have hL2 : (cB n).permMatrix A ^ 2 * Edel (A := A) eps (-eps) (-eps) n *
        (cB n).permMatrix A ^ (3 - 2) = Edel (A := A) (-eps) eps (-eps) n := by
    rw [show (3 : ℕ) - 2 = 1 from rfl, pow_one, hE2]
  -- pairwise orthogonality of the three conjugates
  have hx1 : Edel (A := A) eps (-eps) (-eps) n * Edel (A := A) (-eps) (-eps) eps n = 0 :=
    Edel_mul_Edel_sg0 hA n eps (-eps) (-eps) (-eps) eps heps
  have hx2 : Edel (A := A) eps (-eps) (-eps) n * Edel (A := A) (-eps) eps (-eps) n = 0 :=
    Edel_mul_Edel_sg0 hA n eps (-eps) (-eps) eps (-eps) heps
  have hx3 : Edel (A := A) (-eps) (-eps) eps n * Edel (A := A) eps (-eps) (-eps) n = 0 := by
    have hne : (-eps) ^ 2 = 1 := by rw [neg_sq, heps]
    simpa only [neg_neg] using Edel_mul_Edel_sg0 hA n (-eps) (-eps) eps (-eps) (-eps) hne
  have hx4 : Edel (A := A) (-eps) (-eps) eps n * Edel (A := A) (-eps) eps (-eps) n = 0 := by
    have hne : (-eps) ^ 2 = 1 := by rw [neg_sq, heps]
    simpa only [neg_neg] using Edel_mul_Edel_sg1 hA n (-eps) (-eps) eps (-eps) (-eps) hne
  have hx5 : Edel (A := A) (-eps) eps (-eps) n * Edel (A := A) eps (-eps) (-eps) n = 0 := by
    have hne : (-eps) ^ 2 = 1 := by rw [neg_sq, heps]
    simpa only [neg_neg] using Edel_mul_Edel_sg0 hA n (-eps) eps (-eps) (-eps) (-eps) hne
  have hx6 : Edel (A := A) (-eps) eps (-eps) n * Edel (A := A) (-eps) (-eps) eps n = 0 :=
    Edel_mul_Edel_sg1 hA n eps (-eps) (-eps) (-eps) eps heps
  have horth : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j →
      ((cB n).permMatrix A ^ i * Edel (A := A) eps (-eps) (-eps) n *
          (cB n).permMatrix A ^ (3 - i)) *
        ((cB n).permMatrix A ^ j * Edel (A := A) eps (-eps) (-eps) n *
          (cB n).permMatrix A ^ (3 - j)) = 0 := by
    intro i j hi hj hij
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl
    · exact absurd rfl hij
    · rw [hL0, hL1]; exact hx1
    · rw [hL0, hL2]; exact hx2
    · rw [hL1, hL0]; exact hx3
    · exact absurd rfl hij
    · rw [hL1, hL2]; exact hx4
    · rw [hL2, hL0]; exact hx5
    · rw [hL2, hL1]; exact hx6
    · exact absurd rfl hij
  have key := clsM_orbit (A := A) (ι := IB n) 3 (by norm_num) P (Edel eps (-eps) (-eps) n)
    ((cB n).permMatrix A) hP hF hg hPg hPF horth lam hlam
  rw [orbSum_Edel_eq_Deps hA n eps heps, hspec] at key
  rw [← mul_assoc] at key
  exact key

end StepPsi3Psi2Aux

/-! ## 7.  The assembly -/

theorem step_psi3psi2 (A : Type) [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (p : Work.KT.Mat A) (hp : p.IsIdem) (eps lam : ℂ) (heps : eps ^ 2 = 1) (hlam : lam ^ 3 = 1) :
    Work.KT.cls (Work.KT.cubePart lam (Work.KT.sq2Part eps p)) =
      Work.KT.PsiC.Tcls (A := A) p (lam ^ 2 * eps) - Work.KT.PsiC.Dcls (A := A) p eps := by
  have hmu6 : (lam ^ 2 * eps) ^ 6 = 1 := by
    rw [mul_pow,
      show (lam ^ 2) ^ 6 = 1 by
        rw [← pow_mul, show (2 : ℕ) * 6 = 3 * 4 from rfl, pow_mul, hlam, one_pow],
      show eps ^ 6 = 1 by rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, heps, one_pow],
      mul_one]
  have hsq : (lam ^ 2 * eps) ^ 2 = lam := by
    rw [mul_pow, heps, mul_one,
      show (lam ^ 2) ^ 2 = lam by
        rw [← pow_mul, show (2 : ℕ) * 2 = 3 + 1 from rfl, pow_add, hlam, one_mul, pow_one]]
  have hcu : (lam ^ 2 * eps) ^ 3 = eps := by
    rw [mul_pow,
      show (lam ^ 2) ^ 3 = 1 by
        rw [← pow_mul, show (2 : ℕ) * 3 = 3 * 2 from rfl, pow_mul, hlam, one_pow],
      show eps ^ 3 = eps by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, heps, pow_one, one_mul],
      one_mul]
  have hgd := gamB_decomp A p.1 (lam ^ 2 * eps) hmu6
  rw [hsq, hcu] at hgd
  have hbridge := bridge_cube_sq2 A hA p hp eps lam heps hlam
  -- frame commutations
  have hPB : PB p * PB p = PB p := PB_idem p hA hp
  have hPcB : PB p * (cB p.1).permMatrix A = (cB p.1).permMatrix A * PB p :=
    (PB_comm_frame A hA p hp).2.1
  have hPE : PB p * Eeps (A := A) eps p.1 = Eeps (A := A) eps p.1 * PB p :=
    (PB_comm_frame A hA p hp).2.2.2 eps eps eps
  have hPsB : PB p * (sB p.1).permMatrix A = (sB p.1).permMatrix A * PB p :=
    (PB_comm_frame A hA p hp).1
  have hPF : PB p * Edel (A := A) eps (-eps) (-eps) p.1 = Edel (A := A) eps (-eps) (-eps) p.1 * PB p :=
    (PB_comm_frame A hA p hp).2.2.2 eps (-eps) (-eps)
  have hPhsB : PB p * halfProj (A := A) eps (sB p.1) = halfProj (A := A) eps (sB p.1) * PB p :=
    halfProj_comm_of hA (sB p.1) eps (PB p) hPsB
  have hPD : PB p * Deps (A := A) eps p.1 = Deps (A := A) eps p.1 * PB p := by
    rw [show Deps (A := A) eps p.1 = halfProj (A := A) eps (sB p.1) - Eeps (A := A) eps p.1 from rfl, mul_sub, sub_mul,
      hPhsB, hPE]
  have hQidem : cycProj (A := A) (cB p.1) lam * cycProj (A := A) (cB p.1) lam =
      cycProj (A := A) (cB p.1) lam :=
    cycProj_idem (cB p.1) lam (cB_cube p.1) hlam
  have hPQ : PB p * cycProj (A := A) (cB p.1) lam = cycProj (A := A) (cB p.1) lam * PB p :=
    cycProj_comm_of hA (cB p.1) lam (PB p) hPcB
  have hQE : cycProj (A := A) (cB p.1) lam * Eeps (A := A) eps p.1 = Eeps (A := A) eps p.1 * cycProj (A := A) (cB p.1) lam :=
    (cycProj_comm_of hA (cB p.1) lam (Eeps (A := A) eps p.1) (StepPsi3Psi2Aux.cB_comm_Eeps hA p.1 eps).symm).symm
  have hQsB : cycProj (A := A) (cB p.1) lam * halfProj (A := A) eps (sB p.1) =
      halfProj (A := A) eps (sB p.1) * cycProj (A := A) (cB p.1) lam :=
    (cycProj_comm_of hA (cB p.1) lam (halfProj (A := A) eps (sB p.1))
      (halfProj_comm_of hA (sB p.1) eps ((cB p.1).permMatrix A)
        (StepPsi3Psi2Aux.cB_permMatrix_comm_sB p.1)).symm).symm
  have hQD : cycProj (A := A) (cB p.1) lam * Deps (A := A) eps p.1 = Deps (A := A) eps p.1 * cycProj (A := A) (cB p.1) lam := by
    rw [show Deps (A := A) eps p.1 = halfProj (A := A) eps (sB p.1) - Eeps (A := A) eps p.1 from rfl, mul_sub, sub_mul,
      hQsB, hQE]
  -- the projector identities
  have hEidem : Eeps (A := A) eps p.1 * Eeps (A := A) eps p.1 = Eeps (A := A) eps p.1 := (Deps_idem A p.1 eps heps).2.1
  have hDidem : Deps (A := A) eps p.1 * Deps (A := A) eps p.1 = Deps (A := A) eps p.1 := (Deps_idem A p.1 eps heps).1
  have hED : Eeps (A := A) eps p.1 * Deps (A := A) eps p.1 = 0 := (Deps_idem A p.1 eps heps).2.2.2.1
  have hDE : Deps (A := A) eps p.1 * Eeps (A := A) eps p.1 = 0 := (Deps_idem A p.1 eps heps).2.2.1
  have hHsum : halfProj (A := A) eps (sB p.1) = Eeps (A := A) eps p.1 + Deps (A := A) eps p.1 :=
    (Deps_idem A p.1 eps heps).2.2.2.2
  have hPQidem : (PB p * cycProj (A := A) (cB p.1) lam) * (PB p * cycProj (A := A) (cB p.1) lam) =
      PB p * cycProj (A := A) (cB p.1) lam := DepsAux.idem_mul_of_comm hPB hQidem hPQ
  have hEA : Eeps (A := A) eps p.1 * (PB p * cycProj (A := A) (cB p.1) lam) =
      (PB p * cycProj (A := A) (cB p.1) lam) * Eeps (A := A) eps p.1 :=
    comm_mul_of_comm (Eeps (A := A) eps p.1) (PB p) (cycProj (A := A) (cB p.1) lam) hPE.symm hQE.symm
  have hDA : Deps (A := A) eps p.1 * (PB p * cycProj (A := A) (cB p.1) lam) =
      (PB p * cycProj (A := A) (cB p.1) lam) * Deps (A := A) eps p.1 :=
    comm_mul_of_comm (Deps (A := A) eps p.1) (PB p) (cycProj (A := A) (cB p.1) lam) hPD.symm hQD.symm
  have hidem1 : (PB p * cycProj (A := A) (cB p.1) lam * Eeps (A := A) eps p.1) *
      (PB p * cycProj (A := A) (cB p.1) lam * Eeps (A := A) eps p.1) =
      PB p * cycProj (A := A) (cB p.1) lam * Eeps (A := A) eps p.1 :=
    IdemMul3 (PB p) (cycProj (A := A) (cB p.1) lam) (Eeps (A := A) eps p.1) hPB hQidem hEidem hPQ hPE hQE
  have hidem2 : (PB p * cycProj (A := A) (cB p.1) lam * Deps (A := A) eps p.1) *
      (PB p * cycProj (A := A) (cB p.1) lam * Deps (A := A) eps p.1) =
      PB p * cycProj (A := A) (cB p.1) lam * Deps (A := A) eps p.1 :=
    IdemMul3 (PB p) (cycProj (A := A) (cB p.1) lam) (Deps (A := A) eps p.1) hPB hQidem hDidem hPQ hPD hQD
  have horth12 : (PB p * cycProj (A := A) (cB p.1) lam * Eeps (A := A) eps p.1) *
      (PB p * cycProj (A := A) (cB p.1) lam * Deps (A := A) eps p.1) = 0 := by
    rw [show (PB p * cycProj (A := A) (cB p.1) lam * Eeps (A := A) eps p.1) *
        (PB p * cycProj (A := A) (cB p.1) lam * Deps (A := A) eps p.1) =
        (PB p * cycProj (A := A) (cB p.1) lam) *
          (Eeps (A := A) eps p.1 * (PB p * cycProj (A := A) (cB p.1) lam)) * Deps (A := A) eps p.1 from by noncomm_ring,
      hEA,
      show (PB p * cycProj (A := A) (cB p.1) lam) * ((PB p * cycProj (A := A) (cB p.1) lam) * Eeps (A := A) eps p.1) *
          Deps (A := A) eps p.1 =
        ((PB p * cycProj (A := A) (cB p.1) lam) * (PB p * cycProj (A := A) (cB p.1) lam)) *
          (Eeps (A := A) eps p.1 * Deps (A := A) eps p.1) from by noncomm_ring,
      hPQidem, hED, mul_zero]
  have horth21 : (PB p * cycProj (A := A) (cB p.1) lam * Deps (A := A) eps p.1) *
      (PB p * cycProj (A := A) (cB p.1) lam * Eeps (A := A) eps p.1) = 0 := by
    rw [show (PB p * cycProj (A := A) (cB p.1) lam * Deps (A := A) eps p.1) *
        (PB p * cycProj (A := A) (cB p.1) lam * Eeps (A := A) eps p.1) =
        (PB p * cycProj (A := A) (cB p.1) lam) *
          (Deps (A := A) eps p.1 * (PB p * cycProj (A := A) (cB p.1) lam)) * Eeps (A := A) eps p.1 from by noncomm_ring,
      hDA,
      show (PB p * cycProj (A := A) (cB p.1) lam) * ((PB p * cycProj (A := A) (cB p.1) lam) * Deps (A := A) eps p.1) *
          Eeps (A := A) eps p.1 =
        ((PB p * cycProj (A := A) (cB p.1) lam) * (PB p * cycProj (A := A) (cB p.1) lam)) *
          (Deps (A := A) eps p.1 * Eeps (A := A) eps p.1) from by noncomm_ring,
      hPQidem, hDE, mul_zero]
  -- the three class computations
  have hT : Tcls (A := A) p (lam ^ 2 * eps) =
      clsM (IB p.1) (PB p * (cycProj (A := A) (cB p.1) lam * halfProj (A := A) eps (sB p.1))) := by
    rw [Tcls, hgd]
  have hsplit : clsM (IB p.1) (PB p * cycProj (A := A) (cB p.1) lam * halfProj (A := A) eps (sB p.1)) =
      clsM (IB p.1) (PB p * cycProj (A := A) (cB p.1) lam * Eeps (A := A) eps p.1) +
      clsM (IB p.1) (PB p * cycProj (A := A) (cB p.1) lam * Deps (A := A) eps p.1) := by
    rw [hHsum, mul_add]
    exact clsM_idem_add _ _ hidem1 hidem2 horth12 horth21
  have hcommQE : clsM (IB p.1) (PB p * cycProj (A := A) (cB p.1) lam * Eeps (A := A) eps p.1) =
      clsM (IB p.1) (PB p * Eeps (A := A) eps p.1 * cycProj (A := A) (cB p.1) lam) := by
    rw [show PB p * cycProj (A := A) (cB p.1) lam * Eeps (A := A) eps p.1 =
        PB p * Eeps (A := A) eps p.1 * cycProj (A := A) (cB p.1) lam from by rw [mul_assoc, hQE, ← mul_assoc]]
  have hDcls : clsM (IB p.1) (PB p * cycProj (A := A) (cB p.1) lam * Deps (A := A) eps p.1) =
      Dcls (A := A) p eps := by
    rw [Dcls,
      show PB p * cycProj (A := A) (cB p.1) lam * Deps (A := A) eps p.1 =
        PB p * Deps (A := A) eps p.1 * cycProj (A := A) (cB p.1) lam from by rw [mul_assoc, hQD, ← mul_assoc]]
    exact StepPsi3Psi2Aux.Deps_orbit A hA eps lam heps hlam (PB p) hPB hPcB hPF
  rw [hbridge, hT, ← mul_assoc, hsplit, hcommQE, hDcls, add_sub_assoc, sub_self, add_zero]

end

end Work.PsiC
