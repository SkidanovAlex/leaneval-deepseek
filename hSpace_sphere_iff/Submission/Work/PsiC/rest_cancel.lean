import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.PsiC.BFrame
import Submission.Work.PsiC.PB_comm_frame
import Submission.Work.PsiC.rest_core

namespace Work.PsiC

open Matrix
open Work.KT
open Work.KT.PsiC
open Work.KT.Psi

noncomputable section

section Helpers

variable {A : Type} [Ring A] [Algebra ℂ A]

/-! ## Frame-B permutation facts -/

theorem uB_cube (n : ℕ) : uB n * uB n * uB n = 1 := by
  apply Equiv.ext; intro x; rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨e,f⟩⟩; rfl

theorem vB_cube (n : ℕ) : vB n * vB n * vB n = 1 := by
  apply Equiv.ext; intro x; rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨e,f⟩⟩; rfl

theorem uB_comm_vB (n : ℕ) : uB n * vB n = vB n * uB n := by
  apply Equiv.ext; intro x; rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨e,f⟩⟩; rfl

theorem sB_conj_uB (n : ℕ) : sB n * uB n * sB n = vB n := by
  apply Equiv.ext; intro x; rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨e,f⟩⟩; rfl

theorem sB_conj_vB (n : ℕ) : sB n * vB n * sB n = uB n := by
  apply Equiv.ext; intro x; rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨e,f⟩⟩; rfl

/-! ## `PB` commutes with the frame-B position permutations -/

private theorem PB_comm_uB (p : Mat A) (hA : ∀ x y : A, x * y = y * x) :
    PB p * (uB p.1).permMatrix A = (uB p.1).permMatrix A * PB p := by
  have h' : Matrix.reindex (Phi p.1) (Phi p.1) ((c1A p.1).permMatrix A) =
      (uB p.1).permMatrix A := reindex_permMatrix (Phi p.1) (c1A p.1)
  have hPA : Matrix.reindex (Phi p.1) (Phi p.1) (PA p) = PB p := reindex_Phi_PA p hA
  rw [← h', ← hPA, ← reindex_mul', ← reindex_mul', PA_comm_c1A p hA]

private theorem PB_comm_vB (p : Mat A) (hA : ∀ x y : A, x * y = y * x) :
    PB p * (vB p.1).permMatrix A = (vB p.1).permMatrix A * PB p := by
  have h' : Matrix.reindex (Phi p.1) (Phi p.1) ((c2A p.1).permMatrix A) =
      (vB p.1).permMatrix A := reindex_permMatrix (Phi p.1) (c2A p.1)
  have hPA : Matrix.reindex (Phi p.1) (Phi p.1) (PA p) = PB p := reindex_Phi_PA p hA
  rw [← h', ← hPA, ← reindex_mul', ← reindex_mul', PA_comm_c2A p hA]

/-! ## Cross-commutation of the two cyclic projectors -/

theorem permMatrix_uB_comm_vB (n : ℕ) :
    ((uB n).permMatrix A : Matrix (IB n) (IB n) A) * (vB n).permMatrix A =
      (vB n).permMatrix A * (uB n).permMatrix A := by
  rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul, uB_comm_vB]

theorem cycProj_uB_mul_vB (hA : ∀ x y : A, x * y = y * x) (n : ℕ) (a b : ℂ) :
    cycProj (A := A) (uB n) a * cycProj (A := A) (vB n) b =
      cycProj (A := A) (vB n) b * cycProj (A := A) (uB n) a := by
  have h1 : cycProj (A := A) (uB n) a * ((vB n).permMatrix A : Matrix (IB n) (IB n) A) =
      (vB n).permMatrix A * cycProj (A := A) (uB n) a :=
    (cycProj_comm_of hA (uB n) a ((vB n).permMatrix A) (permMatrix_uB_comm_vB n).symm).symm
  exact cycProj_comm_of hA (vB n) b (cycProj (A := A) (uB n) a) h1

/-! ## Root-of-unity arithmetic -/

theorem omega_ne_one' : omega ≠ (1 : ℂ) :=
  Work.KT.Psi.K3.omega_primRoot.ne_one (by norm_num)

theorem omega_ne_omega_sq' : omega ≠ omega ^ 2 := by
  intro h
  have h' : omega = omega * omega := by rw [← pow_two]; exact h
  have h1 : omega * (1 - omega) = 0 := by rw [mul_sub, mul_one, ← h', sub_self]
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact omega_ne_zero h2
  · exact omega_ne_one' (sub_eq_zero.mp h2).symm

theorem cube_lam_omega (lam : ℂ) (hlam : lam ^ 3 = 1) : (lam * omega) ^ 3 = 1 := by
  rw [mul_pow, hlam, omega_pow_three, one_mul]

theorem cube_lam_omega_sq (lam : ℂ) (hlam : lam ^ 3 = 1) : (lam * omega ^ 2) ^ 3 = 1 := by
  rw [mul_pow, hlam, show (omega ^ 2) ^ 3 = 1 by
    rw [← pow_mul, show 2 * 3 = 3 * 2 from by norm_num, pow_mul, omega_pow_three, one_pow],
    mul_one]

theorem lam_omega_ne_lam_omega_sq (lam : ℂ) (hlam : lam ^ 3 = 1) :
    lam * omega ≠ lam * omega ^ 2 := by
  intro h
  have hlz : lam ≠ 0 := by intro h0; rw [h0] at hlam; norm_num at hlam
  exact omega_ne_omega_sq' (mul_left_cancel₀ hlz h)

/-! ## `halfProj` of `sB` as an `algebraMap` multiple -/

theorem algMap_half_mul (n : ℕ) (M : Matrix (IB n) (IB n) A) :
    algebraMap ℂ (Matrix (IB n) (IB n) A) (1/2) * M = (1/2 : ℂ) • M := by
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem halfProj_one_sB (n : ℕ) :
    halfProj (A := A) 1 (sB n) =
      algebraMap ℂ (Matrix (IB n) (IB n) A) (1/2) * (1 + (sB n).permMatrix A) := by
  rw [halfProj, smulA_eq_smulC, map_one, one_smul, algMap_half_mul]

theorem halfProj_neg_one_sB (n : ℕ) :
    halfProj (A := A) (-1) (sB n) =
      algebraMap ℂ (Matrix (IB n) (IB n) A) (1/2) * (1 - (sB n).permMatrix A) := by
  rw [halfProj, smulA_eq_smulC, map_neg, map_one, neg_smul, one_smul, sub_eq_add_neg,
    algMap_half_mul]

/-! ## Lifting a Murray–von Neumann pair by a commuting idempotent -/

theorem mvN_lift {ι : Type} [Fintype ι] [DecidableEq ι]
    (P R G u v : Matrix ι ι A) (hPP : P*P=P) (hPR : P*R=R*P) (hPG : P*G=G*P)
    (hPv : P*v=v*P) (hR : R*R=R) (hG : G*G=G)
    (hvu : v*u=R) (huv : u*v=G) :
    clsM ι (P*R) = clsM ι (P*G) := by
  refine clsM_eq_of_mvN ?_ ?_ (u*P) (P*v) ?_ ?_
  · calc (P*R)*(P*R) = (P*(R*P))*R := by noncomm_ring
      _ = (P*(P*R))*R := by rw [← hPR]
      _ = ((P*P)*R)*R := by noncomm_ring
      _ = (P*R)*R := by rw [hPP]
      _ = P*(R*R) := by noncomm_ring
      _ = P*R := by rw [hR]
  · calc (P*G)*(P*G) = (P*(G*P))*G := by noncomm_ring
      _ = (P*(P*G))*G := by rw [← hPG]
      _ = ((P*P)*G)*G := by noncomm_ring
      _ = (P*G)*G := by rw [hPP]
      _ = P*(G*G) := by noncomm_ring
      _ = P*G := by rw [hG]
  · calc (P*v)*(u*P) = P*(v*u)*P := by noncomm_ring
      _ = P*R*P := by rw [hvu]
      _ = P*(R*P) := by noncomm_ring
      _ = P*(P*R) := by rw [← hPR]
      _ = (P*P)*R := by noncomm_ring
      _ = P*R := by rw [hPP]
  · calc (u*P)*(P*v) = u*(P*P)*v := by noncomm_ring
      _ = u*P*v := by rw [hPP]
      _ = u*(P*v) := by noncomm_ring
      _ = u*(v*P) := by rw [hPv]
      _ = (u*v)*P := by noncomm_ring
      _ = G*P := by rw [huv]
      _ = P*G := by rw [← hPG]

end Helpers

theorem rest_cancel (A : Type) [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (p : Work.KT.Mat A) (hp : p.IsIdem) (lam : ℂ) (hlam : lam ^ 3 = 1) :
    Work.KT.Psi.clsM (Work.KT.PsiC.IB p.1) (Work.KT.PsiC.PB p *
        (Work.KT.PsiC.cycProj (Work.KT.PsiC.uB p.1) (lam * Work.KT.omega) * Work.KT.PsiC.cycProj (Work.KT.PsiC.vB p.1) (lam * Work.KT.omega ^ 2) +
         Work.KT.PsiC.cycProj (Work.KT.PsiC.uB p.1) (lam * Work.KT.omega ^ 2) * Work.KT.PsiC.cycProj (Work.KT.PsiC.vB p.1) (lam * Work.KT.omega)) *
        Work.KT.PsiC.halfProj 1 (Work.KT.PsiC.sB p.1)) =
      Work.KT.Psi.clsM (Work.KT.PsiC.IB p.1) (Work.KT.PsiC.PB p *
        (Work.KT.PsiC.cycProj (Work.KT.PsiC.uB p.1) (lam * Work.KT.omega) * Work.KT.PsiC.cycProj (Work.KT.PsiC.vB p.1) (lam * Work.KT.omega ^ 2) +
         Work.KT.PsiC.cycProj (Work.KT.PsiC.uB p.1) (lam * Work.KT.omega ^ 2) * Work.KT.PsiC.cycProj (Work.KT.PsiC.vB p.1) (lam * Work.KT.omega)) *
        Work.KT.PsiC.halfProj (-1) (Work.KT.PsiC.sB p.1)) := by
  set P : Matrix (IB p.1) (IB p.1) A := PB p with hP
  set Q1 : Matrix (IB p.1) (IB p.1) A := cycProj (uB p.1) (lam * omega) with hQ1
  set Q2 : Matrix (IB p.1) (IB p.1) A := cycProj (vB p.1) (lam * omega ^ 2) with hQ2
  set R1 : Matrix (IB p.1) (IB p.1) A := cycProj (uB p.1) (lam * omega ^ 2) with hR1
  set R2 : Matrix (IB p.1) (IB p.1) A := cycProj (vB p.1) (lam * omega) with hR2
  set Am : Matrix (IB p.1) (IB p.1) A := Q1 * Q2 with hAm
  set Bm : Matrix (IB p.1) (IB p.1) A := R1 * R2 with hBm
  set X : Matrix (IB p.1) (IB p.1) A := Am + Bm with hX
  set s : Matrix (IB p.1) (IB p.1) A := (sB p.1).permMatrix A with hs
  set h1 : Matrix (IB p.1) (IB p.1) A := halfProj 1 (sB p.1) with hh1
  set hm : Matrix (IB p.1) (IB p.1) A := halfProj (-1) (sB p.1) with hhm
  -- idempotency / orthogonality of the four projectors
  have hQ1idem : Q1 * Q1 = Q1 := by
    rw [hQ1]
    exact cycProj_idem (uB p.1) (lam * omega) (uB_cube p.1) (cube_lam_omega lam hlam)
  have hQ2idem : Q2 * Q2 = Q2 := by
    rw [hQ2]
    exact cycProj_idem (vB p.1) (lam * omega ^ 2) (vB_cube p.1) (cube_lam_omega_sq lam hlam)
  have hR1idem : R1 * R1 = R1 := by
    rw [hR1]
    exact cycProj_idem (uB p.1) (lam * omega ^ 2) (uB_cube p.1) (cube_lam_omega_sq lam hlam)
  have hR2idem : R2 * R2 = R2 := by
    rw [hR2]
    exact cycProj_idem (vB p.1) (lam * omega) (vB_cube p.1) (cube_lam_omega lam hlam)
  have hQ1Q2 : Q1 * Q2 = Q2 * Q1 := by
    rw [hQ1, hQ2]
    exact cycProj_uB_mul_vB hA p.1 (lam * omega) (lam * omega ^ 2)
  have hR1R2 : R1 * R2 = R2 * R1 := by
    rw [hR1, hR2]
    exact cycProj_uB_mul_vB hA p.1 (lam * omega ^ 2) (lam * omega)
  have hQ2R1 : Q2 * R1 = R1 * Q2 := by
    rw [hQ2, hR1]
    exact (cycProj_uB_mul_vB hA p.1 (lam * omega ^ 2) (lam * omega ^ 2)).symm
  have hR2Q1 : R2 * Q1 = Q1 * R2 := by
    rw [hR2, hQ1]
    exact (cycProj_uB_mul_vB hA p.1 (lam * omega) (lam * omega)).symm
  have hne := lam_omega_ne_lam_omega_sq lam hlam
  have hQ1R1 : Q1 * R1 = 0 := by
    rw [hQ1, hR1]
    exact cycProj_orth (uB p.1) (lam * omega) (lam * omega ^ 2) (uB_cube p.1)
      (cube_lam_omega lam hlam) (cube_lam_omega_sq lam hlam) hne
  have hQ2R2 : Q2 * R2 = 0 := by
    rw [hQ2, hR2]
    exact cycProj_orth (vB p.1) (lam * omega ^ 2) (lam * omega) (vB_cube p.1)
      (cube_lam_omega_sq lam hlam) (cube_lam_omega lam hlam) hne.symm
  have hR1Q1 : R1 * Q1 = 0 := by
    rw [hR1, hQ1]
    exact cycProj_orth (uB p.1) (lam * omega ^ 2) (lam * omega) (uB_cube p.1)
      (cube_lam_omega_sq lam hlam) (cube_lam_omega lam hlam) hne.symm
  have hR2Q2 : R2 * Q2 = 0 := by
    rw [hR2, hQ2]
    exact cycProj_orth (vB p.1) (lam * omega) (lam * omega ^ 2) (vB_cube p.1)
      (cube_lam_omega lam hlam) (cube_lam_omega_sq lam hlam) hne
  have hAm_idem : Am * Am = Am := by
    rw [hAm]
    calc (Q1*Q2)*(Q1*Q2) = (Q1*(Q2*Q1))*Q2 := by noncomm_ring
      _ = (Q1*(Q1*Q2))*Q2 := by rw [← hQ1Q2]
      _ = ((Q1*Q1)*(Q2*Q2)) := by noncomm_ring
      _ = Q1*Q2 := by rw [hQ1idem, hQ2idem]
  have hBm_idem : Bm * Bm = Bm := by
    rw [hBm]
    calc (R1*R2)*(R1*R2) = (R1*(R2*R1))*R2 := by noncomm_ring
      _ = (R1*(R1*R2))*R2 := by rw [← hR1R2]
      _ = ((R1*R1)*(R2*R2)) := by noncomm_ring
      _ = R1*R2 := by rw [hR1idem, hR2idem]
  have hAmBm : Am * Bm = 0 := by
    rw [hAm, hBm]
    calc (Q1*Q2)*(R1*R2) = (Q1*(Q2*R1))*R2 := by noncomm_ring
      _ = (Q1*(R1*Q2))*R2 := by rw [hQ2R1]
      _ = ((Q1*R1)*(Q2*R2)) := by noncomm_ring
      _ = 0 := by rw [hQ1R1, hQ2R2, zero_mul]
  have hBmAm : Bm * Am = 0 := by
    rw [hBm, hAm]
    calc (R1*R2)*(Q1*Q2) = (R1*(R2*Q1))*Q2 := by noncomm_ring
      _ = (R1*(Q1*R2))*Q2 := by rw [hR2Q1]
      _ = ((R1*Q1)*(R2*Q2)) := by noncomm_ring
      _ = 0 := by rw [hR1Q1, hR2Q2, zero_mul]
  have hX_idem : X * X = X := by
    rw [hX]
    calc (Am+Bm)*(Am+Bm) = Am*Am + Am*Bm + Bm*Am + Bm*Bm := by noncomm_ring
      _ = Am + 0 + 0 + Bm := by rw [hAm_idem, hAmBm, hBmAm, hBm_idem]
      _ = Am + Bm := by abel
  -- the permutation `s`
  have hs2 : s * s = 1 := by
    rw [hs, ← Matrix.permMatrix_mul, sB_mul_self, Matrix.permMatrix_one]
  have hsQ1s : s * Q1 * s = R2 := by
    rw [hs, hQ1, hR2]
    rw [conj_cycProj_perm (uB p.1) (sB p.1) (sB_mul_self p.1) (lam * omega), sB_conj_uB p.1]
  have hsQ2s : s * Q2 * s = R1 := by
    rw [hs, hQ2, hR1]
    rw [conj_cycProj_perm (vB p.1) (sB p.1) (sB_mul_self p.1) (lam * omega ^ 2), sB_conj_vB p.1]
  have hsAs : s * Am * s = Bm := by
    rw [hAm, hBm]
    have key : (s*Q1*s)*(s*Q2*s) = s*Q1*Q2*s := by
      rw [show (s*Q1*s)*(s*Q2*s) = s*Q1*(s*s)*Q2*s by noncomm_ring, hs2]
      noncomm_ring
    calc s*(Q1*Q2)*s = s*Q1*Q2*s := by noncomm_ring
      _ = (s*Q1*s)*(s*Q2*s) := key.symm
      _ = R2*R1 := by rw [hsQ1s, hsQ2s]
      _ = R1*R2 := by rw [← hR1R2]
  have hsBs : s * Bm * s = Am := by
    rw [← hsAs]
    rw [show s * (s * Am * s) * s = (s*s)*Am*(s*s) by noncomm_ring, hs2, one_mul, mul_one]
  -- `h1`, `hm` in `algebraMap` form
  have h1eq : h1 = algebraMap ℂ (Matrix (IB p.1) (IB p.1) A) (1/2) * (1 + s) := by
    rw [hh1, halfProj_one_sB, ← hs]
  have hmeq : hm = algebraMap ℂ (Matrix (IB p.1) (IB p.1) A) (1/2) * (1 - s) := by
    rw [hhm, halfProj_neg_one_sB, ← hs]
  -- the algebraic core
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ :=
    rest_core Am Bm s hAm_idem hBm_idem hAmBm hBmAm hs2 hsAs
  -- commutation of `P` with everything
  have hPP : P * P = P := by rw [hP]; exact PB_idem p hA hp
  have hPQ1 : P * Q1 = Q1 * P := by
    rw [hP, hQ1]
    exact cycProj_comm_of hA (uB p.1) (lam * omega) (PB p) (PB_comm_uB p hA)
  have hPQ2 : P * Q2 = Q2 * P := by
    rw [hP, hQ2]
    exact cycProj_comm_of hA (vB p.1) (lam * omega ^ 2) (PB p) (PB_comm_vB p hA)
  have hPR1 : P * R1 = R1 * P := by
    rw [hP, hR1]
    exact cycProj_comm_of hA (uB p.1) (lam * omega ^ 2) (PB p) (PB_comm_uB p hA)
  have hPR2 : P * R2 = R2 * P := by
    rw [hP, hR2]
    exact cycProj_comm_of hA (vB p.1) (lam * omega) (PB p) (PB_comm_vB p hA)
  have hPs : P * s = s * P := by rw [hP, hs]; exact PB_comm_sB hA p
  have hPh1 : P * h1 = h1 * P := by
    rw [hh1]
    exact halfProj_comm_of hA (sB p.1) 1 (PB p) (PB_comm_sB hA p)
  have hPhm : P * hm = hm * P := by
    rw [hhm]
    exact halfProj_comm_of hA (sB p.1) (-1) (PB p) (PB_comm_sB hA p)
  have hPAm : P * Am = Am * P := by
    rw [hAm]
    calc P*(Q1*Q2) = (P*Q1)*Q2 := by noncomm_ring
      _ = (Q1*P)*Q2 := by rw [hPQ1]
      _ = Q1*(P*Q2) := by noncomm_ring
      _ = Q1*(Q2*P) := by rw [hPQ2]
      _ = (Q1*Q2)*P := by noncomm_ring
  have hPBm : P * Bm = Bm * P := by
    rw [hBm]
    calc P*(R1*R2) = (P*R1)*R2 := by noncomm_ring
      _ = (R1*P)*R2 := by rw [hPR1]
      _ = R1*(P*R2) := by noncomm_ring
      _ = R1*(R2*P) := by rw [hPR2]
      _ = (R1*R2)*P := by noncomm_ring
  have hPX : P * X = X * P := by
    rw [hX]
    calc P*(Am+Bm) = P*Am + P*Bm := by noncomm_ring
      _ = Am*P + Bm*P := by rw [hPAm, hPBm]
      _ = (Am+Bm)*P := by noncomm_ring
  have hP1s : P * (1 + s) = (1 + s) * P := by
    rw [mul_add, mul_one, hPs, add_mul, one_mul]
  have hP1ms : P * (1 - s) = (1 - s) * P := by
    rw [mul_sub, mul_one, hPs, sub_mul, one_mul]
  have hPe : P * (X*h1) = (X*h1) * P := by
    calc P*(X*h1) = (P*X)*h1 := by noncomm_ring
      _ = (X*P)*h1 := by rw [hPX]
      _ = X*(P*h1) := by noncomm_ring
      _ = X*(h1*P) := by rw [hPh1]
      _ = (X*h1)*P := by noncomm_ring
  have hPf : P * (X*hm) = (X*hm) * P := by
    calc P*(X*hm) = (P*X)*hm := by noncomm_ring
      _ = (X*P)*hm := by rw [hPX]
      _ = X*(P*hm) := by noncomm_ring
      _ = X*(hm*P) := by rw [hPhm]
      _ = (X*hm)*P := by noncomm_ring
  have hPu : P * ((1+s)*Am) = ((1+s)*Am) * P := by
    calc P*((1+s)*Am) = (P*(1+s))*Am := by noncomm_ring
      _ = ((1+s)*P)*Am := by rw [hP1s]
      _ = (1+s)*(P*Am) := by noncomm_ring
      _ = (1+s)*(Am*P) := by rw [hPAm]
      _ = ((1+s)*Am)*P := by noncomm_ring
  have hPv : P * (Am*h1) = (Am*h1) * P := by
    calc P*(Am*h1) = (P*Am)*h1 := by noncomm_ring
      _ = (Am*P)*h1 := by rw [hPAm]
      _ = Am*(P*h1) := by noncomm_ring
      _ = Am*(h1*P) := by rw [hPh1]
      _ = (Am*h1)*P := by noncomm_ring
  have hPu2 : P * ((1-s)*Bm) = ((1-s)*Bm) * P := by
    calc P*((1-s)*Bm) = (P*(1-s))*Bm := by noncomm_ring
      _ = ((1-s)*P)*Bm := by rw [hP1ms]
      _ = (1-s)*(P*Bm) := by noncomm_ring
      _ = (1-s)*(Bm*P) := by rw [hPBm]
      _ = ((1-s)*Bm)*P := by noncomm_ring
  have hPv2 : P * (Bm*hm) = (Bm*hm) * P := by
    calc P*(Bm*hm) = (P*Bm)*hm := by noncomm_ring
      _ = (Bm*P)*hm := by rw [hPBm]
      _ = Bm*(P*hm) := by noncomm_ring
      _ = Bm*(hm*P) := by rw [hPhm]
      _ = (Bm*hm)*P := by noncomm_ring
  -- idempotency of the four idempotents attached to `X`, read off from the core
  have hG1 : (X*h1)*(X*h1) = X*h1 := by rw [h1eq, hX]; exact hc5
  have hG2 : (X*hm)*(X*hm) = X*hm := by rw [hmeq, hX]; exact hc6
  have hvu1 : (Am*h1)*((1+s)*Am) = Am := by rw [h1eq]; exact hc1
  have huv1 : ((1+s)*Am)*(Am*h1) = X*h1 := by rw [h1eq, hX]; exact hc2
  have hvu2 : (Bm*hm)*((1-s)*Bm) = Bm := by rw [hmeq]; exact hc3
  have huv2 : ((1-s)*Bm)*(Bm*hm) = X*hm := by rw [hmeq, hX]; exact hc4
  have hstep1 : clsM (IB p.1) (P*(X*h1)) = clsM (IB p.1) (P*Am) :=
    (mvN_lift P Am (X*h1) ((1+s)*Am) (Am*h1) hPP hPAm hPe hPv hAm_idem hG1 hvu1 huv1).symm
  have hstep3 : clsM (IB p.1) (P*Bm) = clsM (IB p.1) (P*(X*hm)) :=
    mvN_lift P Bm (X*hm) ((1-s)*Bm) (Bm*hm) hPP hPBm hPf hPv2 hBm_idem hG2 hvu2 huv2
  have hstep2 : clsM (IB p.1) (P*Am) = clsM (IB p.1) (P*Bm) := by
    have hconj : s*(P*Bm)*s = P*Am := by
      calc s*(P*Bm)*s = (s*P)*(Bm*s) := by noncomm_ring
        _ = (P*s)*(Bm*s) := by rw [← hPs]
        _ = P*(s*Bm*s) := by noncomm_ring
        _ = P*Am := by rw [hsBs]
    have h1 := clsM_conj (A := A) (ι := IB p.1) (P*Bm) s s hs2 hs2
    rwa [hconj] at h1
  calc clsM (IB p.1) (P * X * h1)
      = clsM (IB p.1) (P * (X * h1)) := by rw [mul_assoc]
    _ = clsM (IB p.1) (P * Am) := hstep1
    _ = clsM (IB p.1) (P * Bm) := hstep2
    _ = clsM (IB p.1) (P * (X * hm)) := hstep3
    _ = clsM (IB p.1) (P * X * hm) := by rw [mul_assoc]

end

end Work.PsiC
