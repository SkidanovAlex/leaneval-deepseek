import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Psi.Basic

/-!
# `Work.KT.PsiC.cls_cyclic` — the cyclic lemma for the Adams–Atiyah K-theory argument

Let `X`, `e` be idempotent matrices over a `ℂ`-algebra `A`, and `u` a unit of order three
commuting with `X`, with `e * u * e = 0` and `e * (u * u) * e = 0`.  Writing
`E = e + u * e * (u * u) + (u * u) * e * u` and `F = (1/3) (1 + λ⁻¹ u + λ⁻² u²)` for `λ³ = 1`,
the projections `X * E * F` and `X * e` are Murray–von Neumann equivalent, so they have the same
class in `K₀`.

The mathematical content: from `e * u * e = 0` and `e * u² * e = 0` the elements
`e`, `ueu²`, `u²eu` are pairwise orthogonal idempotents cyclically permuted by `u`, so
`E = e + ueu² + u²eu` is again idempotent and commutes with `u`; `F` is the spectral projector
of `u` onto the `λ`-eigenspace.  Then `w ↦ F e w` identifies `im (X e)` with `im (X E F)`:
explicitly with `Q = 1 + λ⁻¹u + λ⁻²u² ∈ ℤ[e,u]` one has `Q e Q = E Q`, `e Q e = e`,
`Q Q = 3 Q`, and `(Q e X)(X e Q) = X E Q`, `(X e Q)(Q e X) = 3 (X e)`, so the Murray–von
Neumann maps are `X e Q` and `(1/3) Q e X`.

The scalars are removed from the computation by the rescaling `u ↦ λ⁻¹ u`, which satisfies the
same hypotheses (`(λ⁻¹u)³ = 1`, `e λ⁻¹ u e = 0`, `e (λ⁻¹u)² e = 0`) and turns
`Q = 1 + λ⁻¹u + (λ⁻¹u)²` into a scalar-free expression; the whole computation is then performed
for a general unit of order three (`Q_sq`, `e_Q_e`, `Q_e_Q`, `orbit_idem`) and reassembled in
`cyclic_core`.
-/

namespace Work.KT.PsiC

open Matrix

noncomputable section

variable {R : Type} [Ring R]

lemma u_uu_mul {u : R} (hu : u*u*u = 1) : ∀ x : R, u*(u*(u*x)) = x := by
  intro x; rw [← mul_assoc, ← mul_assoc, hu, one_mul]

lemma e_e_mul {e : R} (he : e*e = e) : ∀ x : R, e*(e*x) = e*x := by
  intro x; rw [← mul_assoc, he]

lemma e_u_e_mul {e u : R} (heu : e*u*e = 0) : ∀ x : R, e*(u*(e*x)) = 0 := by
  intro x; rw [← mul_assoc, ← mul_assoc, heu, zero_mul]

lemma e_uu_e_mul {e u : R} (heu2 : e*(u*u)*e = 0) : ∀ x : R, e*(u*(u*(e*x))) = 0 := by
  intro x
  have h : e*(u*(u*(e*x))) = ((e*(u*u))*e)*x := by noncomm_ring
  rw [h, heu2, zero_mul]

lemma orth_sum {e p q : R} (hee : e*e = e) (hpp : p*p = p) (hqq : q*q = q)
    (hep : e*p = 0) (hpe : p*e = 0) (heq : e*q = 0) (hqe : q*e = 0)
    (hpq : p*q = 0) (hqp : q*p = 0) :
    (e + p + q) * (e + p + q) = e + p + q := by
  noncomm_ring [hee, hpp, hqq, hep, hpe, heq, hqe, hpq, hqp]

lemma orbit_idem {e u : R} (he : e*e = e) (hu : u*u*u = 1) (heu : e*u*e = 0)
    (heu2 : e*(u*u)*e = 0) :
    (e + u*e*(u*u) + (u*u)*e*u) * (e + u*e*(u*u) + (u*u)*e*u)
      = e + u*e*(u*u) + (u*u)*e*u := by
  have huuu := u_uu_mul hu
  have hee := e_e_mul he
  have heue := e_u_e_mul heu
  have heuue := e_uu_e_mul heu2
  have heu' : e*(u*e) = 0 := by rw [← mul_assoc]; exact heu
  have heu2' : e*(u*(u*e)) = 0 := by
    have h : e*(u*(u*(e*1))) = 0 := heuue 1
    simpa using h
  have hpp : (u*e*(u*u))*(u*e*(u*u)) = u*e*(u*u) := by
    have h1 : (u*e*(u*u))*(u*e*(u*u)) = u*(e*(u*(u*(u*(e*(u*u)))))) := by noncomm_ring
    rw [h1, huuu, hee]; noncomm_ring
  have hqq : ((u*u)*e*u)*((u*u)*e*u) = (u*u)*e*u := by
    have h1 : ((u*u)*e*u)*((u*u)*e*u) = u*(u*(e*(u*(u*(u*(e*u)))))) := by noncomm_ring
    rw [h1, huuu, hee]; noncomm_ring
  have hpq : (u*e*(u*u))*((u*u)*e*u) = 0 := by
    have h1 : (u*e*(u*u))*((u*u)*e*u) = u*(e*(u*(u*(u*(u*(e*u)))))) := by noncomm_ring
    rw [h1, huuu, heue]; simp
  have hqp : ((u*u)*e*u)*(u*e*(u*u)) = 0 := by
    have h1 : ((u*u)*e*u)*(u*e*(u*u)) = u*(u*(e*(u*(u*(e*(u*u)))))) := by noncomm_ring
    rw [h1, heuue]; simp
  have hep : e*(u*e*(u*u)) = 0 := by
    have h1 : e*(u*e*(u*u)) = e*(u*(e*(u*u))) := by noncomm_ring
    rw [h1, heue]
  have hpe : (u*e*(u*u))*e = 0 := by
    have h1 : (u*e*(u*u))*e = u*(e*(u*(u*e))) := by noncomm_ring
    rw [h1, heu2']; simp
  have heq : e*((u*u)*e*u) = 0 := by
    have h1 : e*((u*u)*e*u) = e*(u*(u*(e*u))) := by noncomm_ring
    rw [h1, heuue]
  have hqe : ((u*u)*e*u)*e = 0 := by
    have h1 : ((u*u)*e*u)*e = u*(u*(e*(u*e))) := by noncomm_ring
    rw [h1, heu']; simp
  exact orth_sum he hpp hqq hep hpe heq hqe hpq hqp

lemma Q_sq {u : R} (hu : u*u*u = 1) :
    (1 + u + u*u) * (1 + u + u*u) = 3 * (1 + u + u*u) := by
  have hu' : u*(u*u) = 1 := by rw [← mul_assoc]; exact hu
  noncomm_ring [hu']

lemma e_Q_e {e u : R} (he : e*e = e) (heu : e*u*e = 0) (heu2 : e*(u*u)*e = 0) :
    e * (1 + u + u*u) * e = e := by
  have heu' : e*(u*e) = 0 := by rw [← mul_assoc]; exact heu
  have heu2' : e*(u*(u*e)) = 0 := by
    have h : e*(u*(u*(e*1))) = 0 := e_uu_e_mul heu2 1
    simpa using h
  noncomm_ring [he, heu', heu2']

lemma Q_e_Q {e u : R} (hu : u*u*u = 1) :
    (1 + u + u*u) * e * (1 + u + u*u)
      = (e + u*e*(u*u) + (u*u)*e*u) * (1 + u + u*u) := by
  have hu' : u*(u*u) = 1 := by rw [← mul_assoc]; exact hu
  noncomm_ring [hu']

lemma mul_comm_of_comm (X a b : R) (ha : X*a = a*X) (hb : X*b = b*X) :
    X*(a*b) = (a*b)*X := by
  rw [← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]

lemma add_comm_of_comm (X a b : R) (ha : X*a = a*X) (hb : X*b = b*X) :
    X*(a+b) = (a+b)*X := by
  rw [mul_add, add_mul, ha, hb]



variable {M : Type} [Ring M] [Algebra ℂ M]

lemma inv_cube (lam : ℂ) (hlam : lam^3 = 1) : lam⁻¹ * lam⁻¹ * lam⁻¹ = 1 := by
  have h : lam⁻¹^3 = 1 := by rw [inv_pow, hlam, inv_one]
  rwa [show lam⁻¹^3 = lam⁻¹ * lam⁻¹ * lam⁻¹ by ring] at h

lemma inv_cube' (lam : ℂ) (hlam : lam^3 = 1) : lam⁻¹ * (lam⁻¹ * lam⁻¹) = 1 := by
  have h : lam⁻¹^3 = 1 := by rw [inv_pow, hlam, inv_one]
  rwa [show lam⁻¹^3 = lam⁻¹ * (lam⁻¹ * lam⁻¹) by ring] at h

variable {M : Type} [Ring M] [Algebra ℂ M]

theorem cyclic_core (X e u : M) (lam : ℂ)
    (hX : X*X = X) (he : e*e = e) (hu : u*u*u = 1)
    (hXe : X*e = e*X) (hXu : X*u = u*X)
    (heu : e*u*e = 0) (heu2 : e*(u*u)*e = 0) (hlam : lam^3 = 1) :
    (algebraMap ℂ M (1/3) * (1 + algebraMap ℂ M lam⁻¹ * u + algebraMap ℂ M (lam⁻¹^2) * (u*u)) * e * X)
      * (X * e * (1 + algebraMap ℂ M lam⁻¹ * u + algebraMap ℂ M (lam⁻¹^2) * (u*u)))
    = X * (e + u*e*(u*u) + (u*u)*e*u) * (algebraMap ℂ M (1/3) * (1 + algebraMap ℂ M lam⁻¹ * u + algebraMap ℂ M (lam⁻¹^2) * (u*u)))
    ∧ (X * e * (1 + algebraMap ℂ M lam⁻¹ * u + algebraMap ℂ M (lam⁻¹^2) * (u*u)))
      * (algebraMap ℂ M (1/3) * (1 + algebraMap ℂ M lam⁻¹ * u + algebraMap ℂ M (lam⁻¹^2) * (u*u)) * e * X)
    = X * e
    ∧ (X * (e + u*e*(u*u) + (u*u)*e*u) * (algebraMap ℂ M (1/3) * (1 + algebraMap ℂ M lam⁻¹ * u + algebraMap ℂ M (lam⁻¹^2) * (u*u))))
      * (X * (e + u*e*(u*u) + (u*u)*e*u) * (algebraMap ℂ M (1/3) * (1 + algebraMap ℂ M lam⁻¹ * u + algebraMap ℂ M (lam⁻¹^2) * (u*u))))
    = X * (e + u*e*(u*u) + (u*u)*e*u) * (algebraMap ℂ M (1/3) * (1 + algebraMap ℂ M lam⁻¹ * u + algebraMap ℂ M (lam⁻¹^2) * (u*u))) := by
  have hc3 : lam⁻¹ * (lam⁻¹ * lam⁻¹) = 1 := inv_cube' lam hlam
  have hc3' : lam⁻¹ * lam⁻¹ * lam⁻¹ = 1 := inv_cube lam hlam
  set us : M := algebraMap ℂ M lam⁻¹ * u with hus
  set d : M := algebraMap ℂ M (1/3) with hd
  have hA' : us * us = algebraMap ℂ M (lam⁻¹^2) * (u*u) := by
    rw [hus]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul, pow_two]
  rw [← hA']
  have hB' : us*e*(us*us) = u*e*(u*u) := by
    rw [hus]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [hc3', one_smul]
  have hC' : (us*us)*e*us = (u*u)*e*u := by
    rw [hus]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [hc3, one_smul]
  rw [← hB', ← hC']
  set Q : M := 1 + us + us*us with hQ
  set E : M := e + us*e*(us*us) + (us*us)*e*us with hE
  set a : M := X*e*Q with ha
  set b : M := d*Q*e*X with hb
  have hu'3 : us*us*us = 1 := by
    rw [hus]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [hu, hc3, one_smul]
  have heu' : e*us*e = 0 := by
    rw [hus]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm]
    rw [heu, smul_zero]
  have heu'2 : e*(us*us)*e = 0 := by
    rw [hus]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [heu2, smul_zero]
  have hXus : X*us = us*X := by
    rw [hus]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, hXu]
  have hK1 : Q*Q = 3*Q := by rw [hQ]; exact Q_sq hu'3
  have hK2 : e*Q*e = e := by rw [hQ]; exact e_Q_e he heu' heu'2
  have hK3 : Q*e*Q = E*Q := by rw [hQ, hE]; exact Q_e_Q hu'3
  have hXQ : X*Q = Q*X := by
    rw [hQ]
    have h2 : X*(us*us) = (us*us)*X := mul_comm_of_comm X us us hXus hXus
    rw [mul_add, mul_add, mul_one, add_mul, add_mul, one_mul, hXus, h2]
  have hXE : X*E = E*X := by
    rw [hE]
    have h2 : X*(us*us) = (us*us)*X := mul_comm_of_comm X us us hXus hXus
    have h1 : X*(us*e) = (us*e)*X := mul_comm_of_comm X us e hXus hXe
    have h3 : X*(us*e*(us*us)) = (us*e*(us*us))*X := mul_comm_of_comm X (us*e) (us*us) h1 h2
    have h4 : X*((us*us)*e) = ((us*us)*e)*X := mul_comm_of_comm X (us*us) e h2 hXe
    have h5 : X*((us*us)*e*us) = ((us*us)*e*us)*X := mul_comm_of_comm X ((us*us)*e) us h4 hXus
    exact add_comm_of_comm X (e + us*e*(us*us)) ((us*us)*e*us)
      (add_comm_of_comm X e (us*e*(us*us)) hXe h3) h5
  have hmono2 : (X*e*Q)*(Q*e*X) = 3*(X*e) := by
    calc (X*e*Q)*(Q*e*X) = X*e*(Q*Q)*e*X := by noncomm_ring
      _ = X*e*(3*Q)*e*X := by rw [hK1]
      _ = 3*(X*(e*Q*e)*X) := by noncomm_ring
      _ = 3*(X*e*X) := by rw [hK2]
      _ = 3*(X*e) := by
        rw [mul_assoc, ← hXe]
        have h : X*(X*e) = X*e := by rw [← mul_assoc, hX]
        rw [h]
  have hmono1 : (Q*e*X)*(X*e*Q) = X*E*Q := by
    calc (Q*e*X)*(X*e*Q) = Q*e*(X*X)*e*Q := by noncomm_ring
      _ = Q*e*X*e*Q := by rw [hX]
      _ = Q*(e*X)*e*Q := by noncomm_ring
      _ = Q*(X*e)*e*Q := by rw [← hXe]
      _ = Q*X*(e*e)*Q := by noncomm_ring
      _ = Q*X*e*Q := by rw [he]
      _ = Q*(X*e)*Q := by noncomm_ring
      _ = Q*(e*X)*Q := by rw [← hXe]
      _ = Q*e*(X*Q) := by noncomm_ring
      _ = Q*e*(Q*X) := by rw [hXQ]
      _ = (Q*e*Q)*X := by noncomm_ring
      _ = (E*Q)*X := by rw [hK3]
      _ = E*(Q*X) := by noncomm_ring
      _ = E*(X*Q) := by rw [hXQ]
      _ = E*X*Q := by noncomm_ring
      _ = X*E*Q := by rw [← hXE]
  have hthree : (3:M) = algebraMap ℂ M (3:ℂ) := (map_natCast (algebraMap ℂ M) 3).symm
  have hdt : d*Q = (1/3:ℂ) • Q := by rw [hd, Algebra.smul_def]
  have hd3 : (3:M) * d = 1 := by
    rw [hd, hthree, ← map_mul, show (3:ℂ)*(1/3:ℂ) = 1 by norm_num, map_one]
  have hba : b*a = X*E*(d*Q) := by
    calc b*a = d*((Q*e*X)*(X*e*Q)) := by rw [hb, ha]; noncomm_ring
      _ = d*(X*E*Q) := by rw [hmono1]
      _ = X*E*(d*Q) := by rw [hdt, mul_smul_comm, hd, Algebra.smul_def]
  have hab : a*b = X*e := by
    calc a*b = (X*e*Q)*(d*Q*e*X) := by rw [ha, hb]
      _ = (X*e*Q)*((1/3:ℂ) • (Q*e*X)) := by rw [hdt, smul_mul_assoc, smul_mul_assoc]
      _ = (1/3:ℂ) • ((X*e*Q)*(Q*e*X)) := by rw [mul_smul_comm]
      _ = (1/3:ℂ) • (3*(X*e)) := by rw [hmono2]
      _ = X*e := by
          rw [show (3:M)*(X*e) = (3:ℂ) • (X*e) by rw [hthree, Algebra.smul_def]]
          rw [smul_smul, show (1/3:ℂ)*(3:ℂ) = 1 by norm_num, one_smul]
  have hXea : (X*e)*a = a := by
    rw [ha]
    calc (X*e)*(X*e*Q) = X*(e*X)*e*Q := by noncomm_ring
      _ = X*(X*e)*e*Q := by rw [← hXe]
      _ = (X*X)*(e*e)*Q := by noncomm_ring
      _ = X*e*Q := by rw [hX, he]
  have hidem : (X*E*(d*Q))*(X*E*(d*Q)) = X*E*(d*Q) := by
    calc (X*E*(d*Q))*(X*E*(d*Q)) = (b*a)*(b*a) := by rw [← hba]
      _ = b*(a*b)*a := by noncomm_ring
      _ = b*(X*e)*a := by rw [hab]
      _ = b*((X*e)*a) := by noncomm_ring
      _ = b*a := by rw [hXea]
      _ = X*E*(d*Q) := hba
  exact ⟨hba, hab, hidem⟩


/-! ## The cyclic lemma -/

theorem cls_cyclic {A : Type} [Ring A] [Algebra ℂ A]
    {n : ℕ} (X e u : Matrix (Fin n) (Fin n) A)
    (hX : X * X = X) (he : e * e = e) (hu : u * u * u = 1)
    (hXe : X * e = e * X) (hXu : X * u = u * X)
    (heu : e * u * e = 0) (heu2 : e * (u * u) * e = 0)
    (lam : ℂ) (hlam : lam ^ 3 = 1) :
    cls ⟨n, X * (e + u * e * (u * u) + (u * u) * e * u) *
        (algebraMap ℂ (Matrix (Fin n) (Fin n) A) (1 / 3) *
          (1 + algebraMap ℂ (Matrix (Fin n) (Fin n) A) lam⁻¹ * u +
            algebraMap ℂ (Matrix (Fin n) (Fin n) A) (lam⁻¹ ^ 2) * (u * u)))⟩
      = cls ⟨n, X * e⟩ := by
  obtain ⟨hba, hab, hidem⟩ := cyclic_core X e u lam hX he hu hXe hXu heu heu2 hlam
  have hidemQ : Mat.IsIdem (⟨n, X * e⟩ : Mat A) := by
    show (X * e) * (X * e) = X * e
    calc (X * e) * (X * e) = X * (e * X) * e := by noncomm_ring
      _ = X * (X * e) * e := by rw [← hXe]
      _ = (X * X) * (e * e) := by noncomm_ring
      _ = X * e := by rw [hX, he]
  exact cls_eq_of_MvN hidem hidemQ ⟨_, _, hba, hab⟩

end

end Work.KT.PsiC
