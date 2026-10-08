/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.

# Involutions of `PGL(2, q)` fix either two points or none

Let `q = p ^ k` with `p` an odd prime, and let `t ∈ PGL(2, q)` be an involution (`t ^ 2 = 1`,
`t ≠ 1`) acting on the projective line `ℙ¹(q) = P1 (GaloisField p k)`.  Then `t` has either two
distinct fixed points or no fixed point at all:

`Work.DSTR.M110.pglInvolutionFixedPoints`.

The mathematical content is the standard classification of involutions of `PGL(2, q)` (`q` odd):
such a `t` is the image of a matrix `B` with `B * B = c • 1` for some `c ≠ 0`.
 * if `c` is not a square, a fixed point would produce an eigenvalue `λ` of `B` with `λ ^ 2 = c`,
   impossible;
 * if `c = d ^ 2`, then `(B - d) * (B + d) = 0`, and since `B` is not scalar both `B - d` and
   `B + d` have non-zero kernels, giving two independent eigenvectors, hence two fixed points.

The proof is carried out for an arbitrary field `F` of characteristic `≠ 2`
(`Work.DSTR.M110.pglInvolutionFixedPoints_field`) and then specialised.
-/
import Mathlib
import Submission.Work.DSTR.M110.Aut.pglIndex

namespace Work.DSTR.M110

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint Matrix

variable {F : Type*} [Field F] [DecidableEq F]

/-- The scalar matrix `c • 1` is `Matrix.scalar`. -/
lemma smul_one_eq_scalar (c : F) :
    c • (1 : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) c := by
  simp [Matrix.scalar, Matrix.smul_one_eq_diagonal, Matrix.diagonal]

/-- The action of `GL(2,F)` on `F²` is matrix–vector multiplication. -/
lemma gl_smul_eq_mulVec (B : GL (Fin 2) F) (v : Fin 2 → F) :
    B • v = (B : Matrix (Fin 2) (Fin 2) F) *ᵥ v := by
  rw [Matrix.GeneralLinearGroup.fin_two_smul]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The action of the `PGL`-element `mk B` on `ℙ¹(F)` is the action of the matrix `B`. -/
lemma pglHom_mk_apply (B : GL (Fin 2) F) (x : Work.AUTL2.P1 F) :
    Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk B) x = B • x := by
  show (Matrix.ProjGenLinGroup.mk B) • x = B • x
  rw [Matrix.ProjGenLinGroup.mk_smul (fun u a => Work.AUTL2.scalar_smul_eq_self F u a)]

/-- If `P * Q = 0` and `Q ≠ 0` then `P` kills a non-zero vector (`n` arbitrary). -/
lemma exists_mulVec_eq_zero_of_mul_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    (P Q : Matrix n n F) (hPQ : P * Q = 0) (hQ : Q ≠ 0) :
    ∃ v : n → F, v ≠ 0 ∧ P *ᵥ v = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, Q.col j ≠ 0 := by
    by_contra h
    push Not at h
    exact hQ (by ext i j; simpa using congrFun (h j) i)
  exact ⟨Q.col j, hj, by
    rw [← Matrix.mulVec_single_one Q j, Matrix.mulVec_mulVec, hPQ, Matrix.zero_mulVec]⟩

/-- A non-zero eigenvector `v` of `B` (eigenvalue `lam`) spans a fixed point of `mk B` on `ℙ¹(F)`. -/
lemma eigenvector_fixed_point (B : GL (Fin 2) F) (v : Fin 2 → F) (hv : v ≠ 0) {lam : F}
    (hBv : B • v = lam • v) :
    Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk B)
        ((OnePoint.equivProjectivization F).symm (Projectivization.mk F v hv)) =
      (OnePoint.equivProjectivization F).symm (Projectivization.mk F v hv) := by
  rw [pglHom_mk_apply]
  refine (OnePoint.equivProjectivization F).injective ?_
  simp only [OnePoint.equivProjectivization_smul, Equiv.apply_symm_apply]
  conv_lhs => rw [Projectivization.smul_mk]
  exact (Projectivization.mk_eq_mk_iff' F (B • v) v _ hv).mpr ⟨lam, hBv.symm⟩

/-- If `mk B` fixes a point of `ℙ¹(F)` and `B * B = c • 1`, then `c` is a square. -/
lemma isSquare_of_has_fixed_point (B : GL (Fin 2) F) (c : F)
    (hB : (B : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) = c • 1)
    (x : Work.AUTL2.P1 F) (hx : Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk B) x = x) :
    IsSquare c := by
  set v : Fin 2 → F := (OnePoint.equivProjectivization F x).rep with hvdef
  have hv : v ≠ 0 := (OnePoint.equivProjectivization F x).rep_nonzero
  have hmk : Projectivization.mk F v hv = OnePoint.equivProjectivization F x :=
    (OnePoint.equivProjectivization F x).mk_rep
  have hBx : B • x = x := (pglHom_mk_apply B x).symm.trans hx
  have hBp : B • (Projectivization.mk F v hv) = Projectivization.mk F v hv := by
    rw [hmk, ← OnePoint.equivProjectivization_smul, hBx]
  obtain ⟨lam, hlam⟩ : ∃ lam : F, lam • v = B • v := by
    have h2 : Projectivization.mk F (B • v) ((smul_ne_zero_iff_ne B).mpr hv) =
        Projectivization.mk F v hv :=
      (Projectivization.smul_mk B hv).symm.trans hBp
    exact (Projectivization.mk_eq_mk_iff' F (B • v) v _ hv).mp h2
  have hBv : (B : Matrix (Fin 2) (Fin 2) F) *ᵥ v = lam • v := by
    rw [← gl_smul_eq_mulVec]; exact hlam.symm
  have hkey : ((B : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F)) *ᵥ v =
      lam • (lam • v) := by
    calc ((B : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F)) *ᵥ v
        = (B : Matrix (Fin 2) (Fin 2) F) *ᵥ ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ v) :=
          (Matrix.mulVec_mulVec v _ _).symm
      _ = (B : Matrix (Fin 2) (Fin 2) F) *ᵥ (lam • v) := by rw [hBv]
      _ = lam • ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ v) := Matrix.mulVec_smul _ _ _
      _ = lam • (lam • v) := by rw [hBv]
  rw [hB] at hkey
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul] at hkey
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have heq : c * v i = (lam * lam) * v i := by
    have := congrFun hkey i
    simpa [Pi.smul_apply, smul_eq_mul] using this
  exact ⟨lam, mul_right_cancel₀ hi heq⟩

/-- **Structure of involutions of `PGL(2,F)`**, `F` a field with `2 ≠ 0`: an involution fixes
either two distinct points of `ℙ¹(F)` or none. -/
theorem pglInvolutionFixedPoints_field (F : Type*) [Field F] [DecidableEq F] (h2 : (2 : F) ≠ 0)
    (t : Equiv.Perm (Work.AUTL2.P1 F)) (ht : t ∈ Work.AUTL2.pglImage F) (ht2 : orderOf t = 2) :
    (∃ a b : Work.AUTL2.P1 F, a ≠ b ∧ t a = a ∧ t b = b) ∨
      (∀ x : Work.AUTL2.P1 F, t x ≠ x) := by
  obtain ⟨g, hg⟩ := ht
  obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  -- `t` is an involution
  have ht2' : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2, pow_two] at h
    exact h
  -- hence its matrix representative squares to a scalar matrix
  have hBB : Matrix.ProjGenLinGroup.mk (B * B) = 1 := by
    apply Work.AUTL2.Aut.pglHomInjective F
    rw [map_mul, map_mul, hg, ht2', map_one]
  have hcenter : B * B ∈ Subgroup.center (GL (Fin 2) F) := (Matrix.ProjGenLinGroup.mk_eq_one).mp hBB
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range] at hcenter
  obtain ⟨u, hu⟩ := hcenter
  -- and `B` is not a scalar matrix (else `t = 1`)
  have hBns : ¬ ∃ w : Fˣ, B = Matrix.GeneralLinearGroup.scalar (Fin 2) w := by
    rintro ⟨w, hw⟩
    have h1 : t = 1 := by rw [← hg, hw, Matrix.ProjGenLinGroup.mk_scalar, map_one]
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hBBm : (B : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F)
      = (u : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have h := congrArg (fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F)) hu
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar] at h
    rw [(smul_one_eq_scalar (u : F)).symm] at h
    exact h.symm
  by_cases hsq : IsSquare (u : F)
  · -- `c` is a square: two fixed points
    obtain ⟨d, hd⟩ := hsq
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact Units.ne_zero u (by simpa using hd)
    -- normalise: `B' = d⁻¹ • B` is an involution of `GL(2,F)`
    let B' : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero
      (d⁻¹ • (B : Matrix (Fin 2) (Fin 2) F)) (by
        rw [Matrix.det_smul, Fintype.card_fin]
        exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hd0)) B.det_ne_zero)
    have hB'mat : (B' : Matrix (Fin 2) (Fin 2) F) = d⁻¹ • (B : Matrix (Fin 2) (Fin 2) F) :=
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _
    have hB'sq : (B' : Matrix (Fin 2) (Fin 2) F) * (B' : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [hB'mat, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hBBm, hd, smul_smul]
      rw [show d⁻¹ * d⁻¹ * (d * d) = 1 by field_simp, one_smul]
    have hB'ne1 : (B' : Matrix (Fin 2) (Fin 2) F) ≠ -1 := by
      intro hcon
      have h1 : d⁻¹ • (B : Matrix (Fin 2) (Fin 2) F) = -(1 : Matrix (Fin 2) (Fin 2) F) := by
        rw [← hB'mat]; exact hcon
      have h2 : (B : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (-d) := by
        have h3 : d • (d⁻¹ • (B : Matrix (Fin 2) (Fin 2) F))
            = d • (-(1 : Matrix (Fin 2) (Fin 2) F)) := congrArg (fun M => d • M) h1
        rw [smul_smul, mul_inv_cancel₀ hd0, one_smul, smul_neg, ← neg_smul,
          smul_one_eq_scalar] at h3
        exact h3
      apply hBns
      refine ⟨Units.mk0 (-d) (neg_ne_zero.mpr hd0), ?_⟩
      refine Matrix.GeneralLinearGroup.ext (fun i j => ?_)
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, h2]
    have hB'nem1 : (B' : Matrix (Fin 2) (Fin 2) F) ≠ 1 := by
      intro hcon
      have h1 : d⁻¹ • (B : Matrix (Fin 2) (Fin 2) F) = (1 : Matrix (Fin 2) (Fin 2) F) := by
        rw [← hB'mat]; exact hcon
      have h2 : (B : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) d := by
        have h3 : d • (d⁻¹ • (B : Matrix (Fin 2) (Fin 2) F))
            = d • (1 : Matrix (Fin 2) (Fin 2) F) := congrArg (fun M => d • M) h1
        rw [smul_smul, mul_inv_cancel₀ hd0, one_smul, smul_one_eq_scalar] at h3
        exact h3
      apply hBns
      refine ⟨Units.mk0 d hd0, ?_⟩
      refine Matrix.GeneralLinearGroup.ext (fun i j => ?_)
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, h2]
    -- `B'` and `B` have the same image in `PGL`
    have hmkB' : Matrix.ProjGenLinGroup.mk B' = Matrix.ProjGenLinGroup.mk B := by
      rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
      refine ⟨Units.mk0 d hd0, ?_⟩
      refine Matrix.GeneralLinearGroup.ext (fun i j => ?_)
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
      have hm : (d⁻¹ • (B : Matrix (Fin 2) (Fin 2) F)) * Matrix.scalar (Fin 2) d
          = (B : Matrix (Fin 2) (Fin 2) F) := by
        rw [(smul_one_eq_scalar d).symm, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
          smul_smul, inv_mul_cancel₀ hd0, one_smul]
      rw [hB'mat, hm]
    -- `(B' - 1) * (B' + 1) = 0 = (B' + 1) * (B' - 1)`
    have hfac1 : ((B' : Matrix (Fin 2) (Fin 2) F) - 1) * ((B' : Matrix (Fin 2) (Fin 2) F) + 1)
        = 0 := by
      have h1 : ((B' : Matrix (Fin 2) (Fin 2) F) - 1) * ((B' : Matrix (Fin 2) (Fin 2) F) + 1)
          = (B' : Matrix (Fin 2) (Fin 2) F) * B' - 1 := by noncomm_ring
      rw [h1, hB'sq, sub_self]
    have hfac2 : ((B' : Matrix (Fin 2) (Fin 2) F) + 1) * ((B' : Matrix (Fin 2) (Fin 2) F) - 1)
        = 0 := by
      have h1 : ((B' : Matrix (Fin 2) (Fin 2) F) + 1) * ((B' : Matrix (Fin 2) (Fin 2) F) - 1)
          = (B' : Matrix (Fin 2) (Fin 2) F) * B' - 1 := by noncomm_ring
      rw [h1, hB'sq, sub_self]
    have hne1 : (B' : Matrix (Fin 2) (Fin 2) F) + 1 ≠ 0 := by
      intro h; exact hB'ne1 ((add_eq_zero_iff_eq_neg).mp h)
    have hne2 : (B' : Matrix (Fin 2) (Fin 2) F) - 1 ≠ 0 := by
      intro h; exact hB'nem1 (sub_eq_zero.mp h)
    -- two independent eigenvectors, of eigenvalues `1` and `-1`
    obtain ⟨v, hv, hv0⟩ := exists_mulVec_eq_zero_of_mul_eq_zero
      ((B' : Matrix (Fin 2) (Fin 2) F) - 1) ((B' : Matrix (Fin 2) (Fin 2) F) + 1) hfac1 hne1
    obtain ⟨w, hw, hw0⟩ := exists_mulVec_eq_zero_of_mul_eq_zero
      ((B' : Matrix (Fin 2) (Fin 2) F) + 1) ((B' : Matrix (Fin 2) (Fin 2) F) - 1) hfac2 hne2
    have hBv : (B' : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv0
      exact hv0
    have hBw : (B' : Matrix (Fin 2) (Fin 2) F) *ᵥ w = -w := by
      rw [Matrix.add_mulVec, Matrix.one_mulVec, add_eq_zero_iff_eq_neg] at hw0
      exact hw0
    have hv1 : B' • v = (1 : F) • v := by rw [gl_smul_eq_mulVec, hBv, one_smul]
    have hw1 : B' • w = (-1 : F) • w := by rw [gl_smul_eq_mulVec, hBw, neg_one_smul]
    -- the corresponding points of `ℙ¹(F)`
    set p : Work.AUTL2.P1 F :=
      (OnePoint.equivProjectivization F).symm (Projectivization.mk F v hv) with hpdef
    set q : Work.AUTL2.P1 F :=
      (OnePoint.equivProjectivization F).symm (Projectivization.mk F w hw) with hqdef
    have hp' : Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk B') p = p :=
      eigenvector_fixed_point B' v hv hv1
    have hq' : Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk B') q = q :=
      eigenvector_fixed_point B' w hw hw1
    have hp : t p = p := by rw [← hg, ← hmkB']; exact hp'
    have hq : t q = q := by rw [← hg, ← hmkB']; exact hq'
    -- they are distinct (distinct eigenvalues `1 ≠ -1`)
    have hpq : p ≠ q := by
      intro hpqeq
      have hmkeq : Projectivization.mk F v hv = Projectivization.mk F w hw :=
        (OnePoint.equivProjectivization F).symm.injective hpqeq
      obtain ⟨mu, hmu⟩ := (Projectivization.mk_eq_mk_iff' F v w hv hw).mp hmkeq
      have hneg : v = -v := by
        calc v = (B' : Matrix (Fin 2) (Fin 2) F) *ᵥ v := hBv.symm
          _ = (B' : Matrix (Fin 2) (Fin 2) F) *ᵥ (mu • w) := by rw [hmu]
          _ = mu • ((B' : Matrix (Fin 2) (Fin 2) F) *ᵥ w) := Matrix.mulVec_smul _ _ _
          _ = mu • (-w) := by rw [hBw]
          _ = -(mu • w) := smul_neg _ _
          _ = -((B' : Matrix (Fin 2) (Fin 2) F) *ᵥ v) := by rw [hmu, hBv]
          _ = -v := by rw [hBv]
      have h2v : (2 : F) • v = 0 := by
        rw [two_smul]
        exact (eq_neg_iff_add_eq_zero).mp hneg
      exact hv ((smul_eq_zero.mp h2v).resolve_left h2)
    exact Or.inl ⟨p, q, hpq, hp, hq⟩
  · -- `c` is not a square: no fixed point
    exact Or.inr (fun x hx => hsq (isSquare_of_has_fixed_point B (u : F) hBBm x (by rw [hg]; exact hx)))

theorem pglInvolutionFixedPoints (p k : ℕ) [Fact p.Prime] (hp : Odd p)
    [DecidableEq (GaloisField p k)]
    (t : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))
    (ht : t ∈ Work.AUTL2.pglImage (GaloisField p k)) (ht2 : orderOf t = 2) :
    (∃ a b : Work.AUTL2.P1 (GaloisField p k), a ≠ b ∧ t a = a ∧ t b = b) ∨
      (∀ x : Work.AUTL2.P1 (GaloisField p k), t x ≠ x) := by
  haveI : CharP (GaloisField p k) p := inferInstance
  have h2 : (2 : GaloisField p k) ≠ 0 := by
    intro hcon
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p k) p 2).mp hcon
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    obtain ⟨m, hm⟩ := hp
    omega
  exact pglInvolutionFixedPoints_field (GaloisField p k) h2 t ht ht2

end Work.DSTR.M110
