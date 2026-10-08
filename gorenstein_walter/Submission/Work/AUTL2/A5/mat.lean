/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 / A5 : the `PGL`/`PSL` determinant criteria

For a field `F` with `[DecidableEq F]`:

* `pglHom_mk_eq_one_iff` : `pglHom F (mk B) = 1` iff `B` is a scalar matrix;
* `isSquare_det_mem_pslImage` : a Möbius map with square determinant lies in `pslImage`;
* `isSquare_det_of_mul_map_eq_scalar` : if `A * σ(A)` is scalar then `det A` is a square
  (the "norm" computation underlying the A5 case analysis).
-/
import Mathlib
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Mobius
import Submission.Work.AUTL2.Stabilizer
import Submission.Work.AUTL2.Galois.decomposition
import Submission.Work.AUTL2.A5.tools

open scoped MatrixGroups
open OnePoint

set_option linter.style.haveILetI false

namespace Work.AUTL2.A5
open Work.AUTL2

variable {F : Type*} [Field F] [DecidableEq F]

/-- `pglHom F (mk B) = 1` iff `B` is a scalar matrix. -/
theorem pglHom_mk_eq_one_iff (B : Matrix.GeneralLinearGroup (Fin 2) F) :
    pglHom F (Matrix.ProjGenLinGroup.mk B) = 1 ↔
      B ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) := by
  constructor
  · intro hB
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    have hx : ∀ x : P1 F, B • x = x := by
      intro x
      have h := congrFun (congrArg DFunLike.coe hB) x
      rw [Galois.pglHom_mk_apply] at h
      simpa using h
    have h10 : (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
      OnePoint.smul_infty_eq_self_iff.mp (hx ∞)
    have hA0 : B • ((0 : F) : P1 F) =
        (if (B : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 then ∞
          else ↑((B : Matrix (Fin 2) (Fin 2) F) 0 1 / (B : Matrix (Fin 2) (Fin 2) F) 1 1)) := by
      rw [OnePoint.smul_some_eq_ite, h10]
      simp
    have h11 : (B : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
      intro h1
      have h := hx ((0 : F) : P1 F)
      rw [hA0, if_pos h1] at h
      exact OnePoint.infty_ne_coe _ h
    have h01 : (B : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
      have h := hx ((0 : F) : P1 F)
      rw [hA0, if_neg h11, OnePoint.coe_eq_coe] at h
      rcases div_eq_zero_iff.mp h with h | h
      · exact h
      · exact absurd h h11
    have hA1 : B • ((1 : F) : P1 F) =
        (if (B : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 then ∞
          else ↑(((B : Matrix (Fin 2) (Fin 2) F) 0 0 + (B : Matrix (Fin 2) (Fin 2) F) 0 1)
            / (B : Matrix (Fin 2) (Fin 2) F) 1 1)) := by
      rw [OnePoint.smul_some_eq_ite, h10]
      simp
    have h00 : (B : Matrix (Fin 2) (Fin 2) F) 0 0 = (B : Matrix (Fin 2) (Fin 2) F) 1 1 := by
      have h := hx ((1 : F) : P1 F)
      rw [hA1, if_neg h11, OnePoint.coe_eq_coe, h01, add_zero, div_eq_iff h11,
        one_mul] at h
      exact h
    refine ⟨Units.mk0 _ h11, ?_⟩
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      Units.val_mk0]
    fin_cases i <;> fin_cases j <;> simp [h10, h01, h00]
  · intro hB
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hB
    obtain ⟨u, rfl⟩ := hB
    rw [Matrix.ProjGenLinGroup.mk_scalar]
    exact map_one _

/-- A Möbius map whose determinant (with respect to any matrix representative) is a square
lies in `pslImage`. -/
theorem isSquare_det_mem_pslImage (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (h : IsSquare (Matrix.det (A : Matrix (Fin 2) (Fin 2) F))) :
    pglHom F (Matrix.ProjGenLinGroup.mk A) ∈ pslImage F := by
  obtain ⟨c, hc⟩ := h
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hc
    exact Matrix.GeneralLinearGroup.det_ne_zero A hc
  have hdetB : Matrix.det (c⁻¹ • (A : Matrix (Fin 2) (Fin 2) F)) = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, hc]
    field_simp
  let B : Matrix.SpecialLinearGroup (Fin 2) F := ⟨c⁻¹ • (A : Matrix (Fin 2) (Fin 2) F), hdetB⟩
  have hBA : Matrix.SpecialLinearGroup.toGL B *
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc0) = A := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_diagonal,
      Units.val_mk0]
    change (c⁻¹ • (A : Matrix (Fin 2) (Fin 2) F)) i j * c = (A : Matrix (Fin 2) (Fin 2) F) i j
    rw [Matrix.smul_apply, smul_eq_mul]
    field_simp
  refine ⟨QuotientGroup.mk B, ?_⟩
  have hfun : pslHom F (QuotientGroup.mk B) =
      pglHom F (Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL B)) := by
    apply Equiv.ext
    intro x
    rw [pslHom_toGL, Galois.pglHom_mk_apply]
  rw [hfun]
  rw [show Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL B) =
      Matrix.ProjGenLinGroup.mk A from by
    rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
    exact ⟨Units.mk0 c hc0, hBA⟩]

/-- If `A * σ(A)` is a scalar matrix (`σ` an order-two automorphism of `GF(p^k)`, `σ ≠ 1`)
then `det A` is a square.  This is the "norm" computation behind the A5 case analysis. -/
theorem isSquare_det_of_mul_map_eq_scalar (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    (σ : GaloisField p k ≃+* GaloisField p k) (hσ : σ * σ = 1) (hne : σ ≠ 1)
    (A : Matrix.GeneralLinearGroup (Fin 2) (GaloisField p k))
    (h : A * Matrix.GeneralLinearGroup.map (σ : GaloisField p k →+* GaloisField p k) A ∈
        Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p k))) :
    IsSquare (Matrix.det (A : Matrix (Fin 2) (Fin 2) (GaloisField p k))) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨u, hu⟩ := h
  have hφφ : ∀ x : GaloisField p k, σ (σ x) = x := fun x =>
    congrArg (fun e : GaloisField p k ≃+* GaloisField p k => e x) hσ
  have hdet_scalar : ∀ c : GaloisField p k, (Matrix.scalar (Fin 2) c).det = c ^ 2 := by
    intro c
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two]
    ring
  have hσdet : ((Matrix.GeneralLinearGroup.map (σ : GaloisField p k →+* GaloisField p k) A :
      Matrix.GeneralLinearGroup (Fin 2) (GaloisField p k)) :
      Matrix (Fin 2) (Fin 2) (GaloisField p k)).det =
      σ ((A : Matrix (Fin 2) (Fin 2) (GaloisField p k)).det) := by
    rw [show ((Matrix.GeneralLinearGroup.map (σ : GaloisField p k →+* GaloisField p k) A :
        Matrix.GeneralLinearGroup (Fin 2) (GaloisField p k)) :
        Matrix (Fin 2) (Fin 2) (GaloisField p k)) =
        (A : Matrix (Fin 2) (Fin 2) (GaloisField p k)).map (σ : GaloisField p k →+* GaloisField p k)
      from rfl]
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  have hmul : (A : Matrix (Fin 2) (Fin 2) (GaloisField p k)) *
      ((Matrix.GeneralLinearGroup.map (σ : GaloisField p k →+* GaloisField p k) A :
        Matrix.GeneralLinearGroup (Fin 2) (GaloisField p k)) :
        Matrix (Fin 2) (Fin 2) (GaloisField p k)) =
      Matrix.scalar (Fin 2) (u : GaloisField p k) := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, ← Matrix.GeneralLinearGroup.coe_scalar]
    exact (congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) (GaloisField p k) =>
      (g : Matrix (Fin 2) (Fin 2) (GaloisField p k))) hu).symm
  have hδ : (A : Matrix (Fin 2) (Fin 2) (GaloisField p k)).det *
      σ ((A : Matrix (Fin 2) (Fin 2) (GaloisField p k)).det) = (u : GaloisField p k) ^ 2 := by
    have hc := congrArg Matrix.det hmul
    rw [Matrix.det_mul, hσdet, hdet_scalar] at hc
    exact hc
  have hmapmap : Matrix.GeneralLinearGroup.map (σ : GaloisField p k →+* GaloisField p k)
      (Matrix.GeneralLinearGroup.map (σ : GaloisField p k →+* GaloisField p k) A) = A := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply]
    exact hφφ _
  have hMA : Matrix.GeneralLinearGroup.map (σ : GaloisField p k →+* GaloisField p k) A * A =
      Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
    have hcen : Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈
        Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p k)) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨u, rfl⟩
    have hcomm := (Subgroup.mem_center_iff.mp hcen A).symm
    have hM : Matrix.GeneralLinearGroup.map (σ : GaloisField p k →+* GaloisField p k) A =
        A⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
      rw [hu]; group
    rw [hM, mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  have hσu : σ (u : GaloisField p k) = (u : GaloisField p k) := by
    have h1 : Matrix.GeneralLinearGroup.map (σ : GaloisField p k →+* GaloisField p k)
        (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
        Matrix.GeneralLinearGroup.map (σ : GaloisField p k →+* GaloisField p k)
          (A * Matrix.GeneralLinearGroup.map (σ : GaloisField p k →+* GaloisField p k) A) :=
      congrArg _ hu
    rw [Matrix.GeneralLinearGroup.map_mul, hmapmap,
      Matrix.GeneralLinearGroup.map_scalar, hMA] at h1
    have h2 := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) (GaloisField p k) =>
      (g : Matrix (Fin 2) (Fin 2) (GaloisField p k)) 0 0) h1
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.coe_map] at h2
    rw [Matrix.diagonal_apply, Matrix.diagonal_apply, if_pos rfl, if_pos rfl] at h2
    simpa using h2
  obtain ⟨i, h2i, hi⟩ := sigma_pow_repr p k hp hq σ hσ hne
  have hpiodd : Odd (p ^ i) := Odd.pow hp
  obtain ⟨s, hs⟩ : ∃ s, p ^ i - 1 = 2 * s := by
    have h := Nat.odd_iff.mp hpiodd
    exact ⟨(p ^ i - 1) / 2, by omega⟩
  have hupow : (u : GaloisField p k) ^ (p ^ i) = (u : GaloisField p k) := by
    rw [← hi (u : GaloisField p k), hσu]
  have hu1 : (u : GaloisField p k) ^ (p ^ i - 1) = 1 := by
    have hpi : 0 < p ^ i := pow_pos (Nat.Prime.pos Fact.out) i
    have h := hupow
    rw [show p ^ i = (p ^ i - 1) + 1 from by omega, pow_succ] at h
    exact mul_right_cancel₀ (Units.ne_zero u) (by rw [one_mul]; exact h)
  have hδ0 : (A : Matrix (Fin 2) (Fin 2) (GaloisField p k)).det ≠ 0 :=
    Matrix.GeneralLinearGroup.det_ne_zero A
  have hmain : (A : Matrix (Fin 2) (Fin 2) (GaloisField p k)).det ^ (p ^ k / 2) = 1 := by
    have hk2 : p ^ k = (p ^ i) ^ 2 := by rw [← h2i, ← pow_mul, mul_comm]
    have hhalf : p ^ k / 2 = (1 + p ^ i) * ((p ^ i - 1) / 2) := by
      obtain ⟨m, hm⟩ := hpiodd.mul hpiodd
      rw [hk2, show (p ^ i) ^ 2 = p ^ i * p ^ i from by ring]
      rw [show p ^ i * p ^ i / 2 = (p ^ i * p ^ i - 1) / 2 from by rw [hm]; omega]
      have h2 : p ^ i * p ^ i - 1 = (p ^ i - 1) * (p ^ i + 1) := by
        have h := Nat.sq_sub_sq (p ^ i) 1
        rw [one_pow, mul_comm] at h
        rw [← h]; ring
      rw [h2, hs]
      rw [show (2 * s) * (p ^ i + 1) / 2 = s * (p ^ i + 1) from by
        rw [mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]]
      rw [show s * (p ^ i + 1) = (1 + p ^ i) * s from by ring]
      rw [show 2 * s / 2 = s from by omega]
    rw [hhalf, pow_mul]
    have hbase : (A : Matrix (Fin 2) (Fin 2) (GaloisField p k)).det ^ (1 + p ^ i) =
        (u : GaloisField p k) ^ 2 := by
      rw [pow_add, pow_one, ← hi ((A : Matrix (Fin 2) (Fin 2) (GaloisField p k)).det), hδ]
    rw [hbase]
    rw [← pow_mul, show (2 : ℕ) * ((p ^ i - 1) / 2) = p ^ i - 1 from by omega, hu1]
  have hchar : ringChar (GaloisField p k) ≠ 2 := by
    have hp2 : p ≠ 2 := by
      intro h2
      have := hp
      rw [h2] at this
      exact (by decide : ¬ Odd 2) this
    haveI : CharP (GaloisField p k) p := inferInstance
    rw [ringChar.eq (GaloisField p k) p]
    exact hp2
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  rw [FiniteField.isSquare_iff hchar hδ0]
  rw [show Fintype.card (GaloisField p k) = p ^ k from by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p k (by rintro rfl; simp at hq)]]
  exact hmain

/-- `pglHom F` is injective. -/
theorem pglHom_injective : Function.Injective (pglHom F) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  rw [pglHom_mk_eq_one_iff] at hg
  rwa [Matrix.ProjGenLinGroup.mk_eq_one]

/-- `pslHom F` is injective. -/
theorem pslHom_injective : Function.Injective (pslHom F) :=
  (pglHom_injective (F := F)).comp Matrix.ProjectiveSpecialLinearGroup.toPGL_injective

end Work.AUTL2.A5
