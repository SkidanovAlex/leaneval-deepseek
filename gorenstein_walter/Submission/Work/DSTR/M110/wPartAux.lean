/-
An independent proof of the `wPartProof` statement: if `w ∈ PGL(2,F)` commutes with the
non-split involution `t = tB0` then conjugation by `w` acts on the non-split torus
`T = torusPermB0` by the `±1`-power map.
-/
import Mathlib
import Submission.Work.DSTR.M110.torusFrobDefs
import Submission.Work.DSTR.M110.torusPermConjProof
import Submission.Work.DSTR.M110.mul_eq_smul_mul_of_mk_mul_eq
import Submission.Work.L2F.Mat2.commutant_sq_scalar

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint Polynomial Matrix

set_option maxHeartbeats 1000000

namespace Work.DSTR.M110

section MatrixAux

variable {F : Type*} [Field F]

/-- Two matrices centralizing a non-scalar `B` with `B * B = lam • 1`, `lam ≠ 0`, commute. -/
private lemma cent_mul_comm (B X T : Matrix (Fin 2) (Fin 2) F) (lam : F)
    (hB : B * B = lam • 1) (hlam : lam ≠ 0) (hns : ∀ x : F, B ≠ x • 1)
    (hX : X * B = B * X) (hT : T * B = B * T) : X * T = T * X := by
  obtain ⟨a, b, rfl⟩ := Work.L2F.Mat2.commutant_sq_scalar F B X lam hB hlam hns hX
  rw [add_mul, mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.mul_one, hT]

/-- **Key matrix computation.**  If `S B S⁻¹ = -B` and `T` commutes with `B` (where
`B * B = lam • 1`, `lam ≠ 0`, `B` non-scalar, and `char F ≠ 2`), then `(S T S⁻¹) T` is a
scalar matrix. -/
private lemma conj_mul_self_scalar (h2 : (2 : F) ≠ 0)
    (B S T : Matrix (Fin 2) (Fin 2) F) (lam : F)
    (hB : B * B = lam • 1) (hlam : lam ≠ 0) (hns : ∀ x : F, B ≠ x • 1)
    (hSinv : S * S⁻¹ = 1) (hSinS : S⁻¹ * S = 1)
    (hS1 : S * B * S⁻¹ = -B) (hTS : T * B = B * T) :
    ∃ a : F, (S * T * S⁻¹) * T = a • 1 := by
  have hSB : S * B = -(B * S) := by
    have h : S * B * S⁻¹ * S = -B * S := congrArg (fun M => M * S) hS1
    have h' : S * B * S⁻¹ * S = S * B := by
      rw [show S * B * S⁻¹ * S = S * B * (S⁻¹ * S) by noncomm_ring, hSinS, Matrix.mul_one]
    rw [h', neg_mul] at h
    exact h
  have hSinB : S⁻¹ * B = -(B * S⁻¹) := by
    have h : S⁻¹ * (S * B * S⁻¹) = S⁻¹ * (-B) := congrArg (fun M => S⁻¹ * M) hS1
    have h' : S⁻¹ * (S * B * S⁻¹) = B * S⁻¹ := by
      rw [show S⁻¹ * (S * B * S⁻¹) = (S⁻¹ * S) * (B * S⁻¹) by noncomm_ring, hSinS,
        Matrix.one_mul]
    rw [h', mul_neg] at h
    rw [h, neg_neg]
  have hS2B : (S * S) * B = B * (S * S) := by
    calc (S * S) * B = S * (S * B) := Matrix.mul_assoc S S B
      _ = S * (-(B * S)) := by rw [hSB]
      _ = -(S * (B * S)) := by rw [mul_neg]
      _ = -((S * B) * S) := by rw [← Matrix.mul_assoc]
      _ = -((-(B * S)) * S) := by rw [hSB]
      _ = (B * S) * S := by rw [neg_mul, neg_neg]
      _ = B * (S * S) := by rw [Matrix.mul_assoc]
  have hσB : (S * T * S⁻¹) * B = B * (S * T * S⁻¹) := by
    calc (S * T * S⁻¹) * B = (S * T) * (S⁻¹ * B) := by noncomm_ring
      _ = (S * T) * (-(B * S⁻¹)) := by rw [hSinB]
      _ = -((S * T) * (B * S⁻¹)) := by rw [mul_neg]
      _ = -((S * (T * B)) * S⁻¹) := by
            rw [show (S * T) * (B * S⁻¹) = (S * (T * B)) * S⁻¹ by noncomm_ring]
      _ = -((S * (B * T)) * S⁻¹) := by rw [hTS]
      _ = -(((S * B) * T) * S⁻¹) := by
            rw [show (S * (B * T)) * S⁻¹ = ((S * B) * T) * S⁻¹ by noncomm_ring]
      _ = -(((-(B * S)) * T) * S⁻¹) := by rw [hSB]
      _ = ((B * S) * T) * S⁻¹ := by
            rw [show -(((-(B * S)) * T) * S⁻¹) = ((B * S) * T) * S⁻¹ by noncomm_ring]
      _ = (B * (S * T)) * S⁻¹ := by
            rw [show ((B * S) * T) * S⁻¹ = (B * (S * T)) * S⁻¹ by noncomm_ring]
      _ = B * (S * T * S⁻¹) := by noncomm_ring
  have hS2T : (S * S) * T = T * (S * S) :=
    cent_mul_comm B (S * S) T lam hB hlam hns hS2B hTS
  have hTσ : T * (S * T * S⁻¹) = (S * T * S⁻¹) * T :=
    cent_mul_comm B T (S * T * S⁻¹) lam hB hlam hns hTS hσB
  have hTy : S * ((S * T * S⁻¹) * T) * S⁻¹ = (S * T * S⁻¹) * T := by
    have e1 : S * ((S * T * S⁻¹) * T) * S⁻¹ =
        (S * (S * T * S⁻¹) * S⁻¹) * (S * T * S⁻¹) := by
      rw [show S * ((S * T * S⁻¹) * T) * S⁻¹ = S * (S * T * S⁻¹) * T * S⁻¹ by
        noncomm_ring]
      rw [show (S * (S * T * S⁻¹) * S⁻¹) * (S * T * S⁻¹) =
          S * (S * T * S⁻¹) * (S⁻¹ * S) * T * S⁻¹ by noncomm_ring]
      rw [hSinS, Matrix.mul_one]
    rw [e1]
    have e2 : S * (S * T * S⁻¹) * S⁻¹ = T := by
      calc S * (S * T * S⁻¹) * S⁻¹ = ((S * S) * T) * (S⁻¹ * S⁻¹) := by noncomm_ring
        _ = (T * (S * S)) * (S⁻¹ * S⁻¹) := by rw [hS2T]
        _ = T * ((S * S) * (S⁻¹ * S⁻¹)) := by noncomm_ring
        _ = T * 1 := by
              rw [show (S * S) * (S⁻¹ * S⁻¹) = 1 by
                rw [show (S * S) * (S⁻¹ * S⁻¹) = S * (S * S⁻¹) * S⁻¹ by noncomm_ring,
                  hSinv, Matrix.mul_one, hSinv]]
        _ = T := by rw [Matrix.mul_one]
    rw [e2, hTσ]
  have hSyc : (S * T * S⁻¹) * T * B = B * ((S * T * S⁻¹) * T) := by
    calc (S * T * S⁻¹) * T * B = (S * T * S⁻¹) * (T * B) := by noncomm_ring
      _ = (S * T * S⁻¹) * (B * T) := by rw [hTS]
      _ = ((S * T * S⁻¹) * B) * T := by noncomm_ring
      _ = (B * (S * T * S⁻¹)) * T := by rw [hσB]
      _ = B * ((S * T * S⁻¹) * T) := by noncomm_ring
  have hcommS : S * ((S * T * S⁻¹) * T) = ((S * T * S⁻¹) * T) * S := by
    have h := congrArg (fun M => M * S) hTy
    have h' : S * ((S * T * S⁻¹) * T) * S⁻¹ * S = S * ((S * T * S⁻¹) * T) := by
      rw [show S * ((S * T * S⁻¹) * T) * S⁻¹ * S =
          S * ((S * T * S⁻¹) * T) * (S⁻¹ * S) by noncomm_ring, hSinS, Matrix.mul_one]
    rw [h'] at h
    exact h
  obtain ⟨a, b, hab⟩ :=
    Work.L2F.Mat2.commutant_sq_scalar F B ((S * T * S⁻¹) * T) lam hB hlam hns hSyc
  refine ⟨a, ?_⟩
  have hconj : S * ((S * T * S⁻¹) * T) * S⁻¹ = (S * T * S⁻¹) * T := by
    rw [hcommS, Matrix.mul_assoc, hSinv, Matrix.mul_one]
  rw [hab] at hconj
  have hsimp : S * (a • 1 + b • B) * S⁻¹ = a • 1 + (-b) • B := by
    calc S * (a • 1 + b • B) * S⁻¹
        = S * (a • 1) * S⁻¹ + S * (b • B) * S⁻¹ := by rw [mul_add, add_mul]
      _ = a • (S * 1 * S⁻¹) + b • (S * B * S⁻¹) := by
            rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = a • (S * S⁻¹) + b • (S * B * S⁻¹) := by rw [Matrix.mul_one]
      _ = a • 1 + b • (-B) := by rw [hSinv, hS1]
      _ = a • 1 + (-b) • B := by rw [smul_neg, neg_smul]
  rw [hsimp] at hconj
  have hbB : b • B = (-b) • B := (add_left_cancel hconj).symm
  have h2bB : (2 * b) • B = 0 := by
    rw [two_mul, add_smul]
    nth_rw 2 [hbB]
    rw [neg_smul, add_neg_cancel]
  have hb0 : b = 0 := by
    obtain ⟨i, j, hij⟩ : ∃ i j, B i j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hns 0 (by rw [zero_smul]; ext i j; simpa using h i j)
    have h := congrFun (congrFun h2bB i) j
    simp only [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at h
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' h2
      · exact h''
    · exact absurd h' hij
  rw [hb0, zero_smul, add_zero] at hab
  exact hab

end MatrixAux

section Main

variable (p k : ℕ) [Fact p.Prime] (hk : k ≠ 0) [DecidableEq (GaloisField p k)]
  (c : GaloisField p k) (hc : ¬ IsSquare c) (hodd : Odd p)

/-- The companion matrix `B0 c` is not a scalar matrix. -/
private lemma B0_not_scalar_aux : ∀ s : GaloisField p k,
    (B0 c hc : Matrix (Fin 2) (Fin 2) (GaloisField p k)) ≠ s • 1 := by
  intro s hs
  have h10 : (B0 c hc : Matrix (Fin 2) (Fin 2) (GaloisField p k)) 1 0 =
      (s • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p k))) 1 0 := by rw [hs]
  rw [B0_coe, companionMat_apply_one_zero, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), mul_zero] at h10
  exact one_ne_zero h10

private lemma two_ne_zero_aux (hodd : Odd p) : (2 : GaloisField p k) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : GaloisField p k) = 0 := by simpa using h
  have h2 : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p k) p 2).mp h'
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
  · exact (Fact.out : p.Prime).ne_one h1
  · exact (Nat.not_odd_iff_even.mpr (show Even p by rw [h1]; norm_num)) hodd

/-- **The `PGL`-part acts by `±1` on the non-split torus.**  If `w ∈ pglImage` commutes with
the non-split involution `tB0`, then conjugation by `w` acts on `torusPermB0` by the
`ε = ±1`-power map. -/
theorem wPartAux (hk : k ≠ 0) (w : ↥(Work.AUTL2.pgammaL (GaloisField p k)))
    (hw : (w : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) ∈
      Work.AUTL2.pglImage (GaloisField p k))
    (hcomm : (w : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) * tB0 p k c hc =
      tB0 p k c hc * (w : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∀ u : Work.DSTR.M110.TorUnits (GaloisField p k) c,
        (w : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) * torusPermB0 p k c hc u *
            (w : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))⁻¹ =
          torusPermB0 p k c hc (u ^ ε) := by
  obtain ⟨g0, hg0⟩ := MonoidHom.mem_range.mp hw
  obtain ⟨S, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g0
  have hwE : (w : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) =
      Work.AUTL2.pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk S) := hg0.symm
  have hcomm' : Matrix.ProjGenLinGroup.mk S * Matrix.ProjGenLinGroup.mk (B0 c hc) =
      Matrix.ProjGenLinGroup.mk (B0 c hc) * Matrix.ProjGenLinGroup.mk S := by
    apply Work.AUTL2.Aut.pglHomInjective (GaloisField p k)
    rw [map_mul, map_mul, ← hwE]
    exact hcomm
  obtain ⟨u, hu⟩ := mul_eq_smul_mul_of_mk_mul_eq S (B0 c hc) hcomm'.symm
  have hSM : (S : Matrix (Fin 2) (Fin 2) (GaloisField p k)) *
      (S : Matrix (Fin 2) (Fin 2) (GaloisField p k))⁻¹ = 1 := by
    have h := congrArg (fun g : GL (Fin 2) (GaloisField p k) =>
      (g : Matrix (Fin 2) (Fin 2) (GaloisField p k))) (mul_inv_cancel S)
    simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv,
      Matrix.GeneralLinearGroup.coe_one] using h
  have hSinS : (S : Matrix (Fin 2) (Fin 2) (GaloisField p k))⁻¹ *
      (S : Matrix (Fin 2) (Fin 2) (GaloisField p k)) = 1 := by
    have h := congrArg (fun g : GL (Fin 2) (GaloisField p k) =>
      (g : Matrix (Fin 2) (Fin 2) (GaloisField p k))) (inv_mul_cancel S)
    simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv,
      Matrix.GeneralLinearGroup.coe_one] using h
  set Sm : Matrix (Fin 2) (Fin 2) (GaloisField p k) :=
    (S : Matrix (Fin 2) (Fin 2) (GaloisField p k)) with hSmdef
  set Bm : Matrix (Fin 2) (Fin 2) (GaloisField p k) :=
    (B0 c hc : Matrix (Fin 2) (Fin 2) (GaloisField p k)) with hBmdef
  have hconjS : Sm * Bm * Sm⁻¹ = (u : GaloisField p k) • Bm := by
    have hu' : Sm * Bm = (u : GaloisField p k) • (Bm * Sm) := hu
    calc Sm * Bm * Sm⁻¹ = ((u : GaloisField p k) • (Bm * Sm)) * Sm⁻¹ := by rw [hu']
      _ = (u : GaloisField p k) • ((Bm * Sm) * Sm⁻¹) := by rw [Matrix.smul_mul]
      _ = (u : GaloisField p k) • (Bm * (Sm * Sm⁻¹)) := by rw [← Matrix.mul_assoc]
      _ = (u : GaloisField p k) • Bm := by rw [hSM, Matrix.mul_one]
  have hu2 : (u : GaloisField p k) ^ 2 = 1 := by
    have h1 : (Sm * Bm * Sm⁻¹) * (Sm * Bm * Sm⁻¹) =
        c • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p k)) := by
      calc (Sm * Bm * Sm⁻¹) * (Sm * Bm * Sm⁻¹)
          = Sm * Bm * (Sm⁻¹ * Sm) * Bm * Sm⁻¹ := by noncomm_ring
        _ = Sm * Bm * Bm * Sm⁻¹ := by rw [hSinS, Matrix.mul_one]
        _ = Sm * (Bm * Bm) * Sm⁻¹ := by noncomm_ring
        _ = Sm * (c • 1) * Sm⁻¹ := by
              rw [show Bm * Bm = c • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p k)) from
                B0_hB c hc]
        _ = c • (Sm * Sm⁻¹) := by
              rw [show Sm * (c • 1) * Sm⁻¹ = c • (Sm * Sm⁻¹) by
                rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]]
        _ = c • 1 := by rw [hSM]
    have h2 : ((u : GaloisField p k) • Bm) * ((u : GaloisField p k) • Bm) =
        ((u : GaloisField p k) ^ 2 * c) • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p k)) := by
      rw [show ((u : GaloisField p k) • Bm) * ((u : GaloisField p k) • Bm) =
          ((u : GaloisField p k) * u) • (Bm * Bm) by
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul],
        show Bm * Bm = c • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p k)) from B0_hB c hc,
        smul_smul, ← pow_two]
    have h3 : c • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p k)) =
        ((u : GaloisField p k) ^ 2 * c) • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p k)) := by
      rw [← h1, hconjS, h2]
    have h00 := congrFun (congrFun h3 0) 0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
    have hc0 : c ≠ 0 := ne_zero_of_not_isSquare hc
    have hh : (u : GaloisField p k) ^ 2 * c = 1 * c := by rw [one_mul]; exact h00.symm
    exact mul_right_cancel₀ hc0 hh
  have hu1 : (u : GaloisField p k) = 1 ∨ (u : GaloisField p k) = -1 := by
    have hfac : ((u : GaloisField p k) - 1) * ((u : GaloisField p k) + 1) = 0 := by
      rw [show ((u : GaloisField p k) - 1) * ((u : GaloisField p k) + 1) =
        (u : GaloisField p k) ^ 2 - 1 by ring, hu2, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · left; exact sub_eq_zero.mp h
    · right; exact eq_neg_of_add_eq_zero_left h
  rcases hu1 with hu1 | hu1
  · refine ⟨1, Or.inl rfl, fun u' => ?_⟩
    have hS1 : Sm * Bm * Sm⁻¹ = Bm := by rw [hconjS, hu1, one_smul]
    have hS1' : (S : Matrix (Fin 2) (Fin 2) (GaloisField p k)) *
        (B0 c hc : Matrix (Fin 2) (Fin 2) (GaloisField p k)) *
        (S : Matrix (Fin 2) (Fin 2) (GaloisField p k))⁻¹ =
        (B0 c hc : Matrix (Fin 2) (Fin 2) (GaloisField p k)) := hS1
    have hkey := torusPermConjProof (B0 c hc) (B0 c hc) c (B0_hB c hc) (B0_hB c hc) S hS1' u'
    rw [zpow_one, hwE]
    exact hkey.symm
  · refine ⟨-1, Or.inr rfl, fun u' => ?_⟩
    set μ : AdjoinRoot (X ^ 2 - C c : (GaloisField p k)[X]) :=
      ↑((u' : Work.DSTR.M110.TorUnits (GaloisField p k) c) :
        (AdjoinRoot (X ^ 2 - C c : (GaloisField p k)[X]))ˣ) with hμdef
    set Tm : Matrix (Fin 2) (Fin 2) (GaloisField p k) :=
      torusAlgHom (B0 c hc) c (B0_hB c hc) μ with hTmdef
    set B'm : Matrix (Fin 2) (Fin 2) (GaloisField p k) := -Bm with hB'mdef
    have hdetB' : B'm.det ≠ 0 := by
      rw [hB'mdef]
      have h : -Bm = (-1 : GaloisField p k) • Bm := (neg_one_smul (GaloisField p k) Bm).symm
      rw [h, Matrix.det_smul, Fintype.card_fin,
        show (-1 : GaloisField p k) ^ 2 = 1 by ring, one_mul]
      exact Matrix.GeneralLinearGroup.det_ne_zero (B0 c hc)
    let B' : GL (Fin 2) (GaloisField p k) := Matrix.GeneralLinearGroup.mkOfDetNeZero B'm hdetB'
    have hB'coe : (B' : Matrix (Fin 2) (Fin 2) (GaloisField p k)) = -Bm := by
      rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hB'mdef]
    have hB'hB : (B' : Matrix (Fin 2) (Fin 2) (GaloisField p k)) * B' = c • 1 := by
      rw [hB'coe, ← hB'mdef, hB'mdef, neg_mul_neg]
      exact B0_hB c hc
    have hS1' : Sm * Bm * Sm⁻¹ = (B' : Matrix (Fin 2) (Fin 2) (GaloisField p k)) := by
      rw [hconjS, hu1, neg_one_smul, hB'coe]
    have hS1'' : (S : Matrix (Fin 2) (Fin 2) (GaloisField p k)) *
        (B0 c hc : Matrix (Fin 2) (Fin 2) (GaloisField p k)) *
        (S : Matrix (Fin 2) (Fin 2) (GaloisField p k))⁻¹ =
        (B' : Matrix (Fin 2) (Fin 2) (GaloisField p k)) := by
      rw [← hSmdef, ← hBmdef]
      exact hS1'
    have hTS : Tm * Bm = Bm * Tm := by
      change torusAlgHom (B0 c hc) c (B0_hB c hc) μ *
          (B0 c hc : Matrix (Fin 2) (Fin 2) (GaloisField p k)) =
        (B0 c hc : Matrix (Fin 2) (Fin 2) (GaloisField p k)) *
          torusAlgHom (B0 c hc) c (B0_hB c hc) μ
      rw [show (B0 c hc : Matrix (Fin 2) (Fin 2) (GaloisField p k)) =
          torusAlgHom (B0 c hc) c (B0_hB c hc)
            (AdjoinRoot.root (X ^ 2 - C c : (GaloisField p k)[X])) from
          (torusAlgHom_root (B0 c hc) c (B0_hB c hc)).symm]
      rw [← map_mul, ← map_mul, mul_comm μ]
    have hT'eq : torusAlgHom B' c hB'hB μ = Sm * Tm * Sm⁻¹ := by
      rw [torusAlgHom_conj (B0 c hc) B' c (B0_hB c hc) hB'hB S hS1'' μ]
      rfl
    have hscalar := conj_mul_self_scalar (two_ne_zero_aux p k (odd_of_not_isSquare p k hk hc))
      (B0 c hc) S Tm c (B0_hB c hc) (ne_zero_of_not_isSquare hc) (B0_not_scalar_aux p k c hc)
      hSM hSinS (by rw [← hSmdef, ← hBmdef]; exact hS1'') hTS
    obtain ⟨a, ha⟩ := hscalar
    have hmat : ((torusGL B' c hB'hB u' : GL (Fin 2) (GaloisField p k)) :
          Matrix (Fin 2) (Fin 2) (GaloisField p k)) *
        ((torusGL (B0 c hc) c (B0_hB c hc) u' : GL (Fin 2) (GaloisField p k)) :
          Matrix (Fin 2) (Fin 2) (GaloisField p k)) =
        a • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p k)) := by
      simp only [torusGL, Units.coe_map]
      change torusAlgHom B' c hB'hB μ * Tm = a • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p k))
      rw [hT'eq]
      exact ha
    have hprod : Matrix.ProjGenLinGroup.mk (torusGL B' c hB'hB u') *
        Matrix.ProjGenLinGroup.mk (torusGL (B0 c hc) c (B0_hB c hc) u') = 1 := by
      rw [← map_mul, Matrix.ProjGenLinGroup.mk_eq_one, Subgroup.mem_center_iff]
      intro g
      apply Units.ext
      simp only [Matrix.GeneralLinearGroup.coe_mul, hmat]
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    have h1 : Matrix.ProjGenLinGroup.mk (torusGL B' c hB'hB u') =
        (Matrix.ProjGenLinGroup.mk (torusGL (B0 c hc) c (B0_hB c hc) u'))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]; exact hprod
    rw [show (u' : Work.DSTR.M110.TorUnits (GaloisField p k) c) ^ (-1 : ℤ) = u'⁻¹ from
      _root_.zpow_neg_one u', hwE]
    simp only [torusPermB0_apply, map_inv]
    rw [← torusPermConjProof (B0 c hc) B' c (B0_hB c hc) hB'hB S hS1'' u']
    simp only [torusPerm_apply]
    rw [h1, map_inv]

end Main

end Work.DSTR.M110

