import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.hk_idem_C_pre
import Submission.Work.KT.combine_conj
import Submission.Work.KT.matConj

/-!
# Idempotent matrices over `ℂ` are conjugate to `diag(1_r, 0)`

Every idempotent square matrix `p` over `ℂ` is conjugate (through an invertible
matrix) to the diagonal matrix whose first `r` diagonal entries are `1` and whose
remaining diagonal entries are `0`.

The proof is the standard one: read `p` as the linear map `P = Matrix.toLin' p`,
use `P * P = P` to write `ℂ^n = range P ⊕ ker P`, and choose a basis adapted to
this decomposition (a basis of `range P` followed by a basis of `ker P`). In that
basis `P` is the block diagonal matrix `diag(1_r, 0)`.
-/

open Matrix

namespace Work.KT

/-- Conjugating `e.conj f` back by `e.symm` recovers `f`. -/
private theorem conj_symm_conj_aux {R : Type*} [CommSemiring R] {M N : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (e : M ≃ₗ[R] N) (f : Module.End R M) : e.symm.conj (e.conj f) = f := by
  rw [LinearEquiv.conj_apply, LinearEquiv.conj_apply]
  ext x
  simp

/-- Every idempotent square matrix over `ℂ` is conjugate to a diagonal idempotent
`diag(1_r, 0)`. -/
theorem hk_idem_C (n : ℕ) (p : Matrix (Fin n) (Fin n) ℂ) (hp : p * p = p) :
    ∃ (r : ℕ) (g ginv : Matrix (Fin n) (Fin n) ℂ), g * ginv = 1 ∧ ginv * g = 1 ∧
      g * p * ginv = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then (1 : ℂ) else 0) := by
  let P : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := Matrix.toLin' p
  have hP : IsIdempotentElem P := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp]
    dsimp only [P]
    rw [← Matrix.toLin'_mul, hp]
  have hproj : LinearMap.IsProj P.range P := (LinearMap.isProj_range_iff_isIdempotentElem P).mpr hP
  let e : (P.range × P.ker) ≃ₗ[ℂ] (Fin n → ℂ) :=
    Submodule.prodEquivOfIsCompl P.range P.ker hproj.isCompl
  have he : P = e.conj (LinearMap.prodMap LinearMap.id 0) := by
    have h := LinearMap.IsProj.eq_conj_prodMap hproj
    simpa [e] using h
  let r : ℕ := Module.finrank ℂ P.range
  have hdim : Module.finrank ℂ P.range + Module.finrank ℂ P.ker = n := by
    rw [Submodule.finrank_add_eq_of_isCompl hproj.isCompl, Module.finrank_fin_fun]
  have hr : r ≤ n := by dsimp only [r]; omega
  have hk : Module.finrank ℂ P.ker = n - r := by dsimp only [r]; omega
  let bW : Module.Basis (Fin r) ℂ P.range := Module.finBasis ℂ P.range
  let bK : Module.Basis (Fin (n - r)) ℂ P.ker := Module.finBasisOfFinrankEq ℂ P.ker hk
  let E2 : ((Fin r → ℂ) × (Fin (n - r) → ℂ)) ≃ₗ[ℂ] (Fin n → ℂ) := combine n r hr
  let rho : (P.range × P.ker) ≃ₗ[ℂ] ((Fin r → ℂ) × (Fin (n - r) → ℂ)) :=
    bW.equivFun.prodCongr bK.equivFun
  let tau : (P.range × P.ker) ≃ₗ[ℂ] (Fin n → ℂ) := rho.trans E2
  let D : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    Matrix.toLin' (Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then (1 : ℂ) else 0))
  have hE2 : E2.toLinearMap ∘ₗ (LinearMap.prodMap LinearMap.id 0) = D ∘ₗ E2.toLinearMap := by
    simpa only [E2, D] using combine_conj n r hr
  have hE2c : E2.conj (LinearMap.prodMap LinearMap.id 0) = D := by
    rw [LinearEquiv.conj_apply, hE2]
    ext x; simp
  have hrho : rho.conj (LinearMap.prodMap LinearMap.id 0) = LinearMap.prodMap LinearMap.id 0 := by
    apply LinearMap.ext
    intro x
    obtain ⟨a, b⟩ := x
    simp only [rho, LinearEquiv.conj_apply_apply, LinearEquiv.prodCongr_symm,
      LinearEquiv.prodCongr_apply, LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.zero_apply,
      LinearEquiv.apply_symm_apply, map_zero]
  have htau : tau.conj (LinearMap.prodMap LinearMap.id 0) = D := by
    have h1 : tau.conj = rho.conj.trans E2.conj := by
      rw [show tau = rho.trans E2 from rfl, ← LinearEquiv.conj_trans]
    rw [h1, LinearEquiv.trans_apply, hrho, hE2c]
  have hprod : LinearMap.prodMap LinearMap.id 0 = tau.symm.conj D := by
    rw [← conj_symm_conj_aux tau (LinearMap.prodMap LinearMap.id 0), htau]
  let phi : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) := e.symm.trans tau
  have hg : e.symm.conj P = LinearMap.prodMap LinearMap.id 0 := by
    have h : e.symm.conj P = e.symm.conj (e.conj (LinearMap.prodMap LinearMap.id 0)) :=
      congrArg (fun Q => e.symm.conj Q) he
    rw [conj_symm_conj_aux e (LinearMap.prodMap LinearMap.id 0)] at h
    exact h
  have hphi : phi.conj P = D := by
    have h1 : phi.conj = e.symm.conj.trans tau.conj := by
      dsimp only [phi]
      rw [← LinearEquiv.conj_trans]
    rw [h1, LinearEquiv.trans_apply, hg, htau]
  refine ⟨r, LinearMap.toMatrix' (phi : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)),
    LinearMap.toMatrix' (phi.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)), ?_, ?_, ?_⟩
  · exact (matConj n phi (Matrix.toLin' p)).2.1
  · exact (matConj n phi (Matrix.toLin' p)).2.2
  · have h1 := (matConj n phi (Matrix.toLin' p)).1
    rw [LinearMap.toMatrix'_toLin' p] at h1
    have h2 : phi.conj (Matrix.toLin' p) = D := hphi
    rw [h2] at h1
    dsimp only [D] at h1
    rw [LinearMap.toMatrix'_toLin'] at h1
    exact h1

end Work.KT
