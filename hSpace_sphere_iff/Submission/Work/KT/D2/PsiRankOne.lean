import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.k3Aux
import Submission.Work.KT.mvN_comm
import Submission.Work.KT.mvN_additive
import Submission.Work.KT.mvN_assoc
import Submission.Work.KT.sumMvN
import Submission.Work.KT.sum_mvN_congr
import Submission.Work.KT.Dim2.rankOne_projectors

/-!
# `Work.KT.D2UP` / `Work.KT.D2PR`

Self-contained copies of `Work.KT.Dim2.unit_projectors` and `Work.KT.Dim2.psi_rank_one`, in fresh
namespaces, so that the Adams-operation computation for a rank-one `2 × 2` idempotent is available
without depending on the (independently edited) originals.
-/

namespace Work.KT.D2UP

open Matrix

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- `1 + ω⁻¹ + (ω⁻¹)² = 0` for the primitive cube root of unity. -/
private lemma omega_inv_sum_aux : (1 : ℂ) + omega⁻¹ + (omega⁻¹) ^ 2 = 0 := by
  rw [omega_inv_sq, omega_inv]
  linear_combination Work.KT.Psi.K3.omega_sq_add_omega_add_one

/-- The swap permutation on a single index is the identity. -/
private lemma swapPerm_one_eq : (swapPerm 1 : Equiv.Perm (Fin (1 * 1))) = Equiv.refl _ := by
  haveI : Subsingleton (Fin (1 * 1)) := inferInstanceAs (Subsingleton (Fin 1))
  exact Equiv.ext fun x => Subsingleton.elim _ _

/-- The cyclic permutation on a single index is the identity. -/
private lemma cycPerm_one_eq : (cycPerm 1 : Equiv.Perm (Fin (1 * 1 * 1))) = Equiv.refl _ := by
  haveI : Subsingleton (Fin (1 * 1 * 1)) := inferInstanceAs (Subsingleton (Fin 1))
  exact Equiv.ext fun x => Subsingleton.elim _ _

/-- The Kronecker product of two `1 × 1` matrices is their ordinary product. -/
private lemma kronMat_fin1 (X Y : Matrix (Fin 1) (Fin 1) A) : kronMat X Y = X * Y := by
  ext i j
  fin_cases i; fin_cases j
  simp only [kronMat, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
  congr 1 <;> congr 1 <;> exact Subsingleton.elim _ _

/-- `(1 + ε·s)/2` evaluated at `ε = 1` on the trivial `1 × 1` bundle. -/
private lemma sq2_bracket_one :
    algebraMap ℂ A (1/2) •
      ((1 : Matrix (Fin (1*1)) (Fin (1*1)) A) + algebraMap ℂ A (1:ℂ) • 1) = 1 := by
  haveI : Subsingleton (Fin (1*1)) := inferInstanceAs (Subsingleton (Fin 1))
  ext i j
  have hij : i = j := Subsingleton.elim i j
  rw [hij]
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, ↓reduceIte, map_one, smul_eq_mul]
  rw [show (algebraMap ℂ A (1/2:ℂ)) * (1 + 1 * 1) = 1 by
    rw [show (1 : A) + 1 * 1 = (2:A) by norm_num,
      show (2:A) = algebraMap ℂ A 2 by rw [map_ofNat],
      ← map_mul, show (1/2:ℂ) * 2 = 1 by norm_num, map_one]]

/-- `(1 + ε·s)/2` evaluated at `ε = -1` on the trivial `1 × 1` bundle. -/
private lemma sq2_bracket_neg_one :
    ((1 : Matrix (Fin (1*1)) (Fin (1*1)) A) + algebraMap ℂ A (-1:ℂ) • 1) = 0 := by
  haveI : Subsingleton (Fin (1*1)) := inferInstanceAs (Subsingleton (Fin 1))
  ext i j
  have hij : i = j := Subsingleton.elim i j
  rw [hij]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply, ↓reduceIte,
    map_neg, map_one, smul_eq_mul, mul_one]
  simp [add_neg_cancel]

/-- The scalar identity `1 + ω⁻¹ + (ω⁻¹)² = 0` in `A`. -/
private lemma omega_scalar :
    (1 : A) + algebraMap ℂ A omega⁻¹ + algebraMap ℂ A ((omega⁻¹)^2) = 0 := by
  have h : (1 : A) + algebraMap ℂ A omega⁻¹ + algebraMap ℂ A ((omega⁻¹)^2)
      = algebraMap ℂ A ((1:ℂ) + omega⁻¹ + (omega⁻¹)^2) := by
    simp only [map_add, map_one, map_pow]
  rw [h, omega_inv_sum_aux, map_zero]

/-- The order-three spectral projector evaluated at `λ = 1` on the trivial `1 × 1` bundle. -/
private lemma cube_bracket_one :
    algebraMap ℂ A (1/3) • ((1 : Matrix (Fin (1*1*1)) (Fin (1*1*1)) A)
      + algebraMap ℂ A ((1:ℂ)⁻¹) • 1 + algebraMap ℂ A (((1:ℂ)⁻¹)^2) • 1) = 1 := by
  haveI : Subsingleton (Fin (1*1*1)) := inferInstanceAs (Subsingleton (Fin 1))
  ext i j
  have hij : i = j := Subsingleton.elim i j
  rw [hij]
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, ↓reduceIte, map_one, smul_eq_mul,
    inv_one, one_pow, one_mul]
  rw [show (algebraMap ℂ A (1/3:ℂ)) * (1 + 1 + 1) = 1 by
    rw [show (1 : A) + 1 + 1 = (3:A) by norm_num,
      show (3:A) = algebraMap ℂ A 3 by rw [map_ofNat],
      ← map_mul, show (1/3:ℂ) * 3 = 1 by norm_num, map_one]]

/-- The order-three spectral projector evaluated at `λ = ω` on the trivial `1 × 1` bundle. -/
private lemma cube_bracket_omega :
    ((1 : Matrix (Fin (1*1*1)) (Fin (1*1*1)) A) + algebraMap ℂ A omega⁻¹ • 1
      + algebraMap ℂ A ((omega⁻¹)^2) • 1) = 0 := by
  haveI : Subsingleton (Fin (1*1*1)) := inferInstanceAs (Subsingleton (Fin 1))
  ext i j
  have hij : i = j := Subsingleton.elim i j
  rw [hij]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply, ↓reduceIte,
    smul_eq_mul, mul_one]
  exact omega_scalar

/-- `sq2Part 1` of a `1 × 1` idempotent is its square. -/
private lemma sq2Part_one_snd (M : Matrix (Fin 1) (Fin 1) A) :
    (sq2Part (1 : ℂ) (⟨1, M⟩ : Mat A)).2 = M * M := by
  change kronMat M M *
    (algebraMap ℂ A (1/2) • (1 + algebraMap ℂ A (1:ℂ) • (swapPerm 1).permMatrix A)) = M * M
  rw [swapPerm_one_eq, Matrix.permMatrix_refl, sq2_bracket_one, Matrix.mul_one]
  exact kronMat_fin1 M M

/-- `sq2Part (-1)` of a `1 × 1` idempotent vanishes. -/
private lemma sq2Part_neg_one_snd (M : Matrix (Fin 1) (Fin 1) A) :
    (sq2Part (-1 : ℂ) (⟨1, M⟩ : Mat A)).2 = 0 := by
  change kronMat M M *
    (algebraMap ℂ A (1/2) • (1 + algebraMap ℂ A (-1:ℂ) • (swapPerm 1).permMatrix A)) = 0
  rw [swapPerm_one_eq, Matrix.permMatrix_refl, sq2_bracket_neg_one, smul_zero, Matrix.mul_zero]

/-- `cubePart 1` of a `1 × 1` idempotent is its cube. -/
private lemma cubePart_one_snd (M : Matrix (Fin 1) (Fin 1) A) :
    (cubePart (1 : ℂ) (⟨1, M⟩ : Mat A)).2 = M * M * M := by
  change kronMat (kronMat M M) M *
    (algebraMap ℂ A (1/3) • (1 + algebraMap ℂ A ((1:ℂ)⁻¹) • (cycPerm 1).permMatrix A
      + algebraMap ℂ A (((1:ℂ)⁻¹)^2) • ((cycPerm 1).permMatrix A * (cycPerm 1).permMatrix A)))
      = M * M * M
  rw [cycPerm_one_eq, Matrix.permMatrix_refl, Matrix.mul_one, cube_bracket_one, Matrix.mul_one]
  rw [kronMat_fin1 M M, kronMat_fin1 (M * M) M]

/-- `cubePart ω` of a `1 × 1` idempotent vanishes. -/
private lemma cubePart_omega_snd (M : Matrix (Fin 1) (Fin 1) A) :
    (cubePart omega (⟨1, M⟩ : Mat A)).2 = 0 := by
  change kronMat (kronMat M M) M *
    (algebraMap ℂ A (1/3) • (1 + algebraMap ℂ A omega⁻¹ • (cycPerm 1).permMatrix A
      + algebraMap ℂ A (omega⁻¹ ^ 2) • ((cycPerm 1).permMatrix A * (cycPerm 1).permMatrix A)))
      = 0
  rw [cycPerm_one_eq, Matrix.permMatrix_refl, Matrix.mul_one, cube_bracket_omega, smul_zero,
    Matrix.mul_zero]

end

namespace Dim2U

theorem unit_projectors {A : Type} [Ring A] [Algebra ℂ A] :
    Work.KT.sq2Part (1 : ℂ) (Work.KT.Mat.one A 1) = Work.KT.Mat.one A 1 ∧
      Work.KT.sq2Part (-1 : ℂ) (Work.KT.Mat.one A 1) =
        (⟨1, (0 : Matrix (Fin 1) (Fin 1) A)⟩ : Work.KT.Mat A) ∧
      Work.KT.cubePart (1 : ℂ) (Work.KT.Mat.one A 1) = Work.KT.Mat.one A 1 ∧
      Work.KT.cubePart Work.KT.omega (Work.KT.Mat.one A 1) =
        (⟨1, (0 : Matrix (Fin 1) (Fin 1) A)⟩ : Work.KT.Mat A) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show sq2Part (1:ℂ) (⟨1, (1 : Matrix (Fin 1) (Fin 1) A)⟩ : Mat A)
      = (⟨1, (1 : Matrix (Fin 1) (Fin 1) A)⟩ : Mat A)
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      simpa using sq2Part_one_snd (A := A) (1 : Matrix (Fin 1) (Fin 1) A)
  · show sq2Part (-1:ℂ) (⟨1, (1 : Matrix (Fin 1) (Fin 1) A)⟩ : Mat A)
      = (⟨1, (0 : Matrix (Fin 1) (Fin 1) A)⟩ : Mat A)
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      exact sq2Part_neg_one_snd (A := A) (1 : Matrix (Fin 1) (Fin 1) A)
  · show cubePart (1:ℂ) (⟨1, (1 : Matrix (Fin 1) (Fin 1) A)⟩ : Mat A)
      = (⟨1, (1 : Matrix (Fin 1) (Fin 1) A)⟩ : Mat A)
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      simpa using cubePart_one_snd (A := A) (1 : Matrix (Fin 1) (Fin 1) A)
  · show cubePart omega (⟨1, (1 : Matrix (Fin 1) (Fin 1) A)⟩ : Mat A)
      = (⟨1, (0 : Matrix (Fin 1) (Fin 1) A)⟩ : Mat A)
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      exact cubePart_omega_snd (A := A) (1 : Matrix (Fin 1) (Fin 1) A)

end Dim2U

end Work.KT.D2UP

namespace Work.KT.D2PR

open Matrix

noncomputable section

/-- In `K₀`, the class of the zero matrix of any size is `0`. -/
theorem cls_zeroMat {A : Type} [Ring A] (n : ℕ) :
    cls (⟨n, (0 : Matrix (Fin n) (Fin n) A)⟩ : Mat A) = 0 := by
  have hidem : ∀ m : ℕ, Mat.IsIdem (⟨m, (0 : Matrix (Fin m) (Fin m) A)⟩ : Mat A) := by
    intro m
    show (0 : Matrix (Fin m) (Fin m) A) * 0 = 0
    rw [Matrix.mul_zero]
  have h0 : cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) A)⟩ : Mat A) = 0 := by
    have hs := cls_sum (hidem 0) (hidem 0)
    have hsum : (Mat.sum (⟨0, (0 : Matrix (Fin 0) (Fin 0) A)⟩ : Mat A)
        (⟨0, (0 : Matrix (Fin 0) (Fin 0) A)⟩ : Mat A)) =
        (⟨0, (0 : Matrix (Fin 0) (Fin 0) A)⟩ : Mat A) := by
      refine Sigma.ext rfl (heq_of_eq ?_)
      ext i
      exact Fin.elim0 i
    rw [hsum] at hs
    have h' : cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) A)⟩ : Mat A) + 0 =
        cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) A)⟩ : Mat A) +
          cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) A)⟩ : Mat A) := by
      rw [add_zero]; exact hs
    exact (add_left_cancel h').symm
  have hmvn : Mat.MvN (⟨n, (0 : Matrix (Fin n) (Fin n) A)⟩ : Mat A)
      (⟨0, (0 : Matrix (Fin 0) (Fin 0) A)⟩ : Mat A) := by
    refine ⟨0, 0, ?_, ?_⟩
    · show (0 : Matrix (Fin n) (Fin 0) A) * (0 : Matrix (Fin 0) (Fin n) A) = 0
      rw [Matrix.mul_zero]
    · show (0 : Matrix (Fin 0) (Fin n) A) * (0 : Matrix (Fin n) (Fin 0) A) = 0
      rw [Matrix.mul_zero]
  rw [cls_eq_of_mvN (hidem n) (hidem 0) hmvn, h0]

/-- The trivial bundle `1₁` of rank one is idempotent. -/
theorem one_isIdem {A : Type} [Ring A] (n : ℕ) : Mat.IsIdem (Mat.one A n) := by
  unfold Mat.IsIdem Mat.one
  rw [Matrix.one_mul]

/-- The Adams operations on the reduced class of a `2 × 2` idempotent `p` of "rank one": if
`p` is idempotent of trace `1`, satisfies the rank-one identity
`p i l * p j k = p i k * p j l` entrywise (equivalently `(p ⊗ p) · swap = p ⊗ p`, so that the
symmetric/antisymmetric and cyclic projectors act trivially on `p ⊗ p` and `p ⊗ p ⊗ p`), and if
`p ⊗ p ⊕ 1` is MvN to `p ⊕ p` (the Bott relation), then for every `ψ²` (resp. `ψ³`) one has
`ψ (cls p - 1) = 2 • (cls p - 1)` (resp. `= 3 • (cls p - 1)`). -/
theorem psi_rank_one {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (p : Matrix (Fin 2) (Fin 2) A) (hp : p * p = p) (htr : p 0 0 + p 1 1 = 1)
    (h1 : ∀ i j k l : Fin 2, p i l * p j k = p i k * p j l)
    (hmv : Work.KT.Mat.MvN
      (Work.KT.Mat.sum
        (Work.KT.Mat.kron (⟨2, p⟩ : Work.KT.Mat A) (⟨2, p⟩ : Work.KT.Mat A))
        (Work.KT.Mat.one A 1))
      (Work.KT.Mat.sum (⟨2, p⟩ : Work.KT.Mat A) (⟨2, p⟩ : Work.KT.Mat A))) :
    (∀ ψ : Work.KT.K0 A →+ Work.KT.K0 A, Work.KT.IsPsi2 ψ →
      ψ (Work.KT.cls (⟨2, p⟩ : Work.KT.Mat A) - Work.KT.cls (Work.KT.Mat.one A 1)) =
        2 • (Work.KT.cls (⟨2, p⟩ : Work.KT.Mat A) - Work.KT.cls (Work.KT.Mat.one A 1))) ∧
    (∀ ψ : Work.KT.K0 A →+ Work.KT.K0 A, Work.KT.IsPsi3 ψ →
      ψ (Work.KT.cls (⟨2, p⟩ : Work.KT.Mat A) - Work.KT.cls (Work.KT.Mat.one A 1)) =
        3 • (Work.KT.cls (⟨2, p⟩ : Work.KT.Mat A) - Work.KT.cls (Work.KT.Mat.one A 1))) := by
  obtain ⟨hSQ1, hSQm, hCU1, hCUw⟩ := Work.KT.Dim2.rankOne_projectors p h1
  obtain ⟨hUN1, hUNm, hUNc, hUNw⟩ := Work.KT.D2UP.Dim2U.unit_projectors (A := A)
  have hpM : Mat.IsIdem (⟨2, p⟩ : Mat A) := show p * p = p from hp
  have hqidem : Mat.IsIdem (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A)) :=
    Mat.kron_idem hA hpM hpM
  have hridem : Mat.IsIdem (Mat.kron (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A))
      (⟨2, p⟩ : Mat A)) := Mat.kron_idem hA hqidem hpM
  have honeidem : Mat.IsIdem (Mat.one A 1) := one_isIdem 1
  -- the Bott relation for `p ⊗ p`
  have hbott : cls (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A)) + cls (Mat.one A 1) =
      cls (⟨2, p⟩ : Mat A) + cls (⟨2, p⟩ : Mat A) := by
    have h1' : cls (Mat.sum (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A)) (Mat.one A 1)) =
        cls (Mat.sum (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A)) :=
      cls_eq_of_mvN (Mat.sum_idem hqidem honeidem) (Mat.sum_idem hpM hpM) hmv
    rw [cls_sum hqidem honeidem, cls_sum hpM hpM] at h1'
    exact h1'
  have hq : cls (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A)) =
      cls (⟨2, p⟩ : Mat A) + cls (⟨2, p⟩ : Mat A) - cls (Mat.one A 1) :=
    eq_sub_iff_add_eq.mpr hbott
  -- `ψ²` on `p`
  have hpsi2p : ∀ ψ : K0 A →+ K0 A, IsPsi2 ψ →
      ψ (cls (⟨2, p⟩ : Mat A)) = cls (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A)) := by
    intro ψ hψ
    rw [hψ (⟨2, p⟩ : Mat A)]
    unfold psi2Cls
    rw [if_pos hpM, hSQ1, hSQm, cls_zeroMat (2 * 2), sub_zero]
  -- `ψ²` on the unit
  have hpsi2one : ∀ ψ : K0 A →+ K0 A, IsPsi2 ψ →
      ψ (cls (Mat.one A 1)) = cls (Mat.one A 1) := by
    intro ψ hψ
    rw [hψ (Mat.one A 1)]
    unfold psi2Cls
    rw [if_pos honeidem, hUN1, hUNm, cls_zeroMat 1, sub_zero]
  -- `ψ³` on `p`
  have hpsi3p : ∀ ψ : K0 A →+ K0 A, IsPsi3 ψ →
      ψ (cls (⟨2, p⟩ : Mat A)) =
        cls (Mat.kron (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A)) (⟨2, p⟩ : Mat A)) := by
    intro ψ hψ
    rw [hψ (⟨2, p⟩ : Mat A)]
    unfold psi3Cls
    rw [if_pos hpM, hCU1, hCUw, cls_zeroMat (2 * 2 * 2), sub_zero]
  -- `ψ³` on the unit
  have hpsi3one : ∀ ψ : K0 A →+ K0 A, IsPsi3 ψ →
      ψ (cls (Mat.one A 1)) = cls (Mat.one A 1) := by
    intro ψ hψ
    rw [hψ (Mat.one A 1)]
    unfold psi3Cls
    rw [if_pos honeidem, hUNc, hUNw, cls_zeroMat 1, sub_zero]
  -- the second Bott relation, obtained by tensoring the first one with `p`
  have hstep1 : Mat.MvN
      (Mat.kron (Mat.sum (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A)) (Mat.one A 1))
        (⟨2, p⟩ : Mat A))
      (Mat.kron (Mat.sum (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A)) (⟨2, p⟩ : Mat A)) :=
    mvN_kron_left hA hmv hpM
  have hstep2 : Mat.MvN
      (Mat.kron (Mat.sum (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A)) (Mat.one A 1))
        (⟨2, p⟩ : Mat A))
      (Mat.sum (Mat.kron (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A)) (⟨2, p⟩ : Mat A))
        (Mat.kron (Mat.one A 1) (⟨2, p⟩ : Mat A))) :=
    mvN_sum_kron 4 1 2 (kronMat p p) (1 : Matrix (Fin 1) (Fin 1) A) p
  have hstep3 : Mat.MvN
      (Mat.kron (Mat.sum (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A)) (⟨2, p⟩ : Mat A))
      (Mat.sum (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A))
        (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A))) :=
    mvN_sum_kron 2 2 2 p p p
  have hidemA : Mat.IsIdem (Mat.kron (Mat.sum (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A))
      (Mat.one A 1)) (⟨2, p⟩ : Mat A)) :=
    Mat.kron_idem hA (Mat.sum_idem hqidem honeidem) hpM
  have hidemB : Mat.IsIdem (Mat.kron (Mat.sum (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A))
      (⟨2, p⟩ : Mat A)) := Mat.kron_idem hA (Mat.sum_idem hpM hpM) hpM
  have hidemC : Mat.IsIdem (Mat.sum (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A))
      (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A))) := Mat.sum_idem hqidem hqidem
  have hidemE : Mat.IsIdem (Mat.sum (Mat.kron (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A))
      (⟨2, p⟩ : Mat A)) (Mat.kron (Mat.one A 1) (⟨2, p⟩ : Mat A))) :=
    Mat.sum_idem hridem (Mat.kron_idem hA honeidem hpM)
  have hchain : Mat.MvN
      (Mat.kron (Mat.sum (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A)) (Mat.one A 1))
        (⟨2, p⟩ : Mat A))
      (Mat.sum (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A))
        (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A))) :=
    Mat.mvN_trans hidemA hidemB hidemC hstep1 hstep3
  have e1 : cls (Mat.kron (Mat.sum (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A))
        (Mat.one A 1)) (⟨2, p⟩ : Mat A)) =
      cls (Mat.sum (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A))
        (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A))) :=
    cls_eq_of_mvN hidemA hidemC hchain
  have e2 : cls (Mat.kron (Mat.sum (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A))
        (Mat.one A 1)) (⟨2, p⟩ : Mat A)) =
      cls (Mat.sum (Mat.kron (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A))
        (⟨2, p⟩ : Mat A)) (Mat.kron (Mat.one A 1) (⟨2, p⟩ : Mat A))) :=
    cls_eq_of_mvN hidemA hidemE hstep2
  have key : cls (Mat.sum (Mat.kron (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A))
        (⟨2, p⟩ : Mat A)) (Mat.kron (Mat.one A 1) (⟨2, p⟩ : Mat A))) =
      cls (Mat.sum (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A))
        (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A))) := e2.symm.trans e1
  have honep : cls (Mat.kron (Mat.one A 1) (⟨2, p⟩ : Mat A)) = cls (⟨2, p⟩ : Mat A) :=
    cls_eq_of_mvN (Mat.kron_idem hA honeidem hpM) hpM (mvNassoc_kron_unit (⟨2, p⟩ : Mat A))
  have hsplit : cls (Mat.kron (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A)) (⟨2, p⟩ : Mat A)) +
      cls (Mat.kron (Mat.one A 1) (⟨2, p⟩ : Mat A)) =
      cls (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A)) +
        cls (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A)) := by
    rw [← cls_sum hridem (Mat.kron_idem hA honeidem hpM), ← cls_sum hqidem hqidem]
    exact key
  have hrbott : cls (Mat.kron (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A)) (⟨2, p⟩ : Mat A)) =
      3 • cls (⟨2, p⟩ : Mat A) - 2 • cls (Mat.one A 1) := by
    have h := hsplit
    rw [honep, hq] at h
    have h2 : cls (Mat.kron (Mat.kron (⟨2, p⟩ : Mat A) (⟨2, p⟩ : Mat A)) (⟨2, p⟩ : Mat A)) =
        ((cls (⟨2, p⟩ : Mat A) + cls (⟨2, p⟩ : Mat A) - cls (Mat.one A 1)) +
          (cls (⟨2, p⟩ : Mat A) + cls (⟨2, p⟩ : Mat A) - cls (Mat.one A 1))) -
            cls (⟨2, p⟩ : Mat A) := eq_sub_iff_add_eq.mpr h
    rw [h2]
    abel
  constructor
  · intro ψ hψ
    rw [map_sub, hpsi2p ψ hψ, hpsi2one ψ hψ, hq, smul_sub]
    abel
  · intro ψ hψ
    rw [map_sub, hpsi3p ψ hψ, hpsi3one ψ hψ, hrbott, smul_sub]
    abel

end

end Work.KT.D2PR

