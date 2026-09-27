import Mathlib
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.FP.PadDefs
import Submission.Work.KT.FP.lindDefs
import Submission.Work.KT.FP.wPen_admissible
import Submission.Work.KT.FP.wPen_isUnit_of_sum_isUnit

/-!
# `Work.KT.FP.lindAt_adm_mono` — monotonicity of the admissibility bound in the degree bound

If a Laurent matrix `P` over `C(X, ℂ)` has all its coefficients in degrees `[-m, m]`, then
`z^m P(z)` is the polynomial matrix `∑_j z^j • (coeffSeq X n m P j)` carried by the coefficient
sequence `coeffSeq X n m P` of length `2m+1`.  Increasing the degree bound `m ↦ M ≥ m` merely
multiplies this polynomial by the unit `z^{M-m}`:

`penQ X n (2*M) (coeffSeq X n M P) z = z^{M-m} • penQ X n (2*m) (coeffSeq X n m P) z`.

Since the companion pencil `z • wPenAf + wPenBf b` is a unit exactly where the polynomial matrix
`∑_j z^j • b_j` is (`wPen_isUnit_of_sum_isUnit` for the forward direction, `penQ_isUnit_of_pencil`
for the converse, which is the kernel correspondence `wPen_kernel`), invertibility of the pencil on
an annulus `ρ ≤ ‖z‖ ≤ 1` with `ρ > 0` is inherited from the degree bound `m` to any larger bound
`M`.  This is the monotonicity of the "admissible" hypothesis used in `Work.KT.FP.lindAt_pad`.
-/

namespace Work.KT.FP

open Matrix

noncomputable section

set_option linter.unusedVariables false

/-- Reindexing commutes with entrywise mapping of a matrix. -/
theorem map_reindex_adm {A B : Type*} {ι κ : Type*} (e : ι ≃ κ) (M : Matrix ι ι A) (g : A → B) :
    (Matrix.reindex e e M).map g = Matrix.reindex e e (M.map g) := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]

/-- **Converse of the companion-pencil linearisation.** If the W pencil `z • wPenAf + wPenBf c` is
a unit then so is the polynomial matrix `penQ X n d c z = ∑_j z^j • c_j` carried by the coefficient
sequence `c`.  This is the pointwise form of the kernel correspondence `wPen_kernel`. -/
theorem penQ_isUnit_of_pencil (X : Type) [TopologicalSpace X] (n d : ℕ)
    (c : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (z : ℂ)
    (h : IsUnit (z • wPenAf X n d + wPenBf X n d c)) :
    IsUnit (penQ X n d c z) := by
  rw [isUnit_matrix_iff_forall_eval]
  intro x
  have hflat := (isUnit_matrix_iff_forall_eval ((d + 1) * n)
      (z • wPenAf X n d + wPenBf X n d c)).mp h x
  have hkey : z • wPenAf X n d + wPenBf X n d c
      = Matrix.reindex finProdFinEquiv finProdFinEquiv
          (z • wPenA X n d + wPenB X n d c) := by
    simp only [wPenAf, wPenBf, Matrix.reindex_apply, Matrix.submatrix_add, Matrix.submatrix_smul,
      Pi.add_apply, Pi.smul_apply]
  rw [hkey, map_reindex_adm] at hflat
  have hblk : IsUnit ((z • wPenA X n d + wPenB X n d c).map (fun f => f x)) :=
    (isUnit_reindex finProdFinEquiv _).mp hflat
  have hsplit : (z • wPenA X n d + wPenB X n d c).map (fun f => f x)
      = z • (wPenA X n d).map (fun f => f x) + (wPenB X n d c).map (fun f => f x) := by
    rw [Matrix.map_add (fun f : C(X, ℂ) => f x) (fun a b => map_add (Work.KT.evalC x) a b),
      Matrix.map_smul (fun f : C(X, ℂ) => f x) z (fun a => map_smul (Work.KT.evalC x) z a)]
  rw [hsplit] at hblk
  have hmap : (penQ X n d c z).map (fun f => f x)
      = ∑ j : Fin (d + 1), z ^ (j:ℕ) • (c j).map (fun f => f x) := by
    ext a b
    rw [penQ_map_eval, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.smul_apply, Matrix.map_apply]
    simp [smul_eq_mul]
  rw [isUnit_iff_mulVec_eq_zero] at hblk
  rw [hmap, isUnit_iff_mulVec_eq_zero]
  intro w hw
  exact (wPen_kernel n d z (fun j => (c j).map (fun f => f x)) _ _
      (fun i j => wPenA_map_apply X n d x i j)
      (fun i j => wPenB_map_apply X n d c x i j)).mp hblk w hw

/-- **The padded coefficient sum.**  For a sequence `w : ℤ → ℂ` vanishing outside `[-m, m]`, the
coefficient sum over the degree bound `M ≥ m` is `z^{M-m}` times the coefficient sum over the
degree bound `m`. -/
lemma sum_shift_adm (w : ℤ → ℂ) (m M : ℕ) (hmM : m ≤ M) (z : ℂ)
    (hw : ∀ k : ℤ, (m : ℤ) < k ∨ k < -(m : ℤ) → w k = 0) :
    (∑ j : Fin (2 * M + 1), z ^ (j : ℕ) * w ((j : ℤ) - (M : ℤ)))
      = z ^ (M - m) * (∑ j : Fin (2 * m + 1), z ^ (j : ℕ) * w ((j : ℤ) - (m : ℤ))) := by
  set f : Fin (2 * M + 1) → ℂ := fun j => z ^ (j : ℕ) * w ((j : ℤ) - (M : ℤ)) with hf
  set φ : Fin (2 * m + 1) → Fin (2 * M + 1) :=
    fun j' => ⟨M - m + (j' : ℕ), by have := j'.isLt; omega⟩ with hphi
  have hinj : Set.InjOn φ (Finset.univ : Finset (Fin (2 * m + 1))) := by
    intro a _ b _ hab
    have h := congrArg Fin.val hab
    simp only [hphi] at h
    exact Fin.ext (by omega)
  have hf0 : ∀ j : Fin (2 * M + 1), j ∉ (Finset.univ.image φ) → f j = 0 := by
    intro j hj
    have hcase : (j : ℕ) < M - m ∨ M + m < (j : ℕ) := by
      by_contra hc
      rw [not_or, not_lt, not_lt] at hc
      exact hj (Finset.mem_image.mpr ⟨⟨(j : ℕ) - (M - m), by omega⟩,
        Finset.mem_univ _, Fin.ext (by simp only [hphi]; omega)⟩)
    change z ^ (j : ℕ) * w ((j : ℤ) - (M : ℤ)) = 0
    have hwz : w ((j : ℤ) - (M : ℤ)) = 0 := by
      apply hw
      rcases hcase with h | h
      · right
        have h2 : ((j : ℕ) : ℤ) + (m : ℤ) < (M : ℤ) := by
          have : (j : ℕ) + m < M := by omega
          exact_mod_cast this
        linarith
      · left
        have h2 : (M : ℤ) + (m : ℤ) < ((j : ℕ) : ℤ) := by
          exact_mod_cast h
        linarith
    rw [hwz, mul_zero]
  have hstep1 : (∑ j : Fin (2 * M + 1), f j) = ∑ j ∈ (Finset.univ.image φ), f j :=
    (Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => hf0 x hx)).symm
  have hstep2 : (∑ j ∈ (Finset.univ.image φ), f j) = ∑ j' : Fin (2 * m + 1), f (φ j') :=
    Finset.sum_image hinj
  have hterm : ∀ j' : Fin (2 * m + 1),
      f (φ j') = z ^ (M - m) * (z ^ (j' : ℕ) * w ((j' : ℤ) - (m : ℤ))) := by
    intro j'
    have hexp : (((M - m + (j' : ℕ) : ℕ) : ℤ) - (M : ℤ)) = ((j' : ℕ) : ℤ) - (m : ℤ) := by
      rw [Nat.cast_add, Nat.cast_sub hmM]
      ring
    change z ^ (M - m + (j' : ℕ)) * w (((M - m + (j' : ℕ) : ℕ) : ℤ) - (M : ℤ))
        = z ^ (M - m) * (z ^ (j' : ℕ) * w ((j' : ℤ) - (m : ℤ)))
    rw [pow_add, hexp]
    ring
  have hstep3 : (∑ j' : Fin (2 * m + 1), f (φ j'))
      = z ^ (M - m) * ∑ j' : Fin (2 * m + 1),
          (z ^ (j' : ℕ) * w ((j' : ℤ) - (m : ℤ))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j' _ => hterm j')
  rw [hstep1, hstep2, hstep3]

/-- **The matrix identity for the padded coefficient sum.**  If all coefficients of the Laurent
matrix `P` lie in degrees `[-m, m]` and `m ≤ M`, the polynomial matrices carried by the coefficient
sequences `coeffSeq X n m P` and `coeffSeq X n M P` differ by the scalar factor `z^{M-m}`. -/
lemma penQ_shift_adm (X : Type) [TopologicalSpace X]
    (n m M : ℕ) (hmM : m ≤ M)
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
    (hb : ∀ (i j : Fin n) (k : ℤ), (m:ℤ) < k ∨ k < -(m:ℤ) → (P i j).coeff k = 0)
    (z : ℂ) :
    penQ X n (2*M) (coeffSeq X n M P) z
      = (z ^ (M - m)) • penQ X n (2*m) (coeffSeq X n m P) z := by
  ext a b x
  have hL : (penQ X n (2*M) (coeffSeq X n M P) z a b) x
      = ∑ j : Fin (2*M+1), z^(j:ℕ) * ((P a b).coeff ((j:ℤ) - (M:ℤ))) x := by
    have h := penQ_map_eval X n (2*M) (coeffSeq X n M P) z x a b
    simpa [coeffSeq] using h
  have hR : ((z ^ (M - m)) • penQ X n (2*m) (coeffSeq X n m P) z) a b x
      = z^(M-m) * ∑ j : Fin (2*m+1), z^(j:ℕ) * ((P a b).coeff ((j:ℤ) - (m:ℤ))) x := by
    rw [Matrix.smul_apply, ContinuousMap.smul_apply, smul_eq_mul]
    congr 1
    have h := penQ_map_eval X n (2*m) (coeffSeq X n m P) z x a b
    simpa [coeffSeq] using h
  rw [hL, hR]
  exact sum_shift_adm (fun k => (P a b).coeff k x) m M hmM z
    (fun k hk => by rw [hb a b k hk]; rfl)

theorem lindAt_adm_mono (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n m M : ℕ) (hmM : m ≤ M)
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
    (hb : ∀ (i j : Fin n) (k : ℤ), (m : ℤ) < k ∨ k < -(m : ℤ) → (P i j).coeff k = 0)
    {ρ : ℝ} (hρ0 : 0 < ρ)
    (hadm : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • Work.KT.FP.linAf X n m + Work.KT.FP.linBf X n m P)) :
    ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • Work.KT.FP.linAf X n M + Work.KT.FP.linBf X n M P) := by
  intro z hzρ hz1
  -- the pencil at level `m` is a unit, hence so is the polynomial `z^m P(z)`
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz] at hzρ
    simp only [norm_zero] at hzρ
    linarith
  have hQm : IsUnit (penQ X n (2*m) (coeffSeq X n m P) z) :=
    penQ_isUnit_of_pencil X n (2*m) (coeffSeq X n m P) z (hadm z hzρ hz1)
  -- it equals `z^{M-m} • (z^m P(z))`, and `z^{M-m}` is a unit, so the level-`M` polynomial is a unit
  have hQM : IsUnit (penQ X n (2*M) (coeffSeq X n M P) z) := by
    rw [penQ_shift_adm X n m M hmM P hb z]
    have hu : IsUnit (algebraMap ℂ (Matrix (Fin n) (Fin n) C(X, ℂ)) (z ^ (M - m))) :=
      (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hz0)).map (algebraMap ℂ _)
    rw [Algebra.smul_def]
    exact hu.mul hQm
  -- and the level-`M` pencil is a unit wherever its polynomial is
  exact wPen_isUnit_of_sum_isUnit X n (2*M) (coeffSeq X n M P) hz0 hQM

end

end Work.KT.FP
