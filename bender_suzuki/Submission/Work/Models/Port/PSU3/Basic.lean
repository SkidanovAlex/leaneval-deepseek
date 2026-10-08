/-
The unitary group `SU(3, 2^n)` and the projective unitary group `PSU(3, 2^n)`.

`PSU3Model n` (from `ChallengeDeps`) is the image in `PGL(3, 2^(2n))` of the group of matrices
`A` with `Aᴴ J A = J` and `det A = 1`, where `J` is the antidiagonal Hermitian form and
`Aᴴ = (Aᵀ)^(2^n)`.

In this file we set up the basic vocabulary (`herm`, `J3`, `IsSU3`) and prove that
`PSU3Model n` is nontrivial for `n ≥ 2`: the diagonal matrix
`diag(g, g^(2^n - 1), (g^(2^n))⁻¹)` (where `g` generates `GF(2^(2n))ˣ`) lies in `SU(3, 2^n)` and
is not a scalar.
-/
import Mathlib
import ChallengeDeps

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open Matrix LeanEval.GroupTheory.Defs

namespace Submission.PSU3

/-- The field `GF(2^(2n))` of definition of `PSU(3, 2^n)`. -/
abbrev F (n : ℕ) : Type := GaloisField 2 (2 * n)

/-- `Aᴴ = (Aᵀ)^(2^n)`, the `2^n`-Frobenius conjugate transpose. -/
noncomputable def herm {n : ℕ} (A : Matrix (Fin 3) (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n) :=
  Matrix.of fun i j => A j i ^ (2 ^ n)

/-- The Hermitian form with antidiagonal Gram matrix. -/
noncomputable def J3 {n : ℕ} : Matrix (Fin 3) (Fin 3) (F n) := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

/-- The special unitary group `SU(3, 2^n)` as a predicate on `GL(3, 2^(2n))`. -/
def IsSU3 {n : ℕ} (A : GL (Fin 3) (F n)) : Prop :=
  herm (A : Matrix (Fin 3) (Fin 3) (F n)) * J3 * (A : Matrix (Fin 3) (Fin 3) (F n)) = J3 ∧
    GeneralLinearGroup.det A = 1

/-- The defining generators of `PSU3Model n`. -/
theorem PSU3Model_eq (n : ℕ) :
    PSU3Model n = (Subgroup.closure {A : GL (Fin 3) (F n) | IsSU3 A}).map
      ProjGenLinGroup.mk := rfl

/-! ## The maximal torus of `SU(3, 2^n)` -/

/-- A generator of the cyclic group `GF(2^(2n))ˣ`. -/
noncomputable def gen (n : ℕ) : (F n)ˣ :=
  Classical.choose (IsCyclic.exists_generator (α := (F n)ˣ))

lemma gen_spec (n : ℕ) : Subgroup.zpowers (gen n) = ⊤ :=
  (Subgroup.eq_top_iff' (Subgroup.zpowers (gen n))).mpr
    (Classical.choose_spec (IsCyclic.exists_generator (α := (F n)ˣ)))

lemma card_F (n : ℕ) (hn : n ≠ 0) : Nat.card (F n) = 2 ^ (2 * n) :=
  GaloisField.card (p := 2) (n := 2 * n) (by omega)

lemma orderOf_gen (n : ℕ) (hn : n ≠ 0) : orderOf (gen n) = 2 ^ (2 * n) - 1 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers
      ((Subgroup.eq_top_iff' (Subgroup.zpowers (gen n))).mp (gen_spec n)),
    Nat.card_units, card_F n hn]

lemma gen_pow_card (n : ℕ) (hn : n ≠ 0) : (gen n : F n) ^ (2 ^ (2 * n) - 1) = 1 := by
  have h : (gen n) ^ (2 ^ (2 * n) - 1) = 1 := by
    rw [← orderOf_gen n hn]; exact pow_orderOf_eq_one (gen n)
  simpa using congrArg (fun u : (F n)ˣ => (u : F n)) h

/-- `2^n * 2^n = 2^(2n)`. -/
lemma sq_pow (n : ℕ) : 2 ^ n * 2 ^ n = 2 ^ (2 * n) := by
  rw [← pow_add]; ring_nf

lemma pow_card_eq_self (n : ℕ) (hn : n ≠ 0) : (gen n : F n) ^ (2 ^ (2 * n)) = (gen n : F n) := by
  rw [show 2 ^ (2 * n) = (2 ^ (2 * n) - 1) + 1 from
      (Nat.sub_add_cancel Nat.one_le_two_pow).symm,
    pow_succ, gen_pow_card n hn, one_mul]

/-- The exponent identity `(2^n - 1) * 2^n + (2^n - 1) = 2^(2n) - 1`. -/
lemma exp_identity (n : ℕ) (hn : 1 ≤ n) :
    (2 ^ n - 1) * 2 ^ n + (2 ^ n - 1) = 2 ^ (2 * n) - 1 := by
  have hsq : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hs : 1 ≤ (2 ^ n) ^ 2 := by nlinarith [h1]
  rw [hsq]
  zify [hs, h1]
  ring

/-- The diagonal element `diag(g, g^(2^n - 1), (g^(2^n))⁻¹)` of `SU(3, 2^n)`. -/
noncomputable def diagTorus (n : ℕ) : Matrix (Fin 3) (Fin 3) (F n) :=
  Matrix.diagonal ![(gen n : F n), (gen n : F n) ^ (2 ^ n - 1), ((gen n : F n) ^ (2 ^ n))⁻¹]

/-- Conjugating a diagonal matrix by `herm`. -/
lemma herm_diagonal (n : ℕ) (d : Fin 3 → F n) :
    herm (Matrix.diagonal d) = Matrix.diagonal (fun i => d i ^ (2 ^ n)) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [herm, Matrix.diagonal]
  · simp [herm, Matrix.diagonal, h, Ne.symm h]

/-- The determinant of the diagonal torus element. -/
lemma diagTorus_det (n : ℕ) : (diagTorus n).det = 1 := by
  rw [diagTorus, Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  have h1 : (gen n : F n) ≠ 0 := Units.ne_zero (gen n)
  have h2 : (gen n : F n) ^ (2 ^ n) ≠ 0 := pow_ne_zero _ h1
  rw [← pow_succ', Nat.sub_add_cancel Nat.one_le_two_pow, mul_inv_cancel₀ h2]

/-- The diagonal torus element as a unit of `GL(3, 2^(2n))`. -/
noncomputable def diagTorusGL (n : ℕ) : GL (Fin 3) (F n) :=
  Matrix.GeneralLinearGroup.mk'' (diagTorus n) (by rw [diagTorus_det]; exact isUnit_one)

@[simp] lemma diagTorusGL_coe (n : ℕ) :
    ((diagTorusGL n : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) = diagTorus n :=
  Matrix.GeneralLinearGroup.val_mk'' _ _

lemma entry02 (n : ℕ) (hn : n ≠ 0) :
    ((gen n : F n) ^ (2 ^ n)) * ((gen n : F n) ^ (2 ^ n))⁻¹ = 1 :=
  mul_inv_cancel₀ (pow_ne_zero _ (Units.ne_zero (gen n)))

lemma entry11 (n : ℕ) (hn : 1 ≤ n) :
    ((gen n : F n) ^ (2 ^ n - 1)) ^ (2 ^ n) * (gen n : F n) ^ (2 ^ n - 1) = 1 := by
  rw [← pow_mul, ← pow_add, exp_identity n hn]
  exact gen_pow_card n (by omega)

lemma entry20 (n : ℕ) (hn : 1 ≤ n) :
    (((gen n : F n) ^ (2 ^ n)) ^ (2 ^ n))⁻¹ * (gen n : F n) = 1 := by
  rw [← pow_mul, sq_pow, pow_card_eq_self n (by omega),
    inv_mul_cancel₀ (Units.ne_zero (gen n))]

lemma diagTorus_isSU3 (n : ℕ) (hn : 1 ≤ n) : IsSU3 (diagTorusGL n) := by
  refine ⟨?_, ?_⟩
  · simp only [diagTorusGL_coe]
    rw [diagTorus, herm_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [J3, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_three,
        entry02 n (by omega), entry11 n hn, entry20 n hn]
  · show GeneralLinearGroup.det (diagTorusGL n) = 1
    apply Units.ext
    show ((diagTorusGL n : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)).det = 1
    rw [diagTorusGL_coe, diagTorus_det]

/-! ## Nontriviality of `PSU(3, 2^n)` -/

/-- The diagonal torus element is not a scalar. -/
lemma diagTorusGL_not_center (n : ℕ) (hn : 2 ≤ n) :
    diagTorusGL n ∉ Subgroup.center (GL (Fin 3) (F n)) := by
  intro h
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp h
  have h00 : ((diagTorusGL n : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) 0 0 = (u : F n) := by
    rw [← hu]; simp [Matrix.scalar_apply]
  have h11 : ((diagTorusGL n : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) 1 1 = (u : F n) := by
    rw [← hu]; simp [Matrix.scalar_apply]
  rw [diagTorusGL_coe] at h00 h11
  simp only [diagTorus, Matrix.diagonal_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one,
    ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h00 h11
  -- hg : g = g^(2^n - 1)
  have hg : (gen n : F n) = (gen n : F n) ^ (2 ^ n - 1) := by
    rw [h11, h00]
  -- hence g^(2^n - 2) = 1
  have hgpow : (gen n) ^ (2 ^ n - 2) = 1 := by
    refine Units.ext ?_
    have h2 : 2 ≤ 2 ^ n := by
      calc (2:ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsplit : 2 ^ n - 2 + 1 = 2 ^ n - 1 := by omega
    have h2 : (gen n : F n) ^ (2 ^ n - 2) * (gen n : F n) = (gen n : F n) ^ (2 ^ n - 1) := by
      rw [← pow_succ, hsplit]
    have h3 : (gen n : F n) ^ (2 ^ n - 2) = 1 := by
      refine mul_right_cancel₀ (Units.ne_zero (gen n)) ?_
      rw [one_mul]
      exact h2.trans hg.symm
    simpa using h3
  -- but the order of g is 2^(2n) - 1 > 2^n - 2 ≥ 1
  have hdvd : 2 ^ (2 * n) - 1 ∣ 2 ^ n - 2 := by
    rw [← orderOf_gen n (by omega)]
    exact orderOf_dvd_iff_pow_eq_one.mpr hgpow
  have hpos : 0 < 2 ^ n - 2 := by
    have : 4 ≤ 2 ^ n := by
      calc (4:ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hlt : 2 ^ n - 2 < 2 ^ (2 * n) - 1 := by
    have hle : 2 ^ n ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
    omega
  exact absurd hdvd (Nat.not_dvd_of_pos_of_lt hpos hlt)

/-- `PSU(3, 2^n)` is nontrivial for `n ≥ 2`. -/
theorem psu3Model_ne_bot (n : ℕ) (hn : 2 ≤ n) : PSU3Model n ≠ ⊥ := by
  intro hbot
  have hmem : ProjGenLinGroup.mk (diagTorusGL n) ∈ PSU3Model n := by
    rw [PSU3Model_eq]
    exact Subgroup.mem_map_of_mem _
      (Subgroup.subset_closure (diagTorus_isSU3 n (by omega)))
  rw [hbot, Subgroup.mem_bot] at hmem
  exact diagTorusGL_not_center n hn ((ProjGenLinGroup.mk_eq_one).mp hmem)

end Submission.PSU3
