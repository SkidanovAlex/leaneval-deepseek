import Mathlib
import Submission.Commons.Lattice.Counting.finite_pure_sublattices_gram
import Submission.Commons.Lattice.Counting.finite_submodules_between_nsmul
import Submission.Commons.Lattice.Counting.smul_mem_span_of_dvd
import Submission.Commons.Lattice.Counting.pure_span_subfamily
import Submission.Commons.GroupTheory.Hopfian.finite_addSubgroups_of_index_le
import Submission.Commons.LinearAlgebra.Matrix.gram_det_eq_of_span_eq
import Submission.Commons.LinearAlgebra.Matrix.gram_det_ge_submatrix_det_sq
import Submission.Commons.LinearAlgebra.Matrix.det_map_int_real
import Submission.Commons.LinearAlgebra.Matrix.exists_submatrix_det_ne_zero_of_cols_linearIndependent
import Submission.Commons.Lattice.Module.generators_basis_of_finrank

open Module Matrix
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.Lattice.Counting

/-! ## Real Gram determinants of integer matrices -/

/-- map an integer matrix to real -/
def rM {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℤ) : Matrix (Fin n) (Fin r) ℝ :=
  A.map (fun z : ℤ => (z : ℝ))

/-- The real Gram determinant `det(AᵀA)` of an integer matrix `A` (entries cast to ℝ). -/
def gramReal {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℤ) : ℝ :=
  ((rM A).transpose * (rM A)).det

@[simp] lemma map_mul_int_real {n k r : ℕ} (A : Matrix (Fin n) (Fin k) ℤ) (B : Matrix (Fin k) (Fin r) ℤ) :
    rM (A * B) = rM A * rM B := by
  ext i j
  simp [rM, Matrix.mul_apply]

@[simp] lemma map_transpose_int_real {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℤ) :
    rM A.transpose = (rM A).transpose := by
  ext i j
  rfl

@[simp] lemma det_rM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : (rM A).det = (A.det : ℤ) := by
  rw [rM]
  rw [← Int.cast_det A]

/-- Gram determinant of `W * P` in terms of `W` (real matrices). -/
lemma det_gram_mul_right {n r : ℕ} (W : Matrix (Fin n) (Fin r) ℝ) (P : Matrix (Fin r) (Fin r) ℝ) :
    ((W * P).transpose * (W * P)).det = P.det ^ 2 * (W.transpose * W).det := by
  calc
    ((W * P).transpose * (W * P)).det
        = (P.transpose * (W.transpose * W) * P).det := by
            rw [Matrix.transpose_mul]
            simp [Matrix.mul_assoc]
    _ = P.det ^ 2 * (W.transpose * W).det := by
            rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
            ring

/-- Gram-determinant under an integer column change: `gramReal (U * P) = (det P)² * gramReal U`. -/
lemma gramReal_mul_right {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℤ) (P : Matrix (Fin r) (Fin r) ℤ) :
    gramReal (U * P) = (rM P).det ^ 2 * gramReal U := by
  unfold gramReal
  rw [map_mul_int_real U P]
  exact det_gram_mul_right (W := rM U) (P := rM P)

/-- Gram determinant of the family with columns scaled by the integers `a i`. -/
lemma gramReal_diag_scale {n r : ℕ} (V : Matrix (Fin n) (Fin r) ℤ) (a : Fin r → ℤ) :
    gramReal (V * Matrix.diagonal a) = (∏ i : Fin r, (a i : ℝ)) ^ 2 * gramReal V := by
  rw [gramReal_mul_right]
  have hdet : (rM (Matrix.diagonal a)).det = (∏ i : Fin r, (a i : ℝ)) := by
    rw [det_rM]
    rw [Matrix.det_diagonal]
    rw [Int.cast_prod]
  rw [hdet]

/-! ## Smith-normal-form decomposition of a sublattice of `ℤⁿ`

Every rank-`r` submodule `M ≤ ℤⁿ` has a basis `bN` such that relative to some integral basis
`eO` of `ℤⁿ` the basis vectors are `a i`-multiples of the vectors `eO (emb i)`, with `emb`
an embedding of `Fin r` into the (arbitrary) index type of `eO`. -/
lemma snf_structure {n r : ℕ} (M : Submodule ℤ (E n))
    (hfr : Module.finrank ℤ M = r) :
    ∃ (o : ℕ) (eO : Basis (Fin o) ℤ (E n)) (emb : Fin r ↪ Fin o)
      (bN : Basis (Fin r) ℤ M) (a : Fin r → ℤ),
      ((∀ i : Fin r, (bN i : E n) = a i • (eO (emb i) : E n)) ∧
       (∀ i : Fin r, a i ≠ 0)) := by
  classical
  let b0 : Basis (Fin n) ℤ (E n) := Pi.basisFun ℤ (Fin n)
  rcases Submodule.exists_smith_normal_form_of_le b0 M (⊤ : Submodule ℤ (E n)) le_top with
    ⟨n0, o, hno, bO, bN0, a0, hsnf⟩
  have h1 : Module.finrank ℤ M = n0 := by
    simpa using (Module.finrank_eq_card_basis (R := ℤ) bN0)
  have hn0r : n0 = r := by omega
  let φ : Fin r ≃ Fin n0 := finCongr hn0r.symm
  let eO : Basis (Fin o) ℤ (E n) := bO.map (LinearEquiv.ofTop (⊤ : Submodule ℤ (E n)) rfl)
  let emb : Fin r ↪ Fin o :=
    { toFun := fun k => Fin.castLE hno (φ k)
      inj' := by
        intro a b hab
        apply Fin.ext
        have hv := congrArg Fin.val hab
        simp at hv ⊢
        exact hv }
  let bN : Basis (Fin r) ℤ M := bN0.reindex φ.symm
  let a : Fin r → ℤ := fun i => a0 (φ i)
  refine ⟨o, eO, emb, bN, a, ?_, ?_⟩
  · intro i
    have h := hsnf (φ i)
    change (bN0 (φ i) : E n) = a i • (eO (emb i) : E n) at h
    calc
      (bN i : E n) = (bN0 (φ i) : E n) := by
        dsimp [bN]
        simp
      _ = a i • (eO (emb i) : E n) := by
        simpa [a, emb, eO] using h
  · intro i
    by_contra hzero
    dsimp [a] at hzero
    have hrel : (bN0 (φ i) : E n) = 0 := by
      have h := hsnf (φ i)
      simpa [hzero] using h
    exact (Basis.ne_zero bN0 (φ i)) (Subtype.ext hrel)

/-! ## The set under study -/

/-- The set of rank-`r` submodules of `ℤⁿ` admitting a generating witness matrix `A` with
Gram determinant at most `B`.  (This is exactly the set appearing in the statement of
`finite_sublattices_int_count`.) -/
def LatSet (n r : ℕ) (B : ℝ) : Set (Submodule ℤ (E n)) :=
  {M | Module.finrank ℤ M = r ∧
    ∃ A : Matrix (Fin n) (Fin r) ℤ,
      (∀ j : Fin r, (fun i : Fin n => A i j) ∈ M) ∧
      (∀ ⦃x : E n⦄, x ∈ M →
        x ∈ Submodule.span ℤ (Set.range (fun j : Fin r => fun i : Fin n => A i j))) ∧
      gramReal A ≤ B}

/-- The pure analogue (already known to be finite): rank `r`, saturated, with a witness of
bounded Gram determinant having a full-rank minor. -/
def PureLatSet (n r : ℕ) (B : ℝ) : Set (Submodule ℤ (E n)) :=
  {M | Module.finrank ℤ M = r ∧
    (∀ x : E n, (∃ a : ℤ, a ≠ 0 ∧ a • x ∈ M) → x ∈ M) ∧
    ∃ A : Matrix (Fin n) (Fin r) ℤ,
      (∀ j : Fin r, (fun i : Fin n => A i j) ∈ M) ∧
      (∃ e : Fin r ↪ Fin n, (A.submatrix e (fun j : Fin r => j)).det ≠ 0) ∧
      gramReal A ≤ B}

/-- The pure set is finite (this is `finite_pure_sublattices_gram`). -/
lemma pureLatSet_finite (n r : ℕ) (B : ℝ) : (PureLatSet n r B).Finite := by
  classical
  exact finite_pure_sublattices_gram (n := n) (r := r) (B := B)

/-- A witness matrix of a rank-`r` lattice has independent columns, hence a full-rank
`r × r` submatrix with nonzero determinant. -/
lemma witness_full_minor {n r : ℕ} (M : Submodule ℤ (E n))
    (hfr : Module.finrank ℤ M = r) (A : Matrix (Fin n) (Fin r) ℤ)
    (hAcol : ∀ j : Fin r, A.col j ∈ M)
    (hAspan : ∀ ⦃x : E n⦄, x ∈ M → x ∈ Submodule.span ℤ (Set.range A.col)) :
    ∃ e : Fin r ↪ Fin n, (A.submatrix e (fun j : Fin r => j)).det ≠ 0 := by
  classical
  have hli : LinearIndependent ℤ (fun j : Fin r => A.col j) :=
    Commons.Lattice.Module.generators_basis_of_finrank (E := E n) M hfr
      (fun j : Fin r => A.col j) hAcol
      (by intro x hx; exact hAspan hx)
  exact Commons.LinearAlgebra.Matrix.exists_submatrix_det_ne_zero_of_cols_linearIndependent A hli

/-- Version of `witness_full_minor` with the conditions literally in the notation of the
main statement (column entries `fun i => A i j`). -/
lemma witness_full_minor_fun {n r : ℕ} (M : Submodule ℤ (E n))
    (hfr : Module.finrank ℤ M = r) (A : Matrix (Fin n) (Fin r) ℤ)
    (hAcol : ∀ j : Fin r, (fun i : Fin n => A i j) ∈ M)
    (hAspan : ∀ ⦃x : E n⦄, x ∈ M →
      x ∈ Submodule.span ℤ (Set.range (fun j : Fin r => fun i : Fin n => A i j))) :
    ∃ e : Fin r ↪ Fin n, (A.submatrix e (fun j : Fin r => j)).det ≠ 0 := by
  classical
  have hli : LinearIndependent ℤ (fun j : Fin r => fun i : Fin n => A i j) :=
    Commons.Lattice.Module.generators_basis_of_finrank (E := E n) M hfr
      (fun j : Fin r => fun i : Fin n => A i j)
      (by intro j; simpa using hAcol j)
      (by intro x hx; exact (hAspan hx))
  have hcol_eq : (fun j : Fin r => A.col j) = (fun j : Fin r => fun i : Fin n => A i j) := by
    funext j
    funext i
    rfl
  have hliCol : LinearIndependent ℤ A.col := by
    change LinearIndependent ℤ (fun j : Fin r => A.col j)
    rw [hcol_eq]
    exact hli
  exact Commons.LinearAlgebra.Matrix.exists_submatrix_det_ne_zero_of_cols_linearIndependent A hliCol

/-- Gram determinant is at least the square of any full integer minor, so at least `1`. -/
lemma gramReal_ge_one_of_full_minor {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℤ)
    (h : ∃ e : Fin r ↪ Fin n, (A.submatrix e (fun j : Fin r => j)).det ≠ 0) :
    (1 : ℝ) ≤ gramReal A := by
  classical
  rcases h with ⟨e, he⟩
  let z : ℤ := (A.submatrix e (fun j : Fin r => j)).det
  have hz0 : z ≠ 0 := by
    simpa [z] using he
  have hz1 : (1 : ℝ) ≤ (z : ℝ) ^ 2 := by
    have hz1i : 1 ≤ z.natAbs ^ 2 := by
      have : 1 ≤ z.natAbs := by omega
      nlinarith
    rw [← sq_abs (a := (z : ℝ))]
    have hzabs : |(z : ℝ)| = (z.natAbs : ℝ) := by
      have h1 := (Int.cast_abs (R := ℝ) (a := z)).symm
      rw [h1, Int.abs_eq_natAbs]
      norm_num
    rw [hzabs]
    have hsq : ((z.natAbs : ℝ) ^ 2) = ((z.natAbs ^ 2 : ℕ) : ℝ) := by
      norm_num [Nat.cast_pow]
    rw [hsq]
    exact_mod_cast hz1i
  have h1 := Commons.LinearAlgebra.Matrix.gram_det_ge_submatrix_det_sq A e
  have hcast : (((A.submatrix e (fun j : Fin r => j)).map (fun w : ℤ => (w : ℝ))).det) =
      (z : ℝ) := by
    dsimp [z]
    rw [Int.cast_det]
  have hbig : (z : ℝ) ^ 2 ≤ gramReal A := by
    simpa [gramReal, rM, hcast] using h1
  nlinarith

/-! ## Small arithmetic helpers -/

/-- A natural product each of whose factors is at least `1` is at least any single factor. -/
lemma nat_prod_ge_factor {ι : Type*} [Fintype ι] (f : ι → ℕ) (i : ι)
    (hf : ∀ k : ι, 1 ≤ f k) : f i ≤ ∏ k : ι, f k := by
  classical
  have hprod : (1 : ℕ) ≤ ∏ k ∈ (Finset.univ.erase i), f k :=
    Finset.one_le_prod (by intro k hk; exact hf k)
  have hmainReal : (f i : ℝ) ≤ (((∏ k ∈ (Finset.univ.erase i), f k) * f i : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) ≤ ((∏ k ∈ (Finset.univ.erase i), f k : ℕ) : ℝ) := by exact_mod_cast hprod
    have hfR : (0 : ℝ) ≤ (f i : ℝ) := by positivity
    rw [Nat.cast_mul]
    simpa [mul_comm] using (mul_le_mul_of_nonneg_left h1 hfR)
  have hmain : f i ≤ (∏ k ∈ (Finset.univ.erase i), f k) * f i := by exact_mod_cast hmainReal
  have heq : ∏ k : ι, f k = (∏ k ∈ (Finset.univ.erase i), f k) * f i := by
    simpa using (Finset.prod_erase_mul (Finset.univ : Finset ι) f (Finset.mem_univ i)).symm
  rw [heq]
  exact hmain

/-- A real number with `|c i| ≥ 1` for all `i` satisfies `|c i| ≤ ∏ |c k|`. -/
lemma real_prod_ge_factor_abs {ι : Type*} [Fintype ι] (c : ι → ℝ) (i : ι)
    (hc : ∀ k : ι, 1 ≤ |c k|) : |c i| ≤ ∏ k : ι, |c k| := by
  classical
  have hprod : (1 : ℝ) ≤ ∏ k ∈ (Finset.univ.erase i), |c k| := by
    apply Finset.one_le_prod
    intro k hk
    exact hc k
  have heq : ∏ k : ι, |c k| = (∏ k ∈ (Finset.univ.erase i), |c k|) * |c i| := by
    simpa using (Finset.prod_erase_mul (Finset.univ : Finset ι) (fun k : ι => |c k|)
      (Finset.mem_univ i)).symm
  have hle : |c i| ≤ (∏ k ∈ (Finset.univ.erase i), |c k|) * |c i| := by
    simpa [mul_comm] using (mul_le_mul_of_nonneg_left hprod (abs_nonneg (c i)))
  rw [heq]
  exact hle

/-- `a i ∣ (K! : ℤ)` from `0 < (a i).natAbs` and `(a i).natAbs ≤ K`. -/
lemma int_dvd_factorial_cast {a : ℤ} {K : ℕ} (ha0 : 0 < a.natAbs) (haK : a.natAbs ≤ K) :
    a ∣ (K.factorial : ℤ) := by
  have hd : a.natAbs ∣ K.factorial := Nat.dvd_factorial ha0 haK
  rw [← Int.natAbs_dvd_natAbs]
  simpa using hd

/-! ## Real-product bounds used by the cover construction -/

/-- Casting the absolute value of an integer to `ℝ` is the absolute value of the cast. -/
lemma natAbs_real_abs (a : ℤ) : ((a.natAbs : ℕ) : ℝ) = |(a : ℝ)| := by
  have h1 : ((a.natAbs : ℕ) : ℝ) = ((|a| : ℤ) : ℝ) := by
    rw [Int.abs_eq_natAbs]
    simp
  rw [h1]
  rw [Int.cast_abs]

/-- `(∏ |a k|)² = (∏ a k)²` (over reals). -/
lemma prod_abs_sq {r : ℕ} (a : Fin r → ℤ) :
    (∏ k : Fin r, |(a k : ℝ)|) ^ 2 = (∏ k : Fin r, (a k : ℝ)) ^ 2 := by
  rw [sq, sq]
  calc
    (∏ k : Fin r, |(a k : ℝ)|) * (∏ k : Fin r, |(a k : ℝ)|)
        = ∏ k : Fin r, |(a k : ℝ)| * |(a k : ℝ)| := by rw [← Finset.prod_mul_distrib]
    _ = ∏ k : Fin r, (a k : ℝ) * (a k : ℝ) := by
          apply Finset.prod_congr rfl
          intro k hk
          rw [abs_mul_abs_self]
    _ = (∏ k : Fin r, (a k : ℝ)) * (∏ k : Fin r, (a k : ℝ)) := by rw [Finset.prod_mul_distrib]

/-- If all `a k` are nonzero integers, `1 ≤ (∏ a k : ℝ)²`. -/
lemma sq_prod_ge_one {r : ℕ} (a : Fin r → ℤ) (h : ∀ k : Fin r, a k ≠ 0) :
    (1 : ℝ) ≤ (∏ k : Fin r, (a k : ℝ)) ^ 2 := by
  have hn : ∀ k : Fin r, 1 ≤ (a k).natAbs := by
    intro k
    have hz : (a k).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (h k)
    omega
  have hNat : (1 : ℕ) ≤ ∏ k : Fin r, (a k).natAbs :=
    Finset.one_le_prod (by intro k hk; exact hn k)
  have hNatReal : (1 : ℝ) ≤ ((∏ k : Fin r, (a k).natAbs : ℕ) : ℝ) := by exact_mod_cast hNat
  have hcast : ((∏ k : Fin r, (a k).natAbs : ℕ) : ℝ) = ∏ k : Fin r, |(a k : ℝ)| := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro k hk
    exact (natAbs_real_abs (a k))
  have hAbs : (1 : ℝ) ≤ ∏ k : Fin r, |(a k : ℝ)| := by rwa [← hcast]
  have hsq : (1 : ℝ) ^ 2 ≤ (∏ k : Fin r, |(a k : ℝ)|) ^ 2 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hAbs 2
  simpa [prod_abs_sq a] using hsq

/-- If all `a k` are nonzero integers then `(a i)² ≤ (∏ a k)²` (as reals). -/
lemma sq_le_prod_of_int {r : ℕ} (a : Fin r → ℤ) (h : ∀ k : Fin r, a k ≠ 0) (i : Fin r) :
    (a i : ℝ) ^ 2 ≤ (∏ k : Fin r, (a k : ℝ)) ^ 2 := by
  have hz : ∀ k : Fin r, (1 : ℝ) ≤ |(a k : ℝ)| := by
    intro k
    have hzi : (1 : ℤ) ≤ |a k| := Int.one_le_abs (h k)
    have hzR : (1 : ℝ) ≤ ((|a k| : ℤ) : ℝ) := by exact_mod_cast hzi
    simpa [← Int.cast_abs] using hzR
  have habs := real_prod_ge_factor_abs (fun k : Fin r => (a k : ℝ)) i hz
  have habs2 : |(a i : ℝ)| ^ 2 ≤ (∏ k : Fin r, |(a k : ℝ)|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hsq : (∏ k : Fin r, |(a k : ℝ)|) ^ 2 = (∏ k : Fin r, (a k : ℝ)) ^ 2 := prod_abs_sq a
  rw [sq_abs] at habs2
  rw [hsq] at habs2
  exact habs2

/-- If `(a : ℝ)² ≤ B` with `B ≥ 0`, then `|a| ≤ ⌈√B⌉`. -/
lemma natAbs_ceil_of_sq_le {a : ℤ} {B : ℝ} (hB : 0 ≤ B) (h : (a : ℝ) ^ 2 ≤ B) :
    a.natAbs ≤ Nat.ceil (Real.sqrt B) := by
  have hcast : ((a.natAbs : ℕ) : ℝ) = |(a : ℝ)| := natAbs_real_abs a
  have hsq : ((a.natAbs : ℕ) : ℝ) ^ 2 ≤ B := by
    rw [hcast]
    simpa [sq_abs] using h
  have hnonneg : (0 : ℝ) ≤ ((a.natAbs : ℕ) : ℝ) := by positivity
  have hle : ((a.natAbs : ℕ) : ℝ) ≤ Real.sqrt B := (Real.le_sqrt hnonneg hB).2 hsq
  have hK : Real.sqrt B ≤ (Nat.ceil (Real.sqrt B) : ℝ) := Nat.le_ceil (Real.sqrt B)
  exact_mod_cast (le_trans hle hK)

/-! ## Every lattice in `LatSet` has a bounded pure cover -/

/-- The ceiling bound `K := ⌈√B⌉`. -/
def KBound (B : ℝ) : ℕ := Nat.ceil (Real.sqrt B)

/-- Gram determinants of two bases of the same submodule coincide (in `gramReal` notation). -/
lemma gramReal_eq_of_span_eq {n r : ℕ} (M : Submodule ℤ (E n)) (u v : Fin r → E n)
    (h1 : ∀ j : Fin r, u j ∈ M) (h2 : M ≤ Submodule.span ℤ (Set.range u))
    (h3 : LinearIndependent ℤ u) (h4 : ∀ j : Fin r, v j ∈ M)
    (h5 : M ≤ Submodule.span ℤ (Set.range v)) (h6 : LinearIndependent ℤ v) :
    gramReal (fun i : Fin n => fun j : Fin r => u j i) =
    gramReal (fun i : Fin n => fun j : Fin r => v j i) := by
  have h := Commons.LinearAlgebra.Matrix.gram_det_eq_of_span_eq (M := M) (u := u) (v := v)
    h1 h2 h3 h4 h5 h6
  have hMu : (rM (fun i : Fin n => fun j : Fin r => u j i)).transpose *
        (rM (fun i : Fin n => fun j : Fin r => u j i)) =
      ((Matrix.of (fun i : Fin n => fun j : Fin r => u j i)).map (fun z : ℤ => (z : ℝ))).transpose *
        ((Matrix.of (fun i : Fin n => fun j : Fin r => u j i)).map (fun z : ℤ => (z : ℝ))) := by
    rfl
  have hMv : (rM (fun i : Fin n => fun j : Fin r => v j i)).transpose *
        (rM (fun i : Fin n => fun j : Fin r => v j i)) =
      ((Matrix.of (fun i : Fin n => fun j : Fin r => v j i)).map (fun z : ℤ => (z : ℝ))).transpose *
        ((Matrix.of (fun i : Fin n => fun j : Fin r => v j i)).map (fun z : ℤ => (z : ℝ))) := by
    rfl
  have hdet : ((rM (fun i : Fin n => fun j : Fin r => u j i)).transpose *
        (rM (fun i : Fin n => fun j : Fin r => u j i))).det =
      ((rM (fun i : Fin n => fun j : Fin r => v j i)).transpose *
        (rM (fun i : Fin n => fun j : Fin r => v j i))).det := by
    rw [hMu, hMv]
    exact h
  unfold gramReal
  exact hdet


/-- Gram determinant of a matrix whose columns are scaled by integers `a k`. -/
lemma gramReal_scale_cols {n r : ℕ} (V : Matrix (Fin n) (Fin r) ℤ) (a : Fin r → ℤ)
    (W : Matrix (Fin n) (Fin r) ℤ) (hW : ∀ i k, W i k = (a k : ℤ) * V i k) :
    gramReal W = (∏ k : Fin r, (a k : ℝ)) ^ 2 * gramReal V := by
  classical
  have hWV : W = V * Matrix.diagonal a := by
    ext i k
    rw [Matrix.mul_diagonal]
    rw [hW]
    rw [mul_comm]
  rw [hWV]
  rw [gramReal_mul_right]
  congr 1
  rw [det_rM, Matrix.det_diagonal, Int.cast_prod]


/-- Every lattice `M ∈ LatSet n r B` (with `B ≥ 1`) is contained in a pure rank-`r` lattice
`Mbar ∈ PureLatSet n r B` such that `K! • x ∈ M` for every `x ∈ Mbar`, where `K = ⌈√B⌉`. -/
lemma exists_pure_cover {n r : ℕ} (B : ℝ) (hB : 1 ≤ B)
    (M : Submodule ℤ (E n)) (hM : M ∈ LatSet n r B) :
    ∃ (Mbar : Submodule ℤ (E n)), M ≤ Mbar ∧ Mbar ∈ PureLatSet n r B ∧
      (∀ x : E n, x ∈ Mbar → ((KBound B).factorial : ℤ) • x ∈ M) := by
  classical
  rcases hM with ⟨hfr, A, hAcol, hAspan, hgram⟩
  let K : ℕ := KBound B
  obtain ⟨o, eO, emb, bN, a, hrel, hane⟩ := snf_structure M hfr
  let v : Fin r → E n := fun k => (eO (emb k) : E n)
  let w : Fin r → E n := fun k => (bN k : E n)
  let Mbar : Submodule ℤ (E n) := Submodule.span ℤ (Set.range v)
  let V : Matrix (Fin n) (Fin r) ℤ := fun i k => v k i
  have hvlin : LinearIndependent ℤ v := by
    dsimp [v]
    exact eO.linearIndependent.comp (fun k : Fin r => emb k) emb.injective
  have hfinMbar : Module.finrank ℤ Mbar = r := by
    dsimp [Mbar]
    simpa using (finrank_span_eq_card (R := ℤ) (b := v) hvlin)
  have hPure : Pure Mbar := by
    dsimp [Mbar]
    simpa [Pure] using (pure_span_subfamily eO emb)
  have hMspan : M = Submodule.span ℤ (Set.range w) := by
    simpa [w] using (basisValues_span (b := bN))
  have hwkMbar : ∀ k : Fin r, w k ∈ Mbar := by
    intro k
    dsimp [Mbar, w]
    rw [hrel k]
    exact Submodule.smul_mem _ (a k) (Submodule.subset_span ⟨k, rfl⟩)
  have hMleMbar : M ≤ Mbar := by
    rw [hMspan]
    exact Submodule.span_le.mpr (by
      intro y hy
      rcases hy with ⟨k, rfl⟩
      exact hwkMbar k)
  -- gram of the `bN`-basis `w` equals gram of the witness `A`
  let u : Fin r → E n := fun j => fun i : Fin n => A i j
  have hul : LinearIndependent ℤ u := by
    exact Commons.Lattice.Module.generators_basis_of_finrank (E := E n) M hfr u
      (by intro j; simpa [u] using hAcol j)
      (by intro x hx; simpa [u] using (hAspan hx))
  have hwl : LinearIndependent ℤ w := by
    simpa [w] using (basisValues_linearIndependent bN)
  have hgramEq : gramReal A = gramReal (fun i k => w k i) := by
    have h := gramReal_eq_of_span_eq (M := M) (u := u) (v := w)
      (by intro j; simpa [u] using hAcol j)
      (by intro x hx; simpa [u] using (hAspan hx))
      hul
      (by intro k; exact (bN k).2)
      (by rw [hMspan])
      hwl
    simpa [u] using h
  have hgramW : gramReal (fun i k => w k i) ≤ B := by
    simpa [hgramEq] using hgram
  -- gram identity: columns of the `w`-matrix are `a k`-scalings of the `v`-matrix columns
  have hdiag : gramReal (fun i k => w k i) = (∏ k : Fin r, (a k : ℝ)) ^ 2 * gramReal V := by
    have hsc := gramReal_scale_cols (V := fun i k => v k i) a (W := fun i k => w k i) (by
      intro i k
      have hf := congrFun (hrel k) i
      simpa [w, v] using hf)
    simpa [V] using hsc
  -- full minor and gram ≥ 1 for V
  have hVcol_eq : (fun k : Fin r => V.col k) = v := by
    funext k
    funext i
    dsimp [V]
    rfl
  have hVlin : LinearIndependent ℤ V.col := by
    change LinearIndependent ℤ (fun k : Fin r => V.col k)
    rw [hVcol_eq]
    exact hvlin
  have hfullV : ∃ e : Fin r ↪ Fin n, (V.submatrix e (fun j : Fin r => j)).det ≠ 0 := by
    exact Commons.LinearAlgebra.Matrix.exists_submatrix_det_ne_zero_of_cols_linearIndependent V hVlin
  have hgramV1 : (1 : ℝ) ≤ gramReal V := gramReal_ge_one_of_full_minor V hfullV
  have hV0 : (0 : ℝ) ≤ gramReal V := le_trans zero_le_one hgramV1
  -- (∏ (a k : ℝ))² ≤ gramReal W ≤ B
  have hprodW : (∏ k : Fin r, (a k : ℝ)) ^ 2 ≤ gramReal (fun i k => w k i) := by
    rw [hdiag]
    simpa [mul_comm] using (mul_le_mul_of_nonneg_right hgramV1 (sq_nonneg _))
  have hprodB : (∏ k : Fin r, (a k : ℝ)) ^ 2 ≤ B := le_trans hprodW hgramW
  -- gramReal V ≤ B for the witness of Mbar
  have hgramV : gramReal V ≤ B := by
    have hVleW : gramReal V ≤ gramReal (fun i k => w k i) := by
      rw [hdiag]
      have hprod1 : (1 : ℝ) ≤ (∏ k : Fin r, (a k : ℝ)) ^ 2 := sq_prod_ge_one a hane
      have hVleq : gramReal V ≤ (∏ k : Fin r, (a k : ℝ)) ^ 2 * gramReal V := by
        simpa [mul_comm] using (mul_le_mul_of_nonneg_right hprod1 hV0)
      exact hVleq
    exact le_trans hVleW hgramW
  -- bound on each |a i| and factorial divisibility
  have hdiv : ∀ i : Fin r, a i ∣ (K.factorial : ℤ) := by
    intro i
    have hai_le : (a i : ℝ) ^ 2 ≤ B := by
      exact le_trans (sq_le_prod_of_int a hane i) hprodB
    have hnat : (a i).natAbs ≤ K := by
      have hB0 : (0 : ℝ) ≤ B := le_trans (by norm_num : (0 : ℝ) ≤ 1) hB
      dsimp [K, KBound]
      exact natAbs_ceil_of_sq_le (a := a i) hB0 hai_le
    exact int_dvd_factorial_cast (a := a i) (K := K)
      (by have hz : (a i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hane i); omega)
      hnat
  -- factorial containment
  have hKv : ∀ i : Fin r, (K.factorial : ℤ) • v i ∈ M := by
    intro i
    have hmem : (K.factorial : ℤ) • v i ∈ Submodule.span ℤ (Set.range w) :=
      smul_mem_span_of_dvd (v := v) (w := w) a hrel (K := K) hdiv i
    rwa [hMspan]
  have hfact : ∀ x : E n, x ∈ Mbar → (K.factorial : ℤ) • x ∈ M := by
    intro x hx
    have hxspan : x ∈ Submodule.span ℤ (Set.range v) := by
      simpa [Mbar] using hx
    rw [Submodule.mem_span_range_iff_exists_fun] at hxspan
    rcases hxspan with ⟨c, hc⟩
    rw [← hc]
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ ?_
    intro i _
    have heq : (K.factorial : ℤ) • (c i • v i) = c i • ((K.factorial : ℤ) • v i) := by
      rw [smul_smul, mul_comm, ← smul_smul]
    rw [heq]
    exact Submodule.smul_mem M (c i) (hKv i)
  -- assemble
  refine ⟨Mbar, hMleMbar, ?_, hfact⟩
  refine ⟨hfinMbar, ?_, V, ?_, hfullV, hgramV⟩
  · simpa [Pure] using hPure
  · intro j
    dsimp [Mbar, V]
    exact Submodule.subset_span ⟨j, rfl⟩

/-! ## The finiteness theorem -/

theorem finite_sublattices_int_count {n r : ℕ} (B : ℝ) :
    {M : Submodule ℤ (Fin n → ℤ) | Module.finrank ℤ M = r ∧
      (∃ A : Matrix (Fin n) (Fin r) ℤ,
        (∀ j : Fin r, (fun i => A i j) ∈ M) ∧
        (∀ ⦃x⦄, x ∈ M → x ∈ Submodule.span ℤ (Set.range (fun j : Fin r => (fun i => A i j)))) ∧
        (((A.map (fun z : ℤ => (z : ℝ))).transpose *
            (A.map (fun z : ℤ => (z : ℝ)))).det ≤ B))}.Finite := by
  classical
  by_cases hB : B < 1
  · -- no lattices at all
    have hEmpty : LatSet n r B = ∅ := by
      ext M
      constructor
      · intro hM
        rcases hM with ⟨hfr, A, hAcol, hAspan, hgram⟩
        have hfull := witness_full_minor_fun M hfr A hAcol hAspan
        have hg1 : (1 : ℝ) ≤ gramReal A := gramReal_ge_one_of_full_minor A hfull
        have hlt : gramReal A < 1 := lt_of_le_of_lt hgram hB
        exact (not_le_of_gt hlt) hg1
      · intro hx
        simp at hx
    have hEq : {M : Submodule ℤ (E n) |
        Module.finrank ℤ M = r ∧
        (∃ A : Matrix (Fin n) (Fin r) ℤ,
          (∀ j : Fin r, (fun i : Fin n => A i j) ∈ M) ∧
          (∀ ⦃x : E n⦄, x ∈ M →
            x ∈ Submodule.span ℤ (Set.range (fun j : Fin r => fun i : Fin n => A i j))) ∧
          (((A.map (fun z : ℤ => (z : ℝ))).transpose *
              (A.map (fun z : ℤ => (z : ℝ)))).det ≤ B))} = LatSet n r B := by
      ext M
      simp [LatSet, gramReal, rM]
    rw [hEq]
    simp [hEmpty]
  · have hB1 : 1 ≤ B := le_of_not_gt hB
    let Fib : Submodule ℤ (E n) → Set (Submodule ℤ (E n)) :=
      fun Mbar => {N | N ≤ Mbar ∧
        (∀ x : E n, x ∈ Mbar → ((KBound B).factorial : ℤ) • x ∈ N)}
    have hFibFin : ∀ Mbar, Mbar ∈ PureLatSet n r B → (Fib Mbar).Finite := by
      intro Mbar hMbar
      have hL : 0 < (KBound B).factorial := Nat.factorial_pos (KBound B)
      have hf := finite_submodules_between_nsmul n Mbar ((KBound B).factorial) hL
      simpa [Fib] using hf
    have hSub : LatSet n r B ⊆ ⋃ Mbar ∈ PureLatSet n r B, Fib Mbar := by
      intro M hM
      obtain ⟨Mbar, hle, hMB, hfact⟩ := exists_pure_cover B hB1 M hM
      exact Set.mem_iUnion₂.mpr ⟨Mbar, hMB, ⟨hle, hfact⟩⟩
    have hFinUnion : (⋃ Mbar ∈ PureLatSet n r B, Fib Mbar).Finite := by
      exact (pureLatSet_finite n r B).biUnion (by intro Mbar hMbar; exact hFibFin Mbar hMbar)
    have hFinLat : (LatSet n r B).Finite := hFinUnion.subset hSub
    have hEq : {M : Submodule ℤ (E n) |
        Module.finrank ℤ M = r ∧
        (∃ A : Matrix (Fin n) (Fin r) ℤ,
          (∀ j : Fin r, (fun i : Fin n => A i j) ∈ M) ∧
          (∀ ⦃x : E n⦄, x ∈ M →
            x ∈ Submodule.span ℤ (Set.range (fun j : Fin r => fun i : Fin n => A i j))) ∧
          (((A.map (fun z : ℤ => (z : ℝ))).transpose *
              (A.map (fun z : ℤ => (z : ℝ)))).det ≤ B))} = LatSet n r B := by
      ext M
      simp [LatSet, gramReal, rM]
    rwa [hEq]

end Commons.Lattice.Counting

end
