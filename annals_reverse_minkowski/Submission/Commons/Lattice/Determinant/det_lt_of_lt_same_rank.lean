import Mathlib.Data.Int.Star
import Submission.Commons.Lattice.Determinant.gram_det_independent
import Submission.Commons.LinearAlgebra.Independence.discrete_basis_values_linIndep
import Submission.Commons.LinearAlgebra.GramMatrix.gram_change_det

noncomputable section
open scoped BigOperators
open Module Real Matrix

namespace Commons.Lattice.Determinant

/-- The element of `L₂` whose ambient value is the ambient value of `e i ∈ L₁`, for `L₁ ≤ L₂`. -/
def det_lt_inL₂ {N r : ℕ} {L₁ L₂ : Submodule ℤ (Eu N)} (hle : L₁ ≤ L₂)
    (e : Module.Basis (Fin r) ℤ L₁) (i : Fin r) : L₂ :=
  ⟨((e i : L₁) : Eu N), hle (e i).property⟩

/-- The integer change-of-basis matrix: `det_lt_inL₂ hle e j = ∑ i, (A j i : ℤ) • f i` in `L₂`. -/
def det_lt_changeMatrix {N r : ℕ} {L₁ L₂ : Submodule ℤ (Eu N)} (hle : L₁ ≤ L₂)
    (e : Module.Basis (Fin r) ℤ L₁) (f : Module.Basis (Fin r) ℤ L₂) :
    Matrix (Fin r) (Fin r) ℤ :=
  fun j i => f.repr (det_lt_inL₂ hle e j) i

/-- Expansion of the ambient value of `e j ∈ L₁` in terms of the ambient values of the
`ℤ`-basis `f` of `L₂`, with real (integer-cast) coefficients. -/
lemma det_lt_e_expand {N r : ℕ} {L₁ L₂ : Submodule ℤ (Eu N)} (hle : L₁ ≤ L₂)
    (e : Module.Basis (Fin r) ℤ L₁) (f : Module.Basis (Fin r) ℤ L₂) :
    ∀ j : Fin r,
      ((e j : L₁) : Eu N) =
        ∑ i : Fin r, (((det_lt_changeMatrix hle e f j i : ℤ) : ℝ)) • ((f i : L₂) : Eu N) := by
  intro j
  have h := coerce_expand_real (n := N) (m := r) L₂ f (det_lt_inL₂ hle e j)
  simpa [det_lt_changeMatrix, det_lt_inL₂] using h

/-- Expansion of the element `det_lt_inL₂ hle e j ∈ L₂` in the `ℤ`-basis `f` of `L₂`. -/
lemma det_lt_x_expand {N r : ℕ} {L₁ L₂ : Submodule ℤ (Eu N)} (hle : L₁ ≤ L₂)
    (e : Module.Basis (Fin r) ℤ L₁) (f : Module.Basis (Fin r) ℤ L₂) :
    ∀ j : Fin r,
      (det_lt_inL₂ hle e j : L₂) =
        ∑ i : Fin r, (det_lt_changeMatrix hle e f j i : ℤ) • (f i : L₂) := by
  intro j
  simp [det_lt_changeMatrix, det_lt_inL₂]

/-- Gram-determinant change of basis: `det Gram(e) = (det A)² · det Gram(f)`. -/
lemma det_lt_gram_eq {N r : ℕ} {L₁ L₂ : Submodule ℤ (Eu N)} (hle : L₁ ≤ L₂)
    (e : Module.Basis (Fin r) ℤ L₁) (f : Module.Basis (Fin r) ℤ L₂) :
    (Matrix.gram ℝ (fun i : Fin r => ((e i : L₁) : Eu N))).det =
      ((det_lt_changeMatrix hle e f).map (fun z : ℤ => (z : ℝ))).det ^ 2 *
        (Matrix.gram ℝ (fun i : Fin r => ((f i : L₂) : Eu N))).det := by
  classical
  let A : Matrix (Fin r) (Fin r) ℤ := det_lt_changeMatrix hle e f
  have hrel : ∀ j : Fin r,
      ((e j : L₁) : Eu N) = ∑ i : Fin r, (((A j i : ℤ) : ℝ)) • ((f i : L₂) : Eu N) := by
    simpa [A] using det_lt_e_expand hle e f
  simpa [A] using (Commons.LinearAlgebra.GramMatrix.gram_change_det
    (E := Eu N) (e := fun i : Fin r => ((f i : L₂) : Eu N))
    (f := fun j : Fin r => ((e j : L₁) : Eu N)) (A := A) (hfe := hrel))

/-- Gram determinant of the ambient values of a `ℤ`-basis of a discrete submodule is positive. -/
lemma det_lt_gram_pos {N r : ℕ} {L : Submodule ℤ (Eu N)} [DiscreteTopology L]
    (b : Module.Basis (Fin r) ℤ L) :
    0 < (Matrix.gram ℝ (fun i : Fin r => ((b i : L) : Eu N))).det := by
  classical
  have hli : LinearIndependent ℝ (fun i : Fin r => ((b i : L) : Eu N)) := by
    exact Commons.LinearAlgebra.Independence.discrete_basis_values_linIndep (E := Eu N) (ℒ := L) b
  have hpd : (Matrix.gram ℝ (fun i : Fin r => ((b i : L) : Eu N))).PosDef := by
    exact Matrix.posDef_gram_of_linearIndependent hli
  exact Matrix.PosDef.det_pos hpd

/-- If the change-of-basis matrix between a `ℤ`-basis of `L₁` and one of `L₂` (`L₁ ≤ L₂`)
has determinant of absolute value one, then the two submodules coincide: `L₂ ≤ L₁`. -/
lemma det_lt_L₂_le_L₁_of_abs_det_one {N r : ℕ} {L₁ L₂ : Submodule ℤ (Eu N)} (hle : L₁ ≤ L₂)
    (e : Module.Basis (Fin r) ℤ L₁) (f : Module.Basis (Fin r) ℤ L₂)
    (hdet : |(det_lt_changeMatrix hle e f).det| = 1) : L₂ ≤ L₁ := by
  classical
  let A : Matrix (Fin r) (Fin r) ℤ := det_lt_changeMatrix hle e f
  have hdetA : |A.det| = 1 := by simpa [A] using hdet
  have hdet_unit : IsUnit A.det := by
    rw [Int.isUnit_iff]
    exact (abs_eq (a := A.det) (b := (1 : ℤ)) (by norm_num)).mp hdetA
  let C : Matrix (Fin r) (Fin r) ℤ := A⁻¹
  have hCA : C * A = 1 := by
    dsimp [C]
    exact nonsing_inv_mul A hdet_unit
  -- expansion of f k in terms of the x j = det_lt_inL₂ hle e j
  have hf_expand : ∀ k : Fin r,
      (f k : L₂) = ∑ j : Fin r, C k j • (det_lt_inL₂ hle e j) := by
    intro k
    have h₁ : (f k : L₂) = ∑ j : Fin r, C k j • (∑ i : Fin r, A j i • f i) := by
      symm
      calc
        (∑ j : Fin r, C k j • (∑ i : Fin r, A j i • f i))
            = ∑ j : Fin r, ∑ i : Fin r, (C k j * A j i) • f i := by
              apply Finset.sum_congr rfl
              intro j hj
              calc
                C k j • (∑ i : Fin r, A j i • f i) = ∑ i : Fin r, C k j • (A j i • f i) := by
                  exact Finset.smul_sum (s := Finset.univ) (r := C k j)
                    (f := fun i => A j i • f i)
                _ = ∑ i : Fin r, (C k j * A j i) • f i := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [← smul_smul]
        _ = ∑ i : Fin r, ∑ j : Fin r, (C k j * A j i) • f i := by
              exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
                (f := fun j i => (C k j * A j i) • f i)
        _ = ∑ i : Fin r, (∑ j : Fin r, C k j * A j i) • f i := by
              apply Finset.sum_congr rfl
              intro i hi
              exact (Finset.sum_smul (s := Finset.univ) (f := fun j => C k j * A j i)
                (x := f i)).symm
        _ = ∑ i : Fin r, (C * A) k i • f i := by
              apply Finset.sum_congr rfl
              intro i hi
              apply congrArg (fun z : ℤ => z • f i)
              rw [Matrix.mul_apply]
        _ = ∑ i : Fin r, (f.repr (f k)) i • f i := by
              apply Finset.sum_congr rfl
              intro i hi
              apply congrArg (fun z : ℤ => z • f i)
              rw [hCA]
              rw [f.repr_self]
              simp [Matrix.one_apply, Finsupp.single_apply]
        _ = f k := by
              rw [f.sum_repr (f k)]
    calc
      (f k : L₂) = ∑ j : Fin r, C k j • (∑ i : Fin r, A j i • f i) := h₁
      _ = ∑ j : Fin r, C k j • (det_lt_inL₂ hle e j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← det_lt_x_expand hle e f j]
  -- ambient value of f k lies in L₁
  have hf_mem : ∀ k : Fin r, ((f k : L₂) : Eu N) ∈ L₁ := by
    intro k
    have hEqL₂ : (f k : L₂) = ∑ j : Fin r, C k j • (det_lt_inL₂ hle e j) := hf_expand k
    have hEqE : ((f k : L₂) : Eu N) =
        ∑ j : Fin r, (C k j : ℤ) • ((e j : L₁) : Eu N) := by
      calc
        ((f k : L₂) : Eu N) = (Submodule.subtype L₂) (f k) := rfl
        _ = (Submodule.subtype L₂) (∑ j : Fin r, C k j • (det_lt_inL₂ hle e j)) := by
              rw [hEqL₂]
        _ = ∑ j : Fin r, (Submodule.subtype L₂) (C k j • (det_lt_inL₂ hle e j)) := by
              rw [map_sum]
        _ = ∑ j : Fin r, (C k j : ℤ) • (Submodule.subtype L₂) (det_lt_inL₂ hle e j) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [map_smul]
        _ = ∑ j : Fin r, (C k j : ℤ) • ((e j : L₁) : Eu N) := by
              apply Finset.sum_congr rfl
              intro j hj
              simp [det_lt_inL₂]
    rw [hEqE]
    exact Submodule.sum_mem L₁ (fun j hj => Submodule.smul_mem L₁ (C k j) (e j).property)
  -- every element of L₂ lies in L₁
  intro z hz
  let y : L₂ := ⟨z, hz⟩
  have hyE : ((y : L₂) : Eu N) = z := rfl
  have hzexp : z = ∑ i : Fin r, (((f.repr y i : ℤ) : ℝ)) • ((f i : L₂) : Eu N) := by
    rw [← hyE]
    exact coerce_expand_real (n := N) (m := r) L₂ f y
  have hzexpZ : z = ∑ i : Fin r, (f.repr y i : ℤ) • ((f i : L₂) : Eu N) := by
    rw [hzexp]
    apply Finset.sum_congr rfl
    intro i hi
    exact Int.cast_smul_eq_zsmul ℝ (f.repr y i) (((f i : L₂) : Eu N))
  rw [hzexpZ]
  exact Submodule.sum_mem L₁ (fun i hi => Submodule.smul_mem L₁ (f.repr y i) (hf_mem i))


/-- A PROPER sublattice of the same rank has STRICTLY LARGER determinant (genuine-lattice
version: `L₁, L₂` are DISCRETE, so the ambient images of their `ℤ`-bases are ℝ-independent and
the Gram determinants are positive).  For `L₁ < L₂` with `ℤ`-bases `e` of `L₁`, `f` of `L₂`
(same index `Fin r`): `√(gram e) > √(gram f)`. -/
theorem det_lt_of_lt_same_rank {N r : ℕ} {L₁ L₂ : Submodule ℤ (EuclideanSpace ℝ (Fin N))}
    [DiscreteTopology L₁] [DiscreteTopology L₂]
    (e : Module.Basis (Fin r) ℤ L₁) (f : Module.Basis (Fin r) ℤ L₂)
    (h₁₂ : L₁ < L₂) :
    √((Matrix.gram ℝ (fun i : Fin r => ((e i : L₁) : EuclideanSpace ℝ (Fin N)))).det) >
      √((Matrix.gram ℝ (fun i : Fin r => ((f i : L₂) : EuclideanSpace ℝ (Fin N)))).det) := by
  classical
  let hle : L₁ ≤ L₂ := h₁₂.le
  let A : Matrix (Fin r) (Fin r) ℤ := det_lt_changeMatrix hle e f
  let d : ℝ := (A.map (fun z : ℤ => (z : ℝ))).det
  let gramE : ℝ := (Matrix.gram ℝ (fun i : Fin r => ((e i : L₁) : Eu N))).det
  let gramF : ℝ := (Matrix.gram ℝ (fun i : Fin r => ((f i : L₂) : Eu N))).det
  have hgram : gramE = d ^ 2 * gramF := by
    dsimp [gramE, gramF, d, A]
    exact det_lt_gram_eq hle e f
  have hposE : 0 < gramE := det_lt_gram_pos (N := N) e
  have hposF : 0 < gramF := det_lt_gram_pos (N := N) f
  -- the integer change-of-basis determinant is nonzero, |det A| ≥ 2
  have hdetA_ne0 : A.det ≠ 0 := by
    intro hA0
    have hd0 : d = 0 := by
      dsimp [d]
      rw [← Int.cast_det A, hA0]
      norm_num
    have : gramE = 0 := by
      rw [hgram, hd0]
      ring
    linarith
  have hdetA_abs_ne_one : |A.det| ≠ 1 := by
    intro hA1
    have hle2 : L₂ ≤ L₁ := det_lt_L₂_le_L₁_of_abs_det_one hle e f (by simpa [A] using hA1)
    exact (h₁₂.ne) (le_antisymm hle hle2)
  have hdetA_abs_ge : (2 : ℤ) ≤ |A.det| := by
    have h1 : 1 ≤ |A.det| := Int.one_le_abs hdetA_ne0
    omega
  have hd2 : (2 : ℝ) ≤ |d| := by
    dsimp [d]
    rw [← Int.cast_det A]
    exact_mod_cast hdetA_abs_ge
  -- √ gramE = |d| · √ gramF > √ gramF
  have hsqrt : √gramE = |d| * √gramF := by
    calc
      √gramE = √(d ^ 2 * gramF) := by rw [hgram]
      _ = √(d ^ 2) * √gramF := by rw [Real.sqrt_mul (sq_nonneg d) gramF]
      _ = |d| * √gramF := by rw [Real.sqrt_sq_eq_abs]
  have hsqF_pos : 0 < √gramF := (Real.sqrt_pos).2 hposF
  have hmain : |d| * √gramF > √gramF := by
    have h₁ : 2 * √gramF ≤ |d| * √gramF :=
      mul_le_mul_of_nonneg_right hd2 (le_of_lt hsqF_pos)
    have h₂ : √gramF < 2 * √gramF := by nlinarith [hsqF_pos]
    exact lt_of_lt_of_le h₂ h₁
  change √gramE > √gramF
  rw [hsqrt]
  exact hmain

end Commons.Lattice.Determinant