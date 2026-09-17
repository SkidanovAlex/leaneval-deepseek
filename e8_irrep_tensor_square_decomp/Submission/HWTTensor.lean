import Submission.E8Casimir
import Mathlib.Algebra.Lie.TensorProduct
import Submission.Commons.LinearAlgebra.TensorProduct.linearIndependent_tmul_sum

set_option maxHeartbeats 800000

/-!
# Highest weight vectors in a tensor square: the antisymmetric construction

Let `M` be a Lie module over a Lie ring `L` and let `v ∈ M` be a **highest weight vector**: killed
by `e ∈ L` and an eigenvector of `h ∈ L` with eigenvalue `c`.  If `⁅e,f⁆ = h`, then the
antisymmetric combination

  `Z := (f · v) ⊗ v - v ⊗ (f · v) ∈ M ⊗ M`

is again killed by `e`; and if `⁅h,f⁆ = -d • f` then `h · Z = (2c - d) • Z`.

Applied to `e₈` with `v` a highest weight vector of weight `λ` and `f = fᵢ` (so `⁅eᵢ,fᵢ⁆ = hᵢ` and
`⁅h_j,f_i⁆ = -A_{ji} f_i`), this produces a highest weight vector of `V ⊗ V` of weight `2λ - αᵢ`.
Hence `L(2λ - αᵢ) ⊆ V ⊗ V` whenever `2λ - αᵢ` is dominant.

The construction does *not* iterate: with `D_i := f_i⁽¹⁾ - f_i⁽²⁾` one has
`e_j (D_j z) = (h_j⁽¹⁾ - h_j⁽²⁾) z` for a highest weight vector `z`, so `D_j z` is again a highest
weight vector **iff** `z` is balanced (`h⁽¹⁾ z = h⁽²⁾ z` for all `h`), which fails already for
`D_i (v ⊗ v)`.  This is the elementary half of the PRV statement; the general statement
(`L(wλ + w'λ) ⊆ L(λ) ⊗ L(λ)`) is a genuinely deeper theorem.
-/

noncomputable section

open scoped TensorProduct
open TensorProduct LieModule

namespace Submission.HWTTensor

section General

variable {R : Type*} [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra R L]
variable {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- **The antisymmetric construction.**  If `v` is killed by `e`, `⁅e,f⁆ = h` and `h` acts on `v`
by the scalar `c`, then `(f·v) ⊗ v - v ⊗ (f·v)` is killed by `e`. -/
theorem lie_antisym_tmul (e f h : L) (hef : ⁅e, f⁆ = h) (v : M) (hev : ⁅e, v⁆ = 0)
    (c : R) (hhv : ⁅h, v⁆ = c • v) :
    ⁅e, (⁅f, v⁆) ⊗ₜ[R] v - v ⊗ₜ[R] (⁅f, v⁆)⁆ = 0 := by
  have key : ⁅e, ⁅f, v⁆⁆ = c • v := by
    rw [leibniz_lie, hef, hev, lie_zero, add_zero, hhv]
  have hmain : ⁅e, (⁅f, v⁆) ⊗ₜ[R] v - v ⊗ₜ[R] (⁅f, v⁆)⁆
      = ⁅e, ⁅f, v⁆⁆ ⊗ₜ[R] v - v ⊗ₜ[R] ⁅e, ⁅f, v⁆⁆ := by
    rw [lie_sub, lie_tmul_right, lie_tmul_right, hev]
    simp
  rw [hmain, key, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  simp

/-- The antisymmetric construction is a weight vector: if `⁅h,f⁆ = -d • f` and `h` acts on `v` by
`c`, then `h` acts on `(f·v) ⊗ v - v ⊗ (f·v)` by `2c - d`. -/
theorem lie_h_antisym_tmul (h f : L) (d c : R) (v : M) (hfv : ⁅h, f⁆ = (-d) • f)
    (hv : ⁅h, v⁆ = c • v) :
    ⁅h, (⁅f, v⁆) ⊗ₜ[R] v - v ⊗ₜ[R] (⁅f, v⁆)⁆
      = (2 * c - d) • ((⁅f, v⁆) ⊗ₜ[R] v - v ⊗ₜ[R] (⁅f, v⁆)) := by
  have ha : ⁅h, ⁅f, v⁆⁆ = (c - d) • ⁅f, v⁆ := by
    rw [leibniz_lie, hfv, hv, smul_lie, lie_smul, ← add_smul]
    congr 1
    ring
  have hmain : ⁅h, (⁅f, v⁆) ⊗ₜ[R] v - v ⊗ₜ[R] (⁅f, v⁆)⁆
      = ⁅h, ⁅f, v⁆⁆ ⊗ₜ[R] v + (⁅f, v⁆) ⊗ₜ[R] (c • v)
        - ((c • v) ⊗ₜ[R] (⁅f, v⁆) + v ⊗ₜ[R] ⁅h, ⁅f, v⁆⁆) := by
    rw [lie_sub, lie_tmul_right, lie_tmul_right, hv]
  rw [hmain, ha]
  simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  rw [smul_sub, ← add_smul, ← add_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring


/-- Two nonzero eigenvectors of an element of a Lie algebra with **different** eigenvalues over a
field are linearly independent. -/
theorem linearIndependent_of_weight_ne {R : Type*} [Field R] {L : Type*} [LieRing L]
    [LieAlgebra R L] {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M]
    [LieModule R L M] {h : L} {x y : M} {c d : R}
    (hx : ⁅h, x⁆ = c • x) (hy : ⁅h, y⁆ = d • y) (hcd : c ≠ d) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    LinearIndependent R ![x, y] := by
  rw [LinearIndependent.pair_iffₛ]
  intro a b a' b' hab
  have h1 : (a - a') • x + (b - b') • y = 0 := by
    rw [sub_smul, sub_smul]
    rw [show a • x - a' • x + (b • y - b' • y) = (a • x + b • y) - (a' • x + b' • y) by abel,
      hab, sub_self]
  have h2 : ((a - a') * c) • x + ((b - b') * d) • y = 0 := by
    have hh : ⁅h, (a - a') • x + (b - b') • y⁆
        = ((a - a') * c) • x + ((b - b') * d) • y := by
      rw [lie_add, lie_smul, lie_smul, hx, hy, smul_smul, smul_smul]
    rw [h1, lie_zero] at hh
    exact hh.symm
  have h3 : ((a - a') * d) • x + ((b - b') * d) • y = 0 := by
    have hh := congrArg (fun z => d • z) h1
    rw [smul_add, smul_smul, smul_smul, smul_zero, mul_comm d (a - a'), mul_comm d (b - b')] at hh
    exact hh
  have h4 : ((a - a') * c - (a - a') * d) • x = 0 := by
    rw [sub_smul]
    rw [show ((a - a') * c) • x - ((a - a') * d) • x
        = (((a - a') * c) • x + ((b - b') * d) • y)
          - (((a - a') * d) • x + ((b - b') * d) • y) by abel, h2, h3, sub_self]
  have h5 : (a - a') * (c - d) = 0 := by
    rcases smul_eq_zero.mp h4 with h | h
    · rwa [← mul_sub] at h
    · exact absurd h hx0
  have haa : a = a' := by
    rcases mul_eq_zero.mp h5 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd (sub_eq_zero.mp h) hcd
  have hbb : b = b' := by
    rw [haa, sub_self, zero_smul, zero_add] at h1
    rcases smul_eq_zero.mp h1 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hy0
  exact ⟨haa, hbb⟩

end General

section E8

open Commons.Algebra.Lie.SerreConstruction

set_option maxHeartbeats 4000000

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  [LieRingModule (LieAlgebra.e₈ ℂ) M] [LieModule ℂ (LieAlgebra.e₈ ℂ) M]

/-- The antisymmetric vector `(fᵢ · v) ⊗ v - v ⊗ (fᵢ · v)` in the tensor square of a module. -/
def Zt (i : Fin 8) (v : M) : M ⊗[ℂ] M :=
  (⁅SerreF i, v⁆) ⊗ₜ[ℂ] v - v ⊗ₜ[ℂ] (⁅SerreF i, v⁆)

/-- The case `j = i` of `e8_antisym_lieE`. -/
theorem e8_antisym_lieE_self (i : Fin 8) {ψ : Fin 8 → ℂ} {v : M}
    (hev : ∀ j, ⁅SerreE j, v⁆ = 0) (hwt : ∀ j, ⁅SerreH j, v⁆ = ψ j • v) :
    ⁅SerreE i, Zt i v⁆ = 0 := by
  rw [Zt]
  exact lie_antisym_tmul (SerreE i) (SerreF i) (SerreH i)
    (by rw [serreLie_E_F, if_pos rfl]) v (hev i) (ψ i) (hwt i)

/-- The case `j ≠ i` of `e8_antisym_lieE`. -/
theorem e8_antisym_lieE_ne {j i : Fin 8} (hji : j ≠ i) {v : M}
    (hev : ∀ k, ⁅SerreE k, v⁆ = 0) :
    ⁅SerreE j, Zt i v⁆ = 0 := by
  rw [Zt]
  exact lie_antisym_tmul (SerreE j) (SerreF i) 0
    (by rw [serreLie_E_F, if_neg hji]) v (hev j) 0 (by simp)

/-- **The `e₈` case, bracket part.**  If `v` is a highest weight vector (killed by all `eᵢ`), then
for each simple root `i` the vector `Zt i v` is again killed by all `eⱼ`. -/
theorem e8_antisym_lieE (i : Fin 8) {ψ : Fin 8 → ℂ} {v : M}
    (hev : ∀ j, ⁅SerreE j, v⁆ = 0) (hwt : ∀ j, ⁅SerreH j, v⁆ = ψ j • v) (j : Fin 8) :
    ⁅SerreE j, Zt i v⁆ = 0 := by
  by_cases hji : j = i
  · rw [hji]; exact e8_antisym_lieE_self i hev hwt
  · exact e8_antisym_lieE_ne hji hev

/-- **The `e₈` case, weight part.**  The vector `Zt i v` has weight `2ψ - αᵢ`
whenever `v` has weight `ψ`. -/
theorem e8_antisym_lieH (i : Fin 8) {ψ : Fin 8 → ℂ} {v : M}
    (hwt : ∀ j, ⁅SerreH j, v⁆ = ψ j • v) (j : Fin 8) :
    ⁅SerreH j, Zt i v⁆ = (2 * ψ j - ((CartanMatrix.E₈ j i : ℤ) : ℂ)) • Zt i v := by
  rw [Zt]
  have hfv : ⁅SerreH j, SerreF i⁆ = (-(((CartanMatrix.E₈ j i : ℤ) : ℂ))) • SerreF i := by
    rw [serreLie_H_F j i,
      ← Int.cast_smul_eq_zsmul ℂ (-(CartanMatrix.E₈ j i : ℤ)) (SerreF i), Int.cast_neg]
  exact lie_h_antisym_tmul (SerreH j) (SerreF i) (((CartanMatrix.E₈ j i : ℤ) : ℂ)) (ψ j) v
    hfv (hwt j)

/-- **Tensor product of two highest weight vectors.**  If `u₁` and `u₂` are both killed by all
`eⱼ` (in particular, if both have *dominant* weights), then so is `u₁ ⊗ u₂`. -/
theorem e8_hwt_tmul (u₁ u₂ : M) (h₁ : ∀ j, ⁅SerreE j, u₁⁆ = 0) (h₂ : ∀ j, ⁅SerreE j, u₂⁆ = 0) :
    ∀ j, ⁅SerreE j, u₁ ⊗ₜ[ℂ] u₂⁆ = 0 := by
  intro j
  rw [lie_tmul_right, h₁ j, h₂ j, zero_tmul, tmul_zero, add_zero]

/-- The weight of `u₁ ⊗ u₂` is the sum of the weights of `u₁` and `u₂`. -/
theorem e8_hwt_tmul_weight (u₁ u₂ : M) (ψ₁ ψ₂ : Fin 8 → ℂ)
    (h₁ : ∀ j, ⁅SerreH j, u₁⁆ = ψ₁ j • u₁) (h₂ : ∀ j, ⁅SerreH j, u₂⁆ = ψ₂ j • u₂) :
    ∀ j, ⁅SerreH j, u₁ ⊗ₜ[ℂ] u₂⁆ = (ψ₁ j + ψ₂ j) • (u₁ ⊗ₜ[ℂ] u₂) := by
  intro j
  rw [lie_tmul_right, h₁ j, h₂ j]
  simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  rw [← add_smul]

/-- The diagonal of the `E₈` Cartan matrix is `2`. -/
lemma E8_self (i : Fin 8) : CartanMatrix.E₈ i i = 2 := by
  fin_cases i <;> decide

/-- **Nonvanishing.**  If `v ≠ 0` and `fᵢ · v ≠ 0`, then `Zt i v ≠ 0`: the two tensor summands
involve two vectors of *different* `SerreH i`-weights, hence are linearly independent. -/
theorem e8_Zt_ne_zero (i : Fin 8) {ψ : Fin 8 → ℂ} {v : M}
    (hwt : ∀ j, ⁅SerreH j, v⁆ = ψ j • v) (hv : v ≠ 0) (ha : ⁅SerreF i, v⁆ ≠ 0) :
    Zt i v ≠ 0 := by
  intro hzero
  have hdiag : ⁅SerreH i, SerreF i⁆ = (-2 : ℂ) • SerreF i := by
    rw [serreLie_H_F i i, ← Int.cast_smul_eq_zsmul ℂ (-(CartanMatrix.E₈ i i : ℤ)) (SerreF i),
      Int.cast_neg, E8_self]
    norm_num
  have hsa : ⁅SerreH i, ⁅SerreF i, v⁆⁆ = (ψ i - 2) • ⁅SerreF i, v⁆ := by
    rw [leibniz_lie, hdiag, hwt i, smul_lie, lie_smul, ← add_smul]
    congr 1
    ring
  have hli : LinearIndependent ℂ ![(⁅SerreF i, v⁆ : M), v] :=
    linearIndependent_of_weight_ne hsa (hwt i) (by norm_num) ha hv
  have hsum : ∑ k : Fin 2, ![(⁅SerreF i, v⁆ : M), v] k ⊗ₜ[ℂ] ![v, -⁅SerreF i, v⁆] k = 0 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [TensorProduct.tmul_neg]
    rw [← sub_eq_add_neg,
      show (⁅SerreF i, v⁆) ⊗ₜ[ℂ] v - v ⊗ₜ[ℂ] (⁅SerreF i, v⁆) = 0 from hzero]
  have h0 := Commons.LinearAlgebra.TensorProduct.linearIndependent_tmul_sum hli
    ![v, -⁅SerreF i, v⁆] hsum 0
  exact hv (by simpa using h0)

/-- **The `e₈` case.**  If `v` is a highest weight vector of weight `ψ`, then for each simple root
`i` the vector `(fᵢ · v) ⊗ v - v ⊗ (fᵢ · v)` is again a highest weight vector, of weight `2ψ - αᵢ`. -/
theorem e8_hwt_antisym (i : Fin 8) {ψ : Fin 8 → ℂ} {v : M}
    (hev : ∀ j, ⁅SerreE j, v⁆ = 0) (hwt : ∀ j, ⁅SerreH j, v⁆ = ψ j • v) :
    (∀ j, ⁅SerreE j, Zt i v⁆ = 0) ∧
      (∀ j, ⁅SerreH j, Zt i v⁆ = (2 * ψ j - ((CartanMatrix.E₈ j i : ℤ) : ℂ)) • Zt i v) :=
  ⟨fun j => e8_antisym_lieE i hev hwt j, fun j => e8_antisym_lieH i hwt j⟩

end E8

end Submission.HWTTensor
