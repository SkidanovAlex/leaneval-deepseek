/-
# Auxiliary definitions for the truncation rank growth lemmas

This file collects the small definitions used in the proof that the truncation rank
`rk (trunc i G)` grows at most linearly with slope `subDim rk (pctModule K)`.

* `tauSub k W` : the image of a submodule `W ≤ R^m` under the entrywise twist `τ^k`.
* `truncRow G i` : the family of rows of the truncation `trunc i G`, indexed by `Fin (q*i)`.
* `rhoProj m i` : the projection `R^{m(i+1)} → R^{mi}` forgetting the last "degree slice".
* `tauSlice m i` : the "last degree" coordinates of an element of `R^{m(i+1)}`, as a map to `R^m`.
* `iotaSlice m i` : its section, putting a vector of `R^m` in the last degree.
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension.ConstCoeffModule
import Submission.Work.ORHughesFree.NaturalExtension.EltDeg
import Submission.Work.ORVonNeumann.Regular.matrix_vonNeumannRegular
import Submission.Work.ORHughesFree.MatrixBlocks.flattenBlocks_mul

set_option autoImplicit false
universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- The image of a submodule `W ≤ R^m` under the entrywise twist `τ^k = (ofAdd k) • ·`
(twisted scalar action: `c • (τ^k y) = τ^k ((τ^{-k} c) y)`). -/
def tauSub (R : Type u) [Ring R] [MulSemiringAction (Multiplicative ℤ) R] (k : ℤ) {m : ℕ}
    (W : Submodule R (Fin m → R)) : Submodule R (Fin m → R) where
  carrier := {x | ∃ y ∈ W, ∀ i, x i = (Multiplicative.ofAdd k) • (y i)}
  zero_mem' := ⟨0, W.zero_mem, fun i => by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    exact ⟨a + b, W.add_mem ha hb, fun i => by
      simp only [Pi.add_apply, hx i, hy i, smul_add]⟩
  smul_mem' := by
    rintro c x ⟨y, hy, hx⟩
    refine ⟨((Multiplicative.ofAdd (-k)) • c) • y, W.smul_mem _ hy, fun i => ?_⟩
    have key : (Multiplicative.ofAdd k) * (Multiplicative.ofAdd (-k)) = 1 := by
      rw [← ofAdd_add]; simp
    calc (c • x) i = c * x i := rfl
      _ = c * ((Multiplicative.ofAdd k) • y i) := by rw [hx i]
      _ = ((Multiplicative.ofAdd k) • ((Multiplicative.ofAdd (-k)) • c))
            * ((Multiplicative.ofAdd k) • y i) := by rw [smul_smul, key]; simp
      _ = (Multiplicative.ofAdd k) • (((Multiplicative.ofAdd (-k)) • c) * y i) := by
            rw [smul_mul']
      _ = (Multiplicative.ofAdd k) • ((((Multiplicative.ofAdd (-k)) • c) • y) i) := rfl

@[simp]
theorem mem_tauSub {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] {k : ℤ}
    {m : ℕ} {W : Submodule R (Fin m → R)} {x : Fin m → R} :
    x ∈ tauSub R k W ↔ ∃ y ∈ W, ∀ i, x i = (Multiplicative.ofAdd k) • (y i) := Iff.rfl

theorem tauSub_mono {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] {k : ℤ}
    {m : ℕ} {W W' : Submodule R (Fin m → R)} (h : W ≤ W') :
    tauSub R k W ≤ tauSub R k W' := by
  rintro x ⟨y, hy, hx⟩
  exact ⟨y, h hy, hx⟩

@[simp]
theorem tauSub_bot {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] (k : ℤ)
    {m : ℕ} : tauSub R k (⊥ : Submodule R (Fin m → R)) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [mem_tauSub] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  rw [Submodule.mem_bot] at hy ⊢
  ext i
  rw [Pi.zero_apply, hxy i, hy]
  simp

/-- The `x`-th row of `trunc i G`, as an element of `R^{m*i}`. -/
def truncRow {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] {q m : ℕ}
    (G : Matrix (Fin q) (Fin m) (SkewL R)) (i : ℕ) :
    Fin (q * i) → (Fin (m * i) → R) :=
  fun x => fun y => trunc i G x y

/-- The projection `R^{m·(i+1)} → R^{m·i}` forgetting the last degree slice. -/
def rhoProj (R : Type u) [Ring R] (m i : ℕ) :
    (Fin (m * (i + 1)) → R) →ₗ[R] (Fin (m * i) → R) where
  toFun x := fun j => x (finProdFinEquiv (j.divNat, Fin.castLE (Nat.le_succ i) j.modNat))
  map_add' x y := by funext j; simp
  map_smul' c x := by funext j; simp

@[simp]
theorem rhoProj_apply {R : Type u} [Ring R] (m i : ℕ) (x : Fin (m * (i + 1)) → R)
    (j : Fin (m * i)) :
    rhoProj R m i x j =
      x (finProdFinEquiv (j.divNat, Fin.castLE (Nat.le_succ i) j.modNat)) := rfl

/-- The last degree slice of an element of `R^{m·(i+1)}`. -/
def tauSlice (R : Type u) [Ring R] (m i : ℕ) :
    (Fin (m * (i + 1)) → R) →ₗ[R] (Fin m → R) where
  toFun x := fun d => x (finProdFinEquiv (d, Fin.last i))
  map_add' x y := by funext d; simp
  map_smul' c x := by funext d; simp

@[simp]
theorem tauSlice_apply {R : Type u} [Ring R] (m i : ℕ) (x : Fin (m * (i + 1)) → R)
    (d : Fin m) :
    tauSlice R m i x d = x (finProdFinEquiv (d, Fin.last i)) := rfl

/-- The section of `tauSlice` putting a vector of `R^m` in the last degree slice. -/
def iotaSlice (R : Type u) [Ring R] (m i : ℕ) :
    (Fin m → R) →ₗ[R] (Fin (m * (i + 1)) → R) where
  toFun z := fun j => if j.modNat = Fin.last i then z j.divNat else 0
  map_add' x y := by
    funext j
    by_cases h : j.modNat = Fin.last i <;> simp [h]
  map_smul' c x := by
    funext j
    by_cases h : j.modNat = Fin.last i <;> simp [h]

section WeakInverse

/-- Every matrix over a von Neumann regular ring admits a weak inverse:
`A * U * A = A`. -/
theorem exists_mul_mul_eq_self {R : Type u} [Ring R] [VonNeumannRegularRing R] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) R) : ∃ U : Matrix (Fin m) (Fin n) R, A * U * A = A := by
  have hreg : Work.ORVonNeumann.VonNeumannRegular R :=
    fun x => (inferInstance : VonNeumannRegularRing R).exists_mul_inverse x
  obtain ⟨P, _hPP, hspan, hfix⟩ :=
    Work.ORVonNeumann.Regular.exists_idempotent_of_vectors (R := R) hreg m n (fun i j => A i j)
  have hAP : A * P = A := by
    ext i j
    have h := congrFun (hfix i) j
    simp only [Matrix.vecMul_apply, Matrix.col_apply, dotProduct, Matrix.mul_apply] at h ⊢
    exact h
  have hrow : ∀ l : Fin m, ∃ c : Fin n → R, ∑ i, c i • (fun j => A i j) = P l := by
    intro l
    have h := (Submodule.mem_span_range_iff_exists_fun R).mp (hspan (Pi.single l 1))
    rwa [Work.ORVonNeumann.Regular.row_eq_single_vecMul P l] at h
  choose c hc using hrow
  set X : Matrix (Fin m) (Fin n) R := fun l i => c l i with hX
  have hXA : X * A = P := by
    ext l j
    rw [Matrix.mul_apply, hX]
    have h := congrFun (hc l) j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    simpa using h
  exact ⟨X, by rw [Matrix.mul_assoc, hXA, hAP]⟩

end WeakInverse

section PowT

variable {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]

/-- The inverse of `t` in `R[t^{±1};τ]`. -/
noncomputable def skewTinv : SkewL R :=
  SkewMonoidAlgebra.single (Multiplicative.ofAdd (-1 : ℤ)) 1

theorem skewLaurentT_mul_skewTinv : (skewLaurentT : SkewL R) * skewTinv = 1 := by
  rw [skewLaurentT, skewTinv, SkewMonoidAlgebra.single_mul_single]
  simp

theorem skewTinv_mul_skewLaurentT : skewTinv * (skewLaurentT : SkewL R) = 1 := by
  rw [skewLaurentT, skewTinv, SkewMonoidAlgebra.single_mul_single]
  simp

theorem skewLaurentT_pow_eq_single (n : ℕ) :
    (skewLaurentT : SkewL R) ^ n =
      SkewMonoidAlgebra.single (Multiplicative.ofAdd (n : ℤ)) 1 := by
  induction n with
  | zero => simp [skewLaurentT]
  | succ n ih =>
      rw [pow_succ, ih, skewLaurentT, SkewMonoidAlgebra.single_mul_single,
        ← ofAdd_add, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring]
      congr 1
      simp

theorem skewTinv_pow_eq_single (n : ℕ) :
    (skewTinv (R := R)) ^ n =
      SkewMonoidAlgebra.single (Multiplicative.ofAdd (-(n : ℤ))) 1 := by
  induction n with
  | zero => simp [skewTinv]
  | succ n ih =>
      rw [pow_succ, ih, skewTinv, SkewMonoidAlgebra.single_mul_single,
        ← ofAdd_add, show (-(n : ℤ) + -1) = (-((n + 1 : ℕ) : ℤ)) by push_cast; ring]
      congr 1
      simp

theorem skewLaurentT_pow_mul_skewTinv_pow (n : ℕ) :
    (skewLaurentT : SkewL R) ^ n * (skewTinv (R := R)) ^ n = 1 := by
  rw [skewLaurentT_pow_eq_single, skewTinv_pow_eq_single,
    SkewMonoidAlgebra.single_mul_single,
    ← ofAdd_add, show ((n : ℤ) + -(n : ℤ)) = ((0 : ℕ) : ℤ) by ring]
  congr 1
  simp

theorem coeffElt_skewLaurentT_mul (f : SkewL R) (k : ℤ) :
    coeffElt ((skewLaurentT : SkewL R) * f) k =
      (Multiplicative.ofAdd (1 : ℤ)) • coeffElt f (k - 1) := by
  rw [skewLaurentT, coeffElt, coeffElt, SkewMonoidAlgebra.coeff_single_mul]
  have h : (Multiplicative.ofAdd (1 : ℤ))⁻¹ * Multiplicative.ofAdd k
      = Multiplicative.ofAdd (k - 1) := by
    rw [← ofAdd_neg, ← ofAdd_add]; congr 1; ring
  rw [h]; simp

theorem coeffElt_skewTinv_mul (f : SkewL R) (k : ℤ) :
    coeffElt (skewTinv (R := R) * f) k =
      (Multiplicative.ofAdd (-1 : ℤ)) • coeffElt f (k + 1) := by
  rw [skewTinv, coeffElt, coeffElt, SkewMonoidAlgebra.coeff_single_mul]
  have h : (Multiplicative.ofAdd (-1 : ℤ))⁻¹ * Multiplicative.ofAdd k
      = Multiplicative.ofAdd (k + 1) := by
    rw [← ofAdd_neg, ← ofAdd_add]; congr 1; ring
  rw [h]; simp

theorem coeffElt_powT_mul (n : ℕ) (f : SkewL R) (k : ℤ) :
    coeffElt (((skewLaurentT : SkewL R) ^ n) * f) k =
      (Multiplicative.ofAdd (n : ℤ)) • coeffElt f (k - n) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_assoc, coeffElt_skewLaurentT_mul, ih, smul_smul, ← ofAdd_add,
        show (1 + (n : ℤ)) = ((n + 1 : ℕ) : ℤ) by push_cast; ring]
      congr 1
      push_cast; ring

theorem coeffElt_powTinv_mul (n : ℕ) (f : SkewL R) (k : ℤ) :
    coeffElt (((skewTinv (R := R)) ^ n) * f) k =
      (Multiplicative.ofAdd (-(n : ℤ))) • coeffElt f (k + n) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_assoc, coeffElt_skewTinv_mul, ih, smul_smul, ← ofAdd_add,
        show (-1 + -(n : ℤ)) = (-((n + 1 : ℕ) : ℤ)) by push_cast; ring]
      congr 1
      push_cast; ring

end PowT

section RowApply

variable {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]

theorem truncRow_apply {q m : ℕ} (G : Matrix (Fin q) (Fin m) (SkewL R)) (N : ℕ)
    (x : Fin (q * N)) (y : Fin (m * N)) :
    truncRow G N x y =
      coeffElt ((skewLaurentT : SkewL R) ^ (x.modNat : ℕ) * G x.divNat y.divNat)
        ((y.modNat : ℕ) : ℤ) := by
  rw [truncRow, trunc_apply, coeffElt_powT_mul]
  simp only [Matrix.smul_apply, coeffMat_apply]

end RowApply

section Slice

variable {R : Type u} [Ring R]

@[simp]
theorem iotaSlice_apply (m i : ℕ) (z : Fin m → R) (j : Fin (m * (i + 1))) :
    iotaSlice R m i z j = if j.modNat = Fin.last i then z j.divNat else 0 := rfl

theorem iotaSlice_tauSlice (m i : ℕ) {x : Fin (m * (i + 1)) → R}
    (hx : ∀ j : Fin (m * i),
      x (finProdFinEquiv (j.divNat, Fin.castLE (Nat.le_succ i) j.modNat)) = 0) :
    iotaSlice R m i (tauSlice R m i x) = x := by
  funext j
  rw [iotaSlice_apply, tauSlice_apply]
  by_cases h : j.modNat = Fin.last i
  · rw [if_pos h, ← h]
    congr 1
    exact Equiv.apply_symm_apply finProdFinEquiv j
  · rw [if_neg h]
    have hv : (j.modNat : ℕ) < i := by
      have h1 := j.modNat.isLt
      have h2 : (j.modNat : ℕ) ≠ i := fun hh => h (Fin.ext hh)
      omega
    set s' : Fin i := ⟨(j.modNat : ℕ), hv⟩ with hs'
    have hs'cast : Fin.castLE (Nat.le_succ i) s' = j.modNat := Fin.ext rfl
    have hs'm : ((j.divNat, Fin.castLE (Nat.le_succ i) s') : Fin m × Fin (i + 1))
        = finProdFinEquiv.symm j := by
      rw [finProdFinEquiv_symm_apply]
      exact Prod.ext rfl hs'cast
    have hfp : finProdFinEquiv (j.divNat, Fin.castLE (Nat.le_succ i) s') = j := by
      rw [hs'm]
      exact Equiv.apply_symm_apply finProdFinEquiv j
    have key := hx (finProdFinEquiv (j.divNat, s'))
    rw [MatrixBlocks.finProdFinEquiv_fst, MatrixBlocks.finProdFinEquiv_snd] at key
    rw [hfp] at key
    exact key.symm

end Slice

end Work.ORHughesFree.NaturalExtension
