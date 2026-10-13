import Mathlib
import Submission.Work.WilE4.CAD.gcd_core_kernel
import Submission.Work.WilE4.CAD.gcd_eq_of_combination

/-!
# Continuity of the gcd of two polynomial families with constant degrees

`gcd_cont_welloriented`: if `f`, `g` are families of real polynomials whose coefficients depend
continuously on a parameter `x : Fin m → ℝ`, if `natDegree (f x) = p`, `natDegree (g x) = q` and
`natDegree (gcd (f x) (g x)) = ν` hold for `x` near `x₀`, and `gcd (f x₀) (g x₀) ≠ 0`, then every
coefficient of the gcd is continuous at `x₀`.

The proof splits into cases according to the relation between `ν` and `p, q`:

* `ν = 0`: the (monic) gcd has degree `0`, hence equals `1`;
* `ν = p` (resp. `ν = q`): the gcd divides `f` (resp. `g`) and has the same degree, so it is the
  normalisation `f x / leadingCoeff (f x)`;
* `ν < p` and `ν < q`: here the gcd is recovered from a square Sylvester-type linear system whose
  matrix has continuous entries (coefficients of `f`, `g`) and is invertible on the neighbourhood;
  the (unique) solution is then given by the adjugate formula and is therefore continuous.  The two
  algebraic inputs (`gcd_core_kernel`, `gcd_eq_of_combination`) are proved in separate files.
-/

namespace Work.WilE4.CAD

open Polynomial
open scoped Classical

noncomputable section

/-! ## Auxiliary lemmas -/

/-- Coefficients of a family of polynomials transfer along an eventual equality of the families,
without changing the limit value. -/
theorem tendsto_coeff_of_eventuallyEq {α : Type*} [TopologicalSpace α] {x₀ : α}
    {P Q : α → Polynomial ℝ} (h : ∀ᶠ x in nhds x₀, P x = Q x)
    (hQ : ∀ k, ContinuousAt (fun x => (Q x).coeff k) x₀) (k : ℕ) :
    Filter.Tendsto (fun x => (P x).coeff k) (nhds x₀) (nhds ((P x₀).coeff k)) := by
  have hx₀ : P x₀ = Q x₀ := h.self_of_nhds
  have h1 : Filter.Tendsto (fun x => (Q x).coeff k) (nhds x₀) (nhds ((P x₀).coeff k)) := by
    rw [hx₀]
    exact (hQ k).tendsto
  refine h1.congr' ?_
  filter_upwards [h] with x hx
  rw [hx]

/-- The gcd of two polynomials over a field, when nonzero, is monic. -/
theorem monic_gcd_of_ne_zero {f g : Polynomial ℝ} (h : gcd f g ≠ 0) : (gcd f g).Monic := by
  rw [← normalize_gcd f g]
  exact monic_normalize h

/-- If a monic `m` divides `A ≠ 0` with `natDegree A = natDegree m`, then `m` is the
normalisation of `A`. -/
theorem eq_normalize_of_dvd_of_natDegree_eq {m A : Polynomial ℝ} (hm : m.Monic) (hA : A ≠ 0)
    (hdvd : m ∣ A) (hdeg : A.natDegree = m.natDegree) : m = normalize A := by
  obtain ⟨d, hd⟩ := hdvd
  have hdz : d ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hd
    exact hA hd
  have hm0 : m ≠ 0 := hm.ne_zero
  have hmul := natDegree_mul hm0 hdz
  rw [← hd] at hmul
  have hd0 : d.natDegree = 0 := by omega
  have hdc : d = C (d.coeff 0) := eq_C_of_natDegree_eq_zero hd0
  have hc0 : d.coeff 0 ≠ 0 := by
    intro hc
    rw [hdc, hc, C_0] at hdz
    exact hdz rfl
  have hunit : IsUnit (C (d.coeff 0) : Polynomial ℝ) :=
    (Polynomial.isUnit_C).mpr (isUnit_iff_ne_zero.mpr hc0)
  have hnorm : normalize (C (d.coeff 0) : Polynomial ℝ) = 1 := by
    rw [← hunit.unit_spec, normalize_coe_units]
  rw [hd, hdc, normalize_mul, hm.normalize_eq_self, hnorm, mul_one]

/-- Coefficients of `∑ i : Fin n, C (c i) * X ^ i`. -/
theorem coeff_sum_C_mul_X_pow {n k : ℕ} (c : Fin n → ℝ) :
    (∑ i : Fin n, C (c i) * X ^ (i : ℕ)).coeff k = if h : k < n then c ⟨k, h⟩ else 0 := by
  have hsum : (∑ i : Fin n, C (c i) * X ^ (i:ℕ) : Polynomial ℝ)
      = ∑ i : Fin n, monomial (i:ℕ) (c i) :=
    Finset.sum_congr rfl fun i _ => C_mul_X_pow_eq_monomial
  rw [hsum]
  have h2 : (∑ i : Fin n, monomial (i:ℕ) (c i)).coeff k
      = lcoeff ℝ k (∑ i : Fin n, monomial (i:ℕ) (c i)) := rfl
  rw [h2, map_sum]
  simp only [lcoeff_apply, coeff_monomial]
  by_cases hk : k < n
  · rw [dite_eq_left hk, Finset.sum_eq_single ⟨k, hk⟩]
    · simp
    · intro b _ hb
      have hne : ¬ ((b:ℕ) = k) := fun h => hb (Fin.ext h)
      simp [hne]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [dite_eq_right (by omega : ¬ k < n), Finset.sum_eq_zero]
    intro b _
    have hne : ¬ ((b:ℕ) = k) := fun h => hk (h ▸ b.isLt)
    simp [hne]

/-- Continuity of a shifted coefficient. -/
theorem continuous_coeff_X_pow_mul {α : Type*} [TopologicalSpace α] {p : α → Polynomial ℝ}
    (hp : ∀ k, Continuous fun x => (p x).coeff k) (n : ℕ) :
    ∀ k, Continuous fun x => (X ^ n * p x).coeff k := by
  intro k
  by_cases h : n ≤ k
  · have hxy : ∀ x, (X ^ n * p x).coeff k = (p x).coeff (k - n) := by
      intro x
      have := coeff_X_pow_mul (p x) n (k - n)
      rwa [Nat.sub_add_cancel h] at this
    simp only [hxy]
    exact hp _
  · have hnk : k < n := not_le.mp h
    have hxy : ∀ x, (X ^ n * p x).coeff k = 0 := by
      intro x
      exact (X_pow_dvd_iff.mp (dvd_mul_right _ _)) k hnk
    simp only [hxy]
    exact continuous_const

/-- Finite sums of functions continuous at a point. -/
theorem continuousAt_finset_sum {ι α M : Type*} [TopologicalSpace α] [AddCommMonoid M]
    [TopologicalSpace M] [ContinuousAdd M] {x₀ : α} {s : Finset ι} {F : ι → α → M}
    (h : ∀ i ∈ s, ContinuousAt (F i) x₀) :
    ContinuousAt (fun x => ∑ i ∈ s, F i x) x₀ := by
  classical
  induction s using Finset.induction with
  | empty => simpa using continuousAt_const (x := x₀) (y := (0 : M))
  | insert a s ha ih =>
    have h1 : ContinuousAt (fun x => F a x + ∑ i ∈ s, F i x) x₀ :=
      (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine h1.congr ?_
    filter_upwards with x
    rw [Finset.sum_insert ha]

/-! ## The Sylvester-type linear system (non-degenerate case) -/

variable {m : ℕ}

/-- Column polynomials: `X ^ a * f x` (for `a : Fin (q - ν)`) and `X ^ b * g x`
(for `b : Fin (p - ν)`). -/
def sylCol (f g : (Fin m → ℝ) → Polynomial ℝ) (p q ν : ℕ) (x : Fin m → ℝ)
    (j : Fin (q - ν) ⊕ Fin (p - ν)) : Polynomial ℝ :=
  j.elim (fun (a : Fin (q - ν)) => X ^ (a : ℕ) * f x) (fun (b : Fin (p - ν)) => X ^ (b : ℕ) * g x)

/-- Row degrees: `ν + a` and `q + b`; these run through `ν, ν+1, …, p+q-ν-1`. -/
def sylRowDeg (p q ν : ℕ) (i : Fin (q - ν) ⊕ Fin (p - ν)) : ℕ :=
  i.elim (fun (a : Fin (q - ν)) => ν + (a : ℕ)) (fun (b : Fin (p - ν)) => q + (b : ℕ))

/-- The Sylvester-type matrix: the `(i,j)` entry is the coefficient of `X ^ sylRowDeg i` in the
`j`-th column polynomial. -/
def sylMat (f g : (Fin m → ℝ) → Polynomial ℝ) (p q ν : ℕ) (x : Fin m → ℝ) :
    Matrix (Fin (q - ν) ⊕ Fin (p - ν)) (Fin (q - ν) ⊕ Fin (p - ν)) ℝ :=
  fun i j => (sylCol f g p q ν x j).coeff (sylRowDeg p q ν i)

/-- The right-hand side: the vector with a `1` in the row of degree `ν`. -/
def sylE (p q ν : ℕ) (hνq : ν < q) : (Fin (q - ν) ⊕ Fin (p - ν)) → ℝ :=
  Pi.single (Sum.inl ⟨0, Nat.sub_pos_of_lt hνq⟩) 1

/-- The candidate solution of the Sylvester system, given by the adjugate formula. -/
def sylY (f g : (Fin m → ℝ) → Polynomial ℝ) (p q ν : ℕ) (hνq : ν < q) (x : Fin m → ℝ) :
    (Fin (q - ν) ⊕ Fin (p - ν)) → ℝ :=
  ((sylMat f g p q ν x).det)⁻¹ • ((sylMat f g p q ν x).adjugate.mulVec (sylE p q ν hνq))

/-- The row index whose degree is `k`. -/
def sylRowOf (p q ν : ℕ) (k : ℕ) (hνq : ν < q) (hk1 : ν ≤ k) (hk2 : k ≤ p + q - ν - 1) :
    Fin (q - ν) ⊕ Fin (p - ν) :=
  if h : k ≤ q - 1 then Sum.inl (Fin.mk (k - ν) (by omega))
  else Sum.inr (Fin.mk (k - q) (by omega))

theorem sylRowDeg_inl {p q ν : ℕ} (a : Fin (q - ν)) :
    sylRowDeg p q ν (Sum.inl a) = ν + (a : ℕ) := rfl

theorem sylRowDeg_inr {p q ν : ℕ} (b : Fin (p - ν)) :
    sylRowDeg p q ν (Sum.inr b) = q + (b : ℕ) := rfl

theorem sylRowDeg_sylRowOf {p q ν k : ℕ} (hνq : ν < q) (hk1 : ν ≤ k)
    (hk2 : k ≤ p + q - ν - 1) : sylRowDeg p q ν (sylRowOf p q ν k hνq hk1 hk2) = k := by
  rw [sylRowOf]
  split_ifs with h
  · rw [sylRowDeg_inl, Fin.val_mk]; omega
  · rw [sylRowDeg_inr, Fin.val_mk]; omega

/-- The sum of the columns of the Sylvester matrix is a combination of `f x` and `g x`. -/
theorem sylCol_sum {f g : (Fin m → ℝ) → Polynomial ℝ} {p q ν : ℕ} {x : Fin m → ℝ}
    (y : (Fin (q - ν) ⊕ Fin (p - ν)) → ℝ) :
    (∑ j, C (y j) * sylCol f g p q ν x j)
      = (∑ a : Fin (q - ν), C (y (Sum.inl a)) * X ^ (a : ℕ)) * f x
        + (∑ b : Fin (p - ν), C (y (Sum.inr b)) * X ^ (b : ℕ)) * g x := by
  rw [Fintype.sum_sum_type]
  congr 1
  · rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by simp [sylCol, mul_assoc]
  · rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by simp [sylCol, mul_assoc]

/-- Coefficients of the sum of the columns. -/
theorem sylCol_coeff_sum {f g : (Fin m → ℝ) → Polynomial ℝ} {p q ν : ℕ} {x : Fin m → ℝ}
    (y : (Fin (q - ν) ⊕ Fin (p - ν)) → ℝ) (k : ℕ) :
    (∑ j, C (y j) * sylCol f g p q ν x j).coeff k
      = ∑ j, y j * (sylCol f g p q ν x j).coeff k := by
  have h2 : (∑ j, C (y j) * sylCol f g p q ν x j).coeff k
      = lcoeff ℝ k (∑ j, C (y j) * sylCol f g p q ν x j) := rfl
  rw [h2, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [lcoeff_apply, coeff_C_mul]

/-- The matrix-vector product, expanded. -/
theorem sylMat_mulVec {f g : (Fin m → ℝ) → Polynomial ℝ} {p q ν : ℕ} {x : Fin m → ℝ}
    (y : (Fin (q - ν) ⊕ Fin (p - ν)) → ℝ) (i : Fin (q - ν) ⊕ Fin (p - ν)) :
    (sylMat f g p q ν x).mulVec y i
      = (∑ j, C (y j) * sylCol f g p q ν x j).coeff (sylRowDeg p q ν i) := by
  rw [sylCol_coeff_sum]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => by rw [sylMat, mul_comm]

/-- The adjugate formula for the inverse of a matrix. -/
theorem matrix_mulVec_det_inv_smul_adjugate {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (h : M.det ≠ 0) (v : n → ℝ) :
    M.mulVec (M.det⁻¹ • (M.adjugate.mulVec v)) = v := by
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
    Matrix.one_mulVec, smul_smul, inv_mul_cancel₀ h, one_smul]

theorem sylMat_mulVec_sylY {f g : (Fin m → ℝ) → Polynomial ℝ} {p q ν : ℕ} {x : Fin m → ℝ}
    (hνq : ν < q) (hdet : (sylMat f g p q ν x).det ≠ 0) :
    (sylMat f g p q ν x).mulVec (sylY f g p q ν hνq x) = sylE p q ν hνq :=
  matrix_mulVec_det_inv_smul_adjugate _ hdet _

/-- **Kernel triviality.**  In the non-degenerate case the Sylvester-type matrix has trivial
kernel. -/
theorem sylMat_mulVec_eq_zero_of_ker {f g : (Fin m → ℝ) → Polynomial ℝ} {p q ν : ℕ}
    {x : Fin m → ℝ} (hA : f x ≠ 0) (hB : g x ≠ 0) (hAn : (f x).natDegree = p)
    (hBn : (g x).natDegree = q) (hgν : (gcd (f x) (g x)).natDegree = ν) (hνp : ν < p)
    (hνq : ν < q) {y : (Fin (q - ν) ⊕ Fin (p - ν)) → ℝ}
    (hy : (sylMat f g p q ν x).mulVec y = 0) : y = 0 := by
  classical
  set u : Polynomial ℝ := ∑ a : Fin (q - ν), C (y (Sum.inl a)) * X ^ (a : ℕ) with hu
  set v : Polynomial ℝ := ∑ b : Fin (p - ν), C (y (Sum.inr b)) * X ^ (b : ℕ) with hv
  have hW : (∑ j, C (y j) * sylCol f g p q ν x j) = u * f x + v * g x := by
    rw [sylCol_sum, ← hu, ← hv]
  have hlow : (u * f x + v * g x).coeff ν = 0 := by
    rw [← hW]
    have hrow := congrFun hy (Sum.inl (⟨0, Nat.sub_pos_of_lt hνq⟩ : Fin (q - ν)))
    rw [sylMat_mulVec, sylRowDeg_inl, Fin.val_mk, Nat.add_zero] at hrow
    exact hrow
  have hhigh : ∀ k, ν < k → k ≤ p + q - ν - 1 → (u * f x + v * g x).coeff k = 0 := by
    intro k hk1 hk2
    rw [← hW]
    have hrow := congrFun hy (sylRowOf p q ν k hνq (le_of_lt hk1) hk2)
    rw [sylMat_mulVec, sylRowDeg_sylRowOf hνq (le_of_lt hk1) hk2] at hrow
    exact hrow
  have hu_le : u.natDegree ≤ q - ν - 1 := by
    rw [hu]
    refine natDegree_sum_le_of_forall_le _ _ fun a _ => ?_
    calc (C (y (Sum.inl a)) * X ^ (a : ℕ) : Polynomial ℝ).natDegree
        ≤ (X ^ (a : ℕ) : Polynomial ℝ).natDegree := natDegree_C_mul_le _ _
      _ ≤ (a : ℕ) := natDegree_X_pow_le _
      _ ≤ q - ν - 1 := by have := a.isLt; omega
  have hv_le : v.natDegree ≤ p - ν - 1 := by
    rw [hv]
    refine natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
    calc (C (y (Sum.inr b)) * X ^ (b : ℕ) : Polynomial ℝ).natDegree
        ≤ (X ^ (b : ℕ) : Polynomial ℝ).natDegree := natDegree_C_mul_le _ _
      _ ≤ (b : ℕ) := natDegree_X_pow_le _
      _ ≤ p - ν - 1 := by have := b.isLt; omega
  obtain ⟨hu0, hv0⟩ :=
    gcd_core_kernel hA hB hAn hBn hgν hνp hνq hu_le hv_le hlow hhigh
  funext j
  rcases j with a | b
  · have h1 : y (Sum.inl a) = u.coeff (a : ℕ) := by
      rw [hu, coeff_sum_C_mul_X_pow, dite_eq_left a.isLt]
    rw [h1, hu0]
    simp
  · have h1 : y (Sum.inr b) = v.coeff (b : ℕ) := by
      rw [hv, coeff_sum_C_mul_X_pow, dite_eq_left b.isLt]
    rw [h1, hv0]
    simp

/-- In the non-degenerate case the Sylvester-type matrix is invertible. -/
theorem sylMat_det_ne_zero {f g : (Fin m → ℝ) → Polynomial ℝ} {p q ν : ℕ} {x : Fin m → ℝ}
    (hA : f x ≠ 0) (hB : g x ≠ 0) (hAn : (f x).natDegree = p) (hBn : (g x).natDegree = q)
    (hgν : (gcd (f x) (g x)).natDegree = ν) (hνp : ν < p) (hνq : ν < q) :
    (sylMat f g p q ν x).det ≠ 0 := by
  have hinj : Function.Injective (sylMat f g p q ν x).mulVec := by
    intro a b hab
    have h0 : (sylMat f g p q ν x).mulVec (a - b) = 0 := by
      rw [Matrix.mulVec_sub, hab, sub_self]
    have h1 : a - b = 0 := sylMat_mulVec_eq_zero_of_ker hA hB hAn hBn hgν hνp hνq h0
    exact sub_eq_zero.mp h1
  have hlr : IsLeftRegular (sylMat f g p q ν x) :=
    Matrix.isLeftRegular_iff_mulVec_injective.mpr hinj
  exact Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.isLeftRegular_iff_nonsingular.mp hlr)

/-- **Identification of the gcd in the non-degenerate case.** -/
theorem sylY_spec {f g : (Fin m → ℝ) → Polynomial ℝ} {p q ν : ℕ} {x : Fin m → ℝ}
    (hA : f x ≠ 0) (hB : g x ≠ 0) (hAn : (f x).natDegree = p) (hBn : (g x).natDegree = q)
    (hgν : (gcd (f x) (g x)).natDegree = ν) (hνp : ν < p) (hνq : ν < q) :
    (∑ j, C (sylY f g p q ν hνq x j) * sylCol f g p q ν x j) = gcd (f x) (g x) := by
  classical
  set y := sylY f g p q ν hνq x with hy
  have hdet := sylMat_det_ne_zero hA hB hAn hBn hgν hνp hνq
  have hMv := sylMat_mulVec_sylY (f := f) (g := g) (x := x) hνq hdet
  set u : Polynomial ℝ := ∑ a : Fin (q - ν), C (y (Sum.inl a)) * X ^ (a : ℕ) with hu
  set v : Polynomial ℝ := ∑ b : Fin (p - ν), C (y (Sum.inr b)) * X ^ (b : ℕ) with hv
  have hW : (∑ j, C (y j) * sylCol f g p q ν x j) = u * f x + v * g x := by
    rw [sylCol_sum, ← hu, ← hv]
  have hlow : (∑ j, C (y j) * sylCol f g p q ν x j).coeff ν = 1 := by
    have hrow := congrFun hMv (Sum.inl (⟨0, Nat.sub_pos_of_lt hνq⟩ : Fin (q - ν)))
    rw [sylMat_mulVec, sylRowDeg_inl, Fin.val_mk, Nat.add_zero] at hrow
    rw [hrow]
    simp [sylE]
  have hhigh : ∀ k, ν < k → k ≤ p + q - ν - 1 →
      (∑ j, C (y j) * sylCol f g p q ν x j).coeff k = 0 := by
    intro k hk1 hk2
    have hrow := congrFun hMv (sylRowOf p q ν k hνq (le_of_lt hk1) hk2)
    rw [sylMat_mulVec, sylRowDeg_sylRowOf hνq (le_of_lt hk1) hk2] at hrow
    rw [hrow, sylE, Pi.single_eq_of_ne]
    intro hcontra
    have hd := congrArg (sylRowDeg p q ν) hcontra
    rw [sylRowDeg_sylRowOf hνq (le_of_lt hk1) hk2, sylRowDeg_inl, Fin.val_mk,
      Nat.add_zero] at hd
    omega
  have hu_le : u.natDegree ≤ q - ν - 1 := by
    rw [hu]
    refine natDegree_sum_le_of_forall_le _ _ fun a _ => ?_
    calc (C (y (Sum.inl a)) * X ^ (a : ℕ) : Polynomial ℝ).natDegree
        ≤ (X ^ (a : ℕ) : Polynomial ℝ).natDegree := natDegree_C_mul_le _ _
      _ ≤ (a : ℕ) := natDegree_X_pow_le _
      _ ≤ q - ν - 1 := by have := a.isLt; omega
  have hv_le : v.natDegree ≤ p - ν - 1 := by
    rw [hv]
    refine natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
    calc (C (y (Sum.inr b)) * X ^ (b : ℕ) : Polynomial ℝ).natDegree
        ≤ (X ^ (b : ℕ) : Polynomial ℝ).natDegree := natDegree_C_mul_le _ _
      _ ≤ (b : ℕ) := natDegree_X_pow_le _
      _ ≤ p - ν - 1 := by have := b.isLt; omega
  exact gcd_eq_of_combination hA hB hAn hBn hgν hνp hνq hu_le hv_le hW hhigh hlow

/-- Continuity of the entries of the Sylvester-type matrix. -/
theorem continuous_sylMat {f g : (Fin m → ℝ) → Polynomial ℝ} {p q ν : ℕ}
    (hf : ∀ k, Continuous fun x => (f x).coeff k)
    (hg : ∀ k, Continuous fun x => (g x).coeff k) :
    Continuous fun x : Fin m → ℝ => sylMat f g p q ν x := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  rcases i with a | b <;> rcases j with c | d
  · simpa only [sylMat, sylCol, sylRowDeg, Sum.elim_inl] using
      continuous_coeff_X_pow_mul hf (c : ℕ) (ν + (a : ℕ))
  · simpa only [sylMat, sylCol, sylRowDeg, Sum.elim_inl, Sum.elim_inr] using
      continuous_coeff_X_pow_mul hg (d : ℕ) (ν + (a : ℕ))
  · simpa only [sylMat, sylCol, sylRowDeg, Sum.elim_inl, Sum.elim_inr] using
      continuous_coeff_X_pow_mul hf (c : ℕ) (q + (b : ℕ))
  · simpa only [sylMat, sylCol, sylRowDeg, Sum.elim_inr] using
      continuous_coeff_X_pow_mul hg (d : ℕ) (q + (b : ℕ))

/-- Continuity at `x₀` of the components of the candidate solution. -/
theorem continuousAt_sylY {f g : (Fin m → ℝ) → Polynomial ℝ} {p q ν : ℕ} {x₀ : Fin m → ℝ}
    (hf : ∀ k, Continuous fun x => (f x).coeff k)
    (hg : ∀ k, Continuous fun x => (g x).coeff k) (hνq : ν < q)
    (hdet : (sylMat f g p q ν x₀).det ≠ 0) :
    ∀ j, ContinuousAt (fun x => sylY f g p q ν hνq x j) x₀ := by
  intro j
  have hMcont : Continuous fun x : Fin m → ℝ => sylMat f g p q ν x := continuous_sylMat hf hg
  have hdetcont : ContinuousAt (fun x : Fin m → ℝ => (sylMat f g p q ν x).det) x₀ :=
    hMcont.matrix_det.continuousAt
  have hinv : ContinuousAt (fun x : Fin m → ℝ => ((sylMat f g p q ν x).det)⁻¹) x₀ :=
    hdetcont.inv₀ hdet
  have hadj : ContinuousAt
      (fun x : Fin m → ℝ => ((sylMat f g p q ν x).adjugate.mulVec (sylE p q ν hνq)) j) x₀ := by
    simp only [Matrix.mulVec, dotProduct]
    refine continuousAt_finset_sum fun l _ => ?_
    have h1 : ContinuousAt (fun x : Fin m → ℝ => (sylMat f g p q ν x).adjugate j) x₀ :=
      (continuous_apply j).continuousAt.comp (hMcont.matrix_adjugate.continuousAt)
    have h2 : ContinuousAt (fun x : Fin m → ℝ => (sylMat f g p q ν x).adjugate j l) x₀ :=
      (continuous_apply l).continuousAt.comp h1
    exact h2.mul continuousAt_const
  have hthis : (fun x => sylY f g p q ν hνq x j)
      = (fun x => ((sylMat f g p q ν x).det)⁻¹ *
          (((sylMat f g p q ν x).adjugate.mulVec (sylE p q ν hνq)) j)) := by
    funext x
    rw [sylY, Pi.smul_apply, smul_eq_mul]
  rw [hthis]
  exact hinv.mul hadj

/-- Continuity at `x₀` of the coefficients of the candidate `W`. -/
theorem continuousAt_coeff_sylW {f g : (Fin m → ℝ) → Polynomial ℝ} {p q ν : ℕ} {x₀ : Fin m → ℝ}
    (hf : ∀ k, Continuous fun x => (f x).coeff k)
    (hg : ∀ k, Continuous fun x => (g x).coeff k) (hνq : ν < q)
    (hdet : (sylMat f g p q ν x₀).det ≠ 0) (k : ℕ) :
    ContinuousAt (fun x => (∑ j, C (sylY f g p q ν hνq x j) * sylCol f g p q ν x j).coeff k) x₀ := by
  have hY := continuousAt_sylY hf hg hνq hdet
  have hfun : (fun x => (∑ j, C (sylY f g p q ν hνq x j) * sylCol f g p q ν x j).coeff k)
      = (fun x => ∑ j, sylY f g p q ν hνq x j * (sylCol f g p q ν x j).coeff k) := by
    funext x
    exact sylCol_coeff_sum (y := sylY f g p q ν hνq x) k
  rw [hfun]
  refine continuousAt_finset_sum fun j _ => ?_
  refine (hY j).mul ?_
  rcases j with a | b
  · simpa only [sylCol, Sum.elim_inl] using
      (continuous_coeff_X_pow_mul hf (a : ℕ) k).continuousAt
  · simpa only [sylCol, Sum.elim_inr] using
      (continuous_coeff_X_pow_mul hg (b : ℕ) k).continuousAt

/-! ## The main theorem -/

theorem gcd_cont_welloriented {m : ℕ} (f g : (Fin m → ℝ) → Polynomial ℝ) (x₀ : Fin m → ℝ) (ν p q : ℕ)
    (hf : ∀ k, Continuous fun x => (f x).coeff k) (hg : ∀ k, Continuous fun x => (g x).coeff k)
    (hp : ∀ᶠ x in nhds x₀, (f x).natDegree = p) (hq : ∀ᶠ x in nhds x₀, (g x).natDegree = q)
    (hν : ∀ᶠ x in nhds x₀, (gcd (f x) (g x)).natDegree = ν)
    (h0 : gcd (f x₀) (g x₀) ≠ 0) :
    ∀ k, Filter.Tendsto (fun x => (gcd (f x) (g x)).coeff k) (nhds x₀) (nhds ((gcd (f x₀) (g x₀)).coeff k)) := by
  classical
  -- the set of parameters where all the degree conditions hold
  have hne : ∀ᶠ x in nhds x₀, ¬(f x = 0 ∧ g x = 0) := by
    have hfg : f x₀ ≠ 0 ∨ g x₀ ≠ 0 := by
      by_contra h
      push_neg at h
      exact h0 (by rw [h.1, h.2]; simp)
    rcases hfg with hf0 | hg0
    · obtain ⟨k, hk⟩ : ∃ k, (f x₀).coeff k ≠ 0 := by
        by_contra h
        push_neg at h
        exact hf0 (Polynomial.ext fun n => by simpa using h n)
      have hop : {x : Fin m → ℝ | (f x).coeff k ≠ 0} ∈ nhds x₀ :=
        (isOpen_ne.preimage (hf k)).mem_nhds hk
      filter_upwards [hop] with x hx
      exact fun ⟨h1, _⟩ => hx (by rw [h1]; simp)
    · obtain ⟨k, hk⟩ : ∃ k, (g x₀).coeff k ≠ 0 := by
        by_contra h
        push_neg at h
        exact hg0 (Polynomial.ext fun n => by simpa using h n)
      have hop : {x : Fin m → ℝ | (g x).coeff k ≠ 0} ∈ nhds x₀ :=
        (isOpen_ne.preimage (hg k)).mem_nhds hk
      filter_upwards [hop] with x hx
      exact fun ⟨_, h2⟩ => hx (by rw [h2]; simp)
  have hU : ∀ᶠ x in nhds x₀, (f x).natDegree = p ∧ (g x).natDegree = q ∧
      (gcd (f x) (g x)).natDegree = ν ∧ ¬(f x = 0 ∧ g x = 0) := by
    filter_upwards [hp, hq, hν, hne] with x h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have key : ∀ G : (Fin m → ℝ) → Polynomial ℝ,
      (∀ᶠ x in nhds x₀, gcd (f x) (g x) = G x) →
      (∀ k, ContinuousAt (fun x => (G x).coeff k) x₀) →
      ∀ k, Filter.Tendsto (fun x => (gcd (f x) (g x)).coeff k) (nhds x₀)
        (nhds ((gcd (f x₀) (g x₀)).coeff k)) :=
    fun G hG hGc k => tendsto_coeff_of_eventuallyEq hG hGc k
  by_cases hν0 : ν = 0
  · -- case `ν = 0`: the gcd is the constant polynomial `1`
    refine key (fun _ => 1) ?_ ?_
    · filter_upwards [hU] with x hx
      obtain ⟨-, -, hgd, hne'⟩ := hx
      refine eq_one_of_monic_natDegree_zero ?_ (by rw [hgd, hν0])
      refine monic_gcd_of_ne_zero ?_
      intro hzero
      exact hne' ((gcd_eq_zero_iff _ _).mp hzero)
    · intro k
      exact continuousAt_const
  · by_cases hνp : ν = p
    · -- case `ν = p`: the gcd is the normalisation of `f`
      refine key (fun x => C (((f x).coeff p)⁻¹) * f x) ?_ ?_
      · filter_upwards [hU] with x hx
        obtain ⟨hfd, -, hgd, hne'⟩ := hx
        have hfx : f x ≠ 0 := by
          rintro h; rw [h, natDegree_zero] at hfd; omega
        have hmon : (gcd (f x) (g x)).Monic :=
          monic_gcd_of_ne_zero (fun hzero => hne' ((gcd_eq_zero_iff _ _).mp hzero))
        have h1 : gcd (f x) (g x) = normalize (f x) :=
          eq_normalize_of_dvd_of_natDegree_eq hmon hfx (gcd_dvd_left _ _)
            (by rw [hfd, hgd, hνp])
        have h2 : normalize (f x) = C (((f x).coeff p)⁻¹) * f x := by
          rw [normalize_apply, coe_normUnit_of_ne_zero hfx, leadingCoeff, hfd, mul_comm]
        rw [h1, h2]
      · intro k
        have hfun : (fun x => (C (((f x).coeff p)⁻¹) * f x).coeff k)
            = fun x => ((f x).coeff p)⁻¹ * (f x).coeff k := by
          funext x
          rw [coeff_C_mul]
        rw [hfun]
        have hx0 : (f x₀).natDegree = p := (hU.self_of_nhds).1
        have hxp : (f x₀).coeff p ≠ 0 := by
          have hne0 : f x₀ ≠ 0 := by
            rintro h; rw [h, natDegree_zero] at hx0; omega
          rw [← hx0, coeff_natDegree]
          exact leadingCoeff_ne_zero.mpr hne0
        exact ((hf p).continuousAt.inv₀ hxp).mul ((hf k).continuousAt)
    · by_cases hνq : ν = q
      · -- case `ν = q`: the gcd is the normalisation of `g`
        refine key (fun x => C (((g x).coeff q)⁻¹) * g x) ?_ ?_
        · filter_upwards [hU] with x hx
          obtain ⟨-, hgd, hggd, hne'⟩ := hx
          have hgx : g x ≠ 0 := by
            rintro h; rw [h, natDegree_zero] at hgd; omega
          have hmon : (gcd (f x) (g x)).Monic :=
            monic_gcd_of_ne_zero (fun hzero => hne' ((gcd_eq_zero_iff _ _).mp hzero))
          have h1 : gcd (f x) (g x) = normalize (g x) :=
            eq_normalize_of_dvd_of_natDegree_eq hmon hgx (gcd_dvd_right _ _)
              (by rw [hgd, hggd, hνq])
          have h2 : normalize (g x) = C (((g x).coeff q)⁻¹) * g x := by
            rw [normalize_apply, coe_normUnit_of_ne_zero hgx, leadingCoeff, hgd, mul_comm]
          rw [h1, h2]
        · intro k
          have hfun : (fun x => (C (((g x).coeff q)⁻¹) * g x).coeff k)
              = fun x => ((g x).coeff q)⁻¹ * (g x).coeff k := by
            funext x
            rw [coeff_C_mul]
          rw [hfun]
          have hx0 : (g x₀).natDegree = q := (hU.self_of_nhds).2.1
          have hxq : (g x₀).coeff q ≠ 0 := by
            have hne0 : g x₀ ≠ 0 := by
              rintro h; rw [h, natDegree_zero] at hx0; omega
            rw [← hx0, coeff_natDegree]
            exact leadingCoeff_ne_zero.mpr hne0
          exact ((hg q).continuousAt.inv₀ hxq).mul ((hg k).continuousAt)
      · -- case `ν < p` and `ν < q`: the Sylvester system
        have hx0 := hU.self_of_nhds
        have hfx0 : f x₀ ≠ 0 := by
          rintro h
          have hν' := hx0.2.2.1
          rw [h, gcd_zero_left, natDegree_normalize, hx0.2.1] at hν'
          exact hνq hν'.symm
        have hgx0 : g x₀ ≠ 0 := by
          rintro h
          have hν' := hx0.2.2.1
          rw [h, gcd_zero_right, natDegree_normalize, hx0.1] at hν'
          exact hνp hν'.symm
        have hνltp : ν < p := by
          by_contra hcon
          have hle : ν ≤ p := by
            obtain ⟨d, hd⟩ := gcd_dvd_left (f x₀) (g x₀)
            have hd0 : d ≠ 0 := by
              rintro rfl; rw [mul_zero] at hd; exact hfx0 hd
            have hmul := natDegree_mul (monic_gcd_of_ne_zero h0).ne_zero hd0
            rw [← hd, hx0.2.2.1] at hmul
            omega
          exact hνp (le_antisymm hle (not_lt.mp hcon))
        have hνltq : ν < q := by
          by_contra hcon
          have hle : ν ≤ q := by
            obtain ⟨d, hd⟩ := gcd_dvd_right (f x₀) (g x₀)
            have hd0 : d ≠ 0 := by
              rintro rfl; rw [mul_zero] at hd; exact hgx0 hd
            have hmul := natDegree_mul (monic_gcd_of_ne_zero h0).ne_zero hd0
            rw [← hd, hx0.2.2.1] at hmul
            omega
          exact hνq (le_antisymm hle (not_lt.mp hcon))
        refine key (fun x => ∑ j, C (sylY f g p q ν hνltq x j) * sylCol f g p q ν x j) ?_ ?_
        · filter_upwards [hU] with x hx
          obtain ⟨hfd, hgd, hggd, hne'⟩ := hx
          have hfx : f x ≠ 0 := by
            rintro h; rw [h, natDegree_zero] at hfd; omega
          have hgx : g x ≠ 0 := by
            rintro h; rw [h, natDegree_zero] at hgd; omega
          exact (sylY_spec hfx hgx hfd hgd hggd hνltp hνltq).symm
        · intro k
          exact continuousAt_coeff_sylW hf hg hνltq
            (sylMat_det_ne_zero hfx0 hgx0 hx0.1 hx0.2.1 hx0.2.2.1 hνltp hνltq) k

end

end Work.WilE4.CAD
