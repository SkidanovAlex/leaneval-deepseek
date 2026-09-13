import Submission.Grassmann.Restriction

/-!
# Fourier multipliers ("Laplacians") on `L(V,W)` and degree reduction

A **Laplacian** on `L(V,W)` (in the sense of arXiv:2209.04243, Section 3.6-3.9) is a Fourier
multiplier: it keeps the Fourier coefficients on a prescribed set of characters and kills the
rest.  Concretely we define, for a predicate `P` on the dual matrices,

  `lapMul P f = ∑_{X : P X} fhat f X • mchar X`.

The paper's hybrid Laplacians `L_{V₁,W₁}` correspond to the predicate
`P X := (V₁ ≤ range X) ∧ (X⁻¹ V₁ ≤ W₁)`; the `X`-Laplacians `L_X` to `P Y := X ≤ Y`.

The main result of this file is the **degree-reduction lemma**: a *derivative*, i.e. the
restriction `restr Q ι (lapMul P f)` of a Laplacian, has degree at most `deg f - k` whenever
every kept character drops its rank by at least `k` under the restriction (`degLe_restr_lapMul`).
This is the engine of the induction on the degree in the proof of the conditional
hypercontractive inequality (Lemma 3.6 of the paper).
-/

open Matrix Finset BigOperators
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

/-! ## General Fourier multipliers -/

/-- The Fourier multiplier ("Laplacian") associated with a predicate `P` on the dual
matrices: it keeps exactly the Fourier coefficients on characters `mchar X` with `P X`. -/
def lapMul {m n : ℕ} (P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ :=
  fun A => ∑ X : Matrix (Fin n) (Fin m) (ZMod 2),
    if P X then fhat f X * mchar X A else 0

/-- `lapMul P f` as a sum of characters. -/
lemma lapMul_eq_sum {m n : ℕ} (P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    lapMul P f = ∑ X : Matrix (Fin n) (Fin m) (ZMod 2),
      (if P X then fhat f X else 0) • (mchar X) := by
  funext A
  rw [lapMul, Finset.sum_apply]
  refine Finset.sum_congr rfl fun X _ => ?_
  by_cases hX : P X <;> simp [hX]

/-- The Fourier transform of a Laplacian. -/
theorem fhat_lapMul {m n : ℕ} (P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    fhat (lapMul P f) X = (if P X then (2 : ℂ) ^ (m * n) else 0) * fhat f X := by
  have h1 : (∑ A : Matrix (Fin m) (Fin n) (ZMod 2), lapMul P f A * mchar X A) =
      ∑ A : Matrix (Fin m) (Fin n) (ZMod 2),
        ∑ Y : Matrix (Fin n) (Fin m) (ZMod 2),
          (if P Y then fhat f Y * (mchar Y A * mchar X A) else 0) := by
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [lapMul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun Y _ => ?_
    by_cases hY : P Y <;> simp [hY, mul_assoc]
  have h2 : (∑ Y : Matrix (Fin n) (Fin m) (ZMod 2),
        ∑ A : Matrix (Fin m) (Fin n) (ZMod 2),
          (if P Y then fhat f Y * (mchar Y A * mchar X A) else 0)) =
      ∑ Y : Matrix (Fin n) (Fin m) (ZMod 2),
        (if P Y then fhat f Y * (if Y = X then (2 : ℂ) ^ (m * n) else 0) else 0) := by
    refine Finset.sum_congr rfl fun Y _ => ?_
    by_cases hY : P Y
    · simp only [if_pos hY]
      rw [← Finset.mul_sum, mchar_orthogonal Y X]
    · simp [if_neg hY]
  rw [fhat, h1, Finset.sum_comm, h2]
  by_cases hX : P X
  · rw [if_pos hX, Finset.sum_eq_single X]
    · simp [hX]; ring
    · intro Y _ hYX; simp [hYX]
    · intro h; exact absurd (Finset.mem_univ X) h
  · rw [if_neg hX, zero_mul]
    refine Finset.sum_eq_zero fun Y _ => ?_
    by_cases hYX : Y = X
    · rw [hYX]; simp [hX]
    · simp [hYX]

/-- A Laplacian does not increase the degree. -/
lemma degLe_lapMul {m n d : ℕ} {P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop}
    {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ} (hf : DegLe d f) : DegLe d (lapMul P f) := by
  intro X hX
  rw [fhat_lapMul]
  by_cases hP : P X
  · rw [if_pos hP, hf X hX, mul_zero]
  · rw [if_neg hP, zero_mul]

/-- `lapMul P f` is a sum of characters with `P`. -/
lemma lapMul_mem_charLe {m n d : ℕ} {P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop}
    {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ}
    (hP : ∀ X, P X → X.rank ≤ d) : lapMul P f ∈ charLe (m := m) (n := n) d := by
  rw [lapMul_eq_sum]
  refine Submodule.sum_mem _ fun X _ => ?_
  by_cases hX : P X
  · exact Submodule.smul_mem _ _ (mchar_mem_charLe (hP X hX))
  · simp [hX]

/-! ## Restrictions commute with sums -/

lemma restr_sum {m n m' n' : ℕ} {ι : Type*} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (inj : Matrix (Fin m) (Fin m') (ZMod 2)) (s : Finset ι)
    (g : ι → Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    restr Q inj (∑ i ∈ s, g i) = ∑ i ∈ s, restr Q inj (g i) := by
  funext A
  simp only [restr, Finset.sum_apply]

/-- The restriction of a Laplacian is a sum of restricted characters. -/
lemma restr_lapMul_eq {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (inj : Matrix (Fin m) (Fin m') (ZMod 2)) (P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    restr Q inj (lapMul P f) =
      ∑ X : Matrix (Fin n) (Fin m) (ZMod 2),
        (if P X then fhat f X else 0) •
          (mchar (Q * X * inj) : Matrix (Fin m') (Fin n') (ZMod 2) → ℂ) := by
  rw [lapMul_eq_sum, restr_sum]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [restr_smul, restr_mchar]

/-- **Degree reduction.**  If `f` has degree at most `d` and every character kept by `P`
loses at least `k` in rank under the restriction `(Q, ι)`, then the derivative
`restr Q ι (lapMul P f)` has degree at most `d - k`. -/
theorem degLe_restr_lapMul {m n m' n' d k : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (inj : Matrix (Fin m) (Fin m') (ZMod 2)) (P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop)
    {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ} (hf : DegLe d f)
    (hP : ∀ X, P X → (Q * X * inj).rank ≤ X.rank - k) :
    DegLe (d - k) (restr Q inj (lapMul P f)) := by
  rw [degLe_iff_mem_charLe]
  rw [restr_lapMul_eq]
  refine Submodule.sum_mem _ fun X _ => ?_
  by_cases hPX : P X
  · by_cases hfX : fhat f X = 0
    · rw [if_pos hPX, hfX, zero_smul]; exact Submodule.zero_mem _
    · rw [if_pos hPX]
      refine Submodule.smul_mem _ _ (mchar_mem_charLe ?_)
      have hrX : X.rank ≤ d := by
        by_contra hlt
        exact hfX (hf X (Nat.lt_of_not_le hlt))
      exact le_trans (hP X hPX) (Nat.sub_le_sub_right hrX k)
  · simp [hPX]

/-- The restriction of a *shifted* Laplacian is again a sum of restricted characters
(each with an extra factor `mchar X T`). -/
lemma restr_shift_lapMul_eq {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (inj : Matrix (Fin m) (Fin m') (ZMod 2)) (T : Matrix (Fin m) (Fin n) (ZMod 2))
    (P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    restr Q inj (shift T (lapMul P f)) =
      ∑ X : Matrix (Fin n) (Fin m) (ZMod 2),
        (if P X then fhat f X * mchar X T else 0) •
          (mchar (Q * X * inj) : Matrix (Fin m') (Fin n') (ZMod 2) → ℂ) := by
  funext A
  simp only [restr, shift, lapMul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun X _ => ?_
  by_cases hX : P X
  · rw [if_pos hX, if_pos hX]
    have hAX : mchar X (inj * A * Q) = mchar (Q * X * inj) A :=
      congrFun (restr_mchar Q inj X) A
    rw [mchar_add_right X (inj * A * Q) T, hAX]; ring
  · simp [hX]

/-- **Degree reduction for a shifted Laplacian/derivative**: the derivative
`D = (Δ_T ∘ L) restricted` lowers the degree by at least `k`, whenever every character kept by
`P` loses at least `k` in rank under the restriction. -/
theorem degLe_restr_shift_lapMul {m n m' n' d k : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (inj : Matrix (Fin m) (Fin m') (ZMod 2)) (T : Matrix (Fin m) (Fin n) (ZMod 2))
    (P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop)
    {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ} (hf : DegLe d f)
    (hP : ∀ X, P X → (Q * X * inj).rank ≤ X.rank - k) :
    DegLe (d - k) (restr Q inj (shift T (lapMul P f))) := by
  rw [degLe_iff_mem_charLe, restr_shift_lapMul_eq]
  refine Submodule.sum_mem _ fun X _ => ?_
  by_cases hPX : P X
  · by_cases hfX : fhat f X = 0
    · rw [if_pos hPX, hfX, zero_mul, zero_smul]; exact Submodule.zero_mem _
    · rw [if_pos hPX]
      refine Submodule.smul_mem _ _ (mchar_mem_charLe ?_)
      have hrX : X.rank ≤ d := by
        by_contra hlt
        exact hfX (hf X (Nat.lt_of_not_le hlt))
      exact le_trans (hP X hPX) (Nat.sub_le_sub_right hrX k)
  · simp [hPX]

/-! ## The normalised Laplacians (genuine projections)

`lapMul P` is `2^{mn}` times a projection; its normalisation `lapMulN P = 2^{-mn} • lapMul P`
is a genuine idempotent whose Fourier coefficients are simply *cut off* by `P`.  This is the
form in which compositions behave well (`lapMulN_comp`). -/

/-- The **normalised** Fourier multiplier associated with `P`. -/
def lapMulN {m n : ℕ} (P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ :=
  fun A => ((2 : ℂ) ^ (m * n))⁻¹ * lapMul P f A

lemma lapMulN_eq {m n : ℕ} (P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    lapMulN P f = ((2 : ℂ) ^ (m * n))⁻¹ • lapMul P f := rfl

/-- The Fourier transform of a normalised Laplacian cuts the Fourier coefficients off. -/
theorem fhat_lapMulN {m n : ℕ} (P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    fhat (lapMulN P f) X = (if P X then 1 else 0) * fhat f X := by
  rw [lapMulN_eq, fhat_smul, fhat_lapMul]
  have hc : ((2 : ℂ) ^ (m * n)) ≠ 0 := pow_ne_zero _ (by norm_num)
  by_cases hP : P X
  · simp only [if_pos hP]
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  · simp [if_neg hP]

/-- Two functions with the same Fourier coefficients are equal. -/
lemma eq_of_fhat_eq {m n : ℕ} {f g : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ}
    (h : ∀ X : Matrix (Fin n) (Fin m) (ZMod 2), fhat f X = fhat g X) : f = g := by
  funext A
  have h1 := fhat_inversion f A
  have h2 := fhat_inversion g A
  refine mul_left_cancel₀ (pow_ne_zero (m * n) (by norm_num : (2 : ℂ) ≠ 0)) ?_
  rw [← h1, ← h2]
  exact Finset.sum_congr rfl fun X _ => by rw [h X]

/-- Normalised Laplacians are idempotent. -/
theorem lapMulN_idem {m n : ℕ} (P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) : lapMulN P (lapMulN P f) = lapMulN P f := by
  refine eq_of_fhat_eq fun X => ?_
  have hL : fhat (lapMulN P (lapMulN P f)) X = (if P X then 1 else 0) * fhat (lapMulN P f) X :=
    fhat_lapMulN P (lapMulN P f) X
  have hR : fhat (lapMulN P f) X = (if P X then 1 else 0) * fhat f X := fhat_lapMulN P f X
  rw [hL, hR]
  by_cases hP : P X <;> simp [hP]

/-- **Composition of normalised Laplacians corresponds to intersecting the predicates.** -/
theorem lapMulN_comp {m n : ℕ} (P Q : Matrix (Fin n) (Fin m) (ZMod 2) → Prop)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    lapMulN P (lapMulN Q f) = lapMulN (fun X => P X ∧ Q X) f := by
  refine eq_of_fhat_eq fun X => ?_
  rw [fhat_lapMulN P (lapMulN Q f) X, fhat_lapMulN Q f X,
    fhat_lapMulN (fun X => P X ∧ Q X) f X]
  by_cases hP : P X <;> by_cases hQ : Q X <;> simp [hP, hQ]

/-- The normalised Laplacian with the constantly-true predicate is the identity. -/
theorem lapMulN_top {m n : ℕ} (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    lapMulN (fun _ : Matrix (Fin n) (Fin m) (ZMod 2) => True) f = f := by
  refine eq_of_fhat_eq fun X => ?_
  rw [fhat_lapMulN, if_pos trivial, one_mul]

/-- Normalised Laplacians do not increase the degree. -/
lemma degLe_lapMulN {m n d : ℕ} {P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop}
    {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ} (hf : DegLe d f) : DegLe d (lapMulN P f) := by
  intro X hX
  rw [fhat_lapMulN]
  by_cases hP : P X
  · rw [if_pos hP, hf X hX, mul_zero]
  · rw [if_neg hP, zero_mul]

/-- Scaling a function by a *nonzero* constant does not change its degree. -/
lemma degLe_smul_iff {m n d : ℕ} (c : ℂ) (hc : c ≠ 0)
    {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ} : DegLe d (c • f) ↔ DegLe d f := by
  have hf : ∀ X, fhat (c • f) X = c * fhat f X := fun X => fhat_smul c f X
  constructor
  · intro h X hX
    have := h X hX
    rw [hf X] at this
    exact (mul_eq_zero.mp this).resolve_left hc
  · intro h X hX
    rw [hf X, h X hX, mul_zero]

/-- **Degree reduction for shifted normalised Laplacians.** -/
theorem degLe_restr_shift_lapMulN {m n m' n' d k : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (inj : Matrix (Fin m) (Fin m') (ZMod 2)) (T : Matrix (Fin m) (Fin n) (ZMod 2))
    (P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop)
    {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ} (hf : DegLe d f)
    (hP : ∀ X, P X → (Q * X * inj).rank ≤ X.rank - k) :
    DegLe (d - k) (restr Q inj (shift T (lapMulN P f))) := by
  have hmain : restr Q inj (shift T (lapMulN P f)) =
      ((2 : ℂ) ^ (m * n))⁻¹ • restr Q inj (shift T (lapMul P f)) := by
    rw [lapMulN_eq, shift_smul, restr_smul]
  rw [hmain]
  exact (degLe_smul_iff _ (inv_ne_zero (pow_ne_zero _ (by norm_num))) ).mpr
    (degLe_restr_shift_lapMul Q inj T P hf hP)

end

end Submission.Grassmann
