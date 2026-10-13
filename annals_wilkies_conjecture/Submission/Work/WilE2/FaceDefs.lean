/-
  Work.WilE2 — support module for the slice lemma `Work.WilE2.face_hits`.

  Slicing an EA set in `ℝ^{n+1}` by a coordinate hyperplane `x j = σ` produces an EA set in `ℝⁿ`:
  the affine exponents lose the `j`-th coordinate (whose contribution is absorbed into the constant
  term), and the atoms are the corresponding polynomial substitutions.

  * `faceLift j σ y` — `Fin n → ℝ → Fin (n+1) → ℝ`, the point equal to `y` away from `j` and `σ` at
    `j` (`Fin.insertNth`); `faceProj j x` is the inverse (`Fin.removeNth`).
  * `chainFace c j σ` — the restricted chain on `Fin n`: the `j`-th coordinate is removed from the
    linear part and its contribution `a k j * σ` added to the constant term.
  * `faceVarMap` / `faceSub` — the corresponding atom substitution: `X (.inl j) ↦ C σ` and the other
    variables relabelled by `j.succAbove`.  It is total (the `if` branch on the existence of a
    preimage), so it needs no non-emptiness assumption on `Fin n`.
  * `faceSub_eval` — the fundamental identity
    `eaEval (chainFace c j σ) (faceSub j σ Q) y = eaEval c Q (faceLift j σ y)`.
  * `totalDegree_aeval_le_mul`, `atomDeg_faceSub_le` — the substitution does not raise the degree.
  * `sum_image_le_nat` — a `Finset`-sum bookkeeping lemma (a map neither injective nor surjective).
-/
import Mathlib
import Submission.Work.WilE2.VcbDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE2
open WilkiesDesign WilkiesDesign.E

/-! ## §1. The lift/projection of the hyperplane `x j = σ` -/

/-- `y ↦ (σ at j, y elsewhere)`: the inverse of the projection `x ↦ x ∘ j.succAbove` on `{x j = σ}`. -/
def faceLift {n : ℕ} (j : Fin (n+1)) (σ : ℝ) (y : Fin n → ℝ) : Fin (n+1) → ℝ := j.insertNth σ y

/-- The projection `x ↦ x ∘ j.succAbove`, inverse to `faceLift` on the hyperplane `x j = σ`. -/
def faceProj {n : ℕ} (j : Fin (n+1)) (x : Fin (n+1) → ℝ) : Fin n → ℝ := j.removeNth x

theorem faceLift_apply_same {n : ℕ} (j : Fin (n+1)) (σ : ℝ) (y : Fin n → ℝ) :
    faceLift j σ y j = σ := by simp [faceLift]

theorem faceLift_apply_succAbove {n : ℕ} (j : Fin (n+1)) (σ : ℝ) (y : Fin n → ℝ) (i : Fin n) :
    faceLift j σ y (j.succAbove i) = y i := by simp [faceLift]

/-- Away from `j`, `faceLift` is just `y` (at the preimage index). -/
theorem faceLift_apply_of_ne {n : ℕ} (j : Fin (n+1)) (σ : ℝ) (y : Fin n → ℝ) {i : Fin (n+1)}
    (hi : i ≠ j) : faceLift j σ y i = y (Classical.choose (Fin.exists_succAbove_eq hi)) := by
  conv_lhs => rw [← Classical.choose_spec (Fin.exists_succAbove_eq hi)]
  exact faceLift_apply_succAbove j σ y _

theorem faceProj_apply {n : ℕ} (j : Fin (n+1)) (x : Fin (n+1) → ℝ) (i : Fin n) :
    faceProj j x i = x (j.succAbove i) := rfl

@[simp] theorem faceProj_faceLift {n : ℕ} (j : Fin (n+1)) (σ : ℝ) (y : Fin n → ℝ) :
    faceProj j (faceLift j σ y) = y := by
  funext i; simp [faceProj, faceLift]

theorem faceLift_faceProj {n : ℕ} (j : Fin (n+1)) (σ : ℝ) (x : Fin (n+1) → ℝ) (hx : x j = σ) :
    faceLift j σ (faceProj j x) = x := by
  have hupd : Function.update x j σ = x := by
    rw [Function.update_eq_self_iff]; exact hx.symm
  simp only [faceLift, faceProj, Fin.insertNth_removeNth, hupd]

theorem continuous_faceLift {n : ℕ} (j : Fin (n+1)) (σ : ℝ) :
    Continuous (fun y : Fin n → ℝ => faceLift j σ y) := by
  refine continuous_pi fun i => ?_
  by_cases hi : ∃ i' : Fin n, j.succAbove i' = i
  · obtain ⟨i', hi'⟩ := hi
    refine (continuous_apply (A := fun _ : Fin n => ℝ) i').congr fun y => ?_
    rw [← hi', faceLift_apply_succAbove]
  · have hij : i = j := by by_contra h; exact hi (Fin.exists_succAbove_eq h)
    rw [hij]
    exact continuous_const.congr fun y => (faceLift_apply_same j σ y).symm

/-! ## §2. The restricted chain -/

/-- The chain obtained by restricting an `(n+1)`-dimensional EA chain to the hyperplane `x j = σ`:
the `j`-th coordinate leaves the linear form and enters the constant term. -/
def chainFace {n r : ℕ} (c : EAChain (n+1) r) (j : Fin (n+1)) (σ : ℝ) : EAChain n r where
  a := fun k i => c.a k (j.succAbove i)
  b := fun k => c.b k + c.a k j * σ

@[simp] theorem chainFace_a {n r : ℕ} (c : EAChain (n+1) r) (j : Fin (n+1)) (σ : ℝ) (k : Fin r)
    (i : Fin n) : (chainFace c j σ).a k i = c.a k (j.succAbove i) := rfl

@[simp] theorem chainFace_b {n r : ℕ} (c : EAChain (n+1) r) (j : Fin (n+1)) (σ : ℝ) (k : Fin r) :
    (chainFace c j σ).b k = c.b k + c.a k j * σ := rfl

/-- The chain function of the restricted chain is the original one on the hyperplane. -/
theorem chainFace_ell {n r : ℕ} (c : EAChain (n+1) r) (j : Fin (n+1)) (σ : ℝ) (k : Fin r)
    (y : Fin n → ℝ) : (chainFace c j σ).ell k y = c.ell k (faceLift j σ y) := by
  have hsum : (∑ i : Fin (n+1), c.a k i * faceLift j σ y i)
      = c.a k j * σ + ∑ i : Fin n, c.a k (j.succAbove i) * y i := by
    rw [Fin.sum_univ_succAbove (fun i => c.a k i * faceLift j σ y i) j]
    simp [faceLift_apply_same, faceLift_apply_succAbove]
  simp only [EAChain.ell, chainFace]
  rw [hsum]; ring

/-! ## §3. The atom substitution -/

/-- The variable substitution underlying the slice: `Sum.inl j` becomes the constant `σ` and the
other `Sum.inl i` are relabelled by (a choice of) their `j.succAbove`-preimage.  The definition is
by cases on the existence of such a preimage, which makes it total also when `n = 0`. -/
noncomputable def faceVarMap {n r : ℕ} (j : Fin (n+1)) (σ : ℝ) : Fin (n+1) ⊕ Fin r → EAPoly n r :=
  fun s => match s with
    | Sum.inl i => if h : ∃ i' : Fin n, j.succAbove i' = i
        then MvPolynomial.X (Sum.inl (Classical.choose h))
        else MvPolynomial.C σ
    | Sum.inr k => MvPolynomial.X (Sum.inr k)

/-- The atom of the slice: `Q` with the `j`-th variable set to `σ` and the remaining variables
relabelled. -/
noncomputable def faceSub {n r : ℕ} (j : Fin (n+1)) (σ : ℝ) (Q : EAPoly (n+1) r) : EAPoly n r :=
  MvPolynomial.aeval (faceVarMap j σ) Q

@[simp] theorem faceVarMap_inr {n r : ℕ} (j : Fin (n+1)) (σ : ℝ) (k : Fin r) :
    faceVarMap j σ (Sum.inr k) = MvPolynomial.X (Sum.inr k) := rfl

/-- **The slicing identity.**  Evaluating the substituted atom on the restricted chain at `y` is the
same as evaluating the original atom on the original chain at the lifted point. -/
theorem faceSub_eval {n r : ℕ} (c : EAChain (n+1) r) (j : Fin (n+1)) (σ : ℝ)
    (Q : EAPoly (n+1) r) (y : Fin n → ℝ) :
    eaEval (chainFace c j σ) (faceSub j σ Q) y = eaEval c Q (faceLift j σ y) := by
  have key : ∀ s : Fin (n+1) ⊕ Fin r,
      MvPolynomial.aeval (Sum.elim y fun k => Real.exp ((chainFace c j σ).ell k y))
          (faceVarMap j σ s)
        = Sum.elim (faceLift j σ y) (fun k => Real.exp (c.ell k (faceLift j σ y))) s := by
    intro s
    match s with
    | Sum.inl i =>
      by_cases hi : ∃ i' : Fin n, j.succAbove i' = i
      · rw [faceVarMap, dite_eq_left hi]
        simp only [MvPolynomial.aeval_X, Sum.elim_inl]
        conv_rhs => rw [← Classical.choose_spec hi]
        exact (faceLift_apply_succAbove j σ y (Classical.choose hi)).symm
      · rw [faceVarMap, dite_eq_right hi]
        have hij : i = j := by
          by_contra h
          exact hi (Fin.exists_succAbove_eq h)
        subst hij
        simp only [MvPolynomial.aeval_C, Sum.elim_inl, Algebra.algebraMap_self_apply,
          faceLift_apply_same]
    | Sum.inr k =>
      simp only [faceVarMap, MvPolynomial.aeval_X, Sum.elim_inr, chainFace_ell]
  have hcomp : ((MvPolynomial.aeval (Sum.elim y fun k => Real.exp ((chainFace c j σ).ell k y))).comp
        (MvPolynomial.aeval (faceVarMap j σ)))
      = MvPolynomial.aeval (Sum.elim (faceLift j σ y)
          (fun k => Real.exp (c.ell k (faceLift j σ y)))) := by
    rw [MvPolynomial.comp_aeval]
    congr 1
    exact funext key
  exact congrArg (fun f => f Q) hcomp

/-! ## §4. The substitution does not raise the degree -/

/-- Substituting each variable by a polynomial of total degree `≤ d` multiplies the total degree by
at most `d`. -/
theorem totalDegree_aeval_le_mul {R : Type*} [CommSemiring R] {σ τ : Type*}
    (f : σ → MvPolynomial τ R) (d : ℕ) (hf : ∀ s, (f s).totalDegree ≤ d) (p : MvPolynomial σ R) :
    (MvPolynomial.aeval f p).totalDegree ≤ d * p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun v hv => ?_
  rw [MvPolynomial.aeval_monomial]
  have h1 : (MvPolynomial.C (p.coeff v) * Finsupp.prod v (fun i k => f i ^ k)).totalDegree
      ≤ (MvPolynomial.C (p.coeff v)).totalDegree
        + (Finsupp.prod v (fun i k => f i ^ k)).totalDegree :=
    MvPolynomial.totalDegree_mul _ _
  rw [MvPolynomial.totalDegree_C, zero_add] at h1
  refine h1.trans ?_
  rw [Finsupp.prod]
  have h2 : (∏ i ∈ v.support, f i ^ v i).totalDegree
      ≤ ∑ i ∈ v.support, (f i ^ v i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
  refine h2.trans ?_
  have h3 : ∑ i ∈ v.support, (f i ^ v i).totalDegree ≤ ∑ i ∈ v.support, v i * d := by
    refine Finset.sum_le_sum fun i _ => ?_
    exact (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left (v i) (hf i))
  refine h3.trans ?_
  rw [← Finset.sum_mul]
  rw [show (∑ i ∈ v.support, v i) = v.sum (fun _ e => e) from rfl]
  rw [Nat.mul_comm]
  exact Nat.mul_le_mul_left d (MvPolynomial.le_totalDegree hv)

/-- Every value of the face substitution has total degree at most one. -/
theorem faceVarMap_totalDegree_le {n r : ℕ} (j : Fin (n+1)) (σ : ℝ)
    (s : Fin (n+1) ⊕ Fin r) : (faceVarMap j σ s).totalDegree ≤ 1 := by
  match s with
  | Sum.inl i =>
    by_cases h : ∃ i' : Fin n, j.succAbove i' = i
    · rw [faceVarMap, dite_eq_left h, MvPolynomial.totalDegree_X]
    · rw [faceVarMap, dite_eq_right h, MvPolynomial.totalDegree_C]; omega
  | Sum.inr k => rw [faceVarMap, MvPolynomial.totalDegree_X]

/-- The slice substitution does not raise the atom degree, so the degree budget `D` is preserved. -/
theorem atomDeg_faceSub_le {n r : ℕ} (j : Fin (n+1)) (σ : ℝ) (Q : EAPoly (n+1) r) :
    atomDeg (faceSub j σ Q) ≤ atomDeg Q := by
  have h := totalDegree_aeval_le_mul (faceVarMap j σ) 1
    (fun s => faceVarMap_totalDegree_le j σ s) Q
  simp only [Nat.one_mul] at h
  show (faceSub j σ Q).totalDegree + 1 ≤ Q.totalDegree + 1
  exact Nat.add_le_add_right h 1

/-! ## §5. A `Finset`-sum bookkeeping lemma -/

/-- Summing over the image of a map is bounded by summing over the source with multiplicity. -/
theorem sum_image_le_nat {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β) (g : β → ℕ) :
    ∑ x ∈ s.image f, g x ≤ ∑ x ∈ s, g (f x) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.image_insert, Finset.sum_insert ha]
    by_cases hy : f a ∈ Finset.image f s
    · rw [Finset.insert_eq_of_mem hy]
      exact le_trans ih (Nat.le_add_left _ _)
    · rw [Finset.sum_insert hy]
      exact Nat.add_le_add_left ih (g (f a))

end Work.WilE2
