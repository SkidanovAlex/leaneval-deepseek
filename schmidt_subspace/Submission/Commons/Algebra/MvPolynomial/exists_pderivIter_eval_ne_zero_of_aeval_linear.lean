import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Submission.Commons.Algebra.MvPolynomial.pderivIter_properties

set_option linter.unusedSectionVars false

namespace Commons.Algebra.MvPolynomial

open scoped BigOperators
open _root_.MvPolynomial

section

variable {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]

/-! ## Linear substitutions

We study the algebra map `φ : ℚ[X_x] → ℚ[X_y]` given by `X x ↦ ∑ y, A x y * X y`, the
substitution along the linear forms determined by the matrix `A`.  The main chain rule
(`pderiv_aeval_linForm`) computes the effect of a partial derivative on such a substituted
polynomial. -/

/-- The linear form `∑ y, A x y * X y` in the variables indexed by `τ`. -/
noncomputable def linForm (A : σ → τ → ℚ) (x : σ) : MvPolynomial τ ℚ :=
  ∑ y, C (A x y) * X y

lemma aeval_pderiv_X (f : σ → MvPolynomial τ ℚ) (x i : σ) :
    aeval f (pderiv x (X i : MvPolynomial σ ℚ))
      = (if i = x then 1 else 0 : MvPolynomial τ ℚ) := by
  rw [pderiv_X, Pi.single_apply]
  by_cases h : i = x <;> simp [h]

lemma pderiv_linForm (A : σ → τ → ℚ) (y : τ) (i : σ) :
    pderiv y (linForm A i) = C (A i y) := by
  rw [linForm, map_sum]
  rw [Finset.sum_eq_single y]
  · rw [pderiv_C_mul, pderiv_X, Pi.single_eq_same, mul_one]
  · intro b _ hb
    rw [pderiv_C_mul, pderiv_X, Pi.single_eq_of_ne hb, mul_zero]
  · intro hy; exact absurd (Finset.mem_univ y) hy

lemma sum_C_single (A : σ → τ → ℚ) (y : τ) (i : σ) :
    (∑ x, C (A x y) * (if i = x then (1 : MvPolynomial τ ℚ) else 0)) = C (A i y) := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro x _ hx
    rw [if_neg (fun h => hx h.symm), mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

lemma sum_mul_assoc (U B : σ → MvPolynomial τ ℚ) (Q : MvPolynomial τ ℚ) :
    (∑ x, U x * (B x * Q)) = (∑ x, U x * B x) * Q := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro x _; ring

lemma sum_mul_ite (U : σ → MvPolynomial τ ℚ) (R : MvPolynomial τ ℚ) (i : σ) :
    (∑ x, U x * (R * (if i = x then (1 : MvPolynomial τ ℚ) else 0)))
      = R * (∑ x, U x * (if i = x then (1 : MvPolynomial τ ℚ) else 0)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro x _; ring

lemma chain_mulX (A : σ → τ → ℚ) (y : τ) (p : MvPolynomial σ ℚ) (i : σ)
    (hp : pderiv y (aeval (linForm A) p) =
      ∑ x, C (A x y) * aeval (linForm A) (pderiv x p)) :
    pderiv y (aeval (linForm A) (p * X i)) =
      ∑ x, C (A x y) * aeval (linForm A) (pderiv x (p * X i)) := by
  have hgen : ∀ x, aeval (linForm A) (pderiv x (p * X i))
      = aeval (linForm A) (pderiv x p) * linForm A i
        + aeval (linForm A) p * (if i = x then 1 else 0) := by
    intro x
    simp only [pderiv_mul, map_add, map_mul, aeval_X, aeval_pderiv_X]
  have hL : pderiv y (aeval (linForm A) (p * X i)) =
      (∑ x, C (A x y) * aeval (linForm A) (pderiv x p)) * linForm A i
        + aeval (linForm A) p * C (A i y) := by
    rw [map_mul, aeval_X, pderiv_mul, hp, pderiv_linForm]
  have hR : (∑ x, C (A x y) * aeval (linForm A) (pderiv x (p * X i)))
      = (∑ x, C (A x y) * aeval (linForm A) (pderiv x p)) * linForm A i
        + aeval (linForm A) p * C (A i y) := by
    calc (∑ x, C (A x y) * aeval (linForm A) (pderiv x (p * X i)))
        = ∑ x, C (A x y) * (aeval (linForm A) (pderiv x p) * linForm A i
            + aeval (linForm A) p * (if i = x then 1 else 0)) := by
          apply Finset.sum_congr rfl; intro x _; rw [hgen x]
      _ = ∑ x, (C (A x y) * (aeval (linForm A) (pderiv x p) * linForm A i)
            + C (A x y) * (aeval (linForm A) p * (if i = x then 1 else 0))) := by
          apply Finset.sum_congr rfl; intro x _; rw [mul_add]
      _ = (∑ x, C (A x y) * (aeval (linForm A) (pderiv x p) * linForm A i))
            + (∑ x, C (A x y) * (aeval (linForm A) p * (if i = x then 1 else 0))) := by
          rw [Finset.sum_add_distrib]
      _ = (∑ x, C (A x y) * aeval (linForm A) (pderiv x p)) * linForm A i
            + aeval (linForm A) p * C (A i y) := by
          rw [sum_mul_assoc, sum_mul_ite, sum_C_single]
  rw [hL, hR]

/-- **Chain rule for a linear substitution.**  Differentiating the substituted polynomial
`P(X_x ↦ ∑ y, A x y X_y)` in the direction `y` gives the sum, over the source variables `x`, of
`A x y` times the substituted `x`-th partial derivative of `P`. -/
lemma pderiv_aeval_linForm (A : σ → τ → ℚ) (y : τ) (Q : MvPolynomial σ ℚ) :
    pderiv y (aeval (linForm A) Q) =
      ∑ x, C (A x y) * aeval (linForm A) (pderiv x Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p i hp => exact chain_mulX A y p i hp

/-! ## The weight bound

For a multi-index `ν` in the target variables, the multi-indices `J` that can occur when
expanding `∂^ν (P ∘ A)` satisfy `J x ≤ ∑_y [A x y ≠ 0] · ν y`. -/

/-- The weight bound `wtBound A ν x = ∑_y [A x y ≠ 0] · ν y`. -/
noncomputable def wtBound (A : σ → τ → ℚ) (ν : τ →₀ ℕ) (x : σ) : ℕ :=
  ∑ y, if A x y = 0 then 0 else ν y

lemma wtBound_eq_support (A : σ → τ → ℚ) (ν : τ →₀ ℕ) (x : σ) :
    wtBound A ν x = ∑ y ∈ ν.support, if A x y = 0 then 0 else ν y := by
  rw [wtBound]
  exact (Finset.sum_subset (Finset.subset_univ ν.support)
    (fun y _ hy => by rw [Finsupp.notMem_support_iff.mp hy]; simp)).symm

lemma wtBound_add_single (A : σ → τ → ℚ) (ν : τ →₀ ℕ) (a : τ) (b : ℕ) (x : σ) :
    wtBound A (ν + Finsupp.single a b) x = wtBound A ν x + (if A x a = 0 then 0 else b) := by
  have h1 : ∀ y, (if A x y = 0 then (0 : ℕ) else (ν + Finsupp.single a b) y)
      = (if A x y = 0 then 0 else ν y)
        + (if A x y = 0 then 0 else (Finsupp.single a b) y) := by
    intro y
    by_cases h : A x y = 0
    · simp [h]
    · simp only [h, ↓reduceIte]
      rw [Finsupp.add_apply]
  rw [wtBound, Finset.sum_congr rfl (fun y _ => h1 y), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single a]
  · rw [Finsupp.single_eq_same]
  · intro y _ hy
    rw [Finsupp.single_eq_of_ne hy]
    by_cases h : A x y = 0 <;> simp [h]
  · intro h; exact absurd (Finset.mem_univ a) h

lemma wtBound_mono (A : σ → τ → ℚ) {ν₁ ν₂ : τ →₀ ℕ} (h : ν₁ ≤ ν₂) (x : σ) :
    wtBound A ν₁ x ≤ wtBound A ν₂ x := by
  rw [wtBound, wtBound]
  apply Finset.sum_le_sum
  intro y _
  by_cases hA : A x y = 0
  · simp [hA]
  · simp only [hA, ↓reduceIte]
    exact Finsupp.le_def.mp h y

/-- Adding a single `x`-th derivative stays within the bound for `ν + e_a`, provided
`A x a ≠ 0`. -/
lemma add_single_le_wtBound (A : σ → τ → ℚ) {ν : τ →₀ ℕ} {J : σ →₀ ℕ}
    (hJ : ∀ x', J x' ≤ wtBound A ν x') {a : τ} {x : σ} (hA : A x a ≠ 0) :
    ∀ x', (J + Finsupp.single x (1 : ℕ)) x' ≤ wtBound A (ν + Finsupp.single a (1 : ℕ)) x' := by
  intro x'
  rw [wtBound_add_single]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  by_cases hxx : x = x'
  · rw [if_pos hxx]
    have hA' : A x' a ≠ 0 := by rw [← hxx]; exact hA
    rw [if_neg hA']
    exact Nat.succ_le_succ (hJ x')
  · rw [if_neg hxx]
    have := hJ x'
    omega

/-! ## The span of the derivatives that can occur -/

/-- The `ℚ`-subspace of `ℚ[X_y]` spanned by the substituted derivatives `∂^J P` with
`J ≤ wtBound A ν`. -/
noncomputable def derivSpan (A : σ → τ → ℚ) (ν : τ →₀ ℕ) (P : MvPolynomial σ ℚ) :
    Submodule ℚ (MvPolynomial τ ℚ) :=
  Submodule.span ℚ {g : MvPolynomial τ ℚ |
    ∃ J : σ →₀ ℕ, (∀ x, J x ≤ wtBound A ν x) ∧ g = aeval (linForm A) (pderivIter J P)}

/-- One more derivative keeps us inside the span. -/
lemma pderiv_mem_derivSpan (A : σ → τ → ℚ) (P : MvPolynomial σ ℚ) {f : τ →₀ ℕ} {a : τ}
    {J : σ →₀ ℕ} (hJ : ∀ x, J x ≤ wtBound A f x) :
    pderiv a (aeval (linForm A) (pderivIter J P))
      ∈ derivSpan A (f + Finsupp.single a (1 : ℕ)) P := by
  rw [pderiv_aeval_linForm]
  apply Submodule.sum_mem
  intro x _
  have hpd : pderiv x (pderivIter J P) = pderivIter (J + Finsupp.single x (1 : ℕ)) P :=
    (pderivIter_properties (R := ℚ) (σ := σ)).2.2.1 x J P
  rw [hpd]
  by_cases hA : A x a = 0
  · rw [hA, C_0, zero_mul]
    exact Submodule.zero_mem _
  · have hle : ∀ x', (J + Finsupp.single x (1 : ℕ)) x' ≤ wtBound A (f + Finsupp.single a (1 : ℕ)) x' :=
      add_single_le_wtBound A hJ hA
    have hmem : aeval (linForm A) (pderivIter (J + Finsupp.single x (1 : ℕ)) P)
        ∈ derivSpan A (f + Finsupp.single a (1 : ℕ)) P :=
      Submodule.subset_span ⟨_, hle, rfl⟩
    rw [C_mul']
    exact Submodule.smul_mem _ (A x a) hmem

/-- Differentiating once maps `derivSpan A f P` into `derivSpan A (f + e_a) P`. -/
lemma derivSpan_le_map_pderiv (A : σ → τ → ℚ) (f : τ →₀ ℕ) (a : τ) (P : MvPolynomial σ ℚ) :
    Submodule.map (pderiv a).toLinearMap (derivSpan A f P)
      ≤ derivSpan A (f + Finsupp.single a (1 : ℕ)) P := by
  unfold derivSpan
  rw [Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro g ⟨g', ⟨J, hJ, rfl⟩, rfl⟩
  exact pderiv_mem_derivSpan A P hJ

/-- The substituted iterated derivative `∂^ν (P ∘ A)` lies in the span of the substituted
derivatives `∂^J P` with `J ≤ wtBound A ν`. -/
theorem pderivIter_aeval_mem_W (A : σ → τ → ℚ) (ν : τ →₀ ℕ) (P : MvPolynomial σ ℚ) :
    pderivIter ν (aeval (linForm A) P) ∈ derivSpan A ν P := by
  have hstep : ∀ (f : τ →₀ ℕ) (a : τ),
      (∀ P, pderivIter f (aeval (linForm A) P) ∈ derivSpan A f P) →
      ∀ P, pderivIter (f + Finsupp.single a (1 : ℕ)) (aeval (linForm A) P)
        ∈ derivSpan A (f + Finsupp.single a (1 : ℕ)) P := by
    intro f a hf P
    rw [show pderivIter (f + Finsupp.single a (1 : ℕ)) (aeval (linForm A) P)
        = pderiv a (pderivIter f (aeval (linForm A) P)) from
      ((pderivIter_properties (R := ℚ) (σ := τ)).2.2.1 a f (aeval (linForm A) P)).symm]
    exact derivSpan_le_map_pderiv A f a P (Submodule.mem_map_of_mem (hf P))
  have hgen : ∀ (f : τ →₀ ℕ) (a : τ) (b : ℕ),
      (∀ P, pderivIter f (aeval (linForm A) P) ∈ derivSpan A f P) →
      ∀ P, pderivIter (f + Finsupp.single a b) (aeval (linForm A) P)
        ∈ derivSpan A (f + Finsupp.single a b) P := by
    intro f a b
    induction b with
    | zero => intro h P; simpa using h P
    | succ b ih =>
        intro h P
        rw [Finsupp.single_add, ← add_assoc]
        exact hstep (f + Finsupp.single a b) a (ih h) P
  refine Finsupp.induction₂ (motive := fun ν =>
    ∀ P, pderivIter ν (aeval (linForm A) P) ∈ derivSpan A ν P) ν ?_ ?_ P
  · intro P
    rw [show pderivIter (0 : τ →₀ ℕ) (aeval (linForm A) P) = aeval (linForm A) P from
      (pderivIter_properties (R := ℚ) (σ := τ)).1 (aeval (linForm A) P)]
    apply Submodule.subset_span
    refine ⟨0, ?_, ?_⟩
    · intro x; rw [wtBound]; simp
    · rw [(pderivIter_properties (R := ℚ) (σ := σ)).1 P]
  · intro a b f _ _ hf
    exact hgen f a b hf

end

/-! ## The main non-vanishing result -/

theorem exists_pderivIter_eval_ne_zero_of_aeval_linear {σ τ : Type*} [Fintype σ] [Fintype τ]
    [DecidableEq σ] [DecidableEq τ] (A : σ → τ → ℚ) (P : MvPolynomial σ ℚ) (ν : τ →₀ ℕ)
    (z : τ → ℚ)
    (h : MvPolynomial.eval z (Commons.Algebra.MvPolynomial.pderivIter ν
      (MvPolynomial.aeval (fun x => ∑ y, MvPolynomial.C (A x y) * MvPolynomial.X y) P)) ≠ 0) :
    ∃ I : σ →₀ ℕ, (∀ x, I x ≤ ∑ y ∈ ν.support, if A x y = 0 then 0 else ν y) ∧
      MvPolynomial.eval (fun x => ∑ y, A x y * z y)
        (Commons.Algebra.MvPolynomial.pderivIter I P) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hmem : pderivIter ν (aeval (linForm A) P) ∈ derivSpan A ν P := pderivIter_aeval_mem_W A ν P
  have hkill : MvPolynomial.eval z (pderivIter ν (aeval (linForm A) P)) = 0 := by
    have hker : derivSpan A ν P ≤ LinearMap.ker (MvPolynomial.aeval z : MvPolynomial τ ℚ →ₐ[ℚ] ℚ).toLinearMap := by
      rw [derivSpan, Submodule.span_le]
      rintro g ⟨J, hJ, rfl⟩
      show (MvPolynomial.aeval z) (aeval (linForm A) (pderivIter J P)) = 0
      have hb : ∀ x, J x ≤ ∑ y ∈ ν.support, if A x y = 0 then 0 else ν y :=
        fun x => by rw [← wtBound_eq_support A ν x]; exact hJ x
      have key : MvPolynomial.eval (fun x => ∑ y, A x y * z y) (pderivIter J P) = 0 := hcon J hb
      have h1 : (MvPolynomial.aeval z) (aeval (linForm A) (pderivIter J P))
          = (MvPolynomial.aeval (fun x => (MvPolynomial.aeval z) (linForm A x)))
              (pderivIter J P) :=
        congrArg (fun ψ => ψ (pderivIter J P))
          (MvPolynomial.comp_aeval (R := ℚ) (f := linForm A)
            (φ := (MvPolynomial.aeval z : MvPolynomial τ ℚ →ₐ[ℚ] ℚ)))
      have h2 : (fun x => (MvPolynomial.aeval z) (linForm A x)) = (fun x => ∑ y, A x y * z y) := by
        funext x
        rw [linForm, map_sum]
        apply Finset.sum_congr rfl
        intro y _
        rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
        simp
      rw [h1, h2]
      rw [MvPolynomial.aeval_eq_eval]
      exact key
    have hmem' := hker hmem
    rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply] at hmem'
    rwa [MvPolynomial.aeval_eq_eval] at hmem'
  exact h hkill

end Commons.Algebra.MvPolynomial