/-
  WilG4a — uniformity in the derivative order of the `Ω`-format of `badLocus`/`derivZeroSet`.

  `Cells.badLocus_mem` and `Cells.derivZeroSet_mem` give, for each derivative order `j`,
  `Ω`-membership of `badLocus f j` and `derivZeroSet f j` with format `a(D,j)` and degree
  `b` evaluated at `![D,j]`.  What the `F1Affine1`/`signConst` machinery consumes is a
  *single* format `a` and a *single* polynomial `B`, valid for every `j ≤ r + 2`, with the
  degree evaluated at `![D,r]` — i.e. the family of formats must be uniform in the order,
  with `r` absorbing the shift by `2`.

  All coefficients here are natural numbers, so `MvPolynomial.eval` is monotone in the
  evaluation point.  The shift `j ≤ r + 2` is then absorbed into the polynomial by
  post-composing with the substitution `X 1 ↦ X 1 + 2`:

    `eval ![D,r] (bind₁ ![X 0, X 1 + C 2] b) = eval ![D,r+2] b`,

  so that for `B = bind₁ ![X 0, X 1 + C 2] (b₁ + b₂)` we get
  `eval ![D,j] bᵢ ≤ eval ![D,r+2] bᵢ ≤ eval ![D,r] B` as soon as `j ≤ r + 2`.
-/
import Mathlib
import Submission.Work.WilG4a.Cells

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a
open WilkiesConjecture WilkiesDesign

/-! ## Evaluation of `ℕ`-coefficient polynomials is monotone in the point -/

/-- A multivariate polynomial with coefficients in `ℕ` is monotone in its evaluation point:
if `a i ≤ b i` for every variable `i`, then `eval a p ≤ eval b p`. -/
lemma evalNat_mono {σ : Type*} (p : MvPolynomial σ ℕ) {a b : σ → ℕ} (hab : ∀ i, a i ≤ b i) :
    MvPolynomial.eval a p ≤ MvPolynomial.eval b p := by
  refine MvPolynomial.induction_on
    (motive := fun p => MvPolynomial.eval a p ≤ MvPolynomial.eval b p) p ?_ ?_ ?_
  · intro c
    simp
  · intro p q hp hq
    rw [MvPolynomial.eval_add, MvPolynomial.eval_add]
    exact Nat.add_le_add hp hq
  · intro p n hp
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_X]
    exact Nat.mul_le_mul hp (hab n)

/-- Specialisation of monotonicity to two variables, at the points `![D,j]` and `![D,r]`. -/
lemma evalFin2_mono (b : MvPolynomial (Fin 2) ℕ) {D j r : ℕ} (h : j ≤ r) :
    MvPolynomial.eval ![D, j] b ≤ MvPolynomial.eval ![D, r] b :=
  evalNat_mono b (by intro i; fin_cases i <;> simp [h])

/-! ## Absorbing the shift of the second variable -/

/-- Evaluation intertwines the substitution `bind₁` with evaluation of the substituted
variables. -/
lemma eval_bind₁_fin2 (v : Fin 2 → ℕ) (h : Fin 2 → MvPolynomial (Fin 2) ℕ)
    (φ : MvPolynomial (Fin 2) ℕ) :
    MvPolynomial.eval v (MvPolynomial.bind₁ h φ) =
      MvPolynomial.eval (fun i => MvPolynomial.eval v (h i)) φ :=
  MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℕ) v h φ

/-- Substituting `X 1 ↦ X 1 + 2` turns the evaluation point `![D,r]` into `![D,r+2]`. -/
lemma eval_shift_two (b : MvPolynomial (Fin 2) ℕ) (D r : ℕ) :
    MvPolynomial.eval ![D, r]
        (MvPolynomial.bind₁ ![MvPolynomial.X 0, MvPolynomial.X 1 + MvPolynomial.C 2] b) =
      MvPolynomial.eval ![D, r + 2] b := by
  have h : ∀ i : Fin 2, MvPolynomial.eval ![D, r]
      (![MvPolynomial.X 0, MvPolynomial.X 1 + MvPolynomial.C 2] i) = ![D, r + 2] i := by
    intro i
    fin_cases i <;> simp [MvPolynomial.eval_add]
  rw [eval_bind₁_fin2, funext h]

/-- The first summand is bounded by the shifted polynomial evaluated at `![D,r]`. -/
lemma eval_shift_two_le_left (b₁ b₂ : MvPolynomial (Fin 2) ℕ) (D r : ℕ) :
    MvPolynomial.eval ![D, r + 2] b₁ ≤
      MvPolynomial.eval ![D, r]
        (MvPolynomial.bind₁ ![MvPolynomial.X 0, MvPolynomial.X 1 + MvPolynomial.C 2]
          (b₁ + b₂)) := by
  rw [eval_shift_two, MvPolynomial.eval_add]
  exact Nat.le_add_right _ _

/-- The second summand is bounded by the shifted polynomial evaluated at `![D,r]`. -/
lemma eval_shift_two_le_right (b₁ b₂ : MvPolynomial (Fin 2) ℕ) (D r : ℕ) :
    MvPolynomial.eval ![D, r + 2] b₂ ≤
      MvPolynomial.eval ![D, r]
        (MvPolynomial.bind₁ ![MvPolynomial.X 0, MvPolynomial.X 1 + MvPolynomial.C 2]
          (b₁ + b₂)) := by
  rw [eval_shift_two, MvPolynomial.eval_add]
  exact Nat.le_add_left _ _

/-! ## The uniform statement -/

theorem badLocus_derivZeroSet_uniform (S : WilkiesDesign.SOMin)
    (hder : WilkiesDesign.SOMin.SharpDeriv S) (p F0 : ℕ) :
    ∃ (a : ℕ) (B : MvPolynomial (Fin 2) ℕ),
      ∀ (D r : ℕ) (f : (Fin p → ℝ) → ℝ → ℝ),
        Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        ∀ j : ℕ, j ≤ r + 2 →
          (Work.WilG4a.badLocus f j ∈ S.Ω a (MvPolynomial.eval ![D, r] B) (p + 1) ∧
           Work.WilG4a.derivZeroSet f j ∈ S.Ω a (MvPolynomial.eval ![D, r] B) (p + 1)) := by
  obtain ⟨a₁, b₁, h₁⟩ := badLocus_mem S hder p F0
  obtain ⟨a₂, b₂, h₂⟩ := derivZeroSet_mem S hder p F0
  refine ⟨max a₁ a₂,
    MvPolynomial.bind₁ ![MvPolynomial.X 0, MvPolynomial.X 1 + MvPolynomial.C 2] (b₁ + b₂),
    ?_⟩
  intro D r f hf j hj
  have hD₁ : MvPolynomial.eval ![D, j] b₁ ≤
      MvPolynomial.eval ![D, r]
        (MvPolynomial.bind₁ ![MvPolynomial.X 0, MvPolynomial.X 1 + MvPolynomial.C 2]
          (b₁ + b₂)) :=
    le_trans (evalFin2_mono (D := D) (j := j) (r := r + 2) b₁ hj)
      (eval_shift_two_le_left b₁ b₂ D r)
  have hD₂ : MvPolynomial.eval ![D, j] b₂ ≤
      MvPolynomial.eval ![D, r]
        (MvPolynomial.bind₁ ![MvPolynomial.X 0, MvPolynomial.X 1 + MvPolynomial.C 2]
          (b₁ + b₂)) :=
    le_trans (evalFin2_mono (D := D) (j := j) (r := r + 2) b₂ hj)
      (eval_shift_two_le_right b₁ b₂ D r)
  exact ⟨mono_FD_le S (h₁ D j hf) (le_max_left _ _) hD₁,
    mono_FD_le S (h₂ D j hf) (le_max_right _ _) hD₂⟩

end Work.WilG4a
