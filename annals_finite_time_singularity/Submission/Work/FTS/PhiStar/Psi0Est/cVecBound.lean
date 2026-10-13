import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.Psi0Est.AClassDefs
import Submission.Work.FTS.PhiStar.Psi0Classes
import Submission.Work.FTS.PhiStar.Psi0Ode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.Psi0Est.cVecBound` — the coefficients `cVec j r` are bounded on `ℝ`

The coefficient family `cVec` of `AClassDefs` is generated from `c₀,₀ = 2cos 2θ` by the
operations `f ↦ D_θ f`, `f ↦ 4 sin²θ · f`, `f ↦ f + g` and subtraction, starting from the
explicitly `IsCoef` functions.  Since `IsCoef f` (i.e. `f θ = A(sin θ) + cos θ · B(sin θ)`
with `A, B : ℝ[X]`) is closed under all of these and every `IsCoef` function is bounded on
`ℝ`, each `cVec j r` admits a uniform bound `cB j r`, which is the content of `cVecBound`.

Everything is proved here from scratch; the only inputs are the definition of `IsCoef` and
of `cVec` in `AClassDefs`.
-/

noncomputable section

open scoped Real Topology

open Polynomial

namespace Work.FTS.PhiStar.Psi0Est

set_option autoImplicit false

namespace CVecBnd

/-! ## Elementary polynomial evaluation bounds -/

/-- For `|x| ≤ 1`, the value `p.eval x` of a real polynomial is bounded by the sum of the
absolute values of its coefficients (in degrees up to `natDegree p`). -/
lemma abs_eval_le (p : ℝ[X]) (x : ℝ) (hx : |x| ≤ 1) :
    |p.eval x| ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| := by
  rw [Polynomial.eval_eq_sum_range]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  have hxi : |x ^ i| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg x) hx
  calc |p.coeff i| * |x ^ i| ≤ |p.coeff i| * 1 := mul_le_mul_of_nonneg_left hxi (abs_nonneg _)
    _ = |p.coeff i| := by ring

/-! ## The class `IsCoef` is closed under the generating operations, and bounded -/

lemma isCoef_zero : IsCoef (0 : ℝ → ℝ) := ⟨0, 0, fun _ => by simp⟩

lemma isCoef_add {f g : ℝ → ℝ} (hf : IsCoef f) (hg : IsCoef g) : IsCoef (f + g) := by
  obtain ⟨A1, B1, h1⟩ := hf
  obtain ⟨A2, B2, h2⟩ := hg
  exact ⟨A1 + A2, B1 + B2, fun θ => by
    rw [Pi.add_apply, h1 θ, h2 θ]; simp only [Polynomial.eval_add]; ring⟩

lemma isCoef_neg {f : ℝ → ℝ} (hf : IsCoef f) : IsCoef (-f) := by
  obtain ⟨A, B, h⟩ := hf
  exact ⟨-A, -B, fun θ => by
    rw [Pi.neg_apply, h θ]; simp only [Polynomial.eval_neg]; ring⟩

lemma isCoef_sub {f g : ℝ → ℝ} (hf : IsCoef f) (hg : IsCoef g) : IsCoef (f - g) := by
  rw [sub_eq_add_neg]; exact isCoef_add hf (isCoef_neg hg)

lemma isCoef_const_mul (c : ℝ) {f : ℝ → ℝ} (hf : IsCoef f) : IsCoef (fun θ => c * f θ) := by
  obtain ⟨A, B, h⟩ := hf
  exact ⟨Polynomial.C c * A, Polynomial.C c * B, fun θ => by
    dsimp only; rw [h θ]; simp only [Polynomial.eval_mul, Polynomial.eval_C]; ring⟩

/-- `IsCoef` is closed under multiplication: `(A₁ + cB₁)(A₂ + cB₂)` with `c = cos θ`,
`s = sin θ` is `(A₁A₂ + (1-X²)B₁B₂)(s) + c·(A₁B₂ + A₂B₁)(s)`. -/
lemma isCoef_mul {f g : ℝ → ℝ} (hf : IsCoef f) (hg : IsCoef g) : IsCoef (f * g) := by
  obtain ⟨A1, B1, h1⟩ := hf
  obtain ⟨A2, B2, h2⟩ := hg
  refine ⟨A1 * A2 + (1 - X ^ 2) * B1 * B2, A1 * B2 + A2 * B1, ?_⟩
  intro θ
  rw [Pi.mul_apply, h1 θ, h2 θ]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X]
  have hc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
  linear_combination (Polynomial.eval (Real.sin θ) B1 * Polynomial.eval (Real.sin θ) B2) * hc

/-- `IsCoef` is closed under `D_θ = dthU`: writing `f θ = A(s) + c·B(s)` (`s = sin θ`,
`c = cos θ`) one has `deriv f θ = c A'(s) - s B(s) + c² B'(s)`, so
`D_θ f θ = 2 s (1-s²)·A'(s) + c·2s·((1-s²)B'(s) - s B(s))`, an `IsCoef` function with
data `(2X(1-X²)·A', 2X((1-X²)·B' - X·B))`. -/
lemma isCoef_dthU {f : ℝ → ℝ} (hf : IsCoef f) : IsCoef (Work.Spaces.dthU f) := by
  obtain ⟨A, B, h⟩ := hf
  rw [show f = fun θ => Polynomial.eval (Real.sin θ) A
      + Real.cos θ * Polynomial.eval (Real.sin θ) B from funext h]
  clear h
  refine ⟨2 * X * (1 - X ^ 2) * derivative A,
    2 * X * ((1 - X ^ 2) * derivative B - X * B), ?_⟩
  intro θ
  rw [Work.Spaces.dthU_apply]
  have h1 : HasDerivAt (fun θ => Polynomial.eval (Real.sin θ) A)
      (Polynomial.eval (Real.sin θ) (derivative A) * Real.cos θ) θ :=
    (Polynomial.hasDerivAt A (Real.sin θ)).comp θ (Real.hasDerivAt_sin θ)
  have h2 : HasDerivAt (fun θ => Real.cos θ * Polynomial.eval (Real.sin θ) B)
      ((-Real.sin θ) * Polynomial.eval (Real.sin θ) B
        + Real.cos θ * (Polynomial.eval (Real.sin θ) (derivative B) * Real.cos θ)) θ :=
    (Real.hasDerivAt_cos θ).mul
      ((Polynomial.hasDerivAt B (Real.sin θ)).comp θ (Real.hasDerivAt_sin θ))
  have hd : deriv (fun θ => Polynomial.eval (Real.sin θ) A
        + Real.cos θ * Polynomial.eval (Real.sin θ) B) θ
      = Polynomial.eval (Real.sin θ) (derivative A) * Real.cos θ
        + ((-Real.sin θ) * Polynomial.eval (Real.sin θ) B
          + Real.cos θ * (Polynomial.eval (Real.sin θ) (derivative B) * Real.cos θ)) :=
    (h1.add h2).deriv
  rw [hd, Real.sin_two_mul]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
  have hc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
  linear_combination (2 * Real.sin θ * (Polynomial.eval (Real.sin θ) (derivative A)
    + Real.cos θ * Polynomial.eval (Real.sin θ) (derivative B))) * hc

/-- Every `IsCoef` function is bounded on `ℝ`: `|A(sin θ)| ≤ Σ|coeff|` and
`|cos θ · B(sin θ)| ≤ Σ|coeff|`. -/
lemma isCoef_bdd {f : ℝ → ℝ} (hf : IsCoef f) : ∃ M : ℝ, 0 ≤ M ∧ ∀ θ, |f θ| ≤ M := by
  obtain ⟨A, B, h⟩ := hf
  refine ⟨(∑ i ∈ Finset.range (A.natDegree + 1), |A.coeff i|)
    + (∑ i ∈ Finset.range (B.natDegree + 1), |B.coeff i|), by positivity, ?_⟩
  intro θ
  rw [h θ]
  have hA := abs_eval_le A (Real.sin θ) (Real.abs_sin_le_one θ)
  have hB := abs_eval_le B (Real.sin θ) (Real.abs_sin_le_one θ)
  have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  calc |Polynomial.eval (Real.sin θ) A + Real.cos θ * Polynomial.eval (Real.sin θ) B|
      ≤ |Polynomial.eval (Real.sin θ) A|
          + |Real.cos θ * Polynomial.eval (Real.sin θ) B| := abs_add_le _ _
    _ ≤ (∑ i ∈ Finset.range (A.natDegree + 1), |A.coeff i|)
          + 1 * (∑ i ∈ Finset.range (B.natDegree + 1), |B.coeff i|) := by
        apply add_le_add hA
        rw [abs_mul]
        exact mul_le_mul hc hB (abs_nonneg _) (by norm_num)
    _ = _ := by ring

/-! ## The initial data of the recursion -/

lemma isCoef_two_cos_two : IsCoef (fun θ => 2 * Real.cos (2 * θ)) := by
  refine ⟨Polynomial.C 2 - Polynomial.C 4 * X ^ 2, 0, fun θ => ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero, mul_zero, add_zero]
  rw [Real.cos_two_mul']
  nlinarith [Real.sin_sq_add_cos_sq θ]

lemma isCoef_four_sin_sq : IsCoef (fun θ => 4 * Real.sin θ ^ 2) := by
  refine ⟨Polynomial.C 4 * X ^ 2, 0, fun θ => ?_⟩
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero, mul_zero, add_zero]

/-! ## Unfolding `cVec` along the recursion -/

/-- The `cVec`-recursion in its general form: for `k ≠ j`,
`cVec (j+1) (k+1) = D_θ (cVec j (k+1)) + 4sin²θ · cVec j (k+1) + cVec j k`. -/
lemma cVec_succ_succ_of_ne (j k : ℕ) (h : k ≠ j) :
    cVec (j + 1) (k + 1) = fun θ => Work.Spaces.dthU (cVec j (k + 1)) θ
      + 4 * Real.sin θ ^ 2 * cVec j (k + 1) θ + cVec j (k + 1 - 1) θ := by
  cases j with
  | zero =>
    simp only [cVec]
    rw [if_neg (by omega : ¬ k + 1 = 0 + 1), if_neg (by omega : ¬ k + 1 = 0)]
  | succ j =>
    simp only [cVec]
    rw [if_neg (by omega : ¬ k + 1 = j + 1 + 1), if_neg (by omega : ¬ k + 1 = 0)]

/-- **Every coefficient `cVec j r` is in the class `IsCoef`** (hence bounded).  Induction on
`j` with a full case analysis on `r`, using the closure properties above. -/
lemma isCoef_cVec : ∀ j r, IsCoef (cVec j r) := by
  intro j
  induction j with
  | zero =>
    intro r
    rcases r with _ | k
    · rw [cVec_zero_zero]; exact isCoef_two_cos_two
    · rw [cVec_zero_of_ne (k + 1) (by omega)]; exact isCoef_zero
  | succ j ih =>
    intro r
    rcases r with _ | k
    · rw [cVec_succ_zero]
      exact isCoef_add (isCoef_dthU (ih 0)) (isCoef_mul isCoef_four_sin_sq (ih 0))
    · by_cases hk : k = j
      · rw [hk, cVec_succ_self]
        exact isCoef_sub (ih j) isCoef_four_sin_sq
      · rw [cVec_succ_succ_of_ne j k hk]
        exact isCoef_add (isCoef_add (isCoef_dthU (ih (k + 1)))
          (isCoef_mul isCoef_four_sin_sq (ih (k + 1)))) (ih (k + 1 - 1))

end CVecBnd

theorem cVecBound : ∃ cB : ℕ → ℕ → ℝ, (∀ j r, 0 ≤ cB j r) ∧ ∀ j r (θ : ℝ), |Work.FTS.PhiStar.Psi0Est.cVec j r θ| ≤ cB j r := by
  have h : ∀ j r, ∃ M : ℝ, 0 ≤ M ∧ ∀ θ, |cVec j r θ| ≤ M :=
    fun j r => CVecBnd.isCoef_bdd (CVecBnd.isCoef_cVec j r)
  exact ⟨fun j r => Classical.choose (h j r),
    fun j r => (Classical.choose_spec (h j r)).1,
    fun j r θ => (Classical.choose_spec (h j r)).2 θ⟩

end Work.FTS.PhiStar.Psi0Est
