import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.DthIter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Boundedness of the iterates of `Lop` applied to `sin (2θ)` and `cos (2θ)`

`Work.Spaces.Lop u θ = sin (2θ) · u'(θ)` is the action of `D_θ = sin(2θ) ∂_θ` on functions of
`θ` alone.  The functions `θ ↦ sin (2θ)` and `θ ↦ cos (2θ)` are trigonometric polynomials, and
`Lop` multiplies by the trigonometric polynomial `sin (2θ)` and differentiates, so it maps the
`ℝ`-algebra of trigonometric polynomials in `sin (2θ), cos (2θ)` into itself.  Every
trigonometric polynomial is bounded on `ℝ` (indeed bounded in absolute value by the sum of the
absolute values of the coefficients), and only finitely many iterates `r ≤ l` occur, so a
common bound `M` exists.

The formalisation of "trigonometric polynomial" is the inductive closure

`TP := ℝ-span of {sin (2·), cos (2·)} closed under pointwise products`

(`LopTrig.TP` below), together with the three structural facts used in the induction: elements
of `TP` are differentiable everywhere (`LopTrig.TP_differentiable`), bounded
(`LopTrig.TP_bdd`), and `TP` is closed under `deriv` (`LopTrig.TP_deriv`), hence under `Lop`
(`LopTrig.TP_lop`).
-/

open scoped Real

namespace Work.FTS.PhiStar.LinvFlat

namespace LopTrig

/-- The `ℝ`-algebra of trigonometric polynomials in `sin (2θ)` and `cos (2θ)`: the smallest
class of functions `ℝ → ℝ` containing `sin (2·)` and `cos (2·)` and closed under addition,
pointwise multiplication and multiplication by real constants. -/
inductive TP : (ℝ → ℝ) → Prop
  | sin2 : TP (fun θ => Real.sin (2 * θ))
  | cos2 : TP (fun θ => Real.cos (2 * θ))
  | add {f g : ℝ → ℝ} : TP f → TP g → TP (f + g)
  | mul {f g : ℝ → ℝ} : TP f → TP g → TP (f * g)
  | smul (c : ℝ) {f : ℝ → ℝ} : TP f → TP (fun θ => c * f θ)

/-- Every trigonometric polynomial is differentiable everywhere. -/
lemma TP_differentiable : ∀ {f : ℝ → ℝ}, TP f → Differentiable ℝ f
  | _, .sin2 => by fun_prop
  | _, .cos2 => by fun_prop
  | _, .add hf hg => (TP_differentiable hf).add (TP_differentiable hg)
  | _, .mul hf hg => (TP_differentiable hf).mul (TP_differentiable hg)
  | _, .smul c hf => (differentiable_const c).mul (TP_differentiable hf)

/-- Every trigonometric polynomial is bounded in absolute value. -/
lemma TP_bdd : ∀ {f : ℝ → ℝ}, TP f → ∃ M : ℝ, 0 ≤ M ∧ ∀ θ : ℝ, |f θ| ≤ M
  | _, .sin2 => ⟨1, zero_le_one, fun θ => Real.abs_sin_le_one (2 * θ)⟩
  | _, .cos2 => ⟨1, zero_le_one, fun θ => Real.abs_cos_le_one (2 * θ)⟩
  | _, .add hf hg => by
      obtain ⟨M, hM0, hM⟩ := TP_bdd hf
      obtain ⟨N, hN0, hN⟩ := TP_bdd hg
      exact ⟨M + N, add_nonneg hM0 hN0, fun θ => by
        simp only [Pi.add_apply]
        exact le_trans (abs_add_le _ _) (add_le_add (hM θ) (hN θ))⟩
  | _, .mul hf hg => by
      obtain ⟨M, hM0, hM⟩ := TP_bdd hf
      obtain ⟨N, hN0, hN⟩ := TP_bdd hg
      exact ⟨M * N, mul_nonneg hM0 hN0, fun θ => by
        simp only [Pi.mul_apply, abs_mul]
        exact mul_le_mul (hM θ) (hN θ) (abs_nonneg _) hM0⟩
  | _, .smul c hf => by
      obtain ⟨M, hM0, hM⟩ := TP_bdd hf
      exact ⟨|c| * M, mul_nonneg (abs_nonneg c) hM0, fun θ => by
        simp only [abs_mul]
        exact mul_le_mul_of_nonneg_left (hM θ) (abs_nonneg c)⟩

lemma deriv_sin2 : deriv (fun θ : ℝ => Real.sin (2 * θ)) = fun θ => 2 * Real.cos (2 * θ) := by
  funext θ
  rw [deriv_sin (by fun_prop : DifferentiableAt ℝ (fun θ : ℝ => 2 * θ) θ)]
  rw [show deriv (fun θ : ℝ => 2 * θ) θ = 2 from (hasDerivAt_const_mul (2:ℝ) (x := θ)).deriv]
  ring

lemma deriv_cos2 : deriv (fun θ : ℝ => Real.cos (2 * θ)) = fun θ => -2 * Real.sin (2 * θ) := by
  funext θ
  rw [deriv_cos (by fun_prop : DifferentiableAt ℝ (fun θ : ℝ => 2 * θ) θ)]
  rw [show deriv (fun θ : ℝ => 2 * θ) θ = 2 from (hasDerivAt_const_mul (2:ℝ) (x := θ)).deriv]
  ring

lemma deriv_add_TP {f g : ℝ → ℝ} (hf : TP f) (hg : TP g) :
    deriv (f + g) = deriv f + deriv g := by
  funext θ
  rw [deriv_add ((TP_differentiable hf).differentiableAt) ((TP_differentiable hg).differentiableAt)]
  simp only [Pi.add_apply]

lemma deriv_mul_TP {f g : ℝ → ℝ} (hf : TP f) (hg : TP g) :
    deriv (f * g) = deriv f * g + f * deriv g := by
  funext θ
  rw [deriv_mul ((TP_differentiable hf).differentiableAt) ((TP_differentiable hg).differentiableAt)]
  simp only [Pi.add_apply, Pi.mul_apply]

lemma deriv_smul_TP (c : ℝ) {f : ℝ → ℝ} (hf : TP f) :
    deriv (fun θ : ℝ => c * f θ) = fun θ => c * deriv f θ := by
  funext θ
  rw [deriv_const_mul c ((TP_differentiable hf).differentiableAt)]

/-- The class of trigonometric polynomials is closed under differentiation. -/
lemma TP_deriv : ∀ {f : ℝ → ℝ}, TP f → TP (deriv f)
  | _, .sin2 => by
      rw [deriv_sin2]
      exact TP.smul 2 TP.cos2
  | _, .cos2 => by
      rw [deriv_cos2]
      exact TP.smul (-2) TP.sin2
  | _, .add hf hg => by
      rw [deriv_add_TP hf hg]
      exact TP.add (TP_deriv hf) (TP_deriv hg)
  | _, .mul hf hg => by
      rw [deriv_mul_TP hf hg]
      exact TP.add (TP.mul (TP_deriv hf) hg) (TP.mul hf (TP_deriv hg))
  | _, .smul c hf => by
      rw [deriv_smul_TP c hf]
      exact TP.smul c (TP_deriv hf)

/-- The class of trigonometric polynomials is closed under `Lop`. -/
lemma TP_lop {f : ℝ → ℝ} (hf : TP f) : TP (Work.Spaces.Lop f) := by
  change TP (fun θ => Real.sin (2 * θ) * deriv f θ)
  exact TP.mul TP.sin2 (TP_deriv hf)

end LopTrig

theorem Lop_iter_sin_cos_bound (l : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℕ, r ≤ l → ∀ θ : ℝ,
    θ ∈ Set.Ioo 0 (π/2) →
    |(Work.Spaces.Lop^[r]) (fun θ' => Real.sin (2 * θ')) θ| ≤ M ∧
    |(Work.Spaces.Lop^[r]) (fun θ' => Real.cos (2 * θ')) θ| ≤ M := by
  -- every iterate of `Lop` applied to `sin (2·)` or `cos (2·)` is a trigonometric polynomial
  have hmem : ∀ r : ℕ, LopTrig.TP ((Work.Spaces.Lop^[r]) (fun θ' => Real.sin (2 * θ'))) ∧
      LopTrig.TP ((Work.Spaces.Lop^[r]) (fun θ' => Real.cos (2 * θ'))) := by
    intro r
    induction r with
    | zero => exact ⟨LopTrig.TP.sin2, LopTrig.TP.cos2⟩
    | succ r ih =>
        refine ⟨?_, ?_⟩
        · rw [Function.iterate_succ_apply']
          exact LopTrig.TP_lop ih.1
        · rw [Function.iterate_succ_apply']
          exact LopTrig.TP_lop ih.2
  -- hence each single iterate is bounded
  have hbd : ∀ r : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      (∀ θ : ℝ, |(Work.Spaces.Lop^[r]) (fun θ' => Real.sin (2 * θ')) θ| ≤ M) ∧
      (∀ θ : ℝ, |(Work.Spaces.Lop^[r]) (fun θ' => Real.cos (2 * θ')) θ| ≤ M) := by
    intro r
    obtain ⟨M1, hM10, hM1⟩ := LopTrig.TP_bdd (hmem r).1
    obtain ⟨M2, hM20, hM2⟩ := LopTrig.TP_bdd (hmem r).2
    exact ⟨max M1 M2, le_trans hM10 (le_max_left _ _),
      fun θ => le_trans (hM1 θ) (le_max_left _ _),
      fun θ => le_trans (hM2 θ) (le_max_right _ _)⟩
  -- and a common bound for all `r ≤ l` is the sum of the individual bounds
  let B : ℕ → ℝ := fun r => Classical.choose (hbd r)
  have hB : ∀ r : ℕ, 0 ≤ B r ∧
      (∀ θ : ℝ, |(Work.Spaces.Lop^[r]) (fun θ' => Real.sin (2 * θ')) θ| ≤ B r) ∧
      (∀ θ : ℝ, |(Work.Spaces.Lop^[r]) (fun θ' => Real.cos (2 * θ')) θ| ≤ B r) :=
    fun r => Classical.choose_spec (hbd r)
  refine ⟨∑ r ∈ Finset.range (l + 1), B r, Finset.sum_nonneg (fun r _ => (hB r).1), ?_⟩
  intro r hr θ hθ
  have hmem' : r ∈ Finset.range (l + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hr)
  have hsum : B r ≤ ∑ s ∈ Finset.range (l + 1), B s :=
    Finset.single_le_sum (fun i _ => (hB i).1) hmem'
  exact ⟨le_trans ((hB r).2.1 θ) hsum, le_trans ((hB r).2.2 θ) hsum⟩

end Work.FTS.PhiStar.LinvFlat
