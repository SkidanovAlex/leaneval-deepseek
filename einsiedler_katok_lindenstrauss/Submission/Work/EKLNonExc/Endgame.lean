import Submission.Work.EKLNonExc.MatrixFacts

/-!
# The final contradiction for C9 (ROUTE_LEAD L9.4)

If an `Lset hab`-displacement `g` of a return `aPrime c n • z = g • z` has `fmax = 0`, then `g` is
the diagonal matrix `diag(μ,μ,μ⁻²)`, and `α'^n = g * aPrime c (n - log μ)`, so that
`aPrime c (n - log μ) = diag(λ,λ,λ⁻²)` (with `λ = e^n/μ > 3/2 > 1`) fixes `z`.  This contradicts
`NoDiag` (L9.3): no diagonal `diag(λ,λ,λ⁻²)` with `λ > 0`, `λ ≠ 1` fixes a point of `SL₃(ℝ)/SL₃(ℤ)`.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.EKLNonExc

open Work.EKLContract

noncomputable section

/-- An `Lset hab`-element with `fmax = 0` is diagonal, with the `a`- and `b`-diagonal entries
equal. -/
lemma toMat_diag_of_fmax_zero {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    {g : SL3} (hg : g ∈ Lset hab) (hf : fmax a b c g = 0) :
    toMat g = Matrix.diagonal (fun i => if i = c then g c c else g a a) := by
  obtain ⟨haa, hoff⟩ := fmax_eq_zero_of_mem_Lset hab hac hcb hg hf
  ext i j
  rw [Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hic : i = c
    · rw [if_pos rfl, if_pos hic, hic]
    · rw [if_pos rfl, if_neg hic]
      rcases eq_a_or_b_or_c hab hac hcb i with h | h | h
      · rw [h]
      · rw [h]; exact haa.symm
      · exact absurd h hic
  · rw [if_neg hij]
    exact hoff i j hij

/-- The determinant computation: for `g ∈ Lset hab` with `fmax = 0`, the diagonal entries
`(μ, μ, g c c)` satisfy `μ ^ 2 * g c c = 1`. -/
lemma sq_mul_cc_of_fmax_zero {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    {g : SL3} (hg : g ∈ Lset hab) (hf : fmax a b c g = 0) : g a a ^ 2 * g c c = 1 := by
  have hmat := toMat_diag_of_fmax_zero hab hac hcb hg hf
  have hdet : (toMat g).det = 1 := g.property
  rw [hmat, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  fin_cases c <;> simp at hdet ⊢ <;> nlinarith [hdet]

/-- `exp (-2 s) = (exp s ^ 2)⁻¹`. -/
lemma exp_neg_two_mul (s : ℝ) :
    Real.exp (-(2 * s)) = ((Real.exp s) ^ 2)⁻¹ := by
  rw [Real.exp_neg]
  rw [show (2 : ℝ) * s = ((2 : ℕ) : ℝ) * s by norm_num, Real.exp_nat_mul]

/-- `(exp (n - log μ))⁻² = exp (-2n) * μ²` for `μ > 0`. -/
lemma inv_sq_exp_sub_log (μ : ℝ) (hμ : 0 < μ) (n : ℝ) :
    (Real.exp (n - Real.log μ) ^ 2)⁻¹ = Real.exp (-2 * n) * μ ^ 2 := by
  have h1 : Real.exp (((2 : ℕ) : ℝ) * Real.log μ) = μ ^ 2 := by
    rw [Real.exp_nat_mul, Real.exp_log hμ]
  rw [← exp_neg_two_mul,
    show -(2 * (n - Real.log μ)) = -2 * n + ((2 : ℕ) : ℝ) * Real.log μ by push_cast; ring,
    Real.exp_add, h1]

/-- `exp s ≠ 1` when `s ≠ 0`. -/
lemma exp_ne_one {s : ℝ} (hs : s ≠ 0) : Real.exp s ≠ 1 := by
  intro h
  rw [← Real.exp_zero] at h
  exact hs (Real.exp_injective h)

/-- **L9.4.**  An `Lset hab`-return with `fmax = 0` and displacement in the closed box of radius
`≤ 1/2` is impossible, since it produces a nontrivial diagonal `diag(λ,λ,λ⁻²)` fixing a point of
`X₃`. -/
lemma endgame {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (noDiag : ∀ (lam : ℝ), 0 < lam → lam ≠ 1 → ∀ (x : X3) (h : SL3),
      toMat h = Matrix.diagonal (fun i => if i = c then (lam ^ 2)⁻¹ else lam) → h • x ≠ x)
    {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) {g : SL3} {z : X3}
    (hgL : g ∈ Lset hab) (hgb : g ∈ clBox δ) (hf : fmax a b c g = 0)
    (hret : aPrime c (n : ℝ) • z = g • z) : False := by
  have hmu_pos : 0 < g a a := by
    have h1 : |g a a - 1| ≤ δ := by
      have := hgb a a
      rwa [Matrix.one_apply, if_pos rfl] at this
    rw [abs_le] at h1
    linarith [h1.1]
  have hmu_le : g a a ≤ 3 / 2 := by
    have h1 : |g a a - 1| ≤ δ := by
      have := hgb a a
      rwa [Matrix.one_apply, if_pos rfl] at this
    rw [abs_le] at h1
    linarith [h1.2, hδ]
  obtain ⟨hcc, hsq⟩ : g c c = (g a a ^ 2)⁻¹ ∧ g a a ^ 2 * g c c = 1 := by
    have hs := sq_mul_cc_of_fmax_zero hab hac hcb hgL hf
    refine ⟨?_, hs⟩
    field_simp
    linarith [hs]
  -- the diagonal form of `g` with `g c c` replaced by `(μ^2)⁻¹`
  have hgmat : toMat g = Matrix.diagonal (fun i => if i = c then (g a a ^ 2)⁻¹ else g a a) := by
    rw [toMat_diag_of_fmax_zero hab hac hcb hgL hf, ← hcc]
  -- `λ = exp n / μ`
  set s : ℝ := (n : ℝ) - Real.log (g a a) with hsdef
  set lam : ℝ := Real.exp s with hlamdef
  have hlam_pos : 0 < lam := Real.exp_pos s
  have hlog_lt : Real.log (g a a) < (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (2 : ℝ) < Real.exp (n : ℝ) :=
      lt_of_lt_of_le Real.exp_one_gt_two (Real.exp_le_exp.mpr h1)
    have h3 : g a a < Real.exp (n : ℝ) := lt_of_le_of_lt hmu_le (by linarith)
    have h4 : Real.log (g a a) < Real.log (Real.exp (n : ℝ)) := Real.log_lt_log hmu_pos h3
    rwa [Real.log_exp] at h4
  have hs_ne : s ≠ 0 := by
    rw [hsdef]
    exact sub_ne_zero.mpr (ne_of_gt hlog_lt)
  have hlam_ne : lam ≠ 1 := by
    rw [hlamdef]
    exact exp_ne_one hs_ne
  -- the matrix form of `aPrime c (n - log μ)`
  have hDmat : toMat (aPrime c ((n : ℝ) - Real.log (g a a))) =
      Matrix.diagonal (fun i => if i = c then (lam ^ 2)⁻¹ else lam) := by
    rw [toMat_aPrime]
    congr 1
    funext i
    rw [hlamdef, hsdef]
    by_cases hic : i = c <;> simp [hic, exp_neg_two_mul]
  -- `g * aPrime c (n - log μ) = aPrime c n`
  have hprod : g * aPrime c ((n : ℝ) - Real.log (g a a)) = aPrime c (n : ℝ) := by
    apply ext_toMat
    rw [toMat_mul, hgmat, hDmat, toMat_aPrime, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hic : i = c
    · rw [if_pos hic, if_pos hic, if_pos hic, hlamdef]
      rw [inv_sq_exp_sub_log (g a a) hmu_pos (n : ℝ)]
      field_simp
    · rw [if_neg hic, if_neg hic, if_neg hic, hlamdef]
      rw [Real.exp_sub, Real.exp_log hmu_pos]
      field_simp
  -- the element `aPrime c (n - log μ)` is `g⁻¹ * aPrime c n`
  have hD_eq : aPrime c ((n : ℝ) - Real.log (g a a)) = g⁻¹ * aPrime c (n : ℝ) := by
    rw [← hprod, inv_mul_cancel_left]
  have hfix : aPrime c ((n : ℝ) - Real.log (g a a)) • z = z := by
    rw [hD_eq, mul_smul, hret, ← mul_smul, inv_mul_cancel, one_smul]
  exact noDiag lam hlam_pos hlam_ne z (aPrime c ((n : ℝ) - Real.log (g a a))) hDmat hfix

end

end Work.EKLNonExc
