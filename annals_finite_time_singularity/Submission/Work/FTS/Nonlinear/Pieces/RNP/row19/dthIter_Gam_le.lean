import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Have
import Mathlib.Tactic.IntervalCases
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Spaces.Gamma_WlInf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular iterates of `Γ` are dominated by `Γ` (for fixed `α`)

`Γ(θ) = (sin θ cos²θ)^{α/3}` is one of the two basic building blocks of the paper
(jointly with the radial profile `z/(1+z)²`).  On the angular interval `Iθ = [0,π/2]`
the operator `Lop u = sin(2θ)·u'` is the action of `D_θ` on functions of `θ` alone, and
the identity

`D_θ^{j+1} Γ = α · Tfun j α · Γ`  on `(0,π/2)`

(`Work.Spaces.dthU_iter_Gam`) shows that each iterate of `Γ` is `Γ` times a coefficient
built from the bounded sequence `Tfun j α`.  The sibling
`Work.Spaces.dthU_Gam_le` bounds `α · Tfun j α` uniformly in `α ∈ (0,1]`; for the row-19
estimate only a *fixed* `α` is needed, and then the constant may depend on `α`.  This is
the `α`-dependent version: `Work.Spaces.Tfun_iter_bounded` is reproved with the bound
`M` allowed to depend on `α` (the only place the sibling uses `α ≤ 1` is the step
`α·S ≤ S`, which is dropped here).

The main result is `dthIter_Gam_le`: for every `i ≤ 4` and `θ ∈ Iθ`,
`|Lop^[i] Γ θ| ≤ C·Γ(θ)`.
-/

noncomputable section

open scoped Real Topology
open Work.Spaces

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

set_option autoImplicit false

local notation "C∞" => (⊤ : ℕ∞)

/-- The `α`-dependent version of `Work.Spaces.Tfun_iter_bounded`: for every `j` the
iterated angular derivatives `D_θ^m (Tfun j α)` are bounded on `Iθ` by a constant
`M α m` which is allowed to depend on `α` (the sibling `Tfun_iter_bounded` gives a bound
uniform in `α ≤ 1`; here `α > 0` is arbitrary). -/
lemma Tfun_iter_bounded_alpha (j : ℕ) :
    ∃ M : ℝ → ℕ → ℝ, (∀ α : ℝ, 0 ≤ α → ∀ m : ℕ, 0 ≤ M α m) ∧
      ∀ α : ℝ, 0 < α → ∀ θ : ℝ, θ ∈ Iθ → ∀ m : ℕ,
        |dthU^[m] (Tfun j α) θ| ≤ M α m := by
  induction j with
  | zero =>
      refine ⟨fun _ m => qBound m, fun α hα m => qBound_nonneg m, ?_⟩
      intro α hα θ hθ m
      have hT0 : Tfun 0 α = qfun := by funext t; rfl
      rw [hT0]
      exact dthU_qfun_le_qBound m hθ
  | succ j ih =>
      obtain ⟨M, hM0, hMbound⟩ := ih
      refine ⟨fun α m => M α (m + 1) + α * ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * qBound i * M α (m - i), ?_, ?_⟩
      · intro α hα m
        exact add_nonneg (hM0 α hα (m + 1)) (mul_nonneg hα (Finset.sum_nonneg fun i _ =>
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (qBound_nonneg i)) (hM0 α hα _)))
      · intro α hα θ hθ m
        have hTeq : Tfun (j+1) α = dthU (Tfun j α) + (fun θ => α * qfun θ) * (Tfun j α) := by
          funext t; rw [Tfun_succ]; simp only [dthU_apply, Pi.add_apply, Pi.mul_apply]
        have hsm : (fun θ => α * qfun θ) * (Tfun j α)
            = fun θ => α * ((qfun * (Tfun j α)) θ) := by
          funext t; simp only [Pi.mul_apply]; ring
        have hdiff1 : ContDiff ℝ C∞ (dthU (Tfun j α)) := dthU_smooth (Tfun_smooth j α)
        have hdiff2 : ContDiff ℝ C∞ ((fun θ => α * qfun θ) * (Tfun j α)) :=
          (contDiff_const.mul qfun_smooth).mul (Tfun_smooth j α)
        have hdecomp : dthU^[m] (Tfun (j+1) α)
            = fun θ => dthU^[m+1] (Tfun j α) θ + α * (dthU^[m] (qfun * (Tfun j α))) θ := by
          rw [hTeq, dthU_iter_add m _ _ hdiff1 hdiff2, hsm, dthU_iter_const_mul,
            dthU_iter_comp]
          funext t; simp only [Pi.add_apply]
        have hleib : dthU^[m] (qfun * (Tfun j α))
            = ∑ i ∈ Finset.range (m+1), dthCoef m qfun (Tfun j α) i :=
          dthU_iter_mul m qfun (Tfun j α) qfun_smooth (Tfun_smooth j α)
        calc |dthU^[m] (Tfun (j+1) α) θ|
            = |dthU^[m+1] (Tfun j α) θ + α * (dthU^[m] (qfun * (Tfun j α))) θ| := by
                rw [hdecomp]
          _ ≤ |dthU^[m+1] (Tfun j α) θ| + |α * (dthU^[m] (qfun * (Tfun j α))) θ| :=
                abs_add_le _ _
          _ = |dthU^[m+1] (Tfun j α) θ| + α * |(dthU^[m] (qfun * (Tfun j α))) θ| := by
                rw [abs_mul, abs_of_pos hα]
          _ = |dthU^[m+1] (Tfun j α) θ|
                + α * |(∑ i ∈ Finset.range (m+1), dthCoef m qfun (Tfun j α) i) θ| := by
                rw [hleib]
          _ = |dthU^[m+1] (Tfun j α) θ|
                + α * |∑ i ∈ Finset.range (m+1), dthCoef m qfun (Tfun j α) i θ| := by
                rw [Finset.sum_apply]
          _ ≤ M α (m+1)
                + α * ∑ i ∈ Finset.range (m+1), (m.choose i : ℝ) * qBound i * M α (m-i) := by
                apply add_le_add
                · exact hMbound α hα θ hθ (m+1)
                · apply mul_le_mul_of_nonneg_left _ (le_of_lt hα)
                  calc |∑ i ∈ Finset.range (m+1), dthCoef m qfun (Tfun j α) i θ|
                      ≤ ∑ i ∈ Finset.range (m+1), |dthCoef m qfun (Tfun j α) i θ| :=
                        Finset.abs_sum_le_sum_abs _ _
                    _ ≤ ∑ i ∈ Finset.range (m+1), (m.choose i : ℝ) * qBound i * M α (m-i) := by
                        apply Finset.sum_le_sum
                        intro i hi
                        have habs : |dthCoef m qfun (Tfun j α) i θ|
                            = (m.choose i : ℝ) * |dthU^[i] qfun θ|
                              * |dthU^[m-i] (Tfun j α) θ| := by
                          rw [dthCoef_apply, abs_mul, abs_mul,
                            abs_of_nonneg (Nat.cast_nonneg (m.choose i))]
                          ring
                        rw [habs]
                        exact mul_le_mul
                          (mul_le_mul_of_nonneg_left (dthU_qfun_le_qBound i hθ)
                            (Nat.cast_nonneg _))
                          (hMbound α hα θ hθ (m-i)) (abs_nonneg _)
                          (mul_nonneg (Nat.cast_nonneg _) (qBound_nonneg i))

/-- **Row 19, `Γ`-slot.**  For every fixed `α > 0` the first five angular iterates
`Lop^[i] Γ` (`i ≤ 4`) of `Γ(θ) = (sin θ cos²θ)^{α/3}` are dominated by `Γ` itself on the
angular interval `Iθ`.  The constant is allowed to depend on `α` (it is built from the
bounds `M_j α 0` of the coefficient sequence `Tfun `). -/
theorem dthIter_Gam_le {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ i : ℕ, i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Lop^[i] (fun θ => Work.Spaces.Gam α θ) θ| ≤ C * Work.Spaces.Gam α θ := by
  obtain ⟨M0, hM0n, hM0⟩ := Tfun_iter_bounded_alpha 0
  obtain ⟨M1, hM1n, hM1⟩ := Tfun_iter_bounded_alpha 1
  obtain ⟨M2, hM2n, hM2⟩ := Tfun_iter_bounded_alpha 2
  obtain ⟨M3, hM3n, hM3⟩ := Tfun_iter_bounded_alpha 3
  have hα0 : (0 : ℝ) ≤ α := le_of_lt hα
  have h0 : 0 ≤ M0 α 0 := hM0n α hα0 0
  have h1 : 0 ≤ M1 α 0 := hM1n α hα0 0
  have h2 : 0 ≤ M2 α 0 := hM2n α hα0 0
  have h3 : 0 ≤ M3 α 0 := hM3n α hα0 0
  set B : ℝ := M0 α 0 + M1 α 0 + M2 α 0 + M3 α 0 with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; linarith
  -- every `|Tfun j α|`, `j ≤ 3`, is bounded by `B`
  have hTb : ∀ j : ℕ, j ≤ 3 → ∀ θ ∈ Iθ, |Tfun j α θ| ≤ B := by
    intro j hj θ hθ
    interval_cases j
    · exact le_trans (by simpa using hM0 α hα θ hθ 0) (by rw [hBdef]; linarith)
    · exact le_trans (by simpa using hM1 α hα θ hθ 0) (by rw [hBdef]; linarith)
    · exact le_trans (by simpa using hM2 α hα θ hθ 0) (by rw [hBdef]; linarith)
    · exact le_trans (by simpa using hM3 α hα θ hθ 0) (by rw [hBdef]; linarith)
  refine ⟨1 + α * B, ?_, ?_⟩
  · have : 0 ≤ α * B := mul_nonneg hα0 hB0
    linarith
  intro i hi4 θ hθ
  have hG := Gam_bounds α θ hα hθ
  have hLop : Lop = dthU := rfl
  rw [hLop]
  rcases eq_or_ne i 0 with hi0 | hi0
  · subst hi0
    simp only [Function.iterate_zero_apply]
    rw [abs_of_nonneg hG.1]
    exact le_mul_of_one_le_left hG.1 (by linarith [mul_nonneg hα0 hB0])
  · have hipos : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
    have h := dthU_iter_Gam_abs_bound i hipos α hα B
      (hTb (i - 1) (by omega)) θ hθ
    refine le_trans h (mul_le_mul_of_nonneg_right ?_ hG.1)
    have hαB : 0 ≤ α * B := mul_nonneg hα0 hB0
    linarith

end Work.FTS.Nonlinear.Pieces.RNP.row19
