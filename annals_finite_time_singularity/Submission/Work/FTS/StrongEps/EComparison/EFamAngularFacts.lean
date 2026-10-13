/-
# `Work.FTS.StrongEps.EComparison.EFamAngularFacts`

Angular facts about the Dirichlet eigenfunctions of `Lzero`,
`eFam m θ = cos θ · gC (2m+1) (sin θ)`:

* `eFam m` and `deriv (eFam m)` are differentiable on `ℝ`;
* `eFam m` vanishes at both endpoints of `[0, π/2]` at least linearly, with a *common* constant
  `L` for the two endpoints;
* `deriv (eFam m)` is bounded on `[0, π/2]`;
* `tan θ · eFam m θ` is bounded on `(0, π/2)` (there it equals `sin θ · gC (2m+1) (sin θ)`,
  since `tan θ · cos θ = sin θ`).

The ingredients are the two existing lemmas `ClassC.eFam_sin_two_bound`
(`|eFam m θ| ≤ A · sin 2θ` on `[0, π/2]`) and `ClassC.eFam_deriv_bound`
(`|deriv (eFam m)| ≤ Q` on `[0, π/2]`), together with `sin x ≤ x` (`Real.sin_le`) and
`sin (π - x) = sin x` (`Real.sin_pi_sub`) for the two endpoint bounds:
`sin 2θ ≤ 2θ` gives the bound at `0`, and `sin 2θ = sin (π - 2θ) ≤ π - 2θ = 2 (π/2 - θ)` gives the
bound at `π/2`, with the *same* constant `L = 2A + 1`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode
import Submission.Work.FTS.ClassC.eFam_sin_two_bound
import Submission.Work.FTS.ClassC.eFam_deriv_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

/-- `deriv` lowers `C^n` regularity by one (univariate form). -/
lemma contDiff_deriv_of_le_efaf {g : ℝ → ℝ} {n m : WithTop ℕ∞} (h : ContDiff ℝ n g)
    (hm : m + 1 ≤ n) : ContDiff ℝ m (deriv g) := by
  have h1 := h.contDiffOn.deriv_of_isOpen (s := Set.univ) (m := m) isOpen_univ hm
  rwa [contDiffOn_univ] at h1

theorem EFamAngularFacts (m : ℕ) :
    Differentiable ℝ (Work.FTS.PhiStar.Gegenbauer.eFam m) ∧
    Differentiable ℝ (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) ∧
    (∃ L M B : ℝ, 0 < L ∧ 0 < M ∧ 0 ≤ B ∧
      (∀ θ ∈ Set.Icc 0 (Real.pi / 2),
        |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ L * θ) ∧
      (∀ θ ∈ Set.Icc 0 (Real.pi / 2),
        |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ L * (Real.pi / 2 - θ)) ∧
      (∀ θ ∈ Set.Icc 0 (Real.pi / 2),
        |deriv (Work.FTS.PhiStar.Gegenbauer.eFam m) θ| ≤ M) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |Real.tan θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ B)) := by
  obtain ⟨A, hA0, hA⟩ := Work.FTS.ClassC.eFam_sin_two_bound m
  obtain ⟨Q, hQ0, hQ⟩ := Work.FTS.ClassC.eFam_deriv_bound m
  have hC3 : ContDiff ℝ 3 (Work.FTS.PhiStar.Gegenbauer.eFam m) :=
    Work.FTS.ClassC.contDiff_three_eFam m
  refine ⟨hC3.differentiable (by norm_num), ?_, 2 * A + 1, Q + 1, 2 * A, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · exact (contDiff_deriv_of_le_efaf hC3 (m := 2) (by norm_num)).differentiable (by norm_num)
  · linarith
  · linarith
  · linarith
  · -- `|eFam m θ| ≤ (2A+1) θ` on `[0, π/2]`
    intro θ hθ
    have hθ0 : 0 ≤ θ := hθ.1
    have hs : Real.sin (2 * θ) ≤ 2 * θ := Real.sin_le (by linarith)
    have h1 := hA θ hθ
    calc |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ A * Real.sin (2 * θ) := h1
      _ ≤ A * (2 * θ) := mul_le_mul_of_nonneg_left hs hA0
      _ ≤ (2 * A + 1) * θ := by nlinarith [hθ0]
  · -- `|eFam m θ| ≤ (2A+1) (π/2 - θ)` on `[0, π/2]`
    intro θ hθ
    have hpi : 0 ≤ Real.pi - 2 * θ := by linarith [hθ.2, Real.pi_pos]
    have h2 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
    have hs : Real.sin (Real.pi - 2 * θ) ≤ Real.pi - 2 * θ := Real.sin_le hpi
    have h1 := hA θ hθ
    calc |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ A * Real.sin (2 * θ) := h1
      _ = A * Real.sin (Real.pi - 2 * θ) := by rw [Real.sin_pi_sub]
      _ ≤ A * (Real.pi - 2 * θ) := mul_le_mul_of_nonneg_left hs hA0
      _ ≤ (2 * A + 1) * (Real.pi / 2 - θ) := by nlinarith [h2]
  · -- `|deriv (eFam m) θ| ≤ Q + 1` on `[0, π/2]`
    intro θ hθ
    have h1 := hQ θ hθ
    linarith
  · -- `|tan θ · eFam m θ| ≤ 2A` on `(0, π/2)`
    intro θ hθ
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hsin0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hs2 : Real.sin θ ^ 2 ≤ 1 := by nlinarith [hsin0, hsin1]
    have hb := hA θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hdiv : 0 ≤ Real.sin θ / Real.cos θ := div_nonneg hsin0 (le_of_lt hcos)
    have htanabs : |Real.tan θ| = Real.sin θ / Real.cos θ := by
      rw [Real.tan_eq_sin_div_cos, abs_div, abs_of_nonneg hsin0, abs_of_pos hcos]
    calc |Real.tan θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        = |Real.tan θ| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| := abs_mul _ _
      _ = (Real.sin θ / Real.cos θ) * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| := by rw [htanabs]
      _ ≤ (Real.sin θ / Real.cos θ) * (A * Real.sin (2 * θ)) :=
            mul_le_mul_of_nonneg_left hb hdiv
      _ = 2 * A * Real.sin θ ^ 2 := by
            rw [Real.sin_two_mul]
            field_simp
      _ ≤ 2 * A := by nlinarith [hA0, hs2]

end Work.FTS.StrongEps.EComparison
