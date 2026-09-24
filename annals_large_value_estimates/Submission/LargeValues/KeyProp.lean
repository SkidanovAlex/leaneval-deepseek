import ChallengeDeps
import Mathlib
import Submission.Commons.Analysis.Calculus.smooth_bump_support_Icc_deriv_bounds

open LargeValueEstimates
open Asymptotics Complex
set_option autoImplicit false

/-!
# The Guth–Maynard smoothing bump and the statement of Proposition 4.1 (`KeyProp`)

The paper *New large value estimates for Dirichlet polynomials* (Guth–Maynard) fixes once
and for all a smooth function `w : ℝ → ℝ`, supported on `[1,2]`, nonnegative, with
`‖w^{(j)}‖_∞ = O_j(1)` and `w = 1` on `[6/5,9/5]`, and then reduces Theorem 1.1 to
**Proposition 4.1** (`KeyProp` below), the genuinely new estimate.

We take `w` to be the bump provided by the shared commons
(`Commons.Analysis.Calculus.smooth_bump_support_Icc_deriv_bounds`) and fix it as `bumpW`.
-/

namespace Submission.LargeValues

/-- The Guth–Maynard smoothing bump, chosen from the commons. -/
noncomputable def bumpW : ℝ → ℝ :=
  Classical.choose Commons.Analysis.Calculus.smooth_bump_support_Icc_deriv_bounds

theorem bumpW_spec :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) bumpW ∧ (∀ x, 0 ≤ bumpW x) ∧
      (∀ x, bumpW x ≠ 0 → x ∈ Set.Icc 1 2) ∧
      (∀ x ∈ Set.Icc (6 / 5 : ℝ) (9 / 5 : ℝ), bumpW x = 1) ∧
      (∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv j bumpW x| ≤ C) :=
  Classical.choose_spec Commons.Analysis.Calculus.smooth_bump_support_Icc_deriv_bounds

theorem bumpW_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) bumpW := bumpW_spec.1

theorem bumpW_nonneg : ∀ x, 0 ≤ bumpW x := bumpW_spec.2.1

theorem bumpW_eq_zero_of_notMem {x : ℝ} (hx : x ∉ Set.Icc 1 2) : bumpW x = 0 := by
  by_contra h
  exact hx (bumpW_spec.2.2.1 x h)

theorem bumpW_eq_one {x : ℝ} (hx : x ∈ Set.Icc (6 / 5 : ℝ) (9 / 5 : ℝ)) : bumpW x = 1 :=
  bumpW_spec.2.2.2.1 x hx

theorem bumpW_deriv_bdd : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv j bumpW x| ≤ C :=
  bumpW_spec.2.2.2.2

/-- `M N = N^{6/5}`: in Proposition 4.1 the set `W` lives in an interval of length `N^{6/5}`. -/
noncomputable def M (N : ℕ) : ℝ := (N : ℝ) ^ (6 / 5 : ℝ)

theorem M_pos {N : ℕ} (hN : 1 ≤ N) : 0 < M N := by
  rw [M]; exact Real.rpow_pos_of_pos (by exact_mod_cast hN) _

theorem M_ge_one {N : ℕ} (hN : 1 ≤ N) : 1 ≤ M N := by
  rw [M]
  calc (1 : ℝ) = (1 : ℝ) ^ (6 / 5 : ℝ) := by simp
    _ ≤ (N : ℝ) ^ (6 / 5 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hN) (by norm_num)

/-- The Dirichlet polynomial with the smoothing weight inserted. -/
noncomputable def smoothedPoly (N : ℕ) (b : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc N (2 * N), ((bumpW ((n : ℝ) / (N : ℝ))) : ℂ) * b n * (n : ℂ) ^ (I * (t : ℂ))

/-- **Guth–Maynard Proposition 4.1** (`KeyProp`), with the `o_ε(1)` made explicit as an
"eventually" statement: for every `ε > 0` and every threshold there is a larger threshold
`N₁` such that for all `N ≥ N₁`, all `V ∈ [N^{7/10}, N^{4/5}]`, all `1`-bounded coefficient
sequences `b` and every `(N^{6/5})^ε`-separated set `W ⊆ [0, N^{6/5}]` on which the smoothed
polynomial takes values of modulus at least `V`, we have

  `|W| ≤ N^ε · N^{6/5} · N^{12/5} · V^{-4}`.

This is exactly the paper's bound `|W| ≤ T·N^{(12-20σ)/5+o_ε(1)}` with `T = N^{6/5}`,
`V = N^σ`, and the `N^{o_ε(1)}` factor absorbed into `N^ε` by enlarging `N₁`.
(Note `N^{6/5}·N^{12/5}·V^{-4} = N^{18/5-4σ}`.) -/
def KeyPropStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ, ∃ N₁ : ℕ, N₀ ≤ N₁ ∧
    ∀ (N : ℕ), N₁ ≤ N → ∀ (V : ℝ), (N : ℝ) ^ (7 / 10 : ℝ) ≤ V →
      V ≤ (N : ℝ) ^ (4 / 5 : ℝ) →
      ∀ (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) → ∀ (W : Finset ℝ),
        (∀ t ∈ W, t ∈ Set.Icc 0 (M N)) →
        (∀ t ∈ W, ∀ s ∈ W, t ≠ s → (M N) ^ ε ≤ |t - s|) →
        (∀ t ∈ W, V ≤ ‖smoothedPoly N b t‖) →
        (W.card : ℝ) ≤ (N : ℝ) ^ ε * M N * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ)

end Submission.LargeValues
