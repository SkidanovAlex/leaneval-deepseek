import Mathlib
import Submission.Work.PertCrux.shadow_step

/-!
# `Work.Pert.pert2v2.shadow_walk_local` — finite-horizon shadowing with a *local* Lipschitz bound

This is the same shadowing estimate as `Work.Pert.pert2v2.shadow_walk_orbit`, except that the
Lipschitz hypothesis on `F₀` is only available for pairs `u, u' ∈ Q` at distance `≤ B`.  The extra
hypothesis `hB : K ^ m * (η + m * δ) ≤ B` makes the induction go through unchanged: the a priori
closed form `B j = K ^ j * (η + j * δ)` is monotone in `j` (here `K ≥ 1`, `η, δ ≥ 0`), so along
the walk the two iterates are always at distance `≤ K ^ m * (η + m * δ) ≤ B` and the local
Lipschitz hypothesis applies.
-/

namespace Work.Pert.pert2v2

/-- The a priori closed form `j ↦ K ^ j * (η + j * δ)` is monotone for `1 ≤ K`, `0 ≤ η`, `0 ≤ δ`. -/
theorem shadow_local_bound_mono {K η δ : ℝ} {m j : ℕ}
    (hK : 1 ≤ K) (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hj : j ≤ m) :
    K ^ j * (η + (j : ℝ) * δ) ≤ K ^ m * (η + (m : ℝ) * δ) := by
  have hKj : K ^ j ≤ K ^ m := pow_le_pow_right₀ hK hj
  have hjm : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hj
  have h1 : η + (j : ℝ) * δ ≤ η + (m : ℝ) * δ := by
    have := mul_le_mul_of_nonneg_right hjm hδ
    linarith
  have hj0 : (0 : ℝ) ≤ η + (j : ℝ) * δ := by
    have : (0 : ℝ) ≤ (j : ℝ) := by positivity
    have := mul_nonneg this hδ
    linarith
  exact mul_le_mul hKj h1 hj0 (by positivity)

/-- **Finite-horizon shadowing, locally Lipschitz form.**  If `F₀` is `K`-Lipschitz on `Q` at
distance scale `B` (`K ≥ 1`), `F` is `δ`-close to `F₀` on `Q`, the two orbits of `z` (under `F`)
and of `z₀` (under `F₀`) stay in `Q` up to time `m`, `‖z - z₀‖ ≤ η`, and the a priori bound
`K ^ m * (η + m * δ)` does not exceed `B`, then
`‖F^[m] z - F₀^[m] z₀‖ ≤ K ^ m * (η + m * δ)`. -/
theorem shadow_walk_local {F F₀ : ℂ → ℂ} {Q : Set ℂ} {K η δ B : ℝ} {m : ℕ} {z z₀ : ℂ}
    (hK : 1 ≤ K) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hlip : ∀ u ∈ Q, ∀ u' ∈ Q, ‖u - u'‖ ≤ B → ‖F₀ u - F₀ u'‖ ≤ K * ‖u - u'‖)
    (hclose : ∀ u ∈ Q, ‖F u - F₀ u‖ ≤ δ)
    (hstay : ∀ j : ℕ, j ≤ m → F^[j] z ∈ Q)
    (hstay₀ : ∀ j : ℕ, j ≤ m → F₀^[j] z₀ ∈ Q)
    (hzz : ‖z - z₀‖ ≤ η)
    (hB : K ^ m * (η + (m : ℝ) * δ) ≤ B) :
    ‖F^[m] z - F₀^[m] z₀‖ ≤ K ^ m * (η + (m : ℝ) * δ) := by
  have key : ∀ j : ℕ, j ≤ m → ‖F^[j] z - F₀^[j] z₀‖ ≤ K ^ j * (η + (j : ℝ) * δ) := by
    intro j
    induction j with
    | zero => intro _; simpa using hzz
    | succ k ih =>
      intro hk
      have hk' : k ≤ m := le_trans (Nat.le_succ k) hk
      have ihk := ih hk'
      -- the a priori bound keeps the two iterates within the Lipschitz scale `B`
      have hdB : ‖F^[k] z - F₀^[k] z₀‖ ≤ B :=
        le_trans ihk (le_trans (shadow_local_bound_mono hK hη hδ hk') hB)
      have hrec : ‖F^[k + 1] z - F₀^[k + 1] z₀‖ ≤ δ + K * ‖F^[k] z - F₀^[k] z₀‖ := by
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        have h1 : ‖F (F^[k] z) - F₀ (F^[k] z)‖ ≤ δ := hclose _ (hstay k hk')
        have h2 : ‖F₀ (F^[k] z) - F₀ (F₀^[k] z₀)‖ ≤ K * ‖F^[k] z - F₀^[k] z₀‖ :=
          hlip _ (hstay k hk') _ (hstay₀ k hk') hdB
        calc ‖F (F^[k] z) - F₀ (F₀^[k] z₀)‖
            = ‖(F (F^[k] z) - F₀ (F^[k] z)) + (F₀ (F^[k] z) - F₀ (F₀^[k] z₀))‖ := by ring_nf
          _ ≤ ‖F (F^[k] z) - F₀ (F^[k] z)‖ + ‖F₀ (F^[k] z) - F₀ (F₀^[k] z₀)‖ := norm_add_le _ _
          _ ≤ δ + K * ‖F^[k] z - F₀^[k] z₀‖ := add_le_add h1 h2
      exact Work.PertCrux.shadow_step hK hδ ihk hrec
  exact key m le_rfl

end Work.Pert.pert2v2
