import Mathlib
import Submission.Work.PertCrux.shadow_constants
import Submission.Work.PertCrux.shadow_step
import Submission.Work.PertCrux.orbit_shadow_close

/-!
# Tube shadowing: perturbing `f₀` on `L'` perturbs its `m`-step orbits on `L`

This is the `rom`-parametrised form of `Work.PertCrux.orbit_shadow_close`.  Let `L ⊆ L' ⊆ ℂ`,
let `f₀ : ℂ → ℂ` be `K₀`-Lipschitz on `L'` with `K₀ ≥ 1`, suppose `f₀` maps `L` into `L`, and
that every point of `L` has `rom`-room: the ball of radius `rom` around its image is still inside
`L'` (`0 < rom ≤ 1`).  Then for `ε ∈ (0, rom]` and a horizon `m` there are `δ₀ ∈ (0,1]` and
`η > 0` such that *every* `f` which is `δ₀`-close to `f₀` on `L'` satisfies

  `‖f^[j] x - f₀^[j] x₀‖ < ε`  for all `j ≤ m`, whenever `x, x₀ ∈ L` with `‖x - x₀‖ < η`.

The argument is the usual finite-horizon shadowing one: the unperturbed orbit of `x₀` stays in `L`
(invariance), the perturbed orbit of `x` stays in `L'` (the room hypothesis, together with the
error bound), and the errors propagate through the recurrence `e_{j+1} ≤ δ₀ + K₀ e_j`, whose
solution `e_j ≤ K₀^j (η + j δ₀)` is `< ε` by the choice of the constants
(`Work.PertCrux.shadow_constants`, `Work.PertCrux.shadow_step`).
-/

namespace Work.Analysis.PertCrux

theorem tube_shadowing {f₀ : ℂ → ℂ} {L L' : Set ℂ} (hLc : IsCompact L')
    (hLL : L ⊆ L') {K₀ rom : ℝ} (hK₀ : 1 ≤ K₀) (hrom : 0 < rom) (hrom1 : rom ≤ 1)
    (hlip : ∀ z ∈ L', ∀ z' ∈ L', ‖f₀ z - f₀ z'‖ ≤ K₀ * ‖z - z'‖)
    (hmaps : ∀ z ∈ L, f₀ z ∈ L)
    (hroom : ∀ z ∈ L, Metric.ball (f₀ z) rom ⊆ L')
    {m : ℕ} {ε : ℝ} (hε : 0 < ε) (hεrom : ε ≤ rom) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∃ η : ℝ, 0 < η ∧
      ∀ {f : ℂ → ℂ} {x x₀ : ℂ},
        (∀ z ∈ L', ‖f z - f₀ z‖ < δ₀) → x ∈ L → x₀ ∈ L → ‖x - x₀‖ < η →
        ∀ j : ℕ, j ≤ m → ‖f^[j] x - f₀^[j] x₀‖ < ε := by
  -- the shadowing constants: `K₀ ^ j * (η + j δ₀) < ε` for every `j ≤ m`
  obtain ⟨δ₀, η, hδ0pos, hδ0le1, hηpos, hbound⟩ :=
    Work.PertCrux.shadow_constants hK₀ hε (le_trans hεrom hrom1) m
  refine ⟨δ₀, hδ0pos, hδ0le1, η, hηpos, ?_⟩
  intro f x x₀ hfclose hxL hx₀L hxdist j hj
  -- the unperturbed orbit of `x₀` stays in `L`, hence in `L'`
  have hx₀it : ∀ i : ℕ, f₀^[i] x₀ ∈ L := by
    intro i
    induction i with
    | zero => simpa using hx₀L
    | succ i ih => rw [Function.iterate_succ_apply']; exact hmaps _ ih
  have hδ0nonneg : 0 ≤ δ₀ := le_of_lt hδ0pos
  -- invariant along the induction: the perturbed orbit stays in `L'` and the error obeys the
  -- geometric bound `K₀ ^ i * (η + i δ₀)`
  have hmain : ∀ i : ℕ, i ≤ m →
      (f^[i] x ∈ L') ∧ ‖f^[i] x - f₀^[i] x₀‖ ≤ K₀ ^ i * (η + (i : ℝ) * δ₀) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨by simpa using hLL hxL, ?_⟩
      have h0 : ‖x - x₀‖ ≤ η := le_of_lt hxdist
      simpa using h0
    | succ i ih =>
      intro hi
      obtain ⟨hLi, hboundi⟩ := ih (Nat.le_of_succ_le hi)
      -- one step of the recurrence, in unfolded form
      have h1 : ‖f (f^[i] x) - f₀ (f^[i] x)‖ < δ₀ := hfclose _ hLi
      have h2 : ‖f₀ (f^[i] x) - f₀ (f₀^[i] x₀)‖ ≤ K₀ * ‖f^[i] x - f₀^[i] x₀‖ :=
        hlip _ hLi _ (hLL (hx₀it i))
      have hrec' : ‖f (f^[i] x) - f₀ (f₀^[i] x₀)‖
          ≤ δ₀ + K₀ * ‖f^[i] x - f₀^[i] x₀‖ := by
        calc ‖f (f^[i] x) - f₀ (f₀^[i] x₀)‖
            ≤ ‖f (f^[i] x) - f₀ (f^[i] x)‖ + ‖f₀ (f^[i] x) - f₀ (f₀^[i] x₀)‖ := by
              rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
              exact dist_triangle _ _ _
          _ ≤ δ₀ + K₀ * ‖f^[i] x - f₀^[i] x₀‖ := add_le_add (le_of_lt h1) h2
      have hbd' : ‖f (f^[i] x) - f₀ (f₀^[i] x₀)‖
          ≤ K₀ ^ (i + 1) * (η + ((i + 1 : ℕ) : ℝ) * δ₀) :=
        Work.PertCrux.shadow_step hK₀ hδ0nonneg hboundi hrec'
      have hlt' : ‖f (f^[i] x) - f₀ (f₀^[i] x₀)‖ < ε :=
        lt_of_le_of_lt hbd' (hbound (i + 1) hi)
      -- the perturbed orbit point is in the `rom`-ball around the unperturbed one, hence in `L'`
      have hmem' : f (f^[i] x) ∈ L' := by
        apply hroom _ (hx₀it i)
        rw [Metric.mem_ball, dist_eq_norm]
        exact lt_of_lt_of_le hlt' hεrom
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact ⟨hmem', hbd'⟩
  exact lt_of_le_of_lt (hmain j hj).2 (hbound j hj)

end Work.Analysis.PertCrux
