import Mathlib
import Submission.Work.Diff.MP.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.MP

open Set Submission.Diff.Alg

set_option maxHeartbeats 4000000

/-- Uniform first- and second-order Taylor remainder bounds for a local solution `α` of
`α' = Q (α)` with `α 0 = S`, on some interval `[0, δ]` with `0 < δ < ε`. The hypothesis `hQ` is
the elementary quadratic estimate for `Q` (`Work.Diff.MP.Q_sub_norm_le` supplies it with
`c = 5 * n ^ 2`). Intended proof: let `M` bound `‖Q (α t)‖` on the compact `Icc 0 (ε/2)` and set
`δ := min (ε/2) (1/(M+1))`, so `‖α t - S‖ ≤ M * t ≤ 1` on `[0,δ]` by the mean value inequality
`norm_image_sub_le_of_norm_deriv_le_segment'`; `Q` is `K`-Lipschitz on `closedBall S 1` with
`K := 2 * c * (‖S‖ + 1)` by `hQ`; the same mean value inequality applied to
`t ↦ α t - S - t • Q S` (derivative `Q (α t) - Q S`, of norm `≤ K * M * t`) gives the quadratic
bound with `C := K * M + M`.


## Proof

`hODE` makes `α` continuous on the open interval `(-ε, ε)`, hence on the compact `Icc 0 (ε/2)`;
`IsCompact.exists_bound_of_continuousOn` gives `B` with `‖α t‖ ≤ B` there, and `hQ` with `T = 0`
turns this into a bound `M = ‖Q 0‖ + c * B ^ 2` for `‖Q (α t)‖` on `Icc 0 (ε/2)` (`Q` is
*quadratic*, so `hQ` controls `Q` by the first power of the radius plus a constant — this is why
the compact interval in the statement is `Icc 0 (ε/2)` and not the whole `(-ε, ε)`).

For `δ := min (ε/2) (1/(M+1))` and `h ∈ Icc 0 δ`, the mean value inequality applied to `α` on
`[0, h]` with the constant bound `M` gives the *linear* remainder `‖α h - S‖ ≤ M * h ≤ 1`. Hence
on `[0, δ]` we have `‖α t‖ ≤ ‖S‖ + 1`, so `hQ` gives the Lipschitz bound
`‖Q (α t) - Q S‖ ≤ 2 * c * (‖S‖ + 1) * M * h` on `[0, h]`; applying the mean value inequality to
`t ↦ α t - t • Q S` (derivative `Q (α t) - Q S`) gives the quadratic remainder
`‖α h - S - h • Q S‖ ≤ 2 * c * (‖S‖ + 1) * M * h ^ 2`.

The auxiliary function is written as `α - fun y => y • Q S` (rather than the `λ`-expression
`fun y => α y - (S + y • Q S)`) because the latter makes type class search pick the pointwise
`Sub`/`Add`/`SMul` instances of the fourfold Pi type `Curv4 n`, which are not definitionally the
ones coming from its bundled `NormedAddCommGroup` structure, and the `HasDerivAt` statements no
longer unify. -/
theorem ode_taylor_estimates (n : ℕ) (S : Submission.Diff.Alg.Curv4 n) (ε : ℝ) (hε : 0 < ε)
    (α : ℝ → Submission.Diff.Alg.Curv4 n) (hα0 : α 0 = S)
    (hODE : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt α (Submission.Diff.Alg.Q (α t)) t)
    (c : ℝ) (hc : 0 ≤ c)
    (hQ : ∀ R T : Submission.Diff.Alg.Curv4 n,
      ‖Submission.Diff.Alg.Q R - Submission.Diff.Alg.Q T‖ ≤ c * (‖R‖ + ‖T‖) * ‖R - T‖) :
    ∃ δ > 0, δ < ε ∧ ∃ C : ℝ, 0 ≤ C ∧
      (∀ h ∈ Set.Icc 0 δ, ‖α h - (S + h • Submission.Diff.Alg.Q S)‖ ≤ C * h ^ 2) ∧
      (∀ h ∈ Set.Icc 0 δ, ‖α h - S‖ ≤ C * h) := by
  -- `Icc 0 (ε/2)` lies in the interval on which `α` solves the ODE.
  have hε2 : 0 < ε / 2 := by linarith
  have hsub : Icc (0:ℝ) (ε/2) ⊆ Ioo (-ε) ε := by
    intro t ht; exact ⟨by linarith [ht.1, hε], by linarith [ht.2, hε]⟩
  have hcont : ContinuousOn α (Icc (0:ℝ) (ε/2)) := fun t ht =>
    ((hODE t (hsub ht)).continuousAt).continuousWithinAt
  -- `B` bounds `‖α t‖` on the compact interval.
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hBnn : 0 ≤ B := le_trans (norm_nonneg (α 0)) (hB 0 ⟨le_refl 0, le_of_lt hε2⟩)
  -- `M` bounds `‖Q (α t)‖` there.
  set M : ℝ := ‖Q (0 : Curv4 n)‖ + c * B ^ 2 with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    nlinarith [norm_nonneg (Q (0 : Curv4 n)), sq_nonneg B, hc]
  have hMbound : ∀ t ∈ Icc (0:ℝ) (ε/2), ‖Q (α t)‖ ≤ M := by
    intro t ht
    have h1 : ‖Q (α t) - Q 0‖ ≤ c * ‖α t‖ * ‖α t‖ := by
      have := hQ (α t) 0
      simpa using this
    have h2 : c * ‖α t‖ * ‖α t‖ ≤ c * B ^ 2 := by
      have h3 : ‖α t‖ * ‖α t‖ ≤ B * B := mul_le_mul (hB t ht) (hB t ht) (norm_nonneg _) hBnn
      calc c * ‖α t‖ * ‖α t‖ = c * (‖α t‖ * ‖α t‖) := by ring
        _ ≤ c * (B * B) := mul_le_mul_of_nonneg_left h3 hc
        _ = c * B ^ 2 := by ring
    calc ‖Q (α t)‖ = ‖(Q (α t) - Q 0) + Q 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖Q (α t) - Q 0‖ + ‖Q 0‖ := norm_add_le _ _
      _ ≤ c * B ^ 2 + ‖Q 0‖ := by linarith
      _ = M := by rw [hMdef]; ring
  -- The step size.
  set δ : ℝ := min (ε / 2) (1 / (M + 1)) with hδdef
  have hM1 : 0 < M + 1 := by linarith
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min hε2 (by positivity)
  have hδle : δ ≤ ε / 2 := by rw [hδdef]; exact min_le_left _ _
  have hδle2 : δ ≤ 1 / (M + 1) := by rw [hδdef]; exact min_le_right _ _
  have hδltε : δ < ε := by linarith
  have hMδ : M * δ ≤ 1 := by
    have h1 : M * δ ≤ M * (1 / (M + 1)) := mul_le_mul_of_nonneg_left hδle2 hMnn
    have h2 : M * (1 / (M + 1)) = M / (M + 1) := by rw [mul_one_div]
    have h3 : M / (M + 1) ≤ 1 := by rw [div_le_one hM1]; linarith
    linarith
  -- Linear Taylor remainder (mean value inequality for `α` on `[0, h]`).
  have hlin : ∀ h ∈ Icc (0:ℝ) δ, ‖α h - S‖ ≤ M * h := by
    intro h hh
    have hsegsub : Icc (0:ℝ) h ⊆ Ioo (-ε) ε := by
      intro x hx
      exact ⟨by linarith [hx.1, hε], by linarith [hx.2, hh.2, hδltε]⟩
    have hderiv : ∀ x ∈ Icc (0:ℝ) h, HasDerivWithinAt α (Q (α x)) (Icc (0:ℝ) h) x :=
      fun x hx => (hODE x (hsegsub hx)).hasDerivWithinAt
    have hb : ∀ x ∈ Ico (0:ℝ) h, ‖Q (α x)‖ ≤ M :=
      fun x hx => hMbound x ⟨hx.1, le_trans (le_of_lt hx.2) (le_trans hh.2 hδle)⟩
    have key := (norm_image_sub_le_of_norm_deriv_le_segment' hderiv hb) h ⟨hh.1, le_rfl⟩
    simpa [hα0] using key
  have hgc : 0 ≤ 2 * c * (‖S‖ + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) hc) (by linarith [norm_nonneg S])
  have hCnn : 0 ≤ 2 * c * (‖S‖ + 1) * M + M := by
    have h2 : 0 ≤ 2 * c * (‖S‖ + 1) * M := mul_nonneg hgc hMnn
    linarith
  refine ⟨δ, hδpos, hδltε, 2 * c * (‖S‖ + 1) * M + M, hCnn, ?_, ?_⟩
  · -- Quadratic Taylor remainder (mean value inequality for `t ↦ α t - t • Q S` on `[0, h]`).
    intro h hh
    have hsegsub : Icc (0:ℝ) h ⊆ Ioo (-ε) ε := by
      intro x hx
      exact ⟨by linarith [hx.1, hε], by linarith [hx.2, hh.2, hδltε]⟩
    have h1x : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y • Q S) (Q S) x := fun x => by
      simpa using (hasDerivAt_id x).smul_const (Q S)
    -- `Q` is `2 c (‖S‖+1)`-Lipschitz on `[0, h]`, where `‖α x - S‖ ≤ 1`.
    have hgbound : ∀ x ∈ Ico (0:ℝ) h, ‖Q (α x) - Q S‖ ≤ 2 * c * (‖S‖ + 1) * M * h := by
      intro x hx
      have hxδ : ‖α x - S‖ ≤ M * x := hlin x ⟨hx.1, le_trans (le_of_lt hx.2) hh.2⟩
      have hMx1 : M * x ≤ 1 := by
        have h1 : M * x ≤ M * h := mul_le_mul_of_nonneg_left (le_of_lt hx.2) hMnn
        have h2 : M * h ≤ M * δ := mul_le_mul_of_nonneg_left hh.2 hMnn
        linarith
      have hdel1 : ‖α x - S‖ ≤ 1 := le_trans hxδ hMx1
      have hnx : ‖α x‖ ≤ ‖S‖ + 1 := by
        calc ‖α x‖ = ‖(α x - S) + S‖ := by rw [sub_add_cancel]
          _ ≤ ‖α x - S‖ + ‖S‖ := norm_add_le _ _
          _ ≤ 1 + ‖S‖ := by linarith [norm_nonneg S]
          _ = ‖S‖ + 1 := by ring
      have hKx : c * (‖α x‖ + ‖S‖) * ‖α x - S‖ ≤ 2 * c * (‖S‖ + 1) * (M * x) := by
        have ha : ‖α x‖ + ‖S‖ ≤ 2 * (‖S‖ + 1) := by linarith [norm_nonneg S]
        have hc2 : c * (‖α x‖ + ‖S‖) ≤ c * (2 * (‖S‖ + 1)) := mul_le_mul_of_nonneg_left ha hc
        calc c * (‖α x‖ + ‖S‖) * ‖α x - S‖
            ≤ c * (2 * (‖S‖ + 1)) * ‖α x - S‖ := mul_le_mul_of_nonneg_right hc2 (norm_nonneg _)
          _ ≤ c * (2 * (‖S‖ + 1)) * (M * x) :=
              mul_le_mul_of_nonneg_left hxδ (mul_nonneg hc (by linarith [norm_nonneg S]))
          _ = 2 * c * (‖S‖ + 1) * (M * x) := by ring
      calc ‖Q (α x) - Q S‖ ≤ c * (‖α x‖ + ‖S‖) * ‖α x - S‖ := hQ (α x) S
        _ ≤ 2 * c * (‖S‖ + 1) * (M * x) := hKx
        _ ≤ 2 * c * (‖S‖ + 1) * (M * h) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_of_lt hx.2) hMnn) hgc
        _ = 2 * c * (‖S‖ + 1) * M * h := by ring
    have hhd : ∀ x ∈ Icc (0:ℝ) h,
        HasDerivWithinAt (α - fun y : ℝ => y • Q S) (Q (α x) - Q S) (Icc (0:ℝ) h) x :=
      fun x hx => ((hODE x (hsegsub hx)).sub (h1x x)).hasDerivWithinAt
    have key := (norm_image_sub_le_of_norm_deriv_le_segment' hhd hgbound) h ⟨hh.1, le_rfl⟩
    have heq : ‖α h - (S + h • Q S)‖
        = ‖(α - fun y : ℝ => y • Q S) h - (α - fun y : ℝ => y • Q S) 0‖ := by
      simp [hα0]; abel
    rw [heq]
    have hkey2 : ‖(α - fun y : ℝ => y • Q S) h - (α - fun y : ℝ => y • Q S) 0‖
        ≤ (2 * c * (‖S‖ + 1) * M * h) * h := by simpa using key
    calc ‖(α - fun y : ℝ => y • Q S) h - (α - fun y : ℝ => y • Q S) 0‖
        ≤ (2 * c * (‖S‖ + 1) * M * h) * h := hkey2
      _ = 2 * c * (‖S‖ + 1) * M * h ^ 2 := by ring
      _ ≤ (2 * c * (‖S‖ + 1) * M + M) * h ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg h)
  · intro h hh
    have hle : M ≤ 2 * c * (‖S‖ + 1) * M + M := by
      have h2 : 0 ≤ 2 * c * (‖S‖ + 1) * M := mul_nonneg hgc hMnn
      linarith
    calc ‖α h - S‖ ≤ M * h := hlin h hh
      _ ≤ (2 * c * (‖S‖ + 1) * M + M) * h := mul_le_mul_of_nonneg_right hle hh.1

end Work.Diff.MP
