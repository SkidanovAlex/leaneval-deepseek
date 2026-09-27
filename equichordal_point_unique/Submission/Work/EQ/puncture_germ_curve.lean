import Mathlib
import Submission.Work.EQ.H0_path_limit_germ_curve
import Submission.Work.EQ.bp_aux

namespace Work.EQ

/-- Germ-curve constraint for the puncture branch of the path-limit step: the first window entry of
the backward-Puiseux branch `σ` lies on the small unstable germ curve `ugermC a h ·` for every
parameter in a punctured disc, not merely along the path.

Inputs: the uniform backward tail of the path of chains, the window equalities at the parameter
`t s`, a continuous parameter `t s → 0` with `t s ≠ 0` and `‖t s‖ < rhoFin'`, the germ data
`(φ, Yinv, ρY)` from `Work.EQ.germC_graph` together with the strict self-map property of the `y`
coordinate (from `Work.EQ.germC_small_ball_maps`) and the identification `ψ₂ (γ s) → v` with
`‖λ ^ m₁ * v‖ ≤ ρY / 4`, which makes the witnesses `λ ^ m₁ * ψ₂ (γ s)` satisfy `‖·‖ ≤ ρY / 2`
eventually.

Route: at each tail index `s` one has
`ugermC a h (λ ^ m₁ * ψ₂ (γ s)) = (γ s).1 (-m₁) = branchPt a c u R σ (t s) 0`, so
`Work.EQ.H0_path_limit_germ_curve` (module `Submission.Work.EQ.H0_path_limit_germ_curve`) applies
to the sequence `s ↦ t (S + n)` with the witnesses `λ ^ m₁ * ψ₂ (γ (S + n))`.  The strict
positivity and the bound on `t` are inherited, and the eventual bounds on the witnesses (from
`hsm` and `h2`) are made unconditional by shifting the index, which changes no conclusion. -/
theorem puncture_germ_curve {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) {γ : ℝ → Work.EQ.ChainData} {S : ℝ} {n₁ m₁ : ℕ}
    {u : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : AnalyticOnNhd ℂ (fun w : ℂ => Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ n₁ * w))
      (Metric.ball u R))
    (hbw : ∀ s : ℝ, S ≤ s → ∀ n : ℕ, m₁ ≤ n →
      (γ s).1 (-(n : ℤ)) = Work.EQ.ugermC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ n * (γ s).2.2))
    {σ : Fin (n₁ + m₁) → Bool} (hσ : Work.EQ.Adm a
      (fun w : ℂ => Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ n₁ * w)) u R σ)
    {ρY : ℝ} (hρY : 0 < ρY) {φ Yinv : ℂ → ℂ}
    (hYan : AnalyticOnNhd ℂ Yinv (Metric.ball (0 : ℂ) ρY))
    (hY1 : ∀ y ∈ Metric.ball (0 : ℂ) ρY, (Work.EQ.germC a h (Yinv y)).2 = y)
    (hY2 : ∀ y ∈ Metric.ball (0 : ℂ) ρY, (Work.EQ.germC a h (Yinv y)).1 = φ y)
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((Work.EQ.germC a h w).2) = w)
    (hstrict : ∀ w : ℂ, ‖w‖ ≤ ρY → ‖(Work.EQ.germC a h w).2‖ < ρY)
    {t : ℝ → ℂ} (ht0 : ∀ s : ℝ, 0 < ‖t s‖)
    (htρ : ∀ s : ℝ, ‖t s‖ < Work.EQ.rhoFin' a
      (fun w : ℂ => Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ n₁ * w)) u R (n₁ + m₁))
    (ht : Filter.Tendsto t Filter.atTop (nhds 0))
    (hwin : ∀ s : ℝ, S ≤ s → ∀ j : Fin (n₁ + m₁ + 1),
      (γ s).1 ((((j : ℕ) : ℤ) - (m₁ : ℤ))) =
        Work.EQ.branchPt a (fun w : ℂ => Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ n₁ * w))
          u R σ (t s) j)
    {v : ℂ} (hv : v ≠ 0) (h2 : Filter.Tendsto (fun s : ℝ => (γ s).2.2) Filter.atTop (nhds v))
    (hsm : ‖((Work.EQ.eqLam a : ℝ) : ℂ) ^ m₁ * v‖ ≤ ρY / 4) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ Work.EQ.rhoFin' a
        (fun w : ℂ => Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ n₁ * w)) u R (n₁ + m₁) ∧
      ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ' →
        ∃ w : ℂ, w ∈ Metric.ball (0 : ℂ) ρY ∧ w ≠ 0 ∧
          Work.EQ.ugermC a h w = Work.EQ.branchPt a
            (fun w : ℂ => Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ n₁ * w)) u R σ t 0 := by
  -- The eventual non-vanishing of `ψ₂ ∘ γ` and the eventual bound on the witnesses.
  have hone : ∀ᶠ s : ℝ in Filter.atTop, (γ s).2.2 ≠ 0 := h2.eventually_ne hv
  have hbnd : ∀ᶠ s : ℝ in Filter.atTop,
      ‖((Work.EQ.eqLam a : ℝ) : ℂ) ^ m₁ * (γ s).2.2‖ < ρY / 2 := by
    have hlim : Filter.Tendsto
        (fun s : ℝ => ‖((Work.EQ.eqLam a : ℝ) : ℂ) ^ m₁ * (γ s).2.2‖)
        Filter.atTop (nhds ‖((Work.EQ.eqLam a : ℝ) : ℂ) ^ m₁ * v‖) :=
      (h2.const_mul (((Work.EQ.eqLam a : ℝ) : ℂ) ^ m₁)).norm
    have hlt : ‖((Work.EQ.eqLam a : ℝ) : ℂ) ^ m₁ * v‖ < ρY / 2 := by linarith
    exact hlim.eventually (eventually_lt_nhds hlt)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (hone.and hbnd)
  -- Shift the index so that every term of the sequence enjoys both properties.
  let N : ℝ := max (M - S) 0
  let s : ℕ → ℝ := fun n => (n : ℝ) + (S + N)
  have hN0 : 0 ≤ N := le_max_right _ _
  have hNS : M - S ≤ N := le_max_left _ _
  have hsS : ∀ n : ℕ, S ≤ s n := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    simp only [s]
    linarith
  have hsM : ∀ n : ℕ, M ≤ s n := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    simp only [s]
    linarith
  have hStend : Filter.Tendsto s Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) + (S + N)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    simpa only [s] using h1
  -- The sequence of parameters and the sequence of witnesses.
  let T : ℕ → ℂ := fun n => t (s n)
  let W : ℕ → ℂ := fun n => ((Work.EQ.eqLam a : ℝ) : ℂ) ^ m₁ * (γ (s n)).2.2
  have hT0 : ∀ n : ℕ, T n ≠ 0 := by
    intro n
    have h := ht0 (s n)
    rw [norm_pos_iff] at h
    simpa only [T] using h
  have hTlt : ∀ n : ℕ, ‖T n‖ < Work.EQ.rhoFin' a
      (fun w : ℂ => Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ n₁ * w)) u R (n₁ + m₁) :=
    fun n => htρ (s n)
  have hTtend : Filter.Tendsto T Filter.atTop (nhds 0) := ht.comp hStend
  have hlam_ne : ((Work.EQ.eqLam a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by
      rw [Work.EQ.eqLam]
      exact div_ne_zero (by linarith) (by linarith))
  have hWne : ∀ n : ℕ, W n ≠ 0 := by
    intro n
    exact mul_ne_zero (pow_ne_zero _ hlam_ne) (hM (s n) (hsM n)).1
  have hWball : ∀ n : ℕ, ‖W n‖ ≤ ρY / 2 := by
    intro n
    exact le_of_lt (hM (s n) (hsM n)).2
  have hWug : ∀ n : ℕ,
      Work.EQ.ugermC a h (W n) =
        Work.EQ.branchPt a (fun w : ℂ => Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ n₁ * w))
          u R σ (T n) 0 := by
    intro n
    have h1 : (γ (s n)).1 (-(m₁ : ℤ)) = Work.EQ.ugermC a h (W n) := hbw (s n) (hsS n) m₁ le_rfl
    have h2 := hwin (s n) (hsS n) (0 : Fin (n₁ + m₁ + 1))
    have h0 : ((((0 : Fin (n₁ + m₁ + 1)) : ℕ) : ℤ) - (m₁ : ℤ)) = -(m₁ : ℤ) := by simp
    rw [← h1, ← h0]
    exact h2
  obtain ⟨ρ', hρ'0, hρ'le, hρ'⟩ :=
    Work.EQ.H0_path_limit_germ_curve (a := a) ha0 ha1 hh hR hc hσ hρY hYan hY1 hY2 hY3 hstrict
      (t := T) hT0 hTlt hTtend (w := W) hWne hWball hWug
  exact ⟨ρ', hρ'0, hρ'le, hρ'⟩

end Work.EQ
