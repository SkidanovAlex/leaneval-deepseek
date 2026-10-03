import Mathlib
import Submission.Work.Pert.CoordDefs

namespace Work.Pert

/-!
# `Work.Pert.dev_deriv_bound_jourA`

Pointwise derivative bound for the deviation `dev Ψ = Ψ - id` of a Fatou coordinate `Ψ` of the
lifted near-translation `F = liftF u σ α` on the gate `Qm ξ₁ α`, restricted to the journey
`JourA η` (Shishikura (4.2.5), the `JourA` form consumed by the `PertCoordClose` assembly).

The content is elementary.  On `Qc η ξ₁ α ⊇ JourA η` the hypothesis `hder` compares `Ψ'` with
`1/(F - id)`; it remains to compare `1/(F ζ - ζ)` with `1`.  Writing

  `F ζ - ζ = 1 + w`,   `w := F ζ - (ζ + 1)`,

the reverse triangle inequality gives `‖w‖ ≤ 1/32 ⇒ ‖1 + w‖ ≥ 31/32`, whence

  `‖1/(1+w) - 1‖ = ‖w‖/‖1+w‖ ≤ (32/31)‖w‖`,

and `w` is bounded by the two hypotheses `hvt` (`‖w‖ ≤ 1/32`) and `hvl`
(`‖w‖ ≤ (3/2)(‖τ_f ζ‖·‖u(τ_f ζ)‖ + δu)`), the latter combining with `hτb` and `hbdd` into
`‖w‖ ≤ 12/η + (3/2)δu`.  Note `hvl`, `hvt` and `hder` are all applied at the *same* `ζ`, which is
why the hypotheses `hJc`, `hτ`, `hτb`, `hvl` are phrased on `JourA η` and not on `Qc η ξ₁ α`.
-/

/-- If `‖w‖ ≤ 1/32` then `‖1/(w + 1) - 1‖ ≤ (32/31)‖w‖`. -/
private lemma norm_one_div_one_add_sub_one_le (w : ℂ) (hw : ‖w‖ ≤ 1 / 32) :
    ‖1 / (w + 1) - 1‖ ≤ (32 / 31) * ‖w‖ := by
  -- reverse triangle: `1 = ‖1‖ ≤ ‖w + 1‖ + ‖w‖`
  have hnorm : 31 / 32 ≤ ‖w + 1‖ := by
    have h1 : (1 : ℝ) ≤ ‖w + 1‖ + ‖w‖ := by
      have h := norm_sub_le (w + 1) w
      rw [show (w + 1) - w = (1 : ℂ) by ring, norm_one] at h
      exact h
    linarith
  have hne : w + 1 ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at hnorm
    norm_num at hnorm
  have hkey : 1 / (w + 1) - 1 = -w / (w + 1) := by
    field_simp
    ring
  rw [hkey, norm_div, norm_neg]
  calc ‖w‖ / ‖w + 1‖ ≤ ‖w‖ / (31 / 32) :=
        div_le_div_of_nonneg_left (norm_nonneg w) (by norm_num) hnorm
    _ = (32 / 31) * ‖w‖ := by ring

theorem dev_deriv_bound_jourA {ξ₁ η rr δu : ℝ} {u : ℂ → ℂ} {σ α : ℂ} {Ψ : ℂ → ℂ}
    (hη : 100 ≤ η)
    (hΨ : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Ψ (Work.Pert.Qm ξ₁ α))
    (hder : ∀ ζ ∈ Work.Pert.Qc η ξ₁ α,
      ‖deriv Ψ ζ - 1 / (Work.Pert.liftF u σ α ζ - ζ)‖ ≤ 1 / 10000)
    (hbdd : ∀ z ∈ Metric.ball 0 rr, ‖u z‖ ≤ 2)
    (hvt : ∀ ζ ∈ Work.Pert.JourA η, ‖Work.Pert.liftF u σ α ζ - (ζ + 1)‖ ≤ 1 / 32)
    (hJc : ∀ ζ ∈ Work.Pert.JourA η, ζ ∈ Work.Pert.Qc η ξ₁ α)
    (hτ : ∀ ζ ∈ Work.Pert.JourA η, Work.Pert.tauC σ α ζ ∈ Metric.ball 0 rr)
    (hτb : ∀ ζ ∈ Work.Pert.JourA η, ‖Work.Pert.tauC σ α ζ‖ ≤ 4 / η)
    (hvl : ∀ ζ ∈ Work.Pert.JourA η,
      ‖Work.Pert.liftF u σ α ζ - (ζ + 1)‖ ≤
        (3 / 2) * (‖Work.Pert.tauC σ α ζ‖ * ‖u (Work.Pert.tauC σ α ζ)‖ + δu)) :
    (∀ ζ ∈ Work.Pert.JourA η, DifferentiableAt ℂ Ψ ζ) ∧
    (∀ ζ ∈ Work.Pert.JourA η,
      ‖deriv (Work.Pert.dev Ψ) ζ‖ ≤ 1 / 10000 + (32 / 31) * (12 / η + 3 / 2 * δu)) := by
  have hηpos : 0 < η := by linarith
  have hη100 : 0 < η / 100 := by linarith
  -- `JourA η ⊆ Qc η ξ₁ α ⊆ Qm ξ₁ α`, and `Qc` carries an `η/100`-ball inside `Qm`
  have hdiff : ∀ ζ ∈ Work.Pert.JourA η, DifferentiableAt ℂ Ψ ζ := fun ζ hζ =>
    (hΨ.1.mono (hJc ζ hζ).2).differentiableAt (Metric.closedBall_mem_nhds ζ hη100)
  refine ⟨hdiff, fun ζ hζ => ?_⟩
  have hJcζ := hJc ζ hζ
  have hd := hdiff ζ hζ
  have hderiv : deriv (Work.Pert.dev Ψ) ζ = deriv Ψ ζ - 1 := by
    unfold Work.Pert.dev
    exact (hd.hasDerivAt.sub (hasDerivAt_id ζ)).deriv
  rw [hderiv]
  have hder' : ‖deriv Ψ ζ - 1 / (Work.Pert.liftF u σ α ζ - ζ)‖ ≤ 1 / 10000 := hder ζ hJcζ
  -- the defect `w = F ζ - (ζ + 1)` is small
  have hw1 : ‖Work.Pert.liftF u σ α ζ - (ζ + 1)‖ ≤ 1 / 32 := hvt ζ hζ
  have hw2 : ‖Work.Pert.liftF u σ α ζ - (ζ + 1)‖ ≤ 12 / η + 3 / 2 * δu := by
    have hprod : ‖Work.Pert.tauC σ α ζ‖ * ‖u (Work.Pert.tauC σ α ζ)‖ ≤ 8 / η := by
      have h1 := mul_le_mul (hτb ζ hζ) (hbdd _ (hτ ζ hζ)) (norm_nonneg _)
        (le_of_lt (div_pos (by norm_num) hηpos))
      rwa [show (4 / η) * 2 = 8 / η by ring] at h1
    have h2 : ‖Work.Pert.tauC σ α ζ‖ * ‖u (Work.Pert.tauC σ α ζ)‖ + δu ≤ 8 / η + δu := by
      linarith
    have h3 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 3 / 2)
    have h4 : (3 / 2) * (8 / η + δu) = 12 / η + 3 / 2 * δu := by ring
    linarith [hvl ζ hζ, h3]
  -- compare `1/(F ζ - ζ)` with `1`
  have hfrac : ‖1 / (Work.Pert.liftF u σ α ζ - ζ) - 1‖ ≤
      (32 / 31) * (12 / η + 3 / 2 * δu) := by
    have he : Work.Pert.liftF u σ α ζ - ζ
        = (Work.Pert.liftF u σ α ζ - (ζ + 1)) + 1 := by ring
    rw [he]
    exact le_trans (norm_one_div_one_add_sub_one_le _ hw1)
      (mul_le_mul_of_nonneg_left hw2 (by norm_num : (0 : ℝ) ≤ 32 / 31))
  -- triangle inequality
  have htri : ‖deriv Ψ ζ - 1‖ ≤
      ‖deriv Ψ ζ - 1 / (Work.Pert.liftF u σ α ζ - ζ)‖ +
        ‖1 / (Work.Pert.liftF u σ α ζ - ζ) - 1‖ := by
    have h := norm_add_le (deriv Ψ ζ - 1 / (Work.Pert.liftF u σ α ζ - ζ))
      (1 / (Work.Pert.liftF u σ α ζ - ζ) - 1)
    have he : deriv Ψ ζ - 1 / (Work.Pert.liftF u σ α ζ - ζ) +
        (1 / (Work.Pert.liftF u σ α ζ - ζ) - 1) = deriv Ψ ζ - 1 := by ring
    rwa [he] at h
  linarith

end Work.Pert
