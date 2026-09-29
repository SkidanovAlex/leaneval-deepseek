import Mathlib

open scoped Topology

namespace Work.OdeCont

open Filter

/-- Gluing a compatible increasing sequence of holomorphic functions on nested annuli
`r0 < ‖z‖ < τ n`, with `τ n → σ`, into a holomorphic function on `r0 < ‖z‖ < σ`.

The candidate is defined pointwise: at `z` with `‖z‖ < σ` there is some `n` with
`‖z‖ < τ n` (because `τ n → σ`), and any such choice gives the same value by `hagree`.
Differentiability at a point is local: near `z` the glued function coincides with `Y n`
on the open annulus `r0 < ‖w‖ < τ n`. -/
theorem glue_seq {k : ℕ} {r0 σ : ℝ} {τ : ℕ → ℝ} (hτ : ∀ n, r0 < τ n) (hle : ∀ n, τ n ≤ σ)
    (hlim : Filter.Tendsto τ Filter.atTop (nhds σ)) (Y : ℕ → ℂ → Fin k → ℂ)
    (hY : ∀ n, DifferentiableOn ℂ (Y n) {z : ℂ | r0 < ‖z‖ ∧ ‖z‖ < τ n})
    (hagree : ∀ n m, Set.EqOn (Y n) (Y m) {z : ℂ | r0 < ‖z‖ ∧ ‖z‖ < min (τ n) (τ m)}) :
    ∃ Yσ : ℂ → Fin k → ℂ, DifferentiableOn ℂ Yσ {z : ℂ | r0 < ‖z‖ ∧ ‖z‖ < σ} ∧
      ∀ n, Set.EqOn Yσ (Y n) {z : ℂ | r0 < ‖z‖ ∧ ‖z‖ < τ n} := by
  classical
  -- each annulus is open
  have hOpen : ∀ n : ℕ, IsOpen {z : ℂ | r0 < ‖z‖ ∧ ‖z‖ < τ n} := by
    intro n
    have h1 : IsOpen {z : ℂ | r0 < ‖z‖} :=
      (isOpen_Ioi (a := r0)).preimage (f := fun z : ℂ => ‖z‖) continuous_norm
    have h2 : IsOpen {z : ℂ | ‖z‖ < τ n} :=
      (isOpen_Iio (a := τ n)).preimage (f := fun z : ℂ => ‖z‖) continuous_norm
    exact h1.inter h2
  -- the nested annuli cover the limiting annulus
  have hcov : ∀ z : ℂ, ‖z‖ < σ → ∃ n, ‖z‖ < τ n := by
    intro z hz
    have hpos : 0 < σ - ‖z‖ := sub_pos.mpr hz
    have hev : ∀ᶠ n in Filter.atTop, dist (τ n) σ < σ - ‖z‖ :=
      hlim.eventually (Metric.ball_mem_nhds σ hpos)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    refine ⟨N, ?_⟩
    have h2 : σ - τ N ≤ |τ N - σ| := by
      simpa using neg_le_abs (τ N - σ)
    have h3 : |τ N - σ| = dist (τ N) σ := (Real.dist_eq _ _).symm
    linarith [hN N le_rfl, h3]
  let Yσ : ℂ → Fin k → ℂ := fun z => if h : ∃ n, ‖z‖ < τ n then Y (Classical.choose h) z else 0
  have hYσval : ∀ z (h : ∃ n, ‖z‖ < τ n), Yσ z = Y (Classical.choose h) z := by
    intro z h
    simp only [Yσ]
    exact dif_pos h
  -- the glued function agrees with each `Y n` on the corresponding annulus
  have hagreeOn : ∀ n : ℕ, Set.EqOn Yσ (Y n) {z : ℂ | r0 < ‖z‖ ∧ ‖z‖ < τ n} := by
    intro n z hz
    obtain ⟨hz1, hz2⟩ := hz
    have hex : ∃ m, ‖z‖ < τ m := ⟨n, hz2⟩
    rw [hYσval z hex]
    exact hagree (Classical.choose hex) n ⟨hz1, lt_min (Classical.choose_spec hex) hz2⟩
  refine ⟨Yσ, ?_, hagreeOn⟩
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨n, hn⟩ := hcov z hz2
  have hzn : z ∈ {w : ℂ | r0 < ‖w‖ ∧ ‖w‖ < τ n} := ⟨hz1, hn⟩
  have hmem : {w : ℂ | r0 < ‖w‖ ∧ ‖w‖ < τ n} ∈ 𝓝 z := (hOpen n).mem_nhds hzn
  have hdn : DifferentiableAt ℂ (Y n) z := (hY n).differentiableAt hmem
  have heq : Yσ =ᶠ[𝓝 z] Y n := by
    filter_upwards [hmem] with w hw
    exact hagreeOn n hw
  exact (hdn.congr_of_eventuallyEq heq).differentiableWithinAt

end Work.OdeCont
