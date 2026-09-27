import Mathlib

/-!
# `Work.EKLC6Core.shell_borel_cantelli` — the Borel–Cantelli bound on the shell visitation set

If `shell : ℝ → Set X` satisfies the *linear* thin-boundary estimate `μ (shell s) ≤ C s` for all
`s > 0` and `φ` preserves `μ`, then the set of points whose `φ`-orbit meets the shell
`shell (ρ λⁿ)` at *some* time `n ≥ N` has measure tending to `0` as `N → ∞`:

  `μ (⋃_{n ≥ N} φ⁻ⁿ (shell (ρ λⁿ))) ≤ C ρ λ^N / (1 - λ)`.

This is Pisa 7.31 with the *free* rate `λ`: the paper uses `λ` equal to the contraction rate of
the diagonal flow, which only gives the "sandwich" of Definition 7.25; using an exponent
`μ ∈ (λ,1)` instead (the estimate is linear in the radius, so any rate is allowed) is what makes
the atoms of the descending plaque algebra genuinely *open* — see
`Work.EKLC6Core.isOpen_shape_pastSig_of_margin`.
-/

open MeasureTheory Filter
open scoped ENNReal

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

/-- **The tail Borel–Cantelli bound.**  For a measure-preserving `φ`, a shell family with linear
thinness `μ (shell s) ≤ C s`, and a rate `λ ∈ (0,1)`, the measure of the set of points whose orbit
meets the shells `shell (ρ λⁿ)` at some time `n ≥ N` is bounded by `C ρ λ^N / (1 - λ)`, hence
arbitrarily small for large `N`. -/
theorem exists_tail_iUnion_shell_lt {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {φ : X → X} (hmp : MeasurePreserving φ μ μ)
    {shell : ℝ → Set X} {C : ℝ} (hC : 0 < C)
    (hthin : ∀ s : ℝ, 0 < s → μ (shell s) ≤ ENNReal.ofReal (C * s))
    {lam ρ : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hρ : 0 < ρ) :
    ∀ ε : ENNReal, 0 < ε → ∃ N : ℕ,
      μ (⋃ n ∈ Set.Ici N, ((φ^[n]) ⁻¹' shell (ρ * lam ^ n))) < ε := by
  intro ε hε
  by_cases htop : ε = ⊤
  · exact ⟨0, by rw [htop]; exact lt_top_iff_ne_top.mpr (measure_ne_top μ _)⟩
  have hεpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  -- a small real bound gives a bound below `ε`
  have hhalf : ENNReal.ofReal (ε.toReal / 2) < ε := by
    have h2 : ENNReal.ofReal (ε.toReal / 2) < ENNReal.ofReal ε.toReal := by
      rw [ENNReal.ofReal_lt_ofReal_iff hεpos]
      linarith
    rwa [ENNReal.ofReal_toReal htop] at h2
  have h1mlam : 0 < 1 - lam := by linarith
  -- choose `N` with `C ρ λ^N / (1-λ) < ε.toReal / 2`
  have htend : Filter.Tendsto (fun N : ℕ => C * ρ * lam ^ N / (1 - lam)) Filter.atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0.le hlam1).const_mul (C * ρ)
    have h2 : Filter.Tendsto (fun N : ℕ => C * ρ * lam ^ N * (1 - lam)⁻¹) Filter.atTop
        (nhds ((C * ρ * 0) * (1 - lam)⁻¹)) := h.mul_const _
    simpa [div_eq_mul_inv] using h2
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (htend.eventually (isOpen_Iio.mem_nhds (by linarith : (0:ℝ) < ε.toReal / 2)))
  have hN' : C * ρ * lam ^ N / (1 - lam) < ε.toReal / 2 := hN N le_rfl
  refine ⟨N, lt_of_le_of_lt ?_ (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (le_of_lt hN')) hhalf)⟩
  -- the tail is a union over `k` of the shells at time `k + N`
  have hreindex : (⋃ n ∈ Set.Ici N, ((φ^[n]) ⁻¹' shell (ρ * lam ^ n)))
      = ⋃ k : ℕ, ((φ^[k + N]) ⁻¹' shell (ρ * lam ^ (k + N))) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ici, Set.mem_preimage]
    constructor
    · rintro ⟨n, hn, hx⟩
      exact ⟨n - N, by rwa [Nat.sub_add_cancel hn]⟩
    · rintro ⟨k, hx⟩
      exact ⟨k + N, le_add_self, hx⟩
  rw [hreindex]
  -- termwise bound
  have hstep : ∀ k : ℕ, μ (((φ^[k + N]) ⁻¹' shell (ρ * lam ^ (k + N))))
      ≤ ENNReal.ofReal (C * ρ * lam ^ N * lam ^ k) := by
    intro k
    have hpos : 0 < ρ * lam ^ (k + N) := mul_pos hρ (pow_pos hlam0 _)
    have hle := MeasureTheory.Measure.le_map_apply (μ := μ)
      ((hmp.iterate (k + N)).measurable).aemeasurable (shell (ρ * lam ^ (k + N)))
    rw [(hmp.iterate (k + N)).map_eq] at hle
    have h2 : μ (shell (ρ * lam ^ (k + N))) ≤ ENNReal.ofReal (C * (ρ * lam ^ (k + N))) :=
      hthin _ hpos
    have h3 : ENNReal.ofReal (C * (ρ * lam ^ (k + N)))
        = ENNReal.ofReal (C * ρ * lam ^ N * lam ^ k) := by
      congr 1
      rw [pow_add]; ring
    exact le_trans (le_trans hle h2) (le_of_eq h3)
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  refine le_trans (ENNReal.tsum_le_tsum hstep) ?_
  have hsumm : Summable (fun k : ℕ => C * ρ * lam ^ N * lam ^ k) :=
    (summable_geometric_of_lt_one hlam0.le hlam1).mul_left _
  have htsum : (∑' k : ℕ, C * ρ * lam ^ N * lam ^ k) = C * ρ * lam ^ N / (1 - lam) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hlam0.le hlam1, div_eq_mul_inv]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsumm, htsum]

end Work.EKLC6Core
