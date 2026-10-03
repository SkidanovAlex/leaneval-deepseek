import Mathlib
import Submission.Work.F0Facts.Basic
import Submission.Work.F0Facts.FinvRegion
import Submission.Work.F0Facts.finv_mem_repelling
import Submission.Work.F0Facts.norm_finv_lt
import Submission.Work.F0Facts.w3_mem_repelling
import Submission.Work.F0Facts.continuousOn_finv_repelling

/-!
# Convergence of the explicit Step 0 inverse orbit

The backward branch `finv w = (-1 + √(1+4w))/2` of `f₀(z) = z + z²` is a parabolic germ at `0` with
`finv'(0) = 1`.  Its "repelling region"
`repelling = {w | 2 ≤ ‖1 + 4w‖ + re (1 + 4w)}`  (equivalently `re (√(1+4w)) ≥ 1`)
is invariant under `finv`, and on it — away from the fixed point `0` — `finv` strictly contracts in
modulus.  Since `ω = (-1+√3 i)/2` lies in `repelling`, the backward orbit `finv^[n] ω` stays in
`repelling`, its moduli strictly decrease, and a quantitative compactness argument (the pointwise
strict contraction has a positive minimum on each compact annulus `ε ≤ ‖w‖ ≤ ‖ω‖`) forces the limit
to be `0`.  Numerically `‖finv^[n] ω‖ · n → 1`; here only convergence is needed.
-/

namespace Work.F0Facts

open Filter Topology Set Metric
open scoped Topology

noncomputable section

/-- The explicit backward orbit of `ω` under the inverse branch `finv`. -/
def orbit (n : ℕ) : ℂ := finv^[n] w3

lemma orbit_succ (n : ℕ) : orbit (n + 1) = finv (orbit n) :=
  Function.iterate_succ_apply' finv n w3

lemma orbit_mem_repelling (n : ℕ) : orbit n ∈ repelling := by
  induction n with
  | zero => exact w3_mem_repelling
  | succ n ih => rw [orbit_succ]; exact finv_mem_repelling ih

lemma orbit_ne_zero (n : ℕ) : orbit n ≠ 0 := by
  induction n with
  | zero => simpa [orbit] using w3_ne_zero
  | succ n ih => rw [orbit_succ]; exact finv_ne_zero_iff.mpr ih

lemma norm_orbit_lt (n : ℕ) : ‖orbit (n + 1)‖ < ‖orbit n‖ := by
  rw [orbit_succ]
  exact norm_finv_lt (orbit_mem_repelling n) (orbit_ne_zero n)

lemma antitone_norm_orbit : Antitone (fun n => ‖orbit n‖) :=
  antitone_nat_of_succ_le fun n => le_of_lt (norm_orbit_lt n)

/-- Convergence of the explicit Step 0 inverse orbit: the backward iterates of
`ω = (-1+√3 i)/2` under the local inverse branch `finv w = (-1+√(1+4w))/2` of `f₀(z) = z + z²`
converge to `0`. -/
theorem finv_iterate_tendsto :
    Tendsto (fun n : ℕ => Work.F0Facts.finv^[n] Work.F0Facts.w3) atTop (𝓝 0) := by
  show Tendsto orbit atTop (𝓝 0)
  -- For every `ε > 0` the orbit is eventually of modulus `< ε`.
  have key : ∀ ε > 0, ∃ N, ∀ n ≥ N, ‖orbit n‖ < ε := by
    intro ε hε
    by_cases hlt : ∃ n, ‖orbit n‖ < ε
    · -- then all later terms are even smaller, by monotonicity
      obtain ⟨N, hN⟩ := hlt
      exact ⟨N, fun n hn => lt_of_le_of_lt (antitone_norm_orbit hn) hN⟩
    · -- otherwise the orbit stays in the compact annulus `ε ≤ ‖w‖ ≤ ‖ω‖`
      simp only [not_exists, not_lt] at hlt
      exfalso
      set M : ℝ := ‖orbit 0‖ with hM
      let K : Set ℂ := repelling ∩ Metric.closedBall 0 M ∩ {w : ℂ | ε ≤ ‖w‖}
      have hKsub : K ⊆ Metric.closedBall (0:ℂ) M := fun w hw => hw.1.2
      have hKclosed : IsClosed K := by
        refine (isClosed_repelling.inter Metric.isClosed_closedBall).inter ?_
        exact isClosed_le continuous_const (by fun_prop)
      have hKcpt : IsCompact K :=
        IsCompact.of_isClosed_subset (ProperSpace.isCompact_closedBall (0:ℂ) M) hKclosed hKsub
      have hmemR : ∀ w ∈ K, w ∈ repelling := fun w hw => hw.1.1
      have hmemB : ∀ w ∈ K, ‖w‖ ≤ M := fun w hw => by
        have h2 : w ∈ Metric.closedBall (0:ℂ) M := hw.1.2
        simpa [Metric.mem_closedBall, dist_eq_norm] using h2
      have hmemE : ∀ w ∈ K, ε ≤ ‖w‖ := fun w hw => hw.2
      have hKne : K.Nonempty :=
        ⟨orbit 0, ⟨⟨orbit_mem_repelling 0, by simp [hM]⟩, hlt 0⟩⟩
      have hcontFinv : ContinuousOn (fun w => finv w) K :=
        continuousOn_finv_repelling.mono hmemR
      have hne_w : ∀ w ∈ K, w ≠ 0 := fun w hw hw0 => by
        have h1 : ‖w‖ = 0 := by rw [hw0]; simp
        have h2 := hmemE w hw
        linarith
      have hne_finv : ∀ w ∈ K, finv w ≠ 0 := fun w hw => finv_ne_zero_iff.mpr (hne_w w hw)
      -- the gain `1/‖finv w‖ - 1/‖w‖` is continuous on `K`
      have hcont : ContinuousOn (fun w => 1/‖finv w‖ - 1/‖w‖) K := by
        refine ContinuousOn.sub ?_ ?_
        · exact continuousOn_const.div hcontFinv.norm
            (fun w hw => norm_ne_zero_iff.mpr (hne_finv w hw))
        · exact continuousOn_const.div continuous_norm.continuousOn
            (fun w hw => norm_ne_zero_iff.mpr (hne_w w hw))
      -- and strictly positive there
      have hgpos : ∀ w ∈ K, 0 < 1/‖finv w‖ - 1/‖w‖ := by
        intro w hw
        have hwR := hmemR w hw
        have hw0 := hne_w w hw
        have hlt' := norm_finv_lt hwR hw0
        have hp1 : 0 < ‖finv w‖ := norm_pos_iff.mpr (hne_finv w hw)
        have h : 1/‖w‖ < 1/‖finv w‖ := one_div_lt_one_div_of_lt hp1 hlt'
        linarith
      -- hence it has a positive minimum `δ` on `K`
      obtain ⟨w0, hw0K, hmin⟩ := hKcpt.exists_isMinOn hKne hcont
      set δ : ℝ := 1/‖finv w0‖ - 1/‖w0‖ with hδdef
      have hδpos : 0 < δ := hgpos w0 hw0K
      -- so `1/‖orbit n‖` grows by at least `δ` at every step
      have hmain : ∀ n, 1/‖orbit 0‖ + n * δ ≤ 1/‖orbit n‖ := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          have hmem : orbit n ∈ K :=
            ⟨⟨orbit_mem_repelling n, by simpa [hM] using antitone_norm_orbit (Nat.zero_le n)⟩,
              hlt n⟩
          have hgn : δ ≤ 1/‖finv (orbit n)‖ - 1/‖orbit n‖ := by
            simpa [hδdef] using hmin hmem
          rw [orbit_succ]
          have : (↑(n+1) : ℝ) * δ = ↑n * δ + δ := by push_cast; ring
          rw [this]
          linarith
      -- but `1/‖orbit n‖ ≤ 1/ε` throughout: contradiction
      have hub : ∀ n, 1/‖orbit n‖ ≤ 1/ε := fun n => one_div_le_one_div_of_le hε (hlt n)
      obtain ⟨n, hn⟩ := exists_nat_gt ((1/ε)/δ)
      have hn' : 1/ε < ↑n * δ := by
        have h := mul_lt_mul_of_pos_right hn hδpos
        rwa [div_mul_cancel₀ (1/ε) (ne_of_gt hδpos)] at h
      have h1 := hmain n
      have h2 := hub n
      have h3 : (0:ℝ) ≤ 1/‖orbit 0‖ := by positivity
      linarith
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := key ε hε
  exact ⟨N, fun n hn => by simpa [dist_eq_norm] using hN n hn⟩

end

end Work.F0Facts
