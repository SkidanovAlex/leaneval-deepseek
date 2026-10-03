import Mathlib
import Submission.Work.Normal.Basic

open scoped Topology

namespace Work.Transfer

/-- **Divergence destroys normality.**  Suppose a sequence of functions `V n` blows up in norm at a
point `c'`, while the normalized differences `(V n - h1)/(h2 - h1)` stay bounded at some point `c₀`.
Then the family of normalized differences is not normal on any set `U` containing both `c₀` and `c'`
(no regularity of `V`, `h1`, `h2` or openness of `U` is needed).

This is the "Montel hit" step of the transfer argument: an escaping orbit of the IFS at `c'`
cannot coexist with a bounded normalized value at `c₀` on a family that is normal. -/
theorem not_isNormalFamily_div {V : ℕ → ℂ → ℂ} {U : Set ℂ} {c₀ c' : ℂ} {h1 h2 : ℂ → ℂ}
    (hc₀ : c₀ ∈ U) (hc' : c' ∈ U)
    (hbdd : ∃ B : ℝ, ∀ n : ℕ, ‖(V n c₀ - h1 c₀) / (h2 c₀ - h1 c₀)‖ ≤ B)
    (hden' : h2 c' ≠ h1 c')
    (hesc : Filter.Tendsto (fun n : ℕ => ‖V n c'‖) Filter.atTop Filter.atTop) :
    ¬ Work.Normal.IsNormalFamily
      (Set.range fun n : ℕ => fun c : ℂ => (V n c - h1 c) / (h2 c - h1 c)) U := by
  intro hN
  obtain ⟨B, hB⟩ := hbdd
  obtain ⟨φ, hφ, ⟨g, hg⟩ | hg⟩ :=
    hN (fun n c => (V n c - h1 c) / (h2 c - h1 c)) (fun n => ⟨n, rfl⟩)
  · -- Case 1: a subsequence converges locally uniformly to a finite limit function `g`.
    -- Evaluating at `c'` gives boundedness of the subsequence of `V`, contradiction.
    have hpt : Filter.Tendsto (fun n : ℕ => (V (φ n) c' - h1 c') / (h2 c' - h1 c'))
        Filter.atTop (𝓝 (g c')) := hg.tendsto_at hc'
    have hnorm : Filter.Tendsto (fun n : ℕ => ‖(V (φ n) c' - h1 c') / (h2 c' - h1 c')‖)
        Filter.atTop (𝓝 ‖g c'‖) := hpt.norm
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        ‖(V (φ n) c' - h1 c') / (h2 c' - h1 c')‖ < ‖g c'‖ + 1 :=
      hnorm.eventually (isOpen_Iio.mem_nhds (lt_add_one _))
    have hd : h2 c' - h1 c' ≠ 0 := sub_ne_zero.mpr hden'
    set C : ℝ := (‖g c'‖ + 1) * ‖h2 c' - h1 c'‖ + ‖h1 c'‖ with hC
    have hev2 : ∀ᶠ n : ℕ in Filter.atTop, ‖V (φ n) c'‖ ≤ C := by
      filter_upwards [hev] with n hn
      have hV : V (φ n) c' =
          ((V (φ n) c' - h1 c') / (h2 c' - h1 c')) * (h2 c' - h1 c') + h1 c' := by
        rw [div_mul_cancel₀ _ hd]
        ring
      rw [hV, hC]
      calc ‖((V (φ n) c' - h1 c') / (h2 c' - h1 c')) * (h2 c' - h1 c') + h1 c'‖
          ≤ ‖((V (φ n) c' - h1 c') / (h2 c' - h1 c')) * (h2 c' - h1 c')‖ + ‖h1 c'‖ :=
            norm_add_le _ _
        _ = ‖(V (φ n) c' - h1 c') / (h2 c' - h1 c')‖ * ‖h2 c' - h1 c'‖ + ‖h1 c'‖ := by
              rw [norm_mul]
        _ ≤ (‖g c'‖ + 1) * ‖h2 c' - h1 c'‖ + ‖h1 c'‖ := by
              have hle := mul_le_mul_of_nonneg_right hn.le (norm_nonneg (h2 c' - h1 c'))
              linarith
    have hescφ : ∀ᶠ n : ℕ in Filter.atTop, C + 1 ≤ ‖V (φ n) c'‖ :=
      hφ.tendsto_atTop.eventually (hesc.eventually (Filter.eventually_ge_atTop (C + 1)))
    obtain ⟨n, hn1, hn2⟩ := (hev2.and hescφ).exists
    linarith
  · -- Case 2: a subsequence tends locally uniformly to `∞`, contradicting boundedness at `c₀`.
    obtain ⟨N, hN'⟩ := hg {c₀} (by simpa using hc₀) isCompact_singleton (B + 1)
    have h1' : B + 1 ≤ ‖(V (φ N) c₀ - h1 c₀) / (h2 c₀ - h1 c₀)‖ := hN' N le_rfl c₀ rfl
    have h2' := hB (φ N)
    linarith

end Work.Transfer
