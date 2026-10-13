import Mathlib
import Submission.Work.WilC4.pigeonhole_mono

namespace Work.WilC4

/-- Multiplicative pigeonhole on a segment, in the form needed by the Wilkie-conjecture argument.

Given `g` monotone (or antitone) on `[α,β]` with `0 < g t ≤ C`, an integer `m > 0` with
`C/m ≤ δ`, and `N > 0` with `N² ≤ (β/α)^(1/m)`, there is a point `y ∈ [α,β]` whose whole
multiplicative window `[y/N, N y]` lies in `[α,β]` and on which `g` stays within `δ` of `g y`.

This is a short consequence of `pigeonhole_mono`: the latter produces a subinterval
`[u,v] ⊆ [α,β]` with `v/u ≥ (β/α)^(1/m) ≥ N²` on which `g` is within `δ` of its value at the
geometric mean `√(u v)`; taking `y = √(u v)` one has `N² ≤ v/u`, i.e. `N u ≤ √(u v) ≤ v/N`,
so `[y/N, N y] = [√(u v)/N, N √(u v)] ⊆ [u,v]`. -/
theorem cbz_pigeonhole_segment {g : ℝ → ℝ} {α β C δ : ℝ} {m N : ℕ}
    (hα : 0 < α) (hαβ : α < β) (hC : 0 < C)
    (hmono : MonotoneOn g (Set.Icc α β) ∨ AntitoneOn g (Set.Icc α β))
    (hbd : ∀ t ∈ Set.Icc α β, 0 < g t ∧ g t ≤ C)
    (hm : 0 < m) (hδ : C / (m : ℝ) ≤ δ) (hN : 0 < N)
    (hwidth : (N : ℝ) ^ 2 ≤ (β / α) ^ ((1 : ℝ) / (m : ℝ))) :
    ∃ y : ℝ, α ≤ y ∧ y ≤ β ∧ ∀ s : ℝ, y / (N : ℝ) ≤ s → s ≤ (N : ℝ) * y →
      |g s - g y| ≤ δ := by
  obtain ⟨u, v, hαu, huv, hvβ, hratio, hg⟩ :=
    pigeonhole_mono hα hαβ hm hC hmono hbd hδ
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hu_pos : 0 < u := lt_of_lt_of_le hα hαu
  have huv_le : u ≤ v := le_of_lt huv
  have hv_pos : 0 < v := lt_of_lt_of_le hu_pos huv_le
  have huv_nonneg : 0 ≤ u * v := le_of_lt (mul_pos hu_pos hv_pos)
  -- `N² ≤ v/u`, i.e. `N² u ≤ v`, which is the whole content of the width hypothesis.
  have hratio' : (N : ℝ) ^ 2 ≤ v / u := le_trans hwidth hratio
  have hNu_le_v : (N : ℝ) ^ 2 * u ≤ v := (le_div_iff₀ hu_pos).mp hratio'
  -- `√(u v)` sits inside the `N`-scaled window of itself: `N u ≤ √(u v) ≤ v/N`.
  have hNu_nonneg : 0 ≤ (N : ℝ) * u := mul_nonneg hNpos.le hu_pos.le
  have hleft : u ≤ Real.sqrt (u * v) / (N : ℝ) := by
    rw [le_div_iff₀ hNpos, mul_comm u (N : ℝ)]
    calc (N : ℝ) * u = Real.sqrt (((N : ℝ) * u) ^ 2) := (Real.sqrt_sq hNu_nonneg).symm
      _ ≤ Real.sqrt (u * v) := by
          apply Real.sqrt_le_sqrt
          nlinarith [hNu_le_v, hu_pos]
  have hNy_nonneg : 0 ≤ (N : ℝ) * Real.sqrt (u * v) :=
    mul_nonneg hNpos.le (Real.sqrt_nonneg _)
  have hright : (N : ℝ) * Real.sqrt (u * v) ≤ v := by
    have hs : (Real.sqrt (u * v)) ^ 2 = u * v := Real.sq_sqrt huv_nonneg
    calc (N : ℝ) * Real.sqrt (u * v)
        = Real.sqrt (((N : ℝ) * Real.sqrt (u * v)) ^ 2) := (Real.sqrt_sq hNy_nonneg).symm
      _ ≤ Real.sqrt (v ^ 2) := by
          apply Real.sqrt_le_sqrt
          nlinarith [hs, hNu_le_v, hv_pos]
      _ = v := Real.sqrt_sq hv_pos.le
  refine ⟨Real.sqrt (u * v), ?_, ?_, ?_⟩
  · exact le_trans hαu (pm_sqrt_Icc hu_pos huv_le).1
  · exact le_trans (pm_sqrt_Icc hu_pos huv_le).2 hvβ
  · intro s hs1 hs2
    exact hg s ⟨le_trans hleft hs1, le_trans hs2 hright⟩

end Work.WilC4
