/-
# The exact tiling of the periodized window symbols over the scale-`1/N` grid

For every `N ≥ 1` and every real `t`, the window symbols of scale `N` centred at the grid points
`j/N` (`j = 0, …, N-1`) sum to `1`:

`∑_{j<N} ∑_{n∈ℤ} arcChi (N * (t - j/N + n)) = 1`.

Indeed, writing `u = N t`, the term with indices `(j, n)` is `arcChi (u - (j - N n))`, and the map
`(j, n) ↦ j - N n` is a bijection `Fin N × ℤ → ℤ` (`Int.divModEquiv` composed with the negation on
the second factor), so the double sum is just the tiling sum `∑_{k∈ℤ} arcChi (u - k)`, which equals
`1` by the hypothesis `htile`.

This is the exact partition identity used in `Work.KMTAreas.A4.lip2ArcExtract`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2ArcDefs

open scoped BigOperators

namespace Work.KMTAreas.A4

theorem arcChiSumTiling (htile : ∀ u : ℝ, ∑' m : ℤ, Work.KMTAreas.A4.arcChi (u - (m : ℝ)) = 1) (N : ℕ) (hN : 1 ≤ N) (t : ℝ) : ∑ j ∈ Finset.range N, (∑' n : ℤ, Work.KMTAreas.A4.arcChi ((N : ℝ) * (t - (j : ℝ) / (N : ℝ) + (n : ℝ)))) = 1 := by
  -- The tiling sum `g k = arcChi (u - k)` at `u = N t`.
  set g : ℤ → ℂ := fun k => arcChi ((N : ℝ) * t - (k : ℝ)) with hgdef
  -- It is summable, since `htile` evaluates its sum to `1 ≠ 0`.
  have hg : Summable g := by
    by_contra h
    have h0 : ∑' k : ℤ, g k = 0 := tsum_eq_zero_of_not_summable h
    rw [hgdef] at h0
    rw [htile ((N : ℝ) * t)] at h0
    exact one_ne_zero h0
  -- The bijection `(j, n) ↦ n * N + j` from `Fin N × ℤ` to `ℤ`.
  set e : Fin N × ℤ ≃ ℤ :=
    (Equiv.prodComm (Fin N) ℤ).trans (@Int.divModEquiv N ⟨by omega⟩).symm with hedef
  have he : ∀ (j : Fin N) (n : ℤ), e (j, n) = n * (N : ℤ) + (j : ℤ) := by
    intro j n; simp [e]
  have hsum1 : ∑' k : ℤ, g k = 1 := by rw [hgdef]; exact htile ((N : ℝ) * t)
  have hE : ∑' p : Fin N × ℤ, g (e p) = 1 := by
    rw [Equiv.tsum_eq e g, hsum1]
  have hsummableE : Summable (fun p : Fin N × ℤ => g (e p)) := by
    have h := hg.comp_injective e.injective
    simpa only [Function.comp_def] using h
  have hprod : ∑' p : Fin N × ℤ, g (e p) = ∑' j : Fin N, ∑' n : ℤ, g (e (j, n)) :=
    hsummableE.tsum_prod
  -- For a fixed `j`, the inner sum `∑' n, arcChi (N * (t - j/N + n))` is the sum of
  -- `g (e (j, n))`: reindex `n ↦ -n` to match the shape `n * N + j`.
  have hstep (j : Fin N) :
      (∑' n : ℤ, arcChi ((N : ℝ) * (t - (j : ℝ) / (N : ℝ) + (n : ℝ))))
        = ∑' n : ℤ, g (e (j, n)) := by
    rw [← Equiv.tsum_eq (Equiv.neg ℤ)
      (fun n : ℤ => arcChi ((N : ℝ) * (t - (j : ℝ) / (N : ℝ) + (n : ℝ))))]
    refine tsum_congr fun n => ?_
    rw [hgdef, he j n, Equiv.neg_apply]
    congr 1
    push_cast
    field_simp
    ring
  have key : ∑ j : Fin N,
      (∑' n : ℤ, arcChi ((N : ℝ) * (t - ((j : ℕ) : ℝ) / (N : ℝ) + (n : ℝ)))) = 1 := by
    calc ∑ j : Fin N,
          (∑' n : ℤ, arcChi ((N : ℝ) * (t - ((j : ℕ) : ℝ) / (N : ℝ) + (n : ℝ))))
        = ∑ j : Fin N, (∑' n : ℤ, g (e (j, n))) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          exact hstep j
        _ = ∑' j : Fin N, (∑' n : ℤ, g (e (j, n))) := by rw [tsum_fintype]
        _ = ∑' p : Fin N × ℤ, g (e p) := hprod.symm
        _ = 1 := hE
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => ∑' n : ℤ, arcChi ((N : ℝ) * (t - (j : ℝ) / (N : ℝ) + (n : ℝ)))) N]
  exact key

end Work.KMTAreas.A4
