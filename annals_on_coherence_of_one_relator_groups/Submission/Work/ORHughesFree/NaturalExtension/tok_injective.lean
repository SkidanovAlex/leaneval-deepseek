import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.SeriesP
import Submission.Work.ORHughesFree.NaturalExtension.rk_toeplitzSeries_ge_of_leading_general
import Submission.Work.ORHughesFree.NaturalExtension.blim_le_of_eventually_le
import Submission.Work.ORHughesFree.NaturalExtension.blim_of_tendsto
import Submission.Work.ORHughesFree.NaturalExtension.blim_mono
import Submission.Work.ORHughesFree.SkewLaurentSeries.exists_least_nonzero_coeff
import Submission.Work.ORHughesFree.NaturalExtension.blimRank_toeplitzT
import Submission.Work.ORHughesFree.RankAPI.rk_le_left
import Submission.Work.ORHughesFree.NaturalExtension.blim_ge_of_eventually_ge_tendsto
import Submission.Work.ORHughesFree.NaturalExtension.tendsto_leadingRatio
import Submission.Work.ORHughesFree.NaturalExtension.eventually_leading_le_toeplitz

namespace Work.ORHughesFree.NaturalExtension

/-- **[JZLA20, (4)]**: the Toeplitz family of a skew Laurent series is injective modulo the
rank-zero ideal of `P^U_{ω,τ}`.  If `p ≠ 0`, let `i` be the least index with `p.1 i ≠ 0`
(`SkewLaurentSeries.exists_least_nonzero_coeff`); then
`rk (toeplitzSeries N p) ≥ (N - max i (-i)) · rk (p.1 i)` for all `N > max i (-i)`
(`rk_toeplitzSeries_ge_of_leading_general`), and `rk (p.1 i) > 0` because `rk` is faithful, whence
`rk_ω (mkSP ω rk (tok p)) = blim ω (fun n => rk (toeplitzSeries (n+1) p)/(n+1)) ≥ rk (p.1 i) > 0`
(the sequence `n ↦ rk (toeplitzSeries (n+1) p)/(n+1)` dominates, eventually,
`(n+1 - max i (-i))/(n+1) · rk (p.1 i)`, which tends to `rk (p.1 i)`); so
`mkSP ω rk (tok p) ≠ 0` because `x ∈ SPideal ω rk ↔ rkAmp ω rk (oneByOne x) = 0`
(`mem_SPideal`, `rkAmp_apply`, `blimRank_oneByOne`). -/
theorem tok_injective {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.atTop) (rk : Work.ORHughesFree.SylvesterRank U)
    (hfaith : rk.IsFaithful)
    (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) U),
      rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A)
    (p : Work.ORHughesFree.SkewLaurentSeries U) (hp : p ≠ 0) :
    Work.ORHughesFree.NaturalExtension.mkSP ω rk
      (Work.ORHughesFree.NaturalExtension.tok p) ≠ 0 := by
  classical
  -- The least index carrying a non-zero coefficient of `p`, and that coefficient `a`.
  obtain ⟨i, hi0, hlo⟩ := Work.ORHughesFree.SkewLaurentSeries.exists_least_nonzero_coeff p hp
  set a : U := p.1 i with ha
  have ha_ne : a ≠ 0 := hi0
  set y : ℝ := rk.rk 1 1 (Work.ORHughesFree.oneByOne a) with hy
  -- `y > 0` because `rk` is faithful.
  have hy_pos : 0 < y := by
    rcases lt_or_eq_of_le (rk.rk_nonneg 1 1 (Work.ORHughesFree.oneByOne a)) with h | h
    · simpa [hy] using h
    · exact absurd (hfaith a (by simpa [hy] using h.symm)) ha_ne
  -- The normalized rank sequence of the Toeplitz matrices of `p`, and the comparison sequence.
  let f : ℕ → ℝ := fun n => rk.rk (n+1) (n+1)
      (Work.ORHughesFree.NaturalExtension.toeplitzSeries (n+1) p) / ((n+1 : ℕ) : ℝ)
  let g : ℕ → ℝ := fun n =>
      ((((n+1 : ℤ) - max i (-i) : ℤ) : ℝ) / ((n+1 : ℕ) : ℝ)) * y
  -- `f` is bounded by `1`, since the rank of an `(n+1) × (n+1)` matrix is at most `n + 1`.
  have hf_bdd : ∀ n, |f n| ≤ 1 := by
    intro n
    have hNpos : (0:ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
    have h1 : 0 ≤ f n := div_nonneg (rk.rk_nonneg _ _ _) (Nat.cast_nonneg _)
    have h2 : f n ≤ 1 := by
      rw [div_le_one hNpos]
      exact Work.ORHughesFree.RankAPI.rk_le_left rk _
    rw [abs_of_nonneg h1]
    exact h2
  -- `g` tends to `y` and is bounded.
  have hL2 := Work.ORHughesFree.NaturalExtension.tendsto_leadingRatio (max i (-i)) y
  have hg_tendsto : Filter.Tendsto g Filter.atTop (nhds y) := hL2.1
  have hg_bdd : ∀ n, |g n| ≤ (1 + |((max i (-i) : ℤ) : ℝ)|) * |y| := hL2.2
  -- `f` eventually dominates `g`: this is the rank lower bound for the Toeplitz matrix of `p`
  -- with its leading coefficient in degree `i`, normalized.
  have hev : ∀ᶠ n : ℕ in Filter.atTop, g n ≤ f n :=
    Work.ORHughesFree.NaturalExtension.eventually_leading_le_toeplitz rk hτ p i a ha.symm hlo
  have hblow : y ≤ blim ω f :=
    Work.ORHughesFree.NaturalExtension.blim_ge_of_eventually_ge_tendsto (f := f) (g := g) (y := y)
      ω hω hf_bdd hg_bdd hg_tendsto hev
  -- `blim ω f` is the rank of `oneByOne (tok p)` under `rkAmp ω rk`.
  have hblim_eq : blim ω f = (rkAmp ω rk).rk 1 1 (oneByOne (tok p)) := by
    rw [rkAmp_apply, blimRank_oneByOne]
    rfl
  have hpos : (rkAmp ω rk).rk 1 1 (oneByOne (tok p)) ≠ 0 := by
    rw [← hblim_eq]
    exact ne_of_gt (lt_of_lt_of_le hy_pos hblow)
  -- An element with non-zero rank is not in the rank-zero ideal, hence is non-zero in the quotient.
  intro hz
  apply hpos
  rw [← (mem_SPideal ω rk (tok p))]
  exact (Ideal.Quotient.eq_zero_iff_mem).mp hz

end Work.ORHughesFree.NaturalExtension
