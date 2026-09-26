import Mathlib
import Submission.Work.Drive.Mono.Band.BandChartDefs

namespace Work.Drive.Mono.Band

/-- **The chart denominator is bounded below on a compact level set of the height.**  The set
`S = {p | heightV ψ v p = y.1 ∧ alphaV ψ v a₀ p = y.2 * betaV ψ v b₀ p}` is closed, so `S ∩ K` is
compact; if it is contained in the chart domain `{betaV ≠ 0}`, then the continuous nonvanishing
function `|betaV ψ v b₀ ·|` is bounded below by a positive constant there, and by the Archimedean
property we may take the constant of the form `n⁻¹` with `n ≥ 1`.

Route: the sets `{p | ((N : ℝ) + 1)⁻¹ < |betaV ψ v b₀ p|}` (`N : ℕ`) are open and cover `S ∩ K`
because `S ∩ K` misses `{betaV = 0}`; `hK.elim_finite_subcover` gives a finite subcover, and since
the sets are increasing the largest index works, giving the bound `m⁻¹` with
`m = (t.sup id) + 1 ≥ 1` (`inv_anti₀`). -/
theorem exists_betaBound_of_compact (ψ : Submission.Diffeo)
    (v a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) {y : ℝ × ℝ}
    (hC : ({p : ℝ × ℝ | Work.Drive.Mono.Band.heightV ψ v p = y.1 ∧
        Work.Drive.Mono.Band.alphaV ψ v a₀ p = y.2 * Work.Drive.Mono.Band.betaV ψ v b₀ p} ∩ K)
      ⊆ Work.Drive.Mono.Band.chartDomain ψ v b₀) :
    ∃ N : ℕ, 1 ≤ N ∧ ({p : ℝ × ℝ | Work.Drive.Mono.Band.heightV ψ v p = y.1 ∧
        Work.Drive.Mono.Band.alphaV ψ v a₀ p = y.2 * Work.Drive.Mono.Band.betaV ψ v b₀ p} ∩ K)
      ⊆ {p : ℝ × ℝ | (N : ℝ)⁻¹ ≤ |Work.Drive.Mono.Band.betaV ψ v b₀ p|} := by
  -- The level set of the height and of `alphaV = y.2 * betaV` is closed.
  have hSclosed : IsClosed ({p : ℝ × ℝ | heightV ψ v p = y.1 ∧
        alphaV ψ v a₀ p = y.2 * betaV ψ v b₀ p}) := by
    exact (isClosed_eq (contDiff_heightV ψ v).continuous continuous_const).inter
      (isClosed_eq (contDiff_alphaV ψ v a₀).continuous
        (continuous_const.mul (contDiff_betaV ψ v b₀).continuous))
  -- Hence `S ∩ K` is compact.
  have hcpt : IsCompact ({p : ℝ × ℝ | heightV ψ v p = y.1 ∧
        alphaV ψ v a₀ p = y.2 * betaV ψ v b₀ p} ∩ K) :=
    hK.of_isClosed_subset (hSclosed.inter hK.isClosed) Set.inter_subset_right
  have hcont : ContinuousOn (fun p => |betaV ψ v b₀ p|)
      ({p : ℝ × ℝ | heightV ψ v p = y.1 ∧
        alphaV ψ v a₀ p = y.2 * betaV ψ v b₀ p} ∩ K) :=
    ((contDiff_betaV ψ v b₀).continuous.abs).continuousOn
  rcases Set.eq_empty_or_nonempty ({p : ℝ × ℝ | heightV ψ v p = y.1 ∧
        alphaV ψ v a₀ p = y.2 * betaV ψ v b₀ p} ∩ K) with hemp | hne
  · -- The empty case is trivial.
    exact ⟨1, le_refl 1, by rw [hemp]; exact Set.empty_subset _⟩
  · -- `|betaV|` attains its minimum on the compact set.
    obtain ⟨x, hxmem, hxmin⟩ := hcpt.exists_isMinOn hne hcont
    have hxdom : x ∈ chartDomain ψ v b₀ := hC hxmem
    have hcpos : 0 < |betaV ψ v b₀ x| := abs_pos.mpr hxdom
    -- Archimedean: a natural number bounds the inverse of the minimum.
    obtain ⟨m, hm⟩ := exists_nat_ge (|betaV ψ v b₀ x|)⁻¹
    refine ⟨max m 1, le_max_right _ _, ?_⟩
    intro p hp
    have hle : |betaV ψ v b₀ x| ≤ |betaV ψ v b₀ p| := hxmin hp
    have hmle : (m : ℝ) ≤ (max m 1 : ℕ) := by exact_mod_cast Nat.le_max_left m 1
    have hcast : (0:ℝ) < (max m 1 : ℕ) := by
      have : 1 ≤ max m 1 := Nat.le_max_right m 1
      exact_mod_cast this
    have hinv : ((max m 1 : ℕ) : ℝ)⁻¹ ≤ |betaV ψ v b₀ x| := by
      have h : (|betaV ψ v b₀ x|)⁻¹ ≤ ((max m 1 : ℕ) : ℝ) := le_trans hm hmle
      have := (inv_le_inv₀ hcast (inv_pos.mpr hcpos)).mpr h
      simpa [inv_inv] using this
    exact le_trans hinv hle

end Work.Drive.Mono.Band
