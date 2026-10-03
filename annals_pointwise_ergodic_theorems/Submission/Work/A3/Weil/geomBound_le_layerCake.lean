import Mathlib
import Submission.Work.A3.Weil.Defs

/-!
# The layer-cake bound for `geomBound`

`geomBound N x = 1 / max (intDist x) (1/N) = min (N, 1/intDist x)` is at most `2 + 2·C`, where

`C = #{k ∈ [1,N] : intDist x ≤ 1/(2k)}`

counts the integers `k ≤ N` whose reciprocal `1/(2k)` still exceeds `intDist x`.  This is the
elementary observation that `min (N, 1/d) ≤ 2 + 2·min (N, ⌊1/(2d)⌋)`: the loss of a factor `2`
(and the additive `2`) is the price of replacing `1/d` by the number of `k` with `1/(2k) ≥ d`.

The proof is by contradiction and avoids floors: if `2 + 2·C < geomBound N x` then
`2 + 2·C < N` and `intDist x < 1/(2 + 2C)`, so every `k ∈ [1, C+1]` (and there are `C+1` of them,
all `≤ N`) satisfies `intDist x ≤ 1/(2k)`, i.e. lies in the counted set — contradicting that the
set has `C` elements.
-/

namespace Work.A3.Weil

theorem geomBound_le_layerCake {N : ℕ} (hN : 1 ≤ N) (x : ℝ) :
    Work.A3.Weil.geomBound N x ≤ 2 + 2 * (((Finset.Icc 1 N).filter (fun k : ℕ =>
      Submission.VanDerCorput.intDist x ≤ 1 / (2 * (k : ℝ)))).card : ℝ) := by
  classical
  set C : ℕ := ((Finset.Icc 1 N).filter (fun k : ℕ =>
      Submission.VanDerCorput.intDist x ≤ 1 / (2 * (k : ℝ)))).card with hC
  set d : ℝ := Submission.VanDerCorput.intDist x with hd
  by_contra hcon
  rw [not_le] at hcon
  rw [geomBound, ← hd] at hcon
  have hpos2 : (0 : ℝ) < 2 + 2 * (C : ℝ) := by positivity
  have hMpos : 0 < max d ((N : ℝ)⁻¹) :=
    inv_pos.mp (lt_of_lt_of_le hpos2 hcon.le)
  have hltM : max d ((N : ℝ)⁻¹) < 1 / (2 + 2 * (C : ℝ)) := by
    rw [one_div, lt_inv_comm₀ hMpos hpos2]
    exact hcon
  have hdlt : d < 1 / (2 + 2 * (C : ℝ)) := lt_of_le_of_lt (le_max_left _ _) hltM
  have hNlt : (N : ℝ)⁻¹ < 1 / (2 + 2 * (C : ℝ)) :=
    lt_of_le_of_lt (le_max_right _ _) hltM
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have h2CN : 2 + 2 * (C : ℝ) < (N : ℝ) := by
    have h' : (N : ℝ)⁻¹ < (2 + 2 * (C : ℝ))⁻¹ := by rwa [one_div] at hNlt
    exact (inv_lt_inv₀ hNpos hpos2).mp h'
  have hCN : C + 1 ≤ N := by
    have hlt : 2 * C + 2 < N := by
      have : ((2 * C + 2 : ℕ) : ℝ) < (N : ℝ) := by push_cast; linarith
      exact_mod_cast this
    omega
  have hsub : Finset.Icc 1 (C + 1) ⊆ (Finset.Icc 1 N).filter (fun k : ℕ =>
      Submission.VanDerCorput.intDist x ≤ 1 / (2 * (k : ℝ))) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_Icc]
      exact ⟨hk.1, le_trans hk.2 hCN⟩
    · rw [← hd]
      have hkR : (k : ℝ) ≤ (C : ℝ) + 1 := by
        have h1 : (k : ℝ) ≤ ((C + 1 : ℕ) : ℝ) := by exact_mod_cast hk.2
        push_cast at h1
        exact h1
      have hpos : 0 < 2 * (k : ℝ) := by
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
        linarith
      have hle : 1 / (2 + 2 * (C : ℝ)) ≤ 1 / (2 * (k : ℝ)) :=
        one_div_le_one_div_of_le hpos (by linarith)
      exact le_trans hdlt.le hle
  have hcard1 : (Finset.Icc 1 (C + 1)).card ≤
      ((Finset.Icc 1 N).filter (fun k : ℕ =>
        Submission.VanDerCorput.intDist x ≤ 1 / (2 * (k : ℝ)))).card :=
    Finset.card_le_card hsub
  have hcard2 : (Finset.Icc 1 (C + 1)).card = C + 1 := by
    rw [Nat.card_Icc]; omega
  omega

end Work.A3.Weil
