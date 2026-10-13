import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeDefs
import Submission.Work.FTS.StrongEps.EComparison.AngCutSupportFacts
import Submission.Work.FTS.StrongEps.EComparison.EFamAngularFacts
import Submission.Work.FTS.StrongEps.EComparison.Lzero1_mul_sub
import Submission.Work.FTS.StrongEps.EComparison.AngCutDerivFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `SlotsZeroCutoff` — the shrinking angular cut-off `angCut` and its `Lzero1`-commutator

`angCut n θ = smoothTransition (θ/δ_n - 1) · smoothTransition ((π/2 - θ)/δ_n - 1)` with
`δ_n = delta n = 1/(n+1)`.  This file collects the seven facts about it that the zero-mode
comparison argument needs:

1. `angCut n` is `C^k` for every `k`;
2. its topological support lies in `[δ_n, π/2 - δ_n]`;
3. for fixed interior `θ` it equals `1` eventually in `n`;
4. `0 ≤ angCut n ≤ 1`;
5. `δ_n > 0`;
6. `δ_n → 0`;
7. the commutator of `Lzero1 = -∂_θθ + ∂_θ(tan θ ·) - 6` with multiplication by `angCut n` is
   `O(1/δ_n)` **on the layer** where `angCut n` is not locally equal to `1`.

For (7): `Lzero1` is second order, so the product rule gives the exact identity
`Lzero1 (χ·e) θ - χ θ·Lzero1 e θ = -e θ·χ''(θ) + (tan θ·e θ - 2 e'(θ))·χ'(θ)`
(`EComparison.Lzero1_mul_sub`, with `χ = angCut n`, `e = eFam m`).  Since `χ` is locally `1` on
`[2δ_n, π/2 - 2δ_n]` both of its derivatives vanish there, while on the layer
`layer n = (0, 2δ_n) ∪ (π/2 - 2δ_n, π/2)` the eigenfunction `e = eFam m` vanishes at the two
endpoints of the interval: `|e θ| ≤ 2L δ_n` there, the factor `δ_n` absorbing the `1/δ_n^2` of
`χ''` (`AngCutDerivFacts`, `EFamAngularFacts`).  This is exactly why the layer has width `2δ_n`
and not less.  The two auxiliary families of facts are proved in the sibling files
`AngCutSupportFacts.lean` / `AngCutDerivFacts.lean` / `EFamAngularFacts.lean` /
`Lzero1_mul_sub.lean`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.PhiStar.Gegenbauer (eFam)

namespace Work.FTS.StrongEps.EComparison

theorem SlotsZeroCutoff (m : ℕ) :
    (∀ n k : ℕ, ContDiff ℝ k (Work.FTS.StrongEps.EComparison.angCut n)) ∧
    (∀ n : ℕ, tsupport (Work.FTS.StrongEps.EComparison.angCut n)
        ⊆ Set.Icc (Work.FTS.StrongEps.EComparison.delta n)
            (Real.pi / 2 - Work.FTS.StrongEps.EComparison.delta n)) ∧
    (∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      ∀ᶠ n in Filter.atTop, Work.FTS.StrongEps.EComparison.angCut n θ = 1) ∧
    (∀ n : ℕ, ∀ θ : ℝ, 0 ≤ Work.FTS.StrongEps.EComparison.angCut n θ
        ∧ Work.FTS.StrongEps.EComparison.angCut n θ ≤ 1) ∧
    (∀ n : ℕ, 0 < Work.FTS.StrongEps.EComparison.delta n) ∧
    Filter.Tendsto Work.FTS.StrongEps.EComparison.delta Filter.atTop (nhds 0) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.FTS.EllipticEst.Lzero1 (fun t => Work.FTS.StrongEps.EComparison.angCut n t
          * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ
        - Work.FTS.StrongEps.EComparison.angCut n θ
          * Work.FTS.EllipticEst.Lzero1 (Work.FTS.PhiStar.Gegenbauer.eFam m) θ|
        ≤ C / Work.FTS.StrongEps.EComparison.delta n
            * Work.FTS.StrongEps.EComparison.layerInd n θ) := by
  obtain ⟨hsup, hev, hda, hdda, hl1, hl0⟩ := AngCutSupportFacts
  obtain ⟨hde, hdde, L, M, B, hL, hM, hB, he1, he2, he3, he4⟩ := EFamAngularFacts m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) smoothness
    intro n k
    have hδ : delta n ≠ 0 := (delta_pos n).ne'
    have h1 : ContDiff ℝ k (fun θ : ℝ => θ / delta n - 1) := by fun_prop
    have h2 : ContDiff ℝ k (fun θ : ℝ => (Real.pi / 2 - θ) / delta n - 1) := by fun_prop
    exact (Real.smoothTransition.contDiff.comp h1).mul
      (Real.smoothTransition.contDiff.comp h2)
  · exact hsup
  · exact hev
  · -- (4) the pointwise bounds
    intro n θ
    constructor
    · simp only [angCut]
      exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
    · have h := mul_le_mul (Real.smoothTransition.le_one (θ / delta n - 1))
        (Real.smoothTransition.le_one ((Real.pi / 2 - θ) / delta n - 1))
        (Real.smoothTransition.nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simpa [angCut] using h
  · exact delta_pos
  · exact delta_tendsto_zero
  · -- (7) the commutator estimate
    obtain ⟨-, -, -, -, K, hKpos, hK⟩ := AngCutDerivFacts
    refine ⟨2 * L * K + (B + 2 * M) * K, ?_, ?_⟩
    · have h1 : 0 < 2 * L * K := mul_pos (mul_pos (by norm_num) hL) hKpos
      have h2 : 0 ≤ (B + 2 * M) * K := mul_nonneg (by linarith) hKpos.le
      linarith
    · intro n θ hθ0 hθπ
      obtain ⟨hχ1, hχ2, hχ0, hχ0'⟩ := hK n θ
      have hδpos : 0 < delta n := delta_pos n
      have hmemI : θ ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_of_lt hθ0, le_of_lt hθπ⟩
      have hmemIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθπ⟩
      have hcos : Real.cos θ ≠ 0 :=
        (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθπ⟩).ne'
      have hcomm := Lzero1_mul_sub (angCut n) (eFam m) θ hcos (hda n) (hdda n) hde hdde
      by_cases hmem : θ ∈ Set.Icc (2 * delta n) (Real.pi / 2 - 2 * delta n)
      · -- on the middle interval both derivatives of the cut-off vanish
        have hz1 := hχ0 hmem
        have hz2 := hχ0' hmem
        have hz3 : θ ∉ layer n := by
          rw [layer, Set.mem_union]
          rintro (h | h)
          · exact absurd hmem.1 (not_le.mpr h.2)
          · exact absurd hmem.2 (not_le.mpr h.1)
        have hzero : Work.FTS.EllipticEst.Lzero1 (fun t => angCut n t * eFam m t) θ
            - angCut n θ * Work.FTS.EllipticEst.Lzero1 (eFam m) θ = 0 := by
          rw [hcomm]
          simp [hz1, hz2]
        rw [hzero, hl0 n θ hz3, mul_zero]
        simp
      · -- on the layer, `|e|` is `O(δ_n)` and `|tan θ · e|` is bounded
        have hlay : θ ∈ layer n := by
          rw [layer, Set.mem_union]
          rcases lt_or_ge θ (2 * delta n) with h | h
          · exact Or.inl ⟨hθ0, h⟩
          · refine Or.inr ⟨lt_of_not_ge ?_, hθπ⟩
            intro hle
            exact hmem ⟨h, hle⟩
        have he2L : |eFam m θ| ≤ 2 * L * delta n := by
          have hl : θ ∈ Set.Ioo 0 (2 * delta n)
              ∪ Set.Ioo (Real.pi / 2 - 2 * delta n) (Real.pi / 2) := by
            rw [← layer]; exact hlay
          rcases hl with h | h
          · calc |eFam m θ| ≤ L * θ := he1 θ hmemI
              _ ≤ L * (2 * delta n) := by nlinarith [hL.le, h.2.le]
              _ = 2 * L * delta n := by ring
          · calc |eFam m θ| ≤ L * (Real.pi / 2 - θ) := he2 θ hmemI
              _ ≤ L * (2 * delta n) := by nlinarith [hL.le, sub_lt_iff_lt_add.mp h.1]
              _ = 2 * L * delta n := by ring
        have hkey : |Work.FTS.EllipticEst.Lzero1 (fun t => angCut n t * eFam m t) θ
            - angCut n θ * Work.FTS.EllipticEst.Lzero1 (eFam m) θ|
            ≤ (2 * L * K + (B + 2 * M) * K) / delta n := by
          rw [hcomm]
          have h1 : |eFam m θ| * |deriv (deriv (angCut n)) θ| ≤ 2 * L * K / delta n := by
            have h := mul_le_mul he2L hχ2 (abs_nonneg _)
              (mul_nonneg (mul_nonneg (by norm_num) hL.le) hδpos.le)
            refine h.trans_eq ?_
            field_simp
          have h2 : (|Real.tan θ * eFam m θ| + 2 * |deriv (eFam m) θ|) * |deriv (angCut n) θ|
              ≤ (B + 2 * M) * (K / delta n) := by
            refine mul_le_mul ?_ hχ1 (abs_nonneg _) (by linarith)
            have h4 := he4 θ hmemIoo
            have h3 := he3 θ hmemI
            linarith
          have h3 : |-eFam m θ * deriv (deriv (angCut n)) θ
              + (Real.tan θ * eFam m θ - 2 * deriv (eFam m) θ) * deriv (angCut n) θ|
              ≤ |eFam m θ| * |deriv (deriv (angCut n)) θ|
                + (|Real.tan θ * eFam m θ| + 2 * |deriv (eFam m) θ|)
                  * |deriv (angCut n) θ| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_neg, abs_mul]
            refine add_le_add le_rfl ?_
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            have hsub := abs_sub_le (Real.tan θ * eFam m θ) 0 (2 * deriv (eFam m) θ)
            rw [sub_zero, zero_sub, abs_neg, abs_mul] at hsub
            simpa using hsub
          calc |-eFam m θ * deriv (deriv (angCut n)) θ
                + (Real.tan θ * eFam m θ - 2 * deriv (eFam m) θ) * deriv (angCut n) θ|
              ≤ |eFam m θ| * |deriv (deriv (angCut n)) θ|
                + (|Real.tan θ * eFam m θ| + 2 * |deriv (eFam m) θ|)
                  * |deriv (angCut n) θ| := h3
            _ ≤ 2 * L * K / delta n + (B + 2 * M) * (K / delta n) := add_le_add h1 h2
            _ = (2 * L * K + (B + 2 * M) * K) / delta n := by field_simp
        rw [hl1 n θ hlay, mul_one]
        exact hkey

end Work.FTS.StrongEps.EComparison
