/-
# `Work.FIChain.lamPlusB_FIgtil_sieve` — the `β = 19` Fundamental-Lemma main term

The Rosser–Iwaniec upper-bound sieve at the Friedlander–Iwaniec density `g̃ = Submission.ASP.FIgtil`
and the level `D = Δ`, at the *long* delay `B = 19 = 9κ + 1` (`κ = 2`) and the sifting range
`z' = Δ^{1/19}`:

    Σ_{ν ≤ Δ, ♭} λ⁺_ν · (g̃ ν · h(ν))  ≤  K · ∏_{p < ⌈Δ^{1/19}⌉}(1 − g̃ p · h(p)),

with `λ⁺ = lamPlusB 19 Δ`, `h = hSieveC g̃ (1/log Δ)` and `K = (1 + K₁)·4·KFI` absolute.

The proof is the classical layer expansion of the Rosser–Iwaniec weight, at the layer range
`yFI Δ = ⌈Δ^{1/20}⌉₊ + 1` (`= Δ^{1/(B+1)}` up to rounding):

* `lamPlusB_sum_eq_GpB` — the support collapse: `λ⁺_ν ≠ 0` forces `ν | P(yFI Δ)` (each prime factor
  `p` satisfies `p^{20} ≤ Δ`), while conversely every divisor of `P(yFI Δ)` admissible for
  `rdPlusB 19 Δ` satisfies `d < Δ`; hence the Finset sum over `[1,Δ]` equals the divisor sum
  `GpB 19 (nuFI Δ) (yFI Δ) Δ`;
* `GpB_eq_VfB_add_oddLayers` — the Rosser–Iwaniec identity `GpB = VfB + OddLayerSum` for the
  multiplicative density `nuFI Δ = g̃ · h`;
* `oddLayerSum_nuFI_le` (below) — `OddLayerSum 19 ν_Δ (layerCut 19 Δ + 1) Δ yFI ≤ K₁·VfB ν_Δ yFI`,
  by summing the odd layers of the per-layer bound `TnB_FIgtil_perLayer` (`φ` odd-summable);
* `nuFI_VfB_le_zprime` — the `Ω₂` product comparison
  `VfB ν_Δ yFI ≤ 4·KFI·∏_{p < ⌈Δ^{1/19}⌉}(1 − ν_Δ p)`: in the trivial range (where
  `⌈Δ^{1/19}⌉ ≤ yFI`) the range `yFI` is a sub-product; otherwise `LinNormKup` of
  `nuFI_LinNormKup_aux` (from `sharpNorm_two_FIgtil`, `κ = 2`) gives the ratio
  `(log ⌈Δ^{1/19}⌉ / log yFI)² ≤ 4`, since `⌈Δ^{1/19}⌉ ≤ (⌈Δ^{1/20}⌉+1)²`.

The constant is `(1 + K₁)·(4·KFI)`.
-/
import Mathlib
import Submission.Work.FIChain.lamPlusBDefs
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.PerLayerDefs
import Submission.Work.FIChain.PerLayerAux
import Submission.Work.FIChain.TnB_FIgtil_perLayer
import Submission.Work.FIChain.GpB_eq_VfB_add_oddLayers
import Submission.Work.FIChain.sieveDens_mul_one_nonneg
import Submission.Work.FIChain.LamPlusBSieveAssembly
import Submission.Work.FIChain.nuFI_VfB_le_zprime
import Submission.Work.FIChain.lamPlusB_sum_eq_GpB

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The sieve density `nuFI Δ = g̃ · hSieveC g̃ (1/log Δ)`, unfolded. -/
lemma nuFI_apply (Δ n : ℕ) :
    nuFI Δ n = Submission.ASP.FIgtil n
      * hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) n := rfl

/-- The sieve density `nuFI Δ = g̃ · hSieveC g̃ (1/log Δ)` is at most `1` at every prime. -/
lemma nuFI_prime_le_one (Δ : ℕ) (hΔ : 3 ≤ Δ) (p : ℕ) (hp : p.Prime) : nuFI Δ p ≤ 1 :=
  le_trans (nuFI_le_half_of FIgtil_prime_le_third Δ hΔ p hp) (by norm_num)

/-- **The odd-layer sum of the `B = 19` weight is dominated by `VfB`**, uniformly in `Δ`: summing
the per-layer bound of `TnB_FIgtil_perLayer` over the odd indices below the truncation
`layerCut 19 Δ + 1`. -/
lemma oddLayerSum_nuFI_le :
    ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℕ, 3 ≤ Δ →
      OddLayerSum 19 (nuFI Δ) (layerCut 19 (Δ : ℝ) + 1) (Δ : ℝ) (yFI Δ)
        ≤ K * VfB (nuFI Δ) (yFI Δ) := by
  obtain ⟨φ, _hφnn, ⟨K₁, hK₁, hφsum⟩, hper⟩ := TnB_FIgtil_perLayer
  refine ⟨K₁, hK₁, fun Δ hΔ => ?_⟩
  have hV0 : 0 ≤ VfB (nuFI Δ) (yFI Δ) :=
    VfB_nonneg (ν := nuFI Δ) (fun p hp => nuFI_prime_le_one Δ hΔ p hp) (yFI Δ)
  have hstep : (∑ n ∈ (Finset.range (layerCut 19 (Δ : ℝ) + 1)).filter Odd,
        TnB 19 (nuFI Δ) n (Δ : ℝ) (yFI Δ))
      ≤ ∑ n ∈ (Finset.range (layerCut 19 (Δ : ℝ) + 1)).filter Odd,
          φ n * VfB (nuFI Δ) (yFI Δ) :=
    Finset.sum_le_sum (fun n hn => by
      exact hper Δ hΔ n (Finset.mem_filter.mp hn).2)
  rw [OddLayerSum]
  refine le_trans hstep ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (hφsum (layerCut 19 (Δ : ℝ) + 1)) hV0

theorem lamPlusB_FIgtil_sieve :
    ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℕ, 3 ≤ Δ →
      (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          Work.FIChain.lamPlusB 19 (Δ : ℝ) ν * (Submission.ASP.FIgtil ν
            * Work.FIChain.hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) ν))
        ≤ K * ∏ p ∈ Nat.primesBelow (⌈((Δ : ℝ) ^ ((1 : ℝ) / 19))⌉₊),
            (1 - Submission.ASP.FIgtil p
              * Work.FIChain.hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) p) := by
  obtain ⟨K₁, hK₁, hodd⟩ := oddLayerSum_nuFI_le
  refine ⟨(1 + K₁) * (4 * KFI), by have h := KFI_pos; nlinarith, fun Δ hΔ => ?_⟩
  have hν1 : nuFI Δ 1 = 1 := (sieveDens_mul_one_nonneg (1 / Real.log (Δ : ℝ))).1
  have hνmul : ∀ m n : ℕ, Nat.Coprime m n → nuFI Δ (m * n) = nuFI Δ m * nuFI Δ n :=
    (sieveDens_mul_one_nonneg (1 / Real.log (Δ : ℝ))).2.1
  have hsum : (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
        lamPlusB 19 (Δ : ℝ) ν * (Submission.ASP.FIgtil ν
          * hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) ν))
      = GpB 19 (nuFI Δ) (yFI Δ) (Δ : ℝ) := by
    simpa only [nuFI_apply] using lamPlusB_sum_eq_GpB Δ hΔ
  have hprod : VfB (nuFI Δ) (yFI Δ)
      ≤ (4 * KFI) * ∏ p ∈ Nat.primesBelow (⌈(Δ : ℝ) ^ ((1 : ℝ) / 19)⌉₊),
          (1 - Submission.ASP.FIgtil p
            * hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) p) := by
    simpa only [nuFI_apply] using nuFI_VfB_le_zprime Δ hΔ
  rw [hsum, GpB_eq_VfB_add_oddLayers 19 (by norm_num) (nuFI Δ) hν1 hνmul (Δ : ℝ) (yFI Δ)]
  have hmain : VfB (nuFI Δ) (yFI Δ)
        + OddLayerSum 19 (nuFI Δ) (layerCut 19 (Δ : ℝ) + 1) (Δ : ℝ) (yFI Δ)
      ≤ ((1 + K₁) * (4 * KFI))
        * ∏ p ∈ Nat.primesBelow (⌈(Δ : ℝ) ^ ((1 : ℝ) / 19)⌉₊),
            (1 - Submission.ASP.FIgtil p
              * hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) p) := by
    calc VfB (nuFI Δ) (yFI Δ)
          + OddLayerSum 19 (nuFI Δ) (layerCut 19 (Δ : ℝ) + 1) (Δ : ℝ) (yFI Δ)
        ≤ VfB (nuFI Δ) (yFI Δ) + K₁ * VfB (nuFI Δ) (yFI Δ) := by linarith [hodd Δ hΔ]
      _ = (1 + K₁) * VfB (nuFI Δ) (yFI Δ) := by ring
      _ ≤ (1 + K₁) * ((4 * KFI)
            * ∏ p ∈ Nat.primesBelow (⌈(Δ : ℝ) ^ ((1 : ℝ) / 19)⌉₊),
                (1 - Submission.ASP.FIgtil p
                  * hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) p)) :=
          mul_le_mul_of_nonneg_left hprod (by linarith)
      _ = ((1 + K₁) * (4 * KFI))
            * ∏ p ∈ Nat.primesBelow (⌈(Δ : ℝ) ^ ((1 : ℝ) / 19)⌉₊),
                (1 - Submission.ASP.FIgtil p
                  * hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) p) := by ring
  exact hmain

end

end Work.FIChain
