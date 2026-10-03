import Mathlib
import Submission.Work.KMTAreas.A7Hi.LossWeightMono
import Submission.Work.KMTAreas.A7.eLpNorm_residueLp_le
import Submission.Work.KMTAreas.A7.mStargF_band
import Submission.Work.KMTAreas.A7.LoErrAux
import Submission.Commons.MeasureTheory.Lp.eLpNorm_tsum_le_tsum_eLpNorm
import Submission.Work.A7.exists_cw_mStargF_tsum_le
import Submission.Work.KMTAreas.A7.iwArithFreqs_card_le
import Submission.Work.KMTAreas.A7.toLp_tsum_pi
import Submission.Work.KMTAreas.A7.variationalNorm_mul_le
import Submission.Work.KMTAreas.A7Hi.eLpNormResidueLpEq

/-!
# The `g`-side finite-input fibre sampling estimate, from the `Vʳ`-valued narrow-bump fibre bound

This file reduces the target `Work.KMTAreas.A7Hi.FiberVarSamplingGLargeFinite` to the single
analytic input `fiberOpVarUniformLpNoLoss` (or any lemma of that shape): the `Vʳ`-valued `ℓᵖ` bound
for the fibre `fiberOp ρ l (mStarF u) n₀` of a *narrow* bump (`GoodMajorArcs ρ Cρ l (-(2u))`),
with a constant independent of `l, u, n₀`.  The reduction is the per-residue argument: apply the
fibre bound at the residue `n₀ = P.eval n₀` for each of the `q` residues, then use Minkowski over
the residue average (`A7.eLpNorm_residueLp_le`).  See
`NOTES_A7Hi_FiberVarSamplingGLargeFinite_SESSION2.md` for the route and its scope.
-/

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- `lmaxR l₁ l₂ k₁ k₂` *is* the scale `Lnat l₁ l₂ k₁ k₂`, as a real number. -/
theorem lmaxR_eq_Lnat (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ = (Work.KMTAreas.A7.Lnat l₁ l₂ k₁ k₂ : ℝ) := by
  unfold Work.KMTAreas.A7.lmaxR Work.KMTAreas.A7.Lnat Work.Analysis.EndVar.lmax
  push_cast
  ring

/-- The scale `uScale ρ L` is at least half of `2^{2ρL}`. -/
theorem le_two_mul_uScale (ρ : ℝ) (hρ : 0 ≤ ρ) (L : ℕ) :
    (2 : ℝ) ^ (2 * ρ * (L : ℝ)) / 2 ≤ (Work.KMTAreas.A7.uScale ρ L : ℝ) := by
  have hu : Work.KMTAreas.A7.uScale ρ L
      = ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋₊ := by
    simp only [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount, Int.floor_toNat,
      Nat.cast_one, one_mul]
  set x : ℝ := (2 : ℝ) ^ (2 * ρ * (L : ℝ)) with hx
  have hx1 : (1 : ℝ) ≤ x := Real.one_le_rpow (by norm_num) (by positivity)
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  rw [hu]
  rcases le_total x 2 with h2 | h2
  · have h3 : x / 2 ≤ 1 := by linarith
    have h4 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
      have : (1 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx1)
      exact_mod_cast this
    linarith
  · have h3 : x - 1 ≤ (⌊x⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one x
      linarith
    linarith

/-- **The Ionescu–Wainger narrowness of the concrete bump, for large `L`.**  For every `ρ ∈ (0,1]`,
every `d ≥ 1` and every `Cρ > 0` there is `B` such that for `L ≥ B` and `l₂ ≤ L`,

  `GoodMajorArcs ρ Cρ l₂ (-(2 * (d * uScale ρ L)))`,

i.e. `2 * (d * uScale ρ L) ≥ Cρ * 2^{ρ l₂}`. -/
theorem goodMajorArcs_mStargF (ρ : ℝ) (hρ : 0 < ρ) (d : ℕ) (hd : 1 ≤ d) (Cρ : ℝ)
    (hCρ : 0 < Cρ) :
    ∃ B : ℕ, ∀ (L l₂ : ℕ), l₂ ≤ L → B ≤ L →
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₂
        (-(2 * (((d * Work.KMTAreas.A7.uScale ρ L : ℕ) : ℤ)))) := by
  -- choose `B` with `1 ≤ B`, `1 ≤ ρ * B` and `logb 2 (Cρ/d) ≤ ρ * B`
  obtain ⟨B, hB⟩ : ∃ B : ℕ, 1 ≤ B ∧
      max (Real.logb 2 (Cρ / (d : ℝ))) 1 ≤ ρ * (B : ℝ) := by
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hpos : 0 < Cρ / (d : ℝ) := div_pos hCρ hdR
    obtain ⟨B, hB⟩ := exists_nat_ge (max (Real.logb 2 (Cρ / (d : ℝ))) 1 / ρ)
    refine ⟨max B 1, le_max_right B 1, ?_⟩
    have h1 : max (Real.logb 2 (Cρ / (d : ℝ))) 1 / ρ ≤ (max B 1 : ℕ) :=
      le_trans hB (by exact_mod_cast le_max_left B 1)
    have h2 : max (Real.logb 2 (Cρ / (d : ℝ))) 1 ≤ (max B 1 : ℕ) * ρ := by
      rw [div_le_iff₀ hρ] at h1
      linarith
    calc max (Real.logb 2 (Cρ / (d : ℝ))) 1 ≤ (max B 1 : ℕ) * ρ := h2
      _ = ρ * ((max B 1 : ℕ) : ℝ) := by ring
  refine ⟨B, ?_⟩
  intro L l₂ hl₂ hBL
  rw [Work.Analysis.IonescuWainger.GoodMajorArcs]
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hBR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB.1
  have hLBR : (B : ℝ) ≤ (L : ℝ) := by exact_mod_cast hBL
  have hl₂R : (l₂ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hl₂
  -- `Cρ ≤ d * 2^{ρB}`
  have hlog : Real.logb 2 (Cρ / (d : ℝ)) ≤ ρ * (B : ℝ) := le_trans (le_max_left _ _) hB.2
  have hpow : Cρ / (d : ℝ) ≤ (2 : ℝ) ^ (ρ * (B : ℝ)) := by
    have h1 : (2 : ℝ) ^ (Real.logb 2 (Cρ / (d : ℝ))) ≤ (2 : ℝ) ^ (ρ * (B : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
    rwa [Real.rpow_logb (by norm_num) (by norm_num) (div_pos hCρ hdR)] at h1
  have hB2 : Cρ ≤ (d : ℝ) * (2 : ℝ) ^ (ρ * (B : ℝ)) := by
    have := hpow
    rw [div_le_iff₀ hdR] at this
    linarith
  -- `2^{ρ l₂ + ρ B} ≤ 2^{2ρL}`
  have hkey : (2 : ℝ) ^ (ρ * (l₂ : ℝ) + ρ * (B : ℝ)) ≤ (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have g1 : ρ * (l₂ : ℝ) ≤ ρ * (L : ℝ) := mul_le_mul_of_nonneg_left hl₂R hρ.le
    have g2 : ρ * (B : ℝ) ≤ ρ * (L : ℝ) := mul_le_mul_of_nonneg_left hLBR hρ.le
    linarith
  have hfloor := le_two_mul_uScale ρ hρ.le L
  have hu0 : (0 : ℝ) < (Work.KMTAreas.A7.uScale ρ L : ℝ) := by
    have := Work.KMTAreas.A7.uScale_pos hρ.le L
    exact_mod_cast lt_of_lt_of_le zero_lt_one this
  have hmain : Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ))
      ≤ 2 * ((d : ℝ) * (Work.KMTAreas.A7.uScale ρ L : ℝ)) := by
    have h1 : Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ))
        ≤ ((d : ℝ) * (2 : ℝ) ^ (ρ * (B : ℝ))) * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) :=
      mul_le_mul_of_nonneg_right hB2 (Real.rpow_nonneg (by norm_num) _)
    have h2 : ((d : ℝ) * (2 : ℝ) ^ (ρ * (B : ℝ))) * (2 : ℝ) ^ (ρ * (l₂ : ℝ))
        = (d : ℝ) * (2 : ℝ) ^ (ρ * (l₂ : ℝ) + ρ * (B : ℝ)) := by
      rw [Real.rpow_add (by norm_num)]
      ring
    have h3 : (d : ℝ) * (2 : ℝ) ^ (ρ * (l₂ : ℝ) + ρ * (B : ℝ))
        ≤ (d : ℝ) * (2 * (Work.KMTAreas.A7.uScale ρ L : ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
      linarith [hkey, hfloor]
    calc Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ))
        ≤ (d : ℝ) * (2 : ℝ) ^ (ρ * (l₂ : ℝ) + ρ * (B : ℝ)) := by rw [← h2]; exact h1
      _ ≤ (d : ℝ) * (2 * (Work.KMTAreas.A7.uScale ρ L : ℝ)) := h3
      _ = 2 * ((d : ℝ) * (Work.KMTAreas.A7.uScale ρ L : ℝ)) := by ring
  have hcast : ((↑(-(2 * ((d * Work.KMTAreas.A7.uScale ρ L : ℕ) : ℤ))) : ℤ) : ℝ)
      = -(2 * ((d : ℝ) * (Work.KMTAreas.A7.uScale ρ L : ℝ))) := by push_cast; ring
  rw [hcast, show -Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) = -(Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ))) from by ring,
    neg_le_neg_iff]
  exact hmain

end

end Work.KMTAreas.A7Hi
