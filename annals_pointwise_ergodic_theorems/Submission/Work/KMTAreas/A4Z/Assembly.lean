/-
# Theorem `improv`(ii): the final `ℓ¹`/`ℓ^∞` duality

This module contains the last step of the proof of Theorem `improv`(ii) of Krause--Mirek--Tao §5.2
in the form in which the workspace assembles it.  The analytic half of §5.2 (the chain
`lip-2` → `struct-dual` → `propdual-second` → `struct-iii-second` → `siv-second`) delivers, for
`f, g ∈ ℓ²(ℤ)` with `Π_{≤l,≤d(l-Log N)} g = 0` and on good major arcs, the *pairing* bound

  `|⟨Ã_N(f,g), φ⟩| ≤ C 2^{-cl} ‖f‖_{ℓ²} ‖g‖_{ℓ²}`

for every finitely supported `1`-bounded test function `φ`; the present file converts it into the
`ℓ¹` bound of Theorem `improv`(ii), using the elementary duality `(ℓ¹)' = ℓ^∞` on `(ℤ, count)`
(`eLpNorm_one_le_of_bilinPair_le`).

## Main results

* `eLpNorm_one_le_of_bilinPair_le` — the duality `(ℓ¹)' = ℓ^∞`;
* `improvTwoZ_of_pairingBound` — Theorem `improv`(ii) from the pairing bound.
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.Defs
import Submission.Work.KMTAreas.A5.eLpNorm_one_le_of_pairing_le
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.Analysis.InverseTheory
open Work.Analysis.EndVar

namespace Work.KMTAreas.A4Z

/-- **The duality `(ℓ¹)' = ℓ^∞` on `(ℤ, count)`.**  If the pairings of `X` against all
*finitely supported* `1`-bounded test functions are bounded by `C`, then `‖X‖_{ℓ¹} ≤ C`.

The test function `φ = conj (X ·) / ‖X ·‖` on a finite set `F` realises the whole mass of `X` on
`F` at once, so the supremum over finite sets `F` gives the `ℓ¹` norm. -/
theorem eLpNorm_one_le_of_bilinPair_le (X : ℤ → ℂ) (C : ℝ≥0∞)
    (h : ∀ φ : ℤ → ℂ, FinSupp φ → (∀ x : ℤ, ‖φ x‖ ≤ 1) → ‖bilinPair X φ‖ₑ ≤ C) :
    eLpNorm X 1 Measure.count ≤ C := by
  have hbound : ∀ F : Finset ℤ, ∑ x ∈ F, ENNReal.ofReal ‖X x‖ ≤ C := by
    intro F
    set φ : ℤ → ℂ := Work.KMTAreas.A5.kmtPhaseTest X F with hφdef
    have hle : ∀ x : ℤ, ‖φ x‖ ≤ 1 := fun x => by
      rw [hφdef]; exact Work.KMTAreas.A5.kmtPhaseTest_norm_le_one X F x
    have hfin : FinSupp φ := ⟨F, fun x hx => by
      rw [hφdef, Work.KMTAreas.A5.kmtPhaseTest]; exact if_neg hx⟩
    have hint : ENNReal.ofReal ‖bilinPair X φ‖ ≤ C := by
      rw [ofReal_norm]; exact h φ hfin hle
    have hpair : bilinPair X φ = ∑ x ∈ F, ((‖X x‖ : ℝ) : ℂ) := by
      have hzero : ∀ x : ℤ, x ∉ F → X x * φ x = 0 := by
        intro x hx
        rw [hφdef, Work.KMTAreas.A5.kmtPhaseTest, if_neg hx, mul_zero]
      rw [bilinPair, tsum_eq_sum hzero]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [hφdef, Work.KMTAreas.A5.kmtPhaseTest, if_pos hx]
      exact Work.KMTAreas.A5.kmtPhase_mul (X x)
    have hnorm : ENNReal.ofReal ‖∑ x ∈ F, ((‖X x‖ : ℝ) : ℂ)‖
        = ∑ x ∈ F, ENNReal.ofReal ‖X x‖ := by
      have h1 : ∑ x ∈ F, ((‖X x‖ : ℝ) : ℂ) = ((∑ x ∈ F, ‖X x‖ : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
      rw [h1, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun x _ => norm_nonneg _)]
      exact ENNReal.ofReal_sum_of_nonneg (fun x _ => norm_nonneg _)
    calc ∑ x ∈ F, ENNReal.ofReal ‖X x‖
        = ENNReal.ofReal ‖∑ x ∈ F, ((‖X x‖ : ℝ) : ℂ)‖ := hnorm.symm
      _ = ENNReal.ofReal ‖bilinPair X φ‖ := by rw [hpair]
      _ ≤ C := hint
  have hlin : eLpNorm X 1 Measure.count = ∑' x : ℤ, ENNReal.ofReal ‖X x‖ := by
    rw [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), lintegral_count]
    exact tsum_congr fun x => (ofReal_norm (X x)).symm
  rw [hlin, ENNReal.tsum_eq_iSup_sum]
  exact iSup_le hbound

/-- **Theorem `improv`(ii) from the pairing bound of §5.2.**  If for every `ρ ∈ (0,1]` there are
`Cρ > 0` and `C > 0` such that the pairings of `Ã_N(f,g)` against finitely supported `1`-bounded
test functions are bounded by `C 2^{-cl} ‖f‖_{ℓ²}‖g‖_{ℓ²}` whenever `(l, d(l-Log N))` has good
major arcs and `Π_{≤l,≤d(l-Log N)} g = 0`, then `Ã_N(f,g)` satisfies the `ℓ¹` estimate of
Theorem `improv`(ii). -/
theorem improvTwoZ_of_pairingBound (P : Polynomial ℤ) (c : ℝ) (hc : 0 < c)
    (hPair : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
      ∀ (N l : ℕ) (f g φ : ℤ → ℂ), 1 ≤ N →
        MemLp f 2 Measure.count → MemLp g 2 Measure.count → FinSupp φ →
        (∀ x : ℤ, ‖φ x‖ ≤ 1) →
        GoodMajorArcs ρ Cρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) →
        Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) g = 0 →
        ‖bilinPair (AhalfZ N P f g) φ‖ₑ ≤ ENNReal.ofReal (C : ℝ)
          * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))))
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count) :
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
      ∀ (N l : ℕ) (f g : ℤ → ℂ), 1 ≤ N →
        MemLp f 2 Measure.count → MemLp g 2 Measure.count →
        GoodMajorArcs ρ Cρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) →
        Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) g = 0 →
        eLpNorm (fun x : ℤ => AhalfZ N P f g x) 1 Measure.count
          ≤ ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))))
              * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
  intro ρ hρ0 hρ1
  obtain ⟨Cρ, hCρ, C, hC, hP⟩ := hPair ρ hρ0 hρ1
  refine ⟨Cρ, hCρ, C, hC, ?_⟩
  intro N l f g hN hf hg harc hproj
  exact eLpNorm_one_le_of_bilinPair_le _
    (ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))))
      * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count)
    (fun φ hfin h1 => hP N l f g φ hN hf hg hfin h1 harc hproj)

end Work.KMTAreas.A4Z
