import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.K1dirBDefs
import Submission.Work.BoseBoxFock.L1Tails.latCoulomb_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1dirB.coulTail_le` — the lattice-Coulomb tail vanishes at large momentum

The uniform lattice-Coulomb bound `Work.BoseBoxFock.L1Tails.latCoulomb_le` says that for a weight
`W ≥ 0` supported in `ball 0 (ℓ/4)` with finite Coulomb energy,

    ℓ⁻³ Σ_{n ∈ S} ‖Ŵ(κ_n)‖²/‖κ_n‖² ≤ C₀ ∬ W(x)W(y)/‖x−y‖ =: K

for *every* finite set `S` of nonzero lattice labels.  Consequently the supremum `M` of the finite
partial sums of the series `a_n := ‖Ŵ(κ_n)‖²/‖κ_n‖²` is finite, and by definition of the supremum
there is a finite set `G` of lattice labels whose partial sum is within `ε ℓ³` of `M`.  Taking
`Λ = 1 + Σ_{m ∈ G} ‖κ_m‖ > 0`, every lattice label of momentum at least `Λ` lies outside `G`, so
the partial sum over any finite set of such labels is at most `M − Σ_{m∈G} a_m < ε ℓ³`, which is
exactly the statement after multiplying by `ℓ⁻³`.

No regularity of `W` beyond the integrability hypotheses is used: the whole content is the uniform
bound of `latCoulomb_le` plus the elementary supremum argument.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.K1dirB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The zero lattice label carries the zero momentum. -/
private lemma kmomInt_apply_zero (ℓ : ℝ) : Work.BoseBoxFock.kmomInt ℓ 0 = 0 := by
  rw [Work.BoseBoxFock.kmomInt]
  have h : Work.BoseB4.vec (0 : Fin 3 → ℤ) = 0 := by
    ext i; simp [Work.BoseB4.vec]
  rw [h, smul_zero]

theorem coulTail_le {ℓ : ℝ} (hℓ : 0 < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W)
    (hW0 : ∀ᵐ x, 0 ≤ W x) (hWs : ∀ x, ℓ / 4 ≤ ‖x‖ → W x = 0)
    (hJ : MeasureTheory.Integrable (Work.BoseBoxFock.coulInt W)) :
    ∀ ε : ℝ, 0 < ε → ∃ Λ : ℝ, 0 < Λ ∧ ∀ S : Finset (Fin 3 → ℤ),
      (∀ n ∈ S, Λ ≤ ‖Work.BoseBoxFock.kmomInt ℓ n‖) →
      (ℓ ^ 3)⁻¹ * ∑ n ∈ S, ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
        (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2 / ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2 ≤ ε := by
  obtain ⟨C₀, _hC₀nn, hC₀⟩ := Work.BoseBoxFock.L1Tails.latCoulomb_le
  intro ε hε
  set a : (Fin 3 → ℤ) → ℝ := fun n =>
    ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ)) (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2
      / ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2 with ha
  -- the uniform bound on the partial sums
  have hbound : ∀ S : Finset (Fin 3 → ℤ), (0 : Fin 3 → ℤ) ∉ S →
      ∑ n ∈ S, a n ≤ ℓ ^ 3 * (C₀ * ∫ p, Work.BoseBoxFock.coulInt W p) := by
    intro S hS
    have h := hC₀ hℓ hW hW0 hWs hJ S hS
    have hsum : (∑ n ∈ S, a n) = ∑ n ∈ S,
        ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
          (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2 / ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2 := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [ha]
    rw [hsum]
    have hpos : (0 : ℝ) < ℓ ^ 3 := by positivity
    calc ∑ n ∈ S, ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
            (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2 / ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2
        = ℓ ^ 3 * ((ℓ ^ 3)⁻¹ * ∑ n ∈ S, ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
            (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2 / ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
      _ ≤ ℓ ^ 3 * (C₀ * ∫ p, Work.BoseBoxFock.coulInt W p) :=
          mul_le_mul_of_nonneg_left h hpos.le
  -- the supremum of the partial sums
  set P : Set ℝ :=
    {x | ∃ S : Finset (Fin 3 → ℤ), (0 : Fin 3 → ℤ) ∉ S ∧ ∑ n ∈ S, a n = x} with hPdef
  have hPne : P.Nonempty := ⟨0, ∅, by simp, by simp⟩
  have hPbdd : BddAbove P := by
    refine ⟨ℓ ^ 3 * (C₀ * ∫ p, Work.BoseBoxFock.coulInt W p), ?_⟩
    rintro x ⟨S, hS, rfl⟩
    exact hbound S hS
  have hεℓ : (0 : ℝ) < ε * ℓ ^ 3 := mul_pos hε (by positivity)
  obtain ⟨x, ⟨G, hG0, hGx⟩, hxlt⟩ :=
    (lt_csSup_iff hPbdd hPne).mp (sub_lt_self (sSup P) hεℓ)
  -- the explicit threshold
  refine ⟨1 + ∑ n ∈ G, ‖Work.BoseBoxFock.kmomInt ℓ n‖, ?_, ?_⟩
  · have h := Finset.sum_nonneg (s := G) (f := fun n => ‖Work.BoseBoxFock.kmomInt ℓ n‖)
      (fun n _ => norm_nonneg _)
    linarith
  intro S hS
  have hposG : (0 : ℝ) < 1 + ∑ n ∈ G, ‖Work.BoseBoxFock.kmomInt ℓ n‖ := by
    have h := Finset.sum_nonneg (s := G) (f := fun n => ‖Work.BoseBoxFock.kmomInt ℓ n‖)
      (fun n _ => norm_nonneg _)
    linarith
  have hS0 : (0 : Fin 3 → ℤ) ∉ S := by
    intro h0
    have h := hS 0 h0
    rw [kmomInt_apply_zero ℓ, norm_zero] at h
    linarith
  have hmem : ∀ n ∈ G, ‖Work.BoseBoxFock.kmomInt ℓ n‖
      < 1 + ∑ m ∈ G, ‖Work.BoseBoxFock.kmomInt ℓ m‖ := by
    intro n hn
    have h := Finset.single_le_sum
      (f := fun m => ‖Work.BoseBoxFock.kmomInt ℓ m‖) (fun m _ => norm_nonneg _) hn
    linarith
  have hdisj : Disjoint S G := by
    rw [Finset.disjoint_left]
    intro n hnS hnG
    have h1 := hS n hnS
    have h2 := hmem n hnG
    linarith
  have hmemP : ∑ n ∈ S ∪ G, a n ≤ sSup P :=
    le_csSup hPbdd ⟨S ∪ G, by simp [hS0, hG0], rfl⟩
  have hlt' : ∑ n ∈ S, a n < ε * ℓ ^ 3 := by
    rw [Finset.sum_union hdisj] at hmemP
    linarith
  have hgoal : (ℓ ^ 3)⁻¹ * ∑ n ∈ S, a n ≤ ε := by
    calc (ℓ ^ 3)⁻¹ * ∑ n ∈ S, a n
        ≤ (ℓ ^ 3)⁻¹ * (ε * ℓ ^ 3) := mul_le_mul_of_nonneg_left hlt'.le (by positivity)
      _ = ε := by
          rw [mul_comm ε (ℓ ^ 3), ← mul_assoc, inv_mul_cancel₀ (by positivity : ℓ ^ 3 ≠ 0),
            one_mul]
  exact hgoal

end Work.BoseBoxFock.K1dirB
