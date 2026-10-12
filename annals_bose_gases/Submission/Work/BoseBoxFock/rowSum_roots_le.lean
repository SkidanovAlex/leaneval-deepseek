import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairG_dir_leB
import Submission.Work.BoseBoxFock.pairRowS2Assemble
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.rowSum_roots_le` — the row-sum bound for the six fibre roots

The (S2) substitution estimates of `FINDING_PotPairRows_exists.md` §10 consume the *sum over the
pairs* of the six fibre roots
`√(pairEnergy ℓ 𝒢) + √(massBox ℓ 𝒢)` for `𝒢 = pairG13, pairG21, pairG23`.  The per-fibre bounds are
already on the disk (`pairG_dir_leB` for the Dirichlet energies, `pairRowS2Inst.pairG{13,21,23}_L2`
— with the support hypothesis supplied by `pairG_supports` — for the box masses); this module
performs the summation.

The two *budgets* of the bound are, with `pL = pinL2 l Θ₀`, `pD = pinDir l Θ₀`,
`A₂ = ∫‖A‖²`, `L₂ = ∫‖Θ‖²`:

* the **Dirichlet budget** `√C₀ · (cA² · (√pL · √(pD + pL)))`, obtained as the square root of
  `pairG_dir_leB`'s bound;
* the **mass budget** `A₂ · L₂`, obtained as the square root of `pairG{13,21,23}_L2`'s bound
  (whose square root is exactly `A₂ · L₂`, since the bound is a perfect square).

Each of the three fibres contributes both, so the per-pair cost is `3·(Dirichlet) + 3·(mass)`,
and the pair set has `card ≤ n·n` elements.  No sharpness is claimed; the point is that the whole
sum is controlled by the *state* quantities `pL, pD, L₂` and the one-particle content `A₂` of `A`.

`sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-- **Square root of the Dirichlet bound**: if the Dirichlet energy of a fibre is at most
`C·cA²·cA²·pL·(pD + pL)` with all factors nonnegative, then its square root is at most
`√C·(cA²·(√pL·√(pD + pL)))` — the square root of the equality
`(√C·(cA²·(√pL·√(pD+pL))))² = C·cA²·cA²·pL·(pD+pL)`. -/
private lemma sqrt_pairEnergy_le {ℓ : ℝ} {G : E3 → E3 → ℂ} {C cA pL pD : ℝ}
    (hC : 0 ≤ C) (_hcA : 0 ≤ cA) (hpL : 0 ≤ pL) (hpD : 0 ≤ pD)
    (h : L1Tails.pairEnergy ℓ G ≤ C * cA ^ 2 * cA ^ 2 * pL * (pD + pL)) :
    Real.sqrt (L1Tails.pairEnergy ℓ G)
      ≤ Real.sqrt C * (cA ^ 2 * (Real.sqrt pL * Real.sqrt (pD + pL))) := by
  have hpDpL : 0 ≤ pD + pL := by linarith
  set sc := Real.sqrt C * (cA ^ 2 * (Real.sqrt pL * Real.sqrt (pD + pL))) with hsc
  have hsc0 : 0 ≤ sc := by rw [hsc]; positivity
  have hsq : sc ^ 2 = C * cA ^ 2 * cA ^ 2 * pL * (pD + pL) := by
    rw [hsc, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hC, Real.sq_sqrt hpL, Real.sq_sqrt hpDpL]
    ring
  rw [Real.sqrt_le_left hsc0, hsq]
  exact h

/-- **Square root of the mass bound**: the box-mass bound of `pairRowS2Inst` is a perfect square, so
its square root is the product `A₂·L₂` of the two budgets. -/
private lemma sqrt_massBox_le {ℓ : ℝ} {G : E3 → E3 → ℂ} {A2 L2 : ℝ}
    (hA2 : 0 ≤ A2) (hL2 : 0 ≤ L2) (h : massBox ℓ G ≤ A2 * A2 * L2 ^ 2) :
    Real.sqrt (massBox ℓ G) ≤ A2 * L2 := by
  have h0 : 0 ≤ A2 * L2 := mul_nonneg hA2 hL2
  have hsq : (A2 * L2) ^ 2 = A2 * A2 * L2 ^ 2 := by ring
  rw [Real.sqrt_le_left h0, hsq]
  exact h

theorem rowSum_roots_le {n : ℕ} {l : ℝ} (hl : 0 < l)
    {Θ Θ₀ : Work.BoseDict.Xn n → ℂ} {A : EuclideanSpace ℝ (Fin 3) → ℂ} {cA : ℝ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n l)
    (hΘL : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn n => ‖Θ x‖ ^ 2))
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hΘind : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x)
    (hAm : Measurable A) (hAb : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C)
    (hAL : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ‖A x‖ ^ 2))
    (hcA : 0 ≤ cA) (hAc : ∀ x, ‖A x‖ ≤ cA) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∑ p ∈ Submission.BoseGases.pairSet n,
          ((Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy l (Work.BoseBoxFock.pairG13 p Θ A A))
              + Real.sqrt (Work.BoseBoxFock.massBox l (Work.BoseBoxFock.pairG13 p Θ A A)))
            + (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy l (Work.BoseBoxFock.pairG21 p Θ A))
              + Real.sqrt (Work.BoseBoxFock.massBox l (Work.BoseBoxFock.pairG21 p Θ A)))
            + (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy l (Work.BoseBoxFock.pairG23 p Θ A A))
              + Real.sqrt (Work.BoseBoxFock.massBox l (Work.BoseBoxFock.pairG23 p Θ A A))))
        ≤ C * (n : ℝ) * (n : ℝ)
            * (cA ^ 2 * (Real.sqrt (Work.BoseBoxFock.pinL2 l Θ₀)
                  * Real.sqrt (Work.BoseBoxFock.pinDir l Θ₀ + Work.BoseBoxFock.pinL2 l Θ₀))
                + (∫ x : EuclideanSpace ℝ (Fin 3), ‖A x‖ ^ 2)
                  * (∫ x : Work.BoseDict.Xn n, ‖Θ x‖ ^ 2)) := by
  classical
  obtain ⟨C₀, hC₀, h13, h23, h21⟩ := pairG_dir_leB (n := n) hl
  have hΘm' : MeasureTheory.AEStronglyMeasurable Θ := hΘm.aestronglyMeasurable
  have hAm' : MeasureTheory.AEStronglyMeasurable A := hAm.aestronglyMeasurable
  have hpL2 : 0 ≤ pinL2 l Θ₀ := integral_nonneg fun x => by positivity
  have hpD2 : 0 ≤ pinDir l Θ₀ := integral_nonneg fun x => by positivity
  have hA2 : 0 ≤ ∫ x : E3, ‖A x‖ ^ 2 := integral_nonneg fun x => by positivity
  have hL2 : 0 ≤ ∫ x : Xn n, ‖Θ x‖ ^ 2 := integral_nonneg fun x => by positivity
  refine ⟨3 * (Real.sqrt C₀ + 1), by positivity, ?_⟩
  set X := cA ^ 2 * (Real.sqrt (pinL2 l Θ₀) * Real.sqrt (pinDir l Θ₀ + pinL2 l Θ₀)) with hX
  set Y := (∫ x : E3, ‖A x‖ ^ 2) * (∫ x : Xn n, ‖Θ x‖ ^ 2) with hY
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hbudget : 3 * (Real.sqrt C₀ * X) + 3 * Y ≤ (3 * (Real.sqrt C₀ + 1)) * (X + Y) := by
    nlinarith [hX0, hY0, Real.sqrt_nonneg C₀]
  have key : ∀ p ∈ Submission.BoseGases.pairSet n,
      ((Real.sqrt (L1Tails.pairEnergy l (pairG13 p Θ A A))
          + Real.sqrt (massBox l (pairG13 p Θ A A)))
        + (Real.sqrt (L1Tails.pairEnergy l (pairG21 p Θ A))
          + Real.sqrt (massBox l (pairG21 p Θ A)))
        + (Real.sqrt (L1Tails.pairEnergy l (pairG23 p Θ A A))
          + Real.sqrt (massBox l (pairG23 p Θ A A))))
      ≤ 3 * (Real.sqrt C₀ * X) + 3 * Y := by
    intro p hp
    have hpne : p.1 ≠ p.2 := by simpa [Submission.BoseGases.pairSet] using hp
    obtain ⟨hsup13, hsup23, hsup21⟩ := pairG_supports p hpne hΘs
    have hPE13 : L1Tails.pairEnergy l (pairG13 p Θ A A)
        ≤ C₀ * cA ^ 2 * cA ^ 2 * pinL2 l Θ₀ * (pinDir l Θ₀ + pinL2 l Θ₀) :=
      h13 p hpne hΘ₀ hΘind hAm hAm hAc hAc hcA hcA
    have hPE23 : L1Tails.pairEnergy l (pairG23 p Θ A A)
        ≤ C₀ * cA ^ 2 * cA ^ 2 * pinL2 l Θ₀ * (pinDir l Θ₀ + pinL2 l Θ₀) :=
      h23 p hpne hΘ₀ hΘind hAm hAm hAc hAc hcA hcA
    have hPE21 : L1Tails.pairEnergy l (pairG21 p Θ A)
        ≤ C₀ * cA ^ 2 * cA ^ 2 * pinL2 l Θ₀ * (pinDir l Θ₀ + pinL2 l Θ₀) := by
      have h := h21 p hpne hΘ₀ hΘind hAm hAc hcA
      have he : C₀ * cA ^ 4 * pinL2 l Θ₀ * (pinDir l Θ₀ + pinL2 l Θ₀)
          = C₀ * cA ^ 2 * cA ^ 2 * pinL2 l Θ₀ * (pinDir l Θ₀ + pinL2 l Θ₀) := by ring
      rw [he] at h
      exact h
    have hM13 : massBox l (pairG13 p Θ A A)
        ≤ ((∫ x : E3, ‖A x‖ ^ 2) * (∫ x : E3, ‖A x‖ ^ 2))
            * (∫ x : Xn n, ‖Θ x‖ ^ 2) ^ 2 := by
      have h := pairG13_L2 p hpne hsup13 hΘm' hΘL hAm' hAL hAm' hAL
      simpa only [massBox] using h
    have hM23 : massBox l (pairG23 p Θ A A)
        ≤ ((∫ x : E3, ‖A x‖ ^ 2) * (∫ x : E3, ‖A x‖ ^ 2))
            * (∫ x : Xn n, ‖Θ x‖ ^ 2) ^ 2 := by
      have h := pairG23_L2 p hpne hsup23 hΘm' hΘL hAm' hAL hAm' hAL
      simpa only [massBox] using h
    have hM21 : massBox l (pairG21 p Θ A)
        ≤ ((∫ x : E3, ‖A x‖ ^ 2) * (∫ x : E3, ‖A x‖ ^ 2))
            * (∫ x : Xn n, ‖Θ x‖ ^ 2) ^ 2 := by
      have h := pairG21_L2 p hpne hsup21 hΘm' hΘL hAm' hAL
      have he : (∫ x : E3, ‖A x‖ ^ 2) ^ 2 * (∫ x : Xn n, ‖Θ x‖ ^ 2) ^ 2
          = ((∫ x : E3, ‖A x‖ ^ 2) * (∫ x : E3, ‖A x‖ ^ 2))
              * (∫ x : Xn n, ‖Θ x‖ ^ 2) ^ 2 := by ring
      rw [he] at h
      simpa only [massBox] using h
    have hs13 : Real.sqrt (L1Tails.pairEnergy l (pairG13 p Θ A A)) ≤ Real.sqrt C₀ * X := by
      simpa only [hX] using sqrt_pairEnergy_le hC₀ hcA hpL2 hpD2 hPE13
    have hs23 : Real.sqrt (L1Tails.pairEnergy l (pairG23 p Θ A A)) ≤ Real.sqrt C₀ * X := by
      simpa only [hX] using sqrt_pairEnergy_le hC₀ hcA hpL2 hpD2 hPE23
    have hs21 : Real.sqrt (L1Tails.pairEnergy l (pairG21 p Θ A)) ≤ Real.sqrt C₀ * X := by
      simpa only [hX] using sqrt_pairEnergy_le hC₀ hcA hpL2 hpD2 hPE21
    have hm13 : Real.sqrt (massBox l (pairG13 p Θ A A)) ≤ Y := by
      simpa only [hY] using sqrt_massBox_le hA2 hL2 hM13
    have hm23 : Real.sqrt (massBox l (pairG23 p Θ A A)) ≤ Y := by
      simpa only [hY] using sqrt_massBox_le hA2 hL2 hM23
    have hm21 : Real.sqrt (massBox l (pairG21 p Θ A)) ≤ Y := by
      simpa only [hY] using sqrt_massBox_le hA2 hL2 hM21
    linarith [hs13, hs23, hs21, hm13, hm23, hm21]
  have hsum_le :
      ∑ p ∈ Submission.BoseGases.pairSet n,
          ((Real.sqrt (L1Tails.pairEnergy l (pairG13 p Θ A A))
              + Real.sqrt (massBox l (pairG13 p Θ A A)))
            + (Real.sqrt (L1Tails.pairEnergy l (pairG21 p Θ A))
              + Real.sqrt (massBox l (pairG21 p Θ A)))
            + (Real.sqrt (L1Tails.pairEnergy l (pairG23 p Θ A A))
              + Real.sqrt (massBox l (pairG23 p Θ A A))))
        ≤ ∑ _p ∈ Submission.BoseGases.pairSet n, (3 * (Real.sqrt C₀ * X) + 3 * Y) :=
    Finset.sum_le_sum key
  have hsum_const : ∑ _p ∈ Submission.BoseGases.pairSet n, (3 * (Real.sqrt C₀ * X) + 3 * Y)
      = ((Submission.BoseGases.pairSet n).card : ℝ) * (3 * (Real.sqrt C₀ * X) + 3 * Y) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hterm0 : 0 ≤ 3 * (Real.sqrt C₀ * X) + 3 * Y := by positivity
  have hcard : ((Submission.BoseGases.pairSet n).card : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
    have h : (Submission.BoseGases.pairSet n).card ≤ n * n := by
      calc (Submission.BoseGases.pairSet n).card
          ≤ (Finset.univ : Finset (Fin n × Fin n)).card := Finset.card_le_univ _
        _ = n * n := by simp [Fintype.card_prod, Fintype.card_fin]
    exact_mod_cast h
  calc ∑ p ∈ Submission.BoseGases.pairSet n,
          ((Real.sqrt (L1Tails.pairEnergy l (pairG13 p Θ A A))
              + Real.sqrt (massBox l (pairG13 p Θ A A)))
            + (Real.sqrt (L1Tails.pairEnergy l (pairG21 p Θ A))
              + Real.sqrt (massBox l (pairG21 p Θ A)))
            + (Real.sqrt (L1Tails.pairEnergy l (pairG23 p Θ A A))
              + Real.sqrt (massBox l (pairG23 p Θ A A))))
      ≤ ((Submission.BoseGases.pairSet n).card : ℝ) * (3 * (Real.sqrt C₀ * X) + 3 * Y) := by
        rw [hsum_const] at hsum_le
        exact hsum_le
    _ ≤ ((n : ℝ) * (n : ℝ)) * (3 * (Real.sqrt C₀ * X) + 3 * Y) :=
        mul_le_mul_of_nonneg_right hcard hterm0
    _ ≤ ((n : ℝ) * (n : ℝ)) * ((3 * (Real.sqrt C₀ + 1)) * (X + Y)) :=
        mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = 3 * (Real.sqrt C₀ + 1) * (n : ℝ) * (n : ℝ) * (X + Y) := by ring

end Work.BoseBoxFock
