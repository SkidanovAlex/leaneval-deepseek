import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.PolarCoord

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Joint integrability of the two mollifier-convolution pairings

`integrable_conv_pair` is the measure-theoretic core of the `IP6`-transfer estimate for the
Friedrichs mollifier `J_ε` in the log coordinates: the mollifier is an even convolution over the
plane, so after the change of variables `(s,ζ) = (log z, log tan θ)` the level-`k` pairing is an
integral over `(y, p) ∈ (ℝ × ℝ)²` of

  `Q y * k p * G₁ (y - p) * G₂ y`   resp.   `Q y * k p * G₁ y * G₂ (y - p)`,

with `Q` the pulled-back weight (which is only *shift-bounded*,
`Q (y + p) ≤ exp (Cw * (|p.1| + |p.2|)) * Q y`, not bounded) and `k` the mollifier kernel, which is
nonnegative, integrable and supported in the box `|p.1| + |p.2| ≤ 2 ε`.

The proof is an AM–GM: `2 |G₁ (y - p)| |G₂ y| ≤ G₁ (y - p)² + G₂ y²`.  The two resulting pieces are

* `k p * (Q (y - p) * G₁ (y - p)²)` — integrable by the Mathlib convolution lemma
  `MeasureTheory.Integrable.convolution_integrand` (one factor shifted in the first variable),
* `k p * (Q y * G₂ y²)` — a product function, integrable by `Integrable.mul_prod` and `swap`.

The only point that needs the support of `k` is the comparison of the shift bound with a constant
factor: for `p` in the support, `exp (Cw * (|p.1| + |p.2|)) ≤ exp (2 * Cw * ε)`, which is what turns
`Q y ≤ exp (Cw * (|p.1| + |p.2|)) * Q (y - p)` into `Q y ≤ c * Q (y - p)` with `c` *independent*
of `p`; the pointwise bound `k p * f p ≤ c * k p ≤ …` is then a legitimate domination.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces

open MeasureTheory

/-- **The AM–GM pair bound.**  If `k` is nonnegative and supported in the box
`|p.1| + |p.2| ≤ 2 ε`, and the weight `Q ≥ 0` is shift-bounded with constant `Cw ≥ 0`, then the
product `Q y * k p * G (y - p) * H y` is dominated by

`(c/2) * (k p * (Q (y - p) * G (y - p)²)) + (c/2) * (k p * (Q y * H y²))`  with  `c = e^{2 Cw ε}`,

where the two summands are joint *product* functions (one factor shifted, one unshifted). -/
theorem integrable_shifted_pair {k Q G H : ℝ × ℝ → ℝ} {Cw ε : ℝ} (hCw : 0 ≤ Cw)
    (hk : MeasureTheory.Integrable k) (hk0 : ∀ p : ℝ × ℝ, 0 ≤ k p)
    (hksupp : ∀ p : ℝ × ℝ, k p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε)
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh : ∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y)
    (hGm : Measurable G) (hHm : Measurable H)
    (hGi : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G y ^ 2))
    (hHi : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * H y ^ 2)) :
    MeasureTheory.Integrable
      (Function.uncurry fun (y p : ℝ × ℝ) => Q y * k p * G (y - p) * H y) := by
  change MeasureTheory.Integrable
    (fun z : (ℝ × ℝ) × (ℝ × ℝ) => Q z.1 * k z.2 * G (z.1 - z.2) * H z.1) volume
  set c : ℝ := Real.exp (2 * Cw * ε) with hc
  -- the shift bound at `p` is at most the constant `c`, on the support of `k`
  have hc_le : ∀ p : ℝ × ℝ, k p ≠ 0 → Real.exp (Cw * (|p.1| + |p.2|)) ≤ c := by
    intro p hp
    rw [hc]
    apply Real.exp_le_exp.mpr
    have hle : |p.1| + |p.2| ≤ 2 * ε := hksupp p hp
    calc Cw * (|p.1| + |p.2|) ≤ Cw * (2 * ε) := mul_le_mul_of_nonneg_left hle hCw
      _ = 2 * Cw * ε := by ring
  -- on the support, the constant is `≥ 1` (so the unshifted summand is also dominated)
  have hc1 : ∀ p : ℝ × ℝ, k p ≠ 0 → 1 ≤ c := by
    intro p hp
    rw [hc, Real.one_le_exp_iff]
    have hle : |p.1| + |p.2| ≤ 2 * ε := hksupp p hp
    have hnn : (0 : ℝ) ≤ |p.1| + |p.2| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    calc (0 : ℝ) ≤ Cw * (2 * ε) := mul_nonneg hCw (le_trans hnn hle)
      _ = 2 * Cw * ε := by ring
  have hmeas : AEStronglyMeasurable
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => Q z.1 * k z.2 * G (z.1 - z.2) * H z.1)
      (volume.prod volume) :=
    (((hQm.comp measurable_fst).aestronglyMeasurable.mul
        hk.aestronglyMeasurable.comp_snd).mul
      (hGm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable).mul
      (hHm.comp measurable_fst).aestronglyMeasurable
  -- the shifted product is integrable by the convolution lemma for the two factors `k` and `Q G²`
  have hshift : MeasureTheory.Integrable
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => k z.2 * (Q (z.1 - z.2) * G (z.1 - z.2) ^ 2))
      (volume.prod volume) :=
    MeasureTheory.Integrable.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ)
      (μ := volume) (ν := volume) (f := k) (g := fun y : ℝ × ℝ => Q y * G y ^ 2) hk hGi
  -- the unshifted product is integrable by `mul_prod` and commutation of the two variables
  have hprod : MeasureTheory.Integrable
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => k z.2 * (Q z.1 * H z.1 ^ 2)) (volume.prod volume) :=
    (MeasureTheory.Integrable.mul_prod (μ := volume) (ν := volume) (f := k)
      (g := fun y : ℝ × ℝ => Q y * H y ^ 2) hk hHi).swap
  refine MeasureTheory.Integrable.mono'
    (g := fun z : (ℝ × ℝ) × (ℝ × ℝ) => c / 2 * (k z.2 * (Q (z.1 - z.2) * G (z.1 - z.2) ^ 2))
      + c / 2 * (k z.2 * (Q z.1 * H z.1 ^ 2))) ?_ hmeas ?_
  · exact (hshift.const_mul (c / 2)).add (hprod.const_mul (c / 2))
  · filter_upwards with z
    by_cases hp : k z.2 = 0
    · simp [hp]
    · have hB : 0 < k z.2 := lt_of_le_of_ne (hk0 z.2) (Ne.symm hp)
      have hA : 0 ≤ Q z.1 := hQ0 z.1
      have hAB : 0 ≤ Q z.1 * k z.2 := mul_nonneg hA hB.le
      have hQp : 0 ≤ Q (z.1 - z.2) := hQ0 _
      have hG2 : 0 ≤ G (z.1 - z.2) ^ 2 := sq_nonneg _
      have hH2 : 0 ≤ H z.1 ^ 2 := sq_nonneg _
      have hQle : Q z.1 ≤ c * Q (z.1 - z.2) := by
        have h := hQsh (z.1 - z.2) z.2
        rw [sub_add_cancel] at h
        exact le_trans h (mul_le_mul_of_nonneg_right (hc_le z.2 hp) hQp)
      have hAM : |G (z.1 - z.2)| * |H z.1| ≤ (G (z.1 - z.2) ^ 2 + H z.1 ^ 2) / 2 := by
        nlinarith [sq_nonneg (|G (z.1 - z.2)| - |H z.1|), sq_abs (G (z.1 - z.2)),
          sq_abs (H z.1), abs_nonneg (G (z.1 - z.2)), abs_nonneg (H z.1)]
      have hstep1 : Q z.1 * k z.2 * |G (z.1 - z.2)| * |H z.1|
          ≤ (Q z.1 * k z.2 * G (z.1 - z.2) ^ 2 + Q z.1 * k z.2 * H z.1 ^ 2) / 2 := by
        calc Q z.1 * k z.2 * |G (z.1 - z.2)| * |H z.1|
            = (Q z.1 * k z.2) * (|G (z.1 - z.2)| * |H z.1|) := by ring
          _ ≤ (Q z.1 * k z.2) * ((G (z.1 - z.2) ^ 2 + H z.1 ^ 2) / 2) :=
              mul_le_mul_of_nonneg_left hAM hAB
          _ = (Q z.1 * k z.2 * G (z.1 - z.2) ^ 2 + Q z.1 * k z.2 * H z.1 ^ 2) / 2 := by ring
      have hstep2 : Q z.1 * k z.2 * G (z.1 - z.2) ^ 2
          ≤ c * k z.2 * (Q (z.1 - z.2) * G (z.1 - z.2) ^ 2) := by
        calc Q z.1 * k z.2 * G (z.1 - z.2) ^ 2
            = Q z.1 * (k z.2 * G (z.1 - z.2) ^ 2) := by ring
          _ ≤ (c * Q (z.1 - z.2)) * (k z.2 * G (z.1 - z.2) ^ 2) :=
              mul_le_mul_of_nonneg_right hQle (mul_nonneg hB.le hG2)
          _ = c * k z.2 * (Q (z.1 - z.2) * G (z.1 - z.2) ^ 2) := by ring
      have hstep3 : Q z.1 * k z.2 * H z.1 ^ 2 ≤ c * k z.2 * (Q z.1 * H z.1 ^ 2) := by
        calc Q z.1 * k z.2 * H z.1 ^ 2 = 1 * (Q z.1 * k z.2 * H z.1 ^ 2) := by ring
          _ ≤ c * (Q z.1 * k z.2 * H z.1 ^ 2) :=
              mul_le_mul_of_nonneg_right (hc1 z.2 hp) (mul_nonneg hAB hH2)
          _ = c * k z.2 * (Q z.1 * H z.1 ^ 2) := by ring
      have hnorm : ‖Q z.1 * k z.2 * G (z.1 - z.2) * H z.1‖
          = Q z.1 * k z.2 * |G (z.1 - z.2)| * |H z.1| := by
        rw [Real.norm_eq_abs]
        simp only [abs_mul, abs_of_nonneg hA, abs_of_nonneg hB.le]
      rw [hnorm]
      linarith [hstep1, hstep2, hstep3]

theorem integrable_conv_pair {k Q G₁ G₂ : ℝ × ℝ → ℝ} {Cw ε : ℝ} (hCw : 0 ≤ Cw)
    (hk : MeasureTheory.Integrable k) (hk0 : ∀ p : ℝ × ℝ, 0 ≤ k p)
    (hksupp : ∀ p : ℝ × ℝ, k p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε)
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh : ∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y)
    (hG1m : Measurable G₁) (hG2m : Measurable G₂)
    (hI1 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y ^ 2))
    (hI2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₂ y ^ 2)) :
    MeasureTheory.Integrable (Function.uncurry fun (y p : ℝ × ℝ) => Q y * k p * G₁ (y - p) * G₂ y) ∧
      MeasureTheory.Integrable (Function.uncurry fun (y p : ℝ × ℝ) => Q y * k p * G₁ y * G₂ (y - p)) := by
  constructor
  · exact integrable_shifted_pair hCw hk hk0 hksupp hQ0 hQm hQsh hG1m hG2m hI1 hI2
  · -- the second pairing is the first one with the roles of `G₁` and `G₂` exchanged
    refine (integrable_shifted_pair (G := G₂) (H := G₁) hCw hk hk0 hksupp hQ0 hQm hQsh
      hG2m hG1m hI2 hI1).congr ?_
    filter_upwards with z
    simp only [Function.uncurry]
    ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces
