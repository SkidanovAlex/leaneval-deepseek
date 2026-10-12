import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Analysis.BoseBand.OffdiagCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.Analysis.BoseBand.gapWord_fibre_offdiag`

**The off-diagonal fibre integral of FS `eq:DefT`'s second kinetic piece `gapWord` vanishes.**

For a slot `j` lying in two *different* joint sector sets `S ≠ T` of FS §6
(`E_S = jointProj ℓ S Φ`), the polarised combination of the large-box Neumann gap word of the
slot-`j` fibres of `E_SΦ ± E_TΦ` integrates to zero over the configuration box:

    ∫_{abox n ℓ} 1_{Λ(0)}(x_j) [ gapWord(fibre_j(E_SΦ+E_TΦ)(x)) − gapWord(fibre_j(E_SΦ−E_TΦ)(x)) ] dx = 0.

## The argument

`gapWord ℓ b 0 ψ = b ℓ⁻² ∫_{Λ(0)} (Q_0ψ)²` with `Q_0` the mean-free projection on `Λ(0) = acube ℓ`.
Since `j ∈ S ∩ T`, the slot-`j` fibres of `E_SΦ` and of `E_TΦ` have **zero mean** over `acube ℓ`
(`integral_fibre_jointProj_eq_zero`, the pointwise form of `P_j E_S = 0`), so `Q_0` is the
identity on them and the polarisation is the plain product:

    gapWord(fibre_j(A+B)(x)) − gapWord(fibre_j(A−B)(x)) = 4 b ℓ⁻² ∫_{acube ℓ} A(x_{j←z}) B(x_{j←z}) dz,

with `A = E_SΦ`, `B = E_TΦ`.  The remaining box integral is `peel_pair_abox`, which converts it
into `4 b ℓ⁻² ℓ³ ∫_{abox(m+1) ℓ} A·B`, and that vanishes because `E_S` and `E_T` are orthogonal
projections (`jointProj_orthogonal`): the two sectors differ in some slot.
-/

noncomputable section

open MeasureTheory

namespace Work.Analysis.BoseBand

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The fibre of a sum of states -/

/-- The slot-`j` fibre of a sum of two states is the sum of the fibres (pointwise). -/
lemma fibre_add_pi {N : ℕ} (j : Fin N) (A B : Submission.BoseGases.X N → ℝ)
    (x : Submission.BoseGases.X N) :
    Work.BoseKinLoc.fibre N j (A + B) x
      = fun z => Work.BoseKinLoc.fibre N j A x z + Work.BoseKinLoc.fibre N j B x z := rfl

/-- The slot-`j` fibre of a difference of two states is the difference of the fibres. -/
lemma fibre_sub_pi {N : ℕ} (j : Fin N) (A B : Submission.BoseGases.X N → ℝ)
    (x : Submission.BoseGases.X N) :
    Work.BoseKinLoc.fibre N j (A - B) x
      = fun z => Work.BoseKinLoc.fibre N j A x z - Work.BoseKinLoc.fibre N j B x z := rfl

/-! ## 2. The gap word of a mean-free state -/

/-- The mean-free projection `Q_0` is the identity on a state of vanishing `acube ℓ`-mean. -/
lemma Qfree_eq_self_of_integral_eq_zero {ℓ : ℝ} {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∫ z in Submission.BoseGases.acube ℓ, ψ z = 0) :
    Work.BoseKinLoc.Qfree ℓ 0 ψ = ψ := by
  funext z
  simp only [Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ, Work.BSKinetic.bsMean, smul_zero,
    zero_add]
  rw [h, mul_zero, sub_zero]

/-- On a mean-free state the bare gap form is the plain `L²`-mass. -/
lemma gapBare_eq_integral_sq_of_integral_eq_zero {ℓ : ℝ} {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∫ z in Submission.BoseGases.acube ℓ, ψ z = 0) :
    Work.BoseKinLoc.gapBare ℓ 0 ψ
      = ∫ z in Submission.BoseGases.acube ℓ, (ψ z) ^ 2 := by
  rw [Work.BoseKinLoc.gapBare, Qfree_eq_self_of_integral_eq_zero h,
    Work.Analysis.BoseBand.lamBox_zero_eq_acube]

/-- **The polarisation identity of the gap word** on mean-free states: the difference of the gap
words of `ψ₁ + ψ₂` and `ψ₁ − ψ₂` is four times the `L²`-pairing of `ψ₁` and `ψ₂`. -/
lemma gapWord_diff_eq {ℓ b : ℝ} (hℓ : 0 < ℓ) {fA fB : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hAc : Continuous fA) (hBc : Continuous fB)
    (hmA : ∫ z in Submission.BoseGases.acube ℓ, fA z = 0)
    (hmB : ∫ z in Submission.BoseGases.acube ℓ, fB z = 0) :
    Work.BoseKinLoc.gapWord ℓ b 0 (fun z => fA z + fB z)
      - Work.BoseKinLoc.gapWord ℓ b 0 (fun z => fA z - fB z)
      = (b * ℓ ^ (-2 : ℤ) * 4) * ∫ z in Submission.BoseGases.acube ℓ, fA z * fB z := by
  have hABm : ∫ z in Submission.BoseGases.acube ℓ, (fA z + fB z) = 0 := by
    rw [MeasureTheory.integral_add]
    · rw [hmA, hmB, add_zero]
    · exact ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
        hAc.continuousOn
    · exact ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
        hBc.continuousOn
  have hABsm : ∫ z in Submission.BoseGases.acube ℓ, (fA z - fB z) = 0 := by
    rw [MeasureTheory.integral_sub]
    · rw [hmA, hmB, sub_zero]
    · exact ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
        hAc.continuousOn
    · exact ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
        hBc.continuousOn
  have hsq : (∫ z in Submission.BoseGases.acube ℓ, (fA z + fB z) ^ 2)
      - (∫ z in Submission.BoseGases.acube ℓ, (fA z - fB z) ^ 2)
      = 4 * ∫ z in Submission.BoseGases.acube ℓ, fA z * fB z := by
    rw [← MeasureTheory.integral_sub]
    · rw [show (4 : ℝ) * ∫ z in Submission.BoseGases.acube ℓ, fA z * fB z
          = ∫ z in Submission.BoseGases.acube ℓ, 4 * (fA z * fB z) from
        (MeasureTheory.integral_const_mul 4 _).symm]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      ring
    · exact ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
        ((hAc.add hBc).pow 2).continuousOn
    · exact ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
        ((hAc.sub hBc).pow 2).continuousOn
  rw [Work.BoseKinLoc.gapWord, Work.BoseKinLoc.gapWord,
    gapBare_eq_integral_sq_of_integral_eq_zero hABm,
    gapBare_eq_integral_sq_of_integral_eq_zero hABsm]
  rw [show b * ℓ ^ (-2 : ℤ) * (∫ z in Submission.BoseGases.acube ℓ, (fA z + fB z) ^ 2)
        - b * ℓ ^ (-2 : ℤ) * (∫ z in Submission.BoseGases.acube ℓ, (fA z - fB z) ^ 2)
      = b * ℓ ^ (-2 : ℤ) * ((∫ z in Submission.BoseGases.acube ℓ, (fA z + fB z) ^ 2)
        - (∫ z in Submission.BoseGases.acube ℓ, (fA z - fB z) ^ 2)) from by ring]
  rw [hsq]
  ring

/-! ## 3. The off-diagonal vanishing -/

theorem gapWord_fibre_offdiag {ℓ b : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {S T : Finset ℕ} (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n)
    (hjS : (j : ℕ) ∈ S) (hjT : (j : ℕ) ∈ T) (hST : S ≠ T) :
    (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
      (Work.BoseKinLoc.gapWord ℓ b 0
          (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ
            + Work.BoseFixB2.jointProj ℓ T Φ) x)
       - Work.BoseKinLoc.gapWord ℓ b 0
          (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ
            - Work.BoseFixB2.jointProj ℓ T Φ) x))) = 0 := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ m =>
    set A : Submission.BoseGases.X (m + 1) → ℝ := Work.BoseFixB2.jointProj ℓ S Φ with hA
    set B : Submission.BoseGases.X (m + 1) → ℝ := Work.BoseFixB2.jointProj ℓ T Φ with hB
    have hAc : Continuous A := Work.BoseFixB2.Sector.jointProj_continuous hℓ S hΦ.continuous
    have hBc : Continuous B := Work.BoseFixB2.Sector.jointProj_continuous hℓ T hΦ.continuous
    have hmeanA : ∀ x : Submission.BoseGases.X (m + 1),
        ∫ z in Submission.BoseGases.acube ℓ, A (Function.update x j z) = 0 := by
      intro x
      simpa [hA] using integral_fibre_jointProj_eq_zero hℓ j hjS hΦ.continuous x
    have hmeanB : ∀ x : Submission.BoseGases.X (m + 1),
        ∫ z in Submission.BoseGases.acube ℓ, B (Function.update x j z) = 0 := by
      intro x
      simpa [hB] using integral_fibre_jointProj_eq_zero hℓ j hjT hΦ.continuous x
    have hST' : S ∩ Finset.range (m + 1) ≠ T ∩ Finset.range (m + 1) := by
      rw [Finset.inter_eq_left.mpr hS, Finset.inter_eq_left.mpr hT]
      exact hST
    have horth : (∫ x in Submission.BoseGases.abox (m + 1) ℓ, A x * B x) = 0 := by
      have := Work.BoseFixB2.Sector.jointProj_orthogonal hℓ hST' Φ Φ hΦ.continuous hΦ.continuous
      simpa [hA, hB] using this
    -- the indicator `1_{Λ(0)}(x_j)` is one on the configuration box
    rw [show (∫ x in Submission.BoseGases.abox (m + 1) ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
          (Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre (m + 1) j (A + B) x)
           - Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre (m + 1) j (A - B) x)))
        = ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
            (Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre (m + 1) j (A + B) x)
             - Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre (m + 1) j (A - B) x))
        from by
      refine MeasureTheory.setIntegral_congr_fun
        (Submission.BoseGases.abox_measurable (m + 1) ℓ) ?_
      intro x hx
      beta_reduce
      rw [indU_eq_one_of_mem_abox j hx, one_mul]]
    -- the pointwise polarisation of the gap word
    rw [show (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
            (Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre (m + 1) j (A + B) x)
             - Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre (m + 1) j (A - B) x)))
        = ∫ x in Submission.BoseGases.abox (m + 1) ℓ, (b * ℓ ^ (-2 : ℤ) * 4) *
            ∫ z in Submission.BoseGases.acube ℓ,
              A (Function.update x j z) * B (Function.update x j z)
        from by
      refine MeasureTheory.setIntegral_congr_fun
        (Submission.BoseGases.abox_measurable (m + 1) ℓ) ?_
      intro x hx
      beta_reduce
      rw [fibre_add_pi, fibre_sub_pi]
      exact gapWord_diff_eq hℓ (hAc.comp (by fun_prop)) (hBc.comp (by fun_prop))
        (hmeanA x) (hmeanB x)]
    rw [peel_pair_abox hℓ j hAc hBc (b * ℓ ^ (-2 : ℤ) * 4), horth]
    ring

end Work.Analysis.BoseBand
