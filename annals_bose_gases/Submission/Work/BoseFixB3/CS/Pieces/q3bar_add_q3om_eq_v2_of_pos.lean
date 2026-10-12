import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Pieces.lowMult_add_of_pos
import Submission.Work.BoseFixB3.CS.Reduce
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.q3bar_add_q3om_eq_v2_of_pos`

**The sum-level decomposition of `q3barWord + q3omWord` with the hypothesis `0 < κ`.**

The sibling statement `Work.BoseFixB3.CS.Pieces.q3bar_add_q3om_eq_v2` is **false as
written**: it quantifies over `κ : ℝ` with no sign restriction, and for `κ ≤ 0` the
slot identity on which it rests,

  `highSlot_j (aP_i Φ) x = highSlot_j (aP_i (aQ_j Φ)) x + aP_j (aP_i Φ) x · leakFn (x j)`,

fails (although all four integrability hypotheses can hold, so that the integrals are
*honest*).  For `κ ≤ 0` the symbol `p ↦ f(‖p‖/κ)` equals `1`, so `lowMult` is the
"junk-valued" inverse Fourier transform of the box extension: it is the identity at a
point of continuity when `𝓕(1_{Λ}ψ) ∈ L¹` and `0` otherwise
(`CS.lowMult_eq_self_or_eq_zero_of_nonpos`), and in particular a non-zero **constant**
fibre is mapped to `0` (`CS.Pieces.lowMult_oneFn_eq_zero_of_nonpos`: `1_Λ` has a
non-`L¹` transform, `Conv.cubeIndicator_kinFT_not_integrable`).  The identity above then
fails precisely when the `aQ`-part of the fibre is honest and non-zero while the sum
with the (non-zero) constant `aP`-part is junk - e.g. `n = 2`, `Φ(x₀,x₁) = ψ(x₁)` with
`ψ` a bump supported inside `Λ` and `∫_Λ ψ ≠ 0`, and `ω(x) := ψ(x₁)`, `w1 ≡ 1`.

For `0 < κ` the symbol is compactly supported and `lowMult` is linear in the state
(`CS.Pieces.lowMult_add_of_pos`), which yields the slot identity, then the per-pair
identity of integrands, then - the integrability hypotheses `hI1`-`hI4` making all four
integrals honest - the claimed equality of sums.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators

namespace Work.BoseFixB3.CS.Pieces

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. The pointwise slot identity for `0 < κ` -/

/-- **`Q̄_{L,j}(P_iΦ) = Q̄_{L,j}(P_iQ_jΦ) + (P_jP_iΦ)·leakFn(x_j)`.**  For `0 < κ` the
low-momentum multiplier is additive in the state, so it may be applied to the two halves
of the fibre `fibre_j(P_iΦ) = fibre_j(P_iQ_jΦ) + P_jP_iΦ` separately; the second summand
is a *constant* (in the slot-`j` variable), so `lowMult` acts on it as multiplication by
`lowMult 1`, giving the leakage factor `1 − lowMult 1 = leakFn`. -/
theorem highSlot_aP_eq_of_pos (fc : LowCut) (κ ℓ : ℝ) (hκ : 0 < κ) (hℓ : 0 < ℓ)
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) (x : Submission.BoseGases.X n) :
    Work.BoseFixB3.highSlot fc κ ℓ j (aP ℓ i Φ) x
      = Work.BoseFixB3.highSlot fc κ ℓ j (aP ℓ i (aQ ℓ j Φ)) x
        + aP ℓ j (aP ℓ i Φ) x * Work.BoseFixB3.CS.leakFn fc κ ℓ (x j) := by
  have hQc : Continuous (aQ ℓ j Φ) := aQ_continuous hℓ j hΦc
  have hPjc : Continuous (aP ℓ j Φ) := aP_continuous hℓ j hΦc
  have hAc : Continuous (aP ℓ i (aQ ℓ j Φ)) := aP_continuous hℓ i hQc
  have hBc : Continuous (aP ℓ i (aP ℓ j Φ)) := aP_continuous hℓ i hPjc
  -- the pointwise decomposition `P_iΦ = P_iQ_jΦ + P_iP_jΦ`
  have hdecomp : ∀ y : Submission.BoseGases.X n,
      aP ℓ i Φ y = aP ℓ i (aQ ℓ j Φ) y + aP ℓ i (aP ℓ j Φ) y := by
    intro y
    have hsum : (aQ ℓ j Φ + aP ℓ j Φ : Submission.BoseGases.X n → ℝ) = Φ := by
      funext z
      simp [Submission.BoseGases.aQ]
    calc aP ℓ i Φ y = aP ℓ i (aQ ℓ j Φ + aP ℓ j Φ) y := by rw [hsum]
      _ = aP ℓ i (aQ ℓ j Φ) y + aP ℓ i (aP ℓ j Φ) y := aP_add hℓ i hQc hPjc y
  -- the `slot-j` fibre of the second summand is constant
  have hfibB : ∀ y : E3, aP ℓ i (aP ℓ j Φ) (Function.update x j y) = aP ℓ i (aP ℓ j Φ) x :=
    fun y => Work.BoseFixB3.CS.aP_aP_const_slot hℓ hij hΦc x y
  have hfibA : Continuous (fun y : E3 => aP ℓ i (aQ ℓ j Φ) (Function.update x j y)) :=
    hAc.comp (continuous_const.update j continuous_id)
  have hfibBc : Continuous (fun y : E3 => aP ℓ i (aP ℓ j Φ) (Function.update x j y)) :=
    hBc.comp (continuous_const.update j continuous_id)
  -- additivity of `lowMult` on the fibre
  have hlow : Work.BoseBoxFix.lowSlot fc κ ℓ j (aP ℓ i Φ) x
      = Work.BoseBoxFix.lowSlot fc κ ℓ j (aP ℓ i (aQ ℓ j Φ)) x
        + aP ℓ i (aP ℓ j Φ) x * Work.BoseBoxFix.lowMult fc κ ℓ (fun _ : E3 => (1 : ℝ)) (x j) := by
    have hfibeq : (fun y : E3 => aP ℓ i Φ (Function.update x j y))
        = fun y : E3 => aP ℓ i (aQ ℓ j Φ) (Function.update x j y)
            + aP ℓ i (aP ℓ j Φ) (Function.update x j y) := by
      funext y
      exact hdecomp _
    show Work.BoseBoxFix.lowMult fc κ ℓ (fun y : E3 => aP ℓ i Φ (Function.update x j y)) (x j) = _
    rw [hfibeq]
    rw [show (fun y : E3 => aP ℓ i (aQ ℓ j Φ) (Function.update x j y)
          + aP ℓ i (aP ℓ j Φ) (Function.update x j y))
        = (fun y : E3 => aP ℓ i (aQ ℓ j Φ) (Function.update x j y))
          + (fun y : E3 => aP ℓ i (aP ℓ j Φ) (Function.update x j y)) from rfl]
    rw [lowMult_add_of_pos (fc := fc) (κ := κ) (ℓ := ℓ) hκ hfibA hfibBc (x j)]
    congr 1
    rw [show (fun y : E3 => aP ℓ i (aP ℓ j Φ) (Function.update x j y))
        = fun _ : E3 => aP ℓ i (aP ℓ j Φ) x from funext hfibB]
    have hP : (fun _ : E3 => aP ℓ i (aP ℓ j Φ) x)
        = fun z : E3 => aP ℓ i (aP ℓ j Φ) x * (fun _ : E3 => (1 : ℝ)) z := by
      funext z; simp
    rw [hP, Work.BoseFixB3.Eps.lowMult_const_mul fc κ ℓ (aP ℓ i (aP ℓ j Φ) x)
      (fun _ : E3 => (1 : ℝ)) (x j)]
  -- assemble
  have hmain : Work.BoseFixB3.highSlot fc κ ℓ j (aP ℓ i Φ) x
      = aP ℓ i Φ x - (Work.BoseBoxFix.lowSlot fc κ ℓ j (aP ℓ i (aQ ℓ j Φ)) x
          + aP ℓ i (aP ℓ j Φ) x * Work.BoseBoxFix.lowMult fc κ ℓ (fun _ : E3 => (1 : ℝ)) (x j)) := by
    rw [Work.BoseFixB3.highSlot, hlow]
  rw [hmain, hdecomp x, aP_comm hℓ i j hΦc x]
  rw [Work.BoseFixB3.highSlot]
  show aP ℓ i (aQ ℓ j Φ) x + aP ℓ j (aP ℓ i Φ) x
        - (Work.BoseBoxFix.lowSlot fc κ ℓ j (aP ℓ i (aQ ℓ j Φ)) x
          + aP ℓ j (aP ℓ i Φ) x * Work.BoseBoxFix.lowMult fc κ ℓ (fun _ : E3 => (1 : ℝ)) (x j))
      = (aP ℓ i (aQ ℓ j Φ) x - Work.BoseBoxFix.lowSlot fc κ ℓ j (aP ℓ i (aQ ℓ j Φ)) x)
        + aP ℓ j (aP ℓ i Φ) x
          * (1 - Work.BoseBoxFix.lowMult fc κ ℓ (fun _ : E3 => (1 : ℝ)) (x j))
  ring

/-! ## 2. The sum-level decomposition -/

theorem q3bar_add_q3om_eq_v2_of_pos (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) (hκ : 0 < κ)
    (hℓ : 0 < ℓ)
    (w1 ω : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (hΦc : Continuous Φ)
    (hw1 : ∀ p : Fin n × Fin n, MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n => w1 (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)))
    (hω : ∀ p : Fin n × Fin n, MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n => ω (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)))
    (hI1 : ∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        Work.BoseFixB3.highSlot fc κ ℓ p.2
            (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x
        * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x * w1 (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)))
    (hI2 : ∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        Work.BoseFixB3.highSlot fc κ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x
        * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x
        * w1 (x p.1) (x p.2) * ω (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)))
    (hI3 : ∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        Work.BoseFixB3.highSlot fc κ ℓ p.2
            (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x
        * (Submission.BoseGases.q4B ℓ ω Φ p x - ω (x p.1) (x p.2)
            * (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
              + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x))
        * w1 (x p.1) (x p.2)) (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)))
    (hI4 : ∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x) ^ 2
          * Work.BoseFixB3.CS.leakFn fc κ ℓ (x p.2)
          * ω (x p.1) (x p.2) * w1 (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))) :
    Work.BoseFixB3.q3barWord fc κ ℓ w1 Φ + Work.BoseFixB3.q3omWord fc κ ℓ w1 ω Φ
      = 2 * (∑ p ∈ Submission.BoseGases.pairSet n, ∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseFixB3.highSlot fc κ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x *
              (Submission.BoseGases.q4B ℓ ω Φ p x - ω (x p.1) (x p.2) *
                (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
                  + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x)) *
              w1 (x p.1) (x p.2))
        + 2 * (∑ p ∈ Submission.BoseGases.pairSet n, ∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x) ^ 2 *
              Work.BoseFixB3.CS.leakFn fc κ ℓ (x p.2) *
              ω (x p.1) (x p.2) * w1 (x p.1) (x p.2)) := by
  classical
  -- the four integrands
  set I1 : Fin n × Fin n → Submission.BoseGases.X n → ℝ := fun p x =>
    Work.BoseFixB3.highSlot fc κ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x
      * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
      * w1 (x p.1) (x p.2) with hI1def
  set I2 : Fin n × Fin n → Submission.BoseGases.X n → ℝ := fun p x =>
    Work.BoseFixB3.highSlot fc κ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x
      * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x
      * w1 (x p.1) (x p.2) * ω (x p.1) (x p.2) with hI2def
  set R1 : Fin n × Fin n → Submission.BoseGases.X n → ℝ := fun p x =>
    Work.BoseFixB3.highSlot fc κ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x
      * (Submission.BoseGases.q4B ℓ ω Φ p x - ω (x p.1) (x p.2) *
          (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
            + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x))
      * w1 (x p.1) (x p.2) with hR1def
  set R2 : Fin n × Fin n → Submission.BoseGases.X n → ℝ := fun p x =>
    (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x) ^ 2
      * Work.BoseFixB3.CS.leakFn fc κ ℓ (x p.2)
      * ω (x p.1) (x p.2) * w1 (x p.1) (x p.2) with hR2def
  -- the pointwise identity of the integrands, on the pair set
  have hpair : ∀ p ∈ Submission.BoseGases.pairSet n,
      (∫ x in Submission.BoseGases.abox n ℓ, I1 p x) + (∫ x in Submission.BoseGases.abox n ℓ, I2 p x)
        = (∫ x in Submission.BoseGases.abox n ℓ, R1 p x)
          + (∫ x in Submission.BoseGases.abox n ℓ, R2 p x) := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hInt1 : MeasureTheory.Integrable (I1 p)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) := by
      rw [hI1def]; exact hI1 p hp
    have hInt2 : MeasureTheory.Integrable (I2 p)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) := by
      rw [hI2def]; exact hI2 p hp
    have hInt3 : MeasureTheory.Integrable (R1 p)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) := by
      rw [hR1def]; exact hI3 p hp
    have hInt4 : MeasureTheory.Integrable (R2 p)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) := by
      rw [hR2def]; exact hI4 p hp
    have hpoint : ∀ x : Submission.BoseGases.X n, I1 p x + I2 p x = R1 p x + R2 p x := by
      intro x
      have h1 := highSlot_aP_eq_of_pos fc κ ℓ hκ hℓ hne hΦc x
      have h2 := aP_comm hℓ p.1 p.2 hΦc x
      simp only [hI1def, hI2def, hR1def, hR2def, Submission.BoseGases.q4B]
      rw [h1, h2]
      ring
    rw [← MeasureTheory.integral_add hInt1 hInt2,
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint),
      MeasureTheory.integral_add hInt3 hInt4]
  -- assembly
  have hsum : (∑ p ∈ Submission.BoseGases.pairSet n,
        ((∫ x in Submission.BoseGases.abox n ℓ, I1 p x)
          + (∫ x in Submission.BoseGases.abox n ℓ, I2 p x)))
      = ∑ p ∈ Submission.BoseGases.pairSet n,
        ((∫ x in Submission.BoseGases.abox n ℓ, R1 p x)
          + (∫ x in Submission.BoseGases.abox n ℓ, R2 p x)) :=
    Finset.sum_congr rfl hpair
  calc Work.BoseFixB3.q3barWord fc κ ℓ w1 Φ + Work.BoseFixB3.q3omWord fc κ ℓ w1 ω Φ
      = 2 * (∑ p ∈ Submission.BoseGases.pairSet n,
            ((∫ x in Submission.BoseGases.abox n ℓ, I1 p x)
              + (∫ x in Submission.BoseGases.abox n ℓ, I2 p x))) := by
        simp only [Work.BoseFixB3.q3barWord, Work.BoseFixB3.q3omWord, hI1def, hI2def,
          Finset.sum_add_distrib]
        ring
    _ = 2 * (∑ p ∈ Submission.BoseGases.pairSet n,
            ((∫ x in Submission.BoseGases.abox n ℓ, R1 p x)
              + (∫ x in Submission.BoseGases.abox n ℓ, R2 p x))) := by
        rw [hsum]
    _ = 2 * (∑ p ∈ Submission.BoseGases.pairSet n, ∫ x in Submission.BoseGases.abox n ℓ, R1 p x)
          + 2 * (∑ p ∈ Submission.BoseGases.pairSet n, ∫ x in Submission.BoseGases.abox n ℓ, R2 p x) := by
        rw [Finset.sum_add_distrib]
        ring
    _ = 2 * (∑ p ∈ Submission.BoseGases.pairSet n, ∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseFixB3.highSlot fc κ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x *
              (Submission.BoseGases.q4B ℓ ω Φ p x - ω (x p.1) (x p.2) *
                (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
                  + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x)) *
              w1 (x p.1) (x p.2))
        + 2 * (∑ p ∈ Submission.BoseGases.pairSet n, ∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x) ^ 2 *
              Work.BoseFixB3.CS.leakFn fc κ ℓ (x p.2) *
              ω (x p.1) (x p.2) * w1 (x p.1) (x p.2)) := by
        simp only [hR1def, hR2def]

end Work.BoseFixB3.CS.Pieces
