import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.windowCGAuxAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicLowBandAux.nPlusSqWindowTransport`

The **transport** of the corpus's sharp spectral window `⟨n₊²⟩ ≤ 𝓜⟨n₊⟩`
(`Work.BoseBoxFock.PotCubicLowBandAux.spectralNPlusSqLe`, i.e. FS `eq:LocalizedNPlus`) from the
real iterate form `∫ n₊^k Φ·Φ ≤ 𝓜^k ∫ Φ²` to the **complex excited-count** vocabulary used by
`windowCGAux`:

    ∫_{abox} ‖nCf ℓ (boxRestrictC ℓ Φ) x‖² ≤ 𝓜 · cnPlusC ℓ (boxRestrictC ℓ Φ) .

The two sides are related to the real data by three elementary identifications.

* **Pointwise (`nCf_boxRestrictC_eq_nPlusFun`)**: on the box the complex state
  `Θ = boxRestrictC ℓ Φ` agrees with `Φ`, and the complex slot mean `aPC ℓ j Θ` agrees with the
  real slot mean `aP ℓ j Φ` (`aPC_boxRestrictC_eq_aP`, from `aPC_ofReal`), so
  `nCf ℓ Θ x = ((nPlusFun ℓ Φ x : ℝ) : ℂ)` — the complex excited count *is* the real one.  Hence
  `∫ ‖nCf Θ‖² = ∫ (n₊Φ)²`.

* **Self-adjointness (`nPlusFun_pairing_sym`)**: `n₊ = ΣᵢQᵢ` is symmetric for the box pairing
  (each `Qᵢ` is, by `Work.BoseFixB2.Sector.aQ_sym_box`), so `∫ (n₊Φ)² = ∫ (n₊²Φ)·Φ`.

* **The window is `cnPlus`**: `∫ (n₊Φ)·Φ = cnPlus ℓ Φ`
  (`Work.UBBInputs4.cnPlus_eq_qform_nPlus`) and `cnPlus ℓ Φ = cnPlusC ℓ Θ`
  (`cnPlusC_boxRestrictC_eq_cnPlus`).

Chaining these with `spectralNPlusSqLe` gives the target.  Everything is `sorry`-free.
-/

namespace Work.BoseBoxFock.PotCubicLowBandAux

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The complex slot mean of the box restriction

`boxRestrictC ℓ Φ` agrees with `Φ` on `abox n ℓ`; since a slot update of a box configuration by a
cube element stays in the box (`update_mem_abox`), the complex slot mean of the restriction is the
`ℂ`-cast of the real slot mean. -/

/-- On the box, the complex box restriction is the cast of `Φ`. -/
lemma boxRestrictC_eq_ofReal_on {n : ℕ} {ℓ : ℝ} (Φ : Submission.BoseGases.X n → ℝ)
    {z : Submission.BoseGases.X n} (hz : z ∈ Submission.BoseGases.abox n ℓ) :
    Work.BoseBoxFock.boxRestrictC ℓ Φ z = ((Φ z : ℝ) : ℂ) := by
  simp only [Work.BoseBoxFock.boxRestrictC, Set.indicator_of_mem hz]
  simp

/-- **The complex slot mean of the box restriction is the cast of the real slot mean.** -/
lemma aPC_boxRestrictC_eq_aP {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    (Φ : Submission.BoseGases.X n → ℝ) {x : Submission.BoseGases.X n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) :
    Work.BoseBoxFock.aPC ℓ i (Work.BoseBoxFock.boxRestrictC ℓ Φ) x
      = ((Submission.BoseGases.aP ℓ i Φ x : ℝ) : ℂ) := by
  have hcongr : Work.BoseBoxFock.aPC ℓ i (Work.BoseBoxFock.boxRestrictC ℓ Φ) x
      = Work.BoseBoxFock.aPC ℓ i (fun y => ((Φ y : ℝ) : ℂ)) x := by
    simp only [Work.BoseBoxFock.aPC]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      (fun y hy => ?_)
    rw [boxRestrictC_eq_ofReal_on Φ (update_mem_abox i hx hy)]
  rw [hcongr, Work.BoseBoxFock.aPC_ofReal]

/-- **The complex excited count of the box restriction is the cast of the real one.**  On the box,
`nCf ℓ (boxRestrictC ℓ Φ)` is the real excited count `n₊Φ = Σᵢ aQ ℓ i Φ`, cast to `ℂ`. -/
lemma nCf_boxRestrictC_eq_nPlusFun {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (Φ : Submission.BoseGases.X n → ℝ) {x : Submission.BoseGases.X n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) :
    nCf ℓ (Work.BoseBoxFock.boxRestrictC ℓ Φ) x
      = ((Work.BoseBox.nPlusFun ℓ Φ x : ℝ) : ℂ) := by
  simp only [nCf, Work.BoseBox.nPlusFun]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [boxRestrictC_eq_ofReal_on Φ hx, aPC_boxRestrictC_eq_aP hℓ j Φ hx]
  simp only [Submission.BoseGases.aQ, Complex.ofReal_sub]

/-! ## 2. The box symmetry of `n₊ = ΣᵢQᵢ`

`n₊` is symmetric for the box pairing, being a sum of the symmetric slot operators `Qᵢ`
(`Work.BoseFixB2.Sector.aQ_sym_box`, itself `aP_sym_box` + `aQ = 1 − aP`). -/

/-- **Self-adjointness of `n₊` over the box**: `∫ (ΣᵢQᵢ g)·Φ = ∫ g·(ΣᵢQᵢ Φ)`. -/
lemma nPlusFun_pairing_sym {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (g Φ : Submission.BoseGases.X n → ℝ) (hg : Continuous g) (hΦ : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (∑ i : Fin n, Submission.BoseGases.aQ ℓ i g x) * Φ x)
      = ∫ x in Submission.BoseGases.abox n ℓ,
        g x * (∑ i : Fin n, Submission.BoseGases.aQ ℓ i Φ x) := by
  have hL : ∀ i : Fin n, IntegrableOn
      (fun x : Submission.BoseGases.X n => Submission.BoseGases.aQ ℓ i g x * Φ x)
      (Submission.BoseGases.abox n ℓ) (volume) := fun i =>
    Submission.BoseGases.integrableOn_abox_of_continuous hℓ
      ((Submission.BoseGases.aQ_continuous hℓ i hg).mul hΦ)
  have hR : ∀ i : Fin n, IntegrableOn
      (fun x : Submission.BoseGases.X n => g x * Submission.BoseGases.aQ ℓ i Φ x)
      (Submission.BoseGases.abox n ℓ) (volume) := fun i =>
    Submission.BoseGases.integrableOn_abox_of_continuous hℓ
      (hg.mul (Submission.BoseGases.aQ_continuous hℓ i hΦ))
  rw [show (∫ x in Submission.BoseGases.abox n ℓ,
        (∑ i : Fin n, Submission.BoseGases.aQ ℓ i g x) * Φ x)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          ∑ i : Fin n, Submission.BoseGases.aQ ℓ i g x * Φ x from by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with x
        rw [Finset.sum_mul]]
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hL i)]
  trans ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
      g x * Submission.BoseGases.aQ ℓ i Φ x
  · exact Finset.sum_congr rfl (fun i _ => Work.BoseFixB2.Sector.aQ_sym_box hℓ i hg hΦ)
  · rw [show (∫ x in Submission.BoseGases.abox n ℓ,
          g x * (∑ i : Fin n, Submission.BoseGases.aQ ℓ i Φ x))
        = ∫ x in Submission.BoseGases.abox n ℓ,
            ∑ i : Fin n, g x * Submission.BoseGases.aQ ℓ i Φ x from by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with x
          rw [Finset.mul_sum]]
    exact (MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hR i)).symm

/-! ## 3. The transport -/

theorem nPlusSqWindowTransport {n : ℕ} {ℓ 𝓜 : ℝ} (hℓ : 0 < ℓ) (h𝓜 : 0 ≤ 𝓜)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hmom : ∀ k : ℕ, ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseBox.nPlusPow ℓ n k Φ x * Φ x
      ≤ 𝓜 ^ k * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        ‖nCf ℓ (Work.BoseBoxFock.boxRestrictC ℓ Φ) x‖ ^ 2)
      ≤ 𝓜 * Work.BoseBoxFock.cnPlusC ℓ (Work.BoseBoxFock.boxRestrictC ℓ Φ) := by
  have hΦc : Continuous Φ := hΦ.continuous
  have huc : Continuous (Work.BoseBox.nPlusFun ℓ Φ) :=
    Work.BoseFixB2.Recomb.nPlusFun_continuous hℓ hΦc
  -- the first iterate of `n₊`
  have hpow1 : ∀ x : Submission.BoseGases.X n, Work.BoseBox.nPlusPow ℓ n 1 Φ x
      = ∑ i : Fin n, Submission.BoseGases.aQ ℓ i Φ x := by
    intro x
    rw [Work.BoseFixB2.Recomb.nPlusPow_succ_eq ℓ n 0 Φ,
      Work.BoseFixB2.Recomb.nPlusPow_zero_eq ℓ n Φ]
    rfl
  -- the second iterate of `n₊`, as a slot sum of the first iterate
  have hpow2 : ∀ x : Submission.BoseGases.X n, Work.BoseBox.nPlusPow ℓ n 2 Φ x
      = ∑ i : Fin n, Submission.BoseGases.aQ ℓ i (Work.BoseBox.nPlusFun ℓ Φ) x := by
    intro x
    rw [Work.BoseFixB2.Recomb.nPlusPow_succ_eq ℓ n 1 Φ,
      Work.BoseFixB2.Recomb.nPlusPow_succ_eq ℓ n 0 Φ,
      Work.BoseFixB2.Recomb.nPlusPow_zero_eq ℓ n Φ]
    simp only [Work.BoseBox.nPlusFun]
  -- (a) the pointwise transport: the complex excited count is the cast of the real one
  have hstep1 : (∫ x in Submission.BoseGases.abox n ℓ,
        ‖nCf ℓ (Work.BoseBoxFock.boxRestrictC ℓ Φ) x‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ, (Work.BoseBox.nPlusFun ℓ Φ x) ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
      (fun x hx => ?_)
    rw [nCf_boxRestrictC_eq_nPlusFun hℓ Φ hx, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- (b) self-adjointness of `n₊`: `∫ (n₊Φ)² = ∫ (n₊²Φ)·Φ`
  have hstep2 : (∫ x in Submission.BoseGases.abox n ℓ, (Work.BoseBox.nPlusFun ℓ Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ, Work.BoseBox.nPlusPow ℓ n 2 Φ x * Φ x := by
    have hkey := nPlusFun_pairing_sym hℓ (Work.BoseBox.nPlusFun ℓ Φ) Φ huc hΦc
    rw [show (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseBox.nPlusPow ℓ n 2 Φ x * Φ x)
        = ∫ x in Submission.BoseGases.abox n ℓ,
            (∑ i : Fin n, Submission.BoseGases.aQ ℓ i (Work.BoseBox.nPlusFun ℓ Φ) x) * Φ x
        from by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      rw [hpow2 x]]
    rw [hkey]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    have hx' : Work.BoseBox.nPlusFun ℓ Φ x
        = ∑ i : Fin n, Submission.BoseGases.aQ ℓ i Φ x := rfl
    rw [hx']
    ring
  -- (c) the first moment is the box excited count
  have hstep3 : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseBox.nPlusPow ℓ n 1 Φ x * Φ x)
      = Work.BoseBoxFock.cnPlusC ℓ (Work.BoseBoxFock.boxRestrictC ℓ Φ) := by
    rw [Work.BoseBoxFock.cnPlusC_boxRestrictC_eq_cnPlus hℓ Φ,
      Work.UBBInputs4.cnPlus_eq_qform_nPlus hℓ hΦc]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    rw [hpow1 x]
  calc (∫ x in Submission.BoseGases.abox n ℓ,
        ‖nCf ℓ (Work.BoseBoxFock.boxRestrictC ℓ Φ) x‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ, Work.BoseBox.nPlusPow ℓ n 2 Φ x * Φ x := by
        rw [hstep1, hstep2]
    _ ≤ 𝓜 * ∫ x in Submission.BoseGases.abox n ℓ, Work.BoseBox.nPlusPow ℓ n 1 Φ x * Φ x :=
        spectralNPlusSqLe hℓ h𝓜 hΦ hmom
    _ = 𝓜 * Work.BoseBoxFock.cnPlusC ℓ (Work.BoseBoxFock.boxRestrictC ℓ Φ) := by rw [hstep3]

end Work.BoseBoxFock.PotCubicLowBandAux
