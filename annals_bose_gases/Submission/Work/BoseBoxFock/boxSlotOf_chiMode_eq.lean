import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotGroupDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxSlotOf_chiMode_eq` — the slot dictionary of the `χ`-mode

Step (2) of `FINDING_PotChiLin_exists.md` §1 needs the operator identity

    `X_C Θ = Σ_j η_C(x_j)·√(ℓ³)·(aPC ℓ j Θ)`,     `η_C = Work.BoseDict.etaOf e C`,

which is the *per-slot* statement that the `j`-th slot of the first-quantised rank-one operator
`|η_C⟩⟨e₀|` (`Work.BoseDict.boxSlotOf e C (evec m 0) j`) is `η_C(x_j)·√(ℓ³)` times the box slot
mean `aPC ℓ j Θ`.  Since `e₀ = evec m 0` is the pinned condensate mode `e 0 =ᵐ (√ℓ³)⁻¹·θ_Λ`, the
`z`-integral in `boxSlotOf` collapses:

    `∫_z conj(e₀ z)·Θ(x[j↦z]) = conj((√ℓ³)⁻¹)·∫_{Λ} Θ(x[j↦z])`
                              `= √(ℓ³)·ℓ⁻³·∫_{Λ} Θ(x[j↦z]) = √(ℓ³)·aPC ℓ j Θ x`,

because `θ_Λ` is the indicator of the cube `Λ = acube ℓ` (`thetaFun_eq_indicator`,
`conj_thetaFun_eq_self`) and `(√(ℓ³))⁻¹ = √(ℓ³)·(ℓ³)⁻¹` (`Real.sq_sqrt`).

The identity is *pointwise* in `x`, so the a.e. form of the statement is immediate.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

/-- **The `z`-integral of the pinned condensate mode.**  For a mode family pinned by
`e 0 =ᵐ c·θ_Λ` with `c = (√ℓ³)⁻¹`, the conjugate of `e 0` paired with an arbitrary state `Θ` in
the `j`-th slot collapses to `conj c · ∫_{Λ} Θ(x[j↦·])`. -/
private lemma integral_conj_e0 {n m : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Sp → ℂ}
    (hpin : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure Sp),
        e 0 z = ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (j : Fin n) (Θ : Work.BoseDict.Xn n → ℂ) (x : Work.BoseDict.Xn n) :
    (∫ z : Sp, (starRingEnd ℂ) (e 0 z) * Θ (Function.update x j z))
      = (starRingEnd ℂ) ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ)
        * ∫ z in Submission.BoseGases.acube ℓ, Θ (Function.update x j z) := by
  -- The conjugate of the a.e. pinning, using that `θ_Λ` is real-valued.
  have hconjae : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure Sp),
      (starRingEnd ℂ) (e 0 z)
        = (starRingEnd ℂ) ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ)
          * Work.BoseK15.corpusBox.thetaFun ℓ z := by
    filter_upwards [hpin] with z hz
    rw [hz, map_mul, conj_thetaFun_eq_self hℓ]
  -- `θ_Λ·Θ(x[j↦·])` is the indicator of the cube `Λ` applied to `Θ(x[j↦·])`.
  have hθind : (fun z : Sp => Work.BoseK15.corpusBox.thetaFun ℓ z
        * Θ (Function.update x j z))
      = fun z : Sp => (Submission.BoseGases.acube ℓ).indicator
          (fun z => Θ (Function.update x j z)) z := by
    funext z
    rw [thetaFun_eq_indicator hℓ]
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
  rw [show (∫ z : Sp, (starRingEnd ℂ) (e 0 z) * Θ (Function.update x j z))
      = ∫ z : Sp, (starRingEnd ℂ) ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ)
          * (Work.BoseK15.corpusBox.thetaFun ℓ z * Θ (Function.update x j z)) from by
    refine integral_congr_ae ?_
    filter_upwards [hconjae] with z hz
    rw [hz, mul_assoc]]
  rw [MeasureTheory.integral_const_mul, hθind,
    MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]

/-- **The scalar identity** `(√(ℓ³))⁻¹ = √(ℓ³)·(ℓ³)⁻¹` (`ℓ > 0`) in the complex normal form in
which `aPC` presents the box slot mean. -/
private lemma conj_inv_sqrt_eq {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (starRingEnd ℂ) ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ)
      = ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * ((1 / ℓ ^ 3 : ℝ) : ℂ) := by
  have hreal : (Real.sqrt (ℓ ^ 3))⁻¹ = Real.sqrt (ℓ ^ 3) * (1 / ℓ ^ 3) := by
    set s := Real.sqrt (ℓ ^ 3) with hs
    have hs2 : s ^ 2 = ℓ ^ 3 := by rw [hs]; exact Real.sq_sqrt (le_of_lt (pow_pos hℓ 3))
    have hne : s ≠ 0 := by rw [hs]; exact ne_of_gt (Real.sqrt_pos.mpr (pow_pos hℓ 3))
    rw [← hs2]
    field_simp
  rw [← Complex.ofReal_inv, Complex.conj_ofReal, ← Complex.ofReal_mul]
  exact congrArg ((↑) : ℝ → ℂ) hreal

/-- **The slot dictionary of the `χ`-mode.**  The `j`-th slot of the first-quantised rank-one
operator `|η_C⟩⟨e₀|` is `η_C(x_j)·√(ℓ³)·(aPC ℓ j Θ)`, a.e. on the box `abox n ℓ`. -/
theorem boxSlotOf_chiMode_eq {n m : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hpin : ∀ᵐ z ∂(MeasureTheory.volume :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
        e 0 z = ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) *
          Work.BoseK15.corpusBox.thetaFun ℓ z)
    (C : Fin m → ℝ) (Θ : Work.BoseDict.Xn n → ℂ) (j : Fin n) :
    (fun x => Work.BoseDict.boxSlotOf e C (Work.BoseB4.evec m 0) j Θ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)]
      fun x => Work.BoseDict.etaOf e C (x j) * ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) *
          Work.BoseBoxFock.aPC ℓ j Θ x := by
  refine Filter.Eventually.of_forall (fun x => ?_)
  -- `η_{evec 0} = e 0`.
  have he0 : ∀ z : Sp, Work.BoseDict.etaOf e (Work.BoseB4.evec m 0) z = e 0 z :=
    fun z => Work.BoseDict.etaOf_pi_single e 0 z
  -- The collapsed `z`-integral.
  have hJ : (∫ z : Sp, (starRingEnd ℂ) (Work.BoseDict.etaOf e (Work.BoseB4.evec m 0) z)
        * Θ (Function.update x j z))
      = (starRingEnd ℂ) ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ)
        * ∫ z in Submission.BoseGases.acube ℓ, Θ (Function.update x j z) := by
    have hcongr : (fun z : Sp => (starRingEnd ℂ)
          (Work.BoseDict.etaOf e (Work.BoseB4.evec m 0) z) * Θ (Function.update x j z))
        = fun z : Sp => (starRingEnd ℂ) (e 0 z) * Θ (Function.update x j z) := by
      funext z
      rw [he0 z]
    rw [show (∫ z : Sp, (starRingEnd ℂ)
            (Work.BoseDict.etaOf e (Work.BoseB4.evec m 0) z) * Θ (Function.update x j z))
        = ∫ z : Sp, (starRingEnd ℂ) (e 0 z) * Θ (Function.update x j z) from by rw [hcongr]]
    exact integral_conj_e0 hℓ hpin j Θ x
  -- Unfold the definitions.
  have hbox : Work.BoseDict.boxSlotOf e C (Work.BoseB4.evec m 0) j Θ x
      = Work.BoseDict.etaOf e C (x j)
        * ∫ z : Sp, (starRingEnd ℂ) (Work.BoseDict.etaOf e (Work.BoseB4.evec m 0) z)
            * Θ (Function.update x j z) := rfl
  have haPC : Work.BoseBoxFock.aPC ℓ j Θ x
      = ((1 / ℓ ^ 3 : ℝ) : ℂ)
        * ∫ z in Submission.BoseGases.acube ℓ, Θ (Function.update x j z) := rfl
  show Work.BoseDict.boxSlotOf e C (Work.BoseB4.evec m 0) j Θ x
      = Work.BoseDict.etaOf e C (x j) * ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) *
          Work.BoseBoxFock.aPC ℓ j Θ x
  rw [hbox, hJ, haPC, conj_inv_sqrt_eq hℓ]
  ring

end Work.BoseBoxFock
