import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.aPCPairAlg
import Submission.Work.BoseBoxFock.chiRowDict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.n0Slot_ae_real` — the condensate-row slot sum, in the real corpus vocabulary

The box image of the model's condensate number operator `n₀ = a₀†a₀` is the first-quantised
slot sum `Work.BoseDict.boxSlotSum e (rankOne (evec0 m))` (the one-particle rank-one operator of
the condensate coordinate vector `evec0 m = evec 0`).  On the box `abox n ℓ` — i.e. after
restricting the state to the box, `boxRestrictC ℓ Φ` — this slot sum is exactly the sum of the
*real* slot means of the corpus vocabulary:

    boxSlotSum e (rankOne (evec0 m)) (boxRestrictC ℓ Φ) =ᵐ ∑_i ↑(aP ℓ i Φ)

a.e. for `volume ↾ abox n ℓ`.  The three ingredients:

* `rankOne_evec0` — the rank-one operator `|evec 0⟩⟨evec 0|` *is* the corpus's `proj0`, so
  `boxSlotSum_proj0` (`BoxFockDefs`) evaluates the slot sum as `Σ_j boxSlotOf e e₀ e₀ j`;
* `boxSlotOf_evec_zero_eq_aPC` (`boxSlotOf_evec_zero_eq_aPC`) — a.e. on the box the slot operator
  of the pinned condensate vector is the complex slot mean `aPC ℓ j`;
* `aPC_boxRestrictC_apply_ofReal` — on the box, the complex slot mean of `boxRestrictC ℓ Φ` is the
  coercion of the real slot mean `aP ℓ j Φ` (the indicator in `boxRestrictC` is `1` on the box, and
  `Function.update x j y ∈ abox n ℓ` for `x ∈ abox n ℓ`, `y ∈ acube ℓ`).

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The rank-one operator of the condensate coordinate vector is `proj0`**:
`rankOne (evec 0) = (∑_l (evec 0)_l • proj l).smulRight (evec 0) = proj 0`. -/
theorem rankOne_evec0 (m : ℕ) [NeZero m] : rankOne (evec0 m) = proj0 m := by
  have hsum : (∑ l : Fin m, evec0 m l • (LinearMap.proj l : (Fin m → ℝ) →ₗ[ℝ] ℝ))
      = LinearMap.proj (0 : Fin m) := by
    rw [Finset.sum_eq_single (0 : Fin m)]
    · rw [evec0_apply_zero, one_smul]
    · intro l _ hl; rw [evec0_apply_ne hl, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [rankOne, hsum]
  ext v i
  rfl

/-- **On the box, the complex slot mean of the box restriction is the real slot mean.**
`boxRestrictC ℓ Φ = ↑Φ` on `abox n ℓ`, and `x ∈ abox n ℓ`, `y ∈ acube ℓ` imply
`Function.update x j y ∈ abox n ℓ`; hence the integrand of `aPC` is the coercion of the integrand
of `aP`, and `integral_ofReal` identifies the two Bochner integrals. -/
theorem aPC_boxRestrictC_apply_ofReal {n : ℕ} {ℓ : ℝ}
    (Φ : Submission.BoseGases.X n → ℝ) {x : Submission.BoseGases.X n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) (j : Fin n) :
    aPC ℓ j (boxRestrictC ℓ Φ) x = ((Submission.BoseGases.aP ℓ j Φ x : ℝ) : ℂ) := by
  have hpt : ∀ y ∈ Submission.BoseGases.acube ℓ,
      boxRestrictC ℓ Φ (Function.update x j y) = ((Φ (Function.update x j y) : ℝ) : ℂ) := by
    intro y hy
    have hmem : Function.update x j y ∈ Submission.BoseGases.abox n ℓ := by
      intro i
      by_cases hi : i = j
      · subst hi; rw [Function.update_self]; exact hy
      · rw [Function.update_of_ne hi]; exact hx i
    simp only [boxRestrictC]
    rw [Set.indicator_of_mem hmem]
    simp
  have hInt : (∫ y in Submission.BoseGases.acube ℓ,
      boxRestrictC ℓ Φ (Function.update x j y))
      = ((∫ y in Submission.BoseGases.acube ℓ,
          Φ (Function.update x j y) : ℝ) : ℂ) := by
    rw [setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ) hpt]
    exact integral_ofReal (𝕜 := ℂ)
  simp only [aPC, Submission.BoseGases.aP]
  rw [hInt, Complex.ofReal_mul]

/-- **The condensate slot sum at the coordinate vector `evec 0`.**  With `rankOne_evec0` the
coefficients `(rankOne (evec0 m) (evec l')).l` are `δ_{l',0}δ_{l,0}`, so the triple sum collapses
to `Σ_j boxSlotOf e (evec 0) (evec 0) j`, i.e. to `Σ_j uSlot (e 0) j`. -/
theorem boxSlotSum_rankOne_evec0 {m d : ℕ} [NeZero m] (e : Fin m → Work.BoseDict.Sp → ℂ)
    (Θ : Work.BoseDict.Xn d → ℂ) :
    Work.BoseDict.boxSlotSum e (rankOne (evec0 m)) Θ
      = fun x => ∑ j : Fin d,
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m 0) (Work.BoseB4.evec m 0) j Θ x := by
  rw [rankOne_evec0 m, boxSlotSum_proj0]
  funext x
  exact Finset.sum_congr rfl
    (fun j _ => (congrFun (boxSlotOf_evec0_eq_uSlot e j Θ) x).symm)

theorem n0Slot_ae_real {n m : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hpin : e 0 =ᵐ[MeasureTheory.volume] fun z =>
      ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hmeas : ∀ l, Measurable (e l)) (hemem : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m))
        (Work.BoseBoxFock.boxRestrictC ℓ Φ))
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)]
      fun x => ∑ i : Fin n, ((Submission.BoseGases.aP ℓ i Φ x : ℝ) : ℂ) := by
  classical
  -- The pinning hypothesis in the normal form `∃ c, conj c * c = ℓ⁻³ ∧ e 0 =ᵐ c·θ_ℓ`.
  have hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp),
        e 0 z = c * Work.BoseK15.corpusBox.thetaFun ℓ z := by
    refine ⟨((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ), ?_, hpin⟩
    have hsq : Real.sqrt (ℓ ^ 3) * Real.sqrt (ℓ ^ 3) = ℓ ^ 3 :=
      Real.mul_self_sqrt (le_of_lt (pow_pos hℓ 3))
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul, hsq,
      ← Complex.ofReal_inv]
  obtain ⟨c, hcstar, hcae⟩ := hc
  -- The box restriction is supported in the box.
  have hsuppΘ : Function.support (Work.BoseBoxFock.boxRestrictC ℓ Φ)
      ⊆ Submission.BoseGases.abox n ℓ := by
    intro x hx
    by_contra hxc
    refine hx ?_
    simp only [boxRestrictC]
    rw [Set.indicator_of_notMem hxc]
    simp
  -- A.e. on the box, each slot operator is the complex slot mean (`boxSlotOf_evec_zero_eq_aPC`).
  have hslot : ∀ j : Fin n,
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m 0) (Work.BoseB4.evec m 0) j
        (Work.BoseBoxFock.boxRestrictC ℓ Φ) x
      = Work.BoseBoxFock.aPC ℓ j (Work.BoseBoxFock.boxRestrictC ℓ Φ) x :=
    fun j => boxSlotOf_evec_zero_eq_aPC hℓ hemem hsupp ⟨c, hcstar, hcae⟩ _ hsuppΘ j
  rw [boxSlotSum_rankOne_evec0 e (Work.BoseBoxFock.boxRestrictC ℓ Φ)]
  filter_upwards [Filter.eventually_all.mpr hslot,
    MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable n ℓ)] with x hx1 hx2
  exact Finset.sum_congr rfl (fun j _ => by
    rw [hx1 j, aPC_boxRestrictC_apply_ofReal Φ hx2 j])

end Work.BoseBoxFock
