import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Momentum.momDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.junkMomForm` — the *junk* values of the box mean and of the
localised momentum transform

This is the "junk-value" companion of `Work.BoseKinLoc.Momentum.aestronglyMeasurable_momForm`
(the lemma used, in the assembly of that file, to reduce `momForm ℓ d u ψ` to the honest case
whenever `(bsBox ℓ u).indicator ψ` *is* a.e. strongly measurable).

If `(bsBox ℓ u).indicator ψ` is **not** a.e. strongly measurable, then every Bochner integral
in which `ψ` (restricted to the box) appears has the junk value `0` (`MeasureTheory.integral_undef`:
the Bochner integral of a non-integrable — in particular non-a.e.-strongly-measurable —
integrand is `0`).  Consequently

* the box mean `m_u(ψ) = |Λ(u)|⁻¹∫_{Λ(u)}ψ` vanishes, and
* the localised momentum transform `p ↦ ∫ e^{−i⟪p,z⟫}1_{Λ(u)}(z)Q_uψ(z)dz` vanishes for every `p`,

so that both quantities below are exactly `0` and carry no information about `ψ`.

## Proof

Write `Λ = Λ(u)`, `A := 1_Λ` (the indicator of the box), `m := m_u(ψ)`, `Q_uψ = ψ − m` and
`F := 1_Λ·ψ = 1_Λ.indicator ψ`.

*The box mean.*  Put `H := 1_{acube ℓ}·(ψ ∘ (ℓ•u + ·))`.  Since `z ↦ z − ℓ•u` is translation by
`−ℓ•u`, hence quasi-measure-preserving (`MeasureTheory.quasiMeasurePreserving_add_right` for the
translation-invariant `volume`), `H` is not a.e. strongly measurable: `H ∘ (· − ℓ•u) = F`
pointwise, so a.e. strong measurability of `H` would transport to `F`, contradicting `h`.  Hence
`∫ z, H z = 0` (`integral_undef`), and `∫_{Λ(u)}ψ = ∫ z, H z` by `integral_indicator`; dividing by
`|Λ(u)| = ℓ³` gives `m_u(ψ) = 0`.

*The momentum transform.*  Here `A·Q_uψ = A·ψ − m·A = F − m·A`, so the integrand of `kinFT`
is `↑F − (m:ℂ)·↑A`.  If it were a.e. strongly measurable, then so would be `↑F` (adding
`(m:ℂ)↑A`, a.e. strongly measurable because `A` is the indicator of the measurable set
`bsBox ℓ u`), and then so would be `F` itself, by applying the continuous linear projection
`Complex.reCLM` (whose value on a real number is that number).  This contradicts `h`, so the
integrand is not a.e. strongly measurable, hence not integrable: multiplying it by the
everywhere-nonzero continuous factor `e^{−i⟪p,·⟫}` cannot produce an a.e. strongly measurable
function either, so `∫ e^{−i⟪p,z⟫}(↑F(z) − (m:ℂ)↑A(z))dz = 0` by `integral_undef` again.
-/

namespace Work.BoseKinLoc.Momentum

open MeasureTheory

set_option maxHeartbeats 1000000

theorem junkMomForm (ℓ : ℝ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    (h : ¬ MeasureTheory.AEStronglyMeasurable ((Work.BSKinetic.bsBox ℓ u).indicator ψ) MeasureTheory.volume) :
    Work.BSKinetic.bsMean ℓ u ψ = 0 ∧
      ∀ p : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
          ((Work.BoseKinLoc.indU ℓ u z : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ u ψ z : ℝ) : ℂ)) p = 0 := by
  classical
  set m : ℝ := Work.BSKinetic.bsMean ℓ u ψ with hm
  set A : EuclideanSpace ℝ (Fin 3) → ℝ := Work.BoseKinLoc.indU ℓ u with hA
  set F : EuclideanSpace ℝ (Fin 3) → ℝ := (Work.BSKinetic.bsBox ℓ u).indicator ψ with hF
  have hQfree : ∀ z : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.Qfree ℓ u ψ z = ψ z - m := by
    intro z; simp [Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ, hm]
  have hAaux : ∀ z : EuclideanSpace ℝ (Fin 3), A z * ψ z = F z := by
    intro z
    rw [hA, hF, Work.BoseKinLoc.indU, Work.BoseKinLoc.lamBox]
    by_cases hz : z ∈ Work.BSKinetic.bsBox ℓ u <;> simp [hz]
  have hboxmeas : MeasurableSet (Work.BSKinetic.bsBox ℓ u) :=
    (Submission.BoseGases.acube_measurable ℓ).preimage
      (f := fun x : EuclideanSpace ℝ (Fin 3) => x - ℓ • u) (by fun_prop)
  have hA_aesm : AEStronglyMeasurable A volume := by
    rw [hA, Work.BoseKinLoc.indU, Work.BoseKinLoc.lamBox]
    exact aestronglyMeasurable_const.indicator hboxmeas
  -- the box indicator of `ψ` is the translate of the cube indicator of `ψ ∘ (ℓ•u + ·)`
  have htrans : (fun z : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.acube ℓ).indicator (fun w => ψ (ℓ • u + w)) (z + -(ℓ • u))) = F := by
    rw [hF]
    have hmem : ∀ z : EuclideanSpace ℝ (Fin 3),
        z ∈ Work.BSKinetic.bsBox ℓ u ↔ (z + -(ℓ • u)) ∈ Submission.BoseGases.acube ℓ := by
      intro z; simp [Work.BSKinetic.bsBox, sub_eq_add_neg]
    funext z
    simp only [Set.indicator_apply]
    by_cases hz : (z + -(ℓ • u)) ∈ Submission.BoseGases.acube ℓ
    · rw [if_pos hz, if_pos ((hmem z).mpr hz)]
      congr 1
      rw [← sub_eq_add_neg]
      abel
    · rw [if_neg hz, if_neg (fun hc => hz ((hmem z).mp hc))]
  -- hence the translated integrand is not a.e. strongly measurable either
  have hnotH : ¬ AEStronglyMeasurable
      ((Submission.BoseGases.acube ℓ).indicator (fun w => ψ (ℓ • u + w))) volume := by
    intro hH
    refine h ?_
    rw [← htrans]
    exact hH.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_add_right (volume : Measure (EuclideanSpace ℝ (Fin 3))) (-(ℓ • u)))
  have hIntH : ¬ Integrable ((Submission.BoseGases.acube ℓ).indicator (fun w => ψ (ℓ • u + w))) volume :=
    fun hI => hnotH hI.aestronglyMeasurable
  have hmean : Work.BSKinetic.bsMean ℓ u ψ = 0 := by
    rw [Work.BSKinetic.bsMean]
    have h1 : (∫ z in Submission.BoseGases.acube ℓ, ψ (ℓ • u + z)) = 0 := by
      rw [← integral_indicator (f := fun z : EuclideanSpace ℝ (Fin 3) => ψ (ℓ • u + z))
        (Submission.BoseGases.acube_measurable ℓ)]
      exact integral_undef hIntH
    rw [h1, mul_zero]
  refine ⟨hmean, fun p => ?_⟩
  have hne : ∀ y : EuclideanSpace ℝ (Fin 3), Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) ≠ 0 :=
    fun y => Complex.exp_ne_zero _
  -- `Q_uψ = ψ − m`, so the localised integrand is `↑F − (m:ℂ)·↑A`
  have hCform : (fun z : EuclideanSpace ℝ (Fin 3) =>
      ((Work.BoseKinLoc.indU ℓ u z : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ u ψ z : ℝ) : ℂ))
      = fun z => ((F z : ℝ) : ℂ) - (m : ℂ) * ((A z : ℝ) : ℂ) := by
    funext z
    rw [← hA, hQfree z]
    calc ((A z : ℝ) : ℂ) * (((ψ z - m : ℝ)) : ℂ)
        = ((A z : ℝ) : ℂ) * (((ψ z : ℝ) : ℂ) - ((m : ℝ) : ℂ)) := by rw [Complex.ofReal_sub]
      _ = ((A z : ℝ) : ℂ) * ((ψ z : ℝ) : ℂ) - ((A z : ℝ) : ℂ) * ((m : ℝ) : ℂ) := by ring
      _ = ((F z : ℝ) : ℂ) - (m : ℂ) * ((A z : ℝ) : ℂ) := by
            rw [show ((A z : ℝ) : ℂ) * ((ψ z : ℝ) : ℂ) = ((F z : ℝ) : ℂ) by
              rw [← Complex.ofReal_mul, hAaux z], mul_comm]
  have hnotC : ¬ AEStronglyMeasurable (fun z : EuclideanSpace ℝ (Fin 3) =>
      ((Work.BoseKinLoc.indU ℓ u z : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ u ψ z : ℝ) : ℂ)) volume := by
    intro hC
    have hAcomplex : AEStronglyMeasurable (fun z : EuclideanSpace ℝ (Fin 3) => ((A z : ℝ) : ℂ)) volume :=
      Complex.ofRealCLM.continuous.comp_aestronglyMeasurable hA_aesm
    have hCF : AEStronglyMeasurable (fun z : EuclideanSpace ℝ (Fin 3) => ((F z : ℝ) : ℂ)) volume := by
      have hfun : (fun z : EuclideanSpace ℝ (Fin 3) => ((F z : ℝ) : ℂ)) =
          fun z => ((Work.BoseKinLoc.indU ℓ u z : ℝ) : ℂ) *
              ((Work.BoseKinLoc.Qfree ℓ u ψ z : ℝ) : ℂ) + (m : ℂ) * ((A z : ℝ) : ℂ) := by
        funext z
        have hz := congrFun hCform z
        rw [hz]; ring
      rw [hfun]
      exact hC.add (hAcomplex.const_mul (m : ℂ))
    have hF_aesm : AEStronglyMeasurable F volume :=
      Complex.reCLM.continuous.comp_aestronglyMeasurable hCF
    exact h (by simpa using hF_aesm)
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin 3) =>
      (Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))))⁻¹) := by
    refine Continuous.inv₀ ?_ (fun y => hne y)
    fun_prop
  have hInt : ¬ Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) *
        (((Work.BoseKinLoc.indU ℓ u y : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ u ψ y : ℝ) : ℂ))) volume := by
    intro hI
    have h1 : AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin 3) =>
        (Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))))⁻¹ *
        (Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) *
          (((Work.BoseKinLoc.indU ℓ u y : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ u ψ y : ℝ) : ℂ)))) volume :=
      hcont.aestronglyMeasurable.mul hI.aestronglyMeasurable
    refine hnotC ?_
    have heq : (fun y : EuclideanSpace ℝ (Fin 3) =>
        (Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))))⁻¹ *
        (Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) *
          (((Work.BoseKinLoc.indU ℓ u y : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ u ψ y : ℝ) : ℂ))))
        = fun y : EuclideanSpace ℝ (Fin 3) =>
          ((Work.BoseKinLoc.indU ℓ u y : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ u ψ y : ℝ) : ℂ) := by
      funext y
      rw [inv_mul_cancel_left₀ (hne y)]
    rw [← heq]
    exact h1
  rw [Submission.BoseGases.kinFT]
  exact integral_undef hInt

end Work.BoseKinLoc.Momentum
