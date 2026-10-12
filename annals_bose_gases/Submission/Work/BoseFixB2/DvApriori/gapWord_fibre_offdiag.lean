import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.gapWord_fibre_bilinear_peel
import Submission.Work.BoseFixB2.DvApriori.gapWord_sub_eq_of_means_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.gapWord_fibre_offdiag`

The **off-diagonal fibre integral of FS `eq:DefT`'s second kinetic piece** `gapWord`:
for a slot `j` belonging to two *different* joint sector sets `S ≠ T`, the polarised
combination

    ∫_{abox n ℓ} θ₀(x_j) [ gapWord(fibre_j(E_SΦ + E_TΦ)(x)) − gapWord(fibre_j(E_SΦ − E_TΦ)(x)) ] d x

vanishes.

## The argument

Write `A = E_SΦ`, `B = E_TΦ`, `E_S = jointProj ℓ S Φ` the iterated slot projection
`∏_{i∈S}Q_i ∏_{i∉S}P_i` of FS §6.  Since `j ∈ S` and `j ∈ T`:

* **slot-`j` mean zero.**  `P_j E_SΦ = 0` (the corpus's `aP_blockOp_eq_zero`: the slot-`j`
  complement `Q_j` survives every commutation past the operators of the other slots), i.e.
  `∫_{acube ℓ} (E_SΦ)(update x j z) dz = 0` for every `x`; same for `T`.
* **polarisation.**  `gapWord` is `bℓ⁻²` times `gapBare`, and on functions with vanishing box
  mean `Q_0` acts as the identity, so
  `gapWord(ψ₁+ψ₂) − gapWord(ψ₁−ψ₂) = 4bℓ⁻² ∫_{acube ℓ} ψ₁ψ₂`
  (`gapWord_sub_eq_of_means_zero`).
* **peeling the slot.**  With `A, B` continuous, the double integral over the `j`-th coordinate
  collapses (`gapWord_fibre_bilinear_peel`):
  `∫_{abox n ℓ} ∫_{acube ℓ} A(update x j z)B(update x j z) dz dx = ℓ³ ∫_{abox n ℓ} A B`
  — the peeled slot contributes its volume `ℓ³` because the integrand does not depend on it.
* **orthogonality.**  `∫_{abox n ℓ} A B = 0` because the two joint sectors `S ≠ T` differ in
  some slot, hence `E_S, E_T` are orthogonal projections (`jointProj_orthogonal`).

The indicator `θ₀(x_j)` is `1` on `abox n ℓ` (`lamBox ℓ 0 = acube ℓ`), so it can be dropped.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `z ↦ Function.update x j z` is continuous in `z` (the other coordinates are frozen). -/
lemma continuous_update_const {n : ℕ} (j : Fin n) (x : Submission.BoseGases.X n) :
    Continuous fun z : EuclideanSpace ℝ (Fin 3) => Function.update x j z := by
  have h2 : Continuous fun p : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) =>
      Function.update p.1 j p.2 := continuous_update j
  exact h2.comp (continuous_const.prodMk continuous_id)

/-- **The slot-`j` mean of a sector projection vanishes when `j` lies in the sector.**

For `j ∈ S`, the fibre `z ↦ (E_SΦ)(update x j z)` of the joint sector projection has zero
mean over the centred cube `acube ℓ`: this is the pointwise form of the corpus's
`aP_blockOp_eq_zero` (`P_j E_S = 0`). -/
lemma integral_fibre_jointProj_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {S : Finset ℕ} (j : Fin n)
    (hjS : (j : ℕ) ∈ S) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ)
    (x : Submission.BoseGases.X n) :
    ∫ z in Submission.BoseGases.acube ℓ,
      (Work.BoseFixB2.jointProj ℓ S Φ) (Function.update x j z) = 0 := by
  have h := Work.BoseFixB2.Sector.aP_blockOp_eq_zero hℓ j.isLt hjS hΦ
  have hx := congrFun h x
  simp only [Submission.BoseGases.aP] at hx
  have hne : (1 / ℓ ^ 3 : ℝ) ≠ 0 := by positivity
  exact (mul_eq_zero.mp hx).resolve_left hne

theorem gapWord_fibre_offdiag {ℓ b : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {S T : Finset ℕ} (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n)
    (hjS : (j : ℕ) ∈ S) (hjT : (j : ℕ) ∈ T) (hST : S ≠ T) :
    (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
      (Work.BoseKinLoc.gapWord ℓ b 0
          (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
       - Work.BoseKinLoc.gapWord ℓ b 0
          (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x))) = 0 := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ m =>
    have hAc : Continuous (Work.BoseFixB2.jointProj ℓ S Φ) :=
      Work.BoseFixB2.Sector.jointProj_continuous hℓ S hΦ.continuous
    have hBc : Continuous (Work.BoseFixB2.jointProj ℓ T Φ) :=
      Work.BoseFixB2.Sector.jointProj_continuous hℓ T hΦ.continuous
    have hST' : S ∩ Finset.range (m + 1) ≠ T ∩ Finset.range (m + 1) := by
      rw [Finset.inter_eq_left.mpr hS, Finset.inter_eq_left.mpr hT]
      exact hST
    have horth : (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
        Work.BoseFixB2.jointProj ℓ S Φ x * Work.BoseFixB2.jointProj ℓ T Φ x) = 0 :=
      Work.BoseFixB2.Sector.jointProj_orthogonal hℓ hST' Φ Φ hΦ.continuous hΦ.continuous
    -- the pointwise polarisation identity
    have hpoint : ∀ x : Submission.BoseGases.X (m + 1),
        (Work.BoseKinLoc.gapWord ℓ b 0
            (Work.BoseKinLoc.fibre (m + 1) j
              (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
          - Work.BoseKinLoc.gapWord ℓ b 0
            (Work.BoseKinLoc.fibre (m + 1) j
              (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x))
        = (b * ℓ ^ (-2 : ℤ) * 4) * ∫ z in Submission.BoseGases.acube ℓ,
            (Work.BoseFixB2.jointProj ℓ S Φ) (Function.update x j z)
              * (Work.BoseFixB2.jointProj ℓ T Φ) (Function.update x j z) := by
      intro x
      have hfib1 : Work.BoseKinLoc.fibre (m + 1) j
            (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x
          = fun z : EuclideanSpace ℝ (Fin 3) =>
              (Work.BoseFixB2.jointProj ℓ S Φ) (Function.update x j z)
                + (Work.BoseFixB2.jointProj ℓ T Φ) (Function.update x j z) := by
        funext z
        simp [Work.BoseKinLoc.fibre, Pi.add_apply]
      have hfib2 : Work.BoseKinLoc.fibre (m + 1) j
            (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x
          = fun z : EuclideanSpace ℝ (Fin 3) =>
              (Work.BoseFixB2.jointProj ℓ S Φ) (Function.update x j z)
                - (Work.BoseFixB2.jointProj ℓ T Φ) (Function.update x j z) := by
        funext z
        simp [Work.BoseKinLoc.fibre, Pi.sub_apply]
      rw [hfib1, hfib2]
      have hmS : ∫ z in Submission.BoseGases.acube ℓ,
          (Work.BoseFixB2.jointProj ℓ S Φ) (Function.update x j z) = 0 :=
        integral_fibre_jointProj_eq_zero hℓ j hjS hΦ.continuous x
      have hmT : ∫ z in Submission.BoseGases.acube ℓ,
          (Work.BoseFixB2.jointProj ℓ T Φ) (Function.update x j z) = 0 :=
        integral_fibre_jointProj_eq_zero hℓ j hjT hΦ.continuous x
      have hc1 : Continuous fun z : EuclideanSpace ℝ (Fin 3) =>
          (Work.BoseFixB2.jointProj ℓ S Φ) (Function.update x j z) :=
        hAc.comp (continuous_update_const j x)
      have hc2 : Continuous fun z : EuclideanSpace ℝ (Fin 3) =>
          (Work.BoseFixB2.jointProj ℓ T Φ) (Function.update x j z) :=
        hBc.comp (continuous_update_const j x)
      exact gapWord_sub_eq_of_means_zero hℓ hc1 hc2 hmS hmT
    -- the global bilinear form of the bracket
    have hfun : (fun x : Submission.BoseGases.X (m + 1) =>
          (Work.BoseKinLoc.gapWord ℓ b 0
              (Work.BoseKinLoc.fibre (m + 1) j
                (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
            - Work.BoseKinLoc.gapWord ℓ b 0
              (Work.BoseKinLoc.fibre (m + 1) j
                (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x)))
        = fun x => (b * ℓ ^ (-2 : ℤ) * 4) * ∫ z in Submission.BoseGases.acube ℓ,
            (Work.BoseFixB2.jointProj ℓ S Φ) (Function.update x j z)
              * (Work.BoseFixB2.jointProj ℓ T Φ) (Function.update x j z) :=
      funext hpoint
    have hpeel : (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
          (b * ℓ ^ (-2 : ℤ) * 4) * ∫ z in Submission.BoseGases.acube ℓ,
            (Work.BoseFixB2.jointProj ℓ S Φ) (Function.update x j z)
              * (Work.BoseFixB2.jointProj ℓ T Φ) (Function.update x j z))
        = (b * ℓ ^ (-2 : ℤ) * 4) * ℓ ^ 3 * ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
            Work.BoseFixB2.jointProj ℓ S Φ x * Work.BoseFixB2.jointProj ℓ T Φ x :=
      gapWord_fibre_bilinear_peel hℓ j hAc hBc _
    -- the indicator θ₀(x_j) is one on the box
    have hind : (∫ x in Submission.BoseGases.abox (m + 1) ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
          (Work.BoseKinLoc.gapWord ℓ b 0
              (Work.BoseKinLoc.fibre (m + 1) j
                (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
            - Work.BoseKinLoc.gapWord ℓ b 0
              (Work.BoseKinLoc.fibre (m + 1) j
                (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x)))
        = ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
            (Work.BoseKinLoc.gapWord ℓ b 0
                (Work.BoseKinLoc.fibre (m + 1) j
                  (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
              - Work.BoseKinLoc.gapWord ℓ b 0
                (Work.BoseKinLoc.fibre (m + 1) j
                  (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x)) := by
      refine MeasureTheory.setIntegral_congr_fun
        (Submission.BoseGases.abox_measurable (m + 1) ℓ) ?_
      intro x hx
      beta_reduce
      have hmem : x j ∈ Work.BoseKinLoc.lamBox ℓ 0 := by
        rw [show Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ by
              ext y
              simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]]
        exact (Submission.BoseGases.mem_abox_iff (m + 1) ℓ x).mp hx j
      have h1 : Work.BoseKinLoc.indU ℓ 0 (x j) = 1 :=
        Set.indicator_of_mem hmem (fun _ => (1 : ℝ))
      rw [h1, one_mul]
    rw [hind, hfun, hpeel, horth]
    ring

end Work.BoseFixB2.DvApriori
