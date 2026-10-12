import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_a0A2QJointExpansionFib
import Submission.Work.BoseFixB1.SectorAux.boxCompTOrthMeas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.SectorAux.integral_child_sub_kappa_g`

The per-edge correction of the *uncentred* hopping expansion, for a state `Φ` that is only
**measurable and bounded on the box** (`Work.BoseFixB1S.GoodState`) rather than continuous:

    ∫_{abox N ℓ} ψ_{c_i(p)}·(fib(xᵢ) − κ)·ψ_p
      = ∫_{abox N ℓ} ψ_{c_i(p)}·fib(xᵢ)·ψ_p                    (p ∈ hopPairSet i)

where `ψ_{S,T} = boxCompT volA A S T Φ` and `c_i(p) = (p.1.erase i, insert i p.2)`.

## Math

The two sides differ by `κ·∫ ψ_{c_i(p)}·ψ_p`, and that pairing vanishes by the orthogonality of
the three-way box components: the slot `i` is a `P`-slot of the parent `p = (p.1, p.2)`
(`p ∈ hopPairSet i`) and a `Q`-slot of the child (`i ∈ insert i p.2`, `i ∉ p.1.erase i`), so the
`P`-slot case `orth_of_mem_S` applies.  This is exactly the argument of
`Work.BoseFixB1S.integral_child_sub_kappa`; the only change is that continuity of `Φ` is replaced
by `Measurable Φ` plus a bound on `abox N ℓ`, using the `GoodState` form of the orthogonality
(`Work.BoseFixB1.SectorAux.orth_of_mem_S_good`, from `boxCompTOrthMeas`).

The boundedness on the box gives the integrability of the two pieces (`GoodState` components are
bounded on the box via `goodState_boxCompT`, and `integrableOn_abox_of_bound_aesm` /
`integrableOn_mul_of_bound`), which is what `integral_sub` and `integral_const_mul` need.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1.SectorAux

open Submission.BoseGases

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The child component is orthogonal to its parent (`GoodState` form) -/

/-- The joint component of the child `c_i(p) = (p.1.erase i, insert i p.2)` is orthogonal to the
component of the parent `p = (p.1, p.2)`, for a measurable, box-bounded state `Φ`: the slot `i`
is a `Q`-slot of the child and a `P`-slot of the parent, so `orth_of_mem_S` applies. -/
theorem hopChild_orth_good {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Work.BoseFixB1S.GoodState ℓ Φ)
    {i : Fin N} {p : Finset (Fin N) × Finset (Fin N)}
    (hp : p ∈ Work.BoseFixB1S.hopPairSet i) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x
          * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) = 0 := by
  have hpi : i ∈ p.1 := (Work.BoseFixB1S.mem_hopPairSet.mp hp).2
  have h1 : (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
          * Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x) = 0 :=
    orth_of_mem_S_good (S := p.1) (T := p.2) (S' := p.1.erase i) (T' := insert i p.2)
      (j := i) hℓ hvol hA hvolA hAc hpi (Finset.notMem_erase i p.1) hΦ hΦ
  have h2 : (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x
          * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
          * Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x := by
    refine MeasureTheory.setIntegral_congr_fun
      (Submission.BoseGases.abox_measurable N ℓ) (fun x _ => ?_)
    ring
  rw [h2, h1]

/-! ## 2. The requested theorem -/

theorem integral_child_sub_kappa_g {N : ℕ} {ℓ volA κ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hfibm : MeasureTheory.AEStronglyMeasurable fib
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {Cf : ℝ} (hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ Cf)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {Cb : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb)
    {i : Fin N} {p : Finset (Fin N) × Finset (Fin N)} (hp : p ∈ Work.BoseFixB1S.hopPairSet i) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x
          * (fib (x i) - κ) * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x
          * fib (x i) * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
  have hΦG : Work.BoseFixB1S.GoodState ℓ Φ := ⟨hΦm, Cb, hΦb⟩
  obtain ⟨hm1, C1, hb1⟩ :=
    Work.BoseFixB1S.goodState_boxCompT hℓ hvol hA hvolA hAc (p.1.erase i) (insert i p.2) hΦG
  obtain ⟨hm2, C2, hb2⟩ :=
    Work.BoseFixB1S.goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦG
  -- integrability of the two pieces
  have hI1 : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x
          * fib (x i) * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
    refine Work.BoseFixB1S.integrableOn_abox_of_bound_aesm (C := max C1 0 * max Cf 0 * max C2 0)
      hℓ ?_ ?_
    · exact ((hm1.aestronglyMeasurable.mul
        (Submission.BoseGases.aem_comp_coord' i hfibm)).mul hm2.aestronglyMeasurable)
    · intro x hx
      have hxi : x i ∈ Submission.BoseGases.acube ℓ :=
        (Submission.BoseGases.mem_abox_iff N ℓ x).mp hx i
      have h1 : |Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x|
          ≤ max C1 0 := le_trans (hb1 x hx) (le_max_left _ _)
      have h2 : |fib (x i)| ≤ max Cf 0 := le_trans (hfibb (x i) hxi) (le_max_left _ _)
      have h3 : |Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x| ≤ max C2 0 :=
        le_trans (hb2 x hx) (le_max_left _ _)
      have h10 : (0 : ℝ) ≤ max C1 0 := le_max_right _ _
      have h20 : (0 : ℝ) ≤ max Cf 0 := le_max_right _ _
      have h30 : (0 : ℝ) ≤ max C2 0 := le_max_right _ _
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) h10) h3 (abs_nonneg _)
        (mul_nonneg h10 h20)
  have hI2 : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        κ * (Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x
          * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    (Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hm1 hm2 hb1 hb2).const_mul κ
  -- the two integrands differ pointwise by `κ·ψ_{c_i(p)}·ψ_p`
  have hpt : ∀ x : Submission.BoseGases.X N,
      Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x
          * (fib (x i) - κ) * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
        = (Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x
              * fib (x i) * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
            - κ * (Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x
              * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x)) := by
    intro x
    ring
  rw [MeasureTheory.setIntegral_congr_fun
    (Submission.BoseGases.abox_measurable N ℓ) (fun x _ => hpt x)]
  rw [MeasureTheory.integral_sub hI1 hI2, MeasureTheory.integral_const_mul,
    hopChild_orth_good hℓ hvol hA hvolA hAc hΦG hp, mul_zero, sub_zero]

end Work.BoseFixB1.SectorAux
