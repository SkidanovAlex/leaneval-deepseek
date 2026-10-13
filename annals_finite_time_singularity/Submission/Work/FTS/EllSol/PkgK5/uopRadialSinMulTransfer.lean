import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.PkgK5.radialHkNorm_le_sinMul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# `HkMem` transfers from `Λ z · sin(2θ)` to the radial profile `Λ`

Given a radial profile `Λ`, smooth on `(0,∞)`, the membership
`HkMem α k (fun z θ => Λ z * Real.sin (2 * θ))` implies `HkMem α k (fun z θ => Λ z)`.

The point is that the *pure radial* slots of `HkIntegrand α k (Λ · sin 2·)` are
`(D_z^i Λ)² · w² · sin(2θ)^{2-η}`, whose `θ`-integral is `(D_z^i Λ)² w² · A_{2-η}` with
`A_{2-η} = ∫_θ sin(2θ)^{2-η} > 0` (as `2 - η = 1.01 > 0`), and the mixed slots are
non-negative.  Hence, at every `z > 0`,

`Φ z := ∑_{i ≤ k} (D_z^i Λ(z) · w(z))²  ≤  ((k+1)/A_{2-η}) · ∫_θ HkIntegrand α k (Λ·sin 2·) z θ`,

so the integrability of the outer integral (an immediate consequence of `HkMem` of the
`sin 2θ`-multiple) makes `Φ` integrable; and the `θ`-integral of the `HkIntegrand` of `Λ`
itself is `Φ z · A_η` with `A_η = ∫_θ sin(2θ)^{-η}`, again finite.

Note that no hypothesis at all is made on `α`: the argument only ever uses *one* slot of a
sum of non-negative terms, never the evaluation of the mixed slots.
-/

namespace Work.FTS.EllSol.PkgK5

namespace Radial

/-- `D_z^j` of the radial function `(z,θ) ↦ Λ z` equals the one-variable iterate `RIter j Λ`,
also at `z = 0`.  This is the `0 ≤ z` version of `DzIter_radial`: for `j ≥ 1` both sides
vanish at `z = 0` because `D_z` carries a factor `z` (resp. `RIter` a factor `z`). -/
theorem DzIter_radial_nonneg (Λ : ℝ → ℝ) (j : ℕ) {z : ℝ} (hz : 0 ≤ z) (θ : ℝ) :
    Work.Spaces.DzIter j (fun z θ => Λ z) z θ = RIter j Λ z := by
  rcases eq_or_lt_of_le hz with h | h
  · subst h
    cases j with
    | zero => rfl
    | succ m =>
        simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, RIter_succ]
        ring
  · exact DzIter_radial Λ j h θ

/-- The `H^k`-integrand of a radial profile, evaluated on `Iz` (i.e. also at `z = 0`). -/
theorem HkIntegrand_radial_nonneg (α : ℝ) (k : ℕ) (Λ : ℝ → ℝ)
    (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) (z θ : ℝ) (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => Λ z) z θ
      = Phi k Λ z * Real.sin (2 * θ) ^ (-Work.Spaces.eta) := by
  have heta : Work.Spaces.eta ≠ 0 := by norm_num [Work.Spaces.eta]
  rw [Work.Spaces.HkIntegrand]
  have hzsum : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i (fun z θ => Λ z) z θ
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      = Phi k Λ z * Real.sin (2 * θ) ^ (-Work.Spaces.eta) := by
    rw [Phi, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [DzIter_radial_nonneg Λ i hz θ,
      Work.Spaces.sq_mul_div_rpow (RIter i Λ z) (Work.Spaces.w z) (Real.sin (2 * θ))
        Work.Spaces.eta (sin_two_nonneg hθ) heta]
    ring
  have hmix : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i (fun z θ => Λ z) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero (fun i hi => Finset.sum_eq_zero (fun j hj => ?_))
    split_ifs with h
    · rw [mixed_radial_zero Λ j i h.1 z θ]; ring
    · rfl
  rw [hzsum, hmix, add_zero]

/-- `A_{2-η} = ∫_θ sin(2θ)^{2-η} > 0`. -/
theorem Aeta2_pos : 0 < Aeta2 := by
  show 0 < ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (2 - Work.Spaces.eta)
  exact sin_rpow_pos (by norm_num [Work.Spaces.eta])
    (by norm_num [Work.Spaces.eta] : (2 : ℝ) - Work.Spaces.eta ≤ 2)

/-- A single *pure radial* slot of the `H^k`-integrand of `(z,θ) ↦ Λ z · sin(2θ)`. -/
theorem slot_pointwise (α : ℝ) (k i : ℕ) (Λ : ℝ → ℝ)
    (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) {z : ℝ} (hz : 0 < z)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DzIter i (fun z θ => Λ z * Real.sin (2 * θ)) z θ
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      = (RIter i Λ z * Work.Spaces.w z) ^ 2
          * Real.sin (2 * θ) ^ (2 - Work.Spaces.eta) := by
  have heta : Work.Spaces.eta ≠ 2 := by norm_num [Work.Spaces.eta]
  have heta0 : Work.Spaces.eta ≠ 0 := by norm_num [Work.Spaces.eta]
  have hS : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  rw [DzIter_mul_theta Λ hΛ (fun θ : ℝ => Real.sin (2 * θ)) i hz θ,
    Work.Spaces.sq_mul_div_rpow (RIter i Λ z * Real.sin (2 * θ)) (Work.Spaces.w z)
      (Real.sin (2 * θ)) Work.Spaces.eta hS heta0]
  calc (RIter i Λ z * Real.sin (2 * θ)) ^ 2 * (Work.Spaces.w z) ^ 2
        * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
      = (RIter i Λ z * Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)) := by ring
    _ = (RIter i Λ z * Work.Spaces.w z) ^ 2
          * Real.sin (2 * θ) ^ (2 - Work.Spaces.eta) := by
        rw [sq_mul_rpow_neg Work.Spaces.eta heta hS]

/-- **The `i`-th pure radial slot bounds the `i`-th diagonal weight square.** -/
theorem slot_le_thetaIntegral (α : ℝ) (k i : ℕ) (Λ : ℝ → ℝ) (hi : i ≤ k)
    (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) {z : ℝ} (hz : 0 < z)
    (hint : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k
      (fun z θ => Λ z * Real.sin (2 * θ)) z θ) Work.Spaces.Iθ) :
    (RIter i Λ z * Work.Spaces.w z) ^ 2 * Aeta2
      ≤ ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => Λ z * Real.sin (2 * θ)) z θ := by
  set slot : ℝ → ℝ := fun θ => (Work.Spaces.DzIter i (fun z θ => Λ z * Real.sin (2 * θ)) z θ
      * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 with hslot
  have hslotInt : (∫ θ in Work.Spaces.Iθ, slot θ)
      = (RIter i Λ z * Work.Spaces.w z) ^ 2 * Aeta2 := by
    rw [show (∫ θ in Work.Spaces.Iθ, slot θ)
        = ∫ θ in Work.Spaces.Iθ,
            (RIter i Λ z * Work.Spaces.w z) ^ 2
              * Real.sin (2 * θ) ^ (2 - Work.Spaces.eta) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        (fun θ hθ => by rw [hslot]; exact slot_pointwise α k i Λ hΛ hz hθ)]
    rw [MeasureTheory.integral_const_mul]
    rfl
  have hmono : (∫ θ in Work.Spaces.Iθ, slot θ)
      ≤ ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => Λ z * Real.sin (2 * θ)) z θ := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun θ => sq_nonneg _)) hint ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    have hmem : i ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
    have hnonneg : ∀ m ∈ Finset.range (k + 1),
        0 ≤ (Work.Spaces.DzIter m (fun z θ => Λ z * Real.sin (2 * θ)) z θ
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 :=
      fun m _ => sq_nonneg _
    have h1 : (Work.Spaces.DzIter i (fun z θ => Λ z * Real.sin (2 * θ)) z θ
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ ∑ m ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter m (fun z θ => Λ z * Real.sin (2 * θ)) z θ
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 :=
      Finset.single_le_sum hnonneg hmem
    have h2 : 0 ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => Λ z * Real.sin (2 * θ)) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
        split_ifs with h
        · exact sq_nonneg _
        · exact le_refl 0
    rw [hslot, Work.Spaces.HkIntegrand]
    linarith
  rw [← hslotInt]
  exact hmono

/-- **The diagonal weight sum is controlled by the `θ`-integral of the `H^k`-integrand of
the `sin 2θ`-multiple.** -/
theorem Phi_le_thetaIntegral (α : ℝ) (k : ℕ) (Λ : ℝ → ℝ)
    (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) {z : ℝ} (hz : 0 < z)
    (hint : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k
      (fun z θ => Λ z * Real.sin (2 * θ)) z θ) Work.Spaces.Iθ) :
    Phi k Λ z ≤ ((k : ℝ) + 1) / Aeta2 *
      (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => Λ z * Real.sin (2 * θ)) z θ) := by
  have hA := Aeta2_pos
  have hstep : ∀ i ∈ Finset.range (k + 1), (RIter i Λ z * Work.Spaces.w z) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (fun z θ => Λ z * Real.sin (2 * θ)) z θ) / Aeta2 := by
    intro i hi
    exact (le_div_iff₀ hA).mpr
      (slot_le_thetaIntegral α k i Λ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hΛ hz hint)
  calc Phi k Λ z = ∑ i ∈ Finset.range (k + 1), (RIter i Λ z * Work.Spaces.w z) ^ 2 := rfl
    _ ≤ ∑ _i ∈ Finset.range (k + 1),
          (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (fun z θ => Λ z * Real.sin (2 * θ)) z θ) / Aeta2 :=
        Finset.sum_le_sum hstep
    _ = (k + 1 : ℝ) * ((∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (fun z θ => Λ z * Real.sin (2 * θ)) z θ) / Aeta2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        simp only [Nat.cast_add, Nat.cast_one]
    _ = ((k : ℝ) + 1) / Aeta2 * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (fun z θ => Λ z * Real.sin (2 * θ)) z θ) := by
        ring

/-- **`Φ` is integrable on `(0,∞)` as soon as the `sin 2θ`-multiple is in `H^k`.** -/
theorem Phi_integrable (α : ℝ) (k : ℕ) (Λ : ℝ → ℝ)
    (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0))
    (hsin : Work.Spaces.HkMem α k (fun z θ => Λ z * Real.sin (2 * θ))) :
    Integrable (fun z => Phi k Λ z) (volume.restrict (Set.Ioi 0)) := by
  refine MeasureTheory.Integrable.mono'
    ((hsin.2.mono_set Set.Ioi_subset_Ici_self).const_mul (((k : ℝ) + 1) / Aeta2))
    ((continuousOn_Phi k Λ hΛ).aestronglyMeasurable isOpen_Ioi.measurableSet) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict isOpen_Ioi.measurableSet] with z hz
  rw [Real.norm_of_nonneg (Phi_nonneg k Λ z)]
  exact Phi_le_thetaIntegral α k Λ hΛ hz (hsin.1 z (Set.Ioi_subset_Ici_self hz))

end Radial

theorem uopRadialSinMulTransfer {α : ℝ} {k : ℕ} {Λ : ℝ → ℝ}
    (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0))
    (hsin : Work.Spaces.HkMem α k (fun z θ => Λ z * Real.sin (2 * θ))) :
    Work.Spaces.HkMem α k (fun z θ => Λ z) := by
  have hpi := Radial.Phi_integrable α k Λ hΛ hsin
  refine ⟨?_, ?_⟩
  · -- `θ`-integrability at every `z ∈ Iz`
    intro z hz
    have h1 : -1 < -Work.Spaces.eta := by norm_num [Work.Spaces.eta]
    have h2 : -Work.Spaces.eta ≤ 2 := by norm_num [Work.Spaces.eta]
    refine ((Radial.integrable_sin_rpow h1 h2).const_mul (Radial.Phi k Λ z)).congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    show Radial.Phi k Λ z * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
      = Work.Spaces.HkIntegrand α k (fun z θ => Λ z) z θ
    exact (Radial.HkIntegrand_radial_nonneg α k Λ hΛ z θ hz hθ).symm
  · -- integrability of the outer integral
    show Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => Λ z) z θ) (volume.restrict Work.Spaces.Iz)
    rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
    refine (hpi.mul_const Radial.Aeta).congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem isOpen_Ioi.measurableSet (fun z hz => ?_)
    exact (Radial.thetaIntegral_radial α k Λ hΛ hz).symm

end Work.FTS.EllSol.PkgK5
