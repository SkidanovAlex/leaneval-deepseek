import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyLeft
import Submission.Work.FTS.StrongPersist.SupOpenH2Z
import Submission.Work.FTS_EllLimOK.EnergyGap
import Submission.Work.FTS_EllLimOK.PkgJets.cosTailB
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.uopRadialSinMulTransfer =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.sliceBoundEta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.H2.DivQ

open MeasureTheory Set Filter
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The `i = 0` (`η`-weighted) per-slice bound, by a three-region sweep

The target `sliceBoundEta` is proved by splitting `Iθ = [0,π/2]` into the *near* region
`(0,π/8]`, the *middle* region `(π/8,3π/8)` and the *far* region `(3π/8,π/2)`:

* near: substitute `x = sin 2θ` (`thetaOf`) and apply the sharp weighted Hardy bound
  `hardyA_le_W` at level `0` with `γ = η` — here in the form `xEta_integrable`;
* middle: `sin(2θ) ≥ 1/2` there, so the pointwise Poincaré bound `honestPoincarePoint` suffices;
* far: mirror image of the near region under `θ ↦ π/2 - θ`.

All constants are existential. -/

/-- The left-hand integrand `(h θ / sin(2θ))² sin(2θ)^{-η}` of the `i = 0` slice bound. -/
abbrev etaLHS (h : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (h θ / Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The honest `η`-data `∫_{Iθ} (∂_θh)² sin(2θ)^{-η}` of a slice. -/
def etaData (h : ℝ → ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, PsiEta h θ

lemma etaData_nonneg (h : ℝ → ℝ) : 0 ≤ etaData h :=
  MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ => psiEta_nonneg h θ hθ

/-! ### The (existential) constant of the sharp Hardy bound `hardyA_le_W` -/

/-- The constant produced by `hardyA_le_W`. -/
private noncomputable def hardyC : ℝ := Classical.choose hardyA_le_W

private lemma hardyC_pos : 0 < hardyC := (Classical.choose_spec hardyA_le_W).1

/-- The sharp weighted Hardy bound of `hardyA_le_W`, with its constant named. -/
private lemma hardyC_bound (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁))
    (hf0 : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hB : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * iteratedDeriv (k + 1) f x ^ 2) (Set.Ioc 0 x₁)) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * (k : ℝ) - γ)
        * iteratedDeriv k (fun y : ℝ => f y / y) x ^ 2) (Set.Ioc 0 x₁) ∧
      (∫ x in (0 : ℝ)..x₁, x ^ (2 * (k : ℝ) - γ)
          * iteratedDeriv k (fun y : ℝ => f y / y) x ^ 2)
        ≤ hardyC / (1 + γ) ^ 2 *
          (∫ x in (0 : ℝ)..x₁, x ^ (2 * (k : ℝ) - γ) * iteratedDeriv (k + 1) f x ^ 2) :=
  (Classical.choose_spec hardyA_le_W).2 k γ x₁ hx₁ hγ f hf hf0 hB

/-- The constant of the near-region estimate. -/
private noncomputable def etaNear : ℝ := hardyC / (1 + Work.Spaces.eta) ^ 2

private lemma etaNear_pos : 0 < etaNear := by
  rw [etaNear]
  exact div_pos hardyC_pos (pow_pos (by linarith [Work.Spaces.eta_pos]) 2)

/-! ### (I) The near region `(0, π/8]` -/

/-- `θ(sin 2y) = y` for `y ∈ [0, π/8]`. -/
private lemma thetaOf_sin_two_near {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ Real.pi / 8) :
    thetaOf (Real.sin (2 * y)) = y := by
  rw [thetaOf, Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  ring

/-- The change of variables `x = sin(2θ)` on a sub-interval of `(0, π/8]`. -/
private lemma integral_thetaOf_near {y x : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x)
    (hx : x ≤ Real.pi / 8) (g : ℝ → ℝ) :
    (∫ t in y..x, g t)
      = ∫ u in Real.sin (2 * y)..Real.sin (2 * x), g (thetaOf u) * (1 / (2 * kappa u)) := by
  have hy2 : -(Real.pi / 2) ≤ 2 * y := by linarith [Real.pi_pos]
  have hx2 : 2 * x ≤ Real.pi / 2 := by linarith [Real.pi_pos, hx]
  have hsinle : Real.sin (2 * y) ≤ Real.sin (2 * x) := by
    rcases lt_or_eq_of_le hyx with hlt | heq
    · have hmem_y : (2 * y : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨hy2, by linarith [Real.pi_pos]⟩
      have hmem_x : (2 * x : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [Real.pi_pos], hx2⟩
      exact le_of_lt (Real.strictMonoOn_sin hmem_y hmem_x (by linarith))
    · rw [heq]
  have hy0' : 0 ≤ Real.sin (2 * y) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hx1' : Real.sin (2 * x) ≤ xNear := by
    have h4mem : (Real.pi / 4 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hxmem : (2 * x : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], hx2⟩
    have h := Real.strictMonoOn_sin.monotoneOn hxmem h4mem (by linarith [hx])
    simpa [xNear, Real.sin_pi_div_four] using h
  have hmem : ∀ u ∈ Set.uIcc (Real.sin (2 * y)) (Real.sin (2 * x)), u ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro u hu
    rw [Set.uIcc_of_le hsinle] at hu
    exact ⟨by linarith [hu.1, hy0'], by linarith [hu.2, hx1', xNear_lt]⟩
  have hder : ∀ u ∈ Set.Ioo (min (Real.sin (2 * y)) (Real.sin (2 * x)))
      (max (Real.sin (2 * y)) (Real.sin (2 * x))),
      HasDerivAt thetaOf (1 / (2 * kappa u)) u := by
    intro u hu
    rw [min_eq_left hsinle, max_eq_right hsinle] at hu
    exact hasDerivAt_thetaOf_nr
      (hmem u (by rw [Set.uIcc_of_le hsinle]; exact ⟨hu.1.le, hu.2.le⟩))
  have hnn : ∀ u ∈ Set.Ioo (min (Real.sin (2 * y)) (Real.sin (2 * x)))
      (max (Real.sin (2 * y)) (Real.sin (2 * x))), 0 ≤ 1 / (2 * kappa u) := by
    intro u hu
    rw [min_eq_left hsinle, max_eq_right hsinle] at hu
    have h2k : 1 ≤ 2 * kappa u :=
      two_kappa_ge_one ⟨le_of_lt (lt_of_le_of_lt hy0' hu.1), le_trans hu.2.le hx1'⟩
    exact div_nonneg zero_le_one (le_trans zero_le_one h2k)
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := Real.sin (2 * y)) (b := Real.sin (2 * x)) (f := thetaOf)
    (f' := fun u : ℝ => 1 / (2 * kappa u)) (g := g)
    ((Real.continuous_arcsin.div_const 2).continuousOn) hder hnn
  rw [thetaOf_sin_two_near hy (le_trans hyx hx), thetaOf_sin_two_near (le_trans hy hyx) hx]
    at hsub
  simpa only [Function.comp_apply] using hsub.symm

/-- `x^{-η}(∂_x(sliceX h) x)²`, the `x`-side form of the pullback of the near integrand. -/
private abbrev xEta (h : ℝ → ℝ) : ℝ → ℝ :=
  fun x => x ^ (-(Work.Spaces.eta)) * (sliceX h x / x) ^ 2

/-- The `x`-pullback of the left-hand integrand agrees with `xEta` on `(0,x₁]`. -/
private lemma pullback_ident {h : ℝ → ℝ} {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ xNear) :
    etaLHS h (thetaOf u) * (1 / (2 * kappa u)) = xEta h u * (1 / (2 * kappa u)) := by
  have hs : Real.sin (2 * thetaOf u) = u := sin_two_thetaOf_Icc_nr u ⟨hu0.le, hu1⟩
  simp only [etaLHS, xEta, hs, sliceX]
  ring

/-- `x^{-η}(∂_x(sliceX h) x)²` is integrable on the near interval. -/
private lemma etaPiece_integrable {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hDenη : MeasureTheory.IntegrableOn (PsiEta h) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2)
      (Set.Ioo 0 xNear) := by
  have hsub : MeasureTheory.IntegrableOn (SubEta h) (Set.Ioo 0 xNear) :=
    subEta_integrable hDenη
  have hdcont : ContinuousOn (deriv (sliceX h)) (Set.Ioo 0 xNear) := by
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (sliceX h)) (Set.Ioo 0 xNear) :=
      (contDiffOn_sliceX hsm).deriv_of_isOpen isOpen_Ioo (by simp)
    exact h1.continuousOn
  have hcont : ContinuousOn
      (fun x : ℝ => x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2)
      (Set.Ioo 0 xNear) :=
    (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))).mul (hdcont.pow 2)
  refine hsub.mono_nonneg (hcont.aestronglyMeasurable measurableSet_Ioo) ?_ ?_
  · exact (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx =>
      mul_nonneg (Real.rpow_nonneg hx.1.le _) (sq_nonneg _))
  · exact (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx =>
      etaPiece_le_subEta hsm hx)

/-- The integral of `x^{-η}(∂_x(sliceX h) x)²` is at most the `η`-data. -/
private lemma etaPiece_le_data {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hDenη : MeasureTheory.IntegrableOn (PsiEta h) Work.Spaces.Iθ) :
    (∫ x in (0 : ℝ)..xNear, x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2)
      ≤ etaData h := by
  have hIoo : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2)
      (Set.Ioo 0 xNear) := etaPiece_integrable hsm hDenη
  have hsubIoo : MeasureTheory.IntegrableOn (SubEta h) (Set.Ioo 0 xNear) :=
    subEta_integrable hDenη
  have hmono : (∫ x in Set.Ioo (0 : ℝ) xNear,
        x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2)
      ≤ ∫ x in Set.Ioo (0 : ℝ) xNear, SubEta h x :=
    integral_mono_ae hIoo hsubIoo ((ae_restrict_iff' measurableSet_Ioo).mpr
      (Eventually.of_forall fun x hx => etaPiece_le_subEta hsm hx))
  have hsub : (∫ x in Set.Ioo (0 : ℝ) xNear, SubEta h x) ≤ etaData h := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo (f := SubEta h) (x := (0 : ℝ))
        (y := xNear),
      ← intervalIntegral.integral_of_le xNear_pos.le]
    exact (thetaOfSubst (Ψ := PsiEta h) hDenη (psiEta_nonneg h)).2
  calc (∫ x in (0 : ℝ)..xNear, x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2)
      = ∫ x in Set.Ioc (0 : ℝ) xNear,
          x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2 :=
        intervalIntegral.integral_of_le xNear_pos.le
    _ = ∫ x in Set.Ioo (0 : ℝ) xNear,
          x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2 :=
        MeasureTheory.integral_Ioc_eq_integral_Ioo
    _ ≤ ∫ x in Set.Ioo (0 : ℝ) xNear, SubEta h x := hmono
    _ ≤ etaData h := hsub

/-- **The sharp weighted Hardy bound of `hardyA_le_W` in `x`-form.**  `xEta` is integrable on
`(0,x₁)` and its integral is at most `etaNear` times the `η`-data of the slice. -/
private lemma xEta_integrable {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hDenη : MeasureTheory.IntegrableOn (PsiEta h) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (xEta h) (Set.Ioc 0 xNear) ∧
      (∫ x in (0 : ℝ)..xNear, xEta h x) ≤ etaNear * etaData h := by
  have hη1 : -1 < Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
  have hp : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2)
      (Set.Ioc 0 xNear) :=
    (etaPiece_integrable hsm hDenη).congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hp_le : (∫ x in (0 : ℝ)..xNear,
        x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2) ≤ etaData h :=
    etaPiece_le_data hsm hDenη
  have hW : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * ((0 : ℕ) : ℝ) - Work.Spaces.eta)
        * iteratedDeriv (0 + 1) (sliceX h) x ^ 2) (Set.Ioc 0 xNear) := by
    simpa [iteratedDeriv_one] using hp
  have hH0 := hardyC_bound 0 Work.Spaces.eta xNear xNear_pos hη1 (sliceX h)
    (contDiffOn_sliceX_Ioc_nr hsm) (tendsto_sliceX_nr h0) hW
  have hInt : MeasureTheory.IntegrableOn (xEta h) (Set.Ioc 0 xNear) := by
    have h1 := hH0.1
    simp only [iteratedDeriv_zero, Nat.cast_zero, mul_zero, zero_sub] at h1
    exact h1
  have hle : (∫ x in (0 : ℝ)..xNear, xEta h x) ≤ etaNear * etaData h := by
    have h1 := hH0.2
    simp only [iteratedDeriv_zero, iteratedDeriv_one, zero_add, Nat.cast_zero, mul_zero, zero_sub]
      at h1
    refine h1.trans ?_
    rw [etaNear]
    exact mul_le_mul_of_nonneg_left hp_le
      (le_of_lt (div_pos hardyC_pos (pow_pos (by linarith [Work.Spaces.eta_pos]) 2)))
  exact ⟨hInt, hle⟩

/-- The Jacobian `1/(2κ)` is continuous on the near interval. -/
private lemma continuousOn_inv_two_kappa {a : ℝ} (ha : a ≤ xNear) :
    ContinuousOn (fun u : ℝ => 1 / (2 * kappa u)) (Set.Ioc 0 a) := by
  have hκ : Continuous kappa := by
    unfold kappa thetaOf
    fun_prop
  intro u hu
  have h2k : 1 ≤ 2 * kappa u := two_kappa_ge_one ⟨hu.1.le, le_trans hu.2 ha⟩
  have hg : ContinuousAt (fun u : ℝ => 2 * kappa u) u :=
    continuousAt_const.mul hκ.continuousAt
  exact (continuousAt_const.div hg (by linarith)).continuousWithinAt

/-- The truncated integrals of the left-hand integrand on the near region. -/
private lemma near_trunc_bound {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hDenη : MeasureTheory.IntegrableOn (PsiEta h) Work.Spaces.Iθ) :
    ∀ b : ℝ, 0 < b → b ≤ Real.pi / 8 →
      (∫ t in (0 : ℝ)..b, etaLHS h t) ≤ etaNear * etaData h := by
  intro b hb0 hb8
  obtain ⟨hGint, hGle⟩ := xEta_integrable hsm h0 hDenη
  have hsinb_pos : 0 < Real.sin (2 * b) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos, hb8])
  have hsinb_le : Real.sin (2 * b) ≤ xNear := by
    have h4mem : (Real.pi / 4 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hbmem : (2 * b : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos, hb8]⟩
    have h := Real.strictMonoOn_sin.monotoneOn hbmem h4mem (by linarith [hb8])
    simpa [xNear, Real.sin_pi_div_four] using h
  -- the substitution
  have hid := integral_thetaOf_near (le_refl (0 : ℝ)) hb0.le hb8 (etaLHS h)
  simp only [mul_zero, Real.sin_zero] at hid
  -- the pullback agrees with `xEta`
  have hEq : (∫ u in (0 : ℝ)..Real.sin (2 * b),
        etaLHS h (thetaOf u) * (1 / (2 * kappa u)))
      = ∫ u in (0 : ℝ)..Real.sin (2 * b), xEta h u * (1 / (2 * kappa u)) := by
    refine intervalIntegral.integral_congr_ae_restrict ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with u hu
    rw [Set.uIoc_of_le hsinb_pos.le] at hu
    exact pullback_ident hu.1 (le_trans hu.2 hsinb_le)
  -- the Jacobian is `≤ 1`
  have hGsub : MeasureTheory.IntegrableOn (xEta h) (Set.Ioc 0 (Real.sin (2 * b))) :=
    hGint.mono_set fun u hu => ⟨hu.1, le_trans hu.2 hsinb_le⟩
  have hc : ContinuousOn (fun u : ℝ => 1 / (2 * kappa u)) (Set.Ioc 0 (Real.sin (2 * b))) :=
    continuousOn_inv_two_kappa hsinb_le
  have hP : MeasureTheory.IntegrableOn
      (fun u : ℝ => xEta h u * (1 / (2 * kappa u))) (Set.Ioc 0 (Real.sin (2 * b))) :=
    hGsub.mono_nonneg
      (hGsub.aestronglyMeasurable.mul (hc.aestronglyMeasurable measurableSet_Ioc))
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu =>
        mul_nonneg (mul_nonneg (Real.rpow_nonneg hu.1.le _) (sq_nonneg _))
          (div_nonneg zero_le_one (le_trans zero_le_one
            (two_kappa_ge_one ⟨hu.1.le, le_trans hu.2 hsinb_le⟩)))))
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu => by
        have hxnn : 0 ≤ xEta h u :=
          mul_nonneg (Real.rpow_nonneg hu.1.le _) (sq_nonneg _)
        have h2k : 1 ≤ 2 * kappa u := two_kappa_ge_one ⟨hu.1.le, le_trans hu.2 hsinb_le⟩
        have hc1 : 1 / (2 * kappa u) ≤ 1 := by
          rw [div_le_one (by linarith)]; linarith
        calc xEta h u * (1 / (2 * kappa u)) ≤ xEta h u * 1 :=
              mul_le_mul_of_nonneg_left hc1 hxnn
          _ = xEta h u := mul_one _))
  have hstep1 : (∫ u in (0 : ℝ)..Real.sin (2 * b), xEta h u * (1 / (2 * kappa u)))
      ≤ ∫ u in (0 : ℝ)..Real.sin (2 * b), xEta h u := by
    rw [intervalIntegral.integral_of_le hsinb_pos.le,
      intervalIntegral.integral_of_le hsinb_pos.le]
    exact integral_mono_ae hP hGsub ((ae_restrict_iff' measurableSet_Ioc).mpr
      (Eventually.of_forall fun u hu => by
        have hxnn : 0 ≤ xEta h u :=
          mul_nonneg (Real.rpow_nonneg hu.1.le _) (sq_nonneg _)
        have h2k : 1 ≤ 2 * kappa u := two_kappa_ge_one ⟨hu.1.le, le_trans hu.2 hsinb_le⟩
        have hc1 : 1 / (2 * kappa u) ≤ 1 := by
          rw [div_le_one (by linarith)]; linarith
        calc xEta h u * (1 / (2 * kappa u)) ≤ xEta h u * 1 :=
              mul_le_mul_of_nonneg_left hc1 hxnn
          _ = xEta h u := mul_one _))
  have hstep2 : (∫ u in (0 : ℝ)..Real.sin (2 * b), xEta h u)
      ≤ ∫ u in (0 : ℝ)..xNear, xEta h u := by
    refine intervalIntegral.integral_mono_interval le_rfl hsinb_pos.le hsinb_le ?_
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le xNear_pos.le).mpr hGint)
    exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu =>
      mul_nonneg (Real.rpow_nonneg hu.1.le _) (sq_nonneg _))
  calc (∫ t in (0 : ℝ)..b, etaLHS h t)
      = ∫ u in (0 : ℝ)..Real.sin (2 * b),
          etaLHS h (thetaOf u) * (1 / (2 * kappa u)) := hid
    _ = ∫ u in (0 : ℝ)..Real.sin (2 * b), xEta h u * (1 / (2 * kappa u)) := hEq
    _ ≤ ∫ u in (0 : ℝ)..Real.sin (2 * b), xEta h u := hstep1
    _ ≤ ∫ u in (0 : ℝ)..xNear, xEta h u := hstep2
    _ ≤ etaNear * etaData h := hGle

/-- Integrability of the left-hand integrand on the near interval `(0,b)`. -/
private lemma near_integrable_aux {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hDenη : MeasureTheory.IntegrableOn (PsiEta h) Work.Spaces.Iθ) :
    ∀ b : ℝ, 0 < b → b ≤ Real.pi / 8 →
      MeasureTheory.IntegrableOn (etaLHS h) (Set.Ioo 0 b) := by
  intro b hb0 hb8
  obtain ⟨hGint, -⟩ := xEta_integrable hsm h0 hDenη
  have hsinb_pos : 0 < Real.sin (2 * b) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos, hb8])
  have hsinb_le : Real.sin (2 * b) ≤ xNear := by
    have h4mem : (Real.pi / 4 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hbmem : (2 * b : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos, hb8]⟩
    have h := Real.strictMonoOn_sin.monotoneOn hbmem h4mem (by linarith [hb8])
    simpa [xNear, Real.sin_pi_div_four] using h
  have hGsub : MeasureTheory.IntegrableOn (xEta h) (Set.Ioc 0 (Real.sin (2 * b))) :=
    hGint.mono_set fun u hu => ⟨hu.1, le_trans hu.2 hsinb_le⟩
  have hc : ContinuousOn (fun u : ℝ => 1 / (2 * kappa u)) (Set.Ioc 0 (Real.sin (2 * b))) :=
    continuousOn_inv_two_kappa hsinb_le
  have hP : MeasureTheory.IntegrableOn
      (fun u : ℝ => xEta h u * (1 / (2 * kappa u))) (Set.Ioc 0 (Real.sin (2 * b))) :=
    hGsub.mono_nonneg
      (hGsub.aestronglyMeasurable.mul (hc.aestronglyMeasurable measurableSet_Ioc))
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu =>
        mul_nonneg (mul_nonneg (Real.rpow_nonneg hu.1.le _) (sq_nonneg _))
          (div_nonneg zero_le_one (le_trans zero_le_one
            (two_kappa_ge_one ⟨hu.1.le, le_trans hu.2 hsinb_le⟩)))))
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu => by
        have hxnn : 0 ≤ xEta h u :=
          mul_nonneg (Real.rpow_nonneg hu.1.le _) (sq_nonneg _)
        have h2k : 1 ≤ 2 * kappa u := two_kappa_ge_one ⟨hu.1.le, le_trans hu.2 hsinb_le⟩
        have hc1 : 1 / (2 * kappa u) ≤ 1 := by
          rw [div_le_one (by linarith)]; linarith
        calc xEta h u * (1 / (2 * kappa u)) ≤ xEta h u * 1 :=
              mul_le_mul_of_nonneg_left hc1 hxnn
          _ = xEta h u := mul_one _))
  have hP' : MeasureTheory.IntegrableOn
      (fun u : ℝ => etaLHS h (thetaOf u) * (1 / (2 * kappa u)))
      (Set.Ioc 0 (Real.sin (2 * b))) :=
    hP.congr_fun_ae ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu =>
      (pullback_ident hu.1 (le_trans hu.2 hsinb_le)).symm))
  have hIIp : IntervalIntegrable
      (fun u : ℝ => etaLHS h (thetaOf u) * (1 / (2 * kappa u))) volume 0 (Real.sin (2 * b)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hsinb_pos.le).mpr hP'
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.sin (2 * b)) (f := thetaOf)
    (f' := fun u : ℝ => 1 / (2 * kappa u)) (g := etaLHS h)
    ((Real.continuous_arcsin.div_const 2).continuousOn)
    (fun u hu => by
      rw [min_eq_left hsinb_pos.le, max_eq_right hsinb_pos.le] at hu
      exact hasDerivAt_thetaOf_nr ⟨by linarith [hu.1],
        by linarith [hu.2, hsinb_le, xNear_lt]⟩)
    (fun u hu => by
      rw [min_eq_left hsinb_pos.le, max_eq_right hsinb_pos.le] at hu
      have h2k : 1 ≤ 2 * kappa u :=
        two_kappa_ge_one ⟨hu.1.le, le_trans hu.2.le hsinb_le⟩
      exact div_nonneg zero_le_one (le_trans zero_le_one h2k))
  have hII : IntervalIntegrable (etaLHS h) volume 0 b := by
    have h1 := hiff.mp (by simpa only [Function.comp_def] using hIIp)
    rwa [thetaOf_zero_nr, thetaOf_sin_two_near hb0.le hb8] at h1
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb0.le).mp hII).congr_set_ae
    MeasureTheory.Ioo_ae_eq_Ioc

/-- The near-region bound, with its *integrability* conjunct, by monotone convergence from the
truncated bounds `near_trunc_bound`. -/
private theorem nearEta {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hDenη : MeasureTheory.IntegrableOn (PsiEta h) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (etaLHS h) (Set.Ioc 0 (Real.pi / 8)) ∧
      (∫ θ in (0 : ℝ)..(Real.pi / 8), etaLHS h θ) ≤ etaNear * etaData h := by
  have h8pos : (0 : ℝ) < Real.pi / 8 := by linarith [Real.pi_pos]
  have hcont : ContinuousOn (etaLHS h) (Set.Ioo 0 (Real.pi / 8)) := by
    have h1 : ContinuousOn (fun θ : ℝ => h θ / Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 8)) := by
      refine (hsm.continuousOn.mono ?_).div ?_ ?_
      · intro θ hθ; exact ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
      · fun_prop
      · intro θ hθ
        exact ne_of_gt (Work.FTS.H2.sin_two_pos_of_Ioo
          ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩)
    have h2 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (Set.Ioo 0 (Real.pi / 8)) := by
      apply ContinuousOn.rpow
      · fun_prop
      · exact continuousOn_const
      · intro θ hθ
        exact Or.inl (ne_of_gt (Work.FTS.H2.sin_two_pos_of_Ioo
          ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩))
    show ContinuousOn (fun θ : ℝ => (h θ / Real.sin (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (Set.Ioo 0 (Real.pi / 8))
    exact (h1.pow 2).mul h2
  have hnn : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 8), 0 ≤ etaLHS h x := by
    intro x hx
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
      (le_of_lt (Work.FTS.H2.sin_two_pos_of_Ioo ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩)) _)
  obtain ⟨hint, hbound⟩ := Work.FTS.EllipticEst.remov.interval_integral_mono_limit h8pos hcont hnn
    (fun b hb => near_integrable_aux hsm h0 hDenη b hb.1 (le_of_lt hb.2))
    (fun b hb => near_trunc_bound hsm h0 hDenη b hb.1 (le_of_lt hb.2))
  refine ⟨hint.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm, ?_⟩
  rw [Work.FTS.EllipticEst.remov.intervalIntegral_eq_setIntegral_Ioo h8pos.le (etaLHS h)]
  exact hbound

/-! ### (II) The middle region `(π/8, 3π/8)` -/

private theorem midEta :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      MeasureTheory.IntegrableOn (PsiEta h) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (etaLHS h) (Set.Ioc (Real.pi / 8) (3 * Real.pi / 8)) ∧
      (∫ θ in (Real.pi / 8)..(3 * Real.pi / 8), etaLHS h θ)
        ≤ C * etaData h := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := honestPoincarePoint
  refine ⟨(Real.pi / 4) * (4 * 2 ^ Work.Spaces.eta * C₁), by positivity, ?_⟩
  intro h hsm h0 hDenη
  have hcont : ContinuousOn (etaLHS h) midSet := by
    show ContinuousOn (fun θ : ℝ => (h θ / Real.sin (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) midSet
    exact ((continuousOn_div_sin_two hsm).pow 2).mul
      (continuousOn_rpow_neg_sin_two Work.Spaces.eta)
  have hInt : MeasureTheory.IntegrableOn (etaLHS h) midSet :=
    hcont.integrableOn_compact isCompact_Icc
  have hpt : ∀ θ ∈ Set.Icc (Real.pi / 8) (3 * Real.pi / 8),
      etaLHS h θ ≤ 4 * 2 ^ Work.Spaces.eta * C₁ * etaData h := by
    intro θ hθ
    have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := midSet_subset_Ioo hθ
    have hsin : (1 : ℝ) / 2 ≤ Real.sin (2 * θ) := half_le_sin_two_of_mem_mid hθ
    have hsinpos : 0 < Real.sin (2 * θ) := lt_of_lt_of_le (by norm_num) hsin
    have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ≤ 2 ^ Work.Spaces.eta :=
      rpow_neg_sin_two_le_mid Work.Spaces.eta_pos.le hθ
    have h2 : (h θ / Real.sin (2 * θ)) ^ 2 ≤ 4 * (h θ) ^ 2 := by
      have hs2 : (1 : ℝ) ≤ 4 * (Real.sin (2 * θ)) ^ 2 := by nlinarith [hsin]
      have hprod := mul_le_mul_of_nonneg_left hs2 (sq_nonneg (h θ))
      rw [div_pow, div_le_iff₀ (by positivity : (0 : ℝ) < (Real.sin (2 * θ)) ^ 2)]
      nlinarith [hprod]
    have h3 : (h θ) ^ 2 ≤ C₁ * etaData h := by
      have hh := hC₁ h hsm h0 hDenη θ hθIoo
      simpa only [etaData, PsiEta] using hh
    have h4 : (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Real.rpow_nonneg hsinpos.le _
    have hnn : (0 : ℝ) ≤ 4 * (h θ) ^ 2 := by positivity
    have h5 : (h θ / Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ (4 * (h θ) ^ 2) * 2 ^ Work.Spaces.eta := mul_le_mul h2 h1 h4 hnn
    calc etaLHS h θ ≤ (4 * (h θ) ^ 2) * 2 ^ Work.Spaces.eta := h5
      _ = 4 * 2 ^ Work.Spaces.eta * (h θ) ^ 2 := by ring
      _ ≤ 4 * 2 ^ Work.Spaces.eta * (C₁ * etaData h) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 4 * 2 ^ Work.Spaces.eta * C₁ * etaData h := by ring
  refine ⟨hInt.mono_set Set.Ioc_subset_Icc_self, ?_⟩
  have hI1 : IntervalIntegrable (etaLHS h) volume (Real.pi / 8) (3 * Real.pi / 8) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])).mpr
      (hInt.mono_set Set.Ioc_subset_Icc_self)
  have hI2 : IntervalIntegrable (fun _ : ℝ => 4 * 2 ^ Work.Spaces.eta * C₁ * etaData h)
      volume (Real.pi / 8) (3 * Real.pi / 8) := intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on (by linarith [Real.pi_pos]) hI1 hI2 hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  refine hmono.trans (le_of_eq ?_)
  ring

/-! ### (III) The far region `(3π/8, π/2)`, by reflection -/

/-- The `η`-integrand at the reflected argument. -/
private lemma psiEta_refl {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    Set.EqOn (PsiEta fun θ => h (Real.pi / 2 - θ)) (fun θ => PsiEta h (Real.pi / 2 - θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
  intro θ hθ
  simp only [PsiEta]
  rw [far_deriv_reflSlice_eq h hsm hθ, neg_sq, sin_two_reflSlice]

private lemma farEta {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hπ : Filter.Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hDenη : MeasureTheory.IntegrableOn (PsiEta h) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (etaLHS h) (Set.Ioc (3 * Real.pi / 8) (Real.pi / 2)) ∧
      (∫ θ in (3 * Real.pi / 8)..(Real.pi / 2), etaLHS h θ) ≤ etaNear * etaData h := by
  set g : ℝ → ℝ := fun θ => h (Real.pi / 2 - θ) with hg
  have hgsm : ContDiffOn ℝ (⊤ : ℕ∞) g (Set.Ioo 0 (Real.pi / 2)) := by
    rw [hg]
    exact hsm.comp (contDiffOn_const.sub contDiffOn_id)
      (fun θ hθ => ⟨by linarith [hθ.2], by linarith [hθ.1]⟩)
  have hg0 : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    rw [hg]
    have hmap : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (nhdsWithin 0 (Set.Ioi 0))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h2 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝 0) (𝓝 (Real.pi / 2)) := by
          have h3 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝 0)
              (𝓝 (Real.pi / 2 - 0)) := tendsto_const_nhds.sub tendsto_id
          simpa using h3
        exact h2.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with θ hθ
        simp only [Set.mem_Ioi] at hθ
        exact sub_lt_self _ hθ
    simpa [Function.comp_def] using hπ.comp hmap
  have hgDen : MeasureTheory.IntegrableOn (PsiEta g) Work.Spaces.Iθ := by
    have hbase : MeasureTheory.IntegrableOn
        (fun θ : ℝ => PsiEta h (Real.pi / 2 - θ)) Work.Spaces.Iθ :=
      (far_integrableOn_reflθ (PsiEta h)).mpr hDenη
    rw [hg]
    exact hbase.congr_fun_ae (far_ae_eq_of_eqOn_Ioo (psiEta_refl hsm)).symm
  obtain ⟨hnear_int, hnear_bound⟩ := nearEta hgsm hg0 hgDen
  have hdata : etaData g = etaData h := by
    rw [hg]
    show (∫ θ in Work.Spaces.Iθ, PsiEta (fun θ => h (Real.pi / 2 - θ)) θ)
      = ∫ θ in Work.Spaces.Iθ, PsiEta h θ
    rw [MeasureTheory.setIntegral_congr_ae (s := Work.Spaces.Iθ) measurableSet_Icc
      ((ae_restrict_iff' measurableSet_Icc).mp (far_ae_eq_of_eqOn_Ioo (psiEta_refl hsm)))]
    exact far_integral_reflθ (PsiEta h)
  -- the left-hand side transfers across the reflection
  have hfar_eq : (∫ θ in (3 * Real.pi / 8)..(Real.pi / 2), etaLHS h θ)
      = ∫ θ in (0 : ℝ)..(Real.pi / 8), etaLHS g θ := by
    have h1 := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := Real.pi / 8)
      (d := Real.pi / 2) (f := etaLHS h)
    rw [show Real.pi / 2 - Real.pi / 8 = 3 * Real.pi / 8 by ring,
      show Real.pi / 2 - 0 = Real.pi / 2 by ring] at h1
    rw [← h1]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [hg]
    simp only [etaLHS]
    rw [sin_two_reflSlice]
  have hIg : IntervalIntegrable (etaLHS g) volume 0 (Real.pi / 8) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])).mpr hnear_int
  have hcomp : IntervalIntegrable (fun x : ℝ => etaLHS g (Real.pi / 2 - x)) volume
      (Real.pi / 2) (3 * Real.pi / 8) := by
    have h2 := hIg.comp_sub_left (Real.pi / 2)
    rw [show Real.pi / 2 - 0 = Real.pi / 2 by ring,
      show Real.pi / 2 - Real.pi / 8 = 3 * Real.pi / 8 by ring] at h2
    exact h2
  have hcomp' : IntervalIntegrable (etaLHS h) volume (Real.pi / 2) (3 * Real.pi / 8) := by
    refine hcomp.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    refine Eventually.of_forall fun x _ => ?_
    rw [hg]
    simp only [etaLHS]
    rw [show Real.pi / 2 - (Real.pi / 2 - x) = x by ring, sin_two_reflSlice]
  have hfar_int : MeasureTheory.IntegrableOn (etaLHS h)
      (Set.Ioc (3 * Real.pi / 8) (Real.pi / 2)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])).mp hcomp'.symm
  exact ⟨hfar_int, by rw [hfar_eq]; simpa [hdata] using hnear_bound⟩

/-! ### (IV) The assembly -/

/-- **The `i = 0` (weighted Hardy) per-slice bound over the whole of `Iθ`.**

`∫ θ in Iθ, (h θ / sin(2θ))² sin(2θ)^{-η} ≤ C ∫ θ in Iθ, (∂_θh θ)² sin(2θ)^{-η}` for a slice
which is `C^∞` on `(0,π/2)`, vanishes at both endpoints (limits `0`) and has honest
`η`-weighted derivative, together with the *integrability* of the left-hand integrand on `Iθ`.

NOTE (route hint).  `Submission/Work/FTS/H2/DivSinQR/zSlotHardy.lean` contains a full template
sweep of this argument (three regions `(0,π/4]`, `[π/4,π/2)` split there, reflection
bookkeeping in its private `integral_Ioo_comp_sub` / `integrableOn_comp_sub_left_iff`): its only
gap is its local sharp-constant `powerHardyOpen`, which THIS statement does not need — an
existential constant is enough, and `Work.FTS.H2.DivQ.hardyA_le_W` at `k = 0`, `γ := η` supplies
the near-region piece (integrability *and* bound, constant `C/(1+η)²`) after the substitution
`x = sin 2θ` (`thetaOfSubst`, `hardyA_le_W`'s `Ioc 0 x₁` ↔ `Ioo` are a.e. equal).  The middle
region uses `honestPoincarePoint` and `sin(2θ) ≥ 1/√2`; the far region is the reflection
`θ ↦ π/2 - θ`. -/
theorem sliceBoundEta :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv h θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (h θ / Real.sin (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (h θ / Real.sin (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ C * (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  obtain ⟨Cₘ, hCₘpos, hmid⟩ := midEta
  refine ⟨2 * etaNear + Cₘ + 1, by linarith [etaNear_pos, hCₘpos], ?_⟩
  intro h hsm h0 hπ hDenη
  have h8le : (0 : ℝ) ≤ Real.pi / 8 := by linarith [Real.pi_pos]
  have h83 : Real.pi / 8 ≤ 3 * Real.pi / 8 := by linarith [Real.pi_pos]
  have h32 : 3 * Real.pi / 8 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h2pos : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hDenη' : MeasureTheory.IntegrableOn (PsiEta h) Work.Spaces.Iθ := hDenη
  obtain ⟨hnear_int, hnear_bound⟩ := nearEta hsm h0 hDenη'
  obtain ⟨hmid_int, hmid_bound⟩ := hmid h hsm h0 hDenη'
  obtain ⟨hfar_int, hfar_bound⟩ := farEta hsm hπ hDenη'
  have hDnn : 0 ≤ etaData h := etaData_nonneg h
  -- interval integrability of the three pieces
  have hI1 : IntervalIntegrable (etaLHS h) volume (0 : ℝ) (Real.pi / 8) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h8le).mpr hnear_int
  have hI2 : IntervalIntegrable (etaLHS h) volume (Real.pi / 8) (3 * Real.pi / 8) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h83).mpr hmid_int
  have hI3 : IntervalIntegrable (etaLHS h) volume (3 * Real.pi / 8) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h32).mpr hfar_int
  have hIθ : MeasureTheory.IntegrableOn (etaLHS h) Work.Spaces.Iθ := by
    have hI : IntervalIntegrable (etaLHS h) volume (0 : ℝ) (Real.pi / 2) :=
      (hI1.trans hI2).trans hI3
    have hIoc : MeasureTheory.IntegrableOn (etaLHS h) (Set.Ioc (0 : ℝ) (Real.pi / 2)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le h2pos.le).mp hI
    exact hIoc.congr_set_ae
      (MeasureTheory.Ioc_ae_eq_Icc' (μ := volume) (b := Real.pi / 2)
        (measure_singleton (0 : ℝ))).symm
  -- the value of the integral
  have hval : (∫ θ in Work.Spaces.Iθ, etaLHS h θ)
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), etaLHS h θ := by
    rw [Work.Spaces.Iθ, intervalIntegral.integral_of_le h2pos.le,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hsplit : (∫ θ in (0 : ℝ)..(Real.pi / 2), etaLHS h θ)
      = (∫ θ in (0 : ℝ)..(Real.pi / 8), etaLHS h θ)
        + (∫ θ in (Real.pi / 8)..(3 * Real.pi / 8), etaLHS h θ)
        + ∫ θ in (3 * Real.pi / 8)..(Real.pi / 2), etaLHS h θ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hI1 (hI2.trans hI3),
      ← intervalIntegral.integral_add_adjacent_intervals hI2 hI3]
    ring
  refine ⟨?_, ?_⟩
  · change MeasureTheory.IntegrableOn (etaLHS h) Work.Spaces.Iθ
    exact hIθ
  · change (∫ θ in Work.Spaces.Iθ, etaLHS h θ) ≤ (2 * etaNear + Cₘ + 1) * etaData h
    rw [hval, hsplit]
    calc ((∫ θ in (0 : ℝ)..(Real.pi / 8), etaLHS h θ)
          + (∫ θ in (Real.pi / 8)..(3 * Real.pi / 8), etaLHS h θ))
          + ∫ θ in (3 * Real.pi / 8)..(Real.pi / 2), etaLHS h θ
        ≤ etaNear * etaData h + Cₘ * etaData h
          + etaNear * etaData h := by linarith [hnear_bound, hmid_bound, hfar_bound]
      _ = (2 * etaNear + Cₘ) * etaData h := by ring
      _ ≤ (2 * etaNear + Cₘ + 1) * etaData h :=
          mul_le_mul_of_nonneg_right (by linarith) hDnn

end Work.FTS.H2.DivQ
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.radGreen_source_facts_of_compactSupport =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem radGreen_source_facts_of_compactSupport {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (hsupp : ∃ a b : ℝ, 0 < a ∧ ∀ t : ℝ, t ∉ Set.Icc a b → c t = 0) :
    (∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → |c t| ≤ K / t)
    ∧ (∃ K p : ℝ, 0 < K ∧ 3 / 2 < p ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → |c t| ≤ K * t ^ p)
    ∧ MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1)
    ∧ MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioo 0 1)
    ∧ MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)
    ∧ MeasureTheory.IntegrableOn (fun z : ℝ => (c z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  obtain ⟨a, b, ha, hsup⟩ := hsupp
  -- Enlarge the supporting interval so that its left endpoint is `≤` its right endpoint.  (If
  -- `b < a` then `Icc a b = ∅` and the source vanishes identically, so this loses nothing.)
  have hab : a ≤ max b a := le_max_right b a
  have hsup' : ∀ t : ℝ, t ∉ Set.Icc a (max b a) → c t = 0 := fun t ht =>
    hsup t fun h => ht ⟨h.1, le_trans h.2 (le_max_left b a)⟩
  -- The source is globally bounded: it vanishes off the compact set `Icc a (max b a)`.
  have hsub : Set.Icc a (max b a) ⊆ Set.Ioi 0 := fun z hz => lt_of_lt_of_le ha hz.1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.mono hsub)
  have hMnn : (0 : ℝ) ≤ max C 0 := le_max_right C 0
  have hMb : ∀ t : ℝ, |c t| ≤ max C 0 := by
    intro t
    by_cases ht : t ∈ Set.Icc a (max b a)
    · refine le_trans ?_ (le_max_left C 0)
      simpa only [Real.norm_eq_abs] using hC t ht
    · rw [hsup' t ht, abs_zero]
      exact hMnn
  -- The power factor `t ↦ t ^ e` is continuous on `(0,∞)` for every real exponent.
  have hrpow : ∀ e : ℝ, ContinuousOn (fun z : ℝ => z ^ e) (Set.Ioi 0) := fun e =>
    (Work.FTS.ClassC.contDiffOn_rpow_Ioi e 0).continuousOn
  have hw : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    unfold Work.Spaces.w
    refine (((continuous_const.add continuous_id).continuousOn.pow 2).div
      (continuous_id.continuousOn.pow 2) (fun z hz => ?_)).pow 2
    exact pow_ne_zero 2 (ne_of_gt hz)
  refine ⟨Work.FTS.ClassCHon.decay_of_support hMnn hMb hsup',
    Work.FTS.ClassCHon.vanishing_of_support ha hMnn hMb hsup', ?_, ?_, ?_, ?_⟩
  · refine (Work.FTS.ClassCHon.integrableOn_Ioi_of_contOn_of_support ha hab
      (hc.mul (hrpow _)) (fun z hz => by
        simp only [Pi.mul_apply]
        rw [hsup' z hz, zero_mul])).mono_set ?_
    intro z hz
    exact hz.1
  · refine (Work.FTS.ClassCHon.integrableOn_Ioi_of_contOn_of_support ha hab
      (hc.mul (hrpow _)) (fun z hz => by
        simp only [Pi.mul_apply]
        rw [hsup' z hz, zero_mul])).mono_set ?_
    intro z hz
    exact hz.1
  · refine (Work.FTS.ClassCHon.integrableOn_Ioi_of_contOn_of_support ha hab
      (hc.mul (hrpow _)) (fun z hz => by
        simp only [Pi.mul_apply]
        rw [hsup' z hz, zero_mul])).mono_set ?_
    exact Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)
  · refine Work.FTS.ClassCHon.integrableOn_Ioi_of_contOn_of_support ha hab
      ((hc.pow 2).mul hw) ?_
    intro z hz
    show (c z) ^ 2 * (Work.Spaces.w z) ^ 2 = 0
    rw [hsup' z hz]
    ring

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyRight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 2000000

/-! ## The right half `(π/4, π/2]` -/

/-- **The weighted Hardy inequality on the right half.**  Obtained from
`hardy_half_left_open` by the mirror `u ↦ f(π/2 - u)`. -/
theorem hardy_half_right_open {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {f : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
      (Set.Ioc (Real.pi / 4) (Real.pi / 2))) :
    IntegrableOn (fun θ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        (Set.Ioc (Real.pi / 4) (Real.pi / 2)) ∧
      (∫ θ in Set.Ioc (Real.pi / 4) (Real.pi / 2), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        ≤ 4 / β ^ 2 * (Real.pi / 4) ^ 2
            * (∫ θ in Set.Ioc (Real.pi / 4) (Real.pi / 2),
                (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
          + Real.pi / (2 * β) * (f (Real.pi / 4)) ^ 2 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hqpos : (0 : ℝ) < Real.pi / 4 := by linarith
  have hqlt : Real.pi / 4 < Real.pi / 2 := by linarith
  have hder : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt f (deriv f θ) θ :=
    fun θ hθ => hasDerivAt_of_contDiffOn_one hsm hθ
  -- the mirror
  have hg_sm : ContDiffOn ℝ 1 (fun u : ℝ => f (Real.pi / 2 - u)) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_mirror_open hsm
  have hmir : ∀ u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (fun u : ℝ => f (Real.pi / 2 - u)) u = -deriv f (Real.pi / 2 - u) :=
    Work.FTS.H2.Transport3Aux.deriv_mirror_weak hder
  -- integrability of the mirrored derivative integrand
  have hint_g : IntegrableOn
      (fun u : ℝ => (deriv (fun u : ℝ => f (Real.pi / 2 - u)) u) ^ 2
        * (Real.sin (2 * u)) ^ (1 - β)) (Set.Ioc (0 : ℝ) (Real.pi / 4)) := by
    have hIoo : IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
      (integrableOn_Ioc_iff_integrableOn_Ioo).mp hint
    have href := (Work.FTS.EllSol.VthAux.traceAux.reflectIntegrableOn_iff
      (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) hqpos)
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 from by ring] at href
    have h1 : IntegrableOn
        (fun u : ℝ => (deriv f (Real.pi / 2 - u)) ^ 2
          * (Real.sin (2 * (Real.pi / 2 - u))) ^ (1 - β)) (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
      href.mp hIoo
    have h2 : IntegrableOn
        (fun u : ℝ => (deriv f (Real.pi / 2 - u)) ^ 2
          * (Real.sin (2 * u)) ^ (1 - β)) (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
      h1.congr_fun (fun u _ => by
        show deriv f (Real.pi / 2 - u) ^ 2 * Real.sin (2 * (Real.pi / 2 - u)) ^ (1 - β)
          = deriv f (Real.pi / 2 - u) ^ 2 * Real.sin (2 * u) ^ (1 - β)
        rw [show 2 * (Real.pi / 2 - u) = Real.pi - 2 * u from by ring, Real.sin_pi_sub])
        measurableSet_Ioo
    have h3 : IntegrableOn
        (fun u : ℝ => (deriv (fun u : ℝ => f (Real.pi / 2 - u)) u) ^ 2
          * (Real.sin (2 * u)) ^ (1 - β)) (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
      h2.congr_fun (fun u hu => by
        have hu' : u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hu.1, lt_trans hu.2 hqlt⟩
        have hd : deriv (fun u : ℝ => f (Real.pi / 2 - u)) u = -deriv f (Real.pi / 2 - u) :=
          hmir u hu'
        rw [hd]; ring) measurableSet_Ioo
    exact (integrableOn_Ioc_iff_integrableOn_Ioo).mpr h3
  -- apply the left half to the mirror
  have hL := hardy_half_left_open (β := β) hβ hβ1 hg_sm hint_g
  -- the mirror identities
  have e1 : (∫ u in Set.Ioc (0 : ℝ) (Real.pi / 4),
        (f (Real.pi / 2 - u)) ^ 2 * (Real.sin (2 * u)) ^ (β - 1))
      = ∫ θ in Set.Ioc (Real.pi / 4) (Real.pi / 2),
          (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1) := by
    rw [← intervalIntegral.integral_of_le hqpos.le, ← intervalIntegral.integral_of_le hqlt.le]
    exact Work.FTS.H2.Transport3Aux.mirror_sq_sin_rpow (β - 1) f
  have e2 : (∫ u in Set.Ioc (0 : ℝ) (Real.pi / 4),
        (deriv (fun u : ℝ => f (Real.pi / 2 - u)) u) ^ 2 * (Real.sin (2 * u)) ^ (1 - β))
      = ∫ θ in Set.Ioc (Real.pi / 4) (Real.pi / 2),
          (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β) := by
    rw [← intervalIntegral.integral_of_le hqpos.le, ← intervalIntegral.integral_of_le hqlt.le]
    exact Work.FTS.H2.Transport3Aux.mirror_deriv_sq_integral_weak (β := β) hder
  have e3 : (f (Real.pi / 2 - Real.pi / 4)) ^ 2 = (f (Real.pi / 4)) ^ 2 := by
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 from by ring]
  constructor
  · -- integrability of the right-hand integrand
    have hIoo : IntegrableOn
        (fun u : ℝ => (f (Real.pi / 2 - u)) ^ 2 * (Real.sin (2 * u)) ^ (β - 1))
        (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
      (integrableOn_Ioc_iff_integrableOn_Ioo).mp hL.1
    have href := (Work.FTS.EllSol.VthAux.traceAux.reflectIntegrableOn_iff
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1)) hqpos)
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 from by ring] at href
    have h2 : IntegrableOn
        (fun u : ℝ => (f (Real.pi / 2 - u)) ^ 2 * (Real.sin (2 * (Real.pi / 2 - u))) ^ (β - 1))
        (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
      hIoo.congr_fun (fun u _ => by
        show (f (Real.pi / 2 - u)) ^ 2 * Real.sin (2 * u) ^ (β - 1)
          = (f (Real.pi / 2 - u)) ^ 2 * Real.sin (2 * (Real.pi / 2 - u)) ^ (β - 1)
        rw [show 2 * (Real.pi / 2 - u) = Real.pi - 2 * u from by ring, Real.sin_pi_sub])
        measurableSet_Ioo
    have h3 : IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := href.mpr h2
    exact (integrableOn_Ioc_iff_integrableOn_Ioo).mpr h3
  · have hmain := hL.2
    rw [e1, e2, e3] at hmain
    exact hmain

end

end Work.FTS.StrongPersist.N6Trans.SixRoute
end
