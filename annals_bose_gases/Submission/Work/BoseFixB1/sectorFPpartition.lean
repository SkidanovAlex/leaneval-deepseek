import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.bsOneBody_eq_zero_of_far
import Submission.Work.BSKinetic.Decomp.continuous_bsOneBody
import Submission.Work.BSKinetic.FarBump.Defs
import Submission.Work.BSKinetic.FarBump.oneBody_pos_of_low_freq_bound
import Submission.Work.BSKinetic.bsOneBody_eq_dirichlet
import Submission.Work.BSKinetic.cnPlus_eq_slotSum
import Submission.Work.BSKinetic.familyBigKin_eq_slotFamily
import Submission.Work.BSKinetic.familyFormUnproj_eq_kernelForm
import Submission.Work.BSKinetic.familyForm_zero_eq
import Submission.Work.BSKinetic.tBwordBInd_slotSwap_and_integrable
import Submission.Work.BSKinetic.tsupport_bsWin_subset_bsBox
import Submission.Work.BoseFixB1.integralSqSectorPiece
import Submission.Work.FockBridge.SectorAdditive
import Submission.Work.FockBridge.SectorZero
import Submission.Work.FockBridge.convexOn_dlDensityCoeff
import Submission.Work.FockBridge.integrableOn_sectorPiece_sq
import Submission.Work.FockBridge.sectorMassENN_ne_top_of_continuous
import Submission.Work.FockBridge.sum_tBamp_normSq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The sector partition of the weighted second moment (`R_Ψ`'s fibre sum)

FS's second localisation splits a box state over the *count* sectors of the sliding box
`B(u) = dlBox ℓ d u` (`ℓ = sideAt μ (a v)`, `d = paramsAt μ (a v).d`): with
`n_{B(u)}(x) = Σᵢ χ_{B(u)}(xᵢ)²` the smooth per-box count of `Work.BoseFixB1.nCountB` and
`P_k = 1_{n_{B(u)} = k}` the sector projections of `Work.FockBridge.sectorPiece`, every
*multiplication* form — in particular the `R_Ψ`-weight
`psiWeight 1 μ (nCountB/chiMass)` of FS's `eq:aprioriRn+` — decomposes over the sectors:

    ∫_{abox n ℓ} Φ²·F(n(u)/|B(u)|) = Σ_{k ≤ n} ∫_{abox n ℓ} (P_k Φ)²·F(n(u)/|B(u)|).

This is the identity that lets the per-sector rungs (`Work.BoseFixB1S.sectorCountPaymentB1`,
`Work.BoseFixB1S.sectorSharpCountB1`, ...) be summed back into the state-level a-priori bound.

The mathematics is the *finite Fock/particle-number decomposition* of the density:
`Work.FockBridge.sum_sectorPiece_sq` gives
`Σ_{k ∈ range (n+1)} (sectorPiece B k Φ x)² = (Φ x)²` pointwise (the configurational sectors
`{n_B = k}`, `k ≤ n`, partition the box `abox n ℓ`), and the factor `F(nCountB/chiMass)` is a
multiplication weight, so it factors out of the finite sum.  The only analytic input is that
each summand is integrable on the (finite-measure) box, i.e. that the weight
`psiWeight 1 μ (nCountB/chiMass)` is bounded there:

* `nCountB = Σᵢ χ_{B(u)}(xᵢ)² ≥ 0` and `chiMass = ∫χ_{B(u)}² ≥ 0`, so the argument
  `t = nCountB/chiMass` of `F(t) = c(t−μ)²/(1+tμ⁻¹)` is `≥ 0` and the denominator
  `1 + t μ⁻¹ ≥ 1` — no pole, and `F` is continuous on the image;
* `χ` is smooth, so `x ↦ nCountB M ℓ d u x` is continuous for *every* `M, ℓ, d` (including the
  degenerate cases), hence so is the composed weight;
* it is therefore bounded on the compact box `abox n (max |ℓ| 1)` (which contains `abox n ℓ` for
  every real side `ℓ`, including `ℓ ≤ 0`, where `abox n ℓ` is empty or null).

Both ingredients are proved below (`continuous_chiSmallB_all`, `continuous_nCountB_any`,
`integrableOn_sq_mul_psiWeight`); the decomposition itself is the Fock-bridge lemma
`Work.BoseFixB1.integralSqSectorPiece`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

set_option autoImplicit false

/-! ## 1. The weight is bounded on the box -/

/-- The sliding cutoff `χ_{B(u)}(x) = χ(x/ℓ)·χ_M(x/(ℓd) − u)` is continuous in `x` for **every**
`M, ℓ, d, u` (no positivity of `ℓ` or `d` and no `1 ≤ M` is needed: `chiScale` and `chiSmall`
are both globally smooth, the latter because `chiSmallBase_continuous` holds for all `M`). -/
theorem continuous_chiSmallB_all (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmallB M ℓ d u x) := by
  have h1 : Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiScale ℓ x) :=
    Submission.BoseGases.chi_continuous.comp (by fun_prop)
  have h2 : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmall M z) :=
    (Submission.BoseGases.chiSmallBase_continuous M).div_const _
  have h3 : Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) :=
    h2.comp (by fun_prop)
  unfold Submission.BoseGases.chiSmallB
  exact h1.mul h3

/-- The smooth per-box count `x ↦ nCountB M ℓ d u x` is continuous, for every `M, ℓ, d, u`. -/
theorem continuous_nCountB_any (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} :
    Continuous (fun x : Submission.BoseGases.X n => nCountB M ℓ d u x) := by
  rw [show nCountB M ℓ d u = fun x : Submission.BoseGases.X n =>
      ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 from rfl]
  exact continuous_finsetSum _ (fun i _ =>
    ((continuous_chiSmallB_all M ℓ d u).comp (continuous_apply i)).pow 2)

/-- **The `F`-weight integrand is integrable on the box.**  If `f` is measurable and bounded by
`B` on the enlarged box `abox n (max |ℓ| 1)`, then `x ↦ f(x)²·F(nCountB(x)/chiMass)` is
integrable on `abox n ℓ`.  The point of the enlarged box is that `abox n (max |ℓ| 1)` is always
compact (its side is positive), so the continuous ratio `nCountB/chiMass` — and with it the
composed weight — is bounded there, uniformly in `x`; the ratio is also nonnegative, so the
argument of `F` stays in `[0,∞)` where the denominator `1 + tμ⁻¹ ≥ 1` is bounded below. -/
theorem integrableOn_sq_mul_psiWeight {n : ℕ} {ℓ d μ : ℝ} (hμ : 0 < μ) (M : ℕ)
    (u : EuclideanSpace ℝ (Fin 3)) {f : Submission.BoseGases.X n → ℝ} (hf : Measurable f)
    (B : ℝ) (hB : ∀ x ∈ Submission.BoseGases.abox n (max |ℓ| 1), |f x| ≤ B) :
    MeasureTheory.IntegrableOn
      (fun x => (f x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
        (nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u))
      (Submission.BoseGases.abox n ℓ) := by
  set L : ℝ := max |ℓ| 1 with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]; exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  -- `abox n ℓ ⊆ abox n L`, and the latter has finite volume
  have hsub : Submission.BoseGases.abox n ℓ ⊆ Submission.BoseGases.abox n L := by
    rw [hLdef, Submission.BoseGases.abox_eq_pi_acube, Submission.BoseGases.abox_eq_pi_acube]
    refine Set.pi_mono (fun i _ => ?_)
    intro y hy
    rw [Submission.BoseGases.mem_acube_iff] at hy ⊢
    have hle : ℓ ≤ max |ℓ| 1 := le_trans (le_abs_self ℓ) (le_max_left _ _)
    intro m
    exact ⟨by linarith [(hy m).1], by linarith [(hy m).2]⟩
  have hfin : (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))
      (Submission.BoseGases.abox n ℓ) < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono hsub)
      (Submission.BoseGases.abox_lt_top n L hLpos.le)
  -- the count ratio is continuous and nonnegative
  have ht : Continuous (fun x : Submission.BoseGases.X n =>
      nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u) :=
    (continuous_nCountB_any M ℓ d u).div_const _
  have ht0 : ∀ x : Submission.BoseGases.X n,
      0 ≤ nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u := by
    intro x
    refine div_nonneg ?_ (Work.SmallBoxSliding.chiMass_nonneg M ℓ d u)
    rw [show nCountB M ℓ d u x = ∑ i : Fin n,
      (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 from rfl]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  -- so the composed weight `F(t)` is continuous: the denominator `1 + tμ⁻¹` never vanishes
  have hw : Continuous (fun x : Submission.BoseGases.X n =>
      Work.SmallBoxSliding.psiWeight 1 μ
        (nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u)) := by
    unfold Work.SmallBoxSliding.psiWeight
    refine Continuous.div ?_ ?_ ?_
    · exact continuous_const.mul ((ht.sub continuous_const).pow 2)
    · exact continuous_const.add (ht.mul continuous_const)
    · intro x
      have h1 : 0 ≤ nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u * μ⁻¹ :=
        mul_nonneg (ht0 x) (le_of_lt (inv_pos.mpr hμ))
      linarith
  -- hence it is bounded on the compact enlarged box
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n hLpos).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox n L)
    (f := fun x => Work.SmallBoxSliding.psiWeight 1 μ
      (nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u)) hw.continuousOn
  refine MeasureTheory.IntegrableOn.of_bound hfin ?_ (B ^ 2 * C) ?_
  · exact ((hf.pow_const 2).mul hw.measurable).aestronglyMeasurable
  · filter_upwards [MeasureTheory.self_mem_ae_restrict
      (Submission.BoseGases.abox_measurable n ℓ)] with x hx
    have hxL : x ∈ Submission.BoseGases.abox n L := hsub hx
    have hfB : ‖f x‖ ≤ B := by
      rw [Real.norm_eq_abs]
      rw [hLdef] at hxL
      exact hB x hxL
    have hwC : ‖Work.SmallBoxSliding.psiWeight 1 μ
        (nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u)‖ ≤ C := hC x hxL
    rw [norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hfB 2) hwC (norm_nonneg _) (by positivity)

/-! ## 2. The sector bound and the partition identity -/

/-- A sector piece of a state is bounded by any bound of the state, on the same box. -/
theorem sectorPiece_abs_le_of_abs_le {N : ℕ} {L : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (k : ℕ) {Φ : Submission.BoseGases.X N → ℝ} {B : ℝ}
    (hb : ∀ x ∈ Submission.BoseGases.abox N L, |Φ x| ≤ B) (hB0 : 0 ≤ B) :
    ∀ x ∈ Submission.BoseGases.abox N L, |Work.FockBridge.sectorPiece A k Φ x| ≤ B := by
  intro x hx
  by_cases hxs : x ∈ Work.FockBridge.sectorSet A k
  · rw [Work.FockBridge.sectorPiece, Set.indicator_of_mem hxs]
    exact hb x hx
  · rw [Work.FockBridge.sectorPiece, Set.indicator_of_notMem hxs]
    simpa using hB0

/-- **The sector partition of the weighted second moment** in its general form (arbitrary side
`ℓ`, regularity `M`, offset `d`, sliding box `A` and continuous state `Φ`): the `R_Ψ`-weighted
`abox`-mass of `Φ` is the sum, over the count sectors of the sliding box, of the same weight
against the squared sector pieces. -/
theorem sectorFPpartition_general {n : ℕ} {ℓ d μ : ℝ} (hμ : 0 < μ) (M : ℕ)
    (u : EuclideanSpace ℝ (Fin 3)) (A : Set (EuclideanSpace ℝ (Fin 3))) (hA : MeasurableSet A)
    (Φ : Submission.BoseGases.X n → ℝ) (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 μ
          (nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u))
      = ∑ k ∈ Finset.range (n + 1),
          ∫ x in Submission.BoseGases.abox n ℓ,
            (Work.FockBridge.sectorPiece A k Φ x) ^ 2 *
              Work.SmallBoxSliding.psiWeight 1 μ
                (nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u) := by
  -- `Φ` is bounded on the enlarged compact box
  have hLpos : 0 < max |ℓ| 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact n hLpos).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox n (max |ℓ| 1)) (f := Φ) hΦc.continuousOn
  have hBb : ∀ x ∈ Submission.BoseGases.abox n (max |ℓ| 1), |Φ x| ≤ B :=
    fun x hx => by simpa [Real.norm_eq_abs] using hB x hx
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  -- so every sector piece is integrable against the weight, with the uniform bound `max B 0`
  exact integralSqSectorPiece (fun k _ =>
    integrableOn_sq_mul_psiWeight hμ M u
      (hΦc.measurable.indicator (Work.FockBridge.sectorSet_measurable A hA k))
      (max B 0)
      (sectorPiece_abs_le_of_abs_le (A := A) (Φ := Φ) (B := max B 0) k
        (fun x hx => le_trans (hBb x hx) (le_max_left _ _)) hB0))

theorem sectorFPpartition {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseFixB1.bSide v μ))
    (u : EuclideanSpace ℝ (Fin 3)) :
    (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Φ x) ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 μ
          (Work.BoseFixB1.nCountB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u x
            / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u))
      = ∑ k ∈ Finset.range (n + 1),
          ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ),
            (Work.FockBridge.sectorPiece (Work.BoseFixB1.bA v μ u) k
                (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
              Work.SmallBoxSliding.psiWeight 1 μ
                (Work.BoseFixB1.nCountB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bD v μ) u x
                  / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                      (Work.BoseFixB1.bD v μ) u) := by
  exact sectorFPpartition_general (ℓ := Work.BoseFixB1.bSide v μ)
    (d := Work.BoseFixB1.bD v μ) (μ := μ) (M := Work.BoseFixB1.bM v μ) hμ u
    (Work.BoseFixB1.bA v μ u)
    (Work.SmallBoxSliding.measurableSet_dlBox (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bD v μ) u)
    (Φ : Submission.BoseGases.X n → ℝ) Φ.contDiff.continuous

end Work.BoseFixB1
