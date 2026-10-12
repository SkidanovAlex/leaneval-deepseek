import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.chiSmall_lipschitz
import Submission.Work.BoseFixB1S.profHatCube_moments
import Submission.Work.BoseFixB1S.weightedPlancherelKinFT
import Submission.Work.BoseKinLoc.Momentum.cubFT_prod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.cubeProfHatSecondMoment` — the second moment of the cube profile is finite

`profHatCube M p = ∫_z chiSmall M z · cos⟪p,z⟫` is the cosine profile of the normalised cube
cutoff `chiSmall M` (`CubeWindowSymbol`, `Submission/Work/ChiSmall.lean`).  This module proves
that its **second moment** is finite:

`p ↦ ‖p‖²·(profHatCube M p)²` is integrable, for every `M ≥ 1`.

## Route

For `M ≥ 2` this is immediate from the weighted `H¹` Plancherel identity
(`weightedPlancherelKinFT`), because then `chiSmall M` is `C¹`; the *point of the statement* is
the Lipschitz case `M = 1`, where no derivative Plancherel applies directly.

The proof here uses the **explicit a.e. partial derivatives** of the cube bump,
`pcD M k z = cSmall M · phiCDeriv M (z_k) · ∏_{i≠k} phiC M (z_i)`
(`Submission/Work/BoseFixB1S/profHatCube_moments.lean`), which are elements of `L¹ ∩ L²` for
*every* `M ≥ 1` (they are bounded and supported in the unit cube).  Two facts from that module —
`pcKinFT_chiSmall_eq` (`kinFT (chiSmall M) = profHatCube M` pointwise, real and even) and
`pcKinFT_pcD` (the derivative rule `kinFT (∂_k χ_M) p = i·p_k·kinFT (χ_M) p`, obtained there from
the 1D integration by parts `pcFt1IBP`, so that no smoothness of `χ_M` is used) — give the
*pointwise* identity

`‖p‖²·(profHatCube M p)² = Σ_k ‖kinFT (pcD M k) p‖²`.

Each summand is integrable by the unweighted Plancherel identity `kinFT_sq_of_memLp` applied to
the (compactly supported) `pcD M k`; hence so is the sum, and the pointwise identity transfers the
integrability to `‖p‖²·(profHatCube M p)²`.

Only the two elementary `L¹ ∩ L²` facts for `pcD M k` (compact support in the unit ball, and the
bound `≤ |cSmall M|·Mπ`) are re-proved here, in the `pc*`-vocabulary of `profHatCube_moments`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-! ## 1. The explicit partials `pcD M k` are bounded and compactly supported -/

/-- The explicit `k`-th partial derivative of the cube bump vanishes outside the unit ball: if
`‖z‖ > 1` then some coordinate of `z` has `|z_j| > 1/2`, and then either the derivative slot
`phiCDeriv M (z_k)` (if `j = k`) or one of the product slots `phiC M (z_j)` (`j ≠ k`) vanishes. -/
lemma cubeProfHatSecondMoment_pcD_eq_zero {M : ℕ} (hM : 1 ≤ M) (k : Fin 3) {z : E3}
    (hz : 1 < ‖z‖) : pcD M k z = 0 := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, 1 / 2 < |z.ofLp i| := by
    by_contra hcon
    rw [not_exists] at hcon
    have hle : ∀ j : Fin 3, |z.ofLp j| ≤ 1 / 2 := fun j => le_of_not_gt (hcon j)
    have hsq : ‖z‖ ^ 2 ≤ 3 * (1 / 2) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ j, ‖z.ofLp j‖ ^ 2 ≤ ∑ _j : Fin 3, (1 / 2) ^ 2 := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [Real.norm_eq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hle j) 2
        _ = 3 * (1 / 2) ^ 2 := by simp
    have h3 : (3 : ℝ) * (1 / 2) ^ 2 < 1 ^ 2 := by norm_num
    nlinarith [norm_nonneg z, hsq, h3]
  rw [pcD]
  by_cases hik : i = k
  · subst hik
    rw [phiCDeriv_eq_zero_of_half_le (le_of_lt hi), mul_zero, zero_mul]
  · have hzi : phiC M (z.ofLp i) = 0 := phiC_eq_zero_of_half_le hM (le_of_lt hi)
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩) hzi]
    ring

/-- The `k`-th explicit partial derivative of the cube bump is measurable. -/
lemma cubeProfHatSecondMoment_measurable_pcD (M : ℕ) (k : Fin 3) : Measurable (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) := by
  refine Complex.measurable_ofReal.comp ?_
  rw [show pcD M k = fun z : E3 => cSmall M * phiCDeriv M (z.ofLp k)
      * ∏ i ∈ Finset.univ.erase k, phiC M (z.ofLp i) from rfl]
  refine Measurable.mul (Measurable.mul measurable_const ?_) ?_
  · exact (measurable_phiCDeriv M).comp (by fun_prop)
  · refine Finset.measurable_prod _ fun i _ => ?_
    exact (zeta1d_continuous.pow M).measurable.comp (by fun_prop)

/-- `pcD M k : E3 → ℂ` has compact support (contained in the unit ball). -/
lemma cubeProfHatSecondMoment_hasCompactSupport_pcD {M : ℕ} (hM : 1 ≤ M) (k : Fin 3) :
    HasCompactSupport (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) := by
  have hcont_supp : ∀ z : E3, 1 < ‖z‖ → ((pcD M k z : ℝ) : ℂ) = 0 :=
    fun z hz => by rw [cubeProfHatSecondMoment_pcD_eq_zero hM k hz, Complex.ofReal_zero]
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : E3) 1) (isClosed_tsupport _) ?_
  refine closure_minimal ?_ isClosed_closedBall
  intro z hz
  simp only [Function.mem_support, ne_eq] at hz
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  by_contra h
  exact hz (by simp [hcont_supp z (lt_of_not_ge h)])

/-- Uniform bound on the explicit partial derivatives of the cube bump:
`|pcD M k z| ≤ |cSmall M| · (M π)`. -/
lemma cubeProfHatSecondMoment_abs_pcD_le {M : ℕ} (k : Fin 3) (z : E3) :
    ‖((pcD M k z : ℝ) : ℂ)‖ ≤ |cSmall M| * ((M : ℝ) * Real.pi) := by
  rw [pcNorm_ofReal, pcD, abs_mul, abs_mul]
  have hprod : |∏ i ∈ Finset.univ.erase k, phiC M (z.ofLp i)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => abs_phiC_le_one M _)
  calc |cSmall M| * |phiCDeriv M (z.ofLp k)|
          * |∏ i ∈ Finset.univ.erase k, phiC M (z.ofLp i)|
      ≤ |cSmall M| * ((M : ℝ) * Real.pi) * 1 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (abs_phiCDeriv_le M _) (abs_nonneg _)) hprod
          (abs_nonneg _) (mul_nonneg (abs_nonneg _) (by positivity))
    _ = |cSmall M| * ((M : ℝ) * Real.pi) := by ring

/-- `pcD M k ∈ L¹ ∩ L²` for every `M ≥ 1`: it is a.e. strongly measurable, bounded, and
compactly supported. -/
lemma cubeProfHatSecondMoment_memLp_pcD {M : ℕ} (hM : 1 ≤ M) (k : Fin 3) :
    MemLp (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) 1 volume
      ∧ MemLp (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) 2 volume :=
  ⟨(cubeProfHatSecondMoment_hasCompactSupport_pcD hM k).memLp_of_bound (cubeProfHatSecondMoment_measurable_pcD M k).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun z => cubeProfHatSecondMoment_abs_pcD_le k z),
    (cubeProfHatSecondMoment_hasCompactSupport_pcD hM k).memLp_of_bound (cubeProfHatSecondMoment_measurable_pcD M k).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun z => cubeProfHatSecondMoment_abs_pcD_le k z)⟩

/-! ## 2. The pointwise identity and the second moment -/

/-- **The pointwise second-moment identity**: the weighted profile of the cube cutoff is the sum
of the (unweighted) transforms of its explicit partial derivatives. -/
lemma cubeProfHatSecondMoment_pointwise (M : ℕ) (hM : 1 ≤ M) (p : E3) :
    ‖p‖ ^ 2 * (profHatCube M p) ^ 2
      = ∑ k : Fin 3, ‖kinFT (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) p‖ ^ 2 := by
  have hχ : (profHatCube M p) ^ 2
      = ‖kinFT (fun z : E3 => (chiSmall M z : ℂ)) p‖ ^ 2 := by
    rw [pcKinFT_chiSmall_eq M hM p, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  rw [hχ]
  rw [show ‖p‖ ^ 2 = ∑ k : Fin 3, (p.ofLp k) ^ 2 from by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Real.norm_eq_abs, sq_abs]]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pcKinFT_pcD M hM k p]
  have hnorm : ‖Complex.I * (p.ofLp k : ℂ)
        * kinFT (fun z : E3 => (chiSmall M z : ℂ)) p‖ ^ 2
      = (p.ofLp k) ^ 2 * ‖kinFT (fun z : E3 => (chiSmall M z : ℂ)) p‖ ^ 2 := by
    rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_I, one_pow, one_mul,
      pcNorm_ofReal, sq_abs]
  rw [hnorm]

theorem cubeProfHatSecondMoment (M : ℕ) (hM : 1 ≤ M) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖p‖ ^ 2 * (Work.BoseFixB1S.profHatCube M p) ^ 2) := by
  have hInt : ∀ k : Fin 3, Integrable
      (fun p : E3 => ‖kinFT (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) p‖ ^ 2) :=
    fun k => (Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp
      (cubeProfHatSecondMoment_memLp_pcD hM k).1 (cubeProfHatSecondMoment_memLp_pcD hM k).2).1
  have hsum : Integrable
      (fun p : E3 => ∑ k : Fin 3, ‖kinFT (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) p‖ ^ 2) := by
    simpa using integrable_finsetSum (Finset.univ : Finset (Fin 3))
      (f := fun (k : Fin 3) (p : E3) =>
        ‖kinFT (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) p‖ ^ 2)
      (fun k _ => hInt k)
  refine hsum.congr (Filter.Eventually.of_forall fun p => ?_)
  exact (cubeProfHatSecondMoment_pointwise M hM p).symm

end Work.BoseFixB1S
