/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.StrongPersist.L6Aux.BcoefMem6`

The projector coefficient `Bcoef α = (Γ(θ)/c(α))·2z²/(1+z)³` is smooth on the open quadrant and
lies in `ℋ⁶`, with `ℋ⁶`-norm-square bounded uniformly for `α ∈ (0,1]`.

This is the order-`6` companion of the delivered order-`3` statement
`Work.FTS.StrongPersist.L3Aux.bcoef_gamCoef_le` (`SmoothOpen` + `HkMem α 3` + `HkSq α 3 ≤ C`).

## Route

The function separates as `B(z,θ) = C(θ)·B(z)` with `C = gamCoefAng α = Γ/c` and
`B = bcoefRad = 2z²/(1+z)³`.  The order-`6` separation bound `HkIntegrandSepLeGen` (proved in
this directory, for every `k`) splits the `ℋ⁶`-integrand into the product of the angular block
and the radial block, and the two blocks are then bounded separately:

* **angular** (`gamCoef_angBlk6`): `(Γ/c)²sin(2θ)^{-η} + Σ_{1≤i≤6}(D_θ^i(Γ/c))²sin(2θ)^{-γ}`
  is dominated by `K·radAngInt α θ`, with `radAngInt α θ = sin(2θ)^{-η} + α²Γ²sin(2θ)^{-γ}`;
* **radial** (`bcoefRad_zop_bound6` + `radSnorm6_int_le`):
  `|(D_z^j bcoefRad)(z)·w(z)| ≤ K/(1+z)` for `j ≤ 6` and `z ≥ 0`, whence the `z`-integral of the
  radial block `radSnorm6 z = Σ_{q<7}((D_z^q bcoefRad)(z)·w(z))²` is `≤ 14K²`.

The angular block is integrable with uniformly bounded integral (`L3Aux.radAngInt_bound`), so
`HkMem α 6` follows from `LocData.HkMem_of_majorant` and `HkSq α 6 ≤ 14K²·K·M`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.L3Aux.bcoef_gamCoef_le
import Submission.Work.Coercivity.dthIterAng_sq_integrable
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.StrongPersist.L3Aux.L12f_slot_le
import Submission.Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen
import Submission.Work.FTS.StrongPersist.L6Aux.bcoefRad_zop_bound6
import Submission.Work.FTS.StrongPersist.L6Aux.gamCoef_angBlk6
import Submission.Work.FTS.StrongPersist.L6Aux.radSnorm6_int_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L6Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The radial block of the order-`6` separation bound -/

/-- The sum of the squares of the weighted `D_z`-iterates of the radial profile, up to order `6`:
the radial factor produced by the separation bound `HkIntegrandSepLeGen` at `k = 6`. -/
def radSnorm6 (z : ℝ) : ℝ :=
  ∑ q ∈ Finset.range 7,
    ((Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad) z * Work.Spaces.w z) ^ 2

lemma radSnorm6_ge_zero (z : ℝ) : 0 ≤ radSnorm6 z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The radial block in the exact shape produced by `HkIntegrandSepLeGen`: there the weight is
squared inside each summand, whereas `radSnorm6` uses `(X·w)²`. -/
lemma radSnorm6_eq_hkSep (z : ℝ) :
    radSnorm6 z = ∑ q ∈ Finset.range 7,
      (Work.Spaces.DzIter q (fun z' _ => Work.FTS.StrongPersist.L3Aux.bcoefRad z') z 0) ^ 2
        * (Work.Spaces.w z) ^ 2 := by
  rw [radSnorm6]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← mul_pow]
  congr 1
  rw [show Work.Spaces.DzIter q (fun z' _ => Work.FTS.StrongPersist.L3Aux.bcoefRad z') z 0
      = (fun z => Work.Spaces.DzIter q (fun z' _ => Work.FTS.StrongPersist.L3Aux.bcoefRad z') z 0) z
      from rfl]
  rw [Work.Spaces.sliceZ_DzIter q (fun z' _ => Work.FTS.StrongPersist.L3Aux.bcoefRad z') 0]
  rw [show Work.Spaces.OpZ = Work.Spaces.Zop from rfl]

/-! ## The target -/

theorem BcoefMem6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) ∧
    Work.Spaces.HkMem α 6
      (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) ∧
    Work.Spaces.HkSq α 6
      (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) ≤ C := by
  obtain ⟨K, hKpos, hrb⟩ := bcoefRad_zop_bound6
  obtain ⟨K3, hK3pos, hangblk⟩ := gamCoef_angBlk6
  obtain ⟨M, hMpos, hang⟩ := Work.FTS.StrongPersist.L3Aux.radAngInt_bound
  have hK : 0 ≤ K := le_of_lt hKpos
  have hCnn : 0 ≤ 14 * K ^ 2 * (K3 * M) := by positivity
  refine ⟨14 * K ^ 2 * (K3 * M) + 1, by linarith, fun α hα hα1 => ?_⟩
  obtain ⟨hangint, hangbd⟩ := hang α hα hα1
  have hA0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Aux.radAngInt α θ :=
    integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => Work.FTS.StrongPersist.L3Aux.radAngInt_nonneg
        (Work.FTS.StrongPersist.L3Aux.sin_two_nonneg_of_mem_Iθ hθ)))
  have hsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) := by
    simpa only [Work.FTS.StrongPersist.L3Aux.bcoefRad,
      Work.FTS.StrongPersist.L3Aux.gamCoefAng] using
      Work.FTS.StrongPersist.L3Aux.smoothOpen_prod α
  have hmajint : ∀ z : ℝ, MeasureTheory.Integrable
      (fun θ : ℝ => radSnorm6 z * (K3 * Work.FTS.StrongPersist.L3Aux.radAngInt α θ))
      (volume.restrict Work.Spaces.Iθ) := by
    intro z
    exact (hangint.const_mul K3).const_mul (radSnorm6 z)
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6
        (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) z θ
        ≤ radSnorm6 z * (K3 * Work.FTS.StrongPersist.L3Aux.radAngInt α θ) := by
    intro z hz θ hθ
    have h1 := Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen (α := α) (k := 6)
      (C := Work.FTS.StrongPersist.L3Aux.gamCoefAng α)
      (B := Work.FTS.StrongPersist.L3Aux.bcoefRad) (z := z) (θ := θ) hθ
    have h2 := hangblk α hα hα1 θ hθ
    refine h1.trans ?_
    rw [← radSnorm6_eq_hkSep z]
    refine (mul_le_mul_of_nonneg_right h2 (radSnorm6_ge_zero z)).trans ?_
    exact le_of_eq (by ring)
  refine ⟨hsm, ?_, ?_⟩
  · refine Work.FTS.LocData.HkMem_of_majorant α 6
      (M := fun z θ => radSnorm6 z * (K3 * Work.FTS.StrongPersist.L3Aux.radAngInt α θ))
      ?_ ?_ ?_ hpt
    · simpa only [Work.FTS.EllipticEst.Q0] using hsm.continuousOn_HkIntegrand α 6
    · intro z hz
      exact hmajint z
    · have hS : MeasureTheory.IntegrableOn radSnorm6 Work.Spaces.Iz :=
        (radSnorm6_int_le hK hrb).1
      have he : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            radSnorm6 z * (K3 * Work.FTS.StrongPersist.L3Aux.radAngInt α θ))
          = fun z : ℝ => radSnorm6 z
              * (K3 * (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Aux.radAngInt α θ)) := by
        funext z
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      rw [he]
      exact hS.mul_const _
  · rw [Work.Spaces.HkSq]
    have hSint : MeasureTheory.IntegrableOn radSnorm6 Work.Spaces.Iz :=
      (radSnorm6_int_le hK hrb).1
    have hSbd : (∫ z in Work.Spaces.Iz, radSnorm6 z) ≤ 14 * K ^ 2 :=
      (radSnorm6_int_le hK hrb).2
    have hinner : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
          (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) z θ)
          ≤ radSnorm6 z
              * (K3 * (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Aux.radAngInt α θ)) := by
      intro z hz
      have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
          Work.Spaces.HkIntegrand α 6
            (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) z θ
            ≤ radSnorm6 z * (K3 * Work.FTS.StrongPersist.L3Aux.radAngInt α θ) :=
        MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpt z hz θ hθ)
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
        (hmajint z) hae
      refine hmono.trans (le_of_eq ?_)
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have houter := MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
      (hSint.mul_const _)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hinner)
    rw [MeasureTheory.integral_mul_const] at houter
    refine houter.trans ?_
    have h1 : (∫ z in Work.Spaces.Iz, radSnorm6 z)
          * (K3 * (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Aux.radAngInt α θ))
        ≤ 14 * K ^ 2
            * (K3 * (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Aux.radAngInt α θ)) :=
      mul_le_mul_of_nonneg_right hSbd (mul_nonneg (le_of_lt hK3pos) hA0)
    refine h1.trans ?_
    have h2 : 14 * K ^ 2
          * (K3 * (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Aux.radAngInt α θ))
        ≤ 14 * K ^ 2 * (K3 * M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hangbd (le_of_lt hK3pos))
        (by positivity)
    linarith [h2]

end Work.FTS.StrongPersist.L6Aux
