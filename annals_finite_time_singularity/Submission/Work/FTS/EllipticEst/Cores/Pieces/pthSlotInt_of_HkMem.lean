/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.EllipticEst.Cores.Pieces.pthSlotInt_of_HkMem`

The `m`-th plain angular slot of a datum `g ∈ ℋ^k`, with its sharp weight
`sin(2θ)^{2m-γ}`, is integrable on the angular interval `Iθ = [0,π/2]`, for every `z > 0`
and every `1 ≤ m ≤ k`.

The mathematics is entirely in the *weighted chain* of the `H^k`-norm: the operator
`D_θ = sin(2θ)∂_θ` is triangular with respect to the plain derivatives
(`D_θ^m = Σ_{r≤m} a_{m,r}(θ)∂_θ^r` with `a_{m,m} = sin(2θ)^m`), and the quotient
`a_{m,r}/sin(2θ)^r` is bounded, so that `sin(2θ)^m ∂_θ^m g` is dominated by the *weighted*
jet `D_θ^r g`, `1 ≤ r ≤ m`, and the `r = 0` slot is controlled by the `η`-weight of `HkMem`.
Inverting the triangular relation, squaring and applying Cauchy–Schwarz gives the pointwise
bound (`Work.FTS.EllipticEst.remov.selfdth.slot_pointwise_HkIntegrand`, which is the sharp
`D_θ`-chain of `remov.high_chain_sum_self`)

  `w(z)^2 · (∂_θ^m g)^2 · sin(2θ)^{2m-γ} ≤ C · HkIntegrand α k g z θ`   (a.e. in `θ`),

for a constant `C` depending only on `m`.  Since `HkIntegrand α k g z ·` is integrable on
`Iθ` by `HkMem`, and since the slot function is continuous on the *open* interval
(`g` is `C^∞` on the open quadrant, so its `θ`-slices and their iterated derivatives are
continuous there), the slot function is a.e. strongly measurable and a.e. dominated by an
integrable function — hence integrable (`MeasureTheory.Integrable.mono'`).  Dividing by the
constant `w(z)^2 > 0` (`z > 0`) finishes.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.remov.high_chain_sum_self
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.Pieces

open MeasureTheory Set
open scoped Real Topology

/-- The angular weight `sin(2θ)^c` is continuous on the open quadrant `(0,∞) × (0,π/2)`
(the base `sin(2θ)` is strictly positive there). -/
private theorem continuousOn_sin_two_rpow_Qd (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  refine hsin.rpow_const (fun p hp => Or.inl ?_)
  rw [Set.mem_prod] at hp
  obtain ⟨-, h0, h1⟩ := hp
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))

/-- The iterated `θ`-derivative of a datum which is `C^∞` on the open quadrant is continuous
on the open quadrant: `∂_θ` preserves `C^∞` there (`LocData.contDiffOn_pth`). -/
private theorem continuousOn_uncurry_pthIter {g : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (m : ℕ) :
    ContinuousOn (Function.uncurry (Work.Spaces.pthIter m g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hV : IsOpen (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) : Set (ℝ × ℝ)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hcd : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pthIter m g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    induction m with
    | zero => exact hF
    | succ k ih =>
        rw [Work.Spaces.pthIter_succ]
        exact Work.FTS.LocData.contDiffOn_pth hV ih
  exact hcd.continuousOn

/-- The slot `θ ↦ (∂_θ^m g z θ)^2 · sin(2θ)^q` is almost everywhere strongly measurable on
`Iθ` for `z > 0`: it is continuous on the open interval `(0,π/2)`, which exhausts `Iθ` up to
the two null endpoints. -/
private theorem aesm_pthIter_sq_mul_sin_rpow {g : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (m : ℕ) (q : ℝ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => (Work.Spaces.pthIter m g z θ) ^ 2 *
      (Real.sin (2 * θ)) ^ q) (volume.restrict Work.Spaces.Iθ) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.pthIter m g p.1 p.2) ^ 2 *
      (Real.sin (2 * p.2)) ^ q) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((continuousOn_uncurry_pthIter hF m).pow 2).mul (continuousOn_sin_two_rpow_Qd q)
  exact Work.Spaces.aesm_slice_of_continuousOn_Qd
    (fun p : ℝ × ℝ => (Work.Spaces.pthIter m g p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ q)
    hcont hz

theorem pthSlotInt_of_HkMem {α : ℝ} (hα : 0 < α) {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hm : Work.Spaces.HkMem α k g) {z : ℝ} (hz : 0 < z) {m : ℕ} (hm1 : 1 ≤ m) (hmk : m ≤ k) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter m g z θ) ^ 2 *
      (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  -- the a.e. pointwise chain, with a constant depending on `m` only
  obtain ⟨C, hCpos, hC⟩ :=
    Work.FTS.EllipticEst.remov.selfdth.slot_pointwise_HkIntegrand m hm1
  -- `g` is `C^∞` on the open quadrant in the honest (all finite orders) sense
  have hF : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_iff_forall_nat_le.mpr (fun n _ => hg n)
  have hzmem : z ∈ Work.Spaces.Iz := by
    rw [Work.Spaces.Iz, Set.mem_Ici]
    exact le_of_lt hz
  -- the radial constant `w(z)^2` is strictly positive
  have hw : 0 < (Work.Spaces.w z) ^ 2 := by
    have hz2 : (0 : ℝ) < z ^ 2 := by positivity
    have h1 : 0 < (1 + z) ^ 2 := by positivity
    have h2 : 0 < Work.Spaces.w z := by
      rw [Work.Spaces.w]
      exact div_pos h1 hz2
    exact pow_pos h2 2
  -- the majorant: `HkIntegrand` is integrable in `θ` for every `z ∈ Iz` by `HkMem`
  have hint : Integrable (fun θ => (C / (Work.Spaces.w z) ^ 2) *
      Work.Spaces.HkIntegrand α k g z θ) (volume.restrict Work.Spaces.Iθ) :=
    (hm.1 z hzmem).const_mul (C / (Work.Spaces.w z) ^ 2)
  have haesm : AEStronglyMeasurable (fun θ => (Work.Spaces.pthIter m g z θ) ^ 2 *
      (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α))
      (volume.restrict Work.Spaces.Iθ) :=
    aesm_pthIter_sq_mul_sin_rpow hF m _ hz
  have hmem : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Work.Spaces.Iθ :=
    MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc
  have hpt := hC α g k hmk hα hg z hzmem
  refine hint.mono' haesm ?_
  filter_upwards [hpt, hmem] with θ hθ hθmem
  -- the slot is nonnegative on `Iθ`, so its norm is itself
  have hsin : 0 ≤ Real.sin (2 * θ) := by
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθmem
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθmem.1])
      (by linarith [hθmem.2, Real.pi_pos])
  have hslot : 0 ≤ (Work.Spaces.pthIter m g z θ) ^ 2 *
      (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin _)
  rw [Real.norm_eq_abs, abs_of_nonneg hslot, div_mul_eq_mul_div, le_div_iff₀ hw]
  calc (Work.Spaces.pthIter m g z θ) ^ 2 *
        (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α) * (Work.Spaces.w z) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter m g z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)) := by ring
    _ ≤ C * Work.Spaces.HkIntegrand α k g z θ := hθ

end Work.FTS.EllipticEst.Cores.Pieces
