/-
# `Prop.l0_second_aux` — the assembly of the second-order angular estimate (weak class)

This module holds the paper's Step-2 assembly `l0_second_of_i1hh` (plus its elementary quadratic
solve), for the target `Work.FTS.EllipticEst.Prop.l0_second` of `Prop/l0_second.lean`: from the
`I₁` coercivity in the a.e. class *with the two first-order honesties* (`Prop.i1_bare_hh`, proved)
and the first-order estimate `hfirst` (which supplies `Ψ`, `z∂_zΨ`, `Ψ/cos θ`), one obtains

  `‖∂_θθΨ‖_{ℋ⁰} ≤ C(‖F‖_{ℋ⁰} + α‖z∂_zΨ‖_{ℋ⁰})`.

The strengthened weak class `TT.EllWeakPos` supplies the diagonal second-order honesty
`HkMem α 0 (∂_θθ(z∂_zΨ))` as its tenth conjunct (`EllWeakPos.memZPth2`), which is the input
Step 2 of `prop:H2` consumes.
-/

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Honest.Gap9Open
import Submission.Work.FTS.EllipticEst.Honest.SigmaPoincare
import Submission.Work.FTS.EllipticEst.TT.weakIPMems
import Submission.Work.FTS.EllipticEst.AngAWeak.Basic
import Submission.Work.FTS.EllipticEst.H2W.AeWAux.aeI4Of
import Submission.Work.FTS.EllipticEst.H2W.AeWAux.i4SliceIneq
import Submission.Work.FTS.EllipticEst.remov.AeIPMemsSlim
import Submission.Work.FTS.EllipticEst.H2W.Ae.Assembly
import Submission.Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz
import Submission.Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem
import Submission.Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000
/-- **The quadratic solve.**  From `0 ≤ K`, `0 ≤ N` and `X ^ 2 ≤ K * (N ^ 2 + N * X)` one gets
`X ≤ (K + 1) * N`. -/
private theorem quad_solve' {K X N : ℝ} (hK : 0 ≤ K) (hN : 0 ≤ N)
    (h : X ^ 2 ≤ K * (N ^ 2 + N * X)) : X ≤ (K + 1) * N := by
  by_contra hc
  rw [not_le] at hc
  have hXpos : 0 < X := by
    have : 0 ≤ (K + 1) * N := by positivity
    linarith
  have hXN : 0 < X + N := by linarith
  have hprod : 0 < (X - (K + 1) * N) * (X + N) := mul_pos (by linarith) hXN
  have hid : (X - (K + 1) * N) * (X + N) = X ^ 2 - K * (N * X) - K * N ^ 2 - N ^ 2 := by ring
  nlinarith [hprod, hid, h, sq_nonneg N, hK]

/-- **The assembly of Step 2 in the weak class from the honest `I₁` lower bound.**

Assuming the `I₁` coercivity in the a.e. class *with the two first-order honesties* — i.e. exactly
the statement of `Prop.i1_bare_hh`, which the strengthened weak class `TT.EllWeakPos` supplies
through its tenth conjunct `EllWeakPos.memZPth2` — and the first-order estimate `hfirst`, the
second-order angular estimate holds.

The proof is the paper's Step 2: pair the equation with `-∂_θθΨ·w²σ`
(`AngAWeak.I_identity_weak`), bound the five pieces (`I₁` by hypothesis, `I₂`/`I₅`/the source by
Cauchy–Schwarz, `I₄` by `H2W.AeWAux.aeI4Of` applied to `H2W.AeWAux.i4SliceIneq`), and solve the
resulting quadratic inequality with the Step-1 data supplied by `hfirst`. -/
theorem l0_second_of_i1hh (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hI1 : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) →
        Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) →
        - C * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z * Work.Spaces.pz u z θ)
              (fun z θ => z * Work.Spaces.pz u z θ)
            + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z * Work.Spaces.pz u z θ)
                  (fun z θ => z * Work.Spaces.pz u z θ))
              * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                  (Work.Spaces.pthIter 2 u)))
          ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u))
    (hfirst : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
      Work.Spaces.HkMem α 0 Ψ ∧
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) ∧
      Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
      Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
        + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))
        + Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
        ≤ C₁ * Real.sqrt (Work.Spaces.HkSq α 0 F)) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
      Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
        ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))) := by
  obtain ⟨C₂, hC₂pos, hI1'⟩ := hI1
  obtain ⟨C₃, hC₃pos, hI4'⟩ := Work.FTS.EllipticEst.H2W.AeWAux.aeI4Of
    Work.FTS.EllipticEst.H2W.AeWAux.i4SliceIneq
  refine ⟨max (C₂ + C₃ * C₁ ^ 2) (C₂ + C₃ * C₁ + 6 * C₁ + 7) + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 hW
  -- ## the Step-1 data supplied by the first-order estimate
  obtain ⟨hmemΨ, hmemU, hmemPb, hstep1⟩ := hfirst α F Ψ hα hα4 hW
  -- ## the six honesty pairings of the Step-2 identity
  obtain ⟨hFB, hQB, hUB, hG₁B, hΨB, hBB⟩ :=
    Work.FTS.EllipticEst.TT.weakIPMems α F Ψ hα hα4 hW hmemΨ hmemU
  -- ## the almost-everywhere class
  have haeΨ : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar Ψ z = 0 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun z hz => hW.orthPsi z hz
  have haeF : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar F z = 0 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun z hz => hW.orthF z hz
  have hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α Ψ F :=
    ⟨hα, hα4, fun z hz θ h0 h1 => hW.eq z hz θ h0 h1, hW.zero, hW.pi_half, hW.smooth,
      hW.memF, hW.memA, hW.memB, haeΨ, haeF⟩
  -- ## abbreviations
  set B : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ with hB
  set Q : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ with hQ
  set U : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz Ψ z θ with hU
  set G₁ : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ with hG₁
  set PbF : ℝ → ℝ → ℝ := fun z θ => Ψ z θ / Real.cos θ with hPbF
  set f : ℝ := Real.sqrt (Work.Spaces.HkSq α 0 F) with hf
  set b : ℝ := Real.sqrt (Work.Spaces.HkSq α 0 U) with hb
  set X : ℝ := Real.sqrt (Work.Spaces.HkSq α 0 B) with hX
  set Pb : ℝ := Real.sqrt (Work.Spaces.HkSq α 0 PbF) with hPb
  set m : ℝ := Real.sqrt (Work.Spaces.HkSq α 0 Ψ) with hm
  have hf0 : 0 ≤ f := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hm0 : 0 ≤ m := Real.sqrt_nonneg _
  have hPb0 : 0 ≤ Pb := Real.sqrt_nonneg _
  -- ## `HkSq` versus the honest pairing `IP`
  have hb2 : b ^ 2 = Work.FTS.EllipticEst.AngSecond.IP U U := by
    rw [hb, hU, Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
    exact Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  have hX2 : X ^ 2 = Work.FTS.EllipticEst.AngSecond.IP B B := by
    rw [hX, hB, Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
    exact Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  have hPb2 : Pb ^ 2 = Work.FTS.EllipticEst.AngSecond.IP PbF PbF := by
    rw [hPb, hPbF, Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
    exact Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  have hm2 : m ^ 2 = Work.FTS.EllipticEst.AngSecond.IP Ψ Ψ := by
    rw [hm, Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
    exact Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  have hbX : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP U U) = b := by
    rw [← hb2]; exact Real.sqrt_sq hb0
  have hXX : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP B B) = X := by
    rw [← hX2]; exact Real.sqrt_sq hX0
  have hmX : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP Ψ Ψ) = m := by
    rw [← hm2]; exact Real.sqrt_sq hm0
  have hHkPbF : Work.Spaces.HkSq α 0 PbF = Pb ^ 2 := by
    rw [hPb2, Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
  have hHkB : Work.Spaces.HkSq α 0 B = X ^ 2 := by
    rw [hX2, Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
  have hHkF : Work.Spaces.HkSq α 0 F = f ^ 2 := by
    rw [hf, Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α F)]
  -- ## the two deep inputs, in the notation of the assembly
  have hI1b : -C₂ * α ^ 2
      * (Work.FTS.EllipticEst.AngSecond.IP U U
        + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP U U)
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP B B))
      ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP Q B :=
    hI1' α Ψ F hAe hmemU (Work.FTS.EllipticEst.TT.EllWeakPos.memZPth2 hW)
  have hI4b : Work.FTS.EllipticEst.AngSecond.IP G₁ B
      ≤ C₃ * (Work.Spaces.HkSq α 0 PbF
        + Real.sqrt (Work.Spaces.HkSq α 0 PbF) * Real.sqrt (Work.Spaces.HkSq α 0 B)) :=
    hI4' α Ψ hW.smooth hmemPb hW.memB
  -- ## the Step-2 pairing identity
  have hid : α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP Q B
        + α * (5 + α) * Work.FTS.EllipticEst.AngSecond.IP U B
        + Work.FTS.EllipticEst.AngSecond.IP B B
        - Work.FTS.EllipticEst.AngSecond.IP G₁ B
        + 6 * Work.FTS.EllipticEst.AngSecond.IP Ψ B
      = -Work.FTS.EllipticEst.AngSecond.IP F B :=
    Work.FTS.EllipticEst.AngAWeak.I_identity_weak α F Ψ
      (fun z hz θ h0 h1 => hW.eq z hz θ h0 h1) hFB hQB hUB hG₁B hΨB hBB
  -- ## Cauchy–Schwarz for the `I₂`, `I₅` and source slots
  have hcsU : |Work.FTS.EllipticEst.AngSecond.IP U B|
      ≤ Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP U U)
        * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP B B) :=
    Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz
      (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmemU)
      (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hW.memB) hUB
  have hcsΨ : |Work.FTS.EllipticEst.AngSecond.IP Ψ B|
      ≤ Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP Ψ Ψ)
        * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP B B) :=
    Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz
      (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmemΨ)
      (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hW.memB) hΨB
  have hcsF : |Work.FTS.EllipticEst.AngSecond.IP F B|
      ≤ Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP F F)
        * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP B B) :=
    Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz
      (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hW.memF)
      (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hW.memB) hFB
  -- ## the bounds of the individual pieces
  have hI1b' : -C₂ * α ^ 2 * (b ^ 2 + b * X) ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP Q B := by
    have h := hI1b
    rw [← hb2, hXX, Real.sqrt_sq hb0] at h
    exact h
  have e1 : -α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP Q B
      ≤ C₂ * (α ^ 2 * (b ^ 2 + b * X)) := by
    linarith only [hI1b']
  have e2 : -α * (5 + α) * Work.FTS.EllipticEst.AngSecond.IP U B
      ≤ (5 + α) * ((α * b) * X) := by
    have h := (abs_le.mp hcsU).1
    rw [hbX, hXX] at h
    have h5 : 0 ≤ α * (5 + α) := by nlinarith only [hα]
    nlinarith only [h, h5, hb0, hX0]
  have e3 : Work.FTS.EllipticEst.AngSecond.IP G₁ B ≤ C₃ * (Pb ^ 2 + Pb * X) := by
    have h := hI4b
    rw [hHkPbF, hHkB, Real.sqrt_sq hPb0, Real.sqrt_sq hX0] at h
    exact h
  have e4 : -6 * Work.FTS.EllipticEst.AngSecond.IP Ψ B ≤ 6 * (m * X) := by
    have h := (abs_le.mp hcsΨ).1
    rw [hXX, hmX] at h
    linarith only [h]
  have heqF : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP F F) = f := by
    rw [Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq α F, hf]
  have e5 : -Work.FTS.EllipticEst.AngSecond.IP F B ≤ f * X := by
    have h := (abs_le.mp hcsF).1
    rw [hXX, heqF] at h
    linarith only [h]
  -- ## the identity, solved for the self-pairing of `∂_θθΨ`
  have hid' : Work.FTS.EllipticEst.AngSecond.IP B B
      = -α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP Q B
        - α * (5 + α) * Work.FTS.EllipticEst.AngSecond.IP U B
        + Work.FTS.EllipticEst.AngSecond.IP G₁ B
        - 6 * Work.FTS.EllipticEst.AngSecond.IP Ψ B
        - Work.FTS.EllipticEst.AngSecond.IP F B := by
    linarith only [hid]
  -- ## the identity, solved for the self-pairing of `∂_θθΨ`
  have hid' : Work.FTS.EllipticEst.AngSecond.IP B B
      = -α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP Q B
        - α * (5 + α) * Work.FTS.EllipticEst.AngSecond.IP U B
        + Work.FTS.EllipticEst.AngSecond.IP G₁ B
        - 6 * Work.FTS.EllipticEst.AngSecond.IP Ψ B
        - Work.FTS.EllipticEst.AngSecond.IP F B := by
    linarith only [hid]
  -- ## the Step-1 bounds
  have hstep1' : m + α * b + Pb ≤ C₁ * f := by
    have h := hstep1
    rw [hm, hb, hPb, hf] at h
    exact h
  have hm_le : m ≤ C₁ * f := by
    have h2 : 0 ≤ α * b := mul_nonneg hα.le hb0
    linarith only [hstep1', h2, hPb0]
  have hPb_le : Pb ≤ C₁ * f := by
    have h2 : 0 ≤ α * b := mul_nonneg hα.le hb0
    linarith only [hstep1', h2, hm0]
  -- ## the collected bound
  set N : ℝ := f + α * b with hN
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  have hNf : f ≤ N := by rw [hN]; nlinarith only [hb0, hα.le]
  have hNb : α * b ≤ N := by rw [hN]; nlinarith only [hf0]
  have hαb2 : α ^ 2 * b ^ 2 ≤ N ^ 2 := by
    have h1 : α ^ 2 * b ^ 2 = (α * b) ^ 2 := by ring
    rw [h1]
    exact pow_le_pow_left₀ (mul_nonneg hα.le hb0) hNb 2
  have hαbX : α ^ 2 * b * X ≤ N * X := by
    have h1 : α ^ 2 * b ≤ N := by
      have h2 : α ^ 2 * b = α * (α * b) := by ring
      rw [h2]
      have h3 : α * (α * b) ≤ α * N := mul_le_mul_of_nonneg_left hNb hα.le
      have h4 : α * N ≤ 1 * N := mul_le_mul_of_nonneg_right (by linarith) hN0
      linarith only [h3, h4]
    exact mul_le_mul_of_nonneg_right h1 hX0
  have h5bX : (5 + α) * ((α * b) * X) ≤ 6 * (N * X) := by
    have h1 : 5 + α ≤ 6 := by linarith
    have h2 : 0 ≤ (α * b) * X := by positivity
    have h3 : (α * b) * X ≤ N * X := mul_le_mul_of_nonneg_right hNb hX0
    calc (5 + α) * ((α * b) * X) ≤ 6 * ((α * b) * X) := mul_le_mul_of_nonneg_right h1 h2
      _ ≤ 6 * (N * X) := by linarith only [h3]
  have hPb2_le : Pb ^ 2 ≤ C₁ ^ 2 * N ^ 2 := by
    have h1 : Pb ^ 2 ≤ (C₁ * f) ^ 2 := pow_le_pow_left₀ hPb0 hPb_le 2
    have h3 : 0 ≤ C₁ := hC₁.le
    have h4 : C₁ * f ≤ C₁ * N := mul_le_mul_of_nonneg_left hNf h3
    have h2 : (C₁ * f) ^ 2 ≤ (C₁ * N) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg h3 hf0) h4 2
    have h5 : (C₁ * N) ^ 2 = C₁ ^ 2 * N ^ 2 := by ring
    linarith only [h1, h2, h5.le, h5.ge]
  have hPbX_le : Pb * X ≤ C₁ * (N * X) := by
    have h1 : Pb * X ≤ (C₁ * f) * X := mul_le_mul_of_nonneg_right hPb_le hX0
    have h2 : (C₁ * f) * X ≤ (C₁ * N) * X := by
      nlinarith only [mul_le_mul_of_nonneg_right hNf hC₁.le, hX0]
    have h4 : (C₁ * N) * X = C₁ * (N * X) := by ring
    linarith only [h1, h2, h4.le, h4.ge]
  have hmX_le : m * X ≤ C₁ * (N * X) := by
    have h1 : m * X ≤ (C₁ * f) * X := mul_le_mul_of_nonneg_right hm_le hX0
    have h2 : (C₁ * f) * X ≤ (C₁ * N) * X := by
      nlinarith only [mul_le_mul_of_nonneg_right hNf hC₁.le, hX0]
    have h4 : (C₁ * N) * X = C₁ * (N * X) := by ring
    linarith only [h1, h2, h4.le, h4.ge]
  have hbase : X ^ 2 ≤ C₂ * (α ^ 2 * (b ^ 2 + b * X)) + (5 + α) * ((α * b) * X)
      + C₃ * (Pb ^ 2 + Pb * X) + 6 * (m * X) + f * X := by
    have h2 : X ^ 2 = -α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP Q B
        - α * (5 + α) * Work.FTS.EllipticEst.AngSecond.IP U B
        + Work.FTS.EllipticEst.AngSecond.IP G₁ B
        - 6 * Work.FTS.EllipticEst.AngSecond.IP Ψ B
        - Work.FTS.EllipticEst.AngSecond.IP F B := by
      rw [hX2, hid']
    linarith only [h2, e1, e2, e3, e4, e5]
  have p1 : C₂ * (α ^ 2 * (b ^ 2 + b * X)) ≤ C₂ * (N ^ 2 + N * X) := by
    have h1 : α ^ 2 * (b ^ 2 + b * X) ≤ N ^ 2 + N * X := by linarith only [hαb2, hαbX]
    exact mul_le_mul_of_nonneg_left h1 hC₂pos.le
  have p3 : C₃ * (Pb ^ 2 + Pb * X) ≤ C₃ * (C₁ ^ 2 * N ^ 2 + C₁ * (N * X)) := by
    have h1 : Pb ^ 2 + Pb * X ≤ C₁ ^ 2 * N ^ 2 + C₁ * (N * X) := by
      linarith only [hPb2_le, hPbX_le]
    exact mul_le_mul_of_nonneg_left h1 hC₃pos.le
  have p4 : 6 * (m * X) ≤ 6 * (C₁ * (N * X)) := by linarith only [hmX_le]
  have p5 : f * X ≤ N * X := mul_le_mul_of_nonneg_right hNf hX0
  have hkey : X ^ 2 ≤ max (C₂ + C₃ * C₁ ^ 2) (C₂ + C₃ * C₁ + 6 * C₁ + 7) * (N ^ 2 + N * X) := by
    have hNX0 : 0 ≤ N * X := mul_nonneg hN0 hX0
    have hN20 : 0 ≤ N ^ 2 := sq_nonneg N
    have hsum : X ^ 2 ≤ (C₂ + C₃ * C₁ ^ 2) * N ^ 2
        + (C₂ + C₃ * C₁ + 6 * C₁ + 7) * (N * X) := by
      nlinarith only [hbase, p1, h5bX, p3, p4, p5]
    have hle1 : (C₂ + C₃ * C₁ ^ 2) * N ^ 2
        ≤ max (C₂ + C₃ * C₁ ^ 2) (C₂ + C₃ * C₁ + 6 * C₁ + 7) * N ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hN20
    have hle2 : (C₂ + C₃ * C₁ + 6 * C₁ + 7) * (N * X)
        ≤ max (C₂ + C₃ * C₁ ^ 2) (C₂ + C₃ * C₁ + 6 * C₁ + 7) * (N * X) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hNX0
    have hgoal : max (C₂ + C₃ * C₁ ^ 2) (C₂ + C₃ * C₁ + 6 * C₁ + 7) * (N ^ 2 + N * X)
        = max (C₂ + C₃ * C₁ ^ 2) (C₂ + C₃ * C₁ + 6 * C₁ + 7) * N ^ 2
          + max (C₂ + C₃ * C₁ ^ 2) (C₂ + C₃ * C₁ + 6 * C₁ + 7) * (N * X) := by ring
    linarith only [hsum, hle1, hle2, hgoal.le, hgoal.ge]
  have hK0 : 0 ≤ max (C₂ + C₃ * C₁ ^ 2) (C₂ + C₃ * C₁ + 6 * C₁ + 7) := by
    have h1 : 0 ≤ C₂ + C₃ * C₁ ^ 2 := by positivity
    exact le_trans h1 (le_max_left _ _)
  have hfin := quad_solve' hK0 hN0 hkey
  rw [hX, hN, hf, hb] at hfin
  exact hfin

end Work.FTS.EllipticEst.Prop
