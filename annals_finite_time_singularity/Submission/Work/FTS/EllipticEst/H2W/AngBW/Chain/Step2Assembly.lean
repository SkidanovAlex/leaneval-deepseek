import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Assembly
import Submission.Work.FTS.EllipticEst.AngAWeak.Basic
import Submission.Work.FTS.EllipticEst.remov.AeChainDefs
import Submission.Work.FTS.EllipticEst.remov.AeI1PaperDefs
import Submission.Work.FTS.EllipticEst.remov.AeIPMemsSlim
import Submission.Work.FTS.EllipticEst.H2W.AeWAux.aeI4Of
import Submission.Work.FTS.EllipticEst.H2W.AeWAux.i4SliceIneq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H2W/AngBW/Chain/Step2Assembly` — the arithmetic assembly of Step 2

The body below is a verbatim copy of the three (already proved) arithmetic theorems of
`Submission/Work/FTS/EllipticEst/remov/AeStep2Holds.lean` — `quad_solve_pos`,
`step2Ae_of_pos`, `aeStep1_of_full`, `AeI1LowerPos_of_paper` — with the two *analytic* inputs
`remov.AeStep1Full` and `remov.AeI1Paper` kept as explicit hypotheses.  The point of the copy is
to keep the import cone free of the three still-open leaf modules of `remov/`
(`AeStep1FullHolds`, `AeI1PaperHolds`, `AeI1LowerPosHolds`), so that `Step2` can be assembled
from *proved* versions of the two Props (supplied by the sibling modules
`AngBW/Chain/Step1FullProof` and `AngBW/Chain/I1PaperProof`).
-/

namespace Work.FTS.EllipticEst.H2W.AngBW

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

open Work.FTS.EllipticEst.AngSecond
open Work.FTS.EllipticEst.remov

/-- The quadratic solve used at the end of the assembly: if `X² ≤ K(N·X + N²)` with
`K, N ≥ 0` then `X ≤ (K+1)·N`.  (A copy of the private helper of `AngAWeak/Basic.lean`.) -/
private theorem quad_solve_pos {K X N : ℝ} (hK : 0 ≤ K) (hN : 0 ≤ N)
    (h : X ^ 2 ≤ K * (N * X + N ^ 2)) : X ≤ (K + 1) * N := by
  by_cases hX : X ≤ 0
  · nlinarith
  · push_neg at hX
    by_cases hN0 : N = 0
    · subst hN0
      have h2 : X ^ 2 ≤ 0 := by simpa using h
      have h3 : X = 0 := sq_eq_zero_iff.mp (le_antisymm h2 (sq_nonneg X))
      rw [h3]; simp
    · have hNpos : 0 < N := lt_of_le_of_ne hN (Ne.symm hN0)
      by_contra hcon
      push_neg at hcon
      have h1 : 0 < (X - (K + 1) * N) * N := mul_pos (by linarith) hNpos
      nlinarith [hcon, hK, h1, h]

/-- **The bare (positive-term-free) `I₁` lower bound** of Step 2 of `prop:H2` in the class
`AeData`: `-C α²(⟨z∂_zu, z∂_zu⟩_ρ + √⟨z∂_zu, z∂_zu⟩_ρ·√⟨∂_θθu, ∂_θθu⟩_ρ) ≤ α²⟨z²∂_zzu, ∂_θθu⟩_ρ`.

This is the form the Step-2 assembly consumes, and it is *implied* by the paper-shaped
`remov.AeI1Paper` (which keeps the extra nonnegative term
`(1-η)/(1+η)·α²‖∂_θ(z∂_zu)‖²_ρ` on the left) — see `i1Bare_of_paper`. -/
def AeI1Bare : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
      - C * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP
            (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u)
          + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
                (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u))
            * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
                (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u)))
        ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u)

/-- **The Step-1 input actually needed by the Step-2 assembly.**

Weaker than `remov.AeStep1Full` in that it does *not* require the radial bound
`α ‖z∂_zu‖_ρ ≤ C‖G‖_ρ` (which the assembly never uses): only the honesty of `u`, `z∂_zu`,
`u/cos θ` and the two norm bounds `‖u‖_ρ ≤ C‖G‖_ρ`,
`‖u/cos θ‖_ρ ≤ C(‖G‖_ρ + α‖z∂_zu‖_ρ)` are kept. -/
def AeStep1Lite : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 u ∧
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) ∧
      Work.Spaces.HkMem α 0 (fun z θ => u z θ / Real.cos θ) ∧
      Work.FTS.EllipticEst.H2W.Ae.nrm α u ≤ C * Work.FTS.EllipticEst.H2W.Ae.nrm α G ∧
      Work.FTS.EllipticEst.H2W.Ae.nrm α (fun z θ => u z θ / Real.cos θ)
        ≤ C * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
            + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (fun z θ => z * Work.Spaces.pz u z θ))

/-- **The assembly of Step 2 in the class `AeData`** from the three inputs:
Step 1 in the "lite" form `AeStep1Lite` (no `α‖z∂_zu‖`-bound), the honest `I₁` lower bound (`remov.AeI1Paper`) and
positive term `(1-η)/(1+η)·α²‖z∂_z∂_θu‖²_ρ`), the `I₄` upper bound (`AngAWeak.AeI4`) and the
`IPMem` bookkeeping (`AngAWeak.AeIPMems`).

Only the *weak* consequence `-C(‖G‖_ρ‖B‖_ρ + ‖G‖²_ρ) ≤ α²⟨z²∂_zzu, ∂_θθu⟩` of
`AeI1LowerPos` is used: the positive term is dropped (it is nonnegative), so the arithmetic
below is insensitive to whether it is present. -/
theorem step2_of_lite (h1 : AeStep1Lite)
    (h2 : AeI1Bare) (h3 : Work.FTS.EllipticEst.AngAWeak.AeI4)
    (h4 : Work.FTS.EllipticEst.AngAWeak.AeIPMems) :
    Work.FTS.EllipticEst.H2W.Ae.Step2 := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := h1
  obtain ⟨C₂, hC₂pos, hC₂⟩ := h2
  obtain ⟨C₃, hC₃pos, hC₃⟩ := h3
  have hC₁0 : (0 : ℝ) ≤ C₁ := hC₁pos.le
  have hC₂0 : (0 : ℝ) ≤ C₂ := hC₂pos.le
  have hC₃0 : (0 : ℝ) ≤ C₃ := hC₃pos.le
  refine ⟨max (C₂ + C₃ * C₁ ^ 2) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) + 1, ?_, ?_⟩
  · have h0 : (0 : ℝ) ≤ C₂ + C₃ * C₁ ^ 2 := by positivity
    have hle : (0 : ℝ) ≤ max (C₂ + C₃ * C₁ ^ 2) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) :=
      le_trans h0 (le_max_left _ _)
    linarith
  intro α u G hA
  obtain ⟨hmemu, hmemU, hmemPb, huBd, hPbBd⟩ := hC₁ α u G hA
  have hI1 := hC₂ α u G hA hmemU
  have hI4 := hC₃ α u hA.smooth hmemPb hA.memAng2
  obtain ⟨hFB, hQB, hUB, hG₁B, huB, hBB⟩ := h4 α u G hA hmemu hmemU
  have hα : 0 < α := hA.hα
  have hα4 : α ≤ 1 / 4 := hA.hα4
  have hsol := hA.eq
  have hmemG : Work.Spaces.HkMem α 0 G := hA.memG
  have hmemB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u) := hA.memAng2
  -- abbreviations
  set B : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 u with hBdef
  set Q : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ with hQdef
  set U : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz u z θ with hUdef
  set G₁ : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ
    with hG₁def
  set PbF : ℝ → ℝ → ℝ := fun z θ => u z θ / Real.cos θ with hPbFdef
  have hPbHon : Work.Spaces.HkMem α 0 PbF := hmemPb
  set f : ℝ := Work.FTS.EllipticEst.H2W.Ae.nrm α G with hfdef
  set b : ℝ := Work.FTS.EllipticEst.H2W.Ae.nrm α U with hbdef
  set X : ℝ := Work.FTS.EllipticEst.H2W.Ae.nrm α B with hXdef
  set N : ℝ := f + α * b with hNdef
  set Pb : ℝ := Work.FTS.EllipticEst.H2W.Ae.nrm α PbF with hPbdef
  set m : ℝ := Work.FTS.EllipticEst.H2W.Ae.nrm α u with hmdef
  have hf0 : 0 ≤ f := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  have hPb0 : 0 ≤ Pb := Real.sqrt_nonneg _
  have hm0 : 0 ≤ m := Real.sqrt_nonneg _
  -- ## `HkSq` versus the honest `IP`-pairing
  have hb2 : b ^ 2 = IP U U := by
    rw [hbdef, hUdef, Work.FTS.EllipticEst.H2W.Ae.nrm,
      Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
    exact Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  have hX2 : X ^ 2 = IP B B := by
    rw [hXdef, hBdef, Work.FTS.EllipticEst.H2W.Ae.nrm,
      Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
    exact Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  have hf2 : f ^ 2 = IP G G := by
    rw [hfdef, Work.FTS.EllipticEst.H2W.Ae.nrm,
      Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
    exact Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  have hPb2 : Pb ^ 2 = IP PbF PbF := by
    rw [hPbdef, hPbFdef, Work.FTS.EllipticEst.H2W.Ae.nrm,
      Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
    exact Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  have hXeq : Real.sqrt (IP B B) = X := by
    rw [← hX2]; exact Real.sqrt_sq hX0
  have hbeq : Real.sqrt (IP U U) = b := by
    rw [← hb2]; exact Real.sqrt_sq hb0
  have hfeq : Real.sqrt (IP G G) = f := by
    rw [← hf2]; exact Real.sqrt_sq hf0
  have hmeq : Real.sqrt (IP u u) = m := by
    rw [hmdef, Work.FTS.EllipticEst.H2W.Ae.nrm,
      Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
  have hPbeq : Real.sqrt (IP PbF PbF) = Pb := by
    rw [← hPb2]; exact Real.sqrt_sq hPb0
  -- ## the identity, the pieces, and Cauchy–Schwarz
  have hid := Work.FTS.EllipticEst.AngAWeak.I_identity_weak α G u hsol hFB hQB hUB hG₁B huB hBB
  have hcsG := IP_cauchy_schwarz
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmemG)
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmemB) hFB
  have hcsU := IP_cauchy_schwarz
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmemU)
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmemB) hUB
  have hcsu := IP_cauchy_schwarz
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmemu)
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmemB) huB
  -- ## the `I₁` input, in the weak form actually used
  have hI1B : -C₂ * α ^ 2 * (IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
          (Work.FTS.EllipticEst.H2W.Ae.grad u)
        + Real.sqrt (IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
              (Work.FTS.EllipticEst.H2W.Ae.grad u)) * Real.sqrt (IP B B))
      ≤ α ^ 2 * IP Q B := hI1
  -- ## the bounds of the individual pieces
  have e1 : -α ^ 2 * IP Q B ≤ C₂ * (α ^ 2 * b ^ 2) + C₂ * ((α ^ 2 * b) * X) := by
    have hU' : IP (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u)
        = b ^ 2 := by
      change IP U U = b ^ 2
      exact hb2.symm
    rw [hU', Real.sqrt_sq hb0, hXeq] at hI1B
    have hring : C₂ * α ^ 2 * (b ^ 2 + b * X)
        = C₂ * (α ^ 2 * b ^ 2) + C₂ * ((α ^ 2 * b) * X) := by ring
    linarith [hI1B, hring.le, hring.ge]
  have e2 : -α * (5 + α) * IP U B ≤ (5 + α) * ((α * b) * X) := by
    have h := (abs_le.mp hcsU).1
    rw [hbeq, hXeq] at h
    have h5 : 0 ≤ α * (5 + α) := by nlinarith [hα]
    nlinarith [h, h5, hb0, hX0]
  have e3 : IP G₁ B ≤ C₃ * (Pb ^ 2 + Pb * X) := by
    have h := hI4
    rw [← Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq α PbF, ← hPb2, Real.sqrt_sq hPb0,
      ← Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq α B, ← hX2, Real.sqrt_sq hX0] at h
    exact h
  have e4 : -6 * IP u B ≤ 6 * (m * X) := by
    have h := (abs_le.mp hcsu).1
    rw [hmeq, hXeq] at h
    linarith [h]
  have e5 : -IP G B ≤ f * X := by
    have h := (abs_le.mp hcsG).1
    rw [hfeq, hXeq] at h
    linarith [h]
  -- ## the identity, solved for the pairing of `∂_θθu` with itself
  have hid' : IP B B
      = -α ^ 2 * IP Q B - α * (5 + α) * IP U B + IP G₁ B - 6 * IP u B - IP G B := by
    linarith [hid]
  -- ## the elementary consequences of the abbreviations
  have hNf : f ≤ N := by rw [hNdef]; nlinarith [hb0, hα.le]
  have hNb : α * b ≤ N := by rw [hNdef]; nlinarith [hf0]
  have hfX : f * X ≤ N * X := mul_le_mul_of_nonneg_right hNf hX0
  have hf2N : f ^ 2 ≤ N ^ 2 := by
    calc f ^ 2 = f * f := by ring
      _ ≤ N * N := mul_self_le_mul_self hf0 hNf
      _ = N ^ 2 := by ring
  have h5bb : (5 + α) * ((α * b) * X) ≤ (21 / 4) * (N * X) := by
    have h1 : 5 + α ≤ 21 / 4 := by linarith
    have h2 : 0 ≤ (α * b) * X := by positivity
    have h3 : (α * b) * X ≤ N * X := mul_le_mul_of_nonneg_right hNb hX0
    calc (5 + α) * ((α * b) * X) ≤ (21 / 4) * ((α * b) * X) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ ≤ (21 / 4) * (N * X) := mul_le_mul_of_nonneg_left h3 (by norm_num)
  have hmb : m ≤ C₁ * N := by
    have h1 : m ≤ C₁ * f := by rw [hmdef, hfdef]; exact huBd
    exact le_trans h1 (mul_le_mul_of_nonneg_left hNf hC₁pos.le)
  have hPbb : Pb ≤ C₁ * N := by
    rw [hPbdef, hPbFdef, hNdef, hfdef, hbdef]
    exact hPbBd
  have hPb2b : Pb ^ 2 ≤ (C₁ * N) ^ 2 := by
    calc Pb ^ 2 = Pb * Pb := by ring
      _ ≤ (C₁ * N) * (C₁ * N) := mul_self_le_mul_self hPb0 hPbb
      _ = (C₁ * N) ^ 2 := by ring
  have hPbX : Pb * X ≤ (C₁ * N) * X := mul_le_mul_of_nonneg_right hPbb hX0
  have hmX : m * X ≤ (C₁ * N) * X := mul_le_mul_of_nonneg_right hmb hX0
  -- ## the collection
  have hkey : X ^ 2 ≤ (C₂ + C₃ * C₁ ^ 2) * N ^ 2
      + (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X) := by
    have hsum : X ^ 2 ≤ C₂ * (α ^ 2 * b ^ 2) + C₂ * ((α ^ 2 * b) * X) + (5 + α) * ((α * b) * X)
        + C₃ * (Pb ^ 2 + Pb * X) + 6 * (m * X) + f * X := by
      rw [hX2, hid']
      linarith [e1, e2, e3, e4, e5]
    have hαb2 : α ^ 2 * b ^ 2 ≤ N ^ 2 := by
      have h0 : 0 ≤ α * b := mul_nonneg hα.le hb0
      have h1 : (α * b) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ h0 hNb 2
      calc α ^ 2 * b ^ 2 = (α * b) ^ 2 := by ring
        _ ≤ N ^ 2 := h1
    have hαbX : (α ^ 2 * b) * X ≤ N * X := by
      have hle : α ^ 2 * b ≤ N := by
        calc α ^ 2 * b = α * (α * b) := by ring
          _ ≤ α * N := mul_le_mul_of_nonneg_left hNb hα.le
          _ ≤ 1 * N := mul_le_mul_of_nonneg_right (by linarith) hN0
          _ = N := by ring
      exact mul_le_mul_of_nonneg_right hle hX0
    have t1 : C₂ * (α ^ 2 * b ^ 2) + C₂ * ((α ^ 2 * b) * X) ≤ C₂ * (N ^ 2 + N * X) := by
      have h := mul_le_mul_of_nonneg_left (by linarith [hαb2, hαbX] :
        α ^ 2 * b ^ 2 + (α ^ 2 * b) * X ≤ N ^ 2 + N * X) hC₂0
      linarith [h]
    have t4 : C₃ * (Pb ^ 2 + Pb * X) ≤ C₃ * ((C₁ * N) ^ 2 + (C₁ * N) * X) :=
      mul_le_mul_of_nonneg_left (by linarith [hPb2b, hPbX]) hC₃0
    have t5 : 6 * (m * X) ≤ 6 * ((C₁ * N) * X) :=
      mul_le_mul_of_nonneg_left hmX (by norm_num)
    have hcollect : C₂ * (α ^ 2 * b ^ 2) + C₂ * ((α ^ 2 * b) * X) + (5 + α) * ((α * b) * X)
        + C₃ * (Pb ^ 2 + Pb * X) + 6 * (m * X) + f * X
        ≤ C₂ * (N ^ 2 + N * X) + (21 / 4) * (N * X)
          + C₃ * ((C₁ * N) ^ 2 + (C₁ * N) * X) + 6 * ((C₁ * N) * X) + N * X := by
      linarith [t1, h5bb, t4, t5, hfX]
    calc X ^ 2
        ≤ C₂ * (N ^ 2 + N * X) + (21 / 4) * (N * X)
          + C₃ * ((C₁ * N) ^ 2 + (C₁ * N) * X) + 6 * ((C₁ * N) * X) + N * X :=
          le_trans hsum hcollect
      _ = (C₂ + C₃ * C₁ ^ 2) * N ^ 2
          + (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X) := by ring
  have hmain : X ^ 2 ≤ max (C₂ + C₃ * C₁ ^ 2)
      (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X + N ^ 2) := by
    have h1 : (C₂ + C₃ * C₁ ^ 2) * N ^ 2
        ≤ max (C₂ + C₃ * C₁ ^ 2) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * N ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg N)
    have h2 : (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X)
        ≤ max (C₂ + C₃ * C₁ ^ 2) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hN0 hX0)
    have h3 : max (C₂ + C₃ * C₁ ^ 2)
          (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X + N ^ 2)
        = max (C₂ + C₃ * C₁ ^ 2) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X)
          + max (C₂ + C₃ * C₁ ^ 2) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * N ^ 2 := by
      ring
    rw [h3]
    linarith [hkey, h1, h2]
  have hKmax : 0 ≤ max (C₂ + C₃ * C₁ ^ 2) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) := by
    have h0 : (0 : ℝ) ≤ C₂ + C₃ * C₁ ^ 2 := by positivity
    exact le_trans h0 (le_max_left _ _)
  have hfinal := quad_solve_pos hKmax hN0 hmain
  calc Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.Spaces.pthIter 2 u) = X := by rw [hXdef, hBdef]
    _ ≤ (max (C₂ + C₃ * C₁ ^ 2) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) + 1) * N := hfinal
    _ = (max (C₂ + C₃ * C₁ ^ 2) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) + 1)
        * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
          + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (fun z θ => z * Work.Spaces.pz u z θ)) := by
      rw [hNdef, hfdef, hbdef, hUdef]

/-- **`AngAWeak.AeStep1` from `AeStep1Full`**: the companion bound
`‖u/cos θ‖_ρ ≤ C(‖G‖_ρ + α‖z∂_zu‖_ρ)` of Step 1 is strengthened to `‖u/cos θ‖_ρ ≤ C‖G‖_ρ`
with Step 1's first-order bound on `α‖z∂_zu‖_ρ`. -/
theorem aeStep1_of_full (h : AeStep1Full) : Work.FTS.EllipticEst.AngAWeak.AeStep1 := by
  obtain ⟨C, hC, h'⟩ := h
  have hC0 : (0 : ℝ) ≤ C := le_of_lt hC
  refine ⟨max C (C + C * C), lt_max_of_lt_left hC, ?_⟩
  intro α u G hA
  obtain ⟨hmu, hmU, hmBar, huB, hUB, hBarB⟩ := h' α u G hA
  have hG0 : 0 ≤ Work.FTS.EllipticEst.H2W.Ae.nrm α G := Real.sqrt_nonneg _
  have hKey : Work.FTS.EllipticEst.H2W.Ae.nrm α (fun z θ => u z θ / Real.cos θ)
      ≤ (C + C * C) * Work.FTS.EllipticEst.H2W.Ae.nrm α G := by
    have h1 : C * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
        + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u))
        ≤ C * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
            + C * Work.FTS.EllipticEst.H2W.Ae.nrm α G) := by
      refine mul_le_mul_of_nonneg_left ?_ hC0
      linarith [hUB]
    have h2 : C * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
          + C * Work.FTS.EllipticEst.H2W.Ae.nrm α G)
        = (C + C * C) * Work.FTS.EllipticEst.H2W.Ae.nrm α G := by ring
    linarith [hBarB, h1, h2.le, h2.ge]
  refine ⟨hmu, hmU, hmBar, ?_, ?_⟩
  · calc Work.FTS.EllipticEst.H2W.Ae.nrm α u
        ≤ C * Work.FTS.EllipticEst.H2W.Ae.nrm α G := huB
      _ ≤ max C (C + C * C) * Work.FTS.EllipticEst.H2W.Ae.nrm α G :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hG0
  · calc Work.FTS.EllipticEst.H2W.Ae.nrm α (fun z θ => u z θ / Real.cos θ)
        ≤ (C + C * C) * Work.FTS.EllipticEst.H2W.Ae.nrm α G := hKey
      _ ≤ max C (C + C * C) * Work.FTS.EllipticEst.H2W.Ae.nrm α G :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hG0

/-- **`AeI1LowerPos` from `AeI1Paper` and Step 1**: the `⟨z∂_zu, z∂_zu⟩`-errors of the
paper-shaped bound are converted into `‖G‖_ρ`-errors with Step 1's
`α‖z∂_zu‖_ρ ≤ C‖G‖_ρ`.  Indeed `α²⟨z∂_zu, z∂_zu⟩ = (α‖z∂_zu‖_ρ)²` and
`α²√⟨z∂_zu, z∂_zu⟩·√⟨∂_θθu, ∂_θθu⟩ = α·(α‖z∂_zu‖_ρ)·‖∂_θθu‖_ρ`, and
`α‖z∂_zu‖_ρ ≤ C₁‖G‖_ρ`, `α ≤ 1`. -/
theorem AeI1LowerPos_of_paper (h1 : AeStep1Full) (h2 : AeI1Paper) : AeI1LowerPos := by
  obtain ⟨C₁, hC₁, h₁⟩ := h1
  obtain ⟨C, hC, h'⟩ := h2
  have hC10 : (0 : ℝ) ≤ C₁ := le_of_lt hC₁
  have hC0 : (0 : ℝ) ≤ C := le_of_lt hC
  refine ⟨C * max C₁ (C₁ * C₁), by positivity, ?_⟩
  intro α u G hA
  obtain ⟨hmu, hmU, hmBar, huBd, hUBd, hBarBd⟩ := h₁ α u G hA
  have hpaper := h' α u G hA hmU
  have hα : 0 < α := hA.hα
  have hα1 : α ≤ 1 := by linarith [hA.hα4]
  set f : ℝ := Work.FTS.EllipticEst.H2W.Ae.nrm α G with hfdef
  set u₁ : ℝ := Work.FTS.EllipticEst.H2W.Ae.nrm α
    (Work.FTS.EllipticEst.H2W.Ae.grad u) with hu1def
  set X : ℝ := Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.Spaces.pthIter 2 u) with hXdef
  have hf0 : 0 ≤ f := Real.sqrt_nonneg _
  have hu10 : 0 ≤ u₁ := Real.sqrt_nonneg _
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hbBd : α * u₁ ≤ C₁ * f := by
    rw [hu1def, hfdef]; exact hUBd
  have hA' : α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
        (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u)
      = (α * u₁) ^ 2 := by
    rw [Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq, hu1def, Work.FTS.EllipticEst.H2W.Ae.nrm,
      mul_pow, Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)]
  have hB' : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
        (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u)) = u₁ := by
    rw [Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq, hu1def, Work.FTS.EllipticEst.H2W.Ae.nrm]
  have hX' : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
        (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u)) = X := by
    rw [Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq, hXdef, Work.FTS.EllipticEst.H2W.Ae.nrm]
  have hpiece : C * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP
          (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u)
        + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
              (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u)))
      ≤ (C * max C₁ (C₁ * C₁)) * (f * X + f ^ 2) := by
    rw [hB', hX']
    have h5 : α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP
          (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u) + u₁ * X)
        = (α * u₁) ^ 2 + α * (α * u₁) * X := by
      rw [mul_add, hA']; ring
    have hs : (α * u₁) ^ 2 ≤ (C₁ * f) ^ 2 := by
      have h0 : 0 ≤ α * u₁ := mul_nonneg hα.le hu10
      exact pow_le_pow_left₀ h0 hbBd 2
    have ht : α * (α * u₁) * X ≤ (C₁ * f) * X := by
      have hle : α * (α * u₁) ≤ C₁ * f := by
        calc α * (α * u₁) ≤ α * (C₁ * f) := mul_le_mul_of_nonneg_left hbBd hα.le
          _ ≤ 1 * (C₁ * f) := mul_le_mul_of_nonneg_right hα1 (mul_nonneg hC10 hf0)
          _ = C₁ * f := by ring
      exact mul_le_mul_of_nonneg_right hle hX0
    have h7 : (α * u₁) ^ 2 + α * (α * u₁) * X ≤ max C₁ (C₁ * C₁) * (f * X + f ^ 2) := by
      have h3 : C₁ * C₁ * f ^ 2 ≤ max C₁ (C₁ * C₁) * f ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg f)
      have h4 : C₁ * f * X ≤ max C₁ (C₁ * C₁) * (f * X) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hf0 hX0)
      have e3 : max C₁ (C₁ * C₁) * (f * X + f ^ 2)
          = max C₁ (C₁ * C₁) * (f * X) + max C₁ (C₁ * C₁) * f ^ 2 := by ring
      have e : (C₁ * f) ^ 2 + (C₁ * f) * X ≤ max C₁ (C₁ * C₁) * (f * X + f ^ 2) := by
        rw [e3]
        have e1 : (C₁ * f) ^ 2 = C₁ * C₁ * f ^ 2 := by ring
        rw [e1]
        linarith [h3, h4]
      linarith [hs, ht, e]
    calc C * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP
          (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u) + u₁ * X)
        = C * (α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u)
            + u₁ * X)) := by ring
      _ = C * ((α * u₁) ^ 2 + α * (α * u₁) * X) := by rw [h5]
      _ ≤ C * (max C₁ (C₁ * C₁) * (f * X + f ^ 2)) := mul_le_mul_of_nonneg_left h7 hC0
      _ = (C * max C₁ (C₁ * C₁)) * (f * X + f ^ 2) := by ring
  -- combine with the paper-shaped bound
  have hmain : ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) *
        (α ^ 2 * Work.Spaces.HkSq α 0
          (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u)))
      - (C * max C₁ (C₁ * C₁)) * (f * X + f ^ 2)
      ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u) := by
    linarith [hpaper, hpiece]
  simpa only [hfdef, hXdef] using hmain


/-- **Step 2 of `prop:H2` from the two analytic inputs.** -/
theorem step2_of (h1 : AeStep1Lite) (h2 : AeI1Bare) : Work.FTS.EllipticEst.H2W.Ae.Step2 :=
  step2_of_lite h1 h2
    (Work.FTS.EllipticEst.H2W.AeWAux.aeI4Of Work.FTS.EllipticEst.H2W.AeWAux.i4SliceIneq)
    Work.FTS.EllipticEst.remov.aeIPMemsSlim

/-- `AeI1Paper` (with the positive term `(1-η)/(1+η)·α²‖∂_θ(z∂_zu)‖²_ρ`) implies the bare form
`AeI1Bare` (drop a nonnegative left-hand term). -/
theorem i1Bare_of_paper (h : AeI1Paper) : AeI1Bare := by
  obtain ⟨C, hC, h'⟩ := h
  refine ⟨C, hC, fun α u G hA hmem => ?_⟩
  have hpos : 0 ≤ (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta) *
      (α ^ 2 * Work.Spaces.HkSq α 0
        (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u))) := by
    refine mul_nonneg ?_ ?_
    · rw [div_nonneg_iff]
      left
      constructor <;> · rw [Work.Spaces.eta]; norm_num
    · exact mul_nonneg (sq_nonneg α) (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  linarith [h' α u G hA hmem, hpos]

end Work.FTS.EllipticEst.H2W.AngBW
