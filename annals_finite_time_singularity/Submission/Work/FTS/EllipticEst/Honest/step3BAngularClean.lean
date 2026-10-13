/-
Copyright: work module for the Elgindi finite-time singularity project.

# Step 2 of `prop:H2` (`∂_θθΨ`), in a clash-free cone

`Honest/step2Angular` proves `√(HkSq α 0 (∂_θθΨ)) ≤ C (√(HkSq α 0 F) + α√(HkSq α 0 (z∂_zΨ)))`
from the pairing identity `AngSecond.I_identity` plus the three analytic interfaces
`firstOrderHonest` (Step 1), `I1LowerHonest` (the `I₁` lower bound) and `I4UpperHonest`.
That file, however, imports `Honest.honCrossIPMems`, whose cone drags in
`ThetaPoincareDefs` and the `TT` frontier (see `HANDOFF.md`); together with the `I4*` cone it is
therefore not importable by any module that also needs the `TanTheta` slice identities.

This module reproduces the *same proof* with the same hypotheses, but takes the three analytic
interfaces as explicit slots and uses the local `stepCrossIPMems` for the six pairings, so that
its cone is exactly `{Basic, I4UpperHonest, AngSecond.I_identity, AngSecond.IP_cauchy_schwarz,
AngClean.IPMem_F_Phi, AngClean.HkMem_zero_IPMem}` — clash-free (374 files, 0 duplicate
declarations).  The proof is a verbatim adaptation of `Honest/step2Angular`'s.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.I4UpperHonest
import Submission.Work.FTS.EllipticEst.AngSecond.I_identity
import Submission.Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz
import Submission.Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 4000000

/-- **The final quadratic solve.**  From `X² ≤ K(NX + N²)` with `K, N ≥ 0` one gets
`X ≤ (K+1)N` (because `t ↦ t² - Kt - K` is positive for real `t > K+1`). -/
theorem step3QuadSolve {K X N : ℝ} (hK : 0 ≤ K) (hN : 0 ≤ N)
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

/-- **Step 2 of `prop:H2`, from explicit slots.**  `S1mem`/`S1memG`/`S1memQ` are the honesty of
`Ψ`, `z∂_zΨ`, `Ψ/cos θ` (Step 1), `S1b`/`S1bQ` the two norm bounds of Step 1, and `I1` is
`I1LowerHonest`.  The conclusion is the level-`0` `∂_θθΨ`-bound that Step 3 consumes. -/
theorem step3BAngularClean
    (C₁ C₂ : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (S1mem : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ → Work.Spaces.HkMem α 0 Ψ)
    (S1memG : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ →
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))
    (S1memQ : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ →
      Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ))
    (S1b : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ →
      Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
        ≤ C₁ * (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))))
    (S1bQ : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ →
      Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
        ≤ C₁ * (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))))
    (cross : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ →
      Work.Spaces.HkMem α 0 Ψ →
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) →
      Work.FTS.EllipticEst.AngSecond.IPMem F (Work.Spaces.pthIter 2 Ψ) ∧
      Work.FTS.EllipticEst.AngSecond.IPMem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        (Work.Spaces.pthIter 2 Ψ) ∧
      Work.FTS.EllipticEst.AngSecond.IPMem (fun z θ => z * Work.Spaces.pz Ψ z θ)
        (Work.Spaces.pthIter 2 Ψ) ∧
      Work.FTS.EllipticEst.AngSecond.IPMem Ψ (Work.Spaces.pthIter 2 Ψ) ∧
      Work.FTS.EllipticEst.AngSecond.IPMem
        (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
        (Work.Spaces.pthIter 2 Ψ) ∧
      Work.FTS.EllipticEst.AngSecond.IPMem (Work.Spaces.pthIter 2 Ψ)
        (Work.Spaces.pthIter 2 Ψ))
    (I1 : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ →
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) →
      - C₂ * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z * Work.Spaces.pz Ψ z θ)
              (fun z θ => z * Work.Spaces.pz Ψ z θ)
          + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z * Work.Spaces.pz Ψ z θ)
                (fun z θ => z * Work.Spaces.pz Ψ z θ))
            * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 Ψ)
                (Work.Spaces.pthIter 2 Ψ)))
      ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          (Work.Spaces.pthIter 2 Ψ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ →
        Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
          ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))) := by
  obtain ⟨C₃, hC₃pos, hC₃⟩ := I4UpperHonest
  have hK₁0 : (0 : ℝ) ≤ C₂ + C₃ * C₁ ^ 2 + C₃ := by positivity
  refine ⟨max (C₂ + C₃ * C₁ ^ 2 + C₃) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) + 1, by
    linarith [le_max_left (C₂ + C₃ * C₁ ^ 2 + C₃)
      (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1), hK₁0], ?_⟩
  intro α F Ψ hHon
  obtain ⟨hΨmem, hPab⟩ : Work.Spaces.HkMem α 0 Ψ ∧
      Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
        ≤ C₁ * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))) :=
    ⟨S1mem α F Ψ hHon, S1bQ α F Ψ hHon⟩
  obtain ⟨hUmem, hΨb⟩ : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) ∧
      Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
        ≤ C₁ * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))) :=
    ⟨S1memG α F Ψ hHon, S1b α F Ψ hHon⟩
  have hPaMem : Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) := S1memQ α F Ψ hHon
  obtain ⟨hFB, hQB, hUB, hΨB, huB, hBB⟩ := cross α F Ψ hHon hΨmem hUmem
  set f : ℝ := Real.sqrt (Work.Spaces.HkSq α 0 F) with hfdef
  set b : ℝ := Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ)) with hbdef
  set X : ℝ := Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)) with hXdef
  set N : ℝ := f + α * b with hNdef
  set Pb : ℝ := Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ)) with hPbdef
  set m : ℝ := Real.sqrt (Work.Spaces.HkSq α 0 Ψ) with hmdef
  have hα : 0 < α := hHon.hα
  have hα4 : α ≤ 1 / 4 := hHon.hα4
  have hf0 : 0 ≤ f := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  have hPb0 : 0 ≤ Pb := Real.sqrt_nonneg _
  -- ## `HkSq` versus the honest `IP`-pairing, and the Step 1 bounds
  have hb2 : b ^ 2 = Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z * Work.Spaces.pz Ψ z θ)
      (fun z θ => z * Work.Spaces.pz Ψ z θ) := by
    rw [hbdef, IP_self_eq_HkSq]
    exact Real.sq_sqrt (HkSq_zero_nonneg α _)
  have hX2 : X ^ 2 = Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 Ψ)
      (Work.Spaces.pthIter 2 Ψ) := by
    rw [hXdef, IP_self_eq_HkSq]
    exact Real.sq_sqrt (HkSq_zero_nonneg α _)
  have hf2 : f ^ 2 = Work.FTS.EllipticEst.AngSecond.IP F F := by
    rw [hfdef, IP_self_eq_HkSq]
    exact Real.sq_sqrt (HkSq_zero_nonneg α F)
  have hXeq : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 Ψ)
      (Work.Spaces.pthIter 2 Ψ)) = X := by
    rw [← hX2]; exact Real.sqrt_sq hX0
  have hbeq : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z * Work.Spaces.pz Ψ z θ)
      (fun z θ => z * Work.Spaces.pz Ψ z θ)) = b := by
    rw [← hb2]; exact Real.sqrt_sq hb0
  have hfeq : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP F F) = f := by
    rw [← hf2]; exact Real.sqrt_sq hf0
  have hmeq : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP Ψ Ψ) = m := by
    rw [IP_self_eq_HkSq, hmdef]
  have hΨbound : m ≤ C₁ * N := by
    rw [hmdef, hNdef, hfdef, hbdef]; exact hΨb
  have hPbbound : Pb ≤ C₁ * N := by
    rw [hPbdef, hNdef, hfdef, hbdef]; exact hPab
  -- ## the identity, the pieces, and Cauchy–Schwarz
  have hsol : Work.Elliptic.IsBslSol α F Ψ := ⟨hHon.eq, hHon.d0, hHon.dπ, hHon.dec⟩
  have hid := Work.FTS.EllipticEst.AngSecond.I_identity α F Ψ hsol hFB hQB hUB huB hΨB hBB
  have hI1 := I1 α F Ψ hHon hUmem
  have hI4 := hC₃ α F Ψ hHon hΨmem hPaMem
  have hcsU := Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hUmem) hBB hUB
  have hcsPsi := Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hΨmem) hBB hΨB
  have hcsF := Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hHon.memF) hBB hFB
  -- ## the bounds of the individual pieces, in the abbreviations
  have e1 : -α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Work.Spaces.pthIter 2 Ψ)
      ≤ C₂ * (α ^ 2 * b ^ 2) + C₂ * ((α ^ 2 * b) * X) := by
    rw [hbeq, hXeq] at hI1
    rw [hb2]
    have hring : C₂ * (α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => z * Work.Spaces.pz Ψ z θ) (fun z θ => z * Work.Spaces.pz Ψ z θ))
        + C₂ * ((α ^ 2 * b) * X)
        = -(-C₂ * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => z * Work.Spaces.pz Ψ z θ)
            (fun z θ => z * Work.Spaces.pz Ψ z θ) + b * X)) := by ring
    rw [hring]
    linarith [hI1]
  have e2 : -α * (5 + α) * Work.FTS.EllipticEst.AngSecond.IP
      (fun z θ => z * Work.Spaces.pz Ψ z θ) (Work.Spaces.pthIter 2 Ψ)
      ≤ (5 + α) * ((α * b) * X) := by
    have h := (abs_le.mp hcsU).1
    rw [hbeq, hXeq] at h
    nlinarith [h, hα, hb0, hX0]
  have e3 : Work.FTS.EllipticEst.AngSecond.IP
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ) (Work.Spaces.pthIter 2 Ψ)
      ≤ C₃ * (Pb ^ 2 + Pb * X + f ^ 2) := by
    rw [← hPbdef, ← hXdef, ← hfdef] at hI4
    exact hI4
  have e4 : -6 * Work.FTS.EllipticEst.AngSecond.IP Ψ (Work.Spaces.pthIter 2 Ψ) ≤ 6 * (m * X) := by
    have h := (abs_le.mp hcsPsi).1
    rw [hmeq, hXeq] at h
    linarith [h]
  have e5 : -Work.FTS.EllipticEst.AngSecond.IP F (Work.Spaces.pthIter 2 Ψ) ≤ f * X := by
    have h := (abs_le.mp hcsF).1
    rw [hfeq, hXeq] at h
    linarith [h]
  -- ## the identity, solved for the pairing of `∂_θθΨ` with itself
  have hid' : Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 Ψ)
      (Work.Spaces.pthIter 2 Ψ)
      = -α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Work.Spaces.pthIter 2 Ψ)
        - α * (5 + α) * Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => z * Work.Spaces.pz Ψ z θ) (Work.Spaces.pthIter 2 Ψ)
        + Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
          (Work.Spaces.pthIter 2 Ψ)
        - 6 * Work.FTS.EllipticEst.AngSecond.IP Ψ (Work.Spaces.pthIter 2 Ψ)
        - Work.FTS.EllipticEst.AngSecond.IP F (Work.Spaces.pthIter 2 Ψ) := by
    linarith [hid]
  -- ## the elementary consequences of the abbreviations
  have hNf : f ≤ N := by rw [hNdef]; nlinarith [hb0, hα.le]
  have hNb : α * b ≤ N := by rw [hNdef]; nlinarith [hf0]
  have hαb2 : α ^ 2 * b ^ 2 ≤ N ^ 2 := by nlinarith [hNb, hα, hb0, hN0]
  have hαbX : (α ^ 2 * b) * X ≤ N * X := by
    have h1 : α ^ 2 * b ≤ N := by
      have h2 : α ^ 2 * b = α * (α * b) := by ring
      rw [h2]
      calc α * (α * b) ≤ α * N := mul_le_mul_of_nonneg_left hNb hα.le
        _ ≤ 1 * N := by
            have h3 : α ≤ 1 := by linarith
            exact mul_le_mul_of_nonneg_right h3 hN0
        _ = N := by ring
    exact mul_le_mul_of_nonneg_right h1 hX0
  have h5bb : (5 + α) * ((α * b) * X) ≤ (21 / 4) * (N * X) := by
    have h1 : 5 + α ≤ 21 / 4 := by linarith
    have h2 : 0 ≤ (α * b) * X := by positivity
    have h3 : (α * b) * X ≤ N * X := mul_le_mul_of_nonneg_right hNb hX0
    calc (5 + α) * ((α * b) * X) ≤ (21 / 4) * ((α * b) * X) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ ≤ (21 / 4) * (N * X) := mul_le_mul_of_nonneg_left h3 (by norm_num)
  have hPb2 : Pb ^ 2 ≤ (C₁ * N) ^ 2 := by nlinarith [hPbbound, hPb0, hC₁, hN0]
  have hPbX : Pb * X ≤ (C₁ * N) * X := mul_le_mul_of_nonneg_right hPbbound hX0
  have hmX : m * X ≤ (C₁ * N) * X := mul_le_mul_of_nonneg_right hΨbound hX0
  have hfX : f * X ≤ N * X := mul_le_mul_of_nonneg_right hNf hX0
  -- ## the collection
  have hkey : X ^ 2 ≤ (C₂ + C₃ * C₁ ^ 2 + C₃) * N ^ 2
      + (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X) := by
    have hsum : X ^ 2 ≤ C₂ * (α ^ 2 * b ^ 2) + C₂ * ((α ^ 2 * b) * X)
        + (5 + α) * ((α * b) * X) + C₃ * (Pb ^ 2 + Pb * X + f ^ 2)
        + 6 * (m * X) + f * X := by
      rw [hX2, hid']
      linarith [e1, e2, e3, e4, e5]
    have t1 : C₂ * (α ^ 2 * b ^ 2) ≤ C₂ * N ^ 2 := mul_le_mul_of_nonneg_left hαb2 hC₂.le
    have t2 : C₂ * ((α ^ 2 * b) * X) ≤ C₂ * (N * X) := mul_le_mul_of_nonneg_left hαbX hC₂.le
    have t4 : C₃ * (Pb ^ 2 + Pb * X + f ^ 2) ≤ C₃ * ((C₁ * N) ^ 2 + (C₁ * N) * X + N ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ hC₃pos.le
      nlinarith [hPb2, hPbX, hfX, hNf, hN0, hf0]
    have t5 : 6 * (m * X) ≤ 6 * ((C₁ * N) * X) :=
      mul_le_mul_of_nonneg_left hmX (by norm_num)
    have hcollect : C₂ * (α ^ 2 * b ^ 2) + C₂ * ((α ^ 2 * b) * X)
        + (5 + α) * ((α * b) * X) + C₃ * (Pb ^ 2 + Pb * X + f ^ 2)
        + 6 * (m * X) + f * X
        ≤ C₂ * N ^ 2 + C₂ * (N * X) + (21 / 4) * (N * X)
          + C₃ * ((C₁ * N) ^ 2 + (C₁ * N) * X + N ^ 2) + 6 * ((C₁ * N) * X) + N * X := by
      exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add t1 t2) h5bb) t4) t5) hfX
    calc X ^ 2
        ≤ C₂ * N ^ 2 + C₂ * (N * X) + (21 / 4) * (N * X)
          + C₃ * ((C₁ * N) ^ 2 + (C₁ * N) * X + N ^ 2) + 6 * ((C₁ * N) * X) + N * X :=
          le_trans hsum hcollect
      _ = (C₂ + C₃ * C₁ ^ 2 + C₃) * N ^ 2
          + (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X) := by ring
  have hmain : X ^ 2 ≤ max (C₂ + C₃ * C₁ ^ 2 + C₃)
      (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X + N ^ 2) := by
    have h1 : (C₂ + C₃ * C₁ ^ 2 + C₃) * N ^ 2
        ≤ max (C₂ + C₃ * C₁ ^ 2 + C₃) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * N ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg N)
    have h2 : (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X)
        ≤ max (C₂ + C₃ * C₁ ^ 2 + C₃) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hN0 hX0)
    have h3 : max (C₂ + C₃ * C₁ ^ 2 + C₃) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X + N ^ 2)
        = max (C₂ + C₃ * C₁ ^ 2 + C₃) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X)
          + max (C₂ + C₃ * C₁ ^ 2 + C₃) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * N ^ 2 := by
      ring
    rw [h3]
    linarith [hkey, h1, h2]
  have hKmax : 0 ≤ max (C₂ + C₃ * C₁ ^ 2 + C₃) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) :=
    le_trans hK₁0 (le_max_left _ _)
  have hfinal := step3QuadSolve hKmax hN0 hmain
  calc Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)) = X := by rw [hXdef]
    _ ≤ (max (C₂ + C₃ * C₁ ^ 2 + C₃) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) + 1) * N := hfinal
    _ = (max (C₂ + C₃ * C₁ ^ 2 + C₃) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) + 1)
        * (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))) := by
      rw [hNdef, hfdef, hbdef]

end

end Work.FTS.EllipticEst.Honest
