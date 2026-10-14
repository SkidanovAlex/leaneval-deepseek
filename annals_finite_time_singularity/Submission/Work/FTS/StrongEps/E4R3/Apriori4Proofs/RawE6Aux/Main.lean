import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.Jeps_IP6_transfer_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Proofs/RawE6Aux/Main.lean` — the estimate of leaf L-A

`rawE6_pair_bound` is the whole *estimating* part of leaf L-A (`rawE6_ineq`): the ε-pricing of the
mollified slice's `ℋ⁷`-norm, the two multipliers `cW = L₁₂ (J_ε f) 0 / pzNorm`,
`cX = L₁₂ (J_ε X) 0 / pzNorm` of the projections, the transfer error of S1, and the assembly of
the pieces of

  `2 IP6(P₀ J_ε X, f) = 2 IP6(X, W) + 2 cW·IP6(X, bump) + 2 err − 2 cX·IP6(bump, f)`

into the level-six inequality of the ruling's §Verdict 4.  The consumer
(`rawE6_ineq_proof.lean`) supplies all structural and size inputs — the S1-transfer, the
semitame data (S2), the `H6Lin`/`H6Pair` rows, the conservation of the zero mode (leaf F6 in its
proved uniform-data form) and the definitions of `Λ`, `C₁`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.RawE6Aux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem rawE6_pair_bound
    {α ε Cs1 CL2 CLz CC Bb CJ Cg' Ct K7 CL CW A2 Λ C₁ e Ee Y cW cX err : ℝ}
    {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam} {f W X Jf JX D : Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hCs1 : 0 ≤ Cs1) (hCL2 : 0 ≤ CL2) (hCLz : 0 ≤ CLz) (hCC : 0 ≤ CC) (hBb : 0 ≤ Bb)
    (hCJ : 0 ≤ CJ) (hCg' : 0 ≤ Cg') (hCt : 0 ≤ Ct) (hK7 : 0 ≤ K7) (hCL : 0 ≤ CL) (hCW : 0 ≤ CW)
    (hA2 : 0 ≤ A2)
    (hK7eq : K7 = Real.sqrt 2 * (Cg' + (CL2 / Work.FTS.StrongEps.pzNorm) * Bb))
    (hΛ : Λ = 2 * CL * CW + 2 * (A2 * (1 + CW))
        + 2 * (((CL2 / Work.FTS.StrongEps.pzNorm) * CC * Bb + Cs1) * Ct * (1 + K7))
        + 2 * ((CLz / Work.FTS.StrongEps.pzNorm) * Real.exp (CJ / 2) * CC * Bb * Ct
            * (1 + Real.sqrt CW)))
    (hC₁ : C₁ = 2 * (((CL2 / Work.FTS.StrongEps.pzNorm) * CC * Bb + Cs1) * (2 * Ct * (1 + CW))))
    (heEe : Ee = 1 + e) (hY : Y = Real.sqrt Ee) (he0 : 0 ≤ e)
    (hJf : Jf = Work.FTS.StrongEps.Jeps ρ ε f) (hJX : JX = Work.FTS.StrongEps.Jeps ρ ε X)
    (hW : W = Work.FTS.StrongEps.Pz Jf)
    (hcW : cW = Work.Construction.L12 Jf 0 / Work.FTS.StrongEps.pzNorm)
    (hcX : cX = Work.Construction.L12 JX 0 / Work.FTS.StrongEps.pzNorm)
    (herr : err = IP6o α JX f - IP6o α X Jf)
    (hfsmo : Work.FTS.EllipticEst.SmoothOpen f) (hfmem6 : Work.Spaces.HkMem α 6 f)
    (hWQo : Work.FTS.VocabO.HQo α 6 W) (hW7mem : Work.Spaces.HkMem α 7 W)
    (hXQo : Work.FTS.VocabO.HQo α 6 X) (hXmem4 : Work.Spaces.HkMem α 4 X)
    (hJfmem7 : Work.Spaces.HkMem α 7 Jf)
    (hSqWe : Work.Spaces.HkSq α 6 W ≤ CW * e)
    (hlo : Work.Spaces.HkSq α 6 f ≤ e)
    (hX4 : Work.Spaces.HkNorm α 4 X ≤ Ct * (1 + Work.Spaces.HkNorm α 5 W))
    (hX6 : Work.Spaces.HkNorm α 6 X ≤ Ct * (1 + Work.Spaces.HkNorm α 7 W)
      + Ct * (1 + Work.Spaces.HkNorm α 6 W) ^ 2)
    (hJf7 : Work.Spaces.HkNorm α 7 Jf ≤ Cg' * ε⁻¹ * Y)
    (hbump6 : Work.Spaces.HkNorm α 6 Work.FTS.StrongEps.bump ≤ Bb)
    (hbump7 : Work.Spaces.HkNorm α 7 Work.FTS.StrongEps.bump ≤ Bb)
    (hJepsLe : Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.Jeps ρ ε X)
      ≤ Real.exp (CJ * ε) * Work.Spaces.HkSq α 4 X)
    (hErr : |err| ≤ Cs1 * ε * Work.Spaces.HkNorm α 6 X * Work.Spaces.HkNorm α 6 f)
    (hL12sub : |Work.Construction.L12 Jf 0 - Work.Construction.L12 f 0| ≤ CL2 * ε
      * Work.Spaces.HkNorm α 5 f)
    (h12z : |Work.Construction.L12 JX 0| ≤ CLz * Work.Spaces.HkNorm α 4 JX)
    (hL12z : Work.Construction.L12 f 0 = 0)
    (hcs : ∀ u v : Fn, Work.FTS.VocabO.HQo α 6 u → Work.FTS.VocabO.HQo α 6 v →
      |IP6o α u v| ≤ CC * Work.Spaces.HkNorm α 6 u * Work.Spaces.HkNorm α 6 v)
    (hlinB : IP6o α (Work.FTS.StrongPersist.linPart α W) W ≤ CL * Work.Spaces.HkSq α 6 W)
    (hsplitX : IP6o α X W = IP6o α (Work.FTS.StrongPersist.linPart α W) W + IP6o α D W)
    (hpairB : |IP6o α D W| ≤ A2 * (1 + Work.Spaces.HkSq α 6 W)) :
    2 * IP6o α (Work.FTS.StrongEps.Pz JX) f ≤ Λ * Ee + ε * C₁ * Ee ^ 2 := by
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  have hpznn : 0 ≤ Work.FTS.StrongEps.pzNorm := hpzpos.le
  have hα0 : 0 < α := hα.1
  have hεnn : 0 ≤ ε := hε.le
  -- ## the energy scale
  have hEnn : 0 ≤ Ee := by rw [heEe]; linarith
  have hE1 : 1 ≤ Ee := by rw [heEe]; linarith
  have hYnn : 0 ≤ Y := by rw [hY]; exact Real.sqrt_nonneg Ee
  have hY1 : 1 ≤ Y := by rw [hY]; exact Real.one_le_sqrt.mpr hE1
  have hYsq : Y ^ 2 = Ee := by rw [hY]; exact Real.sq_sqrt hEnn
  have hYleE : Y ≤ Ee := by nlinarith [hYsq, hY1, hYnn]
  have hf6 : Work.Spaces.HkNorm α 6 f ≤ Y := by
    calc Work.Spaces.HkNorm α 6 f = Real.sqrt (Work.Spaces.HkSq α 6 f) := rfl
      _ ≤ Real.sqrt e := Real.sqrt_le_sqrt hlo
      _ ≤ Real.sqrt Ee := Real.sqrt_le_sqrt (by rw [heEe]; linarith)
      _ = Y := by rw [hY]
  have hf5 : Work.Spaces.HkNorm α 5 f ≤ Y :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := 5) (by norm_num) hfmem6) hf6
  have hSqW6 : Work.Spaces.HkSq α 6 W ≤ CW * Ee := by
    have h1 : CW * e ≤ CW * Ee :=
      mul_le_mul_of_nonneg_left (by rw [heEe]; linarith) hCW
    linarith [hSqWe, h1]
  have hW6 : Work.Spaces.HkNorm α 6 W ≤ Real.sqrt CW * Y := by
    calc Work.Spaces.HkNorm α 6 W = Real.sqrt (Work.Spaces.HkSq α 6 W) := rfl
      _ ≤ Real.sqrt (CW * Ee) := Real.sqrt_le_sqrt hSqW6
      _ = Real.sqrt CW * Real.sqrt Ee := Real.sqrt_mul hCW Ee
      _ = Real.sqrt CW * Y := by rw [hY]
  have hW5 : Work.Spaces.HkNorm α 5 W ≤ Real.sqrt CW * Y := by
    have h1 : Work.Spaces.HkSq α 5 W ≤ Work.Spaces.HkSq α 6 W :=
      Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hWQo.2
    have h2 : Work.Spaces.HkNorm α 5 W ≤ Work.Spaces.HkNorm α 6 W := Real.sqrt_le_sqrt h1
    linarith [h2, hW6]
  have hW6sq : (Work.Spaces.HkNorm α 6 W) ^ 2 ≤ CW * Ee := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 W)]
    exact hSqW6
  have hX4Y : Work.Spaces.HkNorm α 4 X ≤ Ct * (1 + Real.sqrt CW * Y) := by
    have h1 : Ct * (1 + Work.Spaces.HkNorm α 5 W) ≤ Ct * (1 + Real.sqrt CW * Y) :=
      mul_le_mul_of_nonneg_left (by linarith [hW5]) hCt
    linarith [hX4, h1]
  -- ## smoothness and honesty of the mollified profiles
  have hfQuad : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad :=
    fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hfsmo n
  have hXQuad : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry X) Work.FTS.StrongEps.Quad :=
    fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall X).mp hXQo.1 n
  have hXloc : MeasureTheory.LocallyIntegrable (Work.FTS.StrongEps.logPull X)
      MeasureTheory.volume :=
    Work.FTS.StrongEps.locallyIntegrable_logPull_of_forall_contDiffOn hXQuad
  have hfloc : MeasureTheory.LocallyIntegrable (Work.FTS.StrongEps.logPull f)
      MeasureTheory.volume :=
    Work.FTS.StrongEps.locallyIntegrable_logPull_of_forall_contDiffOn hfQuad
  have hJfQuad : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Jf) Work.FTS.StrongEps.Quad := by
    rw [hJf]
    exact Work.FTS.StrongEps.Jeps_contDiffOn ρ hρ hε hfloc
  have hJXQuad : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry JX) Work.FTS.StrongEps.Quad := by
    rw [hJX]
    exact Work.FTS.StrongEps.Jeps_contDiffOn ρ hρ hε hXloc
  have hJXsmo : Work.FTS.EllipticEst.SmoothOpen JX :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hJXQuad
  have hJXmem4 : Work.Spaces.HkMem α 4 JX := by
    rw [hJX]
    exact Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε hXQuad hXmem4
  have hJXmem6 : Work.Spaces.HkMem α 6 JX := by
    rw [hJX]
    exact Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε hXQuad hXQo.2
  -- ## the two multipliers of the projection
  have hcWbd : |cW| ≤ (CL2 / Work.FTS.StrongEps.pzNorm) * ε * Y := by
    have h1 : |Work.Construction.L12 Jf 0| ≤ CL2 * ε * Work.Spaces.HkNorm α 5 f := by
      have h2 : |Work.Construction.L12 Jf 0 - Work.Construction.L12 f 0|
          ≤ CL2 * ε * Work.Spaces.HkNorm α 5 f := hL12sub
      rwa [hL12z, sub_zero] at h2
    calc |cW| = |Work.Construction.L12 Jf 0| / Work.FTS.StrongEps.pzNorm := by
          rw [hcW, abs_div, abs_of_pos hpzpos]
      _ ≤ (CL2 * ε * Work.Spaces.HkNorm α 5 f) / Work.FTS.StrongEps.pzNorm :=
          div_le_div_of_nonneg_right h1 hpznn
      _ = (CL2 / Work.FTS.StrongEps.pzNorm) * ε * Work.Spaces.HkNorm α 5 f := by ring
      _ ≤ (CL2 / Work.FTS.StrongEps.pzNorm) * ε * Y := by
          have hCL2p : 0 ≤ CL2 / Work.FTS.StrongEps.pzNorm := div_nonneg hCL2 hpznn
          have h1 : (CL2 / Work.FTS.StrongEps.pzNorm) * ε * Work.Spaces.HkNorm α 5 f
              ≤ (CL2 / Work.FTS.StrongEps.pzNorm) * ε * Y :=
            mul_le_mul_of_nonneg_left hf5 (by positivity)
          exact h1
  have hcXbd : |cX| ≤ (CLz / Work.FTS.StrongEps.pzNorm) * Real.exp (CJ / 2) * Ct
      * (1 + Real.sqrt CW * Y) := by
    have hJ4 : Work.Spaces.HkNorm α 4 JX ≤ Real.exp (CJ / 2) * Work.Spaces.HkNorm α 4 X := by
      have h := hJepsLe
      calc Work.Spaces.HkNorm α 4 JX
          ≤ Real.sqrt (Real.exp (CJ * ε) * Work.Spaces.HkSq α 4 X) := by
            rw [hJX]; exact Real.sqrt_le_sqrt h
        _ = Real.sqrt (Real.exp (CJ * ε)) * Real.sqrt (Work.Spaces.HkSq α 4 X) :=
            Real.sqrt_mul (Real.exp_pos _).le _
        _ = Real.exp (CJ * ε / 2) * Work.Spaces.HkNorm α 4 X := by
            rw [sqrt_exp_eq, Work.Spaces.HkNorm]
        _ ≤ Real.exp (CJ / 2) * Work.Spaces.HkNorm α 4 X := by
            refine mul_le_mul_of_nonneg_right ?_ (Work.Spaces.HkNorm_nonneg _ _ _)
            exact Real.exp_le_exp.mpr (by nlinarith [hCJ, hεnn, hε1])
    have h1 : |cX| ≤ (CLz / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 4 JX := by
      calc |cX| = |Work.Construction.L12 JX 0| / Work.FTS.StrongEps.pzNorm := by
            rw [hcX, abs_div, abs_of_pos hpzpos]
        _ ≤ (CLz * Work.Spaces.HkNorm α 4 JX) / Work.FTS.StrongEps.pzNorm :=
            div_le_div_of_nonneg_right h12z hpznn
        _ = (CLz / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 4 JX := by ring
    calc |cX| ≤ (CLz / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 4 JX := h1
      _ ≤ (CLz / Work.FTS.StrongEps.pzNorm) * (Real.exp (CJ / 2) * Work.Spaces.HkNorm α 4 X) :=
          mul_le_mul_of_nonneg_left hJ4 (by positivity)
      _ ≤ (CLz / Work.FTS.StrongEps.pzNorm) * (Real.exp (CJ / 2)
            * (Ct * (1 + Real.sqrt CW * Y))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX4Y (Real.exp_pos _).le)
            (by positivity)
      _ = (CLz / Work.FTS.StrongEps.pzNorm) * Real.exp (CJ / 2) * Ct
            * (1 + Real.sqrt CW * Y) := by ring
  -- ## the ε-pricing of the mollified slice
  have hW7 : Work.Spaces.HkNorm α 7 W
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 7 Jf + |cW| * Bb) := by
    have hfun : Work.FTS.StrongEps.Pz Jf
        = fun z θ => Jf z θ + (-cW) * Work.FTS.StrongEps.bump z θ := by
      funext z θ
      rw [Work.FTS.StrongEps.Pz_apply, hcW]
      ring
    rw [hW, hfun]
    have hbq : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Work.FTS.StrongEps.bump)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall Work.FTS.StrongEps.bump).mp
        Work.FTS.StrongEps.smoothOpen_bump n
    have hbq' : ∀ n : ℕ, ContDiffOn ℝ n
        (Function.uncurry (fun z θ => (-cW) * Work.FTS.StrongEps.bump z θ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall
        (fun z θ => (-cW) * Work.FTS.StrongEps.bump z θ)).mp
        (Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen (-cW)
          Work.FTS.StrongEps.smoothOpen_bump) n
    have hbm : Work.Spaces.HkMem α 7 (fun z θ => (-cW) * Work.FTS.StrongEps.bump z θ) :=
      Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-cW)
        (Work.FTS.StrongEps.PZeroAux.HkMem_bump α 7)
    have h1 := Work.FTS.EllipticEst.HkNorm_add_fts α 7 (f := Jf)
      (g := fun z θ => (-cW) * Work.FTS.StrongEps.bump z θ) hJfQuad hbq' hJfmem7 hbm
    have h2 := Work.FTS.EllipticEst.HkNorm_const_mul α 7 (-cW)
      (f := Work.FTS.StrongEps.bump) hbq
    calc Work.Spaces.HkNorm α 7 (fun z θ => Jf z θ + (-cW) * Work.FTS.StrongEps.bump z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 7 Jf
            + Work.Spaces.HkNorm α 7 (fun z θ => (-cW) * Work.FTS.StrongEps.bump z θ)) := h1
      _ = Real.sqrt 2 * (Work.Spaces.HkNorm α 7 Jf
            + |cW| * Work.Spaces.HkNorm α 7 Work.FTS.StrongEps.bump) := by
          rw [h2, abs_neg]
      _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 7 Jf + |cW| * Bb) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
          have hb : |cW| * Work.Spaces.HkNorm α 7 Work.FTS.StrongEps.bump ≤ |cW| * Bb :=
            mul_le_mul_of_nonneg_left hbump7 (abs_nonneg _)
          linarith [hb]
  have hI7 : ε * Work.Spaces.HkNorm α 7 W ≤ K7 * Y := by
    have h1 : ε * Work.Spaces.HkNorm α 7 W
        ≤ ε * (Real.sqrt 2 * (Work.Spaces.HkNorm α 7 Jf + |cW| * Bb)) :=
      mul_le_mul_of_nonneg_left hW7 hεnn
    have h2 : ε * Work.Spaces.HkNorm α 7 Jf ≤ Cg' * Y := by
      have h3 : ε * (Cg' * ε⁻¹ * Y) = Cg' * Y := by field_simp
      calc ε * Work.Spaces.HkNorm α 7 Jf ≤ ε * (Cg' * ε⁻¹ * Y) :=
            mul_le_mul_of_nonneg_left hJf7 hεnn
        _ = Cg' * Y := h3
    have h4 : ε * (|cW| * Bb) ≤ (CL2 / Work.FTS.StrongEps.pzNorm) * Bb * Y := by
      have h5 : ε * (|cW| * Bb) = (ε * |cW|) * Bb := by ring
      have h6 : ε * |cW| ≤ (CL2 / Work.FTS.StrongEps.pzNorm) * ε * Y * ε := by
        calc ε * |cW| ≤ ε * ((CL2 / Work.FTS.StrongEps.pzNorm) * ε * Y) :=
              mul_le_mul_of_nonneg_left hcWbd hεnn
          _ = (CL2 / Work.FTS.StrongEps.pzNorm) * ε * Y * ε := by ring
      have h7 : ε * ε ≤ 1 := by nlinarith [hεnn, hε1]
      calc ε * (|cW| * Bb) = (ε * |cW|) * Bb := h5
        _ ≤ ((CL2 / Work.FTS.StrongEps.pzNorm) * ε * Y * ε) * Bb :=
            mul_le_mul_of_nonneg_right h6 hBb
        _ ≤ ((CL2 / Work.FTS.StrongEps.pzNorm) * Y) * Bb := by
            refine mul_le_mul_of_nonneg_right ?_ hBb
            have hA : 0 ≤ (CL2 / Work.FTS.StrongEps.pzNorm) * Y :=
              mul_nonneg (div_nonneg hCL2 hpznn) hYnn
            calc (CL2 / Work.FTS.StrongEps.pzNorm) * ε * Y * ε
                = ((CL2 / Work.FTS.StrongEps.pzNorm) * Y) * (ε * ε) := by ring
              _ ≤ ((CL2 / Work.FTS.StrongEps.pzNorm) * Y) * 1 :=
                  mul_le_mul_of_nonneg_left h7 hA
              _ = (CL2 / Work.FTS.StrongEps.pzNorm) * Y := by ring
        _ = (CL2 / Work.FTS.StrongEps.pzNorm) * Bb * Y := by ring
    have h9 : ε * (Real.sqrt 2 * (Work.Spaces.HkNorm α 7 Jf + |cW| * Bb))
        = Real.sqrt 2 * (ε * Work.Spaces.HkNorm α 7 Jf + ε * (|cW| * Bb)) := by ring
    have h10 : Real.sqrt 2 * (ε * Work.Spaces.HkNorm α 7 Jf + ε * (|cW| * Bb))
        ≤ K7 * Y := by
      have h11 : Real.sqrt 2 * (ε * Work.Spaces.HkNorm α 7 Jf + ε * (|cW| * Bb))
          ≤ Real.sqrt 2 * (Cg' * Y + (CL2 / Work.FTS.StrongEps.pzNorm) * Bb * Y) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
        linarith [h2, h4]
      have h12 : Real.sqrt 2 * (Cg' * Y + (CL2 / Work.FTS.StrongEps.pzNorm) * Bb * Y)
          = K7 * Y := by rw [hK7eq]; ring
      linarith [h11, h12.le]
    linarith [h1, h9.le, h9.ge, h10]
  have hI6 : ε * (1 + Work.Spaces.HkNorm α 6 W) ^ 2 ≤ 2 * (1 + CW) * ε * Ee := by
    have h3 : (1 + Work.Spaces.HkNorm α 6 W) ^ 2
        ≤ 2 * (1 + (Work.Spaces.HkNorm α 6 W) ^ 2) := by
      nlinarith [sq_nonneg (Work.Spaces.HkNorm α 6 W - 1)]
    have h4 : 1 + (Work.Spaces.HkNorm α 6 W) ^ 2 ≤ (1 + CW) * Ee := by
      nlinarith [hW6sq, hE1, hEnn, hCW]
    have h5 : (1 + Work.Spaces.HkNorm α 6 W) ^ 2 ≤ 2 * (1 + CW) * Ee := by linarith
    have h6 : ε * (1 + Work.Spaces.HkNorm α 6 W) ^ 2 ≤ ε * (2 * (1 + CW) * Ee) :=
      mul_le_mul_of_nonneg_left h5 hεnn
    calc ε * (1 + Work.Spaces.HkNorm α 6 W) ^ 2 ≤ ε * (2 * (1 + CW) * Ee) := h6
      _ = 2 * (1 + CW) * ε * Ee := by ring
  have hXeps : ε * Work.Spaces.HkNorm α 6 X
      ≤ Ct * (1 + K7) * Y + 2 * Ct * (1 + CW) * ε * Ee := by
    have h1 : ε * Work.Spaces.HkNorm α 6 X
        ≤ ε * (Ct * (1 + Work.Spaces.HkNorm α 7 W)
            + Ct * (1 + Work.Spaces.HkNorm α 6 W) ^ 2) := mul_le_mul_of_nonneg_left hX6 hεnn
    have h4 : Ct * (ε * (1 + Work.Spaces.HkNorm α 7 W)) ≤ Ct * (1 + K7) * Y := by
      have h5 : ε * (1 + Work.Spaces.HkNorm α 7 W) ≤ (1 + K7) * Y := by
        have h6 : ε ≤ Y := le_trans hε1 hY1
        nlinarith [hI7, h6, hK7]
      calc Ct * (ε * (1 + Work.Spaces.HkNorm α 7 W)) ≤ Ct * ((1 + K7) * Y) :=
            mul_le_mul_of_nonneg_left h5 hCt
        _ = Ct * (1 + K7) * Y := by ring
    have h7 : Ct * (ε * (1 + Work.Spaces.HkNorm α 6 W) ^ 2)
        ≤ 2 * Ct * (1 + CW) * ε * Ee := by
      calc Ct * (ε * (1 + Work.Spaces.HkNorm α 6 W) ^ 2) ≤ Ct * (2 * (1 + CW) * ε * Ee) :=
            mul_le_mul_of_nonneg_left hI6 hCt
        _ = 2 * Ct * (1 + CW) * ε * Ee := by ring
    calc ε * Work.Spaces.HkNorm α 6 X
        ≤ ε * (Ct * (1 + Work.Spaces.HkNorm α 7 W)
            + Ct * (1 + Work.Spaces.HkNorm α 6 W) ^ 2) := h1
      _ = Ct * (ε * (1 + Work.Spaces.HkNorm α 7 W))
          + Ct * (ε * (1 + Work.Spaces.HkNorm α 6 W) ^ 2) := by ring
      _ ≤ Ct * (1 + K7) * Y + 2 * Ct * (1 + CW) * ε * Ee := by linarith [h4, h7]
  -- ## the two pairings against `bump`
  have hbumpQo : Work.FTS.VocabO.HQo α 6 Work.FTS.StrongEps.bump :=
    ⟨Work.FTS.StrongEps.smoothOpen_bump, Work.FTS.StrongEps.PZeroAux.HkMem_bump α 6⟩
  have hXbump : |IP6o α X Work.FTS.StrongEps.bump| ≤ CC * Bb * Work.Spaces.HkNorm α 6 X := by
    have h := hcs X Work.FTS.StrongEps.bump hXQo hbumpQo
    calc |IP6o α X Work.FTS.StrongEps.bump|
        ≤ CC * Work.Spaces.HkNorm α 6 X * Work.Spaces.HkNorm α 6 Work.FTS.StrongEps.bump := h
      _ ≤ CC * Work.Spaces.HkNorm α 6 X * Bb :=
          mul_le_mul_of_nonneg_left hbump6 (mul_nonneg hCC (Work.Spaces.HkNorm_nonneg _ _ _))
      _ = CC * Bb * Work.Spaces.HkNorm α 6 X := by ring
  have hbumpf : |IP6o α Work.FTS.StrongEps.bump f| ≤ CC * Bb * Y := by
    have h := hcs Work.FTS.StrongEps.bump f hbumpQo ⟨hfsmo, hfmem6⟩
    calc |IP6o α Work.FTS.StrongEps.bump f|
        ≤ CC * Work.Spaces.HkNorm α 6 Work.FTS.StrongEps.bump
            * Work.Spaces.HkNorm α 6 f := h
      _ ≤ CC * Bb * Work.Spaces.HkNorm α 6 f := by
          have h1 : CC * Work.Spaces.HkNorm α 6 Work.FTS.StrongEps.bump ≤ CC * Bb :=
            mul_le_mul_of_nonneg_left hbump6 hCC
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_right h1 (Work.Spaces.HkNorm_nonneg α 6 f)
      _ ≤ CC * Bb * Y := mul_le_mul_of_nonneg_left hf6 (mul_nonneg hCC hBb)
  -- ## the correction of the pairing, in one block
  have hcorr : |cW| * |IP6o α X Work.FTS.StrongEps.bump| + |err|
        + |cX| * |IP6o α Work.FTS.StrongEps.bump f|
      ≤ ((CL2 / Work.FTS.StrongEps.pzNorm) * CC * Bb + Cs1)
            * (Ct * (1 + K7) * Ee + 2 * Ct * (1 + CW) * ε * Ee ^ 2)
        + (CLz / Work.FTS.StrongEps.pzNorm) * Real.exp (CJ / 2) * CC * Bb * Ct
            * (1 + Real.sqrt CW) * Ee := by
    have h1 : |cW| * |IP6o α X Work.FTS.StrongEps.bump|
        ≤ ((CL2 / Work.FTS.StrongEps.pzNorm) * CC * Bb) * (Y * (ε * Work.Spaces.HkNorm α 6 X)) := by
      calc |cW| * |IP6o α X Work.FTS.StrongEps.bump|
          ≤ ((CL2 / Work.FTS.StrongEps.pzNorm) * ε * Y)
              * (CC * Bb * Work.Spaces.HkNorm α 6 X) :=
            mul_le_mul hcWbd hXbump (abs_nonneg _) (by positivity)
        _ = ((CL2 / Work.FTS.StrongEps.pzNorm) * CC * Bb)
              * (Y * (ε * Work.Spaces.HkNorm α 6 X)) := by ring
    have h2 : |err| ≤ Cs1 * Y * (ε * Work.Spaces.HkNorm α 6 X) := by
      have h3 : Cs1 * ε * Work.Spaces.HkNorm α 6 X * Work.Spaces.HkNorm α 6 f
          ≤ Cs1 * Y * (ε * Work.Spaces.HkNorm α 6 X) := by
        calc Cs1 * ε * Work.Spaces.HkNorm α 6 X * Work.Spaces.HkNorm α 6 f
            = Cs1 * (ε * Work.Spaces.HkNorm α 6 X) * Work.Spaces.HkNorm α 6 f := by ring
          _ ≤ Cs1 * (ε * Work.Spaces.HkNorm α 6 X) * Y := by
              refine mul_le_mul_of_nonneg_left hf6 ?_
              exact mul_nonneg hCs1 (mul_nonneg hεnn (Work.Spaces.HkNorm_nonneg _ _ _))
          _ = Cs1 * Y * (ε * Work.Spaces.HkNorm α 6 X) := by ring
      exact le_trans hErr h3
    have h4 : Y * (ε * Work.Spaces.HkNorm α 6 X)
        ≤ Y * (Ct * (1 + K7) * Y + 2 * Ct * (1 + CW) * ε * Ee) :=
      mul_le_mul_of_nonneg_left hXeps hYnn
    have h5 : Y * (Ct * (1 + K7) * Y + 2 * Ct * (1 + CW) * ε * Ee)
        ≤ (Ct * (1 + K7)) * Ee + (2 * Ct * (1 + CW)) * (ε * Ee ^ 2) := by
      have h6 : (Ct * (1 + K7)) * (Y * Y) ≤ (Ct * (1 + K7)) * Ee := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCt (by linarith))
        rw [← sq, hYsq]
      have h7 : (2 * Ct * (1 + CW)) * (ε * (Y * Ee)) ≤ (2 * Ct * (1 + CW)) * (ε * Ee ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg (by norm_num) hCt) (by linarith))
        refine mul_le_mul_of_nonneg_left ?_ hεnn
        calc Y * Ee ≤ Ee * Ee := mul_le_mul_of_nonneg_right hYleE hEnn
          _ = Ee ^ 2 := by ring
      have h8 : Y * (Ct * (1 + K7) * Y + 2 * Ct * (1 + CW) * ε * Ee)
          = (Ct * (1 + K7)) * (Y * Y) + (2 * Ct * (1 + CW)) * (ε * (Y * Ee)) := by ring
      rw [h8]
      linarith [h6, h7]
    have h9 : ((CL2 / Work.FTS.StrongEps.pzNorm) * CC * Bb)
          * (Y * (ε * Work.Spaces.HkNorm α 6 X)) + Cs1 * Y * (ε * Work.Spaces.HkNorm α 6 X)
        ≤ ((CL2 / Work.FTS.StrongEps.pzNorm) * CC * Bb + Cs1)
            * ((Ct * (1 + K7)) * Ee + (2 * Ct * (1 + CW)) * (ε * Ee ^ 2)) := by
      have h10 := mul_le_mul_of_nonneg_left (le_trans h4 h5)
        (add_nonneg (mul_nonneg (mul_nonneg (div_nonneg hCL2 hpznn) hCC) hBb) hCs1)
      linarith [h10]
    have h11 : |cX| * |IP6o α Work.FTS.StrongEps.bump f|
        ≤ (CLz / Work.FTS.StrongEps.pzNorm) * Real.exp (CJ / 2) * CC * Bb * Ct
            * (1 + Real.sqrt CW) * Ee := by
      have h12 : |cX| * |IP6o α Work.FTS.StrongEps.bump f|
          ≤ ((CLz / Work.FTS.StrongEps.pzNorm) * Real.exp (CJ / 2) * Ct
              * (1 + Real.sqrt CW * Y)) * (CC * Bb * Y) :=
        mul_le_mul hcXbd hbumpf (abs_nonneg _) (by positivity)
      -- (the `positivity` above only sees products of the named nonnegatives)
      have h13 : (1 + Real.sqrt CW * Y) * Y ≤ (1 + Real.sqrt CW) * Ee := by
        have h14 : (1 + Real.sqrt CW * Y) * Y = Y + Real.sqrt CW * (Y * Y) := by ring
        have h15 : Y + Real.sqrt CW * (Y * Y) ≤ Ee + Real.sqrt CW * Ee := by
          have h16 : Y * Y ≤ Ee := by rw [← sq]; exact le_of_eq hYsq
          nlinarith [hYleE, h16, Real.sqrt_nonneg CW]
        have h17 : Ee + Real.sqrt CW * Ee = (1 + Real.sqrt CW) * Ee := by ring
        linarith [h14, h15, h17]
      calc |cX| * |IP6o α Work.FTS.StrongEps.bump f|
          ≤ ((CLz / Work.FTS.StrongEps.pzNorm) * Real.exp (CJ / 2) * Ct
              * (1 + Real.sqrt CW * Y)) * (CC * Bb * Y) := h12
        _ = ((CLz / Work.FTS.StrongEps.pzNorm) * Real.exp (CJ / 2) * Ct * CC * Bb)
              * ((1 + Real.sqrt CW * Y) * Y) := by ring
        _ ≤ ((CLz / Work.FTS.StrongEps.pzNorm) * Real.exp (CJ / 2) * Ct * CC * Bb)
              * ((1 + Real.sqrt CW) * Ee) :=
            mul_le_mul_of_nonneg_left h13 (by positivity)
        _ = (CLz / Work.FTS.StrongEps.pzNorm) * Real.exp (CJ / 2) * CC * Bb * Ct
              * (1 + Real.sqrt CW) * Ee := by ring
    linarith [h1, h2, h9, h11]
  -- ## the identity of the pairing
  have hid : 2 * IP6o α (Work.FTS.StrongEps.Pz JX) f
      = 2 * ((IP6o α X W + cW * IP6o α X Work.FTS.StrongEps.bump) + err
          - cX * IP6o α Work.FTS.StrongEps.bump f) := by
    have h1 : IP6o α (Work.FTS.StrongEps.Pz JX) f
        = IP6o α JX f - cX * IP6o α Work.FTS.StrongEps.bump f := by
      have hfun : Work.FTS.StrongEps.Pz JX
          = fun z θ => JX z θ - cX * Work.FTS.StrongEps.bump z θ := by
        funext z θ
        rw [Work.FTS.StrongEps.Pz_apply, hcX]
      rw [hfun]
      exact IP6o_sub_smul_bump_left α hα0 (v := JX) (u := f) (c := cX) hJXsmo hfsmo hJXmem6
        hfmem6
    have h2 : IP6o α JX f = IP6o α X Jf + err := by rw [herr]; ring
    have h3 : IP6o α X Jf = IP6o α X W + cW * IP6o α X Work.FTS.StrongEps.bump := by
      have hfun : Jf = fun z θ => W z θ + cW * Work.FTS.StrongEps.bump z θ := by
        funext z θ
        rw [hW, Work.FTS.StrongEps.Pz_apply, hcW]
        ring
      have hsm : Work.FTS.EllipticEst.SmoothOpen
          (fun z θ => cW * Work.FTS.StrongEps.bump z θ) :=
        Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen cW
          Work.FTS.StrongEps.smoothOpen_bump
      have hme : Work.Spaces.HkMem α 6 (fun z θ => cW * Work.FTS.StrongEps.bump z θ) :=
        Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen cW
          (Work.FTS.StrongEps.PZeroAux.HkMem_bump α 6)
      rw [hfun]
      rw [IP6o_add_right α hα0 (u := X) (u₁ := W)
        (u₂ := fun z θ => cW * Work.FTS.StrongEps.bump z θ) hXQo.1 hWQo.1 hsm hXQo.2 hWQo.2 hme]
      rw [IP6o_const_mul_right α cW X Work.FTS.StrongEps.bump]
    calc 2 * IP6o α (Work.FTS.StrongEps.Pz JX) f
        = 2 * (IP6o α JX f - cX * IP6o α Work.FTS.StrongEps.bump f) := by rw [h1]
      _ = 2 * (IP6o α X Jf + err - cX * IP6o α Work.FTS.StrongEps.bump f) := by rw [h2]
      _ = 2 * ((IP6o α X W + cW * IP6o α X Work.FTS.StrongEps.bump) + err
            - cX * IP6o α Work.FTS.StrongEps.bump f) := by rw [h3]
  -- ## the assembly
  set S : ℝ := ((CL2 / Work.FTS.StrongEps.pzNorm) * CC * Bb + Cs1)
        * (Ct * (1 + K7) * Ee + 2 * Ct * (1 + CW) * ε * Ee ^ 2)
      + (CLz / Work.FTS.StrongEps.pzNorm) * Real.exp (CJ / 2) * CC * Bb * Ct
        * (1 + Real.sqrt CW) * Ee with hS
  have hcorrS : |cW| * |IP6o α X Work.FTS.StrongEps.bump| + |err|
      + |cX| * |IP6o α Work.FTS.StrongEps.bump f| ≤ S := by
    rw [hS]; exact hcorr
  have hB1 : cW * IP6o α X Work.FTS.StrongEps.bump
      ≤ |cW| * |IP6o α X Work.FTS.StrongEps.bump| := by
    have h : cW * IP6o α X Work.FTS.StrongEps.bump
        ≤ |cW * IP6o α X Work.FTS.StrongEps.bump| := le_abs_self _
    rwa [abs_mul] at h
  have hB2 : err ≤ |err| := le_abs_self _
  have hB3 : -(cX * IP6o α Work.FTS.StrongEps.bump f)
      ≤ |cX| * |IP6o α Work.FTS.StrongEps.bump f| := by
    have h : -(cX * IP6o α Work.FTS.StrongEps.bump f)
        ≤ |-(cX * IP6o α Work.FTS.StrongEps.bump f)| := le_abs_self _
    rwa [abs_neg, abs_mul] at h
  have hB4 : IP6o α D W ≤ A2 * (1 + Work.Spaces.HkSq α 6 W) := le_trans (le_abs_self _) hpairB
  have hA : IP6o α (Work.FTS.StrongPersist.linPart α W) W + IP6o α D W
      ≤ (CL * CW + A2 * (1 + CW)) * Ee := by
    have h3 : 1 + Work.Spaces.HkSq α 6 W ≤ (1 + CW) * Ee :=
      calc 1 + Work.Spaces.HkSq α 6 W ≤ Ee + CW * Ee := add_le_add hE1 hSqW6
        _ = (1 + CW) * Ee := by ring
    have h4 : IP6o α D W ≤ A2 * ((1 + CW) * Ee) :=
      le_trans hB4 (mul_le_mul_of_nonneg_left h3 hA2)
    have h5 : CL * Work.Spaces.HkSq α 6 W ≤ CL * CW * Ee := by
      calc CL * Work.Spaces.HkSq α 6 W ≤ CL * (CW * Ee) := mul_le_mul_of_nonneg_left hSqW6 hCL
        _ = CL * CW * Ee := by ring
    calc IP6o α (Work.FTS.StrongPersist.linPart α W) W + IP6o α D W
        ≤ CL * Work.Spaces.HkSq α 6 W + A2 * ((1 + CW) * Ee) := add_le_add hlinB h4
      _ ≤ CL * CW * Ee + A2 * ((1 + CW) * Ee) := add_le_add h5 le_rfl
      _ = CL * CW * Ee + A2 * (1 + CW) * Ee := by ring
      _ = (CL * CW + A2 * (1 + CW)) * Ee := by ring
  have hA' : IP6o α X W ≤ (CL * CW + A2 * (1 + CW)) * Ee := by
    rw [hsplitX]; exact hA
  have hSq : cW * IP6o α X Work.FTS.StrongEps.bump + err
      - cX * IP6o α Work.FTS.StrongEps.bump f ≤ S := by
    have h2 : (cW * IP6o α X Work.FTS.StrongEps.bump + err)
          + -(cX * IP6o α Work.FTS.StrongEps.bump f)
        ≤ (|cW| * |IP6o α X Work.FTS.StrongEps.bump| + |err|)
          + |cX| * |IP6o α Work.FTS.StrongEps.bump f| :=
      add_le_add (add_le_add hB1 hB2) hB3
    exact le_trans h2 hcorrS
  have hstep : 2 * ((IP6o α X W + cW * IP6o α X Work.FTS.StrongEps.bump) + err
        - cX * IP6o α Work.FTS.StrongEps.bump f)
      ≤ 2 * ((CL * CW + A2 * (1 + CW)) * Ee) + 2 * S := by
    have h := add_le_add (mul_le_mul_of_nonneg_left hA' (by norm_num : (0:ℝ) ≤ 2))
      (mul_le_mul_of_nonneg_left hSq (by norm_num : (0:ℝ) ≤ 2))
    have hgoal : 2 * ((IP6o α X W + cW * IP6o α X Work.FTS.StrongEps.bump) + err
        - cX * IP6o α Work.FTS.StrongEps.bump f)
        = 2 * (IP6o α X W) + 2 * (cW * IP6o α X Work.FTS.StrongEps.bump + err
            - cX * IP6o α Work.FTS.StrongEps.bump f) := by ring
    rw [hgoal]
    exact h
  calc 2 * IP6o α (Work.FTS.StrongEps.Pz JX) f
      = 2 * ((IP6o α X W + cW * IP6o α X Work.FTS.StrongEps.bump) + err
          - cX * IP6o α Work.FTS.StrongEps.bump f) := hid
    _ ≤ 2 * ((CL * CW + A2 * (1 + CW)) * Ee) + 2 * S := hstep
    _ = Λ * Ee + ε * C₁ * Ee ^ 2 := by rw [hΛ, hC₁, hS]; ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.RawE6Aux
