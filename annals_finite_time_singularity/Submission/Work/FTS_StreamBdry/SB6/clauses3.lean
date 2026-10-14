import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeFacts
import Submission.Work.FTS_StreamBdry.SBpsiP.SelfUprime
import Submission.Work.FTS_StreamBdry.sb5_barrier_proved
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25Aux3.PsiPC3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25Aux3.psiP_c3`

The `U`-slot part `P := psiP αG Ψ` of a `C³` stream function is itself `C³` on the open quadrant.

This is `SB3.psiP_c2` with `2` replaced by `3`: SB1′ writes `Ψ = P + κ · gaugeMode` on `Qd`
(`SB1.sb1_gauge_of_parts`), the gauge mode is analytic (`SB25.contDiffOn_uncurry_gaugeMode`), and
`h3` is exactly the `C³` hypothesis on `Ψ`, so the difference `Ψ - κ·gaugeMode` (which agrees with
`P`) is `C³` on `Qd`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25Aux3

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP)

set_option autoImplicit false

/-- `psiP αG Ψ` is `C³` on the open quadrant whenever `Ψ` is. -/
theorem psiP_c3 {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    ContDiffOn ℝ 3 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd := by
  obtain ⟨κ, hκ⟩ := Work.FTS_StreamBdry.SB1.sb1_gauge_of_parts (αG := αG) (M := M)
    hαG h3 hslot
    (Work.FTS_StreamBdry.SB1.psiP_ode hαG h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_diff hαG h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_Vop_bnd hαG h3 hslot)
  have hg : ContDiffOn ℝ 3 (Function.uncurry (gaugeMode αG)) Work.Construction.Qd :=
    (Work.FTS_StreamBdry.SB25.contDiffOn_uncurry_gaugeMode αG).of_le le_top
  have hsub : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ =>
        Function.uncurry Ψ p - κ * Function.uncurry (gaugeMode αG) p)
      Work.Construction.Qd :=
    h3.sub (contDiffOn_const.mul hg)
  refine hsub.congr (fun p hp => ?_)
  obtain ⟨z, θ⟩ := p
  have h := hκ z θ hp
  simp only [Function.uncurry]
  linarith

end Work.FTS_StreamBdry.SB25Aux3
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB3.P2Aux.bslOp_div_s2_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB3.P2Aux

/-- The level-0 ODE for `u := Q/s2` (the `Lgs` identity of `bslOp`, rearranged).

`Lgs` (`Submission/Work/FTS_StreamBdry/SB25/Defs.lean`) satisfies
`bslOp α Q = s2 θ * Lgs α (fun z θ => Q z θ / s2 θ)` with
`Lgs α u = -α^2 * DzIter 2 u - 5*α * Dz u - pthIter 2 u - (4 cos 2θ/sin 2θ - tan θ) * pth u`.
Hence, from `bslOp α Q = F`,
`(Q/s2)'' + c * (Q/s2)' = -F/s2 - (α^2 * DzIter 2 (Q/s2) + 5 * α * Dz (Q/s2))`,
`c = 4 cos 2θ/sin 2θ - tan θ`; this is the statement (in `HasDerivAt` form).
`ContDiffAt ℝ 2 (uncurry Q)` supplies the second-order differentiability of the `θ`-slice. -/
theorem bslOp_div_s2_hasDerivAt {α : ℝ} {Q F : ℝ → ℝ → ℝ}
    (hCt : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 2 (Function.uncurry Q) (z, θ))
    (hlaw : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Elliptic.bslOp α Q z θ = F z θ) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (deriv (fun θ' => Q z θ' / Work.Construction.s2 θ'))
        (-(F z θ) / Work.Construction.s2 θ
          - (4 * Real.cos (2 * θ) / Work.Construction.s2 θ - Real.tan θ)
              * deriv (fun θ' => Q z θ' / Work.Construction.s2 θ') θ
          - (α ^ 2 * Work.Spaces.DzIter 2 (fun z θ => Q z θ / Work.Construction.s2 θ) z θ
              + 5 * α * Work.Spaces.Dz (fun z θ => Q z θ / Work.Construction.s2 θ) z θ)) θ := by
  intro z θ hQd
  -- the standing hypotheses at the point `(z, θ)`
  have hQ : ContDiffAt ℝ 2 (Function.uncurry Q) (z, θ) := hCt z θ hQd
  have hlaw' : Work.Elliptic.bslOp α Q z θ = F z θ := hlaw z θ hQd
  -- unpack `(z, θ) ∈ Qd = (0,∞) × (0,π/2)`
  have hQd' : (z, θ) ∈ Work.Construction.Qd := hQd
  simp only [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hQd'
  obtain ⟨hz, hθ0, hθ1⟩ := hQd'
  have hsin : Work.Construction.s2 θ ≠ 0 := by
    rw [Work.Construction.s2_eq]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  -- the ground-state identity `bslOp α Q = s2 · Lgs α (Q/s2)` (leaf E3)
  have hsplit := Work.FTS_StreamBdry.SB25.bslOp_split α Q hQd hQ
  have hLgs : Work.FTS_StreamBdry.SB25.Lgs α
      (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ
      = F z θ / Work.Construction.s2 θ := by
    rw [eq_div_iff hsin, mul_comm, ← hsplit, hlaw']
  -- unfold `Lgs` and rearrange for `pthIter 2 (Q/s2)`
  have hLgs_exp :
      -(α ^ 2) * Work.Spaces.DzIter 2 (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ
        - 5 * α * Work.Spaces.Dz (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ
        - Work.Spaces.pthIter 2 (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ
        - (4 * Real.cos (2 * θ) / Work.Construction.s2 θ - Real.tan θ)
            * Work.Spaces.pth (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ
        = F z θ / Work.Construction.s2 θ := by
    rw [← hLgs]
    rfl
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
    at hLgs_exp
  have hval : Work.Spaces.pthIter 2 (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ
      = -(F z θ) / Work.Construction.s2 θ
        - (4 * Real.cos (2 * θ) / Work.Construction.s2 θ - Real.tan θ)
            * deriv (fun θ' => Q z θ' / Work.Construction.s2 θ') θ
        - (α ^ 2 * Work.Spaces.DzIter 2 (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ
            + 5 * α * Work.Spaces.Dz (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ) := by
    simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
    rw [neg_div]
    linarith [hLgs_exp]
  -- second-order differentiability of the `θ`-slice of `Q / s2`
  have hslice : ContDiffAt ℝ 2 (fun θ' => Q z θ') θ := by
    have h2 := hQ.comp θ (ContDiffAt.prodMk contDiffAt_const contDiffAt_id)
    convert h2 using 1
    funext x; rfl
  have hs2slice : ContDiffAt ℝ 2 (fun θ' : ℝ => Work.Construction.s2 θ') θ := by
    have h : ContDiffAt ℝ 2 (fun θ' : ℝ => Real.sin (2 * θ')) θ := by fun_prop
    simpa only [Work.Construction.s2_eq] using h
  have hw : ContDiffAt ℝ 2 (fun θ' => Q z θ' / Work.Construction.s2 θ') θ :=
    hslice.div hs2slice hsin
  have hderiv : ContDiffAt ℝ 1 (deriv (fun θ' => Q z θ' / Work.Construction.s2 θ')) θ :=
    hw.derivWithin (m := 1) (by norm_num)
  have hmain : HasDerivAt (deriv (fun θ' => Q z θ' / Work.Construction.s2 θ'))
      (Work.Spaces.pthIter 2 (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ) θ := by
    have h2 := (hderiv.differentiableAt (by norm_num)).hasDerivAt
    convert h2 using 1
    simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  rw [hval] at hmain
  exact hmain

end Work.FTS_StreamBdry.SB3.P2Aux
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB3.P2Aux.pthIter2_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB3.P2Aux

open scoped Real Topology

/-! ## Calculus helpers

The proof is the second-order product rule for `Q = sin 2θ · (Q / sin 2θ)` on the `θ`-slice,
combined with the ground-state identity `bslOp α Q = s2 · Lgs α (Q/s2)` of
`SB25.bslOp_split` (which supplies exactly the `Dz`-terms of the statement). -/

/-- `iteratedDeriv 2 f = deriv (deriv f)`. -/
private lemma iteratedDeriv_two_eq (f : ℝ → ℝ) :
    iteratedDeriv 2 f = deriv (deriv f) := by
  have h : (2 : ℕ) = 1 + 1 := rfl
  rw [h, iteratedDeriv_succ, iteratedDeriv_one]

/-- `deriv s2 θ = 2 cos 2θ`. -/
private lemma deriv_s2_eq (θ : ℝ) :
    deriv Work.Construction.s2 θ = 2 * Real.cos (2 * θ) := by
  have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h3 : HasDerivAt (Real.sin ∘ fun θ' : ℝ => 2 * θ') (Real.cos (2 * θ) * 2) θ :=
      (Real.hasDerivAt_sin (2 * θ)).comp θ h2
    have h4 : Real.cos (2 * θ) * 2 = 2 * Real.cos (2 * θ) := by ring
    rw [h4] at h3
    convert h3 using 1
    funext x; rfl
  show deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ)
  exact h.deriv

/-- `iteratedDeriv 2 s2 θ = -4 s2 θ` (i.e. `s2'' = -4 s2`). -/
private lemma iteratedDeriv_two_s2 (θ : ℝ) :
    iteratedDeriv 2 Work.Construction.s2 θ = -4 * Work.Construction.s2 θ := by
  have h : HasDerivAt (fun θ' : ℝ => 2 * Real.cos (2 * θ')) (-4 * Real.sin (2 * θ)) θ := by
    have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h3 : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-Real.sin (2 * θ) * 2) θ := by
      have hh := (Real.hasDerivAt_cos (2 * θ)).comp θ h2
      simpa only [Function.comp_def] using hh
    have h4 : HasDerivAt (fun θ' : ℝ => 2 * Real.cos (2 * θ'))
        (2 * (-Real.sin (2 * θ) * 2)) θ := h3.const_mul (2 : ℝ)
    have h5 : 2 * (-Real.sin (2 * θ) * 2) = -4 * Real.sin (2 * θ) := by ring
    rw [h5] at h4
    exact h4
  rw [iteratedDeriv_two_eq]
  have hd : deriv Work.Construction.s2 = fun θ' : ℝ => 2 * Real.cos (2 * θ') :=
    funext deriv_s2_eq
  rw [hd, h.deriv]
  rfl

/-- **Second-order product rule for `Q = s2 · u` on the `θ`-slice**:
`Q_{θθ} = -4 s2 u + 4 cos 2θ · u' + s2 · u_{θθ}`. -/
private lemma pthIter2_prod {Q : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hQ : ContDiffAt ℝ 2 (Function.uncurry Q) (z, θ))
    (hsin : Work.Construction.s2 θ ≠ 0) :
    Work.Spaces.pthIter 2 Q z θ
      = -4 * Work.Construction.s2 θ * (Q z θ / Work.Construction.s2 θ)
        + 4 * Real.cos (2 * θ) * deriv (fun θ' => Q z θ' / Work.Construction.s2 θ') θ
        + Work.Construction.s2 θ
          * Work.Spaces.pthIter 2 (fun z θ' => Q z θ' / Work.Construction.s2 θ') z θ := by
  have hs2C : ContDiffAt ℝ 2 Work.Construction.s2 θ := by
    show ContDiffAt ℝ 2 (fun θ' : ℝ => Real.sin (2 * θ')) θ
    fun_prop
  have hA : ContDiffAt ℝ 2 (fun θ' : ℝ => Q z θ') θ := by
    have h := hQ.comp θ (ContDiffAt.prodMk contDiffAt_const contDiffAt_id)
    simpa only [Function.comp_def, Function.uncurry] using h
  have hB : ContDiffAt ℝ 2 (fun θ' : ℝ => Q z θ' / Work.Construction.s2 θ') θ :=
    hA.div hs2C hsin
  have hcont : ContinuousAt Work.Construction.s2 θ := hs2C.continuousAt
  have hev : (fun θ' : ℝ => Q z θ') =ᶠ[𝓝 θ]
      (Work.Construction.s2 * fun θ' : ℝ => Q z θ' / Work.Construction.s2 θ') := by
    filter_upwards [hcont.preimage_mem_nhds (isOpen_ne (x := (0 : ℝ)) |>.mem_nhds hsin)]
      with θ' hθ'
    exact (mul_div_cancel₀ (Q z θ') hθ').symm
  have h1 : Work.Spaces.pthIter 2 Q z θ = iteratedDeriv 2 (fun θ' : ℝ => Q z θ') θ := by
    rw [iteratedDeriv_two_eq]
    simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  have h2 : Work.Spaces.pthIter 2 (fun z θ' => Q z θ' / Work.Construction.s2 θ') z θ
      = iteratedDeriv 2 (fun θ' : ℝ => Q z θ' / Work.Construction.s2 θ') θ := by
    rw [iteratedDeriv_two_eq]
    simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  rw [h1, Filter.EventuallyEq.iteratedDeriv_eq 2 hev, iteratedDeriv_mul hs2C hB, h2]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.reduceSub, iteratedDeriv_zero]
  norm_num
  rw [deriv_s2_eq, iteratedDeriv_two_s2, Work.Construction.s2_eq]
  ring

/-- The second `θ`-derivative of `Q` in terms of `u := Q/s2` and `F = bslOp α Q`:
`Q_{θθ} = -4 s2 u + 2 sin^2 θ * u' - F - s2 * (α^2 DzIter 2 u + 5 α Dz u)`.
Product rule on `Q = s2 * u` together with `bslOp α Q = -s2 * Lgs α u` (equivalently
`bslOp_div_s2_hasDerivAt`, which is being proved in parallel at the sibling path). -/
theorem pthIter2_eq {α : ℝ} {Q F : ℝ → ℝ → ℝ}
    (hCt : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 2 (Function.uncurry Q) (z, θ))
    (hlaw : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Elliptic.bslOp α Q z θ = F z θ) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pthIter 2 Q z θ
        = -4 * Work.Construction.s2 θ * (Q z θ / Work.Construction.s2 θ)
          + 2 * Real.sin θ ^ 2 * deriv (fun θ' => Q z θ' / Work.Construction.s2 θ') θ
          - F z θ
          - Work.Construction.s2 θ
              * (α ^ 2 * Work.Spaces.DzIter 2 (fun z θ => Q z θ / Work.Construction.s2 θ) z θ
                  + 5 * α * Work.Spaces.Dz (fun z θ => Q z θ / Work.Construction.s2 θ) z θ) := by
  intro z θ hmem
  have hs2 : Work.Construction.s2 θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.s2_pos_of_Qd hmem)
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Qd hmem)
  have hsplit : Work.Elliptic.bslOp α Q z θ
      = Work.Construction.s2 θ * Work.FTS_StreamBdry.SB25.Lgs α
          (fun z θ' => Q z θ' / Work.Construction.s2 θ') z θ :=
    Work.FTS_StreamBdry.SB25.bslOp_split α Q hmem (hCt z θ hmem)
  have hF : F z θ = Work.Construction.s2 θ * Work.FTS_StreamBdry.SB25.Lgs α
      (fun z θ' => Q z θ' / Work.Construction.s2 θ') z θ := by
    rw [← hlaw z θ hmem, hsplit]
  rw [pthIter2_prod (hCt z θ hmem) hs2, hF]
  simp only [Work.FTS_StreamBdry.SB25.Lgs, Work.Spaces.pth]
  rw [Work.Construction.s2_eq]
  have hc : Real.sin (2 * θ) * (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ)
      = 4 * Real.cos (2 * θ) - 2 * Real.sin θ ^ 2 := by
    have hs : Real.sin (2 * θ) ≠ 0 := by
      rw [← Work.Construction.s2_eq]; exact hs2
    rw [mul_sub, mul_div_cancel₀ _ hs]
    rw [mul_comm (Real.sin (2 * θ)) (Real.tan θ), ← Work.Construction.s2_eq θ,
      Work.FTS_StreamBdry.tan_mul_s2 hcos]
  linear_combination (-(deriv (fun θ' => Q z θ' / Work.Construction.s2 θ') θ)) * hc

end Work.FTS_StreamBdry.SB3.P2Aux
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB3.law_psiP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB3.law_psiP` — the elliptic law in `D`-form for `psiP`

The SB3 chain (`sb3_bounds`, `sb2_dthDV`, `sb6_rates`) needs the law

`∂_θ V(psiP) = -(αG² D_z² psiP + 5 αG D_z psiP + 6 psiP) - F`

of `SB25.law_Dform`, applied not to `Ψ` but to the `U`-slot part `psiP αG Ψ`.  The passage
`Ψ → psiP` is the gauge decomposition of SB1′

`Ψ = psiP αG Ψ + κ·gaugeMode αG`  on `Qd`,

together with the two facts supplied by `SB25`:

* `gaugeMode` is `bslOp`-harmonic on the quadrant (`SB25.gaugeMode_facts`);
* `bslOp` is additive (`Work.Elliptic.bslOp_add`) and homogeneous
  (`Work.FTS.BSIdent.OddExt.bslOp_const_mul`), and — crucially — *local*
  (`Work.FTS.H2.PhiStarE5.bslOp_congr_of_eventuallyEq`), so that the pointwise identity on the
  open quadrant may be used inside `bslOp`.

Conclusion: `bslOp αG (psiP αG Ψ) = F` on `Qd`, whence `SB25.law_Dform` at `P := psiP αG Ψ`
(`C²` is `SB3.psiP_c2`) gives the stated law.
-/

set_option autoImplicit false

open scoped Real Topology
open Filter Set

namespace Work.FTS_StreamBdry.SB3

theorem law_psiP {αG M : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pth (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ)) z θ
        = -(αG ^ 2 * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ
            + 5 * αG * Work.Spaces.Dz (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ
            + 6 * Work.FTS.StreamBdryIface.psiP αG Ψ z θ) - F z θ := by
  -- SB1′: on the open quadrant, `Ψ = psiP αG Ψ + κ·gaugeMode αG`
  obtain ⟨κ, hκ⟩ := Work.FTS_StreamBdry.SB1.sb1_gauge_of_parts (αG := αG) (M := M)
    hαG h3 hslot
    (Work.FTS_StreamBdry.SB1.psiP_ode hαG h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_diff hαG h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_Vop_bnd hαG h3 hslot)
  -- `psiP` is `C²` on the quadrant, and so is the gauge summand
  have hC2 : ContDiffOn ℝ 2
      (Function.uncurry (Work.FTS.StreamBdryIface.psiP αG Ψ)) Work.Construction.Qd :=
    psiP_c2 hαG h3 hslot
  have hgau : ContDiffOn ℝ 2
      (Function.uncurry (Work.FTS.StreamBdryIface.gaugeMode αG)) Work.Construction.Qd :=
    (Work.FTS_StreamBdry.SB25.contDiffOn_uncurry_gaugeMode αG).of_le le_top
  -- the elliptic law for `psiP`: `bslOp αG (psiP αG Ψ) = F` on `Qd`
  have hlaw : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Elliptic.bslOp αG (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ = F z θ := by
    intro z θ hmem
    obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hmem
    have hcos : Real.cos θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Qd hmem)
    have hnbhd : Work.Construction.Qd ∈ 𝓝 (z, θ) :=
      Work.FTS_StreamBdry.SB25.qd_isOpen.mem_nhds ⟨hz, hθ1, hθ2⟩
    -- the gauge decomposition holds near `(z,θ)`, hence `bslOp` cannot see the difference
    have hev : ∀ᶠ q in 𝓝 (z, θ),
        Ψ q.1 q.2 = (Work.FTS.StreamBdryIface.psiP αG Ψ q.1 q.2
          + κ * Work.FTS.StreamBdryIface.gaugeMode αG q.1 q.2) :=
      Filter.mem_of_superset hnbhd (fun q hq => hκ q.1 q.2 hq)
    have hcongr : Work.Elliptic.bslOp αG Ψ z θ
        = Work.Elliptic.bslOp αG (fun z θ =>
            Work.FTS.StreamBdryIface.psiP αG Ψ z θ
              + κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ) z θ :=
      Work.FTS.H2.PhiStarE5.bslOp_congr_of_eventuallyEq αG hev
    -- additivity of `bslOp` at `(z,θ)`
    have hg2 : ContDiffAt ℝ 2
        (Function.uncurry (fun z θ => κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ))
        (z, θ) :=
      (hgau.contDiffAt hnbhd).const_smul κ
    have hadd : Work.Elliptic.bslOp αG (fun z θ =>
          Work.FTS.StreamBdryIface.psiP αG Ψ z θ
            + κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ) z θ
        = Work.Elliptic.bslOp αG (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ
          + Work.Elliptic.bslOp αG (fun z θ =>
              κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ) z θ :=
      Work.Elliptic.bslOp_add αG (Work.FTS.StreamBdryIface.psiP αG Ψ)
        (fun z θ => κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ) z θ hcos
        (hC2.contDiffAt hnbhd) hg2
    -- the gauge summand is `bslOp`-harmonic
    have hD0 : Work.Elliptic.bslOp αG
        (fun z θ => κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ) z θ = 0 := by
      rw [Work.FTS.BSIdent.OddExt.bslOp_const_mul αG κ
            (Work.FTS.StreamBdryIface.gaugeMode αG) z θ,
        ((Work.FTS_StreamBdry.SB25.gaugeMode_facts hαG).2 z θ hmem).2, mul_zero]
    calc Work.Elliptic.bslOp αG (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ
        = Work.Elliptic.bslOp αG (fun z θ =>
            Work.FTS.StreamBdryIface.psiP αG Ψ z θ
              + κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ) z θ := by
          rw [hadd, hD0, add_zero]
      _ = Work.Elliptic.bslOp αG Ψ z θ := hcongr.symm
      _ = F z θ := hsol.1 z hz θ hθ1 hθ2
  -- `SB25.law_Dform` for `P := psiP αG Ψ`
  exact Work.FTS_StreamBdry.SB25.law_Dform αG F (Work.FTS.StreamBdryIface.psiP αG Ψ) hC2 hlaw

end Work.FTS_StreamBdry.SB3
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB3.psiP_DzLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB3.psiP_DzLe` — `|D_z^j psiP| ≤ M·sin 2θ` for `j ≤ 2`

The SB3 bound `Work.FTS_StreamBdry.PsiPDzLe`: for a `C³` stream function `Ψ` on the open
quadrant whose slot `U'(Ψ) = (-3Ψ - αG z∂_zΨ)/sin 2θ` satisfies the `SlotBd` bounds
(`|D_z^j U'(Ψ)| ≤ M` for `j ≤ 2`, `|D_θ U'(Ψ)| ≤ M`, `|D_z^j V(Ψ)| ≤ M` for `j ≤ 1`), the
`U`-slot part `psiP αG Ψ` of `Ψ` satisfies `|D_z^j (psiP)| ≤ M·sin 2θ` there, for `j ≤ 2`.

Proof (see `SBpsiP/Assembly.lean`): `psiP αG Ψ = -(s2 θ/αG)·J c (U'(Ψ))` *definitionally*
(`c = 3/αG - 1`, `J` the scaled parameter integral of `SB3/DzJDefs`), and `D_z = z∂_z`
commutes with that integral (`SBpsiP.J_Dz_eq`, the crux), hence

  `D_z^j (psiP αG Ψ) = -(s2 θ/αG)·J c (D_z^j U'(Ψ))`   (`j ≤ 2`),

so with `|J c h z θ| ≤ M·(αG/3)` whenever `|h| ≤ M` (`SBpsiP.J_bound_self`),

  `|D_z^j (psiP)| ≤ (s2/αG)·M·(αG/3) = M·sin 2θ/3 ≤ M·sin 2θ`.

The two structural ingredients are the finite-order smoothness of the slot iterates
(`SBpsiP.UprimeIterSmooth_self`, from `Ψ ∈ C³`) and the elementary scaled-integral bound.
-/

noncomputable section

open scoped Real Topology

namespace Work.FTS_StreamBdry.SB3

set_option autoImplicit false

theorem psiP_DzLe {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M) :
    Work.FTS_StreamBdry.PsiPDzLe αG M Ψ := by
  exact Work.FTS_StreamBdry.SBpsiP.psiP_DzLe_of_pieces
    (fun αG hαG Ψ h3 => Work.FTS_StreamBdry.SBpsiP.UprimeIterSmooth_self hαG h3)
    (fun c B hc hB φ hcont hφ => Work.FTS_StreamBdry.SBpsiP.J_bound_self hc hB hcont hφ)
    hαG h3 hslot

end Work.FTS_StreamBdry.SB3
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB3.pth_DzIter_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB3.pth_DzIter_le` — the angular derivative of the `U`-slot part

The second and third conjuncts of `sb3_bounds`: for a `C³` stream function `Ψ` on the open
quadrant `Qd = (0,∞) × (0,π/2)` whose slot `U'(Ψ)` satisfies the `SlotBd` bounds and whose
particular solution `P := psiP αG Ψ` satisfies `|D_z^j P| ≤ Sg·sin 2θ` for `j ≤ 3`, the plain
angular derivative `∂_θ(D_z^j P)` is bounded on `Qd` for `j ≤ 1`.

## The mechanism

`∂_θ P = V(P) + tan θ·P` where `V(Ψ) = ∂_θΨ - tan θ·Ψ` (`Construction.Vop`).  The point of the
statement is that `V` **cannot see the gauge mode** `gaugeMode αG = z^{-3/αG}/cos θ`
(`Vop_gaugeMode`), while SB1′ (`Work.FTS_StreamBdry.SB1.sb1_gauge_of_parts`) says that
`Ψ - P` *is* a multiple of the gauge mode on `Qd`.  Hence

  `V(P) = V(Ψ)`   (`Vop_psiP_eq`, proved here),

and since `SlotBd` bounds `|D_z^j (V Ψ)|` for `j ≤ 1` (`SlotBd.V_le`), while `hK` bounds the
`z`-derivatives of `P` itself, both cases `j ≤ 1` are immediate:

* `j = 0`: `|∂_θP| ≤ |V Ψ| + |tan θ·P| ≤ M + 2 Sg`, using
  `tan θ·sin 2θ = 2 sin²θ ≤ 2` (`tan_mul_s2`);
* `j = 1`: Clairaut (`Work.Spaces.pz_pth_comm`, from `SB3.psiP_c2`) and the angular/rational
  commutation `∂_θ(D_zP) = z·∂_θ∂_zP = z·∂_z∂_θP` turn `∂_θ(D_zP)` into
  `D_z(V Ψ) + tan θ·D_zP`, bounded by `M + 2 Sg`.

Every step is carried out on `Qd` only (where `sin 2θ > 0` and `cos θ > 0`): the boundary
`θ = 0, π/2` is exactly where `tan θ` is not differentiable.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB3

open Work.FTS.StreamBdryIface (Uprime SlotBd gaugeMode psiP)

set_option autoImplicit false

/-! ## §0 Local regularity helpers on the open quadrant -/

/-- The `θ`-partial of a function of class `C^{n+1}` on the open quadrant is of class `C^n`. -/
theorem contDiffOn_uncurry_pth_qd {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) Work.Construction.Qd) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) Work.Construction.Qd := by
  have hQd : IsOpen Work.Construction.Qd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  have hchain : ∀ p ∈ Work.Construction.Qd,
      Work.Spaces.pth G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by norm_num : (n + 1 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (hQd.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p)
      Work.Construction.Qd := h.fderiv_of_isOpen hQd (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) Work.Construction.Qd :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- A `z`-slice of `V Ψ = ∂_θΨ - tan θ·Ψ` is differentiable on the open quadrant, because
`Ψ` is `C³` there (so `∂_θΨ` is `C²`, hence differentiable in `z`). -/
theorem differentiableAt_Vop_slice {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd) {z θ : ℝ}
    (hmem : (z, θ) ∈ Work.Construction.Qd) :
    DifferentiableAt ℝ (fun z' => Work.Construction.Vop Ψ z' θ) z := by
  have hQd : IsOpen Work.Construction.Qd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  have hpth_sm : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth Ψ)) Work.Construction.Qd :=
    contDiffOn_uncurry_pth_qd (n := 2) h3
  have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.pth Ψ z' θ) z :=
    Work.Spaces.differentiableAt_curry_left
      ((hpth_sm.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmem))
  have hd2 : DifferentiableAt ℝ (fun z' => Ψ z' θ) z :=
    Work.FTS_StreamBdry.SB1.diffAt_z_slice hmem h3
  change DifferentiableAt ℝ (fun z' => Work.Spaces.pth Ψ z' θ - Real.tan θ * Ψ z' θ) z
  exact hd1.sub (hd2.const_mul (Real.tan θ))

/-! ## §1 The gauge mode is `V`-invisible, and `V(psiP) = V(Ψ)` -/

/-- The gauge mode is `V`-invisible, in the `∂_θ` form: `∂_θ(gaugeMode) = tan θ · gaugeMode`. -/
lemma pth_gaugeMode_eq {αG z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    Work.Spaces.pth (gaugeMode αG) z θ = Real.tan θ * gaugeMode αG z θ := by
  have hc : Real.cos θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Qd h)
  have hh := Work.FTS_StreamBdry.Vop_gaugeMode (αG := αG) (z := z) (θ := θ) hc
  rw [Work.Construction.Vop] at hh
  linarith

/-- **`V` cannot see the gauge mode**: `V(psiP αG Ψ) = V(Ψ)` on the open quadrant.

This is the only place where SB1′ enters: `Ψ - psiP αG Ψ = κ·gaugeMode` on `Qd`
(`SB1.sb1_gauge_of_parts`), and both `∂_θ` (on the difference) and `V(gaugeMode)` are handled
by the explicit formula `∂_θ(gaugeMode) = tan θ·gaugeMode`. -/
lemma Vop_psiP_eq {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.Vop (psiP αG Ψ) z θ = Work.Construction.Vop Ψ z θ := by
  have hpdiff : Work.FTS_StreamBdry.PsiPDiff αG M Ψ :=
    Work.FTS_StreamBdry.SB1.psiP_diff hαG h3 hslot
  obtain ⟨κ, hκ⟩ := Work.FTS_StreamBdry.SB1.sb1_gauge_of_parts hαG h3 hslot
    (Work.FTS_StreamBdry.SB1.psiP_ode hαG h3 hslot) hpdiff
    (Work.FTS_StreamBdry.SB1.psiP_Vop_bnd hαG h3 hslot)
  intro z θ hmem
  have hsub := Work.FTS_StreamBdry.SB1.Vop_sub_psiP (αG := αG) (M := M) (Ψ := Ψ) hmem h3 hpdiff
  have hθm := Work.FTS_StreamBdry.Qd_theta_mem hmem
  have hzpos := Work.FTS_StreamBdry.Qd_pos hmem
  -- the difference `Ψ - psiP` is `κ·gaugeMode` near `θ`
  have hev : (fun θ' => Ψ z θ' - psiP αG Ψ z θ')
      =ᶠ[𝓝 θ] (fun θ' => κ * gaugeMode αG z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθm] with θ' hθ'
    have hh := hκ z θ' (Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, hθ'.1, hθ'.2⟩)
    linarith
  have hpthW : Work.Spaces.pth (fun z' θ' => Ψ z' θ' - psiP αG Ψ z' θ') z θ
      = κ * Work.Spaces.pth (gaugeMode αG) z θ := by
    have h := hev.deriv_eq
    rw [deriv_const_mul_field] at h
    simpa only [Work.Spaces.pth] using h
  have hκz : Ψ z θ - psiP αG Ψ z θ = κ * gaugeMode αG z θ := by
    have hh := hκ z θ hmem
    linarith
  have hgV : Work.Spaces.pth (gaugeMode αG) z θ = Real.tan θ * gaugeMode αG z θ :=
    pth_gaugeMode_eq hmem
  have hzero : Work.Construction.Vop Ψ z θ - Work.Construction.Vop (psiP αG Ψ) z θ = 0 := by
    rw [← hsub, Work.Construction.Vop, hpthW, hκz, hgV]
    ring
  linarith

/-! ## §2 The `j = 1` split: `∂_z ∂_θ P = ∂_z(V Ψ) + tan θ · ∂_z P` -/

/-- The `θ`-identity `∂_θP = V(Ψ) + tan θ·P` holds with `z`-independent coefficients, so its
`z`-derivative splits as `∂_z(V Ψ) + tan θ·∂_zP`.  The two summands are differentiable in `z`
(`V Ψ` because `∂_θΨ` is `C²` on the open quadrant, `tan θ·P` by `PsiPDiff`), which is exactly
what `deriv_add` needs. -/
lemma pz_pth_psiP_eq {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) {z θ : ℝ} (hmem : (z, θ) ∈ Work.Construction.Qd) :
    Work.Spaces.pz (Work.Spaces.pth (psiP αG Ψ)) z θ
      = Work.Spaces.pz (Work.Construction.Vop Ψ) z θ
        + Real.tan θ * Work.Spaces.pz (psiP αG Ψ) z θ := by
  have hpdiff : Work.FTS_StreamBdry.PsiPDiff αG M Ψ :=
    Work.FTS_StreamBdry.SB1.psiP_diff hαG h3 hslot
  have hV := Vop_psiP_eq hαG h3 hslot
  have hzpos := Work.FTS_StreamBdry.Qd_pos hmem
  have hθm := Work.FTS_StreamBdry.Qd_theta_mem hmem
  have hev : (fun z' => Work.Spaces.pth (psiP αG Ψ) z' θ)
      =ᶠ[𝓝 z] (fun z' => Work.Construction.Vop Ψ z' θ
        + Real.tan θ * psiP αG Ψ z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hzpos] with z' hz'
    have hm' : (z', θ) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr ⟨hz', hθm.1, hθm.2⟩
    have hh := hV z' θ hm'
    rw [Work.Construction.Vop] at hh
    linarith
  rw [show Work.Spaces.pz (Work.Spaces.pth (psiP αG Ψ)) z θ
      = deriv (fun z' => Work.Spaces.pth (psiP αG Ψ) z' θ) z from rfl, hev.deriv_eq]
  have hd1 : DifferentiableAt ℝ (fun z' => Work.Construction.Vop Ψ z' θ) z :=
    differentiableAt_Vop_slice h3 hmem
  have hd2 : DifferentiableAt ℝ (fun z' => Real.tan θ * psiP αG Ψ z' θ) z :=
    (hpdiff z θ hmem).1.const_mul (Real.tan θ)
  rw [show (fun z' => Work.Construction.Vop Ψ z' θ + Real.tan θ * psiP αG Ψ z' θ)
      = (fun z' => Work.Construction.Vop Ψ z' θ)
        + (fun z' => Real.tan θ * psiP αG Ψ z' θ) from rfl,
    deriv_add hd1 hd2, deriv_const_mul_field]
  rfl

/-! ## §3 The theorem -/

theorem pth_DzIter_le {αG M Sg : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hK : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 3,
      |Work.Spaces.DzIter j (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ|
        ≤ Sg * Work.Construction.s2 θ) :
    ∃ K', ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 1,
      |Work.Spaces.pth (Work.Spaces.DzIter j
        (Work.FTS.StreamBdryIface.psiP αG Ψ)) z θ| ≤ K' := by
  refine ⟨M + 2 * Sg, ?_⟩
  -- `Sg ≥ 0` from `hK` at the interior point `(1, π/4)`, where `s2 = 1`
  have hSg0 : 0 ≤ Sg := by
    have h1 : |Work.Spaces.DzIter 0 (psiP αG Ψ) (1 : ℝ) (Real.pi / 4)|
        ≤ Sg * Work.Construction.s2 (Real.pi / 4) :=
      hK 1 (Real.pi / 4) Work.FTS_StreamBdry.SB1.Qd_nonempty 0 (by norm_num)
    have h2 : Work.Construction.s2 (Real.pi / 4) = 1 := by
      rw [Work.Construction.s2_eq, show 2 * (Real.pi / 4) = Real.pi / 2 by ring,
        Real.sin_pi_div_two]
    rw [Work.Spaces.DzIter_zero, h2, mul_one] at h1
    exact le_trans (abs_nonneg _) h1
  intro z θ hmem j hj
  have hθm := Work.FTS_StreamBdry.Qd_theta_mem hmem
  have hcospos : 0 < Real.cos θ := Work.FTS_StreamBdry.cos_pos_of_Qd hmem
  have htan_nonneg : 0 ≤ Real.tan θ := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg
      (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθm.1])
        (by linarith [hθm.2, Real.pi_pos])))
      (le_of_lt hcospos)
  -- the elementary bound `|tan θ·X| ≤ 2 Sg` whenever `|X| ≤ Sg·s2 θ`
  have htanX : ∀ X : ℝ, |X| ≤ Sg * Work.Construction.s2 θ →
      |Real.tan θ * X| ≤ 2 * Sg := by
    intro X hX
    have h1 : Real.tan θ * |X| ≤ Real.tan θ * (Sg * Work.Construction.s2 θ) :=
      mul_le_mul_of_nonneg_left hX htan_nonneg
    have h2 : Real.tan θ * (Sg * Work.Construction.s2 θ) = 2 * Sg * Real.sin θ ^ 2 := by
      rw [show Real.tan θ * (Sg * Work.Construction.s2 θ)
          = Sg * (Real.tan θ * Work.Construction.s2 θ) from by ring,
        Work.FTS_StreamBdry.tan_mul_s2 (ne_of_gt hcospos)]
      ring
    have h3 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    rw [abs_mul, abs_of_nonneg htan_nonneg]
    calc Real.tan θ * |X| ≤ Real.tan θ * (Sg * Work.Construction.s2 θ) := h1
      _ = 2 * Sg * Real.sin θ ^ 2 := h2
      _ ≤ 2 * Sg * 1 := mul_le_mul_of_nonneg_left h3 (by linarith)
      _ = 2 * Sg := by ring
  interval_cases j
  · -- `j = 0`: `∂_θP = V(Ψ) + tan θ·P`
    have hkey : Work.Spaces.pth (psiP αG Ψ) z θ
        = Work.Construction.Vop Ψ z θ + Real.tan θ * psiP αG Ψ z θ := by
      have hh := Vop_psiP_eq hαG h3 hslot z θ hmem
      rw [Work.Construction.Vop] at hh
      linarith
    have hb1 : |Work.Construction.Vop Ψ z θ| ≤ M :=
      Work.FTS_StreamBdry.SlotBd.V_le hslot hmem (j := 0) (by norm_num)
    have hb2 : |Real.tan θ * psiP αG Ψ z θ| ≤ 2 * Sg :=
      htanX _ (hK z θ hmem 0 (by norm_num))
    rw [Work.Spaces.DzIter_zero, hkey]
    exact (abs_add_le _ _).trans (add_le_add hb1 hb2)
  · -- `j = 1`: `∂_θ(D_zP) = D_z(V Ψ) + tan θ·D_zP`
    have hcd : ContDiffAt ℝ 2 (Function.uncurry (psiP αG Ψ)) (z, θ) :=
      (Work.FTS_StreamBdry.SB3.psiP_c2 hαG h3 hslot).contDiffAt
        (Work.FTS_StreamBdry.SB1.isOpen_Qd.mem_nhds hmem)
    have hstep1 : Work.Spaces.pth (Work.Spaces.Dz (psiP αG Ψ)) z θ
        = z * Work.Spaces.pth (Work.Spaces.pz (psiP αG Ψ)) z θ := by
      show deriv (fun θ' => z * Work.Spaces.pz (psiP αG Ψ) z θ') θ
        = z * Work.Spaces.pth (Work.Spaces.pz (psiP αG Ψ)) z θ
      rw [deriv_const_mul_field]
      rfl
    have hfinal : Work.Spaces.pth (Work.Spaces.Dz (psiP αG Ψ)) z θ
        = Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ
          + Real.tan θ * Work.Spaces.Dz (psiP αG Ψ) z θ := by
      rw [hstep1, (Work.Spaces.pz_pth_comm hcd).symm, pz_pth_psiP_eq hαG h3 hslot hmem]
      simp only [Work.Spaces.Dz]
      ring
    have hb1 : |Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ| ≤ M := by
      simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
        Work.FTS_StreamBdry.SlotBd.V_le hslot hmem (j := 1) (by norm_num)
    have hb2 : |Real.tan θ * Work.Spaces.Dz (psiP αG Ψ) z θ| ≤ 2 * Sg :=
      htanX _ (by
        simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
          hK z θ hmem 1 (by norm_num))
    rw [show Work.Spaces.DzIter 1 (psiP αG Ψ) = Work.Spaces.Dz (psiP αG Ψ) from rfl,
      hfinal]
    exact (abs_add_le _ _).trans (add_le_add hb1 hb2)

end Work.FTS_StreamBdry.SB3
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeBound1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.UprimeAux.OdeBound1` — the two-point bound and the crude pointwise bound

If `u'' = H - c u'` on `(0, π/2)` with `|H| ≤ A / sin 2θ + C`, then `G = wfun · u'` satisfies
`G' = wfun · H`, so `|G θ - G ξ| ≤ ∫_ξ^θ gwt A C` (the comparison argument, using that
`gwt A C` is continuous so its primitive is differentiable).  Moreover, the extra global bound
`|sin 2θ · u'| ≤ C₁` gives `|G ξ| ≤ C₁ · wfun ξ / sin 2ξ`, which vanishes at both endpoints.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6.UprimeAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **Two-point bound.**  `|G θ - G ξ| ≤ ∫_ξ^θ gwt A C` for `0 < ξ ≤ θ < π/2`. -/
lemma two_point {u H : ℝ → ℝ → ℝ} {z A C : ℝ}
    (hode : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (u1fun u z)
        (H z θ - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * u1fun u z θ) θ)
    (hH : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |H z θ| ≤ A / Real.sin (2 * θ) + C)
    {ξ θ : ℝ} (hξ : 0 < ξ) (hξθ : ξ ≤ θ) (hθ : θ < Real.pi / 2) :
    |wfun θ * u1fun u z θ - wfun ξ * u1fun u z ξ| ≤ ∫ t in ξ..θ, gwt A C t := by
  have hggcont : Continuous (fun t => gwt A C t) := continuous_gwt A C
  have hmem : ∀ x ∈ Set.Icc ξ θ, x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le hξ hx.1, lt_of_le_of_lt hx.2 hθ⟩
  have hmem' : ∀ x ∈ Set.Ico ξ θ, x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le hξ hx.1, lt_trans hx.2 hθ⟩
  have hG' : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (wfun * u1fun u z) (wfun x * H z x) x := by
    intro x hx
    have h1 := hode x hx
    have h2 := Wderiv hx
    have h3 := h2.mul h1
    have hv : (wfun x * (4 * Real.cos (2 * x) / Real.sin (2 * x) - Real.tan x)) * u1fun u z x
        + wfun x * (H z x - (4 * Real.cos (2 * x) / Real.sin (2 * x) - Real.tan x)
          * u1fun u z x) = wfun x * H z x := by ring
    rw [hv] at h3
    exact h3
  have hineq : ∀ x ∈ Set.Ico ξ θ, wfun x * H z x ≤ gwt A C x := by
    intro x hx
    have hxI := hmem' x hx
    have hwx : 0 ≤ wfun x := le_of_lt (Wpos hxI)
    have hHx := hH x hxI
    calc wfun x * H z x ≤ wfun x * (A / Real.sin (2 * x) + C) :=
          mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hHx) hwx
      _ = gwt A C x := by rw [gwt_def]; ring
  have hGcont : ContinuousOn (wfun * u1fun u z) (Set.Icc ξ θ) := fun x hx =>
    ((hG' x (hmem x hx)).continuousAt).continuousWithinAt
  have hprim : ContinuousOn (fun t => ∫ s in ξ..t, gwt A C s) (Set.Icc ξ θ) := by
    intro x hx
    have hint : IntervalIntegrable (fun t => gwt A C t) volume ξ x :=
      hggcont.intervalIntegrable ξ x
    have hsm : StronglyMeasurableAtFilter (fun t => gwt A C t) (𝓝 x) volume :=
      hggcont.stronglyMeasurableAtFilter volume (𝓝 x)
    exact ((intervalIntegral.integral_hasDerivAt_right hint hsm
      hggcont.continuousAt).continuousAt).continuousWithinAt
  have hB' : ∀ x ∈ Set.Ico ξ θ,
      HasDerivWithinAt (fun t => wfun ξ * u1fun u z ξ + ∫ s in ξ..t, gwt A C s) (gwt A C x)
        (Set.Ici x) x := by
    intro x hx
    have hint : IntervalIntegrable (fun t => gwt A C t) volume ξ x :=
      hggcont.intervalIntegrable ξ x
    have hsm : StronglyMeasurableAtFilter (fun t => gwt A C t) (𝓝 x) volume :=
      hggcont.stronglyMeasurableAtFilter volume (𝓝 x)
    exact ((intervalIntegral.integral_hasDerivAt_right hint hsm
      hggcont.continuousAt).const_add (wfun ξ * u1fun u z ξ)).hasDerivWithinAt
  have hup : wfun θ * u1fun u z θ ≤ wfun ξ * u1fun u z ξ + ∫ t in ξ..θ, gwt A C t :=
    image_le_of_deriv_right_le_deriv_boundary (f := wfun * u1fun u z)
      (f' := fun t => wfun t * H z t) (a := ξ) (b := θ)
      (B := fun t => wfun ξ * u1fun u z ξ + ∫ s in ξ..t, gwt A C s)
      (B' := fun t => gwt A C t)
      hGcont (fun x hx => (hG' x (hmem' x hx)).hasDerivWithinAt)
      (by simp) (continuousOn_const.add hprim) hB' hineq ⟨hξθ, le_refl θ⟩
  have hlow : wfun ξ * u1fun u z ξ ≤ wfun θ * u1fun u z θ + ∫ t in ξ..θ, gwt A C t := by
    have hmain : -(wfun θ * u1fun u z θ)
        ≤ -(wfun ξ * u1fun u z ξ) + ∫ t in ξ..θ, gwt A C t :=
      image_le_of_deriv_right_le_deriv_boundary (f := fun t => -(wfun t * u1fun u z t))
        (f' := fun t => -(wfun t * H z t)) (a := ξ) (b := θ)
        (B := fun t => -(wfun ξ * u1fun u z ξ) + ∫ s in ξ..t, gwt A C s)
        (B' := fun t => gwt A C t)
        hGcont.neg (fun x hx => (hG' x (hmem' x hx)).hasDerivWithinAt.neg) (by simp)
        (continuousOn_const.add hprim) (by
          intro x hx
          have hint : IntervalIntegrable (fun t => gwt A C t) volume ξ x :=
            hggcont.intervalIntegrable ξ x
          have hsm : StronglyMeasurableAtFilter (fun t => gwt A C t) (𝓝 x) volume :=
            hggcont.stronglyMeasurableAtFilter volume (𝓝 x)
          exact ((intervalIntegral.integral_hasDerivAt_right hint hsm
            hggcont.continuousAt).const_add (-(wfun ξ * u1fun u z ξ))).hasDerivWithinAt)
        (by
          intro x hx
          have hxI := hmem' x hx
          have hwx : 0 ≤ wfun x := le_of_lt (Wpos hxI)
          have hHx := hH x hxI
          calc -(wfun x * H z x) = wfun x * (-(H z x)) := by ring
            _ ≤ wfun x * (A / Real.sin (2 * x) + C) :=
                mul_le_mul_of_nonneg_left
                  (le_trans (neg_le_abs (H z x)) hHx) hwx
            _ = gwt A C x := by rw [gwt_def]; ring)
        ⟨hξθ, le_refl θ⟩
    linarith
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- **Crude bound**: `|sin 2θ · u'| ≤ C₁` gives `|G ξ| ≤ C₁ · wfun ξ / sin 2ξ`. -/
lemma crude_G {u H : ℝ → ℝ → ℝ} {z C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hcrude : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Real.sin (2 * θ) * u1fun u z θ| ≤ C₁)
    {ξ : ℝ} (hξ : ξ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |wfun ξ * u1fun u z ξ| ≤ C₁ * (wfun ξ / Real.sin (2 * ξ)) := by
  have hw : 0 ≤ wfun ξ := le_of_lt (Wpos hξ)
  have hs : 0 < Real.sin (2 * ξ) := by
    rw [Real.sin_two_mul]
    have h1 : 0 < Real.sin ξ :=
      Real.sin_pos_of_pos_of_lt_pi hξ.1 (by linarith [hξ.2, Real.pi_pos])
    have h2 : 0 < Real.cos ξ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hξ.1], hξ.2⟩
    positivity
  have h1 : |wfun ξ * u1fun u z ξ| = wfun ξ * |u1fun u z ξ| := by
    rw [abs_mul, abs_of_nonneg hw]
  have h2 : |u1fun u z ξ| ≤ C₁ / Real.sin (2 * ξ) := by
    rw [le_div_iff₀ hs]
    calc |u1fun u z ξ| * Real.sin (2 * ξ)
        = |Real.sin (2 * ξ) * u1fun u z ξ| := by rw [abs_mul, abs_of_pos hs, mul_comm]
      _ ≤ C₁ := hcrude ξ hξ
  rw [h1]
  calc wfun ξ * |u1fun u z ξ| ≤ wfun ξ * (C₁ / Real.sin (2 * ξ)) :=
        mul_le_mul_of_nonneg_left h2 hw
    _ = C₁ * (wfun ξ / Real.sin (2 * ξ)) := by ring

end Work.FTS_StreamBdry.SB6.UprimeAux
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB6.clauses1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP oddPerS)

set_option autoImplicit false

theorem Phi_clause1 {αG M L Kf : ℝ} (hαG : 0 < αG) (hL : 0 < L) (hM : 0 ≤ M) (hKf0 : 0 ≤ Kf)
    {Ψ : ℝ → ℝ → ℝ} (hPpi : ∀ z, (psiP αG Ψ) z (Real.pi / 2) = 0)
    (hDz : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ)
    (hfar : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ|
        ≤ Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |(if 0 < w then oddPerS (psiP αG Ψ) w θ else 0)|
        ≤ A * (Real.pi / 2 - θ) * (1 + w) ^ (-(4 / αG)) := by
  refine ⟨2 * max M Kf * (1 + L) ^ (4 / αG), ?_, ?_⟩
  · have hmm : 0 ≤ max M Kf := le_max_of_le_left hM
    have hr : 0 ≤ (1 + L) ^ (4 / αG) := Real.rpow_nonneg (by linarith) _
    positivity
  intro w θ hw hθ hθ2
  have hmm : 0 ≤ max M Kf := le_max_of_le_left hM
  have hwd : 0 ≤ (1 + w) ^ (-(4 / αG)) := Real.rpow_nonneg (by linarith) _
  have hLw : 0 ≤ (1 + L) ^ (4 / αG) := Real.rpow_nonneg (by linarith) _
  have hA : 0 ≤ 2 * max M Kf * (1 + L) ^ (4 / αG) * (Real.pi / 2 - θ) := by positivity
  by_cases hw0 : 0 < w
  · by_cases hθ0 : 0 < θ
    · rw [Phi_eq_of_pos hPpi hw0 hθ0 (le_of_lt hθ2)]
      have hmem : (w, θ) ∈ Work.Construction.Qd :=
        Work.FTS_StreamBdry.mem_Qd.mpr ⟨hw0, hθ0, hθ2⟩
      have hs2nn : 0 ≤ Work.Construction.s2 θ :=
        Work.FTS_StreamBdry.s2_nonneg_of_Iθ (Work.FTS_StreamBdry.Qd_theta_Iθ hmem)
      have hs2le : Work.Construction.s2 θ ≤ 2 * (Real.pi / 2 - θ) :=
        s2_le_two_mul_sub (le_of_lt hθ2)
      have hπ : 0 ≤ Real.pi / 2 - θ := by linarith
      by_cases hwL : w ≤ L
      · -- compact
        have h1 : |(psiP αG Ψ) w θ| ≤ max M Kf * Work.Construction.s2 θ :=
          (hDz w θ hmem 0 (by norm_num)).trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hs2nn)
        have h3 : 1 ≤ (1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)) := by
          have h4 := one_add_rpow_neg_le hL (by positivity : (0:ℝ) ≤ 4 / αG) hw hwL
          have h5 : (1 + L) ^ (4 / αG) * (1 + L) ^ (-(4 / αG)) = 1 := by
            rw [← Real.rpow_add (by linarith), show 4 / αG + -(4 / αG) = 0 by ring]
            simp
          calc (1 : ℝ) = (1 + L) ^ (4 / αG) * (1 + L) ^ (-(4 / αG)) := h5.symm
            _ ≤ (1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)) :=
                mul_le_mul_of_nonneg_left h4 hLw
        calc |(psiP αG Ψ) w θ| ≤ max M Kf * Work.Construction.s2 θ := h1
          _ ≤ 2 * max M Kf * (Real.pi / 2 - θ) := by
              calc max M Kf * Work.Construction.s2 θ
                  ≤ max M Kf * (2 * (Real.pi / 2 - θ)) :=
                    mul_le_mul_of_nonneg_left hs2le hmm
                _ = 2 * max M Kf * (Real.pi / 2 - θ) := by ring
          _ = 2 * max M Kf * (Real.pi / 2 - θ) * 1 := by ring
          _ ≤ 2 * max M Kf * (Real.pi / 2 - θ)
                * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = 2 * max M Kf * (1 + L) ^ (4 / αG) * (Real.pi / 2 - θ)
                * (1 + w) ^ (-(4 / αG)) := by ring
      · -- far
        have hwL' : L ≤ w := le_of_not_ge hwL
        have h2 : |(psiP αG Ψ) w θ|
            ≤ Kf * Work.Construction.s2 θ * (L / w) ^ (4 / αG) :=
          hfar w θ hmem hwL' 0 (by norm_num)
        have h3 : (L / w) ^ (4 / αG) ≤ (1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)) :=
          div_rpow_le hL (by positivity : (0:ℝ) ≤ 4 / αG) hwL'
        have h4 : Kf * Work.Construction.s2 θ * (L / w) ^ (4 / αG)
            ≤ Kf * Work.Construction.s2 θ * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg hKf0 hs2nn)
        have h5 : Kf * Work.Construction.s2 θ * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)))
            ≤ 2 * max M Kf * (Real.pi / 2 - θ)
              * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hLw hwd)
          calc Kf * Work.Construction.s2 θ ≤ 2 * Kf * (Real.pi / 2 - θ) := by
                calc Kf * Work.Construction.s2 θ ≤ Kf * (2 * (Real.pi / 2 - θ)) :=
                      mul_le_mul_of_nonneg_left hs2le hKf0
                  _ = 2 * Kf * (Real.pi / 2 - θ) := by ring
            _ ≤ 2 * max M Kf * (Real.pi / 2 - θ) := by
                exact mul_le_mul_of_nonneg_right
                  (by linarith [le_max_right M Kf]) (by linarith)
        calc |(psiP αG Ψ) w θ| ≤ Kf * Work.Construction.s2 θ * (L / w) ^ (4 / αG) := h2
          _ ≤ Kf * Work.Construction.s2 θ
                * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) := h4
          _ ≤ 2 * max M Kf * (Real.pi / 2 - θ)
                * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) := h5
          _ = 2 * max M Kf * (1 + L) ^ (4 / αG) * (Real.pi / 2 - θ)
                * (1 + w) ^ (-(4 / αG)) := by ring
    · have hθeq : θ = 0 := le_antisymm (not_lt.mp hθ0) hθ
      rw [hθeq, Phi_zero_theta hPpi, abs_zero]
      have hwk : 0 ≤ (1 + (0:ℝ)) ^ (-(4 / αG)) := Real.rpow_nonneg (by norm_num) _
      have hπ : 0 ≤ Real.pi / 2 - 0 := by linarith [Real.pi_pos]
      have hr : 0 ≤ (1 + L) ^ (4 / αG) := Real.rpow_nonneg (by linarith) _
      positivity
  · rw [Phi_eq_zero_of_nonpos hw0, abs_zero]
    have hwk : 0 ≤ (1 + w) ^ (-(4 / αG)) := Real.rpow_nonneg (by linarith) _
    have hπ : 0 ≤ Real.pi / 2 - θ := by linarith
    have hr : 0 ≤ (1 + L) ^ (4 / αG) := Real.rpow_nonneg (by linarith) _
    positivity

end Work.FTS_StreamBdry.SB6
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB6.clauses2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.Phi_clause2` — the `w`-derivative rate of `Φ`

`Φ w θ = if 0 < w then oddPerS (psiP αG Ψ) w θ else 0` and
`|∂_wΦ w θ| ≤ A (π/2-θ) (1+w)^{-4/αG-1}` on `w ≥ 0`, `0 ≤ θ < π/2`.

Three regimes: the interior `w > 0`, `θ > 0`, where `∂_wΦ = ∂_w(psiP)` splits into the compact
bound `|∂_w psiP| ≤ max K0 M·sin 2θ` (from `D_z psiP` for `w ≥ 1`, and from the near-axis
hypothesis for `w ≤ 1`) and the far-field bound `|∂_w psiP| ≤ Kf sin 2θ (L/w)^{4/αG}/w`; the
axis `θ = 0`, where the whole function in `w` vanishes; and `w = 0`, where it vanishes on
`(-∞,0)` and at `0`, so its derivative at `0` is `0`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP oddPerS)

set_option autoImplicit false

/-- **Clause 2**: `|∂_w Φ w θ| ≤ A₂ (π/2 - θ) (1+w)^{-4/αG-1}`. -/
theorem Phi_clause2 {αG M L Kf K0 : ℝ} (hαG : 0 < αG) (hL : 0 < L) (hM : 0 ≤ M)
    (hKf0 : 0 ≤ Kf) (hK00 : 0 ≤ K0)
    {Ψ : ℝ → ℝ → ℝ} (hPpi : ∀ z, (psiP αG Ψ) z (Real.pi / 2) = 0)
    (hpz : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → z ≤ 1 →
      |Work.Spaces.pz (psiP αG Ψ) z θ| ≤ K0 * Work.Construction.s2 θ)
    (hDz : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ)
    (hfar : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ|
        ≤ Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun w' : ℝ => (if 0 < w' then oddPerS (psiP αG Ψ) w' θ else 0)) w|
        ≤ A * (Real.pi / 2 - θ) * (1 + w) ^ (-(4 / αG) - 1) := by
  have hk0 : (0 : ℝ) ≤ 4 / αG := by positivity
  have hk1 : (0 : ℝ) ≤ 4 / αG + 1 := by positivity
  have hLw : 0 ≤ (1 + L) ^ (4 / αG + 1) := Real.rpow_nonneg (by linarith) _
  have hMm : (0 : ℝ) ≤ max K0 M := le_max_of_le_left hK00
  have hA0 : 0 ≤ max (2 * max K0 M * (1 + L) ^ (4 / αG + 1))
      (2 * Kf * L ^ (4 / αG) * (1 + 1 / L) ^ (4 / αG + 1)) := by
    refine le_max_iff.mpr (Or.inl ?_)
    exact mul_nonneg (mul_nonneg (by norm_num) hMm) hLw
  refine ⟨max (2 * max K0 M * (1 + L) ^ (4 / αG + 1))
    (2 * Kf * L ^ (4 / αG) * (1 + 1 / L) ^ (4 / αG + 1)), hA0, ?_⟩
  intro w θ hw hθ hθ2
  have hwd : 0 ≤ (1 + w) ^ (-(4 / αG) - 1) := Real.rpow_nonneg (by linarith) _
  have hπ : 0 ≤ Real.pi / 2 - θ := by linarith [hθ2, Real.pi_pos]
  by_cases hw0 : 0 < w
  · by_cases hθ0 : 0 < θ
    · rw [Phi_deriv_w hPpi hw0 hθ0 hθ2]
      have hmem : (w, θ) ∈ Work.Construction.Qd :=
        Work.FTS_StreamBdry.mem_Qd.mpr ⟨hw0, hθ0, hθ2⟩
      have hs2nn : 0 ≤ Work.Construction.s2 θ :=
        Work.FTS_StreamBdry.s2_nonneg_of_Iθ (Work.FTS_StreamBdry.Qd_theta_Iθ hmem)
      have hs2le : Work.Construction.s2 θ ≤ 2 * (Real.pi / 2 - θ) :=
        s2_le_two_mul_sub (le_of_lt hθ2)
      by_cases hwL : w ≤ L
      · -- compact: `w ≤ L`
        have hpz' : |Work.Spaces.pz (psiP αG Ψ) w θ| ≤ max K0 M * Work.Construction.s2 θ := by
          by_cases hw1 : w ≤ 1
          · exact (hpz w θ hmem hw1).trans
              (mul_le_mul_of_nonneg_right (le_max_left _ _) hs2nn)
          · have hw1' : 1 ≤ w := le_of_not_ge hw1
            have hD := hDz w θ hmem 1 (by norm_num)
            rw [show Work.Spaces.DzIter 1 (psiP αG Ψ) w θ
                = w * Work.Spaces.pz (psiP αG Ψ) w θ from rfl, abs_mul,
              abs_of_pos hw0] at hD
            have h1 : |Work.Spaces.pz (psiP αG Ψ) w θ| ≤ M * Work.Construction.s2 θ / w :=
              (le_div_iff₀ hw0).mpr (by linarith [hD])
            have h2 : M * Work.Construction.s2 θ / w ≤ M * Work.Construction.s2 θ := by
              rw [div_le_iff₀ hw0]
              calc M * Work.Construction.s2 θ = M * Work.Construction.s2 θ * 1 :=
                    (mul_one _).symm
                _ ≤ M * Work.Construction.s2 θ * w :=
                    mul_le_mul_of_nonneg_left hw1' (mul_nonneg hM hs2nn)
            exact (h1.trans h2).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hs2nn)
        have h3 : (1 : ℝ) ≤ (1 + L) ^ (4 / αG + 1) * (1 + w) ^ (-(4 / αG) - 1) := by
          have h4 : (1 + L) ^ (-(4 / αG + 1)) ≤ (1 + w) ^ (-(4 / αG + 1)) :=
            one_add_rpow_neg_le hL hk1 hw hwL
          have h4' : (1 + L) ^ (-(4 / αG + 1)) ≤ (1 + w) ^ (-(4 / αG) - 1) := by
            rw [show -(4 / αG) - 1 = -(4 / αG + 1) by ring]
            exact h4
          have h5 : (1 + L) ^ (4 / αG + 1) * (1 + L) ^ (-(4 / αG + 1)) = 1 := by
            rw [← Real.rpow_add (by linarith),
              show 4 / αG + 1 + -(4 / αG + 1) = 0 by ring]
            simp
          calc (1 : ℝ) = (1 + L) ^ (4 / αG + 1) * (1 + L) ^ (-(4 / αG + 1)) := h5.symm
            _ ≤ (1 + L) ^ (4 / αG + 1) * (1 + w) ^ (-(4 / αG) - 1) :=
                mul_le_mul_of_nonneg_left h4' hLw
        calc |Work.Spaces.pz (psiP αG Ψ) w θ| ≤ max K0 M * Work.Construction.s2 θ := hpz'
          _ ≤ max K0 M * (2 * (Real.pi / 2 - θ)) :=
              mul_le_mul_of_nonneg_left hs2le (le_max_of_le_left hK00)
          _ = (2 * max K0 M) * (Real.pi / 2 - θ) := by ring
          _ = (2 * max K0 M) * (Real.pi / 2 - θ) * 1 := by ring
          _ ≤ (2 * max K0 M) * (Real.pi / 2 - θ)
                * ((1 + L) ^ (4 / αG + 1) * (1 + w) ^ (-(4 / αG) - 1)) :=
              mul_le_mul_of_nonneg_left h3
                (mul_nonneg (mul_nonneg (by norm_num) hMm) hπ)
          _ = (2 * max K0 M * (1 + L) ^ (4 / αG + 1)) * (Real.pi / 2 - θ)
                * (1 + w) ^ (-(4 / αG) - 1) := by ring
          _ ≤ max (2 * max K0 M * (1 + L) ^ (4 / αG + 1))
                (2 * Kf * L ^ (4 / αG) * (1 + 1 / L) ^ (4 / αG + 1)) * (Real.pi / 2 - θ)
                * (1 + w) ^ (-(4 / αG) - 1) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hπ) hwd
      · -- far field: `L ≤ w`
        have hwL' : L ≤ w := le_of_not_ge hwL
        have hwpos : 0 < w := lt_of_lt_of_le hL hwL'
        have hD := hfar w θ hmem hwL' 1 (by norm_num)
        rw [show Work.Spaces.DzIter 1 (psiP αG Ψ) w θ
            = w * Work.Spaces.pz (psiP αG Ψ) w θ from rfl, abs_mul,
          abs_of_pos hwpos] at hD
        have hpz1 : |Work.Spaces.pz (psiP αG Ψ) w θ|
            ≤ Kf * Work.Construction.s2 θ * (L / w) ^ (4 / αG) / w :=
          (le_div_iff₀ hwpos).mpr (by linarith [hD])
        have hkey : (L / w) ^ (4 / αG) / w
            ≤ L ^ (4 / αG) * (1 + 1 / L) ^ (4 / αG + 1)
              * (1 + w) ^ (-(4 / αG) - 1) := by
          simpa only [show -(4 / αG + 1) = -(4 / αG) - 1 by ring]
            using div_rpow_succ_le (w := w) (L := L) (k := 4 / αG) hL hk0 hwL'
        have hker : 0 ≤ L ^ (4 / αG) * (1 + 1 / L) ^ (4 / αG + 1)
            * (1 + w) ^ (-(4 / αG) - 1) :=
          mul_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt hL) _)
            (Real.rpow_nonneg (by positivity) _)) hwd
        calc |Work.Spaces.pz (psiP αG Ψ) w θ|
            ≤ Kf * Work.Construction.s2 θ * (L / w) ^ (4 / αG) / w := hpz1
          _ = Kf * Work.Construction.s2 θ * ((L / w) ^ (4 / αG) / w) := by ring
          _ ≤ Kf * Work.Construction.s2 θ
                * (L ^ (4 / αG) * (1 + 1 / L) ^ (4 / αG + 1)
                  * (1 + w) ^ (-(4 / αG) - 1)) :=
              mul_le_mul_of_nonneg_left hkey (mul_nonneg hKf0 hs2nn)
          _ ≤ Kf * (2 * (Real.pi / 2 - θ))
                * (L ^ (4 / αG) * (1 + 1 / L) ^ (4 / αG + 1)
                  * (1 + w) ^ (-(4 / αG) - 1)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs2le hKf0) hker
          _ = (2 * Kf * L ^ (4 / αG) * (1 + 1 / L) ^ (4 / αG + 1)) * (Real.pi / 2 - θ)
                * (1 + w) ^ (-(4 / αG) - 1) := by ring
          _ ≤ max (2 * max K0 M * (1 + L) ^ (4 / αG + 1))
                (2 * Kf * L ^ (4 / αG) * (1 + 1 / L) ^ (4 / αG + 1)) * (Real.pi / 2 - θ)
                * (1 + w) ^ (-(4 / αG) - 1) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hπ) hwd
    · -- `θ = 0`: the function of `w` is identically zero
      have hθeq : θ = 0 := le_antisymm (not_lt.mp hθ0) hθ
      rw [hθeq]
      have hfun : (fun w' : ℝ => (if 0 < w' then oddPerS (psiP αG Ψ) w' 0 else 0))
          = fun _ => 0 := by
        funext w'
        by_cases hw' : 0 < w'
        · exact Phi_zero_theta hPpi
        · exact ite_eq_right hw'
      rw [hfun, deriv_const, abs_zero]
      exact mul_nonneg (mul_nonneg hA0 (by linarith [Real.pi_pos])) hwd
  · -- `w ≤ 0`, so `w = 0`
    have hw_eq : w = 0 := le_antisymm (not_lt.mp hw0) hw
    subst hw_eq
    by_cases hd : DifferentiableAt ℝ
      (fun w' : ℝ => (if 0 < w' then oddPerS (psiP αG Ψ) w' θ else 0)) 0
    · have hder : deriv (fun w' : ℝ => (if 0 < w' then oddPerS (psiP αG Ψ) w' θ else 0)) 0
          = 0 :=
        deriv_eq_zero_of_left_eq_zero hd
          (fun y hy => Phi_eq_zero_of_nonpos (P := psiP αG Ψ) (not_lt.mpr (le_of_lt hy)))
          (ite_eq_right (lt_irrefl (0 : ℝ)))
      rw [hder, abs_zero]
      exact mul_nonneg (mul_nonneg hA0 hπ) hwd
    · rw [deriv_zero_of_not_differentiableAt hd, abs_zero]
      exact mul_nonneg (mul_nonneg hA0 hπ) hwd

end Work.FTS_StreamBdry.SB6
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB6.clauses3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.Phi_clause3` — the `θ`-derivative rate of `Φ`

`Φ w θ = if 0 < w then oddPerS (psiP αG Ψ) w θ else 0` and
`|∂_θΦ w θ| ≤ A (1+w)^{-4/αG}` on `w ≥ 0`, `0 ≤ θ < π/2`.

The interior bound `|∂_θ psiP| ≤ Kpth` (compact, `w ≤ L`) or
`∂_θ psiP = V(psiP) + tan θ·psiP` with `|V(psiP)| ≤ Kv (L/w)^{4/αG}` and
`|tan θ·psiP| ≤ 2 Kf (L/w)^{4/αG}` (far).  On the axis `θ = 0` the derivative of the odd
extension is the right difference quotient, controlled by `deriv_theta_zero_le` / `_far`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP oddPerS)

set_option autoImplicit false

/-- The compact weight trick: for `w ≤ L`, `1 ≤ (1+L)^k · (1+w)^{-k}`. -/
lemma one_le_weight {w L k : ℝ} (hL : 0 < L) (hk : 0 ≤ k) (hw0 : 0 ≤ w) (hwL : w ≤ L) :
    (1 : ℝ) ≤ (1 + L) ^ k * (1 + w) ^ (-k) := by
  have hLk : 0 ≤ (1 + L) ^ k := Real.rpow_nonneg (by linarith) _
  have h4 := one_add_rpow_neg_le hL hk hw0 hwL
  have h5 : (1 + L) ^ k * (1 + L) ^ (-k) = 1 := by
    rw [← Real.rpow_add (by linarith), show k + -k = 0 by ring]
    simp
  calc (1 : ℝ) = (1 + L) ^ k * (1 + L) ^ (-k) := h5.symm
    _ ≤ (1 + L) ^ k * (1 + w) ^ (-k) := mul_le_mul_of_nonneg_left h4 hLk

/-- **Clause 3**: `|∂_θ Φ w θ| ≤ A₃ (1+w)^{-4/αG}`. -/
theorem Phi_clause3 {αG M L Kf Kpth Kv : ℝ} (hαG : 0 < αG) (hL : 0 < L) (hM : 0 ≤ M)
    (hKf0 : 0 ≤ Kf) (hKpth0 : 0 ≤ Kpth) (hKv0 : 0 ≤ Kv)
    {Ψ : ℝ → ℝ → ℝ} (hPpi : ∀ z, (psiP αG Ψ) z (Real.pi / 2) = 0)
    (hDz : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ)
    (hfar : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ|
        ≤ Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG))
    (hKpth : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 1,
      |Work.Spaces.pth (Work.Spaces.DzIter j (psiP αG Ψ)) z θ| ≤ Kpth)
    (hVop : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z →
      |Work.Construction.Vop (psiP αG Ψ) z θ| ≤ Kv * (L / z) ^ (4 / αG)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun θ' : ℝ => (if 0 < w then oddPerS (psiP αG Ψ) w θ' else 0)) θ|
        ≤ A * (1 + w) ^ (-(4 / αG)) := by
  have hk0 : (0 : ℝ) ≤ 4 / αG := by positivity
  have hLk : 0 ≤ (1 + L) ^ (4 / αG) := Real.rpow_nonneg (by linarith) _
  have hBk : 0 ≤ max (max Kpth (Kv + 2 * Kf)) (2 * max M Kf) := by
    refine le_max_iff.mpr (Or.inl ?_)
    exact le_max_of_le_left hKpth0
  refine ⟨max (max Kpth (Kv + 2 * Kf)) (2 * max M Kf) * (1 + L) ^ (4 / αG),
    mul_nonneg hBk hLk, ?_⟩
  intro w θ hw hθ hθ2
  have hwk : 0 ≤ (1 + w) ^ (-(4 / αG)) := Real.rpow_nonneg (by linarith) _
  by_cases hw0 : 0 < w
  · by_cases hθ0 : 0 < θ
    · rw [Phi_deriv_theta hPpi hw0 hθ0 hθ2]
      have hmem : (w, θ) ∈ Work.Construction.Qd :=
        Work.FTS_StreamBdry.mem_Qd.mpr ⟨hw0, hθ0, hθ2⟩
      by_cases hwL : w ≤ L
      · -- compact: `w ≤ L`
        have h1 : |Work.Spaces.pth (psiP αG Ψ) w θ| ≤ Kpth := hKpth w θ hmem 0 (by norm_num)
        have h3 := one_le_weight (k := 4 / αG) hL hk0 hw hwL
        calc |Work.Spaces.pth (psiP αG Ψ) w θ| ≤ Kpth := h1
          _ = Kpth * 1 := (mul_one _).symm
          _ ≤ Kpth * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) :=
              mul_le_mul_of_nonneg_left h3 hKpth0
          _ = Kpth * (1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)) := by ring
          _ ≤ max (max Kpth (Kv + 2 * Kf)) (2 * max M Kf) * (1 + L) ^ (4 / αG)
                * (1 + w) ^ (-(4 / αG)) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _)) hLk) hwk
      · -- far field: `L ≤ w`
        have hwL' : L ≤ w := le_of_not_ge hwL
        have hV := hVop w θ hmem hwL'
        have hcos : Real.cos θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Qd hmem)
        have htans : Real.tan θ * Work.Construction.s2 θ = 2 * Real.sin θ ^ 2 :=
          Work.FTS_StreamBdry.tan_mul_s2 hcos
        have htan0 : 0 ≤ Real.tan θ := by
          rw [Real.tan_eq_sin_div_cos]
          refine div_nonneg ?_ (le_of_lt (Work.FTS_StreamBdry.cos_pos_of_Qd hmem))
          exact le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ0])
            (by linarith [hθ2, Real.pi_pos]))
        have htan2 : |Real.tan θ| * Work.Construction.s2 θ ≤ 2 := by
          rw [abs_of_nonneg htan0, htans]
          linarith [Real.sin_sq_le_one θ]
        have hP := hfar w θ hmem hwL' 0 (by norm_num)
        have h1 : |Work.Spaces.pth (psiP αG Ψ) w θ| ≤ (Kv + 2 * Kf) * (L / w) ^ (4 / αG) := by
          have hpth_eq : Work.Spaces.pth (psiP αG Ψ) w θ
              = Work.Construction.Vop (psiP αG Ψ) w θ
                + Real.tan θ * (psiP αG Ψ) w θ := by
            rw [Work.Construction.Vop]
            ring
          rw [hpth_eq]
          have h2 : |Real.tan θ * (psiP αG Ψ) w θ|
              ≤ (|Real.tan θ| * Work.Construction.s2 θ) * (Kf * (L / w) ^ (4 / αG)) := by
            rw [abs_mul]
            calc |Real.tan θ| * |(psiP αG Ψ) w θ|
                ≤ |Real.tan θ| * (Kf * Work.Construction.s2 θ * (L / w) ^ (4 / αG)) :=
                  mul_le_mul_of_nonneg_left hP (abs_nonneg _)
              _ = (|Real.tan θ| * Work.Construction.s2 θ) * (Kf * (L / w) ^ (4 / αG)) := by ring
          have h3 : (|Real.tan θ| * Work.Construction.s2 θ) * (Kf * (L / w) ^ (4 / αG))
              ≤ 2 * (Kf * (L / w) ^ (4 / αG)) :=
            mul_le_mul_of_nonneg_right htan2
              (mul_nonneg hKf0 (Real.rpow_nonneg (by positivity) _))
          have h4 : |Work.Construction.Vop (psiP αG Ψ) w θ| + 2 * (Kf * (L / w) ^ (4 / αG))
              ≤ Kv * (L / w) ^ (4 / αG) + 2 * (Kf * (L / w) ^ (4 / αG)) :=
            add_le_add hV (le_refl _)
          have h5 : Kv * (L / w) ^ (4 / αG) + 2 * (Kf * (L / w) ^ (4 / αG))
              = (Kv + 2 * Kf) * (L / w) ^ (4 / αG) := by ring
          calc |Work.Construction.Vop (psiP αG Ψ) w θ + Real.tan θ * (psiP αG Ψ) w θ|
              ≤ |Work.Construction.Vop (psiP αG Ψ) w θ|
                + |Real.tan θ * (psiP αG Ψ) w θ| := abs_add_le _ _
            _ ≤ |Work.Construction.Vop (psiP αG Ψ) w θ| + 2 * (Kf * (L / w) ^ (4 / αG)) :=
                add_le_add (le_refl _) (h2.trans h3)
            _ ≤ Kv * (L / w) ^ (4 / αG) + 2 * (Kf * (L / w) ^ (4 / αG)) := h4
            _ = (Kv + 2 * Kf) * (L / w) ^ (4 / αG) := h5
        have h2 : (Kv + 2 * Kf) * (L / w) ^ (4 / αG)
            ≤ (Kv + 2 * Kf) * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) :=
          mul_le_mul_of_nonneg_left (div_rpow_le hL hk0 hwL') (by linarith)
        have h3 : (Kv + 2 * Kf) * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)))
            ≤ max (max Kpth (Kv + 2 * Kf)) (2 * max M Kf) * (1 + L) ^ (4 / αG)
              * (1 + w) ^ (-(4 / αG)) := by
          have h4 : Kv + 2 * Kf ≤ max (max Kpth (Kv + 2 * Kf)) (2 * max M Kf) :=
            le_max_of_le_left (le_max_right _ _)
          calc (Kv + 2 * Kf) * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)))
              = (Kv + 2 * Kf) * (1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)) := by ring
            _ ≤ max (max Kpth (Kv + 2 * Kf)) (2 * max M Kf) * (1 + L) ^ (4 / αG)
                  * (1 + w) ^ (-(4 / αG)) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 hLk) hwk
        calc |Work.Spaces.pth (psiP αG Ψ) w θ| ≤ (Kv + 2 * Kf) * (L / w) ^ (4 / αG) := h1
          _ ≤ (Kv + 2 * Kf) * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) := h2
          _ ≤ max (max Kpth (Kv + 2 * Kf)) (2 * max M Kf) * (1 + L) ^ (4 / αG)
                * (1 + w) ^ (-(4 / αG)) := h3
    · -- `θ = 0`: the derivative is the right difference quotient
      have hθeq : θ = 0 := le_antisymm (not_lt.mp hθ0) hθ
      rw [hθeq]
      by_cases hd : DifferentiableAt ℝ
        (fun θ' : ℝ => (if 0 < w then oddPerS (psiP αG Ψ) w θ' else 0)) 0
      · by_cases hwL : w ≤ L
        · have hbd : |deriv (fun θ' : ℝ =>
              (if 0 < w then oddPerS (psiP αG Ψ) w θ' else 0)) 0| ≤ 2 * M :=
            deriv_theta_zero_le hPpi hw0 hM
              (fun t ht0 htπ => hDz w t
                (Work.FTS_StreamBdry.mem_Qd.mpr ⟨hw0, ht0, htπ⟩) 0 (by norm_num)) hd
          have h3 := one_le_weight (k := 4 / αG) hL hk0 hw hwL
          have hB1 : 2 * max M Kf ≤ max (max Kpth (Kv + 2 * Kf)) (2 * max M Kf) :=
            le_max_right _ _
          have hMk0 : 0 ≤ 2 * max M Kf :=
            mul_nonneg (by norm_num) (le_max_of_le_left hM)
          calc |deriv (fun θ' : ℝ =>
                (if 0 < w then oddPerS (psiP αG Ψ) w θ' else 0)) 0| ≤ 2 * M := hbd
            _ ≤ 2 * max M Kf := mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
            _ = 2 * max M Kf * 1 := (mul_one _).symm
            _ ≤ 2 * max M Kf * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) :=
                mul_le_mul_of_nonneg_left h3 hMk0
            _ = 2 * max M Kf * (1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)) := by ring
            _ ≤ max (max Kpth (Kv + 2 * Kf)) (2 * max M Kf) * (1 + L) ^ (4 / αG)
                  * (1 + w) ^ (-(4 / αG)) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB1 hLk) hwk
        · have hwL' : L ≤ w := le_of_not_ge hwL
          have hbd : |deriv (fun θ' : ℝ =>
                (if 0 < w then oddPerS (psiP αG Ψ) w θ' else 0)) 0|
              ≤ 2 * Kf * (L / w) ^ (4 / αG) :=
            deriv_theta_zero_le_far hPpi hL hwL' hKf0
              (fun t ht0 htπ => hfar w t
                (Work.FTS_StreamBdry.mem_Qd.mpr ⟨hw0, ht0, htπ⟩) hwL' 0 (by norm_num)) hd
          have h2 : 2 * Kf * (L / w) ^ (4 / αG)
              ≤ 2 * max M Kf * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) := by
            have h5 : (L / w) ^ (4 / αG)
                ≤ (1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)) := div_rpow_le hL hk0 hwL'
            have h6 : 0 ≤ 2 * Kf := by linarith
            have h7 : 2 * Kf ≤ 2 * max M Kf :=
              mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
            have h8 : 0 ≤ (1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)) :=
              mul_nonneg hLk hwk
            calc 2 * Kf * (L / w) ^ (4 / αG)
                ≤ 2 * Kf * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) :=
                  mul_le_mul_of_nonneg_left h5 h6
              _ ≤ 2 * max M Kf * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) :=
                  mul_le_mul_of_nonneg_right h7 h8
          calc |deriv (fun θ' : ℝ =>
                (if 0 < w then oddPerS (psiP αG Ψ) w θ' else 0)) 0|
              ≤ 2 * Kf * (L / w) ^ (4 / αG) := hbd
            _ ≤ 2 * max M Kf * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) := h2
            _ = 2 * max M Kf * (1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)) := by ring
            _ ≤ max (max Kpth (Kv + 2 * Kf)) (2 * max M Kf) * (1 + L) ^ (4 / αG)
                  * (1 + w) ^ (-(4 / αG)) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hLk) hwk
      · rw [deriv_zero_of_not_differentiableAt hd, abs_zero]
        exact mul_nonneg (mul_nonneg hBk hLk) hwk
  · have hfun : (fun θ' : ℝ => (if 0 < w then oddPerS (psiP αG Ψ) w θ' else 0))
        = fun _ => 0 := by
      funext θ'
      exact ite_eq_right hw0
    rw [hfun, deriv_const, abs_zero]
    exact mul_nonneg (mul_nonneg hBk hLk) hwk

end Work.FTS_StreamBdry.SB6
end
end
