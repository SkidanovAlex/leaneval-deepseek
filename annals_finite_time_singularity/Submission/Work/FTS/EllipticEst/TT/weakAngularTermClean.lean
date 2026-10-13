/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TT.weakAngularTermClean`: the angular first-order term `∂_θ(tan θ · Ψ)` in the weak class

This is the *clean* (dependency-light) form of `TT.weakAngularTerm`: the conclusion

  `HkMem α 0 (∂_θ(tan θ · Ψ))`  and
  `√(HkSq α 0 (∂_θ(tan θ · Ψ))) ≤ C (√(HkSq α 0 F) + α √(HkSq α 0 (z ∂_zΨ)))`

is obtained from the two hypothesis packages `hfirst`, `hsecond` using only the modules of the
`Honest` chapter (`Honest.step3Defs`, `Honest.step3PsiBar`, `Honest.step3Angle`) together with
the local `𝓗^k`-bookkeeping of `Work.FTS.LocData`, i.e. without the almost-everywhere machinery
(`H2W.Ae`, `AngAWeak`) used by `TT.weakAngularTerm`.

## Route

With `u = uOf Ψ = ∂_θ(tan θ · Ψ)` and `P = POf Ψ = sin θ · ∂_θ(Ψ/cos θ)`:

* on the open quadrant `u = Ψ + P` (`Honest.pth_tan_mul_eq_open`);
* hence `√(HkSq α 0 u) ≤ √2 (√(HkSq α 0 Ψ) + √(HkSq α 0 P))`
  (`Honest.sqrt_HkSq_uOf_le`), and `HkMem α 0 u` follows from the pointwise majorant
  `HkIntegrand α 0 u ≤ 2 HkIntegrand α 0 Ψ + 2 HkIntegrand α 0 P`
  (`Work.FTS.LocData.HkMem_of_majorant`);
* `√(HkSq 0 0 P) ≤ C₃ (√(HkSq 0 0 Ψ) + √(HkSq 0 0 (∂_θθΨ)))` is Elgindi's `I₄`-positivity
  (`Honest.step3PsiBar`, Step 2 of `prop:H2`), and the level-`0` integrand is `α`-free
  (`HkIntegrand α 0 = HkIntegrand 0 0`), so the bound transfers to `α`;
* `HkMem α 0 P` comes from the equation, rewritten on the open quadrant as
  `P = α²(z²∂_zzΨ) + α(5+α)(z∂_zΨ) + ∂_θθΨ + F + 5Ψ`, each summand being honest by the
  hypothesis packages (`wac_POf_eq`, `wac_hkMem_POf`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Honest.step3Defs
import Submission.Work.FTS.EllipticEst.Honest.SliceMain
import Submission.Work.FTS.EllipticEst.Honest.slicePsiMemAlt
import Submission.Work.FTS.EllipticEst.Honest.psi_boundary_vanish
import Submission.Work.FTS.EllipticEst.Honest.slice_ident_honest
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.step3Angle
import Submission.Work.FTS.LocData.HkMem_of_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

open Work.FTS.EllipticEst.Honest

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The level-`0` integrand is independent of `α` -/

/-- At level `0` the `𝓗`-integrand is the square of the weighted profile `g·w/sin(2θ)^{η/2}`
(`Honest.HkIntegrand_zero_eq`), which does not involve `α`. -/
theorem wac_HkIntegrand_zero_alpha (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ = Work.Spaces.HkIntegrand 0 0 g z θ := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]

/-- `HkSq α 0` is independent of `α`. -/
theorem wac_HkSq_zero_alpha (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g = Work.Spaces.HkSq 0 0 g := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ =>
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ =>
      wac_HkIntegrand_zero_alpha α g z θ

/-- `HkMem α 0` is independent of `α`. -/
theorem wac_HkMem_zero_alpha {α : ℝ} {g : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkMem α 0 g) : Work.Spaces.HkMem 0 0 g := by
  have hpt : ∀ z θ, Work.Spaces.HkIntegrand 0 0 g z θ = Work.Spaces.HkIntegrand α 0 g z θ :=
    fun z θ => (wac_HkIntegrand_zero_alpha α g z θ).symm
  constructor
  · intro z hz
    exact (h.1 z hz).congr_fun (fun θ _ => hpt z θ) measurableSet_Icc
  · exact h.2.congr_fun (fun z _ => MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ _ => hpt z θ)) measurableSet_Ici

/-! ## Smoothness of `uOf Ψ` on the open quadrant -/

/-- `uOf Ψ = ∂_θ(tan θ · Ψ)` is `C^∞` on the open quadrant whenever `Ψ` is. -/
theorem wac_smoothOpen_uOf {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.Honest.uOf Ψ) := by
  have hΨs : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have htan : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl (f := fun _ : ℝ => Real.tan) (g := Ψ)
      Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl hΨs
  exact htan.pth

/-! ## The rearranged equation on the open quadrant -/

/-- **`POf Ψ` solved from the equation.**  On the open quadrant, `(PolarBSL)` gives
`P = α²·(z²∂_zzΨ) + α(5+α)·(z∂_zΨ) + ∂_θθΨ + F + 5Ψ` (the `Hon`-free form of
`Honest.POf_eq_of_hon`, in the weak class `EllWeakPos`). -/
theorem wac_POf_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : EllWeakPos α 0 F Ψ) {z θ : ℝ}
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.FTS.EllipticEst.Honest.POf Ψ z θ
      = α ^ 2 * Work.FTS.EllipticEst.Honest.AOf Ψ z θ
        + α * (5 + α) * Work.FTS.EllipticEst.Honest.GOf Ψ z θ
        + Work.Spaces.pthIter 2 Ψ z θ + F z θ + 5 * Ψ z θ := by
  have hsol : α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      = -F z θ - α * (5 + α) * (z * Work.Spaces.pz Ψ z θ)
        - Work.Spaces.pthIter 2 Ψ z θ
        + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - 6 * Ψ z θ := by
    have hb := EllWeakPos.eq h z hz θ hθ0 hθ1
    rw [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero] at hb
    linarith [hb]
  have hid := Work.FTS.EllipticEst.Honest.pth_tan_mul_eq_open
    (EllWeakPos.smooth h) hz hθ0 hθ1
  simp only [Work.FTS.EllipticEst.Honest.POf, Work.FTS.EllipticEst.Honest.uOf,
    Work.FTS.EllipticEst.Honest.AOf, Work.FTS.EllipticEst.Honest.GOf] at hid ⊢
  linarith [hsol, hid]

/-! ## The five-term integrand domination for `POf Ψ` -/

/-- **The pointwise five-term domination** of the level-`0` integrand of `POf Ψ`; it holds on
the whole domain (at `z = 0` and at `θ ∈ {0, π/2}` the left-hand side vanishes and the majorant
is nonnegative).  `Hon`-free version of `Honest.HkIntegrand_POf_le`. -/
theorem wac_HkIntegrand_POf_le (α : ℝ) {F Ψ : ℝ → ℝ → ℝ}
    (h : EllWeakPos α 0 F Ψ) (z θ : ℝ)
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Honest.POf Ψ) z θ
      ≤ 5 * (Work.Spaces.HkIntegrand α 0
            (fun z θ => α ^ 2 * Work.FTS.EllipticEst.Honest.AOf Ψ z θ) z θ
        + Work.Spaces.HkIntegrand α 0
            (fun z θ => α * (5 + α) * Work.FTS.EllipticEst.Honest.GOf Ψ z θ) z θ
        + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ
        + Work.Spaces.HkIntegrand α 0 (fun z θ => 5 * Ψ z θ) z θ) := by
  have hnn1 := Work.Spaces.HkIntegrand_nonneg α 0
    (fun z θ => α ^ 2 * Work.FTS.EllipticEst.Honest.AOf Ψ z θ) z θ
  have hnn2 := Work.Spaces.HkIntegrand_nonneg α 0
    (fun z θ => α * (5 + α) * Work.FTS.EllipticEst.Honest.GOf Ψ z θ) z θ
  have hnn3 := Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.pthIter 2 Ψ) z θ
  have hnn4 := Work.Spaces.HkIntegrand_nonneg α 0 F z θ
  have hnn5 := Work.Spaces.HkIntegrand_nonneg α 0 (fun z θ => 5 * Ψ z θ) z θ
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_boundary α _ (Or.inl hz0.symm)]
    nlinarith [hnn1, hnn2, hnn3, hnn4, hnn5]
  · rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).1 with hθ0 | hθ0pos
    · rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_boundary α _ (Or.inr (Or.inl hθ0.symm))]
      nlinarith [hnn1, hnn2, hnn3, hnn4, hnn5]
    · rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).2 with hθπ | hθlt
      · rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_boundary α _ (Or.inr (Or.inr hθπ))]
        nlinarith [hnn1, hnn2, hnn3, hnn4, hnn5]
      · rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
          Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
          Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
          Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
          Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
          Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
          wac_POf_eq h hzpos hθ0pos hθlt]
        set W : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        have hkey := Work.FTS.EllipticEst.Honest.sum_five_sq_le
          (α ^ 2 * Work.FTS.EllipticEst.Honest.AOf Ψ z θ * W)
          (α * (5 + α) * Work.FTS.EllipticEst.Honest.GOf Ψ z θ * W)
          (Work.Spaces.pthIter 2 Ψ z θ * W) (F z θ * W) (5 * Ψ z θ * W)
        have hsplit : (α ^ 2 * Work.FTS.EllipticEst.Honest.AOf Ψ z θ
              + α * (5 + α) * Work.FTS.EllipticEst.Honest.GOf Ψ z θ
              + Work.Spaces.pthIter 2 Ψ z θ + F z θ + 5 * Ψ z θ) * W
            = α ^ 2 * Work.FTS.EllipticEst.Honest.AOf Ψ z θ * W
              + α * (5 + α) * Work.FTS.EllipticEst.Honest.GOf Ψ z θ * W
              + Work.Spaces.pthIter 2 Ψ z θ * W + F z θ * W + 5 * Ψ z θ * W := by ring
        rw [hsplit]
        linarith [hkey]

/-! ## Honesty of `POf Ψ` in the weak class -/

/-- **`HkMem α 0 (POf Ψ)`** from the weak class and the two honesty fields of Step 1.  This is
the `Hon`-free version of `Honest.step3PMem` (equivalently of `Honest.hkMem_POf`): the only
fields of `Hon` used there are `eq`, `sm`, `memF`, `memA`, `memB`, all of which `EllWeakPos`
supplies. -/
theorem wac_hkMem_POf {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : EllWeakPos α 0 F Ψ)
    (hΨ : Work.Spaces.HkMem α 0 Ψ)
    (hG : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.Honest.GOf Ψ)) :
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.Honest.POf Ψ) := by
  have hsm := EllWeakPos.smooth h
  have hmp : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.Honest.POf Ψ) :=
    Work.FTS.EllipticEst.Honest.smoothOpen_POf hsm
  have hm1 : Work.Spaces.HkMem α 0
      (fun z θ => α ^ 2 * Work.FTS.EllipticEst.Honest.AOf Ψ z θ) :=
    Work.FTS.EllipticEst.Honest.HkMem_const_mul' (α ^ 2)
      (f := Work.FTS.EllipticEst.Honest.AOf Ψ) (EllWeakPos.memA h)
  have hm2 : Work.Spaces.HkMem α 0
      (fun z θ => α * (5 + α) * Work.FTS.EllipticEst.Honest.GOf Ψ z θ) :=
    Work.FTS.EllipticEst.Honest.HkMem_const_mul' (α * (5 + α))
      (f := Work.FTS.EllipticEst.Honest.GOf Ψ) hG
  have hm3 : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ) := EllWeakPos.memB h
  have hm4 : Work.Spaces.HkMem α 0 F := EllWeakPos.memF h
  have hm5 : Work.Spaces.HkMem α 0 (fun z θ => 5 * Ψ z θ) :=
    Work.FTS.EllipticEst.Honest.HkMem_const_mul' 5 (f := Ψ) hΨ
  set g1 : ℝ → ℝ → ℝ := fun z θ =>
    Work.Spaces.HkIntegrand α 0
      (fun z θ => α ^ 2 * Work.FTS.EllipticEst.Honest.AOf Ψ z θ) z θ with hg1
  set g2 : ℝ → ℝ → ℝ := fun z θ =>
    Work.Spaces.HkIntegrand α 0
      (fun z θ => α * (5 + α) * Work.FTS.EllipticEst.Honest.GOf Ψ z θ) z θ with hg2
  set g3 : ℝ → ℝ → ℝ := fun z θ =>
    Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ with hg3
  set g4 : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.HkIntegrand α 0 F z θ with hg4
  set g5 : ℝ → ℝ → ℝ := fun z θ =>
    Work.Spaces.HkIntegrand α 0 (fun z θ => 5 * Ψ z θ) z θ with hg5
  set M : ℝ → ℝ → ℝ := fun z θ => 5 * (g1 z θ + g2 z θ + g3 z θ + g4 z θ + g5 z θ) with hM
  refine Work.FTS.LocData.HkMem_of_majorant α 0
    (f := Work.FTS.EllipticEst.Honest.POf Ψ) (M := M)
    (hmp.continuousOn_HkIntegrand α 0) ?_ ?_ ?_
  · -- integrability of the angular slices of the majorant
    intro z hz
    have hb1 : MeasureTheory.IntegrableOn (fun θ => g1 z θ) Work.Spaces.Iθ := hm1.1 z hz
    have hb2 : MeasureTheory.IntegrableOn (fun θ => g2 z θ) Work.Spaces.Iθ := hm2.1 z hz
    have hb3 : MeasureTheory.IntegrableOn (fun θ => g3 z θ) Work.Spaces.Iθ := hm3.1 z hz
    have hb4 : MeasureTheory.IntegrableOn (fun θ => g4 z θ) Work.Spaces.Iθ := hm4.1 z hz
    have hb5 : MeasureTheory.IntegrableOn (fun θ => g5 z θ) Work.Spaces.Iθ := hm5.1 z hz
    have h12 := hb1.add hb2
    have h123 := h12.add hb3
    have h1234 := h123.add hb4
    rw [hM]
    exact (h1234.add hb5).const_mul 5
  · -- integrability of the `z`-integral of the majorant
    set I1 : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, g1 z θ with hI1
    set I2 : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, g2 z θ with hI2
    set I3 : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, g3 z θ with hI3
    set I4 : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, g4 z θ with hI4
    set I5 : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, g5 z θ with hI5
    have hint1 : MeasureTheory.IntegrableOn I1 Work.Spaces.Iz := hm1.2
    have hint2 : MeasureTheory.IntegrableOn I2 Work.Spaces.Iz := hm2.2
    have hint3 : MeasureTheory.IntegrableOn I3 Work.Spaces.Iz := hm3.2
    have hint4 : MeasureTheory.IntegrableOn I4 Work.Spaces.Iz := hm4.2
    have hint5 : MeasureTheory.IntegrableOn I5 Work.Spaces.Iz := hm5.2
    have hSum : MeasureTheory.IntegrableOn
        (fun z => 5 * (I1 z + I2 z + I3 z + I4 z + I5 z)) Work.Spaces.Iz :=
      ((((hint1.add hint2).add hint3).add hint4).add hint5).const_mul 5
    refine MeasureTheory.IntegrableOn.congr_fun hSum (fun z hz => ?_) measurableSet_Ici
    have hb1 : MeasureTheory.IntegrableOn (fun θ => g1 z θ) Work.Spaces.Iθ := hm1.1 z hz
    have hb2 : MeasureTheory.IntegrableOn (fun θ => g2 z θ) Work.Spaces.Iθ := hm2.1 z hz
    have hb3 : MeasureTheory.IntegrableOn (fun θ => g3 z θ) Work.Spaces.Iθ := hm3.1 z hz
    have hb4 : MeasureTheory.IntegrableOn (fun θ => g4 z θ) Work.Spaces.Iθ := hm4.1 z hz
    have hb5 : MeasureTheory.IntegrableOn (fun θ => g5 z θ) Work.Spaces.Iθ := hm5.1 z hz
    have h12 := hb1.add hb2
    have h123 := h12.add hb3
    have h1234 := h123.add hb4
    have s5 : (∫ θ in Work.Spaces.Iθ, ((g1 z θ + g2 z θ + g3 z θ + g4 z θ) + g5 z θ))
        = (∫ θ in Work.Spaces.Iθ, (g1 z θ + g2 z θ + g3 z θ + g4 z θ))
          + (∫ θ in Work.Spaces.Iθ, g5 z θ) :=
      MeasureTheory.integral_add h1234 hb5
    have s4 : (∫ θ in Work.Spaces.Iθ, (g1 z θ + g2 z θ + g3 z θ + g4 z θ))
        = (∫ θ in Work.Spaces.Iθ, (g1 z θ + g2 z θ + g3 z θ))
          + (∫ θ in Work.Spaces.Iθ, g4 z θ) :=
      MeasureTheory.integral_add h123 hb4
    have s3 : (∫ θ in Work.Spaces.Iθ, (g1 z θ + g2 z θ + g3 z θ))
        = (∫ θ in Work.Spaces.Iθ, (g1 z θ + g2 z θ)) + (∫ θ in Work.Spaces.Iθ, g3 z θ) :=
      MeasureTheory.integral_add h12 hb3
    have s2 : (∫ θ in Work.Spaces.Iθ, (g1 z θ + g2 z θ))
        = (∫ θ in Work.Spaces.Iθ, g1 z θ) + (∫ θ in Work.Spaces.Iθ, g2 z θ) :=
      MeasureTheory.integral_add hb1 hb2
    show 5 * (I1 z + I2 z + I3 z + I4 z + I5 z) = ∫ θ in Work.Spaces.Iθ, M z θ
    rw [hM]
    simp only [MeasureTheory.integral_const_mul]
    congr 1
    simp only [hI1, hI2, hI3, hI4, hI5]
    rw [s5, s4, s3, s2]
  · -- the pointwise domination
    intro z hz θ hθ
    have hle := wac_HkIntegrand_POf_le α h z θ hz hθ
    rw [hM]
    simp only [hg1, hg2, hg3, hg4, hg5] at hle ⊢
    exact hle

/-! ## Honesty of `uOf Ψ` from the honesty of `Ψ` and of `POf Ψ` -/

/-- The pointwise majorant of the level-`0` integrand of `uOf Ψ` by the two integrands of `Ψ`
and of `POf Ψ` (on the whole domain: the identity `u = Ψ + P` holds wherever the weight does
not vanish, and both sides vanish where it does). -/
theorem wac_HkIntegrand_uOf_le {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Honest.uOf Ψ) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α 0 Ψ z θ
        + 2 * Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Honest.POf Ψ) z θ := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_uOf_eq hsm hz hθ,
    Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
  set W : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
  have hsplit : (Ψ z θ + Work.FTS.EllipticEst.Honest.POf Ψ z θ) * W
      = Ψ z θ * W + Work.FTS.EllipticEst.Honest.POf Ψ z θ * W := by ring
  rw [hsplit]
  nlinarith [sq_nonneg (Ψ z θ * W - Work.FTS.EllipticEst.Honest.POf Ψ z θ * W)]

/-- **`HkMem α 0 (uOf Ψ)`** from the honesty of `Ψ` and of `POf Ψ`. -/
theorem wac_hkMem_uOf {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hΨ : Work.Spaces.HkMem α 0 Ψ)
    (hP : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.Honest.POf Ψ)) :
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.Honest.uOf Ψ) := by
  have huS : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.Honest.uOf Ψ) :=
    wac_smoothOpen_uOf hsm
  set M : ℝ → ℝ → ℝ := fun z θ => 2 * Work.Spaces.HkIntegrand α 0 Ψ z θ
    + 2 * Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Honest.POf Ψ) z θ with hM
  refine Work.FTS.LocData.HkMem_of_majorant α 0
    (f := Work.FTS.EllipticEst.Honest.uOf Ψ) (M := M)
    (huS.continuousOn_HkIntegrand α 0) ?_ ?_ ?_
  · intro z hz
    rw [hM]
    exact ((hΨ.1 z hz).const_mul 2).add ((hP.1 z hz).const_mul 2)
  · rw [hM]
    refine MeasureTheory.IntegrableOn.congr_fun
      ((hΨ.2.const_mul 2).add (hP.2.const_mul 2)) (fun z hz => ?_) measurableSet_Ici
    simp only [Pi.add_apply]
    try rw [MeasureTheory.integral_add ((hΨ.1 z hz).const_mul 2) ((hP.1 z hz).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  · intro z hz θ hθ
    rw [hM]
    exact wac_HkIntegrand_uOf_le hsm z θ hz hθ

/-! ## The `I₄`/`Ψ̄`-bound of Step 2 (`Honest.step3PsiBar`), reproduced with a clean cone

`Honest.step3PsiBar` is the `I₄`-bound of Step 2 of `prop:H2`, but its proof goes through
`Honest.slice_psi_mem`, whose import `TanTheta.slice_hypotheses` no longer compiles.  The
alternative `Honest.slice_psi_mem_alt` (in `Honest.slicePsiMemAlt`) proves the same
statement with a clean import cone, so the (short) proof of `step3PsiBar` is reproduced
here verbatim with `slice_psi_mem` replaced by `slice_psi_mem_alt`.
-/

local notation "sg" => Work.FTS.EllipticEst.AngSecond.sig

/-- `√(a+b) ≤ √a + √b` for `a, b ≥ 0`. -/
theorem wac_sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- **The `z`-assembly.**  If the slicewise estimate
`∫ sin²θ (∂_θ(Ψ/cos θ))² σ ≤ ∫ (∂_θθΨ)² σ + 2 ∫ Ψ² σ` holds at every `z > 0`, then the
honest `HkSq`-bound holds with constant `2`. -/
theorem wac_bar_of_slice_le (Ψ : ℝ → ℝ → ℝ)
    (hmemΨ : Work.Spaces.HkMem 0 0 Ψ)
    (hmemB : Work.Spaces.HkMem 0 0 (Work.Spaces.pthIter 2 Ψ))
    (hmemG : Work.Spaces.HkMem 0 0 (fun z θ => Real.sin θ
      * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ))
    (hsl : ∀ z : ℝ, 0 < z →
      (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin θ) ^ 2
          * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sg θ)
        ≤ (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sg θ)
          + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)) :
    Real.sqrt (Work.Spaces.HkSq 0 0 (fun z θ => Real.sin θ
        * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ))
      ≤ 2 * (Real.sqrt (Work.Spaces.HkSq 0 0 Ψ)
        + Real.sqrt (Work.Spaces.HkSq 0 0 (Work.Spaces.pthIter 2 Ψ))) := by
  set G : ℝ → ℝ → ℝ := fun z θ => Real.sin θ
    * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ with hG
  set B : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ with hB
  have hmemG' : Work.Spaces.HkMem 0 0 G := hmemG
  have hmemB' : Work.Spaces.HkMem 0 0 B := hmemB
  -- the pointwise (in `z`) inequality, weighted by `w²`
  have hpt : ∀ z ∈ Work.Spaces.Iz,
      (Work.Spaces.w z) ^ 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ)
        ≤ (Work.Spaces.w z) ^ 2 * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
            + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)) := by
    intro z hz
    have hz' : (0 : ℝ) ≤ z := hz
    rcases eq_or_lt_of_le hz' with h | h
    · subst h
      have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
      simp [hw0]
    · have h1 : (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ)
          ≤ (∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
            + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ) := by
        have hG2 : ∀ θ : ℝ, (G z θ) ^ 2 * sg θ = (Real.sin θ) ^ 2
            * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sg θ := by
          intro θ; rw [hG]; ring
        have hB2 : ∀ θ : ℝ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sg θ
            = (B z θ) ^ 2 * sg θ := by
          intro θ; rw [hB]
        calc (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ)
            = (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin θ) ^ 2
                * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sg θ) :=
              MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hG2 θ)
          _ ≤ (∫ θ in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sg θ)
                + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ) := hsl z h
          _ = (∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
                + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ) := by
              rw [show (∫ θ in Set.Ioo 0 (Real.pi / 2),
                    (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sg θ)
                  = ∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ from
                MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hB2 θ)]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  -- integrability of the three `z`-integrands
  have hintG : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ)) Work.Spaces.Iz := by
    refine hmemG'.2.congr_fun (fun z hz => ?_) measurableSet_Ici
    exact hkIntegrand_zero_integral_eq hmemG' hz
  have hintB : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)) Work.Spaces.Iz := by
    refine hmemB'.2.congr_fun (fun z hz => ?_) measurableSet_Ici
    exact hkIntegrand_zero_integral_eq hmemB' hz
  have hintP : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)) Work.Spaces.Iz := by
    refine hmemΨ.2.congr_fun (fun z hz => ?_) measurableSet_Ici
    exact hkIntegrand_zero_integral_eq hmemΨ hz
  have hintR : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
        + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ))) Work.Spaces.Iz := by
    refine (hintB.add (hintP.const_mul 2)).congr_fun (fun z _ => ?_) measurableSet_Ici
    simp only [Pi.add_apply]
    ring
  have hmono : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ))
      ≤ (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
          + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ))) :=
    MeasureTheory.setIntegral_mono_on hintG hintR measurableSet_Ici hpt
  have eL : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ))
      = Work.Spaces.HkSq 0 0 G := (hkSq_zero_eq_sliceW hmemG').symm
  have eR : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
      * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
        + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)))
      = Work.Spaces.HkSq 0 0 B + 2 * Work.Spaces.HkSq 0 0 Ψ := by
    have hsplit : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
          + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)))
        = (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ))
          + 2 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)) := by
      rw [show (fun z => (Work.Spaces.w z) ^ 2
            * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
              + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)))
          = (fun z => (Work.Spaces.w z) ^ 2
              * (∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
            + 2 * ((Work.Spaces.w z) ^ 2
              * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ))) from by
        funext z; ring]
      rw [MeasureTheory.integral_add hintB (hintP.const_mul 2),
        MeasureTheory.integral_const_mul]
    rw [hsplit, hkSq_zero_eq_sliceW hmemB', hkSq_zero_eq_sliceW hmemΨ]
  have hmain : Work.Spaces.HkSq 0 0 G ≤ Work.Spaces.HkSq 0 0 B + 2 * Work.Spaces.HkSq 0 0 Ψ := by
    rw [← eL, ← eR]
    exact hmono
  have hBnn : 0 ≤ Work.Spaces.HkSq 0 0 B := HkSq_zero_nonneg 0 B
  have hPnn : 0 ≤ Work.Spaces.HkSq 0 0 Ψ := HkSq_zero_nonneg 0 Ψ
  have h2 : Real.sqrt 2 ≤ 2 := by
    have h := Real.sqrt_two_lt_three_halves
    linarith
  have h3 := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg (Work.Spaces.HkSq 0 0 Ψ))
  calc Real.sqrt (Work.Spaces.HkSq 0 0 G)
      ≤ Real.sqrt (Work.Spaces.HkSq 0 0 B + 2 * Work.Spaces.HkSq 0 0 Ψ) :=
        Real.sqrt_le_sqrt hmain
    _ ≤ Real.sqrt (Work.Spaces.HkSq 0 0 B) + Real.sqrt (2 * Work.Spaces.HkSq 0 0 Ψ) :=
        wac_sqrt_add_le_sqrt_add_sqrt hBnn (by positivity)
    _ = Real.sqrt (Work.Spaces.HkSq 0 0 B)
          + Real.sqrt 2 * Real.sqrt (Work.Spaces.HkSq 0 0 Ψ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * (Real.sqrt (Work.Spaces.HkSq 0 0 Ψ) + Real.sqrt (Work.Spaces.HkSq 0 0 B)) := by
        linarith [Real.sqrt_nonneg (Work.Spaces.HkSq 0 0 B)]

/-- **The `I₄`/Ψ̄-bound of Step 2 of `prop:H2`.**  Under the honest slice hypotheses, the
`σ`-weighted `L²`-norm of `sin θ · ∂_θ(Ψ/cos θ)` is controlled by the norms of `Ψ` and of
`∂_θθΨ` (the positivity `I_{4,2}` of Elgindi, Annals 194 (2021), tex 890--905).

Route hint: with `ψ = Ψ/cos θ`, `s = sin(2θ)`, `σ = s^{-η}`, the two integrations by parts of
`Work.FTS.EllipticEst.TanTheta.slice_ident` (`TanTheta/slice_ident.lean`, proved; it needs `u`
of class `C²` on a neighbourhood of `[0,π/2]` with `u(π/2) = 0`) give the slicewise identity
`∫ ((1-η)/2·cos 2θ + 2 sin²θ)(ψ')² σ = -∫ sinθ ψ' Ψ'' σ + ((1-η)/2)∫ cos 2θ ψ² σ`.
Its coefficient is `(1-η)/2 + (1+η)sin²θ ≥ (1+η)sin²θ`, so Cauchy--Schwarz in `θ` and Young in
the two slice quantities `y = (∫ sin²θ ψ'² σ)^{1/2}` and `x = (∫(Ψ'')² σ)^{1/2}` give
`y² ≤ C (y·x + ∫ |cos 2θ| ψ² σ)`; multiplying by `w z ^ 2` and integrating in `z` gives the
statement once `∫|cos 2θ|ψ²σ` is controlled (in the strong class this is `I4_psi_bounds`/
`hardy`-type; here it must come from `HkMem (∂_θθΨ)` and `HkMem Ψ`, e.g. via a weighted Agmon
inequality on the slices — note `∫cos2θ ψ² σ` is very negative near `π/2`, not bounded by
`4∫Ψ²σ`).

The honest class (no `SmoothNbhd`) is what makes this non-trivial: the boundary terms of the
two integrations by parts and the integrability of `sinθ cosθ ψ ψ' σ`, `sinθ cosθ ψ' ψ'' σ`
must be recovered from the three `HkMem` hypotheses (a `θ`-truncation `Ψ·χ_ε` argument in
which `slice_ident` applies verbatim, or weighted one-dimensional Hardy/Agmon inequalities on
the slices).  The hypothesis `HkMem (sinθ · ψ')` is not needed for the *truth* of the estimate
but it removes the degenerate case in which a slice of `sinθ ψ'` fails to be integrable, and
is available to the caller. -/
theorem wac_step3PsiBar : ∃ C : ℝ, 0 < C ∧ ∀ (Ψ : ℝ → ℝ → ℝ),
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
    (∀ z, Ψ z 0 = 0) → (∀ z, Ψ z (Real.pi / 2) = 0) →
    Work.Spaces.HkMem 0 0 Ψ →
    Work.Spaces.HkMem 0 0 (Work.Spaces.pthIter 2 Ψ) →
    Work.Spaces.HkMem 0 0
      (fun z θ => Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) →
    Real.sqrt (Work.Spaces.HkSq 0 0
        (fun z θ => Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ))
      ≤ C * (Real.sqrt (Work.Spaces.HkSq 0 0 Ψ)
        + Real.sqrt (Work.Spaces.HkSq 0 0 (Work.Spaces.pthIter 2 Ψ))) := by
  refine ⟨2, by norm_num, ?_⟩
  intro Ψ hsm h0 h1 hmemΨ hmemB hmemG
  refine wac_bar_of_slice_le Ψ hmemΨ hmemB hmemG ?_
  intro z hz
  -- the slice hypotheses
  have hu : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_slice_of_hsm hsm hz 2
  have hB : IntegrableOn (fun θ => (Ψ z θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (integrableOn_sq_mul_sig_of_hkMem hmemΨ hz).mono_set Set.Ioo_subset_Icc_self
  have hX : IntegrableOn (fun θ => (deriv (deriv (fun θ' => Ψ z θ')) θ) ^ 2 * sg θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine ((integrableOn_sq_mul_sig_of_hkMem hmemB hz).mono_set
      Set.Ioo_subset_Icc_self).congr_fun (fun θ _ => ?_) measurableSet_Ioo
    show Work.Spaces.pthIter 2 Ψ z θ ^ 2 * sg θ
      = deriv (deriv (fun θ' => Ψ z θ')) θ ^ 2 * sg θ
    rw [pthIter_two_apply]
  have hY : IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)) := by
    refine ((integrableOn_sq_mul_sig_of_hkMem hmemG hz).mono_set
      Set.Ioo_subset_Icc_self).congr_fun (fun θ _ => ?_) measurableSet_Ioo
    show (Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sg θ
      = (Real.sin θ) ^ 2 * (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2 * sg θ
    rw [pth_div_apply]
    ring
  obtain ⟨hA, hA'⟩ := slice_psi_mem_alt (fun θ => Ψ z θ) hu (h0 z) (h1 z) hB hX hY
  obtain ⟨hv1, hv2, hv3, hv4⟩ :=
    psi_boundary_vanish (fun θ => Ψ z θ) hu (h0 z) (h1 z) hB hX hY hA hA'
  have hident := slice_ident_honest (fun θ => Ψ z θ) hu (h0 z) (h1 z) hB hX hY hA hA'
    hv1 hv2 hv3 hv4
  have hpth : ∀ θ : ℝ, Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
      = deriv (fun θ' => Ψ z θ' / Real.cos θ') θ := fun θ => pth_div_apply Ψ z θ
  have hpth2 : ∀ θ : ℝ, Work.Spaces.pthIter 2 Ψ z θ
      = deriv (deriv (fun θ' => Ψ z θ')) θ := fun θ => pthIter_two_apply Ψ z θ
  simpa only [hpth, hpth2] using
    slice_sq_le_of_ident (fun θ => Ψ z θ) hu hA hA' hB hX hY hident

/-! ## The target -/

theorem weakAngularTermClean (C₁ C_B : ℝ) (hC₁ : 0 < C₁) (hC_B : 0 < C_B)
    (hfirst : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
      Work.Spaces.HkMem α 0 Ψ ∧
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) ∧
      Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
      Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
        + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))
        + Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
        ≤ C₁ * Real.sqrt (Work.Spaces.HkSq α 0 F))
    (hsecond : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
      Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
        ≤ C_B * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ)))) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
      Work.Spaces.HkMem α 0
          (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ)) ∧
      Real.sqrt (Work.Spaces.HkSq α 0
          (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ)))
        ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))) := by
  obtain ⟨C₃, hC₃pos, hC₃⟩ := wac_step3PsiBar
  refine ⟨Real.sqrt 2 * (C₁ + C₃ * (C₁ + 2 * C_B)) + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  obtain ⟨hΨmem, hGmem, _hCmem, hnorm⟩ := hfirst α F Ψ hα hα4 h
  have hBmem := hsecond α F Ψ hα hα4 h
  have hsm := EllWeakPos.smooth h
  have hPmem : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.Honest.POf Ψ) :=
    wac_hkMem_POf h hΨmem hGmem
  have hUmem : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.Honest.uOf Ψ) :=
    wac_hkMem_uOf hsm hΨmem hPmem
  refine ⟨hUmem, ?_⟩
  -- the `I₄`/`Ψ̄`-bound of Step 2 of `prop:H2`, in its `0`-indexed form
  have hI40 : Real.sqrt (Work.Spaces.HkSq 0 0
        (fun z θ => Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ))
      ≤ C₃ * (Real.sqrt (Work.Spaces.HkSq 0 0 Ψ)
        + Real.sqrt (Work.Spaces.HkSq 0 0 (Work.Spaces.pthIter 2 Ψ))) :=
    hC₃ Ψ hsm (EllWeakPos.zero h) (EllWeakPos.pi_half h)
      (wac_HkMem_zero_alpha hΨmem) (wac_HkMem_zero_alpha (EllWeakPos.memB h))
      (wac_HkMem_zero_alpha hPmem)
  have hI4 : Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Honest.POf Ψ))
      ≤ C₃ * (Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
        + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))) := by
    have h2 := hI40
    have e : Work.Spaces.HkSq 0 0
          (fun z θ => Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ)
        = Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Honest.POf Ψ) :=
      (wac_HkSq_zero_alpha α (Work.FTS.EllipticEst.Honest.POf Ψ)).symm
    rw [e, ← wac_HkSq_zero_alpha α Ψ,
      ← wac_HkSq_zero_alpha α (Work.Spaces.pthIter 2 Ψ)] at h2
    exact h2
  -- the two hypothesis packages, through the triangle inequality
  have hN1 : Real.sqrt (Work.Spaces.HkSq α 0 Ψ) ≤ C₁ * Real.sqrt (Work.Spaces.HkSq α 0 F) := by
    have h1 : 0 ≤ α * Real.sqrt (Work.Spaces.HkSq α 0
        (fun z θ => z * Work.Spaces.pz Ψ z θ)) :=
      mul_nonneg hα.le (Real.sqrt_nonneg _)
    have h2 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ)) :=
      Real.sqrt_nonneg _
    linarith [hnorm, h1, h2]
  have hF0 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 F) := Real.sqrt_nonneg _
  have hG0 : 0 ≤ α * Real.sqrt (Work.Spaces.HkSq α 0
      (fun z θ => z * Work.Spaces.pz Ψ z θ)) :=
    mul_nonneg hα.le (Real.sqrt_nonneg _)
  have htr := Work.FTS.EllipticEst.Honest.sqrt_HkSq_uOf_le (α := α) (Ψ := Ψ)
    hsm hΨmem hPmem
  -- the sum of the two norms
  have hsum : Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
        + Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Honest.POf Ψ))
      ≤ (C₁ + C₃ * (C₁ + C_B)) * (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))) := by
    have h2 : Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Honest.POf Ψ))
        ≤ C₃ * (C₁ * Real.sqrt (Work.Spaces.HkSq α 0 F)
            + C_B * (Real.sqrt (Work.Spaces.HkSq α 0 F)
              + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ)))) := by
      refine hI4.trans (mul_le_mul_of_nonneg_left ?_ hC₃pos.le)
      linarith [hN1, hBmem]
    nlinarith [hN1, h2, hF0, hG0, hC₁, hC_B, hC₃pos,
      mul_nonneg hC_B.le hG0, mul_nonneg hC₁.le hG0]
  refine htr.trans ?_
  have hstep : Real.sqrt 2 * (Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
        + Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Honest.POf Ψ)))
      ≤ Real.sqrt 2 * ((C₁ + C₃ * (C₁ + C_B)) * (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ)))) :=
    mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg 2)
  refine hstep.trans ?_
  have hR : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 F)
      + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ)) := by
    linarith [hF0, hG0]
  have hmid : Real.sqrt 2 * ((C₁ + C₃ * (C₁ + C_B)) * (Real.sqrt (Work.Spaces.HkSq α 0 F)
        + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))))
      ≤ Real.sqrt 2 * ((C₁ + C₃ * (C₁ + 2 * C_B)) * (Real.sqrt (Work.Spaces.HkSq α 0 F)
        + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ)))) := by
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
    nlinarith [hF0, hG0, hC₁, hC_B, hC₃pos,
      mul_nonneg (mul_nonneg hC₃pos.le hC_B.le) hG0,
      mul_nonneg (mul_nonneg hC_B.le hC₃pos.le) hF0]
  refine hmid.trans ?_
  nlinarith [hF0, hG0, hR, hC₁, hC_B, hC₃pos, Real.sqrt_nonneg 2,
    mul_nonneg (Real.sqrt_nonneg 2) hR]

end Work.FTS.EllipticEst.TT
