/-
Work.MRMT.Found — **`∂(C h) = S h` for `h ∈ L²(ℂ)` with compact support**:

  `Work.MRMT.IsDzDeriv (Work.MRMT.cauchyTransform h) (Work.MRMT.beurlingL2 ↥(hm.toLp h))`.

Both the Cauchy transform `C` and the Beurling transform `S` (`beurlingL2`, the `L²` Fourier
multiplier with symbol `ξ̄/ξ`) are defined in `Work.MRMT`; the identity is the `L²` avatar of
`C = ∂̄^{-1}` and `S = ∂ C`.

## Route of the proof

* **Smooth case** (`Work.MRMT.Found.isDzDeriv_cauchyTransform_beurlingL2_of_contDiff`): for `u`
  of class `C¹` with compact support, `C u` is again `C¹` and `∂(C u) = C(∂u)`
  (`cauchyTransform_contDiff_one`), the pointwise `∂` of a `C¹` function is its distributional
  `∂` (`Weyl.isDzDeriv_dz`), and `C(∂u) = S u` a.e. (`beurlingL2_eq_cauchyTransform_dz`).

* **Approximation.** For `h ∈ L²` with compact support and every `ε > 0` some mollification `u`
  of `h` by a bump kernel is `C¹`, compactly supported, in `L²`, with `∫ ‖u - h‖² ≤ ε`
  (`Work.MRMT.Found.exists_moll_approx_memLp`).

* **Two `L²`-continuity estimates.** The pairing `g ↦ ∫ z, C g z · ψ z` is continuous in `‖g‖₂`
  for smooth zero-mean compactly supported `ψ`
  (`Work.MRMT.Found.norm_integral_cauchyTransform_sub_pairing_le`), and the pairing
  `g ↦ ∫ z, (S g) z · φ z` is continuous in `‖g‖₂` for continuous compactly supported `φ`
  (`Work.MRMT.Found.norm_integral_beurlingL2_sub_mul_le`).  In the first one the Cauchy
  transform is used to interchange the two integrals
  (`Work.MRMT.Found.integral_cauchyTransform_mul_eq`), whose kernel `1/(ζ - z)` being
  antisymmetric makes `C` *anti*-self-adjoint: `∫ C g · ψ = -∫ g · C ψ`; Cauchy–Schwarz then
  gives the bound with constant `1`.

* **Conclusion.** For each test function `φ` and each `ε > 0` one writes
  `A + B = (A - A_u) + (A_u + B_u) + (B - B_u)`, where `A, B` are the `h`-pairings and
  `A_u, B_u` those of the smooth approximant `u`; the middle term vanishes by the smooth case,
  and the outer two are `≤ √ε · C_φ` by the continuity estimates.  Letting `ε → 0` gives
  `A + B = 0`, i.e. `∫ C h · ∂φ = -∫ S h · φ`.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.beurlingL2_eq_cauchyTransform_dz
import Submission.Work.MRMT.Found.cauchyTransform_contDiff_one
import Submission.Work.MRMT.Found.cauchyTransform_memLp_ball
import Submission.Work.MRMT.Found.memLp_cauchyTransform_dz
import Submission.Work.MRMT.Cauchy.Defs
import Submission.Work.MRMT.Cauchy.integrable_prod_mul_div_sub
import Submission.Work.MRMT.Cauchy.locallyIntegrable_cauchyTransform
import Submission.Work.MRMT.Beltrami.CauchyDzAux
import Submission.Work.MRMT.Weyl.isDzDeriv_moll_gen
import Submission.Work.MRMT.Sobolev.mollification_pairing_tendsto
import Submission.Work.MRMT.QC.existsBumpIntegralMollSubLe
import Submission.Work.MRMT.Found.CauchyPairingAux
import Submission.Work.MRMT.Found.isDzDeriv_cauchyTransform_beurlingL2_of_contDiff
import Submission.Work.MRMT.Found.exists_moll_approx_memLp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal Convolution


/-- The pairing `g ↦ ∫ z, (S g) z * φ z` against a continuous compactly supported `φ` is
continuous for the `L²`-norm on `g`.  This is Cauchy–Schwarz, together with the fact that the
Beurling transform is an isometry of `L²(ℂ)`. -/
theorem norm_integral_beurlingL2_sub_mul_le {φ : ℂ → ℂ} (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) {g₁ g₂ : ℂ → ℂ}
    (h₁ : MeasureTheory.MemLp g₁ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (h₂ : MeasureTheory.MemLp g₂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) :
    ‖(∫ z, ((Work.MRMT.beurlingL2 (h₁.toLp g₁) :
            MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z * φ z)
      - ∫ z, ((Work.MRMT.beurlingL2 (h₂.toLp g₂) :
            MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z * φ z‖
      ≤ ‖h₁.toLp g₁ - h₂.toLp g₂‖ * (∫ z, ‖φ z‖ ^ 2) ^ (1 / 2 : ℝ) := by
  have hφmem : MeasureTheory.MemLp φ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
    hφc.memLp_of_hasCompactSupport hφs
  have hS₁ : MeasureTheory.MemLp
      ((Work.MRMT.beurlingL2 (h₁.toLp g₁) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) 2
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) := MeasureTheory.Lp.memLp _
  have hS₂ : MeasureTheory.MemLp
      ((Work.MRMT.beurlingL2 (h₂.toLp g₂) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) 2
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) := MeasureTheory.Lp.memLp _
  have hI₁ : Integrable (fun z => ((Work.MRMT.beurlingL2 (h₁.toLp g₁) :
      MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z * φ z)
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) := hS₁.integrable_mul hφmem
  have hI₂ : Integrable (fun z => ((Work.MRMT.beurlingL2 (h₂.toLp g₂) :
      MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z * φ z)
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) := hS₂.integrable_mul hφmem
  have hdiff : MeasureTheory.MemLp
      ((fun z => ((Work.MRMT.beurlingL2 (h₁.toLp g₁) :
          MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z)
        - (fun z => ((Work.MRMT.beurlingL2 (h₂.toLp g₂) :
          MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z)) 2
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) := hS₁.sub hS₂
  have hsplit : (∫ z, ((Work.MRMT.beurlingL2 (h₁.toLp g₁) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z * φ z)
      - ∫ z, ((Work.MRMT.beurlingL2 (h₂.toLp g₂) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z * φ z
      = ∫ z, (((Work.MRMT.beurlingL2 (h₁.toLp g₁) :
          MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z
        - ((Work.MRMT.beurlingL2 (h₂.toLp g₂) :
          MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z) * φ z := by
    rw [← integral_sub hI₁ hI₂]
    exact integral_congr_ae (Eventually.of_forall fun z => by ring)
  rw [hsplit]
  have hcs : ‖∫ z, (((Work.MRMT.beurlingL2 (h₁.toLp g₁) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z
        - ((Work.MRMT.beurlingL2 (h₂.toLp g₂) :
          MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z) * φ z‖
      ≤ ∫ z, ‖((Work.MRMT.beurlingL2 (h₁.toLp g₁) :
          MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z
        - ((Work.MRMT.beurlingL2 (h₂.toLp g₂) :
          MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z‖
          * ‖φ z‖ := by
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    exact integral_congr_ae (Eventually.of_forall fun z => norm_mul _ _)
  refine hcs.trans ?_
  have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (f := (fun z => ((Work.MRMT.beurlingL2 (h₁.toLp g₁) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z)
      - (fun z => ((Work.MRMT.beurlingL2 (h₂.toLp g₂) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z))
    (g := φ)
    (show (2 : ℝ).HolderConjugate 2 by rw [Real.holderConjugate_iff]; norm_num)
    (by simpa using hdiff) (by simpa using hφmem)
  refine hholder.trans ?_
  have hkey : (∫ z, ‖((Work.MRMT.beurlingL2 (h₁.toLp g₁) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z
      - ((Work.MRMT.beurlingL2 (h₂.toLp g₂) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z‖ ^ 2)
      = ‖h₁.toLp g₁ - h₂.toLp g₂‖ ^ 2 := by
    have htp : hdiff.toLp (fun z => ((Work.MRMT.beurlingL2 (h₁.toLp g₁) :
          MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z
        - ((Work.MRMT.beurlingL2 (h₂.toLp g₂) :
          MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z)
        = Work.MRMT.beurlingL2 (h₁.toLp g₁) - Work.MRMT.beurlingL2 (h₂.toLp g₂) := by
      refine MeasureTheory.Lp.ext ?_
      exact (MeasureTheory.MemLp.coeFn_toLp hdiff).trans
        (MeasureTheory.Lp.coeFn_sub _ _).symm
    rw [Work.MRMT.Beltrami.integral_norm_sq_eq_toLp_norm_sq
      (fun z => ((Work.MRMT.beurlingL2 (h₁.toLp g₁) :
          MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z
        - ((Work.MRMT.beurlingL2 (h₂.toLp g₂) :
          MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z) hdiff,
      htp, ← map_sub, Work.MRMT.norm_beurlingL2]
  simp only [Pi.sub_apply, Real.rpow_two]
  rw [hkey, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]

theorem isDzDeriv_cauchyTransform_eq_beurlingL2 {h : ℂ → ℂ}
    (hm : MeasureTheory.MemLp h 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hs : HasCompactSupport h) :
    Work.MRMT.IsDzDeriv (Work.MRMT.cauchyTransform h)
      (((Work.MRMT.beurlingL2 (hm.toLp h)) : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) := by
  have hgint : Integrable h (MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
    Work.MRMT.Sobolev.integrable_of_memLp_two_hasCompactSupport hm hs
  have hCloc : LocallyIntegrable (Work.MRMT.cauchyTransform h) (MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
    Work.MRMT.Cauchy.locallyIntegrable_cauchyTransform h hgint
  have hSloc : LocallyIntegrable
      (((Work.MRMT.beurlingL2 (hm.toLp h)) : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ)
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
    (MeasureTheory.Lp.memLp _).locallyIntegrable (by norm_num)
  refine ⟨hCloc, hSloc, fun φ => ?_⟩
  have hψc : ContDiff ℝ 1 (fun z => Work.MRMT.dz (φ : ℂ → ℂ) z) :=
    (Work.MRMT.Found.contDiff_dz_testFunction φ).of_le (by simp)
  have hψs : HasCompactSupport (fun z => Work.MRMT.dz (φ : ℂ → ℂ) z) :=
    Work.MRMT.Found.hasCompactSupport_dz φ.hasCompactSupport
  have hψ0 : ∫ z, Work.MRMT.dz (φ : ℂ → ℂ) z = 0 :=
    Work.MRMT.Beltrami.integral_dz_eq_zero_of_contDiff (φ : ℂ → ℂ) (n := 1) (by norm_num)
      (φ.contDiff.of_le (by norm_num)) φ.hasCompactSupport
  have hψcont : Continuous (fun z => Work.MRMT.dz (φ : ℂ → ℂ) z) := hψc.continuous
  have hI1 : Integrable (fun z => Work.MRMT.cauchyTransform h z * Work.MRMT.dz (φ : ℂ → ℂ) z)
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
    refine (hCloc.integrable_smul_left_of_hasCompactSupport hψcont hψs).congr ?_
    filter_upwards with z
    rw [smul_eq_mul, mul_comm]
  have hI2 : Integrable (fun z => ((Work.MRMT.beurlingL2 (hm.toLp h)) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) z * (φ : ℂ → ℂ) z)
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
    have h := hSloc.integrable_smul_left_of_hasCompactSupport φ.continuous φ.hasCompactSupport
    refine h.congr ?_
    filter_upwards with z
    rw [smul_eq_mul, mul_comm]
  refine ⟨hI1, hI2, ?_⟩
  set A : ℂ := ∫ z, Work.MRMT.cauchyTransform h z * Work.MRMT.dz (φ : ℂ → ℂ) z with hAdef
  set B : ℂ := ∫ z, ((Work.MRMT.beurlingL2 (hm.toLp h)) :
      MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) z * (φ : ℂ → ℂ) z with hBdef
  have hAB : A + B = 0 := by
    refine norm_eq_zero.mp (le_antisymm ?_ (norm_nonneg _))
    set C : ℝ := (∫ z, ‖Work.MRMT.cauchyTransform (fun z => Work.MRMT.dz (φ : ℂ → ℂ) z) z‖ ^ 2) ^ (1 / 2 : ℝ)
      + (∫ z, ‖(φ : ℂ → ℂ) z‖ ^ 2) ^ (1 / 2 : ℝ) with hCdef
    have key : ∀ ε : ℝ, 0 < ε → ‖A + B‖ ≤ Real.sqrt ε * C := by
      intro ε hε
      obtain ⟨N, hcd, hcs, hmem, hle⟩ := Work.MRMT.Found.exists_moll_approx_memLp hm hs hε
      set u : ℂ → ℂ := Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump N).normed
        (MeasureTheory.volume : MeasureTheory.Measure ℂ)) h with hudef
      have hsm := Work.MRMT.Found.isDzDeriv_cauchyTransform_beurlingL2_of_contDiff hcd hcs hmem
      have hsm' : (∫ z, Work.MRMT.cauchyTransform u z * Work.MRMT.dz (φ : ℂ → ℂ) z)
          = -(∫ z, ((Work.MRMT.beurlingL2 (hmem.toLp u)) :
              MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) z * (φ : ℂ → ℂ) z) :=
        (hsm.2.2 φ).2.2
      have hE := Work.MRMT.Found.norm_integral_cauchyTransform_sub_pairing_le (g₁ := h) (g₂ := u) hψc hψs hψ0 hm hmem hs hcs
      have hS := Work.MRMT.Found.norm_integral_beurlingL2_sub_mul_le (g₁ := h) (g₂ := u)
        φ.continuous φ.hasCompactSupport hm hmem
      have hnorm2 : ‖hmem.toLp u - hm.toLp h‖ ^ 2 = ∫ z, ‖u z - h z‖ ^ 2 := by
        rw [← MeasureTheory.MemLp.toLp_sub hmem hm,
          ← Work.MRMT.Beltrami.integral_norm_sq_eq_toLp_norm_sq (u - h) (hmem.sub hm)]
        simp only [Pi.sub_apply]
      have hsq : ‖hm.toLp h - hmem.toLp u‖ = Real.sqrt (∫ z, ‖u z - h z‖ ^ 2) := by
        have hthis := Real.sqrt_sq (norm_nonneg (hmem.toLp u - hm.toLp h))
        rw [hnorm2] at hthis
        rw [norm_sub_rev]
        exact hthis.symm
      have hdiff_le : ‖hm.toLp h - hmem.toLp u‖ ≤ Real.sqrt ε := by
        rw [hsq]
        exact Real.sqrt_le_sqrt hle
      have hAuBu : (∫ z, Work.MRMT.cauchyTransform u z * Work.MRMT.dz (φ : ℂ → ℂ) z)
          + (∫ z, ((Work.MRMT.beurlingL2 (hmem.toLp u)) :
              MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) z * (φ : ℂ → ℂ) z) = 0 := by
        rw [hsm']; ring
      have hab : A + B = (A - ∫ z, Work.MRMT.cauchyTransform u z * Work.MRMT.dz (φ : ℂ → ℂ) z)
          + (B - ∫ z, ((Work.MRMT.beurlingL2 (hmem.toLp u)) :
              MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) z * (φ : ℂ → ℂ) z) := by
        linear_combination hAuBu
      calc ‖A + B‖
          = ‖(A - ∫ z, Work.MRMT.cauchyTransform u z * Work.MRMT.dz (φ : ℂ → ℂ) z)
              + (B - ∫ z, ((Work.MRMT.beurlingL2 (hmem.toLp u)) :
                  MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) z * (φ : ℂ → ℂ) z)‖ := by
            rw [hab]
        _ ≤ ‖A - ∫ z, Work.MRMT.cauchyTransform u z * Work.MRMT.dz (φ : ℂ → ℂ) z‖
              + ‖B - ∫ z, ((Work.MRMT.beurlingL2 (hmem.toLp u)) :
                  MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) z * (φ : ℂ → ℂ) z‖ :=
            norm_add_le _ _
        _ ≤ ‖hm.toLp h - hmem.toLp u‖ * (∫ z, ‖Work.MRMT.cauchyTransform (fun z => Work.MRMT.dz (φ : ℂ → ℂ) z) z‖ ^ 2) ^ (1 / 2 : ℝ)
              + ‖hm.toLp h - hmem.toLp u‖ * (∫ z, ‖(φ : ℂ → ℂ) z‖ ^ 2) ^ (1 / 2 : ℝ) :=
            add_le_add hE hS
        _ = ‖hm.toLp h - hmem.toLp u‖ * C := by rw [hCdef]; ring
        _ ≤ Real.sqrt ε * C := by
            refine mul_le_mul_of_nonneg_right hdiff_le ?_
            rw [hCdef]; positivity
    have htend : Tendsto (fun ε : ℝ => Real.sqrt ε * C) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hcont : Continuous fun ε : ℝ => Real.sqrt ε * C := Real.continuous_sqrt.mul continuous_const
      have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using h
    have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), ‖A + B‖ ≤ Real.sqrt ε * C :=
      (eventually_nhdsWithin_iff).mpr (Filter.Eventually.of_forall fun ε hε => key ε hε)
    exact ge_of_tendsto htend hev
  have hgoal : A = -B := eq_neg_of_add_eq_zero_left hAB
  rw [hAdef, hBdef] at hgoal
  exact hgoal


end Work.MRMT.Found
