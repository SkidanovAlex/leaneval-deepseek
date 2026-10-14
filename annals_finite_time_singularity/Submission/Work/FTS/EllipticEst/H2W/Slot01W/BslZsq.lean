import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.MinImports
import Submission.Work.Elliptic.WtoHAux
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.Zsq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.EllipticEst.AeS1.DzSliceIdentities =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-! ## The two slice identities

The first identity is the `m = 1`, `i = 0` instance of
`Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open` (i.e. `z²∂_z²` commutes with
`D_z = z∂_z`).  The second is the commutation of `∂_z` with the iterated `∂_θ`, which is
Clairaut's theorem iterated, together with the trivial commutation of `∂_θ` with the
`z`-multiplication. -/

/-- `SmoothOpen` is closed under the iterated `∂_θ`. -/
theorem SmoothOpen_pthIter_local {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (i : ℕ) : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i F) := by
  induction i with
  | zero => simpa using hF
  | succ i ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- Multiplication by the first variable commutes with `∂_θ` (the factor is constant in the
differentiated variable). -/
theorem pth_mul_fst (g : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => z * g z θ) = fun z θ => z * Work.Spaces.pth g z θ := by
  funext z θ
  simpa only [Work.Spaces.pth] using
    deriv_const_mul_field (v := fun θ' => g z θ') (x := θ) z

/-- Multiplication by the first variable commutes with the iterates of `∂_θ`. -/
theorem pthIter_mul_fst (g : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.pthIter n (fun z θ => z * g z θ)
      = fun z θ => z * Work.Spaces.pthIter n g z θ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]
      exact pth_mul_fst (Work.Spaces.pthIter n g)

/-- **`∂_z` commutes with the iterates of `∂_θ`** on the open quadrant, for data which are
`C^∞` there.  Iterated Clairaut: the induction step moves `∂_z` across the outermost
`∂_θ`, and the inner derivative is identified by locality of `∂_θ` on the open quadrant
(`Work.Spaces.pth_congr_of_isOpen`). -/
theorem pz_pthIter_comm_open (f : ℝ → ℝ → ℝ) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (n : ℕ) : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pz (Work.Spaces.pthIter n f) z θ
        = Work.Spaces.pthIter n (Work.Spaces.pz f) z θ := by
  induction n with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h1, h2⟩
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pthIter n f)) (z, θ) :=
        ((SmoothOpen_pthIter_local hf n).contDiffAt
          (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).of_le (by norm_num)
      rw [Work.Spaces.pthIter_succ, Work.Spaces.pz_pth_comm hcd, Work.Spaces.pthIter_succ]
      exact Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
        (fun p hp => by
          obtain ⟨hz', h1', h2'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
          exact ih p.1 p.2 hz' h1' h2') hmem

theorem Dz_slice_identities (Ψ : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
    ∧ (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ
        = Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) := by
  have hf : ∀ n : ℕ, ContDiffOn ℝ (↑n) (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mp hsm
  constructor
  · -- `z²∂_z²` commutes with `D_z = z∂_z`: the instance `m = 1`, `i = 0` of
    -- `zsq_pzIter2_mixed_open`.
    intro z θ hz h1 h2
    have h := Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open Ψ hf 1 0 hz ⟨h1, h2⟩
    simp only [Work.Spaces.mixed_zero_right] at h
    exact h.symm
  · -- `∂_z` commutes with `∂_θ²`, and `z` is constant in `θ`.
    intro z θ hz h1 h2
    have hA := pz_pthIter_comm_open Ψ hsm 2 z θ hz h1 h2
    have hB := congrFun (congrFun (pthIter_mul_fst (Work.Spaces.pz Ψ) 2) z) θ
    show z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (fun z θ => z * Work.Spaces.pz Ψ z θ) z θ
    rw [hA]
    exact hB.symm

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceMomentFinite =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2

/-- `Lzero1` applied to the `θ`-slice is the two-variable `Lzero` of a function with the same
slice (both depend only on the `θ`-slice). -/
private theorem Lzero1_slice_eq (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.EllipticEst.Lzero1 (fun t : ℝ => Ψ z t) θ = Work.Elliptic.Lzero Ψ z θ := by
  simp only [Work.FTS.EllipticEst.Lzero1, Work.Elliptic.Lzero, Work.Spaces.pthIter_succ,
    Work.Spaces.pthIter_zero, Work.Spaces.pth]

/-- Dividing an integrand by a nonzero constant preserves integrability. -/
private theorem integrableOn_of_const_mul {c : ℝ} (hc : c ≠ 0) {f : ℝ → ℝ}
    (h : MeasureTheory.IntegrableOn (fun θ : ℝ => c * f θ) Iθ) :
    MeasureTheory.IntegrableOn f Iθ := by
  have h' : MeasureTheory.IntegrableOn (fun θ : ℝ => c⁻¹ * (c * f θ)) Iθ :=
    h.const_mul c⁻¹
  refine h'.congr (Filter.Eventually.of_forall (fun θ => ?_))
  field_simp

theorem AeSliceMomentFinite (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.pz u z θ * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.pzIter 2 u z θ * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun t : ℝ => u z t) θ
          * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  have hα : 0 < α := h.hα
  -- the `C^∞`-on-the-open-quadrant structure of `u`, `G` and `z²∂_z²u`
  have hU : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hG : Work.FTS.EllipticEst.SmoothOpen G :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hU)
      (fun z θ hz hθ hθ2 => h.eq z hz θ hθ hθ2)
  have hA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) :=
    Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq hU
  -- ## the pairings of `G` and of `z²∂_z²u` with the angular profile
  have hGsg : MeasureTheory.IntegrableOn (fun θ : ℝ => G z θ * sg θ) Iθ :=
    (Work.FTS.EllipticEst.remov.ws_absMoment
      (Work.FTS.EllipticEst.remov.ws_aesm_slice hG hz)
      (Work.FTS.EllipticEst.remov.ws_slot_slice hG h.memG 0 (Nat.zero_le 0) hz)).1
  have hAsg : MeasureTheory.IntegrableOn (fun θ : ℝ => (z ^ 2 * Work.Spaces.pzIter 2 u z θ) * sg θ)
      Iθ :=
    (Work.FTS.EllipticEst.remov.ws_absMoment
      (Work.FTS.EllipticEst.remov.ws_aesm_slice hA hz)
      (Work.FTS.EllipticEst.remov.ws_slot_slice hA h.memRad2 0 (Nat.zero_le 0) hz)).1
  -- ## the third conjunct
  have h3 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun t : ℝ => u z t) θ * sg θ) Iθ := by
    obtain ⟨C, _hCpos, hC⟩ :=
      Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB h.smooth h.memAng2 hz
    exact Work.FTS.EllipticEst.Endpt.Lzero1_slice_mul_integrable h.smooth h.memAng2 hz hC
  -- ## the second conjunct (divide the pairing of `z²∂_z²u` by `z²`)
  have h2 : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.pzIter 2 u z θ * sg θ) Iθ := by
    have h' : MeasureTheory.IntegrableOn
        (fun θ : ℝ => z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)) Iθ := by
      refine hAsg.congr (Filter.Eventually.of_forall (fun θ => ?_))
      ring
    exact integrableOn_of_const_mul (pow_ne_zero 2 (ne_of_gt hz)) h'
  -- ## the first conjunct, from the equation
  have hLsg : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.Lzero u z θ * sg θ) Iθ := by
    refine h3.congr (Filter.Eventually.of_forall (fun θ => ?_))
    show Work.FTS.EllipticEst.Lzero1 (fun t : ℝ => u z t) θ * sg θ
      = Work.Elliptic.Lzero u z θ * sg θ
    rw [Lzero1_slice_eq u z θ]
  have hRHS : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Elliptic.Lzero u z θ - α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
        - G z θ) * sg θ) Iθ := by
    have ha : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ) * sg θ) Iθ := by
      refine (hAsg.const_mul (α ^ 2)).congr (Filter.Eventually.of_forall (fun θ => ?_))
      ring
    refine ((hLsg.sub ha).sub hGsg).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [Pi.sub_apply]
    ring
  have hae : (fun θ : ℝ => (α * (5 + α) * z)⁻¹ * ((Work.Elliptic.Lzero u z θ
        - α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ - G z θ) * sg θ))
      =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ : ℝ => Work.Spaces.pz u z θ * sg θ) := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    have heq := h.eq z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply] at heq
    have hden : α * (5 + α) * z ≠ 0 := ne_of_gt (by positivity)
    have hkey : Work.Elliptic.Lzero u z θ - α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
        - G z θ = α * (5 + α) * z * Work.Spaces.pz u z θ := by linarith
    show (α * (5 + α) * z)⁻¹ * ((Work.Elliptic.Lzero u z θ
        - α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ - G z θ) * sg θ)
      = Work.Spaces.pz u z θ * sg θ
    rw [hkey]
    field_simp
  exact ⟨(hRHS.const_mul ((α * (5 + α) * z)⁻¹)).congr hae, h2, h3⟩

end Work.FTS.EllipticEst.H2W.AeProof
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Slot01W.BslZsq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- DECLARATION THINNING: this module was byte-identical (modulo imports) to
-- `Submission.Work.FTS.EllipticEst.H2W.bslOp_zsq_pzIter2`, so importing both was a duplicate-declaration error.
-- The names stay available to every consumer through the import above.
end
