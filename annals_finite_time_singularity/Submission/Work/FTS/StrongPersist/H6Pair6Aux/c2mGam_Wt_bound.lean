import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Pinning.integrableOn_sq_rpow_of_HkMem
import Submission.Work.FTS_EllLimOK.wt_bddAbove_of_compact
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.ClassC.HkMem_seven_slots_of_plain_family =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## 1. The operator algebra on the open quadrant -/


/-- The iterates of `∂_θ` compose. -/
theorem seven_pthIter_add (m n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter (m + n) f = Work.Spaces.pthIter m (Work.Spaces.pthIter n f) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add, Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]

/-- The iterates of `D_z` compose. -/
theorem seven_DzIter_add (j b : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter (j + b) f = Work.Spaces.DzIter j (Work.Spaces.DzIter b f) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Nat.succ_add]
      show Work.Spaces.Dz (Work.Spaces.DzIter (j + b) f)
        = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.DzIter b f))
      rw [ih]

/-- **Clairaut for `∂_θ` and the `D_z`-iterates**: on the open quadrant the plain angular
derivative commutes with `D_z^b` for data which are `C^∞` there. -/
theorem seven_pth_DzIter_eqOn_Q0 {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (b : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (Work.Spaces.DzIter b f) z θ
        = Work.Spaces.DzIter b (Work.Spaces.pth f) z θ := by
  induction b with
  | zero => intro z θ _ _ _; rfl
  | succ b ih =>
      intro z θ hz hθ hπ
      have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hπ⟩
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter b f)) (z, θ) :=
        ((hf.DzIter b).forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
      have h1 : Work.Spaces.pth (Work.Spaces.DzIter (b + 1) f) z θ
          = Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter b f)) z θ := by
        show Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter b f)) z θ = _
        exact Work.Blocks.Half.pth_Dz_apply_of hcd
      rw [h1]
      have h2 : Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter b f)) z θ
          = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.pth f)) z θ :=
        Work.Blocks.Half.Dz_congrOn (g := Work.Spaces.pth (Work.Spaces.DzIter b f))
          (g' := Work.Spaces.DzIter b (Work.Spaces.pth f))
          Work.FTS.EllipticEst.isOpen_Q0
          (fun p hp' => ih p.1 p.2 hp'.1 hp'.2.1 hp'.2.2) hp
      rw [h2]
      rfl

/-- **Clairaut for the whole `∂_θ`-iterates and `D_z^b`**: `∂_θ^r` commutes with `D_z^b` on
the open quadrant. -/
theorem seven_pthIter_DzIter_eqOn_Q0 {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (r b : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pthIter r (Work.Spaces.DzIter b f) z θ
        = Work.Spaces.DzIter b (Work.Spaces.pthIter r f) z θ := by
  induction r with
  | zero => intro z θ _ _ _; rfl
  | succ r ih =>
      intro z θ hz hθ hπ
      have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hπ⟩
      have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ Work.FTS.EllipticEst.Q0 :=
        (Continuous.prodMk_right z).continuousAt.eventually
          (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
      have hslice : (fun θ' => Work.Spaces.pthIter r (Work.Spaces.DzIter b f) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DzIter b (Work.Spaces.pthIter r f) z θ') := by
        filter_upwards [hnb] with θ' hθ'
        exact ih z θ' hz hθ'.2.1 hθ'.2.2
      have h1 : Work.Spaces.pthIter (r + 1) (Work.Spaces.DzIter b f) z θ
          = Work.Spaces.pth (Work.Spaces.DzIter b (Work.Spaces.pthIter r f)) z θ := by
        show Work.Spaces.pth (Work.Spaces.pthIter r (Work.Spaces.DzIter b f)) z θ = _
        exact hslice.deriv_eq
      rw [h1]
      exact seven_pth_DzIter_eqOn_Q0 (SmoothOpen_pthIter_classC hf r) b z θ hz hθ hπ

/-- **Clairaut for `∂_z` and the `∂_θ`-iterates**: `∂_z ∂_θ^r = ∂_θ^r ∂_z` on the open
quadrant. -/
theorem seven_pz_pthIter_eqOn_Q0 {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (r : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pz (Work.Spaces.pthIter r f) z θ
        = Work.Spaces.pthIter r (Work.Spaces.pz f) z θ := by
  induction r with
  | zero => intro z θ _ _ _; rfl
  | succ r ih =>
      intro z θ hz hθ hπ
      have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hπ⟩
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pthIter r f)) (z, θ) :=
        (((SmoothOpen_pthIter_classC hf r).forall 2)).contDiffAt
          (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
      have h1 : Work.Spaces.pz (Work.Spaces.pthIter (r + 1) f) z θ
          = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pthIter r f)) z θ := by
        show Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pthIter r f)) z θ = _
        exact Work.Spaces.pz_pth_comm hcd
      rw [h1]
      have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ Work.FTS.EllipticEst.Q0 :=
        (Continuous.prodMk_right z).continuousAt.eventually
          (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
      have hslice : (fun θ' => Work.Spaces.pz (Work.Spaces.pthIter r f) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pthIter r (Work.Spaces.pz f) z θ') := by
        filter_upwards [hnb] with θ' hθ'
        exact ih z θ' hz hθ'.2.1 hθ'.2.2
      have h2 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pthIter r f)) z θ
          = Work.Spaces.pth (Work.Spaces.pthIter r (Work.Spaces.pz f)) z θ := hslice.deriv_eq
      rw [h2]
      rfl

/-- **`∂_θ` commutes with `z²∂_z²`** on the open quadrant. -/
theorem seven_pzIter_two_pthIter_eqOn_Q0 {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (r : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pzIter 2 (Work.Spaces.pthIter r f) z θ
        = Work.Spaces.pthIter r (Work.Spaces.pzIter 2 f) z θ := by
  intro z θ hz hθ hπ
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hπ⟩
  have h1 : Work.Spaces.pzIter 2 (Work.Spaces.pthIter r f) z θ
      = Work.Spaces.pz (Work.Spaces.pthIter r (Work.Spaces.pz f)) z θ := by
    show Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.pthIter r f)) z θ = _
    exact Work.Blocks.Half.pz_congrOn (g := Work.Spaces.pz (Work.Spaces.pthIter r f))
      (g' := Work.Spaces.pthIter r (Work.Spaces.pz f)) Work.FTS.EllipticEst.isOpen_Q0
      (fun p hp' => seven_pz_pthIter_eqOn_Q0 hf r p.1 p.2 hp'.1 hp'.2.1 hp'.2.2) hp
  rw [h1]
  have h2 : Work.Spaces.pz (Work.Spaces.pthIter r (Work.Spaces.pz f)) z θ
      = Work.Spaces.pthIter r (Work.Spaces.pz (Work.Spaces.pz f)) z θ :=
    seven_pz_pthIter_eqOn_Q0 hf.pz r z θ hz hθ hπ
  rw [h2]
  rfl

/-- `∂_θ^r` commutes with multiplication by the `z`-only factor `z²` (identically, no
smoothness needed). -/
theorem seven_pthIter_zsq_mul (r : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter r (fun z θ => z ^ 2 * g z θ)
      = fun z θ => z ^ 2 * Work.Spaces.pthIter r g z θ := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]
      funext z θ
      show deriv (fun θ' => z ^ 2 * Work.Spaces.pthIter r g z θ') θ
        = z ^ 2 * deriv (fun θ' => Work.Spaces.pthIter r g z θ') θ
      rw [deriv_const_mul_field]


/-! ## 2. The level-`0` identity `z²∂_z²h = D_z²h − D_zh` and its honesty transfer -/

/-- `(x − y)²c² ≤ 2(xc)² + 2(yc)²`. -/
theorem seven_sq_sub_mul_sq_le (x y c : ℝ) :
    ((x - y) * c) ^ 2 ≤ 2 * (x * c) ^ 2 + 2 * (y * c) ^ 2 := by
  nlinarith [sq_nonneg ((x + y) * c)]

/-- On the open quadrant, `z²∂_z²h = D_z²h − D_zh`. -/
theorem seven_zsq_pzIter_two_eq (h : ℝ → ℝ → ℝ) (hh : Work.FTS.EllipticEst.SmoothOpen h) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      z ^ 2 * Work.Spaces.pzIter 2 h z θ
        = Work.Spaces.DzIter 2 h z θ - Work.Spaces.DzIter 1 h z θ := by
  intro z θ hz hθ hπ
  have hd : HasDerivAt (fun z' => Work.Spaces.pzIter 1 h z' θ)
      (Work.Spaces.pzIter 2 h z θ) z := hh.hasDerivAt_slice_pzIter 1 ⟨hθ, hπ⟩ hz
  have e2 : Work.Spaces.DzIter 2 h z θ
      = z * (Work.Spaces.pzIter 1 h z θ + z * Work.Spaces.pzIter 2 h z θ) := by
    show z * deriv (fun z' => z' * Work.Spaces.pzIter 1 h z' θ) z = _
    have hmul : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pzIter 1 h z' θ)
        (1 * Work.Spaces.pzIter 1 h z θ + z * Work.Spaces.pzIter 2 h z θ) z :=
      (hasDerivAt_id z).mul hd
    rw [hmul.deriv]
    ring
  have e1 : Work.Spaces.DzIter 1 h z θ = z * Work.Spaces.pzIter 1 h z θ := rfl
  rw [e1, e2]
  ring


/-! ## 3. The three conjuncts -/


end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_bad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `row15_bad`: the "bad" angular endpoint for the `N₂^{ss}` row

Row 15 of the nonlinear estimates is about `N₂^{ss} = -2·U(Φ̃_*)·∂_θF_*`.  The whole row is
an `ℋ⁴`-estimate, and the bookkeeping of `row15_bookkeeping` needs to know that the angular
integral of `HkIntegrand α 4 (N₂^{ss})` at a fixed `z > 0` converges; the "bad" branch is
ruled out by the present lemma:

> if `θ ↦ U(Φ̃_*)(z,θ)` is *bounded away from zero* on a right neighbourhood of `θ = 0`, then
> `θ ↦ HkIntegrand α 4 (N₂^{ss}) z θ` is **not** integrable on `Iθ = [0,π/2]`.

The mathematics is a one-sided blow-up test.  `F_*(z,θ) = α (Γ(θ)/c)·F̲(z)` factorizes with
`Γ(θ) = (sin θ cos²θ)^{α/3}`, so for `0 < α ≤ 1` the angular derivative
`∂_θ F_*(z,θ) = cst(z)·Γ'(θ)` blows up like `θ^{α/3-1}` as `θ → 0⁺`.  Hence with
`|U(Φ̃_*)| ≥ δ`,

  `|N₂^{ss}(z,θ)| = 2|U(Φ̃_*)(z,θ)|·|∂_θF_*(z,θ)| ≳ δ·c·θ^{α/3-1}`,

and the `i = 0` term of the pure-`D_z` part of `HkIntegrand` carries the weight
`sin(2θ)^{-η}`, so on a right neighbourhood of `0`,

  `HkIntegrand α 4 (N₂^{ss}) z θ ≳ θ^{2α/3-2-η}`.

Since `2α/3 - 2 - η ≤ -7/3 < -1`, this power is not integrable at `0`, so the whole
integrand is not integrable on `Iθ`.

Two ingredients are imported from sibling modules of this directory:

* `pth_Fstar_lower` — the quantitative lower bound `|∂_θF_*(z,θ)| ≥ c θ^{α/3-1}` near `0`;
* `notIntegrableOn_Itheta_of_rpow_lower` — the measure-theoretic divergence test for a
  `C·θ^p` lower bound with `p ≤ -1`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option maxHeartbeats 1600000

/-! ## Two elementary auxiliary lemmas -/



/-! ## The pointwise lower bound for `HkIntegrand` -/


/-! ## The target -/


end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.L12XnBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

set_option autoImplicit false

/-- **A sup bound for `L₁₂(·)(z)` on the whole domain, from the `ℋ⁴`-size of the profile.** -/
theorem L12XnBound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ f : Work.FTS.Galerkin.Fn,
    Work.FTS.VocabO.HQo α 4 f → ∀ z : ℝ, 0 ≤ z →
      |Work.Construction.L12 f z| ≤ C * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨C, hCpos, hkey⟩ := Work.FTS.StrongEps.L12.L12_z_lipschitz
  refine ⟨C, hCpos, fun α hα f hf z hz => ?_⟩
  have hzero_sm : Work.FTS.EllipticEst.SmoothOpen (fun _ _ : ℝ => (0 : ℝ)) := by
    show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (fun _ _ : ℝ => (0 : ℝ)))
      Work.FTS.EllipticEst.Q0
    exact contDiffOn_const
  have hzero : Work.FTS.VocabO.HQo α 4 (fun _ _ : ℝ => (0 : ℝ)) :=
    ⟨hzero_sm, Work.FTS.Galerkin.Inhabit.HkMem_zeroF α 4⟩
  have hdiff : (fun z θ : ℝ => f z θ - 0) = f := by
    funext z θ; rw [sub_zero]
  have h := hkey α hα f (fun _ _ : ℝ => (0 : ℝ)) hf hzero (by rw [hdiff]; exact hf) z hz
  rw [hdiff, Work.FTS.Galerkin.L12_zero_fun z, sub_zero] at h
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hden : 0 < Real.sqrt (1 + z) := Real.sqrt_pos.mpr (by linarith)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (1 + z) := by
    have h1 : (1 : ℝ) ≤ 1 + z := by linarith
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + z) := Real.sqrt_le_sqrt h1
  have hle : C / Real.sqrt (1 + z) ≤ C := by
    rw [div_le_iff₀ hden]
    calc C = C * 1 := (mul_one C).symm
      _ ≤ C * Real.sqrt (1 + z) := mul_le_mul_of_nonneg_left hsqrt1 hCpos.le
  calc |Work.Construction.L12 f z| ≤ C / Real.sqrt (1 + z) * Work.FTS.Nonlin.Xn α f := h
    _ ≤ C * Work.FTS.Nonlin.Xn α f := mul_le_mul_of_nonneg_right hle hX

end Work.FTS.StrongEps.E5Aux2
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsZero.Bridge.LGammaSlice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsZero.Bridge

set_option linter.unusedVariables false

/-- **Angular-slice integrability of `𝓛_Γ`, positive half-line.**

For a datum `f` which is `C^∞` on the open quadrant and lies in `ℋ⁴`, and for which the
angular slice `θ ↦ K(θ)·∂_z f (s,θ)` is integrable for every `s > 0`, the same holds for
`θ ↦ K(θ)·(𝓛_Γ f)(s,θ)/s`.

The two `θ`-dependent pieces of `𝓛_Γ f/s` are
* `θ ↦ K θ · f s θ / s` — integrable by `sliceK_integrableOn_of_continuousOn` (`K` is bounded
  by `3`, the slice `f s ·` is square-integrable by `HkMem α 4 f` and `Iθ` has finite measure),
  together with `θ ↦ K θ · ∂_z f s θ` (the hypothesis `hpz`, scaled by `s`), and
* the contribution of `L₁₂(f)(s)`, which is *constant* in `θ`: the `θ`-dependence is
  `K θ · Γ(θ)/(c(1+s)²)`, which is continuous (hence integrable on the compact `Iθ`), and the
  constant factor `L₁₂(f)(s)` is pulled out.

The pointwise identity
`K θ · 𝓛_Γ f s θ = (1 - 2/(1+s))·(K θ f s θ) + s·(K θ ∂_z f s θ)
   - (K θ · 2sΓ(θ)/(c(1+s)²))·L₁₂(f)(s)`
is a pure ring identity (all the divisions are kept as atoms), so no positivity of `c` is
needed. -/
theorem LGammaSlice {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hpz : ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.pz f s θ) Work.Spaces.Iθ) :
    ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Coercivity.LGamma α f s θ / s) Work.Spaces.Iθ := by
  intro s hs
  -- `f` is continuous on the open quadrant, so the `f`-slice is integrable
  have hC : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0 := hsm.continuousOn
  have h1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ :=
    Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn hC hmem s hs
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- `K·f` (the division by `s` is undone with `s ≠ 0`)
  have hKf : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f s θ) Work.Spaces.Iθ := by
    have h : MeasureTheory.IntegrableOn
        (fun θ : ℝ => s * (Work.Spaces.K θ * f s θ / s)) Work.Spaces.Iθ := h1.const_mul s
    exact h.congr_fun (fun θ _ => by field_simp) hIθ
  -- `K·Γ` is integrable on `Iθ` (continuous on the compact interval)
  have hKΓ : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.Gam α θ) Work.Spaces.Iθ := by
    exact (Work.Spaces.CAux.integrableOn_GamK α hα).congr_fun (fun θ _ => by ring) hIθ
  -- the `L₁₂`-term: a continuous `θ`-dependent factor times the constant `L₁₂(f)(s)`
  have h3 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.K θ * (2 * s * Work.Spaces.Gam α θ
          / (Work.Spaces.c α * (1 + s) ^ 2))) * Work.Coercivity.L12f f s) Work.Spaces.Iθ := by
    have h : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (2 * s / (Work.Spaces.c α * (1 + s) ^ 2)
            * (Work.Spaces.K θ * Work.Spaces.Gam α θ)) * Work.Coercivity.L12f f s)
        Work.Spaces.Iθ := (hKΓ.const_mul (2 * s / (Work.Spaces.c α * (1 + s) ^ 2))).mul_const _
    exact h.congr_fun (fun θ _ => by ring) hIθ
  -- assemble: `K θ · 𝓛_Γ f s θ = (1 - 2/(1+s))·(K θ f) + s·(K θ ∂_z f) - (K θ B)·L₁₂(f)(s)`
  have hmain : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Coercivity.LGamma α f s θ) Work.Spaces.Iθ := by
    have h : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (1 - 2/(1+s)) * (Work.Spaces.K θ * f s θ)
          + s * (Work.Spaces.K θ * Work.Spaces.pz f s θ)
          - (Work.Spaces.K θ * (2 * s * Work.Spaces.Gam α θ
              / (Work.Spaces.c α * (1 + s) ^ 2))) * Work.Coercivity.L12f f s)
        Work.Spaces.Iθ :=
      ((hKf.const_mul (1 - 2/(1+s))).add ((hpz s hs).const_mul s)).sub h3
    exact h.congr_fun (fun θ _ => by
      simp only [Work.Coercivity.LGamma, Work.Coercivity.L, Work.Spaces.Dz]
      ring) hIθ
  -- finally divide by `s`, which is a constant factor
  have h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => s⁻¹ * (Work.Spaces.K θ * Work.Coercivity.LGamma α f s θ)) Work.Spaces.Iθ :=
    hmain.const_mul s⁻¹
  exact h.congr_fun (fun θ _ => by ring) hIθ

end Work.FTS.StrongEps.EpsZero.Bridge
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12.LocUnifMaster =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.L12

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The master bound -/


end Work.FTS.StrongEps.L12
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.gamQfun_jet_continuousOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular jet `θ ↦ D_θ^i (a · Γ(θ) · q(θ))` is continuous on `(0, π/2)`

`Γ(θ) = (sin θ · cos²θ)^{α/3}` and `q(θ) = cos 2θ - 1/3` are both smooth on the open
interval `(0, π/2)` (`contDiffOn_Gam_Ioo` for `Γ`, elementary for `q`), and the operator
`dthU φ = sin(2θ)·φ'` preserves `C^∞`-regularity on an open set
(`contDiffOn_dthU_iter_open`).  Hence every iterate `dthU^[i]` of the product is continuous
on `(0, π/2)`, with no restriction on `i` (in particular for `i ≤ 6`).
-/

open scoped Real Topology ContDiff

namespace Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux

/-- The angular factor `q(θ) = cos 2θ - 1/3` is smooth on the open interval. -/
lemma contDiffOn_qfun :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun θ : ℝ => Work.Spaces.qfun θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have h : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun θ : ℝ => Real.cos (2 * θ) - 1 / 3) (Set.Ioo 0 (Real.pi / 2)) := by
    fun_prop
  refine h.congr (fun θ _ => ?_)
  simp only [Work.Spaces.qfun_apply]

/-- The profile `θ ↦ a · Γ(θ) · q(θ)` is smooth on the open interval. -/
lemma contDiffOn_gamQfun (α a : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun θ : ℝ => a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ))
      (Set.Ioo 0 (Real.pi / 2)) :=
  contDiffOn_const.mul
    ((Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_Gam_Ioo α).mul contDiffOn_qfun)


end Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.c2mGam_Wt_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-- The `𝒲^{l,∞}`-weight `Wt α θ = sin(2θ)^{-α/5}/(α + sin 2θ)` times the pointwise
bound `Γ(θ)·(sin²2θ + α)` for the `D_θ`-iterates of `ψ = c2m·Γ` is bounded by `1` on the
whole of `Iθ` (at the two endpoints both factors `Wt` and `Γ` vanish). -/
theorem gam_mul_sq_add_alpha_mul_Wt_le_one {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)
      * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ ≤ 1 := by
  by_cases hθo : θ ∈ Set.Ioo 0 (Real.pi / 2)
  · have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Work.FTS.Nonlinear.FstarPkg.sin_two_nonneg_of_mem_Iθ hθ
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hB : Work.Spaces.Gam α θ * Real.sin (2 * θ) ^ (-(α / 5)) ≤ 1 :=
      Work.FTS.Nonlinear.FstarPkg.GamSinRpowMulLeOne hα hα1 hθ
    have hden : 0 < α + Real.sin (2 * θ) := by linarith
    have hnum : 0 ≤ Real.sin (2 * θ) ^ 2 + α := by positivity
    have hfrac : (Real.sin (2 * θ) ^ 2 + α) / (α + Real.sin (2 * θ)) ≤ 1 := by
      rw [div_le_one hden]
      nlinarith [hs0, hs1, hα]
    have hid : Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)
          * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ
        = (Work.Spaces.Gam α θ * Real.sin (2 * θ) ^ (-(α / 5)))
          * ((Real.sin (2 * θ) ^ 2 + α) / (α + Real.sin (2 * θ))) := by
      simp only [Work.FTS.Nonlinear.FstarPkg.DthAux.Wt]
      ring
    rw [hid]
    simpa using mul_le_mul hB hfrac (div_nonneg hnum hden.le) (by norm_num : (0 : ℝ) ≤ 1)
  · have hcases : θ = 0 ∨ θ = Real.pi / 2 := by
      rcases hθ with ⟨h0, h1⟩
      rcases lt_or_eq_of_le h0 with h | h
      · right
        by_contra hne
        exact hθo ⟨h, lt_of_le_of_ne h1 hne⟩
      · exact Or.inl h.symm
    have hs : Real.sin (2 * θ) = 0 := by
      rcases hcases with h | h
      · rw [h]; simp
      · rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    have hWt : Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ = 0 := by
      simp only [Work.FTS.Nonlinear.FstarPkg.DthAux.Wt, hs]
      rw [Real.zero_rpow (by intro hc; linarith [hα]), zero_div]
    rw [hWt, mul_zero]
    norm_num

/-- On `Iθ` the angular factor `ψ = c2m·Γ`, its `D_θ`-iterates to order `6` and the
`𝒲^{6,∞}`-weight `Wt` satisfy `|D_θ^j ψ| · Wt ≤ 10⁹`, uniformly in `0 < α ≤ 1`. -/
theorem c2mGam_Wt_bound : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    ∀ (j : ℕ), 1 ≤ j → j ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |(Work.Spaces.Lop^[j]) (Work.Construction.psiA α) θ|
        * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ ≤ K := by
  obtain ⟨D, hD, hDb⟩ := Work.Construction.H6N_GammaTerm_Lop_bound
  refine ⟨D, hD, ?_⟩
  intro α hα hα1 j hj1 hj6 θ hθ
  by_cases hθo : θ ∈ Set.Ioo 0 (Real.pi / 2)
  · have hbd := hDb α hα hα1 j hj1 hj6 θ hθo
    have hWt0 : 0 ≤ Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ :=
      Work.FTS.Nonlinear.FstarPkg.DthAux.Wt_nonneg hα hθ
    have hkern : Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)
        * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ ≤ 1 :=
      gam_mul_sq_add_alpha_mul_Wt_le_one hα hα1 hθ
    have hid : (D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α))
          * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ
        = D * (Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)
          * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ) := by ring
    calc |(Work.Spaces.Lop^[j]) (Work.Construction.psiA α) θ|
          * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ
        ≤ (D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α))
            * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ :=
          mul_le_mul_of_nonneg_right hbd hWt0
      _ = D * (Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)
            * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ) := hid
      _ ≤ D * 1 := mul_le_mul_of_nonneg_left hkern hD.le
      _ = D := by ring
  · have hcases : θ = 0 ∨ θ = Real.pi / 2 := by
      rcases hθ with ⟨h0, h1⟩
      rcases lt_or_eq_of_le h0 with h | h
      · right
        by_contra hne
        exact hθo ⟨h, lt_of_le_of_ne h1 hne⟩
      · exact Or.inl h.symm
    have hs : Real.sin (2 * θ) = 0 := by
      rcases hcases with h | h
      · rw [h]; simp
      · rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    have hWt : Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ = 0 := by
      simp only [Work.FTS.Nonlinear.FstarPkg.DthAux.Wt, hs]
      rw [Real.zero_rpow (by intro hc; linarith [hα]), zero_div]
    rw [hWt, mul_zero]
    exact hD.le

end Work.FTS.StrongPersist.H6Pair6Aux
end
