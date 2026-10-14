import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.HkMemGradU
import Submission.Work.FTS.EllipticEst.Honest.HonSliceSigmaLower
import Submission.Work.FTS.EllipticEst.Honest.I4UpperHonest
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.Prop.Ang2.Sig2
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceMomentIdentity
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceBounds
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.T2Qaux.SupAux
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Majorant6
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.Spaces.ProductRuleInW
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.hardy_N =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/hardy_N` — the sharp weighted Hardy bound of `I₁`, integrated in `z`

The slicewise sharp bound `hardy_slice_ae` (constant `(1+η)^{-2}`, from
`H2W.SlotA.sharpHardyCosWeight_open`) is integrated against the radial weight `w(z)²`.

Because the `z`-uniform version `weightedNLePp` needs the slice integrability for *every*
`z ∈ Iz` (which is not available), the integration is done here directly, with the standard
`by_cases` on the `z`-integrability of the weighted `N`-energy: in the integrable case
`integral_mono_ae` applies, and in the non-integrable case the totalised integral is `0` and
the right-hand side is non-negative.
-/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)



end

end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.aeSigmaEnergyIneq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.AeStepOneAux.Sig2

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option maxHeartbeats 3200000

local notation "sg" => Work.FTS.EllipticEst.sEta
local notation "Ith" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

/-! ## The `σ`-weighted angular energy of `∂_θu` -/




theorem Rslice_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ Rslice u z := by
  rw [Rslice_eq_integral]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
    mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.H2W.AeProof.AeSigma.sEtaR_nonneg hθ))

theorem Zslice_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ Zslice u z := by
  rw [Zslice_eq_integral]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
    mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.H2W.AeProof.AeSigma.sEtaR_nonneg hθ))

/-! ## The slicewise transfer of the coercivity hypothesis -/


/-! ## The `σ`-slice energy of `∂_θu`: honesty and integrability -/



/-! ## The main theorem -/


end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.OrthCond_lambda_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option linter.unusedVariables false

/-!
# `OrthCond_lambda_zero`: the `θ → 0⁺` trace of a solution with orthogonal data vanishes

Target: for `0 < α ≤ 1/4`, `k ≥ 2`, a datum `(F,Ψ)` of the trace-free class `EllHypT α k F Ψ`
satisfying the orthogonality condition

  `OrthCond (fun z θ => Ψ z θ + Gsing α F z · sin 2θ)`

(equivalently `F_*(Ψ) = -(4/15) Gsing α F`), the angular slice `θ ↦ Ψ z θ` tends to `0` at
`θ → 0⁺` for **every** `z > 0`.

## Route

Write `B_j = Bmom Ψ j` for the `j`-th radial moment `∫_θ D_z^jΨ·sinθcos²θ` and
`Λ(z) = lim_{θ→0⁺} Ψ z θ`.  Two facts about `Λ` are available in the workspace:

* the `θ`-integration by parts `∫_θ Lzero1(Ψ z ·)·sinθcos²θ = -Λ(z)`
  (`Endpt.Lzero1_integral_eq_neg_limit`), with the existence of `Λ` from
  `remov.SourceBound.auxLimitAtZero`;
* the decomposition of the *same* integral along the equation
  (`remov.SourceBound.moment_decomposition`):

  `-Λ(z) = F_*(F)(z) + α²z²M₂(z) + α(5+α)zM₁(z)`,  `M_j = ∫_θ ∂_z^jΨ·sinθcos²θ`.

So the whole content is the pointwise identity

  **(S)**  `F_*(F)(z) + α²B₂(z) + 5αB₁(z) = 0`  for every `z > 0`

(the relation between the plain moments `M_j` and the `D_z`-moments `B_j` being `B₁ = zM₁`,
`B₂ = B₁ + z²M₂`).

The function `Sfun = B₀(F) + α²B₂ + 5αB₁` is

* **continuous** on `(0,∞)`: `B₀(F)` and `B₁` are moments of `F` and `Ψ`, and
  `B₂ = B₁ + B₀(z²∂_zzΨ)` is a moment of `z²∂_zzΨ` — all continuous by
  `Fstar_Hk_le_open.continuousOn_Bmom`;
* **zero almost everywhere**: `OrthCond` gives `B₀(Ψ) = -(4/15) Gsing α F`, the moment tower
  `Fstar_Hk_le_open.ae_hasDerivAt_Bmom` gives `B₁' = B₂/z` a.e., so with `Gsing ∈ C²`
  (`UopHk.Gsing_cDiff_kp1`) and the Euler ODE for `Gsing` (`Elliptic.Gsing_ode`) one gets
  `B₁ = -(4/15) z ∂_zGsing` and `B₂ = -(4/15) z(∂_zGsing + z∂_zzGsing)` a.e., whence

  `Sfun = F_*(F) - (4/15)(α²z²G'' + α(5+α)zG') = F_*(F) - F_*(F) = 0`  a.e.

A continuous function vanishing a.e. on `(0,∞)` vanishes identically, which is **(S)**; the
endpoint data then give `Λ = 0`.
-/

/-! ## The function whose vanishing is proved -/

/-- `Sfun α F Ψ = B₀(F) + α²B₂(Ψ) + 5αB₁(Ψ)`, the combination for which the equation, the
orthogonality condition and the `Gsing`-ODE give both continuity and a.e. vanishing. -/
def Sfun (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun w => Work.FTS.EllipticEst.Bmom F 0 w + α ^ 2 * Work.FTS.EllipticEst.Bmom Ψ 2 w
    + 5 * α * Work.FTS.EllipticEst.Bmom Ψ 1 w

/-! ## Elementary integrability and moment identities -/



/-- **Slice integrability of `g z · · sinθcos²θ` from level-`0` honesty.**  For `g` continuous on
the open quadrant with `HkMem α 0 g`, the absorption
`|g z θ·sinθcos²θ| ≤ (g z θ·w z/sin(2θ)^{η/2})² + 1` and the honesty of the level-`0` integrand
give integrability of the slice for every `z > 0`. -/
theorem integrableOn_slice_mul_sinCos2 {α : ℝ} {g : ℝ → ℝ → ℝ} {z : ℝ}
    (hcont : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmem : Work.Spaces.HkMem α 0 g) (hz : 0 < z) :
    IntegrableOn (fun θ : ℝ => g z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hz)
  have h1 : IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 g z θ) Work.Spaces.Iθ :=
    hmem.1 z hzI
  have hvol : (volume : Measure ℝ) Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have h2 : IntegrableOn
      (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 g z θ + 1) Work.Spaces.Iθ :=
    h1.add (integrableOn_const hvol)
  have hsc : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    unfold Work.Elliptic.sinCos2
    fun_prop
  have haesm : AEStronglyMeasurable (fun θ : ℝ => g z θ * Work.Elliptic.sinCos2 θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => g p.1 p.2 * Work.Elliptic.sinCos2 p.2) (hcont.mul hsc) hz
  refine Integrable.mono' h2 haesm ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
  rw [Real.norm_eq_abs]
  have hb := abs_mul_sinCos2_le_weighted (f := fun θ : ℝ => g z θ) hz hθ
  have hkey : Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simp [Work.Spaces.HkIntegrand]
  rw [hkey]
  linarith [hb]






/-! ## The target -/


end Work.FTS.EllipticEst.Cores
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Pieces.TopSlotIntegrability =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.Pieces

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers

The a.e.-form of the radial variable, the additivity/const-multiple rules for the iterates of
`∂_θ` (the module `remov.PsiSlotBounds`, which contains `pthIter_add`, cannot be imported at the
moment, so the two-line induction is redone here), the measurability of the slots, and the
monotonicity of the angular weight `sin(2θ)^a` in the exponent. -/

/-- Almost every `z ∈ Iz = [0,∞)` is positive (the only missing point is `0`). -/
private theorem ts_ae_pos_Iz :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), (0 : ℝ) < z := by
  rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici, MeasureTheory.ae_iff]
  have h1 : {x : ℝ | ¬ (x ∈ Set.Ici (0 : ℝ) → (0 : ℝ) < x)} = {0} := by
    ext x
    simp only [Set.mem_Ici, not_imp, not_lt, Set.mem_singleton_iff]
    constructor
    · intro h; linarith [h.1, h.2]
    · intro h; subst h; norm_num
  rw [h1]
  exact MeasureTheory.measure_singleton 0


/-- `∂_θ^{m+n} f = ∂_θ^m (∂_θ^n f)`. -/
private theorem ts_pthIter_add (m n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter (m + n) f = Work.Spaces.pthIter m (Work.Spaces.pthIter n f) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_add, Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]

/-- `∂_θ^n (c·f) = c·∂_θ^n f` for a constant `c` (no smoothness needed). -/
private theorem ts_pthIter_const_mul (c : ℝ) (n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter n (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pthIter n f z θ := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]
      funext z θ
      simp only [Work.Spaces.pth]
      rw [deriv_const_mul_field']

/-- The angular slice `θ ↦ ∂_θ^{n+1} f z θ` is measurable (no smoothness needed). -/
private theorem ts_measurable_pthIter_succ (n : ℕ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Measurable (fun θ => Work.Spaces.pthIter (n + 1) f z θ) := by
  have h : (fun θ => Work.Spaces.pthIter (n + 1) f z θ)
      = deriv (fun θ' => Work.Spaces.pthIter n f z θ') := by
    funext θ
    rw [Work.Spaces.pthIter_succ]
    rfl
  rw [h]
  exact measurable_deriv _

/-- The angular weight `θ ↦ sin(2θ)^q` is measurable. -/
private theorem ts_measurable_sin_rpow (q : ℝ) :
    Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ q) :=
  (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const q

/-- For `θ` in the open interval the weight `sin(2θ)^a` is antitone in the exponent. -/
private theorem ts_sin_rpow_le {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) {a b : ℝ}
    (hab : a ≤ b) : (Real.sin (2 * θ)) ^ b ≤ (Real.sin (2 * θ)) ^ a := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsplit : (Real.sin (2 * θ)) ^ b
      = (Real.sin (2 * θ)) ^ a * (Real.sin (2 * θ)) ^ (b - a) := by
    rw [← Real.rpow_add hs, show a + (b - a) = b from by ring]
  have hle : (Real.sin (2 * θ)) ^ (b - a) ≤ 1 :=
    Real.rpow_le_one hs.le hs1 (by linarith)
  have hnn : 0 ≤ (Real.sin (2 * θ)) ^ a := Real.rpow_nonneg hs.le a
  rw [hsplit]
  calc (Real.sin (2 * θ)) ^ a * (Real.sin (2 * θ)) ^ (b - a)
      ≤ (Real.sin (2 * θ)) ^ a * 1 := mul_le_mul_of_nonneg_left hle hnn
    _ = (Real.sin (2 * θ)) ^ a := mul_one _

/-- `SmoothOpen` is closed under multiplication by a constant. -/
private theorem ts_smoothOpen_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  have hfun : Function.uncurry (fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := by
    funext p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
  exact (contDiffOn_const : ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ × ℝ => c)
    Work.FTS.EllipticEst.Q0).mul hf

/-- `SmoothOpen` is closed under the iterated `∂_θ`. -/
private theorem ts_smoothOpen_pthIter {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (n : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- `SmoothOpen` is closed under addition. -/
private theorem ts_smoothOpen_add {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => f p.1 p.2) Work.FTS.EllipticEst.Q0 := hf.forall n
  have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => g p.1 p.2) Work.FTS.EllipticEst.Q0 := hg.forall n
  have h3 := h1.add h2
  have hfun : Function.uncurry (fun z θ => f z θ + g z θ)
      = fun p : ℝ × ℝ => f p.1 p.2 + g p.1 p.2 := by
    funext p; rfl
  rw [hfun]
  exact h3

/-- `Work.Stability.smoothOrder` is not zero (it is the genuine smooth order `∞`). -/
private theorem ts_smoothOrder_ne_zero : Work.Stability.smoothOrder ≠ 0 := by
  simp [Work.Stability.smoothOrder]

/-- On the open quadrant the iterated `∂_θ` is additive for `SmoothOpen` data. -/
private theorem ts_pthIter_add_on_Q0 {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) (n : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pthIter n f z θ + Work.Spaces.pthIter n g z θ := by
  induction n with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨h1, h2⟩
      have heq : (fun θ' : ℝ => Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pthIter n f z θ' + Work.Spaces.pthIter n g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pthIter n f z θ') θ :=
        (((ts_smoothOpen_pthIter hf n).curry_θ hz).differentiableOn ts_smoothOrder_ne_zero
          |>.differentiableAt (isOpen_Ioo.mem_nhds hθ))
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pthIter n g z θ') θ :=
        (((ts_smoothOpen_pthIter hg n).curry_θ hz).differentiableOn ts_smoothOrder_ne_zero
          |>.differentiableAt (isOpen_Ioo.mem_nhds hθ))
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pth]
      exact heq.deriv_eq.trans (deriv_add hd1 hd2)

/-! ## The `a.e.`-integrability bundle -/

/- **Discharge of the a.e.-in-`z` integrability bundle consumed by `TopSlotTwoD`.**
Intended namespace: `Work.FTS.EllipticEst.Cores.Pieces`.

From the hypotheses of the target statement alone (a weak datum `EllWeakPos α k F Ψ` with `k ≥ 3`
and the two level-`(k-1)` norm bounds, with the parameter `D`), conclude for almost every `z > 0`:

* `θ ↦ Ψ z θ` is continuous on the closed interval (the proved
  `Work.FTS.EllipticEst.remov.weakSliceRegular`);
* the `(k+2)`-nd angular derivative slot with weight `σ^{2k-γ}` is integrable — it is the mixed
  level-`k` slot of `HkSq α k (∂_θθΨ)`, honest by `EllWeakPos.memB`;
* the `k`-th angular derivative slot of `Gsrc α F Ψ = F + α²z²∂_z²Ψ + α(5+α)D_zΨ` is integrable —
  the pieces come from `EllWeakPos.memF` (levels `≤ k` of `F`), `EllWeakPos.memA`
  (levels `≤ k` of `z²∂_z²Ψ`) and from `EllWeakPos.memB` for the `D_zΨ`-piece (via the proved
  `Work.FTS.EllipticEst.remov.EllWeakPos_DzIter_one_shift_of_two_le`, which supplies
  `HkMem α (k-1) (pthIter 2 (DzIter 1 Ψ))`, together with `∂_θ^k(D_zΨ) = ∂_θ^{k-2}(∂_θθ(D_zΨ))`
  and `σ^{2k-γ} ≤ σ^{2(k-2)-γ}`; note that the real-valued bound (2) alone is *not* enough here,
  because `HkSq` is a Bochner integral and returns junk `0` when the integrand is non-integrable);
* the `u`-family `Icc 3 (k+1)`, the `η`-term and the two unweighted `L²` terms (the last two follow
  from the slice continuity and smoothness on the open interval).

The transfer "integrability of the `D_θ`-slots ↦ integrability of the plain slots" is the sharp
forward expansion `σ^{2m}(∂_θ^m f)² ≤ C Σ_{q∈Icc 1 m}(D_θ^q f)²` in which the `q = 0` term is absent
(the coefficient of `∂_θ^0` in `D_θ^m` vanishes because `D_θ(const) = 0`);
`Work.FTS.EllipticEst.remov.DthIter_expansion` (`dthCoef_eq_sin_pow_mul_dB`, `DthCoef_sin_pow_bound`,
`dthCoef_self`) and `Work.FTS.EllipticEst.Cores.Pieces.pthIter_sq_mul_sin_pow_le` are the available
ingredients. -/
theorem TopSlotIntegrability (k : ℕ) (hk : 3 ≤ k) (D : ℝ) (hD : 0 < D) :
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
        ≤ D * Work.Spaces.HkNorm α k F →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        ContinuousOn (fun t => Ψ z t) (Set.Icc 0 (Real.pi / 2)) ∧
        MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter k
          (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ ∧
        (∀ i ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn (fun θ =>
          (Work.Spaces.pthIter i Ψ z θ) ^ 2 *
            (Real.sin (2 * θ)) ^ (2 * (i : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iθ) ∧
        MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 *
          Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
          Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn (fun θ => (Ψ z θ) ^ 2) Work.Spaces.Iθ) := by
  intro α F Ψ hα hα4 h _hH1 _hH2
  filter_upwards [ts_ae_pos_Iz] with z hz
  have hk1 : 1 ≤ k := by omega
  -- the smoothness of `Ψ` and of its iterates
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hG : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := hΨ.pth.pth
  -- the slice bundle of `weakSliceRegular`
  obtain ⟨hcont, -, -, -, hPsi2, hPsi1, hPsi2sEta⟩ :=
    Work.FTS.EllipticEst.remov.weakSliceRegular k hk1 α F Ψ hα hα4 h z hz
  have hPsi2' : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using
      hPsi2sEta
  have hPsi1' : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
      Work.Spaces.Iθ := by
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using hPsi1
  refine ⟨hcont, ?_, ?_, ?_, hPsi2', hPsi1', hPsi2⟩
  · -- the top slot `∂_θ^{k+2}Ψ`
    have h := pthSlotInt_of_HkMem (α := α) hα (k := k) (g := Work.Spaces.pthIter 2 Ψ)
      (fun n => hG.forall n) h.memB hz (m := k) (by omega) le_rfl
    have hfun : (fun θ => (Work.Spaces.pthIter k (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        = fun θ => (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) := by
      funext θ
      rw [← ts_pthIter_add k 2 Ψ]
    rw [hfun] at h
    exact h
  · -- the angular source `Gsrc α F Ψ`
    set A : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ with hAdef
    set B : ℝ → ℝ → ℝ := Work.Spaces.DzIter 1 Ψ with hBdef
    set c : ℝ := α * (5 + α) with hcdef
    have hFs : Work.FTS.EllipticEst.SmoothOpen F :=
      Work.FTS.EllipticEst.remov.ws_smoothOpen_F h
    have hAs : Work.FTS.EllipticEst.SmoothOpen A :=
      show Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) from
        Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq hΨ
    have hBs : Work.FTS.EllipticEst.SmoothOpen B :=
      show Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ) from hΨ.DzIter 1
    have hiF := pthSlotInt_of_HkMem (α := α) hα (k := k) (g := F)
      (fun n => hFs.forall n) h.memF hz (m := k) (by omega) le_rfl
    have hiA := pthSlotInt_of_HkMem (α := α) hα (k := k) (g := A)
      (fun n => hAs.forall n) h.memA hz (m := k) (by omega) le_rfl
    -- the `D_zΨ`-piece: `HkMem α (k-1) (∂_θ²(D_zΨ))` from the radial shift
    have hBmem0 : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.AeMom.Repair.HkMem_Dz_shift (α := α) (k := k) hk1 hG h.memB
    have hBmem : Work.Spaces.HkMem α (k - 1) (Work.Spaces.pthIter 2 B) := by
      rw [hBdef]
      refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hBmem0 ?_
      intro z' hz' θ hθ
      exact (Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ 1
        (show ((z', θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hz', hθ⟩)).symm
    have hiB0 := pthSlotInt_of_HkMem (α := α) hα (k := k - 1) (g := Work.Spaces.pthIter 2 B)
      (fun n => (ts_smoothOpen_pthIter hBs 2).forall n)
      hBmem hz (m := k - 2) (by omega) (by omega)
    have hexpB : 2 * ((k - 2 : ℕ) : ℝ) - Work.Spaces.gam α
        ≤ 2 * (k : ℝ) - Work.Spaces.gam α := by
      have : ((k - 2 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 2
      linarith
    have hiB1 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter k B z θ) ^ 2 *
        (Real.sin (2 * θ)) ^ (2 * ((k - 2 : ℕ) : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ := by
      have hfun : (fun θ => (Work.Spaces.pthIter (k - 2) (Work.Spaces.pthIter 2 B) z θ) ^ 2 *
            (Real.sin (2 * θ)) ^ (2 * ((k - 2 : ℕ) : ℝ) - Work.Spaces.gam α))
          = fun θ => (Work.Spaces.pthIter k B z θ) ^ 2 *
            (Real.sin (2 * θ)) ^ (2 * ((k - 2 : ℕ) : ℝ) - Work.Spaces.gam α) := by
        funext θ
        rw [← ts_pthIter_add (k - 2) 2 B, show k - 2 + 2 = k from by omega]
      rw [hfun] at hiB0
      exact hiB0
    have hiB : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter k B z θ) ^ 2 *
        (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ := by
      have hm : Measurable (fun θ => Work.Spaces.pthIter k B z θ) := by
        have h := ts_measurable_pthIter_succ (k - 1) B z
        rwa [show k - 1 + 1 = k from by omega] at h
      have hmeasw : Measurable (fun θ : ℝ =>
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) :=
        ts_measurable_sin_rpow _
      refine MeasureTheory.Integrable.mono' hiB1
        (((hm.pow_const 2).mul hmeasw).aestronglyMeasurable) ?_
      refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
      have hsin : 0 ≤ Real.sin (2 * θ) :=
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])).le
      have hw : 0 ≤ (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) :=
        Real.rpow_nonneg hsin _
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hw)]
      exact mul_le_mul_of_nonneg_left (ts_sin_rpow_le hθ hexpB) (sq_nonneg _)
    -- the pointwise expansion of `∂_θ^k(Gsrc α F Ψ)`
    have hgrp : Work.FTS.EllipticEst.Mine.Gsrc α F Ψ
        = fun z θ => (F z θ + α ^ 2 * A z θ) + c * B z θ := by
      funext z θ
      rw [hAdef, hBdef, hcdef]
      simp only [Work.FTS.EllipticEst.Mine.Gsrc, Work.Spaces.DzIter_succ,
        Work.Spaces.DzIter_zero, Work.Spaces.Dz]
    have hsm1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ + α ^ 2 * A z θ) :=
      ts_smoothOpen_add hFs (ts_smoothOpen_const_mul (α ^ 2) hAs)
    have hsm2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * B z θ) :=
      ts_smoothOpen_const_mul c hBs
    have hAc : Work.FTS.EllipticEst.SmoothOpen (fun z θ => α ^ 2 * A z θ) :=
      ts_smoothOpen_const_mul (α ^ 2) hAs
    have hdecomp : ∀ {z' θ : ℝ}, 0 < z' → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.pthIter k (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z' θ
          = Work.Spaces.pthIter k F z' θ + α ^ 2 * Work.Spaces.pthIter k A z' θ
            + c * Work.Spaces.pthIter k B z' θ := by
      intro z' θ hz' hθ0 hθ1
      rw [hgrp, ts_pthIter_add_on_Q0 hsm1 hsm2 k z' θ hz' hθ0 hθ1,
        ts_pthIter_add_on_Q0 hFs hAc k z' θ hz' hθ0 hθ1]
      rw [ts_pthIter_const_mul (α ^ 2) k A, ts_pthIter_const_mul c k B]
    -- the three integrable pieces, with the constants pulled out
    have hpartF : MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.pthIter k F z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ := hiF
    have hpartA : MeasureTheory.IntegrableOn (fun θ =>
        (α ^ 2 * Work.Spaces.pthIter k A z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ :=
      (hiA.const_mul ((α ^ 2) ^ 2)).congr
        (Filter.Eventually.of_forall (fun θ => by ring))
    have hpartB : MeasureTheory.IntegrableOn (fun θ =>
        (c * Work.Spaces.pthIter k B z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ :=
      (hiB.const_mul (c ^ 2)).congr (Filter.Eventually.of_forall (fun θ => by ring))
    have hmaj : MeasureTheory.IntegrableOn (fun θ => 3 *
        ((Work.Spaces.pthIter k F z θ) ^ 2 *
            (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
          + ((α ^ 2 * Work.Spaces.pthIter k A z θ) ^ 2 *
              (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
            + (c * Work.Spaces.pthIter k B z θ) ^ 2 *
              (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)))) Work.Spaces.Iθ :=
      (hpartF.add (hpartA.add hpartB)).const_mul 3
    have hm : Measurable (fun θ =>
        Work.Spaces.pthIter k (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) := by
      have h := ts_measurable_pthIter_succ (k - 1) (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z
      rwa [show k - 1 + 1 = k from by omega] at h
    have haesm : AEStronglyMeasurable (fun θ =>
        (Work.Spaces.pthIter k (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      ((hm.pow_const 2).mul (ts_measurable_sin_rpow _)).aestronglyMeasurable
    refine MeasureTheory.Integrable.mono' hmaj haesm ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    have hdec := hdecomp (z' := z) (θ := θ) hz hθ.1 hθ.2
    have hsin : 0 ≤ Real.sin (2 * θ) :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])).le
    have hw : 0 ≤ (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) :=
      Real.rpow_nonneg hsin _
    have hsq : (Work.Spaces.pthIter k F z θ
          + α ^ 2 * Work.Spaces.pthIter k A z θ + c * Work.Spaces.pthIter k B z θ) ^ 2
        ≤ 3 * ((Work.Spaces.pthIter k F z θ) ^ 2
            + ((α ^ 2 * Work.Spaces.pthIter k A z θ) ^ 2
              + (c * Work.Spaces.pthIter k B z θ) ^ 2)) := by
      nlinarith [sq_nonneg (Work.Spaces.pthIter k F z θ
          - α ^ 2 * Work.Spaces.pthIter k A z θ),
        sq_nonneg (α ^ 2 * Work.Spaces.pthIter k A z θ
          - c * Work.Spaces.pthIter k B z θ),
        sq_nonneg (c * Work.Spaces.pthIter k B z θ
          - Work.Spaces.pthIter k F z θ)]
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin _)), hdec]
    calc (Work.Spaces.pthIter k F z θ + α ^ 2 * Work.Spaces.pthIter k A z θ
            + c * Work.Spaces.pthIter k B z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
        ≤ (3 * ((Work.Spaces.pthIter k F z θ) ^ 2
            + ((α ^ 2 * Work.Spaces.pthIter k A z θ) ^ 2
              + (c * Work.Spaces.pthIter k B z θ) ^ 2))) *
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) :=
          mul_le_mul_of_nonneg_right hsq hw
      _ = 3 * ((Work.Spaces.pthIter k F z θ) ^ 2 *
              (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
            + ((α ^ 2 * Work.Spaces.pthIter k A z θ) ^ 2 *
                (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
              + (c * Work.Spaces.pthIter k B z θ) ^ 2 *
                (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) := by ring

  · -- the family `Icc 3 (k+1)`
    intro i hi
    have hi3 : 3 ≤ i := (Finset.mem_Icc.mp hi).1
    have hik : i ≤ k + 1 := (Finset.mem_Icc.mp hi).2
    have h := pthSlotInt_of_HkMem (α := α) hα (k := k) (g := Work.Spaces.pthIter 2 Ψ)
      (fun n => hG.forall n) h.memB hz (m := i - 2) (by omega) (by omega)
    have hexp : 2 * ((i - 2 : ℕ) : ℝ) - Work.Spaces.gam α
        = 2 * (i : ℝ) - 4 - Work.Spaces.gam α := by
      rw [Nat.cast_sub (by omega : 2 ≤ i)]
      push_cast
      ring
    have hfun : (fun θ => (Work.Spaces.pthIter (i - 2) (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * ((i - 2 : ℕ) : ℝ) - Work.Spaces.gam α))
        = fun θ => (Work.Spaces.pthIter i Ψ z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (i : ℝ) - 4 - Work.Spaces.gam α) := by
      funext θ
      rw [← ts_pthIter_add (i - 2) 2 Ψ, show i - 2 + 2 = i from by omega, hexp]
    rw [hfun] at h
    exact h
end

end Work.FTS.EllipticEst.Cores.Pieces
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Dispatch.aeSigmaEnergyD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.H2W.Ae

namespace Work.FTS.EllipticEst.Dispatch.SigmaRad

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

local notation "σw" => Work.FTS.EllipticEst.sEta

/-!
# The `σ`-weighted radial energy inequality of Step 1 of `prop:H2`

`α² HkSq α 0 (z∂_zu) ≤ C (HkSq α 0 G + HkSq α 0 u)` for data in the almost-everywhere class
`Work.FTS.EllipticEst.H2W.Ae.AeData`, together with the honesty of `z∂_zu`.

The proof is the main body of `Work.FTS.EllipticEst.H2W.Ae.aeSigmaEnergyH2`
(`H2W/AeStepOneAux/aeSigmaEnergyClean.lean`), with two substitutions:

* the truncated `σ`-energy identity `Work.FTS.EllipticEst.H2W.Ae.aeTruncSigmaIdAe` (currently a
  `sorry`) is replaced by the proved `Work.FTS.EllipticEst.Dispatch.aeTruncSigmaIdD` (the
  `G`-form of the proved `Dispatch.truncRadialIbpTheta`);
* the cutoff family `Work.FTS.EllipticEst.H2W.Ae.aeSigmaCutoffSeq` (currently a `sorry`) is
  replaced by the proved `Work.FTS.EllipticEst.Mine.zcutFam` together with the weighted
  derivative bounds `Honest.omegaW_deriv_bounds` + `AeStepOneAux.chi_second_le`.
-/

theorem aeSigmaEnergyD : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.L2Mem (fun z θ => z * Work.Spaces.pz u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ∧
      α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ C * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
  obtain ⟨K, hKpos, hKslice⟩ := aeSigmaSliceLower
  -- the cutoff family with the weighted derivative bounds
  obtain ⟨χ, C₁, C₂, hC₁pos, hC₂pos, hχsm, hχ01, hχleft, hχmid, hχright, hχd1, hχd2, hχlim⟩ :=
    Work.FTS.EllipticEst.Mine.zcutFam
  have hC₁nn : 0 ≤ C₁ := le_of_lt hC₁pos
  have hchi2 : ∀ n z, |z ^ 2 * deriv (deriv (χ n)) z| ≤ C₂ + C₁ := fun n z =>
    Work.FTS.EllipticEst.AeStepOneAux.Sig2.chi_second_le (hχsm n 2) (hχd1 n) (hχd2 n) z
  have hC₂nn : 0 ≤ C₂ + C₁ := by linarith
  have hχabs : ∀ n z, |χ n z| ≤ 1 := fun n z => by
    rw [abs_of_nonneg (hχ01 n z).1]; exact (hχ01 n z).2
  have hχdiff : ∀ n, ContDiff ℝ 2 (χ n) := fun n => hχsm n 2
  have hχsupp : ∀ (n : ℕ) (z : ℝ),
      z ∉ Set.Icc (1 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1)) → χ n z = 0 := by
    intro n z hz
    rcases lt_or_ge z (1 / ((n : ℝ) + 1)) with h | h
    · exact hχleft n z (le_of_lt h)
    · have h2 : 2 * ((n : ℝ) + 1) < z := by
        rcases lt_or_ge (2 * ((n : ℝ) + 1)) z with h2 | h2
        · exact h2
        · exact absurd (Set.mem_Icc.mpr ⟨h, h2⟩) hz
      exact hχright n z (le_of_lt h2)
  set C0 : ℝ := max (3 + C₁) (6 + 4 * C₁ + (C₂ + C₁)) with hC0def
  have hC0pos : 0 < C0 := by
    rw [hC0def]
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hmm1 : ∀ n, ∀ z, 0 < z → |deriv (fun y : ℝ => y * (Work.Spaces.w y ^ 2 * χ n y)) z|
      ≤ (3 + C₁) * (Work.Spaces.w z) ^ 2 := fun n =>
    (Work.FTS.EllipticEst.Honest.omegaW_deriv_bounds (hχsm n 2) (hχd1 n) (hchi2 n)
      (hχabs n) hC₁nn hC₂nn).1
  have hmm2 : ∀ n, ∀ z, 0 < z →
      |deriv (fun y : ℝ => deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x ^ 2 * χ n x)) y) z|
      ≤ (6 + 4 * C₁ + (C₂ + C₁)) * (Work.Spaces.w z) ^ 2 := fun n =>
    (Work.FTS.EllipticEst.Honest.omegaW_deriv_bounds (hχsm n 2) (hχd1 n) (hchi2 n)
      (hχabs n) hC₁nn hC₂nn).2
  have hχbd2 : ∀ n z, 0 < z → |deriv (fun z' : ℝ => χ n z' * phiW z' * z') z| ≤ C0 * phiW z := by
    intro n z hz
    have h := hmm1 n z hz
    have hfun : (fun y : ℝ => y * (Work.Spaces.w y ^ 2 * χ n y))
        = fun y : ℝ => χ n y * phiW y * y := by
      funext y; simp only [phiW]; ring
    rw [hfun] at h
    calc |deriv (fun z' : ℝ => χ n z' * phiW z' * z') z|
        ≤ (3 + C₁) * phiW z := h
      _ ≤ C0 * phiW z := by
          refine mul_le_mul_of_nonneg_right ?_ (by simp only [phiW]; positivity)
          rw [hC0def]; exact le_max_left _ _
  have hχbd1 : ∀ n z, 0 < z →
      |deriv (deriv (fun z' : ℝ => χ n z' * phiW z' * z' ^ 2)) z| ≤ C0 * phiW z := by
    intro n z hz
    have h := hmm2 n z hz
    have hfe : (fun x : ℝ => x ^ 2 * (Work.Spaces.w x ^ 2 * χ n x))
        = fun x : ℝ => χ n x * phiW x * x ^ 2 := by
      funext x; simp only [phiW]; ring
    have hfun : (fun y : ℝ => deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x ^ 2 * χ n x)) y)
        = fun y : ℝ => deriv (fun x : ℝ => χ n x * phiW x * x ^ 2) y := by
      rw [hfe]
    rw [hfun] at h
    calc |deriv (deriv (fun z' : ℝ => χ n z' * phiW z' * z' ^ 2)) z|
        ≤ (6 + 4 * C₁ + (C₂ + C₁)) * phiW z := h
      _ ≤ C0 * phiW z := by
          refine mul_le_mul_of_nonneg_right ?_ (by simp only [phiW]; positivity)
          rw [hC0def]; exact le_max_right _ _
  refine ⟨3 + K + 2 * C0, by positivity, ?_⟩
  intro α u G hA
  refine ⟨l2mem_grad_profile hA, ?_⟩
  have hα0 : (0 : ℝ) ≤ α := le_of_lt (AeData.hα hA)
  have hα4 : α ≤ 1 / 4 := AeData.hα4 hA
  have hmemU : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G hA
  have hmemX : Work.Spaces.HkMem α 0 (grad u) := Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G hA
  have hmemG : Work.Spaces.HkMem α 0 G := AeData.memG hA
  have hmemR : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) :=
    AeData.memRad2 hA
  have hUslice : ∀ z, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2 * σw θ) Work.Spaces.Iθ :=
    (integrableOn_of_HkMem_zero hmemU).1
  have hGslice : ∀ z, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => (G z θ) ^ 2 * σw θ) Work.Spaces.Iθ :=
    (integrableOn_of_HkMem_zero hmemG).1
  have hUint : MeasureTheory.IntegrableOn (fun z =>
      phiW z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ)) Work.Spaces.Iz :=
    weighted_slice_integrable hmemU
  have hGint : MeasureTheory.IntegrableOn (fun z =>
      phiW z * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * σw θ)) Work.Spaces.Iz :=
    weighted_slice_integrable hmemG
  have hXint : MeasureTheory.IntegrableOn (fun z =>
      phiW z * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ))
      Work.Spaces.Iz := weighted_slice_integrable hmemX
  have hRint : MeasureTheory.IntegrableOn (fun z =>
      phiW z * (∫ θ in Work.Spaces.Iθ, (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 * σw θ))
      Work.Spaces.Iz := weighted_slice_integrable hmemR
  -- the slice mass and the two scalars
  set U : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ with hUdef
  set UU : ℝ := ∫ z in Work.Spaces.Iz, phiW z * U z with hUUdef
  set GG : ℝ := ∫ z in Work.Spaces.Iz,
    phiW z * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * σw θ) with hGGdef
  have hUnn : ∀ z, 0 ≤ U z := fun z => by rw [hUdef]; exact uMass_nonneg u z
  have hUint' : MeasureTheory.IntegrableOn (fun z => phiW z * U z) Work.Spaces.Iz := by
    simpa only [hUdef] using hUint
  have hUUnn : 0 ≤ UU := by
    rw [hUUdef]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards with z
    exact mul_nonneg (phiW_nonneg z) (hUnn z)
  have hGGnn : 0 ≤ GG := by
    rw [hGGdef]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards with z
    exact mul_nonneg (phiW_nonneg z) (uMass_nonneg G z)
  -- the a.e. slice lower bound, transferred to `Iz`
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      -(K * U z) ≤ ∫ θ in Work.Spaces.Iθ,
          Work.Elliptic.Lzero u z θ * u z θ * σw θ := by
    have h0 := hKslice α u G hA
    rw [Work.Spaces.Iz, MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
    filter_upwards [h0] with z hz
    have hL1 : Work.FTS.EllipticEst.Lzero1 (fun θ => u z θ)
        = fun θ => Work.Elliptic.Lzero u z θ := by
      funext θ
      simp only [Work.FTS.EllipticEst.Lzero1, Work.Elliptic.Lzero,
        Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
    rw [hL1] at hz
    have hUz : U z = ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ := rfl
    rw [hUz]
    simpa using hz
  -- ## (1) the source pairing
  have hB1 : ∀ n : ℕ, (∫ z in Work.Spaces.Iz, χ n z * phiW z *
      (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * σw θ)) ≤ (1 / 2) * (GG + UU) := by
    intro n
    have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        |χ n z * phiW z * (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * σw θ)|
          ≤ (1 / 2) * (phiW z * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * σw θ)
              + phiW z * U z) := by
      filter_upwards [ae_pos_of_mem_Iz] with z hz
      have hτ := theta_pairing_le (f := fun θ => G z θ) (g := fun θ => u z θ)
        (hGslice z hz) (hUslice z hz)
      have hφ : 0 ≤ phiW z := phiW_nonneg z
      have hχ0 : 0 ≤ χ n z := (hχ01 n z).1
      have hχ1 : χ n z ≤ 1 := (hχ01 n z).2
      rw [abs_mul, abs_mul, abs_of_nonneg hφ, abs_of_nonneg hχ0]
      have hUeq : U z = ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ := by rw [hUdef]
      rw [hUeq]
      calc χ n z * phiW z * |∫ θ in Work.Spaces.Iθ, G z θ * u z θ * σw θ|
          ≤ (1 * phiW z) * ((1 / 2) * ((∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * σw θ)
              + (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ))) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_right hχ1 hφ) hτ
              (abs_nonneg _) (mul_nonneg zero_le_one hφ)
        _ = (1 / 2) * (phiW z * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * σw θ)
              + phiW z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ)) := by ring
    have hmono : (∫ z in Work.Spaces.Iz, |χ n z * phiW z *
          (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * σw θ)|)
        ≤ ∫ z in Work.Spaces.Iz, (1 / 2) * (phiW z *
            (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * σw θ) + phiW z * U z) := by
      have hsum : MeasureTheory.IntegrableOn (fun z => phiW z *
          (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * σw θ) + phiW z * U z) Work.Spaces.Iz :=
        hGint.add hUint'
      exact MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun z => abs_nonneg _) (hsum.const_mul (1 / 2)) hpt
    have hval : (∫ z in Work.Spaces.Iz, (1 / 2) * (phiW z *
          (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * σw θ) + phiW z * U z))
        = (1 / 2) * (GG + UU) := by
      rw [zIntegral_const_mul (1 / 2), MeasureTheory.integral_add hGint hUint',
        hGGdef, hUUdef]
    have h1 : (∫ z in Work.Spaces.Iz, χ n z * phiW z *
          (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * σw θ))
        ≤ |∫ z in Work.Spaces.Iz, χ n z * phiW z *
          (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * σw θ)| := le_abs_self _
    have h2 : |∫ z in Work.Spaces.Iz, χ n z * phiW z *
          (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * σw θ)|
        ≤ ∫ z in Work.Spaces.Iz, |χ n z * phiW z *
          (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * σw θ)| := by
      simpa only [Real.norm_eq_abs] using
        MeasureTheory.norm_integral_le_integral_norm (fun z => χ n z * phiW z *
          (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * σw θ))
    linarith [h1, h2, hmono, hval]
  -- ## (2) the angular self-form term
  have hB2 : ∀ n : ℕ, -(∫ z in Work.Spaces.Iz, χ n z * phiW z *
      (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ * σw θ)) ≤ K * UU := by
    intro n
    set σterm : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Elliptic.Lzero u z θ * u z θ * σw θ with hσterm
    by_cases hint : MeasureTheory.Integrable (fun z => χ n z * phiW z * σterm z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz)
    · have hneg : MeasureTheory.Integrable
          (fun z => -(χ n z * phiW z * σterm z))
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := hint.neg
      have hKint : MeasureTheory.Integrable
          (fun z => χ n z * phiW z * (K * U z))
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
        have haesm : MeasureTheory.AEStronglyMeasurable
            (fun z => χ n z * phiW z * (K * U z))
            (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
          have h1 : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => χ n z)
              (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
            ((hχdiff n).continuous).aestronglyMeasurable
          have h2 : MeasureTheory.AEStronglyMeasurable phiW
              (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
            aestronglyMeasurable_phiW
          have h3 : MeasureTheory.AEStronglyMeasurable U
              (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
            have hUU : AEMeasurable (fun z => phiW z * U z)
                (MeasureTheory.volume.restrict Work.Spaces.Iz) := hUint'.aemeasurable
            have hφm : AEMeasurable phiW
                (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
              aemeasurable_phiW
            have hquot : AEMeasurable (fun z => (phiW z * U z) / phiW z)
                (MeasureTheory.volume.restrict Work.Spaces.Iz) := hUU.div hφm
            refine hquot.aestronglyMeasurable.congr ?_
            filter_upwards [ae_pos_of_mem_Iz] with z hz
            have hφz : phiW z ≠ 0 := by
              rw [phiW]
              exact pow_ne_zero 2 (div_ne_zero (pow_ne_zero 2 (by linarith))
                (pow_ne_zero 2 hz.ne'))
            rw [mul_div_cancel_left₀ _ hφz]
          exact ((h1.mul h2).mul (h3.const_mul K))
        have hbdd : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
            ‖χ n z * phiW z * (K * U z)‖ ≤ K * (phiW z * U z) := by
          filter_upwards with z
          have hφ : 0 ≤ phiW z := phiW_nonneg z
          have hK0 : 0 ≤ K := le_of_lt hKpos
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hχ01 n z).1,
            abs_of_nonneg hφ, abs_of_nonneg (mul_nonneg hK0 (hUnn z))]
          calc χ n z * phiW z * (K * U z) ≤ 1 * phiW z * (K * U z) := by
                refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hK0 (hUnn z))
                exact mul_le_mul_of_nonneg_right (hχ01 n z).2 hφ
            _ = K * (phiW z * U z) := by ring
        exact Integrable.mono' (hUint'.const_mul K) haesm hbdd
      have hmono : (∫ z in Work.Spaces.Iz, -(χ n z * phiW z * σterm z))
          ≤ ∫ z in Work.Spaces.Iz, χ n z * phiW z * (K * U z) := by
        refine MeasureTheory.integral_mono_ae hneg hKint ?_
        filter_upwards [hslice] with z hz
        have hφ : 0 ≤ phiW z := phiW_nonneg z
        have hχ0 : 0 ≤ χ n z := (hχ01 n z).1
        have hprod : 0 ≤ χ n z * phiW z := mul_nonneg hχ0 hφ
        have hz' : -σterm z ≤ K * U z := by
          have hσz : σterm z = ∫ θ in Work.Spaces.Iθ,
              Work.Elliptic.Lzero u z θ * u z θ * σw θ := by simp only [hσterm]
          rw [hσz]; linarith [hz]
        calc -(χ n z * phiW z * σterm z) = χ n z * phiW z * (-σterm z) := by ring
          _ ≤ χ n z * phiW z * (K * U z) := mul_le_mul_of_nonneg_left hz' hprod
      have hval : (∫ z in Work.Spaces.Iz, χ n z * phiW z * (K * U z)) ≤ K * UU := by
        have h1 : (∫ z in Work.Spaces.Iz, χ n z * phiW z * (K * U z))
            ≤ ∫ z in Work.Spaces.Iz, K * (phiW z * U z) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun z =>
              mul_nonneg (mul_nonneg (hχ01 n z).1 (phiW_nonneg z))
                (mul_nonneg (le_of_lt hKpos) (hUnn z)))
            (hUint'.const_mul K) ?_
          filter_upwards with z
          have hφ : 0 ≤ phiW z := phiW_nonneg z
          have hK0 : 0 ≤ K := le_of_lt hKpos
          calc χ n z * phiW z * (K * U z) ≤ 1 * phiW z * (K * U z) := by
                refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hK0 (hUnn z))
                exact mul_le_mul_of_nonneg_right (hχ01 n z).2 hφ
            _ = K * (phiW z * U z) := by ring
        have h2 : (∫ z in Work.Spaces.Iz, K * (phiW z * U z)) = K * UU := by
          rw [zIntegral_const_mul K (fun z => phiW z * U z), hUUdef]
        linarith [h1, h2]
      have h3 : -(∫ z in Work.Spaces.Iz, χ n z * phiW z * σterm z)
          = ∫ z in Work.Spaces.Iz, -(χ n z * phiW z * σterm z) := by
        rw [MeasureTheory.integral_neg]
      linarith [hmono, hval, h3]
    · have hzero : (∫ z in Work.Spaces.Iz, χ n z * phiW z * σterm z) = 0 :=
        MeasureTheory.integral_undef hint
      have hpos : 0 ≤ K * UU := mul_nonneg (le_of_lt hKpos) hUUnn
      rw [hzero]; linarith [hpos]
  -- ## (3) the `(z²w²)''` term
  have hB3 : ∀ n : ℕ, (∫ z in Work.Spaces.Iz,
      deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z * U z) ≤ C0 * UU := by
    intro n
    have hb : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        |deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z| ≤ C0 * phiW z := by
      filter_upwards [ae_pos_of_mem_Iz] with z hz
      simpa only [phiW] using hχbd1 n z hz
    have h := weighted_le_of_bound
      (c := fun z => deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z)
      (m := U) (C := C0) (le_of_lt hC0pos) hUint' hUnn hb
    have h2 : |∫ z in Work.Spaces.Iz,
        deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z * U z| ≤ C0 * UU := by
      simpa only [hUUdef] using h
    linarith [le_abs_self (∫ z in Work.Spaces.Iz,
      deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z * U z), h2]
  -- ## (4) the `(zw²)'` term
  have hB4 : ∀ n : ℕ, -(∫ z in Work.Spaces.Iz,
      deriv (fun z => χ n z * phiW z * z) z * U z) ≤ C0 * UU := by
    intro n
    have hb : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        |deriv (fun z => χ n z * phiW z * z) z| ≤ C0 * phiW z := by
      filter_upwards [ae_pos_of_mem_Iz] with z hz
      simpa only [phiW] using hχbd2 n z hz
    have h := weighted_le_of_bound (c := fun z => deriv (fun z => χ n z * phiW z * z) z)
      (m := U) (C := C0) (le_of_lt hC0pos) hUint' hUnn hb
    have h2 : |∫ z in Work.Spaces.Iz,
        deriv (fun z => χ n z * phiW z * z) z * U z| ≤ C0 * UU := by
      simpa only [hUUdef] using h
    linarith [neg_le_abs (∫ z in Work.Spaces.Iz,
      deriv (fun z => χ n z * phiW z * z) z * U z), h2]
  -- ## the truncated identity
  have hident : ∀ n : ℕ,
      (∫ z in Work.Spaces.Iz, χ n z * phiW z *
          (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * σw θ))
        = α ^ 2 * (∫ z in Work.Spaces.Iz, χ n z * phiW z *
              (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ))
          + (∫ z in Work.Spaces.Iz, χ n z * phiW z *
              (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ * σw θ))
          - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
              deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z
                * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ))
          + ((α * (5 + α)) / 2) * (∫ z in Work.Spaces.Iz,
              deriv (fun z => χ n z * phiW z * z) z
                * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ)) := by
    intro n
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2n : (0 : ℝ) < ((n : ℝ) + 1) := by linarith
    have h1 := aeTruncSigmaIdD α u G hA (χ n) (1 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1))
      (by positivity)
      (by
        have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
          rw [div_le_one h2n]; linarith
        linarith)
      (hχdiff n) (hχsupp n) (fun z => hχ01 n z)
    simpa only [phiW] using h1
  -- ## combining into a uniform bound
  have hkey : ∀ n : ℕ, α ^ 2 * (∫ z in Work.Spaces.Iz, χ n z * phiW z *
        (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ))
      ≤ (1 / 2) * (GG + UU) + K * UU + (α ^ 2 / 2) * (C0 * UU)
        + ((α * (5 + α)) / 2) * (C0 * UU) := by
    intro n
    have hid := hident n
    have h1 := hB1 n
    have h2 := hB2 n
    have h3 := hB3 n
    have h4 := hB4 n
    have hc1 : 0 ≤ α ^ 2 / 2 := by positivity
    have hc2 : 0 ≤ (α * (5 + α)) / 2 := by nlinarith [hα0]
    have h3' : (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
        deriv (deriv (fun z => χ n z * phiW z * z ^ 2)) z
          * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ)) ≤ (α ^ 2 / 2) * (C0 * UU) :=
      mul_le_mul_of_nonneg_left h3 hc1
    have h4' : ((α * (5 + α)) / 2) * (-(∫ z in Work.Spaces.Iz,
        deriv (fun z => χ n z * phiW z * z) z
          * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ))) ≤ ((α * (5 + α)) / 2) * (C0 * UU) :=
      mul_le_mul_of_nonneg_left h4 hc2
    linarith [hid, h1, h2, h3', h4']
  -- ## the limit and the conclusion
  have hXeq : Work.Spaces.HkSq α 0 (grad u)
      = ∫ z in Work.Spaces.Iz, phiW z *
          (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ) := by
    simpa only [grad, phiW] using HkSq_eq_weighted α (grad u)
  have hlim : Filter.Tendsto (fun n => α ^ 2 * (∫ z in Work.Spaces.Iz, χ n z * phiW z *
        (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ)))
      Filter.atTop (nhds (α ^ 2 * Work.Spaces.HkSq α 0 (grad u))) := by
    rw [hXeq]
    exact (tendsto_radial_energy α u hA.smooth hXint χ hχdiff hχ01 hχlim).const_mul (α ^ 2)
  have hupper : α ^ 2 * Work.Spaces.HkSq α 0 (grad u)
      ≤ (1 / 2) * (GG + UU) + K * UU + (α ^ 2 / 2) * (C0 * UU)
        + ((α * (5 + α)) / 2) * (C0 * UU) :=
    le_of_tendsto' hlim hkey
  -- ## rewriting the two auxiliary scalars
  have hGGeq : GG = Work.Spaces.HkSq α 0 G := by
    rw [hGGdef, HkSq_eq_weighted α G]
  have hUUeq : UU = Work.Spaces.HkSq α 0 u := by
    rw [hUUdef, hUdef, ← HkSq_eq_weighted α u]
  have hGnn : 0 ≤ Work.Spaces.HkSq α 0 G := Work.Spaces.HkSq_nonneg α 0 G
  have hUnn'' : 0 ≤ Work.Spaces.HkSq α 0 u := Work.Spaces.HkSq_nonneg α 0 u
  rw [hGGeq, hUUeq] at hupper
  -- ## the constant
  have hα2le : α ^ 2 ≤ 1 / 16 := by
    have h := mul_le_mul hα4 hα4 hα0 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [pow_two]
    calc α * α ≤ (1 / 4 : ℝ) * (1 / 4) := h
      _ = 1 / 16 := by norm_num
  have hC1 : (α ^ 2 / 2) * (C0 * Work.Spaces.HkSq α 0 u)
      ≤ (1 / 2) * (C0 * Work.Spaces.HkSq α 0 u) := by
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (le_of_lt hC0pos) hUnn'')
    linarith
  have hC2 : ((α * (5 + α)) / 2) * (C0 * Work.Spaces.HkSq α 0 u)
      ≤ 1 * (C0 * Work.Spaces.HkSq α 0 u) := by
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (le_of_lt hC0pos) hUnn'')
    nlinarith [hα4, hα0]
  nlinarith [hupper, hC1, hC2, hGnn, hUnn'', hKpos, hC0pos, hα0, hα2le]

end Work.FTS.EllipticEst.Dispatch.SigmaRad

namespace Work.FTS.EllipticEst.Dispatch

/-- **The `σ`-weighted radial energy inequality of Step 1 of `prop:H2`** (Elgindi, Annals
194 (2021)) in the almost-everywhere class `Work.FTS.EllipticEst.H2W.Ae.AeData`, together with
the honesty of `z ∂_z u`:

`α² HkSq α 0 (z∂_zu) ≤ C (HkSq α 0 G + HkSq α 0 u)`.

This is the declaration of the required name `Work.FTS.EllipticEst.Dispatch.aeSigmaEnergyD`;
it is the `SigmaRad` theorem proved above in this file. -/
theorem aeSigmaEnergyD : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.L2Mem (fun z θ => z * Work.Spaces.pz u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ∧
      α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ C * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) :=
  Work.FTS.EllipticEst.Dispatch.SigmaRad.aeSigmaEnergyD

end Work.FTS.EllipticEst.Dispatch
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.W5Clean.sliceStep5Vg0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option autoImplicit false



end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.W5Clean.sliceStep5Vv0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open MeasureTheory Set Filter
open scoped Real Topology Interval

/-! ## The `v²`-weighted slice bound

This is the "light weight" companion of `slice_step5`: it bounds
`∫_{Iθ} (u/cos θ)² sin(2θ)^{2-γ}` by the same right-hand side as Step 5.

The whole content is the *pointwise* bound of `Work.FTS.EllipticEst.remov.div_cos_sq_le_M`,

  `(u θ / cos θ)² ≤ 100 ∫_{Iθ} (u'')² sEta`   for `θ ∈ (0, π/2)`,

together with the trivial estimate `sin(2θ)^{2-γ} ≤ 1` on `Iθ` (which holds because
`sin(2θ) ∈ [0,1]` there and `2 - γ ≥ 1/2 > 0`).  Integrating over the finite interval
`Iθ` therefore gives `≤ 100 · (π/2) · ∫ (u'')² sEta ≤ 200 · RHS`.  No Hardy inequality
and no use of the equation `Lzero1 u = g` is needed. -/
theorem sliceStep5Vv0 : ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
    1 ≤ γ → γ ≤ 3 / 2 →
    ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)) →
    ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
    u 0 = 0 → u (Real.pi / 2) = 0 →
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ))
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
              Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
  refine ⟨200, by norm_num, ?_⟩
  intro γ u g hγ1 hγ2 hu4 hucont hu0 hu1 hode hI4 hI3 hI2 hI1 hI0 hIg2
  have hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) := hu4.of_le (by norm_num)
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hsin_nn_Iθ : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  set M : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
    Work.FTS.EllipticEst.sEta θ with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.remov.sEta_nonneg_Iθ hθ))
  -- a.e. on `Iθ` the point lies in the open interval, where `div_cos_sq_le_M` applies
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    have h : Set.Icc (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) :=
      (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ))).symm
    rw [(show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl),
      MeasureTheory.Measure.restrict_congr_set h]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have hkey : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 100 * M := by
    filter_upwards [hae] with θ hθ
    have h1 : (u θ / Real.cos θ) ^ 2 ≤ 100 * M := by
      have h := Work.FTS.EllipticEst.remov.div_cos_sq_le_M u hu2 hucont hu0 hu1 hI2 θ hθ
      rwa [← hMdef] at h
    have hsin_nn : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hw_le : Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1 :=
      Real.rpow_le_one hsin_nn (Real.sin_le_one _) (by linarith)
    have hw_nn : 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) := Real.rpow_nonneg hsin_nn _
    calc (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ (100 * M) * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
          mul_le_mul_of_nonneg_right h1 hw_nn
      _ ≤ (100 * M) * 1 := mul_le_mul_of_nonneg_left hw_le (by linarith)
      _ = 100 * M := by ring
  have hvol : (volume : Measure ℝ) Work.Spaces.Iθ < ⊤ := by
    rw [(show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl), Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.AEStronglyMeasurable.mul ?_ ?_
    · exact ((MeasureTheory.AEStronglyMeasurable.div₀
        (hucont.aestronglyMeasurable hIθ_meas)
        (Real.continuous_cos.measurable.aestronglyMeasurable)).pow 2)
    · exact ((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 - γ)).measurable.comp
        (Real.continuous_sin.measurable.comp
          (continuous_const.mul continuous_id).measurable)).aestronglyMeasurable
  have hkey' : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      ‖(u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)‖ ≤ 100 * M := by
    filter_upwards [hkey, hae] with θ h1 hθ
    have hnn : 0 ≤ (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact h1
  have hLHS_int : MeasureTheory.IntegrableOn
      (fun θ => (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.of_bound hvol haesm (100 * M) hkey'
  have hconst_int : MeasureTheory.IntegrableOn (fun _ : ℝ => (100 * M : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.of_bound hvol MeasureTheory.aestronglyMeasurable_const (100 * M)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hM0] : (0 : ℝ) ≤ 100 * M)])
  have hvolreal : (volume : Measure ℝ).real Work.Spaces.Iθ = Real.pi / 2 := by
    rw [MeasureTheory.Measure.real_def,
      (show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl), Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), sub_zero]
  have hLHS_le : (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) ≤ 100 * M * (Real.pi / 2) := by
    calc (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ))
        ≤ ∫ _θ in Work.Spaces.Iθ, (100 * M : ℝ) :=
          MeasureTheory.integral_mono_ae hLHS_int hconst_int hkey
      _ = 100 * M * (Real.pi / 2) := by
          rw [MeasureTheory.setIntegral_const, hvolreal, smul_eq_mul]; ring
  have hB2_0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ) :=
    MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin_nn_Iθ θ hθ) _))
  have hA3_0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
    MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin_nn_Iθ θ hθ) _))
  have hA1_0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg hIθ_meas (fun θ _ => sq_nonneg _)
  have hA0_0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg hIθ_meas (fun θ _ => sq_nonneg _)
  have hMleR : M ≤ (((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) +
        ∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)) + M +
        ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2) +
      ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 := by
    linarith [hB2_0, hA3_0, hA1_0, hA0_0]
  have hpi_le : 100 * (Real.pi / 2) ≤ 200 := by nlinarith [Real.pi_lt_four]
  calc (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ))
      ≤ 100 * M * (Real.pi / 2) := hLHS_le
    _ = (100 * (Real.pi / 2)) * M := by ring
    _ ≤ 200 * M := mul_le_mul_of_nonneg_right hpi_le hM0
    _ ≤ 200 * ((((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)) +
          ∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 - γ)) + M +
          ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2) +
        ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hMleR (by norm_num)

end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.W5Clean.sliceStep5Vv1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open MeasureTheory Set Filter
open scoped Real Topology Interval

/-- The `(∂_θ(u/cos θ))²`-weighted slice bound of Step 5.

The content is `Work.FTS.EllipticEst.remov.slice5_vweight_le`, which bounds
`∫_{Iθ} (∂_θ(u/cos θ))² sin(2θ)^{4-γ'}` by a universal multiple of
`∫ (u'')² sEta + ∫ (u')² + ∫ u²`, with a constant that is *independent* of `γ'`
(namely `2000`) but which is only exposed to us existentially.  We therefore
instantiate it at the largest admitted exponent `γ' = 3/2` (weight `sin(2θ)^{5/2}`,
the smallest of the weights `sin(2θ)^{4-γ}`, `γ ∈ [1, 3/2]`, because `sin(2θ) ≤ 1`
on `Iθ`) and add the two nonnegative Step 5 terms `∫(g'')²ψ`,
`∫(u''')² sin(2θ)^{2-γ}` to the right-hand side. -/
theorem sliceStep5Vv1 : ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
    1 ≤ γ → γ ≤ 3 / 2 →
    ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)) →
    ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
    u 0 = 0 → u (Real.pi / 2) = 0 →
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
              Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    Work.FTS.EllipticEst.remov.slice5_vweight_le (3 / 2) (by norm_num) le_rfl
  refine ⟨C₁ + 1, by linarith, ?_⟩
  intro γ u g hγ1 hγ2 hu4 hucont hu0 hu1 hode hI4 hI3 hI2 hI1 hI0 hIg2
  obtain ⟨_, hFv_int32, _, hFv_bnd⟩ :=
    hC₁ u (hu4.of_le (by norm_num)) hucont hu0 hu1 hI2 hI1 hI0
  -- elementary facts about the interval and the weight
  have hIθ_eq : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) := rfl
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
    rw [hIθ_eq]; exact measurableSet_Icc
  have hsin2_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    rw [hIθ_eq] at hθ
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    have h : Set.Icc (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) :=
      (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ))).symm
    rw [hIθ_eq, MeasureTheory.Measure.restrict_congr_set h]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have hsin2pos_of_mem_Ioo : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  -- `sin(2θ)^{4-γ} ≤ sin(2θ)^{4-3/2}` on the open interval
  have hpt : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      (deriv (fun t => u t / Real.cos t) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
        ≤ (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - 3 / 2) := by
    filter_upwards [hae] with θ hθ
    have hs := hsin2pos_of_mem_Ioo θ hθ
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hexp : 4 - 3 / 2 ≤ 4 - γ := by linarith
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hs hs1 hexp)
      (sq_nonneg _)
  -- integrability of the `γ`-weighted integrand, by domination through the `3/2` one
  have hFv_int : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono hFv_int32 ?_ ?_
    · refine MeasureTheory.AEStronglyMeasurable.mul ?_ ?_
      · exact ((measurable_deriv (fun t => u t / Real.cos t)).pow_const 2).aestronglyMeasurable
      · exact ((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 4 - γ)).measurable.comp
          (Real.continuous_sin.measurable.comp
            (continuous_const.mul continuous_id).measurable)).aestronglyMeasurable
    · filter_upwards [hpt, hae] with θ hθ hθ'
      have hs := hsin2pos_of_mem_Ioo θ hθ'
      have h1 : (0 : ℝ) ≤ deriv (fun t => u t / Real.cos t) θ ^ 2 *
          (Real.sin (2 * θ)).rpow (4 - γ) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _)
      have h2 : (0 : ℝ) ≤ deriv (fun θ' => u θ' / Real.cos θ') θ ^ 2 *
          (Real.sin (2 * θ)).rpow (4 - 3 / 2) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg h2]
      exact hθ
  have hcmp := MeasureTheory.integral_mono_ae hFv_int hFv_int32 hpt
  -- nonnegativity of the five right-hand-side integrals
  have hA2nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.remov.sEta_nonneg_Iθ hθ))
  have hA1nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg hIθ_meas (fun θ _ => sq_nonneg _)
  have hA0nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg hIθ_meas (fun θ _ => sq_nonneg _)
  have hB2nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ) :=
    MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin2_nn θ hθ) _))
  have hA3nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
    MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin2_nn θ hθ) _))
  -- the mild amplification of the right-hand side
  have hPQ : (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ)
      + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
      + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
      ≤ (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
              Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) := by
    linarith [hB2nn, hA3nn]
  have hP0 : 0 ≤ (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ)
      + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
      + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) := by
    linarith [hA2nn, hA1nn, hA0nn]
  have hstep : C₁ * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ)
      + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
      + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2))
      ≤ (C₁ + 1) * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
              Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) :=
    mul_le_mul (by linarith : C₁ ≤ C₁ + 1) hPQ hP0 (by linarith : (0 : ℝ) ≤ C₁ + 1)
  calc (∫ θ in Work.Spaces.Iθ, (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ (∫ θ in Work.Spaces.Iθ, (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - 3 / 2)) := hcmp
    _ ≤ C₁ * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
            Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := hFv_bnd
    _ ≤ (C₁ + 1) * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
              Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := hstep

end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Mine.CutoffPieces.momentChainZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Mine.CutoffPieces

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary angular helpers -/



/-- `sinθcos²θ ≥ 0` on `Iθ`. -/
private lemma sinCos2_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  obtain ⟨h0, h1⟩ := hθ
  rw [Work.Elliptic.sinCos2]
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨h0, by linarith [h1, Real.pi_pos]⟩
  positivity

/-- The angular profile is continuous. -/
private lemma continuous_sinCos2 : Continuous (fun θ : ℝ => Work.Elliptic.sinCos2 θ) := by
  show Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
  fun_prop

/-- The level-`0` `HkIntegrand` is the single weighted square. -/
private lemma HkIntegrand_zero_eq' (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand, Work.Spaces.DzIter_zero]

/-- `sEta` is nonnegative on `Iθ`. -/
private lemma sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  refine Real.rpow_nonneg ?_ _
  refine Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]


/-! ## The `Ψ`-slice is `L¹` against the angular profile -/


/-! ## The `∂_z²Ψ`-integrand: slice and box integrability -/






/-! ## The first moment: rectangle integrability and vanishing of its interval integrals -/




/-! ## An interval-vanishing criterion -/



/-! ## The second moment -/



/-- **A primitive-constancy criterion.**  If `g` vanishes a.e. on `(z₀,∞)`, `f` is locally
integrable there and `∫_a^b f = g b - g a` for all `z₀ ≤ a < b`, then `f` vanishes a.e. on
`(z₀,∞)`: its primitive `Q(z) = ∫_{z₀}^z f` is a.e. equal to the constant `-g z₀`, hence (being
continuous) identically equal to it, so `f = Q' = 0` a.e. by the Lebesgue differentiation
theorem. -/
theorem ae_zero_of_primitive_const {f g : ℝ → ℝ} {z₀ : ℝ} (hz₀ : 0 < z₀)
    (hint : ∀ a b : ℝ, z₀ ≤ a → a < b → IntervalIntegrable f MeasureTheory.volume a b)
    (hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi z₀)), g z = 0)
    (hrel : ∀ a b : ℝ, z₀ ≤ a → a < b → ∫ t in a..b, f t = g b - g a) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi z₀)), f z = 0 := by
  set Q : ℝ → ℝ := fun z => ∫ t in z₀..z, f t with hQ
  -- `Q` is constant on `[z₀,∞)`
  have hQconst : ∀ z : ℝ, z₀ ≤ z → Q z = -g z₀ := by
    intro z hz
    have hy : z₀ < max z (z₀ + 1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hzy : z ∈ Set.Icc z₀ (max z (z₀ + 1)) := ⟨hz, le_max_left _ _⟩
    have hIntv : MeasureTheory.IntegrableOn f (Set.Icc z₀ (max z (z₀ + 1))) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hy.le).mp (hint z₀ _ le_rfl hy)
    have hcont : ContinuousOn Q (Set.Icc z₀ (max z (z₀ + 1))) := by
      have h2 : Set.uIcc z₀ (max z (z₀ + 1)) = Set.Icc z₀ (max z (z₀ + 1)) :=
        Set.uIcc_of_le hy.le
      have h3 : MeasureTheory.IntegrableOn f (Set.uIcc z₀ (max z (z₀ + 1))) := by
        rw [h2]; exact hIntv
      simpa only [h2] using intervalIntegral.continuousOn_primitive_interval h3
    have hae' : Q =ᵐ[MeasureTheory.volume.restrict (Set.Icc z₀ (max z (z₀ + 1)))]
        (fun _ => -g z₀) := by
      have hg : ∀ᵐ w ∂(MeasureTheory.volume.restrict
          (Set.Icc z₀ (max z (z₀ + 1)))), g w = 0 := by
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at hae
        have hne : ∀ᵐ w : ℝ, w ≠ z₀ := by rw [MeasureTheory.ae_iff]; simp
        filter_upwards [hae, hne] with w hw hwne hwmem
        exact hw (lt_of_le_of_ne hwmem.1 (Ne.symm hwne))
      filter_upwards [hg, MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with w hw hwmem
      rcases eq_or_lt_of_le hwmem.1 with h | h
      · rw [← h] at hw ⊢
        show ∫ t in z₀..z₀, f t = -g z₀
        rw [intervalIntegral.integral_same, hw]; ring
      · show ∫ t in z₀..w, f t = -g z₀
        rw [hrel z₀ w le_rfl h, hw]; ring
    have hEq := MeasureTheory.Measure.eqOn_of_ae_eq hae' hcont
      (continuousOn_const : ContinuousOn (fun _ : ℝ => -g z₀) _)
      (fun x hx => by
        rw [interior_Icc, closure_Ioo (ne_of_lt hy)]
        exact hx)
    exact hEq hzy
  -- the Lebesgue differentiation theorem identifies `f` with `Q'`
  have hstep : ∀ y : ℝ, z₀ < y →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Icc z₀ y)), f x = 0 := by
    intro y hy
    have hldt := IntervalIntegrable.ae_hasDerivAt_integral (hint z₀ y le_rfl hy)
    rw [Set.uIcc_of_le hy.le] at hldt
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    have hne : ∀ᵐ x : ℝ, x ≠ z₀ := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hldt, hne] with x hx hxne hxmem
    have hxz : z₀ < x := lt_of_le_of_ne hxmem.1 (Ne.symm hxne)
    have hder : HasDerivAt Q (f x) x := hx hxmem z₀ ⟨le_rfl, hy.le⟩
    have hfun : (fun _ : ℝ => -g z₀) =ᶠ[𝓝 x] Q := by
      filter_upwards [isOpen_Ioi.mem_nhds hxz] with y' hy'
      exact (hQconst y' hy'.le).symm
    have hder0 : HasDerivAt (fun _ : ℝ => -g z₀) (f x) x :=
      hder.congr_of_eventuallyEq hfun
    exact hder0.unique (hasDerivAt_const x (-g z₀))
  -- cover `(z₀,∞)` by the intervals `[z₀, z₀+n+1]`
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi, MeasureTheory.ae_iff]
  have hbad : MeasureTheory.volume {z : ℝ | z₀ < z ∧ f z ≠ 0} = 0 := by
    have hsub : {z : ℝ | z₀ < z ∧ f z ≠ 0} ⊆ ⋃ n : ℕ,
        ({z : ℝ | f z ≠ 0} ∩ Set.Icc z₀ (z₀ + (n : ℝ) + 1)) := by
      intro z hz
      obtain ⟨n, hn⟩ := exists_nat_ge (z - z₀)
      exact Set.mem_iUnion.mpr ⟨n, hz.2, le_of_lt hz.1, by linarith⟩
    refine le_antisymm ?_ bot_le
    calc MeasureTheory.volume {z : ℝ | z₀ < z ∧ f z ≠ 0}
        ≤ MeasureTheory.volume (⋃ n : ℕ,
            ({z : ℝ | f z ≠ 0} ∩ Set.Icc z₀ (z₀ + (n : ℝ) + 1))) :=
          MeasureTheory.measure_mono hsub
      _ ≤ ∑' n : ℕ, MeasureTheory.volume ({z : ℝ | f z ≠ 0}
            ∩ Set.Icc z₀ (z₀ + (n : ℝ) + 1)) := MeasureTheory.measure_iUnion_le _
      _ = 0 := by
          refine ENNReal.tsum_eq_zero.mpr (fun n => ?_)
          have hy : z₀ < z₀ + (n : ℝ) + 1 := by
            have : (0 : ℝ) ≤ (n : ℝ) := by positivity
            linarith
          have h := hstep (z₀ + (n : ℝ) + 1) hy
          rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff] at h
          convert h using 2
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Icc, not_imp]
          tauto
  have hset : {z : ℝ | ¬(z ∈ Set.Ioi z₀ → f z = 0)} = {z : ℝ | z₀ < z ∧ f z ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Ioi, not_imp]
  rw [hset]
  exact hbad



end Work.FTS.EllipticEst.Mine.CutoffPieces
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.fk_contDiffOn_four =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.RNP24

set_option autoImplicit false

/-! ## The shift `f ↦ D_z f` at the level of the tower -/

/-- `SmoothQuad` is closed under `D_z = z ∂_z` (`Work.FTS.LocData.contDiffOn_Dz`). -/
theorem smoothQuad_Dz {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) :
    Work.FTS.LocData.SmoothQuad (Work.Spaces.Dz f) :=
  Work.FTS.LocData.contDiffOn_Dz Work.Spaces.isOpen_quadU hf



/-! ## The differentiation tower -/


/-! ## The target -/


end Work.FTS.Nonlinear.Pieces.RNP.RNP24
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row10aux.Rop_PhiTs_smoothQuad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `SmoothQuad (ℛ(Φ̃_*))` for an `SmoothQuad` datum `Φ_s`

Row 10 of the design table needs the *coefficient* `ℛ(Φ̃_*)` of the nonlinear term `N₁^{*g}`
to be smooth on the open quadrant: this file supplies exactly that,
`Rop_PhiTs_smoothQuad`.

Two observations do the work, and both are elementary.

* `ℛ` is a rational expression in `Ψ`, `∂_zΨ`, `∂_θΨ` and `sin θ`, `cos θ`, divided by
  `cos θ`.  On the open quadrant `θ ∈ (0, π/2)` every one of those ingredients is `C^∞`
  (`Work.FTS.LocData.contDiffOn_pz`/`contDiffOn_pth` for the two derivatives, and
  `cos θ ≠ 0` for the division), so `ℛ` preserves `SmoothQuad`.

* `Φ̃_* = Φ_s - Θ_*(α)` with `Θ_*(α) = (1/(4α)) sin(2θ) L₁₂(F_*)(z)`.  The profile identity
  `L₁₂(F_*)(z) = 2α/(1+z)` (valid on the whole range `z > -1`, which is the range of
  `SmoothQuad`: `Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one`) turns `Θ_*(α)` into
  the completely explicit `sin(2θ)/(2(1+z))`, which is visibly `C^∞` on the open quadrant.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row10aux

set_option autoImplicit false

/-! ## `ℛ` preserves `SmoothQuad` -/

/-- **The operator `ℛ` preserves `C^∞`-smoothness on the open quadrant.**  The only point to
check is that the division by `cos θ` is legitimate there: on `quadU` the angle lies in
`(0, π/2)`, where `cos` is strictly positive.  All the remaining factors are the smooth
functions `sin θ`, `cos θ`, `z`, the datum `Ψ` itself, and its two first derivatives
(`contDiffOn_pz`, `contDiffOn_pth`). -/
theorem smoothQuad_Rop {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.LocData.SmoothQuad Ψ) :
    Work.FTS.LocData.SmoothQuad (Work.Construction.Rop α Ψ) := by
  have hpz : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz Ψ)) Work.Spaces.quadU :=
    Work.FTS.LocData.contDiffOn_pz Work.Spaces.isOpen_quadU hΨ
  have hpth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth Ψ)) Work.Spaces.quadU :=
    Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU hΨ
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2) Work.Spaces.quadU :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2) Work.Spaces.quadU :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p) Work.Spaces.quadU :=
    (contDiffOn_const.mul hsin).mul hΨ
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p)
      Work.Spaces.quadU :=
    ((contDiffOn_const.mul hsin).mul contDiffOn_fst).mul hpz
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p)
      Work.Spaces.quadU :=
    hcos.mul hpth
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p
        + α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p
        + Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p) Work.Spaces.quadU :=
    (h1.add h2).add h3
  have hne : ∀ p ∈ Work.Spaces.quadU, Real.cos p.2 ≠ 0 := by
    intro p hp
    have hpos : 0 < Real.cos p.2 :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [(Set.mem_Ioo.mp hp.2).1, Real.pi_pos], (Set.mem_Ioo.mp hp.2).2⟩
    exact ne_of_gt hpos
  refine (hnum.div hcos hne).congr ?_
  intro p _
  obtain ⟨z, θ⟩ := p
  rfl

/-! ## The singular part `Θ_*(α) = Θ α (F_*)` of `Φ̃_*` -/

/-- **`Θ_*(α)` is `C^∞` on the open quadrant.**  By the profile identity
`L₁₂(F_*)(z) = 2α/(1+z)` (valid for every `z > -1`) it is the explicit function
`(z, θ) ↦ sin(2θ)/(2(1+z))`, which is smooth there because the denominator `2(1+z)` is
positive. -/
theorem smoothQuad_Theta_Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.LocData.SmoothQuad (Work.Construction.Theta α (Work.Construction.Fstar α)) := by
  have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) / (2 * (1 + p.1))) Work.Spaces.quadU := by
    have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.Spaces.quadU :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hden : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => 2 * (1 + p.1)) Work.Spaces.quadU :=
      contDiffOn_const.mul (contDiffOn_const.add contDiffOn_fst)
    have hne : ∀ p ∈ Work.Spaces.quadU, 2 * (1 + p.1) ≠ 0 := by
      intro p hp
      have hp1 : (0 : ℝ) < 1 + p.1 := by
        have := Set.mem_Ioi.mp hp.1; linarith
      positivity
    exact hnum.div hden hne
  refine hsmooth.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hz : -1 < z := Set.mem_Ioi.mp hp.1
  simp only [Function.uncurry, Work.Construction.Theta, Work.Construction.s2]
  rw [Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 hz]
  field_simp
  ring

/-! ## The target -/


end Work.FTS.Nonlinear.Pieces.RNP.row10aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Assembly6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.WProd6

open Work.Spaces
open Work.FTS.EllipticEst (SmoothOpen)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- `√(x⁻¹) = x^(-1/2)` for `x > 0`. -/
theorem sqrt_inv_eq_rpow_neg_half6 {x : ℝ} (hx : 0 < x) :
    Real.sqrt x⁻¹ = x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hx.le]
  congr 1
  ring

/-- **The measure-theoretic assembly of the `𝒲^{6,∞}`-priced product rule**, from the three
slot lemmas. -/
theorem wprod6_of_slots
    (hZ : ∃ Cz : ℝ, 0 < Cz ∧
      ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
        Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
        Work.FTS.EllipticEst.SmoothOpen g →
        ∀ i : ℕ, i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ Cz * (Work.Spaces.WlInf α 6 f) ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ)
    (hMe : ∃ CB : ℝ, 0 < CB ∧
      ∀ (α : ℝ) (g : ℝ → ℝ → ℝ) (d : ℕ), 0 < α → α ≤ 1 →
        Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g → d ≤ 5 →
        ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
          ≤ CB * ((Work.Spaces.w z) ^ 2
                * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
              + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z))
    (hMx : ∀ CB : ℝ, ∃ Cm : ℝ, 0 < Cm ∧
      ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
        Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
        Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
        (∀ d : ℕ, d ≤ 5 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
            ≤ CB * ((Work.Spaces.w z) ^ 2
                  * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
                + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z)) →
        ∀ I J : ℕ, 1 ≤ I → I + J ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Cm * (Work.Spaces.WlInf α 6 f) ^ 2
              * GmajW6 α g z θ) :
    ∃ Ci α₂ : ℝ, 0 < Ci ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Work.FTS.Galerkin.Fn,
        Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
        Work.FTS.VocabO.HQo α 6 g →
        Work.Spaces.HkMem α 6 (fun z θ => f z θ * g z θ) ∧
        Work.Spaces.HkNorm α 6 (fun z θ => f z θ * g z θ)
          ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 6 f
              * Work.Spaces.HkNorm α 6 g := by
  obtain ⟨Cz, hCz0, hzslot⟩ := hZ
  obtain ⟨CB, hCB0, hCmean⟩ := hMe
  obtain ⟨Cm, hCm0, hmslot⟩ := hMx CB
  refine ⟨Real.sqrt (42701 * (7 * Cz + 49 * Cm)) + 1, 1, by positivity, by norm_num, ?_⟩
  intro α hαIoc f g hf hfm hg
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  obtain ⟨hgsm, hgm⟩ := hg
  set K : ℝ := 7 * Cz + 49 * Cm with hKdef
  set Kg : ℝ := 1 + 700 * (1 + 6 * (gam α - 1)⁻¹) with hKgdef
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hKgpos : 0 < Kg := by
    rw [hKgdef]
    have h1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
    have h2 : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr h1.le
    linarith
  have hWnn : 0 ≤ WlInf α 6 f := WlInf_nonneg α 6 f hfm
  have hfgsm : SmoothOpen (fun z θ => f z θ * g z θ) := hf.mul hgsm
  -- the pointwise majorant, with the two slot lemmas instantiated
  have hmajor : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ
        ≤ K * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ := by
    have h := prod_majorant_winf6 hα hα1 hf hfm hgsm hgm hCz0 hCm0
      (fun i hi z θ hz hθ1 hθ2 => hzslot α f g hα hα1 hf hfm hgsm i hi z θ hz hθ1 hθ2)
      (fun I J hI hIJ z θ hz hθ1 hθ2 =>
        hmslot α f g hα hα1 hf hfm hgsm hgm
          (fun d hd z' θ' hz' hθ1' hθ2' => hCmean α g d hα hα1 hgsm hgm hd z' θ' hz' hθ1' hθ2')
          I J hI hIJ z θ hz hθ1 hθ2)
    intro z hz θ hθ
    rw [hKdef]
    exact h z hz θ hθ
  -- integrability of the angular slices of the product's integrand
  have hslice : ∀ z ∈ Iz, IntegrableOn (fun θ => HkIntegrand α 6
      (fun z θ => f z θ * g z θ) z θ) Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
    · have hz0 : z = 0 := hzz.symm
      subst hz0
      have hzero : (fun θ => HkIntegrand α 6 (fun z θ => f z θ * g z θ) 0 θ)
          = fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => HkIntegrand_zero_z α 6 _ θ
      rw [hzero]
      exact integrableOn_zero
    · refine Integrable.mono'
        ((GmajW6_integrableOn_theta hα hα1 hgm hz).const_mul (K
          * (WlInf α 6 f) ^ 2)) ?_ ?_
      · exact aesm_slice_of_continuousOn_Qd _
          (hfgsm.continuousOn_HkIntegrand α 6) hzpos
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        rw [Real.norm_of_nonneg (HkIntegrand_nonneg α 6 _ z θ)]
        exact hmajor z hz θ hθ
  -- the angular integral of the majorant at every radius
  have hinner : ∀ z ∈ Iz,
      (∫ θ in Iθ, HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ K * (WlInf α 6 f) ^ 2 * (Kg * HgInt6 α g z) := by
    intro z hz
    have hint : IntegrableOn (fun θ => (K * (WlInf α 6 f) ^ 2)
        * GmajW6 α g z θ) Iθ :=
      (GmajW6_integrableOn_theta hα hα1 hgm hz).const_mul _
    have h1 : (∫ θ in Iθ, HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ ∫ θ in Iθ, (K * (WlInf α 6 f) ^ 2) * GmajW6 α g z θ :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun θ => HkIntegrand_nonneg α 6 _ z θ) hint
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hmajor z hz θ hθ))
    rw [MeasureTheory.integral_const_mul] at h1
    have h2 : (∫ θ in Iθ, GmajW6 α g z θ) ≤ Kg * HgInt6 α g z := by
      simpa only [hKgdef] using GmajW6_theta_integral_le (α := α) (g := g) hα hα1 hgm hz
    calc (∫ θ in Iθ, HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (WlInf α 6 f) ^ 2) * (∫ θ in Iθ, GmajW6 α g z θ) := h1
      _ ≤ (K * (WlInf α 6 f) ^ 2) * (Kg * HgInt6 α g z) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hKpos.le (sq_nonneg _))
  -- the dominating function of the `z`-integral
  have hbdd : ∀ z ∈ Iz,
      (∫ θ in Iθ, HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (WlInf α 6 f) ^ 2 * Kg) * HgInt6 α g z := by
    intro z hz
    have h1 := hinner z hz
    calc (∫ θ in Iθ, HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ K * (WlInf α 6 f) ^ 2 * (Kg * HgInt6 α g z) := h1
      _ = (K * (WlInf α 6 f) ^ 2 * Kg) * HgInt6 α g z := by ring
  have hdom : IntegrableOn (fun z => (K * (WlInf α 6 f) ^ 2 * Kg)
      * HgInt6 α g z) Iz :=
    hgm.2.const_mul (K * (WlInf α 6 f) ^ 2 * Kg)
  -- a.e. strong measurability of the `z`-slice integral
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Iθ,
      HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
      (volume.restrict Iz) := by
    have h := (aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => HkIntegrand α 6 (fun z θ => f z θ * g z θ) p.1 p.2)
      (hfgsm.continuousOn_HkIntegrand α 6)).integral_prod_right'
    have hfun : (fun z => ∫ θ, HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ
          ∂(volume.restrict Iθ))
        = (fun z => ∫ θ in Iθ,
            HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ) := rfl
    rw [← hfun]
    exact h
  have hzg : IntegrableOn (fun z => ∫ θ in Iθ,
      HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ) Iz := by
    refine Integrable.mono' hdom haesm ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ =>
      HkIntegrand_nonneg α 6 _ z θ)]
    exact hbdd z hz
  refine ⟨⟨hslice, hzg⟩, ?_⟩
  have hSq : HkSq α 6 (fun z θ => f z θ * g z θ)
      ≤ (K * (WlInf α 6 f) ^ 2 * Kg) * HkSq α 6 g := by
    have h1 : HkSq α 6 (fun z θ => f z θ * g z θ)
        ≤ ∫ z in Iz, (K * (WlInf α 6 f) ^ 2 * Kg) * HgInt6 α g z := by
      rw [HkSq]
      exact setIntegral_mono_of_nonneg
        (fun z _ => integral_nonneg fun θ => HkIntegrand_nonneg α 6 _ z θ)
        (fun z hz => hbdd z hz) hdom
    refine le_trans h1 ?_
    rw [MeasureTheory.integral_const_mul, HgInt6_z_integral]
  -- the passage to the `ℋ⁶`-norm
  have hXn : HkNorm α 6 (fun z θ => f z θ * g z θ)
      ≤ Real.sqrt (K * Kg) * WlInf α 6 f * HkNorm α 6 g := by
    have h1 : HkNorm α 6 (fun z θ => f z θ * g z θ)
        ≤ Real.sqrt ((K * Kg) * (WlInf α 6 f) ^ 2 * HkSq α 6 g) := by
      rw [show HkNorm α 6 (fun z θ => f z θ * g z θ)
            = Real.sqrt (HkSq α 6 (fun z θ => f z θ * g z θ)) from rfl]
      refine Real.sqrt_le_sqrt ?_
      calc HkSq α 6 (fun z θ => f z θ * g z θ)
          ≤ (K * (WlInf α 6 f) ^ 2 * Kg) * HkSq α 6 g := hSq
        _ = (K * Kg) * (WlInf α 6 f) ^ 2 * HkSq α 6 g := by ring
    refine le_trans h1 (le_of_eq ?_)
    rw [show HkNorm α 6 g = Real.sqrt (HkSq α 6 g) from rfl,
      Real.sqrt_mul (show (0 : ℝ) ≤ (K * Kg) * (WlInf α 6 f) ^ 2 by positivity),
      Real.sqrt_mul (show (0 : ℝ) ≤ K * Kg by positivity),
      Real.sqrt_sq hWnn]
  refine le_trans hXn ?_
  -- `√(K Kg) ≤ √(42701 K) α^{-1/2}`
  have hKg_le : Kg ≤ 42701 * α⁻¹ := by
    have h1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
    have hginv : (gam α - 1)⁻¹ = 10 / α := by
      rw [gam_sub_one, inv_div]
    have hαinv : (1 : ℝ) ≤ α⁻¹ := by rw [one_le_inv₀ hα]; exact hα1
    rw [hKgdef, hginv, div_eq_mul_inv]
    ring_nf
    nlinarith [hαinv]
  have hsqrt : Real.sqrt (K * Kg) ≤ Real.sqrt (42701 * K) * α ^ (-(1 / 2 : ℝ)) := by
    have h1 : K * Kg ≤ 42701 * K * α⁻¹ := by
      calc K * Kg ≤ K * (42701 * α⁻¹) := mul_le_mul_of_nonneg_left hKg_le hKpos.le
        _ = 42701 * K * α⁻¹ := by ring
    refine le_trans (Real.sqrt_le_sqrt h1) ?_
    rw [show (42701 : ℝ) * K * α⁻¹ = (42701 * K) * α⁻¹ from by ring,
      Real.sqrt_mul (show (0 : ℝ) ≤ 42701 * K by positivity),
      sqrt_inv_eq_rpow_neg_half6 hα]
  have hmain : Real.sqrt (K * Kg) * WlInf α 6 f * HkNorm α 6 g
      ≤ Real.sqrt (42701 * K) * α ^ (-(1 / 2 : ℝ)) * WlInf α 6 f
        * HkNorm α 6 g := by
    calc Real.sqrt (K * Kg) * WlInf α 6 f * HkNorm α 6 g
        = Real.sqrt (K * Kg) * (WlInf α 6 f * HkNorm α 6 g) := by ring
      _ ≤ (Real.sqrt (42701 * K) * α ^ (-(1 / 2 : ℝ)))
            * (WlInf α 6 f * HkNorm α 6 g) :=
          mul_le_mul_of_nonneg_right hsqrt (mul_nonneg hWnn (Real.sqrt_nonneg _))
      _ = Real.sqrt (42701 * K) * α ^ (-(1 / 2 : ℝ)) * WlInf α 6 f
            * HkNorm α 6 g := by ring
  calc Real.sqrt (K * Kg) * WlInf α 6 f * HkNorm α 6 g
      ≤ Real.sqrt (42701 * K) * α ^ (-(1 / 2 : ℝ)) * WlInf α 6 f
          * HkNorm α 6 g := hmain
    _ = Real.sqrt (42701 * (7 * Cz + 49 * Cm)) * α ^ (-(1 / 2 : ℝ))
          * WlInf α 6 f * HkNorm α 6 g := by rw [hKdef]
    _ ≤ (Real.sqrt (42701 * (7 * Cz + 49 * Cm)) + 1) * α ^ (-(1 / 2 : ℝ))
          * WlInf α 6 f * HkNorm α 6 g := by
        have h1 : (0 : ℝ) ≤ Real.sqrt (42701 * (7 * Cz + 49 * Cm)) := Real.sqrt_nonneg _
        have h2 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
        have h3 : (0 : ℝ) ≤ WlInf α 6 f := hWnn
        have h4 : (0 : ℝ) ≤ HkNorm α 6 g := Real.sqrt_nonneg _
        nlinarith [mul_nonneg (mul_nonneg h2 h3) h4,
          mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4]

end Work.FTS.StrongPersist.H6Rows.WProd6
end
end
