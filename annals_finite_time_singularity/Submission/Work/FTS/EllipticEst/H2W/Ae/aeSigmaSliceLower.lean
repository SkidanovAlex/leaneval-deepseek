import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.HkMemGradU
import Submission.Work.FTS.EllipticEst.Honest.HonSliceSigmaLower
import Submission.Work.FTS.EllipticEst.Honest.I4UpperHonest
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongPersist.N6.Swap6
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.QDefs
import Submission.Work.H2W.momentChainAe
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.AeStepOneAux.sliceCoerciveAe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeStepOneAux

open scoped Real Topology
open MeasureTheory Set Filter


end Work.FTS.EllipticEst.AeStepOneAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.CutEnergy.aeCutAfiniteA =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak.AeCutA

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

/-!
# `AeCutAfinite` — finiteness of the cut-off radial `L²`-norm of `∂_z u`

For a datum `AeData α u G` of the almost-everywhere class of the level-`0` elliptic estimate
and a cut-off `φ ∈ C²` with compact support contained in `(0,∞)` and `0 ≤ φ ≤ 1`, the
hypothesis

`∫⁻ z in Iz, ofReal (φ z * w z ^ 2) * (∫⁻ θ in Iθ, ofReal (u z θ ^ 2)) ≠ ⊤`

is turned into

`∫⁻ z in Iz, ofReal (φ z * w z ^ 2 * z ^ 2) * (∫⁻ θ in Iθ, ofReal ((∂_z u z θ) ^ 2)) ≠ ⊤`,

i.e. the *radial first derivative* of `u` is square-integrable against `φ w² z²`.

## Route

The work is done by the radial Agmon–Nirenberg interpolation of the tree,
`Work.FTS.EllipticEst.H2W.Ae.hkMem_gradU`: for `AeData α u G` the level-`0` `ℋ`-membership
`HkMem α 0 (D_z u)` of `D_z u = z ∂_z u` holds.  Unfolding `HkMem` at `k = 0` it says
exactly that

`A z := ∫_θ (z ∂_z u z θ * w z / sin(2θ)^{η/2})²`

is integrable in `z`, which by `ofReal_integral_eq_lintegral_ofReal` makes
`∫⁻ z, ofReal (A z) ≠ ⊤`.

The desired integral is dominated by this one: the only point is the *pointwise* bound (for
`θ ∈ (0,π/2)`, where `0 < sin(2θ) ≤ 1`)

`φ z * w z ² * z ² * (∂_z u z θ)² ≤ (z ∂_z u z θ * w z / sin(2θ)^{η/2})²`,

which is `φ z ≤ sin(2θ)^{-η}` multiplied by the nonnegative factor `w z ² * z ² *
(∂_z u z θ)²` (`φ z ≤ 1 ≤ sin(2θ)^{-η}`, and `sin(2θ)^{-η}` is exactly the square of the
angular part of the `ℋ⁰`-weight).  Pulling the constant `ofReal (φ z w z ² z ²)` inside the
`θ`-lintegral (`lintegral_const_mul'`, `ofReal_mul`) and integrating the resulting a.e.
pointwise bound over `θ` gives the claim.
-/

/-- The square of the angular factor `w / sin(2θ)^{η/2}` of the `ℋ⁰`-weight, written with a
single `rpow`: `(w / s^{η/2})² = w² s^{-η}` for `s ≥ 0`. -/
private lemma sinRpow_div_sq (w s : ℝ) (hs : 0 ≤ s) (η : ℝ) :
    (w / s ^ (η / 2)) ^ 2 = w ^ 2 * s ^ (-η) := by
  have h2 : (s ^ (η / 2)) ^ 2 = s ^ η := by
    rw [← Real.rpow_natCast (x := s ^ (η / 2)) (n := 2)]
    rw [← Real.rpow_mul (x := s) hs (η / 2) ((2 : ℕ) : ℝ)]
    norm_num
  rw [div_pow, h2, Real.rpow_neg hs]
  ring

/-- Almost every `θ ∈ Iθ = [0,π/2]` lies in the *open* interval `(0,π/2)` (the complement is
the two-point set `{0, π/2}`). -/
private lemma ae_mem_Ioo_of_Iθ_restrict :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  change ∀ᵐ θ ∂(volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))),
    θ ∈ Set.Ioo 0 (Real.pi / 2)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  rw [MeasureTheory.ae_iff]
  have hsub : {θ : ℝ | ¬ (θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) →
      θ ∈ Set.Ioo 0 (Real.pi / 2))} ⊆ ({0, Real.pi / 2} : Set ℝ) := by
    intro θ hθ
    obtain ⟨h1, h2⟩ := not_imp.mp hθ
    rw [Set.mem_Icc] at h1
    rw [Set.mem_Ioo] at h2
    have hθeq : θ = 0 ∨ θ = Real.pi / 2 := by
      by_cases h : θ ≤ 0
      · exact Or.inl (le_antisymm h h1.1)
      · refine Or.inr (le_antisymm h1.2 ?_)
        by_contra hge
        exact h2 ⟨lt_of_not_ge h, lt_of_not_ge hge⟩
    rcases hθeq with h | h <;> simp [h]
  refine measure_mono_null hsub ?_
  exact (Set.Finite.insert 0 (Set.finite_singleton (Real.pi / 2))).measure_zero volume

/-- The pointwise domination of the cut-off radial integrand by the `ℋ⁰`-integrand of
`D_z u = z ∂_z u`, on the *open* angular interval: for `0 ≤ φ ≤ 1` and
`θ ∈ (0,π/2)`,

`φ z * w z ² * z ² * (∂_z u z θ)² ≤ (z ∂_z u z θ * w z / sin(2θ)^{η/2})²`
`  = HkIntegrand α 0 (grad u) z θ`.

(`HkIntegrand α 0 f z θ` is the single term `(f z θ * w z / sin(2θ)^{η/2})²`.) -/
private lemma hkIntegrand_weight_le (φ : ℝ → ℝ) (hφ1 : ∀ z, φ z ≤ 1) (u : ℝ → ℝ → ℝ)
    (α z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    φ z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsr : 1 ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
    have h : (1 : ℝ) ^ (-Work.Spaces.eta) ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
      Real.rpow_le_rpow_of_nonpos hs hs1 (by have := Work.Spaces.eta_pos; linarith)
    simpa using h
  have hhk : Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
      = ((z * Work.Spaces.pz u z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simp [Work.Spaces.HkIntegrand, Work.FTS.EllipticEst.H2W.Ae.grad]
  rw [hhk, mul_pow,
    sinRpow_div_sq (Work.Spaces.w z) (Real.sin (2 * θ)) hs.le Work.Spaces.eta]
  have hX : 0 ≤ (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2 := by positivity
  calc φ z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2
      = φ z * ((Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2) := by ring
    _ ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
          * ((Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2) :=
        mul_le_mul_of_nonneg_right (le_trans (hφ1 z) hsr) hX
    _ = (z * Work.Spaces.pz u z θ) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by ring

theorem aeCutAfiniteA (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (φ : ℝ → ℝ) (hφsm : ContDiff ℝ 2 φ) (hcpt : HasCompactSupport φ)
    (hφ0 : ∀ z : ℝ, z ≤ 0 → φ z = 0) (hφnn : ∀ z : ℝ, 0 ≤ φ z) (hφ1 : ∀ z : ℝ, φ z ≤ 1)
    (hM : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))) ≠ ⊤) :
    (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2))) ≠ ⊤ := by
  -- The radial Agmon--Nirenberg certificate: `D_z u = z ∂_z u` is `ℋ⁰`, i.e. the weighted
  -- square of `z ∂_z u` is jointly integrable.
  obtain ⟨hsl, hzint⟩ := Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h
  -- The desired lintegral is dominated by the (finite) `ℋ⁰`-lintegral of `grad u`.
  have hKey : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2)))
      ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
            (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    have hAz : MeasureTheory.Integrable
        (fun θ => Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ)
        (volume.restrict Work.Spaces.Iθ) := (hsl z hz).integrable
    have hA0 : 0 ≤ φ z * (Work.Spaces.w z) ^ 2 * z ^ 2 :=
      mul_nonneg (mul_nonneg (hφnn z) (sq_nonneg _)) (sq_nonneg _)
    calc ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2))
        = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)
            * ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2) := by
          rw [← MeasureTheory.lintegral_const_mul'
            (ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2 * z ^ 2))
            (fun θ => ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2)) ENNReal.ofReal_ne_top]
      _ = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
            (φ z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2) := by
          refine MeasureTheory.lintegral_congr (fun θ => ?_)
          rw [← ENNReal.ofReal_mul hA0]
      _ ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
            (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ) := by
          refine MeasureTheory.lintegral_mono_ae ?_
          filter_upwards [ae_mem_Ioo_of_Iθ_restrict] with θ hθ
          exact ENNReal.ofReal_le_ofReal (hkIntegrand_weight_le φ hφ1 u α z θ hθ)
      _ = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
            (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ) := by
          rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            (μ := volume.restrict Work.Spaces.Iθ) hAz
            (Filter.Eventually.of_forall fun θ =>
              Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)]
  refine ne_top_of_le_ne_top ?_ hKey
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hzint.integrable)
      (Filter.Eventually.of_forall fun z => integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)]
  exact ENNReal.ofReal_ne_top

end Work.FTS.EllipticEst.AngAWeak.AeCutA
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.aeTruncIdent =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `aeTruncIdent` — the truncated energy identity in the almost-everywhere class

Target: for `AeData α u G`, a weight `W ∈ C²` with compact support, vanishing near `0`, the
truncated `w²`-energy identity

`∫_z W w² (∫_θ G u) = α² ∫_z W w² z² (∫_θ (∂_zu)²) + ∫_z W w² (∫_θ (L₀u) u)
   - (α²/2) ∫_z (W w² z²)'' (∫_θ u²) + (α(5+α)/2) ∫_z (W w² z)' (∫_θ u²)`

holds.  Here `Iz = [0,∞)`, `Iθ = [0,π/2]`, `w z = (1+z)²/z²`.

## Route

`bslOp α u = G` on the open quadrant, so the left-hand side may be written with `bslOp α u`; for
each fixed `θ ∈ (0,π/2)` the one-dimensional integration by parts in `z` of the slice
`z ↦ u z θ` against the radial weight `σ = W w²` gives (`remov.ibpZZ`, `remov.ibpZ`)

`∫_z σ z² ∂_zzu · u = ½ ∫_z (W w² z²)'' u² - ∫_z W w² z² (∂_zu)²`,
`∫_z σ z ∂_zu · u = -½ ∫_z (W w² z)' u²`

(no boundary terms: `σ` vanishes near `0` and at `∞`).  Integrating in `θ` and swapping the five
double integrals (Fubini) gives the identity.  The joint integrability that Fubini consumes is
supplied by the companion lemmas `aeUMassBound`, `aeBoxMem`, `AeJoint2.aeJointInt`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The `θ`-slice of a function that is smooth on the open quadrant is smooth on `(0,∞)`. -/
theorem contDiffOn_slice_z {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (n : ℕ) :
    ContDiffOn ℝ n (fun z => u z θ) (Set.Ioi 0) := by
  have hmap : MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi 0) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun z hz => ⟨hz, hθ⟩
  have hlin : ContDiffOn ℝ n (fun z : ℝ => (z, θ)) (Set.Ioi 0) := by fun_prop
  have hc := (hsm n).comp hlin hmap
  simpa [Function.comp_def, Function.uncurry] using hc

/-- `(w z)^2` is smooth on `(0,∞)` (`w z = (1+z)^2/z^2`). -/
theorem contDiffOn_wsq : ContDiffOn ℝ 2 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ 2 (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) := by
    refine ContDiffOn.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro z hz
      have hz0 : z ≠ 0 := ne_of_gt hz
      positivity
  have h2 : ContDiffOn ℝ 2 (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Ioi 0) := h1.pow 2
  refine h2.congr ?_
  intro z hz
  rw [Work.Spaces.w, div_pow]

/-- A function continuous on `(0,∞)` which vanishes on `(0,δ]` and on `[R,∞)`, with `0 < δ ≤ R`,
is integrable on `(0,∞)`. -/
theorem integrableOn_Ioi_of_support {f : ℝ → ℝ} {δ R : ℝ} (hδ0 : 0 < δ) (hδR : δ ≤ R)
    (hcont : ContinuousOn f (Set.Ioi 0))
    (hδ : ∀ z, z < δ → f z = 0) (hR : ∀ z, R < z → f z = 0) :
    IntegrableOn f (Set.Ioi 0) := by
  have hsub : Set.Icc δ R ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le hδ0 hz.1
  have h1 : IntegrableOn f (Set.Icc δ R) := (hcont.mono hsub).integrableOn_compact isCompact_Icc
  have h2 : IntegrableOn f (Set.Ioo (0 : ℝ) δ) :=
    ((MeasureTheory.integrable_zero ℝ ℝ volume).integrableOn).congr_fun
      (fun z hz => (hδ z hz.2).symm) measurableSet_Ioo
  have h3 : IntegrableOn f (Set.Ioi R) :=
    ((MeasureTheory.integrable_zero ℝ ℝ volume).integrableOn).congr_fun
      (fun z hz => (hR z hz).symm) measurableSet_Ioi
  have hunion : Set.Ioo (0 : ℝ) δ ∪ Set.Icc δ R ∪ Set.Ioi R = Set.Ioi (0 : ℝ) := by
    ext z
    constructor
    · rintro ((hz | hz) | hz)
      · exact hz.1
      · exact lt_of_lt_of_le hδ0 hz.1
      · exact lt_of_lt_of_le hδ0 (le_of_lt (lt_of_le_of_lt hδR hz))
    · intro hz
      rcases lt_or_ge z δ with h | h
      · exact Or.inl (Or.inl ⟨hz, h⟩)
      · rcases le_or_gt z R with h2 | h2
        · exact Or.inl (Or.inr ⟨h, h2⟩)
        · exact Or.inr h2
  rw [← hunion]
  exact (h2.union h1).union h3

/-- `volume.restrict Iz` and `volume.restrict (0,∞)` give the same integrability. -/
theorem integrableOn_Iz_iff_Ioi {f : ℝ → ℝ} :
    IntegrableOn f Work.Spaces.Iz ↔ IntegrableOn f (Set.Ioi 0) := by
  have h : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  change MeasureTheory.Integrable f (MeasureTheory.volume.restrict Work.Spaces.Iz)
    ↔ MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
  rw [h]

/-- A function vanishing on `(0,δ)` has limit `0` at `0⁺` within `(0,∞)`. -/
theorem tendsto_nhdsWithin_zero_of_eq_zero {f : ℝ → ℝ} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : ∀ z, z < δ → f z = 0) :
    Filter.Tendsto f (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)) (Iio_mem_nhds hδ0)] with z hz
  exact (hδ z hz).symm

/-- A function vanishing on `(R,∞)` has limit `0` at `∞`. -/
theorem tendsto_atTop_zero_of_eq_zero {f : ℝ → ℝ} {R : ℝ}
    (hR : ∀ z, R < z → f z = 0) :
    Filter.Tendsto f Filter.atTop (𝓝 0) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop R] with z hz
  exact (hR z hz).symm

/-- **The `∂_zz`-integration by parts of the truncated identity, slice by slice in `θ`.** -/
theorem sliceIBP_zz (α : ℝ) (u : ℝ → ℝ → ℝ) (W : ℝ → ℝ) (hW2 : ContDiff ℝ 2 W)
    {δ R θ : ℝ} (hδ0 : 0 < δ) (hδR : δ ≤ R) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hδW : ∀ z, z ≤ δ → W z = 0) (hRW : ∀ z, R ≤ z → W z = 0)
    (hslice : ContDiffOn ℝ 2 (fun z => u z θ) (Set.Ioi 0)) :
    (∫ z in Work.Spaces.Iz, (W z * (Work.Spaces.w z) ^ 2 * z ^ 2)
        * (Work.Spaces.pzIter 2 u z θ * u z θ))
      = (1 / 2) * (∫ z in Work.Spaces.Iz,
          deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * (u z θ) ^ 2)
        - (∫ z in Work.Spaces.Iz, (W z * (Work.Spaces.w z) ^ 2 * z ^ 2)
            * (Work.Spaces.pz u z θ) ^ 2) := by
  set σ : ℝ → ℝ := fun z => W z * (Work.Spaces.w z) ^ 2 with hσdef
  set φ : ℝ → ℝ := fun z => u z θ with hφdef
  have hσsm : ContDiffOn ℝ 2 σ (Set.Ioi 0) := by
    rw [hσdef]; exact hW2.contDiffOn.mul contDiffOn_wsq
  have hσc : ContinuousOn σ (Set.Ioi 0) := hσsm.continuousOn
  have hφc : ContinuousOn φ (Set.Ioi 0) := by rw [hφdef]; exact hslice.continuousOn
  have hφ1sm : ContDiffOn ℝ 1 (deriv φ) (Set.Ioi 0) := by
    rw [hφdef]; exact hslice.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hφ1c : ContinuousOn (deriv φ) (Set.Ioi 0) := hφ1sm.continuousOn
  have hφ2c : ContinuousOn (fun z => deriv (deriv φ) z) (Set.Ioi 0) :=
    (hslice.deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num)).continuousOn_deriv_of_isOpen
      isOpen_Ioi (by norm_num)
  have hw2c : ContinuousOn (fun z => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
    contDiffOn_wsq.continuousOn
  -- vanishing of `σ` and of its derivatives below `δ` / above `R`
  have hσz : ∀ z, z ≤ δ → σ z = 0 := by
    intro z hz; rw [hσdef]; simp [hδW z hz]
  have hσzR : ∀ z, R ≤ z → σ z = 0 := by
    intro z hz; rw [hσdef]; simp [hRW z hz]
  have hσev : ∀ z, z < δ →
      (fun z' => z' ^ 2 * σ z') =ᶠ[𝓝 z] 0 := by
    intro z hz
    filter_upwards [IsOpen.mem_nhds isOpen_Iio hz] with z' hz'
    simp only [hσz z' hz'.le, mul_zero, Pi.zero_apply]
  have hσevR : ∀ z, R < z →
      (fun z' => z' ^ 2 * σ z') =ᶠ[𝓝 z] 0 := by
    intro z hz
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi hz] with z' hz'
    simp only [hσzR z' hz'.le, mul_zero, Pi.zero_apply]
  have hd1 : ∀ z, z < δ → deriv (fun z' => z' ^ 2 * σ z') z = 0 := by
    intro z hz; rw [(hσev z hz).deriv_eq]; simp
  have hd1R : ∀ z, R < z → deriv (fun z' => z' ^ 2 * σ z') z = 0 := by
    intro z hz; rw [(hσevR z hz).deriv_eq]; simp
  have hd2 : ∀ z, z < δ → deriv (deriv (fun z' => z' ^ 2 * σ z')) z = 0 := by
    intro z hz
    have hev : (fun z' => deriv (fun z'' => z'' ^ 2 * σ z'') z') =ᶠ[𝓝 z] 0 := by
      filter_upwards [IsOpen.mem_nhds isOpen_Iio hz] with z' hz'
      exact hd1 z' hz'
    rw [hev.deriv_eq]; simp
  have hd2R : ∀ z, R < z → deriv (deriv (fun z' => z' ^ 2 * σ z')) z = 0 := by
    intro z hz
    have hev : (fun z' => deriv (fun z'' => z'' ^ 2 * σ z'') z') =ᶠ[𝓝 z] 0 := by
      filter_upwards [IsOpen.mem_nhds isOpen_Ioi hz] with z' hz'
      exact hd1R z' hz'
    rw [hev.deriv_eq]; simp
  -- continuity of the four integrands of `ibpZZ`
  have hσ2 : ContDiffOn ℝ 2 (fun z : ℝ => z ^ 2 * σ z) (Set.Ioi 0) :=
    (by fun_prop : ContDiffOn ℝ 2 (fun z : ℝ => z ^ 2) (Set.Ioi 0)).mul hσsm
  have hdσ1c : ContinuousOn (fun z => deriv (fun z' => z' ^ 2 * σ z') z) (Set.Ioi 0) :=
    hσ2.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hdσ2c : ContinuousOn (fun z => deriv (deriv (fun z' => z' ^ 2 * σ z')) z) (Set.Ioi 0) :=
    (hσ2.deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num)).continuousOn_deriv_of_isOpen
      isOpen_Ioi (by norm_num)
  have hc1 : ContinuousOn (fun z => z ^ 2 * σ z * φ z * deriv (deriv φ) z) (Set.Ioi 0) :=
    (((continuousOn_id.pow 2).mul hσc).mul hφc).mul hφ2c
  have hc2 : ContinuousOn (fun z => deriv (fun z' => z' ^ 2 * σ z') z * φ z * deriv φ z)
      (Set.Ioi 0) :=
    (hdσ1c.mul hφc).mul hφ1c
  have hc3 : ContinuousOn (fun z => σ z * (z * deriv φ z) ^ 2) (Set.Ioi 0) :=
    hσc.mul ((continuousOn_id.mul hφ1c).pow 2)
  have hc4 : ContinuousOn (fun z => deriv (deriv (fun z' => z' ^ 2 * σ z')) z * φ z ^ 2)
      (Set.Ioi 0) :=
    hdσ2c.mul (hφc.pow 2)
  -- integrability
  have hi1 : IntegrableOn (fun z => z ^ 2 * σ z * φ z * deriv (deriv φ) z) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support hδ0 hδR hc1
      (fun z hz => by rw [hσz z hz.le]; ring)
      (fun z hz => by rw [hσzR z hz.le]; ring)
  have hi2 : IntegrableOn (fun z => deriv (fun z' => z' ^ 2 * σ z') z * φ z * deriv φ z)
      (Set.Ioi 0) :=
    integrableOn_Ioi_of_support hδ0 hδR hc2
      (fun z hz => by rw [hd1 z hz]; ring)
      (fun z hz => by rw [hd1R z hz]; ring)
  have hi3 : IntegrableOn (fun z => σ z * (z * deriv φ z) ^ 2) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support hδ0 hδR hc3
      (fun z hz => by rw [hσz z hz.le]; ring)
      (fun z hz => by rw [hσzR z hz.le]; ring)
  have hi4 : IntegrableOn (fun z => deriv (deriv (fun z' => z' ^ 2 * σ z')) z * φ z ^ 2)
      (Set.Ioi 0) :=
    integrableOn_Ioi_of_support hδ0 hδR hc4
      (fun z hz => by rw [hd2 z hz]; ring)
      (fun z hz => by rw [hd2R z hz]; ring)
  -- boundary limits
  have hb0 : Filter.Tendsto (fun z => z ^ 2 * σ z * φ z * deriv φ z)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
    tendsto_nhdsWithin_zero_of_eq_zero hδ0 (fun z hz => by rw [hσz z hz.le]; ring)
  have hbT : Filter.Tendsto (fun z => z ^ 2 * σ z * φ z * deriv φ z) Filter.atTop (𝓝 0) :=
    tendsto_atTop_zero_of_eq_zero (fun z hz => by rw [hσzR z hz.le]; ring)
  have hb0' : Filter.Tendsto (fun z => deriv (fun z' => z' ^ 2 * σ z') z * φ z ^ 2)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
    tendsto_nhdsWithin_zero_of_eq_zero hδ0 (fun z hz => by rw [hd1 z hz]; ring)
  have hbT' : Filter.Tendsto (fun z => deriv (fun z' => z' ^ 2 * σ z') z * φ z ^ 2)
      Filter.atTop (𝓝 0) :=
    tendsto_atTop_zero_of_eq_zero (fun z hz => by rw [hd1R z hz]; ring)
  have hmain := Work.FTS.EllipticEst.remov.ibpZZ σ φ hσsm (by rw [hφdef]; exact hslice)
    hi1 hi2 hi3 hi4 hb0 hbT hb0' hbT'
  -- rewrite the four integrals into the shapes of the statement
  rw [hσdef, hφdef] at hmain
  have e1 : (∫ z in Set.Ioi (0 : ℝ), (fun z => W z * (Work.Spaces.w z) ^ 2) z * z ^ 2
        * deriv (deriv (fun z => u z θ)) z * u z θ)
      = ∫ z in Work.Spaces.Iz, (W z * (Work.Spaces.w z) ^ 2 * z ^ 2)
          * (Work.Spaces.pzIter 2 u z θ * u z θ) := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [show deriv (deriv (fun z => u z θ)) z = Work.Spaces.pzIter 2 u z θ from rfl]
    ring
  have e2 : (∫ z in Set.Ioi (0 : ℝ),
        deriv (deriv (fun z => z ^ 2 * (W z * (Work.Spaces.w z) ^ 2))) z * (u z θ) ^ 2)
      = ∫ z in Work.Spaces.Iz,
          deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * (u z θ) ^ 2 := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [show (fun z' => z' ^ 2 * (W z' * (Work.Spaces.w z') ^ 2))
        = fun z' => W z' * (Work.Spaces.w z') ^ 2 * z' ^ 2 from by funext z'; ring]
  have e3 : (∫ z in Set.Ioi (0 : ℝ), (fun z => W z * (Work.Spaces.w z) ^ 2) z
        * (z * deriv (fun z' => u z' θ) z) ^ 2)
      = ∫ z in Work.Spaces.Iz, (W z * (Work.Spaces.w z) ^ 2 * z ^ 2)
          * (Work.Spaces.pz u z θ) ^ 2 := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [show deriv (fun z' => u z' θ) z = Work.Spaces.pz u z θ from rfl]
    ring
  rw [e1, e2, e3] at hmain
  exact hmain

/-- **The `∂_z`-integration by parts of the truncated identity, slice by slice in `θ`.** -/
theorem sliceIBP_z (α : ℝ) (u : ℝ → ℝ → ℝ) (W : ℝ → ℝ) (hW2 : ContDiff ℝ 2 W)
    {δ R θ : ℝ} (hδ0 : 0 < δ) (hδR : δ ≤ R) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hδW : ∀ z, z ≤ δ → W z = 0) (hRW : ∀ z, R ≤ z → W z = 0)
    (hslice : ContDiffOn ℝ 2 (fun z => u z θ) (Set.Ioi 0)) :
    (∫ z in Work.Spaces.Iz, (W z * (Work.Spaces.w z) ^ 2 * z)
        * (Work.Spaces.pz u z θ * u z θ))
      = -(1 / 2) * (∫ z in Work.Spaces.Iz,
          deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2) := by
  have hσsm : ContDiffOn ℝ 2 (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
    hW2.contDiffOn.mul contDiffOn_wsq
  have hσc : ContinuousOn (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
    hσsm.continuousOn
  have hφc : ContinuousOn (fun z : ℝ => u z θ) (Set.Ioi 0) := hslice.continuousOn
  have hφ1c : ContinuousOn (deriv (fun z : ℝ => u z θ)) (Set.Ioi 0) :=
    (hslice.deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num)).continuousOn
  have hσz : ∀ z, z ≤ δ → W z * (Work.Spaces.w z) ^ 2 = 0 := by
    intro z hz; rw [hδW z hz]; ring
  have hσzR : ∀ z, R ≤ z → W z * (Work.Spaces.w z) ^ 2 = 0 := by
    intro z hz; rw [hRW z hz]; ring
  have hσev : ∀ z, z < δ → (fun z' => z' * (W z' * (Work.Spaces.w z') ^ 2)) =ᶠ[𝓝 z] 0 := by
    intro z hz
    filter_upwards [IsOpen.mem_nhds isOpen_Iio hz] with z' hz'
    simp only [hσz z' hz'.le, mul_zero, Pi.zero_apply]
  have hσevR : ∀ z, R < z → (fun z' => z' * (W z' * (Work.Spaces.w z') ^ 2)) =ᶠ[𝓝 z] 0 := by
    intro z hz
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi hz] with z' hz'
    simp only [hσzR z' hz'.le, mul_zero, Pi.zero_apply]
  have hd1 : ∀ z, z < δ → deriv (fun z' => z' * (W z' * (Work.Spaces.w z') ^ 2)) z = 0 := by
    intro z hz; rw [(hσev z hz).deriv_eq]; simp
  have hd1R : ∀ z, R < z → deriv (fun z' => z' * (W z' * (Work.Spaces.w z') ^ 2)) z = 0 := by
    intro z hz; rw [(hσevR z hz).deriv_eq]; simp
  have hσzs : ContDiffOn ℝ 2 (fun z : ℝ => z * (W z * (Work.Spaces.w z) ^ 2)) (Set.Ioi 0) :=
    (by fun_prop : ContDiffOn ℝ 2 (fun z : ℝ => z) (Set.Ioi 0)).mul hσsm
  have hi1 : IntegrableOn (fun z => z * (W z * (Work.Spaces.w z) ^ 2) * u z θ
      * deriv (fun z => u z θ) z) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support hδ0 hδR
      (((((by fun_prop : ContinuousOn (fun z : ℝ => z) (Set.Ioi 0)).mul hσc).mul hφc).mul hφ1c).congr fun z _ => rfl)
      (fun z hz => by rw [hσz z hz.le]; ring)
      (fun z hz => by rw [hσzR z hz.le]; ring)
  have hi2 : IntegrableOn (fun z => deriv (fun z' => z' * (W z' * (Work.Spaces.w z') ^ 2)) z
      * (u z θ) ^ 2) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support hδ0 hδR
      ((hσzs.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mul (hφc.pow 2))
      (fun z hz => by rw [hd1 z hz]; ring)
      (fun z hz => by rw [hd1R z hz]; ring)
  have hb0 : Filter.Tendsto (fun z => z * (W z * (Work.Spaces.w z) ^ 2) * (u z θ) ^ 2)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
    tendsto_nhdsWithin_zero_of_eq_zero hδ0 (fun z hz => by rw [hσz z hz.le]; ring)
  have hbT : Filter.Tendsto (fun z => z * (W z * (Work.Spaces.w z) ^ 2) * (u z θ) ^ 2)
      Filter.atTop (𝓝 0) :=
    tendsto_atTop_zero_of_eq_zero (fun z hz => by rw [hσzR z hz.le]; ring)
  have hmain := Work.FTS.EllipticEst.remov.ibpZ
    (fun z => W z * (Work.Spaces.w z) ^ 2) (fun z => u z θ) hσsm hslice
    hi1 hi2 hb0 hbT
  have e1 : (∫ z in Set.Ioi (0 : ℝ), (W z * (Work.Spaces.w z) ^ 2)
        * (z * deriv (fun z => u z θ) z) * u z θ)
      = ∫ z in Work.Spaces.Iz, (W z * (Work.Spaces.w z) ^ 2 * z)
          * (Work.Spaces.pz u z θ * u z θ) := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [show deriv (fun z => u z θ) z = Work.Spaces.pz u z θ from rfl]
    ring
  have e2 : (∫ z in Set.Ioi (0 : ℝ),
        deriv (fun z' => z' * (W z' * (Work.Spaces.w z') ^ 2)) z * (u z θ) ^ 2)
      = ∫ z in Work.Spaces.Iz,
          deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2 := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [show (fun z' => z' * (W z' * (Work.Spaces.w z') ^ 2))
        = fun z' => W z' * (Work.Spaces.w z') ^ 2 * z' from by funext z'; ring]
  rw [e1, e2] at hmain
  exact hmain

/-- **The truncated energy identity, slice by slice in `θ`.**  `hIntL` is the (a.e.-in-`θ`)
integrability of the `L₀`-pairing, which is what the joint integrability of the parent theorem
supplies. -/
theorem sliceIBP (α : ℝ) (u : ℝ → ℝ → ℝ) (W : ℝ → ℝ) (hW2 : ContDiff ℝ 2 W)
    {δ R θ : ℝ} (hδ0 : 0 < δ) (hδR : δ ≤ R) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hδW : ∀ z, z ≤ δ → W z = 0) (hRW : ∀ z, R ≤ z → W z = 0)
    (hslice : ContDiffOn ℝ 2 (fun z => u z θ) (Set.Ioi 0))
    (hIntL : IntegrableOn (fun z => W z * (Work.Spaces.w z) ^ 2
        * (Work.Elliptic.Lzero u z θ * u z θ)) Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
        * (Work.Elliptic.bslOp α u z θ * u z θ))
      = α ^ 2 * (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2 * z ^ 2
            * (Work.Spaces.pz u z θ) ^ 2)
        + (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
            * (Work.Elliptic.Lzero u z θ * u z θ))
        - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
            deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * (u z θ) ^ 2)
        + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
            deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2) := by
  have hσc : ContinuousOn (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
    (hW2.contDiffOn.mul contDiffOn_wsq).continuousOn
  have hφc : ContinuousOn (fun z : ℝ => u z θ) (Set.Ioi 0) := hslice.continuousOn
  have hφ1c : ContinuousOn (deriv (fun z : ℝ => u z θ)) (Set.Ioi 0) :=
    (hslice.deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num)).continuousOn
  have hφ2c : ContinuousOn (fun z => deriv (deriv (fun z : ℝ => u z θ)) z) (Set.Ioi 0) :=
    ((hslice.deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num))).continuousOn_deriv_of_isOpen
      isOpen_Ioi (by norm_num)
  have hσz : ∀ z, z ≤ δ → W z * (Work.Spaces.w z) ^ 2 = 0 := by
    intro z hz; rw [hδW z hz]; ring
  have hσzR : ∀ z, R ≤ z → W z * (Work.Spaces.w z) ^ 2 = 0 := by
    intro z hz; rw [hRW z hz]; ring
  -- integrability of the two radial pieces
  have hcontA : ContinuousOn (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2
      * (Work.Spaces.pzIter 2 u z θ * u z θ)) (Set.Ioi 0) :=
    ((hσc.mul (by fun_prop : ContinuousOn (fun z : ℝ => z ^ 2) (Set.Ioi 0))).congr (fun z _ => by simp only [Pi.mul_apply])).mul
      (hφ2c.mul hφc)
  have hcontB : ContinuousOn (fun z => W z * (Work.Spaces.w z) ^ 2 * z
      * (Work.Spaces.pz u z θ * u z θ)) (Set.Ioi 0) :=
    ((hσc.mul (by fun_prop : ContinuousOn (fun z : ℝ => z) (Set.Ioi 0))).congr (fun z _ => by simp only [Pi.mul_apply])).mul (hφ1c.mul hφc)
  have hIA : IntegrableOn (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2
      * (Work.Spaces.pzIter 2 u z θ * u z θ)) Work.Spaces.Iz := by
    rw [integrableOn_Iz_iff_Ioi]
    exact integrableOn_Ioi_of_support hδ0 hδR hcontA
      (fun z hz => by rw [hσz z hz.le]; ring)
      (fun z hz => by rw [hσzR z hz.le]; ring)
  have hIB : IntegrableOn (fun z => W z * (Work.Spaces.w z) ^ 2 * z
      * (Work.Spaces.pz u z θ * u z θ)) Work.Spaces.Iz := by
    rw [integrableOn_Iz_iff_Ioi]
    exact integrableOn_Ioi_of_support hδ0 hδR hcontB
      (fun z hz => by rw [hσz z hz.le]; ring)
      (fun z hz => by rw [hσzR z hz.le]; ring)
  have hA2 : IntegrableOn (fun z => α ^ 2 * ((W z * (Work.Spaces.w z) ^ 2 * z ^ 2)
      * (Work.Spaces.pzIter 2 u z θ * u z θ))) Work.Spaces.Iz := hIA.const_mul _
  have hB2 : IntegrableOn (fun z => (α * (5 + α)) * ((W z * (Work.Spaces.w z) ^ 2 * z)
      * (Work.Spaces.pz u z θ * u z θ))) Work.Spaces.Iz := hIB.const_mul _
  have hAB2 : IntegrableOn (fun z => α ^ 2 * ((W z * (Work.Spaces.w z) ^ 2 * z ^ 2)
      * (Work.Spaces.pzIter 2 u z θ * u z θ))
        + (α * (5 + α)) * ((W z * (Work.Spaces.w z) ^ 2 * z)
      * (Work.Spaces.pz u z θ * u z θ))) Work.Spaces.Iz := hA2.add hB2
  have hkey : (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
        * (Work.Elliptic.bslOp α u z θ * u z θ))
      = (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
            * (Work.Elliptic.Lzero u z θ * u z θ))
        - (α ^ 2 * (∫ z in Work.Spaces.Iz, (W z * (Work.Spaces.w z) ^ 2 * z ^ 2)
              * (Work.Spaces.pzIter 2 u z θ * u z θ))
          + (α * (5 + α)) * (∫ z in Work.Spaces.Iz, (W z * (Work.Spaces.w z) ^ 2 * z)
              * (Work.Spaces.pz u z θ * u z θ))) := by
    rw [show (fun z => W z * (Work.Spaces.w z) ^ 2
          * (Work.Elliptic.bslOp α u z θ * u z θ))
        = fun z => W z * (Work.Spaces.w z) ^ 2 * (Work.Elliptic.Lzero u z θ * u z θ)
            - (α ^ 2 * ((W z * (Work.Spaces.w z) ^ 2 * z ^ 2)
                * (Work.Spaces.pzIter 2 u z θ * u z θ))
              + (α * (5 + α)) * ((W z * (Work.Spaces.w z) ^ 2 * z)
                * (Work.Spaces.pz u z θ * u z θ))) from by
      funext z; rw [Work.Elliptic.bslOp_apply]; ring]
    simp only [MeasureTheory.integral_sub hIntL hAB2, MeasureTheory.integral_add hA2 hB2,
      MeasureTheory.integral_const_mul]
  rw [hkey]
  simp only [sliceIBP_zz α u W hW2 hδ0 hδR hθ hδW hRW hslice,
    sliceIBP_z α u W hW2 hδ0 hδR hθ hδW hRW hslice]
  ring



end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Dispatch.aeJointIntegrableF =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Dispatch

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- The product measure `dz dθ` on the quadrant `(0,∞) × Iθ`. -/
abbrev nuFts : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict (Set.Ioi 0)).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-! ## The measure `nuFts` and its concentration on the open quadrant -/

/-- `nuFts` is the restriction of the planar Lebesgue measure to the open quadrant. -/
theorem nu_eq_Q0 :
    nuFts = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  change (MeasureTheory.volume.restrict (Set.Ioi 0)).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) = _
  rw [MeasureTheory.Measure.prod_restrict]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ _)
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
        (b := Real.pi / 2)).symm)

/-- Almost every `(z,θ) ∈ nuFts` has `z > 0`. -/
theorem ae_mem_Ioi_nu : ∀ᵐ p ∂nuFts, 0 < p.1 := by
  rw [nu_eq_Q0]
  exact MeasureTheory.ae_restrict_of_forall_mem
    ((isOpen_Ioi.prod isOpen_Ioo).measurableSet) (fun p hp => hp.1)

/-- Almost every `(z,θ) ∈ nuFts` has `θ ∈ (0, π/2)`. -/
theorem ae_mem_Ioo_nu : ∀ᵐ p ∂nuFts, p.2 ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [nu_eq_Q0]
  exact MeasureTheory.ae_restrict_of_forall_mem
    ((isOpen_Ioi.prod isOpen_Ioo).measurableSet) (fun p hp => hp.2)

/-! ## a.e. strong measurability from continuity on the open quadrant -/

/-- A function continuous on the open quadrant is a.e. strongly measurable for `nuFts`. -/
theorem aesm_prod_of_continuousOn_Q0 {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F Q0) :
    MeasureTheory.AEStronglyMeasurable F nuFts := by
  rw [nu_eq_Q0]
  exact hF.aestronglyMeasurable (isOpen_Ioi.prod isOpen_Ioo).measurableSet




/-! ## The level-`0` integrand dominates the unweighted square -/

/-- On the open angular interval, `σ = sin(2θ)^{-η} ≥ 1`, hence
`w(z)² f(z,θ)² ≤ HkIntegrand α 0 f z θ`. -/
theorem sq_weight_le_Hk (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.w z) ^ 2 * (f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 0 f z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have h1 : (1 : ℝ) ≤ Work.FTS.EllipticEst.sEta θ := one_le_sEta_D hθ
  have h2 : (f z θ) ^ 2 ≤ (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    simpa using mul_le_mul_of_nonneg_left h1 (sq_nonneg (f z θ))
  rw [HkIntegrand_zero_D α f hθI]
  exact mul_le_mul_of_nonneg_left h2 (sq_nonneg (Work.Spaces.w z))

/-! ## Joint integrability of the `ℋ⁰`-integrand -/

/-- **Joint integrability of an `ℋ⁰`-integrand.**  Tonelli: the slicewise and outer
integrability of `HkMem α 0 g` give the integrability of `HkIntegrand α 0 g` against the
product measure, the a.e. strong measurability of the slices converting the `lintegral` in
`θ` into an honest integral. -/
theorem integrable_HkIntegrand_of_hkMem {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α 0 g)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 g p.1 p.2) nuFts) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 g p.1 p.2) nuFts := by
  have hnn : ∀ p : ℝ × ℝ, 0 ≤ Work.Spaces.HkIntegrand α 0 g p.1 p.2 := fun p =>
    Work.Spaces.HkIntegrand_nonneg α 0 g p.1 p.2
  -- the inner lintegral is the `ofReal` of the slice integral, for every `z > 0`
  have hslice : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g z θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ) := by
    intro z hz
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (hm.1 z (Set.mem_Ici.mpr (le_of_lt hz)))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ))).symm
  -- the lintegral over the product measure
  have hkey : (∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g p.1 p.2) ∂nuFts)
      = ENNReal.ofReal (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 g z θ) := by
    rw [MeasureTheory.lintegral_prod
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g p.1 p.2))
      haesm.aemeasurable.ennreal_ofReal]
    have hinner : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g z θ)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      exact hslice z hz
    rw [MeasureTheory.lintegral_congr_ae hinner]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (hm.2.mono_set Set.Ioi_subset_Ici_self)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z _ =>
        MeasureTheory.integral_nonneg
          (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ)))).symm
  refine ⟨haesm, ?_⟩
  rw [MeasureTheory.HasFiniteIntegral]
  rw [show (∫⁻ p : ℝ × ℝ, ‖Work.Spaces.HkIntegrand α 0 g p.1 p.2‖ₑ ∂nuFts)
      = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g p.1 p.2) ∂nuFts from
    MeasureTheory.lintegral_congr_ae
      (Filter.Eventually.of_forall (fun p => Real.enorm_of_nonneg (hnn p)))]
  rw [hkey]
  exact ENNReal.ofReal_lt_top

/-- The `ℋ⁰`-integrand of a function which is `SmoothOpen` and honestly in `ℋ⁰` is jointly
integrable on `nuFts`. -/
theorem integrable_HkIntegrand_of_smoothOpen {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 0 f) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2) nuFts :=
  integrable_HkIntegrand_of_hkMem hm
    (aesm_prod_of_continuousOn_Q0
      (F := fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
      (hf.continuousOn_HkIntegrand α 0))

/-! ## The domination lemmas -/

/-- A function dominated a.e. by a nonnegative multiple of `HkIntegrand α 0 f` is integrable. -/
theorem integrable_of_le_const_mul_HkIntegrand {α : ℝ} {f : ℝ → ℝ → ℝ} {F : ℝ × ℝ → ℝ}
    {K : ℝ} (hK0 : 0 ≤ K) (haesm : MeasureTheory.AEStronglyMeasurable F nuFts)
    (hf : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2) nuFts)
    (hbd : ∀ᵐ p ∂nuFts, ‖F p‖ ≤ K * Work.Spaces.HkIntegrand α 0 f p.1 p.2) :
    MeasureTheory.Integrable F nuFts :=
  (hf.const_mul K).mono' haesm hbd



/-! ## The second derivative of the truncated radial weight `χw²z²` -/

/-- `Wcut χ = χ·w²` is `C²` on `(0,∞)`. -/
theorem contDiffOn_two_Wcut {χ : ℝ → ℝ} (hχsm : ContDiff ℝ 2 χ) :
    ContDiffOn ℝ 2 (Wcut χ) (Set.Ioi 0) := by
  have hw : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
    funext z; rw [Work.Spaces.w]
  have hw2 : ContDiffOn ℝ 2 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    rw [hw]
    refine (ContDiffOn.div ?_ ?_ ?_).pow 2
    · fun_prop
    · fun_prop
    · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)
  exact ContDiffOn.mul hχsm.contDiffOn hw2





/-! ## The main theorem -/


end Work.FTS.EllipticEst.Dispatch
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Ae

set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "σ" => Work.FTS.EllipticEst.sEta

/-! ## Elementary facts -/

/-- The angular weight `σ = sin(2θ)^{-η}` is nonnegative on `Iθ`. -/
theorem sigma_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ σ θ :=
  Real.rpow_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _

/-- `|a b| ≤ (a² + b²)/2`. -/
theorem abs_mul_le_half_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : (0 : ℝ) ≤ (|a| - |b|) ^ 2 := sq_nonneg _
  rw [abs_mul, ← sq_abs a, ← sq_abs b]
  nlinarith [h]

/-! ## The one-sided limits of `deriv` of a weighted-`H²` slice -/

/-- For a slice which is `C²` on `(0, π/2)` and whose `σ`-weighted second derivative is
integrable, `deriv` has finite one-sided limits at `0⁺` and at `(π/2)⁻`. -/
theorem slice_deriv_limits {f : ℝ → ℝ}
    (h2 : ContDiffOn ℝ 2 f Iθo)
    (hdd : IntegrableOn (fun θ => (deriv (fun t => deriv f t) θ) ^ 2 * σ θ)
      Work.Spaces.Iθ) :
    (∃ L : ℝ, Tendsto (deriv f) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds L)) ∧
      (∃ L : ℝ, Tendsto (deriv f) (nhdsWithin (Real.pi / 2) (Iio (Real.pi / 2))) (nhds L)) := by
  have hπ : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hsq := Work.FTS.EllipticEst.sliceLim_integrableOn_sq_of_integrableOn_mul_sEta f hdd
  have habs := Work.FTS.EllipticEst.sliceLim_integrableOn_abs_of_integrableOn_sq f hsq
  have hmem : AEStronglyMeasurable (fun θ : ℝ => deriv (fun t : ℝ => deriv f t) θ)
      (volume.restrict Iθo) := (measurable_deriv (deriv f)).aestronglyMeasurable
  have hint : IntegrableOn (fun θ : ℝ => deriv (fun t : ℝ => deriv f t) θ) Iθo := by
    rw [MeasureTheory.IntegrableOn]
    refine (MeasureTheory.integrable_norm_iff hmem).mp ?_
    rw [MeasureTheory.IntegrableOn] at habs
    simpa [Real.norm_eq_abs] using habs
  have hder1 : ∀ x ∈ Iθo, HasDerivAt f (deriv f x) x := by
    intro x hx
    exact ((h2.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
  have hder2 : ∀ x ∈ Iθo, HasDerivAt (deriv f) (deriv (deriv f) x) x := by
    intro x hx
    exact (((h2.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).contDiffAt
      (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
  exact ⟨Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv
      (f := deriv f) (f' := fun θ => deriv (fun t : ℝ => deriv f t) θ) hπ hder2 hint,
    Work.FTS.EllipticEst.H2W.exists_tendsto_nhdsLT_of_integrableOn_deriv
      (f := deriv f) (f' := fun θ => deriv (fun t : ℝ => deriv f t) θ)
      (a := (0 : ℝ)) (b := Real.pi / 2) hπ hder2 hint⟩

/-! ## The `σ`-weighted self-form integrand of a slice -/

/-- **The `σ`-weighted `Lzero1`-self-form integrand of a slice is integrable on `Iθ`.**

For `f` which is `C²` on `(0, π/2)` with `(f'')²σ` and `f²σ` integrable on `Iθ`, and with the
endpoint bounds `|f θ| ≤ C (π/2 - θ)`, `|f' θ| ≤ C` (`C > 0`), the integrand `Lzero1 f · f · σ`
is integrable on `Iθ`. -/
theorem slice_lzero_sigma_integrable {f : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hsm2 : ContDiffOn ℝ 2 f Iθo)
    (hdd : IntegrableOn (fun θ => (deriv (fun t => deriv f t) θ) ^ 2 * σ θ) Work.Spaces.Iθ)
    (hu2 : IntegrableOn (fun θ => (f θ) ^ 2 * σ θ) Work.Spaces.Iθ)
    (hb2 : ∀ θ ∈ Iθo, |f θ| ≤ C * (Real.pi / 2 - θ))
    (hb3 : ∀ θ ∈ Iθo, |deriv f θ| ≤ C) :
    IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ * σ θ) Work.Spaces.Iθ := by
  -- the pointwise identity on the open interval
  have hpoint : ∀ θ ∈ Iθo, Work.FTS.EllipticEst.Lzero1 f θ * f θ
      = -(deriv (fun t => deriv f t) θ) * f θ + (f θ / Real.cos θ) ^ 2
        + Real.tan θ * deriv f θ * f θ - 6 * (f θ) ^ 2 := by
    intro θ hθ
    have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩)
    have hd1 : DifferentiableAt ℝ f θ :=
      (hsm2.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    have hd2 : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.mpr hcos
    have hderiv_tan : deriv (fun t : ℝ => Real.tan t * f t) θ
        = f θ / Real.cos θ ^ 2 + Real.tan θ * deriv f θ := by
      have h := deriv_mul hd2 hd1
      rw [Real.deriv_tan, one_div, inv_mul_eq_div] at h
      exact h
    simp only [Work.FTS.EllipticEst.Lzero1, hderiv_tan]
    ring
  -- continuity of the explicit form on the open interval
  have hcos_ne : ∀ θ ∈ Iθo, Real.cos θ ≠ 0 := fun θ hθ => ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩)
  have hcd1 : ContinuousOn (deriv f) Iθo :=
    hsm2.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcd2 : ContinuousOn (fun θ => deriv (fun t : ℝ => deriv f t) θ) Iθo :=
    (hsm2.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn_deriv_of_isOpen
      isOpen_Ioo (by norm_num)
  have htan : ContinuousOn Real.tan Iθo := Real.continuousOn_tan.mono (fun θ hθ => hcos_ne θ hθ)
  have hcont_expl : ContinuousOn (fun θ : ℝ => -(deriv (fun t => deriv f t) θ) * f θ
      + (f θ / Real.cos θ) ^ 2 + Real.tan θ * deriv f θ * f θ - 6 * (f θ) ^ 2) Iθo := by
    have h1 : ContinuousOn (fun θ : ℝ => -(deriv (fun t => deriv f t) θ) * f θ) Iθo :=
      hcd2.neg.mul hsm2.continuousOn
    have h2 : ContinuousOn (fun θ : ℝ => (f θ / Real.cos θ) ^ 2) Iθo :=
      (hsm2.continuousOn.div Real.continuous_cos.continuousOn
        (fun θ hθ => hcos_ne θ hθ)).pow 2
    have h3 : ContinuousOn (fun θ : ℝ => Real.tan θ * deriv f θ * f θ) Iθo :=
      (htan.mul hcd1).mul hsm2.continuousOn
    have h4 : ContinuousOn (fun θ : ℝ => 6 * (f θ) ^ 2) Iθo :=
      (hsm2.continuousOn.pow 2).const_mul 6
    exact ((h1.add h2).add h3).sub h4
  have hcont_lz : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 f θ * f θ) Iθo :=
    hcont_expl.congr (fun θ hθ => (hpoint θ hθ))
  have hσcont : ContinuousOn σ Iθo := by
    have h1 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) Iθo :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    show ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo
    exact h1.rpow_const (fun θ hθ => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hθ.1]) (by linarith [hθ.2]))))
  have haesm : AEStronglyMeasurable
      (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 f θ * f θ * σ θ) (volume.restrict Iθo) :=
    (hcont_lz.mul hσcont).aestronglyMeasurable measurableSet_Ioo
  -- the integrable majorant
  have hmaj : IntegrableOn (fun θ : ℝ => (1 / 2) * ((deriv (fun t => deriv f t) θ) ^ 2 * σ θ)
      + (13 / 2 : ℝ) * ((f θ) ^ 2 * σ θ)
      + ((C * (Real.pi / 2)) ^ 2 + (Real.pi / 2) * C ^ 2) * σ θ) Iθo :=
    (((hdd.mono_set Ioo_subset_Icc_self).const_mul (1 / 2)).add
      ((hu2.mono_set Ioo_subset_Icc_self).const_mul (13 / 2 : ℝ))).add
      ((Work.FTS.EllipticEst.remov.ws_sEta_integrableOn.mono_set
        Ioo_subset_Icc_self).const_mul _)
  -- the pointwise bound
  have hbound : ∀ θ ∈ Iθo, ‖Work.FTS.EllipticEst.Lzero1 f θ * f θ * σ θ‖
      ≤ (1 / 2) * ((deriv (fun t => deriv f t) θ) ^ 2 * σ θ)
        + (13 / 2 : ℝ) * ((f θ) ^ 2 * σ θ)
        + ((C * (Real.pi / 2)) ^ 2 + (Real.pi / 2) * C ^ 2) * σ θ := by
    intro θ hθ
    have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
    have hσnn : 0 ≤ σ θ := Real.rpow_nonneg
      (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2]))) _
    -- `π/2 - θ ≤ (π/2) cos θ`
    have hδle : Real.pi / 2 - θ ≤ (Real.pi / 2) * Real.cos θ := by
      have hδ0 : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
      have hmul : (2 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.cos θ := by
        have h := Real.mul_le_sin (x := Real.pi / 2 - θ) hδ0.le
          (by linarith [Real.pi_pos, hθ.1])
        rwa [Real.sin_pi_div_two_sub] at h
      have hpi : (Real.pi / 2) * (2 / Real.pi) = 1 := by
        have h2 : (2 : ℝ) / Real.pi = (Real.pi / 2)⁻¹ := (inv_div Real.pi 2).symm
        rw [h2, mul_inv_cancel₀ (by positivity : (Real.pi / 2) ≠ 0)]
      have h1 := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ Real.pi / 2)
      rwa [← mul_assoc, hpi, one_mul] at h1
    have hδdiv : (Real.pi / 2 - θ) / Real.cos θ ≤ Real.pi / 2 := by
      rw [div_le_iff₀ hcos]
      exact hδle
    -- `|f θ| / cos θ ≤ C (π/2)`
    have hfcos : |f θ / Real.cos θ| ≤ C * (Real.pi / 2) := by
      rw [abs_div, abs_of_pos hcos]
      calc |f θ| / Real.cos θ ≤ (C * (Real.pi / 2 - θ)) / Real.cos θ :=
            div_le_div_of_nonneg_right (hb2 θ hθ) hcos.le
        _ = C * ((Real.pi / 2 - θ) / Real.cos θ) := by
            rw [div_eq_mul_inv]
            ring
        _ ≤ C * (Real.pi / 2) := mul_le_mul_of_nonneg_left hδdiv hC.le
    have htan_le : |Real.tan θ| ≤ 1 / Real.cos θ := by
      rw [Real.tan_eq_sin_div_cos, abs_div, abs_of_pos hcos]
      exact div_le_div_of_nonneg_right (Real.abs_sin_le_one θ) hcos.le
    -- the four pieces of the explicit form
    have h1 : |-(deriv (fun t => deriv f t) θ) * f θ|
        ≤ ((-(deriv (fun t => deriv f t) θ)) ^ 2 + (f θ) ^ 2) / 2 :=
      abs_mul_le_half_sq _ _
    have h2 : |(f θ / Real.cos θ) ^ 2| ≤ (C * (Real.pi / 2)) ^ 2 := by
      rw [abs_sq]
      have h := pow_le_pow_left₀ (abs_nonneg (f θ / Real.cos θ)) hfcos 2
      rwa [sq_abs] at h
    have h3 : |Real.tan θ * deriv f θ * f θ| ≤ (Real.pi / 2) * C ^ 2 := by
      rw [abs_mul, abs_mul]
      calc |Real.tan θ| * |deriv f θ| * |f θ|
          ≤ (1 / Real.cos θ) * C * (C * (Real.pi / 2 - θ)) := by
            refine mul_le_mul (mul_le_mul htan_le (hb3 θ hθ) (abs_nonneg _)
              (by positivity)) (hb2 θ hθ) (abs_nonneg _) (by positivity)
        _ = C ^ 2 * ((Real.pi / 2 - θ) / Real.cos θ) := by
            rw [div_eq_mul_inv]
            ring
        _ ≤ C ^ 2 * (Real.pi / 2) := mul_le_mul_of_nonneg_left hδdiv (sq_nonneg C)
        _ = (Real.pi / 2) * C ^ 2 := by ring
    have h4 : |6 * (f θ) ^ 2| = 6 * (f θ) ^ 2 := by
      rw [abs_of_nonneg (by positivity)]
    have hkey : |Work.FTS.EllipticEst.Lzero1 f θ * f θ|
        ≤ (1 / 2) * (deriv (fun t => deriv f t) θ) ^ 2 + (13 / 2 : ℝ) * (f θ) ^ 2
          + ((C * (Real.pi / 2)) ^ 2 + (Real.pi / 2) * C ^ 2) := by
      rw [hpoint θ hθ]
      have htri : |-(deriv (fun t => deriv f t) θ) * f θ + (f θ / Real.cos θ) ^ 2
            + Real.tan θ * deriv f θ * f θ - 6 * (f θ) ^ 2|
          ≤ |-(deriv (fun t => deriv f t) θ) * f θ| + |(f θ / Real.cos θ) ^ 2|
            + |Real.tan θ * deriv f θ * f θ| + |6 * (f θ) ^ 2| := by
        have hA := abs_add_le (-(deriv (fun t => deriv f t) θ) * f θ
            + (f θ / Real.cos θ) ^ 2 + Real.tan θ * deriv f θ * f θ)
          (-(6 * (f θ) ^ 2))
        rw [abs_neg] at hA
        have hB := abs_add_le (-(deriv (fun t => deriv f t) θ) * f θ
            + (f θ / Real.cos θ) ^ 2) (Real.tan θ * deriv f θ * f θ)
        have hC' := abs_add_le (-(deriv (fun t => deriv f t) θ) * f θ)
          ((f θ / Real.cos θ) ^ 2)
        have hsplit : -(deriv (fun t => deriv f t) θ) * f θ + (f θ / Real.cos θ) ^ 2
              + Real.tan θ * deriv f θ * f θ - 6 * (f θ) ^ 2
            = (-(deriv (fun t => deriv f t) θ) * f θ + (f θ / Real.cos θ) ^ 2
              + Real.tan θ * deriv f θ * f θ) + (-(6 * (f θ) ^ 2)) := by ring
        rw [hsplit]
        linarith [hA, hB, hC', h4]
      nlinarith [htri, h1, h2, h3]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hσnn]
    calc |Work.FTS.EllipticEst.Lzero1 f θ * f θ| * σ θ
        ≤ ((1 / 2) * (deriv (fun t => deriv f t) θ) ^ 2 + (13 / 2 : ℝ) * (f θ) ^ 2
            + ((C * (Real.pi / 2)) ^ 2 + (Real.pi / 2) * C ^ 2)) * σ θ :=
          mul_le_mul_of_nonneg_right hkey hσnn
      _ = (1 / 2) * ((deriv (fun t => deriv f t) θ) ^ 2 * σ θ)
            + (13 / 2 : ℝ) * ((f θ) ^ 2 * σ θ)
            + ((C * (Real.pi / 2)) ^ 2 + (Real.pi / 2) * C ^ 2) * σ θ := by ring
  have hIntIoo : IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ * σ θ) Iθo :=
    hmaj.mono' haesm (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => hbound θ hθ))
  exact IntegrableOn.congr_set_ae hIntIoo (by
    show Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2)
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2)).symm)

/-! ## The target -/

/-- **L1 — the `σ`-weighted angular self-form lower bound for the slices of an `AeData` datum.**
(File `Submission/Work/FTS/EllipticEst/H2W/Ae/aeSigmaSliceLower.lean`, declaration
`Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower`.)

Route (do prove it; the pieces are all in the tree and are `#print axioms`-clean — check with
`#print axioms`, do NOT trust import-cone greps):
* for a.e. `z`, `Work.FTS.EllipticEst.H2W.AeProof.AeSliceLeftTendstoAe` gives
  `Tendsto (u z) (𝓝[>] 0) (𝓝 0)` and `Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto` gives the
  same at `(π/2)⁻` (for every `z > 0`); `AeData.dirZero`/`AeData.dirPi` give the *values*
  `u z 0 = u z (π/2) = 0`;
* `(∂_θθ u(z,·))² σ` is integrable (`Honest.HkMemSliceSqSigma` + `AeData.memAng2`), hence
  `deriv (u z)` has finite one-sided limits at `0` and `π/2` (Cauchy criterion: the difference of
  two values is bounded by `√(∫(∂_θθu)²σ)·√(∫σ⁻¹)` with `σ⁻¹ = sin(2θ)^η` integrable), so the
  hypotheses of `Work.FTS.EllipticEst.Honest.PthCore.contDiffOnOneExtension` hold;
* apply `Work.FTS.EllipticEst.Honest.HonSliceSigmaLower` (`η = Work.Spaces.eta`, `hη0`, `hη1`)
  to the extension `g`; its hypotheses are `ContDiffOn ℝ 2 g (Ioo 0 (π/2))`,
  `ContDiffOn ℝ 1 g (Icc 0 (π/2))`, `g 0 = g (π/2) = 0`, and the integrability of `(g')²σ`,
  `(g'')²σ`, `g²σ` on `Ioo` and of `Lzero1 g · g · σ` on `Iθ` (the last one via the equation
  `Lzero1 u = G + α²z²∂_zzu + α(5+α)z∂_zu`, `AeData.eq`, plus Cauchy–Schwarz); it gives
  `((1-η)/(1+η))∫(g')²σ ≤ ∫(Lzero1 g)gσ + K∫g²σ`;
* drop the nonnegative left-hand term (so `-K∫g²σ ≤ ∫(Lzero1 g)gσ`) and transfer back to the
  slice: `g` and `u z` agree on `Ioo`, so the `Iθ`-integrals of the two integrands agree.
The constant `K` must depend only on `η` (universal in `α`, `u`, `G`). -/
theorem aeSigmaSliceLower : ∃ K : ℝ, 0 < K ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        -K * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          ≤ ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.Lzero1 (fun θ => u z θ) θ * u z θ
                * Work.FTS.EllipticEst.sEta θ := by
  obtain ⟨K, hK0, hK⟩ :=
    Honest.HonSliceSigmaLower Work.Spaces.eta Work.Spaces.eta_nonneg Work.Spaces.eta_lt_one
  obtain ⟨_C0, _hC0, hSq⟩ := WeakMoment.SliceSqBoundsOpen
  refine ⟨K, hK0, ?_⟩
  intro α u G h
  -- the a.e. left trace, and the a.e. continuity of the slice on the closed interval
  have hL := Work.FTS.EllipticEst.H2W.AeLeftClean.sliceLeftTendstoClean α u G h
  have hC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) Work.Spaces.Iθ := by
    filter_upwards [hL, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hLz hz
    refine Work.FTS.EllipticEst.H2W.AeProof.continuousOn_Icc_of_tendsto
      (by linarith [Real.pi_pos]) ?_ ?_ ?_
    · exact (Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip h.smooth hz 1).continuousOn
    · simpa only [h.dirZero z] using hLz
    · simpa only [h.dirPi z] using
        (Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto α u G h z hz)
  filter_upwards [hL, hC, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
    with z hLz hCz hz
  set f : ℝ → ℝ := fun θ => u z θ with hfdef
  have hf0 : f 0 = 0 := by rw [hfdef]; exact h.dirZero z
  have hfπ : f (Real.pi / 2) = 0 := by rw [hfdef]; exact h.dirPi z
  have hCz' : ContinuousOn f Work.Spaces.Iθ := by simpa only [hfdef] using hCz
  have hLz' : Tendsto f (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    simpa only [hfdef] using hLz
  have hπlim : Tendsto f (nhdsWithin (Real.pi / 2) (Iio (Real.pi / 2))) (nhds 0) := by
    simpa only [hfdef] using
      (Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto α u G h z hz)
  -- the slice is smooth on the open interval
  have hsm_all : ∀ n : ℕ, ContDiffOn ℝ n f Iθo := fun n =>
    Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip h.smooth hz n
  have hsm2 : ContDiffOn ℝ 2 f Iθo := hsm_all 2
  -- `(∂_θθ u(z,·))²σ` is integrable
  have hdd : IntegrableOn (fun θ => (deriv (fun t => deriv f t) θ) ^ 2 * σ θ)
      Work.Spaces.Iθ := by
    have h1 : IntegrableOn (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * σ θ)
        Work.Spaces.Iθ := Honest.HkMemSliceSqSigma (α := α) h.memAng2 hz
    refine h1.congr_fun (fun θ _ => ?_) measurableSet_Icc
    change Work.Spaces.pthIter 2 u z θ ^ 2 * σ θ = deriv (fun t : ℝ => deriv f t) θ ^ 2 * σ θ
    have hpth : Work.Spaces.pthIter 2 u z θ = deriv (fun t : ℝ => deriv f t) θ := rfl
    rw [hpth]
  -- `f²σ` and `(f')²σ` are integrable on `Iθ`
  obtain ⟨hu2, _hu2b, hdu, _hdub⟩ := hSq f hsm_all hCz' hf0 hfπ hdd
  -- the endpoint bounds
  obtain ⟨C, hCpos, _hb1, hb2, hb3⟩ :=
    AngAWeak.angSliceBoundsWeak f hsm2 hCz' hf0 hfπ hdd
  -- the `Lzero1`-self-form integrand is integrable on the slice
  have hlz : IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ * σ θ)
      Work.Spaces.Iθ :=
    slice_lzero_sigma_integrable hCpos hsm2 hdd hu2 hb2 hb3
  -- the one-sided limits of `deriv`
  obtain ⟨hlim0, hlimπ⟩ := slice_deriv_limits hsm2 hdd
  -- the `C¹` extension of the slice to the closed interval
  obtain ⟨g, hg1, hg0, hgpi, hgeq⟩ :=
    Honest.PthCore.contDiffOnOneExtension (f := f) (hsm_all 1) hLz' hπlim hlim0 hlimπ
  -- the slice itself is `C²` on the open interval and `C¹` on the closed one
  have hg2 : ContDiffOn ℝ 2 g Iθo := hsm2.congr (fun x hx => (hgeq x hx).1)
  have hgeqIcc : ∀ θ ∈ Work.Spaces.Iθ, g θ = f θ := by
    intro θ hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · rw [← h0, hg0, hf0]
    rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · rw [h1, hgpi, hfπ]
    · exact (hgeq θ ⟨h0, h1⟩).1
  have hf1 : ContDiffOn ℝ 1 f Work.Spaces.Iθ :=
    hg1.congr (fun x hx => (hgeqIcc x hx).symm)
  -- the honest slicewise coercivity
  have hres := hK f hsm2 hf1 hf0 hfπ
    (hdu.mono_set Ioo_subset_Icc_self) (hdd.mono_set Ioo_subset_Icc_self)
    (hu2.mono_set Ioo_subset_Icc_self) hlz
  -- drop the nonnegative derivative term
  have hnn : 0 ≤ ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
      * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * σ θ) := by
    refine mul_nonneg ?_ ?_
    · have h1 : (0 : ℝ) < 1 + Work.Spaces.eta := by linarith [Work.Spaces.eta_nonneg]
      exact div_nonneg (by linarith [Work.Spaces.eta_lt_one]) h1.le
    · exact MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
        (fun θ hθ => mul_nonneg (sq_nonneg _) (sigma_nonneg_Iθ hθ))
  have hfinal : -K * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * σ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 f θ * f θ * σ θ := by
    have h := hres
    have h2 := hnn
    simp only [Work.FTS.EllipticEst.sEta] at h h2 ⊢
    linarith
  simpa only [hfdef] using hfinal

end Work.FTS.EllipticEst.H2W.Ae
end
end
