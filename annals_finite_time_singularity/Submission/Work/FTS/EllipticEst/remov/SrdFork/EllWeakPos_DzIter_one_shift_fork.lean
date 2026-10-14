import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.Zsq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.Dz_slice_identities
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.CleanBase
import Submission.Work.FTS.H2.T2Qaux.SupAux
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zSchurWindowDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option autoImplicit false

/-! ## The angular weight `σ_η` at the two endpoints -/

theorem thEta_zero : Work.FTS.EllipticEst.thEta 0 = 0 := by
  rw [Work.FTS.EllipticEst.thEta, show (2 : ℝ) * 0 = 0 by norm_num, Real.sin_zero]
  exact Real.zero_rpow (by norm_num [Work.Spaces.eta])

theorem thEta_pi_half : Work.FTS.EllipticEst.thEta (Real.pi / 2) = 0 := by
  rw [Work.FTS.EllipticEst.thEta, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  exact Real.zero_rpow (by norm_num [Work.Spaces.eta])

theorem measurable_thEta : Measurable Work.FTS.EllipticEst.thEta :=
  Measurable.pow_const (Real.measurable_sin.comp (measurable_const.mul measurable_id))
    (-(Work.Spaces.eta))

/-! ## The pointwise majorant of the angular derivative of a slice -/

/-- **The pointwise majorant of `∂_θG(z, ·)`.**  For a trace-class datum `G` and `z > 0`, the
angular derivative of the slice satisfies

  `|∂_θG(z,s)| ≤ |∂_θG(z,π/4)| + √(∫_{Iθ} (∂_θ²G(z,θ))² σ_η θ) · √(π/4)`

for every `s ∈ (0, π/2)` (fundamental theorem of calculus from the landmark angle `π/4`
together with the interval Cauchy–Schwarz bound); `thSliceMajorant G z` is the square of that
bound.  The proofs are `pth_slice_sq_le_majorant` (the pointwise bound) and
`win_majorant_integrable` (its integrability along the logarithmic window). -/
def thSliceMajorant (G : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (|Work.Spaces.pth G z (Real.pi / 4)|
    + Real.sqrt (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      * Real.sqrt (Real.pi / 4)) ^ 2

theorem thSliceMajorant_nonneg (G : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ thSliceMajorant G z :=
  sq_nonneg _

/-! ## The kernel `sKerd δ` is bounded and supported in `[-δ, δ]` -/

/-- **Bound and support of the derivative kernel.**  For `δ > 0` the continuous kernel
`sKerd δ = deriv (sKer δ)` (whose support is contained in `(-δ, δ)`) is bounded on all of `ℝ`
by some `M ≥ 0`. -/
theorem exists_sKerd_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ u : ℝ, |Work.FTS.EllSol.EllPkgAux.sKerd δ u| ≤ M) ∧
      (∀ u : ℝ, δ < |u| → Work.FTS.EllSol.EllPkgAux.sKerd δ u = 0) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -δ) (b := δ)).exists_bound_of_continuousOn
    (Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd δ).continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_, ?_⟩
  · intro u
    by_cases hu : u ∈ Set.Icc (-δ) δ
    · have h := hC u hu
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_max_left _ _)
    · have hlt : δ < |u| := by
        rw [Set.mem_Icc, not_and_or] at hu
        rcases hu with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have hz : Work.FTS.EllSol.EllPkgAux.sKerd δ u = 0 :=
        Work.FTS.EllSol.PkgK5.i0TraceMoll.AuxDz.sKerd_eq_zero_of_le_abs hδ (le_of_lt hlt)
      rw [hz, abs_zero]
      exact le_max_right _ _
  · intro u hu
    exact Work.FTS.EllSol.PkgK5.i0TraceMoll.AuxDz.sKerd_eq_zero_of_le_abs hδ (le_of_lt hu)

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.aeSigmaUpgradeRho =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

/-! ## Elementary facts about the two `θ`-integrals and the two radial domains -/


/-- `Iz = [0,∞)` and `Ioi 0` carry the same measure (`{0}` is null). -/
private theorem restrict_Iz_eq_restrict_Ioi_prv :
    MeasureTheory.volume.restrict Iz = MeasureTheory.volume.restrict (Set.Ioi 0) := by
  rw [Work.Spaces.Iz]
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))]


/-! ## The per-slice honesty of `∂_θu` -/

/-- **For `z > 0` the angular slice of `∂_θu` is square-integrable.**  The `HkMem`-honesty of
`∂_θθu` (which `AeData` supplies) makes `(∂_θθu(z,·))²σ` integrable, hence `∂_θθu(z,·) ∈ L¹`
by Cauchy–Schwarz against `σ^{-1} = sin(2θ)^{η} ∈ L¹`; then `∂_θu(z,·)` has finite endpoint
limits and is bounded (`SliceBddSqSigma`), and a bounded function on `Iθ` is square
integrable. -/
private theorem slice_pth_sq_integrable {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth u z θ) ^ 2) Iθ := by
  have hsm2 : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Honest.contDiffOn_slice u hz (h.smooth 2)
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t : ℝ => deriv (fun θ' => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Iθ := by
    have h0 := Work.FTS.EllipticEst.Honest.HkMemSliceSqSigma h.memAng2 hz
    simpa only [Work.Spaces.pth, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
      Nat.reduceAdd] using h0
  obtain ⟨C, _hCpos, hC⟩ := Work.FTS.EllipticEst.Honest.SliceBddSqSigma hsm2 h2
  have hvol : (MeasureTheory.volume : Measure ℝ) Iθ < ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  refine MeasureTheory.IntegrableOn.of_bound hvol
    ((measurable_deriv (fun t : ℝ => u z t)).aestronglyMeasurable.pow 2) (C ^ 2) ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo fun θ hθ => ?_
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  calc (deriv (fun t : ℝ => u z t) θ) ^ 2
      = |deriv (fun t : ℝ => u z t) θ| ^ 2 := by rw [sq_abs]
    _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hC θ hθ).1 2

/-! ## The `L2Mem` hypothesis of `aeSigmaUp` from the weak integral hypothesis -/


/-! ## The target -/


end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Pieces.TopSlotAux.lowSlots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `lowSlots`: the three low angular slots of the elliptic `ℋ^k` estimate

The target is the low-order angular part of Elgindi's `ℋ^k` elliptic estimate: for a datum
`EllWeakPos α k F Ψ` of the weak class with `k ≥ 3` and under the single level-`(k-1)` norm bound

  `α²|z²∂_z²Ψ|_{ℋ^{k-1}} + |∂_θθΨ|_{ℋ^{k-1}} ≤ D |F|_{ℋ^k}`,

the three slots `∫∫ w²(∂_θθΨ)²σ`, `∫∫ w²(∂_θΨ)²` and `∫∫ w²Ψ²` (the `η`-term and the two
`L²`-bounded slots of `TopSlotRhsDom`) are bounded by `C·|F|²_{ℋ^k}`, with `C` depending on `D`
and `k` only.

The proof has two parts.

* The `η`-slot `∫∫ w²(∂_θθΨ)² σ` is a single summand of the `ℋ^{k-1}`-integrand of
  `∂_θθΨ` (the `i = 0` slot, `σ = sin(2θ)^{-η}`), so it is at most
  `HkSq α (k-1) (∂_θθΨ) ≤ D²·HkSq α k F` — the second inequality being the square of the
  hypothesis (via `HkSq_eq_HkNorm_sq`).  The level-`(k-1)` honesty of `∂_θθΨ` is
  `HkMem_descend_open` applied to `EllWeakPos.memB`.

* The two `L²`-slots are handled *slicewise* by the proved all-order slice bound
  `TT.ESW.low_order_le`:  for `z > 0` the slice `u = Ψ z ·` is `C²` on `(0,π/2)` with vanishing
  angular moment, right endpoint limit `0` and `∫(u'')²σ < ∞`, and the first-order slice bound
  `∫(u')² + ∫u² ≤ 20∫(u'')²σ` holds (`TT.ESW.slice_low_order`).  Integrating the resulting
  pointwise (in `z`) bounds `∫(∂_θΨ)² ≤ 20∫(∂_θθΨ)²σ` and `∫Ψ² ≤ 20∫(∂_θθΨ)²σ` against `w²`
  needs only the honest integrability of `z ↦ w(z)²∫(∂_θθΨ)²σ`, which is the
  `i = 0`-slot of `HkMem α k (∂_θθΨ)` (`TT.ESW.integrable_w_sq_thetaEnergy`); the two
  `L²`-integrands themselves need not be integrable thanks to `integral_mono_of_nonneg`.

Constants are existential, so all losses are absorbed into `C = 41 D² + 1`.
-/

namespace Work.FTS.EllipticEst.Cores.Pieces.TopSlotAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

/-- **The `i = 0` slot of the `ℋ^k`-integrand dominates the `η`-weighted square of the centre.**
For `f` with honest `ℋ^k`-integrand and `z ∈ Iz`,
`w(z)²·∫_θ (f z θ)² σ(θ) ≤ ∫_θ HkIntegrand α k f z θ`.  This is the per-`z` comparison behind
`Work.Spaces.L2Sq_DzIter_le_HkSq` at `i = 0`. -/
private theorem slot_le_HkIntegrand {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k g) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 z hz) ?_
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _)
        (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.Honest.sEta_nonneg hθ))
  · refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo fun θ hθ => ?_
    have h1 := Work.Spaces.sq_le_HkIntegrand_z α k g z θ 0 (Nat.zero_le k)
    simp only [Work.Spaces.DzIter_zero] at h1
    have h2 := Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z)
      (show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    simp only [Work.FTS.EllipticEst.sEta] at h1 ⊢
    calc (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by ring
      _ = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
          h2.symm
      _ ≤ Work.Spaces.HkIntegrand α k g z θ := h1




end Work.FTS.EllipticEst.Cores.Pieces.TopSlotAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Slot01W.DzSliceIdent =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- DECLARATION THINNING: this module was byte-identical (modulo imports) to
-- `Submission.Work.FTS.EllipticEst.remov.Dz_slice_identities` (same namespaces), so importing both was a duplicate-declaration error.
-- The names stay available to every consumer through the import above.
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SrdFork.EllWeakPos_DzIter_one_shift_fork =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Tools

Three bookkeeping facts are needed, none of which is analytic:

* `SmoothOpen_of_bslOp_eq`: the source `F` of the weak class is `C^∞` on the open quadrant,
  because there it coincides with `bslOp α Ψ`;
* `HkMem_Dz_shift`: the *membership* form of the `D_z`-shift
  `HkIntegrand α (k-1) (D_z f) ≤ (k + k²)·HkIntegrand α k f` (`Step.HkIntegrand_shift_le`),
  obtained through the domination lemma `HkMem_of_majorant_ae`;
* `Dz_pthIter2_eq`: `D_z` commutes with `∂_θ²` on the open quadrant (Clairaut twice). -/

/-- **The source of the weak class is `C^∞` on the open quadrant.**  On `Q0` it agrees with
`bslOp α Ψ`, which is `C^∞` there by `SmoothOpen_bslOp_of_smoothOpen`. -/
theorem SmoothOpen_of_bslOp_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ) :
    Work.FTS.EllipticEst.SmoothOpen F :=
  Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨ) heq

/-- The shifted mixed slots, at the genuine smooth order: for `f` of class `C^∞` on the open
quadrant and `(z,θ)` in the open quadrant, `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f`.
This is `D_z`-commutation with `D_θ^i` (`DthIterDzCommOpen`) followed by
`D_z^j (D_z g) = D_z^{j+1} g` and the local congruence of iterated `D_z` on the open quadrant. -/
theorem mixed_Dz_shift_eq {j i : ℕ} (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (j + 1) i f z θ := by
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i f)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz f))) Step.Qd :=
    Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen f hg i
  have hpt : (z, θ) ∈ Step.Qd := ⟨hz, hθ⟩
  have hcongr : Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.DthIter i f)) z θ :=
    Step.DzIter_congr_of_isOpen Step.isOpen_Qd hcomm.symm j hpt
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
    = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i f) z θ
  rw [hcongr, Step.DzIter_Dz j (Work.Spaces.DthIter i f)]

/-- **The pointwise `D_z`-shift bound on the open quadrant, at the genuine smooth order.**
Every slot of `HkIntegrand α (k-1) (D_z f)` is a slot of `HkIntegrand α k f` (up to the
commutation of `D_z` with `D_θ^i`), and each single slot is dominated by the whole integrand;
counting `k` radial and `k·k` mixed slots gives the factor `k + k²`. -/
theorem HkIntegrand_Dz_shift_le (α : ℝ) {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hZ : Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
      ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
    have hterm : ∀ i ∈ Finset.range k,
        (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hik : i + 1 ≤ k := by
        have := Finset.mem_range.mp hi
        omega
      rw [Step.DzIter_Dz i f]
      exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ (i + 1) hik
    have h1 : Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
        = ∑ i ∈ Finset.range k,
            (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2 := by
      unfold Step.Zsum
      exact Finset.sum_congr (by rw [show k - 1 + 1 = k from by omega])
        (fun i _ => rfl)
    rw [h1]
    calc (∑ i ∈ Finset.range k,
          (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2)
        ≤ ∑ _i ∈ Finset.range k, Work.Spaces.HkIntegrand α k f z θ :=
          Finset.sum_le_sum hterm
      _ = (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM : Step.Msum α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
    rw [Step.Msum_eq_rows, show k - 1 + 1 = k from by omega]
    have hterm : ∀ i ∈ Finset.range k,
        (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hstep : (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _j ∈ Finset.range (k - i), Work.Spaces.HkIntegrand α k f z θ := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        by_cases hi1 : 1 ≤ i
        · rw [if_pos hi1]
          rw [mixed_Dz_shift_eq f hz hθ hg]
          have hj' : i + (j + 1) ≤ k := by
            have := Finset.mem_range.mp hj
            omega
          exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i (j + 1) hi1 hj'
        · rw [if_neg hi1]
          exact hHnn
      refine le_trans hstep ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hcast : ((k - i : ℕ) : ℝ) ≤ (k : ℝ) := by
        have : k - i ≤ k := by omega
        exact_mod_cast this
      have hci : (0 : ℝ) ≤ ((k - i : ℕ) : ℝ) := by positivity
      nlinarith [hHnn, hcast, hci]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hsum : (∑ _i ∈ Finset.range k, (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ)
        = ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    exact hsum.le
  rw [Step.HkIntegrand_eq α k f z θ] at hZ hM ⊢
  rw [Step.HkIntegrand_eq α (k - 1) (Work.Spaces.Dz f) z θ]
  have hnn : 0 ≤ Step.Zsum k f z θ + Step.Msum α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  nlinarith [hZ, hM, hnn]

/-- **`∂_z` commutes with `∂_θ²` on the open quadrant**: Clairaut's theorem applied twice
(the first step with `∂_θ Ψ` as the function, the second by congruence on the open set). -/
theorem pz_pthIter_two_comm {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.AgreeOnQ
      (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ))
      (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ)) := by
  intro z θ hz hθ hlt
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hlt⟩
  have hcd : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      ContDiffAt ℝ 2 (Function.uncurry Ψ) (z', θ') := fun z' θ' hz' hθ' hlt' =>
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mp hΨ 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ', hlt'⟩))
  have hcd_pth : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth Ψ)) (z, θ) :=
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.pth Ψ)).mp
      (Work.FTS.EllipticEst.SmoothOpen.pth hΨ) 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  have h1 : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Ψ)) z θ :=
    Work.Spaces.pz_pth_comm (f := Work.Spaces.pth Ψ) hcd_pth
  have hagree : Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.pz (Work.Spaces.pth Ψ))
      (Work.Spaces.pth (Work.Spaces.pz Ψ)) :=
    fun z' θ' hz' hθ' hlt' => Work.Spaces.pz_pth_comm (f := Ψ) (hcd z' θ' hz' hθ' hlt')
  have h2 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz Ψ)) z θ :=
    Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
      (fun p hp => by
        obtain ⟨z', θ'⟩ := p
        exact hagree z' θ' hp.1 hp.2.1 hp.2.2) hmem
  show Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  exact h1.trans h2

/-- **`D_z` commutes with `∂_θ²` on the open quadrant.**  Since `D_z f = z·∂_z f` and the
factor `z` does not depend on `θ`, the plain commutation `pz_pthIter_two_comm` gives the
identity for `D_z` as well. -/
theorem Dz_pthIter_two_comm {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ))
      (Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)) := by
  have hplain := pz_pthIter_two_comm hΨ
  have hmul : Work.Spaces.pth (Work.Spaces.Dz Ψ)
      = fun z θ => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ := by
    funext z θ
    show deriv (fun θ' => z * Work.Spaces.pz Ψ z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz Ψ z θ') θ
    rw [deriv_const_mul_field]
  have hstep : Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)
      = fun z θ => z * Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ := by
    have h2 : Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)
        = Work.Spaces.pth (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ) := by
      rw [← hmul]
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
    rw [h2]
    funext z θ
    show deriv (fun θ' => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pth (Work.Spaces.pz Ψ) z θ') θ
    rw [deriv_const_mul_field]
  intro z θ hz hθ hlt
  show z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ) z θ
  rw [hstep, hplain z θ hz hθ hlt]

/-! ## The target -/

/-- **The assembly of the shift, given the two moment conditions.**

All nine fields of `EllWeakPos α (k-1) (D_z F) (D_z Ψ)` are produced here except the two moment
conditions, which are supplied as explicit hypotheses:

* the equation is preserved because `bslOp` commutes with `D_z`
  (`Work.FTS.EllipticEst.TT.bslOp_DzIter_eq`);
* the Dirichlet data are preserved (`Work.FTS.EllipticEst.TT.DzIter_zero_at_zero`,
  `..._pi_half`);
* the smoothness is preserved (`SmoothOpen.DzIter`);
* the `ℋ`-membership of the three fields follows from the pointwise domination
  `HkIntegrand α (k-1) (D_z g) ≤ ((k:ℝ)+(k:ℝ)*(k:ℝ)) * HkIntegrand α k g`
  (`Work.FTS.EllipticEst.remov.HkIntegrand_Dz_shift_le`, at the genuine `C^∞` order, via
  `Work.FTS.EllipticEst.HkMem_of_majorant_ae`) for `g ∈ {F, z²∂_zzΨ, ∂_θθΨ}`;
* the auxiliary identities are `pthIter 2 (D_z Ψ) = D_z (pthIter 2 Ψ)`
  (`Dz_pthIter_two_comm`) and `z² ∂_zz(D_z Ψ) = D_z (z² ∂_zzΨ)`
  (`Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm`), both pointwise on the open quadrant. -/
theorem EllWeakPos_DzIter_one_shift_of_moments {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hmomF : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0)
    (hmomΨ : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.TT.EllWeakPos.smoothOpen h
  have hSF : Work.FTS.EllipticEst.SmoothOpen F :=
    SmoothOpen_of_bslOp_eq hSΨ (fun z θ hz hθ hlt => h.1 z hz θ hθ hlt)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the equation commutes with `D_z`
    exact Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 1 h.smooth h.1
  · -- the Dirichlet data at `θ = 0`
    exact Work.FTS.EllipticEst.TT.DzIter_zero_at_zero Ψ 1 h.zero
  · -- the Dirichlet data at `θ = π/2`
    exact Work.FTS.EllipticEst.TT.DzIter_zero_at_pi_half Ψ 1 h.pi_half
  · -- the source moment condition
    exact hmomF
  · -- the solution moment condition
    exact hmomΨ
  · -- smoothness on the open quadrant is preserved by `D_z`
    intro n
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.DzIter 1 Ψ)).mp
      (Work.FTS.EllipticEst.TT.EllWeakPos.smoothOpen_DzIter h 1) n
  · -- `D_z F ∈ ℋ^{k-1}`
    have hmem : Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz F) :=
      HkMem_Dz_shift hk hSF h.memF
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hmem
  · -- `z² ∂_zz(D_z Ψ) ∈ ℋ^{k-1}`
    have hG : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      Work.FTS.EllipticEst.AeMom.Repair.SmoothOpen.zsq_mul (Work.FTS.EllipticEst.SmoothOpen.pzIter hSΨ 2)
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
      HkMem_Dz_shift hk hG h.memA
    have hEqOn := Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm Ψ hSΨ 1 0
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    exact (hEqOn (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
      from ⟨hz, hθ⟩)).symm
  · -- `∂_θθ(D_z Ψ) ∈ ℋ^{k-1}`
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) :=
      HkMem_Dz_shift hk (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hSΨ 2) h.memB
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    exact Dz_pthIter_two_comm hSΨ z θ hz hθ.1 hθ.2
  · -- `z ∂_z∂_θθ(D_z Ψ) ∈ ℋ^{k-1}`
    have hGs : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) :=
      Work.FTS.EllipticEst.SmoothOpen.Dz
        (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hSΨ 2)
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) :=
      HkMem_Dz_shift hk hGs h.memZPth2
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    have hEqOn : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)))
        (Function.uncurry (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      rintro ⟨z', θ'⟩ ⟨hz', hθ'⟩
      exact Dz_pthIter_two_comm hSΨ z' θ' hz' hθ'.1 hθ'.2
    have hpe : Work.Spaces.pz (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ
        = Work.Spaces.pz (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ :=
      Work.Spaces.pz_congr_of_isOpen (isOpen_Ioi.prod isOpen_Ioo)
        hEqOn.symm ⟨hz, hθ⟩
    rw [hpe]
    rfl


/-- **The shift, for `2 ≤ k`.**  This is the instance of `EllWeakPos_DzIter_one_shift` which is
needed by the induction step of `prop:Hk` (the shifted data are consumed at level `k-1 ≥ 2`) and
by `shift_weak`; here both moment conditions are available from the *proved* lemmas
`Fstar_DzIter_one_F_ge_two` (the `F`-half, via the chain rule at `j = 0, 1` and the continuity of
`F_*(D_z F)`) and `Fstar_DzIter_one_Psi` (the `Ψ`-half, by the first-order difference-quotient
argument), so the statement is complete. -/
theorem EllWeakPos_DzIter_one_shift_of_two_le {α : ℝ} {k : ℕ} (hk : 2 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) :=
  EllWeakPos_DzIter_one_shift_of_moments (by omega) h
    (Fstar_DzIter_one_F_ge_two hk h) (Fstar_DzIter_one_Psi (by omega) h)

end Work.FTS.EllipticEst.remov
end
end
