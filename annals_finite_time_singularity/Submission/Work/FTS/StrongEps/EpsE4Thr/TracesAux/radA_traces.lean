import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.radA_jet_small
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_const_mul
import Submission.Work.FTS.StrongEps.EpsLocalPStar.JepsMarginalZero_zero
import Submission.Work.FTS.StrongEps.EpsRLX.N0DiffClassC
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.HomClsSlotsZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

set_option autoImplicit false

/-- **The slots of the packages depend only on the source** (the pivot replacement of the refuted
`HomClsZero`).  The packages `EllPkgGo`/`EllPkgK` constrain a solution `Ψ` of the elliptic law with
source `F` only through the three *slots* `Rop α (PhiTil α F Ψ)`, `Uop α (PhiTil α F Ψ) / sin 2θ`,
`Vop (PhiTil α F Ψ)`; that is literally how `N` and `gRHS` consume the stream function:
`N α F Φ = 2·Rop(PhiTil) z θ·F - 2·Uop(PhiTil)·∂_θF - 2α·Vop(PhiTil)·D_zF - …`, so the whole
right-hand side of the scheme sees `Φ` only through the three slots.  Moreover *uniqueness* of `Ψ`
in that class is **false**: a sibling delegate proved
`Work.FTS.StrongEps.EComparison.HomClsZeroRefute.exists_counterexample`
(`Submission/Work/FTS/StrongEps/EComparison/HomClsZeroRefute.lean`, `sorry`-free), with the
homogeneous mode `z^{-3/α} / cos θ` (the special radial exponent `α s = -3`, for which
`Uop α (mode) ≡ 0`, `Vop (mode) ≡ 0`, `Rop α (mode) ≡ 0`, so the three `HkMem` hypotheses of the
class hold *vacuously*).

The assertion below is that the *slots*, unlike `Ψ` itself, are still pinned by the source
(equivalently, by the closure of `EllPkgCls` under differences, that every homogeneous element of
the class has vanishing slots on the open quadrant).  This is exactly the input that
`EComparison.E_sub_eq_of_uniq` needs in place of the refuted `Ψ`-uniqueness.

The conclusion is restricted to the *open* quadrant `θ ∈ (0, π/2)`, as two reviews required: the
five hypotheses only constrain `w` on `Q0`/`Iθ` (and `SmoothOpen`, `IsBslSol` and all three
`HkMem`-integrands see nothing outside `(0,∞) × (0,π/2)`), so an extension of a quadrant solution
that is non-trivial off `(0,π/2)` satisfies everything and breaks an unrestricted `∀ θ : ℝ`.  Nothing
is lost downstream: the slots are compared only through `HkSq`/`HkMem`, which integrate over `Iθ`.

Route.  `bslOp α w = 0` with the Dirichlet data and the `z`-decay; a separable homogeneous mode
`w = z^r ψ(θ)` must satisfy `α²r² + 5αr = λ` for an eigenvalue `λ` of the angular operator
`Lzero`, and then `Rop α w = z^r((2+αr) tan θ · ψ + ψ')` etc.: a mode whose slot does *not* vanish
has a `z`-profile whose exponent conflicts with the (non-vacuous) `HkMem` bound — the weight
`Work.Spaces.w(z)² ≍ z^{-4}` at `z → 0⁺` forces the slot's `z`-moment to be finite, while the decay
conjunct of `IsBslSol` forces the opposite growth.  A review checked the eigenfunction `tan θ` and
the combinations `a tanθ + b secθ`: their slots are `∝ z^{-3/α}` and fail `hR`/`hV`, while the
`αr = -3`, `ψ = 1/cos θ` mode has all three slots identically zero.  The class is not vacuous for
the *slots*: `w = z^{-5/α} sin 2θ` has `Rop α w = z^{-5/α}(2cos2θ - 6sin²θ) ≠ 0` and is correctly
excluded by `HkMem α 6 (Rop α w)`. -/
theorem HomClsSlotsZero {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {w : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen w)
    (hsol : Work.Elliptic.IsBslSol α (fun _ _ => (0 : ℝ)) w)
    (hR : Work.Spaces.HkMem α 6 (Work.Construction.Rop α w))
    (hU : Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.Uop α w z θ / Work.Construction.s2 θ))
    (hV : Work.Spaces.HkMem α 6 (Work.Construction.Vop w)) :
    (∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Rop α w z θ = 0) ∧
    (∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Uop α w z θ = 0) ∧
    (∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Vop w z θ = 0) := by
  -- ## The auxiliary homogeneous solution `Φ = Uop α w = -3w - α·D_z w`
  set Φ : ℝ → ℝ → ℝ := Work.Construction.Uop α w with hΦdef
  have hΦfun : Φ = fun z θ => (-3 : ℝ) • w z θ + (-α) • (Work.Spaces.Dz w) z θ := by
    funext z θ
    simp only [hΦdef, Work.Construction.Uop, Work.Spaces.Dz, Work.Spaces.pz, smul_eq_mul]
    ring
  have hsm' : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry w) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall w).mp hsm n
  have hDzsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz w) := hsm.Dz
  -- `Φ` is `C^∞` on the open quadrant
  have hΦsm : Work.FTS.EllipticEst.SmoothOpen Φ := by
    rw [Work.FTS.EllipticEst.smoothOpen_iff_forall]
    intro n
    have h1 : ContDiffOn ℝ n (Function.uncurry w) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hsm' n
    have h2 : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz w))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.Dz w)).mp hDzsm n
    have h3 : ContDiffOn ℝ n (fun p : ℝ × ℝ => (-3 : ℝ) • Function.uncurry w p
        + (-α) • Function.uncurry (Work.Spaces.Dz w) p) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (h1.const_smul (-3)).add (h2.const_smul (-α))
    have hfun : Function.uncurry Φ = fun p : ℝ × ℝ => (-3 : ℝ) • Function.uncurry w p
        + (-α) • Function.uncurry (Work.Spaces.Dz w) p := by
      funext p
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry, hΦfun, Work.Spaces.Dz, Work.Spaces.pz, smul_eq_mul]
    rwa [hfun]
  have hΦcont : ContinuousOn (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mp hΦsm 0).continuousOn
  -- ## the equation for `Φ`
  have hw_eq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α w z θ = 0 := by
    intro z hz θ h0 h1
    have h := hsol.1 z hz θ h0 h1
    simpa using h
  have hΦsol : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Φ z θ = 0 := by
    intro z hz θ h0 h1
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩)
    have hv : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h0, h1⟩
    have hnb : (Work.FTS.EllipticEst.Q0 : Set (ℝ × ℝ)) ∈ 𝓝 (z, θ) :=
      Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hv
    have hD1 : Work.Elliptic.bslOp α (Work.Spaces.Dz w) z θ = 0 := by
      have h := Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α (fun _ _ => (0 : ℝ)) w 1
        hsm' hw_eq z hz θ h0 h1
      have hz0 : Work.Spaces.DzIter 1 (fun _ _ => (0 : ℝ)) z θ = 0 := by
        simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
          Work.Spaces.pz]
        simp
      rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] at h
      rw [h, hz0]
    have hAdd : Work.Elliptic.bslOp α Φ z θ
        = (-3 : ℝ) * Work.Elliptic.bslOp α w z θ
          + (-α) * Work.Elliptic.bslOp α (Work.Spaces.Dz w) z θ := by
      rw [hΦfun]
      have hb3 : Work.Elliptic.bslOp α (fun z θ => (-3 : ℝ) • w z θ) z θ
          = (-3 : ℝ) * Work.Elliptic.bslOp α w z θ := by
        simpa only [smul_eq_mul] using
          Work.FTS.BSIdent.OddExt.bslOp_const_mul α (-3) w z θ
      have hba : Work.Elliptic.bslOp α (fun z θ => (-α) • (Work.Spaces.Dz w) z θ) z θ
          = (-α) * Work.Elliptic.bslOp α (Work.Spaces.Dz w) z θ := by
        simpa only [smul_eq_mul] using
          Work.FTS.BSIdent.OddExt.bslOp_const_mul α (-α) (Work.Spaces.Dz w) z θ
      rw [Work.Elliptic.bslOp_add α (fun z θ => (-3 : ℝ) • w z θ)
        (fun z θ => (-α) • (Work.Spaces.Dz w) z θ) z θ hcos]
      · rw [hb3, hba]
      · exact ((hsm' 2).contDiffAt hnb).const_smul (-3)
      · exact (((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.Dz w)).mp hDzsm 2).contDiffAt
          hnb).const_smul (-α)
    rw [hAdd, hw_eq z hz θ h0 h1, hD1]
    ring
  -- ## the Dirichlet value at `θ = 0`
  have hΦ0 : ∀ z, Φ z 0 = 0 := by
    intro z
    have hw0 : w z 0 = 0 := hsol.2.1 z
    have hpz0 : Work.Spaces.pz w z 0 = 0 := by
      have hfun : (fun z' : ℝ => w z' 0) = fun _ => (0 : ℝ) :=
        funext fun z' => hsol.2.1 z'
      simp only [Work.Spaces.pz]
      rw [hfun, deriv_const]
    simp only [hΦdef, Work.Construction.Uop]
    rw [hw0, hpz0]
    ring
  -- ## the slot hypothesis for `Φ`
  have hHk : Work.Spaces.HkMem α 6 (fun z θ => Φ z θ / Work.Construction.s2 θ) := hU
  -- ## the slice integrability
  have hInt : ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => Φ z θ ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
    SlotsZeroSliceInt hΦsm hΦ0 hHk
  -- ## all modal moments vanish for a.e. `z`
  have hMom : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∀ m : ℕ, (∫ θ in Work.Spaces.Iθ,
        Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) = 0 := by
    refine MeasureTheory.ae_all_iff.mpr (fun m => ?_)
    have hC1 := SlotsZeroModeODE (α := α) (Φ := Φ)
      (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mp hΦsm n) hΦsol hΦ0 hHk m
    exact EulerWeakZero (α := α) (L := Work.FTS.PhiStar.Gegenbauer.lam m) hα hC1.1 hC1.2.1 hC1.2.2
  -- ## `Φ` vanishes on the open quadrant
  have hΦzero : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Φ z θ = 0 :=
    SlotsZeroComplete (Φ := Φ) hΦcont hInt hMom
  have hUzero : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Uop α w z θ = 0 := by
    intro z hz θ hθ
    have h := hΦzero z hz θ hθ
    simpa only [← hΦdef] using h
  exact SlotsZeroRest hα hsm hUzero hV

end Work.FTS.StrongEps.EComparison
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.radA_traces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.TracesAux

/-! ## The two one-dimensional reductions

With `w z = (1+z)²/z²` one has `z·(m·w z)² = m²·(1+z)^4/z³`, so a jet bound
`|m| ≤ K z²` near `0` (resp. `|m| ≤ K/z` at `∞`) gives the two boundary traces.  These are the
two elementary facts that turn a jet estimate on `radA α x` into the trace conclusion. -/

/-- **The trace at `z → 0⁺` from a quadratic jet bound.**  If `|f z| ≤ K z²` on `(0,1)` then
`z·(f z·w z)² → 0` as `z → 0⁺` (the bound is `≤ 16 K² z`). -/
theorem tendsto_z_mul_w_sq_small {f : ℝ → ℝ} {K : ℝ}
    (h : ∀ z : ℝ, 0 < z → z < 1 → |f z| ≤ K * z ^ 2) :
    Filter.Tendsto (fun z : ℝ => z * (f z * Work.Spaces.w z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hdom : Filter.Tendsto (fun z : ℝ => 16 * K ^ 2 * z)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun z : ℝ => 16 * K ^ 2 * z) (nhds (0 : ℝ))
        (nhds (16 * K ^ 2 * 0)) := tendsto_const_nhds.mul Filter.tendsto_id
    rw [mul_zero] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' ?_ ?_ hdom
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact mul_nonneg hz.le (sq_nonneg _)
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with z hz
    obtain ⟨hz0, hz1⟩ := hz
    have hf2 : (f z) ^ 2 ≤ (K * z ^ 2) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (h z hz0 hz1) 2
    have hw2 : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
      rw [Work.Spaces.w]
      field_simp
    calc z * (f z * Work.Spaces.w z) ^ 2
        = z * (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := by rw [mul_pow]; ring
      _ ≤ z * (K * z ^ 2) ^ 2 * (Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf2 hz0.le) (sq_nonneg _)
      _ = K ^ 2 * z ^ 5 * ((1 + z) ^ 4 / z ^ 4) := by rw [hw2]; ring
      _ = K ^ 2 * z * (1 + z) ^ 4 := by field_simp
      _ ≤ K ^ 2 * z * 16 := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (sq_nonneg K) hz0.le)
          have h1z : 1 + z ≤ 2 := by linarith
          have h0z : (0 : ℝ) ≤ 1 + z := by linarith
          have hb := pow_le_pow_left₀ h0z h1z 4
          norm_num at hb
          exact hb
      _ = 16 * K ^ 2 * z := by ring

/-- **The trace at `z → ∞` from a `1/z` jet bound.**  If `|f z| ≤ K/z` on `[1,∞)` then
`z·(f z·w z)² → 0` as `z → ∞` (the bound is `≤ 16 K²/z`, using `w z ≤ 4` there). -/
theorem tendsto_z_mul_w_sq_big {f : ℝ → ℝ} {K : ℝ}
    (h : ∀ z : ℝ, 1 ≤ z → |f z| ≤ K / z) :
    Filter.Tendsto (fun z : ℝ => z * (f z * Work.Spaces.w z) ^ 2) Filter.atTop (nhds 0) := by
  have hdom : Filter.Tendsto (fun z : ℝ => 16 * K ^ 2 / z) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun z : ℝ => 16 * K ^ 2 * z⁻¹) Filter.atTop
        (nhds (16 * K ^ 2 * 0)) :=
      (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (16 * K ^ 2)
    rw [mul_zero] at h1
    refine h1.congr' (Filter.Eventually.of_forall fun z => ?_)
    show 16 * K ^ 2 * z⁻¹ = 16 * K ^ 2 / z
    rw [div_eq_mul_inv]
  refine squeeze_zero' ?_ ?_ hdom
  · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with z hz
    exact mul_nonneg hz (sq_nonneg _)
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with z hz
    have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
    have hf2 : (f z) ^ 2 ≤ (K / z) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (h z hz) 2
    have hw2 : (Work.Spaces.w z) ^ 2 ≤ 16 := by
      have hzw : (1 + z) / z ≤ 2 := by
        rw [div_le_iff₀ hz0]
        linarith
      have h0 : (0 : ℝ) ≤ (1 + z) / z := by positivity
      calc (Work.Spaces.w z) ^ 2 = ((1 + z) / z) ^ 4 := by
            rw [Work.Spaces.w]
            field_simp
        _ ≤ 2 ^ 4 := pow_le_pow_left₀ h0 hzw 4
        _ = 16 := by norm_num
    calc z * (f z * Work.Spaces.w z) ^ 2
        = z * (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := by rw [mul_pow]; ring
      _ ≤ z * (K / z) ^ 2 * 16 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hf2 hz0.le) hw2 (sq_nonneg _) ?_
          exact mul_nonneg hz0.le (sq_nonneg _)
      _ = 16 * K ^ 2 / z := by field_simp

/-- **The radial trace hypotheses for the transfer profile `radA α x`.**

`radA α x z = −ampA α z·L₁₂(x)(z) + (ampB α z/c α)·L₁₂(Transport x)(0)` with
`ampA α z = 2z/(c α (1+z)²)`, `ampB α z = 2z²/(1+z)³` (`Transfer/Profiles.lean`); these are
exactly the two hypotheses that `TracesAux.BdryTraces_Gam_mul_rad` consumes in order to
conclude `BdryTraces α 4 (Corr α x)` from `Corr α x = Γ(θ)·radA α x (z)`
(`Transfer.Corr_eq_radA`).

Proof ingredients (all available: `regQo_LGammaT_Aux` + the tree):

* treat the two summands `r₁ = −ampA·L₁₂ x` and `r₂ = (ampB/c α)·L₁₂(Transport x)(0)`
  separately, so no additivity of `DzdIter` is needed: the two conclusions combine by
  `(x+y)² ≤ 2x²+2y²`;
* `DzdIter b (ampA·L₁₂ x) = Σ_{l≤b} C(b,l)·(DzdIter l ampA)·(DzdIter (b−l) L₁₂ x)` on `z > 0`
  (`OpenPkg.ProdOpen.leibniz_open_mixed` applied to the `SmoothOpen` factors `ampA α` and
  `L₁₂ x`; `Aux.L12f_eq_elliptic` identifies `Work.Coercivity.L12f x` with
  `Work.Elliptic.L12`);
* `|DzdIter m (L₁₂ x) z| ≤ D₀ z^{3/2}` on `(0,1)` (`Aux.DzdIter_L12f_small`, from the tower
  `DzdIter (k+1) (L₁₂ x) = −Qang x k` of `OpenPkg.l12_open_bundle` together with `hQ`),
  and `|DzdIter m (L₁₂ x) z| ≤ D₁` for every `z > 0` (`Aux.DzdIter_L12f_bdd`, which is where
  `ClassC` — via `classC_mixed_sup_le_four` — is used);
* `|DzdIter l (ampA α) z| ≤ K_l·z/(1+z)²` (`hA`), hence `≤ K_l·min(z,1/z)`;
* `|DzdIter b (ampB α) z| ≤ D·z²/(1+z)³` (`Aux.DzdIter_ampB_bdd`, from `ClassCRHS.DzBoundR0`),
  and scalar multiples of `ampB` are handled by `Aux.DzdIter_const_mul`;
* finally `z·(m·w)² = m²(1+z)^4/z³` (`w z = (1+z)²/z²`), so it suffices that the jets are
  `O(z²)` near `0` and `O(1/z)` at `∞`; the two polynomial limit lemmas needed here are
  private to the prover (they are not yet in `Aux`). -/
theorem radA_traces {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Work.FTS.Galerkin.Fn}
    (hx : Work.FTS.ClassC.ClassC α x) {C : ℝ} (hC : 0 < C)
    (hQ : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z → z < 1 →
      |Work.Elliptic.Qang x k z| ≤ C * z ^ ((3 : ℝ) / 2))
    (hA : ∀ b : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z|
        ≤ K * (z / (1 + z) ^ 2)) :
    (∀ b : ℕ, b ≤ 4 → Filter.Tendsto
      (fun z : ℝ => z * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.radA α x) z
        * Work.Spaces.w z) ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) ∧
    (∀ b : ℕ, b ≤ 4 → Filter.Tendsto
      (fun z : ℝ => z * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.radA α x) z
        * Work.Spaces.w z) ^ 2) Filter.atTop (nhds 0)) := by
  -- the two jet estimates on `radA α x` (delegated, proved in the sibling modules)
  obtain ⟨K₁, -, h₁⟩ := radA_jet_small hα hx hC hQ hA
  obtain ⟨K₂, -, h₂⟩ := radA_jet_big hα hx hC hQ hA
  -- `O(z²)` at `0⁺` gives the trace at `0⁺`, `O(1/z)` at `∞` the trace at `∞`
  exact ⟨fun b hb => tendsto_z_mul_w_sq_small (h₁ b hb),
    fun b hb => tendsto_z_mul_w_sq_big (h₂ b hb)⟩

end Work.FTS.StrongEps.EpsE4Thr.TracesAux
end
