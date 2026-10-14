import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.qDzLe
import Submission.Work.FTS.StrongPersist.N6.Slots
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.HkSq_terms
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.vSliceSupLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

/-- **The angular-slice bound for the lowest mixed slot `D_θf`.**

For a datum `f` which is `C^∞` on the open quadrant and honestly in `ℋ⁴`, and for every `z > 0`,
the angular slice at `z` of the mixed slot `mixed 0 1 f = D_θ f`, weighted by `sin(2θ)^{-γ}`, is
dominated by twice the `ℋ⁴`-square of `f`:

  `∫_θ sin(2θ)^{-γ} (D_θ f z θ)² dθ ≤ 2 |f|²_{ℋ⁴}`.

The two ingredients are the one-dimensional weighted radial Agmon inequality
(`SixAux.zslice6_hardy`, applied at the fixed angle `θ` to the radial slice `z ↦ sin(2θ)^{-γ/2}
D_θf(z,θ)`) and the Tonelli identity `SdaAux.sda_HkSqSwap_open` for the `ℋ⁴`-integrand of an
open-class datum, which supplies the radial integrability of the slices for almost every angle.
The equality case of the constant `2` is the Agmon constant: the two radial `L²`-integrals
`∫ (D_θf)² Wt²` and `∫ (D_zD_θf)² Wt²` are the two summands `(i,j) = (1,0)` resp. `(1,1)` of
`HkIntegrand α 4 f`, and each is at most `HkSq α 4 f`. -/
theorem vSliceSupLe : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 0 1 f z θ) ^ 2)
        ≤ 2 * Work.Spaces.HkSq α 4 f := by
  intro α f hα hα1 hF hmem z hz
  obtain ⟨hswap, hGint, hGslice⟩ :=
    Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α f hF hmem
  -- the pointwise (in `θ`) slice bound, dominated by the `ℋ⁴`-integrand of `f`
  have hleG : (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 0 1 f z θ) ^ 2)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun θ => 2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s θ) := by
    filter_upwards [hGslice, Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with θ hθint hθ
    obtain ⟨h1, h2⟩ :=
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.vSliceAux.slotRadialIntegrable α f θ hθ hF hθint
    have hA :=
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.vSliceAux.sliceZAgmon α f z θ hz hθ hF h1 h2
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    -- the `(1,1)`-summand of `HkIntegrand` dominates the Agmon right-hand side
    have hmono : (∫ s in Work.Spaces.Iz, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 1 1 f s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
        ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s θ := by
      refine MeasureTheory.setIntegral_mono_of_nonneg (fun s _ => ?_) (fun s _ => ?_) hθint
      · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hsin.le _) (sq_nonneg _))
          (sq_nonneg _)
      · have hkey : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 1 1 f s θ) ^ 2 * (Work.Spaces.w s) ^ 2
            = (Work.Spaces.mixed 1 1 f s θ * Work.Spaces.Wt α s θ) ^ 2 := by
          rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α s θ hsin]
          ring
        rw [hkey]
        exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f s θ 1 1 le_rfl (by norm_num)
    calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 0 1 f z θ) ^ 2
        ≤ 2 * ∫ s in Work.Spaces.Iz, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 1 1 f s θ) ^ 2 * (Work.Spaces.w s) ^ 2 := hA
      _ ≤ 2 * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s θ := by
          linarith
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 0 1 f z θ) ^ 2) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      mul_nonneg (Real.rpow_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])) _) (sq_nonneg _))
  calc (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 0 1 f z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ,
          2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s θ) :=
        MeasureTheory.integral_mono_of_nonneg hnn (hGint.const_mul 2) hleG
    _ = 2 * Work.Spaces.HkSq α 4 f := by
        rw [MeasureTheory.integral_const_mul, hswap]

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.xSliceAgmon5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-! ## The `∂_θ`-form of the second angular integral

The slice Agmon inequality `Work.H2.T1Q.SliceSupOpen` is stated with the plain derivative
`(∂_θ u)² · sin(2θ)^{2-γ}`; the weight used in the level-six pairing is the `D_θ`-normalised
one, `sin(2θ)^{-γ}·(D_z^5D_θA)²`.  Since `D_θ = sin(2θ)·∂_θ` and `D_z^bD_θA = sin(2θ)·∂_θ(D_z^bA)`
on the open quadrant (`Work.FTS.TransportS.SlotT2.supOpen_mixed_eq_sin_pth`), the two integrals
coincide: `sin(2θ)^{-γ}·(sin(2θ)·∂_θu)² = (∂_θu)²·sin(2θ)^{2-γ}`. -/

/-- The second angular integral of the slice Agmon estimate, rewritten from the plain
`∂_θ`-form into the weighted `D_z^5D_θA`-form. -/
theorem xSliceAgmon5_secondInt {α : ℝ} {A : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen A) {z : ℝ} (hz : 0 < z) :
    (∫ θ' in Work.Spaces.Iθ,
        (deriv (fun θ'' => Work.Spaces.DzIter 5 A z θ'') θ') ^ 2
          * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α))
      = ∫ θ' in Work.Spaces.Iθ,
          (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 5 1 A z θ') ^ 2 := by
  rw [MeasureTheory.setIntegral_congr_set Work.FTS.TransportS.SlotT2.supOpen_Iθ_ae_eq]
  rw [MeasureTheory.setIntegral_congr_set Work.FTS.TransportS.SlotT2.supOpen_Iθ_ae_eq]
  refine MeasureTheory.setIntegral_congr_fun
    (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (fun θ' hθ' => ?_)
  have hsin : 0 < Real.sin (2 * θ') :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ'.1]) (by linarith [hθ'.2, Real.pi_pos])
  have hmix : Work.Spaces.mixed 5 1 A z θ'
      = Real.sin (2 * θ') * deriv (fun θ'' => Work.Spaces.DzIter 5 A z θ'') θ' :=
    Work.FTS.TransportS.SlotT2.supOpen_mixed_eq_sin_pth hF 5 hz hθ'
  have hkey : (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α))
        * (Real.sin (2 * θ')) ^ 2
      = (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α) := by
    have h2 : (Real.sin (2 * θ')) ^ 2 = (Real.sin (2 * θ')) ^ (2 : ℝ) :=
      (Real.rpow_natCast _ 2).symm
    rw [h2, ← Real.rpow_add hsin]
    ring_nf
  rw [hmix, mul_pow, ← hkey]
  ring

/-- **The slice Agmon inequality at order five.**

For `A` smooth on the open quadrant with honest `ℋ⁶`-membership and every `z > 0`,
`θ ∈ (0,π/2)`:
`(D_z^5A(z,θ))² ≤ (4/π)·∫_{Iθ}(D_z^5A(z,·))² + (200/(γ-1))·∫_{Iθ} sin(2·)^{-γ}·(D_z^5D_θA(z,·))²`.

This is the `b = 5` instantiation of the open-interval slice estimate
`Work.H2.T1Q.SliceSupOpen` at the slice `θ' ↦ D_z^5A(z,θ')`: the differentiability is
`SmoothOpen.DzIter` restricted to the open interval, the two integrability hypotheses are
`SixAux.integrableOn_sq6` (the mean term) and `SixAux.integrableOn_pth_weight6` (the
Dirichlet term, at `b = 5 ≤ 5`), and the second integral is recast in the `D_θ`-normalised
weight by `xSliceAgmon5_secondInt`. -/
theorem xSliceAgmon5 : ∀ (α : ℝ) (A : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 6 A →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter 5 A z θ) ^ 2
        ≤ (4 / Real.pi) * (∫ θ' in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ') ^ 2)
          + (200 / (Work.Spaces.gam α - 1))
            * (∫ θ' in Work.Spaces.Iθ,
                (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed 5 1 A z θ') ^ 2) := by
  intro α A hα hα1 hF hmem z θ hz hθ0 hθπ
  have hslice : ContDiffOn ℝ 1 (fun θ' => Work.Spaces.DzIter 5 A z θ')
      (Set.Ioo 0 (Real.pi / 2)) :=
    ((hF.DzIter 5).curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
  have hint2 := Work.FTS.StrongPersist.N6Trans.SixAux.integrableOn_sq6 (α := α) (f := A)
    hα hF hmem (b := 5) (by norm_num) (z := z) hz
  have hintp := Work.FTS.StrongPersist.N6Trans.SixAux.integrableOn_pth_weight6 (α := α) (f := A)
    hα hα1 hF hmem (b := 5) (by norm_num) (z := z) hz
  have hmain := Work.H2.T1Q.SliceSupOpen α (fun θ' => Work.Spaces.DzIter 5 A z θ')
    hα hα1 hslice hint2 hintp θ ⟨hθ0, hθπ⟩
  rw [xSliceAgmon5_secondInt hF hz] at hmain
  exact hmain

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.zProdIntLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

/-- `sin (2θ) ≥ 0` for `θ ∈ Iθ = [0,π/2]`. -/
private lemma sin_two_nonneg_Iθ' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- The square of the mixed weight `Wt α z θ = w z · sin(2θ)^{-γ/2}` is
`w z² · sin(2θ)^{-γ}`, for nonnegative `sin(2θ)`. -/
private lemma Wt_sq_eq' (α z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ ((2 : ℝ)) from
      (Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2).symm]
  rw [← Real.rpow_mul hs]
  rw [show (-(Work.Spaces.gam α / 2)) * (2 : ℝ) = -(Work.Spaces.gam α) by ring]

/-- The squared weighted mixed slot, in the unfolded `w² s^{-γ} (D_z⁵D_θf)²` form of the
statement (valid where `sin(2θ) ≥ 0`). -/
private lemma slot_sq_eq' (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hs : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 5 1 f z θ) ^ 2) := by
  rw [mul_pow, Wt_sq_eq' α z θ hs]
  ring

theorem zProdIntLe : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 5 1 f z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
    (∫ z, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 5 1 f z θ) ^ 2)
      ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      ≤ Work.Spaces.HkSq α 6 f := by
  intro α f hα hα1 hsm hmem
  -- The weighted slot `j = 5` of `HkIntegrand α 6 f`: integrability and value bound.
  obtain ⟨hint, hle⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.mixedSlotL2 α ⟨hα, hα1⟩ f 5 hsm hmem le_rfl
  -- The pointwise unfolding `(D_z⁵D_θf · Wt)² = w² · (s^{-γ} · (D_z⁵D_θf)²)` of the slot.
  have hident : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        = (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 5 1 f z θ) ^ 2) := by
    intro z
    rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      (fun θ hθ => slot_sq_eq' α f z θ (sin_two_nonneg_Iθ' hθ)))]
    rw [MeasureTheory.integral_const_mul]
  refine ⟨hint.congr (Filter.Eventually.of_forall hident), ?_⟩
  calc (∫ z, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 5 1 f z θ) ^ 2)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      = ∫ z, (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) :=
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun z => (hident z).symm)
    _ = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := rfl
    _ ≤ Work.Spaces.HkSq α 6 f := hle

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.sigmaDivisibility =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# σ-divisibility: the identity `leafGam α · D_θ = w²·sin(2θ)^{1-γ}·∂_θ`

`D_θ = sin(2θ)·∂_θ` and `leafGam α = w²·sin(2θ)^{-γ}` with `γ = 1 + α/10`, so the `sin(2θ)`
carried by the operator **cancels one power** of the `γ`-weight: for `σ = sin 2θ > 0`

  `leafGam α · D_θ A · Y · D_θ Y = w² · σ^{2-γ} · ∂_θA · Y · ∂_θY`,

and on `[0,π/2]` the new weight `σ^{2-γ} = σ^{1-α/10}` is **bounded** by `1`, whereas
`σ^{-γ}` is not even integrable near `θ = 0, π/2`.

This module records the identity and the three `L²`-bounds it buys at the *bounded* weight
`σ^{2-γ}`, for the three factors of the `b = 5` pairing
`leafGam α · D_θA · D_z^5 f · D_θ(D_z^5 f)`:

* `canon_A_slot` — the A-factor `∂_θA` (equivalently the `(0,1)`-slot of `A`, level 4);
* `canon_Z_slot` — the `θ`-derivative `∂_θ(D_z^b f)` (equivalently the `(b,1)`-slot, `b ≤ 5`);
* `canon_mid_slot` — the pure-`z` factor `D_z^b f` (`b ≤ 5`) with the **critical** weight
  `σ^{-(1-α/10)}` dominating `σ^{2-γ}` (`qDzLe` / `thetaHardyApp`).

Together with `pairing_Dth_eq_canon` this reduces the `b = 5` case to the trilinear form
`∫∫ w²σ^{2-γ} ∂_θA · D_z^5f · ∂_θ(D_z^5f)` with all three factors `L²` at the same *bounded*
weight — the form on which the alignment-penalty argument of the next layer has to work.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 1600000


/-! ## § 1. The pointwise σ-divisibility identities -/

/-- **The σ-divisibility identity (two factors).**  For `σ = sin 2θ > 0`,
`leafGam α · D_θ A = w²·σ^{1-γ}·∂_θA`. -/
theorem leafGam_mul_Dth_eq {α z θ : ℝ} (hσ : 0 < Real.sin (2 * θ)) (A : ℝ → ℝ → ℝ) :
    Work.FTS.TransportS.leafGam α z θ * Work.Spaces.Dth A z θ
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
        * Work.Spaces.pth A z θ := by
  set s := Real.sin (2 * θ) with hs
  have h1 : s ^ (-(Work.Spaces.gam α)) * s = s ^ (1 - Work.Spaces.gam α) := by
    have h := Real.rpow_add hσ (-(Work.Spaces.gam α)) (1 : ℝ)
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  have hfun : Work.Spaces.Dth A z θ = s * Work.Spaces.pth A z θ := rfl
  have hlf : Work.FTS.TransportS.leafGam α z θ
      = (Work.Spaces.w z) ^ 2 * s ^ (-(Work.Spaces.gam α)) := rfl
  rw [hfun, hlf, hs]
  calc (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
        * (Real.sin (2 * θ) * Work.Spaces.pth A z θ)
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
          * Real.sin (2 * θ)) * Work.Spaces.pth A z θ := by ring
    _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
          * Work.Spaces.pth A z θ := by rw [h1]




/-! ## § 2. The bounded weight `σ^{2-γ}` -/

theorem canonW_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
  Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _



/-! ## § 3. The three `L²`-bounds at the bounded weight -/




end

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
end
