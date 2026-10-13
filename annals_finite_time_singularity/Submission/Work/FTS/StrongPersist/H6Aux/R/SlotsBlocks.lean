/-
# The four level-one slot estimates for the base case `base_R`

This file assembles the lower bound

  `-r · H1IP α h h ≤ H1IP α (Lhat h) h`

out of the four `wip`-pairings that make up `H1IP`, for `h` smooth on the open quadrant
with honest `ℋ²`-integral.

The route is *not* the full expansion of `Lhat h` against all four slots.  Instead:

* the two *zeroth order* slots (`wip ρ_η (Lhat h) h` and `wip (w²) (Lhat h) h`) are bounded
  below by the pointwise AM–GM
  `Lhat h·h·ρ ≥ -(1/2)(D_z h)²ρ - (9/2)(D_θh)²ρ - 2h²ρ`,
  which involves only *first* derivatives of `h` — no integration by parts at all;
* the two *first order* slots (`wip ρ_η (D_z (Lhat h)) (D_z h)` and
  `wip ρ_γ (D_θ (Lhat h)) (D_θ h)`) are first rewritten with the commutator identities of
  `Lhat` (`D_θ Lhat = Lhat D_θ`, `D_z Lhat = Lhat D_z + Ê₂`), then expanded, and the
  *adjacent* pairings `∫ (D_z g)·g·ρ` and `∫ (D_θ g)·g·ρ` (with `g = D_z h` resp. `g = D_θ h`)
  are converted into the `g²`-slot by the two integration by parts `wip_Dz_ibp` and
  `wip_Dth_ibp`.  This is where the second derivatives of `h` are consumed (in the
  integrability hypotheses only), and where `HkMem α 2 h` is used.

Every integral produced on the way is dominated by `HkSq α 1 h ≤ H1IP α h h`, so the
constant `r` is universal.

## Integrability strategy

`HkMem α 2 h` makes `HkIntegrand α 2 h` jointly integrable.  Everything else is obtained
from `integrableOfHkDom`: an integrand that is continuous on the open quadrant and a.e.
dominated by `C·HkIntegrand α 2 h` is integrable.  The a.e. domination is provided by the
block bounds `sq_le_Hk_dz` / `sq_le_Hk_mixed` (the `D_z`- and mixed summands of the
`ℋ²`-integrand) together with `2|uv| ≤ u² + v²`.

Conventions: `ρ_β = Rho β = w²·sin(2θ)^{-β}` (so `ρ_0 = w²`), `η = 99/100`,
`γ = gam α = 1 + α/10`, `Iθ = [0,π/2]`, `Iz = [0,∞)`, `dz dθ` measure.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.Coer1.Defs
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts
import Submission.Work.FTS.CoercivityFix.DzSelf.H1IP_Dz_self
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.StrongPersist.H6Aux.wip_Dz_ibp
import Submission.Work.FTS.StrongPersist.H6Aux.LhatCommOpen
import Submission.Work.FTS.StrongPersist.H6Aux.R.DthIbp
import Submission.Work.FTS.StrongPersist.H6Aux.R.SlotsBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux.R

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 3200000
/-! ## Weight facts and block bounds (continued) -/
theorem sq_dz_le_Hk (α : ℝ) {h : Fn} {k : ℕ} (i : ℕ) (hi : i ≤ k) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.DzIter i h p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ Work.Spaces.HkIntegrand α k h p.1 p.2 := by
  filter_upwards [ae_angle_Ioo] with p hp
  obtain ⟨z, θ⟩ := p
  obtain ⟨h1, h2⟩ := hp
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hkey : (Work.Spaces.DzIter i h z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter i h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ := by
    rw [mul_pow, div_half_sq _ _ _ hs]
    simp only [Rhoq, Work.FTS.CoercivityFix.Coer1.Rho,
      Work.FTS.CoercivityFix.Coer1.sig]
  rw [← hkey]
  exact Work.Spaces.sq_le_HkIntegrand_z α k h z θ i hi

/-- The `ℋ²`-summand attached to a mixed block, with the `γ`-weight. -/
theorem sq_mixed_le_Hk_gam (α : ℝ) (hα : 0 < α) {h : Fn} {k j i : ℕ} (hi : 1 ≤ i)
    (hij : i + j ≤ k) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.mixed j i h p.1 p.2) ^ 2 * Rhoq (Work.Spaces.gam α) p.1 p.2
        ≤ Work.Spaces.HkIntegrand α k h p.1 p.2 := by
  filter_upwards [ae_angle_Ioo] with p hp
  obtain ⟨z, θ⟩ := p
  obtain ⟨h1, h2⟩ := hp
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hkey : (Work.Spaces.mixed j i h z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.mixed j i h z θ) ^ 2 * Rhoq (Work.Spaces.gam α) z θ := by
    have hW : Work.Spaces.Wt α z θ
        = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := rfl
    rw [hW, mul_pow, mul_half_sq _ _ _ hs]
    simp only [Rhoq, Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig]
  rw [← hkey]
  exact Work.Spaces.sq_le_HkIntegrand_mixed α k h z θ i j hi hij

/-- The mixed block with the `η`-weight is dominated through the `γ`-weight. -/
theorem sq_mixed_le_Hk_eta (α : ℝ) (hα : 0 < α) {h : Fn} {k j i : ℕ} (hi : 1 ≤ i)
    (hij : i + j ≤ k) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.mixed j i h p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ Work.Spaces.HkIntegrand α k h p.1 p.2 := by
  filter_upwards [sq_mixed_le_Hk_gam (k := k) α hα hi hij, Rhoq_eta_le_gam α hα] with p hp hle
  refine le_trans ?_ hp
  exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)

/-- A pure `D_z`-block with the plain radial weight. -/
theorem sq_dz_le_Hk_w (α : ℝ) {h : Fn} {k : ℕ} (i : ℕ) (hi : i ≤ k) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.DzIter i h p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
        ≤ Work.Spaces.HkIntegrand α k h p.1 p.2 := by
  filter_upwards [sq_dz_le_Hk (k := k) α i hi, w2_le_Rhoq_eta] with p hp hle
  refine le_trans ?_ hp
  exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)

/-- A mixed block with the plain radial weight. -/
theorem sq_mixed_le_Hk_w (α : ℝ) (hα : 0 < α) {h : Fn} {k j i : ℕ} (hi : 1 ≤ i)
    (hij : i + j ≤ k) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.mixed j i h p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
        ≤ Work.Spaces.HkIntegrand α k h p.1 p.2 := by
  filter_upwards [sq_mixed_le_Hk_eta (k := k) α hα hi hij, w2_le_Rhoq_eta] with p hp hle
  refine le_trans ?_ hp
  exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)

/-- The commutator defect `Ê₂h` against the `η`-weight. -/
theorem sq_E2_le_Hk (α : ℝ) (hα : 0 < α) {h : Fn} {k : ℕ} (hk : 1 ≤ k) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.FTS.CoercivityFix.E2hat h p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ 2 * Work.Spaces.HkIntegrand α k h p.1 p.2 := by
  filter_upwards [sq_dz_le_Hk (h := h) (k := k) α 0 (by omega),
    sq_mixed_le_Hk_eta (h := h) (k := k) (j := 0) (i := 1) α hα (by norm_num) (by omega),
    ae_radius_pos, ae_snd_mem_Iθ] with p h0 h1 hzp hθ
  obtain ⟨z, θ⟩ := p
  have hz : 0 ≤ z := le_of_lt hzp
  have he : |Work.FTS.CoercivityFix.E2hat h z θ|
      ≤ (2 * |h z θ| + 3 * |Work.Spaces.Dth h z θ|) / 4 :=
    Work.FTS.CoercivityFix.E2hat_abs_le h hz
  have hX : 0 ≤ (2 * |h z θ| + 3 * |Work.Spaces.Dth h z θ|) / 4 := by positivity
  have hsq : (Work.FTS.CoercivityFix.E2hat h z θ) ^ 2
      ≤ ((2 * |h z θ| + 3 * |Work.Spaces.Dth h z θ|) / 4) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hX]
    exact he
  have hcs : ((2 * |h z θ| + 3 * |Work.Spaces.Dth h z θ|) / 4) ^ 2
      ≤ (13 / 16) * ((h z θ) ^ 2 + (Work.Spaces.Dth h z θ) ^ 2) := by
    have h1'' : (2 * |h z θ| + 3 * |Work.Spaces.Dth h z θ|) ^ 2
        ≤ 13 * (|h z θ| ^ 2 + |Work.Spaces.Dth h z θ| ^ 2) := by
      nlinarith [sq_nonneg (3 * |h z θ| - 2 * |Work.Spaces.Dth h z θ|)]
    have h1' : (2 * |h z θ| + 3 * |Work.Spaces.Dth h z θ|) ^ 2
        ≤ 13 * ((h z θ) ^ 2 + (Work.Spaces.Dth h z θ) ^ 2) := by
      simpa only [sq_abs] using h1''
    have h5 : ((2 * |h z θ| + 3 * |Work.Spaces.Dth h z θ|) / 4) ^ 2
        = (2 * |h z θ| + 3 * |Work.Spaces.Dth h z θ|) ^ 2 / 16 := by ring
    rw [h5]
    linarith [h1']
  have hrho : 0 ≤ Rhoq Work.Spaces.eta z θ :=
    Work.FTS.CoercivityFix.Coer1.Rho_nonneg Work.Spaces.eta z θ hθ
  have hDth : (Work.Spaces.Dth h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ
      ≤ Work.Spaces.HkIntegrand α k h z θ := h1
  have hh : (h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ
      ≤ Work.Spaces.HkIntegrand α k h z θ := h0
  have hnn : 0 ≤ Work.Spaces.HkIntegrand α k h z θ :=
    Work.Spaces.HkIntegrand_nonneg α k h z θ
  calc (Work.FTS.CoercivityFix.E2hat h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ
      ≤ (13 / 16) * ((h z θ) ^ 2 + (Work.Spaces.Dth h z θ) ^ 2)
          * Rhoq Work.Spaces.eta z θ :=
        mul_le_mul_of_nonneg_right (le_trans hsq hcs) hrho
    _ = (13 / 16) * ((h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ)
          + (13 / 16) * ((Work.Spaces.Dth h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ) := by
        ring
    _ ≤ (13 / 16) * Work.Spaces.HkIntegrand α k h z θ
          + (13 / 16) * Work.Spaces.HkIntegrand α k h z θ := by
        linarith [hh, hDth]
    _ ≤ 2 * Work.Spaces.HkIntegrand α k h z θ := by linarith [hnn]

/-! ## Continuity of the blocks on the open quadrant -/

theorem continuousOn_w2_Q0 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2) Q0 := by
  have hfun : (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      = fun p : ℝ × ℝ => ((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2 := by
    funext p; rfl
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2)
    (fun p hp => pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))).pow 2

theorem continuousOn_sinpow_Q0 (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q)) Q0 := by
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    rw [Work.FTS.EllipticEst.mem_Q0] at hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos])
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

theorem continuousOn_Rhoq_Q0 (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Rhoq q p.1 p.2) Q0 := by
  have hfun : (fun p : ℝ × ℝ => Rhoq q p.1 p.2)
      = fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q) := by
    funext p
    simp only [Rhoq, Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig]
  rw [hfun]
  exact continuousOn_w2_Q0.mul (continuousOn_sinpow_Q0 q)

theorem continuousOn_zdiv_sq_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => p.1 / (1 + p.1) ^ 2) Q0 :=
  continuousOn_fst.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (fun p hp => pow_ne_zero 2 (by linarith [(Work.FTS.EllipticEst.mem_Q0.mp hp).1]))

theorem continuousOn_E2hat_Q0 {h : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen h) :
    ContinuousOn (Function.uncurry (Work.FTS.CoercivityFix.E2hat h)) Q0 := by
  have hfun : Function.uncurry (Work.FTS.CoercivityFix.E2hat h)
      = fun p : ℝ × ℝ => (p.1 / (1 + p.1) ^ 2)
          * (2 * h p.1 p.2 + 3 * Work.Spaces.Dth h p.1 p.2) := by
    funext p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair]
    rw [Work.FTS.CoercivityFix.E2hat_eq]
    ring
  rw [hfun]
  exact continuousOn_zdiv_sq_Q0.mul
    ((hs.continuousOn.const_mul 2).add (hs.Dth.continuousOn.const_mul 3))

theorem continuousOn_Lhat_Q0 {h : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen h) :
    ContinuousOn (Function.uncurry (Work.FTS.CoercivityFix.Lhat h)) Q0 := by
  have hfun : Function.uncurry (Work.FTS.CoercivityFix.Lhat h)
      = fun p : ℝ × ℝ => h p.1 p.2 + Work.Spaces.Dz h p.1 p.2
          - 2 * h p.1 p.2 / (1 + p.1) - 3 * Work.Spaces.Dth h p.1 p.2 / (1 + p.1) := by
    funext p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair]
    rw [Work.FTS.CoercivityFix.Lhat_eq]
    try ring
  rw [hfun]
  have h1 : ContinuousOn (fun p : ℝ × ℝ => 2 * h p.1 p.2 / (1 + p.1)) Q0 :=
    ((hs.continuousOn.const_mul 2).div (continuousOn_const.add continuousOn_fst)
      (fun p hp => by linarith [(Work.FTS.EllipticEst.mem_Q0.mp hp).1]))
  have h2 : ContinuousOn (fun p : ℝ × ℝ => 3 * Work.Spaces.Dth h p.1 p.2 / (1 + p.1)) Q0 :=
    ((hs.Dth.continuousOn.const_mul 3).div (continuousOn_const.add continuousOn_fst)
      (fun p hp => by linarith [(Work.FTS.EllipticEst.mem_Q0.mp hp).1]))
  exact ((hs.continuousOn.add hs.Dz.continuousOn).sub h1).sub h2

/-! ## Integrability of weighted squares and of products -/

/-- A weighted square a.e. dominated by a multiple of `HkIntegrand α 2 h` is integrable. -/
theorem integrable_sq_of_bound (α : ℝ) (k : ℕ) {h X ρ : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen h) (hm : Work.Spaces.HkMem α k h) {C : ℝ}
    (hC : 0 ≤ C)
    (hXc : ContinuousOn (Function.uncurry X) Q0)
    (hρc : ContinuousOn (Function.uncurry ρ) Q0)
    (hρnn : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), 0 ≤ ρ p.1 p.2)
    (hb : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
        (X p.1 p.2) ^ 2 * ρ p.1 p.2 ≤ C * Work.Spaces.HkIntegrand α k h p.1 p.2) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => (X z θ) ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine integrableOfHkDom (C := C) α k hs hm ?_ ?_
  · convert (hXc.mul hXc).mul hρc using 1
    funext p
    simp only [Function.uncurry, Pi.mul_apply]
    try ring
  · filter_upwards [hb, hρnn] with p hp hnn
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hnn)]
    exact hp

/-- The product of two blocks whose weighted squares are a.e. dominated by `HkIntegrand` is
integrable. -/
theorem integrable_mul_of_sq (α : ℝ) (k : ℕ) {h u v ρ : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen h) (hm : Work.Spaces.HkMem α k h) {Cu Cv : ℝ}
    (hCu : 0 ≤ Cu) (hCv : 0 ≤ Cv)
    (huc : ContinuousOn (Function.uncurry u) Q0)
    (hvc : ContinuousOn (Function.uncurry v) Q0)
    (hρc : ContinuousOn (Function.uncurry ρ) Q0)
    (hρnn : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), 0 ≤ ρ p.1 p.2)
    (hu : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
        (u p.1 p.2) ^ 2 * ρ p.1 p.2 ≤ Cu * Work.Spaces.HkIntegrand α k h p.1 p.2)
    (hv : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
        (v p.1 p.2) ^ 2 * ρ p.1 p.2 ≤ Cv * Work.Spaces.HkIntegrand α k h p.1 p.2) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => u z θ * v z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine integrableOfHkDom (C := Cu + Cv) α k hs hm ?_ ?_
  · exact (huc.mul hvc).mul hρc
  · filter_upwards [hu, hv, hρnn] with p hup hvp hnn
    have h2 : 2 * (|u p.1 p.2 * v p.1 p.2| * ρ p.1 p.2)
        ≤ (u p.1 p.2) ^ 2 * ρ p.1 p.2 + (v p.1 p.2) ^ 2 * ρ p.1 p.2 := by
      have := Work.FTS.CoercivityFix.Coer1.two_abs_mul_le (u p.1 p.2) (v p.1 p.2) (ρ p.1 p.2) hnn
      linarith [this]
    have h3 : |u p.1 p.2 * v p.1 p.2 * ρ p.1 p.2| ≤ (Cu + Cv) * Work.Spaces.HkIntegrand α k h p.1 p.2 := by
      rw [abs_mul, abs_of_nonneg hnn]
      nlinarith [h2, hup, hvp]
    simpa using h3

/-- `Rhoq 0 = w²`: the `q = 0` weight is the plain radial square. -/
theorem Rhoq_zero : Rhoq 0 = fun z _ => (Work.Spaces.w z) ^ 2 := by
  funext z θ
  simp only [Rhoq, Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig,
    neg_zero, Real.rpow_zero, mul_one]

/-- A.e. `D_θ D_z h = mixed 1 1 h` on the open quadrant. -/
theorem ae_DthDz {h : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen h) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      Work.Spaces.Dth (Work.Spaces.Dz h) p.1 p.2
        = Work.Spaces.mixed 1 1 h p.1 p.2 := by
  filter_upwards [ae_angle_Ioo, ae_radius_pos] with p hθ hz
  obtain ⟨z, θ⟩ := p
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hz, hθ.1, hθ.2⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry h) (z, θ) :=
    (hs.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).of_le
      (by simp [Work.Stability.smoothOrder])
  exact (Work.Spaces.Dz_Dth_comm hcd).symm

/-- The mixed block `D_θ D_z h` against the `η`-weight. -/
theorem sq_DthDz_le_Hk (α : ℝ) (hα : 0 < α) {h : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen h)
    {k : ℕ} (hk : 2 ≤ k) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.Dth (Work.Spaces.Dz h) p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ Work.Spaces.HkIntegrand α k h p.1 p.2 := by
  filter_upwards [sq_mixed_le_Hk_eta (h := h) (k := k) (j := 1) (i := 1) α hα
    (by norm_num) (by omega), ae_DthDz hs] with p hp hc
  rw [hc]; exact hp

/-! ## The `Lhat`-blocks -/

/-- Four-term AM–GM: `(a+b+c+d)² ≤ 4(a²+b²+c²+d²)`. -/
theorem four_sq_le (a b c d : ℝ) : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

/-- `(c·a)² ≤ C²·a²` when `0 ≤ C` and `|c| ≤ C`. -/
theorem sq_mul_le_abs {c a C : ℝ} (hC : 0 ≤ C) (h : |c| ≤ C) :
    (c * a) ^ 2 ≤ C ^ 2 * a ^ 2 := by
  have h1 : c ^ 2 ≤ C ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hC]
    exact h
  nlinarith [h1, sq_nonneg a]

theorem abs_two_div_le {z : ℝ} (hz : 0 ≤ z) : |2 / (1 + z)| ≤ 2 := by
  rw [abs_of_nonneg (by positivity), div_le_iff₀ (by linarith : (0:ℝ) < 1 + z)]
  linarith

theorem abs_three_div_le {z : ℝ} (hz : 0 ≤ z) : |3 / (1 + z)| ≤ 3 := by
  rw [abs_of_nonneg (by positivity), div_le_iff₀ (by linarith : (0:ℝ) < 1 + z)]
  linarith

/-- `(Lhat h)²` against the `η`-weight. -/
theorem sq_Lhat_le_Hk (α : ℝ) (hα : 0 < α) {h : Fn} {k : ℕ} (hk : 1 ≤ k) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.FTS.CoercivityFix.Lhat h p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ 60 * Work.Spaces.HkIntegrand α k h p.1 p.2 := by
  filter_upwards [sq_dz_le_Hk (h := h) (k := k) α 0 (by omega),
    sq_dz_le_Hk (h := h) (k := k) α 1 (by omega),
    sq_mixed_le_Hk_eta (h := h) (k := k) (j := 0) (i := 1) α hα (by norm_num) (by omega),
    ae_radius_pos, ae_snd_mem_Iθ] with p h0 h1 h2 hzp hθ
  obtain ⟨z, θ⟩ := p
  dsimp only at h0 h1 h2 hzp hθ ⊢
  have hz : 0 ≤ z := le_of_lt hzp
  have hc1 : |-(2 / (1 + z))| ≤ 2 := by
    rw [abs_neg]; exact abs_two_div_le hz
  have hc2 : |-(3 / (1 + z))| ≤ 3 := by
    rw [abs_neg]; exact abs_three_div_le hz
  have hpt : (Work.FTS.CoercivityFix.Lhat h z θ) ^ 2
      ≤ 4 * (5 * (h z θ) ^ 2 + (Work.Spaces.Dz h z θ) ^ 2
          + 9 * (Work.Spaces.Dth h z θ) ^ 2) := by
    have hL := Work.FTS.CoercivityFix.Lhat_eq h z θ
    have h4 := four_sq_le (h z θ) (Work.Spaces.Dz h z θ)
      (-(2 / (1 + z)) * h z θ) (-(3 / (1 + z)) * Work.Spaces.Dth h z θ)
    have h5 := sq_mul_le_abs (C := 2) (by norm_num) hc1 (a := h z θ)
    have h6 := sq_mul_le_abs (C := 3) (by norm_num) hc2 (a := Work.Spaces.Dth h z θ)
    rw [hL]
    have hL2 : h z θ + Work.Spaces.Dz h z θ - 2 * h z θ / (1 + z)
          - 3 * Work.Spaces.Dth h z θ / (1 + z)
        = h z θ + Work.Spaces.Dz h z θ + -(2 / (1 + z)) * h z θ
          + -(3 / (1 + z)) * Work.Spaces.Dth h z θ := by ring
    rw [hL2]
    nlinarith [h4, h5, h6]
  have hrho : 0 ≤ Rhoq Work.Spaces.eta z θ :=
    Work.FTS.CoercivityFix.Coer1.Rho_nonneg Work.Spaces.eta z θ hθ
  have hnn : 0 ≤ Work.Spaces.HkIntegrand α k h z θ :=
    Work.Spaces.HkIntegrand_nonneg α k h z θ
  have h0' : (h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ
      ≤ Work.Spaces.HkIntegrand α k h z θ := h0
  have h1' : (Work.Spaces.Dz h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ
      ≤ Work.Spaces.HkIntegrand α k h z θ := h1
  have h2' : (Work.Spaces.Dth h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ
      ≤ Work.Spaces.HkIntegrand α k h z θ := h2
  calc (Work.FTS.CoercivityFix.Lhat h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ
      ≤ (4 * (5 * (h z θ) ^ 2 + (Work.Spaces.Dz h z θ) ^ 2
          + 9 * (Work.Spaces.Dth h z θ) ^ 2)) * Rhoq Work.Spaces.eta z θ :=
        mul_le_mul_of_nonneg_right hpt hrho
    _ = 20 * ((h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ)
          + 4 * ((Work.Spaces.Dz h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ)
          + 36 * ((Work.Spaces.Dth h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ) := by ring
    _ ≤ 60 * Work.Spaces.HkIntegrand α k h z θ := by linarith [h0', h1', h2', hnn]

/-- `(Lhat (D_z h))²` against the `η`-weight. -/
theorem sq_LhatDz_le_Hk (α : ℝ) (hα : 0 < α) {h : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen h) {k : ℕ} (hk : 2 ≤ k) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h) p.1 p.2) ^ 2
          * Rhoq Work.Spaces.eta p.1 p.2
        ≤ 60 * Work.Spaces.HkIntegrand α k h p.1 p.2 := by
  filter_upwards [sq_dz_le_Hk (h := h) (k := k) α 1 (by omega),
    sq_dz_le_Hk (h := h) (k := k) α 2 (by omega),
    sq_DthDz_le_Hk (h := h) (k := k) α hα hs hk,
    ae_radius_pos, ae_snd_mem_Iθ] with p h0 h1 h2 hzp hθ
  obtain ⟨z, θ⟩ := p
  dsimp only at h0 h1 h2 hzp hθ ⊢
  have hz : 0 ≤ z := le_of_lt hzp
  have hc1 : |-(2 / (1 + z))| ≤ 2 := by
    rw [abs_neg]; exact abs_two_div_le hz
  have hc2 : |-(3 / (1 + z))| ≤ 3 := by
    rw [abs_neg]; exact abs_three_div_le hz
  have hpt : (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h) z θ) ^ 2
      ≤ 4 * (5 * (Work.Spaces.Dz h z θ) ^ 2 + (Work.Spaces.DzIter 2 h z θ) ^ 2
          + 9 * (Work.Spaces.Dth (Work.Spaces.Dz h) z θ) ^ 2) := by
    have hL := Work.FTS.CoercivityFix.Lhat_eq (Work.Spaces.Dz h) z θ
    have h4 := four_sq_le (Work.Spaces.Dz h z θ) (Work.Spaces.DzIter 2 h z θ)
      (-(2 / (1 + z)) * Work.Spaces.Dz h z θ)
      (-(3 / (1 + z)) * Work.Spaces.Dth (Work.Spaces.Dz h) z θ)
    have h5 := sq_mul_le_abs (C := 2) (by norm_num) hc1 (a := Work.Spaces.Dz h z θ)
    have h6 := sq_mul_le_abs (C := 3) (by norm_num) hc2
      (a := Work.Spaces.Dth (Work.Spaces.Dz h) z θ)
    rw [hL]
    have hL2 : Work.Spaces.Dz h z θ + Work.Spaces.Dz (Work.Spaces.Dz h) z θ
          - 2 * Work.Spaces.Dz h z θ / (1 + z)
          - 3 * Work.Spaces.Dth (Work.Spaces.Dz h) z θ / (1 + z)
        = Work.Spaces.Dz h z θ + Work.Spaces.DzIter 2 h z θ
          + -(2 / (1 + z)) * Work.Spaces.Dz h z θ
          + -(3 / (1 + z)) * Work.Spaces.Dth (Work.Spaces.Dz h) z θ := by
      rw [show Work.Spaces.Dz (Work.Spaces.Dz h) = Work.Spaces.DzIter 2 h from rfl]
      ring
    rw [hL2]
    nlinarith [h4, h5, h6]
  have hrho : 0 ≤ Rhoq Work.Spaces.eta z θ :=
    Work.FTS.CoercivityFix.Coer1.Rho_nonneg Work.Spaces.eta z θ hθ
  have hnn : 0 ≤ Work.Spaces.HkIntegrand α k h z θ :=
    Work.Spaces.HkIntegrand_nonneg α k h z θ
  have h0' : (Work.Spaces.Dz h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ
      ≤ Work.Spaces.HkIntegrand α k h z θ := h0
  have h1' : (Work.Spaces.DzIter 2 h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ
      ≤ Work.Spaces.HkIntegrand α k h z θ := h1
  have h2' : (Work.Spaces.Dth (Work.Spaces.Dz h) z θ) ^ 2 * Rhoq Work.Spaces.eta z θ
      ≤ Work.Spaces.HkIntegrand α k h z θ := h2
  calc (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h) z θ) ^ 2
        * Rhoq Work.Spaces.eta z θ
      ≤ (4 * (5 * (Work.Spaces.Dz h z θ) ^ 2 + (Work.Spaces.DzIter 2 h z θ) ^ 2
          + 9 * (Work.Spaces.Dth (Work.Spaces.Dz h) z θ) ^ 2))
          * Rhoq Work.Spaces.eta z θ :=
        mul_le_mul_of_nonneg_right hpt hrho
    _ = 20 * ((Work.Spaces.Dz h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ)
          + 4 * ((Work.Spaces.DzIter 2 h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ)
          + 36 * ((Work.Spaces.Dth (Work.Spaces.Dz h) z θ) ^ 2
              * Rhoq Work.Spaces.eta z θ) := by ring
    _ ≤ 60 * Work.Spaces.HkIntegrand α k h z θ := by linarith [h0', h1', h2', hnn]

/-- `(Lhat (D_θ h))²` against the `γ`-weight. -/
theorem sq_LhatDth_le_Hk (α : ℝ) (hα : 0 < α) {h : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen h) {k : ℕ} (hk : 2 ≤ k) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth h) p.1 p.2) ^ 2
          * Rhoq (Work.Spaces.gam α) p.1 p.2
        ≤ 60 * Work.Spaces.HkIntegrand α k h p.1 p.2 := by
  filter_upwards [sq_mixed_le_Hk_gam (h := h) (k := k) (j := 0) (i := 1) α hα
      (by norm_num) (by omega),
    sq_mixed_le_Hk_gam (h := h) (k := k) (j := 1) (i := 1) α hα (by norm_num) (by omega),
    sq_mixed_le_Hk_gam (h := h) (k := k) (j := 0) (i := 2) α hα (by norm_num) (by omega),
    ae_radius_pos, ae_snd_mem_Iθ] with p h0 h1 h2 hzp hθ
  obtain ⟨z, θ⟩ := p
  dsimp only at h0 h1 h2 hzp hθ ⊢
  have hz : 0 ≤ z := le_of_lt hzp
  have hc1 : |-(2 / (1 + z))| ≤ 2 := by
    rw [abs_neg]; exact abs_two_div_le hz
  have hc2 : |-(3 / (1 + z))| ≤ 3 := by
    rw [abs_neg]; exact abs_three_div_le hz
  have hpt : (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth h) z θ) ^ 2
      ≤ 4 * (5 * (Work.Spaces.Dth h z θ) ^ 2 + (Work.Spaces.mixed 1 1 h z θ) ^ 2
          + 9 * (Work.Spaces.mixed 0 2 h z θ) ^ 2) := by
    have hL := Work.FTS.CoercivityFix.Lhat_eq (Work.Spaces.Dth h) z θ
    have h4 := four_sq_le (Work.Spaces.Dth h z θ) (Work.Spaces.mixed 1 1 h z θ)
      (-(2 / (1 + z)) * Work.Spaces.Dth h z θ)
      (-(3 / (1 + z)) * Work.Spaces.mixed 0 2 h z θ)
    have h5 := sq_mul_le_abs (C := 2) (by norm_num) hc1 (a := Work.Spaces.Dth h z θ)
    have h6 := sq_mul_le_abs (C := 3) (by norm_num) hc2 (a := Work.Spaces.mixed 0 2 h z θ)
    rw [hL]
    have hL2 : Work.Spaces.Dth h z θ + Work.Spaces.Dz (Work.Spaces.Dth h) z θ
          - 2 * Work.Spaces.Dth h z θ / (1 + z)
          - 3 * Work.Spaces.Dth (Work.Spaces.Dth h) z θ / (1 + z)
        = Work.Spaces.Dth h z θ + Work.Spaces.mixed 1 1 h z θ
          + -(2 / (1 + z)) * Work.Spaces.Dth h z θ
          + -(3 / (1 + z)) * Work.Spaces.mixed 0 2 h z θ := by
      rw [show Work.Spaces.Dz (Work.Spaces.Dth h) = Work.Spaces.mixed 1 1 h from rfl,
        show Work.Spaces.Dth (Work.Spaces.Dth h) = Work.Spaces.mixed 0 2 h from rfl]
      ring
    rw [hL2]
    nlinarith [h4, h5, h6]
  have hrho : 0 ≤ Rhoq (Work.Spaces.gam α) z θ :=
    Work.FTS.CoercivityFix.Coer1.Rho_nonneg (Work.Spaces.gam α) z θ hθ
  have hnn : 0 ≤ Work.Spaces.HkIntegrand α k h z θ :=
    Work.Spaces.HkIntegrand_nonneg α k h z θ
  have h0' : (Work.Spaces.Dth h z θ) ^ 2 * Rhoq (Work.Spaces.gam α) z θ
      ≤ Work.Spaces.HkIntegrand α k h z θ := h0
  have h1' : (Work.Spaces.mixed 1 1 h z θ) ^ 2 * Rhoq (Work.Spaces.gam α) z θ
      ≤ Work.Spaces.HkIntegrand α k h z θ := h1
  have h2' : (Work.Spaces.mixed 0 2 h z θ) ^ 2 * Rhoq (Work.Spaces.gam α) z θ
      ≤ Work.Spaces.HkIntegrand α k h z θ := h2
  calc (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth h) z θ) ^ 2
        * Rhoq (Work.Spaces.gam α) z θ
      ≤ (4 * (5 * (Work.Spaces.Dth h z θ) ^ 2 + (Work.Spaces.mixed 1 1 h z θ) ^ 2
          + 9 * (Work.Spaces.mixed 0 2 h z θ) ^ 2))
          * Rhoq (Work.Spaces.gam α) z θ :=
        mul_le_mul_of_nonneg_right hpt hrho
    _ = 20 * ((Work.Spaces.Dth h z θ) ^ 2 * Rhoq (Work.Spaces.gam α) z θ)
          + 4 * ((Work.Spaces.mixed 1 1 h z θ) ^ 2 * Rhoq (Work.Spaces.gam α) z θ)
          + 36 * ((Work.Spaces.mixed 0 2 h z θ) ^ 2 * Rhoq (Work.Spaces.gam α) z θ) := by ring
    _ ≤ 60 * Work.Spaces.HkIntegrand α k h z θ := by linarith [h0', h1', h2', hnn]

/-- The angular derivative `D_θ g` is continuous on the open quadrant for smooth `g`. -/
theorem continuousOn_Dth_Q0 {g : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen g) :
    ContinuousOn (Function.uncurry (Work.Spaces.Dth g)) Q0 := by
  have h : ContinuousOn (Function.uncurry (fun z θ =>
      Real.sin (2 * θ) * Work.Spaces.pth g z θ)) Q0 :=
    (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).mul
      (hs.pth).continuousOn)
  convert h using 1
  funext p
  rfl

end Work.FTS.StrongPersist.H6Aux.R
