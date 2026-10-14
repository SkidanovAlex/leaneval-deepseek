import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.abs_Qang_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.L12Aux

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary angular facts

The two endpoints `θ = 0` and `θ = π/2` of `Iθ = [0,π/2]` form a null set, and on the *open*
interval `sin(2θ) > 0`, so every `rpow`-identity below is stated on `Ioo 0 (π/2)`. -/

private lemma sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private lemma continuousOn_sin_two :
    ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)

/-- `(x ^ a) ^ 2 = x ^ (2 * a)` for a positive base. -/
private lemma rpow_sq_of_pos (x a : ℝ) (hx : 0 < x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [pow_two, ← Real.rpow_add hx, show a + a = 2 * a by ring]

/-- Integrability on `Iθ` of a function which is continuous on the open interval and uniformly
bounded there (the two endpoints being null). -/
private lemma integrableOn_Iθ_of_continuousOn_Ioo_of_bound {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 2))) {M : ℝ}
    (hM : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ M) :
    IntegrableOn f Work.Spaces.Iθ := by
  show Integrable f (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
  refine Integrable.mono'
    (MeasureTheory.integrableOn_const (μ := MeasureTheory.volume)
      (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) (C := M)
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (by simp))
    (hf.aestronglyMeasurable measurableSet_Ioo) ?_
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
    (fun θ hθ => by rw [Real.norm_eq_abs]; exact hM θ hθ)

/-- **Cauchy–Schwarz with the two `rpow`-weights split between the two factors.**

For `U`, `V` continuous on the open interval with the two weighted squares integrable,

  `(∫_{Iθ} |U| · |V|)² ≤ (∫_{Iθ} U² sin(2θ)^η) · (∫_{Iθ} V² sin(2θ)^{-η})`.

This is `Work.Spaces.cs_integral` applied to `|U| sin(2θ)^{η/2}` and `|V| sin(2θ)^{-η/2}`,
whose product is `|U| |V|` on the open interval (the only place it is used, so that the
endpoints — where `sin(2θ) = 0` and the `rpow`s are junk — are irrelevant). -/
private theorem cs_split_eta {U V : ℝ → ℝ}
    (hU : ContinuousOn U (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hV : ContinuousOn V (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hUint : IntegrableOn (fun θ => (U θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
      Work.Spaces.Iθ)
    (hVint : IntegrableOn (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, |U θ| * |V θ|) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (U θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
        * (∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  change Integrable (fun θ => (U θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
    (MeasureTheory.volume.restrict Work.Spaces.Iθ) at hUint
  change Integrable (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    (MeasureTheory.volume.restrict Work.Spaces.Iθ) at hVint
  rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo] at hUint hVint ⊢
  have hIoo : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) :=
    fun θ hθ => sin_two_pos_of_mem_Ioo hθ
  have hwcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    continuousOn_sin_two.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ)))
  have hvcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    continuousOn_sin_two.rpow_const
      (fun _ _ => Or.inr (div_nonneg Work.Spaces.eta_nonneg (by norm_num)))
  have hucont : ContinuousOn (fun θ : ℝ => |U θ| * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hU.abs.mul hvcont
  have hvcont' : ContinuousOn
      (fun θ : ℝ => |V θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hV.abs.mul hwcont
  have hu2 : Integrable
      (fun θ : ℝ => (|U θ| * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hUint.congr (MeasureTheory.ae_restrict_of_forall_mem hIoo (fun θ hθ => by
      show (U θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta)
        = (|U θ| * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      rw [mul_pow, sq_abs, rpow_sq_of_pos _ _ (hsinpos θ hθ),
        show 2 * (Work.Spaces.eta / 2) = Work.Spaces.eta by ring]))
  have hv2 : Integrable
      (fun θ : ℝ => (|V θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hVint.congr (MeasureTheory.ae_restrict_of_forall_mem hIoo (fun θ hθ => by
      show (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        = (|V θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
      rw [mul_pow, sq_abs, rpow_sq_of_pos _ _ (hsinpos θ hθ),
        show 2 * (-(Work.Spaces.eta / 2)) = -(Work.Spaces.eta) by ring]))
  have humem : MemLp (fun θ : ℝ => |U θ| * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) 2
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (MeasureTheory.memLp_two_iff_integrable_sq (hucont.aestronglyMeasurable hIoo)).mpr hu2
  have hvmem : MemLp (fun θ : ℝ => |V θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) 2
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (MeasureTheory.memLp_two_iff_integrable_sq (hvcont'.aestronglyMeasurable hIoo)).mpr hv2
  have hcs := Work.Spaces.cs_integral humem hvmem
  have e1 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (|U x| * (Real.sin (2 * x)) ^ (Work.Spaces.eta / 2))
          * (|V x| * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2))))
      = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), |U x| * |V x| := by
    refine MeasureTheory.setIntegral_congr_fun hIoo (fun x hx => ?_)
    rw [show (|U x| * (Real.sin (2 * x)) ^ (Work.Spaces.eta / 2))
          * (|V x| * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2)))
        = (|U x| * |V x|) * ((Real.sin (2 * x)) ^ (Work.Spaces.eta / 2)
            * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2))) by ring,
      ← Real.rpow_add (hsinpos x hx),
      show Work.Spaces.eta / 2 + -(Work.Spaces.eta / 2) = 0 by ring,
      Real.rpow_zero, mul_one]
  have e2 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (|U x| * (Real.sin (2 * x)) ^ (Work.Spaces.eta / 2)) ^ 2)
      = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (U x) ^ 2 * (Real.sin (2 * x)) ^ (Work.Spaces.eta) := by
    refine MeasureTheory.setIntegral_congr_fun hIoo (fun x hx => ?_)
    show (|U x| * (Real.sin (2 * x)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (U x) ^ 2 * (Real.sin (2 * x)) ^ (Work.Spaces.eta)
    rw [mul_pow, sq_abs, rpow_sq_of_pos _ _ (hsinpos x hx),
      show 2 * (Work.Spaces.eta / 2) = Work.Spaces.eta by ring]
  have e3 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (|V x| * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2))) ^ 2)
      = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (V x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)) := by
    refine MeasureTheory.setIntegral_congr_fun hIoo (fun x hx => ?_)
    show (|V x| * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2))) ^ 2
      = (V x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta))
    rw [mul_pow, sq_abs, rpow_sq_of_pos _ _ (hsinpos x hx),
      show 2 * (-(Work.Spaces.eta / 2)) = -(Work.Spaces.eta) by ring]
  rw [e1, e2, e3] at hcs
  exact hcs

/-- **The angular moment is dominated by the angular energy.**

`Qang x k z = ∫_{Iθ} K(θ) · D_z^k x (z,θ) dθ` with `K(θ) = 3 sinθ cos²θ`
(`Work.Elliptic.Qang`, `Work.Elliptic.Ktheta`), and
`Pz x k z = ∫_{Iθ} (D_z^k x (z,θ))² · sin(2θ)^{-η} dθ` (`η = 99/100`; see
`Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.Defs`).

For `ClassC α x`, `α ∈ (0,1]`, `k ≤ 3` and `z > 0`,

  `|Qang x k z| ≤ √(∫_{Iθ} K² sin(2θ)^η) · √(Pz x k z)`,

Proof route: `‖∫‖ ≤ ∫‖·‖` (`MeasureTheory.norm_integral_le_integral_norm`, with
`Real.norm_eq_abs`) and Cauchy–Schwarz (`Work.Spaces.cs_integral`) applied to the two nonnegative
factors `|K(θ)| sin(2θ)^{η/2}` and `|D_z^k x z θ| sin(2θ)^{-η/2}`, whose product is
`|K(θ) D_z^k x z θ|` (at the endpoints both sides vanish since `K(0) = K(π/2) = 0` and
`0^{-η/2} = 0`).  The `L²`-memberships come from `|K| ≤ 3`, `sin(2θ)^η ≤ 1` on `Iθ`
(so `∫_{Iθ} K² sin^η ≤ 9 * π/2 < ∞`) and from the uniform bound on `D_z^k x`
(`Work.FTS.StrongEps.classC_mixed_sup_le_four`, `k ≤ 3 ≤ 4`) together with the integrability of
`sin(2θ)^{-η}` on `Iθ` (`η < 1`, `Work.Spaces.sin_two_rpow` with `p = -η`). -/
theorem abs_Qang_le {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Work.FTS.Galerkin.Fn}
    (hx : Work.FTS.ClassC.ClassC α x) {k : ℕ} (hk : k ≤ 3) :
    ∀ z : ℝ, 0 < z → |Work.Elliptic.Qang x k z|
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
          (Work.Elliptic.Ktheta θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
        * Real.sqrt (Pz x k z) := by
  intro z hz
  -- the `ℋ⁴`-membership carried by the class
  have hmem4 : Work.Spaces.HkMem α 4 x :=
    Work.FTS.OpenPkg.HkMem_mono_open hx.reg 4 (by norm_num) hx.mem
  -- continuity of the two slots on the open angular interval
  have hKc : ContinuousOn (fun θ : ℝ => Work.Elliptic.Ktheta θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hfun : (fun θ : ℝ => Work.Elliptic.Ktheta θ)
        = fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2 := by funext θ; rfl
    rw [hfun]
    exact ((continuous_const.mul Real.continuous_sin).mul
      (Real.continuous_cos.pow 2)).continuousOn
  have hVc : ContinuousOn (fun θ : ℝ => Work.Spaces.DzIter k x z θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((hx.reg.DzIter k).curry_θ hz).continuousOn
  -- integrability of the two Cauchy–Schwarz slots
  have hUint : IntegrableOn (fun θ : ℝ => (Work.Elliptic.Ktheta θ) ^ 2
      * (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) Work.Spaces.Iθ := by
    refine integrableOn_Iθ_of_continuousOn_Ioo_of_bound (M := 9) ?_ ?_
    · exact (hKc.pow 2).mul (continuousOn_sin_two.rpow_const
        (fun _ _ => Or.inr Work.Spaces.eta_nonneg))
    · intro θ hθ
      have hspos : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
      have hs : (Real.sin θ) ^ 2 ≤ 1 := by
        have h := Real.abs_sin_le_one θ
        nlinarith [abs_nonneg (Real.sin θ), sq_abs (Real.sin θ)]
      have hc : (Real.cos θ) ^ 2 ≤ 1 := by
        have h := Real.abs_cos_le_one θ
        nlinarith [abs_nonneg (Real.cos θ), sq_abs (Real.cos θ)]
      have hK2 : (Work.Elliptic.Ktheta θ) ^ 2 ≤ 9 := by
        rw [Work.Elliptic.Ktheta]
        nlinarith [hs, hc, sq_nonneg (Real.cos θ ^ 2), sq_nonneg (Real.sin θ)]
      have hsIn : (Real.sin (2 * θ)) ^ (Work.Spaces.eta) ≤ 1 :=
        Real.rpow_le_one hspos.le (Real.sin_le_one (2 * θ)) Work.Spaces.eta_nonneg
      have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (Work.Spaces.eta) :=
        Real.rpow_nonneg hspos.le _
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hsnn)]
      simpa using mul_le_mul hK2 hsIn hsnn (by norm_num : (0 : ℝ) ≤ 9)
  have hVint : IntegrableOn (fun θ : ℝ => (Work.Spaces.DzIter k x z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    Work.FTS.GalBasis.cc.Subcut.LNA.IntegrableOn_DzIter_sq_sEta hx.reg hmem4 (by omega) hz
  -- Cauchy–Schwarz in the angular variable
  have hcs := cs_split_eta hKc hVc hUint hVint
  -- the triangle inequality for the integral
  have hstep1 : |Work.Elliptic.Qang x k z|
      ≤ ∫ θ in Work.Spaces.Iθ, |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter k x z θ| := by
    have h := MeasureTheory.abs_integral_le_integral_abs
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k x z θ)
    simpa only [Work.Elliptic.Qang, abs_mul] using h
  -- nonnegativity of the three integrals
  have hAnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (Work.Elliptic.Ktheta θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta) :=
    MeasureTheory.setIntegral_nonneg
      (show MeasurableSet Work.Spaces.Iθ from by
        rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _))
  have hWnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter k x z θ| :=
    MeasureTheory.setIntegral_nonneg
      (show MeasurableSet Work.Spaces.Iθ from by
        rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  calc |Work.Elliptic.Qang x k z|
      ≤ ∫ θ in Work.Spaces.Iθ, |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter k x z θ| :=
        hstep1
    _ = Real.sqrt ((∫ θ in Work.Spaces.Iθ,
          |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter k x z θ|) ^ 2) :=
        (Real.sqrt_sq hWnn).symm
    _ ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ,
            (Work.Elliptic.Ktheta θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
          * Pz x k z) := by
        refine Real.sqrt_le_sqrt ?_
        simpa only [Pz] using hcs
    _ = Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Work.Elliptic.Ktheta θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
          * Real.sqrt (Pz x k z) := Real.sqrt_mul hAnn (Pz x k z)

end Work.FTS.StrongEps.EpsE4Thr.L12Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.hasDerivAt_Pz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.L12Aux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The angular integrand of `Pz`, with the `z`-variable displayed: `(D_z^k x u θ)² sin(2θ)^{-η}`.

The angular weight `sin(2θ)^{-η}` is kept as a function of `θ` so that it can play the rôle of
the dominating weight in the parametric-integral theorem; the `z`-derivative of this function
is `PzF'`. -/
private def PzF (x : Work.FTS.Galerkin.Fn) (k : ℕ) : ℝ → ℝ → ℝ :=
  fun u θ => (Work.Spaces.DzIter k x u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The `z`-derivative of `PzF`: `2 · D_z^k x u θ · ∂_z(D_z^k x) u θ · sin(2θ)^{-η}`. -/
private def PzF' (x : Work.FTS.Galerkin.Fn) (k : ℕ) : ℝ → ℝ → ℝ :=
  fun u θ => 2 * (Work.Spaces.DzIter k x u θ * Work.Spaces.pz (Work.Spaces.DzIter k x) u θ)
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

private theorem PzF_apply (x : Work.FTS.Galerkin.Fn) (k : ℕ) (u θ : ℝ) :
    PzF x k u θ = (Work.Spaces.DzIter k x u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
  rfl

private theorem PzF'_apply (x : Work.FTS.Galerkin.Fn) (k : ℕ) (u θ : ℝ) :
    PzF' x k u θ = 2 * (Work.Spaces.DzIter k x u θ * Work.Spaces.pz (Work.Spaces.DzIter k x) u θ)
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
  rfl

/-- **The pointwise sup bound for the `D_z`-iterates of a `ClassC` profile.**

`classC_mixed_sup_le_four` bounds every mixed slot of order `≤ 4` on the open quadrant, and
`mixed b 0 x = D_z^b x` definitionally, so all the `D_z`-iterates up to order `4` are bounded by
a single constant `K₀` on the open quadrant. -/
private theorem dzIter_sup_le {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Work.FTS.Galerkin.Fn}
    (hx : Work.FTS.ClassC.ClassC α x) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ b : ℕ, b ≤ 4 → ∀ {u θ : ℝ}, 0 < u → 0 < θ → θ < π / 2 →
      |Work.Spaces.DzIter b x u θ| ≤ K₀ := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.classC_mixed_sup_le_four
  refine ⟨C / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.StrongGlobal.Xn6 α x,
    mul_nonneg (div_nonneg hCpos.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _), ?_⟩
  intro b hb u θ hu hθ0 hθ1
  have hmem : (u, θ) ∈ Work.Construction.Qd := by
    rw [Work.Construction.Qd]; exact ⟨hu, hθ0, hθ1⟩
  have h := hC α hα hx b 0 (by omega) hmem
  simpa using h

/-- The angular weight `θ ↦ sin(2θ)^{-η}` is continuous on the open quadrant (where `sin 2θ > 0`),
and so is the full `z`-derivative integrand. -/
private theorem continuousOn_sin_rpow_eta :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (x := 2 * p.2)
      (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos]))))

/-- **The derivative of the angular energy `Pz`.**

`Pz x k z = ∫_{Iθ} (D_z^k x (z,θ))² sin(2θ)^{-η} dθ` and
`Qz x k z = ∫_{Iθ} D_z^k x (z,θ) · D_z^{k+1} x (z,θ) sin(2θ)^{-η} dθ`
(`D_z = z ∂_z`, `D_z^{k+1} = D_z (D_z^k)`, `η = 99/100`; see
`Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.Defs`).

For `ClassC α x` with `α ∈ (0,1]` and `k ≤ 3`, and every `z > 0`,

  `(Pz x k)' z = (2/z) · Qz x k z`.

Proof route: `DzIter (k+1) x = Dz (DzIter k x) = z * pz (DzIter k x)` is `rfl`, so pointwise
`∂_z ((DzIter k x z θ)² sin(2θ)^{-η}) = 2 * DzIter k x z θ * pz (DzIter k x) z θ * sin(2θ)^{-η}`
by `Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice_DzIter` and the product rule.  Apply
Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with `μ = volume.restrict (Ioo 0 (π/2))`
(which equals `volume.restrict Iθ` by `Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo`),
`s = Ioo (z/2) (2*z)`, `bound θ = (4 * C₀^2 / z) * sin(2θ)^{-η}`, where
`Work.FTS.StrongEps.classC_mixed_sup_le_four` bounds `|mixed b 0 x t θ| ≤ C₀` on the open
quadrant for `b ≤ 4`; `bound` is integrable since `η < 1` (`Work.Spaces.sin_two_rpow` with
`p = -η`).  The a.e. strong measurability of the slices is
`Work.FTS.EllipticEst.SmoothOpen.aesm_slice_summand` composed with `summand_sq_eq`.  Finally move
the constants out of the integral and use `z * pz (DzIter k x) z θ = DzIter (k+1) x z θ`. -/
theorem hasDerivAt_Pz {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Work.FTS.Galerkin.Fn}
    (hx : Work.FTS.ClassC.ClassC α x) {k : ℕ} (hk : k ≤ 3) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (Pz x k) (2 / z * Qz x k z) z := by
  have hF : Work.FTS.EllipticEst.SmoothOpen x := hx.reg
  obtain ⟨K₀, hK₀nn, hK₀⟩ := dzIter_sup_le hα hx
  -- the localisation neighbourhood of `z`
  have hnhds : Set.Ioo (z / 2) (2 * z) ∈ 𝓝 z :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hk4 : k ≤ 4 := by omega
  have hk14 : k + 1 ≤ 4 := by omega
  -- the rate `2 K₀ / z` at which the angular weight grows
  have hrate : 0 ≤ 2 * K₀ / z := div_nonneg (by linarith) hz.le
  -- the slice of the `z`-derivative of the `k`-th iterate: `|∂_z(D_z^k x)| ≤ 2K₀/z`
  have hpz_le : ∀ {u θ : ℝ}, 0 < u → z / 2 < u → 0 < θ → θ < π / 2 →
      |Work.Spaces.pz (Work.Spaces.DzIter k x) u θ| ≤ 2 * K₀ / z := by
    intro u θ hu hzu hθ0 hθ1
    have hb := hK₀ (k + 1) hk14 hu hθ0 hθ1
    have hident : u * |Work.Spaces.pz (Work.Spaces.DzIter k x) u θ|
        = |Work.Spaces.DzIter (k + 1) x u θ| := by
      rw [Work.Spaces.DzIter_succ]
      simp only [Work.Spaces.Dz]
      rw [abs_mul, abs_of_pos hu]
    have h2 : |Work.Spaces.pz (Work.Spaces.DzIter k x) u θ| ≤ K₀ / u := by
      rw [le_div_iff₀ hu]
      rw [mul_comm]
      rw [hident]
      exact hb
    have h3 : K₀ / u ≤ 2 * K₀ / z := by
      rw [div_le_iff₀ hu]
      calc K₀ = (2 * K₀ / z) * (z / 2) := by field_simp
        _ ≤ (2 * K₀ / z) * u := mul_le_mul_of_nonneg_left (le_of_lt hzu) hrate
    exact le_trans h2 h3
  -- ### measurability of the slices
  have hmeas_F : ∀ᶠ u in 𝓝 z,
      AEStronglyMeasurable (PzF x k u) (volume.restrict (Set.Ioo 0 (π / 2))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with u hu
    have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter k x p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      ((hF.DzIter k).continuousOn.pow 2).mul continuousOn_sin_rpow_eta
    have h := Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter k x p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) hcont hu
    rw [← Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    exact h
  have hmeas_F' : AEStronglyMeasurable (PzF' x k z)
      (volume.restrict (Set.Ioo 0 (π / 2))) := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ => 2 * (Work.Spaces.DzIter k x p.1 p.2
        * Work.Spaces.pz (Work.Spaces.DzIter k x) p.1 p.2)
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      ((continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => (2 : ℝ))
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))).mul
        ((hF.DzIter k).continuousOn.mul ((hF.DzIter k).pz).continuousOn)).mul
        continuousOn_sin_rpow_eta
    have h := Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => 2 * (Work.Spaces.DzIter k x p.1 p.2
        * Work.Spaces.pz (Work.Spaces.DzIter k x) p.1 p.2)
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) hcont hz
    rw [← Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    exact h
  -- ### integrability of the slice at `z`
  have h_int : Integrable (PzF x k z) (volume.restrict (Set.Ioo 0 (π / 2))) := by
    have hwz' : Work.Spaces.w z ≠ 0 := by rw [Work.Spaces.w]; positivity
    have hwz : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hwz'
    have hs := Work.FTS.EllipticEst.integrableOn_zSummand α 7 hF hx.mem k (by omega)
      (Set.mem_Ici.mpr hz.le)
    have h2 : IntegrableOn (PzF x k z) Work.Spaces.Iθ :=
      MeasureTheory.IntegrableOn.congr_fun (hs.const_mul ((Work.Spaces.w z) ^ 2)⁻¹)
        (fun θ hθ => by
          show (Work.Spaces.w z ^ 2)⁻¹ * (Work.Spaces.DzIter k x z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
            = PzF x k z θ
          rw [PzF_apply, summand_sq_eq x k hθ]
          field_simp [hwz'])
        (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
    rw [← Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    exact h2
  -- ### integrability of the dominating bound
  have hb_int : Integrable (fun θ : ℝ => (2 * K₀ * (2 * K₀ / z))
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict (Set.Ioo 0 (π / 2))) := by
    have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta])).1
    rw [← Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    exact h.const_mul _
  -- ### the a.e. bound on the derivative
  have h_bound : ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
      ∀ u ∈ Set.Ioo (z / 2) (2 * z), ‖PzF' x k u θ‖ ≤ (2 * K₀ * (2 * K₀ / z))
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ u hu => ?_)
    have hθ0 : 0 < θ := hθ.1
    have hθ1 : θ < π / 2 := hθ.2
    have hu0 : 0 < u := lt_trans (by linarith) hu.1
    have hsθ : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      (Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith)
        (by linarith [Real.pi_pos])) _).le
    have hA := hK₀ k hk4 hu0 hθ0 hθ1
    have hB := hpz_le hu0 hu.1 hθ0 hθ1
    have hnorm : ‖PzF' x k u θ‖ = 2 * |Work.Spaces.DzIter k x u θ|
        * |Work.Spaces.pz (Work.Spaces.DzIter k x) u θ|
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [PzF'_apply, Real.norm_eq_abs]
      simp only [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num), abs_of_nonneg hsθ]
      ring
    rw [hnorm]
    have h2K : 0 ≤ 2 * K₀ := by linarith
    exact mul_le_mul
      (mul_le_mul (by linarith : 2 * |Work.Spaces.DzIter k x u θ| ≤ 2 * K₀) hB
        (abs_nonneg _) h2K)
      (le_refl _) hsθ (mul_nonneg h2K hrate)

  -- ### the a.e. pointwise derivative
  have h_diff : ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
      ∀ u ∈ Set.Ioo (z / 2) (2 * z),
        HasDerivAt (fun u' => PzF x k u' θ) (PzF' x k u θ) u := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ u hu => ?_)
    have hu0 : 0 < u := lt_trans (by linarith) hu.1
    have h1 := ((hF.hasDerivAt_slice_DzIter k hθ hu0).pow 2).congr_deriv
      (show (2 : ℝ) * Work.Spaces.DzIter k x u θ ^ (2 - 1)
            * Work.Spaces.pz (Work.Spaces.DzIter k x) u θ
          = 2 * (Work.Spaces.DzIter k x u θ * Work.Spaces.pz (Work.Spaces.DzIter k x) u θ) by
        rw [show 2 - 1 = (1 : ℕ) from rfl, pow_one]; ring)
    have h2 := h1.mul_const ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    simpa only [PzF_apply, PzF'_apply, Pi.pow_apply] using h2

  -- ### differentiate under the integral sign
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioo 0 (π / 2)))
    (bound := fun θ : ℝ => (2 * K₀ * (2 * K₀ / z)) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    (F := PzF x k) (F' := PzF' x k) (x₀ := z) (s := Set.Ioo (z / 2) (2 * z))
    hnhds hmeas_F h_int hmeas_F' h_bound hb_int h_diff
  -- ### identify the two sides with `Pz` and `Qz`
  have hfun : Pz x k = fun u => ∫ a, PzF x k u a
      ∂(volume.restrict (Set.Ioo 0 (π / 2))) := by
    funext u
    simp only [Pz]
    rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    simp only [PzF_apply]
  have hQz : Qz x k z = z * ∫ a, (Work.Spaces.DzIter k x z a
      * Work.Spaces.pz (Work.Spaces.DzIter k x) z a)
      * (Real.sin (2 * a)) ^ (-(Work.Spaces.eta))
      ∂(volume.restrict (Set.Ioo 0 (π / 2))) := by
    simp only [Qz]
    rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    have hpt : (fun θ => Work.Spaces.DzIter k x z θ * Work.Spaces.DzIter (k + 1) x z θ
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = fun θ => z * ((Work.Spaces.DzIter k x z θ
          * Work.Spaces.pz (Work.Spaces.DzIter k x) z θ)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      funext θ
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
      ring
    rw [hpt, MeasureTheory.integral_const_mul]
  have hF'val : (∫ a, PzF' x k z a ∂(volume.restrict (Set.Ioo 0 (π / 2))))
      = 2 * ∫ a, (Work.Spaces.DzIter k x z a * Work.Spaces.pz (Work.Spaces.DzIter k x) z a)
          * (Real.sin (2 * a)) ^ (-(Work.Spaces.eta))
          ∂(volume.restrict (Set.Ioo 0 (π / 2))) := by
    have hpt : (fun a => PzF' x k z a)
        = fun a => 2 * ((Work.Spaces.DzIter k x z a
          * Work.Spaces.pz (Work.Spaces.DzIter k x) z a)
          * (Real.sin (2 * a)) ^ (-(Work.Spaces.eta))) := by
      funext a
      rw [PzF'_apply]
      ring
    rw [hpt, MeasureTheory.integral_const_mul]
  have hval : 2 / z * Qz x k z
      = ∫ a, PzF' x k z a ∂(volume.restrict (Set.Ioo 0 (π / 2))) := by
    rw [hQz, hF'val]
    field_simp
  rw [hfun, hval]
  exact key.2

end Work.FTS.StrongEps.EpsE4Thr.L12Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.sq_two_Qz_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.L12Aux

set_option linter.unusedVariables false

/-! ## Two elementary pointwise identities for the weighted slices

The Cauchy–Schwarz argument is run on the *weighted* slices
`U θ = D_z^k x (z,θ) · w z / sin(2θ)^{η/2}`, whose a.e. strong measurability and whose square
integrability are supplied by the `HkMem`-machinery of `Work.FTS.EllipticEst.OpenQDefs`
(`SmoothOpen.aesm_slice_summand`, `integrableOn_zSummand`).  The price is that the integrals
`∫_{Iθ} U²`, `∫_{Iθ} U·V` have to be converted back into `(w z)²·Pz` resp. `(w z)²·Qz`, which
needs the two `Real.rpow` identities below. -/

/-- **The square of `c / sin(2θ)^{η/2}`**, in endpoint-safe form (`sin(2θ) = 0` is allowed:
both sides vanish there). -/
theorem div_rpow_half_sq (c s : ℝ) (hs : 0 ≤ s) :
    (c / s ^ (Work.Spaces.eta / 2)) ^ 2 = c ^ 2 * s ^ (-(Work.Spaces.eta)) := by
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h]
    simp [Real.zero_rpow (by norm_num [Work.Spaces.eta] : -(Work.Spaces.eta) ≠ 0),
      Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0)]
  · have hsq : (s ^ (Work.Spaces.eta / 2)) ^ 2 = s ^ Work.Spaces.eta := by
      rw [sq, ← Real.rpow_add h]
      ring_nf
    rw [div_pow, hsq, Real.rpow_neg h.le]
    field_simp

/-- **The product of two consecutive weighted slices.**  For `θ ∈ Iθ`,
`(D_z^k x·w/s^{η/2})·(D_z^{k+1} x·w/s^{η/2}) = (w z)²·D_z^k x·D_z^{k+1} x·s^{-η}` with
`s = sin(2θ)` — the `sin(2θ)^{-η}`-weighted correlation integrand of `Qz`, times `(w z)²`. -/
theorem summand_prod_eq (x : Work.FTS.Galerkin.Fn) (k : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DzIter k x z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      * (Work.Spaces.DzIter (k + 1) x z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      = (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter k x z θ
        * Work.Spaces.DzIter (k + 1) x z θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hs := sin_two_nonneg_of_mem_Iθ hθ
  rw [show (Work.Spaces.DzIter k x z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      * (Work.Spaces.DzIter (k + 1) x z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      = Work.Spaces.DzIter k x z θ * Work.Spaces.DzIter (k + 1) x z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 from by ring,
    div_rpow_half_sq (Work.Spaces.w z) (Real.sin (2 * θ)) hs]
  ring

/-- **Cauchy–Schwarz for the angular correlation `Qz`.**

`Pz x k z = ∫_{Iθ} (D_z^k x (z,θ))² sin(2θ)^{-η} dθ` and
`Qz x k z = ∫_{Iθ} D_z^k x (z,θ) · D_z^{k+1} x (z,θ) sin(2θ)^{-η} dθ`
(see `Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.Defs`).

For `ClassC α x`, `α ∈ (0,1]`, `k ≤ 3` and `z > 0`,

  `(2 · Qz x k z)^2 ≤ 4 · Pz x k z · Pz x (k+1) z`,

i.e. `|z (Pz x k)' z| ≤ 2 √(Pz x k z · Pz x (k+1) z)` (combine with `hasDerivAt_Pz`).

Proof route: `2 * Qz x k z = ∫ θ in Iθ, (2 * DzIter k x z θ * DzIter (k+1) x z θ)
* sin(2θ)^{-η}`, and the integrand factors as
`(√2 * DzIter k x z θ * sin(2θ)^{-η/2}) * (√2 * DzIter (k+1) x z θ * sin(2θ)^{-η/2})`.
Apply `Work.Spaces.cs_integral` (or `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`); the
required `MemLp 2` of both factors follows from the uniform bound
`|DzIter j x z θ| ≤ C₀` on the open quadrant (`Work.FTS.StrongEps.classC_mixed_sup_le_four`
with `j ≤ 4`, so `k, k+1 ≤ 4`) and the integrability of `sin(2θ)^{-η}` on `Iθ` (`η < 1`,
`Work.Spaces.sin_two_rpow` with `p = -η`).  Use `Real.rpow_add`/`Real.rpow_neg`
(`(sin(2θ)^{-η/2})² = sin(2θ)^{-η}`) and `L12Aux.summand_sq_eq` as needed. -/
theorem sq_two_Qz_le {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Work.FTS.Galerkin.Fn}
    (hx : Work.FTS.ClassC.ClassC α x) {k : ℕ} (hk : k ≤ 3) {z : ℝ} (hz : 0 < z) :
    (2 * Qz x k z) ^ 2 ≤ 4 * Pz x k z * Pz x (k + 1) z := by
  -- the two weighted angular slices
  set U : ℝ → ℝ := fun θ => Work.Spaces.DzIter k x z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) with hU
  set V : ℝ → ℝ := fun θ => Work.Spaces.DzIter (k + 1) x z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) with hV
  -- they are square-integrable on `Iθ`
  have hUaesm : AEStronglyMeasurable U (volume.restrict Work.Spaces.Iθ) := by
    rw [hU]
    exact hx.reg.aesm_slice_summand k hz
  have hVaesm : AEStronglyMeasurable V (volume.restrict Work.Spaces.Iθ) := by
    rw [hV]
    exact hx.reg.aesm_slice_summand (k + 1) hz
  have hUint : Integrable (fun θ => U θ ^ 2) (volume.restrict Work.Spaces.Iθ) := by
    rw [hU]
    exact Work.FTS.EllipticEst.integrableOn_zSummand α 7 hx.reg hx.mem k (by omega)
      (Set.mem_Ici.mpr hz.le)
  have hVint : Integrable (fun θ => V θ ^ 2) (volume.restrict Work.Spaces.Iθ) := by
    rw [hV]
    exact Work.FTS.EllipticEst.integrableOn_zSummand α 7 hx.reg hx.mem (k + 1) (by omega)
      (Set.mem_Ici.mpr hz.le)
  have hUmem : MemLp U 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hUaesm).2 hUint
  have hVmem : MemLp V 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hVaesm).2 hVint
  -- Cauchy–Schwarz
  have hcs := Work.Spaces.cs_integral (s := Work.Spaces.Iθ) hUmem hVmem
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- the three integrals
  have eUV : (∫ θ in Work.Spaces.Iθ, U θ * V θ)
      = (Work.Spaces.w z) ^ 2 * Qz x k z :=
    calc (∫ θ in Work.Spaces.Iθ, U θ * V θ)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
            (Work.Spaces.DzIter k x z θ * Work.Spaces.DzIter (k + 1) x z θ
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
          refine MeasureTheory.setIntegral_congr_fun hIθ (fun θ hθ => ?_)
          rw [hU, hV]
          exact summand_prod_eq x k hθ
      _ = (Work.Spaces.w z) ^ 2 * Qz x k z := by
          rw [MeasureTheory.integral_const_mul]
          rfl
  have eU2 : (∫ θ in Work.Spaces.Iθ, U θ ^ 2) = (Work.Spaces.w z) ^ 2 * Pz x k z :=
    calc (∫ θ in Work.Spaces.Iθ, U θ ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
            ((Work.Spaces.DzIter k x z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
          refine MeasureTheory.setIntegral_congr_fun hIθ (fun θ hθ => ?_)
          rw [hU, summand_sq_eq x k hθ]
          ring
      _ = (Work.Spaces.w z) ^ 2 * Pz x k z := by
          rw [MeasureTheory.integral_const_mul]
          rfl
  have eV2 : (∫ θ in Work.Spaces.Iθ, V θ ^ 2) = (Work.Spaces.w z) ^ 2 * Pz x (k + 1) z :=
    calc (∫ θ in Work.Spaces.Iθ, V θ ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
            ((Work.Spaces.DzIter (k + 1) x z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
          refine MeasureTheory.setIntegral_congr_fun hIθ (fun θ hθ => ?_)
          rw [hV, summand_sq_eq x (k + 1) hθ]
          ring
      _ = (Work.Spaces.w z) ^ 2 * Pz x (k + 1) z := by
          rw [MeasureTheory.integral_const_mul]
          rfl
  -- cancel the positive factor `(w z)^4`
  have hw : (0 : ℝ) < (Work.Spaces.w z) ^ 2 := by
    rw [Work.Spaces.w]
    positivity
  have hkey : (Qz x k z) ^ 2 ≤ Pz x k z * Pz x (k + 1) z := by
    rw [eUV, eU2, eV2] at hcs
    have h3 : ((Work.Spaces.w z) ^ 2) ^ 2 * (Qz x k z) ^ 2
        ≤ ((Work.Spaces.w z) ^ 2) ^ 2 * (Pz x k z * Pz x (k + 1) z) := by
      nlinarith [hcs]
    exact le_of_mul_le_mul_left h3 (pow_pos hw 2)
  have h4 : (2 * Qz x k z) ^ 2 = 4 * (Qz x k z) ^ 2 := by ring
  rw [h4]
  nlinarith [hkey]

end Work.FTS.StrongEps.EpsE4Thr.L12Aux
end
end
