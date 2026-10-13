import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.Defs
import Submission.Work.FTS.StrongEps.classC_mixed_sup_le_four
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.GalBasis.cc.Subcut.LNA.IntegrableOn_DzIter_sq_sEta

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
