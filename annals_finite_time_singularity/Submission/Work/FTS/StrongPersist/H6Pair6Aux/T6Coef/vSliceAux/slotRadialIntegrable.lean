import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `vSliceAux/slotRadialIntegrable`: the two mixed slots are radially integrable

The `ℋ⁴`-integrand of Elgindi's weighted space is the finite sum of the squares of the
weighted derivatives `D_z^i f · w/ sin(2θ)^{η/2}` and `D_z^j D_θ^i f · W` (`i ≥ 1`), where
`W = w · sin(2θ)^{-γ/2}`.  Hence *each* of its summands is integrable wherever the whole
`HkIntegrand` is, being a nonnegative summand of it.

This file records the two slots needed by the angular Agmon/Poincaré inequality on the
`θ`-slice, namely `(i, j) = (1, 0)` and `(1, 1)`: for every interior angle `θ`,
`IntegrableOn (fun s => HkIntegrand α 4 f s θ) Iz` implies

  `IntegrableOn (fun s => sin(2θ)^{-γ} · (D_z^j D_θ f s θ)² · w(s)²) Iz`,   `j ≤ 3`,

since on the open interval the `(i,j) = (1,j)` summand of the integrand is *exactly*
`sin(2θ)^{-γ} · (D_z^j D_θ f)² · w²` (`sq_rpow_neg` undoes the half exponent of `wTheta`).
The a.e. strong measurability of that radial slice comes from the joint continuity of
`(z, θ) ↦ D_z^j D_θ f · W` on the open quadrant (`SmoothOpen` supplies it, and only `z > 0`,
`0 < θ < π/2` are needed; the missing point `z = 0` is null).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.vSliceAux

set_option autoImplicit false

/-! ## Elementary facts about the weights -/

/-- `(s^{-γ/2})² = s^{-γ}` for `s > 0`: the half exponent of `wTheta` is undone by squaring. -/
private lemma sq_rpow_neg (s γ : ℝ) (hs : 0 < s) : (s ^ (-(γ / 2))) ^ 2 = s ^ (-γ) := by
  rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hs)]
  congr 1
  ring

/-- The weight `W = w · sin(2θ)^{-γ/2}` is continuous on the open quadrant (both `z > 0` and
`θ ∈ (0,π/2)` are needed: `w` is finite at `z > 0` and `sin(2θ) > 0` at interior angles). -/
private lemma continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      Work.FTS.EllipticEst.Q0 := by
    have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun2]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2)
      (fun p hp => pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))
  exact hw.mul
    (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp))))

/-- The `z`-slice at a fixed interior angle of a function continuous on the open quadrant
`Q0 = (0,∞) × (0,π/2)` is a.e. strongly measurable for `volume.restrict Iz` (the omitted
point is `z = 0`, a null set). -/
private lemma aesm_zslice_of_continuousOn_Q0 (G : ℝ × ℝ → ℝ)
    (hG : ContinuousOn G Work.FTS.EllipticEst.Q0) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    AEStronglyMeasurable (fun z : ℝ => G (z, θ)) (volume.restrict Work.Spaces.Iz) := by
  have hIz : (volume.restrict Work.Spaces.Iz : Measure ℝ) = volume.restrict (Set.Ioi (0 : ℝ)) :=
    (MeasureTheory.Measure.restrict_congr_set
      (show Set.Ioi (0 : ℝ) =ᵐ[volume] Work.Spaces.Iz
        from MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))).symm
  rw [hIz]
  exact (hG.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun z hz => ⟨hz, hθ⟩)).aestronglyMeasurable measurableSet_Ioi

/-- On the open interval the squared weighted mixed slot is `sin(2θ)^{-γ} · (D_z^j D_θ^i f)² · w²`:
this is the `(i,j)`-summand of `HkIntegrand` written with the angular weight separated off. -/
private lemma slot_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) (θ : ℝ)
    (hs : 0 < Real.sin (2 * θ)) (z : ℝ) :
    (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow,
    sq_rpow_neg (Real.sin (2 * θ)) (Work.Spaces.gam α) hs]
  ring

/-! ## The single mixed slot -/

/-- **A single mixed slot of `HkIntegrand α 4` is radially integrable.**  If the `θ`-slice of
the `ℋ⁴`-integrand is integrable on `Iz`, then so is the `(i,j)`-slot
`sin(2θ)^{-γ} · (D_z^j D_θ^i f)² · w²` for every `i ≥ 1`, `i + j ≤ 4`. -/
private lemma slot_integrable {α : ℝ} {f : ℝ → ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hint : MeasureTheory.IntegrableOn
      (fun s => Work.Spaces.HkIntegrand α 4 f s θ) Work.Spaces.Iz)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    MeasureTheory.IntegrableOn (fun s => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed j i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  -- identify the slot with the `(i,j)`-summand of the integrand
  have hEq : (fun s : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
      = fun s : ℝ => (Work.Spaces.mixed j i f s θ * Work.Spaces.Wt α s θ) ^ 2 := by
    funext s
    exact (slot_eq α f j i θ hs s).symm
  rw [hEq]
  refine MeasureTheory.Integrable.mono' hint
    ((aesm_zslice_of_continuousOn_Q0 _
      (((hF.mixed j i).continuousOn).mul (continuousOn_Wt_Q0 α)) hθ).pow 2) ?_
  filter_upwards with s
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f s θ i j hi hij

/-! ## The requested statement -/

theorem slotRadialIntegrable : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (θ : ℝ),
    θ ∈ Set.Ioo 0 (Real.pi / 2) →
    Work.FTS.EllipticEst.SmoothOpen f →
    MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α 4 f s θ) Work.Spaces.Iz →
      MeasureTheory.IntegrableOn (fun s => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 0 1 f s θ) ^ 2 * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz ∧
      MeasureTheory.IntegrableOn (fun s => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 1 1 f s θ) ^ 2 * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz := by
  intro α f θ hθ hF hint
  exact ⟨slot_integrable hθ hF hint 0 1 le_rfl (by norm_num),
    slot_integrable hθ hF hint 1 1 le_rfl (by norm_num)⟩

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.vSliceAux
