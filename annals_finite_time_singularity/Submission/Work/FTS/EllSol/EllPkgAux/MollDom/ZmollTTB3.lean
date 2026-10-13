/-
# `ZmollTTB3` — the core estimate for `zmoll_ttDom`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.ZmollTTB2
import Submission.Work.FTS.EllSol.EllPkgAux.thMollTransfer2
import Submission.Work.FTS.EllSol.EllPkgAux.mollHdom

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ

open Work.FTS.EllSol.PkgK5.K5c

/-- **The core estimate.**  Everything except the `TraceClass` bookkeeping. -/
theorem zmoll_ttDom_core (G : ℝ → ℝ → ℝ) (hF : FourInts G) (hsl : SliceData G)
    (hdom : LocallyIntegrable (fun t : ℝ => ∫ s in Iθ, |Hxyc G t s|) volume)
    (hsqrt : LocallyIntegrable (fun t : ℝ => Real.sqrt (E2s G (Real.exp t))) volume)
    (δ ε : ℝ) (hP : Params δ ε) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ θ ∈ Iθ,
        |Work.Spaces.pth (Work.Spaces.pth (zmoll G δ ε)) z θ|
          ≤ ∫ t : ℝ, sKer δ (Real.log z - t) *
              (∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) := by
  obtain ⟨hε0, hε1, hδ0, hδ1⟩ := hP
  have hSnfun : LocallyIntegrable (fun t : ℝ => SNg G t) volume := by
    have hfun : (fun t : ℝ => ∫ s in Iθ, |Hxyc G t s|) = (fun t : ℝ => SNg G t) := by
      funext t
      simp only [SNg]
      refine MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun s hs => ?_)
      simp only [Hxyc, Work.FTS.EllSol.PkgK5.K5c.Qext_of_mem G (Real.exp t) s hs]
    rw [hfun] at hdom
    exact hdom
  obtain ⟨Mk, hMk0, hMk⟩ := kmθ_bdd hε0
  obtain ⟨Mk2, hMk20, hMk2⟩ := kmθθ_bdd hε0
  have hJboundB : ∀ y t : ℝ, ‖JB G ε y t‖ ≤ (Mk • SNg G) t := by
    intro y t
    simpa only [Real.norm_eq_abs, JB, Pi.smul_apply, smul_eq_mul] using
      abs_fold_le G hsl hMk0 (fun y s => hMk y s) y t
  have hJboundC : ∀ y t : ℝ, ‖JC G ε y t‖ ≤ (Mk2 • SNg G) t := by
    intro y t
    simpa only [Real.norm_eq_abs, JC, Pi.smul_apply, smul_eq_mul] using
      abs_fold_le G hsl hMk20 (fun y s => hMk2 y s) y t
  have hJboundA : ∀ y t : ℝ, ‖JA G ε y t‖ ≤ ((3 * (ε * sMass)⁻¹) • SNg G) t := by
    intro y t
    simpa only [Real.norm_eq_abs, JA, Pi.smul_apply, smul_eq_mul] using
      abs_fold_le G hsl (by have := sMass_pos; positivity)
        (fun y s => le_trans (abs_km_le_KJ hε0 y s)
          (Work.FTS.EllSol.EllPkgAux.KJ_le hε0 y s)) y t
  have hCjA : LocallyIntegrable (fun t : ℝ => (Mk • SNg G) t) volume := hSnfun.smul Mk
  have hCjB : LocallyIntegrable (fun t : ℝ => (Mk2 • SNg G) t) volume := hSnfun.smul Mk2
  have hJintA : ∀ x : ℝ, ∀ p q : ℝ,
      IntegrableOn (fun t : ℝ => JA G ε x t) (Set.Icc p q) := by
    intro x p q
    have hb : IntegrableOn (fun t : ℝ => ((3 * (ε * sMass)⁻¹) • SNg G) t) (Set.Icc p q) :=
      (hSnfun.integrableOn_isCompact isCompact_Icc).const_mul _
    refine Integrable.mono' hb ((aesm_JA G hsl.sm ε x).restrict) ?_
    exact Filter.Eventually.of_forall fun t => hJboundA x t
  have hJintB : ∀ x : ℝ, ∀ p q : ℝ,
      IntegrableOn (fun t : ℝ => JB G ε x t) (Set.Icc p q) := by
    intro x p q
    have hb : IntegrableOn (fun t : ℝ => (Mk • SNg G) t) (Set.Icc p q) :=
      (hSnfun.integrableOn_isCompact isCompact_Icc).const_mul _
    refine Integrable.mono' hb ((aesm_JB G hsl.sm ε x).restrict) ?_
    exact Filter.Eventually.of_forall fun t => hJboundB x t
  have hJintC : ∀ x : ℝ, ∀ p q : ℝ,
      IntegrableOn (fun t : ℝ => JC G ε x t) (Set.Icc p q) := by
    intro x p q
    have hb : IntegrableOn (fun t : ℝ => (Mk2 • SNg G) t) (Set.Icc p q) :=
      (hSnfun.integrableOn_isCompact isCompact_Icc).const_mul _
    refine Integrable.mono' hb ((aesm_JC G hsl.sm ε x).restrict) ?_
    exact Filter.Eventually.of_forall fun t => hJboundC x t
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
  intro θ hθ
  have hθw : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hA : ∀ x ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4),
      HasDerivAt (fun x' : ℝ => ∫ t : ℝ, sKer δ (Real.log z - t) * JA G ε x' t)
        (∫ t : ℝ, sKer δ (Real.log z - t) * JB G ε x t) x := by
    intro x hx
    exact conv_t_step (JA G ε) (JB G ε) hδ0 (by linarith) hCjA
      (fun y => aesm_JA G hsl.sm ε y) (fun y => aesm_JB G hsl.sm ε y) hJintA
      (fun t y => inner_hasDerivAt (K := fun y s => km ε y s) (K' := fun y s => kmθ ε y s)
        (C := Mk) (fun y => continuous_km ε y) (fun y => continuous_kmθ ε y)
        (fun y s => hMk y s) (fun y s => hasDerivAt_km_theta ε y s)
        (hsl.cont (Real.exp t) (Real.exp_pos t)))
      hJboundB x
  have hB : ∀ x ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4),
      HasDerivAt (fun x' : ℝ => ∫ t : ℝ, sKer δ (Real.log z - t) * JB G ε x' t)
        (∫ t : ℝ, sKer δ (Real.log z - t) * JC G ε x t) x := by
    intro x hx
    exact conv_t_step (JB G ε) (JC G ε) hδ0 (by linarith) hCjB
      (fun y => aesm_JB G hsl.sm ε y) (fun y => aesm_JC G hsl.sm ε y) hJintB
      (fun t y => inner_hasDerivAt (K := fun y s => kmθ ε y s) (K' := fun y s => kmθθ ε y s)
        (C := Mk2) (fun y => continuous_kmθ ε y) (fun y => continuous_kmθθ ε y)
        (fun y s => hMk2 y s) (fun y s => hasDerivAt_kmθ_theta ε y s)
        (hsl.cont (Real.exp t) (Real.exp_pos t)))
      hJboundC x
  have hfold : ∀ x ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4),
      zmoll G δ ε z x = ∫ t : ℝ, sKer δ (Real.log z - t) * JA G ε x t := by
    intro x hx
    simp only [Work.FTS.EllSol.PkgK5.K5c.zmoll, JA]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    change sKer δ (Real.log z - t) * thMoll G ε (Real.exp t) x
      = sKer δ (Real.log z - t) * ∫ s in Iθ, km ε x s * G (Real.exp t) s
    rw [Work.FTS.EllSol.EllPkgAux.thMoll_fold (u := G) (z := Real.exp t) (θ' := x)
      hε0 hε1 (hsl.val0 _) (hsl.valpi _) (hsl.cont _ (Real.exp_pos t)) hx.1 hx.2]
    simp only [Work.FTS.EllSol.EllPkgAux.Kern, km]
  have hderiv1 : (fun x : ℝ => deriv (fun x' : ℝ => zmoll G δ ε z x') x)
      =ᶠ[𝓝 θ] fun x : ℝ => ∫ t : ℝ, sKer δ (Real.log z - t) * JB G ε x t := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4), isOpen_Ioo.mem_nhds hθw, ?_⟩
    intro x hx
    have h1 : (fun x' : ℝ => zmoll G δ ε z x')
        =ᶠ[𝓝 x] fun x' : ℝ => ∫ t : ℝ, sKer δ (Real.log z - t) * JA G ε x' t :=
      Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4), isOpen_Ioo.mem_nhds hx, hfold⟩
    show deriv (fun x' : ℝ => zmoll G δ ε z x') x
        = ∫ t : ℝ, sKer δ (Real.log z - t) * JB G ε x t
    rw [Filter.EventuallyEq.deriv_eq h1]
    exact (hA x hx).deriv
  have hd2 : deriv (deriv (fun x' : ℝ => zmoll G δ ε z x')) θ
      = ∫ t : ℝ, sKer δ (Real.log z - t) * JC G ε θ t := by
    rw [Filter.EventuallyEq.deriv_eq hderiv1, (hB θ hθw).deriv]
  have hd3 : Work.Spaces.pth (Work.Spaces.pth (zmoll G δ ε)) z θ
      = ∫ t : ℝ, sKer δ (Real.log z - t) *
          (∫ s in Iθ, km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) := by
    rw [show Work.Spaces.pth (Work.Spaces.pth (zmoll G δ ε)) z θ
        = deriv (deriv (fun x' : ℝ => zmoll G δ ε z x')) θ from rfl, hd2]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show sKer δ (Real.log z - t) * JC G ε θ t
        = sKer δ (Real.log z - t) *
          (∫ s in Iθ, km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s)
    rw [JC, ibp_km hsl hε0 hε1 (Real.exp_pos t) hθ]
    simp only [Work.Spaces.pth]
  rw [hd3]
  have hint : Integrable (fun t : ℝ => sKer δ (Real.log z - t) *
      ∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) volume :=
    rhs_integrable G hsl hsqrt hδ0 hε0 hz
  calc |∫ t : ℝ, sKer δ (Real.log z - t) *
        (∫ s in Iθ, km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s)|
      ≤ ∫ t : ℝ, ‖sKer δ (Real.log z - t) *
          (∫ s in Iθ, km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s)‖ :=
        MeasureTheory.norm_integral_le_integral_norm (μ := volume)
          (fun t : ℝ => sKer δ (Real.log z - t) *
            (∫ s in Iθ, km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s))
    _ = ∫ t : ℝ, sKer δ (Real.log z - t) *
          ‖∫ s in Iθ, km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s‖ := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        show ‖sKer δ (Real.log z - t) *
            (∫ s in Iθ, km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s)‖
          = sKer δ (Real.log z - t) *
            ‖∫ s in Iθ, km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s‖
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sKer_nonneg hδ0 _)]
        simp only [Real.norm_eq_abs]
    _ ≤ ∫ t : ℝ, sKer δ (Real.log z - t) *
          (∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t =>
          mul_nonneg (sKer_nonneg hδ0 _) (norm_nonneg _)) hint ?_
        exact Filter.Eventually.of_forall fun t =>
          mul_le_mul_of_nonneg_left
            (by simpa only [Real.norm_eq_abs] using abs_inner_le_KJ G hsl hε0 θ t)
            (sKer_nonneg hδ0 _)

end Work.FTS.EllSol.EllPkgAux.MollDom
