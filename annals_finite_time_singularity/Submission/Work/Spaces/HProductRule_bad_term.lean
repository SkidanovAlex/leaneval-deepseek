import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.Have
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.EGap.integrableOn_PhiD
import Submission.Work.FTS_RegExport.RXT.Slots.v2_paramC2
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_f_bound
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.thD_reindex
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.Blocks.IMC.Dz_cot_box_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.IMC

set_option autoImplicit false








end Work.Blocks.IMC
end
-- ===== merged: Submission.Work.Blocks.IMC.hardy_weighted_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.IMC

noncomputable section

set_option autoImplicit false

/-! ## Elementary angular identities -/



/-! ## Vanishing off the radial support, and smoothness of the slices -/






/-! ## Identification of the angular integrals with the Hardy quantities -/


/-! ## Integrability of the two dominating outer integrands -/


/-! ## The slicewise Hardy inequality -/


/-! ## The main theorem -/


end

end Work.Blocks.IMC
end
-- ===== merged: Submission.Work.Blocks.IMC.mixed_pairing_identity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.IMC

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## Vanishing of the derived quantities off the support

A function which vanishes on the (open) complement of `[δ,R]` in the `z`-variable has all its
`z`- and `θ`-derivatives vanishing there too, since it is locally `0`. -/








/-! ## Slice smoothness -/


/-! ## The one-dimensional integration by parts at fixed `θ` -/


/-! ## Continuity on the open strip of the two pairing integrands -/



/-! ## From the strip to the quadrant, and bounds on the box -/


/-! ## The Fubini reduction -/




/-! ## The mixed pairing identity -/


end Work.Blocks.IMC
end
end
-- ===== merged: Submission.Work.Blocks.IMC.weighted_sq_idents =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.IMC

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Vanishing of the derived functions off the support in `z` -/






/-! ## Bounds on the compact box -/


/-- Squaring a function preserves continuity in the uncurried form. -/
private theorem continuousOn_uncurry_sq {F : ℝ → ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (h : ContinuousOn (Function.uncurry F) s) :
    ContinuousOn (Function.uncurry (fun z θ => F z θ ^ 2)) s :=
  (h.pow 2).congr (fun _ _ => rfl)

/-! ## The Fubini bridge -/


/-! ## The three identities -/


end Work.Blocks.IMC
end
end
-- ===== merged: Submission.Work.Coercivity.dthIterAng_sq_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

namespace CT

/-- `CT.DthIterAng i` is the `i`-fold iterate of the univariate operator `Spaces.dthU`
(`dthU φ = sin(2·) · φ'`); in particular `D_θ^i Γ = dthU^[i] Γ`. -/
lemma DthIterAng_eq_iterate (i : ℕ) (g : ℝ → ℝ) :
    DthIterAng i g = Spaces.dthU^[i] g := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [DthIterAng_succ, ih, Function.iterate_succ_apply']
      rfl

end CT

/-- `Γ(θ) = (sin θ cos²θ)^{α/3}` is continuous on the angular interval `Iθ`. -/
lemma dthIterAng_continuousOn_Gam (α : ℝ) (hα : 0 < α) :
    ContinuousOn (Spaces.Gam α) Spaces.Iθ := by
  change ContinuousOn (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)) Spaces.Iθ
  have hbase : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Spaces.Iθ := by
    fun_prop
  have hα3 : (0 : ℝ) ≤ α / 3 := by linarith
  exact hbase.rpow_const (p := α / 3) (fun θ _ => Or.inr hα3)

/-- Every angular derivative `D_θ^i Γ` is continuous on `Iθ`.

For `i ≥ 1`, `D_θ^i Γ` agrees on `Iθ` with the everywhere smooth function
`α · Tfun (i-1) α · Γ`: the identity `dthU_iter_Gam` holds on the open interval
`(0,π/2)`, and at both endpoints the two sides vanish (`sin(2θ) = 0` kills the left-hand
side, and `Γ = 0` kills the right-hand side). -/
lemma dthIterAng_continuousOn (i : ℕ) (α : ℝ) (hα : 0 < α) :
    ContinuousOn (CT.DthIterAng i (Spaces.Gam α)) Spaces.Iθ := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    simpa using dthIterAng_continuousOn_Gam α hα
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have heq : ∀ θ ∈ Spaces.Iθ,
        CT.DthIterAng (k + 1) (Spaces.Gam α) θ = α * Spaces.Tfun k α θ * Spaces.Gam α θ := by
      intro θ hθ
      rw [CT.DthIterAng_eq_iterate]
      rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · subst h0
        rw [Spaces.dthU_iter_eq_zero_of_sin_eq_zero' (fun t => Spaces.Gam α t) (by omega)
          (by simp), Spaces.Gam_zero_left α (ne_of_gt hα)]
        ring
      rcases eq_or_lt_of_le hθ.2 with h1 | h1
      · subst h1
        rw [Spaces.dthU_iter_eq_zero_of_sin_eq_zero' (fun t => Spaces.Gam α t) (by omega)
          (by rw [show 2 * (π / 2) = π from by ring, Real.sin_pi]),
          Spaces.Gam_zero_right α (ne_of_gt hα)]
        ring
      · exact Spaces.dthU_iter_Gam k α hα ⟨h0, h1⟩
    have hcont : ContinuousOn (fun θ : ℝ => α * Spaces.Tfun k α θ * Spaces.Gam α θ) Spaces.Iθ :=
      ((continuous_const.mul (Spaces.Tfun_smooth k α).continuous).continuousOn).mul
        (dthIterAng_continuousOn_Gam α hα)
    exact hcont.congr (fun θ hθ => heq θ hθ)

/-- **A uniform bound `|D_θ^i Γ| ≤ C_i Γ` on `Iθ`.**  For `i = 0` one can take `C_0 = 1`
(since `0 ≤ Γ ≤ 1`), and for `i ≥ 1` the bound `Spaces.dthU_Gam_le` gives
`|D_θ^i Γ| ≤ α · tBound (i-1) 0 · Γ`. -/
lemma dthIterAng_le_Gam (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Spaces.Iθ, |CT.DthIterAng i (Spaces.Gam α) θ| ≤ C * Spaces.Gam α θ := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    refine ⟨1, zero_le_one, fun θ hθ => ?_⟩
    rw [CT.DthIterAng_zero]
    exact le_of_eq (by rw [one_mul, abs_of_nonneg (Spaces.Gam_bounds α θ hα hθ).1])
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    refine ⟨α * Spaces.tBound k 0, mul_nonneg (le_of_lt hα) (Spaces.tBound_nonneg k 0),
      fun θ hθ => ?_⟩
    rw [CT.DthIterAng_eq_iterate]
    simpa using Spaces.dthU_Gam_le (k + 1) (by omega) α hα hα1 θ hθ

/-- The `γ`-integrand `(D_θ^i Γ)² sin(2θ)^{-γ}` is dominated pointwise by
`C_i² sin(2θ)^{2α/3 - γ}` on `Iθ`. -/
lemma dthIterAng_sq_mul_le_gam {α C : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 ≤ C) {i : ℕ}
    (hbound : ∀ θ ∈ Spaces.Iθ, |CT.DthIterAng i (Spaces.Gam α) θ| ≤ C * Spaces.Gam α θ) :
    ∀ θ ∈ Spaces.Iθ,
      (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
        ≤ C ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Spaces.gam α) := by
  intro θ hθ
  have hG := Spaces.Gam_bounds α θ hα hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hw0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := Real.rpow_nonneg hs0 _
  have hne : 2 * α / 3 + -(Spaces.gam α) ≠ 0 := by
    have hlt : 2 * α / 3 < Spaces.gam α := by
      rw [Spaces.gam]
      nlinarith
    linarith
  have hsq : (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2
      ≤ C ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3) := by
    have h2 : |CT.DthIterAng i (Spaces.Gam α) θ| ≤ |C * Spaces.Gam α θ| := by
      rw [abs_of_nonneg (mul_nonneg hC hG.1)]
      exact hbound θ hθ
    have h1 : (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2 ≤ (C * Spaces.Gam α θ) ^ 2 := by
      calc (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2
          = |CT.DthIterAng i (Spaces.Gam α) θ| ^ 2 := by rw [sq_abs]
        _ ≤ |C * Spaces.Gam α θ| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
        _ = (C * Spaces.Gam α θ) ^ 2 := by rw [sq_abs]
    calc (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2 ≤ (C * Spaces.Gam α θ) ^ 2 := h1
      _ = C ^ 2 * (Spaces.Gam α θ) ^ 2 := by ring
      _ ≤ C ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3) :=
          mul_le_mul_of_nonneg_left (Gam_sq_le_sin_two α hα θ hθ) (sq_nonneg C)
  calc (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
      ≤ (C ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) :=
        mul_le_mul_of_nonneg_right hsq hw0
    _ = C ^ 2 * ((Real.sin (2 * θ)) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) :=
        by ring
    _ = C ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 + -(Spaces.gam α)) := by
        rw [Real.rpow_add' hs0 hne]
    _ = C ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Spaces.gam α) := by ring_nf

/-- The `η`-integrand `(D_θ^i Γ)² sin(2θ)^{-η}` is dominated pointwise by
`C_i² sin(2θ)^{-η}` on `Iθ`. -/
lemma dthIterAng_sq_mul_le_eta {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C) {i : ℕ}
    (hbound : ∀ θ ∈ Spaces.Iθ, |CT.DthIterAng i (Spaces.Gam α) θ| ≤ C * Spaces.Gam α θ) :
    ∀ θ ∈ Spaces.Iθ,
      (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
        ≤ C ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
  intro θ hθ
  have hG := Spaces.Gam_bounds α θ hα hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hsq : (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2 ≤ C ^ 2 := by
    have h2 : |CT.DthIterAng i (Spaces.Gam α) θ| ≤ |C * Spaces.Gam α θ| := by
      rw [abs_of_nonneg (mul_nonneg hC hG.1)]
      exact hbound θ hθ
    have h1 : (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2 ≤ (C * Spaces.Gam α θ) ^ 2 := by
      calc (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2
          = |CT.DthIterAng i (Spaces.Gam α) θ| ^ 2 := by rw [sq_abs]
        _ ≤ |C * Spaces.Gam α θ| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
        _ = (C * Spaces.Gam α θ) ^ 2 := by rw [sq_abs]
    calc (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2 ≤ (C * Spaces.Gam α θ) ^ 2 := h1
      _ = C ^ 2 * (Spaces.Gam α θ) ^ 2 := by ring
      _ ≤ C ^ 2 * 1 ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg C)
          nlinarith [hG.1, hG.2]
      _ = C ^ 2 := by ring
  exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hs0 _)

/-- The `γ`-weighted square of `D_θ^i Γ` is integrable on `Iθ`. -/
lemma dthIterAng_sq_integrable_gam (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (i : ℕ) :
    IntegrableOn (fun θ => (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) Spaces.Iθ := by
  obtain ⟨C, hC0, hbound⟩ := dthIterAng_le_Gam α hα hα1 i
  set q : ℝ := 1 - 17 * α / 30 with hqdef
  have hq0 : 0 < q := by simp only [hqdef]; linarith
  have hq1 : q < 1 := by simp only [hqdef]; linarith
  obtain ⟨hBint, -⟩ := integral_sin_two_neg_rpow_le q hq0 hq1
  have hmaj : IntegrableOn (fun θ : ℝ => C ^ 2 * (Real.sin (2 * θ)) ^ (-q)) Spaces.Iθ :=
    hBint.const_mul _
  -- measurability: the integrand is continuous on the open interval, which differs from
  -- `Iθ` by the null set `{0, π/2}`
  have hIoo : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Spaces.Iθ := by
    rw [Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc
  have hcont_sin : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
      (Set.Ioo 0 (π / 2)) := by
    refine ContinuousOn.rpow_const ?_ ?_
    · fun_prop
    · intro θ hθ
      have h1 : (0 : ℝ) < 2 * θ := by linarith [hθ.1]
      have h2 : 2 * θ < Real.pi := by linarith [hθ.2, Real.pi_pos]
      exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2))
  have hcont_f : ContinuousOn (fun θ => (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) (Set.Ioo 0 (π / 2)) :=
    (((dthIterAng_continuousOn i α hα).mono Set.Ioo_subset_Icc_self).pow 2).mul hcont_sin
  have hmeas : AEStronglyMeasurable (fun θ => (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) (volume.restrict Spaces.Iθ) := by
    rw [← MeasureTheory.Measure.restrict_congr_set hIoo]
    exact hcont_f.aestronglyMeasurable measurableSet_Ioo
  have hpoint := dthIterAng_sq_mul_le_gam hα hα1 hC0 hbound
  have hexp : 2 * α / 3 - Spaces.gam α = -q := by simp only [hqdef, Spaces.gam]; ring
  refine hmaj.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _))]
  have h := hpoint θ hθ
  rw [hexp] at h
  exact h

/-- The `η`-weighted square of `D_θ^i Γ` is integrable on `Iθ`. -/
lemma dthIterAng_sq_integrable_eta (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (i : ℕ) :
    IntegrableOn (fun θ => (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.eta)) Spaces.Iθ := by
  obtain ⟨C, hC0, hbound⟩ := dthIterAng_le_Gam α hα hα1 i
  obtain ⟨hBint, -⟩ := integral_sin_two_neg_rpow_le Spaces.eta Spaces.eta_pos Spaces.eta_lt_one
  have hmaj : IntegrableOn (fun θ : ℝ => C ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      Spaces.Iθ := hBint.const_mul _
  have hIoo : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Spaces.Iθ := by
    rw [Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc
  have hcont_sin : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (Set.Ioo 0 (π / 2)) := by
    refine ContinuousOn.rpow_const ?_ ?_
    · fun_prop
    · intro θ hθ
      have h1 : (0 : ℝ) < 2 * θ := by linarith [hθ.1]
      have h2 : 2 * θ < Real.pi := by linarith [hθ.2, Real.pi_pos]
      exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2))
  have hcont_f : ContinuousOn (fun θ => (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.eta)) (Set.Ioo 0 (π / 2)) :=
    (((dthIterAng_continuousOn i α hα).mono Set.Ioo_subset_Icc_self).pow 2).mul hcont_sin
  have hmeas : AEStronglyMeasurable (fun θ => (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.eta)) (volume.restrict Spaces.Iθ) := by
    rw [← MeasureTheory.Measure.restrict_congr_set hIoo]
    exact hcont_f.aestronglyMeasurable measurableSet_Ioo
  have hpoint := dthIterAng_sq_mul_le_eta hα hC0 hbound
  refine hmaj.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _))]
  exact hpoint θ hθ

theorem dthIterAng_sq_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∀ i : ℕ, MeasureTheory.IntegrableOn (fun θ => (Work.Coercivity.CT.DthIterAng i (Work.Spaces.Gam α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ)
    ∧ (∀ i : ℕ, MeasureTheory.IntegrableOn (fun θ => (Work.Coercivity.CT.DthIterAng i (Work.Spaces.Gam α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ) :=
  ⟨fun i => dthIterAng_sq_integrable_gam α hα hα1 i,
   fun i => dthIterAng_sq_integrable_eta α hα hα1 i⟩

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Construction.H6N_GammaTerm_Lop_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter

namespace Work.Construction

set_option autoImplicit false

set_option maxHeartbeats 1000000

/-! ## Two general tools -/

/-- The derivative of a monomial sum, in shifted form. -/
theorem deriv_mono_succ (k : ℕ) (a : ℕ → ℝ) (x : ℝ) :
    deriv (fun y : ℝ => ∑ j ∈ Finset.range (k+1), a j * y ^ j) x
      = ∑ j ∈ Finset.range k, ((j : ℝ) + 1) * a (j+1) * x ^ j := by
  have hfun : (fun y : ℝ => ∑ j ∈ Finset.range (k+1), a j * y ^ j)
      = fun y : ℝ => a 0 + ∑ j ∈ Finset.range k, a (j+1) * y ^ (j+1) := by
    funext y
    rw [Finset.sum_range_succ']
    ring
  rw [hfun, deriv_const_add (a 0)]
  rw [show (fun y : ℝ => ∑ j ∈ Finset.range k, a (j+1) * y ^ (j+1))
      = (∑ j ∈ Finset.range k, fun y : ℝ => a (j+1) * y ^ (j+1)) from by
    funext y; rw [Finset.sum_apply]]
  rw [deriv_sum (fun j hj => by fun_prop)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [((hasDerivAt_pow (j+1) x).const_mul (a (j+1))).deriv, Nat.add_sub_cancel]
  push_cast
  ring

/-- A monomial sum in the variable `r ∈ [0,1]` is bounded by the sum of the absolute
values of its coefficients. -/
theorem abs_sum_mul_pow_le (n : ℕ) (r : ℝ) (b : ℕ → ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |∑ k ∈ Finset.range n, b k * r ^ k| ≤ ∑ k ∈ Finset.range n, |b k| := by
  calc |∑ k ∈ Finset.range n, b k * r ^ k| ≤ ∑ k ∈ Finset.range n, |b k * r ^ k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ Finset.range n, |b k| * r ^ k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [abs_mul, abs_of_nonneg (pow_nonneg hr0 k)]
    _ ≤ ∑ k ∈ Finset.range n, |b k| := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_of_le_one_right (abs_nonneg (b k)) (pow_le_one₀ hr0 hr1)

/-! ## The coefficient tables -/

/-- The `x`-coefficients of the powers of `α/3` in `A₄`:
`A₄ = ∑ k (α/3)^k ∑ j ac4 k j x^j`. -/
def ac4 : ℕ → ℕ → ℝ
  | 0, 0 => 0 | 0, 1 => 768 | 0, 2 => -11520 | 0, 3 => 38400 | 0, 4 => -46080 | 0, 5 => 18432
  | 1, 0 => 0 | 1, 1 => 3840 | 1, 2 => -44160 | 1, 3 => 132480 | 1, 4 => -149760 | 1, 5 => 57600
  | 2, 0 => 0 | 2, 1 => 7680 | 2, 2 => -63360 | 2, 3 => 162240 | 2, 4 => -167040 | 2, 5 => 60480
  | 3, 0 => 0 | 3, 1 => 7680 | 3, 2 => -42240 | 3, 3 => 86400 | 3, 4 => -77760 | 3, 5 => 25920
  | 4, 0 => -512 | 4, 1 => 3840 | 4, 2 => -11520 | 4, 3 => 17280 | 4, 4 => -12960 | 4, 5 => 3888
  | _, _ => 0

/-- The `x`-coefficients of the powers of `α/3` in `D₄ = ∂ₓA₄`:
`D₄ = ∑ k (α/3)^k ∑ j dq4 k j x^j`. -/
def dq4 : ℕ → ℕ → ℝ
  | 0, 0 => 768 | 0, 1 => -23040 | 0, 2 => 115200 | 0, 3 => -184320 | 0, 4 => 92160
  | 1, 0 => 3840 | 1, 1 => -88320 | 1, 2 => 397440 | 1, 3 => -599040 | 1, 4 => 288000
  | 2, 0 => 7680 | 2, 1 => -126720 | 2, 2 => 486720 | 2, 3 => -668160 | 2, 4 => 302400
  | 3, 0 => 7680 | 3, 1 => -84480 | 3, 2 => 259200 | 3, 3 => -311040 | 3, 4 => 129600
  | 4, 0 => 3840 | 4, 1 => -23040 | 4, 2 => 51840 | 4, 3 => -51840 | 4, 4 => 19440
  | _, _ => 0

/-- The `x`-coefficients of the powers of `α/3` in `A₅`:
`A₅ = ∑ k (α/3)^k ∑ j cc5 k j x^j`. -/
def cc5 : ℕ → ℕ → ℝ
  | 0, 0 => 0 | 0, 1 => -3072 | 0, 2 => 95232 | 0, 3 => -552960 | 0, 4 => 1198080
  | 0, 5 => -1105920 | 0, 6 => 368640
  | 1, 0 => 0 | 1, 1 => -18432 | 1, 2 => 419328 | 1, 3 => -2165760 | 1, 4 => 4400640
  | 1, 5 => -3898368 | 1, 6 => 1262592
  | 2, 0 => 0 | 2, 1 => -46080 | 2, 2 => 737280 | 2, 3 => -3248640 | 2, 4 => 6013440
  | 2, 5 => -5011200 | 2, 6 => 1555200
  | 3, 0 => 0 | 3, 1 => -61440 | 3, 2 => 668160 | 3, 3 => -2403840 | 3, 4 => 3922560
  | 3, 5 => -3006720 | 3, 6 => 881280
  | 4, 0 => 0 | 4, 1 => -46080 | 4, 2 => 322560 | 4, 3 => -898560 | 4, 4 => 1244160
  | 4, 5 => -855360 | 4, 6 => 233280
  | 5, 0 => 2048 | 5, 1 => -18432 | 5, 2 => 69120 | 5, 3 => -138240 | 5, 4 => 155520
  | 5, 5 => -93312 | 5, 6 => 23328
  | _, _ => 0

/-- The mono coefficients of `A₄`: `A₄ = ∑ j a4 j α · x^j`. -/
def a4 (j : ℕ) (α : ℝ) : ℝ := ∑ k ∈ Finset.range 5, ac4 k j * (α/3)^k

/-- The explicit polynomial `D₄ = ∂ₓA₄`. -/
def D4p (x α : ℝ) : ℝ := ∑ k ∈ Finset.range 5, (∑ j ∈ Finset.range 5, dq4 k j * x^j) * (α/3)^k

/-- The mono coefficients of `A₅`: `A₅ = ∑ j c5 j α · x^j`. -/
def c5 (j : ℕ) (α : ℝ) : ℝ := ∑ k ∈ Finset.range 6, cc5 k j * (α/3)^k

/-- The fifth angular polynomial: the result of one more application of the operator
`-4x(1-x)∂ₓ + (α/3)(6x-4)` to `A₄`. -/
def Aang5 (x α : ℝ) : ℝ :=
  -4 * x * (1 - x) * deriv (fun y : ℝ => Aang 4 y α) x + (α/3) * (6 * x - 4) * Aang 4 x α

/-- The sixth angular polynomial. -/
def Aang6 (x α : ℝ) : ℝ :=
  -4 * x * (1 - x) * deriv (fun y : ℝ => Aang5 y α) x + (α/3) * (6 * x - 4) * Aang5 x α

/-! ## The explicit derivative of `A₄` -/

theorem deriv_Aang_four (x α : ℝ) : deriv (fun y : ℝ => Aang 4 y α) x = D4p x α := by
  have h : (fun y : ℝ => Aang 4 y α) = fun y : ℝ =>
      a4 0 α + a4 1 α * y + a4 2 α * y^2 + a4 3 α * y^3 + a4 4 α * y^4 + a4 5 α * y^5 := by
    funext y
    simp only [Aang_four]
    unfold a4
    norm_num [ac4, Finset.sum_range_succ]
    ring
  rw [h, deriv_mono5]
  unfold D4p a4
  norm_num [dq4, ac4, Finset.sum_range_succ]
  ring

/-! ## The explicit expansion of `A₅` -/

theorem Aang5_eq_mono (x α : ℝ) : Aang5 x α = ∑ j ∈ Finset.range 7, c5 j α * x ^ j := by
  rw [Aang5, deriv_Aang_four]
  unfold D4p c5
  norm_num [cc5, dq4, Aang_four, Finset.sum_range_succ]
  ring

theorem differentiable_Aang5 (α : ℝ) : Differentiable ℝ (fun y : ℝ => Aang5 y α) := by
  rw [show (fun y : ℝ => Aang5 y α) = fun y : ℝ => ∑ j ∈ Finset.range 7, c5 j α * y ^ j from
    funext (fun y => Aang5_eq_mono y α)]
  fun_prop

/-! ## The pointwise bounds -/

/-- `|D₄(x,α)| ≤ 4325808` on `[0,1] × (0,1]`. -/
theorem abs_D4p_le (x α : ℝ) (hx : x ∈ Set.Icc 0 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    |D4p x α| ≤ 4325808 := by
  have hx0 := hx.1
  have hx1 := hx.2
  have hβ0 : 0 ≤ α / 3 := by linarith
  have hβ1 : α / 3 ≤ 1 := by linarith
  have h2 : |∑ k ∈ Finset.range 5, (∑ j ∈ Finset.range 5, dq4 k j * x ^ j) * (α/3)^k|
      ≤ 4325808 := by
    calc |∑ k ∈ Finset.range 5, (∑ j ∈ Finset.range 5, dq4 k j * x ^ j) * (α/3)^k|
        ≤ ∑ k ∈ Finset.range 5, |(∑ j ∈ Finset.range 5, dq4 k j * x ^ j) * (α/3)^k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ Finset.range 5, |(∑ j ∈ Finset.range 5, dq4 k j * x ^ j)| * (α/3)^k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
      _ ≤ ∑ k ∈ Finset.range 5, (∑ j ∈ Finset.range 5, |dq4 k j|) * 1 := by
          apply Finset.sum_le_sum
          intro k hk
          have hk1 : |∑ j ∈ Finset.range 5, dq4 k j * x ^ j| ≤ ∑ j ∈ Finset.range 5, |dq4 k j| :=
            abs_sum_mul_pow_le 5 x (dq4 k) hx0 hx1
          have hk2 : (α/3)^k ≤ 1 := pow_le_one₀ hβ0 hβ1
          exact mul_le_mul hk1 hk2 (pow_nonneg hβ0 k) (by positivity)
      _ = 4325808 := by norm_num [Finset.sum_range_succ, dq4]
  rw [D4p]
  exact h2

/-- `|A₅(x,α)| ≤ 24325808·(α + 4x(1-x))` on `[0,1] × (0,1]`. -/
theorem Aang5_bound (x α : ℝ) (hx : x ∈ Set.Icc 0 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    |Aang5 x α| ≤ 24325808 * (α + 4 * x * (1 - x)) := by
  have hx0 := hx.1
  have hx1 := hx.2
  have h4 : 0 ≤ 4 * x * (1 - x) := by nlinarith
  have hβ0 : 0 ≤ α / 3 := by linarith
  have hD4 : |D4p x α| ≤ 4325808 := abs_D4p_le x α hx hα hα1
  have hA : |Aang 4 x α| ≤ 10 ^ 7 * (α + 4 * x * (1 - x)) := glop_Aang_bound_four x α hx hα hα1
  have hx4 : |6 * x - 4| ≤ 4 := by
    rw [abs_le]; constructor <;> linarith
  rw [Aang5, deriv_Aang_four]
  have hsplit : |(-4) * x * (1 - x) * D4p x α + (α/3) * (6 * x - 4) * Aang 4 x α|
      ≤ 4 * x * (1 - x) * 4325808 + (α/3) * 4 * (10^7 * (α + 4 * x * (1 - x))) := by
    have h1 : |(-4) * x * (1 - x) * D4p x α| = 4 * x * (1 - x) * |D4p x α| := by
      rw [abs_mul, abs_of_nonpos (by nlinarith : (-4) * x * (1 - x) ≤ 0)]
      ring
    have h2 : |(α/3) * (6 * x - 4) * Aang 4 x α| = (α/3) * |6 * x - 4| * |Aang 4 x α| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hβ0]
    have h3 : 4 * x * (1 - x) * |D4p x α| ≤ 4 * x * (1 - x) * 4325808 :=
      mul_le_mul_of_nonneg_left hD4 h4
    have h5 : (α/3) * |6 * x - 4| * |Aang 4 x α|
        ≤ (α/3) * 4 * (10^7 * (α + 4 * x * (1 - x))) := by
      have h6 : |6*x - 4| * |Aang 4 x α| ≤ 4 * (10^7 * (α + 4*x*(1-x))) :=
        mul_le_mul hx4 hA (abs_nonneg _) (by norm_num)
      have := mul_le_mul_of_nonneg_left h6 hβ0
      linarith [this]
    calc |(-4) * x * (1 - x) * D4p x α + (α/3) * (6 * x - 4) * Aang 4 x α|
        ≤ |(-4) * x * (1 - x) * D4p x α| + |(α/3) * (6 * x - 4) * Aang 4 x α| := abs_add_le _ _
      _ = 4 * x * (1 - x) * |D4p x α| + (α/3) * |6 * x - 4| * |Aang 4 x α| := by rw [h1, h2]
      _ ≤ 4 * x * (1 - x) * 4325808 + (α/3) * 4 * (10^7 * (α + 4 * x * (1 - x))) :=
          add_le_add h3 h5
  have hfin : 4 * x * (1 - x) * 4325808 + (α/3) * 4 * (10^7 * (α + 4 * x * (1 - x)))
      ≤ 24325808 * (α + 4 * x * (1 - x)) := by
    nlinarith [h4, hα, hα1, sq_nonneg (1 - x)]
  linarith [hsplit, hfin]

/-- `|∂ₓA₅(x,α)| ≤ 196578816` on `[0,1] × (0,1]`. -/
theorem deriv_Aang5_bound (x α : ℝ) (hx : x ∈ Set.Icc 0 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    |deriv (fun y : ℝ => Aang5 y α) x| ≤ 196578816 := by
  have hx0 := hx.1
  have hx1 := hx.2
  have hβ0 : 0 ≤ α / 3 := by linarith
  have hβ1 : α / 3 ≤ 1 := by linarith
  have hfun : (fun y : ℝ => Aang5 y α) = fun y : ℝ => ∑ j ∈ Finset.range (6+1), c5 j α * y ^ j :=
    funext (fun y => Aang5_eq_mono y α)
  rw [hfun, deriv_mono_succ 6 (fun j => c5 j α) x]
  calc |∑ j ∈ Finset.range 6, ((j:ℝ) + 1) * c5 (j + 1) α * x ^ j|
      ≤ ∑ j ∈ Finset.range 6, |((j:ℝ) + 1) * c5 (j + 1) α| :=
        abs_sum_mul_pow_le 6 x (fun j => ((j:ℝ) + 1) * c5 (j+1) α) hx0 hx1
    _ = ∑ j ∈ Finset.range 6, ((j:ℝ) + 1) * |c5 (j + 1) α| := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (j:ℝ) + 1)]
    _ ≤ ∑ j ∈ Finset.range 6, ((j:ℝ) + 1) * (∑ k ∈ Finset.range 6, |cc5 k (j+1)|) := by
        apply Finset.sum_le_sum
        intro j hj
        have hc : |c5 (j+1) α| ≤ ∑ k ∈ Finset.range 6, |cc5 k (j+1)| := by
          rw [c5]
          exact abs_sum_mul_pow_le 6 (α/3) (fun k => cc5 k (j+1)) hβ0 hβ1
        exact mul_le_mul_of_nonneg_left hc (by positivity)
    _ = 196578816 := by norm_num [Finset.sum_range_succ, cc5]

/-- `|A₆(x,α)| ≤ 245230432·(α + 4x(1-x))` on `[0,1] × (0,1]`. -/
theorem Aang6_bound (x α : ℝ) (hx : x ∈ Set.Icc 0 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    |Aang6 x α| ≤ 245230432 * (α + 4 * x * (1 - x)) := by
  have hx0 := hx.1
  have hx1 := hx.2
  have h4 : 0 ≤ 4 * x * (1 - x) := by nlinarith
  have hβ0 : 0 ≤ α / 3 := by linarith
  have hd5 : |deriv (fun y : ℝ => Aang5 y α) x| ≤ 196578816 := deriv_Aang5_bound x α hx hα hα1
  have hA : |Aang5 x α| ≤ 24325808 * (α + 4 * x * (1 - x)) := Aang5_bound x α hx hα hα1
  have hx4 : |6 * x - 4| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  rw [Aang6]
  have hsplit : |(-4) * x * (1 - x) * deriv (fun y : ℝ => Aang5 y α) x
        + (α/3) * (6 * x - 4) * Aang5 x α|
      ≤ 4 * x * (1 - x) * 196578816 + (α/3) * 4 * (24325808 * (α + 4 * x * (1 - x))) := by
    have h1 : |(-4) * x * (1 - x) * deriv (fun y : ℝ => Aang5 y α) x|
        = 4 * x * (1 - x) * |deriv (fun y : ℝ => Aang5 y α) x| := by
      rw [abs_mul, abs_of_nonpos (by nlinarith : (-4) * x * (1 - x) ≤ 0)]
      ring
    have h2 : |(α/3) * (6 * x - 4) * Aang5 x α| = (α/3) * |6 * x - 4| * |Aang5 x α| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hβ0]
    have h3 : 4 * x * (1 - x) * |deriv (fun y : ℝ => Aang5 y α) x|
        ≤ 4 * x * (1 - x) * 196578816 :=
      mul_le_mul_of_nonneg_left hd5 h4
    have h5 : (α/3) * |6 * x - 4| * |Aang5 x α|
        ≤ (α/3) * 4 * (24325808 * (α + 4 * x * (1 - x))) := by
      have h6 : |6*x - 4| * |Aang5 x α| ≤ 4 * (24325808 * (α + 4*x*(1-x))) :=
        mul_le_mul hx4 hA (abs_nonneg _) (by norm_num)
      have := mul_le_mul_of_nonneg_left h6 hβ0
      linarith [this]
    calc |(-4) * x * (1 - x) * deriv (fun y : ℝ => Aang5 y α) x
          + (α/3) * (6 * x - 4) * Aang5 x α|
        ≤ |(-4) * x * (1 - x) * deriv (fun y : ℝ => Aang5 y α) x|
          + |(α/3) * (6 * x - 4) * Aang5 x α| := abs_add_le _ _
      _ = 4 * x * (1 - x) * |deriv (fun y : ℝ => Aang5 y α) x|
          + (α/3) * |6 * x - 4| * |Aang5 x α| := by rw [h1, h2]
      _ ≤ 4 * x * (1 - x) * 196578816 + (α/3) * 4 * (24325808 * (α + 4 * x * (1 - x))) :=
          add_le_add h3 h5
  have hfin : 4 * x * (1 - x) * 196578816 + (α/3) * 4 * (24325808 * (α + 4 * x * (1 - x)))
      ≤ 245230432 * (α + 4 * x * (1 - x)) := by
    nlinarith [h4, hα, hα1]
  linarith [hsplit, hfin]

/-! ## The fifth and sixth iterates -/

theorem Lop_iter_psiA5 (α : ℝ) (hα : 0 < α) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.Lop^[5] (psiA α)) θ = Work.Spaces.Gam α θ * Aang5 (Real.cos θ ^ 2) α := by
  intro θ hθ
  have h4 : (Work.Spaces.Lop^[4] (psiA α))
      =ᶠ[𝓝 θ] fun y => Work.Spaces.Gam α y * Aang 4 (Real.cos y ^ 2) α := by
    filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
    exact glop_Lop_iter_psiA α hα 4 le_rfl y hy
  rw [Function.iterate_succ_apply']
  rw [show Work.Spaces.Lop (Work.Spaces.Lop^[4] (psiA α)) θ
      = Work.Spaces.Lop (fun y => Work.Spaces.Gam α y * Aang 4 (Real.cos y ^ 2) α) θ from by
    show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[4] (psiA α)) θ
        = Real.sin (2 * θ) * deriv (fun y => Work.Spaces.Gam α y * Aang 4 (Real.cos y ^ 2) α) θ
    rw [h4.deriv_eq]]
  rw [glop_step α hα (fun y : ℝ => Aang 4 y α) (differentiable_Aang 4 le_rfl α) θ hθ]
  simp only [Aang5]

theorem Lop_iter_psiA6 (α : ℝ) (hα : 0 < α) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.Lop^[6] (psiA α)) θ = Work.Spaces.Gam α θ * Aang6 (Real.cos θ ^ 2) α := by
  intro θ hθ
  have h5 : (Work.Spaces.Lop^[5] (psiA α))
      =ᶠ[𝓝 θ] fun y => Work.Spaces.Gam α y * Aang5 (Real.cos y ^ 2) α := by
    filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
    exact Lop_iter_psiA5 α hα y hy
  rw [Function.iterate_succ_apply']
  rw [show Work.Spaces.Lop (Work.Spaces.Lop^[5] (psiA α)) θ
      = Work.Spaces.Lop (fun y => Work.Spaces.Gam α y * Aang5 (Real.cos y ^ 2) α) θ from by
    show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[5] (psiA α)) θ
        = Real.sin (2 * θ) * deriv (fun y => Work.Spaces.Gam α y * Aang5 (Real.cos y ^ 2) α) θ
    rw [h5.deriv_eq]]
  rw [glop_step α hα (fun y : ℝ => Aang5 y α) (differentiable_Aang5 α) θ hθ]
  simp only [Aang6]

/-! ## The target theorem -/

theorem H6N_GammaTerm_Lop_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ i : ℕ, 1 ≤ i → i ≤ 6 →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(Work.Spaces.Lop^[i] (Work.Construction.psiA α)) θ|
          ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := by
  refine ⟨10 ^ 9, by norm_num, ?_⟩
  intro α hα hα1 i hi1 hi6 θ hθ
  have hGam0 : 0 ≤ Work.Spaces.Gam α θ :=
    (Work.Spaces.Gam_bounds α θ hα (Set.Ioo_subset_Icc_self hθ)).1
  have hxc : Real.cos θ ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨sq_nonneg _, by linarith [Real.cos_sq_le_one θ]⟩
  have hsin2 : 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2) = Real.sin (2 * θ) ^ 2 := by
    rw [Real.sin_two_mul]; ring_nf; rw [Real.sin_sq]; ring
  have step : ∀ (j : ℕ) (a : ℝ → ℝ)
      (hh : (Work.Spaces.Lop^[j] (psiA α)) θ = Work.Spaces.Gam α θ * a (Real.cos θ ^ 2))
      (C : ℝ) (hC : |a (Real.cos θ ^ 2)| ≤ C * (α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2)))
      (hC9 : C ≤ 10 ^ 9),
      |(Work.Spaces.Lop^[j] (psiA α)) θ|
        ≤ 10 ^ 9 * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := by
    intro j a hh C hC hC9
    rw [hh]
    calc |Work.Spaces.Gam α θ * a (Real.cos θ ^ 2)|
        = Work.Spaces.Gam α θ * |a (Real.cos θ ^ 2)| := by
          rw [abs_mul, abs_of_nonneg hGam0]
      _ ≤ Work.Spaces.Gam α θ * (C * (α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2))) :=
          mul_le_mul_of_nonneg_left hC hGam0
      _ = C * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := by rw [hsin2]; ring
      _ ≤ 10 ^ 9 * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := by
          have hpos : 0 ≤ Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) :=
            mul_nonneg hGam0 (by nlinarith [sq_nonneg (Real.sin (2 * θ)), hα])
          nlinarith [hpos, hC9]
  interval_cases i
  · exact step 1 (fun x => Aang 1 x α) (glop_Lop_iter_psiA α hα 1 (by norm_num) θ hθ) (10^7)
      (glop_Aang_bound_one _ _ hxc hα hα1) (by norm_num)
  · exact step 2 (fun x => Aang 2 x α) (glop_Lop_iter_psiA α hα 2 (by norm_num) θ hθ) (10^7)
      (glop_Aang_bound_two _ _ hxc hα hα1) (by norm_num)
  · exact step 3 (fun x => Aang 3 x α) (glop_Lop_iter_psiA α hα 3 (by norm_num) θ hθ) (10^7)
      (glop_Aang_bound_three _ _ hxc hα hα1) (by norm_num)
  · exact step 4 (fun x => Aang 4 x α) (glop_Lop_iter_psiA α hα 4 le_rfl θ hθ) (10^7)
      (glop_Aang_bound_four _ _ hxc hα hα1) (by norm_num)
  · exact step 5 (fun x => Aang5 x α) (Lop_iter_psiA5 α hα θ hθ) 24325808
      (Aang5_bound _ _ hxc hα hα1) (by norm_num)
  · exact step 6 (fun x => Aang6 x α) (Lop_iter_psiA6 α hα θ hθ) 245230432
      (Aang6_bound _ _ hxc hα hα1) (by norm_num)

end Work.Construction
end
end
-- ===== merged: Submission.Work.Elliptic.DivSinIBPWeight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-! ## The pointwise derivative of the primitive `DivSinWP`

`DivSinWP γ h θ = -(1/2) sin(2θ)^{3-γ} cos(2θ) (u'(θ))²` with `u = SinQ h`, so that

`d/dθ DivSinWP γ h θ = WDfun γ h θ = W2 θ - (3-γ) W1 θ - W3 θ`

on `(0, π/2)`.  This is the pointwise identity underlying the weighted integration by parts. -/


/-! ## The primitive vanishes at both endpoints -/



/-! ## Integrability of the integrands

Every integrand is bounded on `Iθ = [0, π/2]` by a constant multiple of `C²`, where `C` is
the constant of `SliceBdd_ae_bounds`.  On `Iθ` the powers `sin(2θ)^p` with `p ≥ 0` are at
most `1`, `cos(2θ)² ≤ 1`, `|u'| ≤ C` and — crucially, so that the `u''` factor causes no
trouble — `|sin(2θ) u''| ≤ C`. -/







end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.DivSinIdentityB =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false



private lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa [sub_eq_add_neg] using abs_add_le a (-b)





end Work.Elliptic
end
end
-- ===== merged: Submission.Work.EllipticEst.Blocks.slice_d_expansion =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Blocks


end Work.EllipticEst.Blocks
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.TVRed.tvHypBundle =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

open scoped Real Topology
open MeasureTheory Set Filter

theorem tvHypBundle {f : ℝ → ℝ} {ψ : ℝ → ℝ} {C F₀ F₁ L : ℝ}
    (hψ : Work.EllipticEst.Core.i0Aux.IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hlim0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F₀))
    (hlim1 : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F₁))
    (hP : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hE : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    ContDiffOn ℝ 2 (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)
        (Set.Ioo 0 (Real.pi / 2)) ∧
    Filter.Tendsto (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) ∧
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv (deriv (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)) θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  obtain ⟨hS0, hS1, hS2⟩ := tvh_surr_sq_integrable hψ hL
  have hs : ContDiff ℝ 2 (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) :=
    surr_smooth hψ (ne_of_gt hL)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hf.sub hs.contDiffOn
  · simpa only [sub_self] using hlim0.sub (surr_tendsto_left (F₀ := F₀) (F₁ := F₁) hψ hL hLp)
  · simpa only [sub_self] using hlim1.sub (surr_tendsto_right (F₀ := F₀) (F₁ := F₁) hψ hL hLp)
  · exact tvh_integrableOn_sq_sub hP hS0 (tvh_aesm_of_contDiffOn hf)
      hs.continuous.aestronglyMeasurable
  · -- first derivative
    have hdf : AEStronglyMeasurable (deriv f) (volume.restrict Work.Spaces.Iθ) :=
      tvh_aesm_of_contDiffOn (hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num))
    have hds : AEStronglyMeasurable
        (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L))
        (volume.restrict Work.Spaces.Iθ) :=
      (hs.continuous_deriv (by norm_num)).aestronglyMeasurable
    have hbase := tvh_integrableOn_sq_sub hA hS1 hdf hds
    refine hbase.congr ?_
    have hae : deriv (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => deriv f θ
          - deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) :=
      tvh_ae_eq_of_forall_Ioo (fun θ hθ => tvh_deriv_sub hf hs θ hθ)
    filter_upwards [hae] with θ hθ
    rw [hθ]
  · -- second derivative
    have hdf2 : AEStronglyMeasurable (deriv (deriv f)) (volume.restrict Work.Spaces.Iθ) :=
      tvh_aesm_of_contDiffOn
        ((hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).deriv_of_isOpen
          isOpen_Ioo (m := 0) (by norm_num))
    have hds2 : AEStronglyMeasurable
        (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)))
        (volume.restrict Work.Spaces.Iθ) := by
      have h1 : ContDiff ℝ 1 (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) := by
        simpa using hs.deriv' (n := 1)
      exact (h1.continuous_deriv (by norm_num)).aestronglyMeasurable
    have hbase := tvh_integrableOn_sq_sub hE hS2 hdf2 hds2
    refine hbase.congr ?_
    have hae : deriv (deriv (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ))
        =ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => deriv (deriv f) θ
          - deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) :=
      tvh_ae_eq_of_forall_Ioo (fun θ hθ => tvh_deriv2_sub hf hs θ hθ)
    filter_upwards [hae] with θ hθ
    rw [hθ]

end Work.EllipticEst.Core.i0Aux.TVRed
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.TVRed.tvh_surr_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

variable {ψ : ℝ → ℝ} {C F₀ F₁ L : ℝ}

/-! ## Continuity of the bump's derivatives and of the surrogate's derivatives -/

/-- A bump is `C²`, so its first derivative is continuous. -/
lemma tvh_continuous_deriv (hψ : IsBump ψ C) : Continuous (deriv ψ) :=
  hψ.contDiff.continuous_deriv (by norm_num)

/-- A bump is `C²`, so its second derivative is continuous. -/
lemma tvh_continuous_deriv2 (hψ : IsBump ψ C) : Continuous (deriv (deriv ψ)) :=
  (hψ.contDiff.deriv' (n := 1)).continuous_deriv (by norm_num)

/-- The surrogate is continuous. -/
lemma tvh_continuous_surr (hψ : IsBump ψ C) (hL : L ≠ 0) :
    Continuous (surrFun ψ F₀ F₁ L) :=
  (surr_smooth hψ hL).continuous

/-- The first derivative of the surrogate is continuous: by the chain-rule identity
`deriv_surr_eq` it is an explicit sum of compositions of `deriv ψ` with affine maps. -/
lemma tvh_continuous_deriv_surr (hψ : IsBump ψ C) (hL : L ≠ 0) :
    Continuous (deriv (surrFun ψ F₀ F₁ L)) := by
  have h1 : Continuous fun θ : ℝ => deriv ψ (θ / L) :=
    (tvh_continuous_deriv hψ).comp (by continuity)
  have h2 : Continuous fun θ : ℝ => deriv ψ ((Real.pi / 2 - θ) / L) :=
    (tvh_continuous_deriv hψ).comp (by continuity)
  rw [show deriv (surrFun ψ F₀ F₁ L) = fun θ : ℝ =>
      F₀ * (deriv ψ (θ / L) * (1 / L))
        + F₁ * (deriv ψ ((Real.pi / 2 - θ) / L) * (-(1 / L)))
      from funext (deriv_surr_eq hψ hL)]
  exact ((h1.mul_const (1 / L)).const_mul F₀).add ((h2.mul_const (-(1 / L))).const_mul F₁)

/-- The second derivative of the surrogate is continuous, from `deriv2_surr_eq`. -/
lemma tvh_continuous_deriv2_surr (hψ : IsBump ψ C) (hL : L ≠ 0) :
    Continuous (deriv (deriv (surrFun ψ F₀ F₁ L))) := by
  have h1 : Continuous fun θ : ℝ => deriv (deriv ψ) (θ / L) :=
    (tvh_continuous_deriv2 hψ).comp (by continuity)
  have h2 : Continuous fun θ : ℝ => deriv (deriv ψ) ((Real.pi / 2 - θ) / L) :=
    (tvh_continuous_deriv2 hψ).comp (by continuity)
  rw [show deriv (deriv (surrFun ψ F₀ F₁ L)) = fun θ : ℝ =>
      F₀ * (deriv (deriv ψ) (θ / L) * (1 / L)) * (1 / L)
        + F₁ * (deriv (deriv ψ) ((Real.pi / 2 - θ) / L) * (-(1 / L))) * (-(1 / L))
      from funext (deriv2_surr_eq hψ hL)]
  exact (((h1.mul_const (1 / L)).const_mul F₀).mul_const (1 / L)).add
    (((h2.mul_const (-(1 / L))).const_mul F₁).mul_const (-(1 / L)))

/-! ## The integrability theorem -/

theorem tvh_surr_integrable {ψ : ℝ → ℝ} {C F₀ F₁ L : ℝ}
    (hψ : Work.EllipticEst.Core.i0Aux.IsBump ψ C) (hL : 0 < L) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  have hL0 : L ≠ 0 := ne_of_gt hL
  refine ⟨?_, ?_, ?_⟩
  · -- `(surr)² thEta` is dominated by `(|F₀| + |F₁|)² thEta`
    refine tvh_integrableOn_of_abs_le
      (F := fun θ => (|F₀| + |F₁|) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (tvh_integrableOn_const_mul_thEta _) ?_ ?_
    · exact ((tvh_continuous_surr hψ hL0).aestronglyMeasurable.pow 2).mul tvh_aesm_thEta
    · intro θ hθ
      have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
      have hb : |Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ| ≤ |F₀| + |F₁| :=
        surr_bound hψ θ
      have h2 : (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 ≤ (|F₀| + |F₁|) ^ 2 := by
        have h := pow_le_pow_left₀
          (abs_nonneg (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)) hb 2
        rwa [sq_abs] at h
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hσ)]
      exact mul_le_mul_of_nonneg_right h2 hσ
  · -- `(surr')² thEta` is dominated by `(C (|F₀| + |F₁|) / L)² thEta`
    refine tvh_integrableOn_of_abs_le
      (F := fun θ => (C * (|F₀| + |F₁|) / L) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (tvh_integrableOn_const_mul_thEta _) ?_ ?_
    · exact ((tvh_continuous_deriv_surr hψ hL0).aestronglyMeasurable.pow 2).mul tvh_aesm_thEta
    · intro θ hθ
      have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
      have hb : |deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ|
          ≤ C * (|F₀| + |F₁|) / L :=
        deriv_surr_bound hψ hL θ
      have h2 : (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2
          ≤ (C * (|F₀| + |F₁|) / L) ^ 2 := by
        have h := pow_le_pow_left₀
          (abs_nonneg (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ)) hb 2
        rwa [sq_abs] at h
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hσ)]
      exact mul_le_mul_of_nonneg_right h2 hσ
  · -- `(surr'')² thEta` is dominated by `(C (|F₀| + |F₁|) / L²)² thEta`
    refine tvh_integrableOn_of_abs_le
      (F := fun θ => (C * (|F₀| + |F₁|) / L ^ 2) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (tvh_integrableOn_const_mul_thEta _) ?_ ?_
    · exact ((tvh_continuous_deriv2_surr hψ hL0).aestronglyMeasurable.pow 2).mul tvh_aesm_thEta
    · intro θ hθ
      have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
      have hb : |deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ|
          ≤ C * (|F₀| + |F₁|) / L ^ 2 :=
        deriv2_surr_bound hψ hL θ
      have h2 : (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2
          ≤ (C * (|F₀| + |F₁|) / L ^ 2) ^ 2 := by
        have h := pow_le_pow_left₀
          (abs_nonneg (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ)) hb 2
        rwa [sq_abs] at h
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hσ)]
      exact mul_le_mul_of_nonneg_right h2 hσ

end

end Work.EllipticEst.Core.i0Aux.TVRed
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.endpointValuesCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false


end Work.EllipticEst.Core.i0Aux
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.eFamParsevalDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

local notation "Iθ" => Work.Spaces.Iθ

/-- The `m`-th Gegenbauer mode of `Lzero`, as a (reducible) alias for
`Work.FTS.PhiStar.Gegenbauer.eFam m`. -/
abbrev eM (m : ℕ) : ℝ → ℝ := Work.FTS.PhiStar.Gegenbauer.eFam m

/-- The squared `L²(Iθ, cos θ dθ)`-norm of the `m`-th mode. -/
def eFamD (m : ℕ) : ℝ := ∫ θ in Iθ, eM m θ ^ 2 * Real.cos θ

/-- `eFam_norm_fts`, restated for `eFamD`. -/
theorem eFamD_eq (m : ℕ) :
    eFamD m = ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) :=
  Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts m

theorem eFamD_pos (m : ℕ) : 0 < eFamD m := by
  rw [eFamD_eq]
  positivity

/-- The modes are bounded on `Iθ` (they are `cos θ` times a polynomial in `sin θ`, and
`sin θ` stays in `[-1,1]`). -/
theorem eFam_abs_le (m : ℕ) : ∃ C : ℝ, ∀ θ ∈ Iθ, ‖eM m θ‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.continuousOn)
  refine ⟨C, fun θ hθ => ?_⟩
  have hsin : Real.sin θ ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith [Real.neg_one_le_sin θ], Real.sin_le_one θ⟩
  have h2 := hC (Real.sin θ) hsin
  have h1 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  calc ‖eM m θ‖
      = |Real.cos θ| * |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)| := by
        rw [Real.norm_eq_abs, eM, Work.FTS.PhiStar.Gegenbauer.eFam, abs_mul]
    _ ≤ 1 * C := by
        refine mul_le_mul h1 ?_ (abs_nonneg _) zero_le_one
        rwa [Real.norm_eq_abs] at h2
    _ = C := one_mul C

theorem eFam_memLp (m : ℕ) : MemLp (eM m) 2 Work.FTS.EllipticEst.LevelOneAsm.angMeasure := by
  obtain ⟨C, hC⟩ := eFam_abs_le m
  refine MemLp.of_bound ?_ C ?_
  · exact ((Real.continuous_cos.mul
      (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
        Real.continuous_sin))).aestronglyMeasurable
  · filter_upwards [Work.FTS.EllipticEst.LevelOneAsm.ae_mem_Iθ_angMeasure] with θ hθ
    exact hC θ hθ

/-- The class of the `m`-th mode in `L²(Iθ, cos θ dθ)`. -/
def eFamLp (m : ℕ) : Lp ℝ 2 Work.FTS.EllipticEst.LevelOneAsm.angMeasure := MemLp.toLp (eM m) (eFam_memLp m)

theorem eFamLp_coe (m : ℕ) : (eFamLp m : ℝ → ℝ) =ᵐ[Work.FTS.EllipticEst.LevelOneAsm.angMeasure] eM m :=
  MemLp.coeFn_toLp (eFam_memLp m)

/-- The normalised modes `eFamE m = (√(eFamD m))⁻¹ • eFamLp m`. -/
def eFamE (m : ℕ) : Lp ℝ 2 Work.FTS.EllipticEst.LevelOneAsm.angMeasure := (Real.sqrt (eFamD m))⁻¹ • eFamLp m


/-- The inner product of an `L²`-class with the `m`-th mode class is the weighted integral on
`Iθ`. -/
theorem inner_toLp_eFamLp {f : ℝ → ℝ} (hf : MemLp f 2 Work.FTS.EllipticEst.LevelOneAsm.angMeasure) (m : ℕ) :
    inner ℝ (MemLp.toLp f hf) (eFamLp m) = ∫ θ in Iθ, f θ * eM m θ * Real.cos θ :=
  Work.FTS.EllipticEst.LevelOneAsm.inner_toLp_toLp hf (eFam_memLp m)

theorem inner_toLp_eFamE {f : ℝ → ℝ} (hf : MemLp f 2 Work.FTS.EllipticEst.LevelOneAsm.angMeasure) (m : ℕ) :
    inner ℝ (MemLp.toLp f hf) (eFamE m)
      = (Real.sqrt (eFamD m))⁻¹ * ∫ θ in Iθ, f θ * eM m θ * Real.cos θ := by
  rw [eFamE, inner_smul_right, inner_toLp_eFamLp]

theorem inner_eFamE_toLp {g : ℝ → ℝ} (hg : MemLp g 2 Work.FTS.EllipticEst.LevelOneAsm.angMeasure) (m : ℕ) :
    inner ℝ (eFamE m) (MemLp.toLp g hg)
      = (Real.sqrt (eFamD m))⁻¹ * ∫ θ in Iθ, eM m θ * g θ * Real.cos θ := by
  have hcomm : (∫ θ in Iθ, g θ * eM m θ * Real.cos θ)
      = ∫ θ in Iθ, eM m θ * g θ * Real.cos θ :=
    setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  rw [real_inner_comm, inner_toLp_eFamE, hcomm]

/-- The inner product of the `m`-th mode with an arbitrary `L²`-class is the weighted integral
against that class's representative. -/
theorem inner_eFamLp_any (m : ℕ) (y : Lp ℝ 2 Work.FTS.EllipticEst.LevelOneAsm.angMeasure) :
    inner ℝ (eFamLp m) y = ∫ θ in Iθ, eM m θ * (y : ℝ → ℝ) θ * Real.cos θ := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : (fun a => inner ℝ ((eFamLp m : ℝ → ℝ) a) ((y : ℝ → ℝ) a))
      =ᵐ[Work.FTS.EllipticEst.LevelOneAsm.angMeasure] fun a => eM m a * (y : ℝ → ℝ) a := by
    filter_upwards [eFamLp_coe m] with a ha
    rw [ha, Real.inner_apply]
  rw [integral_congr_ae h1, Work.FTS.EllipticEst.LevelOneAsm.integral_angMeasure]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

/-- **The weighted integral of a mode on `Iθ` equals its interval integral on `(0, π/2)`** (the
two differ only at `θ = 0`, which is a null set); needed to compare `cmode` (interval form) with
the inner product (set-integral form). -/
theorem integral_Iθ_eq_intervalIntegral (f : ℝ → ℝ) :
    (∫ θ in Iθ, f θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le
    (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)).symm

end Work.EllipticEst.ModalSolution
end
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.eFam_pythagoras =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set
open scoped Real BigOperators

namespace Work.EllipticEst.ModalSolution

/-- The truncated mode sum `∑_{m ≤ N} cmode m F z · eFam m θ`, as a function of `θ`. -/
def sumEFam (F : ℝ → ℝ → ℝ) (z : ℝ) (N : ℕ) : ℝ → ℝ :=
  fun θ => ∑ m ∈ Finset.range (N + 1),
    Work.FTS.PhiStar.Series.cmode m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ

/-- The set integral over `Iθ = [0, π/2]` is the interval integral over `0..π/2`. -/
theorem setIntegral_Iθ_eq_intervalIntegral (g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]

attribute [local fun_prop] continuous_eFam

/-- `cmode m F z` times the norm of `eFam m` is the `e_m`-moment of the slice `F z ·`. -/
theorem cmode_mul_norm (F : ℝ → ℝ → ℝ) (z : ℝ) (m : ℕ) :
    Work.FTS.PhiStar.Series.cmode m F z
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
  have hnum : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ :=
    (setIntegral_Iθ_eq_intervalIntegral _).symm
  have hden : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ :=
    (setIntegral_Iθ_eq_intervalIntegral _).symm
  have hne : (∫ θ in Work.Spaces.Iθ,
        Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) ≠ 0 := by
    rw [Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts m]
    positivity
  simp only [Work.FTS.PhiStar.Series.cmode, hnum, hden]
  exact div_mul_cancel₀ _ hne

/-- **Pythagoras for the truncated angular eigenbasis.** -/
theorem eFam_pythagoras (F : ℝ → ℝ → ℝ) (z : ℝ) (N : ℕ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => F z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hz : MeasureTheory.IntegrableOn (fun θ => F z θ ^ 2 * Real.cos θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ,
        (F z θ - ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m F z *
            Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ)
      = (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)
        - ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) := by
  change (∫ θ in Work.Spaces.Iθ, (F z θ - sumEFam F z N θ) ^ 2 * Real.cos θ)
      = (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)
        - ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
  have hzI : MeasureTheory.Integrable (fun θ => F z θ ^ 2 * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hz
  have hint : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun θ => F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      Work.Spaces.Iθ := fun m =>
        Work.EllipticEst.ModalSolution.EFP.integrableOn_mul_eFam_cos F z m hmeas hz
  have hcontS : Continuous (sumEFam F z N) := by
    show Continuous (fun θ : ℝ => ∑ m ∈ Finset.range (N + 1),
      Work.FTS.PhiStar.Series.cmode m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
    fun_prop
  have hmeasS : MeasureTheory.AEStronglyMeasurable (sumEFam F z N)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hcontS.aestronglyMeasurable
  have hSSI : MeasureTheory.Integrable (fun θ => sumEFam F z N θ ^ 2 * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ((hcontS.pow 2).mul Real.continuous_cos).continuousOn.integrableOn_compact isCompact_Icc
  have hFSI : MeasureTheory.Integrable (fun θ => F z θ * sumEFam F z N θ * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono'
      (g := fun θ : ℝ => (1 / 2) * (F z θ ^ 2 * Real.cos θ)
        + (1 / 2) * (sumEFam F z N θ ^ 2 * Real.cos θ)) ?_ ?_ ?_
    · exact (hzI.const_mul (1 / 2)).add (hSSI.const_mul (1 / 2))
    · exact (hmeas.mul hmeasS).mul Real.continuous_cos.aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
        with θ hθ
      have hc : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
      have hsq : Real.sqrt (Real.cos θ) ^ 2 = Real.cos θ := Real.sq_sqrt hc
      rw [Real.norm_eq_abs]
      have hAB : (|F z θ| * Real.sqrt (Real.cos θ)) * (|sumEFam F z N θ| * Real.sqrt (Real.cos θ))
          = |F z θ * sumEFam F z N θ * Real.cos θ| := by
        rw [mul_mul_mul_comm, ← sq, hsq, abs_mul, abs_mul, abs_of_nonneg hc]
      rw [← hAB]
      nlinarith [sq_nonneg (|F z θ| * Real.sqrt (Real.cos θ)
            - |sumEFam F z N θ| * Real.sqrt (Real.cos θ)),
        sq_abs (F z θ), sq_abs (sumEFam F z N θ), hsq]
  -- (P) the cross integral
  have hP : (∫ θ in Work.Spaces.Iθ, F z θ * sumEFam F z N θ * Real.cos θ)
      = ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) := by
    have h1 : (∫ θ in Work.Spaces.Iθ, F z θ * (∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * Real.cos θ)
        = ∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F z *
            (∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
              * Real.cos θ) :=
      Work.EllipticEst.ModalSolution.EFP.integral_mul_finset_sum (Finset.range (N + 1))
        (fun m => Work.FTS.PhiStar.Series.cmode m F z)
        (fun m => Work.FTS.PhiStar.Gegenbauer.eFam m) (fun θ => F z θ)
        (fun m _ => hint m)
    have h2 : (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F z *
            (∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
              * Real.cos θ))
        = ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2
              * Real.cos θ) := by
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [← cmode_mul_norm F z m]
      ring
    exact h1.trans h2
  -- (Q) the squared-sum integral
  have hQ : (∫ θ in Work.Spaces.Iθ, sumEFam F z N θ ^ 2 * Real.cos θ)
      = ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) :=
    Work.EllipticEst.ModalSolution.EFP.sum_sq_orth_collapse (Finset.range (N + 1))
      (fun m => Work.FTS.PhiStar.Series.cmode m F z)
      (fun m => Work.FTS.PhiStar.Gegenbauer.eFam m)
      (fun m => continuous_eFam m)
      (fun m _ n _ hmn => eFam_orthogonal_Iθ m n hmn)
  -- the expansion of the square
  have hexp : (∫ θ in Work.Spaces.Iθ, (F z θ - sumEFam F z N θ) ^ 2 * Real.cos θ)
      = (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)
        - 2 * (∫ θ in Work.Spaces.Iθ, F z θ * sumEFam F z N θ * Real.cos θ)
        + (∫ θ in Work.Spaces.Iθ, sumEFam F z N θ ^ 2 * Real.cos θ) := by
    have hA : MeasureTheory.Integrable
        (fun θ : ℝ => F z θ ^ 2 * Real.cos θ - 2 * (F z θ * sumEFam F z N θ * Real.cos θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hzI.sub (hFSI.const_mul 2)
    have hB : MeasureTheory.Integrable
        (fun θ : ℝ => 2 * (F z θ * sumEFam F z N θ * Real.cos θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hFSI.const_mul 2
    have hC : MeasureTheory.Integrable (fun θ : ℝ => sumEFam F z N θ ^ 2 * Real.cos θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hSSI
    have e1 : (∫ θ in Work.Spaces.Iθ, (F z θ - sumEFam F z N θ) ^ 2 * Real.cos θ)
        = (∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => F z θ ^ 2 * Real.cos θ
              - 2 * (F z θ * sumEFam F z N θ * Real.cos θ)) θ
            + (fun θ : ℝ => sumEFam F z N θ ^ 2 * Real.cos θ) θ) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    have e2 : (∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => F z θ ^ 2 * Real.cos θ
              - 2 * (F z θ * sumEFam F z N θ * Real.cos θ)) θ
            + (fun θ : ℝ => sumEFam F z N θ ^ 2 * Real.cos θ) θ)
        = (∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => F z θ ^ 2 * Real.cos θ
              - 2 * (F z θ * sumEFam F z N θ * Real.cos θ)) θ)
          + (∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => sumEFam F z N θ ^ 2 * Real.cos θ) θ) :=
      MeasureTheory.integral_add hA hC
    have e3 : (∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => F z θ ^ 2 * Real.cos θ
              - 2 * (F z θ * sumEFam F z N θ * Real.cos θ)) θ)
        = (∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => F z θ ^ 2 * Real.cos θ) θ)
          - (∫ θ in Work.Spaces.Iθ,
              (fun θ : ℝ => 2 * (F z θ * sumEFam F z N θ * Real.cos θ)) θ) :=
      MeasureTheory.integral_sub (f := fun θ : ℝ => F z θ ^ 2 * Real.cos θ)
        (g := fun θ : ℝ => 2 * (F z θ * sumEFam F z N θ * Real.cos θ)) hzI hB
    have e4 : (∫ θ in Work.Spaces.Iθ,
          (fun θ : ℝ => 2 * (F z θ * sumEFam F z N θ * Real.cos θ)) θ)
        = 2 * (∫ θ in Work.Spaces.Iθ, F z θ * sumEFam F z N θ * Real.cos θ) :=
      MeasureTheory.integral_const_mul 2 (fun θ : ℝ => F z θ * sumEFam F z N θ * Real.cos θ)
    have e5 : (∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => sumEFam F z N θ ^ 2 * Real.cos θ) θ)
        = (∫ θ in Work.Spaces.Iθ, sumEFam F z N θ ^ 2 * Real.cos θ) := rfl
    have e6 : (∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => F z θ ^ 2 * Real.cos θ) θ)
        = (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ) := rfl
    rw [e1, e2, e3, e4, e5, e6]
  rw [hexp, hP, hQ]
  ring

end Work.EllipticEst.ModalSolution
end
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.eFam_residual_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

set_option linter.style.haveILetI false



end Work.EllipticEst.ModalSolution
end
end
-- ===== merged: Submission.Work.FTS.ClassC.HonestCut.HkMemAe_of_lintegral_k =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.HonestCut

theorem HkMemAe_of_lintegral_k {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hslmeas : ∀ z ∈ Work.Spaces.Iz,
      AEMeasurable (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hfin : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ)) ≤ ENNReal.ofReal C)
    (hmeas : AEMeasurable (fun z => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ))
        (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ)
          Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
        (Set.Ioi 0) := by
  -- The `H^k` integrand is a sum of squares (`Work.Spaces.HkIntegrand_nonneg`), so the
  -- general measure-theory principle of `HkMemAe_of_lintegral` applies verbatim; the only
  -- difference from the level-`0` statement is the shape of the integrand, which is
  -- nonnegative for every `k`.
  exact ae_integrableOn_and_integrableOn_of_lintegral_le
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
    (fun z hz => hslmeas z (Set.Ioi_subset_Ici_self hz)) hfin hmeas

end Work.FTS.ClassC.HonestCut
end
-- ===== merged: Submission.Work.FTS.ClassCHon.CmpSupp.eNorm_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real

namespace Work.FTS.ClassCHon.CmpSupp

/-- Closed form of the modal norm: `eNorm m = ((2m+2)(2m+3))/(4m+5)`. -/
theorem eNorm_eq (m : ℕ) :
    Work.EllipticEst.ModalSolution.eNorm m
      = ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) := by
  rw [Work.EllipticEst.ModalSolution.eNorm, Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts m]

/-- The closed form is always at least `1`, since `(2m+2)(2m+3) - (4m+5) = 4m² + 6m + 1`. -/
theorem one_le_eNorm_closed (m : ℕ) :
    1 ≤ ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (m : ℝ) + 5)]
  nlinarith [sq_nonneg ((m : ℝ) + 1), (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]

/-- The closed form dominates `m`, since `(2m+2)(2m+3) - m(4m+5) = 5m + 6 ≥ 0`. -/
theorem cast_le_eNorm_closed (m : ℕ) :
    (m : ℝ) ≤ ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (m : ℝ) + 5)]
  nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]

theorem eNorm_bounds (m : ℕ) :
    1 ≤ Work.EllipticEst.ModalSolution.eNorm m
      ∧ (m : ℝ) ≤ Work.EllipticEst.ModalSolution.eNorm m := by
  rw [eNorm_eq m]
  exact ⟨one_le_eNorm_closed m, cast_le_eNorm_closed m⟩

end Work.FTS.ClassCHon.CmpSupp
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.HcoefSplit.radGreen_split_le_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.HcoefSplit

theorem radGreen_split_le_gen {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {m : ℕ} (hm : 1 ≤ m)
    {c : ℝ → ℝ} {z L B : ℝ} (hz : 0 < z) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hcL : ∀ t ∈ Set.Icc (z / 2) (2 * z), |c t| ≤ L)
    (hc : MeasureTheory.IntegrableOn (fun t : ℝ => (c t * Work.Spaces.w t) ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => c t * Work.Spaces.w t)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hBs : Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * Work.Spaces.w t) ^ 2) ≤ B) :
    |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ Work.FTS.EllExist.rgK α m *
      (L * (1 / Work.FTS.EllExist.rgQ α m + 1 / Work.FTS.EllExist.rgP α m)
        + B * ((2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
              / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
            + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
              / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3))) := by
  -- the two exponent hypotheses of `radGreen_split_le` are implied by `0 < α ≤ 1/4`, `1 ≤ m`
  have hq : 1 < Work.FTS.EllExist.rgQ α m := by
    have h := Work.FTS.EllExist.rgQ_ge hα hα4 hm
    linarith
  have hp : 3 / 2 < Work.FTS.EllExist.rgP α m := by
    have h := Work.FTS.EllExist.rgP_ge hα hα4 hm
    linarith
  exact Work.FTS.ClassCHon.Hcoef.radGreen_split_le hα hz hL hB hq hp hcL hc hcm hBs

end Work.FTS.ClassCHon.HcoefSplit
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2norm.z_A1_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2norm



end Work.FTS.CoercivityFix.Transfer.E2norm
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.radGreen_l2_near_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

open MeasureTheory Set
open scoped Real Topology

-- `radGreen α m c` is the decaying solution of the mode-`m` radial Euler equation
-- `-α²z²a'' - α(5+α)z a' + λ_m a = c` (λ_m = 2m(2m+5)), in explicit Green's-function form
-- (`Work.FTS.PhiStar.Radial.radGreen`, with `s⁻ = -(2m+5)/α`, `s⁺ = 2m/α`,
--  `K = 1/(α(4m+5))`).  This is the `z → 0` half of the weighted `L²`-honesty of `radGreen`,
-- i.e. of the mode-`m` coefficient `a m = radGreen α m (cmode m F)` of the solution
-- `Ψ = Σ_m a m(z) e_m(θ)` of `bslOp α Ψ = F`.
--
-- ROUTE (as proved; the two Green terms separately, `radGreen = K(G₁+G₂)` and `(G₁+G₂)² ≤ 2G₁²+2G₂²`).
-- With `G₁ := G1 α m c = z^{s⁻}∫_0^z c t^{-1-s⁻}dt` and `G₂ := G2 α m c = z^{s⁺}∫_z^∞ c t^{-1-s⁺}dt`
-- (`s⁻ = -(2m+5)/α`, `s⁺ = 2m/α`, `K = 1/(α(4m+5))`; see `RadGreenDefs`), both terms are estimated
-- by an *energy identity* plus the FTC — no Tonelli/Fubini is needed, and this is the route
-- formalised here (`G1_est`, `G2_est`):
-- * `z·G₁' = s⁻·G₁ + c`  and  `z·G₂' = s⁺·G₂ - c`; hence `u := G₁²/z³` satisfies
--   `u' = ((2s⁻-3)G₁² + 2cG₁)/z⁴` and `v := G₂²/z³` satisfies `v' = ((2s⁺-3)G₂² - 2cG₂)/z⁴`.
-- * FTC on `[x,y] ⊆ (0,1)`: `(3-2s⁻)∫_x^y G₁²/z⁴ = 2∫_x^y cG₁/z⁴ + G₁(x)²/x³ - G₁(y)²/y³`.
--   The *pointwise* estimate `|G₁(z)| ≤ z^{3/2}√(M₀/(2a+3))` (`a := (2m+5)/α = -s⁻`,
--   `M₀ := ∫_0^1 c²/z⁴ < ∞`) only gives `G₁²/z⁴ = O(1/z)`, which is NOT integrable, so the endpoint
--   term is bounded instead by an AM–GM with the `x`-dependent weight `λ := x^{a-1/2}`
--   (`2|XY| ≤ λX² + Y²/λ`, `X = |c u|/u`, `Y = u^a`): `G₁(x)²/x³ ≤ CΦ` uniformly for `x ∈ (0,1]`.
--   The AM–GM `2|cG₁|/z⁴ ≤ η c²/z⁴ + η^{-1}G₁²/z⁴`, `η := 2/(3-2s⁻)`, together with
--   `∫_x^y c²/z⁴ ≤ M₀` then bounds `∫_x^y G₁²/z⁴` uniformly in `0 < x < y < 1`.
-- * For `G₂` the same identity on `[x,1]` has the harmless endpoint `-G₂(x)²/x³ ≤ 0` and
--   `G₂(1)² = (∫_{Ioi 1} c t^{-1-s⁺}dt)² ≤ (∫_{Ioi 1}|c|t^{-1-s⁺}dt)²`, which is finite by `hinf`;
--   no decay of `G₂` at `0` is needed, and none holds (for `c(z) = z²`, `∫_{Ioi z} c t^{-1-s⁺}dt`
--   blows up like `z^{-s⁺-1}` while `G₂(z) = z^{s⁺}·(that)` stays bounded).
-- * `integrableOn_add_sq_div_of_interval_bounds` (`IooIntervalTool`) turns the two uniform interval
--   bounds and the two continuity statements into `IntegrableOn ((G₁+G₂)²/z⁴) (0,1)`; multiplying by
--   `K²` and rewriting `radGreen = K(G₁+G₂)` gives the claim.
-- The range `1 ≤ m`, `α ≤ 1/4` is load-bearing: `2s⁺ = 4m/α ≥ 16 > 3`, which is what makes the
-- `G₂`-energy identity's AM–GM and the `z → 0` behaviour of `G₂²/z⁴` work.

theorem radGreen_l2_near_zero (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m)
    {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => |c t| * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z ^ 2 / z ^ 4) (Set.Ioo 0 1) := by
  -- `radGreen = K·(G1 + G2)`; each of the two Green terms has uniformly bounded weighted
  -- `L²`-interval integrals near `z = 0` and is continuous on `(0,1)`, so their sum has an integrable
  -- weighted square (`integrableOn_add_sq_div_of_interval_bounds`); multiplying by `K²` gives the claim.
  obtain ⟨⟨M₁, hM₁, hb₁⟩, hc₁⟩ := G1_est α hα m hc h0
  obtain ⟨⟨M₂, hM₂, hb₂⟩, hc₂⟩ := G2_est α hα hα4 m hm hc h0 hinf
  have hc₂' : ContinuousOn (fun z => G2 α m c z) (Set.Ioo 0 1) :=
    hc₂.mono Set.Ioo_subset_Ioi_self
  have hsum : MeasureTheory.IntegrableOn
      (fun z => (G1 α m c z + G2 α m c z) ^ 2 / z ^ 4) (Set.Ioo 0 1) :=
    integrableOn_add_sq_div_of_interval_bounds hM₁ hM₂ hc₁ hc₂' hb₁ hb₂
  have hkey : (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z ^ 2 / z ^ 4)
      = fun z => (1 / (α * (4 * (m : ℝ) + 5))) ^ 2 *
          ((G1 α m c z + G2 α m c z) ^ 2 / z ^ 4) := by
    funext z
    rw [radGreen_eq_G1_add_G2]
    ring
  rw [hkey]
  exact hsum.const_mul _



end Work.FTS.EllExist.Honesty
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.KernelDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Work.FTS.EllSol.PkgK5.K5c

local notation "Iθ" => Work.Spaces.Iθ
local notation "σθ" => Work.FTS.EllipticEst.thEta

/-- The three-image mollification kernel of the doubly odd extension. -/
def KJ (ε θ s : ℝ) : ℝ :=
  sKer ε (θ - s) + sKer ε (θ + s) + sKer ε (θ + s - Real.pi)

theorem KJ_nonneg {ε : ℝ} (hε : 0 < ε) (θ s : ℝ) : 0 ≤ KJ ε θ s := by
  simp only [KJ]
  exact add_nonneg (add_nonneg (sKer_nonneg hε _) (sKer_nonneg hε _)) (sKer_nonneg hε _)

theorem KJ_le {ε : ℝ} (hε : 0 < ε) (θ s : ℝ) : KJ ε θ s ≤ 3 * (ε * sMass)⁻¹ := by
  have h1 := Work.FTS.EllSol.K5cAux.sKer_le_inv hε (θ - s)
  have h2 := Work.FTS.EllSol.K5cAux.sKer_le_inv hε (θ + s)
  have h3 := Work.FTS.EllSol.K5cAux.sKer_le_inv hε (θ + s - Real.pi)
  simp only [KJ]
  linarith

theorem continuous_KJ (ε : ℝ) : Continuous (fun p : ℝ × ℝ => KJ ε p.1 p.2) := by
  have hc : Continuous (fun t : ℝ => sKer ε t) := Work.FTS.EllSol.K5cAux.continuous_sKer ε
  have h1 : Continuous (fun p : ℝ × ℝ => sKer ε (p.1 - p.2)) :=
    hc.comp (continuous_fst.sub continuous_snd)
  have h2 : Continuous (fun p : ℝ × ℝ => sKer ε (p.1 + p.2)) :=
    hc.comp (continuous_fst.add continuous_snd)
  have h3 : Continuous (fun p : ℝ × ℝ => sKer ε (p.1 + p.2 - Real.pi)) :=
    hc.comp ((continuous_fst.add continuous_snd).sub continuous_const)
  simp only [KJ]
  exact (h1.add h2).add h3

theorem integrable_sKer_sub {ε θ : ℝ} (hε : 0 < ε) :
    Integrable (fun s : ℝ => sKer ε (θ - s)) volume := by
  have h := (Work.FTS.EllSol.K5cAux.integrable_sKer hε).comp_sub_right θ
  refine h.congr (Filter.Eventually.of_forall (fun s => ?_))
  show sKer ε (s - θ) = sKer ε (θ - s)
  rw [show θ - s = -(s - θ) by ring, sKer_even]

theorem integrable_sKer_add {ε θ : ℝ} (hε : 0 < ε) :
    Integrable (fun s : ℝ => sKer ε (θ + s)) volume := by
  have h := (Work.FTS.EllSol.K5cAux.integrable_sKer hε).comp_sub_right (-θ)
  refine h.congr (Filter.Eventually.of_forall (fun s => ?_))
  show sKer ε (s - -θ) = sKer ε (θ + s)
  rw [show s - -θ = θ + s by ring]

theorem integrable_sKer_shift {ε θ : ℝ} (hε : 0 < ε) :
    Integrable (fun s : ℝ => sKer ε (θ + s - Real.pi)) volume := by
  have h := (Work.FTS.EllSol.K5cAux.integrable_sKer hε).comp_sub_right (Real.pi - θ)
  refine h.congr (Filter.Eventually.of_forall (fun s => ?_))
  show sKer ε (s - (Real.pi - θ)) = sKer ε (θ + s - Real.pi)
  rw [show s - (Real.pi - θ) = θ + s - Real.pi by ring]

theorem integrable_KJ_slice {ε θ : ℝ} (hε : 0 < ε) :
    Integrable (fun s : ℝ => KJ ε θ s) volume := by
  have h1 := integrable_sKer_sub (θ := θ) hε
  have h2 := integrable_sKer_add (θ := θ) hε
  have h3 := integrable_sKer_shift (θ := θ) hε
  have hsum : (fun s : ℝ => KJ ε θ s)
      = (fun s : ℝ => sKer ε (θ - s) + sKer ε (θ + s) + sKer ε (θ + s - Real.pi)) := rfl
  rw [hsum]
  exact (h1.add h2).add h3

theorem integral_KJ_line {ε θ : ℝ} (hε : 0 < ε) : (∫ s : ℝ, KJ ε θ s) = 3 := by
  have h1 : (∫ s : ℝ, sKer ε (θ - s)) = 1 := by
    rw [show (fun s : ℝ => sKer ε (θ - s)) = fun s : ℝ => sKer ε (s - θ) by
      funext s; rw [show θ - s = -(s - θ) by ring, sKer_even]]
    rw [MeasureTheory.integral_sub_right_eq_self, sKer_integral_eq_one hε]
  have h2 : (∫ s : ℝ, sKer ε (θ + s)) = 1 := by
    rw [show (fun s : ℝ => sKer ε (θ + s)) = fun s : ℝ => sKer ε (s - (-θ)) by
      funext s; rw [show s - -θ = θ + s by ring]]
    rw [MeasureTheory.integral_sub_right_eq_self, sKer_integral_eq_one hε]
  have h3 : (∫ s : ℝ, sKer ε (θ + s - Real.pi)) = 1 := by
    rw [show (fun s : ℝ => sKer ε (θ + s - Real.pi))
        = fun s : ℝ => sKer ε (s - (Real.pi - θ)) by
      funext s; rw [show s - (Real.pi - θ) = θ + s - Real.pi by ring]]
    rw [MeasureTheory.integral_sub_right_eq_self, sKer_integral_eq_one hε]
  have hi1 : Integrable (fun s : ℝ => sKer ε (θ - s)) volume := integrable_sKer_sub (θ := θ) hε
  have hi2 : Integrable (fun s : ℝ => sKer ε (θ + s)) volume := integrable_sKer_add (θ := θ) hε
  have hi3 : Integrable (fun s : ℝ => sKer ε (θ + s - Real.pi)) volume :=
    integrable_sKer_shift (θ := θ) hε
  have hsum : (∫ s : ℝ, KJ ε θ s)
      = (∫ s : ℝ, sKer ε (θ - s) + sKer ε (θ + s) + sKer ε (θ + s - Real.pi)) := rfl
  rw [hsum]
  have e2 : (∫ s : ℝ, sKer ε (θ - s) + sKer ε (θ + s) + sKer ε (θ + s - Real.pi))
      = (∫ s : ℝ, sKer ε (θ - s) + sKer ε (θ + s))
        + ∫ s : ℝ, sKer ε (θ + s - Real.pi) :=
    MeasureTheory.integral_add (hi1.add hi2) hi3
  have e1 : (∫ s : ℝ, sKer ε (θ - s) + sKer ε (θ + s))
      = (∫ s : ℝ, sKer ε (θ - s)) + ∫ s : ℝ, sKer ε (θ + s) :=
    MeasureTheory.integral_add hi1 hi2
  rw [e2, e1, h1, h2, h3]
  norm_num

theorem KJ_mass {ε θ : ℝ} (hε : 0 < ε) (_hθ : θ ∈ Iθ) :
    ∫ s in Iθ, KJ ε θ s ≤ 3 := by
  have hint : Integrable (fun s : ℝ => KJ ε θ s) volume := integrable_KJ_slice hε
  have h1 : (∫ s in Iθ, KJ ε θ s) ≤ ∫ s : ℝ, KJ ε θ s :=
    MeasureTheory.setIntegral_le_integral hint
      (Filter.Eventually.of_forall (fun s => KJ_nonneg hε θ s))
  rw [integral_KJ_line hε] at h1
  exact h1

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.radialAuxAng =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Radial profiles vs. their `sin (2θ)`-multiples: the angular identities

Part 2 of the proof of `Work.FTS.EllSol.PkgK5.radialHkNorm_le_sinMul`: the `D_θ`-algebra
(the `Lop` iterates of `sin 2·`, the product identity `D_θ^i (Λ·B) = Λ · D_θ^i B`, the
vanishing of the angular derivatives of a radial profile and the mixed identity).
-/

namespace Work.FTS.EllSol.PkgK5

namespace Radial

/-! ## The angular profile `sin (2θ)` -/

/-- All `Lop`-iterates of `sin (2·)` are smooth everywhere. -/
theorem contDiffOn_LopIter_sin :
    ∀ i n : ℕ, ContDiffOn ℝ n (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)))
      Set.univ := by
  intro i
  induction i with
  | zero =>
    intro n
    exact (by fun_prop : ContDiffOn ℝ n (fun θ : ℝ => Real.sin (2 * θ)) Set.univ)
  | succ i ih =>
    intro n
    have h1 : ContDiffOn ℝ (n + 1)
        (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ))) Set.univ := ih (n + 1)
    have h2 : ContDiffOn ℝ n
        (deriv (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)))) Set.univ :=
      h1.deriv_of_isOpen isOpen_univ (by simp)
    have h3 : Work.FTS.EllipticEst.LopIter (i + 1) (fun θ : ℝ => Real.sin (2 * θ))
        = fun θ => Real.sin (2 * θ)
            * deriv (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ))) θ := by
      rw [Work.FTS.EllipticEst.LopIter_succ]; rfl
    rw [h3]
    exact ((by fun_prop : ContDiffOn ℝ n (fun θ : ℝ => Real.sin (2 * θ)) Set.univ)).mul h2

theorem differentiable_LopIter_sin (i : ℕ) :
    Differentiable ℝ (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ))) := fun θ =>
  ((contDiffOn_LopIter_sin i 1).differentiableOn (by simp)).differentiableAt (by simp)

theorem continuous_LopIter_sin (i : ℕ) :
    Continuous (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ))) :=
  continuousOn_univ.mp (contDiffOn_LopIter_sin i 0).continuousOn

/-- `D_θ^i` of a function of the form `(z,θ) ↦ Λ z · B θ` is `(Λ z) · D_θ^i B θ`. -/
theorem DthIter_mul_theta (Λ B : ℝ → ℝ)
    (hB : ∀ i : ℕ, Differentiable ℝ (Work.FTS.EllipticEst.LopIter i B)) :
    ∀ i : ℕ, Work.Spaces.DthIter i (fun z θ => Λ z * B θ)
      = fun z θ => Λ z * Work.FTS.EllipticEst.LopIter i B θ := by
  intro i
  induction i with
  | zero => funext z θ; simp
  | succ i ih =>
    funext z θ
    have hfun : (fun θ' => Work.Spaces.DthIter i (fun z θ => Λ z * B θ) z θ')
        = fun θ' => Λ z * Work.FTS.EllipticEst.LopIter i B θ' := by
      funext θ'
      rw [congrFun (congrFun ih z) θ']
    have hd : DifferentiableAt ℝ (Work.FTS.EllipticEst.LopIter i B) θ := hB i θ
    rw [Work.Spaces.DthIter_succ]
    simp only [Work.Spaces.Dth, Work.Spaces.pth, hfun, deriv_const_mul _ hd,
      Work.FTS.EllipticEst.LopIter_succ, Work.Spaces.Lop]
    ring

/-- `D_θ^i (Λ·sin 2·) = Λ · D_θ^i (sin 2·)`. -/
theorem DthIter_sinMul (Λ : ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => Λ z * Real.sin (2 * θ))
      = fun z θ => Λ z * Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ :=
  DthIter_mul_theta Λ (fun θ : ℝ => Real.sin (2 * θ)) differentiable_LopIter_sin i

/-! ## Vanishing of the angular derivatives of a radial function -/

theorem DthIter_radial_zero (Λ : ℝ → ℝ) (m : ℕ) :
    Work.Spaces.DthIter (m + 1) (fun z θ => Λ z) = 0 := by
  induction m with
  | zero =>
    funext z θ
    simp [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
  | succ m ih =>
    rw [show m + 1 + 1 = (m + 1) + 1 from rfl, Work.Spaces.DthIter_succ, ih]
    funext z θ
    simp [Work.Spaces.Dth, Work.Spaces.pth]

theorem Dz_zero (j : ℕ) : Work.Spaces.DzIter j (0 : ℝ → ℝ → ℝ) = 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Work.Spaces.DzIter_succ, ih]
    funext z θ
    simp [Work.Spaces.Dz, Work.Spaces.pz]

/-- The mixed summands of `HkIntegrand` vanish for a radial function. -/
theorem mixed_radial_zero (Λ : ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => Λ z) z θ = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rw [Work.Spaces.mixed, DthIter_radial_zero Λ m, Dz_zero j]
  rfl

/-- The mixed derivative of `(z,θ) ↦ Λ z · sin(2θ)`. -/
theorem mixed_sinMul (Λ : ℝ → ℝ) (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0))
    (j i : ℕ) {z : ℝ} (hz : 0 < z) (θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => Λ z * Real.sin (2 * θ)) z θ
      = RIter j Λ z * Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ := by
  have h1 : Work.Spaces.mixed j i (fun z θ => Λ z * Real.sin (2 * θ))
      = Work.Spaces.DzIter j
          (fun z θ => Λ z * Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) := by
    rw [Work.Spaces.mixed, DthIter_sinMul Λ i]
  rw [h1, DzIter_mul_theta Λ hΛ (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ))) j hz θ]

/-! ## Two `rpow` rewrites -/

theorem rpow_neg_half_sq (γ : ℝ) (hγ : γ ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    (s ^ (-(γ / 2))) ^ 2 = s ^ (-γ) := by
  rcases lt_or_eq_of_le hs with h | h
  · rw [sq, ← Real.rpow_add h]
    congr 1
    ring
  · subst h
    have h1 : -(γ / 2) ≠ 0 := by intro hc; exact hγ (by linarith [neg_eq_zero.mp hc])
    have h2 : -γ ≠ 0 := by intro hc; exact hγ (by linarith [neg_eq_zero.mp hc])
    rw [Real.zero_rpow h1, Real.zero_rpow h2]
    norm_num

theorem sq_mul_rpow_neg (e : ℝ) (he : e ≠ 2) {s : ℝ} (hs : 0 ≤ s) :
    s ^ 2 * s ^ (-e) = s ^ (2 - e) := by
  rcases lt_or_eq_of_le hs with h | h
  · rw [← Real.rpow_natCast s 2, ← Real.rpow_add h]
    ring_nf
  · subst h
    have h3 : 2 - e ≠ 0 := by intro hc; exact he (by linarith)
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, Real.zero_rpow h3]

end Radial

end Work.FTS.EllSol.PkgK5
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.corrSlice_limits =====
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

/-- `x ^ p → 0` as `x → 0⁺` for `p > 0`. -/
lemma tendsto_rpow_nhdsGT_zero {p : ℝ} (hp : 0 < p) :
    Tendsto (fun x : ℝ => x ^ p) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h : Tendsto (fun x : ℝ => (x⁻¹) ^ (-p)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (tendsto_rpow_neg_atTop hp).comp tendsto_inv_nhdsGT_zero
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [Real.inv_rpow (le_of_lt hx) (-p), Real.rpow_neg (le_of_lt hx) p, inv_inv]











end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.slice_f_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Blocks

set_option autoImplicit false

/-! ## Auxiliary lemmas for `slice_f_bound`

Write `s = sin(2θ)`, `L = D_θ = sin(2θ) ∂_θ`, `v = sliceV u = u''`, `γ = gam α`, `η = eta`,
`P = slicePhi α K u θ` and `B` for the explicit constant built in the proof (depending only on
`K`).  The plan is:

* `L²u = s²·v + 2cos(2θ)·(L u)`, and for `i ≥ 2` two applications of the iterated Leibniz rule
  expand `L^i u` into the two sums of `sfF1`, `sfF2`.
* Since `|L^a(s²) θ| ≤ D·s²` (`sfb_Lop_sin_sq_bound`) and `|L^a(2cos 2θ) θ| ≤ 4D`
  (`sfb_cos_iter_bound`), each `v`-term is bounded by a fixed multiple of `P` (using `s^4 ≤ 1`
  and `s^{4-γ} ≤ sin(2θ)^{-η} = thEta`) and each `u`-term by `16 D² B^{i-1} P` (strong
  induction on `i`; the indices occurring in the `u`-terms are `1 ≤ j ≤ i-1`).
* `sq_sum_le_card_mul_sum_sq` and the binomial bound `Σ_a C(n,a)² ≤ (n+1)4^n`
  (`sfb_choose_sq_sum_le`) turn this into `(L^i u θ)² sin(2θ)^{-γ} ≤ 34(i-1)²D²4^{i-2}B^{i-1}P
  ≤ B^i·P`.
* The `u`-term `(u θ)² sin(2θ)^{-η}` is `Blocks.slice_self_sq_le` combined with
  `∫_{Iθ} sin(2θ)^η ≤ π/2`. -/















/-! ## Locality of the iterates of `L` -/






/-! ## The iterates of `sin(2θ)²` and of `2 cos(2θ)` -/






/-! ## The expansion of `L^{n+2} u` -/







end Work.FTS.EllipticEst.Blocks
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LevelOneAsm.eigFun_parseval =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.LevelOneAsm

local notation "Iθ" => Work.Spaces.Iθ


end Work.FTS.EllipticEst.LevelOneAsm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Mine.slice_ident_bound_fts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Mine

set_option autoImplicit false
set_option linter.unusedSimpArgs false





end Work.FTS.EllipticEst.Mine
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.TIProp.Helpers =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Elementary bounds for the weighted angular interpolation

This module collects the elementary facts used by the proof of
`Work.FTS.EllipticEst.Prop.thetaInterpCoreOfTraceBounds`:

* positivity of the angular weight `σ = sin(2θ)^{-η}` on the open interval;
* the fact that almost every point of `Iθ` lies in the open interval;
* the tail bound `∫_0^{L/2} σ ≤ 200 L^{1-η}` (and its mirror image);
* the scaled endpoint bound `F² L^{1-η} ≤ 200 P` from `F² ≤ 2L^{3+η}E + 100L^{η-1}P` and
  `L⁴ = P/(16(P+E))`.
-/

namespace Work.FTS.EllipticEst.Prop.TIProp

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

local notation "σ" => Work.FTS.EllipticEst.thEta

/-- `thEta` is nonnegative on the open angular interval. -/
lemma thEta_nonneg_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 ≤ σ θ :=
  Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩


/-- Almost every point of `Iθ` lies in the open angular interval. -/
lemma ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  change ∀ᵐ θ ∂(volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))),
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
  refine measure_mono_null ?_ ((Set.toFinite ({0, Real.pi / 2} : Set ℝ)).measure_zero volume)
  rintro θ hθ
  rw [Set.mem_setOf_eq, not_imp] at hθ
  obtain ⟨h1, h2⟩ := hθ
  rw [Set.mem_Icc] at h1
  rw [Set.mem_Ioo] at h2
  rw [not_and_or, not_lt, not_lt] at h2
  rcases h2 with h2 | h2
  · exact Or.inl (le_antisymm h2 h1.1)
  · exact Or.inr (le_antisymm h1.2 h2)

/-- The tail mass of the angular weight: `∫_0^{L/2} σ ≤ 200 L^{1-η}` (open interval form). -/
lemma thEta_tail_left_Ioo {L : ℝ} (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    (∫ θ in Set.Ioo (0 : ℝ) (L / 2), σ θ) ≤ 200 * L ^ (1 - Work.Spaces.eta) := by
  have h := Work.EllipticEst.Core.i0Aux.TVRed.thEta_tail_left (L := L) hL hLp
  rwa [MeasureTheory.integral_Icc_eq_integral_Ioc,
    MeasureTheory.integral_Ioc_eq_integral_Ioo] at h

/-- The tail mass of the angular weight at the right endpoint (open interval form). -/
lemma thEta_tail_right_Ioo {L : ℝ} (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    (∫ θ in Set.Ioo (Real.pi / 2 - L / 2) (Real.pi / 2), σ θ)
      ≤ 200 * L ^ (1 - Work.Spaces.eta) := by
  have h := Work.EllipticEst.Core.i0Aux.TVRed.thEta_tail_right (L := L) hL hLp
  rwa [MeasureTheory.integral_Icc_eq_integral_Ioc,
    MeasureTheory.integral_Ioc_eq_integral_Ioo] at h

/-- **Scaled endpoint bound.**  If `L⁴ = P/(16(P+E))` and `F² ≤ 2L^{3+η}E + 100L^{η-1}P`, then
`F²L^{1-η} ≤ 200P`. -/
lemma endpoint_scale {F L P E : ℝ} (hL : 0 < L) (hPpos : 0 < P) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hL4 : L ^ 4 = P / (16 * (P + E)))
    (hF : F ^ 2 ≤ 2 * L ^ (3 + Work.Spaces.eta) * E
      + 100 * L ^ (Work.Spaces.eta - 1) * P) :
    F ^ 2 * L ^ (1 - Work.Spaces.eta) ≤ 200 * P := by
  have h1 : L ^ (3 + Work.Spaces.eta) * L ^ (1 - Work.Spaces.eta) = L ^ (4 : ℝ) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have h2 : L ^ (Work.Spaces.eta - 1) * L ^ (1 - Work.Spaces.eta) = 1 := by
    rw [← Real.rpow_add hL,
      show Work.Spaces.eta - 1 + (1 - Work.Spaces.eta) = (0 : ℝ) by ring, Real.rpow_zero]
  have h := mul_le_mul_of_nonneg_right hF (Real.rpow_nonneg hL.le (1 - Work.Spaces.eta))
  have h3 : (2 * L ^ (3 + Work.Spaces.eta) * E + 100 * L ^ (Work.Spaces.eta - 1) * P)
        * L ^ (1 - Work.Spaces.eta)
      = 2 * (L ^ (3 + Work.Spaces.eta) * L ^ (1 - Work.Spaces.eta)) * E
        + 100 * (L ^ (Work.Spaces.eta - 1) * L ^ (1 - Work.Spaces.eta)) * P := by ring
  rw [h3, h1, h2] at h
  have h4 : L ^ (4 : ℝ) * E ≤ P / 16 := by
    have hc : L ^ (4 : ℝ) = L ^ 4 := Real.rpow_natCast L 4
    rw [hc, hL4, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

end Work.FTS.EllipticEst.Prop.TIProp
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.TraceLeftPieces.Prod =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `F₀ L₀` bound `F₀ L₀ ≤ (K/2) A + √(A D)`
-/

namespace Work.FTS.EllipticEst.Prop.TraceLeftCore

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-! ### Comparison of the plain `L²`-integrals with the weighted energies -/


/-! ### The `F₀ L₀` bound -/


end

end Work.FTS.EllipticEst.Prop.TraceLeftCore
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.I1SliceIBP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-- The angular weight `σ θ = sin(2θ)^{-η}` (a copy of `AngSecond.sigE`). -/
abbrev sigE := Work.FTS.EllipticEst.AngSecond.sigE

/-- `σ'` (a copy of `AngSecond.sigD`). -/
abbrev sigD := Work.FTS.EllipticEst.AngSecond.sigD

/-- `σ''` (a copy of `AngSecond.sigDD`). -/
abbrev sigDD := Work.FTS.EllipticEst.AngSecond.sigDD

/-- `cos(2θ)` (a copy of `AngSecond.c2`). -/
abbrev c2 := Work.FTS.EllipticEst.AngSecond.c2

/-! ## 1. The majorant `(π/4)^p (θ^{-p} + (π/2-θ)^{-p})` -/



/-! ## 2. The derivative of `σ'` -/


/-! ## 3. The endpoint limits of the two antiderivatives -/


/-- A one-sided squeeze: an eventually nonnegative function dominated eventually by a function
tending to `0` tends to `0`. -/
theorem tendsto_zero_of_eventually_le {f g : ℝ → ℝ} {l : Filter ℝ}
    (hf : ∀ᶠ t in l, 0 ≤ f t) (hfg : ∀ᶠ t in l, f t ≤ g t) (hg : Tendsto g l (nhds 0)) :
    Tendsto f l (nhds 0) := by
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hf] with t ht
    linarith
  · have h := (tendsto_order.mp hg).2 b hb
    filter_upwards [h, hfg] with t ht hle
    linarith






end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.angSlot_le_AngRHS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Every angular slot of `u` is dominated by `AngRHS`

`AngRHS k γ u g` (see `remov/slice_ang_reduce.lean`) is the sum of the five weighted norms

* `∫ g^{(k)}² sin(2θ)^{2k-γ}`,   (the source term)
* `∑_{j=3}^{k+1} ∫ u^{(j)}² sin(2θ)^{2j-4-γ}`,
* `∫ u''² sin(2θ)^{-η}`,
* `∫ u'²`,   `∫ u²`.

The present file proves that for `1 ≤ γ ≤ 5/4` and `k ≥ 2` **every** slot
`∫ u^{(j)}² sin(2θ)^{2k-γ}` with `j ≤ k+1` (and the corresponding integrability)
is bounded by `AngRHS k γ u g`.  The only mathematical input is that the weight
`sin(2θ)^{2k-γ}` is dominated by the matching weight of the corresponding summand:

* `j = 0, 1`: `sin(2θ)^{2k-γ} ≤ 1`;
* `j = 2`:     `sin(2θ)^{2k-γ} ≤ sin(2θ)^{-η}`  (`-η ≤ 2k - γ`);
* `j ≥ 3`:     `sin(2θ)^{2k-γ} ≤ sin(2θ)^{2j-4-γ}`  (`j ≤ k+2`),

each applied after multiplication by the nonnegative factor `u^{(j)}²`.

The reduction is packaged in `angSlot_weight_mono`, which turns the monotonicity of
the weight (on `(0,π/2)`, where `0 < sin(2θ) ≤ 1`, plus the trivial endpoint case
`sin(2θ) = 0`) into simultaneous integrability and integral comparison.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-! ## Elementary facts about `Iθ`, and the `rpow`/`iteratedDeriv` bridges

The statement uses `Real.rpow` explicitly, so the comparison lemmas are restated with
`Real.rpow` on the left-hand side (the corresponding Mathlib lemmas are stated with the
`x ^ y` notation, which `rw` does not match against `Real.rpow`). -/

lemma angSlot_Iθ_measurable : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc

lemma angSlot_sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

lemma angSlot_rpow_zero (x : ℝ) : Real.rpow x (0 : ℝ) = 1 := Real.rpow_zero x

lemma angSlot_zero_rpow {y : ℝ} (hy : y ≠ 0) : Real.rpow (0 : ℝ) y = 0 := Real.zero_rpow hy

lemma angSlot_iteratedDeriv_two (u : ℝ → ℝ) : iteratedDeriv 2 u = deriv (deriv u) := by
  rw [iteratedDeriv_succ', iteratedDeriv_one]

lemma angSlot_itd0_mul_rpow_zero (u : ℝ → ℝ) :
    (fun θ : ℝ => (iteratedDeriv 0 u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (0 : ℝ))
      = fun θ : ℝ => (u θ) ^ 2 := by
  funext θ
  simp only [iteratedDeriv_zero, angSlot_rpow_zero, mul_one]

lemma angSlot_itd1_mul_rpow_zero (u : ℝ → ℝ) :
    (fun θ : ℝ => (iteratedDeriv 1 u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (0 : ℝ))
      = fun θ : ℝ => (deriv u θ) ^ 2 := by
  funext θ
  simp only [iteratedDeriv_one, angSlot_rpow_zero, mul_one]

lemma angSlot_itd2_mul_rpow (u : ℝ → ℝ) (q : ℝ) :
    (fun θ : ℝ => (iteratedDeriv 2 u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) q)
      = fun θ : ℝ => (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) q := by
  funext θ
  simp only [angSlot_iteratedDeriv_two]

/-! ## Measurability of the iterated derivatives on `Iθ` -/

/-- `iteratedDeriv j u` is almost everywhere strongly measurable for the restriction of the
Lebesgue measure to `Iθ`, as soon as `u ∈ C^{k+2}` on the *open* interval and `j ≤ k+2`:
on the open interval the function is continuous (`ContDiffOn.continuousOn_iteratedDerivWithin`
combined with `iteratedDerivWithin = iteratedDeriv` there), and the two endpoints of `Iθ`
form a null set. -/
theorem angSlot_measurable_iteratedDeriv {k j : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2))) (hj : j ≤ k + 2) :
    AEStronglyMeasurable (fun θ : ℝ => iteratedDeriv j u θ)
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
  have hs : UniqueDiffOn ℝ (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo.uniqueDiffOn
  have hle : (j : WithTop ℕ∞) ≤ (k + 2 : WithTop ℕ∞) := by
    exact_mod_cast (show j ≤ k + 2 by omega)
  have hc : ContinuousOn (iteratedDerivWithin j u (Set.Ioo 0 (Real.pi / 2)))
      (Set.Ioo 0 (Real.pi / 2)) := hu.continuousOn_iteratedDerivWithin hle hs
  have hc' : ContinuousOn (fun θ => iteratedDeriv j u θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hc.congr (fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm)
  have h1 : AEStronglyMeasurable (fun θ => iteratedDeriv j u θ)
      ((volume : Measure ℝ).restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hc'.aestronglyMeasurable measurableSet_Ioo
  have hae : (Work.Spaces.Iθ : Set ℝ) =ᵐ[(volume : Measure ℝ)] Set.Ioo 0 (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ))).symm
  rwa [Measure.restrict_congr_set hae]

/-! ## The weight comparison: a larger `rpow` exponent gives a smaller weight -/

/-- **The slot comparison.**  For `0 < Q` and `q ≤ Q`, the `Q`-weighted slot of
`iteratedDeriv j u` is integrable as soon as the `q`-weighted one is, and its integral is at
most the `q`-weighted integral.

On `(0,π/2)` the weight comparison is monotonicity of `x ↦ x^r` on `0 < x ≤ 1`; at the
endpoints `sin(2θ) = 0` the left-hand side vanishes because `Q ≠ 0`, while the right-hand
side is nonnegative. -/
theorem angSlot_weight_mono {Q q : ℝ} (hQ : 0 < Q) (hq : q ≤ Q) (j : ℕ) {u : ℝ → ℝ}
    (hA : AEStronglyMeasurable (fun θ : ℝ => iteratedDeriv j u θ)
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ))
    (hIntBig : IntegrableOn
      (fun θ : ℝ => (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) q)
        Work.Spaces.Iθ) :
    IntegrableOn
        (fun θ : ℝ => (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) Q)
          Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) Q)
        ≤ (∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) q) := by
  have hrpow : Continuous (fun x : ℝ => x ^ Q) :=
    continuous_iff_continuousAt.mpr (fun x => Real.continuousAt_rpow_const x Q (Or.inr hQ.le))
  have hsin2 : Continuous (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hcontQ : Continuous (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) Q) := hrpow.comp hsin2
  have hsmQ : AEStronglyMeasurable
      (fun θ : ℝ => (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) Q)
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
    (hA.pow 2).mul hcontQ.measurable.aestronglyMeasurable
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) Q
        ≤ (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) q := by
    filter_upwards [MeasureTheory.ae_restrict_mem angSlot_Iθ_measurable] with θ hθ
    rcases eq_or_lt_of_le (angSlot_sin_two_nonneg hθ) with h0 | hpos
    · rw [← h0, angSlot_zero_rpow (ne_of_gt hQ), mul_zero]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg le_rfl q)
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hpos (Real.sin_le_one _) hq) (sq_nonneg _)
  have hnorm : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      ‖(iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) Q‖
        ≤ (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) q := by
    filter_upwards [hae, MeasureTheory.ae_restrict_mem angSlot_Iθ_measurable] with θ hle hθ
    have hnn : 0 ≤ (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) Q :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (angSlot_sin_two_nonneg hθ) Q)
    rw [Real.norm_of_nonneg hnn]
    exact hle
  have hIntQ : IntegrableOn
      (fun θ : ℝ => (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) Q)
        Work.Spaces.Iθ := hIntBig.mono' hsmQ hnorm
  exact ⟨hIntQ, integral_mono_ae hIntQ hIntBig hae⟩

/-! ## `AngRHS` unfolded -/

lemma angSlot_AngRHS_unfold (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) :
    AngRHS k γ u g
      = (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
            (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
        + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)))
        + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
        + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) := rfl

/-! ## The target -/

theorem angSlot_le_AngRHS (k : ℕ) (hk : 2 ≤ k) :
    ∀ (γ : ℝ) (u g : ℝ → ℝ),
      1 ≤ γ → γ ≤ 5 / 4 →
      ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv k g θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ →
      (∀ j ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn
          (fun θ => (iteratedDeriv j u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)) Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      ∀ j : ℕ, j ≤ k + 1 →
        MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv j u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
  intro γ u g _hγ1 hγ2 hu _hcont hInt_gk hInt_high hInt_2 hInt_1 hInt_0 j hj
  have hQpos : 0 < 2 * (k : ℝ) - γ := by
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => iteratedDeriv j u θ)
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
    angSlot_measurable_iteratedDeriv hu (by omega)
  -- nonnegativity of the four remaining components of `AngRHS`
  have hnn1 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
    setIntegral_nonneg angSlot_Iθ_measurable (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (angSlot_sin_two_nonneg hθ) _))
  have hnn2 : 0 ≤ ∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
      (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ) :=
    Finset.sum_nonneg (fun j _ => setIntegral_nonneg angSlot_Iθ_measurable (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (angSlot_sin_two_nonneg hθ) _)))
  have hnn3 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) :=
    setIntegral_nonneg angSlot_Iθ_measurable (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (angSlot_sin_two_nonneg hθ) _))
  have hnn4 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
    setIntegral_nonneg angSlot_Iθ_measurable (fun θ _ => sq_nonneg _)
  have hnn5 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
    setIntegral_nonneg angSlot_Iθ_measurable (fun θ _ => sq_nonneg _)
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j by omega) with rfl | rfl | rfl | hj3
  · -- `j = 0`: the slot is dominated by `∫ u²`
    have hbig : IntegrableOn (fun θ : ℝ => (iteratedDeriv 0 u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (0 : ℝ)) Work.Spaces.Iθ := by
      simpa only [iteratedDeriv_zero, angSlot_rpow_zero, mul_one] using hInt_0
    obtain ⟨hInt, hle⟩ := angSlot_weight_mono hQpos
      (by linarith : (0 : ℝ) ≤ 2 * (k : ℝ) - γ) 0 hmeas hbig
    rw [angSlot_itd0_mul_rpow_zero u] at hle
    refine ⟨hInt, le_trans hle ?_⟩
    rw [angSlot_AngRHS_unfold]
    linarith [hnn1, hnn2, hnn3, hnn4]
  · -- `j = 1`: the slot is dominated by `∫ u'²`
    have hbig : IntegrableOn (fun θ : ℝ => (iteratedDeriv 1 u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (0 : ℝ)) Work.Spaces.Iθ := by
      simpa only [iteratedDeriv_one, angSlot_rpow_zero, mul_one] using hInt_1
    obtain ⟨hInt, hle⟩ := angSlot_weight_mono hQpos
      (by linarith : (0 : ℝ) ≤ 2 * (k : ℝ) - γ) 1 hmeas hbig
    rw [angSlot_itd1_mul_rpow_zero u] at hle
    refine ⟨hInt, le_trans hle ?_⟩
    rw [angSlot_AngRHS_unfold]
    linarith [hnn1, hnn2, hnn3, hnn5]
  · -- `j = 2`: the slot is dominated by `∫ u''² sin(2θ)^{-η}`
    have hbig : IntegrableOn (fun θ : ℝ => (iteratedDeriv 2 u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
      simpa only [angSlot_iteratedDeriv_two] using hInt_2
    obtain ⟨hInt, hle⟩ := angSlot_weight_mono hQpos
      (by linarith [hQpos, Work.Spaces.eta_pos] : -(Work.Spaces.eta) ≤ 2 * (k : ℝ) - γ)
      2 hmeas hbig
    rw [angSlot_itd2_mul_rpow u (-(Work.Spaces.eta))] at hle
    refine ⟨hInt, le_trans hle ?_⟩
    rw [angSlot_AngRHS_unfold]
    linarith [hnn1, hnn2, hnn4, hnn5]
  · -- `3 ≤ j`: the slot is one summand of the `j`-sum of `AngRHS`
    have hjmem : j ∈ Finset.Icc 3 (k + 1) := Finset.mem_Icc.mpr ⟨hj3, hj⟩
    have hq : 2 * (j : ℝ) - 4 - γ ≤ 2 * (k : ℝ) - γ := by
      have hjle : (j : ℝ) ≤ (k : ℝ) + 2 := by
        exact_mod_cast (show j ≤ k + 2 by omega)
      linarith
    obtain ⟨hInt, hle⟩ := angSlot_weight_mono hQpos hq j hmeas (hInt_high j hjmem)
    have hsum : (∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
        ≤ ∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
            (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ) :=
      Finset.single_le_sum
        (s := Finset.Icc 3 (k + 1))
        (f := fun i => ∫ θ in Work.Spaces.Iθ, (iteratedDeriv i u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (i : ℝ) - 4 - γ))
        (fun i _ => setIntegral_nonneg angSlot_Iθ_measurable (fun θ hθ =>
          mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (angSlot_sin_two_nonneg hθ) _))) hjmem
    refine ⟨hInt, le_trans hle (le_trans hsum ?_)⟩
    rw [angSlot_AngRHS_unfold]
    linarith [hnn1, hnn3, hnn4, hnn5]

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice_ang_asm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Assembly lemmas for `slice_ang_gen`

See `NOTES_slice_ang_v_bound.md`.  The target `remov/slice_ang_gen` is reduced to

* `ang_ode_iterate` (proved): `∂^{k+1}(tan θ·u) = u^{(k+2)} + 6u^{(k)} + g^{(k)}`;
* `slice_ang_A_le` (proved): the pairing `A = ∫∂^{k+1}(tan θ·u)u^{(k+2)}q` satisfies
  `A ≤ ½∫(u^{(k+2)})²q + C·R`, given the weighted `v = u/cos θ` bounds
  `∫(v^{(m)})²q ≤ CK·R`, `m ≤ k+1`;
* the weighted `v`-bounds themselves: `slice_ang_v_outer` / `slice_ang_v_far`.

This file contains the elementary bookkeeping: the pointwise AM–GM, the nonnegativity of `AngRHS`,
the splitting of an `Iθ`-integral into the outer and far windows, the reduction
`∫(u^{(k)})²q ≤ AngRHS`, and the final combination.
-/

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

lemma sin_two_nonneg_Iθ_asm {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- The full hypothesis bundle of the target `slice_ang_gen` (`k` is the fixed order). -/
def SliceHyp (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) : Prop :=
  1 ≤ γ ∧ γ ≤ 5 / 4
    ∧ ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2))
    ∧ ContinuousOn u (Set.Icc 0 (Real.pi / 2))
    ∧ u 0 = 0 ∧ u (Real.pi / 2) = 0
    ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ)
    ∧ MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv (k + 2) u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv k g θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ
    ∧ (∀ j ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn
        (fun θ => (iteratedDeriv j u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)) Work.Spaces.Iθ)
    ∧ MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) Work.Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ

lemma Iθ_measurable_asm : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc

/-- Each of the last four terms of `AngRHS` is nonnegative. -/
lemma angRHS_rest_nonneg (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) :
    (0 ≤ ∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
    ∧ (0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)))
    ∧ (0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
    ∧ (0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) := by
  refine ⟨Finset.sum_nonneg fun j _ => ?_, ?_, ?_, ?_⟩
  · exact MeasureTheory.setIntegral_nonneg Iθ_measurable_asm
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_asm hθ) _))
  · exact MeasureTheory.setIntegral_nonneg Iθ_measurable_asm
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_asm hθ) _))
  · exact MeasureTheory.setIntegral_nonneg Iθ_measurable_asm (fun θ _ => sq_nonneg _)
  · exact MeasureTheory.setIntegral_nonneg Iθ_measurable_asm (fun θ _ => sq_nonneg _)


/-- The `g^{(k)}`-slot is dominated by `AngRHS`. -/
lemma g_slot_le_angRHS (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) ≤ AngRHS k γ u g := by
  obtain ⟨hB, hC, hD, hE⟩ := angRHS_rest_nonneg k γ u g
  unfold AngRHS
  linarith

/-- Splitting an `Iθ`-integral over the outer and far windows. -/
lemma integral_split_Iθ (f : ℝ → ℝ)
    (h1 : MeasureTheory.IntegrableOn f (Set.Icc 0 (3 * Real.pi / 8)))
    (h2 : MeasureTheory.IntegrableOn f (Set.Icc (3 * Real.pi / 8) (Real.pi / 2))) :
    (∫ θ in Work.Spaces.Iθ, f θ)
      = (∫ θ in Set.Icc 0 (3 * Real.pi / 8), f θ)
        + (∫ θ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2), f θ) := by
  have h3 : (0 : ℝ) ≤ 3 * Real.pi / 8 := by positivity
  have h3' : 3 * Real.pi / 8 ≤ Real.pi / 2 := by
    have := Real.pi_pos; linarith
  have hsub1 : Set.Icc (0 : ℝ) (3 * Real.pi / 8) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨hx.1, le_trans hx.2 h3'⟩
  have hsub2 : Set.Icc (3 * Real.pi / 8) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_trans h3 hx.1, hx.2⟩
  have hU : Set.Icc (0 : ℝ) (3 * Real.pi / 8) ∪ Set.Icc (3 * Real.pi / 8) (Real.pi / 2)
      = Work.Spaces.Iθ := by
    ext x; constructor
    · rintro (hx | hx)
      · exact ⟨hx.1, le_trans hx.2 h3'⟩
      · exact ⟨le_trans h3 hx.1, hx.2⟩
    · intro hx
      rcases le_total x (3 * Real.pi / 8) with h | h
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr ⟨h, hx.2⟩
  have hdisj : MeasureTheory.AEDisjoint MeasureTheory.volume
      (Set.Icc (0 : ℝ) (3 * Real.pi / 8)) (Set.Icc (3 * Real.pi / 8) (Real.pi / 2)) := by
    show MeasureTheory.volume (Set.Icc (0 : ℝ) (3 * Real.pi / 8)
      ∩ Set.Icc (3 * Real.pi / 8) (Real.pi / 2)) = 0
    refine MeasureTheory.measure_mono_null (t := ({3 * Real.pi / 8} : Set ℝ))
      (fun x hx => ?_) (Real.volume_singleton (a := 3 * Real.pi / 8))
    rw [Set.mem_inter_iff] at hx
    exact le_antisymm hx.1.2 hx.2.1
  rw [← hU]
  exact MeasureTheory.setIntegral_union₀ hdisj (measurableSet_Icc.nullMeasurableSet) h1 h2

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.zHardyAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary continuity facts on `[a,b] ⊆ (0,∞)` -/






/-! ## The finite-interval inequality -/


/-! ## The boundary term at `0` along dyadic annuli -/

theorem zHardy_seq_bot (H : ℝ → ℝ) (hH : IntegrableOn H (Set.Ioc (0:ℝ) 1))
    (hHnn : ∀ z, 0 ≤ H z)
    (hcont : ∀ k : ℕ, ContinuousOn H (Set.Icc ((1/2:ℝ) ^ (k + 1)) ((1/2:ℝ) ^ k))) :
    ∃ ε : ℕ → ℝ,
      (∀ k, ε k ∈ Set.Icc ((1/2:ℝ) ^ (k + 1)) ((1/2:ℝ) ^ k)) ∧
        Tendsto ε atTop (𝓝 0) ∧
        Tendsto (fun k => H (ε k) * ε k) atTop (𝓝 0) := by
  have hle : ∀ k : ℕ, (1/2:ℝ) ^ (k + 1) ≤ (1/2:ℝ) ^ k := by
    intro k
    have h0 : (0:ℝ) < (1/2:ℝ) ^ k := by positivity
    rw [pow_succ]
    nlinarith
  have hmin : ∀ k : ℕ, ∃ x : ℝ, x ∈ Set.Icc ((1/2:ℝ) ^ (k + 1)) ((1/2:ℝ) ^ k) ∧
      ∀ y ∈ Set.Icc ((1/2:ℝ) ^ (k + 1)) ((1/2:ℝ) ^ k), H x ≤ H y := by
    intro k
    obtain ⟨x, hx, hxm⟩ := isCompact_Icc.exists_isMinOn
      ⟨_, Set.left_mem_Icc.mpr (hle k)⟩ (hcont k)
    exact ⟨x, hx, fun y hy => isMinOn_iff.mp hxm y hy⟩
  choose x hxmem hxmin using hmin
  have htail : Tendsto (fun k : ℕ => ∫ z in Set.Ioc (0:ℝ) ((1/2:ℝ) ^ k), H z) atTop (𝓝 0) := by
    have hanti : Antitone (fun k : ℕ => Set.Ioc (0:ℝ) ((1/2:ℝ) ^ k)) := by
      intro a b hab
      exact Set.Ioc_subset_Ioc_right (pow_le_pow_of_le_one (by norm_num) (by norm_num) hab)
    have hInter : (⋂ k : ℕ, Set.Ioc (0:ℝ) ((1/2:ℝ) ^ k)) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
      have hzk : ∀ k : ℕ, z ∈ Set.Ioc (0:ℝ) ((1/2:ℝ) ^ k) := fun k => Set.mem_iInter.mp hz k
      have hpos : 0 < z := (hzk 0).1
      have ht : Tendsto (fun k : ℕ => (1/2:ℝ) ^ k) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have hzle : z ≤ 0 := ge_of_tendsto ht (Eventually.of_forall fun k => (hzk k).2)
      linarith
    have h := tendsto_setIntegral_of_antitone (μ := volume) (f := H)
      (s := fun k : ℕ => Set.Ioc (0:ℝ) ((1/2:ℝ) ^ k))
      (fun k => measurableSet_Ioc) hanti ⟨0, by simpa using hH⟩
    simpa only [hInter, setIntegral_empty] using h
  refine ⟨x, hxmem, ?_, ?_⟩
  · refine squeeze_zero
      (fun k => le_of_lt (lt_of_lt_of_le (by positivity) (Set.mem_Icc.mp (hxmem k)).1))
      (fun k => (Set.mem_Icc.mp (hxmem k)).2) ?_
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  · have hbnd : ∀ k : ℕ, H (x k) * x k ≤ 2 * (∫ z in Set.Ioc (0:ℝ) ((1/2:ℝ) ^ k), H z) :=
      fun k => by
      have hxle : x k ≤ (1/2:ℝ) ^ k := (Set.mem_Icc.mp (hxmem k)).2
      have hHx : 0 ≤ H (x k) := hHnn _
      have h1 : H (x k) * x k ≤ 2 * (H (x k) * ((1/2:ℝ) ^ k - (1/2:ℝ) ^ (k + 1))) := by
        have hb : ((1/2:ℝ) ^ k - (1/2:ℝ) ^ (k + 1)) * 2 = (1/2:ℝ) ^ k := by
          rw [pow_succ]; ring
        calc H (x k) * x k ≤ H (x k) * ((1/2:ℝ) ^ k) := mul_le_mul_of_nonneg_left hxle hHx
          _ = 2 * (H (x k) * ((1/2:ℝ) ^ k - (1/2:ℝ) ^ (k + 1))) := by rw [← hb]; ring
      have h3 : H (x k) * ((1/2:ℝ) ^ k - (1/2:ℝ) ^ (k + 1))
          ≤ ∫ y in (1/2:ℝ) ^ (k + 1)..(1/2:ℝ) ^ k, H y := by
        have hci : IntervalIntegrable H volume ((1/2:ℝ) ^ (k + 1)) ((1/2:ℝ) ^ k) := by
          apply ContinuousOn.intervalIntegrable
          rw [Set.uIcc_of_le (hle k)]
          exact hcont k
        have h := intervalIntegral.integral_mono_on (hle k)
          (intervalIntegrable_const (c := H (x k))) hci (fun y hy => hxmin k y hy)
        rw [intervalIntegral.integral_const] at h
        calc H (x k) * ((1/2:ℝ) ^ k - (1/2:ℝ) ^ (k + 1))
            = ((1/2:ℝ) ^ k - (1/2:ℝ) ^ (k + 1)) * H (x k) := by ring
          _ ≤ ∫ y in (1/2:ℝ) ^ (k + 1)..(1/2:ℝ) ^ k, H y := h
      have h4 : ∫ y in (1/2:ℝ) ^ (k + 1)..(1/2:ℝ) ^ k, H y
          ≤ ∫ y in Set.Ioc (0:ℝ) ((1/2:ℝ) ^ k), H y := by
        rw [intervalIntegral.integral_of_le (hle k)]
        refine setIntegral_mono_set ?_ ?_ ?_
        · refine hH.mono_set fun y hy => ⟨hy.1, ?_⟩
          exact le_trans hy.2 (pow_le_one₀ (by norm_num) (by norm_num))
        · exact Eventually.of_forall hHnn
        · exact Eventually.of_forall fun y hy => ⟨lt_of_lt_of_le (by positivity) hy.1.le, hy.2⟩
      exact le_trans h1
        (le_trans (mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 2))
          (mul_le_mul_of_nonneg_left h4 (by norm_num : (0:ℝ) ≤ 2)))
    have htend : Tendsto (fun k : ℕ => 2 * (∫ z in Set.Ioc (0:ℝ) ((1/2:ℝ) ^ k), H z))
        atTop (𝓝 0) := by
      simpa using htail.const_mul 2
    exact squeeze_zero
      (fun k => mul_nonneg (hHnn _)
        (le_of_lt (lt_of_lt_of_le (by positivity) (Set.mem_Icc.mp (hxmem k)).1)))
      hbnd htend

/-! ## The boundary term at `∞` along `[k+1, 2k+2]` -/

theorem zHardy_seq_top (H : ℝ → ℝ) (hH : IntegrableOn H (Set.Ioi (1:ℝ)))
    (hHnn : ∀ z, 0 ≤ H z)
    (hcont : ∀ k : ℕ, ContinuousOn H (Set.Icc ((k:ℝ) + 1) (2 * ((k:ℝ) + 1)))) :
    ∃ M : ℕ → ℝ,
      (∀ k : ℕ, M k ∈ Set.Icc ((k:ℝ) + 1) (2 * ((k:ℝ) + 1))) ∧
        Tendsto M atTop atTop ∧
        Tendsto (fun k => H (M k) * M k) atTop (𝓝 0) := by
  have hle : ∀ k : ℕ, (k:ℝ) + 1 ≤ 2 * ((k:ℝ) + 1) := by
    intro k
    have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  have hmin : ∀ k : ℕ, ∃ x : ℝ, x ∈ Set.Icc ((k:ℝ) + 1) (2 * ((k:ℝ) + 1)) ∧
      ∀ y ∈ Set.Icc ((k:ℝ) + 1) (2 * ((k:ℝ) + 1)), H x ≤ H y := by
    intro k
    obtain ⟨x, hx, hxm⟩ := isCompact_Icc.exists_isMinOn
      ⟨_, Set.left_mem_Icc.mpr (hle k)⟩ (hcont k)
    exact ⟨x, hx, fun y hy => isMinOn_iff.mp hxm y hy⟩
  choose x hxmem hxmin using hmin
  have htail : Tendsto (fun k : ℕ => ∫ z in Set.Ioi ((k:ℝ) + 1), H z) atTop (𝓝 0) := by
    have hanti : Antitone (fun k : ℕ => Set.Ioi ((k:ℝ) + 1)) := by
      intro a b hab
      exact Set.Ioi_subset_Ioi (by
        have : (a:ℝ) ≤ (b:ℝ) := Nat.cast_le.mpr hab
        linarith)
    have hInter : (⋂ k : ℕ, Set.Ioi ((k:ℝ) + 1)) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
      have hzk : ∀ k : ℕ, z ∈ Set.Ioi ((k:ℝ) + 1) := fun k => Set.mem_iInter.mp hz k
      have h0 : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      have ht : Tendsto (fun k : ℕ => ((k:ℝ) + 1)) atTop atTop := by
        simpa using tendsto_atTop_add_const_right atTop (1:ℝ) h0
      have hev : ∀ᶠ k : ℕ in atTop, z < (k:ℝ) + 1 := ht.eventually_gt_atTop z
      obtain ⟨n, hn⟩ := eventually_atTop.mp hev
      have h1 : (n:ℝ) + 1 < z := hzk n
      have h2 : z < (n:ℝ) + 1 := hn n le_rfl
      linarith
    have h := tendsto_setIntegral_of_antitone (μ := volume) (f := H)
      (s := fun k : ℕ => Set.Ioi ((k:ℝ) + 1)) (fun k => measurableSet_Ioi) hanti
      ⟨0, by simpa using hH⟩
    simpa only [hInter, setIntegral_empty] using h
  refine ⟨x, hxmem, ?_, ?_⟩
  · refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
    have := (Set.mem_Icc.mp (hxmem k)).1
    linarith
  · refine squeeze_zero
      (fun k => mul_nonneg (hHnn _) (by
        have := (Set.mem_Icc.mp (hxmem k)).1
        have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        linarith))
      (fun k => ?_) (by simpa using htail.const_mul 2)
    have hxle : x k ≤ 2 * ((k:ℝ) + 1) := (Set.mem_Icc.mp (hxmem k)).2
    have hHx : 0 ≤ H (x k) := hHnn _
    have h1 : H (x k) * x k ≤ 2 * (H (x k) * (2 * ((k:ℝ) + 1) - ((k:ℝ) + 1))) := by
      calc H (x k) * x k ≤ H (x k) * (2 * ((k:ℝ) + 1)) := mul_le_mul_of_nonneg_left hxle hHx
        _ = 2 * (H (x k) * (2 * ((k:ℝ) + 1) - ((k:ℝ) + 1))) := by ring
    have h3 : H (x k) * (2 * ((k:ℝ) + 1) - ((k:ℝ) + 1))
        ≤ ∫ y in ((k:ℝ) + 1)..(2 * ((k:ℝ) + 1)), H y := by
      have hci : IntervalIntegrable H volume ((k:ℝ) + 1) (2 * ((k:ℝ) + 1)) := by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le (hle k)]
        exact hcont k
      have h := intervalIntegral.integral_mono_on (hle k)
        (intervalIntegrable_const (c := H (x k))) hci (fun y hy => hxmin k y hy)
      rw [intervalIntegral.integral_const] at h
      calc H (x k) * (2 * ((k:ℝ) + 1) - ((k:ℝ) + 1))
          = (2 * ((k:ℝ) + 1) - ((k:ℝ) + 1)) * H (x k) := by ring
        _ ≤ ∫ y in ((k:ℝ) + 1)..(2 * ((k:ℝ) + 1)), H y := h
    have h4 : ∫ y in ((k:ℝ) + 1)..(2 * ((k:ℝ) + 1)), H y
        ≤ ∫ y in Set.Ioi ((k:ℝ) + 1), H y := by
      rw [intervalIntegral.integral_of_le (hle k)]
      refine setIntegral_mono_set ?_ ?_ ?_
      · refine hH.mono_set fun y hy => ?_
        have hy' : (k:ℝ) + 1 < y := hy
        have hk : (1:ℝ) ≤ (k:ℝ) + 1 := by
          have h0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
          linarith
        exact lt_of_le_of_lt hk hy'
      · exact Eventually.of_forall hHnn
      · exact Eventually.of_forall fun y hy => hy.1
    exact le_trans h1
      (le_trans (mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_left h4 (by norm_num : (0:ℝ) ≤ 2)))

/-! ## Convergence of the truncated integrals -/

theorem zHardy_tendsto_setIntegral_Ioc (G : ℝ → ℝ) (hG : IntegrableOn G (Set.Ioi (0:ℝ)))
    {ε M : ℕ → ℝ} (hε0 : ∀ k, 0 < ε k)
    (hε : Tendsto ε atTop (𝓝 0)) (hM : Tendsto M atTop atTop) :
    Tendsto (fun k => ∫ z in Set.Ioc (ε k) (M k), G z) atTop
      (𝓝 (∫ z in Set.Ioi (0:ℝ), G z)) := by
  have hGind : Integrable ((Set.Ioi (0:ℝ)).indicator G) volume :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hG
  have hmain : Tendsto (fun k : ℕ => ∫ z, (Set.Ioc (ε k) (M k)).indicator G z) atTop
      (𝓝 (∫ z, (Set.Ioi (0:ℝ)).indicator G z)) := by
    refine tendsto_integral_of_dominated_convergence (μ := volume)
      (bound := fun z => ‖(Set.Ioi (0:ℝ)).indicator G z‖)
      (F := fun k z => (Set.Ioc (ε k) (M k)).indicator G z)
      (f := fun z => (Set.Ioi (0:ℝ)).indicator G z) ?_ hGind.norm ?_ ?_
    · intro k
      have h1 : AEStronglyMeasurable
          (fun z : ℝ => (Set.Ioc (ε k) (M k)).indicator ((Set.Ioi (0:ℝ)).indicator G) z)
          volume := hGind.aestronglyMeasurable.indicator measurableSet_Ioc
      refine h1.congr ?_
      filter_upwards with z
      by_cases hz : z ∈ Set.Ioc (ε k) (M k)
      · have hz0 : z ∈ Set.Ioi (0:ℝ) := lt_trans (hε0 k) hz.1
        simp only [Set.indicator_of_mem hz, Set.indicator_of_mem hz0]
      · simp only [Set.indicator_of_notMem hz]
    · intro k
      filter_upwards with z
      by_cases hz : z ∈ Set.Ioc (ε k) (M k)
      · have hz0 : z ∈ Set.Ioi (0:ℝ) := lt_trans (hε0 k) hz.1
        rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz0]
      · rw [Set.indicator_of_notMem hz, norm_zero]
        exact norm_nonneg _
    · filter_upwards with z
      by_cases hz0 : z ∈ Set.Ioi (0:ℝ)
      · have hev1 : ∀ᶠ k : ℕ in atTop, ε k < z :=
          hε (isOpen_Iio.mem_nhds (show (0:ℝ) ∈ Set.Iio z from hz0))
        have hev2 : ∀ᶠ k : ℕ in atTop, z < M k := hM (Ioi_mem_atTop z)
        refine (tendsto_const_nhds (x := (Set.Ioi (0:ℝ)).indicator G z)).congr' ?_
        filter_upwards [hev1, hev2] with k h1 h2
        rw [Set.indicator_of_mem (show z ∈ Set.Ioc (ε k) (M k) from ⟨h1, le_of_lt h2⟩),
          Set.indicator_of_mem hz0]
      · have hev : ∀ᶠ k : ℕ in atTop,
            (Set.Ioi (0:ℝ)).indicator G z = (Set.Ioc (ε k) (M k)).indicator G z := by
          filter_upwards with k
          rw [Set.indicator_of_notMem hz0,
            Set.indicator_of_notMem (fun h => hz0 (lt_trans (hε0 k) h.1))]
        exact (tendsto_const_nhds (x := (Set.Ioi (0:ℝ)).indicator G z)).congr' hev
  have h1 : ∀ k : ℕ, (∫ z, (Set.Ioc (ε k) (M k)).indicator G z)
      = ∫ z in Set.Ioc (ε k) (M k), G z := fun k =>
    MeasureTheory.integral_indicator measurableSet_Ioc
  have h2 : (∫ z, (Set.Ioi (0:ℝ)).indicator G z) = ∫ z in Set.Ioi (0:ℝ), G z :=
    MeasureTheory.integral_indicator measurableSet_Ioi
  rw [funext h1, h2] at hmain
  exact hmain

/-! ## Smoothness of the iterates of `rDz` -/


end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.H2.IBPWeight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The angular-slice differentiability of a `SmoothNbhd` function at interior points. -/
theorem differentiableAt_slice (v : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd v) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) : DifferentiableAt ℝ (fun θ' => v z θ') θ :=
  Work.Coercivity.smoothNbhd_slice_differentiableAt v hsm hz hθ



end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.STIbp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000



end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.Transport3Aux.HW.hardy_half_a_weak =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `sin(2θ)`-weighted Hardy inequality on `[0,π/4]`, weak hypotheses

The statement is the one of `Work.FTS.H2.Transport3Aux.hardy_half_a`, but the function `f` is
only assumed to be continuous on `[0,π/2]` and differentiable on the *open* interval, with a
bounded derivative there (`|f'| ≤ C`); no continuity of `f'` is required.

The proof is the one of `hardy_half_a`: the power-weighted Hardy inequality with boundary term
`Work.FTS.H2.Transport3Aux.hardy_power_weak` (proved in `num_int_1d_aux` for exactly these weak
hypotheses), together with Jordan's inequality `(4/π)θ ≤ sin(2θ) ≤ 1` on `[0,π/4]`.  The only
extra input needed is that `θ ↦ (deriv f θ)^2 * w(θ)` is interval integrable for the two weights
`w = θ^{β+1}` and `w = sin(2θ)^{1-β}`, which follows by domination since `deriv f` is measurable
(`measurable_deriv`) and bounded on the open interval.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Transport3Aux.HW

set_option maxHeartbeats 1000000



end Work.FTS.H2.Transport3Aux.HW
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP26.BangDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter

namespace Work.FTS.Nonlinear.Pieces.RNP26

set_option autoImplicit false

/-- The `i`-th angular polynomial `Bᵢ(x,α)` of the `θ`-calculation for `ψ = sin²θ·Γ`,
`i ≤ 4` (written in the split form `4x(1-x)Vᵢ + ∑_{k≥1}(α/3)^k P_{i,k}`). -/
def Bang (i : ℕ) : ℝ → ℝ → ℝ := fun x α =>
  match i with
  | 0 => 1 - x
  | 1 => 4 * x * (1 - x) * 1
      + (α / 3) * (-4 + 10 * x - 6 * x ^ 2)
  | 2 => 4 * x * (1 - x) * (-4 + 8 * x)
      + (α / 3) * (-56 * x + 128 * x ^ 2 - 72 * x ^ 3)
      + (α / 3) ^ 2 * (16 - 64 * x + 84 * x ^ 2 - 36 * x ^ 3)
  | 3 => 4 * x * (1 - x) * (16 - 96 * x + 96 * x ^ 2)
      + (α / 3) * (288 * x - 1536 * x ^ 2 + 2304 * x ^ 3 - 1056 * x ^ 4)
      + (α / 3) ^ 2 * (480 * x - 1776 * x ^ 2 + 2160 * x ^ 3 - 864 * x ^ 4)
      + (α / 3) ^ 3 * (-64 + 352 * x - 720 * x ^ 2 + 648 * x ^ 3 - 216 * x ^ 4)
  | 4 => 4 * x * (1 - x) * (-64 + 896 * x - 2304 * x ^ 2 + 1536 * x ^ 3)
      + (α / 3) * (-1408 * x + 15616 * x ^ 2 - 45696 * x ^ 3 + 50688 * x ^ 4 - 19200 * x ^ 5)
      + (α / 3) ^ 2 * (-3072 * x + 24000 * x ^ 2 - 58560 * x ^ 3 + 57792 * x ^ 4 - 20160 * x ^ 5)
      + (α / 3) ^ 3 * (-3328 * x + 17152 * x ^ 2 - 32832 * x ^ 3 + 27648 * x ^ 4 - 8640 * x ^ 5)
      + (α / 3) ^ 4 * (256 - 1792 * x + 4992 * x ^ 2 - 6912 * x ^ 3 + 4752 * x ^ 4 - 1296 * x ^ 5)
  | _ => 0

@[simp] theorem Bang_zero (x α : ℝ) : Bang 0 x α = 1 - x := rfl

@[simp] theorem Bang_one (x α : ℝ) : Bang 1 x α =
    4 * x * (1 - x) * 1 + (α / 3) * (-4 + 10 * x - 6 * x ^ 2) := rfl

@[simp] theorem Bang_two (x α : ℝ) : Bang 2 x α =
    4 * x * (1 - x) * (-4 + 8 * x)
      + (α / 3) * (-56 * x + 128 * x ^ 2 - 72 * x ^ 3)
      + (α / 3) ^ 2 * (16 - 64 * x + 84 * x ^ 2 - 36 * x ^ 3) := rfl

@[simp] theorem Bang_three (x α : ℝ) : Bang 3 x α =
    4 * x * (1 - x) * (16 - 96 * x + 96 * x ^ 2)
      + (α / 3) * (288 * x - 1536 * x ^ 2 + 2304 * x ^ 3 - 1056 * x ^ 4)
      + (α / 3) ^ 2 * (480 * x - 1776 * x ^ 2 + 2160 * x ^ 3 - 864 * x ^ 4)
      + (α / 3) ^ 3 * (-64 + 352 * x - 720 * x ^ 2 + 648 * x ^ 3 - 216 * x ^ 4) := rfl

@[simp] theorem Bang_four (x α : ℝ) : Bang 4 x α =
    4 * x * (1 - x) * (-64 + 896 * x - 2304 * x ^ 2 + 1536 * x ^ 3)
      + (α / 3) * (-1408 * x + 15616 * x ^ 2 - 45696 * x ^ 3 + 50688 * x ^ 4 - 19200 * x ^ 5)
      + (α / 3) ^ 2 * (-3072 * x + 24000 * x ^ 2 - 58560 * x ^ 3 + 57792 * x ^ 4 - 20160 * x ^ 5)
      + (α / 3) ^ 3 * (-3328 * x + 17152 * x ^ 2 - 32832 * x ^ 3 + 27648 * x ^ 4 - 8640 * x ^ 5)
      + (α / 3) ^ 4 * (256 - 1792 * x + 4992 * x ^ 2 - 6912 * x ^ 3 + 4752 * x ^ 4
          - 1296 * x ^ 5) := rfl

/-- The polynomials `Bᵢ` (`i ≤ 4`) are differentiable. -/
theorem differentiable_Bang (j : ℕ) (hj : j ≤ 4) (α : ℝ) :
    Differentiable ℝ (fun y : ℝ => Bang j y α) := by
  interval_cases j
  · simp only [Bang_zero]; fun_prop
  · simp only [Bang_one]; fun_prop
  · simp only [Bang_two]; fun_prop
  · simp only [Bang_three]; fun_prop
  · simp only [Bang_four]; fun_prop

/-- The recurrence `Bᵢ₊₁ = -4x(1-x)Bᵢ' + (α/3)(6x-4)Bᵢ` for `i ≤ 3`, in the exact shape
produced by `Work.Construction.glop_step`. -/
theorem bang_succ (j : ℕ) (hj : j ≤ 3) (x α : ℝ) :
    -4 * x * (1 - x) * deriv (fun y : ℝ => Bang j y α) x
      + (α / 3) * (6 * x - 4) * Bang j x α = Bang (j + 1) x α := by
  interval_cases j
  · have h : (fun y : ℝ => Bang 0 y α)
        = fun y : ℝ => 1 + (-1) * y + 0 * y ^ 2 + 0 * y ^ 3 + 0 * y ^ 4 + 0 * y ^ 5 := by
      funext y
      simp only [Bang_zero]
      ring
    rw [h, Work.Construction.deriv_mono5, Bang_one, Bang_zero]
    ring
  · have h : (fun y : ℝ => Bang 1 y α)
        = fun y : ℝ => (-(4 : ℝ) * α / 3) + (4 + 10 * α / 3) * y
            + (-4 - 2 * α) * y ^ 2 + 0 * y ^ 3 + 0 * y ^ 4 + 0 * y ^ 5 := by
      funext y
      simp only [Bang_one]
      ring
    rw [h, Work.Construction.deriv_mono5, Bang_two, Bang_one]
    ring
  · have h : (fun y : ℝ => Bang 2 y α)
        = fun y : ℝ => (16 * α ^ 2 / 9) + (-16 - 56 * α / 3 - 64 * α ^ 2 / 9) * y
            + (48 + 128 * α / 3 + 28 * α ^ 2 / 3) * y ^ 2
            + (-32 - 24 * α - 4 * α ^ 2) * y ^ 3 + 0 * y ^ 4 + 0 * y ^ 5 := by
      funext y
      simp only [Bang_two]
      ring
    rw [h, Work.Construction.deriv_mono5, Bang_three, Bang_two]
    ring
  · have h : (fun y : ℝ => Bang 3 y α)
        = fun y : ℝ => (-(64 : ℝ) * α ^ 3 / 27)
            + (64 + 96 * α + 160 * α ^ 2 / 3 + 352 * α ^ 3 / 27) * y
            + (-448 - 512 * α - 592 * α ^ 2 / 3 - 80 * α ^ 3 / 3) * y ^ 2
            + (768 + 768 * α + 240 * α ^ 2 + 24 * α ^ 3) * y ^ 3
            + (-384 - 352 * α - 96 * α ^ 2 - 8 * α ^ 3) * y ^ 4 + 0 * y ^ 5 := by
      funext y
      simp only [Bang_three]
      ring
    rw [h, Work.Construction.deriv_mono5, Bang_four, Bang_three]
    ring

/-- `D_θ^i ψ(θ) = Γ(θ)·Bᵢ(cos²θ, α)` for `i ≤ 4` and `θ ∈ (0,π/2)`, where
`ψ(θ) = sin²θ·Γ(θ)`. -/
theorem bang_iter (α : ℝ) (hα : 0 < α) (i : ℕ) (hi : i ≤ 4) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.Lop^[i] (fun θ : ℝ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ)) θ
        = Work.Spaces.Gam α θ * Bang i (Real.cos θ ^ 2) α := by
  induction i with
  | zero =>
      intro θ hθ
      simp only [Function.iterate_zero, id_eq, Bang_zero]
      rw [Real.sin_sq]
      ring
  | succ j ih =>
      intro θ hθ
      have hj : j ≤ 4 := le_trans (Nat.le_succ j) hi
      have hev : (Work.Spaces.Lop^[j] (fun θ : ℝ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ))
          =ᶠ[𝓝 θ] (fun y => Work.Spaces.Gam α y * Bang j (Real.cos y ^ 2) α) := by
        filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
        exact ih hj y hy
      rw [Function.iterate_succ_apply']
      rw [show Work.Spaces.Lop
            (Work.Spaces.Lop^[j] (fun θ : ℝ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ)) θ
          = Work.Spaces.Lop
              (fun y => Work.Spaces.Gam α y * Bang j (Real.cos y ^ 2) α) θ from by
        show Real.sin (2 * θ)
              * deriv (Work.Spaces.Lop^[j]
                  (fun θ : ℝ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ)) θ
            = Real.sin (2 * θ)
              * deriv (fun y => Work.Spaces.Gam α y * Bang j (Real.cos y ^ 2) α) θ
        rw [hev.deriv_eq]]
      rw [Work.Construction.glop_step α hα (fun y : ℝ => Bang j y α)
        (differentiable_Bang j hj α) θ hθ]
      rw [bang_succ j (by omega) (Real.cos θ ^ 2) α]

end Work.FTS.Nonlinear.Pieces.RNP26
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.PsiExpAux.MomentEqOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux.PsiExpAux

open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false

/-! ## Uniqueness of a `C⁰` function from its `eFam`-moments

The Dirichlet eigenfunctions `eFam n θ = cos θ · C^{(3/2)}_{2n+1}(sin θ)` of `Work.Elliptic.Lzero`
are complete with respect to the weight `cos θ dθ` on `Iθ = [0, π/2]`
(`Work.FTS.PhiStar.Gegenbauer.eFam_complete`): a function orthogonal to every `eFam n` vanishes
a.e.  Consequently two continuous functions with the same `eFam`-moments coincide.

The proof is soft.  Put `g := w - v`; then `g` is continuous on the compact `Iθ`, so it is a.e.
strongly measurable, `g ^ 2 * cos` is integrable on `Iθ`, and each `g * eFam n * cos` (as well as
the two pieces `w * eFam n * cos`, `v * eFam n * cos`) is integrable there.  Linearity of the
integral turns the agreement of the moments into `∫_{Iθ} g · eFam n · cos = 0` for every `n`, and
completeness gives `g =ᵐ 0`.  Since `g` is continuous and `Iθ ⊆ closure (interior Iθ)`
(`Iθ = [0, π/2]`, so `interior Iθ = (0, π/2)` and it is dense in `Iθ`), the a.e. equality upgrades
to the pointwise equality `g = 0` on `Iθ` (`Measure.eqOn_of_ae_eq`), in particular on `Ioo 0 π/2`.
-/

/-- `eFam m` is continuous on `ℝ`. -/
theorem continuous_eFam_psi (m : ℕ) :
    Continuous (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
  Real.continuous_cos.mul
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
      Real.continuous_sin)

theorem MomentEqOn (v w : ℝ → ℝ)
    (hv : ContinuousOn v (Set.Icc 0 (Real.pi / 2)))
    (hw : ContinuousOn w (Set.Icc 0 (Real.pi / 2)))
    (hmom : ∀ n : ℕ, (∫ θ in Work.Spaces.Iθ, w θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
        = ∫ θ in Work.Spaces.Iθ, v θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), w θ = v θ := by
  -- `g := w - v` is continuous on `Iθ`
  have hgcont : ContinuousOn (fun θ : ℝ => w θ - v θ) Work.Spaces.Iθ := hw.sub hv
  -- hence a.e. strongly measurable there
  have haesm : AEStronglyMeasurable (fun θ : ℝ => w θ - v θ)
      (volume.restrict Work.Spaces.Iθ) :=
    hgcont.aestronglyMeasurable measurableSet_Icc
  -- and `g ^ 2 * cos` is integrable on the compact `Iθ`
  have hint : IntegrableOn (fun θ : ℝ => (w θ - v θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
    ContinuousOn.integrableOn_compact isCompact_Icc
      ((hgcont.pow 2).mul Real.continuous_cos.continuousOn)
  -- the two pieces of a moment are integrable on `Iθ` (continuity on a compact set)
  have hintw : ∀ n : ℕ,
      Integrable (fun θ : ℝ => w θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
        (volume.restrict Work.Spaces.Iθ) := fun n =>
    ContinuousOn.integrableOn_compact isCompact_Icc
      ((hw.mul (continuous_eFam_psi n).continuousOn).mul Real.continuous_cos.continuousOn)
  have hintv : ∀ n : ℕ,
      Integrable (fun θ : ℝ => v θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
        (volume.restrict Work.Spaces.Iθ) := fun n =>
    ContinuousOn.integrableOn_compact isCompact_Icc
      ((hv.mul (continuous_eFam_psi n).continuousOn).mul Real.continuous_cos.continuousOn)
  -- the moments of `g` vanish, by linearity of the integral
  have hmom0 : ∀ n : ℕ,
      ∫ θ in Work.Spaces.Iθ,
          (w θ - v θ) * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ = 0 := by
    intro n
    have hsplit : (∫ θ in Work.Spaces.Iθ,
          (w θ - v θ) * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
        = ∫ θ in Work.Spaces.Iθ,
            (w θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ
              - v θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) :=
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    rw [hsplit, integral_sub (hintw n) (hintv n), hmom n, sub_self]
  -- completeness of the Dirichlet eigenbasis
  have hae := Work.FTS.PhiStar.Gegenbauer.eFam_complete (fun θ : ℝ => w θ - v θ)
    haesm hint hmom0
  -- a.e. equality of continuous functions upgrades to equality on the closed interval
  have hsub : Work.Spaces.Iθ ⊆ closure (interior Work.Spaces.Iθ) := by
    have hne : (0 : ℝ) ≠ Real.pi / 2 := by positivity
    change Set.Icc (0 : ℝ) (Real.pi / 2)
      ⊆ closure (interior (Set.Icc (0 : ℝ) (Real.pi / 2)))
    intro θ hθ
    rw [closure_interior_Icc hne]
    exact hθ
  have heqon : EqOn (fun θ : ℝ => w θ - v θ) (fun _ : ℝ => (0 : ℝ)) Work.Spaces.Iθ :=
    Measure.eqOn_of_ae_eq hae hgcont continuousOn_const hsub
  intro θ hθ
  have h0 : w θ - v θ = 0 := heqon (Set.Ioo_subset_Icc_self hθ)
  exact sub_eq_zero.mp h0

end

end Work.FTS.PhiStar.FlatWAux.PsiExpAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.TsumLopDerivU =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

open scoped Real Topology
open Filter

theorem TsumLopDerivU (c : ℕ → ℝ) (q : ℕ → ℝ → ℝ) (B : ℕ → ℝ)
    (hB0 : ∀ m : ℕ, 0 ≤ B m)
    (hcB : Summable fun m : ℕ => |c m| * B m)
    (hq : ∀ m : ℕ, ContDiffOn ℝ 8 (q m) (Set.Ioo 0 (Real.pi / 2)))
    (hqb : ∀ (m r : ℕ), r ≤ 8 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |iteratedDeriv r (q m) θ| ≤ B m) :
    ∀ i : ℕ, i ≤ 6 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.Lop^[i]) (deriv (fun θ' => ∑' m : ℕ, c m * q m θ')) θ
        = ∑' m : ℕ, c m * (Work.Spaces.Lop^[i]) (deriv (q m)) θ := by
  set F : ℝ → ℝ := fun θ' => ∑' m : ℕ, c m * q m θ' with hFdef
  have hU : IsOpen (Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioo
  have hqtr : (Real.pi / 4) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have key : ∀ i : ℕ, i ≤ 6 → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.Lop^[i]) (deriv F) θ
        = ∑' m, c m * (Work.Spaces.Lop^[i]) (deriv (q m)) θ := by
    intro i
    induction i with
    | zero =>
        intro _ θ hθ
        simp only [Function.iterate_zero_apply]
        have hd : HasDerivAt F (∑' m, c m * deriv (q m) θ) θ := by
          refine hasDerivAt_tsum_of_isPreconnected
            (u := fun m : ℕ => |c m| * B m)
            (g := fun m (y : ℝ) => c m * q m y)
            (g' := fun m (y : ℝ) => c m * deriv (q m) y)
            hcB hU isPreconnected_Ioo ?_ ?_ hqtr ?_ hθ
          · intro m y hy
            have hdiff : DifferentiableAt ℝ (q m) y :=
              ((hq m).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
            exact hdiff.hasDerivAt.const_mul (c m)
          · intro m y hy
            rw [Real.norm_eq_abs, abs_mul]
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            simpa only [iteratedDeriv_one] using hqb m 1 (by norm_num) y hy
          · refine Summable.of_norm_bounded hcB (fun m => ?_)
            rw [Real.norm_eq_abs, abs_mul]
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            simpa only [iteratedDeriv_zero] using hqb m 0 (by norm_num) (Real.pi / 4) hqtr
        rw [hd.deriv]
    | succ i ih =>
        intro hi6 θ hθ
        have hi5 : i ≤ 5 := by omega
        set a : ℝ := θ / 2 with hadef
        set b : ℝ := (θ + Real.pi / 2) / 2 with hbdef
        have ha : 0 < a := by rw [hadef]; linarith [hθ.1]
        have hab : a ≤ b := by rw [hadef, hbdef]; linarith [Real.pi_pos]
        have hb : b < Real.pi / 2 := by rw [hbdef]; linarith [hθ.2]
        have hθab : θ ∈ Set.Ioo a b := by
          constructor
          · rw [hadef]; linarith [hθ.1]
          · rw [hbdef]; linarith [hθ.2]
        have hsub : Set.Ioo a b ⊆ Set.Ioo 0 (Real.pi / 2) := fun y hy =>
          ⟨by linarith [hy.1], by linarith [hy.2, hb]⟩
        have hIH : ∀ y ∈ Set.Ioo a b,
            (Work.Spaces.Lop^[i]) (deriv F) y
              = ∑' m, c m * (Work.Spaces.Lop^[i]) (deriv (q m)) y :=
          fun y hy => ih (by omega) y (hsub hy)
        obtain ⟨Kv, K', hKv0, hK'0, hbnd⟩ :=
          TsumLopDerivAux.Lop_iter_deriv_bound q B hq hqb i 1 (by omega) (by omega) ha hab hb
        have hbval : ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Set.Icc a b →
            |(Work.Spaces.Lop^[i]) (deriv (q m)) θ'| ≤ Kv * B m := by
          intro m θ' hθ'
          simpa only [iteratedDeriv_one] using (hbnd m θ' hθ').1
        have hbnd' : ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Set.Icc a b →
            |deriv ((Work.Spaces.Lop^[i]) (deriv (q m))) θ'| ≤ K' * B m := by
          intro m θ' hθ'
          simpa only [iteratedDeriv_one] using (hbnd m θ' hθ').2
        have hderiv := TsumLopDerivAux.tsum_Lop_iter_deriv_hasDerivAt c q B hcB hq i (by omega)
          ha hab hb K' Kv hK'0 hKv0 hbnd' hbval θ hθab
        calc (Work.Spaces.Lop^[i + 1]) (deriv F) θ
            = Real.sin (2 * θ) * deriv ((Work.Spaces.Lop^[i]) (deriv F)) θ := by
                rw [show (Work.Spaces.Lop^[i + 1]) (deriv F)
                    = Work.Spaces.Lop ((Work.Spaces.Lop^[i]) (deriv F)) from
                      Function.iterate_succ_apply' Work.Spaces.Lop i (deriv F)]
                rfl
          _ = Real.sin (2 * θ)
                * deriv (fun y : ℝ => ∑' m, c m * (Work.Spaces.Lop^[i]) (deriv (q m)) y) θ := by
                congr 1
                exact Filter.EventuallyEq.deriv_eq (by
                  filter_upwards [isOpen_Ioo.mem_nhds hθab] with y hy
                  exact hIH y hy)
          _ = Real.sin (2 * θ)
                * (∑' m, c m * deriv ((Work.Spaces.Lop^[i]) (deriv (q m))) θ) := by
                rw [hderiv.deriv]
          _ = ∑' m, c m * (Real.sin (2 * θ)
                * deriv ((Work.Spaces.Lop^[i]) (deriv (q m))) θ) := by
                rw [← tsum_mul_left]
                exact tsum_congr fun m => by ring
          _ = ∑' m, c m * (Work.Spaces.Lop^[i + 1]) (deriv (q m)) θ := by
                refine tsum_congr fun m => ?_
                congr 1
                rw [show (Work.Spaces.Lop^[i + 1]) (deriv (q m))
                    = Work.Spaces.Lop ((Work.Spaces.Lop^[i]) (deriv (q m))) from
                      Function.iterate_succ_apply' Work.Spaces.Lop i (deriv (q m))]
                rfl
  intro i hi θ hθ
  simpa only [hFdef] using key i hi θ hθ

end Work.FTS.PhiStar.FlatWAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.SlotsZeroComplete =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- NOTE: `open scoped Real` is what makes the bare `π` in the statement below denote
-- `Real.pi` (the intended semantics; without it the statement does not even elaborate,
-- since the workspace sets `autoImplicit = false`).  It also matches `Work.Spaces.Iθ`,
-- which is defined as `Set.Icc 0 (π/2)` with `π = Real.pi`.
open scoped Real
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

theorem SlotsZeroComplete {Φ : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hInt : ∀ z, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => Φ z θ ^ 2 * Real.cos θ) Work.Spaces.Iθ)
    (hmom : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∀ m : ℕ, (∫ θ in Work.Spaces.Iθ,
        Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) = 0) :
    ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Φ z θ = 0 := by
  -- `Work.Spaces.Iθ` and `Ioo 0 (π/2)` are the two faces of the angular interval.
  have hIθ : Work.Spaces.Iθ = Set.Icc 0 (π / 2) := by simp only [Work.Spaces.Iθ]
  have hIoo : volume.restrict (Set.Ioo 0 (π / 2)) = volume.restrict Work.Spaces.Iθ := by
    rw [hIθ]
    exact MeasureTheory.restrict_Ioo_eq_restrict_Icc (μ := volume) (a := 0) (b := π / 2)
  -- Every `z`-slice of `Φ` is continuous on the open angular interval.
  have hslice : ∀ z, 0 < z → ContinuousOn (fun θ => Φ z θ) (Set.Ioo 0 (π / 2)) := by
    intro z hz
    exact hcont.comp ((continuous_const.prodMk continuous_id).continuousOn)
      (fun θ hθ => ⟨hz, hθ⟩)
  -- STEP 1.  For a.e. `z > 0` the whole `θ`-slice vanishes: the moment condition against the
  -- complete family `eFam` (completeness = `eFam_complete`) gives vanishing a.e. in `θ`, and the
  -- slice is continuous, so it vanishes everywhere on the open interval.
  have hgoodR : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      ∀ θ ∈ Set.Ioo 0 (π / 2), Φ z θ = 0 := by
    filter_upwards [hmom, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hmom_z hz
    have hcs := hslice z hz
    have hgm : AEStronglyMeasurable (fun θ => Φ z θ) (volume.restrict Work.Spaces.Iθ) := by
      rw [← hIoo]
      exact hcs.aestronglyMeasurable measurableSet_Ioo
    have hae : (fun θ => Φ z θ) =ᵐ[volume.restrict (Set.Ioo 0 (π / 2))] (fun _ => 0) := by
      rw [hIoo]
      exact Work.FTS.PhiStar.Gegenbauer.eFam_complete (fun θ => Φ z θ) hgm (hInt z hz) hmom_z
    intro θ hθ
    exact MeasureTheory.Measure.eqOn_Ioo_of_ae_eq volume hae hcs continuousOn_const hθ
  -- the same statement read on `volume` (with the `0 < z` hypothesis stated explicitly)
  have hgood : ∀ᵐ z ∂volume, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Φ z θ = 0 :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mp hgoodR
  -- STEP 2.  Upgrade a.e. `z` to every `z > 0` by joint continuity in `(z,θ)`.
  intro z hz θ hθ
  have hzcont : ContinuousOn (fun z' => Φ z' θ) (Set.Ioi 0) :=
    hcont.comp ((continuous_id.prodMk continuous_const).continuousOn)
      (fun z' hz' => ⟨hz', hθ⟩)
  have hgoodθ : ∀ᵐ z' ∂volume, z' ∈ Set.Ioi 0 → Φ z' θ = 0 := by
    filter_upwards [hgood] with z' hz' hzmem
    exact hz' hzmem θ hθ
  have hae : (fun z' => Φ z' θ) =ᵐ[volume.restrict (Set.Ioi 0)] (fun _ => 0) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr hgoodθ
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae isOpen_Ioi hzcont continuousOn_const hz

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.HQoAux.integral_sq_basis_second_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongEps.HQoAux

theorem integral_sq_basis_second_le {G : ℝ → ℝ → ℝ} {a b c d C K : ℝ}
    (h₁ : MeasureTheory.IntegrableOn (fun x : ℝ × ℝ => (Work.Spaces.pzIter 2 G x.1 x.2) ^ 2)
      (Set.Icc a b ×ˢ Set.Icc c d))
    (h₂ : MeasureTheory.IntegrableOn (fun x : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2)
      (Set.Icc a b ×ˢ Set.Icc c d))
    (h₃ : MeasureTheory.IntegrableOn (fun x : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2)
      (Set.Icc a b ×ˢ Set.Icc c d))
    (h₄ : MeasureTheory.IntegrableOn (fun x : ℝ × ℝ => (Work.Spaces.pthIter 2 G x.1 x.2) ^ 2)
      (Set.Icc a b ×ˢ Set.Icc c d))
    (hb₁ : ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pzIter 2 G z θ) ^ 2 ≤ C * K)
    (hb₂ : ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pz (Work.Spaces.pth G) z θ) ^ 2 ≤ C * K)
    (hb₃ : ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pth (Work.Spaces.pz G) z θ) ^ 2 ≤ C * K)
    (hb₄ : ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pthIter 2 G z θ) ^ 2 ≤ C * K) :
    ∫ x in Set.Icc a b ×ˢ Set.Icc c d,
        (|Work.Spaces.pzIter 2 G x.1 x.2| + |Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2|
          + |Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2| + |Work.Spaces.pthIter 2 G x.1 x.2|) ^ 2
      ≤ 16 * C * K := by
  -- The elementary pointwise inequality `(Σ|pᵢ|)² ≤ 4 Σ pᵢ²`.
  have hpt : ∀ p q r t : ℝ, (|p| + |q| + |r| + |t|) ^ 2 ≤ 4 * (p^2 + q^2 + r^2 + t^2) := by
    intro p q r t
    have h1 : |p|^2 = p^2 := sq_abs p
    have h2 : |q|^2 = q^2 := sq_abs q
    have h3 : |r|^2 = r^2 := sq_abs r
    have h4 : |t|^2 = t^2 := sq_abs t
    nlinarith [sq_nonneg (|p| - |q|), sq_nonneg (|p| - |r|), sq_nonneg (|p| - |t|),
      sq_nonneg (|q| - |r|), sq_nonneg (|q| - |t|), sq_nonneg (|r| - |t|),
      abs_nonneg p, abs_nonneg q, abs_nonneg r, abs_nonneg t]
  -- Integrated form of `hpt` for four arbitrary functions on the rectangle.
  have key : ∀ (f₁ f₂ f₃ f₄ : ℝ × ℝ → ℝ),
      IntegrableOn (fun x => (f₁ x)^2) (Set.Icc a b ×ˢ Set.Icc c d) →
      IntegrableOn (fun x => (f₂ x)^2) (Set.Icc a b ×ˢ Set.Icc c d) →
      IntegrableOn (fun x => (f₃ x)^2) (Set.Icc a b ×ˢ Set.Icc c d) →
      IntegrableOn (fun x => (f₄ x)^2) (Set.Icc a b ×ˢ Set.Icc c d) →
      ∫ x in Set.Icc a b ×ˢ Set.Icc c d, (|f₁ x| + |f₂ x| + |f₃ x| + |f₄ x|) ^ 2
        ≤ 4 * ((∫ x in Set.Icc a b ×ˢ Set.Icc c d, (f₁ x)^2)
            + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (f₂ x)^2)
            + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (f₃ x)^2)
            + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (f₄ x)^2)) := by
    intro f₁ f₂ f₃ f₄ h₁ h₂ h₃ h₄
    have h12 : Integrable (fun x => (f₁ x)^2 + (f₂ x)^2)
        (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := h₁.add h₂
    have h123 : Integrable (fun x => (f₁ x)^2 + (f₂ x)^2 + (f₃ x)^2)
        (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := h12.add h₃
    have hgi : Integrable (fun x => 4 * ((f₁ x)^2 + (f₂ x)^2 + (f₃ x)^2 + (f₄ x)^2))
        (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := h123.add h₄ |>.const_mul 4
    have hm := integral_mono_of_nonneg (μ := volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))
      (f := fun x => (|f₁ x| + |f₂ x| + |f₃ x| + |f₄ x|) ^ 2)
      (g := fun x => 4 * ((f₁ x)^2 + (f₂ x)^2 + (f₃ x)^2 + (f₄ x)^2))
      (Filter.Eventually.of_forall fun x => sq_nonneg _)
      hgi (Filter.Eventually.of_forall fun x => hpt (f₁ x) (f₂ x) (f₃ x) (f₄ x))
    calc ∫ x in Set.Icc a b ×ˢ Set.Icc c d, (|f₁ x| + |f₂ x| + |f₃ x| + |f₄ x|) ^ 2
        = ∫ x, (|f₁ x| + |f₂ x| + |f₃ x| + |f₄ x|) ^ 2
            ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := rfl
      _ ≤ ∫ x, 4 * ((f₁ x)^2 + (f₂ x)^2 + (f₃ x)^2 + (f₄ x)^2)
            ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := hm
      _ = 4 * ((∫ x in Set.Icc a b ×ˢ Set.Icc c d, (f₁ x)^2)
            + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (f₂ x)^2)
            + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (f₃ x)^2)
            + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (f₄ x)^2)) := by
          rw [integral_const_mul, integral_add h123 h₄, integral_add h12 h₃, integral_add h₁ h₂]
  have hkey := key (fun x : ℝ × ℝ => Work.Spaces.pzIter 2 G x.1 x.2)
      (fun x : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2)
      (fun x : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2)
      (fun x : ℝ × ℝ => Work.Spaces.pthIter 2 G x.1 x.2) h₁ h₂ h₃ h₄
  -- Fubini: the rectangle integral of each square is the corresponding iterated integral.
  have e₁ : ∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pzIter 2 G x.1 x.2) ^ 2
      = ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pzIter 2 G z θ) ^ 2 :=
    MeasureTheory.setIntegral_prod
      (fun x : ℝ × ℝ => (Work.Spaces.pzIter 2 G x.1 x.2) ^ 2) h₁
  have e₂ : ∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2
      = ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pz (Work.Spaces.pth G) z θ) ^ 2 :=
    MeasureTheory.setIntegral_prod
      (fun x : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2) h₂
  have e₃ : ∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2
      = ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pth (Work.Spaces.pz G) z θ) ^ 2 :=
    MeasureTheory.setIntegral_prod
      (fun x : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2) h₃
  have e₄ : ∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pthIter 2 G x.1 x.2) ^ 2
      = ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pthIter 2 G z θ) ^ 2 :=
    MeasureTheory.setIntegral_prod
      (fun x : ℝ × ℝ => (Work.Spaces.pthIter 2 G x.1 x.2) ^ 2) h₄
  have hb₁' : (∫ x in Set.Icc a b ×ˢ Set.Icc c d,
      (Work.Spaces.pzIter 2 G x.1 x.2) ^ 2) ≤ C * K := e₁ ▸ hb₁
  have hb₂' : (∫ x in Set.Icc a b ×ˢ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2) ≤ C * K := e₂ ▸ hb₂
  have hb₃' : (∫ x in Set.Icc a b ×ˢ Set.Icc c d,
      (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2) ≤ C * K := e₃ ▸ hb₃
  have hb₄' : (∫ x in Set.Icc a b ×ˢ Set.Icc c d,
      (Work.Spaces.pthIter 2 G x.1 x.2) ^ 2) ≤ C * K := e₄ ▸ hb₄
  have hkey' : ∫ x in Set.Icc a b ×ˢ Set.Icc c d,
        (|Work.Spaces.pzIter 2 G x.1 x.2| + |Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2|
          + |Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2| + |Work.Spaces.pthIter 2 G x.1 x.2|) ^ 2
      ≤ 4 * ((∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pzIter 2 G x.1 x.2) ^ 2)
          + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2)
          + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2)
          + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pthIter 2 G x.1 x.2) ^ 2)) := hkey
  calc ∫ x in Set.Icc a b ×ˢ Set.Icc c d,
        (|Work.Spaces.pzIter 2 G x.1 x.2| + |Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2|
          + |Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2| + |Work.Spaces.pthIter 2 G x.1 x.2|) ^ 2
      ≤ 4 * ((∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pzIter 2 G x.1 x.2) ^ 2)
          + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2)
          + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2)
          + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pthIter 2 G x.1 x.2) ^ 2)) := hkey'
    _ ≤ 4 * (C * K + C * K + C * K + C * K) := by linarith [hb₁', hb₂', hb₃', hb₄']
    _ = 16 * C * K := by ring

end Work.FTS.StrongEps.HQoAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.HQoAux.integral_sq_sum4_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.HQoAux



end Work.FTS.StrongEps.HQoAux
end
-- ===== merged: Submission.Work.FTS_EllLimOK.BoxDataH.WithinVec =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.BoxDataH

open Work.FTS_EllLimOK.BoxRegAux (dz dth dir1 consD prod_dir1_le_one prod_consD_dir1_le_one
  norm_dz_le_one norm_dth_le_one)

set_option autoImplicit false

/-! ## The six within-partials -/

/-- The `z`-partial, within the set `s`. -/
def wPz (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  iteratedFDerivWithin ℝ 1 F s p (dir1 dz)

/-- The `θ`-partial, within the set `s`. -/
def wPth (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  iteratedFDerivWithin ℝ 1 F s p (dir1 dth)

/-- The `∂_z∂_z`-partial, within the set `s`. -/
def wPzz (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  iteratedFDerivWithin ℝ 2 F s p (consD dz (dir1 dz))

/-- The `∂_z∂_θ`-partial, within the set `s`. -/
def wPzt (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  iteratedFDerivWithin ℝ 2 F s p (consD dz (dir1 dth))

/-- The `∂_θ∂_z`-partial, within the set `s`. -/
def wPtz (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  iteratedFDerivWithin ℝ 2 F s p (consD dth (dir1 dz))

/-- The `∂_θ∂_θ`-partial, within the set `s`. -/
def wPtt (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  iteratedFDerivWithin ℝ 2 F s p (consD dth (dir1 dth))

/-- The six within-partials as one `Fin 6 → ℝ`-valued map (the Arzelà–Ascoli family). -/
def wJet (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Fin 6 → ℝ :=
  ![wPz s F p, wPth s F p, wPzz s F p, wPtz s F p, wPzt s F p, wPtt s F p]

@[simp] theorem wJet_apply_zero (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    wJet s F p 0 = wPz s F p := rfl

@[simp] theorem wJet_apply_one (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    wJet s F p 1 = wPth s F p := rfl

@[simp] theorem wJet_apply_two (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    wJet s F p 2 = wPzz s F p := rfl

@[simp] theorem wJet_apply_three (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    wJet s F p 3 = wPtz s F p := rfl

@[simp] theorem wJet_apply_four (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    wJet s F p 4 = wPzt s F p := rfl

@[simp] theorem wJet_apply_five (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    wJet s F p 5 = wPtt s F p := rfl

/-! ## Unique differentiability of a non-degenerate box -/

/-- The closed box `cbox a b = [a,b] × [0,π/2]` with `a < b` is a set of unique differentiability
(a product of two non-degenerate closed intervals). -/
theorem uniqueDiffOn_cbox {a b : ℝ} (hab : a < b) : UniqueDiffOn ℝ (cbox a b) :=
  (uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc (by linarith [Real.pi_pos]))

/-! ## Bridges to the `fderivWithin` form -/

theorem wPz_eq_fderivWithin {s : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hs : UniqueDiffWithinAt ℝ s p) :
    wPz s F p = fderivWithin ℝ F s p dz := by
  rw [wPz, iteratedFDerivWithin_one_apply hs]
  rfl

theorem wPth_eq_fderivWithin {s : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hs : UniqueDiffWithinAt ℝ s p) :
    wPth s F p = fderivWithin ℝ F s p dth := by
  rw [wPth, iteratedFDerivWithin_one_apply hs]
  rfl

theorem wPzz_eq_fderivWithin {s : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hs : UniqueDiffOn ℝ s) (hp : p ∈ s) :
    wPzz s F p = fderivWithin ℝ (fderivWithin ℝ F s) s p dz dz := by
  rw [wPzz, iteratedFDerivWithin_two_apply F hs hp]
  rfl

theorem wPzt_eq_fderivWithin {s : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hs : UniqueDiffOn ℝ s) (hp : p ∈ s) :
    wPzt s F p = fderivWithin ℝ (fderivWithin ℝ F s) s p dz dth := by
  rw [wPzt, iteratedFDerivWithin_two_apply F hs hp]
  rfl

theorem wPtz_eq_fderivWithin {s : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hs : UniqueDiffOn ℝ s) (hp : p ∈ s) :
    wPtz s F p = fderivWithin ℝ (fderivWithin ℝ F s) s p dth dz := by
  rw [wPtz, iteratedFDerivWithin_two_apply F hs hp]
  rfl

theorem wPtt_eq_fderivWithin {s : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hs : UniqueDiffOn ℝ s) (hp : p ∈ s) :
    wPtt s F p = fderivWithin ℝ (fderivWithin ℝ F s) s p dth dth := by
  rw [wPtt, iteratedFDerivWithin_two_apply F hs hp]
  rfl

/-! ## Componentwise bounds from the operator-norm bounds -/

/-- Componentwise bound of `wJet` from the operator-norm bounds of `iteratedFDerivWithin`. -/
theorem abs_wJet_le {s : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {K : ℝ}
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ p ∈ s, ‖iteratedFDerivWithin ℝ k F s p‖ ≤ K) :
    ∀ p ∈ s, ∀ m : Fin 6, |wJet s F p m| ≤ K := by
  intro p hp m
  have key1 : ∀ (u : ℝ × ℝ), ‖u‖ ≤ 1 →
      |iteratedFDerivWithin ℝ 1 F s p (dir1 u)| ≤ K := by
    intro u hu
    have h1 : ‖iteratedFDerivWithin ℝ 1 F s p (dir1 u)‖
        ≤ ‖iteratedFDerivWithin ℝ 1 F s p‖ * ∏ i : Fin 1, ‖dir1 u i‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    have h2 : ∏ i : Fin 1, ‖dir1 u i‖ ≤ 1 := prod_dir1_le_one u hu
    have h4 : (0 : ℝ) ≤ ∏ i : Fin 1, ‖dir1 u i‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
    rw [Real.norm_eq_abs] at h1
    calc |iteratedFDerivWithin ℝ 1 F s p (dir1 u)|
        ≤ ‖iteratedFDerivWithin ℝ 1 F s p‖ * ∏ i : Fin 1, ‖dir1 u i‖ := h1
      _ ≤ K * ∏ i : Fin 1, ‖dir1 u i‖ :=
          mul_le_mul_of_nonneg_right (hb 1 (by norm_num) p hp) h4
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left h2
          (le_trans (norm_nonneg _) (hb 1 (by norm_num) p hp))
      _ = K := mul_one K
  have key2 : ∀ (u v : ℝ × ℝ), ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      |iteratedFDerivWithin ℝ 2 F s p (consD v (dir1 u))| ≤ K := by
    intro u v hu hv
    have h1 : ‖iteratedFDerivWithin ℝ 2 F s p (consD v (dir1 u))‖
        ≤ ‖iteratedFDerivWithin ℝ 2 F s p‖ * ∏ i : Fin 2, ‖consD v (dir1 u) i‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    have h2 : ∏ i : Fin 2, ‖consD v (dir1 u) i‖ ≤ 1 := prod_consD_dir1_le_one u v hu hv
    have h4 : (0 : ℝ) ≤ ∏ i : Fin 2, ‖consD v (dir1 u) i‖ :=
      Finset.prod_nonneg (fun _ _ => norm_nonneg _)
    rw [Real.norm_eq_abs] at h1
    calc |iteratedFDerivWithin ℝ 2 F s p (consD v (dir1 u))|
        ≤ ‖iteratedFDerivWithin ℝ 2 F s p‖ * ∏ i : Fin 2, ‖consD v (dir1 u) i‖ := h1
      _ ≤ K * ∏ i : Fin 2, ‖consD v (dir1 u) i‖ :=
          mul_le_mul_of_nonneg_right (hb 2 (by norm_num) p hp) h4
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left h2
          (le_trans (norm_nonneg _) (hb 2 (by norm_num) p hp))
      _ = K := mul_one K
  fin_cases m
  · show |wJet s F p 0| ≤ K
    rw [wJet_apply_zero, wPz]
    exact key1 dz norm_dz_le_one
  · show |wJet s F p 1| ≤ K
    rw [wJet_apply_one, wPth]
    exact key1 dth norm_dth_le_one
  · show |wJet s F p 2| ≤ K
    rw [wJet_apply_two, wPzz]
    exact key2 dz dz norm_dz_le_one norm_dz_le_one
  · show |wJet s F p 3| ≤ K
    rw [wJet_apply_three, wPtz]
    exact key2 dz dth norm_dz_le_one norm_dth_le_one
  · show |wJet s F p 4| ≤ K
    rw [wJet_apply_four, wPzt]
    exact key2 dth dz norm_dth_le_one norm_dz_le_one
  · show |wJet s F p 5| ≤ K
    rw [wJet_apply_five, wPtt]
    exact key2 dth dth norm_dth_le_one norm_dth_le_one

/-- The `Fin 6`-norm of the within-jet vector is bounded by the operator-norm bound. -/
theorem norm_wJet_le {s : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {K : ℝ} {p : ℝ × ℝ} (hp : p ∈ s)
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ q ∈ s, ‖iteratedFDerivWithin ℝ k F s q‖ ≤ K) :
    ‖wJet s F p‖ ≤ K := by
  have hK : 0 ≤ K := le_trans (norm_nonneg _) (hb 0 (by norm_num) p hp)
  rw [pi_norm_le_iff_of_nonneg hK]
  intro m
  rw [Real.norm_eq_abs]
  exact abs_wJet_le hb p hp m

/-- The Hölder bound for the four second-order components of `wJet`. -/
theorem abs_wJet_sub_le_hölder {s : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {K β : ℝ}
    (hh : ∀ p ∈ s, ∀ q ∈ s,
      ‖iteratedFDerivWithin ℝ 2 F s p - iteratedFDerivWithin ℝ 2 F s q‖
        ≤ K * ‖p - q‖ ^ β)
    (hK : 0 ≤ K) :
    ∀ p ∈ s, ∀ q ∈ s, ∀ m : Fin 6, 2 ≤ m →
      |wJet s F p m - wJet s F q m| ≤ K * ‖p - q‖ ^ β := by
  intro p hp q hq m hm
  have hprod : ∀ (u v : ℝ × ℝ), ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      |iteratedFDerivWithin ℝ 2 F s p (consD v (dir1 u))
        - iteratedFDerivWithin ℝ 2 F s q (consD v (dir1 u))| ≤ K * ‖p - q‖ ^ β := by
    intro u v hu hv
    have h4 : (0 : ℝ) ≤ K * ‖p - q‖ ^ β :=
      mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _)
    have h5 : (0 : ℝ) ≤ ∏ i : Fin 2, ‖consD v (dir1 u) i‖ :=
      Finset.prod_nonneg (fun _ _ => norm_nonneg _)
    have h2 : ∏ i : Fin 2, ‖consD v (dir1 u) i‖ ≤ 1 := prod_consD_dir1_le_one u v hu hv
    have key : ‖(iteratedFDerivWithin ℝ 2 F s p - iteratedFDerivWithin ℝ 2 F s q)
        (consD v (dir1 u))‖ ≤ K * ‖p - q‖ ^ β := by
      refine le_trans (ContinuousMultilinearMap.le_opNorm _ _) ?_
      calc ‖iteratedFDerivWithin ℝ 2 F s p - iteratedFDerivWithin ℝ 2 F s q‖
            * ∏ i : Fin 2, ‖consD v (dir1 u) i‖
          ≤ (K * ‖p - q‖ ^ β) * ∏ i : Fin 2, ‖consD v (dir1 u) i‖ :=
            mul_le_mul_of_nonneg_right (hh p hp q hq) h5
        _ ≤ (K * ‖p - q‖ ^ β) * 1 := mul_le_mul_of_nonneg_left h2 h4
        _ = K * ‖p - q‖ ^ β := mul_one _
    rw [sub_apply, Real.norm_eq_abs] at key
    exact key
  fin_cases m
  · exact absurd hm (by decide)
  · exact absurd hm (by decide)
  · show |wJet s F p 2 - wJet s F q 2| ≤ K * ‖p - q‖ ^ β
    rw [wJet_apply_two, wJet_apply_two, wPzz, wPzz]
    exact hprod dz dz norm_dz_le_one norm_dz_le_one
  · show |wJet s F p 3 - wJet s F q 3| ≤ K * ‖p - q‖ ^ β
    rw [wJet_apply_three, wJet_apply_three, wPtz, wPtz]
    exact hprod dz dth norm_dz_le_one norm_dth_le_one
  · show |wJet s F p 4 - wJet s F q 4| ≤ K * ‖p - q‖ ^ β
    rw [wJet_apply_four, wJet_apply_four, wPzt, wPzt]
    exact hprod dth dz norm_dth_le_one norm_dz_le_one
  · show |wJet s F p 5 - wJet s F q 5| ≤ K * ‖p - q‖ ^ β
    rw [wJet_apply_five, wJet_apply_five, wPtt, wPtt]
    exact hprod dth dth norm_dth_le_one norm_dth_le_one

/-! ## Continuity of the components on the box -/

/-- Continuity on the box of the six components of `wJet`, from `C²`-smoothness within the box. -/
theorem continuousOn_wJet {a b : ℝ} {F : ℝ × ℝ → ℝ} (hab : a < b)
    (hsm : ContDiffOn ℝ 2 F (cbox a b)) :
    ∀ m : Fin 6, ContinuousOn (fun p : ℝ × ℝ => wJet (cbox a b) F p m) (cbox a b) := by
  have hU : UniqueDiffOn ℝ (cbox a b) := uniqueDiffOn_cbox hab
  have h1 : ContinuousOn (iteratedFDerivWithin ℝ 1 F (cbox a b)) (cbox a b) :=
    hsm.continuousOn_iteratedFDerivWithin (m := 1) (by norm_num) hU
  have h2 : ContinuousOn (iteratedFDerivWithin ℝ 2 F (cbox a b)) (cbox a b) :=
    hsm.continuousOn_iteratedFDerivWithin (m := 2) (by norm_num) hU
  intro m
  fin_cases m
  · refine (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => ℝ × ℝ) ℝ
      (dir1 dz)).continuous).comp_continuousOn h1).congr (fun p _ => ?_)
    rfl
  · refine (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => ℝ × ℝ) ℝ
      (dir1 dth)).continuous).comp_continuousOn h1).congr (fun p _ => ?_)
    rfl
  · refine (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ × ℝ) ℝ
      (consD dz (dir1 dz))).continuous).comp_continuousOn h2).congr (fun p _ => ?_)
    rfl
  · refine (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ × ℝ) ℝ
      (consD dth (dir1 dz))).continuous).comp_continuousOn h2).congr (fun p _ => ?_)
    rfl
  · refine (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ × ℝ) ℝ
      (consD dz (dir1 dth))).continuous).comp_continuousOn h2).congr (fun p _ => ?_)
    rfl
  · refine (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ × ℝ) ℝ
      (consD dth (dir1 dth))).continuous).comp_continuousOn h2).congr (fun p _ => ?_)
    rfl

/-! ## The retraction of the plane onto the box -/

/-- The clamping of a real number onto the interval `[a,b]`. -/
def clampI (a b t : ℝ) : ℝ := max a (min t b)

theorem clampI_mem {a b t : ℝ} (hab : a ≤ b) : clampI a b t ∈ Set.Icc a b :=
  ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem clampI_eq_of_mem {a b t : ℝ} (h : t ∈ Set.Icc a b) : clampI a b t = t := by
  rw [clampI, min_eq_left h.2, max_eq_right h.1]

theorem abs_clampI_sub_le (a b x y : ℝ) : |clampI a b x - clampI a b y| ≤ |x - y| := by
  have h1 : |min x b - min y b| ≤ |x - y| := by
    refine le_trans (abs_min_sub_min_le_max x b y b) ?_
    rw [max_le_iff]
    exact ⟨le_rfl, by simp⟩
  have h2 : |max a (min x b) - max a (min y b)| ≤ |min x b - min y b| := by
    refine le_trans (abs_max_sub_max_le_max a (min x b) a (min y b)) ?_
    rw [max_le_iff]
    exact ⟨by simp, le_rfl⟩
  calc |clampI a b x - clampI a b y| = |max a (min x b) - max a (min y b)| := rfl
    _ ≤ |min x b - min y b| := h2
    _ ≤ |x - y| := h1

/-- The `1`-Lipschitz retraction of the plane onto the box `cbox a b`. -/
def clampB (a b : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (clampI a b p.1, clampθ p.2)


theorem dist_clampB_le (a b : ℝ) (p q : ℝ × ℝ) :
    dist (clampB a b p) (clampB a b q) ≤ dist p q := by
  rw [Prod.dist_eq, Prod.dist_eq, sup_le_iff]
  constructor
  · refine le_trans ?_ le_sup_left
    rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs, Real.norm_eq_abs]
    exact abs_clampI_sub_le a b p.1 q.1
  · refine le_trans ?_ le_sup_right
    rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs, Real.norm_eq_abs]
    exact abs_clampθ_sub_clampθ_le p.2 q.2

theorem clampB_mem_cbox {a b : ℝ} {p : ℝ × ℝ} (hab : a ≤ b) : clampB a b p ∈ cbox a b :=
  ⟨clampI_mem hab, ⟨clampθ_nonneg _, clampθ_le _⟩⟩

theorem clampB_eq_of_mem_cbox {a b : ℝ} {p : ℝ × ℝ} (hp : p ∈ cbox a b) :
    clampB a b p = p := by
  obtain ⟨hp1, hp2⟩ := mem_cbox.mp hp
  simp only [clampB, clampI_eq_of_mem hp1, clampθ_eq_of_mem hp2]

end Work.FTS_EllLimOK.BoxDataH
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.EGap.Lzero_integral_eq_boxReg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory

namespace Work.FTS_EllLimOK.EGap

/-- A two-point set in `ℝ` is null. -/
private theorem volume_pair_eq_zero (a b : ℝ) :
    (MeasureTheory.volume ({a, b} : Set ℝ)) = 0 := by
  have hfin : ({a, b} : Set ℝ).Finite := by simp
  exact hfin.measure_zero MeasureTheory.volume

theorem Lzero_integral_eq_boxReg (α : ℝ) (v : ℝ → ℝ → ℝ) (z : ℝ) (hz : 0 < z)
    (hbox : Work.FTS_EllLimOK.BoxReg v)
    (heq : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.bslOp α v z θ = 0) :
    (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero v z θ * v z θ)
      = α ^ 2 * z ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 v z θ * v z θ)
        + α * (5 + α) * z * (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz v z θ * v z θ) := by
  -- The equation `bslOp α v z = 0` on the open angle interval gives the pointwise identity
  -- of integrands there.
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Elliptic.Lzero v z θ * v z θ
        = α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 v z θ * v z θ)
          + α * (5 + α) * z * (Work.Spaces.pz v z θ * v z θ) := by
    intro θ hθ
    have h0 : Work.Elliptic.Lzero v z θ
        = (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 v z θ
          + (α * (5 + α) * z) * Work.Spaces.pz v z θ := by
      have h := heq θ hθ
      simp only [Work.Elliptic.bslOp_apply] at h
      linarith
    rw [h0]
    ring
  -- Hence the two integrands agree almost everywhere on `Iθ`: they can differ only at the
  -- two endpoints `θ = 0` and `θ = π/2`, a null set.
  have hae : (fun θ : ℝ => Work.Elliptic.Lzero v z θ * v z θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 v z θ * v z θ)
        + α * (5 + α) * z * (Work.Spaces.pz v z θ * v z θ)) := by
    change ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Elliptic.Lzero v z θ * v z θ
        = α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 v z θ * v z θ)
          + α * (5 + α) * z * (Work.Spaces.pz v z θ * v z θ)
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc,
      MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (volume_pair_eq_zero 0 (π / 2))
    intro x hx
    by_contra hmem
    have hx0 : x ≠ 0 := fun h0 => hmem (by simp [h0])
    have hxpi : x ≠ π / 2 := fun hp => hmem (by simp [hp])
    refine hx (fun hxI => ?_)
    simp only [Work.Spaces.Iθ, Set.mem_Icc] at hxI
    exact hpt x ⟨lt_of_le_of_ne hxI.1 (Ne.symm hx0),
      lt_of_le_of_ne hxI.2 hxpi⟩
  -- `BoxReg` makes the two `z`-derivative slices continuous, hence integrable, on `Iθ`.
  have hzmem : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
  obtain ⟨-, -, hpzcont, hp2cont⟩ :=
    boxReg_facts (show z / 2 < 2 * z by linarith)
      (hbox (z / 2) (2 * z) (by linarith) (by linarith))
  have hcurve : ContinuousOn (fun θ : ℝ => ((z, θ) : ℝ × ℝ)) Work.Spaces.Iθ :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hpzslice : ContinuousOn (fun θ : ℝ => Work.Spaces.pz v z θ) Work.Spaces.Iθ :=
    hpzcont.comp hcurve (fun θ hθ => ⟨hzmem, hθ⟩)
  have hp2slice : ContinuousOn (fun θ : ℝ => Work.Spaces.pzIter 2 v z θ) Work.Spaces.Iθ :=
    hp2cont.comp hcurve (fun θ hθ => ⟨hzmem, hθ⟩)
  have hvslice : ContinuousOn (fun θ : ℝ => v z θ) Work.Spaces.Iθ := (hbox.slice hz).continuousOn
  have hBint : Integrable (fun θ : ℝ => Work.Spaces.pzIter 2 v z θ * v z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (hp2slice.mul hvslice).integrableOn_compact isCompact_Icc
  have hCint : Integrable (fun θ : ℝ => Work.Spaces.pz v z θ * v z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (hpzslice.mul hvslice).integrableOn_compact isCompact_Icc
  -- Linearity of the integral.
  have hsplit : (∫ θ in Work.Spaces.Iθ,
        (α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 v z θ * v z θ)
          + α * (5 + α) * z * (Work.Spaces.pz v z θ * v z θ)))
      = α ^ 2 * z ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 v z θ * v z θ)
        + α * (5 + α) * z * (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz v z θ * v z θ) := by
    rw [MeasureTheory.integral_add (hBint.const_mul (α ^ 2 * z ^ 2))
        (hCint.const_mul (α * (5 + α) * z)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_congr_ae hae]
  exact hsplit

end Work.FTS_EllLimOK.EGap
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.Support.fderiv_fderiv_uncurry_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2.Support

set_option autoImplicit false

/-- **The second Fréchet derivative of a `C²` curried function, in terms of the four second
partials.**

For `f : ℝ → ℝ → ℝ` of class `C²` at `(z,θ)`, the second Fréchet derivative of
`F = Function.uncurry f` at `(z,θ)` is the curried bilinear form whose four entries are the
second partials `∂_z∂_z f`, `∂_θ∂_z f`, `∂_z∂_θ f`, `∂_θ∂_θ f`, i.e.
`D²F(v,w) = v.1 w.1 ∂_z∂_zf + v.1 w.2 ∂_θ∂_zf + v.2 w.1 ∂_z∂_θf + v.2 w.2 ∂_θ∂_θf`.

The two first partials of `F` are `A := pz f` and `B := pth f`; `fderiv ℝ (uncurry f)` agrees
near `(z,θ)` with `q ↦ copBilin (A q, B q) = ellCop (A q) (B q)`, so its derivative is the
composition of `copBilin` with the derivative of the pair `(A,B)`, which by the first-order
formula is `(ellCop ∂_zA ∂_θA).prod (ellCop ∂_zB ∂_θB)`. -/
theorem fderiv_fderiv_uncurry_eq
    {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) :
    fderiv ℝ (fderiv ℝ (Function.uncurry f)) (z, θ)
      = Work.FTS_EllLimOK.copBilin.comp
        ((Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pz f) z θ)
            (Work.Spaces.pth (Work.Spaces.pz f) z θ)).prod
          (Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pth f) z θ)
            (Work.Spaces.pth (Work.Spaces.pth f) z θ))) := by
  -- an open neighbourhood of `(z,θ)` on which `Function.uncurry f` is `C²`
  have hsmU : ContDiffWithinAt ℝ 2 (Function.uncurry f) Set.univ (z, θ) := h
  obtain ⟨u, hu_open, hu_mem, hu_cd⟩ :=
    hsmU.contDiffOn' (le_refl (2 : WithTop ℕ∞)) (by intro hc; simp at hc)
  have hu_eq : insert (z, θ) Set.univ ∩ u = u := by ext x; simp
  rw [hu_eq] at hu_cd
  have hdiff_u : ∀ q ∈ u, DifferentiableAt ℝ (Function.uncurry f) q := fun q hq =>
    (hu_cd.contDiffAt (hu_open.mem_nhds hq)).differentiableAt (by norm_num)
  have h_ev_pz : Function.uncurry (Work.Spaces.pz f) =ᶠ[𝓝 (z, θ)]
      fun q : ℝ × ℝ => fderiv ℝ (Function.uncurry f) q (1, 0) := by
    filter_upwards [hu_open.mem_nhds hu_mem] with q hq
    exact Work.Spaces.pz_eq_fderiv (hdiff_u q hq)
  have h_ev_pth : Function.uncurry (Work.Spaces.pth f) =ᶠ[𝓝 (z, θ)]
      fun q : ℝ × ℝ => fderiv ℝ (Function.uncurry f) q (0, 1) := by
    filter_upwards [hu_open.mem_nhds hu_mem] with q hq
    exact Work.Spaces.pth_eq_fderiv (hdiff_u q hq)
  have hdF1 : ContDiffAt ℝ 1 (fderiv ℝ (Function.uncurry f)) (z, θ) :=
    h.fderiv_right (m := 1) (by norm_num)
  have hdiffF1 : DifferentiableAt ℝ (fderiv ℝ (Function.uncurry f)) (z, θ) :=
    hdF1.differentiableAt (by norm_num)
  have hdA : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pz f)) (z, θ) :=
    (hdiffF1.clm_apply (differentiableAt_const ((1 : ℝ), (0 : ℝ)))).congr_of_eventuallyEq
      h_ev_pz
  have hdB : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth f)) (z, θ) :=
    (hdiffF1.clm_apply (differentiableAt_const ((0 : ℝ), (1 : ℝ)))).congr_of_eventuallyEq
      h_ev_pth
  have hA : HasFDerivAt (fun q : ℝ × ℝ => Work.Spaces.pz f q.1 q.2)
      (Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pz f) z θ)
        (Work.Spaces.pth (Work.Spaces.pz f) z θ)) (z, θ) :=
    hdA.hasFDerivAt.congr_fderiv
      (Work.FTS_EllLimOK.ProducerH.BoxAux.fderiv_uncurry_eq_ellCop (g := Work.Spaces.pz f) hdA)
  have hB : HasFDerivAt (fun q : ℝ × ℝ => Work.Spaces.pth f q.1 q.2)
      (Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pth f) z θ)
        (Work.Spaces.pth (Work.Spaces.pth f) z θ)) (z, θ) :=
    hdB.hasFDerivAt.congr_fderiv
      (Work.FTS_EllLimOK.ProducerH.BoxAux.fderiv_uncurry_eq_ellCop (g := Work.Spaces.pth f) hdB)
  have hg_ev : fderiv ℝ (Function.uncurry f) =ᶠ[𝓝 (z, θ)]
      fun q : ℝ × ℝ => Work.FTS_EllLimOK.copBilin
        (Work.Spaces.pz f q.1 q.2, Work.Spaces.pth f q.1 q.2) := by
    filter_upwards [hu_open.mem_nhds hu_mem] with q hq
    rw [Work.FTS_EllLimOK.ProducerH.BoxAux.fderiv_uncurry_eq_ellCop (g := f) (hdiff_u q hq),
      Work.FTS_EllLimOK.copBilin_apply]
  have hpair : HasFDerivAt
      (fun q : ℝ × ℝ => (Work.Spaces.pz f q.1 q.2, Work.Spaces.pth f q.1 q.2))
      ((Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pz f) z θ)
          (Work.Spaces.pth (Work.Spaces.pz f) z θ)).prod
        (Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pth f) z θ)
          (Work.Spaces.pth (Work.Spaces.pth f) z θ))) (z, θ) := hA.prodMk hB
  have hcomp : HasFDerivAt (fun q : ℝ × ℝ => Work.FTS_EllLimOK.copBilin
      (Work.Spaces.pz f q.1 q.2, Work.Spaces.pth f q.1 q.2))
      (Work.FTS_EllLimOK.copBilin.comp
        ((Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pz f) z θ)
            (Work.Spaces.pth (Work.Spaces.pz f) z θ)).prod
          (Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pth f) z θ)
            (Work.Spaces.pth (Work.Spaces.pth f) z θ)))) (z, θ) :=
    (ContinuousLinearMap.hasFDerivAt Work.FTS_EllLimOK.copBilin).comp (z, θ) hpair
  exact hg_ev.fderiv_eq.trans hcomp.fderiv

end Work.FTS_EllLimOK.ProducerH.H2.Support
end
-- ===== merged: Submission.Work.RPFresh.slice_sq_le_right =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.RPFresh

open MeasureTheory Set intervalIntegral Filter
open scoped Real Topology

set_option autoImplicit false



end Work.RPFresh
end
-- ===== merged: Submission.Work.Spaces.HProductRule_bad_term =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false



/-! ## The bad term of the `H^4` product rule -/


end Work.Spaces
end
end
