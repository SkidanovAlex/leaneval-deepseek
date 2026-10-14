import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCaseHard
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.radialMul6Cont
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.N6_fkH
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12FieldsAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000


/-- `SmoothOpen` is closed under negation. -/
theorem so_neg {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => - g z θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen] at hg ⊢
  have h : Function.uncurry (fun z θ => - g z θ) = - Function.uncurry g := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [h]
  exact hg.neg



end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.SepMem6Local =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Integrability on `Iθ` of `sin(2θ)^p` for every `p > -1` (not just `p ≤ 0`). -/
theorem integrableOn_sin_two_rpow {p : ℝ} (hp : -1 < p) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) Work.Spaces.Iθ := by
  by_cases h : p ≤ 0
  · exact (Work.Spaces.sin_two_rpow p hp h).1
  · push_neg at h
    have hne : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
      rw [show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    refine MeasureTheory.Integrable.mono'
      (integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ)) hne)
      (((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const p)
        |>.aestronglyMeasurable) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    have h0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    rw [Real.norm_of_nonneg (Real.rpow_nonneg h0 p)]
    exact Real.rpow_le_one h0 (Real.sin_le_one _) h.le

/-- `D_z`-iterates of a radial function: `DzIter j (fun z _ => ρ z) z θ = DzdIter j ρ z`. -/
theorem DzIter_z_only (ρ : ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z _ => ρ z) z θ = Work.Elliptic.DzdIter j ρ z := by
  induction j generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, Work.Elliptic.DzdIter_succ]
      show z * deriv (fun z' => Work.Spaces.DzIter n (fun z _ => ρ z) z' θ) z
        = z * deriv (Work.Elliptic.DzdIter n ρ) z
      have h : (fun z' => Work.Spaces.DzIter n (fun z _ => ρ z) z' θ)
          = fun z' => Work.Elliptic.DzdIter n ρ z' := by
        funext z'; exact ih z'
      rw [h]


end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T3RowGroup =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000


end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCoefCase =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

/-- **The mismatch case of the level-six coefficient row.**  For the coefficient slot
`X = D_z^{b₁}D_θ^{a₁}A` of order `a₁ ≥ 1`, `a₁ + b₁ ≤ 2`, the datum slots
`Y = D_z^{b-b₁}D_θ^{a-a₁} f`, `Z = D_z^bD_θ^a f` of total order `a + b ≤ 6`, and the leaf
weight `leafGam α = w²sin(2θ)^{-γ}`,

`|∫∫ leafGam α · X · Y · Z| ≤ C α^{-3} (1 + K0 + K4) (1 + |f|²_{ℋ⁶})`.

The three index cases `a₁ < a`, `a = a₁ ∧ ¬(a₁ = 1 ∧ b₁ = 0)` and `a = a₁ = 1 ∧ b₁ = 0` are
proved in the sibling modules `mismatchCaseLt`, `mismatchCaseGe`, `mismatchCaseHard`. -/
theorem mismatchCoefCase : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (A f : ℝ → ℝ → ℝ) (K0 K4 : ℝ) (a b a₁ b₁ : ℕ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 4 A →
      Work.Spaces.HkMem α 6 A →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0) →
      Work.FTS.Nonlin.Xn α A ≤ K4 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 7 f →
      Work.Spaces.VanishTheta f →
      1 ≤ a₁ → a₁ + b₁ ≤ 2 → a₁ ≤ a → b₁ ≤ b → a + b ≤ 6 →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed b₁ a₁ A p.1 p.2
          * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
            * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
  obtain ⟨C1, hC1pos, hLt⟩ := mismatchCaseLt
  obtain ⟨C2, hC2pos, hGe⟩ := mismatchCaseGe
  obtain ⟨C3, hC3pos, hHard⟩ := mismatchCaseHard
  refine ⟨max C1 (max C2 C3), lt_of_lt_of_le hC1pos (le_max_left _ _), ?_⟩
  intro α hα A f K0 K4 a b a₁ b₁ hAsm hA4 hA6 hAbdd hA4bnd hfsm hf7 hfv
    ha₁ hab₁ ha₁a hb₁b hab
  have hK0 : 0 ≤ K0 :=
    le_trans (abs_nonneg (A 1 (Real.pi / 4)))
      (hAbdd 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos]))
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hA4bnd
  have hX : 0 ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f) :=
    mul_nonneg (by linarith) (by linarith [Work.Spaces.HkSq_nonneg α 6 f])
  have hα3 : 0 ≤ α ^ (-(3 : ℝ)) := Real.rpow_nonneg hα.1.le _
  have hshape : ∀ c : ℝ, c ≤ max C1 (max C2 C3) →
      c * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))
        ≤ max C1 (max C2 C3) * α ^ (-(3 : ℝ))
          * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
    intro c hc
    have h1 : c * α ^ (-(3 : ℝ)) ≤ max C1 (max C2 C3) * α ^ (-(3 : ℝ)) :=
      mul_le_mul_of_nonneg_right hc hα3
    have h2 : c * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))
        ≤ max C1 (max C2 C3) * α ^ (-(3 : ℝ))
          * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
      calc c * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))
          = (c * α ^ (-(3 : ℝ))) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by ring
        _ ≤ (max C1 (max C2 C3) * α ^ (-(3 : ℝ)))
              * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) :=
            mul_le_mul_of_nonneg_right h1 hX
        _ = max C1 (max C2 C3) * α ^ (-(3 : ℝ))
              * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by ring
    exact h2
  by_cases hlt : a₁ < a
  · obtain ⟨hint, hbd⟩ := hLt α hα A f K0 K4 a b a₁ b₁ hAsm hA4 hA6 hAbdd hA4bnd hfsm hf7 hfv
      ha₁ hab₁ ha₁a hb₁b hab hlt
    exact ⟨hint, hbd.trans (hshape C1 (le_max_left C1 (max C2 C3)))⟩
  · have hae : a = a₁ := by omega
    by_cases hb : a₁ = 1 ∧ b₁ = 0
    · obtain ⟨hint, hbd⟩ := hHard α hα A f K0 K4 a b a₁ b₁ hAsm hA4 hA6 hAbdd hA4bnd hfsm
        hf7 hfv ha₁ hab₁ ha₁a hb₁b hab hae hb.1 hb.2
      exact ⟨hint, hbd.trans (hshape C3
        (le_trans (le_max_right C2 C3) (le_max_right C1 (max C2 C3))))⟩
    · obtain ⟨hint, hbd⟩ := hGe α hα A f K0 K4 a b a₁ b₁ hAsm hA4 hA6 hAbdd hA4bnd hfsm
        hf7 hfv ha₁ hab₁ ha₁a hb₁b hab hae hb
      exact ⟨hint, hbd.trans (hshape C2
        (le_trans (le_max_left C2 C3) (le_max_right C1 (max C2 C3))))⟩

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
end
