import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.SmoothErr
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces.err_expansion =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Real Topology
open Set Filter

/-! ## The multiplier `(χ n · ζ n − 1)` is smooth on the open quadrant -/

private theorem chiZeta_sub_one_smoothOpen (n : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      Work.FTS.PhiStar.Honesty.CptApp.chiR n z
        * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun k => ?_
  have h1 : ContDiffOn ℝ k
      (fun p : ℝ × ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n p.1)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.PhiStar.Honesty.CptApp.contDiff_chiR n k).contDiffOn.comp contDiffOn_fst
      (fun p _ => Set.mem_univ p.1)
  have h2 : ContDiffOn ℝ k
      (fun p : ℝ × ℝ => Work.FTS.PhiStar.Honesty.CptApp.zetaR n p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.PhiStar.Honesty.CptApp.contDiff_zetaR n k).contDiffOn.comp contDiffOn_snd
      (fun p _ => Set.mem_univ p.2)
  exact (h1.mul h2).sub contDiffOn_const

/-! ## Oddness of the iterated operators (unconditional) -/

private theorem dz_neg_local (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => - f z θ) = fun z θ => - Work.Spaces.Dz f z θ := by
  funext z θ
  show z * deriv (fun z' => - f z' θ) z = - (z * deriv (fun z' => f z' θ) z)
  rw [show (fun z' => - f z' θ) = fun z' => (-1 : ℝ) * f z' θ from by funext z'; ring,
    deriv_const_mul_field]
  ring

private theorem dth_neg_local (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => - f z θ) = fun z θ => - Work.Spaces.Dth f z θ := by
  funext z θ
  show Real.sin (2 * θ) * deriv (fun θ' => - f z θ') θ
    = - (Real.sin (2 * θ) * deriv (fun θ' => f z θ') θ)
  rw [show (fun θ' => - f z θ') = fun θ' => (-1 : ℝ) * f z θ' from by funext θ'; ring,
    deriv_const_mul_field]
  ring

private theorem dzIter_neg_local (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter k (fun z θ => - f z θ)
      = fun z θ => - Work.Spaces.DzIter k f z θ := by
  induction k with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ, dz_neg_local]

private theorem dthIter_neg_local (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter k (fun z θ => - f z θ)
      = fun z θ => - Work.Spaces.DthIter k f z θ := by
  induction k with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ, dth_neg_local]

private theorem mixed_neg_local (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => - f z θ)
      = fun z θ => - Work.Spaces.mixed j i f z θ := by
  simp only [Work.Spaces.mixed]
  rw [dthIter_neg_local, dzIter_neg_local]

private theorem mixed_neg_apply (j i : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => - f z θ) z θ
      = - Work.Spaces.mixed j i f z θ := by
  have h := congrFun (congrFun (mixed_neg_local j i f) z) θ
  simpa using h

/-! ## A function of `θ` alone has `D_θ`-iterates independent of `z` -/

private theorem DthIter_z_indep (i : ℕ) (u : ℝ → ℝ) :
    ∀ z θ, Work.Spaces.DthIter i (fun _ (θ' : ℝ) => u θ') z θ
      = Work.Spaces.DthIter i (fun _ (θ' : ℝ) => u θ') 0 θ := by
  induction i with
  | zero => intro z θ; rfl
  | succ i ih =>
      intro z θ
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      have hfun : (fun θ' => Work.Spaces.DthIter i (fun _ (θ' : ℝ) => u θ') z θ')
          = (fun θ' => Work.Spaces.DthIter i (fun _ (θ' : ℝ) => u θ') 0 θ') :=
        funext fun θ' => ih z θ'
      rw [hfun]

/-! ## `rDzIter` is the iterate of `Zop` -/

private theorem rDzIter_eq_iterate (j : ℕ) (m : ℝ → ℝ) :
    Work.FTS.EllipticEst.rDzIter j m = Work.Spaces.Zop^[j] m := by
  induction j with
  | zero => rfl
  | succ n ih =>
      rw [Work.FTS.EllipticEst.rDzIter_succ, ih, Function.iterate_succ_apply']
      rfl

/-! ## The separated (radial × angular) product -/

private theorem mixed_sep (j i : ℕ) (m u : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => m z * u θ) z θ
      = Work.Spaces.DzIter j (fun z _ : ℝ => m z) z 0
        * Work.Spaces.DthIter i (fun _ (θ' : ℝ) => u θ') 0 θ := by
  have hcomm : Work.Spaces.DthIter i (fun z θ => m z * u θ)
      = fun z θ => m z * (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => u θ') 0 θ) := by
    have h := Work.Coercivity.DthIter_mulZm i m (fun _ (θ' : ℝ) => u θ')
    rw [h]
    funext z θ
    rw [DthIter_z_indep i u z θ]
  have hslice := congrFun (Work.Spaces.Zop_slice j (fun z _ : ℝ => m z) 0) z
  rw [Work.Spaces.mixed, hcomm,
    Work.FTS.EllipticEst.DzIter_mul_of_radial j m
      (fun θ' => Work.Spaces.DthIter i (fun _ (θ' : ℝ) => u θ') 0 θ') z θ,
    rDzIter_eq_iterate j m, hslice]

/-! ## The expansion of the error -/

theorem err_expansion (n : ℕ) (hn : 2 ≤ n) {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (j i : ℕ) (z θ : ℝ)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.Spaces.mixed j i (Work.FTS.PhiStar.Honesty.CptApp.err n F) z θ
      = (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a
                    (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                      * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
                 * Work.Spaces.mixed (j - b) (i - a) F z θ))
        - Work.Spaces.DzIter j
            (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z) z 0
          * Work.Spaces.DthIter i
            (fun _ θ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.rho θ) 0 θ := by
  have hn1 : 1 ≤ n := by omega
  -- the pointwise decomposition of the error
  have herr : Work.FTS.PhiStar.Honesty.CptApp.err n F
      = fun z θ =>
          (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
              * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) * F z θ
            + -(Work.FTS.PhiStar.Honesty.CptApp.mu n F z
                * Work.FTS.PhiStar.Honesty.CptApp.rho θ) := by
    funext z' θ'
    rw [Work.FTS.PhiStar.Honesty.CptApp.err, Work.FTS.PhiStar.Honesty.CptApp.approx,
      Work.FTS.PhiStar.Honesty.CptApp.mu]
    ring
  have hA : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) * F z θ) :=
    Work.FTS.PhiStar.Honesty.CptApp.EstAux.smoothOpen_chiZeta_sub_one hF n
  have hB : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      -(Work.FTS.PhiStar.Honesty.CptApp.mu n F z
        * Work.FTS.PhiStar.Honesty.CptApp.rho θ)) :=
    (Work.FTS.PhiStar.Honesty.CptApp.EstAux.smoothOpen_muRho hF hn1).neg
  rw [herr, Work.FTS.EllipticEst.SmoothOpen.mixed_add hA hB j i z θ hz hθ0 hθ1,
    mixed_neg_apply j i (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z
      * Work.FTS.PhiStar.Honesty.CptApp.rho θ) z θ,
    Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed j i
      (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
        * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) F
      (chiZeta_sub_one_smoothOpen n) hF z θ hz hθ0 hθ1,
    mixed_sep j i (fun z => Work.FTS.PhiStar.Honesty.CptApp.mu n F z)
      Work.FTS.PhiStar.Honesty.CptApp.rho z θ]
  ring

end Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.EstCrux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Measurability on the angular interval -/

theorem measurable_thShrink (n : ℕ) : Measurable (thShrink n) := by
  have hs : MeasurableSet {θ : ℝ | θ < 2 / (n : ℝ) ∨ Real.pi / 2 - 2 / (n : ℝ) < θ} :=
    (measurableSet_lt measurable_id measurable_const).union
      (measurableSet_lt measurable_const measurable_id)
  have h : thShrink n = fun θ : ℝ => if θ ∈ {θ : ℝ |
      θ < 2 / (n : ℝ) ∨ Real.pi / 2 - 2 / (n : ℝ) < θ} then (1 : ℝ) else 0 := by
    funext θ
    unfold thShrink
    by_cases hc : θ < 2 / (n : ℝ) ∨ Real.pi / 2 - 2 / (n : ℝ) < θ <;> simp [hc]
  rw [h]
  exact Measurable.ite hs measurable_const measurable_const

/-- A function continuous on `(0,π/2)` is a.e. measurable for the restricted measure on `Iθ`. -/
theorem aemeasurable_restrict_Iθ {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioo 0 (π / 2))) :
    AEMeasurable g (volume.restrict Work.Spaces.Iθ) := by
  have hI : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo 0 (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.restrict_Ioo_eq_restrict_Icc).symm
  rw [hI]
  exact hg.aemeasurable measurableSet_Ioo

theorem aemeasurable_ofReal_restrict_Iθ {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioo 0 (π / 2))) :
    AEMeasurable (fun θ => ENNReal.ofReal (g θ)) (volume.restrict Work.Spaces.Iθ) :=
  ENNReal.measurable_ofReal.comp_aemeasurable (aemeasurable_restrict_Iθ hg)

/-- The `θ`-integrand of the localised Hardy group is a.e. measurable. -/
theorem aemeasurable_ofReal_thShrink {u : ℝ → ℝ} (hu : ContinuousOn u (Set.Ioo 0 (π / 2)))
    (n : ℕ) (c C : ℝ) :
    AEMeasurable (fun θ => ENNReal.ofReal (C * (thShrink n θ * (u θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-c)))) (volume.restrict Work.Spaces.Iθ) := by
  have h1 : AEMeasurable (fun θ => u θ ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    aemeasurable_restrict_Iθ (hu.pow 2)
  have hsincont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-c)) (Set.Ioo 0 (π / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (show 0 < 2 * θ from by linarith [hθ.1])
        (show 2 * θ < Real.pi from by linarith [hθ.2, Real.pi_pos]))))
  have h2 : AEMeasurable (fun θ => (Real.sin (2 * θ)) ^ (-c))
      (volume.restrict Work.Spaces.Iθ) := aemeasurable_restrict_Iθ hsincont
  have h3 : AEMeasurable (thShrink n) (volume.restrict Work.Spaces.Iθ) :=
    (measurable_thShrink n).aemeasurable
  have h4 : AEMeasurable (fun θ => C * (thShrink n θ * (u θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-c))) (volume.restrict Work.Spaces.Iθ) :=
    (((h3.mul h1).mul h2).const_mul C)
  exact ENNReal.measurable_ofReal.comp_aemeasurable h4

/-- The iterates `D_θ^i ρ` (as functions of `θ`) are smooth. -/
theorem contDiff_dthIter_rho (i : ℕ) :
    ∀ m : ℕ, ContDiff ℝ m (fun θ : ℝ => Work.Spaces.DthIter i (fun _ θ' : ℝ => rho θ') 0 θ) := by
  induction i with
  | zero => intro m; simpa using Work.FTS.PhiStar.Honesty.CptApp.contDiff_rho m
  | succ i ih =>
      intro m
      have hg : ContDiff ℝ (m + 1)
          (fun θ : ℝ => Work.Spaces.DthIter i (fun _ θ' : ℝ => rho θ') 0 θ) := ih (m + 1)
      have hd : ContDiff ℝ m (deriv
          (fun θ : ℝ => Work.Spaces.DthIter i (fun _ θ' : ℝ => rho θ') 0 θ)) := hg.deriv'
      have hsin : ContDiff ℝ m (fun θ : ℝ => Real.sin (2 * θ)) :=
        (Real.contDiff_sin (n := (m : WithTop ℕ∞))).comp (contDiff_const.mul contDiff_id)
      have heq : (fun θ : ℝ => Work.Spaces.DthIter (i + 1) (fun _ θ' : ℝ => rho θ') 0 θ)
          = fun θ : ℝ => Real.sin (2 * θ) * deriv
              (fun θ' : ℝ => Work.Spaces.DthIter i (fun _ θ' : ℝ => rho θ') 0 θ') θ := by
        funext θ
        rfl
      rw [heq]
      exact hsin.mul hd

/-- The `ρ`-profile is a.e. measurable on `Iθ`. -/
theorem continuousOn_rhoProf (α : ℝ) (k : ℕ) :
    ContinuousOn (rhoProf α k) (Set.Ioo 0 (π / 2)) := by
  unfold rhoProf
  refine continuousOn_finsetSum _ fun i _ => ?_
  refine (((contDiff_dthIter_rho i 1).continuous.continuousOn).pow 2).mul ?_
  exact ContinuousOn.add
    (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (show 0 < 2 * θ from by linarith [hθ.1])
        (show 2 * θ < Real.pi from by linarith [hθ.2, Real.pi_pos])))))
    (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (show 0 < 2 * θ from by linarith [hθ.1])
        (show 2 * θ < Real.pi from by linarith [hθ.2, Real.pi_pos])))))

theorem aemeasurable_ofReal_rhoProf (α : ℝ) (k : ℕ) :
    AEMeasurable (fun θ => ENNReal.ofReal (rhoProf α k θ)) (volume.restrict Work.Spaces.Iθ) :=
  aemeasurable_ofReal_restrict_Iθ (continuousOn_rhoProf α k)

/-- The `Ω_n`-part of the `ℋᵏ`-integrand of `F` is a.e. measurable on every `θ`-slice. -/
theorem aemeasurable_ofReal_omegaPart (α : ℝ) (k : ℕ) (n : ℕ) {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    AEMeasurable (fun θ => ENNReal.ofReal (omegaPart α k n F z θ))
      (volume.restrict Work.Spaces.Iθ) := by
  have hs : MeasurableSet {θ : ℝ | (z, θ) ∈ Omega n} :=
    (Omega_measurable n).preimage (measurable_const.prodMk measurable_id)
  have hzge : (0 : ℝ) ≤ z := hz
  rcases eq_or_lt_of_le hzge with h0 | hpos
  · rw [← h0]
    have hzero : (fun θ => ENNReal.ofReal (omegaPart α k n F 0 θ)) = fun _ => 0 := by
      funext θ
      unfold omegaPart
      split_ifs
      · rw [Work.FTS.LocData.HkIntegrand_zero_fst]; simp
      · simp
    rw [hzero]
    exact aemeasurable_const
  · have hcont : ContinuousOn (fun θ => Work.Spaces.HkIntegrand α k F z θ)
        (Set.Ioo 0 (π / 2)) :=
      (hsm.continuousOn_HkIntegrand α k).comp
        (continuousOn_const.prodMk continuousOn_id) (fun θ hθ => ⟨hpos, hθ⟩)
    have hmeas : AEMeasurable (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k F z θ))
        (volume.restrict Work.Spaces.Iθ) := aemeasurable_ofReal_restrict_Iθ hcont
    have hind : (fun θ => ENNReal.ofReal (omegaPart α k n F z θ))
        = Set.indicator {θ : ℝ | (z, θ) ∈ Omega n}
            (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k F z θ)) := by
      funext θ
      unfold omegaPart
      by_cases h : (z, θ) ∈ Omega n <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    rw [hind]
    exact hmeas.indicator hs


/-! ## The three inputs, as hypotheses -/

/-- The Block₁ slot bound of `Est.err_dzSlot_le`. -/
def DzSlotLe (k : ℕ) (C : ℝ) : Prop :=
  ∀ (α : ℝ) (n : ℕ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → 3 ≤ n →
    Work.FTS.EllipticEst.SmoothOpen F →
    ∀ (i : ℕ), i ≤ k → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DzIter i (err n F) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ C * Good α k n F z θ

/-- The Block₂ slot bound of `Est.err_mixedSlot_le`. -/
def MixedSlotLe (k : ℕ) (C : ℝ) : Prop :=
  ∀ (α : ℝ) (n : ℕ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → 3 ≤ n →
    Work.FTS.EllipticEst.SmoothOpen F →
    ∀ (i j : ℕ), 1 ≤ i → i + j ≤ k → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.mixed j i (err n F) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ C * Good α k n F z θ

/-- The localised angular Hardy bound of `Est.hardyShrink_slice`. -/
def HardySliceLe (k : ℕ) (α : ℝ) (CH : ℝ) : Prop :=
  ∀ (F : ℝ → ℝ → ℝ) (n s : ℕ), 3 ≤ n → s + 1 ≤ k →
    Work.FTS.EllipticEst.SmoothOpen F → Work.FTS.PhiStar.ThetaTraces α k F →
    ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.w z) ^ 2
          * (thShrink n θ * (Work.Spaces.DzIter s F z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))))
        ≤ ENNReal.ofReal CH
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (omegaPart α k n F z θ))

/-! ## The pointwise bound of the error's integrand by the majorant -/

theorem HkIntegrand_err_le (k : ℕ) {C1 : ℝ} (hC1 : 0 ≤ C1)
    (h1 : DzSlotLe k C1) (h2 : MixedSlotLe k C1) :
    ∀ (α : ℝ) (n : ℕ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → 3 ≤ n →
      Work.FTS.EllipticEst.SmoothOpen F →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (err n F) z θ
          ≤ (2 * ((k : ℝ) + 1) ^ 2 * C1) * Good α k n F z θ := by
  intro α n F hα hα1 hn hsm z hz θ hθ
  have hGnn : 0 ≤ Good α k n F z θ := Good_nonneg α k n F hθ
  have hZ := Finset.sum_le_sum (s := Finset.range (k + 1))
    (f := fun i => (Work.Spaces.DzIter i (err n F) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    (g := fun _ => C1 * Good α k n F z θ)
    (fun i hi => h1 α n F hα hα1 hn hsm i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) z hz θ hθ)
  have hM := Finset.sum_le_sum (s := Finset.range (k + 1)) (fun i _ =>
    Finset.sum_le_sum (s := Finset.range (k + 1))
      (f := fun j => if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i (err n F) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      (g := fun _ => C1 * Good α k n F z θ)
      (fun j hj => by
        by_cases hc : 1 ≤ i ∧ i + j ≤ k
        · rw [if_pos hc]
          exact h2 α n F hα hα1 hn hsm i j hc.1 hc.2 z hz θ hθ
        · rw [if_neg hc]
          exact mul_nonneg hC1 hGnn))
  have hZeq : (∑ _i ∈ Finset.range (k + 1), C1 * Good α k n F z θ)
      = ((k : ℝ) + 1) * (C1 * Good α k n F z θ) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hMeq : (∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1),
      C1 * Good α k n F z θ)
      = ((k : ℝ) + 1) ^ 2 * (C1 * Good α k n F z θ) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring
  rw [Work.Spaces.HkIntegrand]
  have hkc : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hK1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hGnn' : 0 ≤ C1 * Good α k n F z θ := mul_nonneg hC1 hGnn
  have hKle : (k : ℝ) + 1 ≤ ((k : ℝ) + 1) ^ 2 := by
    have h : 0 ≤ (k : ℝ) * ((k : ℝ) + 1) := mul_nonneg hkc (by linarith)
    nlinarith [h]
  have h1' : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i (err n F) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ (((k : ℝ) + 1) ^ 2) * (C1 * Good α k n F z θ) := by
    refine le_trans hZ ?_
    rw [hZeq]
    exact mul_le_mul_of_nonneg_right hKle hGnn'
  have h2' : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (err n F) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ (((k : ℝ) + 1) ^ 2) * (C1 * Good α k n F z θ) := by
    refine le_trans hM ?_
    rw [hMeq]
  have hsum := add_le_add h1' h2'
  refine le_trans hsum ?_
  have : ((k : ℝ) + 1) ^ 2 * (C1 * Good α k n F z θ)
      + ((k : ℝ) + 1) ^ 2 * (C1 * Good α k n F z θ)
      = (2 * ((k : ℝ) + 1) ^ 2 * C1) * Good α k n F z θ := by ring
  rw [← this]


/-! ## An unconditional finset form of `ofReal_add_le` -/

theorem ofReal_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact le_trans ENNReal.ofReal_add_le (add_le_add le_rfl ih)

/-! ## The `θ`-integral bound for the error's `ℋᵏ`-integrand -/

theorem err_theta_lintegral_le (k : ℕ) (α : ℝ) {C1 CH : ℝ} (hC1 : 0 ≤ C1) (hCH : 0 ≤ CH)
    (h1 : DzSlotLe k C1) (h2 : MixedSlotLe k C1) (hH : HardySliceLe k α CH) :
    ∀ (n : ℕ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → 3 ≤ n →
      Work.FTS.EllipticEst.SmoothOpen F → Work.FTS.PhiStar.ThetaTraces α k F →
      ∀ z ∈ Work.Spaces.Iz,
        (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k (err n F) z θ))
          ≤ ENNReal.ofReal (2 * ((k : ℝ) + 1) ^ 2 * C1 * ((k : ℝ) * CH + 1) + 1)
              * ((∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (omegaPart α k n F z θ))
                + ENNReal.ofReal ((Work.Spaces.w z) ^ 2
                    * ∑ m ∈ Finset.range (k + 1),
                        (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2)
                  * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ))) := by
  intro n F hα hα1 hn hsm htr z hz
  have hzge : (0 : ℝ) ≤ z := hz
  have hkc : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  set Cc : ℝ := 2 * ((k : ℝ) + 1) ^ 2 * C1 with hCc
  have hCcpos : 0 ≤ Cc := by rw [hCc]; positivity
  set P : ℝ≥0∞ := ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (omegaPart α k n F z θ) with hP
  set RP : ℝ≥0∞ := ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ) with hRP
  set Q : ℝ≥0∞ := ENNReal.ofReal ((Work.Spaces.w z) ^ 2
      * ∑ m ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2) with hQ
  rcases eq_or_lt_of_le hzge with h0 | hpos
  · rw [← h0]
    have hzero : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k (err n F) 0 θ)) = 0 := by
      simp [Work.FTS.LocData.HkIntegrand_zero_fst]
    rw [hzero]
    exact bot_le
  · -- ## Step 1: the error's integrand is dominated by the majorant
    have step1 : (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (err n F) z θ))
        ≤ ENNReal.ofReal Cc * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Good α k n F z θ)) := by
      calc (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k (err n F) z θ))
          ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Cc * Good α k n F z θ) := by
            refine lintegral_mono_ae (MeasureTheory.ae_restrict_of_forall_mem
              measurableSet_Icc fun θ hθ => ?_)
            refine ENNReal.ofReal_le_ofReal ?_
            rw [hCc]
            exact HkIntegrand_err_le k hC1 h1 h2 α n F hα hα1 hn hsm z hz θ hθ
        _ = ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal Cc * ENNReal.ofReal (Good α k n F z θ) := by
            refine lintegral_congr fun θ => ?_
            rw [ENNReal.ofReal_mul hCcpos]
        _ = ENNReal.ofReal Cc * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Good α k n F z θ)) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    -- ## Step 2: the majorant splits into the three groups
    have hRhoMeas : AEMeasurable (fun θ => Q * ENNReal.ofReal (rhoProf α k θ))
        (volume.restrict Work.Spaces.Iθ) := (aemeasurable_ofReal_rhoProf α k).const_mul Q
    have hQrho : ∀ θ : ℝ, ENNReal.ofReal ((∑ m ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2)
            * ((Work.Spaces.w z) ^ 2 * rhoProf α k θ)) = Q * ENNReal.ofReal (rhoProf α k θ) := by
      intro θ
      rw [hQ, ENNReal.ofReal_mul (Finset.sum_nonneg fun m _ => sq_nonneg _),
        ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z)),
        ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
      ring
    have hle : ∀ θ : ℝ, ENNReal.ofReal (Good α k n F z θ)
        ≤ (ENNReal.ofReal (omegaPart α k n F z θ)
            + ∑ s ∈ Finset.range k, ENNReal.ofReal (thShrink n θ
                * ((Work.Spaces.DzIter s F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))))
          + Q * ENNReal.ofReal (rhoProf α k θ) := by
      intro θ
      rw [Good]
      refine le_trans ENNReal.ofReal_add_le ?_
      rw [hQrho θ]
      refine add_le_add ?_ le_rfl
      refine le_trans ENNReal.ofReal_add_le ?_
      refine add_le_add le_rfl ?_
      rw [Finset.mul_sum]
      exact ofReal_sum_le _ _
    have hmid : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Good α k n F z θ))
        ≤ P + (∑ s ∈ Finset.range k, ENNReal.ofReal CH * P) + Q * RP := by
      have hsum : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Good α k n F z θ))
          ≤ ∫⁻ θ in Work.Spaces.Iθ, (ENNReal.ofReal (omegaPart α k n F z θ)
              + ∑ s ∈ Finset.range k, ENNReal.ofReal (thShrink n θ
                  * ((Work.Spaces.DzIter s F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))))
              + Q * ENNReal.ofReal (rhoProf α k θ) := lintegral_mono hle
      rw [lintegral_add_right' _ hRhoMeas] at hsum
      have hinner : (∫⁻ θ in Work.Spaces.Iθ, (ENNReal.ofReal (omegaPart α k n F z θ)
            + ∑ s ∈ Finset.range k, ENNReal.ofReal (thShrink n θ
                * ((Work.Spaces.DzIter s F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))))
          = P + ∑ s ∈ Finset.range k, (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (thShrink n θ
                * ((Work.Spaces.DzIter s F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))) := by
        rw [lintegral_add_left' (aemeasurable_ofReal_omegaPart α k n hsm hz)]
        congr 1
        refine lintegral_finsetSum' _ fun s hs => ?_
        refine (aemeasurable_ofReal_thShrink (u := fun θ => Work.Spaces.DzIter s F z θ)
          ((hsm.DzIter s).curry_θ hpos).continuousOn (n := n) (c := Work.Spaces.gam α)
          (C := (Work.Spaces.w z) ^ 2)).congr ?_
        filter_upwards with θ
        congr 1
        ring
      have hhardy : ∀ s ∈ Finset.range k,
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (thShrink n θ
              * ((Work.Spaces.DzIter s F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))))
            ≤ ENNReal.ofReal CH * P := by
        intro s hs
        have hsk : s + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.mp hs)
        have hres := hH F n s hn hsk hsm htr z (Set.mem_Ioi.mpr hpos)
        have heq : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (thShrink n θ
              * ((Work.Spaces.DzIter s F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))))
            = (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.w z) ^ 2
                * (thShrink n θ * (Work.Spaces.DzIter s F z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))) := by
          refine lintegral_congr fun θ => ?_
          congr 1
          ring
        rw [heq, hP]
        exact hres
      have hsum2 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Good α k n F z θ))
          ≤ (P + (∑ s ∈ Finset.range k, (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (thShrink n θ
                * ((Work.Spaces.DzIter s F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))))) + Q * RP := by
        rw [hinner] at hsum
        rw [lintegral_const_mul' Q _ ENNReal.ofReal_ne_top, ← hRP] at hsum
        exact hsum
      exact le_trans hsum2 (add_le_add (add_le_add le_rfl (Finset.sum_le_sum hhardy)) le_rfl)
    -- ## Step 3: `ENNReal` arithmetic
    have hsumCH : (∑ _s ∈ Finset.range k, ENNReal.ofReal CH * P)
        = ENNReal.ofReal ((k : ℝ) * CH) * P := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast (n := k),
        ← mul_assoc, ← ENNReal.ofReal_mul hkc]
    have hfin : ENNReal.ofReal Cc * (P + (∑ _s ∈ Finset.range k, ENNReal.ofReal CH * P)
          + Q * RP)
        ≤ ENNReal.ofReal (Cc * (1 + (k : ℝ) * CH) + 1) * (P + Q * RP) := by
      have h1k : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + (k : ℝ) * CH) := by
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hkc hCH])
      have hexpand : P + ENNReal.ofReal ((k : ℝ) * CH) * P
          = ENNReal.ofReal (1 + (k : ℝ) * CH) * P := by
        rw [show ENNReal.ofReal (1 + (k : ℝ) * CH)
            = 1 + ENNReal.ofReal ((k : ℝ) * CH) by
              rw [ENNReal.ofReal_add zero_le_one (mul_nonneg hkc hCH), ENNReal.ofReal_one]]
        ring
      have hstep : P + (∑ _s ∈ Finset.range k, ENNReal.ofReal CH * P) + Q * RP
          ≤ ENNReal.ofReal (1 + (k : ℝ) * CH) * (P + Q * RP) := by
        rw [hsumCH, hexpand]
        calc ENNReal.ofReal (1 + (k : ℝ) * CH) * P + Q * RP
            ≤ ENNReal.ofReal (1 + (k : ℝ) * CH) * P
                + ENNReal.ofReal (1 + (k : ℝ) * CH) * (Q * RP) := by
              refine add_le_add le_rfl ?_
              exact le_mul_of_one_le_left' h1k
          _ = ENNReal.ofReal (1 + (k : ℝ) * CH) * (P + Q * RP) := by
              rw [mul_add]
      refine le_trans (mul_le_mul_right hstep (ENNReal.ofReal Cc)) ?_
      rw [← mul_assoc, ← ENNReal.ofReal_mul hCcpos]
      refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
      linarith
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (err n F) z θ))
        ≤ ENNReal.ofReal Cc * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Good α k n F z θ)) :=
          step1
      _ ≤ ENNReal.ofReal Cc * (P + (∑ s ∈ Finset.range k, ENNReal.ofReal CH * P)
            + Q * RP) := mul_le_mul_right hmid _
      _ ≤ ENNReal.ofReal (Cc * (1 + (k : ℝ) * CH) + 1) * (P + Q * RP) := hfin
      _ = ENNReal.ofReal (2 * ((k : ℝ) + 1) ^ 2 * C1 * ((k : ℝ) * CH + 1) + 1)
            * (P + Q * RP) := by
          have : (2 * ((k : ℝ) + 1) ^ 2 * C1 * (1 + (k : ℝ) * CH) + 1)
              = 2 * ((k : ℝ) + 1) ^ 2 * C1 * ((k : ℝ) * CH + 1) + 1 := by ring
          rw [hCc, this]
      _ = ENNReal.ofReal (2 * ((k : ℝ) + 1) ^ 2 * C1 * ((k : ℝ) * CH + 1) + 1)
            * ((∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (omegaPart α k n F z θ))
              + ENNReal.ofReal ((Work.Spaces.w z) ^ 2
                  * ∑ m ∈ Finset.range (k + 1),
                      (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2)
                * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ))) := by
          rw [← hP, ← hQ, ← hRP]

end Work.FTS.PhiStar.Honesty.CptApp
end
end
