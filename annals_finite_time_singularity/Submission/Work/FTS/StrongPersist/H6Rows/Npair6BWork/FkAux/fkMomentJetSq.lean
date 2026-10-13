import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS.StrongPersist.QangAe6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkPairingSup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

/-!
# The weighted `L²`-price of the moment jet `D_z^b (FK f)`

`fkMomentJetSq` records that the `b`-th `D_z`-iterate of the angular moment `FK f` is an
element of the radial `L²(w²)`-space, priced by the full `ℋ⁶`-energy of the datum:

  `∫_z (D_z^b (FK f) z)² w(z)² dz ≤ C · HkSq α 6 f`,   `b ≤ 6`.

The proof is the two-step reduction already used for the pointwise companion
(`fkDzdIterSqLe`, `Npair6SupAux.DzIter_FK_eq_ae`):

* `D_z^b (FK f) = FK (D_z^b f)` almost everywhere in `z` (`DzIter_FK_eq_ae` composed with
  `Elliptic.DzIter_rad`), which is *exactly* what makes the weight `w²` harmless;
* the angular Cauchy–Schwarz bound `(FK (D_z^b f) z)² ≤ 16 ∫_θ (D_z^b f z θ)²`
  (`FKdzIter_sq_le`), applied at `z > 0`;
* the pointwise domination `w(z)² (D_z^b f z θ)² ≤ HkIntegrand α 6 f z θ` on the open
  quadrant (`dzIter_sq_w_sq_le_HkIntegrand_k`, since `b ≤ 6` is one of the `D_z`-slots of
  `ℋ⁶`), which after integrating in `θ` gives `∫_θ w² (D_z^b f)² ≤ ∫_θ HkIntegrand`.

The constant is the universal `16`; no `α`-dependence appears anywhere.
-/

/-- The angular moment `z ↦ FK (D_z^k f) z` of an open-quadrant datum is a.e. strongly
measurable on `Iz`: it is the `θ`-marginal of the jointly continuous (on the open quadrant)
function `(z,θ) ↦ D_z^k f z θ · K θ`. -/
private theorem aesm_FK_DzIter_aux {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (k : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => Work.Construction.FK (Work.Spaces.DzIter k f) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.DzIter k f p.1 p.2 * Work.Spaces.K p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((hF.DzIter k).continuousOn).mul (by unfold Work.Spaces.K; fun_prop)
  have hjoint := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have h := hjoint.integral_prod_right'
  simpa only [Work.Construction.FK] using h

/-- The radial weight squared, `z ↦ w z ^ 2`, is a.e. strongly measurable on `Iz` (it is
continuous on the open half-line, and `Iz` agrees with `Ioi 0` up to a null set). -/
private theorem aesm_w_sq_aux :
    MeasureTheory.AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    unfold Work.Spaces.w
    refine ContinuousOn.pow (ContinuousOn.div ?_ ?_ ?_) 2
    · fun_prop
    · fun_prop
    · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)
  have h : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    hcont.aestronglyMeasurable (μ := MeasureTheory.volume) measurableSet_Ioi
  rw [show (MeasureTheory.volume.restrict Work.Spaces.Iz)
      = MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) from
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
  exact h

theorem fkMomentJetSq : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (f : Work.FTS.Galerkin.Fn),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    ∀ (b : ℕ), b ≤ 6 →
      MeasureTheory.IntegrableOn
          (fun z => (Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z) ^ 2
            * (Work.Spaces.w z) ^ 2) ≤ C * Work.Spaces.HkSq α 6 f := by
  refine ⟨16, by norm_num, ?_⟩
  intro α hαmem f hsm hm6 b hb
  -- the a.e. identification `D_z^b (FK f) = FK (D_z^b f)`
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z
        = Work.Construction.FK (Work.Spaces.DzIter b f) z := by
    have h := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae hsm hm6 b hb
    filter_upwards [h] with z hz
    rw [← Work.Elliptic.DzIter_rad (fun w => Work.Construction.FK f w) b z 0]
    exact hz 0
  -- the a.e. pointwise domination by `16 ∫_θ HkIntegrand α 6 f`
  have hdom : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z) ^ 2
        * (Work.Spaces.w z) ^ 2
        ≤ 16 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ := by
    have hae' : ∀ᵐ z ∂(MeasureTheory.volume), z ∈ Work.Spaces.Iz →
        Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z
          = Work.Construction.FK (Work.Spaces.DzIter b f) z :=
      (MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici).mp hae
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [hae', MeasureTheory.Measure.ae_ne (MeasureTheory.volume) (0:ℝ)]
      with z he hne hzI
    have he' := he hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hne)
    -- the angular Cauchy–Schwarz bound for the moment of the `b`-th derivative
    have hFK := FKdzIter_sq_le (α := α) hsm hm6 b hb hzpos
    -- the weighted angular energy is a slot of `ℋ⁶`
    have hIle : (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter b f z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ := by
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
        (hm6.1 z hzI) ?_
      filter_upwards [ae_mem_Ioo_Iθ_k] with θ hθ
      have hsin : 0 < Real.sin (2*θ) := Real.sin_pos_of_pos_of_lt_pi
        (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      simpa only [mul_comm] using dzIter_sq_w_sq_le_HkIntegrand_k α 6 f z θ hsin b hb
    calc (Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z) ^ 2
          * (Work.Spaces.w z) ^ 2
        = (Work.Construction.FK (Work.Spaces.DzIter b f) z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
          rw [he']
      _ ≤ (16 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
            * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hFK (sq_nonneg _)
      _ = 16 * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter b f z θ) ^ 2) := by
          rw [MeasureTheory.integral_const_mul]; ring
      _ ≤ 16 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ :=
          mul_le_mul_of_nonneg_left hIle (by norm_num)
  -- a.e. strong measurability of the integrand
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => (Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => (Work.Construction.FK (Work.Spaces.DzIter b f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (aesm_FK_DzIter_aux hsm b).pow 2 |>.mul aesm_w_sq_aux
    refine h1.congr ?_
    filter_upwards [hae] with z hz
    rw [hz]
  have hint : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' (hm6.2.const_mul 16) haesm ?_
    filter_upwards [hdom] with z hz
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hz
  refine ⟨hint, ?_⟩
  have hmain : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z) ^ 2
          * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz,
          16 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      (hm6.2.const_mul 16) hdom
  refine le_trans hmain ?_
  rw [MeasureTheory.integral_const_mul, Work.Spaces.HkSq]

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
