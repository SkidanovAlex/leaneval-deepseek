import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.GalFields.RHS.SharpAux.HonTerms.Base
import Submission.Work.FTS.GalFields.Tail.FK_Fstar_add
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.Nonlinear.Open.PiecesHkOpen
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.Physical.BiotSavart.bsAdmissibleStripFull_comp_clock
import Submission.Work.FTS.RegPkgGal.GalMinAssembly
import Submission.Work.FTS.RegPkgGal.GalMinConv
import Submission.Work.FTS.RegPkgGal.PartsAssembly
import Submission.Work.FTS.RegPkgGal.R5Parts
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_LocDatum3a.Assembly
import Submission.Work.FTS_LocDatum3a.L12_Jeps_interchange_mine
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.FTS_RegExport.RX0.sup2_extG_ext_hIS
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXB.l12_zero_lim_proved
import Submission.Work.FTS_RegExport.RXR1.pzIter_bound_weighted
import Submission.Work.FTS_RegExport.RXR1.slice_diff_weighted
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.st1_fb_theta
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.Supp
import Submission.Work.FTS_RegExport.VPDefs
import Submission.Work.FTS_StreamBdry.SB4.lim_mixed_plainE
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
-- ===== merged: Submission.Work.FTS.GalFields.RHS.SharpAux.Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS.Sharp

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-! ## The twenty terms as a list -/

/-- The twenty monomials of the difference, in the order of the identity. -/
def termList (α : ℝ) (Φs : Fn) (EllSol : Fn → Fn) (g g' h : Fn) : List Fn :=
  [TRA α Φs h, TRB α EllSol g' h, TRC α EllSol h, TRD α EllSol g h,
   TUA α Φs h, TUB α EllSol g' h, TUC α EllSol h, TUD α EllSol g h,
   TVA α Φs h, TVB α EllSol g' h, TVC α EllSol h, TVD α EllSol g h,
   TDA α h, TDB α g' h, TDC α h, TDD α g h,
   TEA α h, TEB α g' h, TEC α h, TED α g h]

/-- The folded sum of the list is the left-associated chain of the identity. -/
theorem termList_foldr (α : ℝ) (Φs : Fn) (EllSol : Fn → Fn) (g g' h : Fn) :
    (termList α Φs EllSol g g' h).foldr (fun f acc => f + acc) (0 : Fn)
      = (TRA α Φs h + TRB α EllSol g' h + TRC α EllSol h + TRD α EllSol g h
        + TUA α Φs h + TUB α EllSol g' h + TUC α EllSol h + TUD α EllSol g h
        + TVA α Φs h + TVB α EllSol g' h + TVC α EllSol h + TVD α EllSol g h
        + TDA α h + TDB α g' h + TDC α h + TDD α g h
        + TEA α h + TEB α g' h + TEC α h + TED α g h) := by
  simp only [termList, List.foldr_cons, List.foldr_nil]
  abel

/-- The length of the term list is `20`. -/
theorem termList_length (α : ℝ) (Φs : Fn) (EllSol : Fn → Fn) (g g' h : Fn) :
    (termList α Φs EllSol g g' h).length = 20 := rfl

/-! ## Sums over lists -/

/-- The sum of a list of `SmoothOpen` functions is `SmoothOpen`. -/
theorem smoothOpen_listFoldr (L : List Fn)
    (hS : ∀ f ∈ L, Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (L.foldr (fun f acc => f + acc) (0 : Fn)) := by
  induction L with
  | nil =>
      have h0 : ([] : List Fn).foldr (fun f acc => f + acc) (0 : Fn) = fun _ _ => (0 : ℝ) := rfl
      rw [h0, Work.FTS.EllipticEst.SmoothOpen]
      exact (contDiffOn_const (c := (0 : ℝ)) (s := Work.FTS.EllipticEst.Q0)).congr
        (fun p _ => rfl)
  | cons f L ih =>
      rw [List.foldr_cons]
      exact Work.FTS.EllipticEst.smoothOpen_add (hS f (by simp))
        (ih (fun a ha => hS a (by simp [ha])))

/-- The sum of a list of `HkMem α 4` functions is `HkMem α 4`. -/
theorem HkMem_listFoldr {α : ℝ} (L : List Fn)
    (hS : ∀ f ∈ L, Work.FTS.EllipticEst.SmoothOpen f)
    (hM : ∀ f ∈ L, Work.Spaces.HkMem α 4 f) :
    Work.Spaces.HkMem α 4 (L.foldr (fun f acc => f + acc) (0 : Fn)) := by
  induction L with
  | nil =>
      have h0 : ([] : List Fn).foldr (fun f acc => f + acc) (0 : Fn) = fun _ _ => (0 : ℝ) := rfl
      rw [h0]
      exact Work.FTS.LocData.HkMem_zero_fun α 4
  | cons f L ih =>
      rw [List.foldr_cons]
      exact Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 (hS f (by simp))
        (smoothOpen_listFoldr L (fun a ha => hS a (by simp [ha])))
        (hM f (by simp)) (ih (fun a ha => hS a (by simp [ha])) (fun a ha => hM a (by simp [ha])))

/-- **The `ℋ⁴`-norm of a list-sum**: with the factor `2^{length}`. -/
theorem HkNorm_listFoldr_le {α : ℝ} (hα : 0 < α) (L : List Fn)
    (hS : ∀ f ∈ L, Work.FTS.EllipticEst.SmoothOpen f)
    (hM : ∀ f ∈ L, Work.Spaces.HkMem α 4 f) :
    Work.FTS.Nonlin.Xn α (L.foldr (fun f acc => f + acc) (0 : Fn))
      ≤ 2 ^ L.length * (L.foldr (fun f acc => Work.FTS.Nonlin.Xn α f + acc) 0) := by
  induction L with
  | nil =>
      have h0 : ([] : List Fn).foldr (fun f acc => f + acc) (0 : Fn) = fun _ _ => (0 : ℝ) := rfl
      rw [h0, List.length_nil, List.foldr_nil, pow_zero, one_mul]
      have hz : Work.FTS.Nonlin.Xn α (fun _ _ => (0 : ℝ)) = 0 := by
        simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, Work.Spaces.HkSq]
        rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (fun _ _ => (0 : ℝ)) z θ) = fun _ => (0 : ℝ) from by
          funext z
          simp only [Work.FTS.GalFields.RHS.HkIntegrand_zero_fun, MeasureTheory.integral_zero]]
        simp
      rw [hz]
  | cons f L ih =>
      rw [List.foldr_cons, List.length_cons, List.foldr_cons]
      have hfl : ∀ a ∈ L, Work.FTS.EllipticEst.SmoothOpen a := fun a ha => hS a (by simp [ha])
      have hml : ∀ a ∈ L, Work.Spaces.HkMem α 4 a := fun a ha => hM a (by simp [ha])
      have hsmS := smoothOpen_listFoldr L hfl
      have hmS := HkMem_listFoldr L hfl hml
      have hstep := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα (hS f (by simp)) hsmS
        (hM f (by simp)) hmS
      have hih := ih hfl hml
      have hpow : (1 : ℝ) ≤ 2 ^ L.length := one_le_pow₀ (by norm_num)
      have hXf : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
      have hsum0 : 0 ≤ L.foldr (fun f acc => Work.FTS.Nonlin.Xn α f + acc) 0 := by
        have : ∀ (M : List Fn), 0 ≤ M.foldr (fun f acc => Work.FTS.Nonlin.Xn α f + acc) 0 := by
          intro M
          induction M with
          | nil => simp
          | cons a M ih2 =>
              rw [List.foldr_cons]
              exact add_nonneg (Work.Spaces.HkNorm_nonneg α 4 a) ih2
        exact this L
      calc Work.FTS.Nonlin.Xn α
            ((f :: L).foldr (fun f acc => f + acc) (0 : Fn))
          = Work.FTS.Nonlin.Xn α (f + L.foldr (fun f acc => f + acc) (0 : Fn)) := by
            rw [List.foldr_cons]
        _ ≤ 2 * (Work.FTS.Nonlin.Xn α f
              + Work.FTS.Nonlin.Xn α (L.foldr (fun f acc => f + acc) (0 : Fn))) := hstep
        _ ≤ 2 * (Work.FTS.Nonlin.Xn α f
              + 2 ^ L.length * (L.foldr (fun f acc => Work.FTS.Nonlin.Xn α f + acc) 0)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact add_le_add (le_refl _) hih
        _ ≤ 2 ^ (L.length + 1)
              * (Work.FTS.Nonlin.Xn α f + L.foldr (fun f acc => Work.FTS.Nonlin.Xn α f + acc) 0) := by
            rw [pow_succ]
            nlinarith [hpow, hXf, hsum0]
        _ = 2 ^ (f :: L).length
              * ((f :: L).foldr (fun f acc => Work.FTS.Nonlin.Xn α f + acc) 0) := by
            rw [List.length_cons, List.foldr_cons]

end Work.FTS.GalFields.RHS.Sharp
end
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.SharpAux.HonestTermsBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS.SharpAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000


end Work.FTS.GalFields.RHS.SharpAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Work.Certificate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Work

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## Small API: `SmoothOpen` is stable under scalar multiplication -/


/-! ## The datum-side hypotheses of `EpsUniformMem` do not force the `C₀`-ball

The first theorem is the crux: from the conclusion of `EpsE4` (plus the datum's `hd`) one derives
`Xn α g₀ ≤ √2 C₀ α²`.  It is the composition of the two delegated lemmas
(`epsUniformMem_Jeps_bound`: the `τ = 0` clause reads `Xn α (Jeps ρ ε g₀) ≤ C₀ α²`;
`Xn_le_sqrt_two_mul_of_Jeps_bound`: the mollifier-approximation estimate upgrades this to the
bound on `Xn α g₀`). -/


/-! ## An admissible datum of size exactly `α²`

The project's own datum `locG6 α L β` (with the `L₁₂`-condition produced by
`LocData6.locG6_data`) is admissible for every `ε > 0` (`FTS_LocDatum3a.locG6_epsDatum`) and has
positive `ℋ⁴`-size (its value at `(2L+1, π/4)` is `⁻(α/c)·Fstar(2L+1)·Gam(π/4) ≠ 0`, and the
`ℋ⁴`-integrand is continuous and positive there).  Rescaling it by
`c := α² / Xn α (locG6 α L β)` gives a datum of `ℋ⁴`-size exactly `α²`, admissible for every `ε`
(the class `EpsDatum` is scale-invariant) and vanishing on the angular boundary. -/




end Work.FTS.StrongEps.EpsE4Work
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.GfKer_aesm_slices =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Measurability and slice integrability of the Tonelli kernel `GfKer`

The joint kernel of the Tonelli step in `Gf_le` is

  `GfKer α U t z = 1_{t<z} · ζ(z) · φ(t)`,  `ζ = GfZeta α`,  `φ = GfPhi α U`

(see `Gf_le_defs`).  This file proves the two measure-theoretic prerequisites of that step:

* `Function.uncurry (GfKer α U)` is a.e. strongly measurable for the product of the two restricted
  measures on `(0,∞)`;
* for every `t > 0` the `z`-slice `z ↦ GfKer α U t z` is integrable on `(0,∞)`.

The first is measurability bookkeeping (`mass_aesm` for the `t`-factor, continuity of `ζ` on
`(0,∞)` for the `z`-factor and the Borel set `{t < z}`); the second uses that the slice is
supported on `(t,∞)`, where `ζ(z) = w(z)²z^{-(β+1)}` is dominated by `(1+1/t)⁴ z^{-(β+1)}`,
an integrable power since `β > 0` for `0 < α ≤ 1`.
-/

namespace Work.FTS_EllLimOK.ProducerH

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The `z`-factor `ζ = GfZeta` -/

/-- The `z`-factor `ζ(z) = w(z)²|z|^{-(β+1)}` of the kernel is continuous on `(0,∞)`. -/
theorem continuousOn_GfZeta (α : ℝ) :
    ContinuousOn (fun z : ℝ => GfZeta α z) (Set.Ioi 0) := by
  have hbase : ContinuousOn
      (fun z : ℝ => (Work.Spaces.w z) ^ 2 * z ^ (-(beta α + 1))) (Set.Ioi 0) := by
    refine continuousOn_w_sq.mul ?_
    exact (continuous_id.continuousOn).rpow_const (fun x hx => Or.inl (ne_of_gt hx))
  refine hbase.congr (fun z hz => ?_)
  unfold GfZeta
  rw [abs_of_pos (show (0 : ℝ) < z from hz)]

/-- **`ζ` is integrable on `(t,∞)` for `t > 0`** (with `β > 0`): on that half-line
`ζ(z) = w(z)²z^{-(β+1)}` is dominated by the integrable power `(1+1/t)⁴ z^{-(β+1)}`, because
`w(z) = (1+1/z)² ≤ (1+1/t)²` for `z ≥ t`. -/
theorem integrableOn_GfZeta (α : ℝ) (hβ : 0 < beta α) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun z : ℝ => GfZeta α z) (Set.Ioi t) := by
  have href : IntegrableOn (fun z : ℝ => z ^ (-(beta α + 1))) (Set.Ioi t) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) ht
  have hg : Integrable (fun z : ℝ => (1 + 1 / t) ^ 4 * z ^ (-(beta α + 1)))
      (volume.restrict (Set.Ioi t)) := href.const_mul ((1 + 1 / t) ^ 4)
  have hf : AEStronglyMeasurable (fun z : ℝ => GfZeta α z) (volume.restrict (Set.Ioi t)) :=
    ((continuousOn_GfZeta α).mono (Set.Ioi_subset_Ioi (le_of_lt ht))).aestronglyMeasurable
      measurableSet_Ioi
  refine Integrable.mono' hg hf ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  have hzt : t < z := hz
  have hz0 : 0 < z := lt_trans ht hzt
  have h1 : (1 : ℝ) + 1 / z ≤ 1 + 1 / t := by
    have h := one_div_le_one_div_of_le ht (le_of_lt hzt)
    linarith
  have h2 : 0 ≤ (1 : ℝ) + 1 / z := by positivity
  have hwz : Work.Spaces.w z = (1 + 1 / z) ^ 2 := by
    rw [Work.Spaces.w, ← div_pow]
    congr 1
    rw [add_div, div_self (ne_of_gt hz0)]
    ring
  have hw2 : (Work.Spaces.w z) ^ 2 ≤ (1 + 1 / t) ^ 4 := by
    have h3 : ((1 + 1 / z) ^ 2) ^ 2 ≤ ((1 + 1 / t) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ h2 h1 2) 2
    calc (Work.Spaces.w z) ^ 2 = ((1 + 1 / z) ^ 2) ^ 2 := by rw [hwz]
      _ ≤ ((1 + 1 / t) ^ 2) ^ 2 := h3
      _ = (1 + 1 / t) ^ 4 := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg (GfZeta_nonneg α z)]
  unfold GfZeta
  rw [abs_of_pos hz0]
  exact mul_le_mul_of_nonneg_right hw2 (Real.rpow_nonneg (le_of_lt hz0) (-(beta α + 1)))

/-! ## Joint a.e. strong measurability -/

/-- **Joint a.e. strong measurability of the kernel.**  For `U ∈ ℋ⁰` the function
`(t,z) ↦ GfKer α U t z` is a.e. strongly measurable for the product of the restricted measures
on `(0,∞)`. -/
theorem GfKer_uncurry_aesm (α : ℝ) {U : ℝ → ℝ → ℝ} (hU : Work.Spaces.HkMem α 0 U) :
    MeasureTheory.AEStronglyMeasurable (Function.uncurry (GfKer α U))
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioi 0))) := by
  have hζ : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => GfZeta α z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (continuousOn_GfZeta α).aestronglyMeasurable measurableSet_Ioi
  have hmass : MeasureTheory.AEStronglyMeasurable (mass α U)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := mass_aesm α U hU
  have habs : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => |t| ^ (beta α + 4))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have hcont : ContinuousOn (fun t : ℝ => t ^ (beta α + 4)) (Set.Ioi 0) :=
      (continuous_id.continuousOn).rpow_const (fun x hx => Or.inl (ne_of_gt hx))
    refine (hcont.aestronglyMeasurable measurableSet_Ioi).congr ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
    show t ^ (beta α + 4) = |t| ^ (beta α + 4)
    rw [abs_of_pos (show (0 : ℝ) < t from ht)]
  have hden : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => ((1 + t) ^ 4)⁻¹)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have hc : ContinuousOn (fun t : ℝ => (1 + t) ^ 4) (Set.Ioi 0) :=
      ((continuous_const.add continuous_id).pow 4).continuousOn
    exact (hc.inv₀ (fun t ht => pow_ne_zero 4 (by linarith [show (0 : ℝ) < t from ht]))).aestronglyMeasurable
      measurableSet_Ioi
  have hφ : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => GfPhi α U t)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have hprod : MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ => |t| ^ (beta α + 4) * mass α U t * ((1 + t) ^ 4)⁻¹)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := (habs.mul hmass).mul hden
    refine hprod.congr ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t _ => ?_)
    show |t| ^ (beta α + 4) * mass α U t * ((1 + t) ^ 4)⁻¹
        = |t| ^ (beta α + 4) * mass α U t / (1 + t) ^ 4
    rw [div_eq_mul_inv]
  have hζ2 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => GfZeta α p.2)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioi 0))) := hζ.comp_snd
  have hφ2 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => GfPhi α U p.1)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioi 0))) := hφ.comp_fst
  have hind : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => if p.1 < p.2 then (1 : ℝ) else 0)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioi 0))) := by
    have hset : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
      measurableSet_lt measurable_fst measurable_snd
    exact (Measurable.ite hset measurable_const measurable_const).aestronglyMeasurable
  show MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ((if p.1 < p.2 then 1 else 0) * GfZeta α p.2) * GfPhi α U p.1)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioi 0)))
  exact (hind.mul hζ2).mul hφ2

/-! ## Integrability of the `z`-slices -/

/-- **The `z`-slices of the kernel are integrable.**  For `0 < α ≤ 1` and every `t > 0` the
function `z ↦ GfKer α U t z` is integrable on `(0,∞)`: it is supported on `(t,∞)` — where `ζ` is
integrable — and equals `ζ` there up to the multiplicative constant `φ(t)`. -/
theorem GfKer_slice_integrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (U : ℝ → ℝ → ℝ)
    {t : ℝ} (ht : 0 < t) :
    MeasureTheory.Integrable (GfKer α U t)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hZetat : IntegrableOn (fun z : ℝ => GfZeta α z) (Set.Ioi t) :=
    integrableOn_GfZeta α (beta_pos hα hα1) ht
  have hOn_t : IntegrableOn (fun z : ℝ => (if t < z then 1 else 0) * GfZeta α z)
      (Set.Ioi t) := by
    refine hZetat.congr_fun ?_ measurableSet_Ioi
    intro z hz
    show GfZeta α z = (if t < z then 1 else 0) * GfZeta α z
    rw [ite_eq_left (show t < z from hz), one_mul]
  have hmain : Integrable (fun z : ℝ => (if t < z then 1 else 0) * GfZeta α z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hOn_t.of_forall_sdiff_eq_zero measurableSet_Ioi (fun x hx => by
      have hx2 : ¬ (t < x) := hx.2
      rw [ite_eq_right hx2, zero_mul])
  have hfin : Integrable (fun z : ℝ => ((if t < z then 1 else 0) * GfZeta α z)
      * GfPhi α U t) (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hmain.mul_const (GfPhi α U t)
  show Integrable (fun z : ℝ => ((if t < z then 1 else 0) * GfZeta α z) * GfPhi α U t)
      (MeasureTheory.volume.restrict (Set.Ioi 0))
  exact hfin

/-! ## The requested lemma -/

theorem GfKer_aesm_slices {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {U : ℝ → ℝ → ℝ}
    (hU : Work.Spaces.HkMem α 0 U) :
    MeasureTheory.AEStronglyMeasurable (Function.uncurry (GfKer α U))
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod (MeasureTheory.volume.restrict (Set.Ioi 0))) ∧
      (∀ t ∈ Set.Ioi (0 : ℝ), MeasureTheory.Integrable (GfKer α U t)
        (MeasureTheory.volume.restrict (Set.Ioi 0))) :=
  ⟨GfKer_uncurry_aesm α hU, fun _ ht => GfKer_slice_integrable hα hα1 U ht⟩

end Work.FTS_EllLimOK.ProducerH
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.GfKer_touter_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `t`-outer slice of the Tonelli kernel

This module proves the `t`-outer bound for the joint Tonelli kernel
`GfKer α U t z = 1_{t<z} · ζ(z) · φ(t)` of `Gf_le_defs`:

  `∫_{z>0} GfKer α U t z dz ≤ A(t)/β`,  `A = mass α U`,  `β = beta α = 3/α - 1`,
  (`0 < α ≤ 1`, `t > 0`).

This is the first of the two estimates that make the Tonelli step in `Gf_le` work (the
other is the identification `z ↦ ∫_t GfKer α U t z = Gf α U z`).

Mathematically: `φ(t) = t^{β+4} A(t)/(1+t)^4` and `ζ(z) = w(z)² z^{-(β+1)}`, with
`w(z)² z⁴ = (1+z)⁴`; for `z ≥ t > 0` the weight monotonicity `w(z)² ≤ w(t)²`
(`z ↦ (1+1/z)²` is decreasing) bounds the `z`-integral by
`ζ(t)`-normalised: `∫_{z>t} ζ ≤ w(t)² ∫_{z>t} z^{-(β+1)} = w(t)² t^{-β}/β`, and
`(t^{β+4}/(1+t)^4)·(w(t)² t^{-β}) = 1`, so the product collapses to `A(t)/β`.

The statement is unconditional in `U` (no `ℋ⁰` hypothesis is needed for this half; only
nonnegativity of `mass` enters).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS_EllLimOK.ProducerH

/-- **The `t`-outer bound for the Tonelli kernel.**  For `0 < α ≤ 1` and `t > 0`,

  `∫_{z>0} GfKer α U t z dz ≤ mass α U t / beta α`.

Route: `GfKer` vanishes for `z ≤ t`, so the integral over `(0,∞)` is an integral over
`(t,∞)`; there `w(z)² ≤ w(t)²` and `ζ(z) ≤ w(t)² z^{-(β+1)}`, whose integral is
`w(t)² t^{-β}/β` (`integral_Ioi_rpow_of_lt`); the `t`-factor `φ(t) = t^{β+4}A(t)/(1+t)^4`
times `w(t)² = (1+t)^4/t^4` and `t^{-β}` is exactly `1/β` times `A(t)`. -/
theorem GfKer_touter_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {U : ℝ → ℝ → ℝ}
    {t : ℝ} (ht : 0 < t) :
    ∫ z, GfKer α U t z ∂(MeasureTheory.volume.restrict (Set.Ioi 0))
      ≤ mass α U t / beta α := by
  have hβ : 0 < beta α := beta_pos hα hα1
  have hlt : -(beta α + 1) < -1 := by linarith
  -- `w(t)² = (1+t)⁴/t⁴`
  have hw2 : (Work.Spaces.w t) ^ 2 = (1 + t) ^ 4 / t ^ 4 := by
    rw [eq_div_iff (pow_ne_zero 4 (ne_of_gt ht))]
    exact w_sq_mul_z4 (ne_of_gt ht)
  -- the pointwise bound for the `z`-factor on `z > t`
  have hGZle : ∀ z ∈ Set.Ioi t,
      GfZeta α z ≤ (Work.Spaces.w t) ^ 2 * z ^ (-(beta α + 1)) := by
    intro z hz
    have hzt : 0 < z := lt_trans ht hz
    have hwt : Work.Spaces.w t = (1 + 1 / t) ^ 2 := by
      rw [Work.Spaces.w, ← div_pow]; congr 1; field_simp; ring
    have hwz : Work.Spaces.w z = (1 + 1 / z) ^ 2 := by
      rw [Work.Spaces.w, ← div_pow]; congr 1; field_simp; ring
    have h1 : (1 : ℝ) + 1 / z ≤ 1 + 1 / t := by
      have := one_div_le_one_div_of_le ht (le_of_lt hz)
      linarith
    have h2 : (0 : ℝ) ≤ 1 + 1 / z := by
      have : 0 < 1 / z := by positivity
      linarith
    have hwle' : Work.Spaces.w z ≤ Work.Spaces.w t := by
      rw [hwz, hwt]
      exact pow_le_pow_left₀ h2 h1 2
    have hwle : (Work.Spaces.w z) ^ 2 ≤ (Work.Spaces.w t) ^ 2 :=
      pow_le_pow_left₀ (by rw [hwz]; positivity) hwle' 2
    simp only [GfZeta, abs_of_pos hzt]
    exact mul_le_mul_of_nonneg_right hwle (Real.rpow_nonneg (le_of_lt hzt) _)
  -- integrability of the dominating function on `(t,∞)`
  have hBint : IntegrableOn (fun z : ℝ => (Work.Spaces.w t) ^ 2 * z ^ (-(beta α + 1)))
      (Set.Ioi t) :=
    (integrableOn_Ioi_rpow_of_lt hlt ht).const_mul _
  -- continuity of the `z`-factor on `(t,∞)`
  have hcont : ContinuousOn (fun z : ℝ => GfZeta α z) (Set.Ioi t) := by
    have h1 : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi t) := by
      have hb : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi t) :=
        ContinuousOn.div (((continuous_const.add continuous_id).pow 2).continuousOn)
          ((continuous_id.pow 2).continuousOn)
          (fun z hz => pow_ne_zero 2 (ne_of_gt (lt_trans ht hz)))
      have h2 : ContinuousOn ((fun z : ℝ => (1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Ioi t) := hb.pow 2
      convert h2 using 1
      funext z
      simp only [Work.Spaces.w, Pi.pow_apply]
    have h2 : ContinuousOn (fun z : ℝ => |z| ^ (-(beta α + 1))) (Set.Ioi t) := by
      intro z hz
      exact ((Real.continuousAt_rpow_const _ _
        (Or.inl (abs_ne_zero.mpr (ne_of_gt (lt_trans ht hz))))).comp
        continuous_abs.continuousAt).continuousWithinAt
    convert h1.mul h2 using 1
    funext z
    simp only [GfZeta, Pi.mul_apply]
  have hGZint : IntegrableOn (fun z : ℝ => GfZeta α z) (Set.Ioi t) := by
    refine Integrable.mono' hBint (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [Real.norm_of_nonneg (GfZeta_nonneg α z)]
    exact hGZle z hz
  have hmono : ∫ z in Set.Ioi t, GfZeta α z ≤
      ∫ z in Set.Ioi t, (Work.Spaces.w t) ^ 2 * z ^ (-(beta α + 1)) :=
    setIntegral_mono_on hGZint hBint measurableSet_Ioi hGZle
  -- the value of the dominating integral
  have hval : ∫ z in Set.Ioi t, (Work.Spaces.w t) ^ 2 * z ^ (-(beta α + 1))
      = (Work.Spaces.w t) ^ 2 * t ^ (-(beta α)) / beta α := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt ht]
    rw [show -(beta α + 1) + 1 = -(beta α) from by ring, neg_div_neg_eq, mul_div_assoc]
  -- `GfKer` vanishes for `z ≤ t`
  have hvan : ∫ z in Set.Ioi (0 : ℝ), GfKer α U t z = ∫ z in Set.Ioi t, GfKer α U t z := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi ht.le) ?_
    intro z hz
    have hzt : ¬ t < z := fun h => hz.2 h
    simp [GfKer, hzt]
  -- on `(t,∞)` the kernel is the `t`-factor times the `z`-factor
  have hcongr : ∫ z in Set.Ioi t, GfKer α U t z
      = ∫ z in Set.Ioi t, GfPhi α U t * GfZeta α z := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    rw [GfKer, ite_eq_left (show t < z from hz)]; ring
  have harith : GfPhi α U t * ((Work.Spaces.w t) ^ 2 * t ^ (-(beta α)) / beta α)
      = mass α U t / beta α := by
    rw [GfPhi_eq_of_pos α U ht, hw2]
    have hpow : t ^ (beta α + 4) * t ^ (-(beta α)) = t ^ 4 := by
      rw [← Real.rpow_add ht]; norm_num
    field_simp
    have heq : t ^ (beta α + 4) * mass α U t * t ^ (-(beta α))
        = mass α U t * (t ^ (beta α + 4) * t ^ (-(beta α))) := by ring
    rw [heq, hpow]
  calc ∫ z, GfKer α U t z ∂(MeasureTheory.volume.restrict (Set.Ioi 0))
      = ∫ z in Set.Ioi (0 : ℝ), GfKer α U t z := rfl
    _ = ∫ z in Set.Ioi t, GfKer α U t z := hvan
    _ = ∫ z in Set.Ioi t, GfPhi α U t * GfZeta α z := hcongr
    _ = GfPhi α U t * ∫ z in Set.Ioi t, GfZeta α z := integral_const_mul _ _
    _ ≤ GfPhi α U t * ((Work.Spaces.w t) ^ 2 * t ^ (-(beta α)) / beta α) := by
        apply mul_le_mul_of_nonneg_left _ (GfPhi_nonneg α U t)
        calc ∫ z in Set.Ioi t, GfZeta α z
            ≤ ∫ z in Set.Ioi t, (Work.Spaces.w t) ^ 2 * z ^ (-(beta α + 1)) := hmono
          _ = (Work.Spaces.w t) ^ 2 * t ^ (-(beta α)) / beta α := hval
    _ = mass α U t / beta α := harith

end Work.FTS_EllLimOK.ProducerH
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.GfKer_zslice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `z`-slice of the Tonelli kernel of `Gf`

The joint kernel of the Tonelli step computing `Gf α U z = w(z)² ∫₀¹ v^β M₁(zv) dv` is

  `GfKer α U t z = 1_{t<z} · ζ(z) · φ(t)`   (`ζ = GfZeta`, `φ = GfPhi`).

Here we prove the identity that identifies the `z`-slice of that kernel with `Gf`:

  `∫_{(0,∞)} GfKer α U t z dt = Gf α U z`   for `z > 0`,

with **no** regularity hypothesis on `U` (both the substitution `t = zv`, `mom_subst`, and the
indicator/pull-out steps are exact identities of Bochner integrals).  The pointwise input is

  `GfPhi α U t = t^β M₁(t)`   for `t > 0`   (`GfPhi_eq_rpow_mom`),

which combines `GfPhi_eq_of_pos`, `mass_eq_w2_mom` and `w_sq_mul_z4`.
-/
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH

/-- On `t > 0` the `t`-factor of the Tonelli kernel is exactly `t^β M₁(t)`. -/
theorem GfPhi_eq_rpow_mom (α : ℝ) (U : ℝ → ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    GfPhi α U t = t ^ beta α * mom U t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hw2 : (Work.Spaces.w t) ^ 2 = (1 + t) ^ 4 / t ^ 4 := by
    rw [eq_div_iff (pow_ne_zero 4 ht0), w_sq_mul_z4 ht0]
  rw [GfPhi_eq_of_pos α U ht, mass_eq_w2_mom, hw2, Real.rpow_add ht]
  field_simp
  rw [Real.rpow_ofNat]

/-- The `0..z` form of the inner integral of `Gf`, obtained from the substitution `t = zv`. -/
theorem integral_zero_z_eq (α : ℝ) (U : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z) :
    ∫ t in (0 : ℝ)..z, t ^ beta α * mom U t
      = z ^ (beta α + 1) * ∫ v in (0 : ℝ)..1, v ^ beta α * mom U (z * v) := by
  have hp : z ^ (beta α + 1) * z ^ (-(beta α + 1)) = 1 := by
    rw [← Real.rpow_add hz, add_neg_cancel, Real.rpow_zero]
  rw [mom_subst α U hz, ← mul_assoc, hp, one_mul]

/-- The `z`-slice of the Tonelli kernel integrates to `Gf`. -/
theorem GfKer_zslice {α : ℝ} {U : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z) :
    ∫ t, GfKer α U t z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)) = Gf α U z := by
  have hker : (fun t => GfKer α U t z)
      = (Set.Iio z).indicator (fun t => GfZeta α z * GfPhi α U t) := by
    funext t
    simp only [GfKer, Set.indicator_apply, Set.mem_Iio]
    by_cases h : t < z <;> simp only [h, ite_true, ite_false, one_mul, zero_mul]
  have hset : Set.Ioi (0 : ℝ) ∩ Set.Iio z = Set.Ioo 0 z := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio, Set.mem_Ioo]
  have hred : ∫ t, GfKer α U t z ∂(MeasureTheory.volume.restrict (Set.Ioi 0))
      = GfZeta α z * ∫ t in (0 : ℝ)..z, t ^ beta α * mom U t := by
    rw [hker, MeasureTheory.setIntegral_indicator measurableSet_Iio, hset]
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      (fun t ht => GfPhi_eq_rpow_mom α U ht.1)]
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (le_of_lt hz)]
  rw [hred, integral_zero_z_eq α U hz, Gf, GfZeta, abs_of_pos hz]
  have hp : z ^ (-(beta α + 1)) * z ^ (beta α + 1) = 1 := by
    rw [← Real.rpow_add hz, neg_add_cancel, Real.rpow_zero]
  rw [show (Work.Spaces.w z ^ 2 * z ^ (-(beta α + 1)))
          * (z ^ (beta α + 1) * ∫ v in (0 : ℝ)..1, v ^ beta α * mom U (z * v))
        = Work.Spaces.w z ^ 2 * (z ^ (-(beta α + 1)) * z ^ (beta α + 1))
            * ∫ v in (0 : ℝ)..1, v ^ beta α * mom U (z * v) from by ring,
      hp, mul_one]

end Work.FTS_EllLimOK.ProducerH
end
end
-- ===== merged: Submission.Work.FTS_MuLipC.Poly1.n_poly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS_MuLipC.Poly1

open Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Locality of `∂_z`, `∂_θ` and of `ℛ`, `𝒰`, `𝒱` on the open quadrant

All the identities below hold on the open quadrant `Q0 = {z > 0, 0 < θ < π/2}`; the operators
`ℛ`, `𝒰`, `𝒱` are built from the *pointwise* data `Ψ(z,θ)`, `∂_zΨ(z,θ)`, `∂_θΨ(z,θ)`, so two
stream profiles that agree on the open quadrant (which is an open neighbourhood of every
interior point) produce the same value of the operator there.  This is what lets the split
`Φ̃_{F_*+u} = Φ̃_{F_*} + U_u` (which is only available at `z > 0`, where `L₁₂` is additive) be
transported through `ℛ`, `𝒰`, `𝒱`. -/

theorem pz_congr_Q0 {f g : Fn} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    Work.Spaces.pz f z θ = Work.Spaces.pz g z θ := by
  have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ⟩
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ Work.FTS.EllipticEst.Q0 :=
    (Continuous.prodMk_left θ).continuousAt.eventually
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzθ)
  have hev : (fun z' => f z' θ) =ᶠ[𝓝 z] (fun z' => g z' θ) :=
    hnb.mono fun z' hz' => h z' θ hz'.1 hz'.2.1 hz'.2.2
  simpa only [Work.Spaces.pz] using hev.deriv_eq

theorem pth_congr_Q0 {f g : Fn} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    Work.Spaces.pth f z θ = Work.Spaces.pth g z θ := by
  have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ⟩
  have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ Work.FTS.EllipticEst.Q0 :=
    (Continuous.prodMk_right z).continuousAt.eventually
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzθ)
  have hev : (fun θ' => f z θ') =ᶠ[𝓝 θ] (fun θ' => g z θ') :=
    hnb.mono fun θ' hθ' => h z θ' hθ'.1 hθ'.2.1 hθ'.2.2
  simpa only [Work.Spaces.pth] using hev.deriv_eq

/-- `ℛ` depends on `Ψ` only through the open quadrant. -/
theorem Rop_congr_Q0 {α : ℝ} {f g : Fn} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    Work.Construction.Rop α f z θ = Work.Construction.Rop α g z θ := by
  have hpz := pz_congr_Q0 hz hθ h
  have hpth := pth_congr_Q0 hz hθ h
  simp only [Work.Construction.Rop, hpz, hpth, h z θ hz hθ.1 hθ.2]

/-- `𝒰` depends on `Ψ` only through the open quadrant. -/
theorem Uop_congr_Q0 {α : ℝ} {f g : Fn} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    Work.Construction.Uop α f z θ = Work.Construction.Uop α g z θ := by
  have hpz := pz_congr_Q0 hz hθ h
  simp only [Work.Construction.Uop, hpz, h z θ hz hθ.1 hθ.2]

/-- `𝒱` depends on `Ψ` only through the open quadrant. -/
theorem Vop_congr_Q0 {f g : Fn} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    Work.Construction.Vop f z θ = Work.Construction.Vop g z θ := by
  have hpth := pth_congr_Q0 hz hθ h
  simp only [Work.Construction.Vop, hpth, h z θ hz hθ.1 hθ.2]

/-! ## Smoothness of the perturbative stream function and additivity of `FK` -/


/-- `U_g` is `C^∞` on the open quadrant, from the elliptic package of the pair `(g, E g)`. -/
theorem smoothOpen_Ug {α Ce : ℝ} (hα : 0 < α) {E : Fn → Fn} {g : Fn}
    (hell : Work.FTS.VocabO.EllPkgGo α Ce g (E g)) :
    Work.FTS.EllipticEst.SmoothOpen (Ug α E g) :=
  Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα hell

/-- **Additivity of the angular moment `FK` on two honest profiles.** -/
theorem FK_add_of_SmoothOpen_HkMem {α : ℝ} {a b : Fn}
    (ha : Work.FTS.EllipticEst.SmoothOpen a) (hb : Work.FTS.EllipticEst.SmoothOpen b)
    (hma : Work.Spaces.HkMem α 4 a) (hmb : Work.Spaces.HkMem α 4 b)
    {z : ℝ} (hz : 0 < z) :
    Work.Construction.FK (fun z θ => a z θ + b z θ) z
      = Work.Construction.FK a z + Work.Construction.FK b z :=
  Work.FTS.GalFields.RHS.FK_add_of_slices (ne_of_gt hz)
    (Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem ha hma hz)
    (Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hb hmb hz)

/-- **The `N` polynomial structure on the class `C`**: with `E` additive and `ℝ`-homogeneous
(a linear map in the application), the bilinear block satisfies
`Sn α Φs E g = C1 α Φs + Lin1 α Φs E g + Quad1 α E g` on the open quadrant, together with the
two polarization identities `Lin1 α Φs E (u+d) = Lin1 α Φs E u + Lin1 α Φs E d` and
`Quad1 α E (u+d) = Quad1 α E u + Bil1 α E u d + Bil1 α E d u + Quad1 α E d`.
The definitions are in `Submission/Work/FTS_MuLipC/LinQuad.lean`.  Ingredients: the profile-level
additivities `L₁₂(F_*+g) = L₁₂F_* + L₁₂g` (`Work.FTS.Nonlinear.Pieces.L12FK_add_ge0`, and for the
`u+d` conjuncts `Work.FTS.GalBasis.cc.L12_add_of_HkMem` / `Work.FTS.GalFields.RHS.Sharp.L12_sub_ge0`)
and `FK(F_*+g) = FK F_* + FK g` (`Work.FTS_MuLamOK.Rows.Rl1Defs.FKaddOpen`,
`Work.FTS.GalFields.RHS.smoothOpen_N_Ftot_gal.FK_add_of_slices`); the additivity of
`Rop`/`Uop`/`Vop` in their field argument (`Work.FTS.GalFields.RHS.Sharp.Rop_add_Q0`,
`Uop_add_Q0`, `Vop_add_Q0`, available from `Work.FTS.OpenPkg.smoothOpen_PhiTil_star` and
`Work.FTS.GalFields.RHS.smoothOpen_N_Ftot.smoothOpen_PhiTil`); that of `pth`/`Dz` on the sum
(`Work.FTS.NonlinRows.Rl1.openSlice_pth_add`, `openSlice_pz_add`,
`Work.FTS.Nonlinear.Pieces.Dz_add_of_diff`); and `E (u+d) = Eu + Ed` for the linearity of
`U_g = E(·) − (1/(4α))·sin(2θ)·L₁₂(·)`. -/
theorem n_poly {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {u d : Work.FTS.Galerkin.Fn}
    (hu : Work.FTS.ClassC.ClassC α u) (hd : Work.FTS.ClassC.ClassC α d)
    (hEadd : ∀ a b : Work.FTS.Galerkin.Fn, E (a + b) = E a + E b)
    (hEsmul : ∀ (c : ℝ) (a : Work.FTS.Galerkin.Fn), E (c • a) = c • E a)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α f →
      Work.FTS.VocabO.EllPkgGo α Ce f (E f)) :
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS_MuLipC.Sn α Φs E u z θ
        = (Work.FTS_MuLipC.C1 α Φs + Work.FTS_MuLipC.Lin1 α Φs E u
            + Work.FTS_MuLipC.Quad1 α E u) z θ) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS_MuLipC.Lin1 α Φs E (fun z' θ' => u z' θ' + d z' θ') z θ
        = (Work.FTS_MuLipC.Lin1 α Φs E u + Work.FTS_MuLipC.Lin1 α Φs E d) z θ) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS_MuLipC.Quad1 α E (fun z' θ' => u z' θ' + d z' θ') z θ
        = (Work.FTS_MuLipC.Quad1 α E u + Work.FTS_MuLipC.Bil1 α E u d
            + Work.FTS_MuLipC.Bil1 α E d u + Work.FTS_MuLipC.Quad1 α E d) z θ) := by
  have huS : Work.FTS.EllipticEst.SmoothOpen u := hu.reg
  have hdS : Work.FTS.EllipticEst.SmoothOpen d := hd.reg
  have hu4 : Work.Spaces.HkMem α 4 u := Work.FTS.ClassC.classC_hkMem_four hu
  have hd4 : Work.Spaces.HkMem α 4 d := Work.FTS.ClassC.classC_hkMem_four hd
  have hFs : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  -- smoothness of the (constant and perturbative) stream functions
  have hZs : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil_star hα hα1 hstar
  have hUgu : Work.FTS.EllipticEst.SmoothOpen (Ug α E u) := smoothOpen_Ug hα (hell u hu)
  have hUgd : Work.FTS.EllipticEst.SmoothOpen (Ug α E d) := smoothOpen_Ug hα (hell d hd)
  -- `L₁₂` additivity on `F_* + u` resp. on `u + d`
  have hLu : ∀ z : ℝ, 0 ≤ z →
      Work.Construction.L12 (Work.Construction.Ftot α u) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z
          + Work.Construction.L12 u z :=
    fun z hz => (Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add hα hα1 huS hu4).1 z hz
  have hLud : ∀ z : ℝ, 0 ≤ z →
      Work.Construction.L12 (fun z θ => u z θ + d z θ) z
        = Work.Construction.L12 u z + Work.Construction.L12 d z :=
    Work.FTS_MuLipC.Poly0.L12_add_of_SmoothOpen_HkMem huS hdS hu4 hd4
  -- additivity of `E` in the eta-expanded form of the statement
  have hEadd' : ∀ a b : Fn, E (fun z θ => a z θ + b z θ) = E a + E b := by
    intro a b
    rw [show (fun z θ => a z θ + b z θ) = (a + b : Fn) from by funext z θ; rfl]
    exact hEadd a b
  refine ⟨?_, ?_, ?_⟩
  · -- ### the polynomial identity for `Sn`
    intro z θ hz hθ0 hθ1
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hθ0, hθ1⟩
    -- the perturbative potential splits into the star part and `U_u`
    have hZgpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Construction.PhiTil α (Work.Construction.Ftot α u)
            (fun z θ => Φs z θ + E u z θ) z θ
          = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
            + Ug α E u z θ := by
      intro z θ hz h1 h2
      have hL := hLu z hz.le
      simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.FTS_MuLipC.Ug,
        Work.Construction.s2]
      rw [hL]
      ring
    have hRop := (Rop_congr_Q0 (α := α) (f := Work.Construction.PhiTil α (Work.Construction.Ftot α u)
          (fun z θ => Φs z θ + E u z θ))
        (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Ug α E u z θ) hz hθ hZgpt).trans
      (Work.FTS.GalFields.RHS.Sharp.Rop_add_Q0 (α := α)
        (f := Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
        (g := Ug α E u) hZs hUgu z θ hz hθ0 hθ1)
    have hUop := (Uop_congr_Q0 (α := α) (f := Work.Construction.PhiTil α (Work.Construction.Ftot α u)
          (fun z θ => Φs z θ + E u z θ))
        (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Ug α E u z θ) hz hθ hZgpt).trans
      (Work.FTS.GalFields.RHS.Sharp.Uop_add_Q0 (α := α)
        (f := Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
        (g := Ug α E u) hZs hUgu z θ hz hθ0 hθ1)
    have hVop := (Vop_congr_Q0 (f := Work.Construction.PhiTil α (Work.Construction.Ftot α u)
          (fun z θ => Φs z θ + E u z θ))
        (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Ug α E u z θ) hz hθ hZgpt).trans
      (Work.FTS.GalFields.RHS.Sharp.Vop_add_Q0
        (f := Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
        (g := Ug α E u) hZs hUgu z θ hz hθ0 hθ1)
    have hpth : Work.Spaces.pth (Work.Construction.Ftot α u) z θ
        = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth u z θ :=
      Work.FTS.NonlinRows.Rl1.openSlice_pth_add hFs huS hz hθ
    have hDz : Work.Spaces.Dz (Work.Construction.Ftot α u) z θ
        = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz u z θ :=
      Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
        (Work.FTS.NonlinRows.Rl1.openSlice_pz_add hFs huS hz hθ)
    have hFK : Work.Construction.FK (Work.Construction.Ftot α u) z
        = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK u z :=
      Work.FTS_MuLamOK.Rows.FKaddOpen hα huS hu4 z hz
    have hF : Work.Construction.Ftot α u z θ
        = Work.Construction.Fstar α z θ + u z θ := rfl
    simp only [Work.FTS_MuLipC.Sn_apply, Work.Construction.N, Work.FTS_MuLipC.C1,
      Work.FTS_MuLipC.Lin1, Work.FTS_MuLipC.Quad1, Pi.add_apply]
    rw [hRop, hUop, hVop, hpth, hDz, hFK, hF]
    ring
  · -- ### `Lin1` is additive in the profile
    intro z θ hz hθ0 hθ1
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hθ0, hθ1⟩
    have hUgpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        Ug α E (fun z' θ' => u z' θ' + d z' θ') z θ
          = (fun z θ => Ug α E u z θ + Ug α E d z θ) z θ := by
      intro z θ hz h1 h2
      have hL := hLud z hz.le
      have hE := hEadd' u d
      simp only [Work.FTS_MuLipC.Ug, Work.Construction.s2]
      rw [hE, hL]
      simp only [Pi.add_apply]
      ring
    have hRop := (Rop_congr_Q0 (α := α) (f := Ug α E (fun z' θ' => u z' θ' + d z' θ'))
        (g := fun z θ => Ug α E u z θ + Ug α E d z θ) hz hθ hUgpt).trans
      (Work.FTS.GalFields.RHS.Sharp.Rop_add_Q0 (α := α) (f := Ug α E u) (g := Ug α E d)
        hUgu hUgd z θ hz hθ0 hθ1)
    have hUop := (Uop_congr_Q0 (α := α) (f := Ug α E (fun z' θ' => u z' θ' + d z' θ'))
        (g := fun z θ => Ug α E u z θ + Ug α E d z θ) hz hθ hUgpt).trans
      (Work.FTS.GalFields.RHS.Sharp.Uop_add_Q0 (α := α) (f := Ug α E u) (g := Ug α E d)
        hUgu hUgd z θ hz hθ0 hθ1)
    have hVop := (Vop_congr_Q0 (f := Ug α E (fun z' θ' => u z' θ' + d z' θ'))
        (g := fun z θ => Ug α E u z θ + Ug α E d z θ) hz hθ hUgpt).trans
      (Work.FTS.GalFields.RHS.Sharp.Vop_add_Q0 (f := Ug α E u) (g := Ug α E d)
        hUgu hUgd z θ hz hθ0 hθ1)
    have hpth : Work.Spaces.pth (fun z' θ' => u z' θ' + d z' θ') z θ
        = Work.Spaces.pth u z θ + Work.Spaces.pth d z θ :=
      Work.FTS.NonlinRows.Rl1.openSlice_pth_add huS hdS hz hθ
    have hDz : Work.Spaces.Dz (fun z' θ' => u z' θ' + d z' θ') z θ
        = Work.Spaces.Dz u z θ + Work.Spaces.Dz d z θ :=
      Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
        (Work.FTS.NonlinRows.Rl1.openSlice_pz_add huS hdS hz hθ)
    have hFK : Work.Construction.FK (fun z' θ' => u z' θ' + d z' θ') z
        = Work.Construction.FK u z + Work.Construction.FK d z :=
      FK_add_of_SmoothOpen_HkMem huS hdS hu4 hd4 hz
    simp only [Work.FTS_MuLipC.Lin1, Pi.add_apply]
    rw [hRop, hUop, hVop, hpth, hDz, hFK]
    ring
  · -- ### the polarization identity of the quadratic block
    intro z θ hz hθ0 hθ1
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hθ0, hθ1⟩
    have hUgpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        Ug α E (fun z' θ' => u z' θ' + d z' θ') z θ
          = (fun z θ => Ug α E u z θ + Ug α E d z θ) z θ := by
      intro z θ hz h1 h2
      have hL := hLud z hz.le
      have hE := hEadd' u d
      simp only [Work.FTS_MuLipC.Ug, Work.Construction.s2]
      rw [hE, hL]
      simp only [Pi.add_apply]
      ring
    have hRop := (Rop_congr_Q0 (α := α) (f := Ug α E (fun z' θ' => u z' θ' + d z' θ'))
        (g := fun z θ => Ug α E u z θ + Ug α E d z θ) hz hθ hUgpt).trans
      (Work.FTS.GalFields.RHS.Sharp.Rop_add_Q0 (α := α) (f := Ug α E u) (g := Ug α E d)
        hUgu hUgd z θ hz hθ0 hθ1)
    have hUop := (Uop_congr_Q0 (α := α) (f := Ug α E (fun z' θ' => u z' θ' + d z' θ'))
        (g := fun z θ => Ug α E u z θ + Ug α E d z θ) hz hθ hUgpt).trans
      (Work.FTS.GalFields.RHS.Sharp.Uop_add_Q0 (α := α) (f := Ug α E u) (g := Ug α E d)
        hUgu hUgd z θ hz hθ0 hθ1)
    have hVop := (Vop_congr_Q0 (f := Ug α E (fun z' θ' => u z' θ' + d z' θ'))
        (g := fun z θ => Ug α E u z θ + Ug α E d z θ) hz hθ hUgpt).trans
      (Work.FTS.GalFields.RHS.Sharp.Vop_add_Q0 (f := Ug α E u) (g := Ug α E d)
        hUgu hUgd z θ hz hθ0 hθ1)
    have hpth : Work.Spaces.pth (fun z' θ' => u z' θ' + d z' θ') z θ
        = Work.Spaces.pth u z θ + Work.Spaces.pth d z θ :=
      Work.FTS.NonlinRows.Rl1.openSlice_pth_add huS hdS hz hθ
    have hDz : Work.Spaces.Dz (fun z' θ' => u z' θ' + d z' θ') z θ
        = Work.Spaces.Dz u z θ + Work.Spaces.Dz d z θ :=
      Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
        (Work.FTS.NonlinRows.Rl1.openSlice_pz_add huS hdS hz hθ)
    have hFK : Work.Construction.FK (fun z' θ' => u z' θ' + d z' θ') z
        = Work.Construction.FK u z + Work.Construction.FK d z :=
      FK_add_of_SmoothOpen_HkMem huS hdS hu4 hd4 hz
    simp only [Work.FTS_MuLipC.Quad1, Work.FTS_MuLipC.Bil1, Pi.add_apply]
    rw [hRop, hUop, hVop, hpth, hDz, hFK]
    ring

end Work.FTS_MuLipC.Poly1
end
-- ===== merged: Submission.Work.FTS_RegExport.RX0.forallRegPkgOfParts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RX0

theorem forallRegPkgOfParts {α : ℝ} {g Φ : Work.FTS.Galerkin.Fam} {m : ℝ → ℝ}
    {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ} {a b c : ℝ}
    (H : ∀ S > 0, ∃ Lz7 : ℝ, Work.FTS.RegExportIface.GalMin' α S g m Vz Vθ cs a b c Lz7)
    (H5 : ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S g Φ) :
    ∀ S > 0, Work.FTS.RegPkgGal.RegPkg' α S (Work.FTS.RegPkgGal.Avort m)
      (Work.FTS.RegPkgGal.Bdyn m) (Work.FTS.RegPkgGal.extG g) := by
  exact forall_regPkg_of_parts' H H5

end Work.FTS_RegExport.RX0
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.L12fAux.L12f_C1Jet_hsupp_unsat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5L.L12fAux

set_option autoImplicit false

/-! ## §1 A uniform lower bound for the angular integrand of `c`, for every exponent `> 0` -/

theorem gamK_lower_pos {β θ : ℝ} (hβ0 : 0 < β) (hθ : θ ∈ Set.Icc (π / 6) (π / 4)) :
    (1 / 4 : ℝ) ^ (β / 3) * (3 / 4) ≤ Work.Spaces.Gam β θ * Work.Spaces.K θ := by
  have hpi := Real.pi_pos
  have hθ1 : π / 6 ≤ θ := hθ.1
  have hθ2 : θ ≤ π / 4 := hθ.2
  have hmem1 : θ ∈ Set.Icc (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
  have hmem2 : π / 6 ∈ Set.Icc (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
  have hsin1 : (1 : ℝ) / 2 ≤ Real.sin θ := by
    have h1 := Real.monotoneOn_sin hmem2 hmem1 hθ1
    rwa [Real.sin_pi_div_six] at h1
  have hmem3 : θ ∈ Set.Icc 0 π := ⟨by linarith, by linarith⟩
  have hmem4 : π / 4 ∈ Set.Icc 0 π := ⟨by linarith, by linarith⟩
  have hcos1 : Real.cos (π / 4) ≤ Real.cos θ := Real.antitoneOn_cos hmem3 hmem4 hθ2
  rw [Real.cos_pi_div_four] at hcos1
  have hcos2 : (1 : ℝ) / 2 ≤ Real.cos θ ^ 2 := by
    have h2 : (Real.sqrt 2 / 2) ^ 2 = (1 : ℝ) / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    have h3 : (Real.sqrt 2 / 2) ^ 2 ≤ Real.cos θ ^ 2 :=
      sq_le_sq' (by linarith [Real.sqrt_nonneg 2]) hcos1
    linarith [h2, h3]
  have hu : (1 : ℝ) / 4 ≤ Real.sin θ * Real.cos θ ^ 2 := by nlinarith [hsin1, hcos2]
  have hsin0 : 0 ≤ Real.sin θ := by linarith
  have hcos20 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  have hGam : (1 / 4 : ℝ) ^ (β / 3) ≤ Work.Spaces.Gam β θ := by
    rw [Work.Spaces.Gam]
    exact Real.rpow_le_rpow (by norm_num) hu (by positivity)
  have hK : (3 / 4 : ℝ) ≤ Work.Spaces.K θ := by
    rw [Work.Spaces.K]
    nlinarith [hu, hsin0, hcos20]
  have hGam0 : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (β / 3) := Real.rpow_nonneg (by norm_num) _
  calc (1 / 4 : ℝ) ^ (β / 3) * (3 / 4) ≤ (1 / 4 : ℝ) ^ (β / 3) * Work.Spaces.K θ :=
        mul_le_mul_of_nonneg_left hK hGam0
    _ ≤ Work.Spaces.Gam β θ * Work.Spaces.K θ :=
        mul_le_mul_of_nonneg_right hGam (by rw [Work.Spaces.K]; positivity)

/-! ## §2 `c` is positive on `(0,∞)` -/

theorem c_pos {β : ℝ} (hβ0 : 0 < β) : 0 < Work.Spaces.c β := by
  have hpi := Real.pi_pos
  have h_int : IntegrableOn (fun θ : ℝ => Work.Spaces.Gam β θ * Work.Spaces.K θ)
      Work.Spaces.Iθ := Work.Spaces.CAux.integrableOn_GamK β hβ0
  have h_nonneg : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (0 : ℝ) ≤ Work.Spaces.Gam β θ * Work.Spaces.K θ := by
    rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun θ hθ => (Work.Spaces.gamK_bounds β θ hβ0 hθ).1
  have hvol : volume.real (Set.Icc (π / 6) (π / 4)) = π / 12 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)]
    ring
  have hsub : Set.Icc (π / 6) (π / 4) ⊆ Work.Spaces.Iθ := fun θ hθ =>
    ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hst : Set.Icc (π / 6) (π / 4) ≤ᵐ[volume] Work.Spaces.Iθ := by
    filter_upwards with θ hθ
    exact hsub hθ
  have hfin : volume (Set.Icc (π / 6) (π / 4)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hge : (1 / 4 : ℝ) ^ (β / 3) * (3 / 4) * volume.real (Set.Icc (π / 6) (π / 4))
      ≤ ∫ θ in Set.Icc (π / 6) (π / 4), Work.Spaces.Gam β θ * Work.Spaces.K θ :=
    MeasureTheory.setIntegral_ge_of_const_le_real measurableSet_Icc hfin
      (fun θ hθ => gamK_lower_pos hβ0 hθ) (h_int.mono_set hsub)
  have hle : ∫ θ in Set.Icc (π / 6) (π / 4), Work.Spaces.Gam β θ * Work.Spaces.K θ
      ≤ Work.Spaces.c β := by
    rw [Work.Spaces.c]
    exact MeasureTheory.setIntegral_mono_set h_int h_nonneg hst
  have hpos : (0 : ℝ) < (1 / 4 : ℝ) ^ (β / 3) * (3 / 4)
      * volume.real (Set.Icc (π / 6) (π / 4)) := by
    rw [hvol]
    have h1 : (0 : ℝ) < (1 / 4 : ℝ) ^ (β / 3) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  linarith

/-! ## §3 The angular values `u = sinθcos²θ` at `3π/4` and `2π/3` -/




/-! ## §4 The identity forced by `hsupp` implies a fixed ratio -/


/-! ## §5 The refutation -/


end Work.FTS_RegExport.RXR5L.L12fAux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Bounds` — the pointwise bounds on the pulled-back coefficients

`|a| ≤ M`, `|b| ≤ 2M`, `|c| ≤ M(3+4α)`, `|f| ≤ Kσ` for `τ ∈ (0,S]`, and `|φ(·,0)| ≤ K₀` — the
numerical hypotheses of the cone maximum principle, in the pulled-back variables.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false

/-! ### The pointwise bounds on the pulled-back coefficients -/






end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Pullback =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Pullback` — the pulled-back equation for `φ = u/ω`

In the logarithmic coordinates of `RXT.Defs`, the weight ratio `φ` satisfies

  `∂_τ φ = f − (a·∂_sφ + b·∂_ψφ + c·φ)`,

with `a = Vz`, `b = 2Vθ/sin 2θ`, `c = cs + 2Vz/(1+z) + α·c2m(θ)·b`, `f = σ/ω` — the content of
`phi_hasDerivAt_τ` below.  The ingredients are the two chain rules `phi_hasDerivAt_s`,
`phi_hasDerivAt_ψ` and the two algebraic relations `dz_relation`, `pth_relation` between the
partial derivatives of `u` and the components `dphi_s`, `dphi_ψ`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false


/-- The `z`-slice of a `C¹` function on `dom S` is differentiable, with derivative `pz`. -/
theorem hasDerivAt_zslice {S : ℝ} {U : ℝ → ℝ → ℝ → ℝ}
    (hU : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => U p.1 p.2.1 p.2.2) (dom S))
    {z θ τ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2)
    (hτ : τ ∈ Set.Icc (0:ℝ) S) :
    HasDerivAt (fun z' : ℝ => U z' θ τ) (Work.Spaces.pz (fun z θ => U z θ τ) z θ) z := by
  have hslice : ContDiffOn ℝ 1 (fun z : ℝ => U z θ τ) (Set.Ioi (0:ℝ)) := by
    have h1 : ContDiffOn ℝ 1 (fun z : ℝ => (z, θ, τ)) (Set.Ioi (0:ℝ)) := by fun_prop
    have h2 : Set.MapsTo (fun z : ℝ => (z, θ, τ)) (Set.Ioi (0:ℝ)) (dom S) := by
      intro z hz
      exact ⟨hz, ⟨hθ0, hθπ⟩, hτ⟩
    have := hU.comp h1 h2
    simpa [dom, Function.comp_def] using this
  have hd : DifferentiableWithinAt ℝ (fun z : ℝ => U z θ τ) (Set.Ioi (0:ℝ)) z :=
    hslice.differentiableOn one_ne_zero z hz
  have hd' : DifferentiableAt ℝ (fun z : ℝ => U z θ τ) z :=
    hd.differentiableAt (isOpen_Ioi.mem_nhds hz)
  simpa only [Work.Spaces.pz] using hd'.hasDerivAt


/-! ### The three derivative identities for `φ = u/ω` -/







end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.PullDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.PullDefs` — the pulled-back unknown `φ = w/ω` and its coefficients

This is the (self-contained) interface used by `weighted_integrated_mp` (T5c of the RX-St1 leaf
plan) in the logarithmic coordinates `s = log z`, `ψ = log tan θ` of
`Work.FTS_RegExport.RXT.Defs`.

Only the *hypotheses* of T5c are used (continuity of `w`, the two partial-derivative relations
`D_z w = wz/z`, `D_θ w = wθ/sin 2θ` with *continuous* `wz`, `wθ`, and the integral identity),
so everything here is stated in terms of `wz`, `wθ` directly (no `C¹` on the slab is assumed).

The pulled-back unknown is `pw α w s ψ τ = w (eˢ) (arctan e^ψ) τ / om α s ψ` with
`om α s ψ = ω α (eˢ) (arctan e^ψ)`.  Its derivatives are

* `pws α wz w  = ∂_sφ = wz/om − 2φ/(1+z)`   (`= dphi_s` of `RXT.Pullback`),
* `pwψ α wθ w  = ∂_ψφ = wθ/(2·om) − α·c2m(θ)·φ`   (`= dphi_ψ` of `RXT.Pullback`),

the second because `dθ/dψ = sin 2θ/2` and `∂_θw = wθ/sin 2θ`.

The coefficients of the pulled-back transport equation are
`coefA Vz = Vz`, `coefB b = 2b`, `coefC α Vz b = 2Vz/(1+z) + 2α·c2m(θ)·b`
(the original angular velocity being `Vθ = b·sin 2θ`), and the source is `srcF α R = R/om`;
the algebraic core is `pw_alg`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS_RegExport.RXT (cz cth om)

set_option autoImplicit false

/-- The pulled-back unknown `φ = w/ω` in logarithmic coordinates. -/
def pw (α : ℝ) (w : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s ψ τ => w (cz s) (cth ψ) τ / om α s ψ

/-- The `s`-derivative `∂_sφ = wz/om − 2φ/(1+z)` of the pulled-back unknown. -/
def pws (α : ℝ) (wz : ℝ → ℝ → ℝ → ℝ) (w : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s ψ τ => wz (cz s) (cth ψ) τ / om α s ψ - 2 * pw α w s ψ τ / (1 + cz s)

/-- The `ψ`-derivative `∂_ψφ = wθ/(2·om) − α·c2m(θ)·φ` of the pulled-back unknown. -/
def pwψ (α : ℝ) (wθ : ℝ → ℝ → ℝ → ℝ) (w : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s ψ τ => wθ (cz s) (cth ψ) τ / (2 * om α s ψ)
    - pw α w s ψ τ * (α * Work.Construction.c2m (cth ψ))

/-- The source `R/om` of the pulled-back equation. -/
def srcF (α : ℝ) (R : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s ψ τ => R (cz s) (cth ψ) τ / om α s ψ

/-- The `s`-coefficient `a = Vz`. -/
def coefA (Vz : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ := fun s ψ τ => Vz (cz s) (cth ψ) τ

/-- The `ψ`-coefficient `b = 2Vθ/sin 2θ = 2·(Vθ = b sin 2θ)`. -/
def coefB (Vθ : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ := fun s ψ τ => 2 * Vθ (cz s) (cth ψ) τ

/-- The zero-order coefficient `c = 2Vz/(1+z) + 2α·c2m(θ)·b` (`b = Vθ/sin 2θ`). -/
def coefC (α : ℝ) (Vz Vθ : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s ψ τ => 2 * Vz (cz s) (cth ψ) τ / (1 + cz s)
    + α * Work.Construction.c2m (cth ψ) * (2 * Vθ (cz s) (cth ψ) τ)


/-- **The algebraic core of the pull-back**: dividing the original equation
`∂_τw = R − (Vz·wz + b·wθ)` by `om = ω(cz s, cth ψ)` produces the pulled-back transport
equation with coefficients `coefA Vz`, `coefB b`, `coefC α Vz b` and source `srcF α R`. -/
lemma pw_alg {α : ℝ} (hα : 0 < α) {Vz b R w wz wθ : ℝ → ℝ → ℝ → ℝ} {s ψ τ : ℝ} :
    (R (cz s) (cth ψ) τ - (Vz (cz s) (cth ψ) τ * wz (cz s) (cth ψ) τ
        + b (cz s) (cth ψ) τ * wθ (cz s) (cth ψ) τ)) / om α s ψ
      = srcF α R s ψ τ
        - (coefA Vz s ψ τ * pws α wz w s ψ τ + coefB b s ψ τ * pwψ α wθ w s ψ τ
          + coefC α Vz b s ψ τ * pw α w s ψ τ) := by
  have h1 : (1 + cz s) ≠ 0 := by have := Work.FTS_RegExport.RXT.cz_pos s; positivity
  have h2 : om α s ψ ≠ 0 :=
    ne_of_gt (Work.FTS_RegExport.RXT.om_pos (α := α) hα)
  have h3 : om α s ψ * om α s ψ ≠ 0 := mul_ne_zero h2 h2
  simp only [srcF, coefA, coefB, coefC, pws, pwψ, pw]
  field_simp
  ring

end Work.FTS_RegExport.RXT.Sys
end
end
