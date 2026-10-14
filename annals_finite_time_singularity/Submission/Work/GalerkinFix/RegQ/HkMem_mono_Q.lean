import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Coercivity.HkMem_mono
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.Cutoff
-- ===== merged: Submission.Work.FTS.CoercivityStep.Norm.HkMem_add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep.Norm

set_option autoImplicit false

/-! ## `SmoothNbhd` is closed under addition -/


/-! ## The pointwise domination, almost everywhere in `θ` -/


/-! ## The main theorem -/


end Work.FTS.CoercivityStep.Norm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.HkSq_eq_lintegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option maxHeartbeats 800000

/-- **`HkSq` as a `lintegral`.**  `Work.Spaces.HkSq` is the iterated *Bochner* integral of the
nonnegative integrand `Work.Spaces.HkIntegrand`, and `integral_eq_lintegral_of_nonneg_ae` turns
such a Bochner integral into the `toReal` of the corresponding `lintegral` as soon as the outer
integrand is a.e. strongly measurable.

That measurability is where the smoothness hypothesis is used: the uncurried integrand is
continuous on the open quadrant `(0,∞) × (0,π/2)` — the iterated weighted derivatives are `C^∞`
there because `f` is, and the weights `w(z)`, `sin(2θ)^{-γ/2}` are continuous there — while the
complement of the open quadrant inside `Iz ×ˢ Iθ` is the null set
`{z = 0} ∪ {θ = 0} ∪ {θ = π/2}`.  `Work.Spaces.aesm_of_continuousOn_Qd` performs that transfer;
the remaining step is `MeasureTheory.AEStronglyMeasurable.integral_prod_right'` for the partial
`θ`-integration. -/
theorem HkSq_eq_lintegral (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    Work.Spaces.HkSq α k f
      = ENNReal.toReal (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)) := by
  -- `∀ n, ContDiffOn ℝ n …` is exactly genuine `C^∞` (`Work.Stability.smoothOrder`).
  have hsm : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := contDiffOn_infty.mpr hf
  have hQ : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  -- `sin (2θ) > 0` on the open quadrant.
  have hsinpos : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos])
  -- Continuity of the two weights on the open quadrant.
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  have hsinpow : ∀ c : ℝ, ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := fun c =>
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hWt : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
        = fun p : ℝ × ℝ =>
            Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
      funext p; rfl
    rw [hfun]
    exact hw.mul (hsinpow _)
  have hwdiv : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hw.div (hsinpow _) (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _))
  -- The iterated weighted derivatives are continuous on the open quadrant.
  have hDzC : ∀ i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := fun i =>
    (Work.FTS.LocData.contDiffOn_DzIter hQ hsm i).continuousOn
  have hmC : ∀ j i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := fun j i =>
    (Work.FTS.LocData.contDiffOn_mixed hQ hsm j i).continuousOn
  -- Hence the uncurried `ℋ^k`-integrand is continuous on the open quadrant.
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hHk : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
        = fun p : ℝ × ℝ =>
            (∑ i ∈ Finset.range (k + 1),
                (Work.Spaces.DzIter i f p.1 p.2
                  * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
              + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                  if 1 ≤ i ∧ i + j ≤ k
                  then (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2
                  else 0 := by
      funext p; rfl
    rw [hHk]
    refine ContinuousOn.add ?_ ?_
    · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i _ => ?_)
      exact ((hDzC i).mul hwdiv).pow 2
    · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i _ =>
        continuousOn_finsetSum (Finset.range (k + 1)) (fun j _ => ?_))
      split_ifs with h
      · exact ((hmC j i).mul hWt).pow 2
      · exact continuousOn_const
  -- Continuity on the open quadrant gives a.e. strong measurability for the product measure,
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  -- hence the partially `θ`-integrated integrand is a.e. strongly measurable for `dz`,
  have hslice : AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      (volume.restrict Work.Spaces.Iz) :=
    hmeas.integral_prod_right'
  -- and the Bochner/`lintegral` bridge, valid for nonnegative a.e. strongly measurable
  -- functions, concludes.
  rw [Work.Spaces.HkSq]
  exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun z =>
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ) hslice

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.OpenQDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

variable {F G : ℝ → ℝ → ℝ}

/-! ## The open quadrant and the smoothness class -/

/-- The open quadrant `(0,∞) × (0,π/2)` of the elliptic estimates. -/
def Q0 : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

theorem isOpen_Q0 : IsOpen Q0 := isOpen_Ioi.prod isOpen_Ioo

theorem mem_Q0 {z θ : ℝ} : (z, θ) ∈ Q0 ↔ 0 < z ∧ 0 < θ ∧ θ < π / 2 := by
  simp only [Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]

/-- **The smoothness class of the open-quadrant statements**: the uncurried `F` is `C^∞` on
the open quadrant `(0,∞) × (0,π/2)`. -/
def SmoothOpen (F : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry F) Q0

/-- `SmoothOpen` is exactly the raw hypothesis shape used by the statements of the chapter. -/
theorem smoothOpen_iff_forall (F : ℝ → ℝ → ℝ) :
    SmoothOpen F ↔ ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) Q0 := by
  constructor
  · intro h n
    exact contDiffOn_iff_forall_nat_le.mp h n le_top
  · intro h
    exact contDiffOn_iff_forall_nat_le.mpr (fun m _ => h m)

theorem smoothOpen_of_forall {F : ℝ → ℝ → ℝ}
    (h : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) Q0) : SmoothOpen F :=
  (smoothOpen_iff_forall F).mpr h

theorem SmoothOpen.forall (hF : SmoothOpen F) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry F) Q0 :=
  (smoothOpen_iff_forall F).mp hF n

/-! ## The bridge from the re-scoped strong class

`EllHyp.smooth` is `Work.Spaces.SmoothInt Ψ` (`C^∞` on the open strip `(-1,∞) × (0,π/2)` plus
`C^∞` `z`-slices), so a consumer that used `EllHyp.smooth` only for *open-quadrant* facts can
switch to these two lemmas instead of demanding `SmoothNbhd`.  (The boundary `θ`-facts — e.g.
`SmoothNbhd (∂_θΨ)` at `θ = 0, π/2` — are *not* consequences of `SmoothInt`; those consumers are
the class-B residue.) -/

/-- The open-quadrant smoothness component of `SmoothInt`: this is the replacement for
`SmoothNbhd_smoothOpen`/`smoothOpen_of_smoothNbhd` at the (re-scoped) field `EllHyp.smooth`. -/
theorem smoothOpen_of_smoothInt {F : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothInt F) : SmoothOpen F := by
  refine (smoothOpen_iff_forall F).mpr fun n => ?_
  have hsub : Q0 ⊆ Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) := by
    intro p hp
    have hp' : p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) := hp
    have hp1 : (0 : ℝ) < p.1 := (Set.mem_prod.mp hp').1
    have hp2 : p.2 ∈ Set.Ioo (0 : ℝ) (π / 2) := (Set.mem_prod.mp hp').2
    exact Set.mem_prod.mpr ⟨show (-1 : ℝ) < p.1 from by linarith, hp2⟩
  exact ((h.1.of_le le_top).mono hsub).of_le le_top


/-! ## The iterated operators preserve `C^∞` on the open quadrant -/

theorem SmoothOpen.pz (hF : SmoothOpen F) : SmoothOpen (Work.Spaces.pz F) :=
  Work.FTS.LocData.contDiffOn_pz isOpen_Q0 hF

theorem SmoothOpen.pth (hF : SmoothOpen F) : SmoothOpen (Work.Spaces.pth F) :=
  Work.FTS.LocData.contDiffOn_pth isOpen_Q0 hF

theorem SmoothOpen.Dz (hF : SmoothOpen F) : SmoothOpen (Work.Spaces.Dz F) :=
  Work.FTS.LocData.contDiffOn_Dz isOpen_Q0 hF

theorem SmoothOpen.Dth (hF : SmoothOpen F) : SmoothOpen (Work.Spaces.Dth F) :=
  Work.FTS.LocData.contDiffOn_Dth isOpen_Q0 hF

theorem SmoothOpen.pzIter (hF : SmoothOpen F) (i : ℕ) : SmoothOpen (Work.Spaces.pzIter i F) := by
  induction i with
  | zero => simpa using hF
  | succ i ih => rw [Work.Spaces.pzIter_succ]; exact ih.pz

theorem SmoothOpen.DzIter (hF : SmoothOpen F) (i : ℕ) : SmoothOpen (Work.Spaces.DzIter i F) :=
  Work.FTS.LocData.contDiffOn_DzIter isOpen_Q0 hF i

theorem SmoothOpen.DthIter (hF : SmoothOpen F) (i : ℕ) : SmoothOpen (Work.Spaces.DthIter i F) :=
  Work.FTS.LocData.contDiffOn_DthIter isOpen_Q0 hF i

theorem SmoothOpen.mixed (hF : SmoothOpen F) (j i : ℕ) : SmoothOpen (Work.Spaces.mixed j i F) :=
  Work.FTS.LocData.contDiffOn_mixed isOpen_Q0 hF j i

/-! ## Slices -/

/-- The `z`-slice of a function `C^∞` on the open quadrant, at an interior angle. -/
theorem SmoothOpen.curry_z (hF : SmoothOpen F) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z => F z θ) (Set.Ioi 0) :=
  Work.FTS.LocData.contDiffOn_slice_z hF hθ

/-- The `θ`-slice of a function `C^∞` on the open quadrant, at a positive radius. -/
theorem SmoothOpen.curry_θ (hF : SmoothOpen F) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => F z θ) (Set.Ioo 0 (π / 2)) :=
  Work.FTS.LocData.contDiffOn_slice_θ hF hz

/-- **The `z`-derivative of the slice.**  For `θ` interior, the slice `z ↦ F z θ` is
differentiable at every `z > 0`, with derivative `Work.Spaces.pz F z θ`. -/
theorem SmoothOpen.hasDerivAt_slice (hF : SmoothOpen F) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2))
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' : ℝ => F z' θ) (Work.Spaces.pz F z θ) z :=
  ((hF.curry_z hθ).differentiableOn (by simp)).differentiableAt
    (isOpen_Ioi.mem_nhds hz) |>.hasDerivAt

/-- **The `z`-derivative of the slice of an iterated `∂_z`-derivative.** -/
theorem SmoothOpen.hasDerivAt_slice_pzIter (hF : SmoothOpen F) (i : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter i F z' θ)
      (Work.Spaces.pzIter (i + 1) F z θ) z := by
  have h := (hF.pzIter i).hasDerivAt_slice hθ hz
  simpa only [Work.Spaces.pzIter_succ] using h

/-- **The `z`-derivative of the slice of an iterated `D_z`-derivative.** -/
theorem SmoothOpen.hasDerivAt_slice_DzIter (hF : SmoothOpen F) (i : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' : ℝ => Work.Spaces.DzIter i F z' θ)
      (Work.Spaces.pz (Work.Spaces.DzIter i F) z θ) z :=
  (hF.DzIter i).hasDerivAt_slice hθ hz

/-! ## Continuity of the weighted derivatives on the open quadrant -/

/-- The weight `w z / sin(2θ)^{η/2}` is continuous on the open quadrant. -/
theorem continuousOn_wdivsin_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1
      / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Q0 := by
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt (mem_Q0.mp hp).1)
  have hsin : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Q0 :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  exact hw.div hsin (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _))

/-- The uncurried weighted `D_z`-summand is continuous on the open quadrant. -/
theorem SmoothOpen.continuousOn_summand (hF : SmoothOpen F) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i F p.1 p.2
      * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) Q0 :=
  ((hF.DzIter i).continuousOn).mul continuousOn_wdivsin_Q0

/-- The uncurried `ℋ^k`-integrand is continuous on the open quadrant. -/
theorem SmoothOpen.continuousOn_HkIntegrand (hF : SmoothOpen F) (α : ℝ) (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2) Q0 := by
  have hz : ∀ i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i F p.1 p.2) Q0 :=
    fun i => (hF.DzIter i).continuousOn
  have hm : ∀ j i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i F p.1 p.2) Q0 :=
    fun j i => (hF.mixed j i).continuousOn
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hWt : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
        = fun p : ℝ × ℝ => Work.Spaces.w p.1
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
      funext p; rfl
    rw [hfun]
    have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Q0 := by
      have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
          = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
        funext p; rfl
      rw [hfun2]
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
        (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt (mem_Q0.mp hp).1))
    refine hw.mul ?_
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hHk : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
      = fun p : ℝ × ℝ =>
          (∑ i ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter i F p.1 p.2
                * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.mixed j i F p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2
                else 0 := by
    funext p; rfl
  rw [hHk]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i _ => ?_)
    exact (((hz i).mul continuousOn_wdivsin_Q0)).pow 2
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i _ =>
      continuousOn_finsetSum (Finset.range (k + 1)) (fun j _ => ?_))
    split_ifs with h
    · exact (((hm j i).mul hWt)).pow 2
    · exact continuousOn_const

/-! ## Measurability and integrability of the angular slices of a summard -/

/-- The angular slice of the weighted `D_z`-summand is a.e. strongly measurable. -/
theorem SmoothOpen.aesm_slice_summand (hF : SmoothOpen F) (i : ℕ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.DzIter i F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hF.continuousOn_summand i) hz

/-- The angular slice of the plain `∂_z`-iterate is a.e. strongly measurable. -/
theorem SmoothOpen.aesm_slice_pzIter (hF : SmoothOpen F) (i : ℕ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.pzIter i F z θ)
      (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Spaces.pzIter i F p.1 p.2) (hF.pzIter i).continuousOn hz

/-- A single weighted `D_z`-summand of the `ℋ^k`-integrand is integrable on the angular slice,
for every `z ∈ Iz`, as soon as `F ∈ ℋ^k`.  (The open-quadrant analogue of
`Work.FTS.EllipticEst.integrableOn_zSummand`.) -/
theorem integrableOn_zSummand (α : ℝ) (k : ℕ) {F : ℝ → ℝ → ℝ} (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (i : ℕ) (hi : i ≤ k) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    IntegrableOn (fun θ : ℝ => (Work.Spaces.DzIter i F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- at `z = 0` the radial weight vanishes and the summand is identically zero
    have hzero : ∀ θ : ℝ, (Work.Spaces.DzIter i F 0 θ
        * (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = 0 := by
      intro θ
      rw [Work.Spaces.w]
      norm_num
    rw [show (fun θ : ℝ => (Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = fun _ : ℝ => (0 : ℝ) from by
      funext θ; rw [← hz0]; exact hzero θ]
    exact integrableOn_zero
  · refine Integrable.mono' (hmem.1 z hz) ((hF.aesm_slice_summand i hzpos).pow 2) ?_
    rw [ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from by
      rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
    exact Eventually.of_forall fun θ _ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_z α k F z θ i hi

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Set Filter

namespace Work.FTS.EllipticEst.ThetaU.OpenSliceAux

/-- On an open set `V` on which `f` is `C^∞`, a single `D_θ` moves across any number of
iterates of `D_z`: `D_θ (D_z^j f) = D_z^j (D_θ f)` on `V`. -/
theorem Dth_DzIter_eqOn_of_smooth {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter j f)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.Dth f))) V := by
  induction j with
  | zero => intro y hy; rfl
  | succ j ih =>
      -- `D_z^j f` is still `C^∞` on `V`, hence `C²` at `y`: Clairaut applies there.
      have hfj : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DzIter j f)) V :=
        Work.FTS.LocData.contDiffOn_DzIter hV hf j
      intro y hy
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter j f)) y :=
        (hfj.contDiffAt (hV.mem_nhds hy)).of_le (by simp)
      have hstep : Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter j f)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DzIter j f)) y.1 y.2 :=
        (Work.Spaces.Dz_Dth_comm hcd).symm
      show Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter j f)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.Dth f)) y.1 y.2
      rw [hstep]
      -- the two functions agree on the open set `V`, so their `z`-derivatives agree at `y`.
      show y.1 * Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DzIter j f)) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter j (Work.Spaces.Dth f)) y.1 y.2
      rw [Work.Spaces.pz_congr_of_isOpen hV ih hy]

/-- **Commutation of the mixed curvilinear derivatives on an arbitrary open set.**  If the
uncurried profile `g` is `C^n` on the open set `V` for every `n` — i.e. genuinely smooth on
`V` — then `D_θ^i` and `D_z^j` commute on `V`, so that `D_θ^i (D_z^j g) = mixed j i g` there. -/
theorem DthIter_DzIter_eqOn_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g : ℝ → ℝ → ℝ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) V) (j i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.DzIter j g)))
      (Function.uncurry (Work.Spaces.mixed j i g)) V := by
  have hsm : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V :=
    contDiffOn_infty.mpr hg
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.DzIter j g)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.DthIter i g))) V := by
    induction i with
    | zero => intro y hy; rfl
    | succ i ih =>
        have hgi : ContDiffOn ℝ Work.Stability.smoothOrder
            (Function.uncurry (Work.Spaces.DthIter i g)) V :=
          Work.FTS.LocData.contDiffOn_DthIter hV hsm i
        intro y hy
        show Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter j g)) y.1 y.2
            = Work.Spaces.DzIter j (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
        -- replace `D_θ^i (D_z^j g)` by `D_z^j (D_θ^i g)` inside the outer `D_θ`.
        have hcon : Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter j g)) y.1 y.2
            = Work.Spaces.Dth (Work.Spaces.DzIter j (Work.Spaces.DthIter i g)) y.1 y.2 := by
          show Real.sin (2 * y.2)
                * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.DzIter j g)) y.1 y.2
              = Real.sin (2 * y.2)
                * Work.Spaces.pth (Work.Spaces.DzIter j (Work.Spaces.DthIter i g)) y.1 y.2
          rw [Work.Spaces.pth_congr_of_isOpen hV ih hy]
        rw [hcon]
        exact Dth_DzIter_eqOn_of_smooth hV hgi j hy
  intro y hy
  exact hcomm hy

end Work.FTS.EllipticEst.ThetaU.OpenSliceAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Set Filter

namespace Work.FTS.EllipticEst.ThetaU.OpenSliceAux

/-- Pointwise Clairaut for `∂_θ` and `D_z = z ∂_z`: at a point where the uncurried `f` is `C²`,
`∂_θ (z ∂_z f) = z ∂_z (∂_θ f)`.  (Both sides are `z · ∂_θ∂_z f`; the `θ`-derivative of the
`z`-partial is the `z`-partial of the `θ`-derivative by `Work.Spaces.pz_pth_comm`, and the
factor `z` may be pulled out of the `θ`-derivative by `deriv_const_mul_field`.) -/
private lemma pth_Dz_eq_of_contDiffAt_two {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) :
    Work.Spaces.pth (Work.Spaces.Dz f) z θ = Work.Spaces.Dz (Work.Spaces.pth f) z θ := by
  have h1 : Work.Spaces.pth (Work.Spaces.Dz f) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz f) z θ := by
    show deriv (fun θ' => z * Work.Spaces.pz f z θ') θ
      = z * Work.Spaces.pth (Work.Spaces.pz f) z θ
    rw [deriv_const_mul_field]
    rfl
  have h2 : Work.Spaces.Dz (Work.Spaces.pth f) z θ
      = z * Work.Spaces.pz (Work.Spaces.pth f) z θ := rfl
  rw [h1, h2, (Work.Spaces.pz_pth_comm h).symm]

theorem pth_DzIter_eqOn_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g : ℝ → ℝ → ℝ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j g)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth g))) V := by
  have hsm : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V :=
    contDiffOn_infty.mpr hg
  induction j with
  | zero => intro y hy; rfl
  | succ j ih =>
      -- `D_z^j g` is still `C^∞` on `V`, hence `C²` at `y`: Clairaut applies there.
      have hgj : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DzIter j g)) V :=
        Work.FTS.LocData.contDiffOn_DzIter hV hsm j
      intro y hy
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter j g)) y :=
        (hgj.contDiffAt (hV.mem_nhds hy)).of_le (by simp)
      have hstep : Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j g)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j g)) y.1 y.2 :=
        pth_Dz_eq_of_contDiffAt_two hcd
      show Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j g)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth g)) y.1 y.2
      rw [hstep]
      -- the two functions agree on the open set `V`, so their `z`-partials agree at `y`.
      show y.1 * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter j g)) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter j (Work.Spaces.pth g)) y.1 y.2
      rw [Work.Spaces.pz_congr_of_isOpen hV ih hy]

end Work.FTS.EllipticEst.ThetaU.OpenSliceAux
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option maxHeartbeats 800000

theorem abs_integral_K_S_Gaz_le (α : ℝ) (h : ℝ → ℝ → ℝ) {s : ℝ}
    (hint : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 h s θ)
      Work.Spaces.Iθ) :
    |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Sw θ * Gaz h s θ|
      ≤ BK * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 h s θ) := by
  -- the angular profile, the weighted datum and the square root of the majorant
  set u : ℝ → ℝ := fun θ => Work.Spaces.K θ * Sw θ with hu
  set v : ℝ → ℝ := fun θ => Gaz h s θ with hv
  set w : ℝ → ℝ := fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 h s θ) with hw
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hHk_nn : ∀ θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4 h s θ :=
    fun θ => Work.Spaces.HkIntegrand_nonneg α 4 h s θ
  have hw_nn : ∀ θ : ℝ, 0 ≤ w θ := by
    intro θ; rw [hw]; exact Real.sqrt_nonneg _
  -- the pointwise domination of the weighted datum by `w`
  have hvw : ∀ θ : ℝ, |v θ| ≤ w θ := by
    intro θ; rw [hv, hw]; exact abs_Gaz_le_sqrt_HkIntegrand α h s θ
  -- continuity/measurability
  have hcont_K : Continuous Work.Spaces.K := by
    change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have hcont_u : Continuous u := by
    rw [hu]; exact hcont_K.mul continuous_sw
  have hw_aesm : AEStronglyMeasurable w (volume.restrict Work.Spaces.Iθ) := by
    rw [hw]
    exact (hint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  -- integrability of `u²` and of `w²`
  have hu2_int : IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ :=
    (hcont_u.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hw2_int : IntegrableOn (fun θ => (w θ) ^ 2) Work.Spaces.Iθ := by
    refine hint.congr_fun (fun θ _ => ?_) hIθ
    rw [hw]; exact (Real.sq_sqrt (hHk_nn θ)).symm
  -- integrability of the majorant `|u|·w`
  have huw_int : IntegrableOn (fun θ => |u θ| * w θ) Work.Spaces.Iθ := by
    have hmaj : IntegrableOn (fun θ => ((u θ) ^ 2 + (w θ) ^ 2) / 2) Work.Spaces.Iθ :=
      (hu2_int.add hw2_int).div_const 2
    refine hmaj.mono' ((hcont_u.abs.aestronglyMeasurable).mul hw_aesm) ?_
    filter_upwards with θ
    have h1 : 0 ≤ |u θ| := abs_nonneg _
    have h2 : 0 ≤ w θ := hw_nn θ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2, abs_of_nonneg h1]
    have key : |u θ| * w θ ≤ (|u θ| ^ 2 + (w θ) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|u θ| - w θ), sq_nonneg (|u θ| + w θ)]
    rw [sq_abs (u θ)] at key
    exact key
  -- `L²`-membership of the two measurable factors
  have hMemLp_u : MemLp (fun θ => |u θ|) 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => |u θ|) hcont_u.abs.aestronglyMeasurable).mpr
      (hu2_int.congr (Filter.Eventually.of_forall fun θ => (sq_abs (u θ)).symm))
  have hMemLp_w : MemLp w 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ) hw_aesm).mpr hw2_int
  have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt (u := fun θ => |u θ|)
    (v := w) hMemLp_u hMemLp_w
  -- the two square roots of the integrals
  have hsqrt_u : Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2) = BK := by
    rw [BK]
    congr 1
    simp only [hu]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun θ => sq_abs (Work.Spaces.K θ * Sw θ))
  have hsqrt_w : Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2)
      = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 h s θ) := by
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    rw [hw]; exact Real.sq_sqrt (hHk_nn θ)
  -- the three steps
  have h1 : |∫ θ in Work.Spaces.Iθ, u θ * v θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |u θ * v θ| := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Work.Spaces.Iθ)
        (f := fun θ => u θ * v θ))
  have h2 : ∫ θ in Work.Spaces.Iθ, |u θ * v θ| ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => abs_nonneg _) huw_int
      (Filter.Eventually.of_forall fun θ => ?_)
    show |u θ * v θ| ≤ |u θ| * w θ
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hvw θ) (abs_nonneg _)
  have h3 : ∫ θ in Work.Spaces.Iθ, |u θ| * w θ
      = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := by
    rw [abs_of_nonneg]
    exact MeasureTheory.integral_nonneg fun θ => mul_nonneg (abs_nonneg _) (hw_nn θ)
  calc |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Sw θ * Gaz h s θ|
      = |∫ θ in Work.Spaces.Iθ, u θ * v θ| := by simp only [hu, hv]
    _ ≤ ∫ θ in Work.Spaces.Iθ, |u θ * v θ| := h1
    _ ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := h2
    _ = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := h3
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2) := hcs
    _ = BK * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 h s θ) := by
        rw [hsqrt_u, hsqrt_w]

end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.integral_abs_L12dens_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc

open MeasureTheory Filter

/-- **The integrated pointwise bound on the `L₁₂`-density.**
If `|L12dens h s| ≤ Wlam s · (BK · √(∫_θ HkIntegrand α 4 h s θ))` for every `s > 0` and
`h ∈ ℋ⁴_α`, then the same bound holds after integrating in `s`:

`∫_{s>0} |L12dens h s| ≤ BK · √W2 · √(HkSq α 4 h)`.

This is Cauchy–Schwarz in the radial variable: the weight `Wlam` is square-integrable on
`(0,∞)` with `∫ Wlam² = W2`, and `∫_{(0,∞)} (√(∫_θ HkIntegrand))² = HkSq α 4 h`
(the two sets `(0,∞)` and `ℤ = [0,∞)` differ by the null set `{0}`). -/
theorem integral_abs_L12dens_le (α : ℝ) (h : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 4 h)
    (hbd : ∀ s ∈ Set.Ioi (0 : ℝ), |Work.Construction.L12dens h s|
      ≤ Wlam s * (BK * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 h s θ))) :
    ∫ s in Set.Ioi (0 : ℝ), |Work.Construction.L12dens h s|
      ≤ BK * Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 4 h) := by
  -- the angular marginal `H` and its square root `A`
  set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 h s θ with hH
  set A : ℝ → ℝ := fun s => Real.sqrt (H s) with hA
  have hHnn : ∀ s, 0 ≤ H s :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 h s θ
  have hAnn : ∀ s, 0 ≤ A s := fun s => Real.sqrt_nonneg _
  -- `H` is integrable on `(0,∞)` (hence so is `A²`)
  have hH_int : IntegrableOn H (Set.Ioi 0) := hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hH_aesm : AEStronglyMeasurable H (volume.restrict (Set.Ioi 0)) :=
    hH_int.aestronglyMeasurable
  have hA_aesm : AEStronglyMeasurable A (volume.restrict (Set.Ioi 0)) := by
    rw [hA]
    exact (hH_aesm.aemeasurable.sqrt).aestronglyMeasurable
  have hA2_int : IntegrableOn (fun s => A s ^ 2) (Set.Ioi 0) := by
    refine hH_int.congr ?_
    filter_upwards with s
    rw [hA]
    exact (Real.sq_sqrt (hHnn s)).symm
  have hA_memLp : MemLp A 2 (volume.restrict (Set.Ioi 0)) :=
    (memLp_two_iff_integrable_sq hA_aesm).mpr hA2_int
  -- the radial weight `Wlam` is square-integrable
  have hWlam_aesm : AEStronglyMeasurable Wlam (volume.restrict (Set.Ioi 0)) := by
    change AEStronglyMeasurable (fun s : ℝ => s / (1 + s) ^ 2)
      (volume.restrict (Set.Ioi 0))
    refine ContinuousOn.aestronglyMeasurable (μ := volume)
      (continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_)
      measurableSet_Ioi
    intro s hs
    have hne : (1 : ℝ) + s ≠ 0 := by
      simp only [Set.mem_Ioi] at hs
      linarith
    exact pow_ne_zero 2 hne
  have hWlam_sq_int : IntegrableOn (fun s => Wlam s ^ 2) (Set.Ioi 0) := by
    simpa only [Wlam] using Work.Elliptic.psi_sq_integrable_aux
  have hWlam_memLp : MemLp Wlam 2 (volume.restrict (Set.Ioi 0)) :=
    (memLp_two_iff_integrable_sq hWlam_aesm).mpr hWlam_sq_int
  -- `∫_{(0,∞)} A² = HkSq α 4 h`, up to the null set `{0}`
  have hW2eq : ∫ s in Set.Ioi 0, Wlam s ^ 2 = W2 := rfl
  have hIz_eq : ∫ s in Work.Spaces.Iz, H s = Work.Spaces.HkSq α 4 h := by
    rw [hH]; rfl
  have hA2sq : ∫ s in Set.Ioi 0, A s ^ 2 = Work.Spaces.HkSq α 4 h := by
    have h1 : ∫ s in Set.Ioi 0, A s ^ 2 = ∫ s in Set.Ioi 0, H s :=
      setIntegral_congr_fun measurableSet_Ioi fun s _ => by
        rw [hA]; exact Real.sq_sqrt (hHnn s)
    have h2 : ∫ s in Set.Ioi 0, H s = ∫ s in Work.Spaces.Iz, H s :=
      MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici' (MeasureTheory.measure_singleton 0))
    rw [h1, h2, hIz_eq]
  -- Cauchy–Schwarz in the radial variable
  have hCS : ∫ s in Set.Ioi 0, Wlam s * A s
      ≤ Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 4 h) := by
    have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
      (u := Wlam) (v := A) (s := Set.Ioi 0) hWlam_memLp hA_memLp
    rw [hA2sq, hW2eq] at hcs
    have hnn : 0 ≤ ∫ s in Set.Ioi 0, Wlam s * A s := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      show ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)), (0 : ℝ) ≤ Wlam s * A s
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun s hs =>
        mul_nonneg (Wlam_nonneg (le_of_lt hs)) (hAnn s)
    rwa [abs_of_nonneg hnn] at hcs
  -- AM–GM, giving integrability of the majorant
  have hAMGM : ∀ s ∈ Set.Ioi (0 : ℝ), Wlam s * A s ≤ Wlam s ^ 2 + A s ^ 2 := by
    intro s _
    nlinarith [sq_nonneg (Wlam s - A s)]
  have hsum_int : IntegrableOn (fun s => Wlam s ^ 2 + A s ^ 2) (Set.Ioi 0) :=
    hWlam_sq_int.add hA2_int
  have hdom_int : IntegrableOn (fun s => BK * (Wlam s * A s)) (Set.Ioi 0) := by
    refine Integrable.mono' (hsum_int.const_mul BK) ?_ ?_
    · exact (hWlam_aesm.mul hA_aesm).const_mul BK
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hnn : 0 ≤ BK * (Wlam s * A s) :=
        mul_nonneg BK_nonneg (mul_nonneg (Wlam_nonneg (le_of_lt hs)) (hAnn s))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left (hAMGM s hs) BK_nonneg
  have h2 : ∫ s in Set.Ioi 0, |Work.Construction.L12dens h s|
      ≤ ∫ s in Set.Ioi 0, BK * (Wlam s * A s) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun s => abs_nonneg _) hdom_int ?_
    show ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)),
      |Work.Construction.L12dens h s| ≤ BK * (Wlam s * A s)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun s hs => ?_
    have hb := hbd s hs
    have hbA : |Work.Construction.L12dens h s| ≤ Wlam s * (BK * A s) := by
      simpa only [hA, hH] using hb
    calc |Work.Construction.L12dens h s| ≤ Wlam s * (BK * A s) := hbA
      _ = BK * (Wlam s * A s) := by ring
  have h3 : ∫ s in Set.Ioi 0, BK * (Wlam s * A s)
      = BK * ∫ s in Set.Ioi 0, Wlam s * A s :=
    MeasureTheory.integral_const_mul BK _
  have h4 : BK * ∫ s in Set.Ioi 0, Wlam s * A s
      ≤ BK * (Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 4 h)) :=
    mul_le_mul_of_nonneg_left hCS BK_nonneg
  calc ∫ s in Set.Ioi 0, |Work.Construction.L12dens h s|
      ≤ ∫ s in Set.Ioi 0, BK * (Wlam s * A s) := h2
    _ = BK * ∫ s in Set.Ioi 0, Wlam s * A s := h3
    _ ≤ BK * (Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 4 h)) := h4
    _ = BK * Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 4 h) := by ring

end Work.FTS.GalBasis.cc
end
-- ===== merged: Submission.Work.FTS.Galerkin.Hilbert =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin

set_option autoImplicit false

/-! ## Accessors for the `ℋ⁴` inner product -/

theorem IsH4Inner.IP_self_nonneg {α : ℝ} {IP : Fn → Fn → ℝ} (h : IsH4Inner α IP) (f : Fn) :
    0 ≤ IP f f := h.isHkIP.2.2.1 f



/-- **Coercivity of `𝓛_Γ^T`** (Propositions `HkCoercivity` of the paper, audit N2): there is
`c > 0` with `c |f|²_{ℋ⁴} ≤ IP (𝓛_Γ^T f) f` for admissible `f`. -/
theorem IsH4Inner.coercive {α : ℝ} {IP : Fn → Fn → ℝ} (h : IsH4Inner α IP) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : Fn, Coercivity.HkAdm α 4 f →
      c * Spaces.HkSq α 4 f ≤ IP (Coercivity.LGammaT α f) f :=
  h.isHkIP.2.2.2.2.2




/-! ## Bilinearity consequences -/








/-! ## The pairing property of an `IP`-orthonormal Galerkin basis -/

/-- **The Galerkin span is `IP`-isometric to `ℝⁿ`.**  This is the *usable* form of the
`IP`-orthonormality of the Galerkin basis `φ`: the pairing of two Galerkin combinations is the
Euclidean pairing of their coefficient vectors.  It is derived from the raw orthonormality
`∀ i j, IP (φ i) (φ j) = if i = j then 1 else 0` by `Projection/ip_galFun_pair`
(the derivation needs no membership hypothesis, since the bilinearity fields of
`Work.Construction.IsH4IP` are unrestricted). -/
def IsIPOrthonormal (IP : Fn → Fn → ℝ) (φ : ℕ → Fn) : Prop :=
  ∀ (n : ℕ) (d c : Fin n → ℝ), IP (galFun φ d) (galFun φ c) = ∑ k : Fin n, d k * c k

/-- The `k`-th test function has coefficient vector `Pi.single k 1`. -/
theorem galFun_single (φ : ℕ → Fn) {n : ℕ} (k : Fin n) :
    galFun φ (Pi.single k (1 : ℝ)) = φ (k : ℕ) := by
  funext z θ
  simp only [galFun]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- Coefficient extraction: the `k`-th coefficient of a Galerkin combination is its `IP`-pairing
with the `k`-th test function. -/
theorem IsIPOrthonormal.coeff {IP : Fn → Fn → ℝ} {φ : ℕ → Fn} (h : IsIPOrthonormal IP φ)
    (n : ℕ) (c : Fin n → ℝ) (k : Fin n) : IP (galFun φ c) (φ (k : ℕ)) = c k := by
  have h1 := h n c (Pi.single k (1 : ℝ))
  rw [← galFun_single φ k, h1]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hk
    exact absurd (Finset.mem_univ k) hk




end Work.FTS.Galerkin
end
end
-- ===== merged: Submission.Work.FTS.H2.HQ.HardyThetaQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.HQ

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped Real Topology
open MeasureTheory Set Filter

open Work.Spaces
open Work.FTS.LocData (SmoothQuad)

/-! ## Elementary angular facts on `Iθ = [0,π/2]`

These are re-proved here (rather than imported from the localisation chapter) so that the file
rests only on the one-dimensional ingredients of `Work.Spaces`: the angular Hardy inequality
`Work.Spaces.HardyTheta`, the weighted Cauchy–Schwarz estimate of `Work.Spaces.HardyZ` and the
quantitative bound `Work.Spaces.sin_two_rpow` for the singular weight. -/

/-- `sin (2θ) ≥ 0` on the closed interval `Iθ = [0,π/2]`. -/
theorem hq_sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin (2θ) > 0` on the open interval `(0,π/2)`. -/
theorem hq_sin_two_pos_of_mem_Ioo {θ : ℝ} (h : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2, Real.pi_pos])

/-- Monotonicity of the interval integral against the set integral over `Iθ`: for `0 < a ≤ b`
and `b < π/2` the interval `[a,b]` sits inside `Iθ`, so the integral of a nonnegative
integrable function over `[a,b]` is at most its integral over `Iθ`. -/
theorem hq_interval_integral_le_setIntegral_Iθ {F : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b < π / 2) (hint : IntegrableOn F Iθ) (hnn : ∀ x ∈ Iθ, 0 ≤ F x) :
    (∫ x in a..b, F x) ≤ ∫ x in Iθ, F x := by
  rw [intervalIntegral.integral_of_le hab]
  refine setIntegral_mono_set hint (ae_restrict_of_forall_mem measurableSet_Icc hnn) ?_
  exact Eventually.of_forall fun x hx =>
    ⟨le_of_lt (lt_trans ha hx.1), le_of_lt (lt_of_le_of_lt hx.2 hb)⟩

/-- **Elgindi's angular Hardy inequality in the interior class.**  `Work.Spaces.HardyTheta`
(proved) is the same inequality for `Work.Spaces.SmoothNbhd` functions, i.e. *analyticity* on a
neighbourhood of the closed quadrant — a class that is false for `F_*`, for the stream functions
and for the cut-off `χ`.  The statement below keeps only what the proof uses: `u` is
`SmoothQuad` (genuine `C^∞` on the open strip `(-1,∞) × (0,π/2)`), the `θ`-slice at the fixed
`z > -1` tends to `0` at `θ → 0⁺` (this replaces `VanishTheta`: only the *limit* from inside is
used, never the value at `θ = 0`), and the Hardy integrand is integrable.  Conclusion:

  `(u z θ)² ≤ (100/(γ-1)) ∫_Iθ (∂_θ u(z,σ))² sin(2σ)^{2-γ} dσ`   for `0 < θ < π/2`.

Proof route (the same as the proved `Work.Spaces.HardyTheta`): for `0 < ε < θ < π/2` write
`u z θ - u z ε = ∫_ε^θ ∂_θ u z σ dσ` (FTC, using `SmoothQuad` for differentiability on
`(0,π/2)` and `hz : -1 < z` for the slice), apply the weighted Cauchy–Schwarz
`Work.Spaces.hardyZ_interval_integral_mul_le_sqrt` to the two factors
`∂_θu · sin(2σ)^{(2-γ)/2}` and `sin(2σ)^{(γ-2)/2}`, bound the second factor's integral by
`100/(γ-1)` (`Work.Spaces.sin_two_rpow`), and let `ε → 0⁺` using `h0`.
`Submission/Work/FTS/H2/LinfQ.lean` contains a draft of this proof (`HardyThetaO`); note that
that file does not compile, so do not import it — write your own. -/
theorem HardyThetaQ (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (u : ℝ → ℝ → ℝ) (z : ℝ)
    (hu : Work.FTS.LocData.SmoothQuad u) (hz : z ∈ Set.Ioi (-1))
    (h0 : Filter.Tendsto (fun θ => u z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.pth u z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo 0 (π / 2), (u z θ) ^ 2 ≤
      (100 / (Work.Spaces.gam α - 1)) * MeasureTheory.integral
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (fun σ => (Work.Spaces.pth u z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) := by
  have hγ1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hp1 : -1 < gam α - 2 := by rw [gam]; linarith
  have hp0 : gam α - 2 ≤ 0 := by rw [gam]; linarith
  have hne0 : Work.Stability.smoothOrder ≠ 0 := Work.FTS.LocData.smoothOrder_ne_zero
  -- smoothness of the `θ`-slice and of its derivative on `(0,π/2)`
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => u z θ')
      (Set.Ioo 0 (π / 2)) :=
    hu.curry_θ hz
  have hdth : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => pth u z θ')
      (Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.contDiffOn_slice_θ
      (Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU hu) hz
  intro θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < π / 2 := hθ.2
  set A : ℝ := ∫ σ in Iθ, (pth u z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) with hAdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact setIntegral_nonneg measurableSet_Icc fun σ hσ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hq_sin_two_nonneg hσ) _)
  have hKnn : 0 ≤ 100 / (gam α - 1) := div_nonneg (by norm_num) hγ1.le
  -- the bound at every `ε ∈ (0,θ)`
  have hkey : ∀ ε ∈ Set.Ioo 0 θ, (u z θ - u z ε) ^ 2 ≤ (100 / (gam α - 1)) * A := by
    intro ε hε
    have hεθ : ε ≤ θ := le_of_lt hε.2
    have hsub : Set.uIcc ε θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
      intro x hx
      rw [Set.uIcc_of_le hεθ] at hx
      exact ⟨lt_of_lt_of_le hε.1 hx.1, lt_of_le_of_lt hx.2 hθ1⟩
    have hsubI : Set.Icc ε θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
      rw [← Set.uIcc_of_le hεθ]; exact hsub
    have hcontθ : ContinuousOn (fun θ' => u z θ') (Set.Icc ε θ) :=
      hslice.continuousOn.mono hsubI
    have hpthcont : ContinuousOn (fun s => pth u z s) (Set.uIcc ε θ) :=
      hdth.continuousOn.mono hsub
    have hderiv : ∀ x ∈ Set.Ioo ε θ, HasDerivAt (fun θ' => u z θ') (pth u z x) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (π / 2) :=
        ⟨lt_trans hε.1 hx.1, lt_of_lt_of_le hx.2 hθ1.le⟩
      exact ((hslice.differentiableOn hne0).differentiableAt
        (isOpen_Ioo.mem_nhds hx')).hasDerivAt
    have hintε : IntervalIntegrable (fun s => pth u z s) volume ε θ :=
      hpthcont.intervalIntegrable
    have hFTC : ∫ s in ε..θ, pth u z s = u z θ - u z ε :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hεθ hcontθ hderiv hintε
    have hsincont : ∀ c : ℝ,
        ContinuousOn (fun s : ℝ => (Real.sin (2 * s)) ^ c) (Set.uIcc ε θ) := fun c =>
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun s hs => Or.inl (ne_of_gt (hq_sin_two_pos_of_mem_Ioo (hsub hs))))
    have hcs := hardyZ_interval_integral_mul_le_sqrt ε θ hεθ
      (hpthcont.mul (hsincont ((2 - gam α) / 2))) (hsincont ((gam α - 2) / 2))
    have hcongr : ∫ s in ε..θ,
          (pth u z s * (Real.sin (2 * s)) ^ ((2 - gam α) / 2))
            * (Real.sin (2 * s)) ^ ((gam α - 2) / 2)
        = ∫ s in ε..θ, pth u z s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hs' := hsub hs
      have hsin : 0 < Real.sin (2 * s) := hq_sin_two_pos_of_mem_Ioo hs'
      have h1 : (Real.sin (2 * s)) ^ ((2 - gam α) / 2)
          * (Real.sin (2 * s)) ^ ((gam α - 2) / 2) = 1 := by
        rw [← Real.rpow_add hsin, show (2 - gam α) / 2 + (gam α - 2) / 2 = 0 by ring,
          Real.rpow_zero]
      rw [mul_assoc, h1, mul_one]
    have hAint : ∫ s in ε..θ, (pth u z s * (Real.sin (2 * s)) ^ ((2 - gam α) / 2)) ^ 2 ≤ A := by
      have hEq : ∫ s in ε..θ, (pth u z s * (Real.sin (2 * s)) ^ ((2 - gam α) / 2)) ^ 2
          = ∫ s in ε..θ, (pth u z s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        have hs' := hsub hs
        have h1 : ((Real.sin (2 * s)) ^ ((2 - gam α) / 2)) ^ 2
            = (Real.sin (2 * s)) ^ (2 - gam α) := by
          rw [pow_two, ← Real.rpow_add (hq_sin_two_pos_of_mem_Ioo hs')]
          congr 1
          ring
        rw [mul_pow, h1]
      rw [hEq, hAdef]
      exact hq_interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1 hint fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hq_sin_two_nonneg hx) _)
    have hBint : ∫ s in ε..θ, ((Real.sin (2 * s)) ^ ((gam α - 2) / 2)) ^ 2
        ≤ 100 / (gam α - 1) := by
      have hEq : ∫ s in ε..θ, ((Real.sin (2 * s)) ^ ((gam α - 2) / 2)) ^ 2
          = ∫ s in ε..θ, (Real.sin (2 * s)) ^ (gam α - 2) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [pow_two, ← Real.rpow_add (hq_sin_two_pos_of_mem_Ioo (hsub hs))]
        congr 1
        ring
      rw [hEq]
      refine le_trans (hq_interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1
        (sin_two_rpow (gam α - 2) hp1 hp0).1
        (fun x hx => Real.rpow_nonneg (hq_sin_two_nonneg hx) _)) ?_
      have h2 := (sin_two_rpow (gam α - 2) hp1 hp0).2
      rwa [show (gam α - 2) + 1 = gam α - 1 by ring] at h2
    have hstep : |u z θ - u z ε| ≤ Real.sqrt A * Real.sqrt (100 / (gam α - 1)) := by
      rw [← hFTC, ← hcongr]
      exact le_trans hcs (mul_le_mul (Real.sqrt_le_sqrt hAint) (Real.sqrt_le_sqrt hBint)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hsq : (u z θ - u z ε) ^ 2
        ≤ (Real.sqrt A * Real.sqrt (100 / (gam α - 1))) ^ 2 :=
      sq_le_sq' (by linarith [neg_abs_le (u z θ - u z ε), hstep])
        (le_trans (le_abs_self _) hstep)
    calc (u z θ - u z ε) ^ 2
        ≤ (Real.sqrt A * Real.sqrt (100 / (gam α - 1))) ^ 2 := hsq
      _ = A * (100 / (gam α - 1)) := by rw [mul_pow, Real.sq_sqrt hAnn, Real.sq_sqrt hKnn]
      _ = (100 / (gam α - 1)) * A := by ring
  -- pass to the limit `ε → 0⁺`
  have hlim : Tendsto (fun ε => (u z θ - u z ε) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 ((u z θ) ^ 2)) := by
    have h1 : Tendsto (fun ε => u z θ - u z ε) (𝓝[>] (0 : ℝ)) (𝓝 (u z θ - 0)) :=
      tendsto_const_nhds.sub h0
    simpa using h1.pow 2
  refine le_of_tendsto hlim ?_
  rw [eventually_nhdsWithin_iff]
  filter_upwards [isOpen_Iio.mem_nhds hθ0] with ε hε hε0
  exact hkey ε ⟨hε0, hε⟩

end Work.FTS.H2.HQ
end
-- ===== merged: Submission.Work.FTS.H2.L12densIntegrable =====
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

set_option linter.unusedVariables false

/-- `SmoothQuad` gives continuity of the uncurried datum on the open quadrant `Qd`. -/
private lemma continuousOn_uncurry_Qd {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g) :
    ContinuousOn (Function.uncurry g) Qd := by
  have h := hsm
  rw [Work.FTS.LocData.SmoothQuad] at h
  exact h.continuousOn.mono (fun p hp => by
    simp only [Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
    exact ⟨by linarith [hp.1], hp.2⟩)

/-! ## Pointwise domination of `g²` by the `ℋ⁴`-integrand

The `D_z⁰`-term of `HkIntegrand α 4 g` carries the weight `w/sin(2θ)^{η/2}`; since
`sin(2θ)^{η/2} ≤ 1` and `w ≥ 1` on the quadrant, this term dominates `g² w²`, hence
`g²` is dominated by `HkIntegrand/(w s)²`.  The radial weight `w s = (1+s)²/s²` is exactly
what absorbs the `1/s` of the density in the Cauchy–Schwarz step. -/

/-- On the open quadrant, `(g s θ)² ≤ HkIntegrand α 4 g s θ / (w s)²`. -/
private lemma g_sq_le_HkIntegrand_div_w_sq (α : ℝ) (g : ℝ → ℝ → ℝ) {s θ : ℝ} (hs : 0 < s)
    (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    (g s θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ / (Work.Spaces.w s) ^ 2 := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  set S : ℝ := (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hSdef
  have hSpos : 0 < S := by rw [hSdef]; exact Real.rpow_pos_of_pos hsin _
  have hSsq : S ^ 2 ≤ 1 := by
    have h2 : S ^ 2 = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
      rw [hSdef, ← Real.rpow_natCast, ← Real.rpow_mul hsin.le]; norm_num
    calc S ^ 2 = (Real.sin (2 * θ)) ^ Work.Spaces.eta := h2
      _ ≤ 1 := Real.rpow_le_one hsin.le (Real.sin_le_one _) (le_of_lt Work.Spaces.eta_pos)
  have hkey : (g s θ * (Work.Spaces.w s / S)) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ := by
    simpa only [Work.Spaces.DzIter_zero] using
      Work.Spaces.sq_le_HkIntegrand_z α 4 g s θ 0 (by norm_num)
  have hwpos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hstep : (g s θ) ^ 2 * (Work.Spaces.w s) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ := by
    calc (g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
        ≤ (g s θ) ^ 2 * (Work.Spaces.w s) ^ 2 / S ^ 2 := by
          rw [le_div_iff₀ (pow_pos hSpos 2)]
          nlinarith [mul_nonneg (sq_nonneg (g s θ)) (sq_nonneg (Work.Spaces.w s)), hSsq]
      _ = (g s θ * (Work.Spaces.w s / S)) ^ 2 := by
          rw [mul_pow, div_pow, mul_div_assoc]
      _ ≤ _ := hkey
  exact (le_div_iff₀ (pow_pos hwpos 2)).mpr hstep

/-! ## The pointwise bound on the density -/

/-- **The pointwise bound on the `L₁₂`-density.**  For `g` smooth on the open quadrant and
`g ∈ ℋ⁴`, and for `s > 0`,

`|L12dens g s| ≤ (√(∫_θ K(θ)² dθ) + 1)·(s/(1+s)²)·√(∫_θ HkIntegrand α 4 g s θ)`.

The angular integral is bounded by Cauchy–Schwarz in `θ` (`Work.Spaces.cs_integral`)
against `Ktheta ∈ L²` and the slice `L²`-norm `√(∫_θ (g s θ)²)`, which in turn is dominated
by `√(∫_θ HkIntegrand α 4 g s θ)/w s` through the pointwise domination above; the factor
`(1/(s·w s)) = s/(1+s)²` is the sublinear weight at the origin that makes the density
integrable there. -/
private lemma L12dens_abs_le_quad (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) {s : ℝ}
    (hs : 0 < s) :
    |Work.Elliptic.L12dens g s|
      ≤ (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
        * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
  have hcontg : ContinuousOn (Function.uncurry g) Qd := continuousOn_uncurry_Qd hsm
  have haesm : AEStronglyMeasurable (fun θ => g s θ) (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry g) hcontg hs
  have hwpos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hw1 : 1 ≤ Work.Spaces.w s := Work.Elliptic.one_le_w hs
  have hpk : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (g s θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ / (Work.Spaces.w s) ^ 2 :=
    Work.Elliptic.ae_restrict_Iθ_of_Ioo (fun θ h0 h1 => g_sq_le_HkIntegrand_div_w_sq α g hs h0 h1)
  -- the θ-slice of `g²` is integrable on `Iθ`, dominated by the `ℋ⁴`-integrand
  have hSqInt : IntegrableOn (fun θ => (g s θ) ^ 2) Work.Spaces.Iθ := by
    refine Integrable.mono' (hmem.1 s hs.le) (haesm.pow 2) ?_
    filter_upwards [hpk] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    refine le_trans hθ ?_
    rw [div_le_iff₀ (pow_pos hwpos 2)]
    calc Work.Spaces.HkIntegrand α 4 g s θ
        = Work.Spaces.HkIntegrand α 4 g s θ * 1 := by ring
      _ ≤ Work.Spaces.HkIntegrand α 4 g s θ * (Work.Spaces.w s) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith [hw1]) (Work.Spaces.HkIntegrand_nonneg α 4 g s θ)
  have hKmem : MemLp (fun θ => Work.Elliptic.Ktheta θ) 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq
      Work.Elliptic.continuous_ktheta.aestronglyMeasurable).mpr
      ((Work.Elliptic.continuous_ktheta.continuousOn.pow 2).integrableOn_compact isCompact_Icc)
  have hGmem : MemLp (fun θ => g s θ) 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq haesm).mpr hSqInt
  have hcs := Work.Spaces.cs_integral hKmem hGmem
  have hA : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    integral_nonneg (fun θ => sq_nonneg _)
  have hH : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ :=
    integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g s θ)
  have hintle : ∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) / (Work.Spaces.w s) ^ 2 := by
    have h := MeasureTheory.integral_mono_ae hSqInt ((hmem.1 s hs.le).div_const _) hpk
    rwa [MeasureTheory.integral_div] at h
  -- Cauchy–Schwarz in the angle, then the slice `L²`-bound
  have hab : |∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * g s θ|
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
          / Work.Spaces.w s) := by
    have h1 : |∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * g s θ|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) := by
      calc |∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * g s θ|
          = Real.sqrt ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * g s θ) ^ 2) :=
            (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2)) := Real.sqrt_le_sqrt hcs
        _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) := Real.sqrt_mul hA _
    have h2 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2)
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
          / Work.Spaces.w s := by
      calc Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2)
          ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
              / (Work.Spaces.w s) ^ 2) := Real.sqrt_le_sqrt hintle
        _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
              / Real.sqrt ((Work.Spaces.w s) ^ 2) := Real.sqrt_div hH _
        _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
              / Work.Spaces.w s := by
            rw [Real.sqrt_sq_eq_abs, abs_of_pos hwpos]
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))
  have key : (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
          / Work.Spaces.w s)) / s
      = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
    rw [Work.Spaces.w]; field_simp; try ring
  rw [Work.Elliptic.L12dens_eq_angMoment_div, Work.Elliptic.angMoment, abs_div, abs_of_pos hs]
  calc |∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * g s θ| / s
      ≤ (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
          / Work.Spaces.w s)) / s := by
        rw [div_le_div_iff_of_pos_right hs]; exact hab
    _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := key
    _ ≤ (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1) * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)

/-! ## A.e. strong measurability of the density

The joint integrand `(s,θ) ↦ K(θ)·g(s,θ)/s` is continuous on the open quadrant, hence a.e.
strongly measurable for `(volume.restrict Iz).prod (volume.restrict Iθ)`
(`Work.Spaces.aesm_of_continuousOn_Qd`); Fubini measurability of the partial integral
(`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`) then gives the a.e. strong
measurability of `s ↦ ∫_θ K(θ)·g(s,θ)/s = L12dens g s` for `volume.restrict Iz`. -/

/-- `L12dens g` is a.e. strongly measurable on `Iz = [0,∞)` for `SmoothQuad` data. -/
private lemma L12dens_aesm (g : ℝ → ℝ → ℝ) (hsm : Work.FTS.LocData.SmoothQuad g) :
    AEStronglyMeasurable (Work.Elliptic.L12dens g) (volume.restrict Work.Spaces.Iz) := by
  have hcontg : ContinuousOn (Function.uncurry g) Qd := continuousOn_uncurry_Qd hsm
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2) Qd :=
    Work.Elliptic.continuous_ktheta.comp_continuousOn continuous_snd.continuousOn
  have hF : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * g p.1 p.2 / p.1) Qd :=
    (h1.mul hcontg).div continuousOn_fst (fun p hp => ne_of_gt hp.1)
  have hjoint := Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * g p.1 p.2 / p.1) hF
  have h := hjoint.integral_prod_right' (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
  convert h using 1
  funext z
  rfl

/-! ## The main theorem -/

/-- `L12dens g ∈ L¹((0,∞))` from `SmoothQuad g` and `HkMem α 4 g` alone (no analyticity, no
`SmoothNbhd`).  Route: `|L12dens g s| ≤ sqrt(∫_θ Ktheta²)·(1/w s)·sqrt(∫_θ HkIntegrand α 4 g s θ)`
for `s > 0` (Cauchy–Schwarz in `θ` against `Ktheta ∈ L²`, together with
`(g s θ)² ≤ HkIntegrand α 4 g s θ / (w s)²` for a.e. `θ`, which is
`Work.Spaces.sq_le_HkIntegrand_z` combined with `sin(2θ)^{η/2} ≤ 1` and `w ≥ 1`);
then Cauchy–Schwarz in `s` against `(1/w s)/s = s/(1+s)² ∈ L²((0,∞))`
(`Work.Elliptic.psi_sq_integrable_aux`, in `Submission/Work/Elliptic/L12densFacts.lean`) and
`∫_s ∫_θ HkIntegrand α 4 g = HkSq α 4 g` (that is the definition of `HkSq`; no integrability of
the product measure is needed: the inner `θ`-integral is finite for every `s ∈ Iz` by `hmem.1`
and the pointwise domination, and `hmem.2` gives the outer integral). -/
theorem L12densIntegrable (α : ℝ) (g : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi 0) := by
  set C : ℝ := Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have haesm := L12dens_aesm g hsm
  -- AM–GM domination of the density by an integrable function, a.e. on `Iz`
  have hbd : ∀ᵐ s ∂(volume.restrict Work.Spaces.Iz),
      ‖Work.Elliptic.L12dens g s‖ ≤ (C / 2) * ((s / (1 + s) ^ 2) ^ 2
        + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with s hs
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ s from hs) with h0 | hpos
    · -- at `s = 0` both sides are `0` (the density is divided by `0`, hence vanishes)
      subst h0
      have hz : Work.Elliptic.L12dens g 0 = 0 := by
        rw [Work.Elliptic.L12dens]; simp
      rw [hz, norm_zero]
      have hX : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g 0 θ :=
        integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ)
      refine mul_nonneg (by linarith [hCpos]) ?_
      have h0' : ((0 : ℝ) / (1 + 0) ^ 2) ^ 2 = 0 := by norm_num
      rw [h0', zero_add]
      exact hX
    · have h1 := L12dens_abs_le_quad α g hsm hmem hpos
      have hX : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ :=
        integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g s θ)
      have hAM : C * (s / (1 + s) ^ 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
          ≤ (C / 2) * ((s / (1 + s) ^ 2) ^ 2
            + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
        nlinarith [sq_nonneg ((s / (1 + s) ^ 2)
            - Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)),
          Real.sq_sqrt hX]
      rw [Real.norm_eq_abs, hCdef]
      exact le_trans h1 hAM
  -- the dominating function is integrable on `Iz`
  have hH_int : IntegrableOn (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
      Work.Spaces.Iz := hmem.2
  have hpsi : IntegrableOn (fun s => (s / (1 + s) ^ 2) ^ 2) Work.Spaces.Iz := by
    change MeasureTheory.Integrable (fun s : ℝ => (s / (1 + s) ^ 2) ^ 2)
      (volume.restrict Work.Spaces.Iz)
    rw [← Work.Elliptic.restrict_Ioi_eq_restrict_Iz]
    exact Work.Elliptic.psi_sq_integrable_aux
  have hdom : IntegrableOn (fun s => (C / 2) * ((s / (1 + s) ^ 2) ^ 2
      + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)) Work.Spaces.Iz :=
    (hpsi.add hH_int).const_mul (C / 2)
  have hIntIz : IntegrableOn (Work.Elliptic.L12dens g) Work.Spaces.Iz := hdom.mono' haesm hbd
  exact hIntIz.mono_set Set.Ioi_subset_Ici_self

end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.LocData.DzIter_bumpZ_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- **The action of `D_z = z ∂_z` on functions of `z` alone**: `T1 g z = z ∂_z g z`.  This is
`Work.Spaces.Dz` on a function which does not depend on `θ`; pulling the iteration down to one
variable makes the compact-support argument transparent. -/
noncomputable def T1 (g : ℝ → ℝ) : ℝ → ℝ := fun z => z * deriv g z

/-- A function vanishing off a *closed* set has zero derivative on the complement: the complement
is open, so such a point has a whole neighbourhood on which the function is `0`. -/
theorem deriv_eq_zero_of_eq_zero_off_closed {g : ℝ → ℝ} {s : Set ℝ} (hs : IsClosed s)
    (hvan : ∀ z', z' ∉ s → g z' = 0) {z : ℝ} (hz : z ∉ s) : deriv g z = 0 := by
  have hmem : sᶜ ∈ 𝓝 z := hs.isOpen_compl.mem_nhds hz
  have hev : g =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [hmem] with z' hz'
    exact hvan z' hz'
  rw [Filter.EventuallyEq.deriv_eq hev]
  simp

/-- `T1` preserves `C^∞`: the derivative of a smooth function is smooth. -/
theorem T1_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (T1 g) := by
  have h := (contDiff_deriv hg).1
  rw [show T1 g = (fun z : ℝ => z * deriv g z) from rfl]
  exact ContDiff.mul contDiff_id h

/-- **The invariant of the iteration**: every iterate of `T1` applied to a smooth function
vanishing off `[3/4, 7/4]` is again smooth and vanishes off `[3/4, 7/4]`. -/
theorem T1_iterate_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hvan : ∀ z, z ∉ Set.Icc (3 / 4 : ℝ) (7 / 4) → g z = 0) (c : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) ((T1^[c]) g) ∧
      ∀ z, z ∉ Set.Icc (3 / 4 : ℝ) (7 / 4) → (T1^[c]) g z = 0 := by
  induction c with
  | zero => exact ⟨by simpa using hg, by simpa using hvan⟩
  | succ c ih =>
      obtain ⟨hc, hv⟩ := ih
      refine ⟨?_, ?_⟩
      · rw [Function.iterate_succ_apply']
        exact T1_contDiff hc
      · intro z hz
        rw [Function.iterate_succ_apply']
        show z * deriv ((T1^[c]) g) z = 0
        rw [deriv_eq_zero_of_eq_zero_off_closed isClosed_Icc hv hz, mul_zero]

/-- Every iterate of `T1` on `bumpZ` is bounded on the whole line. -/
theorem exists_bound_T1_iterate_bumpZ (c : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℝ, |(T1^[c]) bumpZ z| ≤ M := by
  obtain ⟨hc, hv⟩ := T1_iterate_contDiff BumpZ_contDiff bumpZ_eq_zero_of_notMem_Icc c
  exact exists_bound_of_continuous_of_vanishes_off_Icc (by norm_num) hc.continuous hv

/-- **`D_z^c` on `bumpZ` as a function of `z` is the `c`-th iterate of `T1`.**  The `θ`-variable is
a dummy in `fun z _ => bumpZ z`, so `Work.Spaces.pz` is the plain derivative. -/
theorem DzIter_bumpZ_eq (c : ℕ) (θ z : ℝ) :
    Work.Spaces.DzIter c (fun z _ => bumpZ z) z θ = (T1^[c]) bumpZ z := by
  induction c generalizing z with
  | zero => rfl
  | succ c ih =>
      rw [Work.Spaces.DzIter_succ, Function.iterate_succ_apply']
      have hfun : (fun z' : ℝ => Work.Spaces.DzIter c (fun z _ => bumpZ z) z' θ)
          = (T1^[c]) bumpZ := funext fun z' => ih z'
      show z * deriv (fun z' : ℝ => Work.Spaces.DzIter c (fun z _ => bumpZ z) z' θ) z
          = T1 ((T1^[c]) bumpZ) z
      rw [hfun]
      rfl

/-- **The `D_z`-derivatives of the bump up to order `4` are uniformly bounded.** -/
theorem DzIter_bumpZ_bound :
    ∃ C : ℝ, ∀ c : ℕ, c ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => bumpZ z) z θ| ≤ C := by
  classical
  let M : ℕ → ℝ := fun c => Classical.choose (exists_bound_T1_iterate_bumpZ c)
  have hM : ∀ c : ℕ, 0 ≤ M c ∧ ∀ z : ℝ, |(T1^[c]) bumpZ z| ≤ M c := fun c =>
    Classical.choose_spec (exists_bound_T1_iterate_bumpZ c)
  refine ⟨∑ c ∈ Finset.range 5, M c, ?_⟩
  intro c hc z _hz θ
  rw [DzIter_bumpZ_eq c θ z]
  have h1 : |(T1^[c]) bumpZ z| ≤ M c := (hM c).2 z
  have h2 : M c ≤ ∑ d ∈ Finset.range 5, M d :=
    Finset.single_le_sum (fun d _ => (hM d).1) (Finset.mem_range.mpr (by omega))
  linarith

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.Fstar_factor =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-- The `z`-argument of `DthIter i (fun _ θ' => Gam α θ')` is dummy. -/
theorem DthIter_gamFn_z_indep (α : ℝ) (i : ℕ) (z z' θ : ℝ) :
    Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') z θ
      = Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') z' θ := by
  induction i generalizing z z' θ with
  | zero => rfl
  | succ i ih =>
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [show (fun θ' => Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') z θ')
            = (fun θ' => Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') z' θ')
          from funext (fun t => ih z z' t)]

/-- The `∂_z`-iterates of `Fstar α` act on the `z`-factor `FM.Fstar`. -/
theorem DzIter_Fstar_eq (α : ℝ) (i : ℕ) :
    Work.Spaces.DzIter i (Work.Construction.Fstar α)
      = fun z θ => (α / Work.Spaces.c α) * Work.Spaces.Gam α θ
          * Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z θ := by
  induction i with
  | zero =>
      funext z θ
      simp only [Work.Spaces.DzIter_zero]
      rw [Work.Construction.Fstar]
      ring
  | succ i ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      rw [deriv_const_mul_field]
      ring

/-- The `∂_θ`-iterates of `Fstar α` act on the `θ`-factor `Gam α`. -/
theorem DthIter_Fstar_eq (α : ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (Work.Construction.Fstar α)
      = fun z θ => (α / Work.Spaces.c α) * Work.FM.Fstar z
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') z θ := by
  induction i with
  | zero =>
      funext z θ
      simp only [Work.Spaces.DthIter_zero]
      rw [Work.Construction.Fstar]
      ring
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_field]
      ring

/-- The mixed iterates of `Fstar α` are the product of the two one-dimensional iterates. -/
theorem mixed_Fstar_eq (α : ℝ) (i j : ℕ) :
    Work.Spaces.mixed j i (Work.Construction.Fstar α)
      = fun z θ => (α / Work.Spaces.c α)
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ
          * Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ := by
  have h2 : Work.Spaces.DthIter i (Work.Construction.Fstar α)
      = fun z θ => ((α / Work.Spaces.c α)
            * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)
          * (fun z _ => Work.FM.Fstar z) z θ := by
    rw [DthIter_Fstar_eq]
    funext z θ
    rw [DthIter_gamFn_z_indep α i z 0 θ]
    ring
  rw [Work.Spaces.mixed, h2, DzIter_mul_theta_factor]

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.HkIntegrand_add_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Additivity of the iterated operators on the open quadrant

The data are `SmoothQuad`, i.e. `C^∞` on `quadU = (-1,∞) × (0,π/2)`; on that open set the
derivatives are honest, so `deriv_add` gives the additivity of `D_z`, and induction gives it
for `D_z^i` and `D_θ^i`. -/

/-- Two functions agreeing on `quadU` have the same `D_z`-iterates there. -/
private lemma DzIter_congr_quad {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, -1 < z → 0 < θ → θ < π / 2 → F z θ = G z θ) (j : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter j F z θ = Work.Spaces.DzIter j G z θ := by
  induction j with
  | zero => intro z θ hz h1 h2; exact h z θ hz h1 h2
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n F z' θ) =ᶠ[𝓝 z]
          (fun z' => Work.Spaces.DzIter n G z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq]

/-- `D_θ`-iterates are additive on the open quadrant for `SmoothQuad` data. -/
private lemma DthIter_add_quad {a b : ℝ → ℝ → ℝ} (ha : SmoothQuad a)
    (hb : SmoothQuad b) (i : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DthIter i (fun z θ => a z θ + b z θ) z θ
        = Work.Spaces.DthIter i a z θ + Work.Spaces.DthIter i b z θ := by
  induction i with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun θ' => Work.Spaces.DthIter n (fun z θ => a z θ + b z θ) z θ') =ᶠ[𝓝 θ]
          (fun θ' => Work.Spaces.DthIter n a z θ' + Work.Spaces.DthIter n b z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (π / 2) from ⟨h1, h2⟩)] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n a z θ') θ :=
        ha.differentiableAt_slice_DthIter n hz ⟨h1, h2⟩
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n b z θ') θ :=
        hb.differentiableAt_slice_DthIter n hz ⟨h1, h2⟩
      have hd : deriv (fun θ' => Work.Spaces.DthIter n a z θ' + Work.Spaces.DthIter n b z θ') θ
          = deriv (fun θ' => Work.Spaces.DthIter n a z θ') θ
            + deriv (fun θ' => Work.Spaces.DthIter n b z θ') θ :=
        deriv_add hd1 hd2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq, hd]
      ring

/-- `D_z`-iterates are additive on the open quadrant for `SmoothQuad` data. -/
private lemma DzIter_add_quad {a b : ℝ → ℝ → ℝ} (ha : SmoothQuad a)
    (hb : SmoothQuad b) (i : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter i (fun z θ => a z θ + b z θ) z θ
        = Work.Spaces.DzIter i a z θ + Work.Spaces.DzIter i b z θ := by
  induction i with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => a z θ + b z θ) z' θ) =ᶠ[𝓝 z]
          (fun z' => Work.Spaces.DzIter n a z' θ + Work.Spaces.DzIter n b z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n a z' θ) z :=
        ha.differentiableAt_slice_DzIter n hz ⟨h1, h2⟩
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n b z' θ) z :=
        hb.differentiableAt_slice_DzIter n hz ⟨h1, h2⟩
      have hd : deriv (fun z' => Work.Spaces.DzIter n a z' θ + Work.Spaces.DzIter n b z' θ) z
          = deriv (fun z' => Work.Spaces.DzIter n a z' θ) z
            + deriv (fun z' => Work.Spaces.DzIter n b z' θ) z :=
        deriv_add hd1 hd2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq, hd]
      ring

/-- The mixed operators `D_z^j D_θ^i` are additive on the open quadrant for `SmoothQuad` data. -/
private lemma mixed_add_quad {a b : ℝ → ℝ → ℝ} (ha : SmoothQuad a)
    (hb : SmoothQuad b) (j i : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed j i (fun z θ => a z θ + b z θ) z θ
        = Work.Spaces.mixed j i a z θ + Work.Spaces.mixed j i b z θ := by
  intro z θ hz h1 h2
  have hcongr := DzIter_congr_quad (j := j)
    (F := Work.Spaces.DthIter i (fun z θ => a z θ + b z θ))
    (G := fun z θ => Work.Spaces.DthIter i a z θ + Work.Spaces.DthIter i b z θ)
    (fun z θ hz h1 h2 => DthIter_add_quad ha hb i z θ hz h1 h2) z θ hz h1 h2
  have hadd := DzIter_add_quad (ha.DthIter i) (hb.DthIter i) j z θ hz h1 h2
  simp only [Work.Spaces.mixed]
  exact hcongr.trans hadd

/-! ## Vanishing of the integrand on the two boundary lines -/

/-- At `sin(2θ) = 0` the `D_θ`-iterates of order `≥ 1` vanish at that same `θ`. -/
private lemma DthIter_succ_eq_zero_of_sin (f : ℝ → ℝ → ℝ) {θ : ℝ} (hs : Real.sin (2 * θ) = 0)
    (m : ℕ) (z : ℝ) : Work.Spaces.DthIter (m + 1) f z θ = 0 := by
  simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth, hs, zero_mul]

/-- A function whose `θ`-slice vanishes identically has vanishing `D_z`-iterates there. -/
private lemma DzIter_eq_zero_of_slice (f : ℝ → ℝ → ℝ) {θ : ℝ} (h : ∀ z, f z θ = 0) :
    ∀ (j : ℕ) (z : ℝ), Work.Spaces.DzIter j f z θ = 0 := by
  intro j
  induction j with
  | zero => intro z; exact h z
  | succ n ih =>
      intro z
      have hslice : (fun z' => Work.Spaces.DzIter n f z' θ) = fun _ => (0 : ℝ) := funext ih
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [hslice]
      simp

/-- At `sin(2θ) = 0` every mixed derivative `D_z^j D_θ^i` with `i ≥ 1` vanishes at `(z,θ)`. -/
private lemma mixed_eq_zero_of_sin (f : ℝ → ℝ → ℝ) {θ : ℝ} (hs : Real.sin (2 * θ) = 0)
    {j i : ℕ} (hi : 1 ≤ i) (z : ℝ) : Work.Spaces.mixed j i f z θ = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  simp only [Work.Spaces.mixed]
  exact DzIter_eq_zero_of_slice (Work.Spaces.DthIter (m + 1) f) (θ := θ)
    (fun z' => DthIter_succ_eq_zero_of_sin f hs m z') j z

/-- The `ℋ^k`-integrand vanishes on the angular boundary `sin(2θ) = 0`: the first sum is killed
by the `1/sin(2θ)^{η/2}` factor and the second by the `D_θ`-factors of all its summands. -/
private lemma HkIntegrand_eq_zero_of_sin (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hs : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α k f z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have hsin : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hs, Real.zero_rpow (by norm_num [Work.Spaces.eta])]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hsin, div_zero, mul_zero, zero_pow (by norm_num)]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hc
    · rw [mixed_eq_zero_of_sin f hs hc.1 z, zero_mul, zero_pow (by norm_num)]
    · rfl
  rw [h1, h2, add_zero]

/-- The `ℋ^k`-integrand vanishes on the radial boundary `z = 0` (where `w 0 = 0`). -/
private lemma HkIntegrand_eq_zero_of_z_eq_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  simp [Work.Spaces.w, Work.Spaces.Wt, Work.Spaces.wTheta]

/-! ## The algebraic core: sums of squares of sums -/

private lemma sum_sq_add_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ) :
    (∑ i ∈ s, (x i + y i) ^ 2) ≤ 2 * (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, y i ^ 2) := by
  calc (∑ i ∈ s, (x i + y i) ^ 2)
      ≤ ∑ i ∈ s, (2 * x i ^ 2 + 2 * y i ^ 2) :=
        Finset.sum_le_sum fun i _ => by
          have h := add_sq_le (a := x i) (b := y i); linarith
    _ = 2 * (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, y i ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The pointwise inequality, given the additivity of the iterated operators at `(z,θ)`. -/
private lemma HkIntegrand_add_le_pt (α : ℝ) (k : ℕ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hz : ∀ i, Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.DzIter i f z θ + Work.Spaces.DzIter i g z θ)
    (hm : ∀ i j, Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ) :
    Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α k f z θ
        + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  have hZ : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    have h1 : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∑ i ∈ Finset.range (k + 1),
          ((Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
            + (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hz i]; ring
    rw [h1]
    exact sum_sq_add_le _ _ _
  have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
    set S : Finset (ℕ × ℕ) := ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
      (fun p => 1 ≤ p.1 ∧ p.1 + p.2 ≤ k) with hS
    have e : ∀ u : ℝ → ℝ → ℝ,
        (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i u z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          = ∑ p ∈ S, (Work.Spaces.mixed p.2 p.1 u z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      intro u
      rw [hS, Finset.sum_filter, Finset.sum_product]
    rw [e f, e g, e (fun z θ => f z θ + g z θ)]
    have hconv : (∑ p ∈ S,
          (Work.Spaces.mixed p.2 p.1 (fun z θ => f z θ + g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2)
        = ∑ p ∈ S, ((Work.Spaces.mixed p.2 p.1 f z θ * Work.Spaces.Wt α z θ)
            + (Work.Spaces.mixed p.2 p.1 g z θ * Work.Spaces.Wt α z θ)) ^ 2 := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hm p.1 p.2]; ring
    rw [hconv]
    exact sum_sq_add_le _ _ _
  simp only [Work.Spaces.HkIntegrand]
  linarith [hZ, hM]

/-! ## The theorem -/

theorem HkIntegrand_add_le (α : ℝ) (k : ℕ) {a b : ℝ → ℝ → ℝ} (hsa : SmoothQuad a)
    (hsb : SmoothQuad b) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => a z θ + b z θ) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α k a z θ + 2 * Work.Spaces.HkIntegrand α k b z θ := by
  by_cases hz0 : z = 0
  · rw [hz0, HkIntegrand_eq_zero_of_z_eq_zero]
    have h1 := Work.Spaces.HkIntegrand_nonneg α k a 0 θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α k b 0 θ
    linarith
  by_cases hs : Real.sin (2 * θ) = 0
  · rw [HkIntegrand_eq_zero_of_sin α k (fun z θ => a z θ + b z θ) hs]
    have h1 := Work.Spaces.HkIntegrand_nonneg α k a z θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α k b z θ
    linarith
  · have hzge : 0 ≤ z := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hz
    have hzpos : 0 < z := lt_of_le_of_ne hzge (Ne.symm hz0)
    have hbnd : 0 ≤ θ ∧ θ ≤ π / 2 := by simpa only [Work.Spaces.Iθ, Set.mem_Icc] using hθ
    have hθ1 : 0 < θ := by
      rcases eq_or_lt_of_le hbnd.1 with h | h
      · exact absurd (by rw [← h]; simp) hs
      · exact h
    have hθ2 : θ < π / 2 := by
      rcases lt_or_eq_of_le hbnd.2 with h | h
      · exact h
      · exact absurd (by rw [h, show (2 : ℝ) * (π / 2) = π from by ring, Real.sin_pi]) hs
    exact HkIntegrand_add_le_pt α k a b z θ
      (fun i => DzIter_add_quad hsa hsb i z θ (by linarith) hθ1 hθ2)
      (fun i j => mixed_add_quad hsa hsb j i z θ (by linarith) hθ1 hθ2)

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.HkSq_const_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory

namespace Work.FTS.LocData

theorem HkSq_const_mul (α : ℝ) (k : ℕ) (β : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkSq α k (fun z θ => β * f z θ) = β ^ 2 * Work.Spaces.HkSq α k f := by
  have hpoint : ∀ z θ : ℝ,
      Work.Spaces.HkIntegrand α k (fun z θ => β * f z θ) z θ
        = β ^ 2 * Work.Spaces.HkIntegrand α k f z θ :=
    fun z θ => HkIntegrand_const_mul α k β f z θ
  have hinner : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => β * f z θ) z θ)
        = β ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z
    rw [funext (fun θ => hpoint z θ)]
    exact integral_const_mul (β ^ 2)
      (fun θ => Work.Spaces.HkIntegrand α k f z θ)
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  simp only [hinner]
  exact integral_const_mul (β ^ 2)
    (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.Phi_div_deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.LocData

theorem Phi_div_deriv (n : ℕ) (hn : n ≤ 3) {z : ℝ} (hz : z ≠ -1) :
    z * deriv (fun w : ℝ => PhiR n w / (1 + w) ^ (n + 2)) z
      = PhiR (n + 1) z / (1 + z) ^ (n + 3) := by
  have h1 : (1 : ℝ) + z ≠ 0 := by
    intro h
    exact hz (by linarith)
  interval_cases n
  · -- n = 0 :  PhiR 0 w = 2w,  PhiR 1 z = 2z(1-z)
    show z * deriv (fun w : ℝ => PhiR 0 w / (1 + w) ^ 2) z = PhiR 1 z / (1 + z) ^ 3
    have hsub2 : (2 : ℕ) - 1 = 1 := by norm_num
    have hp2 : (1 + z) ^ 2 ≠ 0 := pow_ne_zero 2 h1
    have hnum : HasDerivAt (fun w : ℝ => PhiR 0 w) 2 z := by
      have h0 : HasDerivAt (fun w : ℝ => 2 * w) 2 z :=
        hasDerivAt_const_mul (c := (2 : ℝ)) (x := z)
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ 2) (2 * (1 + z)) z := by
      have h0 : HasDerivAt ((fun w : ℝ => 1 + w) ^ 2) (2 * (1 + z)) z := by
        refine ((((hasDerivAt_id' (x := z)).const_add (1 : ℝ)).pow 2).congr_deriv ?_)
        simp [hsub2]
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hq : HasDerivAt (fun w : ℝ => PhiR 0 w / (1 + w) ^ 2)
        (2 * (1 - z) / (1 + z) ^ 3) z := by
      refine (hnum.fun_div hden (pow_ne_zero 2 h1)).congr_deriv ?_
      simp only [PhiR_zero]
      field_simp [h1, hp2]
      ring
    have hgoal : deriv (fun w : ℝ => PhiR 0 w / (1 + w) ^ 2) z
        = 2 * (1 - z) / (1 + z) ^ 3 := by
      simpa using hq.deriv
    rw [hgoal, PhiR_one]
    ring
  · -- n = 1 :  PhiR 1 w = 2w(1-w),  PhiR 2 z = 2z(1-4z+z²)
    show z * deriv (fun w : ℝ => PhiR 1 w / (1 + w) ^ 3) z = PhiR 2 z / (1 + z) ^ 4
    have hsub3 : (3 : ℕ) - 1 = 2 := by norm_num
    have hp3 : (1 + z) ^ 3 ≠ 0 := pow_ne_zero 3 h1
    have hp32 : ((1 + z) ^ 3) ^ 2 ≠ 0 := pow_ne_zero 2 hp3
    have hnum : HasDerivAt (fun w : ℝ => PhiR 1 w) (2 * (1 - z) + 2 * z * (-1)) z := by
      have ha : HasDerivAt (fun w : ℝ => 2 * w) 2 z :=
        hasDerivAt_const_mul (c := (2 : ℝ)) (x := z)
      have hb : HasDerivAt (fun w : ℝ => 1 - w) (-1) z :=
        (hasDerivAt_id' (x := z)).const_sub (1 : ℝ)
      have h0 : HasDerivAt ((fun w : ℝ => 2 * w) * (fun w : ℝ => 1 - w))
          (2 * (1 - z) + 2 * z * (-1)) z := ha.mul hb
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ 3) (3 * (1 + z) ^ 2) z := by
      have h0 : HasDerivAt ((fun w : ℝ => 1 + w) ^ 3) (3 * (1 + z) ^ 2) z := by
        refine ((((hasDerivAt_id' (x := z)).const_add (1 : ℝ)).pow 3).congr_deriv ?_)
        simp [hsub3]
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hq : HasDerivAt (fun w : ℝ => PhiR 1 w / (1 + w) ^ 3)
        (2 * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4) z := by
      refine (hnum.fun_div hden (pow_ne_zero 3 h1)).congr_deriv ?_
      simp only [PhiR_one]
      field_simp [h1, hp3, hp32]
      ring
    have hgoal : deriv (fun w : ℝ => PhiR 1 w / (1 + w) ^ 3) z
        = 2 * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4 := by
      simpa using hq.deriv
    rw [hgoal, PhiR_two]
    ring
  · -- n = 2 :  PhiR 2 w = 2w(1-4w+w²),  PhiR 3 z = 2z(1-11z+11z²-z³)
    show z * deriv (fun w : ℝ => PhiR 2 w / (1 + w) ^ 4) z = PhiR 3 z / (1 + z) ^ 5
    have hsub2 : (2 : ℕ) - 1 = 1 := by norm_num
    have hsub4 : (4 : ℕ) - 1 = 3 := by norm_num
    have hp4 : (1 + z) ^ 4 ≠ 0 := pow_ne_zero 4 h1
    have hp42 : ((1 + z) ^ 4) ^ 2 ≠ 0 := pow_ne_zero 2 hp4
    have hsq : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
      have h0 : HasDerivAt ((fun x : ℝ => x) ^ 2) (2 * z) z := by
        refine (((hasDerivAt_id' (x := z)).pow 2).congr_deriv ?_)
        simp [hsub2]
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hquad : HasDerivAt (fun w : ℝ => 1 - 4 * w + w ^ 2) (-4 + 2 * z) z := by
      have h4 : HasDerivAt (fun w : ℝ => 4 * w) 4 z :=
        hasDerivAt_const_mul (c := (4 : ℝ)) (x := z)
      have hlin : HasDerivAt (fun w : ℝ => 1 - 4 * w) (0 - 4) z :=
        (hasDerivAt_const (c := (1 : ℝ)) (x := z)).sub h4
      exact (hlin.add hsq).congr_deriv (by ring)
    have ha : HasDerivAt (fun w : ℝ => 2 * w) 2 z :=
      hasDerivAt_const_mul (c := (2 : ℝ)) (x := z)
    have hnum : HasDerivAt (fun w : ℝ => PhiR 2 w)
        (2 * (1 - 4 * z + z ^ 2) + 2 * z * (-4 + 2 * z)) z := by
      have h0 : HasDerivAt ((fun w : ℝ => 2 * w) * (fun w : ℝ => 1 - 4 * w + w ^ 2))
          (2 * (1 - 4 * z + z ^ 2) + 2 * z * (-4 + 2 * z)) z := ha.mul hquad
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ 4) (4 * (1 + z) ^ 3) z := by
      have h0 : HasDerivAt ((fun w : ℝ => 1 + w) ^ 4) (4 * (1 + z) ^ 3) z := by
        refine ((((hasDerivAt_id' (x := z)).const_add (1 : ℝ)).pow 4).congr_deriv ?_)
        simp [hsub4]
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hq : HasDerivAt (fun w : ℝ => PhiR 2 w / (1 + w) ^ 4)
        (2 * (1 - 11 * z + 11 * z ^ 2 - z ^ 3) / (1 + z) ^ 5) z := by
      refine (hnum.fun_div hden (pow_ne_zero 4 h1)).congr_deriv ?_
      simp only [PhiR_two]
      field_simp [h1, hp4, hp42]
      ring
    have hgoal : deriv (fun w : ℝ => PhiR 2 w / (1 + w) ^ 4) z
        = 2 * (1 - 11 * z + 11 * z ^ 2 - z ^ 3) / (1 + z) ^ 5 := by
      simpa using hq.deriv
    rw [hgoal, PhiR_three]
    ring
  · -- n = 3 :  PhiR 3 w = 2w(1-11w+11w²-w³),  PhiR 4 z = 2z(1-26z+66z²-26z³+z⁴)
    show z * deriv (fun w : ℝ => PhiR 3 w / (1 + w) ^ 5) z = PhiR 4 z / (1 + z) ^ 6
    have hsub2 : (2 : ℕ) - 1 = 1 := by norm_num
    have hsub3 : (3 : ℕ) - 1 = 2 := by norm_num
    have hsub5 : (5 : ℕ) - 1 = 4 := by norm_num
    have hp5 : (1 + z) ^ 5 ≠ 0 := pow_ne_zero 5 h1
    have hp52 : ((1 + z) ^ 5) ^ 2 ≠ 0 := pow_ne_zero 2 hp5
    have hsq : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
      have h0 : HasDerivAt ((fun x : ℝ => x) ^ 2) (2 * z) z := by
        refine (((hasDerivAt_id' (x := z)).pow 2).congr_deriv ?_)
        simp [hsub2]
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hcu : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ 2) z := by
      have h0 : HasDerivAt ((fun x : ℝ => x) ^ 3) (3 * z ^ 2) z := by
        refine (((hasDerivAt_id' (x := z)).pow 3).congr_deriv ?_)
        simp [hsub3]
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hcub : HasDerivAt (fun w : ℝ => 1 - 11 * w + 11 * w ^ 2 - w ^ 3)
        (-11 + 22 * z - 3 * z ^ 2) z := by
      have h11 : HasDerivAt (fun w : ℝ => 11 * w) 11 z :=
        hasDerivAt_const_mul (c := (11 : ℝ)) (x := z)
      have h11sq : HasDerivAt (fun w : ℝ => 11 * w ^ 2) (11 * (2 * z)) z :=
        hsq.const_mul (11 : ℝ)
      have hlin : HasDerivAt (fun w : ℝ => 1 - 11 * w) (0 - 11) z :=
        (hasDerivAt_const (c := (1 : ℝ)) (x := z)).sub h11
      exact ((hlin.add h11sq).sub hcu).congr_deriv (by ring)
    have ha : HasDerivAt (fun w : ℝ => 2 * w) 2 z :=
      hasDerivAt_const_mul (c := (2 : ℝ)) (x := z)
    have hnum : HasDerivAt (fun w : ℝ => PhiR 3 w)
        (2 * (1 - 11 * z + 11 * z ^ 2 - z ^ 3) + 2 * z * (-11 + 22 * z - 3 * z ^ 2)) z := by
      have h0 : HasDerivAt ((fun w : ℝ => 2 * w) * (fun w : ℝ => 1 - 11 * w + 11 * w ^ 2 - w ^ 3))
          (2 * (1 - 11 * z + 11 * z ^ 2 - z ^ 3) + 2 * z * (-11 + 22 * z - 3 * z ^ 2)) z :=
        ha.mul hcub
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ 5) (5 * (1 + z) ^ 4) z := by
      have h0 : HasDerivAt ((fun w : ℝ => 1 + w) ^ 5) (5 * (1 + z) ^ 4) z := by
        refine ((((hasDerivAt_id' (x := z)).const_add (1 : ℝ)).pow 5).congr_deriv ?_)
        simp [hsub5]
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hq : HasDerivAt (fun w : ℝ => PhiR 3 w / (1 + w) ^ 5)
        (2 * (1 - 26 * z + 66 * z ^ 2 - 26 * z ^ 3 + z ^ 4) / (1 + z) ^ 6) z := by
      refine (hnum.fun_div hden (pow_ne_zero 5 h1)).congr_deriv ?_
      simp only [PhiR_three]
      field_simp [h1, hp5, hp52]
      ring
    have hgoal : deriv (fun w : ℝ => PhiR 3 w / (1 + w) ^ 5) z
        = 2 * (1 - 26 * z + 66 * z ^ 2 - 26 * z ^ 3 + z ^ 4) / (1 + z) ^ 6 := by
      simpa using hq.deriv
    rw [hgoal, PhiR_four]
    ring

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.Phi_w_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

/-- **Conversion step.**  A bound `|PhiR i z| ≤ 2z(1+z)^i` for `z ≥ 1` gives the weighted
bound `|w z · Phi i z θ| ≤ 2/z`: indeed `w z · Phi i z θ = PhiR i z /(z²(1+z)^i)` and the
denominator is positive. -/
theorem Phi_w_le_of_abs_PhiR (i : ℕ) {z : ℝ} (hz1 : 1 ≤ z) (θ : ℝ)
    (h : |PhiR i z| ≤ 2 * z * (1 + z) ^ i) :
    |Work.Spaces.w z * Phi i z θ| ≤ 2 / z := by
  have hz : 0 < z := lt_of_lt_of_le one_pos hz1
  have hden : 0 < z ^ 2 * (1 + z) ^ i := by positivity
  have hkey : Work.Spaces.w z * Phi i z θ = PhiR i z / (z ^ 2 * (1 + z) ^ i) := by
    simp only [Work.Spaces.w, Phi]
    field_simp
    ring
  rw [hkey, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have h2 : 2 / z * (z ^ 2 * (1 + z) ^ i) = 2 * z * (1 + z) ^ i := by field_simp
  rw [h2]
  exact h

theorem Phi_w_le (i : ℕ) (hi : i ≤ 4) {z : ℝ} (hz1 : 1 ≤ z) (θ : ℝ) :
    |Work.Spaces.w z * Phi i z θ| ≤ 2 / z := by
  refine Phi_w_le_of_abs_PhiR i hz1 θ ?_
  interval_cases i
  · simp only [PhiR_zero, pow_zero, mul_one]
    rw [abs_of_pos (by linarith : (0 : ℝ) < 2 * z)]
  · simp only [PhiR_one, pow_one]
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * z),
      abs_of_nonpos (by linarith : 1 - z ≤ 0)]
    nlinarith [hz1]
  · simp only [PhiR_two]
    have habs : |1 - 4 * z + z ^ 2| ≤ (1 + z) ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (z - 1 / 2), hz1]
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * z)]
    exact mul_le_mul_of_nonneg_left habs (by linarith : (0 : ℝ) ≤ 2 * z)
  · simp only [PhiR_three]
    have habs : |1 - 11 * z + 11 * z ^ 2 - z ^ 3| ≤ (1 + z) ^ 3 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (z - 2), sq_nonneg (z - 2 / 7), hz1]
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * z)]
    exact mul_le_mul_of_nonneg_left habs (by linarith : (0 : ℝ) ≤ 2 * z)
  · simp only [PhiR_four]
    have habs : |1 - 26 * z + 66 * z ^ 2 - 26 * z ^ 3 + z ^ 4| ≤ (1 + z) ^ 4 := by
      rw [abs_le]
      constructor <;>
        nlinarith [sq_nonneg (z - 1), sq_nonneg (z ^ 2 - 11 / 2 * z + 1), sq_nonneg z, hz1]
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * z)]
    exact mul_le_mul_of_nonneg_left habs (by linarith : (0 : ℝ) ≤ 2 * z)

end Work.FTS.LocData
end
-- ===== merged: Submission.Work.FTS.LocData.SmoothQuad_Fstar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

/-- The reference profile `F_*` is `C^∞` on the open quadrant (no hypothesis on `α`). -/
theorem SmoothQuad_Fstar (α : ℝ) : SmoothQuad (Work.Construction.Fstar α) :=
  Fstar_smoothQuad α

end Work.FTS.LocData
end
-- ===== merged: Submission.Work.FTS.LocData.SmoothQuad_hLoc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The two factors of `hLoc` -/

/-- The radial factor `bumpZ z = χ(4z - 5)` of the bump is `C^∞` on `ℝ` (at the genuine smooth
order `Work.Stability.smoothOrder`). -/
theorem contDiff_bumpZ : ContDiff ℝ Work.Stability.smoothOrder bumpZ := by
  unfold bumpZ
  exact Work.Stability.chi_contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

/-- The angular factor `Γ(θ) = (sinθ·cos²θ)^{α/3}` of the bump and of the profile `F_*` is `C^∞`
on the open interval `(0, π/2)`: there the base `sinθ·cos²θ` is positive, so the real power is a
composite of `exp` and `log` and loses no smoothness. -/
theorem contDiffOn_Gam_Ioo (α : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Work.Spaces.Gam α) (Set.Ioo 0 (π / 2)) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) (Set.Ioo 0 (π / 2)) :=
    ((Real.contDiff_sin (n := Work.Stability.smoothOrder)).mul
      ((Real.contDiff_cos (n := Work.Stability.smoothOrder)).pow 2)).contDiffOn
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ => α / 3)
      (Set.Ioo 0 (π / 2)) := contDiffOn_const
  have hne : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 2), Real.sin x * Real.cos x ^ 2 ≠ 0 := by
    intro x hx
    have hs : 0 < Real.sin x :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos])
    have hc : 0 < Real.cos x :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
    positivity
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun x : ℝ => (Real.sin x * Real.cos x ^ 2) ^ (α / 3)) (Set.Ioo 0 (π / 2)) :=
    ContDiffOn.rpow h1 h2 hne
  exact h3.congr (fun x _ => rfl)

/-! ## Functions of a single variable are `SmoothQuad` -/

/-- A function of `z` alone is `SmoothQuad` as soon as its slice is `C^∞` on `ℝ`. -/
theorem smoothQuad_of_fst {f : ℝ → ℝ} (hf : ContDiff ℝ Work.Stability.smoothOrder f) :
    SmoothQuad (fun z _ => f z) := by
  rw [SmoothQuad]
  exact hf.contDiffOn.comp contDiffOn_fst (fun _ _ => Set.mem_univ _)

/-- A function of `θ` alone is `SmoothQuad` as soon as its slice is `C^∞` on `(0, π/2)`. -/
theorem smoothQuad_of_snd {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder f (Set.Ioo 0 (π / 2))) :
    SmoothQuad (fun _ θ => f θ) := by
  rw [SmoothQuad]
  exact hf.comp contDiffOn_snd (fun _ hp => hp.2)

/-! ## The bump -/

theorem SmoothQuad_hLoc (α : ℝ) : SmoothQuad (hLoc α) :=
  smoothQuad_mul (smoothQuad_of_fst contDiff_bumpZ)
    (smoothQuad_of_snd (contDiffOn_Gam_Ioo α))

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.c_ge_three_fifths =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The lower bound `3/5 ≤ c(α)`

The normalisation constant of Elgindi's paper is
`c(α) = ∫_{[0,π/2]} Γ(θ)K(θ) dθ` with `Γ(θ) = (sin θ cos²θ)^{α/3}` and
`K(θ) = 3 sin θ cos²θ`; only the range `1/10 ≤ c(α) ≤ 10` is needed in the paper
(`Work.Spaces.c_bounds`), but the localisation data used in this development
needs the sharper lower bound `3/5 ≤ c(α)` for `0 < α ≤ 1`.

On `Iθ` the integrand is `Γ(θ)K(θ) = 3 s^{1+α/3}` with `s = sin θ cos²θ ∈ [0,1]`.
Since `α ≤ 1` gives `1 + α/3 ≤ 4/3` and `s ≤ 1`,
`s^{1+α/3} ≥ s^{4/3} ≥ s - √s/5` (`Work.FTS.LocData.rpow_one_add_ge_sub_sqrt`,
whose content is that `sup_{v∈[0,1]} v³(1-v²) = 6√3/(25√5) ≈ 0.186 < 1/5`).
Integrating and using the two elementary integrals
`∫_{Iθ} s dθ = 1/3` and `∫_{Iθ} √s dθ = 2/3` gives

`c(α) ≥ 3(1/3 - (1/5)(2/3)) = 3/5`.

(The sharp value is `c(1) = 3 ∫_0^{π/2} (sin θ cos²θ)^{4/3} dθ ≈ 0.6545`.)
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

/-- The elementary angular integral `∫_{[0,π/2]} sin θ cos²θ dθ = 1/3`.

This is Mathlib's `integral_sin_mul_cos_sq` transported from the interval
`0..π/2` to the set `Work.Spaces.Iθ = Set.Icc 0 (π/2)`. -/
theorem integral_sin_mul_cos_sq_Iθ :
    ∫ θ in Work.Spaces.Iθ, Real.sin θ * Real.cos θ ^ 2 = 1 / 3 := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2),
      integral_sin_mul_cos_sq]
  norm_num [Real.cos_zero, Real.cos_pi_div_two]

theorem c_ge_three_fifths (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (3 : ℝ)/5 ≤ Work.Spaces.c α := by
  -- `s = sin θ cos²θ ∈ [0,1]` on `Iθ`.
  have hsq_nonneg : ∀ θ ∈ Work.Spaces.Iθ, (0 : ℝ) ≤ Real.sin θ * Real.cos θ ^ 2 := by
    intro θ hθ
    have hs : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    positivity
  have hsq_le_one : ∀ θ ∈ Work.Spaces.Iθ, Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
    intro θ hθ
    have hs : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hc : Real.cos θ ^ 2 ≤ 1 := by
      have h := sq_le_sq' (Real.neg_one_le_cos θ) (Real.cos_le_one θ)
      simpa using h
    have hc0 : (0 : ℝ) ≤ Real.cos θ ^ 2 := by positivity
    simpa using mul_le_mul hs hc hc0 (by norm_num : (0 : ℝ) ≤ 1)
  -- Integrability of the two pieces of the comparison function.
  have hcont_s : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
  have hcont_sqrt :
      ContinuousOn (fun θ : ℝ => Real.sqrt (Real.sin θ * Real.cos θ ^ 2)) Work.Spaces.Iθ :=
    hcont_s.sqrt
  have hsqrt_int :
      IntegrableOn (fun θ : ℝ => Real.sqrt (Real.sin θ * Real.cos θ ^ 2)) Work.Spaces.Iθ :=
    hcont_sqrt.integrableOn_Icc
  have hK_int : IntegrableOn (fun θ : ℝ => Work.Spaces.K θ) Work.Spaces.Iθ := by
    refine ContinuousOn.integrableOn_Icc ?_
    simp only [Work.Spaces.K]
    fun_prop
  have hlb_int : IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ - (3/5) * Real.sqrt (Real.sin θ * Real.cos θ ^ 2))
      Work.Spaces.Iθ :=
    hK_int.sub (hsqrt_int.const_mul (3/5))
  -- The pointwise comparison `K θ - (3/5)√s ≤ Γ(θ)K(θ)` on `Iθ`.
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.K θ - (3/5) * Real.sqrt (Real.sin θ * Real.cos θ ^ 2)
        ≤ Work.Spaces.Gam α θ * Work.Spaces.K θ := by
    intro θ hθ
    have hA := rpow_one_add_ge_sub_sqrt (Real.sin θ * Real.cos θ ^ 2)
      (hsq_nonneg θ hθ) (hsq_le_one θ hθ) α hα hα1
    -- `Γ(θ)K(θ) = 3 s^{1+α/3}`
    have hident : Work.Spaces.Gam α θ * Work.Spaces.K θ
        = 3 * (Real.sin θ * Real.cos θ ^ 2) ^ (1 + α / 3) := by
      have h1 : (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) * (Real.sin θ * Real.cos θ ^ 2)
          = (Real.sin θ * Real.cos θ ^ 2) ^ (1 + α / 3) := by
        rw [Real.rpow_add' (hsq_nonneg θ hθ) (by positivity : 1 + α / 3 ≠ 0), Real.rpow_one]
        ring
      rw [Work.Spaces.Gam, Work.Spaces.K]
      calc (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) * (3 * Real.sin θ * Real.cos θ ^ 2)
          = 3 * ((Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)
              * (Real.sin θ * Real.cos θ ^ 2)) := by ring
        _ = 3 * (Real.sin θ * Real.cos θ ^ 2) ^ (1 + α / 3) := by rw [h1]
    have hkey : 3 * (Real.sin θ * Real.cos θ ^ 2
        - Real.sqrt (Real.sin θ * Real.cos θ ^ 2) / 5)
        ≤ 3 * (Real.sin θ * Real.cos θ ^ 2) ^ (1 + α / 3) :=
      mul_le_mul_of_nonneg_left hA (by norm_num)
    have hrew : Work.Spaces.K θ - (3/5) * Real.sqrt (Real.sin θ * Real.cos θ ^ 2)
        = 3 * (Real.sin θ * Real.cos θ ^ 2
            - Real.sqrt (Real.sin θ * Real.cos θ ^ 2) / 5) := by
      rw [Work.Spaces.K]; ring
    rw [hrew, hident]
    exact hkey
  have hmono := MeasureTheory.setIntegral_mono_on hlb_int
    (Work.Spaces.CAux.integrableOn_GamK α hα) measurableSet_Icc hpt
  -- The two integrals.
  have hKval : ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ = 1 := by
    have hK_eq : (fun θ : ℝ => Work.Spaces.K θ)
        = fun θ : ℝ => 3 * (Real.sin θ * Real.cos θ ^ 2) := by
      funext θ; rw [Work.Spaces.K]; ring
    rw [hK_eq, MeasureTheory.integral_const_mul, integral_sin_mul_cos_sq_Iθ]
    norm_num
  have hsqrtval : ∫ θ in Work.Spaces.Iθ,
      (3/5) * Real.sqrt (Real.sin θ * Real.cos θ ^ 2) = 2/5 := by
    rw [MeasureTheory.integral_const_mul, integral_sqrt_sin_mul_cos_sq]
    norm_num
  have hval : ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.K θ - (3/5) * Real.sqrt (Real.sin θ * Real.cos θ ^ 2)) = 3/5 := by
    rw [MeasureTheory.integral_sub hK_int (hsqrt_int.const_mul (3/5)), hKval, hsqrtval]
    norm_num
  calc (3 : ℝ)/5 = ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.K θ - (3/5) * Real.sqrt (Real.sin θ * Real.cos θ ^ 2)) := hval.symm
    _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ := hmono
    _ = Work.Spaces.c α := rfl

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.integrableOn_L12dens_zfar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-- **The `L₁₂`-density of the far part is integrable on `(0,∞)`.**  On `(0,∞)` it is the
explicit elementary function `s ↦ (1 - χ(s/L))·α·2/(1+s)²`, the product of the bounded factor
`1 - χ(s/L) ∈ [0,1]` with the integrable function `α·2/(1+s)²`; domination by an integrable
function gives the result. -/
theorem integrableOn_L12dens_zfar (α L : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) :
    MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (Work.Stability.zfar L (Work.Construction.Fstar α)))
      (Set.Ioi (0 : ℝ)) := by
  have hLpos : (0 : ℝ) < L := by linarith
  -- On `(0,∞)` the density is the elementary function `(1 - χ(s/L))·α·2/(1+s)²`.
  have hpt : ∀ s ∈ Set.Ioi (0 : ℝ),
      Work.FM.L12dens Work.Spaces.K (Work.Stability.zfar L (Work.Construction.Fstar α)) s
        = (1 - Work.Stability.chi (s / L)) * (α * (2 * (s + 1) ^ (-2 : ℝ))) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hs1 : (0 : ℝ) < s + 1 := by linarith
    have hFdiv : Work.FM.Fstar s / s = 2 * (s + 1) ^ (-2 : ℝ) := by
      have h2 : (s + 1) ^ (-2 : ℝ) = 1 / (s + 1) ^ 2 := by
        simp only [Real.rpow_neg (le_of_lt hs1), Real.rpow_ofNat, one_div]
      rw [h2]
      unfold Work.FM.Fstar
      field_simp
      ring
    rw [L12dens_zfar_Fstar, Work.Construction.L12dens_Fstar hα hα1 s, hFdiv]
  -- The dominating function `s ↦ α·2/(1+s)²` is integrable on `(0,∞)`.
  have hbase : MeasureTheory.IntegrableOn (fun s : ℝ => α * (2 * (s + 1) ^ (-2 : ℝ)))
      (Set.Ioi (0 : ℝ)) := by
    have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => (s + 1) ^ (-2 : ℝ))
        (Set.Ioi (0 : ℝ)) :=
      integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (by norm_num) (by norm_num)
    have h2 : MeasureTheory.IntegrableOn (fun s : ℝ => (2 * α) * (s + 1) ^ (-2 : ℝ))
        (Set.Ioi (0 : ℝ)) := h1.const_mul (2 * α)
    refine MeasureTheory.IntegrableOn.congr_fun h2 (fun s _ => by ring) measurableSet_Ioi
  -- Bounded measurable factor times integrable function.
  have hexp : MeasureTheory.IntegrableOn
      (fun s : ℝ => (1 - Work.Stability.chi (s / L)) * (α * (2 * (s + 1) ^ (-2 : ℝ))))
      (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.Integrable.bdd_mul (c := 1) hbase ?_ ?_
    · exact (continuous_const.sub
        (Work.Stability.chi_continuous.comp (continuous_id.div_const L))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun s => ?_)
      rw [Real.norm_eq_abs]
      have h1 : Work.Stability.chi (s / L) ≤ 1 := Work.Stability.chi_le_one _
      have h2 : 0 ≤ Work.Stability.chi (s / L) := Work.Stability.chi_nonneg _
      rw [abs_of_nonneg (by linarith)]
      linarith
  exact MeasureTheory.IntegrableOn.congr_fun hexp (fun s hs => (hpt s hs).symm) measurableSet_Ioi

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.integrableOn_bumpZ_div =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

theorem integrableOn_bumpZ_div :
    MeasureTheory.IntegrableOn (fun s : ℝ => Work.FTS.LocData.bumpZ s / s) (Set.Ioi (0 : ℝ)) := by
  -- The function is continuous on the compact support interval.
  have hK : MeasureTheory.IntegrableOn (fun s : ℝ => Work.FTS.LocData.bumpZ s / s)
      (Set.Icc (3 / 4 : ℝ) (7 / 4)) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine (BumpZ_contDiff.continuous.continuousOn).div continuous_id.continuousOn ?_
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx.1
    exact ne_of_gt hx0
  have hmeas : MeasurableSet (Set.Icc (3 / 4 : ℝ) (7 / 4)) := measurableSet_Icc
  -- Its indicator is integrable for `volume` (compact support), hence on `Ioi 0`.
  have hind : MeasureTheory.Integrable
      ((Set.Icc (3 / 4 : ℝ) (7 / 4)).indicator
        (fun s : ℝ => Work.FTS.LocData.bumpZ s / s)) MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff hmeas).mpr hK
  have h2 : MeasureTheory.IntegrableOn
      ((Set.Icc (3 / 4 : ℝ) (7 / 4)).indicator
        (fun s : ℝ => Work.FTS.LocData.bumpZ s / s)) (Set.Ioi (0 : ℝ)) :=
    hind.integrableOn
  -- On `Ioi 0` the indicator agrees with the function itself, since `bumpZ` vanishes off `K`.
  refine MeasureTheory.IntegrableOn.congr_fun h2 (fun x _ => ?_) measurableSet_Ioi
  by_cases hxK : x ∈ Set.Icc (3 / 4 : ℝ) (7 / 4)
  · rw [Set.indicator_of_mem hxK]
  · rw [Set.indicator_of_notMem hxK, bumpZ_eq_zero_of_notMem_Icc x hxK, zero_div]

end Work.FTS.LocData
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PggAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `PggAux` — the elementary ingredients of the `gg`-row estimate

This module collects the parts of the proof of `Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgg`
that do not use the nonlinearity: elementary properties of the radial weight
`w = (1+z)²/z²`, the fact that `θ ∈ (0,π/2)` holds a.e. on `Iθ`, and the three *slot*
bounds `w·(D_z^j D_θ^i G)² ≤ HkIntegrand α 4 G` for `(j,i) = (0,0), (0,1), (1,0)` (in
pointwise-interior and a.e. form).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces

set_option autoImplicit false

/-! ## The weight `w` -/

theorem w_nonneg_aux (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

theorem one_le_w_aux {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg z, hz]


/-- `θ ∈ (0,π/2)` is an a.e. statement on `Iθ`. -/
theorem ae_mem_Ioo_Iθ_aux :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hset : (Set.Ioo (0 : ℝ) (Real.pi / 2)) =ᵐ[MeasureTheory.volume] Work.Spaces.Iθ :=
    MeasureTheory.Ioo_ae_eq_Icc
  have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := MeasureTheory.ae_restrict_mem measurableSet_Ioo
  rw [MeasureTheory.Measure.restrict_congr_set hset] at h1
  exact h1

theorem sin_two_pos_aux {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) := by
  have h2 : (2 : ℝ) * θ ∈ Set.Ioo 0 Real.pi :=
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  exact Real.sin_pos_of_pos_of_lt_pi h2.1 h2.2

theorem sin_two_le_one_aux (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

/-- `w z ≤ (w z / sin(2θ)^{η/2})²` for `z > 0`, `θ ∈ (0,π/2)`. -/
theorem w_le_div_rpow_sq {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.w z ≤ (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 := by
  have hs0 : 0 < Real.sin (2 * θ) := sin_two_pos_aux hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := sin_two_le_one_aux θ
  have hη : (0 : ℝ) ≤ Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  have hsη : Real.sin (2 * θ) ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs0) hs1 hη
  have hden : (0 : ℝ) < Real.sin (2 * θ) ^ Work.Spaces.eta := Real.rpow_pos_of_pos hs0 _
  have hsq2 : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = Real.sin (2 * θ) ^ Work.Spaces.eta := by
    rw [sq, ← Real.rpow_add hs0]
    congr 1
    ring
  rw [div_pow, hsq2, le_div_iff₀ hden]
  calc Work.Spaces.w z * Real.sin (2 * θ) ^ Work.Spaces.eta
      ≤ Work.Spaces.w z * 1 := mul_le_mul_of_nonneg_left hsη (w_nonneg_aux z)
    _ = Work.Spaces.w z := mul_one _
    _ ≤ Work.Spaces.w z * Work.Spaces.w z :=
        le_mul_of_one_le_left (w_nonneg_aux z) (one_le_w_aux hz)
    _ = Work.Spaces.w z ^ 2 := (sq _).symm

/-- `w z ≤ Wt α z θ ^ 2` for `0 ≤ α`, `z > 0`, `θ ∈ (0,π/2)`. -/
theorem w_le_Wt_sq (α : ℝ) (hα : 0 ≤ α) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.w z ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
  have hs0 : 0 < Real.sin (2 * θ) := sin_two_pos_aux hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := sin_two_le_one_aux θ
  have hγ : (0 : ℝ) ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hth : 1 ≤ Work.Spaces.wTheta α θ := by
    rw [Work.Spaces.wTheta]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs0 hs1 (by linarith)
  have hth2 : 1 ≤ (Work.Spaces.wTheta α θ) ^ 2 := by nlinarith [hth]
  have h1 : Work.Spaces.w z ≤ (Work.Spaces.w z) ^ 2 := by
    rw [sq]
    exact le_mul_of_one_le_left (w_nonneg_aux z) (one_le_w_aux hz)
  have h2 : (Work.Spaces.w z) ^ 2 ≤ (Work.Spaces.w z) ^ 2 * (Work.Spaces.wTheta α θ) ^ 2 :=
    le_mul_of_one_le_right (by positivity) hth2
  rw [Work.Spaces.Wt, mul_pow]
  exact le_trans h1 h2

/-! ## The three slot bounds -/

theorem w_mul_sq_le_HkIntegrand_self (α : ℝ) {G : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.w z * (G z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 G z θ := by
  have h1 : Work.Spaces.w z * (G z θ) ^ 2
      ≤ (G z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    calc Work.Spaces.w z * (G z θ) ^ 2
        ≤ (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 * (G z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (w_le_div_rpow_sq hz hθ) (sq_nonneg _)
      _ = (G z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
  refine le_trans h1 ?_
  simpa only [Work.Spaces.DzIter_zero] using
    Work.Spaces.sq_le_HkIntegrand_z α 4 G z θ 0 (by norm_num)

theorem w_mul_sq_le_HkIntegrand_Dth (α : ℝ) (hα : 0 ≤ α) {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.w z * (Work.Spaces.Dth G z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 G z θ := by
  have h1 : Work.Spaces.w z * (Work.Spaces.Dth G z θ) ^ 2
      ≤ (Work.Spaces.Dth G z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    calc Work.Spaces.w z * (Work.Spaces.Dth G z θ) ^ 2
        ≤ (Work.Spaces.Wt α z θ) ^ 2 * (Work.Spaces.Dth G z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (w_le_Wt_sq α hα hz hθ) (sq_nonneg _)
      _ = (Work.Spaces.Dth G z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
  refine le_trans h1 ?_
  simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
    using Work.Spaces.sq_le_HkIntegrand_mixed α 4 G z θ 1 0 le_rfl (by norm_num)

theorem w_mul_sq_le_HkIntegrand_Dz (α : ℝ) {G : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.w z * (Work.Spaces.Dz G z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 G z θ := by
  have h1 : Work.Spaces.w z * (Work.Spaces.Dz G z θ) ^ 2
      ≤ (Work.Spaces.Dz G z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    calc Work.Spaces.w z * (Work.Spaces.Dz G z θ) ^ 2
        ≤ (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
            * (Work.Spaces.Dz G z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (w_le_div_rpow_sq hz hθ) (sq_nonneg _)
      _ = (Work.Spaces.Dz G z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
  refine le_trans h1 ?_
  simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
    Work.Spaces.sq_le_HkIntegrand_z α 4 G z θ 1 (by norm_num)

/-! ## The a.e.-in-`θ` forms -/

theorem ae_w_mul_sq_self_le_HkIntegrand (α : ℝ) {G : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w z * (G z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 G z θ := by
  filter_upwards [ae_mem_Ioo_Iθ_aux] with θ hθ
  exact w_mul_sq_le_HkIntegrand_self α hz hθ

theorem ae_w_mul_sq_Dth_le_HkIntegrand (α : ℝ) (hα : 0 ≤ α) {G : ℝ → ℝ → ℝ} {z : ℝ}
    (hz : 0 < z) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w z * (Work.Spaces.Dth G z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 G z θ := by
  filter_upwards [ae_mem_Ioo_Iθ_aux] with θ hθ
  exact w_mul_sq_le_HkIntegrand_Dth α hα hz hθ

theorem ae_w_mul_sq_Dz_le_HkIntegrand (α : ℝ) {G : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w z * (Work.Spaces.Dz G z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 G z θ := by
  filter_upwards [ae_mem_Ioo_Iθ_aux] with θ hθ
  exact w_mul_sq_le_HkIntegrand_Dz α hz hθ

/-! ## Continuity and a.e.-measurability of the slots of a `SmoothQuad` function -/

theorem quad_subset : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
    ⊆ (Set.Ioi (-1) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num)) (le_refl _)

theorem contOn_uncurry_of_smoothQuad {G : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad G) :
    ContinuousOn (Function.uncurry G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  (h.mono quad_subset).continuousOn

theorem contOn_uncurry_Dth_of_smoothQuad {G : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad G) :
    ContinuousOn (Function.uncurry (Work.Spaces.Dth G))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  ((Work.FTS.LocData.contDiffOn_Dth Work.FTS.LocData.isOpen_quadU h).mono quad_subset).continuousOn

theorem contOn_uncurry_Dz_of_smoothQuad {G : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad G) :
    ContinuousOn (Function.uncurry (Work.Spaces.Dz G))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  ((Work.FTS.LocData.contDiffOn_Dz Work.FTS.LocData.isOpen_quadU h).mono quad_subset).continuousOn

theorem aesm_uncurry_of_smoothQuad {G : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad G) :
    MeasureTheory.AEStronglyMeasurable (Function.uncurry G)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ (contOn_uncurry_of_smoothQuad h)

theorem aesm_uncurry_Dth_of_smoothQuad {G : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad G) :
    MeasureTheory.AEStronglyMeasurable (Function.uncurry (Work.Spaces.Dth G))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ (contOn_uncurry_Dth_of_smoothQuad h)

theorem aesm_uncurry_Dz_of_smoothQuad {G : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad G) :
    MeasureTheory.AEStronglyMeasurable (Function.uncurry (Work.Spaces.Dz G))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ (contOn_uncurry_Dz_of_smoothQuad h)

theorem aesm_slice_of_smoothQuad {G : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad G) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable (fun θ => G z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _ (contOn_uncurry_of_smoothQuad h) hz

theorem aesm_slice_Dth_of_smoothQuad {G : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad G)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.Dth G z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _ (contOn_uncurry_Dth_of_smoothQuad h) hz

theorem aesm_slice_Dz_of_smoothQuad {G : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad G)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.Dz G z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _ (contOn_uncurry_Dz_of_smoothQuad h) hz

end Work.FTS.Nonlinear.Pieces.rl1Pieces
end
end
-- ===== merged: Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
# `HkMem` is monotone in the order `k`, in the *interior* smoothness class

`Work.Spaces.HkMem α k f` says that the `ℋ^k`-integrand of `f` has honest iterated integrals
over the domain `Iz ×ˢ Iθ = [0,∞) × [0,π/2]` with the measure `dz dθ`:

* every angular slice `θ ↦ HkIntegrand α k f z θ` is integrable on `Iθ` (for `z ∈ Iz`), and
* `z ↦ ∫_θ HkIntegrand α k f z θ` is integrable on `Iz`.

`HkIntegrand α (k+1) f` is obtained from `HkIntegrand α k f` by *adding* finitely many further
summands, each of them a square of a weighted derivative of `f`
(`Work.Spaces.HkIntegrand_mono`).  Hence the `(k+1)`-integrand *dominates* the `k`-integrand
pointwise and admits as its own `θ`-slices and slice-integral exactly the two integrability
certificates contained in `Work.Spaces.HkMem α (k+1) f`.

The only extra input needed is the a.e. strong measurability of the *smaller* integrand (a
function dominated by an integrable function need not be integrable without it).  This is where
smoothness enters: for `f` of class `Work.FTS.LocData.SmoothQuad` (genuine `C^∞` on the open
quadrant `z > -1`, `0 < θ < π/2` — the class preserved by the cut-off of the route, *not* the
analytic class `Work.Spaces.SmoothNbhd`), the integrand is `ContinuousOn` on the open quadrant
(`Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad`); the closed quadrant differs from the
open one by null sets, and on the single slice `z = 0` the integrand vanishes identically since
the radial weight `w 0 = 0`.  So the domination machinery
`Work.FTS.LocData.HkMem_of_majorant` applies verbatim, with the majorant `M` being the
`(k+1)`-integrand itself.

This is the `SmoothQuad` replacement of `Work.Coercivity.HkMem_mono`, whose measurability input
is stated for the (strictly stronger, cut-off-incompatible) analytic class `Spaces.SmoothNbhd`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.GalerkinFix.RegQ

/-- **`HkMem` is monotone in the order, in the interior class.**  If `f` is `C^∞` on the open
quadrant and its `ℋ^{k+1}`-integrand has honest iterated integrals, then so does its
`ℋ^k`-integrand. -/
theorem HkMem_mono_Q {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) (h : Work.Spaces.HkMem α (k + 1) f) :
    Work.Spaces.HkMem α k f :=
  Work.FTS.LocData.HkMem_of_majorant α k
    (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α k f hf)
    h.1 h.2
    (fun z _ θ _ => Work.Spaces.HkIntegrand_mono α k f z θ)

end Work.GalerkinFix.RegQ
end
end
