import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.StrongEps.E5Aux3.contDiffOn_two_of_jetLim
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.tower_jet_identities
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2W.asliceMomentEq
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.fderiv_uncurry_mixed_eq_clmPair =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

set_option autoImplicit false

/-- The `D_z`-slot is `z` times the plain `z`-derivative of the slot: this is the definitional
identity `mixed (j+1) i u = Dz (mixed j i u)`. -/
theorem mixed_succ_left_eq (u : ℝ → ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed (j + 1) i u z θ
      = z * Work.Spaces.pz (Work.Spaces.mixed j i u) z θ := rfl

/-- **The Fréchet derivative of an uncurried mixed slot.**  On the open quadrant, for
`u ∈ C^∞`, the derivative of `p ↦ D_z^j D_θ^i u (p.1, p.2)` is the pair of the next slots,
divided by the factors `z` resp. `sin(2θ)` carried by the operators `D_z`, `D_θ`. -/
theorem fderiv_uncurry_mixed_eq_clmPair {u : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen u)
    (j i : ℕ) {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    fderiv ℝ (Function.uncurry (Work.Spaces.mixed j i u)) p
      = Work.FTS.StrongEps.E5Aux.clmPair
          (Work.Spaces.mixed (j + 1) i u p.1 p.2 / p.1,
           Work.Spaces.mixed j (i + 1) u p.1 p.2 / Real.sin (2 * p.2)) := by
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have hdiff : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.mixed j i u)) p :=
    (((hsm.mixed j i).forall 2).differentiableOn (by norm_num)).differentiableAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
  rw [Work.FTS.StrongEps.E5Aux.fderiv_uncurry_eq_clmPair hdiff]
  have hpz : Work.Spaces.pz (Work.Spaces.mixed j i u) p.1 p.2
      = Work.Spaces.mixed (j + 1) i u p.1 p.2 / p.1 := by
    have h : Work.Spaces.mixed (j + 1) i u p.1 p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.mixed j i u) p.1 p.2 :=
      mixed_succ_left_eq u j i p.1 p.2
    rw [h, mul_div_cancel_left₀ _ (ne_of_gt hz)]
  have hpth : Work.Spaces.pth (Work.Spaces.mixed j i u) p.1 p.2
      = Work.Spaces.mixed j (i + 1) u p.1 p.2 / Real.sin (2 * p.2) :=
    Work.FTS.StrongEps.E5Aux3.pth_mixed_eq hsm j i p hp
  rw [hpz, hpth]

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.PhiAEStronglyMeasurable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# A.e. strong measurability of the parametric integral `Phi`

The function

  `x = (θ, p₂) ↦ ∫ p₁, ∂₁^m (Jker ρ ε) (p₁, p₂) · W (e^{s - p₁}) (thShift θ p₂)`

is a.e. strongly measurable for the measure
`(volume.restrict Iθ).prod (volume.restrict [-ε,ε])`.

The proof separates the integrand into the product of two factors:

* the kernel factor `q ↦ ∂₁^m (Jker ρ ε) (q.1, q.2.2)` is *continuous*: the kernel is `C^∞` on
  the whole plane (`Jker_smooth`, from the smoothness of `ρ`), and
  `contDiffOn_uncurry_pzIter_le` turns the iterated `∂₁`-derivative of a smooth function into a
  continuous function of both variables;
* the profile factor `q ↦ W (e^{s-q.1}) (thShift q.2.1 q.2.2)` is continuous *on the set*
  `S = {q | q.2.1 ∈ (0, π/2)}`: there `thShift` is continuous (away from the poles of `tan`) and
  the shifted point `(e^{s-q.1}, thShift q.2.1 q.2.2)` lies in the open quadrant `Q0`, where `W`
  is smooth.  The set `S` is conull for `volume.prod ((volume.restrict Iθ).prod ...)` — its
  complement only involves the two endpoints `0, π/2` of `Iθ`, a null set — so the behaviour of
  `W` off the quadrant is irrelevant.

Both factors are a.e. strongly measurable for the joint measure, hence so is their product, and
`AEStronglyMeasurable.integral_prod_right'` (applied to the swapped variables) gives the a.e.
strong measurability of the `p₁`-integral as a function of `x`.
-/

theorem PhiAEStronglyMeasurable {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {W : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen W) (m : ℕ) (s : ℝ) :
    MeasureTheory.AEStronglyMeasurable (fun x : ℝ × ℝ => ∫ p₁ : ℝ,
      Work.Spaces.pzIter m (fun a b => Work.FTS.StrongEps.Jker ρ ε (a, b)) p₁ x.2
        * W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))) := by
  set S : Set (ℝ × (ℝ × ℝ)) := {q | q.2.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} with hSdef
  -- ### the kernel factor is jointly continuous
  have hKcont : Continuous (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.pzIter m (fun a b => Work.FTS.StrongEps.Jker ρ ε (a, b)) q.1 q.2.2) := by
    have hbase : ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞)
        (Function.uncurry (fun a b : ℝ => Work.FTS.StrongEps.Jker ρ ε (a, b))) Set.univ :=
      (Work.FTS.StrongEps.Jker_smooth hρ ε (n := m)).contDiffOn
    have h1 : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞)
        (Function.uncurry (Work.Spaces.pzIter m
          (fun a b : ℝ => Work.FTS.StrongEps.Jker ρ ε (a, b)))) Set.univ :=
      Work.FTS.GalBasis.contDiffOn_uncurry_pzIter_le
        (G := fun a b : ℝ => Work.FTS.StrongEps.Jker ρ ε (a, b))
        (V := Set.univ) isOpen_univ hbase m 0 (by omega)
    exact ((contDiffOn_univ.mp h1).continuous).comp (continuous_fst.prodMk continuous_snd.snd)
  -- ### the profile factor is continuous on `S`
  have hcontW : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      W (Real.exp (s - q.1)) (Work.FTS.StrongEps.thShift q.2.1 q.2.2)) S := by
    rw [hSdef]
    have htan : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => Real.tan q.2.1)
        {q : ℝ × (ℝ × ℝ) | q.2.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} := by
      refine Real.continuousOn_tan.comp continuous_snd.fst.continuousOn (fun q hq => ?_)
      simp only [Set.mem_ofPred_eq] at hq
      exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hq.1], hq.2⟩).ne'
    have h1 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => Real.tan q.2.1 * Real.exp (-q.2.2))
        {q : ℝ × (ℝ × ℝ) | q.2.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} :=
      htan.mul (Real.continuous_exp.comp_continuousOn (continuous_snd.snd.neg).continuousOn)
    have hth : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => Work.FTS.StrongEps.thShift q.2.1 q.2.2)
        {q : ℝ × (ℝ × ℝ) | q.2.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} := by
      have h2 := Real.continuous_arctan.comp_continuousOn h1
      simpa only [Work.FTS.StrongEps.thShift, Function.comp_def] using h2
    have hexp : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => Real.exp (s - q.1))
        {q : ℝ × (ℝ × ℝ) | q.2.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} := by fun_prop
    have hpair : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
        (Real.exp (s - q.1), Work.FTS.StrongEps.thShift q.2.1 q.2.2))
        {q : ℝ × (ℝ × ℝ) | q.2.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} := hexp.prodMk hth
    have hmem : ∀ q ∈ {q : ℝ × (ℝ × ℝ) | q.2.1 ∈ Set.Ioo (0 : ℝ) (π / 2)},
        (Real.exp (s - q.1), Work.FTS.StrongEps.thShift q.2.1 q.2.2) ∈ Work.FTS.EllipticEst.Q0 :=
      fun q hq => ⟨Real.exp_pos _, Work.FTS.StrongEps.thShift_mem hq⟩
    have h3 := hsm.continuousOn.comp hpair hmem
    simpa only [Function.uncurry, Function.comp_def] using h3
  have hSmeas : MeasurableSet S := by
    rw [hSdef]
    exact (isOpen_Ioo.preimage continuous_snd.fst).measurableSet
  -- ### `S` is conull
  have hnull : (MeasureTheory.volume.prod ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
      (MeasureTheory.volume.restrict (Set.Icc (-ε) ε)))) Sᶜ = 0 := by
    have hB : (MeasureTheory.volume.restrict Work.Spaces.Iθ) ((Set.Ioo (0 : ℝ) (π / 2))ᶜ) = 0 := by
      rw [Measure.restrict_apply measurableSet_Ioo.compl]
      have h0 : (MeasureTheory.volume : Measure ℝ) ({0} ∪ {π / 2}) = 0 :=
        measure_union_null (measure_singleton 0) (measure_singleton (π / 2))
      refine measure_mono_null ?_ h0
      intro x hx
      simp only [Work.Spaces.Iθ, Set.mem_inter_iff, Set.mem_Icc, Set.mem_compl_iff, Set.mem_Ioo,
        Set.mem_union, Set.mem_singleton_iff] at hx ⊢
      obtain ⟨hxn, hxI⟩ := hx
      rcases lt_or_ge (0 : ℝ) x with h | h
      · rcases lt_or_ge x (π / 2) with h2 | h2
        · exact absurd ⟨h, h2⟩ hxn
        · exact Or.inr (le_antisymm hxI.2 h2)
      · exact Or.inl (le_antisymm h hxI.1)
    have hinner : ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict (Set.Icc (-ε) ε)))
        (((Set.Ioo (0 : ℝ) (π / 2))ᶜ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
      rw [Measure.prod_prod, hB]
      simp
    rw [hSdef]
    have hset : ({q : ℝ × (ℝ × ℝ) | q.2.1 ∈ Set.Ioo (0 : ℝ) (π / 2)}ᶜ : Set (ℝ × (ℝ × ℝ)))
        = (Set.univ : Set ℝ) ×ˢ (((Set.Ioo (0 : ℝ) (π / 2))ᶜ) ×ˢ (Set.univ : Set ℝ)) := by
      ext q
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true,
        true_and]
    rw [hset, Measure.prod_prod, hinner]
    simp
  have hW : AEStronglyMeasurable (fun q : ℝ × (ℝ × ℝ) =>
      W (Real.exp (s - q.1)) (Work.FTS.StrongEps.thShift q.2.1 q.2.2))
      (MeasureTheory.volume.prod ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict (Set.Icc (-ε) ε)))) := by
    have hSae : ∀ᵐ q ∂(MeasureTheory.volume.prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
          (MeasureTheory.volume.restrict (Set.Icc (-ε) ε)))), q ∈ S := by
      filter_upwards [compl_mem_ae_iff.mpr hnull] with q hq
      simpa only [Set.mem_compl_iff, not_not] using hq
    rw [← Measure.restrict_eq_self_of_ae_mem hSae]
    exact hcontW.aestronglyMeasurable hSmeas
  -- ### the joint integrand, and the parametric integral
  have hjoint : AEStronglyMeasurable (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.pzIter m (fun a b => Work.FTS.StrongEps.Jker ρ ε (a, b)) q.1 q.2.2
        * W (Real.exp (s - q.1)) (Work.FTS.StrongEps.thShift q.2.1 q.2.2))
      (MeasureTheory.volume.prod ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict (Set.Icc (-ε) ε)))) :=
    hKcont.aestronglyMeasurable.mul hW
  have hswap := hjoint.prod_swap
  exact MeasureTheory.AEStronglyMeasurable.integral_prod_right'
    (μ := (MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
      (MeasureTheory.volume.restrict (Set.Icc (-ε) ε)))
    (ν := (MeasureTheory.volume : Measure ℝ)) hswap

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.XBallIterExistsAux.PhiFam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.XBallIterExistsAux

set_option autoImplicit false

/-! ## The compact measure space of the parametric argument -/

/-- The compact measure space of the parametric-integral argument: the angle `θ ∈ Iθ` and the
second kernel variable `p₂ ∈ [-ε,ε]`. -/
def Jmu (ε : ℝ) : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
    (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))

instance instIsFiniteMeasureJmu (ε : ℝ) : MeasureTheory.IsFiniteMeasure (Jmu ε) := by
  rw [Jmu]; infer_instance

/-- On `Jmu ε` the angle is a.e. in the *open* interval; this is what makes the two endpoints
`0, π/2` (where `W` is not controlled) irrelevant. -/
theorem ae_mem_Ioo_Jmu {ε : ℝ} : ∀ᵐ x ∂(Jmu ε), x.1 ∈ Set.Ioo 0 (Real.pi / 2) := by
  apply MeasureTheory.Measure.quasiMeasurePreserving_fst.ae
  rw [show (MeasureTheory.volume.restrict Work.Spaces.Iθ : MeasureTheory.Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) from
    (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-! ## The kernel in the log-angular variable -/

/-- `Jker ρ ε` as a curried function of the two log-coordinates. -/
def kern (ρ : ℝ × ℝ → ℝ) (ε : ℝ) : ℝ → ℝ → ℝ := fun a b => Work.FTS.StrongEps.Jker ρ ε (a, b)

theorem uncurry_kern (ρ : ℝ × ℝ → ℝ) (ε : ℝ) :
    Function.uncurry (kern ρ ε) = Work.FTS.StrongEps.Jker ρ ε := rfl


/-- The `m`-th `s`-derivative family of the angular slice of `J_ε W` in the log variable. -/
def Phi (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (W : ℝ → ℝ → ℝ) (m : ℕ) (s : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∫ p₁ : ℝ, Work.Spaces.pzIter m (kern ρ ε) p₁ x.2
    * W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2)


/-! ## Smoothness, support and the first derivative of the kernel slices -/

theorem contDiff_kern_slice {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (ε : ℝ) (m : ℕ) (p₂ : ℝ) :
    ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (fun p₁ : ℝ => Work.Spaces.pzIter m (kern ρ ε) p₁ p₂) := by
  have hbase : ContDiffOn ℝ (((m + 1 : ℕ) : WithTop ℕ∞))
      (Function.uncurry (kern ρ ε)) Set.univ := by
    rw [uncurry_kern]
    exact (Work.FTS.StrongEps.Jker_smooth hρ ε (n := m + 1)).contDiffOn
  have hjoint : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞)
      (Function.uncurry (Work.Spaces.pzIter m (kern ρ ε))) Set.univ :=
    Work.FTS.GalBasis.contDiffOn_uncurry_pzIter_le (G := kern ρ ε) (V := Set.univ)
      isOpen_univ hbase m 1 (by omega)
  have hg : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) (fun p₁ : ℝ => (p₁, p₂)) Set.univ := by fun_prop
  have hcomp := hjoint.comp hg (fun x _ => trivial)
  exact contDiffOn_univ.mp (by simpa only [Function.comp_def, Function.uncurry] using hcomp)

theorem hasCompactSupport_kern_slice {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) (m : ℕ) (p₂ : ℝ) :
    HasCompactSupport (fun p₁ : ℝ => Work.Spaces.pzIter m (kern ρ ε) p₁ p₂) := by
  induction m with
  | zero =>
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) ε) ?_
    intro p₁ hp
    have h1 : Work.FTS.StrongEps.Jker ρ ε (p₁, p₂) ≠ 0 := hp
    have h2 := Work.FTS.StrongEps.Jker_ne_zero_support hρ hε h1
    have h3 : p₁ ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p₂]
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    rw [sq_le_sq] at h3
    rwa [abs_of_nonneg hε.le] at h3
  | succ m ih =>
    have h := ih.deriv
    rwa [show deriv (fun p₁ : ℝ => Work.Spaces.pzIter m (kern ρ ε) p₁ p₂)
        = fun p₁ : ℝ => Work.Spaces.pzIter (m + 1) (kern ρ ε) p₁ p₂ from by
      funext p₁
      rw [Work.Spaces.pzIter_succ, Work.Spaces.pz]] at h

theorem deriv_pzIter_kern_slice (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (m : ℕ) (p₂ : ℝ) :
    deriv (fun p₁ : ℝ => Work.Spaces.pzIter m (kern ρ ε) p₁ p₂)
      = fun p₁ : ℝ => Work.Spaces.pzIter (m + 1) (kern ρ ε) p₁ p₂ := by
  funext p₁
  rw [Work.Spaces.pzIter_succ, Work.Spaces.pz]

/-- **The `s`-derivative of the family**: `∂_s (Phi m) = Phi (m+1)`, for every log-angle `x.1`
in the open quadrant.  The derivative is routed onto the kernel by `ConvDeriv`. -/
theorem hasDerivAt_Phi {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {W : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen W) (m : ℕ) (s : ℝ)
    {x : ℝ × ℝ} (hx : x.1 ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun s' => Phi ρ ε W m s' x) (Phi ρ ε W (m + 1) s x) s := by
  have hκ : ContDiff ℝ 1 (fun p₁ : ℝ => Work.Spaces.pzIter m (kern ρ ε) p₁ x.2) :=
    contDiff_kern_slice hρ ε m x.2
  have hκc : HasCompactSupport (fun p₁ : ℝ => Work.Spaces.pzIter m (kern ρ ε) p₁ x.2) :=
    hasCompactSupport_kern_slice hρ.moll hε m x.2
  have hg : LocallyIntegrable (fun t : ℝ =>
      W (Real.exp t) (Work.FTS.StrongEps.thShift x.1 x.2)) volume := by
    have hmem : ∀ t : ℝ,
        (Real.exp t, Work.FTS.StrongEps.thShift x.1 x.2) ∈ Work.FTS.EllipticEst.Q0 :=
      fun t => ⟨Real.exp_pos t, Work.FTS.StrongEps.thShift_mem hx⟩
    have hcont : ContinuousOn (Function.uncurry W) Work.FTS.EllipticEst.Q0 := hsm.continuousOn
    have h1 : Continuous (fun t : ℝ =>
        (Real.exp t, Work.FTS.StrongEps.thShift x.1 x.2)) := by fun_prop
    exact (hcont.comp_continuous h1 hmem).locallyIntegrable
  have h := Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ConvDeriv hκ hκc hg s
  simpa only [Phi, deriv_pzIter_kern_slice] using h

/-! ## The support of the `p₁`-derivatives of the kernel -/

theorem kern_eq_zero_of_abs_gt {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {p₁ p₂ : ℝ} (h : ε < |p₁| ∨ ε < |p₂|) :
    kern ρ ε p₁ p₂ = 0 := by
  by_contra hne
  have hsup := Work.FTS.StrongEps.Jker_ne_zero_support hρ hε hne
  rcases h with h | h
  · have : ε ^ 2 < |p₁| ^ 2 := pow_lt_pow_left₀ h hε.le (by norm_num)
    rw [sq_abs] at this
    nlinarith [sq_nonneg p₂]
  · have : ε ^ 2 < |p₂| ^ 2 := pow_lt_pow_left₀ h hε.le (by norm_num)
    rw [sq_abs] at this
    nlinarith [sq_nonneg p₁]

/-- The `m`-th `p₁`-derivative of the kernel vanishes off the square `[-ε,ε] × [-ε,ε]`. -/
theorem pzIter_kern_eq_zero_of_abs_gt {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) (m : ℕ) {p₁ p₂ : ℝ} (h : ε < |p₁| ∨ ε < |p₂|) :
    Work.Spaces.pzIter m (kern ρ ε) p₁ p₂ = 0 := by
  induction m generalizing p₁ with
  | zero => exact kern_eq_zero_of_abs_gt hρ hε h
  | succ m ih =>
    rw [Work.Spaces.pzIter_succ, Work.Spaces.pz]
    rcases h with h | h
    · -- `|p₁| > ε`: the slice is zero on a neighbourhood of `p₁`
      have hmem : ∀ᶠ a in 𝓝 p₁, ε < |a| :=
        (continuous_abs.continuousAt).eventually (eventually_gt_nhds h)
      have heq : (fun a : ℝ => Work.Spaces.pzIter m (kern ρ ε) a p₂) =ᶠ[𝓝 p₁] 0 := by
        filter_upwards [hmem] with a ha
        exact ih (Or.inl ha)
      rw [heq.deriv_eq]
      simp
    · have hone : (fun a : ℝ => Work.Spaces.pzIter m (kern ρ ε) a p₂) = fun _ => (0 : ℝ) := by
        funext a
        exact ih (Or.inr h)
      rw [hone]
      simp

/-- The `m`-th `p₁`-derivative of the kernel vanishes when either coordinate is outside
`[-ε,ε]`. -/
theorem pzIter_kern_eq_zero_of_not_mem {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) (m : ℕ) {p₁ p₂ : ℝ}
    (h : p₁ ∉ Set.Icc (-ε) ε ∨ p₂ ∉ Set.Icc (-ε) ε) :
    Work.Spaces.pzIter m (kern ρ ε) p₁ p₂ = 0 := by
  refine pzIter_kern_eq_zero_of_abs_gt hρ hε m ?_
  have key : ∀ q : ℝ, q ∉ Set.Icc (-ε) ε → ε < |q| := by
    intro q hq
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hq
    rcases hq with hq | hq
    · exact lt_of_lt_of_le (by linarith : ε < -q) (neg_le_abs q)
    · exact lt_of_lt_of_le hq (le_abs_self q)
  rcases h with h | h
  · exact Or.inl (key p₁ h)
  · exact Or.inr (key p₂ h)

/-- A uniform bound for the `m`-th kernel derivative on the square `[-ε,ε] × [-ε,ε]`. -/
theorem exists_kernBound {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Set.Icc (-ε) ε ×ˢ Set.Icc (-ε) ε,
      |Work.Spaces.pzIter m (kern ρ ε) p.1 p.2| ≤ C := by
  have hbase : ContDiffOn ℝ (((m + 1 : ℕ) : WithTop ℕ∞))
      (Function.uncurry (kern ρ ε)) Set.univ := by
    rw [uncurry_kern]
    exact (Work.FTS.StrongEps.Jker_smooth hρ ε (n := m + 1)).contDiffOn
  have h0 : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞)
      (Function.uncurry (Work.Spaces.pzIter m (kern ρ ε))) Set.univ :=
    Work.FTS.GalBasis.contDiffOn_uncurry_pzIter_le (G := kern ρ ε) (V := Set.univ)
      isOpen_univ hbase m 0 (by omega)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (h0.continuousOn.mono (Set.subset_univ _))
  refine ⟨max C 0, le_max_right _ _, fun p hp => ?_⟩
  simpa only [Function.uncurry, Real.norm_eq_abs] using
    le_trans (hC p hp) (le_max_left C 0)

/-- **The pointwise domination of the family**: on the slab `s ∈ (s₀-1, s₀+1)` (encoded by the
condition `hs` on the range of `e^{s-p₁}` over the support of the kernel) the family is dominated
by `C · G (thShift x.1 x.2)`, where `G` bounds the slices `W z ·` uniformly in `z ∈ [a,b]`. -/
theorem abs_Phi_le {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {W : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen W)
    {G : ℝ → ℝ} {a b : ℝ} (hGnn : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ G θ)
    (hdom : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |W z θ| ≤ G θ)
    {s : ℝ} (hs : ∀ p₁ : ℝ, p₁ ∈ Set.Icc (-ε) ε → Real.exp (s - p₁) ∈ Set.Icc a b)
    (m : ℕ) {x : ℝ × ℝ} (hx : x.1 ∈ Set.Ioo 0 (Real.pi / 2)) :
    |Phi ρ ε W m s x| ≤ (2 * ε * (Classical.choose (exists_kernBound hρ hε m)))
      * G (Work.FTS.StrongEps.thShift x.1 x.2) := by
  set C := Classical.choose (exists_kernBound hρ hε m) with hCdef
  have hCnn : 0 ≤ C := (Classical.choose_spec (exists_kernBound hρ hε m)).1
  have hCb : ∀ p ∈ Set.Icc (-ε) ε ×ˢ Set.Icc (-ε) ε,
      |Work.Spaces.pzIter m (kern ρ ε) p.1 p.2| ≤ C :=
    (Classical.choose_spec (exists_kernBound hρ hε m)).2
  have hθ' : Work.FTS.StrongEps.thShift x.1 x.2 ∈ Set.Ioo 0 (Real.pi / 2) :=
    Work.FTS.StrongEps.thShift_mem hx
  have hGθ : 0 ≤ G (Work.FTS.StrongEps.thShift x.1 x.2) := hGnn _ hθ'
  -- pointwise bound on the integrand
  have hpt : ∀ p₁ : ℝ, |Work.Spaces.pzIter m (kern ρ ε) p₁ x.2
        * W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2)|
      ≤ |Work.Spaces.pzIter m (kern ρ ε) p₁ x.2| * G (Work.FTS.StrongEps.thShift x.1 x.2) := by
    intro p₁
    rw [abs_mul]
    by_cases hzero : Work.Spaces.pzIter m (kern ρ ε) p₁ x.2 = 0
    · simp [hzero]
    · have hp1 : p₁ ∈ Set.Icc (-ε) ε := by
        by_contra hp
        exact hzero (pzIter_kern_eq_zero_of_not_mem hρ.moll hε m (Or.inl hp))
      have hW : |W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2)|
          ≤ G (Work.FTS.StrongEps.thShift x.1 x.2) :=
        hdom _ (hs p₁ hp1) _ hθ'
      exact mul_le_mul_of_nonneg_left hW (abs_nonneg _)
  -- the `p₁`-integral of the kernel derivative is bounded by `2ε * C`
  have hind : ∀ p₁ : ℝ, |Work.Spaces.pzIter m (kern ρ ε) p₁ x.2|
      ≤ C * Set.indicator (Set.Icc (-ε) ε) (fun _ => (1 : ℝ)) p₁ := by
    intro p₁
    by_cases hp : p₁ ∈ Set.Icc (-ε) ε
    · rw [Set.indicator_of_mem hp, mul_one]
      by_cases h2 : x.2 ∈ Set.Icc (-ε) ε
      · exact hCb (p₁, x.2) ⟨hp, h2⟩
      · rw [pzIter_kern_eq_zero_of_not_mem hρ.moll hε m (Or.inr h2), abs_zero]
        exact hCnn
    · rw [pzIter_kern_eq_zero_of_not_mem hρ.moll hε m (Or.inl hp), abs_zero,
        Set.indicator_of_notMem hp, mul_zero]
  have hInt : (∫ p₁ : ℝ, |Work.Spaces.pzIter m (kern ρ ε) p₁ x.2|) ≤ 2 * ε * C := by
    have hκint : Integrable (fun p₁ : ℝ => |Work.Spaces.pzIter m (kern ρ ε) p₁ x.2|) volume :=
      ((contDiff_kern_slice hρ ε m x.2).continuous.abs).integrable_of_hasCompactSupport
        (hasCompactSupport_kern_slice hρ.moll hε m x.2).abs
    have hbdd : Integrable (fun p₁ : ℝ =>
        C * Set.indicator (Set.Icc (-ε) ε) (fun _ => (1 : ℝ)) p₁) volume :=
      (integrable_indicator_iff measurableSet_Icc).2
        (integrableOn_const measure_Icc_lt_top.ne) |>.const_mul C
    calc (∫ p₁ : ℝ, |Work.Spaces.pzIter m (kern ρ ε) p₁ x.2|)
        ≤ ∫ p₁ : ℝ, C * Set.indicator (Set.Icc (-ε) ε) (fun _ => (1 : ℝ)) p₁ :=
          integral_mono hκint hbdd hind
      _ = C * ∫ p₁ : ℝ, Set.indicator (Set.Icc (-ε) ε) (fun _ => (1 : ℝ)) p₁ := by
          rw [integral_const_mul]
      _ = C * (volume.real (Set.Icc (-ε) ε)) := by
          rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one]
      _ = 2 * ε * C := by
          rw [MeasureTheory.Measure.real, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith)]
          ring
  have hIntκ : Integrable (fun p₁ : ℝ => |Work.Spaces.pzIter m (kern ρ ε) p₁ x.2|
      * G (Work.FTS.StrongEps.thShift x.1 x.2)) volume :=
    (((contDiff_kern_slice hρ ε m x.2).continuous.abs).integrable_of_hasCompactSupport
      (hasCompactSupport_kern_slice hρ.moll hε m x.2).abs).mul_const _
  calc |Phi ρ ε W m s x|
      = |∫ p₁ : ℝ, Work.Spaces.pzIter m (kern ρ ε) p₁ x.2
          * W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2)| := rfl
    _ ≤ ∫ p₁ : ℝ, |Work.Spaces.pzIter m (kern ρ ε) p₁ x.2
          * W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2)| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ p₁ : ℝ, |Work.Spaces.pzIter m (kern ρ ε) p₁ x.2|
          * G (Work.FTS.StrongEps.thShift x.1 x.2) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun p₁ => abs_nonneg _) hIntκ
          (Filter.Eventually.of_forall hpt)
    _ = (∫ p₁ : ℝ, |Work.Spaces.pzIter m (kern ρ ε) p₁ x.2|)
          * G (Work.FTS.StrongEps.thShift x.1 x.2) := by
        rw [integral_mul_const]
    _ ≤ (2 * ε * C) * G (Work.FTS.StrongEps.thShift x.1 x.2) :=
        mul_le_mul_of_nonneg_right hInt hGθ

end Work.FTS.StrongEps.EpsE4Thr.XBallIterExistsAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.smoothOpen_slice_of_epsRHSP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

/-! ## (1) The scheme in integral form

The pointwise ODE of `IsEpsSolP` on the open quadrant, integrated over `[0,τ]` by the fundamental
theorem of calculus (the integrand is continuous in `s` by `hcont`). -/

/-! ## (2) The bootstrap: primitives of the mixed slots are `C^n` for every `n`

Given the two clauses (continuity of the primitives, and the two slice derivatives of a
primitive), the induction on `n` is immediate from `contDiffOn_succ_of_partials`: the `z`- and
`θ`-derivatives of the primitive of `mixed j i (W ·)` are the primitives of `mixed (j+1) i (W ·)`
and `mixed j (i+1) (W ·)` divided by `z` resp. `sin 2θ`, and dividing a `C^n` function by the
nowhere-vanishing smooth factors `z` and `sin 2θ` keeps it `C^n` on `Q0`. -/

/-! ## (3) The target -/


end Work.FTS.StrongEps
end
end
