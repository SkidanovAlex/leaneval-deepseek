/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/XBallLimAux/FstarJepsSmooth.lean`

**The angular moment `F_* (J_ε W)` is `C^∞` on `(0,∞)`** for `W` smooth on the open quadrant with
`HkMem α 1 W` — a copy of `Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmooth` (the tree's proof, complete
but resting on the `sorry`-stub `FstarJepsSmoothAux.ThShiftPreimageNull`) in which the single
`MajorantIntegrable` input is taken from the `sorry`-free `XBallLimAux.MajorantIntegrable`.

The declaration name is `Work.FTS.StrongEps.EpsE4Thr.XBallLimAux.FstarJepsSmooth`; it is consumed
by the cloned `XBallLimAux.FstarPzJepsSmooth`, the `fsm` input of the class-`C` clause of the limit
slice in `Submission/Work/FTS/StrongEps/EpsE4Thr/XBallLimExists.lean`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.GalBasis.exists_mixed_bound
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ConvDeriv
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ParamIntegral
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ThShiftSubst
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ZSliceDomination
import Submission.Work.FTS.StrongEps.EpsE4Thr.XBallLimAux.MajorantIntegrable
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.PhiAEStronglyMeasurable
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.FubiniSwap

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.XBallLimAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The log-coordinate kernel and the derivative family

`J_ε` is, in the log coordinates `s = log z`, `ζ = log tan θ`, the convolution of `logPull W`
with the kernel `Jker ρ ε`; in the *un-shifted* angular variable `θ` it reads

  `J_ε W (e^s) θ = ∫ p, Jker ρ ε p * W (e^{s - p.1}) (thShift θ p.2)`.

For the parametric-integral argument we keep the `p₂`-integration *outside* the `s`-family (it
becomes part of the measure space, so that the angular substitution bound of
`FstarJepsSmoothAux.ThShiftSubst` can be used for the domination) and route all `s`-derivatives
of the remaining `p₁`-convolution onto the kernel.  The resulting family is

  `Phi ρ ε W m s x = ∫ p₁, ∂₁^m (Jker ρ ε) (p₁, x.2) · W (e^{s - p₁}) (thShift x.1 x.2)`,
  `x = (θ, p₂) ∈ Iθ × [-ε,ε]`,

with `∂_s (Phi m) = Phi (m+1)`. -/

/-- `Jker ρ ε` as a curried function of the two log-coordinates. -/
def kern (ρ : ℝ × ℝ → ℝ) (ε : ℝ) : ℝ → ℝ → ℝ := fun a b => Work.FTS.StrongEps.Jker ρ ε (a, b)

theorem uncurry_kern (ρ : ℝ × ℝ → ℝ) (ε : ℝ) :
    Function.uncurry (kern ρ ε) = Work.FTS.StrongEps.Jker ρ ε := rfl

theorem kern_apply (ρ : ℝ × ℝ → ℝ) (ε a b : ℝ) :
    kern ρ ε a b = Work.FTS.StrongEps.Jker ρ ε (a, b) := rfl

/-- The `m`-th `s`-derivative family of the angular slice of `J_ε W` in the log variable. -/
def Phi (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (W : ℝ → ℝ → ℝ) (m : ℕ) (s : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∫ p₁ : ℝ, Work.Spaces.pzIter m (kern ρ ε) p₁ x.2
    * W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2)

theorem Phi_apply (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (W : ℝ → ℝ → ℝ) (m : ℕ) (s : ℝ) (x : ℝ × ℝ) :
    Phi ρ ε W m s x = ∫ p₁ : ℝ, Work.Spaces.pzIter m (kern ρ ε) p₁ x.2
      * W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2) := rfl

/-! ### Smoothness, support and the first derivative of the kernel slices -/

theorem contDiff_kern_slice {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) (ε : ℝ) (m : ℕ) (p₂ : ℝ) :
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

theorem hasCompactSupport_kern_slice {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) (m : ℕ) (p₂ : ℝ) :
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
in the open quadrant.  The derivative is routed onto the kernel by
`FstarJepsSmoothAux.ConvDeriv`. -/
theorem hasDerivAt_Phi {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {W : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen W) (m : ℕ) (s : ℝ) {x : ℝ × ℝ}
    (hx : x.1 ∈ Set.Ioo 0 (Real.pi / 2)) :
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

/-! ### Support and uniform bounds for the kernel slices -/

/-- The `m`-th `p₁`-derivative of the kernel slice vanishes for `|p₁| > ε`. -/
theorem pzIter_kern_eq_zero_of_eps_lt_abs {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) (m : ℕ) {p₁ p₂ : ℝ} (h : ε < |p₁|) :
    Work.Spaces.pzIter m (kern ρ ε) p₁ p₂ = 0 := by
  induction m generalizing p₁ with
  | zero =>
    refine Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε (fun hmem => ?_)
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    have h2 : ‖p₁‖ ≤ ‖((p₁, p₂) : ℝ × ℝ)‖ := norm_fst_le ((p₁, p₂) : ℝ × ℝ)
    rw [Real.norm_eq_abs] at h2
    linarith
  | succ m ih =>
    rw [Work.Spaces.pzIter_succ, Work.Spaces.pz]
    have h0 : (fun a : ℝ => Work.Spaces.pzIter m (kern ρ ε) a p₂) =ᶠ[𝓝 p₁] fun _ => (0 : ℝ) := by
      have hd : 0 < (|p₁| - ε) / 2 := by linarith [abs_nonneg p₁]
      filter_upwards [Metric.ball_mem_nhds p₁ hd] with a ha
      rw [Metric.mem_ball, Real.dist_eq] at ha
      refine ih ?_
      have h1 : |p₁| - |a - p₁| ≤ |a| := by
        have h3 : |p₁| - |a| ≤ |p₁ - a| := abs_sub_abs_le_abs_sub p₁ a
        rw [abs_sub_comm] at h3
        linarith
      linarith [h1, ha, h]
    rw [h0.deriv_eq, deriv_const]

/-- The `m`-th `p₁`-derivative of the kernel slice vanishes for `|p₂| > ε`. -/
theorem pzIter_kern_eq_zero_of_eps_lt_abs_snd {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) (m : ℕ) {p₂ : ℝ} (h : ε < |p₂|) (p₁ : ℝ) :
    Work.Spaces.pzIter m (kern ρ ε) p₁ p₂ = 0 := by
  induction m generalizing p₁ with
  | zero =>
    refine Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε (fun hmem => ?_)
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    have h2 : ‖p₂‖ ≤ ‖((p₁, p₂) : ℝ × ℝ)‖ := norm_snd_le ((p₁, p₂) : ℝ × ℝ)
    rw [Real.norm_eq_abs] at h2
    linarith
  | succ m ih =>
    rw [Work.Spaces.pzIter_succ, Work.Spaces.pz]
    have h0 : (fun a : ℝ => Work.Spaces.pzIter m (kern ρ ε) a p₂) =ᶠ[𝓝 p₁] fun _ => (0 : ℝ) :=
      Filter.Eventually.of_forall fun a => ih a
    rw [h0.deriv_eq, deriv_const]

/-- A uniform bound for the kernel slices on the box `[-ε,ε] × [-ε,ε]`. -/
theorem exists_kern_box_bound {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (m : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p₁ ∈ Set.Icc (-ε) ε, ∀ p₂ ∈ Set.Icc (-ε) ε,
      ‖Work.Spaces.pzIter m (kern ρ ε) p₁ p₂‖ ≤ M := by
  have hJ : Continuous (fun q : ℝ × ℝ => ‖Work.Spaces.pzIter m (kern ρ ε) q.1 q.2‖) := by
    have h1 : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞)
        (Function.uncurry (Work.Spaces.pzIter m (kern ρ ε))) Set.univ :=
      Work.FTS.GalBasis.contDiffOn_uncurry_pzIter_le (G := kern ρ ε) (V := Set.univ) isOpen_univ
        (by rw [uncurry_kern]; exact (Work.FTS.StrongEps.Jker_smooth hρ ε (n := m)).contDiffOn)
        m 0 (by omega)
    exact ((contDiffOn_univ.mp h1).continuous).norm
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hJ.continuousOn
  refine ⟨|M|, abs_nonneg _, ?_⟩
  intro p₁ h₁ p₂ h₂
  exact le_trans (by simpa using hM (p₁, p₂) ⟨h₁, h₂⟩) (le_abs_self M)

/-- The kernel slices have uniformly bounded `p₁`-integrals. -/
theorem exists_kern_slice_integral_le {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ}
    (hε : 0 < ε) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p₂ : ℝ, ∫ p₁ : ℝ, ‖Work.Spaces.pzIter m (kern ρ ε) p₁ p₂‖ ≤ C := by
  obtain ⟨M, hM0, hM⟩ := exists_kern_box_bound hρ hε m
  refine ⟨M * (2 * ε), mul_nonneg hM0 (by linarith), fun p₂ => ?_⟩
  have hsmall : ∀ x : ℝ, x ∉ Set.Icc (-ε) ε → ε < |x| := by
    intro x hx
    by_contra hc
    push_neg at hc
    exact hx ⟨by linarith [neg_abs_le x, hc], by linarith [le_abs_self x, hc]⟩
  have hbnd : ∀ x : ℝ, ‖Work.Spaces.pzIter m (kern ρ ε) x p₂‖ ≤ M := by
    intro x
    by_cases hx : x ∈ Set.Icc (-ε) ε
    · by_cases h2 : p₂ ∈ Set.Icc (-ε) ε
      · exact hM x hx p₂ h2
      · rw [pzIter_kern_eq_zero_of_eps_lt_abs_snd (p₂ := p₂) hρ.moll hε m (hsmall p₂ h2) x, norm_zero]
        exact hM0
    · rw [pzIter_kern_eq_zero_of_eps_lt_abs (p₁ := x) hρ.moll hε m (hsmall x hx), norm_zero]
      exact hM0
  have hrestrict : (∫ p₁ : ℝ, ‖Work.Spaces.pzIter m (kern ρ ε) p₁ p₂‖)
      = ∫ p₁ in Set.Icc (-ε) ε, ‖Work.Spaces.pzIter m (kern ρ ε) p₁ p₂‖ :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun p₁ : ℝ => ‖Work.Spaces.pzIter m (kern ρ ε) p₁ p₂‖)
      (s := Set.Icc (-ε) ε) (fun x hx => by rw [pzIter_kern_eq_zero_of_eps_lt_abs (p₁ := x) hρ.moll hε m (hsmall x hx), norm_zero])).symm
  rw [hrestrict]
  calc ∫ x in Set.Icc (-ε) ε, ‖Work.Spaces.pzIter m (kern ρ ε) x p₂‖
      ≤ ∫ _ in Set.Icc (-ε) ε, M := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x => norm_nonneg _)
          (MeasureTheory.integrableOn_const (C := M) ?_) ?_
        · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx
          exact hbnd x
    _ = M * (2 * ε) := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.Measure.real_def,
          Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
        ring

/-! ### The measure space on `(θ, p₂)` and the parametrised family -/

/-- The measure space `(θ,p₂) ∈ Iθ × [-ε,ε]` on which the `p₂`-integration of `J_ε W` lives. -/
abbrev Mu (ε : ℝ) : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
    (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))

/-- Almost every `(θ,p₂)` has `θ` in the open quadrant. -/
theorem ae_fst_mem_Ioo {ε : ℝ} : ∀ᵐ x ∂Mu ε, x.1 ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [MeasureTheory.ae_iff]
  have hmeas : MeasurableSet {x : ℝ × ℝ | ¬ (x.1 ∈ Set.Ioo 0 (Real.pi / 2))} :=
    measurableSet_Ioo.compl.preimage measurable_fst
  rw [MeasureTheory.Measure.prod_apply_symm hmeas]
  have h0 : ∀ p₂ : ℝ, (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ((fun x : ℝ => (x, p₂)) ⁻¹' {x : ℝ × ℝ | ¬ (x.1 ∈ Set.Ioo 0 (Real.pi / 2))}) = 0 := by
    intro p₂
    have hset : (fun x : ℝ => (x, p₂)) ⁻¹' {x : ℝ × ℝ | ¬ (x.1 ∈ Set.Ioo 0 (Real.pi / 2))}
        = {θ : ℝ | ¬ (θ ∈ Set.Ioo 0 (Real.pi / 2))} := rfl
    rw [hset]
    change (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ((Set.Ioo 0 (Real.pi / 2))ᶜ) = 0
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo.compl]
    have hsub : (Set.Ioo 0 (Real.pi / 2))ᶜ ∩ Work.Spaces.Iθ ⊆ ({0, Real.pi / 2} : Set ℝ) := by
      intro θ hθ
      rw [Set.mem_inter_iff, Set.mem_compl_iff, Work.Spaces.Iθ, Set.mem_Icc] at hθ
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_cases h1 : θ = 0
      · exact Or.inl h1
      · refine Or.inr ?_
        by_contra h2
        exact hθ.1 ⟨lt_of_le_of_ne hθ.2.1 (Ne.symm h1), lt_of_le_of_ne hθ.2.2 h2⟩
    have h3 : MeasureTheory.volume ({0, Real.pi / 2} : Set ℝ) = 0 := by
      rw [Set.insert_eq]
      exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
        (MeasureTheory.measure_singleton _)
    exact MeasureTheory.measure_mono_null (t := ({0, Real.pi / 2} : Set ℝ)) hsub h3
  rw [show (fun p₂ : ℝ => (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ((fun x : ℝ => (x, p₂)) ⁻¹' {x : ℝ × ℝ | ¬ (x.1 ∈ Set.Ioo 0 (Real.pi / 2))})) = fun _ => (0 : ENNReal) from
    funext h0]
  simp

/-- The kernel slices are integrable, with a bound uniform in `p₂`. -/
theorem integrable_kern_slice_norm {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ}
    (hε : 0 < ε) (m : ℕ) (p₂ : ℝ) :
    Integrable (fun p₁ : ℝ => ‖Work.Spaces.pzIter m (kern ρ ε) p₁ p₂‖) volume :=
  ((contDiff_kern_slice hρ ε m p₂).continuous.norm.integrable_of_hasCompactSupport
    (hasCompactSupport_kern_slice hρ.moll hε m p₂).norm)

/-- The pointwise bound for the family `Phi`. -/
theorem Phi_abs_le {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {W : ℝ → ℝ → ℝ} {G : ℝ → ℝ} {a b s₀ C : ℝ} (hab : a ≤ b)
    (hdom : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |W z θ| ≤ G θ)
    (hs : ∀ s ∈ Set.Ioo (s₀ - 1) (s₀ + 1), ∀ p₁ ∈ Set.Icc (-ε) ε,
      Real.exp (s - p₁) ∈ Set.Icc a b) (m : ℕ)
    (hC : ∀ p₂ : ℝ, ∫ p₁ : ℝ, ‖Work.Spaces.pzIter m (kern ρ ε) p₁ p₂‖ ≤ C) :
    ∀ s ∈ Set.Ioo (s₀ - 1) (s₀ + 1), ∀ {θ : ℝ}, θ ∈ Set.Ioo 0 (Real.pi / 2) → ∀ p₂ : ℝ,
      |Phi ρ ε W m s (θ, p₂)| ≤ C * G (Work.FTS.StrongEps.thShift θ p₂) := by
  intro s hsint θ hθ p₂
  have hGnn : 0 ≤ G (Work.FTS.StrongEps.thShift θ p₂) := by
    have h := hdom a (Set.left_mem_Icc.mpr hab) (Work.FTS.StrongEps.thShift θ p₂)
      (Work.FTS.StrongEps.thShift_mem hθ)
    linarith [abs_nonneg (W a (Work.FTS.StrongEps.thShift θ p₂))]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (hC p₂) hGnn)
  rw [Phi]
  rw [← Real.norm_eq_abs]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  rw [← MeasureTheory.integral_mul_const (G (Work.FTS.StrongEps.thShift θ p₂))
    (fun p₁ : ℝ => ‖Work.Spaces.pzIter m (kern ρ ε) p₁ p₂‖)]
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun p₁ => norm_nonneg _)
    ((integrable_kern_slice_norm hρ hε m p₂).mul_const _) ?_
  filter_upwards with p₁
  rw [norm_mul]
  by_cases hp₁ : p₁ ∈ Set.Icc (-ε) ε
  · have h2 := hdom (Real.exp (s - p₁)) (hs s hsint p₁ hp₁)
      (Work.FTS.StrongEps.thShift θ p₂) (Work.FTS.StrongEps.thShift_mem hθ)
    rw [Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  · have hp₁' : ε < |p₁| := by
      by_contra hc
      push_neg at hc
      exact hp₁ ⟨by linarith [neg_abs_le p₁, hc], by linarith [le_abs_self p₁, hc]⟩
    rw [pzIter_kern_eq_zero_of_eps_lt_abs (p₁ := p₁) hρ.moll hε m hp₁', norm_zero, zero_mul,
      zero_mul]

/-- The domination needed by `ParamIntegral`. -/
theorem exists_bound_data {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {W : ℝ → ℝ → ℝ} {G : ℝ → ℝ} {a b s₁ : ℝ} (hab : a ≤ b)
    (hdom : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |W z θ| ≤ G θ)
    (hint : Integrable (fun x : ℝ × ℝ => Work.Elliptic.sinCos2 x.1 *
      G (Work.FTS.StrongEps.thShift x.1 x.2)) (Mu ε))
    (hs : ∀ s ∈ Set.Ioo (s₁ - 1) (s₁ + 1), ∀ p₁ ∈ Set.Icc (-ε) ε,
      Real.exp (s - p₁) ∈ Set.Icc a b) :
    ∀ k : ℕ, ∃ B : ℝ × ℝ → ℝ, Integrable B (Mu ε) ∧ ∀ᵐ x ∂Mu ε,
      ∀ s ∈ Set.Ioo (s₁ - 1) (s₁ + 1),
        |Work.Elliptic.sinCos2 x.1 * Phi ρ ε W k s x| ≤ B x := by
  intro k
  obtain ⟨C, hC0, hC⟩ := exists_kern_slice_integral_le hρ hε k
  refine ⟨fun x => C * (Work.Elliptic.sinCos2 x.1 * G (Work.FTS.StrongEps.thShift x.1 x.2)),
    hint.const_mul C, ?_⟩
  filter_upwards [ae_fst_mem_Ioo (ε := ε)] with x hx s hsint
  have hsin0 : 0 ≤ Work.Elliptic.sinCos2 x.1 := by
    rw [Work.Elliptic.sinCos2]
    exact mul_nonneg (Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hx.1,
      by linarith [hx.2, Real.pi_pos]⟩) (sq_nonneg _)
  have h1 : |Phi ρ ε W k s x| ≤ C * G (Work.FTS.StrongEps.thShift x.1 x.2) :=
    Phi_abs_le hρ hε hab hdom hs k (fun p₂ => hC p₂) s hsint hx x.2
  rw [abs_mul, abs_of_nonneg hsin0]
  calc Work.Elliptic.sinCos2 x.1 * |Phi ρ ε W k s x|
      ≤ Work.Elliptic.sinCos2 x.1 * (C * G (Work.FTS.StrongEps.thShift x.1 x.2)) :=
        mul_le_mul_of_nonneg_left h1 hsin0
    _ = C * (Work.Elliptic.sinCos2 x.1 * G (Work.FTS.StrongEps.thShift x.1 x.2)) := by ring

/-! ### The main theorem -/

theorem FstarJepsSmooth {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {α : ℝ} {W : Work.FTS.Galerkin.Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen W) (hmem : Work.Spaces.HkMem α 1 W) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε W))
      (Set.Ioi 0) := by
  intro m
  rw [isOpen_Ioi.contDiffOn_iff]
  intro z₀ hz₀
  -- the log point and the interval data around it
  set s₀ : ℝ := Real.log z₀ with hs₀def
  have hz₀' : 0 < z₀ := hz₀
  set a : ℝ := Real.exp (s₀ - 1 - ε) with hadef
  set b : ℝ := Real.exp (s₀ + 1 + ε) with hbdef
  have ha : 0 < a := Real.exp_pos _
  have hab : a ≤ b := by
    rw [hadef, hbdef]
    exact Real.exp_le_exp.mpr (by linarith)
  obtain ⟨G, hGint, hGdom⟩ :=
    Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ZSliceDomination hsm hmem ha hab
  obtain ⟨G', hG'sm, hG'int, hG'eq, hGu, hGw, hGwG⟩ :=
    Work.FTS.StrongEps.EpsE4Thr.XBallLimAux.MajorantIntegrable hGint hε
  -- the range condition for `s` in the interval
  have hsrange : ∀ s ∈ Set.Ioo (s₀ - 1) (s₀ + 1), ∀ p₁ ∈ Set.Icc (-ε) ε,
      Real.exp (s - p₁) ∈ Set.Icc a b := by
    intro s hs p₁ hp₁
    obtain ⟨hs1, hs2⟩ := hs
    obtain ⟨hp1, hp2⟩ := hp₁
    rw [hadef, hbdef]
    exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr (by linarith)⟩
  -- the identity on the interval
  have hident : ∀ s ∈ Set.Ioo (s₀ - 1) (s₀ + 1),
      Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε W) (Real.exp s)
        = ∫ x : ℝ × ℝ, Work.Elliptic.sinCos2 x.1 * Phi ρ ε W 0 s x ∂Mu ε :=
    fun s hs => Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.FubiniSwap hρ.moll hε hsm
      hGdom hGwG s (hsrange s hs)
  -- the parametric integral
  have hmeas : ∀ k : ℕ, ∀ s : ℝ, AEStronglyMeasurable
      (fun x : ℝ × ℝ => Work.Elliptic.sinCos2 x.1 * Phi ρ ε W k s x) (Mu ε) := by
    intro k s
    refine AEStronglyMeasurable.mul ?_ (Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.PhiAEStronglyMeasurable
      hρ hε hsm k s)
    have hcont : Continuous fun x : ℝ × ℝ => Work.Elliptic.sinCos2 x.1 := by
      rw [show Work.Elliptic.sinCos2 = fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 from rfl]
      fun_prop
    exact hcont.aestronglyMeasurable
  have hderiv : ∀ k : ℕ, ∀ᵐ x ∂Mu ε, ∀ s : ℝ,
      HasDerivAt (fun s' => Work.Elliptic.sinCos2 x.1 * Phi ρ ε W k s' x)
        (Work.Elliptic.sinCos2 x.1 * Phi ρ ε W (k + 1) s x) s := by
    intro k
    filter_upwards [ae_fst_mem_Ioo (ε := ε)] with x hx
    intro s
    exact (hasDerivAt_Phi hρ hε hsm k s hx).const_mul _
  have hbound : ∀ k : ℕ, ∀ s₁ : ℝ, ∃ B : ℝ × ℝ → ℝ, Integrable B (Mu ε) ∧ ∀ᵐ x ∂Mu ε,
      ∀ s ∈ Set.Ioo (s₁ - 1) (s₁ + 1),
        |Work.Elliptic.sinCos2 x.1 * Phi ρ ε W k s x| ≤ B x := by
    intro k s₁
    set a₁ : ℝ := Real.exp (s₁ - 1 - ε) with ha₁def
    set b₁ : ℝ := Real.exp (s₁ + 1 + ε) with hb₁def
    have ha₁ : 0 < a₁ := Real.exp_pos _
    have hab₁ : a₁ ≤ b₁ := by
      rw [ha₁def, hb₁def]
      exact Real.exp_le_exp.mpr (by linarith)
    obtain ⟨G₁, hG₁int, hG₁dom⟩ :=
      Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ZSliceDomination hsm hmem ha₁ hab₁
    obtain ⟨G₁', hG₁'sm, hG₁'int, hG₁'eq, hG₁u, hG₁w, hG₁wG⟩ :=
      Work.FTS.StrongEps.EpsE4Thr.XBallLimAux.MajorantIntegrable hG₁int hε
    have hsrange₁ : ∀ s ∈ Set.Ioo (s₁ - 1) (s₁ + 1), ∀ p₁ ∈ Set.Icc (-ε) ε,
        Real.exp (s - p₁) ∈ Set.Icc a₁ b₁ := by
      intro s hs p₁ hp₁
      obtain ⟨hs1, hs2⟩ := hs
      obtain ⟨hp1, hp2⟩ := hp₁
      rw [ha₁def, hb₁def]
      exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr (by linarith)⟩
    exact exists_bound_data hρ hε hab₁ hG₁dom hG₁wG hsrange₁ k
  have hCD : ContDiff ℝ m (fun s : ℝ => ∫ x : ℝ × ℝ,
      Work.Elliptic.sinCos2 x.1 * Phi ρ ε W 0 s x ∂Mu ε) :=
    Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ParamIntegral
      (Φ := fun k s x => Work.Elliptic.sinCos2 x.1 * Phi ρ ε W k s x)
      hmeas hderiv hbound m
  -- transfer to `z`
  have hlog : ∀ᶠ z in 𝓝 z₀, Real.log z ∈ Set.Ioo (s₀ - 1) (s₀ + 1) := by
    have hl : ContinuousAt Real.log z₀ := Real.continuousAt_log (ne_of_gt hz₀')
    have hmem : Set.Ioo (s₀ - 1) (s₀ + 1) ∈ 𝓝 (Real.log z₀) :=
      isOpen_Ioo.mem_nhds (by rw [hs₀def]; exact ⟨by linarith, by linarith⟩)
    exact hl.preimage_mem_nhds hmem
  refine (hCD.contDiffAt.comp z₀ (Real.contDiffAt_log.mpr (ne_of_gt hz₀'))).congr_of_eventuallyEq ?_
  filter_upwards [hlog, isOpen_Ioi.mem_nhds hz₀'] with z hz hzpos
  rw [← Real.exp_log hzpos, hident (Real.log z) hz]
  simp only [Function.comp_apply, Real.log_exp]

end Work.FTS.StrongEps.EpsE4Thr.XBallLimAux
