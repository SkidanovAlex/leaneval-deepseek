import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.GalBasis.exists_cc_of_honClass
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le
import Submission.Work.FTS.StrongEps.EpsSqTools.HkSqJepsPzPre
import Submission.Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps
import Submission.Work.FTS.StrongEps.PZeroAux.bumpHkNormBound
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.zeroTermDth
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.classCThetaHolder
import Submission.Work.FTS_RegExport.RXR5L.coef_tau_lip
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.THL.vopPert_theta_holder
import Submission.Work.FTS_StreamBdry.Inputs.residual_slot_jetsB
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.EpsEngine.LocalStepEngine =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps

set_option autoImplicit false


end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.MeasAlt.IterMeas =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine.MeasAlt

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- The open quadrant. -/
private def Q0 : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

/-! ## Two elementary facts about a.e. strong measurability and restrictions -/

/-- Cutting a function off outside `s` preserves a.e. strong measurability, when it is known w.r.t.
the restricted measure. -/
theorem aesm_indicator_of_aesm_restrict {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) {f : α → ℝ}
    (h : MeasureTheory.AEStronglyMeasurable f (μ.restrict s)) :
    MeasureTheory.AEStronglyMeasurable (s.indicator f) μ := by
  obtain ⟨g, hg, hae⟩ := h
  have h1 : ∀ᵐ x ∂μ, x ∈ s → f x = g x := (ae_restrict_iff' hs).mp hae
  have hae' : s.indicator f =ᵐ[μ] s.indicator g := by
    filter_upwards [h1] with x hx
    by_cases hxs : x ∈ s
    · simp only [Set.indicator_of_mem hxs]; exact hx hxs
    · simp only [Set.indicator_of_notMem hxs]
  exact ((hg.aestronglyMeasurable.indicator hs)).congr hae'.symm



/-! ## The Carathéodory step -/



end Work.FTS.EpsEngine.MeasAlt
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.MeasAlt.aesm_slice_of_lipschitz_gate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.MeasAlt

open MeasureTheory Set Filter

open scoped Topology

set_option maxHeartbeats 1000000

/-! ## The dyadic approximation

For `τ_k s := min δ (⌊2 ^ k * s⌋₊ / 2 ^ k)` we need three things:

* `measurable_dyadicApprox` — for *arbitrary* `F`, `V`, `z`, `θ` the function
  `s ↦ F (V (τ_k s)) z θ` is measurable.  It is the composition of the measurable map
  `⌊2 ^ k ·⌋₊ : ℝ → ℕ` with an arbitrary function on the natural numbers (which are discrete), so
  no measurability of `s ↦ V s` is needed;
* `tau_mem` — `τ_k s ∈ [0,δ]` for `s ∈ [0,δ]` (so that `V (τ_k s) ∈ P`);
* `tau_sub_bounds` — `0 ≤ s - τ_k s ≤ 2^{-k}` on `[0,δ]`.
-/

/-- **The dyadic approximant of the curve is measurable.**  The composition of the measurable map
`⌊2 ^ k ·⌋₊ : ℝ → ℕ` with the arbitrary function `m ↦ F (V (min δ (m / 2 ^ k))) z θ` on the
discrete space `ℕ`. -/
private lemma measurable_dyadicApprox {F : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)} {V : ℝ → ℝ → ℝ → ℝ}
    {δ z θ : ℝ} (k : ℕ) :
    Measurable (fun s : ℝ =>
      F (V (min δ ((Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k))) z θ) := by
  have h : Measurable ((fun m : ℕ => F (V (min δ ((m : ℝ) / (2 : ℝ) ^ k))) z θ) ∘
      fun s : ℝ => Nat.floor ((2 : ℝ) ^ k * s)) :=
    (measurable_of_countable (fun m : ℕ => F (V (min δ ((m : ℝ) / (2 : ℝ) ^ k))) z θ)).comp
      (Nat.floor_mono.measurable.comp (measurable_const.mul measurable_id))
  simpa only [Function.comp_def] using h

/-- **The dyadic point stays in the horizon**: `min δ (⌊2 ^ k s⌋₊ / 2 ^ k) ∈ [0,δ]` when `δ ≥ 0`. -/
private lemma tau_mem {δ s : ℝ} (hδ : 0 ≤ δ) (k : ℕ) :
    min δ ((Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k) ∈ Set.Icc (0 : ℝ) δ := by
  have hq : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hfl : (0 : ℝ) ≤ (Nat.floor ((2 : ℝ) ^ k * s) : ℝ) := Nat.cast_nonneg _
  have hx : 0 ≤ (Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k := div_nonneg hfl hq.le
  exact ⟨le_min hδ hx, min_le_left _ _⟩

/-- **The dyadic point does not overshoot**: for `s ∈ [0,δ]` one has `τ_k s ≤ s` and
`s - τ_k s ≤ 2^{-k}`. -/
private lemma tau_sub_bounds {δ s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) δ) (k : ℕ) :
    min δ ((Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k) ≤ s ∧
    s - min δ ((Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k) ≤ ((2 : ℝ) ^ k)⁻¹ := by
  have hq : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hs0 : 0 ≤ s := hs.1
  have hfls : (Nat.floor ((2 : ℝ) ^ k * s) : ℝ) ≤ s * (2 : ℝ) ^ k := by
    rw [mul_comm s]; exact Nat.floor_le (mul_nonneg hq.le hs0)
  have hle : (Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k ≤ s := by
    rw [div_le_iff₀ hq]; exact hfls
  have hmin : min δ ((Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k)
      = (Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k := min_eq_right (hle.trans hs.2)
  constructor
  · rw [hmin]; exact hle
  · rw [hmin]
    have hcast : s * (2 : ℝ) ^ k < (Nat.floor ((2 : ℝ) ^ k * s) : ℝ) + 1 := by
      rw [mul_comm s ((2 : ℝ) ^ k)]; exact Nat.lt_floor_add_one _
    have hone : ((2 : ℝ) ^ k)⁻¹ * (2 : ℝ) ^ k = 1 := inv_mul_cancel₀ (ne_of_gt hq)
    have key : s - ((2 : ℝ) ^ k)⁻¹ ≤ (Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k := by
      rw [le_div_iff₀ hq]
      have hexp : (s - ((2 : ℝ) ^ k)⁻¹) * (2 : ℝ) ^ k = s * (2 : ℝ) ^ k - 1 := by
        rw [sub_mul, hone]
      rw [hexp]
      linarith [hcast]
    linarith [key]

/-- **The Lipschitz gate against the curve itself**: on `[0,δ]` the dyadic approximant differs
from `F (V s) z θ` by at most `Cpt · √Lb · 2^{-k}`, at a point of the open quadrant. -/
private lemma lip_bound {F : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)} {V : ℝ → ℝ → ℝ → ℝ}
    {P : (ℝ → ℝ → ℝ) → Prop} {α δ Cpt Lb z θ : ℝ}
    (hδ : 0 ≤ δ) (hLb : 0 ≤ Lb) (hCpt : 0 ≤ Cpt)
    (hV : ∀ s ∈ Set.Icc 0 δ, P (V s))
    (hpt : ∀ u v : ℝ → ℝ → ℝ, P u → P v → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F u z θ - F v z θ|
        ≤ Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)))
    (hdc : ∀ s t : ℝ, s ∈ Set.Icc 0 δ → t ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsSq α (fun z θ => V s z θ - V t z θ) ≤ Lb * (s - t) ^ 2)
    (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < Real.pi / 2)
    {s : ℝ} (hs : s ∈ Set.Icc 0 δ) (k : ℕ) :
    |F (V (min δ ((Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k))) z θ - F (V s) z θ|
      ≤ Cpt * Real.sqrt Lb * ((2 : ℝ) ^ k)⁻¹ := by
  set τ := min δ ((Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k) with hτdef
  have hτmem : τ ∈ Set.Icc (0 : ℝ) δ := by simpa only [hτdef] using tau_mem (δ := δ) hδ k
  have htb := tau_sub_bounds (δ := δ) hs k
  rw [← hτdef] at htb
  have hEps : Work.FTS.StrongEps.EpsSq α (fun z θ => V τ z θ - V s z θ) ≤ Lb * (s - τ) ^ 2 := by
    have h := hdc τ s hτmem hs
    rwa [show (τ - s) ^ 2 = (s - τ) ^ 2 from by ring] at h
  have hsqrt : Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => V τ z θ - V s z θ))
      ≤ Real.sqrt (Lb * (s - τ) ^ 2) := Real.sqrt_le_sqrt hEps
  have hbound : Real.sqrt (Lb * (s - τ) ^ 2) = Real.sqrt Lb * |s - τ| := by
    rw [Real.sqrt_mul hLb, Real.sqrt_sq_eq_abs]
  have hdiff : |s - τ| ≤ ((2 : ℝ) ^ k)⁻¹ := by
    rw [abs_of_nonneg (sub_nonneg.mpr htb.1)]
    exact htb.2
  calc |F (V τ) z θ - F (V s) z θ|
      ≤ Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => V τ z θ - V s z θ)) :=
        hpt (V τ) (V s) (hV τ hτmem) (hV s hs) z θ hz hθ1 hθ2
    _ ≤ Cpt * Real.sqrt (Lb * (s - τ) ^ 2) := mul_le_mul_of_nonneg_left hsqrt hCpt
    _ = Cpt * (Real.sqrt Lb * |s - τ|) := by rw [hbound]
    _ ≤ Cpt * (Real.sqrt Lb * ((2 : ℝ) ^ k)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ hCpt
        exact mul_le_mul_of_nonneg_left hdiff (Real.sqrt_nonneg _)
    _ = Cpt * Real.sqrt Lb * ((2 : ℝ) ^ k)⁻¹ := by ring

/-- **Measurability in the time variable, from the Lipschitz gate alone** (the
rational-approximation step of the fallback for `EpsEngine.hmeasIter_of_epsClass`).

`V : ℝ → Fn` is a curve of profiles whose values on `[0,δ]` lie in a class `P` on which `F` is
continuous on the open quadrant, vanishes off it, and is pointwise Lipschitz w.r.t. the `EpsSq`
metric (`hpt`).  If moreover `V` is `EpsSq`-Lipschitz in the time variable on `[0,δ]` (`hdc`), then
for every fixed `(z,θ)` the function `s ↦ F (V s) z θ` is a.e. strongly measurable on `[0,δ]`.

Proof (dyadic approximation *against the curve itself*, so no convexity/density/separability is
involved): let `τ_k s := min δ (Nat.floor (2 ^ k * s) / 2 ^ k)`, which on `[0,δ]` takes values in
the *finite* set `{min δ (m / 2 ^ k) : m ≤ Nat.floor (2 ^ k * δ)}` and satisfies
`0 ≤ s - τ_k s ≤ 2^{-k}`; hence
`g_k s := if s ∈ Set.Icc 0 δ then F (V (τ_k s)) z θ else 0` is measurable (a finite sum of
indicators of the measurable level sets `{s ∈ Icc 0 δ : Nat.floor (2 ^ k * s) = m}` times the
constants `F (V (min δ (m / 2 ^ k))) z θ`), and it converges pointwise on `Icc 0 δ` to
`s ↦ F (V s) z θ` by `hpt` + `hdc`; conclude with `aestronglyMeasurable_of_tendsto_ae`. -/
theorem aesm_slice_of_lipschitz_gate {F : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)} {V : ℝ → ℝ → ℝ → ℝ}
    {P : (ℝ → ℝ → ℝ) → Prop} {α δ Cpt Lb : ℝ}
    (hδ : 0 ≤ δ) (hLb : 0 ≤ Lb) (hCpt : 0 ≤ Cpt)
    (hV : ∀ s ∈ Set.Icc 0 δ, P (V s))
    (hcont : ∀ w : ℝ → ℝ → ℝ, P w → ContinuousOn (fun q : ℝ × ℝ => F w q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hzero : ∀ (w : ℝ → ℝ → ℝ) (q : ℝ × ℝ),
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → F w q.1 q.2 = 0)
    (hpt : ∀ u v : ℝ → ℝ → ℝ, P u → P v → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F u z θ - F v z θ|
        ≤ Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)))
    (hdc : ∀ s t : ℝ, s ∈ Set.Icc 0 δ → t ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsSq α (fun z θ => V s z θ - V t z θ) ≤ Lb * (s - t) ^ 2) :
    ∀ z θ : ℝ, MeasureTheory.AEStronglyMeasurable (fun s : ℝ => F (V s) z θ)
      (MeasureTheory.volume.restrict (Set.Icc 0 δ)) := by
  classical
  intro z θ
  by_cases hq : 0 < z ∧ 0 < θ ∧ θ < Real.pi / 2
  · -- on the open quadrant: dyadic approximation against the curve itself
    obtain ⟨hz, hθ1, hθ2⟩ := hq
    have hmeas : ∀ k : ℕ, Measurable (fun s : ℝ =>
        F (V (min δ ((Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k))) z θ) :=
      fun k => measurable_dyadicApprox k
    have hlim : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc 0 δ)),
        Tendsto (fun k : ℕ =>
            F (V (min δ ((Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k))) z θ)
          atTop (nhds (F (V s) z θ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have ht : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) atTop (nhds 0) :=
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).inv_tendsto_atTop
      have ht2 : Tendsto (fun k : ℕ => (Cpt * Real.sqrt Lb) * ((2 : ℝ) ^ k)⁻¹)
          atTop (nhds 0) := by
        have h2 := ht.const_mul (Cpt * Real.sqrt Lb)
        simpa only [mul_zero] using h2
      refine squeeze_zero (g := fun k : ℕ => (Cpt * Real.sqrt Lb) * ((2 : ℝ) ^ k)⁻¹)
        (fun k => norm_nonneg _) (fun k => ?_) ht2
      rw [Real.norm_eq_abs]
      exact lip_bound hδ hLb hCpt hV hpt hdc hz hθ1 hθ2 hs k
    exact aestronglyMeasurable_of_tendsto_ae atTop
      (fun k => (hmeas k).aestronglyMeasurable) hlim
  · -- off the open quadrant `F (V s) z θ` vanishes identically
    have hzall : ∀ s : ℝ, F (V s) z θ = 0 := by
      intro s
      have hmem : (z, θ) ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := by
        intro hmem
        exact hq (by simpa only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] using hmem)
      exact hzero (V s) (z, θ) hmem
    rw [show (fun s : ℝ => F (V s) z θ) = fun _ => (0 : ℝ) from funext hzall]
    exact aestronglyMeasurable_const

end Work.FTS.EpsEngine.MeasAlt
end
-- ===== merged: Submission.Work.FTS.EpsEngine.continuousOn_Feps_of_epsClass =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open Work.FTS.Galerkin (Fn)

/-- **The pointwise unfolding of `profRHS`**: the pre-mollified right-hand side is the linear part
plus the four blocks `-μ̄·AK α`, `N₀`, `N`, `N_*` of the `g`-equation (`Construction.gRHS`), with
the modulation constants `μ̄ = mubarOf`, `μ = muOf`, `lam = lamfun μ` of the profile.  This is the
form in which the smoothness of `profRHS` is assembled. -/
theorem profRHS_apply_eq (α : ℝ) (Φs : Fn) (E : Fn → Fn) (u : Fn) (z θ : ℝ) :
    Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E u z θ
      = Work.FTS.StrongPersist.linPart α u z θ
        + (-(Work.FTS.StrongEps.EpsRLX.mubarOf α Φs E u) * Work.Construction.AK α z θ
          + Work.Construction.N0 α (Work.Construction.Ftot α u) u z θ
          + Work.Construction.N α (Work.Construction.Ftot α u)
              (fun z θ => Φs z θ + E u z θ) z θ
          + Work.Construction.Nstar (Work.FTS.StrongEps.EpsRLX.muOf α Φs E u)
              (Work.Construction.lamfun (Work.FTS.StrongEps.EpsRLX.muOf α Φs E u)) u z θ) := rfl

/-- **`profRHS` is `C^∞` on the open quadrant at every class-`C` profile.**  The analytic inputs
are the open-quadrant smoothness of the profile itself (`ClassC.reg`), the elliptic package of the
profile (`hEll`), the star package of `Φs` (`hstar`) and the smoothness of the four blocks of
`gRHS`; the modulation constants are *numbers*, so no `MuLamOK`/`HkNorm` bound is needed for the
regularity. -/
theorem smoothOpen_profRHS_of_classC {α Ce Cs : ℝ} {Φs : Fn} {E : Fn → Fn} {W : Fn}
    (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hW : Work.FTS.ClassC.ClassC α W) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W) := by
  have hEllW : Work.FTS.VocabO.EllPkgGo α Ce W (E W) := (hEll W hW).1
  obtain ⟨-, -, hLGsmo, hN0smo, hNsmo⟩ :=
    Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα.1 hα.2 hW hEllW hstar
  -- the linear part `linPart α W = -(L_Γ^T W)`
  have hnegL : Work.FTS.EllipticEst.SmoothOpen (fun z θ => -Work.Coercivity.LGammaT α W z θ) :=
    hLGsmo.neg
  have hLinsmo : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongPersist.linPart α W) := by
    refine Work.FTS.EllipticEst.SmoothOpen.congr hnegL (fun z θ _ _ _ => ?_)
    simp only [Work.FTS.StrongPersist.linPart]
  -- the `-μ̄·AK α` block
  have hAKsmo : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      -(Work.FTS.StrongEps.EpsRLX.mubarOf α Φs E W) * Work.Construction.AK α z θ) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul _ (Work.FTS.StrongPersist.AK_smoothO α)
  -- the `N_*` block
  have hNssmo : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Nstar (Work.FTS.StrongEps.EpsRLX.muOf α Φs E W)
        (Work.Construction.lamfun (Work.FTS.StrongEps.EpsRLX.muOf α Φs E W)) W) :=
    Work.FTS.GalFields.RHS.smoothOpen_Nstar_of hW.reg
  -- the nonlinear block `gRHS`
  have hkeysmo : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      -(Work.FTS.StrongEps.EpsRLX.mubarOf α Φs E W) * Work.Construction.AK α z θ
        + Work.Construction.N0 α (Work.Construction.Ftot α W) W z θ
        + Work.Construction.N α (Work.Construction.Ftot α W)
            (fun z θ => Φs z θ + E W z θ) z θ
        + Work.Construction.Nstar (Work.FTS.StrongEps.EpsRLX.muOf α Φs E W)
            (Work.Construction.lamfun (Work.FTS.StrongEps.EpsRLX.muOf α Φs E W)) W z θ) :=
    ((hAKsmo.add hN0smo).add hNsmo).add hNssmo
  have hsumsmo : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      Work.FTS.StrongPersist.linPart α W z θ
        + (-(Work.FTS.StrongEps.EpsRLX.mubarOf α Φs E W) * Work.Construction.AK α z θ
          + Work.Construction.N0 α (Work.Construction.Ftot α W) W z θ
          + Work.Construction.N α (Work.Construction.Ftot α W)
              (fun z θ => Φs z θ + E W z θ) z θ
          + Work.Construction.Nstar (Work.FTS.StrongEps.EpsRLX.muOf α Φs E W)
              (Work.Construction.lamfun (Work.FTS.StrongEps.EpsRLX.muOf α Φs E W)) W z θ)) :=
    hLinsmo.add hkeysmo
  refine Work.FTS.EllipticEst.SmoothOpen.congr hsumsmo (fun z θ _ _ _ => ?_)
  exact (profRHS_apply_eq α Φs E W z θ).symm


end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Flow5Leaves.PzJepsCalc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Flow5Leaves/PzJepsCalc.lean` — linearity and pricing of the projected mollifier `Pz ∘ J_ε`

The three facts about `W_ε = Pz ∘ J_ε` that the level-four product rule
(`Flow5Leaves/IP4_JfamP_hasDerivWithinAt_of_flow.lean`) consumes:

* `Pz_const_mul`      — `Pz` commutes with multiplication by a scalar (`L₁₂` is homogeneous,
                        `GalBasis.L12_const_mul`);
* `PzJeps_const_mul`  — `W_ε` is homogeneous (`EpsE4Work.Jeps_smul` + the previous);
* `PzJeps_pricing`    — `W_ε f ∈ HQo α 4` and `‖W_ε f‖_{ℋ⁴} ≤ K ‖f‖_{ℋ⁶}` (`PzHkNormFour` +
                        `HkSq_Jeps_le` + monotonicity of the norm in the order).

Nothing here is analytic beyond the two cited estimates.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Flow5Leaves

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`Pz` commutes with multiplication by a scalar** (`L₁₂` is homogeneous,
`GalBasis.L12_const_mul`). -/
theorem Pz_const_mul (c : ℝ) (f : Fn) :
    Work.FTS.StrongEps.Pz (fun z θ => c * f z θ)
      = fun z θ => c * Work.FTS.StrongEps.Pz f z θ := by
  funext z θ
  rw [Work.FTS.StrongEps.Pz_apply, Work.FTS.StrongEps.Pz_apply,
    Work.FTS.GalBasis.L12_const_mul c f 0]
  ring

/-- **The projected mollifier is homogeneous**: `Pz (J_ε (c • f)) = c • Pz (J_ε f)`
(`Jeps_smul` + `Pz_const_mul`). -/
theorem PzJeps_const_mul (ρ : ℝ × ℝ → ℝ) (ε c : ℝ) (f : Fn) :
    Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (fun z θ => c * f z θ))
      = fun z θ => c * Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f) z θ := by
  have h : (fun z θ => c * f z θ) = c • f := by
    funext z θ
    simp only [Pi.smul_apply, smul_eq_mul]
  have h2 : c • Work.FTS.StrongEps.Jeps ρ ε f
      = fun z θ => c * Work.FTS.StrongEps.Jeps ρ ε f z θ := by
    funext z θ
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [h, Work.FTS.StrongEps.EpsE4Work.Jeps_smul, h2,
    Pz_const_mul c (Work.FTS.StrongEps.Jeps ρ ε f)]

/-- **Pricing of the projected mollified profile**: `Pz (J_ε f)` is honestly `ℋ⁴` and its
`ℋ⁴`-norm is controlled by the `ℋ⁶`-norm of `f`.  (`PzHkNormFour` gives the `ℋ⁴`-boundedness of
`Pz`, `HkSq_Jeps_le` the `E1`-boundedness of `J_ε`, and the `ℋ⁶`-input is read through the
monotonicity of the norm in the order.) -/
theorem PzJeps_pricing {α ε : ℝ} {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ {f : Fn}, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 6 f →
      Work.FTS.VocabO.HQo α 4 (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f)) ∧
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f))
        ≤ K * Work.Spaces.HkNorm α 6 f := by
  obtain ⟨A, hApos, hA⟩ := Work.FTS.StrongEps.PZeroAux.PzHkNormFour
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.HkSq_Jeps_le ρ hρ.moll
  refine ⟨A * Real.exp (C / 2) + 1, by positivity, ?_⟩
  intro f hsm hm6
  have hsmc : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsm
  have hm4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 4 (by norm_num) hm6
  have hsmJ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε f) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hsmc
  have hmJ4 : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε f) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε hsmc hm4
  refine ⟨⟨Work.FTS.StrongEps.EpsLocalPStar.smoothOpen_Pz hsmJ,
    Work.FTS.StrongEps.PZeroAux.PzJepsHkMem 4 hρ hα hε hsmc hm4⟩, ?_⟩
  have hJ := hC α hα 4 ε hε hε1 f hsmc hm4 hmJ4
  have hsqrt : Real.sqrt (Real.exp (C * ε)) = Real.exp (C * ε / 2) := by
    have h2 : (Real.exp (C * ε / 2)) ^ 2 = Real.exp (C * ε) := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [← h2, Real.sqrt_sq_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  have hNJ : Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.Jeps ρ ε f)
      ≤ Real.exp (C / 2) * Work.Spaces.HkNorm α 6 f := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.Jeps ρ ε f))
        ≤ Real.sqrt (Real.exp (C * ε) * Work.Spaces.HkSq α 4 f) := Real.sqrt_le_sqrt hJ
      _ = Real.sqrt (Real.exp (C * ε)) * Real.sqrt (Work.Spaces.HkSq α 4 f) :=
          Real.sqrt_mul (Real.exp_pos _).le _
      _ = Real.exp (C * ε / 2) * Real.sqrt (Work.Spaces.HkSq α 4 f) := by rw [hsqrt]
      _ ≤ Real.exp (C / 2) * Real.sqrt (Work.Spaces.HkSq α 6 f) := by
          refine mul_le_mul (Real.exp_le_exp.mpr ?_) (Real.sqrt_le_sqrt ?_)
            (Real.sqrt_nonneg _) (Real.exp_pos _).le
          · have hε0 : 0 ≤ ε := hε.le
            nlinarith [hCpos, hε1, hε0]
          · have h45 : Work.Spaces.HkSq α 4 f ≤ Work.Spaces.HkSq α 5 f :=
              Work.Coercivity.HkSq_mono α 4
                (Work.FTS.OpenPkg.HkMem_mono_open hsm 5 (by norm_num) hm6)
            have h56 : Work.Spaces.HkSq α 5 f ≤ Work.Spaces.HkSq α 6 f :=
              Work.Coercivity.HkSq_mono α 5 hm6
            exact le_trans h45 h56
      _ = Real.exp (C / 2) * Work.Spaces.HkNorm α 6 f := rfl
  calc Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f))
      ≤ A * Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.Jeps ρ ε f) :=
        hA α hα 4 le_rfl _ hsmJ hmJ4
    _ ≤ A * (Real.exp (C / 2) * Work.Spaces.HkNorm α 6 f) :=
        mul_le_mul_of_nonneg_left hNJ hApos.le
    _ ≤ (A * Real.exp (C / 2) + 1) * Work.Spaces.HkNorm α 6 f := by
        have h6 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
        have he : (0 : ℝ) < Real.exp (C / 2) := Real.exp_pos _
        nlinarith

end Work.FTS.StrongEps.E4R3.Flow5Leaves
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.rem_eq_intervalIntegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits

/-!
# `rem_eq_intervalIntegral` — the remainder of the fake-time increment is the interval
integral of the (shifted) right-hand side

`rem u v s τ = u s - u τ - (s - τ) • v` is the remainder of the first-order expansion of a curve
of profiles at fake time `τ` with derivative `v` (`E4R5.rem`).  For a family `g` whose fake-time
increment is *volterra* — `g z θ t = g z θ 0 + ∫₀^t Feps (slice g u) z θ du` on `[0,δ]` — the
remainder is exactly the integral over `[τ,s]` of the difference
`Feps (slice g u) - Feps (slice g τ)`.

The proof is the fundamental theorem of calculus in its "interval difference" form: two
primitives differ by the integral over the interval between the two base points, and the integral
of a constant is `(s - τ) • c`.
-/

/-- **Interval difference of a primitive.**  If `F` is a primitive of `f` on `[0,δ]` with base
point `0` (i.e. `F t = C + ∫₀^t f` for `t ∈ [0,δ]`) and `f` is interval integrable on `[0,δ]`,
then for any two points `a`, `b` of `[0,δ]`,
`F b - F a = ∫_a^b f`.

(The extra flexibility of arbitrary *signed* base points is what makes this usable for the
oriented integral `∫_τ^s`: when `s < τ` both sides change sign.) -/
theorem sub_eq_intervalIntegral_of_primitive {f : ℝ → ℝ} {F : ℝ → ℝ} {δ C : ℝ}
    (hF : ∀ t ∈ Set.Icc (0 : ℝ) δ, F t = C + ∫ u in (0 : ℝ)..t, f u)
    (hint : IntervalIntegrable f MeasureTheory.volume 0 δ)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) δ) (hb : b ∈ Set.Icc (0 : ℝ) δ) :
    F b - F a = ∫ u in a..b, f u := by
  have hδ0 : (0 : ℝ) ≤ δ := le_trans ha.1 ha.2
  have hIa : IntervalIntegrable f MeasureTheory.volume 0 a :=
    hint.mono_set (by
      rw [Set.uIcc_of_le ha.1, Set.uIcc_of_le hδ0]
      exact Set.Icc_subset_Icc le_rfl ha.2)
  have hIb : IntervalIntegrable f MeasureTheory.volume 0 b :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hb.1, Set.uIcc_of_le hδ0]
      exact Set.Icc_subset_Icc le_rfl hb.2)
  have hkey := intervalIntegral.integral_interval_sub_left hIb hIa
  rw [← hkey, hF b hb, hF a ha]
  ring

theorem rem_eq_intervalIntegral {α δ ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hvol : ∀ z θ τ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → τ ∈ Set.Icc 0 δ →
      g z θ τ = g z θ 0 + ∫ s in (0 : ℝ)..τ,
        Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) z θ)
    (hint : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      IntervalIntegrable (fun u : ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E
        (Work.FTS.Galerkin.slice g u) z θ) MeasureTheory.volume 0 δ)
    {s τ z θ : ℝ} (hs : s ∈ Set.Icc 0 δ) (hτ : τ ∈ Set.Icc 0 δ)
    (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.FTS.StrongEps.EpsE4Thr.E4R5.rem (Work.FTS.Galerkin.slice g)
        (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ)) s τ z θ
      = ∫ u in τ..s, (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g u) z θ
          - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ) := by
  have hprim : ∀ t ∈ Set.Icc (0 : ℝ) δ,
      g z θ t = g z θ 0 + ∫ u in (0 : ℝ)..t, Work.FTS.EpsEngine.Feps α ρ ε Φs E
        (Work.FTS.Galerkin.slice g u) z θ := fun t ht => hvol z θ t hzθ ht
  have hdiff : g z θ s - g z θ τ = ∫ u in τ..s, Work.FTS.EpsEngine.Feps α ρ ε Φs E
      (Work.FTS.Galerkin.slice g u) z θ :=
    sub_eq_intervalIntegral_of_primitive hprim (hint z θ hzθ) hτ hs
  -- the integrand is interval integrable on the (oriented) interval `τ..s`
  have hintτs : IntervalIntegrable (fun u : ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E
      (Work.FTS.Galerkin.slice g u) z θ) MeasureTheory.volume τ s := by
    refine (hint z θ hzθ).mono_set' ?_
    intro x hx
    rw [Set.mem_uIoc] at hx ⊢
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨lt_of_le_of_lt hτ.1 h1, le_trans h2 hs.2⟩
    · exact Or.inl ⟨lt_of_le_of_lt hs.1 h1, le_trans h2 hτ.2⟩
  have hcint : IntervalIntegrable (fun _ : ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E
      (Work.FTS.Galerkin.slice g τ) z θ) MeasureTheory.volume τ s := intervalIntegrable_const
  -- integral of the difference = difference of the integrals = the remainder
  have hsub : ∫ u in τ..s, (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g u) z θ
          - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ)
      = (g z θ s - g z θ τ) - (s - τ) * Work.FTS.EpsEngine.Feps α ρ ε Φs E
          (Work.FTS.Galerkin.slice g τ) z θ := by
    rw [intervalIntegral.integral_sub hintτs hcint, hdiff.symm, intervalIntegral.integral_const,
      smul_eq_mul]
  rw [hsub]
  simp only [Work.FTS.StrongEps.EpsE4Thr.E4R5.rem, Work.FTS.Galerkin.slice_apply]

end Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits
end
-- ===== merged: Submission.Work.FTS.StrongEps.IsEpsSolPQ.EpsSq_intervalIntegral_le_sqrt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.IsEpsSolPQ

open Work.FTS.StrongEps.EpsLocalPStar

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-- `EpsSq` is the single integral of the weighted square against the product measure
`DomM = (volume↾Iz).prod (volume↾Iθ)` (Fubini for the iterated set integral). -/
private theorem EpsSq_eq_integral_DomM_prv {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsMem α f) :
    Work.FTS.StrongEps.EpsSq α f
      = ∫ p : ℝ × ℝ, (f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2 ∂DomM := by
  have hint : Integrable (fun p : ℝ × ℝ =>
      (f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) DomM :=
    EpsMem_iff_integrable2.mp hf
  rw [Work.FTS.StrongEps.EpsSq, DomM]
  exact (MeasureTheory.integral_prod _ hint).symm

theorem EpsSq_intervalIntegral_le_sqrt {α a b B : ℝ} (hab : a ≤ b) (hB : 0 ≤ B)
    {w : Work.FTS.Galerkin.Fn} {G : ℝ → Work.FTS.Galerkin.Fn}
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => G q.1 q.2.1 q.2.2 * Work.FTS.StrongEps.epsW α q.2.1 q.2.2)
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        Work.FTS.StrongEps.EpsLocalPStar.DomM))
    (hGmem : Filter.Eventually (fun s : ℝ => Work.FTS.StrongEps.EpsMem α (G s))
      (MeasureTheory.ae (MeasureTheory.volume.restrict (Set.uIoc a b))))
    (hBd : Filter.Eventually (fun s : ℝ => Work.FTS.StrongEps.EpsSq α (G s) ≤ B)
      (MeasureTheory.ae (MeasureTheory.volume.restrict (Set.uIoc a b))))
    (hwmem : Work.FTS.StrongEps.EpsMem α w)
    (hw : Filter.Eventually (fun p : ℝ × ℝ => w p.1 p.2 = ∫ s in a..b, G s p.1 p.2)
      (MeasureTheory.ae Work.FTS.StrongEps.EpsLocalPStar.DomM)) :
    Work.FTS.StrongEps.EpsSq α w
      ≤ (∫ s in a..b, Real.sqrt (Work.FTS.StrongEps.EpsSq α (G s))) ^ 2 := by
  classical
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  -- the weighted curve, as a function of the pair `(s, p)`
  set F : ℝ → ℝ × ℝ → ℝ :=
    fun s p => G s p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2 with hF
  -- the parameter measure is finite
  haveI hνfin : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc a b)) := ⟨by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_uIoc,
      abs_of_nonneg hba]
    exact ENNReal.ofReal_lt_top⟩
  -- the interval integral of a profile is the integral of its weighted slice: the weight is
  -- constant in the parameter
  have hslice : ∀ p : ℝ × ℝ, (∫ s in a..b, G s p.1 p.2) * Work.FTS.StrongEps.epsW α p.1 p.2
      = ∫ s, F s p ∂(MeasureTheory.volume.restrict (Set.uIoc a b)) := by
    intro p
    rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab, hF]
    exact (MeasureTheory.integral_mul_const (Work.FTS.StrongEps.epsW α p.1 p.2)
      (fun s => G s p.1 p.2)).symm
  -- a.e. in `s`, the integral of the weighted square is the energy of the slice
  have hsq_eq : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
      (∫ p, F s p ^ 2 ∂DomM) = Work.FTS.StrongEps.EpsSq α (G s) := by
    refine hGmem.mono fun s hs => ?_
    rw [EpsSq_eq_integral_DomM_prv hs, hF]
  -- a.e. strong measurability of the slice energy
  have haesm : MeasureTheory.AEStronglyMeasurable (fun s => ∫ p, F s p ^ 2 ∂DomM)
      (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    (hmeas.pow 2).integral_prod_right'
  -- the size is bounded by `√B` on the (finite) interval, hence integrable
  have hbdd : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
      ‖Real.sqrt (∫ p, F s p ^ 2 ∂DomM)‖ ≤ Real.sqrt B := by
    filter_upwards [hsq_eq, hBd] with s heq hle
    rw [heq, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_le_sqrt_iff hB).mpr hle
  have hint : Integrable (fun s => Real.sqrt (∫ p, F s p ^ 2 ∂DomM))
      (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    Integrable.of_bound (Real.continuous_sqrt.comp_aestronglyMeasurable haesm) (Real.sqrt B) hbdd
  -- the slices are square-integrable a.e. in the parameter
  have hsq : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
      Integrable (fun p : ℝ × ℝ => F s p ^ 2) DomM :=
    hGmem.mono fun s hs => EpsMem_iff_integrable2.mp hs
  -- Minkowski's inequality for the `L²`-norm of the parameter integral
  obtain ⟨_, hmink⟩ := l2_integral_le (μ := DomM)
    (ν := MeasureTheory.volume.restrict (Set.uIoc a b)) (F := F) hmeas hsq hint
  -- the left-hand side is the norm of the parameter integral
  have hLHS : Work.FTS.StrongEps.EpsSq α w
      = ∫ p, (∫ s, F s p ∂(MeasureTheory.volume.restrict (Set.uIoc a b))) ^ 2 ∂DomM := by
    rw [EpsSq_eq_integral_DomM_prv hwmem]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hw] with p hp
    rw [hp, hslice p]
  -- the right-hand side is the interval integral of the slice sizes
  have hRHS : (∫ s, Real.sqrt (∫ p, F s p ^ 2 ∂DomM)
        ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))
      = ∫ s in a..b, Real.sqrt (Work.FTS.StrongEps.EpsSq α (G s)) := by
    have h' := hsq_eq
    rw [Set.uIoc_of_le hab] at h'
    rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab]
    exact MeasureTheory.integral_congr_ae (h'.mono fun s hs => congrArg Real.sqrt hs)
  calc Work.FTS.StrongEps.EpsSq α w
      = ∫ p, (∫ s, F s p ∂(MeasureTheory.volume.restrict (Set.uIoc a b))) ^ 2 ∂DomM := hLHS
    _ ≤ (∫ s, Real.sqrt (∫ p, F s p ^ 2 ∂DomM)
          ∂(MeasureTheory.volume.restrict (Set.uIoc a b))) ^ 2 := hmink
    _ = (∫ s in a..b, Real.sqrt (Work.FTS.StrongEps.EpsSq α (G s))) ^ 2 := by rw [hRHS]

end Work.FTS.StrongEps.IsEpsSolPQ
end
end
