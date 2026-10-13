/-
Copyright: work module for the Elgindi finite-time singularity project.

# The **corrected** angular truncated identity `truncThetaIbpSep`

The requested lemma `I1Wk.truncThetaIbp` (see `truncThetaIbp.lean`) is **false as stated**: the
angular integration by parts carries a boundary bracket
`B θ = σθ ψθ vθ v'θ - η σθ cos2θ/sin2θ ψθ vθ² - (1/2)σθ ψ'θ vθ²` which the hypotheses
(`support ψ ⊆ Ioo 0 (π/2)`, `HasCompactSupport ψ`, `u` only `C^∞` on the *open* quadrant) do not
force to vanish.  `I1Wk/NOTES_truncThetaIbp_FALSE.md` records the counterexample
`u (z,θ) = z θ^{-3/5}` (there `LHS = 0` while `RHS = -2η·(positive) < 0`).

This file proves the **true** statement: the same identity with the hypothesis

  `hψsep : ∃ a b, 0 < a ∧ a < b ∧ b < π/2 ∧ tsupport ψ ⊆ Ioo a b`

(use `tsupport`, the *closed* support, not `support`).  Then `ψ` and `ψ'` vanish on a
neighbourhood of both corners, every integrand is supported in `tsupport χ × [a,b]` where `u`'s
derivatives are continuous (hence bounded), so all integrals are honest and the bracket
vanishes.  This is exactly the situation of the intended application, where `ψ = ψ_δ` runs
through a family of smooth bumps with `tsupport ψ_δ ⊆ (δ/2, π/2-δ/2)`.

Two forms are provided:

* `truncThetaIbpSep` — the RHS as a *single* iterated integral of the combined integrand (no
  integrability hypothesis at all);
* `truncThetaIbpSep_split` — the RHS in the *exact* shape of the requested statement (four
  separate iterated integrals), assuming the four outer `z`-integrands are `IntegrableOn Ioi 0`.

The mathematical heart is `I1Wk.sliceThetaIbpSep` (the 1-D slice identity `S2`), proved in
`sibling file: sliceThetaIbpSep.lean`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_second_trunc
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.sliceThetaIbpSep2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Elementary facts -/

lemma sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])

/-- A function continuous on `[a,b]` and vanishing off `[a,b]` is `IntegrableOn (0,π/2)`. -/
lemma integrableOn_Ioo_of_compact_support {a b : ℝ} {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hzero : ∀ θ, θ ∉ Set.Icc a b → f θ = 0) :
    MeasureTheory.IntegrableOn f (Set.Ioo 0 (Real.pi / 2)) := by
  have hInd : MeasureTheory.Integrable ((Set.Icc a b).indicator f) MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
      (hcont.integrableOn_compact isCompact_Icc)
  have hfun : (Set.Icc a b).indicator f
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))] f := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ _
    by_cases h : θ ∈ Set.Icc a b
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h]
      exact (hzero θ h).symm
  exact MeasureTheory.Integrable.congr (hInd.integrableOn (s := Set.Ioo 0 (Real.pi / 2))) hfun

/-- `ψ` vanishes off `[a,b]` when `tsupport ψ ⊆ (a,b)`. -/
lemma eq_zero_of_tsupport_subset {ψ : ℝ → ℝ} {a b : ℝ} (hsupp : tsupport ψ ⊆ Set.Ioo a b)
    {θ : ℝ} (hθ : θ ∉ Set.Icc a b) : ψ θ = 0 :=
  image_eq_zero_of_notMem_tsupport fun hmem =>
    hθ ⟨le_of_lt (hsupp hmem).1, le_of_lt (hsupp hmem).2⟩

/-- `ψ` vanishes *on a neighbourhood* of every point outside `[a,b]`. -/
lemma eventuallyEq_zero_of_tsupport_subset {ψ : ℝ → ℝ} {a b : ℝ}
    (hsupp : tsupport ψ ⊆ Set.Ioo a b) {θ : ℝ} (hθ : θ ∉ Set.Icc a b) :
    ψ =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
  have hmem : θ ∉ tsupport ψ := fun hmem =>
    hθ ⟨le_of_lt (hsupp hmem).1, le_of_lt (hsupp hmem).2⟩
  filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hmem] with τ hτ
  exact image_eq_zero_of_notMem_tsupport hτ

/-- The second derivative of `ψ` vanishes off `[a,b]`. -/
lemma deriv_deriv_eq_zero_of_tsupport_subset {ψ : ℝ → ℝ} {a b : ℝ}
    (hsupp : tsupport ψ ⊆ Set.Ioo a b) {θ : ℝ} (hθ : θ ∉ Set.Icc a b) :
    deriv (deriv ψ) θ = 0 := by
  have h1 : ψ =ᶠ[𝓝 θ] fun _ => (0 : ℝ) :=
    eventuallyEq_zero_of_tsupport_subset hsupp hθ
  rw [(h1.deriv).deriv_eq]
  simp [deriv_const]

/-- Integrability on `(0,π/2)` of `wt · F` for a weight `wt` continuous on `[a,b]` and vanishing
off `[a,b]`, and `F` continuous on `[a,b]`. -/
lemma integrableOn_Ioo_of_wt_mul {a b : ℝ} {wt F : ℝ → ℝ}
    (hwtc : ContinuousOn wt (Set.Icc a b))
    (hwt0 : ∀ θ, θ ∉ Set.Icc a b → wt θ = 0) (hFc : ContinuousOn F (Set.Icc a b)) :
    MeasureTheory.IntegrableOn (fun θ => wt θ * F θ) (Set.Ioo 0 (Real.pi / 2)) :=
  integrableOn_Ioo_of_compact_support (hwtc.mul hFc) fun θ hθ => by rw [hwt0 θ hθ, zero_mul]

/-- Linearity of a set integral over four `ℝ`-valued functions. -/
lemma integral_lin4 {μ : MeasureTheory.Measure ℝ} {s : Set ℝ} (f1 f2 f3 f4 : ℝ → ℝ)
    (c1 c2 c3 c4 : ℝ)
    (h1 : MeasureTheory.IntegrableOn f1 s μ) (h2 : MeasureTheory.IntegrableOn f2 s μ)
    (h3 : MeasureTheory.IntegrableOn f3 s μ) (h4 : MeasureTheory.IntegrableOn f4 s μ) :
    (∫ x in s, c1 * f1 x - c2 * f2 x - c3 * f3 x + c4 * f4 x ∂μ)
      = c1 * (∫ x in s, f1 x ∂μ) - c2 * (∫ x in s, f2 x ∂μ)
        - c3 * (∫ x in s, f3 x ∂μ) + c4 * (∫ x in s, f4 x ∂μ) := by
  have h12 : MeasureTheory.IntegrableOn (fun x => c1 * f1 x - c2 * f2 x) s μ :=
    (h1.const_mul c1).sub (h2.const_mul c2)
  have h123 : MeasureTheory.IntegrableOn (fun x => c1 * f1 x - c2 * f2 x - c3 * f3 x) s μ :=
    h12.sub (h3.const_mul c3)
  rw [MeasureTheory.integral_add h123 (h4.const_mul c4),
    MeasureTheory.integral_sub h12 (h3.const_mul c3),
    MeasureTheory.integral_sub (h1.const_mul c1) (h2.const_mul c2),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-! ## Clairaut: the `θ`-derivatives of the `z`-slice of `∂_z u` -/

/-- `(θ ↦ z ∂_z u z θ)' θ = z ∂_z∂_θu z θ`. -/
lemma deriv_slice_pz (u : ℝ → ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => z * Work.Spaces.pz u z θ') θ
      = z * Work.Spaces.pz (Work.Spaces.pth u) z θ := by
  have hmem : (z, θ) ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2) := ⟨hz, hθ⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ) :=
    (hu 2).contDiffAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hmem)
  have hp : Work.Spaces.pth (Work.Spaces.pz u) z θ = Work.Spaces.pz (Work.Spaces.pth u) z θ :=
    (Work.Spaces.pz_pth_comm hcd).symm
  rw [deriv_const_mul_field]
  exact congrArg (fun t => z * t) hp

/-- `(θ ↦ ∂_θ(z ∂_z u z ·))' θ = z ∂_z∂_θ∂_θu z θ`. -/
lemma deriv_deriv_slice_pz (u : ℝ → ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => deriv (fun θ'' => z * Work.Spaces.pz u z θ'') θ') θ
      = z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hu
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  -- the inner derivative, identified on a neighbourhood of `θ`
  have hnhds : (fun θ' => deriv (fun θ'' => z * Work.Spaces.pz u z θ'') θ')
      =ᶠ[𝓝 θ] fun θ' => z * Work.Spaces.pz (Work.Spaces.pth u) z θ' := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact deriv_slice_pz u hu hz hθ'
  rw [Filter.EventuallyEq.deriv_eq hnhds, deriv_const_mul_field]
  congr 1
  have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth u)) (z, θ) :=
    ((hS.pth).forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  have hp : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth u)) z θ
      = Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth u)) z θ :=
    (Work.Spaces.pz_pth_comm hcd).symm
  simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using hp

/-! ## The inner (`θ`)-integral identity at a fixed `z`

This is `sliceThetaIbpSep` transported along the two Clairaut identities: for `z > 0` the slice
`v = (θ ↦ z ∂_z u z θ)` has `v' = z ∂_z∂_θu` and `v'' = z ∂_z∂_θ∂_θu`. -/

theorem inner_ident (u : ℝ → ℝ → ℝ) (ψ : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hψ : ContDiff ℝ 2 ψ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hb : b < Real.pi / 2) (hsupp : tsupport ψ ⊆ Set.Ioo a b)
    {z : ℝ} (hz : 0 < z) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * ((z * Work.Spaces.pz u z θ) * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)))
      = -2 * Work.Spaces.eta * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (z * Work.Spaces.pz u z θ)^2)
        - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
            * (∫ θ in Set.Ioo 0 (Real.pi / 2),
                (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                  * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2)
        - (2 * Work.Spaces.eta / (1 + Work.Spaces.eta))
            * (∫ θ in Set.Ioo 0 (Real.pi / 2),
                (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                  * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
                      - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
                        * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2)
        + (1/2) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * deriv (deriv ψ) θ
              * (z * Work.Spaces.pz u z θ)^2) := by
  have hv : ContDiffOn ℝ 2 (fun θ => z * Work.Spaces.pz u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have hS : Work.FTS.EllipticEst.SmoothOpen u :=
      Work.FTS.EllipticEst.smoothOpen_of_forall hu
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun θ => Work.Spaces.pz u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      (hS.pz).curry_θ hz
    have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun θ => z * Work.Spaces.pz u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      contDiffOn_const.mul h1
    exact h2.of_le (by simp)
  have hslice := sliceThetaIbpSep2 (fun θ => z * Work.Spaces.pz u z θ) ψ hv hψ
    ⟨a, b, ha, hab, hb, hsupp⟩
  -- identify the second derivative of the slice
  have hv'' : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv (fun θ' => z * Work.Spaces.pz u z θ')) θ
        = z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ :=
    fun θ hθ => deriv_deriv_slice_pz u hu hz hθ
  have hv' : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (fun θ' => z * Work.Spaces.pz u z θ') θ
        = z * Work.Spaces.pz (Work.Spaces.pth u) z θ :=
    fun θ hθ => deriv_slice_pz u hu hz hθ
  -- rewrite the four integrals of the slice identity into the stated shape
  have e1 : (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * ((fun θ' => z * Work.Spaces.pz u z θ') θ
              * deriv (deriv (fun θ' => z * Work.Spaces.pz u z θ')) θ))
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * ((z * Work.Spaces.pz u z θ) * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)) :=
    setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => by rw [hv'' θ hθ])
  have e2 : (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * ((fun θ' => z * Work.Spaces.pz u z θ') θ)^2)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (z * Work.Spaces.pz u z θ)^2 :=
    setIntegral_congr_fun measurableSet_Ioo (fun θ _ => rfl)
  have e3 : (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * (deriv (fun θ' => z * Work.Spaces.pz u z θ') θ)^2)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2 :=
    setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => by rw [hv' θ hθ])
  have e4 : (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * (deriv (fun θ' => z * Work.Spaces.pz u z θ') θ
              - (1 + Work.Spaces.eta) * (fun θ' => z * Work.Spaces.pz u z θ') θ
                * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
              - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
                * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2 :=
    setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => by rw [hv' θ hθ])
  have e5 : (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * deriv (deriv ψ) θ
          * ((fun θ' => z * Work.Spaces.pz u z θ') θ)^2)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * deriv (deriv ψ) θ
          * (z * Work.Spaces.pz u z θ)^2 :=
    setIntegral_congr_fun measurableSet_Ioo (fun θ _ => rfl)
  rw [e1, e2, e3, e4, e5] at hslice
  exact hslice

/-! ## Integrability of the four angular integrands (at a fixed `z > 0`) -/

/-- The four angular integrands occurring in the corrected identity are `IntegrableOn (0,π/2)`
as soon as `tsupport ψ ⊆ (a,b) ⊂ (0,π/2)`: they are continuous on `[a,b]` and vanish off it. -/
theorem theta_integrable (u : ℝ → ℝ → ℝ) (ψ : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hψ : ContDiff ℝ 2 ψ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hb : b < Real.pi / 2) (hsupp : tsupport ψ ⊆ Set.Ioo a b)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z * Work.Spaces.pz u z θ)^2) (Set.Ioo 0 (Real.pi / 2))
    ∧ MeasureTheory.IntegrableOn (fun θ => (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2) (Set.Ioo 0 (Real.pi / 2))
    ∧ MeasureTheory.IntegrableOn (fun θ => (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
            - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
              * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2)
        (Set.Ioo 0 (Real.pi / 2))
    ∧ MeasureTheory.IntegrableOn (fun θ => (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))
        * deriv (deriv ψ) θ * (z * Work.Spaces.pz u z θ)^2) (Set.Ioo 0 (Real.pi / 2)) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u := Work.FTS.EllipticEst.smoothOpen_of_forall hu
  have hsub : Set.Icc a b ⊆ Set.Ioo 0 (Real.pi / 2) := fun θ hθ =>
    ⟨lt_of_lt_of_le ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩
  have hsin : ∀ θ ∈ Set.Icc a b, Real.sin (2*θ) ≠ 0 := fun θ hθ =>
    ne_of_gt (sin_two_pos_of_mem_Ioo (hsub hθ))
  have hcont_sin : ContinuousOn (fun θ : ℝ => Real.sin (2*θ)) (Set.Icc a b) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcont_sig : ContinuousOn (fun θ : ℝ => (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)))
      (Set.Icc a b) :=
    hcont_sin.rpow_const (p := -(Work.Spaces.eta)) fun θ hθ => Or.inl (hsin θ hθ)
  have hcont_sig1 : ContinuousOn (fun θ : ℝ => (Real.sin (2*θ)) ^ (-(1:ℝ))) (Set.Icc a b) :=
    hcont_sin.rpow_const (p := (-1 : ℝ)) fun θ hθ => Or.inl (hsin θ hθ)
  have hcont_cos : ContinuousOn (fun θ : ℝ => Real.cos (2*θ)) (Set.Icc a b) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hcont_psi : ContinuousOn ψ (Set.Icc a b) := hψ.continuous.continuousOn
  have hcont_psi2 : ContinuousOn (deriv (deriv ψ)) (Set.Icc a b) := by
    have hc : Continuous (iteratedDeriv 2 ψ) := hψ.continuous_iteratedDeriv 2 (by simp)
    refine (hc.continuousOn).congr (fun θ _ => ?_)
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hcont_pzu : ContinuousOn (fun θ : ℝ => z * Work.Spaces.pz u z θ) (Set.Icc a b) :=
    (continuousOn_const.mul ((hS.pz).curry_θ hz).continuousOn).mono hsub
  have hcont_pthpzu : ContinuousOn (fun θ : ℝ => z * Work.Spaces.pz (Work.Spaces.pth u) z θ)
      (Set.Icc a b) :=
    (continuousOn_const.mul (((hS.pth).pz).curry_θ hz).continuousOn).mono hsub
  have hz0 : ∀ θ, θ ∉ Set.Icc a b → ψ θ = 0 := fun θ hθ =>
    eq_zero_of_tsupport_subset hsupp hθ
  have hz2 : ∀ θ, θ ∉ Set.Icc a b → deriv (deriv ψ) θ = 0 := fun θ hθ =>
    deriv_deriv_eq_zero_of_tsupport_subset hsupp hθ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := integrableOn_Ioo_of_wt_mul (a := a) (b := b) hcont_psi hz0
      (hcont_sig.mul (hcont_pzu.pow 2))
    exact h.congr_fun (fun θ _ => by simp only [Pi.mul_apply, Pi.pow_apply]; ring) measurableSet_Ioo
  · have h := integrableOn_Ioo_of_wt_mul (a := a) (b := b) hcont_psi hz0
      (hcont_sig.mul (hcont_pthpzu.pow 2))
    exact h.congr_fun (fun θ _ => by simp only [Pi.mul_apply, Pi.pow_apply]; ring) measurableSet_Ioo
  · have hF3 : ContinuousOn (fun θ => (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))
        * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
            - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
              * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2) (Set.Icc a b) := by
      refine hcont_sig.mul ?_
      refine (hcont_pthpzu.sub ?_).pow 2
      exact ((continuousOn_const (c := 1 + Work.Spaces.eta)).mul hcont_pzu).mul hcont_cos
        |>.mul hcont_sig1
    have h := integrableOn_Ioo_of_wt_mul (a := a) (b := b) hcont_psi hz0 hF3
    exact h.congr_fun (fun θ _ => by simp only [Pi.mul_apply, Pi.pow_apply]; ring) measurableSet_Ioo
  · have h := integrableOn_Ioo_of_wt_mul (a := a) (b := b) hcont_psi2 hz2
      (hcont_sig.mul (hcont_pzu.pow 2))
    exact h.congr_fun (fun θ _ => by simp only [Pi.mul_apply, Pi.pow_apply]; ring) measurableSet_Ioo

/-! ## The corrected truncated identity

The statement below differs from the requested `truncThetaIbp` in exactly two ways:

* the hypothesis `hψsupp` (about `Function.support ψ`) is replaced by `hψsep` (the *closed*
  support `tsupport ψ` is separated from both corners, which is what kills the angular boundary
  bracket);
* the RHS is a *single* iterated integral of the four-term combination (with each of the four
  angular pairings written as an explicit `θ`-integral).  Splitting it into the four separate
  iterated integrals of the requested statement needs only the linearity of the outer integral
  and is done in `truncThetaIbpSep_split` below, under the corresponding integrability
  hypotheses. -/

theorem truncThetaIbpSep (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχsupp : Function.support χ ⊆ Set.Ioi (0:ℝ))
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (hψsep : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < Real.pi / 2 ∧ tsupport ψ ⊆ Set.Ioo a b) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), χ z * (Work.Spaces.w z)^2
        * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z * Work.Spaces.pz u z θ) * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ))
    = ∫ z in Set.Ioi 0,
        (-2 * Work.Spaces.eta
            * (χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
                (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                  * (z * Work.Spaces.pz u z θ)^2))
          - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
            * (χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
                (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                  * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2))
          - (2 * Work.Spaces.eta / (1 + Work.Spaces.eta))
            * (χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
                (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                  * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
                      - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
                        * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2))
          + (1/2) * (χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
                (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))
                  * deriv (deriv ψ) θ * (z * Work.Spaces.pz u z θ)^2))) := by
  obtain ⟨a, b, ha, hab, hb, hsupp⟩ := hψsep
  refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
  have hzpos : 0 < z := hz
  -- pull the `θ`-independent factor `χ z · w z ^ 2` out of the LHS integral
  have hL : (∫ θ in Set.Ioo 0 (Real.pi / 2), χ z * (Work.Spaces.w z)^2
        * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z * Work.Spaces.pz u z θ) * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ))
      = χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
            * ((z * Work.Spaces.pz u z θ)
                * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ))) := by
    rw [← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by ring)
  rw [hL, inner_ident u ψ hu hψ ha hab hb hsupp hzpos]
  ring

/-- **The corrected angular truncated identity in the exact shape of the requested statement.**

Same statement as `truncThetaIbpSep`, with the RHS written as the four separate iterated integrals
of the request.  The passage from the single-integral form needs the linearity of the outer `z`
-integral, hence the four integrability hypotheses `ho1`–`ho4` (which hold automatically in the
intended application, where `χ` is compactly supported in `(0,∞)` and the four `θ`-integrands are
bounded on `tsupport χ × [a,b]`). -/
theorem truncThetaIbpSep_split (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχsupp : Function.support χ ⊆ Set.Ioi (0:ℝ))
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (hψsep : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < Real.pi / 2 ∧ tsupport ψ ⊆ Set.Ioo a b)
    (ho1 : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (z * Work.Spaces.pz u z θ)^2))
      (Set.Ioi 0))
    (ho2 : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2))
      (Set.Ioi 0))
    (ho3 : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
              - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
                * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2))
      (Set.Ioi 0))
    (ho4 : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))
          * deriv (deriv ψ) θ * (z * Work.Spaces.pz u z θ)^2))
      (Set.Ioi 0)) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), χ z * (Work.Spaces.w z)^2
        * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z * Work.Spaces.pz u z θ) * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ))
      = -2 * Work.Spaces.eta * (∫ z in Set.Ioi 0,
            χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                * (z * Work.Spaces.pz u z θ)^2))
        - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * (∫ z in Set.Ioi 0,
            χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2))
        - (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * (∫ z in Set.Ioi 0,
            χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
                    - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
                      * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2))
        + (1/2) * (∫ z in Set.Ioi 0,
            χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))
                * deriv (deriv ψ) θ * (z * Work.Spaces.pz u z θ)^2)) := by
  rw [truncThetaIbpSep u χ ψ hu hχ hχc hχsupp hψ hψc hψsep]
  rw [integral_lin4
    (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
      (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (z * Work.Spaces.pz u z θ)^2))
    (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
      (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2))
    (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
      (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
            - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
              * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2))
    (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
      (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))
        * deriv (deriv ψ) θ * (z * Work.Spaces.pz u z θ)^2))
    (-2 * Work.Spaces.eta) ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
    (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) (1/2) ho1 ho2 ho3 ho4]

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
