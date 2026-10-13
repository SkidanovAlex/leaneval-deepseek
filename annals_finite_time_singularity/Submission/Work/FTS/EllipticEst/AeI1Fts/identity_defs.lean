/-
# `AeI1Fts/identity_defs` — the pointwise calculus and integrability vocabulary for `identity`

This module collects the elementary facts shared by the target
`Work.FTS.EllipticEst.AeI1Fts.identity` (the weak-class `I₁` chain identity) and by the
auxiliary lemmas it is assembled from:

* the four slots `U u = z ∂_z u`, `V u = z ∂_z∂_θ u`, `Hh u = z ∂_z∂_θθu`, `AA u = z²∂_zz u`,
  `BB u = ∂_θθu` as the corresponding `D_z`/plain derivatives (`rfl`-level), together with the
  inheritance of `SmoothOpen` (hence joint continuity on the open quadrant) by each of them;
* the slice derivative facts `∂_θ(U u) = V u` and `∂_θ(V u) = Hh u` (Clairaut);
* the elementary angular weight facts (`sigE θ = sin(2θ)^{-η}` positive and differentiable on
  the open interval, with derivative `-2η cos(2θ)·sig1 θ`);
* the pointwise θ-identity `∂_θ(U·V·σ) = V²σ + U·Hh·σ - 2η·U·V·cos(2θ)·σ₁`, which is the
  angular integration by parts (2) of the paper's chain;
* the `ℋ⁰`-integrand identity `HkIntegrand α 0 f = w²(f²σ)` on `Iθ`, and the joint
  integrability of the `ℋ⁰`-integrand of an honestly `ℋ⁰` datum.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.pointwise_ident
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.H2.STBasic
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.EllipticEst.Dispatch.aeJointIntegrableF

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## The slots as operators -/

theorem U_eq_Dz (u : ℝ → ℝ → ℝ) : U u = Work.Spaces.Dz u := rfl

theorem V_eq_Dz_pth (u : ℝ → ℝ → ℝ) : V u = Work.Spaces.Dz (Work.Spaces.pth u) := rfl

theorem Hh_eq_Dz_pthIter (u : ℝ → ℝ → ℝ) :
    Hh u = Work.Spaces.Dz (Work.Spaces.pthIter 2 u) := rfl

theorem AA_eq (u : ℝ → ℝ → ℝ) :
    AA u = fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ := rfl

theorem BB_eq (u : ℝ → ℝ → ℝ) : BB u = Work.Spaces.pthIter 2 u := rfl

/-! ## `SmoothOpen` for the slots -/

theorem SmoothOpen.mul' {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => f z θ * g z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => f z θ * g z θ)) Q0
  have hfun : Function.uncurry (fun z θ : ℝ => f z θ * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p * Function.uncurry g p := rfl
  rw [hfun]
  exact hf.mul hg

theorem SmoothOpen.pthIter {F : ℝ → ℝ → ℝ} (hF : SmoothOpen F) (i : ℕ) :
    SmoothOpen (Work.Spaces.pthIter i F) := by
  induction i with
  | zero => simpa using hF
  | succ i ih =>
      rw [Work.Spaces.pthIter_succ]
      exact SmoothOpen.pth ih

theorem smoothOpen_U {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) : SmoothOpen (U u) :=
  hS.Dz

theorem smoothOpen_V {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) : SmoothOpen (V u) :=
  hS.pth.Dz

theorem smoothOpen_Hh {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) : SmoothOpen (Hh u) :=
  SmoothOpen.Dz (SmoothOpen.pthIter hS 2)

theorem smoothOpen_AA {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) : SmoothOpen (AA u) := by
  have h1 : SmoothOpen (fun z θ : ℝ => z ^ 2) := by
    show ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z θ : ℝ => z ^ 2)) Q0
    have hfun : Function.uncurry (fun z θ : ℝ => z ^ 2) = fun p : ℝ × ℝ => p.1 ^ 2 := rfl
    rw [hfun]
    exact (contDiff_fst.pow 2).contDiffOn
  have h2 : SmoothOpen (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) :=
    SmoothOpen.mul' h1 (hS.pzIter 2)
  simpa only [AA_eq] using h2

theorem smoothOpen_BB {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) : SmoothOpen (BB u) := by
  simpa only [BB_eq] using SmoothOpen.pthIter hS 2

theorem continuousOn_U {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) :
    ContinuousOn (Function.uncurry (U u)) Q0 := (smoothOpen_U hS).continuousOn

theorem continuousOn_V {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) :
    ContinuousOn (Function.uncurry (V u)) Q0 := (smoothOpen_V hS).continuousOn

theorem continuousOn_Hh {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) :
    ContinuousOn (Function.uncurry (Hh u)) Q0 := (smoothOpen_Hh hS).continuousOn

theorem continuousOn_AA {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) :
    ContinuousOn (Function.uncurry (AA u)) Q0 := (smoothOpen_AA hS).continuousOn

theorem continuousOn_BB {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) :
    ContinuousOn (Function.uncurry (BB u)) Q0 := (smoothOpen_BB hS).continuousOn

/-! ## Slice derivatives (Clairaut) -/

theorem contDiffAt_uncurry {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Iθo) (n : ℕ) : ContDiffAt ℝ n (Function.uncurry u) (z, θ) :=
  (hS.forall n).contDiffAt
    (isOpen_Q0.mem_nhds (mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩))

/-- The `θ`-slice of `U u` has derivative `V u` on the open quadrant. -/
theorem slice_deriv_U {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Iθo) : deriv (fun θ' => U u z θ') θ = V u z θ := by
  have hcl : Work.Spaces.pz (Work.Spaces.pth u) z θ
      = Work.Spaces.pth (Work.Spaces.pz u) z θ :=
    Work.Spaces.pz_pth_comm (contDiffAt_uncurry hS hz hθ 2)
  have hdiff : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz u z θ') θ :=
    ((hS.pz).curry_θ hz).differentiableOn (by norm_num) |>.differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  show deriv (fun θ' => z * Work.Spaces.pz u z θ') θ
      = z * Work.Spaces.pz (Work.Spaces.pth u) z θ
  rw [deriv_const_mul z hdiff]
  change z * Work.Spaces.pth (Work.Spaces.pz u) z θ = z * Work.Spaces.pz (Work.Spaces.pth u) z θ
  rw [hcl]

/-- The `θ`-slice of `V u` has derivative `Hh u` on the open quadrant. -/
theorem slice_deriv_V {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Iθo) : deriv (fun θ' => V u z θ') θ = Hh u z θ := by
  have hcl : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth u)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth u)) z θ :=
    Work.Spaces.pz_pth_comm (contDiffAt_uncurry (SmoothOpen.pth hS) hz hθ 2)
  have hdiff : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz (Work.Spaces.pth u) z θ') θ :=
    ((SmoothOpen.pz (SmoothOpen.pth hS)).curry_θ hz).differentiableOn (by norm_num)
      |>.differentiableAt (isOpen_Ioo.mem_nhds hθ)
  show deriv (fun θ' => z * Work.Spaces.pz (Work.Spaces.pth u) z θ') θ
      = z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ
  rw [deriv_const_mul z hdiff]
  change z * Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth u)) z θ
      = z * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth u)) z θ
  rw [hcl]

theorem smoothOrder_le_one : (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
  rw [Work.Stability.smoothOrder]
  exact WithTop.coe_le_coe.mpr le_top

/-- The `θ`-slice of `U u` is `C^∞` on the open interval. -/
theorem contDiffOn_slice_U {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => U u z θ) Iθo :=
  (smoothOpen_U hS).curry_θ hz

theorem contDiffOn_slice_V {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => V u z θ) Iθo :=
  (smoothOpen_V hS).curry_θ hz

theorem contDiffOn_slice_U_one {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ 1 (fun θ => U u z θ) Iθo :=
  (contDiffOn_slice_U hS hz).of_le smoothOrder_le_one

theorem contDiffOn_slice_V_one {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ 1 (fun θ => V u z θ) Iθo :=
  (contDiffOn_slice_V hS hz).of_le smoothOrder_le_one

/-! ## The angular weights -/

theorem sigE_eq_sEta (θ : ℝ) : sigE θ = Work.FTS.EllipticEst.sEta θ := rfl

theorem sigE_pos {θ : ℝ} (hθ : θ ∈ Iθo) : 0 < sigE θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  exact Real.rpow_pos_of_pos hs _

theorem sigE_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sigE θ := by
  rw [sigE]
  exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])) _

/-- `∂_θ sin(2θ)^{-η} = -2η cos(2θ)·sin(2θ)^{-1-η}`. -/
theorem hasDerivAt_sigE {θ : ℝ} (hθ : θ ∈ Iθo) :
    HasDerivAt sigE (-(2 * Work.Spaces.eta * Real.cos (2 * θ) * sig1 θ)) θ := by
  have h := Work.FTS.H2.hasDerivAt_sin_rpow (-(Work.Spaces.eta)) θ hθ
  rw [show -(Work.Spaces.eta) - 1 = -(1 + Work.Spaces.eta) by ring] at h
  refine h.congr_deriv ?_
  rw [sig1]
  ring

/-! ## The pointwise `θ`-identity -/

/-- **Pointwise `θ`-identity of the chain.**
`∂_θ(U·V·σ) = V²σ + U·Hh·σ - 2η·U·V·cos(2θ)·σ₁` on the open quadrant. -/
theorem hasDerivAt_theta_ident {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Iθo) :
    HasDerivAt (fun θ' => U u z θ' * V u z θ' * sigE θ')
      ((V u z θ) ^ 2 * sigE θ + U u z θ * Hh u z θ * sigE θ
        - 2 * Work.Spaces.eta
            * (U u z θ * V u z θ * Real.cos (2 * θ) * sig1 θ)) θ := by
  have hdU : DifferentiableAt ℝ (fun θ' => U u z θ') θ :=
    ((smoothOpen_U hS).curry_θ hz).differentiableOn (by norm_num) |>.differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hdV : DifferentiableAt ℝ (fun θ' => V u z θ') θ :=
    ((smoothOpen_V hS).curry_θ hz).differentiableOn (by norm_num) |>.differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hU' : HasDerivAt (fun θ' => U u z θ') (V u z θ) θ :=
    (hdU.hasDerivAt).congr_deriv (slice_deriv_U hS hz hθ)
  have hV' : HasDerivAt (fun θ' => V u z θ') (Hh u z θ) θ :=
    (hdV.hasDerivAt).congr_deriv (slice_deriv_V hS hz hθ)
  have hσ' := hasDerivAt_sigE hθ
  have hmain : HasDerivAt (((fun θ' => U u z θ') * fun θ' => V u z θ') * sigE)
      (V u z θ ^ 2 * sigE θ + U u z θ * Hh u z θ * sigE θ
        - 2 * Work.Spaces.eta
            * (U u z θ * V u z θ * Real.cos (2 * θ) * sig1 θ)) θ := by
    refine ((hU'.mul hV').mul hσ').congr_deriv ?_
    simp only [Pi.mul_apply]
    ring
  have hfun : (fun θ' => U u z θ' * V u z θ' * sigE θ')
      = ((fun θ' => U u z θ') * fun θ' => V u z θ') * sigE := rfl
  rw [hfun]
  exact hmain

theorem theta_deriv_ident {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Iθo) :
    deriv (fun θ' => U u z θ' * V u z θ' * sigE θ') θ
      = (V u z θ) ^ 2 * sigE θ + U u z θ * Hh u z θ * sigE θ
        - 2 * Work.Spaces.eta
            * (U u z θ * V u z θ * Real.cos (2 * θ) * sig1 θ) :=
  (hasDerivAt_theta_ident hS hz hθ).deriv

/-! ## The `ℋ⁰`-integrand on `Iθ` and joint integrability -/

/-- On `Iθ`, the level-`0` integrand is `w(z)²·(f(z,θ)²·σ(θ))`. -/
theorem hk_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * sigE θ) :=
  Work.FTS.EllipticEst.Dispatch.HkIntegrand_zero_D α f hθ

/-- Joint integrability of the `ℋ⁰`-integrand of a `SmoothOpen`, honestly `ℋ⁰` datum. -/
theorem integrable_HkIntegrand_zero {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : SmoothOpen f) (hm : Work.Spaces.HkMem α 0 f) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
      Work.FTS.EllipticEst.Dispatch.nuFts :=
  Work.FTS.EllipticEst.Dispatch.integrable_HkIntegrand_of_smoothOpen hf hm

/-- The weighted square `w²·f²·σ` is jointly integrable for an honestly `ℋ⁰` datum. -/
theorem integrable_sq_weight_zero {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : SmoothOpen f) (hm : Work.Spaces.HkMem α 0 f) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * ((f p.1 p.2) ^ 2 * sigE p.2))
      Work.FTS.EllipticEst.Dispatch.nuFts := by
  refine (integrable_HkIntegrand_zero hf hm).congr ?_
  filter_upwards [Work.FTS.EllipticEst.Dispatch.ae_mem_Ioo_nu] with p hp
  have hIθ : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hp.1, le_of_lt hp.2⟩
  exact hk_zero_eq α f hIθ

/-! ## The iterated integral over the open quadrant

`II g = ∫_z ∫_θ g` over `(0,∞) × (0,π/2)`, the form in which the target `identity` is
stated.  Everything below is expressed through `II` so that the assembly does not have to
manipulate the two integrations separately. -/

/-- `II g = ∫_{z>0} ∫_{0<θ<π/2} g z θ`. -/
def II (g : ℝ → ℝ → ℝ) : ℝ := ∫ z in Set.Ioi 0, ∫ θ in Iθo, g z θ

theorem II_congr {g h : ℝ → ℝ → ℝ} (hgh : ∀ z θ, g z θ = h z θ) : II g = II h :=
  MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun z _ => MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hgh z θ))

theorem II_add {g h : ℝ → ℝ → ℝ}
    (hg : ∀ z ∈ Set.Ioi (0:ℝ), MeasureTheory.IntegrableOn (fun θ => g z θ) Iθo)
    (hh : ∀ z ∈ Set.Ioi (0:ℝ), MeasureTheory.IntegrableOn (fun θ => h z θ) Iθo)
    (hG : MeasureTheory.IntegrableOn (fun z => ∫ θ in Iθo, g z θ) (Set.Ioi 0))
    (hH : MeasureTheory.IntegrableOn (fun z => ∫ θ in Iθo, h z θ) (Set.Ioi 0)) :
    II (fun z θ => g z θ + h z θ) = II g + II h := by
  have h1 : (∫ z in Set.Ioi 0, ∫ θ in Iθo, (g z θ + h z θ))
      = ∫ z in Set.Ioi 0, ((∫ θ in Iθo, g z θ) + ∫ θ in Iθo, h z θ) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun z hz => MeasureTheory.integral_add (hg z hz) (hh z hz))
  rw [II, II, II, h1, MeasureTheory.integral_add hG hH]

theorem II_const_mul (c : ℝ) (g : ℝ → ℝ → ℝ) : II (fun z θ => c * g z θ) = c * II g := by
  have h1 : (∫ z in Set.Ioi 0, ∫ θ in Iθo, c * g z θ)
      = ∫ z in Set.Ioi 0, c * (∫ θ in Iθo, g z θ) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun z _ => MeasureTheory.integral_const_mul c (fun θ => g z θ))
  rw [II, II, h1, MeasureTheory.integral_const_mul]

/-- The product measure `dz dθ` on `(0,∞) × (0,π/2)`. -/
abbrev nuQ : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict (Set.Ioi 0)).prod
    (MeasureTheory.volume.restrict Iθo)

theorem nuQ_eq : nuQ = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
    (Set.Ioi 0 ×ˢ Iθo) :=
  MeasureTheory.Measure.prod_restrict _ _

/-- **Fubini for `II`**: pull a radial factor out of the angular integral. -/
theorem II_swap {K : ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.Integrable (fun p : ℝ × ℝ => K p.1 * G p.1 p.2) nuQ) :
    (∫ z in Set.Ioi 0, K z * (∫ θ in Iθo, G z θ))
      = ∫ θ in Iθo, ∫ z in Set.Ioi 0, K z * G z θ := by
  have h1 : (∫ z in Set.Ioi (0 : ℝ), K z * (∫ θ in Iθo, G z θ))
      = ∫ z, ∫ θ, K z * G z θ
          ∂(MeasureTheory.volume.restrict Iθo)
          ∂(MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
      (fun z => (MeasureTheory.integral_const_mul (K z) (fun θ => G z θ)).symm))
  rw [h1]
  exact MeasureTheory.integral_integral_swap hint

/-- `II` of a product integrand, `w²(z)·σ(θ)` factored out. -/
theorem II_w2_sig {g : ℝ → ℝ → ℝ} :
    II (fun z θ => (Work.Spaces.w z) ^ 2 * sigE θ * g z θ)
      = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, sigE θ * g z θ := by
  rw [II]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  have hre : (fun θ => (Work.Spaces.w z) ^ 2 * sigE θ * g z θ)
      = fun θ => (Work.Spaces.w z) ^ 2 * (sigE θ * g z θ) := by
    funext θ; ring
  rw [hre, MeasureTheory.integral_const_mul]

end Work.FTS.EllipticEst.AeI1Fts
