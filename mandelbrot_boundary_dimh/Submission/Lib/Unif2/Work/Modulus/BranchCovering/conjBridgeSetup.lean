import Mathlib
import Submission.Lib.Unif2.Work.Modulus.PeriodSetup
import Submission.Lib.Unif2.Work.Modulus.Defs
import Submission.Lib.Unif2.Work.Modulus.puncturedHarmonic
import Submission.Lib.Unif2.Work.Modulus.exists_holomorphic_modulus_of_branchOnPunctured
import Submission.Lib.Unif2.Work.SimplyConnected.ModulusDefs
import Submission.Lib.Unif2.Work.SimplyConnected.Modulus.exists_isModulusBranch_of_ne

/-!
# The bridge from the conjugate étale space to the modulus bundle: bookkeeping

Let `X` be a connected complex one-manifold, `z₀ : X` and `E : X → ℝ` a Green function with pole
`z₀` (`Work.UnitGreen.IsUnitGreenFunctionAt`).  In `conjBridgeMap` we construct a continuous map from the
conjugate étale space `((X ∖ {z₀}) × ℝ, greenConjTopology z₀ E)` of `Submission.Conjugate` to the
modulus bundle `Work.SC.ModulusBundle z₀ E` of `Work.SC.ModulusDefs`, sending a conjugate value `t`
at `u` to the branch of the modulus whose value at `u` is `exp (-(E u + i t))`.

This module collects the *transport* lemmas that the construction needs, so that the proof of
`conjBridgeMap` is a clean application of them:

* `punctImage` / `punctLift` — the image in `X` of an open set of the punctured surface, and the
  extension of a function on the punctured surface to `X` (by `0` at the pole);
* `isModulusBranch_punctLift` — if `F` is a local conjugate of `E` on the punctured surface (a
  holomorphic `F` with `Re F = E`), then `exp (-F)`, read on `X`, is a branch of the modulus;
* the germ lemmas `chartDeriv_const_mul`, `chartDeriv_congr_of_eventuallyEq`,
  `exists_ratio_eventually_of_isModulusBranch_of_ne`,
  `eventually_eq_of_value_eq_of_isModulusBranch_of_ne` — the local rigidity of branches of the
  modulus (two branches with the same value at an off-pole common point agree near it), which is
  what makes the bridge map well behaved.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.Modulus.BranchCovering

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## The image of a set of the punctured surface, and the lift of a function on it -/

/-- The image in `X` of a set `B` of the punctured surface `X ∖ {z₀}`. -/
def punctImage {z₀ : X} (B : Set (puncturedOpens z₀)) : Set X := Subtype.val '' B

/-- A set of the punctured surface has open image in `X`. -/
theorem isOpen_punctImage {z₀ : X} {B : Set (puncturedOpens z₀)} (hB : IsOpen B) :
    IsOpen (punctImage B) :=
  IsOpen.isOpenMap_subtype_val (isOpen_punctured z₀) B hB

/-- The extension of a function on the punctured surface to `X` (with the value `0` at the pole). -/
def punctLift {z₀ : X} (G : puncturedOpens z₀ → ℂ) : X → ℂ :=
  fun y => if h : y = z₀ then 0 else G ⟨y, h⟩

/-- Off the pole, the lift is the original function. -/
theorem punctLift_apply {z₀ : X} {G : puncturedOpens z₀ → ℂ} {y : X} (hy : y ≠ z₀) :
    punctLift G y = G ⟨y, hy⟩ := dif_neg hy

/-- A point of the image of `B` is the underlying point of a point of `B`. -/
theorem mem_punctImage {z₀ : X} {B : Set (puncturedOpens z₀)} {y : X} :
    y ∈ punctImage B ↔ ∃ v ∈ B, v.1 = y := Iff.rfl

/-- **A local conjugate of `E` on the punctured surface gives a branch of the modulus on `X`.** -/
theorem isModulusBranch_punctLift {z₀ : X} {E : X → ℝ} {B : Set (puncturedOpens z₀)}
    {F : puncturedOpens z₀ → ℂ} (hB : IsOpen B)
    (hF : Submission.HolomorphicOnX F B) (hre : ∀ v ∈ B, (F v).re = E v.1) :
    Work.SC.IsModulusBranch z₀ E (punctImage B)
      (punctLift (fun v => Complex.exp (-(F v)))) := by
  refine ⟨isOpen_punctImage hB, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨v, hvB, rfl⟩ := hy
    refine Work.Modulus.holomorphicOnXAt_of_punctured (z₀ := z₀) (Φ := fun v => Complex.exp (-(F v)))
      (fun y hy => punctLift_apply hy) v.2 ?_
    exact (hF v hvB).cexp_neg
  · intro y hy hy0 h
    rw [punctLift_apply hy0] at h
    exact Complex.exp_ne_zero _ h
  · intro y hy hy0
    obtain ⟨v, hvB, rfl⟩ := hy
    rw [punctLift_apply v.2, Complex.norm_exp, Complex.neg_re, hre v hvB]

/-! ## Elementary complex analysis bookkeeping -/

/-- Adding a real multiple of `I` does not change the real part. -/
theorem add_pureImag_re (z : ℂ) (r : ℝ) : (z + (r : ℂ) * Complex.I).re = z.re := by
  simp [Complex.add_re, Complex.mul_re]

/-- Adding a real multiple of `I` adds `r` to the imaginary part. -/
theorem add_pureImag_im (z : ℂ) (r : ℝ) : (z + (r : ℂ) * Complex.I).im = z.im + r := by
  simp [Complex.add_im, Complex.mul_im]

/-- `exp (-F v)` depends on `F v` only through `Re (F v)` and `Im (F v)`. -/
theorem exp_neg_eq_of_re {z₀ : X} {E : X → ℝ} {F : puncturedOpens z₀ → ℂ}
    {v : puncturedOpens z₀} (hre : (F v).re = E v.1) :
    Complex.exp (-(F v)) = Complex.exp (-((E v.1 : ℂ) + ((F v).im : ℂ) * Complex.I)) := by
  have h1 : F v = (E v.1 : ℂ) + ((F v).im : ℂ) * Complex.I := by
    have h2 : F v = ((F v).re : ℂ) + ((F v).im : ℂ) * Complex.I :=
      (Complex.re_add_im (F v)).symm
    rw [hre] at h2
    exact h2
  rw [h1.symm]

/-! ## Germ rigidity of the branches of the modulus -/

/-- The derivative in the preferred chart of a constant multiple. -/
theorem chartDeriv_const_mul {Φ : X → ℂ} {x : X} (hΦ : Submission.HolomorphicOnXAt Φ x)
    (c : ℂ) :
    Work.SC.chartDeriv (fun y => c * Φ y) x = c * Work.SC.chartDeriv Φ x := by
  rw [Work.SC.chartDeriv, Work.SC.chartDeriv]
  have hfun : (fun y : X => c * Φ y) ∘ (chartAt ℂ x).symm
      = fun w : ℂ => c * (Φ ∘ (chartAt ℂ x).symm) w := rfl
  rw [hfun, deriv_const_mul c hΦ.differentiableAt]

/-- The chart derivative only depends on the germ. -/
theorem chartDeriv_congr_of_eventuallyEq {Φ Ψ : X → ℂ} {y : X} (h : Φ =ᶠ[𝓝 y] Ψ) :
    Work.SC.chartDeriv Φ y = Work.SC.chartDeriv Ψ y := by
  rw [Work.SC.chartDeriv, Work.SC.chartDeriv]
  have hsymm : (chartAt ℂ y).symm ((chartAt ℂ y) y) = y :=
    (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  have hcont : Tendsto (chartAt ℂ y).symm (𝓝 ((chartAt ℂ y) y)) (𝓝 y) := by
    have h' : Tendsto (chartAt ℂ y).symm (𝓝 ((chartAt ℂ y) y))
        (𝓝 ((chartAt ℂ y).symm ((chartAt ℂ y) y))) :=
      (chartAt ℂ y).continuousAt_symm ((chartAt ℂ y).map_source (mem_chart_source ℂ y))
    rwa [hsymm] at h'
  have h' : (Φ ∘ (chartAt ℂ y).symm) =ᶠ[𝓝 ((chartAt ℂ y) y)] (Ψ ∘ (chartAt ℂ y).symm) := by
    filter_upwards [hcont.eventually h] with w hw
    exact hw
  exact h'.deriv_eq

/-- A branch of the modulus multiplied by a constant of modulus one is again a branch. -/
theorem isModulusBranch_const_mul {z₀ : X} {E : X → ℝ} {U : Set X} {Φ : X → ℂ}
    (hΦ : Work.SC.IsModulusBranch z₀ E U Φ) {c : ℂ} (hc : ‖c‖ = 1) :
    Work.SC.IsModulusBranch z₀ E U (fun y => c * Φ y) := by
  obtain ⟨hUo, hhol, hne, hmod⟩ := hΦ
  refine ⟨hUo, fun y hy => (hhol y hy).const_mul c, ?_, ?_⟩
  · intro y hy hy0 h
    rcases mul_eq_zero.mp h with h | h
    · rw [h, norm_zero] at hc
      linarith
    · exact hne y hy hy0 h
  · intro y hy hy0
    rw [norm_mul, hmod y hy hy0, hc, one_mul]

/-- **Two branches of the modulus are proportional near an off-pole common point.**  The ratio of
two branches is holomorphic there and has constant modulus one, hence is locally constant. -/
theorem exists_ratio_eventually_of_isModulusBranch_of_ne {z₀ : X} {E : X → ℝ} {U V : Set X}
    {Φ Ψ : X → ℂ} (hΦ : Work.SC.IsModulusBranch z₀ E U Φ)
    (hΨ : Work.SC.IsModulusBranch z₀ E V Ψ) {y : X} (hy : y ∈ U ∩ V) (hy0 : y ≠ z₀) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ Ψ =ᶠ[𝓝 y] (fun x => c * Φ x) := by
  have hdiv : Submission.HolomorphicOnXAt (fun x => Ψ x / Φ x) y := by
    rw [Submission.HolomorphicOnXAt]
    have h1 : Submission.HolomorphicOnXAt Ψ y := hΨ.holomorphic y hy.2
    have h2 : Submission.HolomorphicOnXAt Φ y := hΦ.holomorphic y hy.1
    have h3 : Φ y ≠ 0 := hΦ.ne_zero y hy.1 hy0
    rw [Submission.HolomorphicOnXAt] at h1 h2
    have h3' : (Φ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) ≠ 0 := by
      rw [Function.comp_apply, (chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
      exact h3
    have heq : (fun x : X => Ψ x / Φ x) ∘ (chartAt ℂ y).symm =
        (Ψ ∘ (chartAt ℂ y).symm) / (Φ ∘ (chartAt ℂ y).symm) := rfl
    rw [heq]
    exact h1.div h2 h3'
  have hmem : ∀ᶠ x in 𝓝 y, x ∈ U ∩ V ∧ x ≠ z₀ := by
    filter_upwards [hΦ.1.mem_nhds hy.1, hΨ.1.mem_nhds hy.2,
      (isOpen_compl_singleton (x := z₀)).mem_nhds (by simpa using hy0)] with x hxU hxV hxz
    exact ⟨⟨hxU, hxV⟩, by simpa using hxz⟩
  have hnorm : ∀ᶠ x in 𝓝 y, ‖Ψ x / Φ x‖ = ‖Ψ y / Φ y‖ := by
    filter_upwards [hmem] with x hx
    rw [norm_div, norm_div, hΨ.norm_eq x hx.1.2 hx.2, hΦ.norm_eq x hx.1.1 hx.2,
      hΨ.norm_eq y hy.2 hy0, hΦ.norm_eq y hy.1 hy0]
    simp
  have hev := Submission.HolomorphicOnXAt.eventually_eq_const_of_eventually_norm_eq hdiv hnorm
  refine ⟨Ψ y / Φ y, ?_, ?_⟩
  · rw [norm_div, hΨ.norm_eq y hy.2 hy0, hΦ.norm_eq y hy.1 hy0, div_self (Real.exp_ne_zero _)]
  · have hΦne' : ∀ᶠ x in 𝓝 y, Φ x ≠ 0 := by
      filter_upwards [hmem] with x hx
      exact hΦ.ne_zero x hx.1.1 hx.2
    filter_upwards [hev, hΦne'] with x hx hxne
    rw [← hx, div_mul_cancel₀ _ hxne]

/-- **Two branches of the modulus with the same value at an off-pole common point agree near it.** -/
theorem eventually_eq_of_value_eq_of_isModulusBranch_of_ne {z₀ : X} {E : X → ℝ} {U V : Set X}
    {Φ Ψ : X → ℂ} (hΦ : Work.SC.IsModulusBranch z₀ E U Φ)
    (hΨ : Work.SC.IsModulusBranch z₀ E V Ψ) {y : X} (hy : y ∈ U ∩ V) (hy0 : y ≠ z₀)
    (hval : Ψ y = Φ y) : Ψ =ᶠ[𝓝 y] Φ := by
  obtain ⟨c, hc, hev⟩ := exists_ratio_eventually_of_isModulusBranch_of_ne hΦ hΨ hy hy0
  have hcy : Ψ y = c * Φ y := hev.eq_of_nhds
  have hne : Φ y ≠ 0 := hΦ.ne_zero y hy.1 hy0
  have hc1 : c = 1 := by
    have h1 : c * Φ y = (1 : ℂ) * Φ y := by rw [one_mul, ← hcy, hval]
    exact mul_right_cancel₀ hne h1
  filter_upwards [hev] with x hx
  rw [hx, hc1, one_mul]

end Work.Modulus.BranchCovering
