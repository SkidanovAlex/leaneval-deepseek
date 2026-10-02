/-
# GATE2 / EXL — the exit loop from an *arc segment* through the ray lift

`Work.GATE2.EXL.exitLoop_of_curve` builds the exit loop at `x₀` from a *single* compact curve
`lam : [0,1] → ℂ` running from `x₀ - 1` to `x₀`, on which the four pieces of data (the window
`Re < -1`, the avoidance of `K c`, the `α`-window of the critical Böttcher deviation, the potential
floor `(3/4)·G(Ψ(x₀-1))` and the offset-avoidance `(W)`) are given.

The consumers of the dichotomy hand in the data on **two** pieces: an arbitrary arc
`B : [0,1] → ℂ` from the real base point `x'` to the point `γ₁ s₁` of the ray lift, and the
fundamental ray piece `γ₁ '' [s₁-1, s₁]` (the `1`-period of the lift, `γ₁ (s+1) = γ₁ s + 1`, closes
it up: `γ₁ (s₁-1) = γ₁ s₁ - 1`).

The present lemma assembles the closed loop

    x' - 1  --(B - 1)-->  γ₁(s₁-1)  --(γ₁)-->  γ₁ s₁  --(B reversed)-->  x'

and hands it to `exitLoop_of_curve` at `x₀ = x'`.  This is exactly the curve geometry of the
design's §2.3 (b0): the arc is traversed in both directions, shifted down by `1` first, so that the
loop starts at `x' - 1` and ends at `x'`.

The four pieces of data are read off the hypotheses on the two arcs:

* `Re < -1` and the `1/16384`-window: `hBre`/`hB1re` and `hdev`/`hdev1` for the two traversals of
  `B`, and `deviation_varphiCrit_eq_zero` on the ray piece (the deviation vanishes identically on a
  dynamical ray);
* the avoidance of `K c`: `hK`/`hK1` on `B`, and on the ray piece the potential floor `hfloorγ`
  together with `green_pos_of_notMem_K` at the base (`Ψ (B 0 - 1) ∉ K c`);
* the potential floor: `hfloorB`/`hfloorB1` on the two traversals of `B` and `hfloorγ` on the ray
  piece;
* the offset-avoidance `(W)`: the offset from the base `x' - 1` has nonzero imaginary part on both
  traversals of `B` (at `t > 0`, `hsgn`) and on the ray piece (`hsgnγ`), the only exceptional
  points being the two endpoints, where the offsets are `0` and `1`.
-/
import Mathlib
import Submission.Work.GATE2.EXL.exitLoop_of_curve
import Submission.Work.GATE2.EXL.arcLift_exists
import Submission.Work.GATE2.ExitPathInputs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2.EXL

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-! ## The reparametrisation of the unit interval used by `Path.trans` -/

/-- The point `2t` of the unit interval, when `t ≤ 1/2`. -/
private def rep (t : unitInterval) (h : (t : ℝ) ≤ 1 / 2) : unitInterval :=
  ⟨2 * (t : ℝ), by constructor <;> linarith [t.2.1, t.2.2, h]⟩

/-- The point `2t - 1` of the unit interval, when `1/2 < t`. -/
private def repm (t : unitInterval) (h : 1 / 2 < (t : ℝ)) : unitInterval :=
  ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.2.1, t.2.2, h]⟩

private theorem trans_le {X : Type*} [TopologicalSpace X] {x y z : X} (γ : Path x y) (γ' : Path y z)
    (t : unitInterval) (h : (t : ℝ) ≤ 1 / 2) : γ.trans γ' t = γ (rep t h) := by
  rw [Path.trans_apply, dif_pos h]
  refine congrArg γ (Subtype.ext ?_)
  simp [rep]

private theorem trans_gt {X : Type*} [TopologicalSpace X] {x y z : X} (γ : Path x y) (γ' : Path y z)
    (t : unitInterval) (h : 1 / 2 < (t : ℝ)) : γ.trans γ' t = γ' (repm t h) := by
  rw [Path.trans_apply, dif_neg (not_le.mpr h)]
  refine congrArg γ' (Subtype.ext ?_)
  simp [repm]

/-! ## The offset-avoidance `(W)` on the pieces through `B` -/

/-- **The slit condition at a point of the form `B r - B 0 + c`** (`c` real, `c.re > -1/2`):
the offset from the base has nonzero imaginary part as soon as `r > 0`, and at `r = 0` it equals
`c`, which is `> -1/2` and hence on the right of the cut of `Ω₀`. -/
private theorem slit_B_sub_add (B : C(unitInterval, ℂ)) {x : ℝ} (hB0 : B 0 = ((x : ℝ) : ℂ))
    {r : unitInterval} (hsgn : 0 < (r : ℝ) → (B r).im ≠ 0)
    (c : ℂ) (hc : c.im = 0) (hcre : -(1 / 2 : ℝ) < c.re) :
    B r - B 0 + c ∈ Work.GATE2.slitAt 0 := by
  rw [Work.GATE2.slitAt]
  rintro ⟨him, hre⟩
  by_cases hr : 0 < (r : ℝ)
  · apply hsgn hr
    have hB0im : (B 0).im = 0 := by rw [hB0]; simp
    rw [Complex.add_im, Complex.sub_im, hB0im, hc, sub_zero, add_zero] at him
    exact him
  · have hr0 : (r : ℝ) = 0 := le_antisymm (not_lt.mp hr) r.2.1
    have hrr : r = (0 : unitInterval) := Subtype.ext hr0
    have hc' : B r - B 0 + c = c := by rw [hrr]; ring
    rw [hc'] at hre
    linarith

/-! ## The main statement -/

theorem exitLoop_of_arcSegment {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (Lray : Work.ELRig.RayCylLift d fl)
    {x' s₁ : ℝ} (B : C(unitInterval, ℂ))
    (hB0 : B 0 = ((x' : ℝ) : ℂ)) (hB1 : B 1 = Lray.γ₁ s₁)
    (hBre : ∀ t : unitInterval, (B t).re < -(3 / 2 : ℝ))
    (hB1re : ∀ u ∈ Set.Icc (0 : ℝ) 1, (Lray.γ₁ (s₁ - 1 + u)).re < -(3 / 2 : ℝ))
    (hsgn : ∀ t : unitInterval, 0 < (t : ℝ) → (B t).im ≠ 0)
    (hsgnγ : ∀ s : ℝ, (Lray.γ₁ s).im ≠ 0)
    (hK : ∀ t : unitInterval, fl.Ψ (B t) ∉ Work.EL.K c)
    (hK1 : ∀ t : unitInterval, fl.Ψ (B t - 1) ∉ Work.EL.K c)
    (hdev : ∀ t : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (B t))| < 1 / 16384)
    (hdev1 : ∀ t : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (B t - 1))| <
        1 / 16384)
    (hfloorB : ∀ t : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (B 0 - 1)) <
        Work.Bottcher.green c (fl.Ψ (B t)))
    (hfloorB1 : ∀ t : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (B 0 - 1)) <
        Work.Bottcher.green c (fl.Ψ (B t - 1)))
    (hfloorγ : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (B 0 - 1)) <
        Work.Bottcher.green c (fl.Ψ (Lray.γ₁ (s₁ - 1 + u)))) :
    ∃ r₀ v : ℝ, 0 < r₀ ∧ Nonempty (Work.GATE2.ExitLoop c fl.Ψ x' r₀ v Work.EL.alpha1) := by
  classical
  have hM : c ∈ Mandelbar := Work.FSeed.API.mem_Mandelbar d
  -- ### the three pieces of the arc `x' - 1 → x'`
  let qB : Path (B 0) (Lray.γ₁ s₁) := ⟨B, rfl, by simpa using hB1⟩
  let q1 : Path (B 0 - 1) (Lray.γ₁ (s₁ - 1)) :=
    ⟨⟨fun t : unitInterval => B t - 1, by fun_prop⟩, rfl,
      by
        show B 1 - 1 = Lray.γ₁ (s₁ - 1)
        rw [hB1]
        have hp := Lray.per₁ (s₁ - 1)
        rw [sub_add_cancel] at hp
        rw [hp]; ring⟩
  let q2 : Path (Lray.γ₁ (s₁ - 1)) (Lray.γ₁ s₁) :=
    ⟨⟨fun t : unitInterval => Lray.γ₁ (s₁ - 1 + (t : ℝ)),
        Lray.cont₁.comp (continuous_const.add continuous_subtype_val)⟩,
      by
        show Lray.γ₁ (s₁ - 1 + ((0 : unitInterval) : ℝ)) = Lray.γ₁ (s₁ - 1)
        rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, add_zero],
      by
        show Lray.γ₁ (s₁ - 1 + ((1 : unitInterval) : ℝ)) = Lray.γ₁ s₁
        rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, show s₁ - 1 + 1 = s₁ from by ring]⟩
  let lamP : Path (B 0 - 1) (B 0) := (q1.trans q2).trans qB.symm
  let lam : C(unitInterval, ℂ) := lamP.toContinuousMap
  have hlam : ∀ t : unitInterval, lam t = lamP t := fun t => rfl
  have hlam0 : lam 0 = B 0 - 1 := by rw [hlam 0]; exact Path.source lamP
  have hfl0 : fl.Ψ (lam 0) = fl.Ψ (B 0 - 1) := by rw [hlam0]
  have hq3 : ∀ s : unitInterval, qB.symm s = B (unitInterval.symm s) := by
    intro s; rw [Path.symm_apply]; rfl
  -- ### the three case description of `lam t`
  have hcase : ∀ t : unitInterval,
      (∃ r : unitInterval, lamP t = B r - 1) ∨
      (∃ r : unitInterval, lamP t = Lray.γ₁ (s₁ - 1 + (r : ℝ))) ∨
      (∃ r : unitInterval, lamP t = B r) := by
    intro t
    by_cases h1 : (t : ℝ) ≤ 1 / 2
    · rw [trans_le (q1.trans q2) qB.symm t h1]
      by_cases h2 : ((rep t h1 : unitInterval) : ℝ) ≤ 1 / 2
      · refine Or.inl ⟨rep (rep t h1) h2, ?_⟩
        rw [trans_le q1 q2 (rep t h1) h2]; rfl
      · refine Or.inr (Or.inl ⟨repm (rep t h1) (not_le.mp h2), ?_⟩)
        rw [trans_gt q1 q2 (rep t h1) (not_le.mp h2)]; rfl
    · refine Or.inr (Or.inr ⟨unitInterval.symm (repm t (not_le.mp h1)), ?_⟩)
      rw [trans_gt (q1.trans q2) qB.symm t (not_le.mp h1)]
      rw [hq3]
  -- ### `Re < -1`
  have hre : ∀ t : unitInterval, (lam t).re < -1 := by
    intro t
    rw [hlam t]
    rcases hcase t with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨r, hr⟩
    · rw [hr]; simp only [Complex.sub_re, Complex.one_re]; linarith [hBre r]
    · rw [hr]; linarith [hB1re (r : ℝ) r.2]
    · rw [hr]; linarith [hBre r]
  -- ### off the filled Julia set
  have hK' : ∀ t : unitInterval, fl.Ψ (lam t) ∉ Work.EL.K c := by
    intro t
    rw [hlam t]
    rcases hcase t with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨r, hr⟩
    · rw [hr]; exact hK1 r
    · rw [hr]
      refine Work.PARIMPL.notMem_K_of_green_pos ?_
      have h1 : 0 < Work.Bottcher.green c (fl.Ψ (B 0 - 1)) :=
        Work.PARIMPL.green_pos_of_notMem_K (hK1 (0 : unitInterval))
      have h2 := hfloorγ (r : ℝ) r.2
      linarith
    · rw [hr]; exact hK r
  -- ### the `α₁`-window
  have hwin : ∀ t : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (lam t))| <
        1 / 16384 := by
    intro t
    rw [hlam t]
    rcases hcase t with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨r, hr⟩
    · rw [hr]; exact hdev1 r
    · rw [hr]
      have h :=
        deviation_varphiCrit_eq_zero d.hN d.bottcher hM (Lray.img₁ (s₁ - 1 + (r : ℝ)))
      rw [h]; norm_num
    · rw [hr]; exact hdev r
  -- ### the potential floor
  have hfloor : ∀ t : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (lam 0)) <
        Work.Bottcher.green c (fl.Ψ (lam t)) := by
    intro t
    rw [hfl0, hlam t]
    rcases hcase t with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨r, hr⟩
    · rw [hr]; exact hfloorB1 r
    · rw [hr]; exact hfloorγ (r : ℝ) r.2
    · rw [hr]; exact hfloorB r
  -- ### the offset-avoidance `(W)`
  have hB01im : (B 0 - 1).im = 0 := by
    rw [Complex.sub_im, Complex.one_im, sub_zero, hB0]; simp
  have hslit : ∀ t : unitInterval, lam t - lam 0 ∈ Work.GATE2.slitAt 0 := by
    intro t
    rw [hlam t, hlam0]
    rcases hcase t with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨r, hr⟩
    · rw [hr]
      have heq : B r - 1 - (B 0 - 1) = B r - B 0 + 0 := by ring
      rw [heq]
      exact slit_B_sub_add B hB0 (fun h => hsgn r h) (0 : ℂ) (by simp) (by norm_num)
    · rw [hr]
      rw [Work.GATE2.slitAt]
      rintro ⟨him, -⟩
      refine hsgnγ (s₁ - 1 + (r : ℝ)) ?_
      rw [Complex.sub_im, hB01im, sub_zero] at him
      exact him
    · rw [hr]
      have heq : B r - (B 0 - 1) = B r - B 0 + 1 := by ring
      rw [heq]
      exact slit_B_sub_add B hB0 (fun h => hsgn r h) (1 : ℂ) (by simp) (by norm_num)
  -- ### assemble
  obtain ⟨r₀, v, hr₀, hE⟩ :=
    exitLoop_of_curve (fl := fl) (α := Work.EL.alpha1) (x₀ := x') lam
      (by rw [hlam0, hB0]; push_cast; ring)
      (by rw [hlam 1, Path.target lamP, hB0])
      hre hK' hwin hfloor hslit
  exact ⟨r₀, v, hr₀, hE⟩

end Work.GATE2.EXL
