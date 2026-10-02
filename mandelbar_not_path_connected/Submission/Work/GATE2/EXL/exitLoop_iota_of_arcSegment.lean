/-
# GATE2 / EXL — the `ι`-image of an arc segment gives the exit loop at `x' + 1/2`

`Work.GATE2.EXL.exitLoop_of_curve` builds the exit loop `Work.GATE2.ExitLoop` of the `α`-window at
a leak centre `x₀` out of a *single* curve `lam : [0,1] → ℂ` running from `x₀ − 1` to `x₀`, lying
off `K c₀`, inside the thin `α`-window, with the potential floor and the offset-avoidance (W).

Here the curve is glued from three pieces:

* the arc `B` from `x'` to `γ₁ s₁`, reflected by the `ι`-symmetry `w ↦ star w + 1/2` and shifted by
  `−1`: `Λ₁ t = star (B t) + 1/2 − 1`, from `x' − 1/2` to `γ₂ s₁ − 1` (the shift is the
  `1`-periodicity `γ₂ (s₁ − 1) = γ₂ s₁ − 1`);
* the second ray piece `γ₂ (s₁ − 1 + t)`, from `γ₂ s₁ − 1` to `γ₂ s₁`;
* the reversed reflection of `B`: `Λ₃ t = star (B (unitInterval.symm t)) + 1/2`, from `γ₂ s₁` back
  to `x' + 1/2`.

The leak centre is `x₀ = x' + 1/2` and the angle is `α₂` (the second lift `γ₂ = ι γ₁` is the
`α₂`-ray lift).  The three pieces are exactly the three families of hypotheses of the statement:

| piece | off `K c` | `α₂`-window | potential floor against `Ψ (x' − 1/2)` |
|-------|-----------|-------------|----------------------------------------|
| `B − 1`, reflected | `hK1` | `hdev1` | `hfloor1` |
| `γ₂` | `hKγ` | `hdevγ` | `hfloorγ` |
| `B`, reflected | `hK` | `hdev` | `hfloor` |

The sign hypotheses `hsgn` (the arc `B` is real only at its initial point `t = 0`) and `hsgnγ`
(the first ray lift is never real) are what makes the offset-avoidance (W) hold: the offsets
`Λ t − Λ 0` are either non-real or real and `> −1/2`.  The bound `Re < −3/2` along the pieces gives
the exit window `Re < −1` of UT.
-/
import Mathlib
import Submission.Work.GATE2.Dichotomy2
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
set_option maxHeartbeats 4000000

noncomputable section

namespace Work.GATE2.EXL

/-! ## Gluing two paths -/

/-- A concatenation of paths, evaluated on the left half of the unit interval. -/
private theorem trans_apply_le {X : Type*} [TopologicalSpace X] {x y z : X} (γ : Path x y)
    (γ' : Path y z) (t : unitInterval) (h : (t : ℝ) ≤ 1 / 2) :
    (γ.trans γ') t = γ ⟨2 * (t : ℝ), by constructor <;> linarith [t.2.1, t.2.2, h]⟩ := by
  rw [Path.trans_apply, dite_eq_left h]

/-- A concatenation of paths, evaluated on the right half of the unit interval. -/
private theorem trans_apply_gt {X : Type*} [TopologicalSpace X] {x y z : X} (γ : Path x y)
    (γ' : Path y z) (t : unitInterval) (h : 1 / 2 < (t : ℝ)) :
    (γ.trans γ') t = γ' ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.2.1, t.2.2, h]⟩ := by
  rw [Path.trans_apply, dite_eq_right (not_le.mpr h)]

theorem exitLoop_iota_of_arcSegment {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (Lray : Work.ELRig.RayCylLift d fl)
    {x' s₁ : ℝ} (B : C(unitInterval, ℂ))
    (hB0 : B 0 = ((x' : ℝ) : ℂ)) (hB1 : B 1 = Lray.γ₁ s₁)
    (hBre : ∀ t : unitInterval, (B t).re < -(3 / 2 : ℝ))
    (hB1re : ∀ u ∈ Set.Icc (0 : ℝ) 1, (Lray.γ₁ (s₁ - 1 + u)).re < -(3 / 2 : ℝ))
    (hsgn : ∀ t : unitInterval, 0 < (t : ℝ) → (B t).im ≠ 0)
    (hsgnγ : ∀ s : ℝ, (Lray.γ₁ s).im ≠ 0)
    (hK : ∀ t : unitInterval, fl.Ψ (star (B t) + 1 / 2) ∉ Work.EL.K c)
    (hK1 : ∀ t : unitInterval, fl.Ψ (star (B t - 1) + 1 / 2) ∉ Work.EL.K c)
    (hKγ : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      fl.Ψ (Lray.γ₂ (s₁ - 1 + u)) ∉ Work.EL.K c)
    (hdev : ∀ t : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha2
        (fl.Ψ (star (B t) + 1 / 2))| < 1 / 16384)
    (hdev1 : ∀ t : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha2
        (fl.Ψ (star (B t - 1) + 1 / 2))| < 1 / 16384)
    (hdevγ : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha2
        (fl.Ψ (Lray.γ₂ (s₁ - 1 + u)))| < 1 / 16384)
    (hfloor : ∀ t : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (star (B 0 - 1) + 1 / 2)) <
        Work.Bottcher.green c (fl.Ψ (star (B t) + 1 / 2)))
    (hfloor1 : ∀ t : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (star (B 0 - 1) + 1 / 2)) <
        Work.Bottcher.green c (fl.Ψ (star (B t - 1) + 1 / 2)))
    (hfloorγ : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (star (B 0 - 1) + 1 / 2)) <
        Work.Bottcher.green c (fl.Ψ (Lray.γ₂ (s₁ - 1 + u)))) :
    ∃ r₀ v : ℝ, 0 < r₀ ∧
      Nonempty (Work.GATE2.ExitLoop c fl.Ψ (x' + 1 / 2) r₀ v Work.EL.alpha2) := by
  classical
  -- ## 0. arithmetic on the reflection `ι w = star w + 1/2`
  have hconj_re : ∀ z : ℂ, (star z).re = z.re := fun z => Complex.conj_re z
  have hconj_im : ∀ z : ℂ, (star z).im = -z.im := fun z => Complex.conj_im z
  have hconj_real : ∀ x : ℝ, star ((x : ℝ) : ℂ) = ((x : ℝ) : ℂ) :=
    fun x => Complex.conj_ofReal x
  -- ## 1. the `-1`-periodicity of the second lift
  have hper2 : Lray.γ₂ (s₁ - 1) = Lray.γ₂ s₁ - 1 := by
    have h := Lray.per₂ (s₁ - 1)
    rw [show s₁ - 1 + 1 = s₁ from by ring] at h
    exact eq_sub_iff_add_eq.mpr h.symm
  -- ## 2. the `ι`-reflection of the arc `B`
  let A : Path (((x' + 1 / 2 : ℝ)) : ℂ) (Lray.γ₂ s₁) :=
    { toContinuousMap :=
        ⟨fun t : unitInterval => star (B t) + 1 / 2,
          (Complex.continuous_conj.comp B.continuous).add continuous_const⟩
      source' := by
        show star (B 0) + 1 / 2 = ((x' + 1 / 2 : ℝ) : ℂ)
        rw [hB0, hconj_real]
        push_cast
        ring
      target' := by
        show star (B 1) + 1 / 2 = Lray.γ₂ s₁
        rw [hB1, ← Lray.anti s₁] }
  -- ## 3. the three pieces of the exit curve
  let P₁ : Path (((x' - 1 / 2 : ℝ)) : ℂ) (Lray.γ₂ s₁ - 1) :=
    { toContinuousMap := ⟨fun t : unitInterval => A t - 1, by fun_prop⟩
      source' := by
        show A 0 - 1 = ((x' - 1 / 2 : ℝ) : ℂ)
        rw [Path.source A]
        push_cast
        ring
      target' := by
        show A 1 - 1 = Lray.γ₂ s₁ - 1
        rw [Path.target A] }
  let P₂ : Path (Lray.γ₂ s₁ - 1) (Lray.γ₂ s₁) :=
    { toContinuousMap :=
        ⟨fun t : unitInterval => Lray.γ₂ (s₁ - 1 + (t : ℝ)), by
          exact Lray.cont₂.comp (continuous_subtype_val.const_add (s₁ - 1))⟩
      source' := by
        show Lray.γ₂ (s₁ - 1 + ((0 : unitInterval) : ℝ)) = Lray.γ₂ s₁ - 1
        rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, add_zero]
        exact hper2
      target' := by
        show Lray.γ₂ (s₁ - 1 + ((1 : unitInterval) : ℝ)) = Lray.γ₂ s₁
        rw [show ((1 : unitInterval) : ℝ) = 1 from rfl,
          show s₁ - 1 + 1 = s₁ from by ring] }
  let Λ : Path (((x' - 1 / 2 : ℝ)) : ℂ) (((x' + 1 / 2 : ℝ)) : ℂ) := (P₁.trans P₂).trans A.symm
  -- ## 4. the values of `Λ` on the three thirds
  have hA_app : ∀ s : unitInterval, A s = star (B s) + 1 / 2 := fun s => rfl
  have hP1_app : ∀ s : unitInterval, P₁ s = A s - 1 := fun s => rfl
  have hP2_app : ∀ s : unitInterval, P₂ s = Lray.γ₂ (s₁ - 1 + (s : ℝ)) := fun s => rfl
  have hval1 : ∀ (t : unitInterval) (h : (t : ℝ) ≤ 1 / 4) (s : unitInterval)
      (hs : (s : ℝ) = 4 * (t : ℝ)), Λ t = P₁ s := by
    intro t h s hs
    show ((P₁.trans P₂).trans A.symm) t = _
    rw [trans_apply_le (P₁.trans P₂) A.symm t (by linarith [h]),
      trans_apply_le P₁ P₂ _ (by linarith [h])]
    refine congrArg P₁ (Subtype.ext ?_)
    rw [hs]
    ring
  have hval2 : ∀ (t : unitInterval) (h : 1 / 4 < (t : ℝ)) (h₂ : (t : ℝ) ≤ 1 / 2)
      (s : unitInterval) (hs : (s : ℝ) = 4 * (t : ℝ) - 1), Λ t = P₂ s := by
    intro t h h₂ s hs
    show ((P₁.trans P₂).trans A.symm) t = _
    rw [trans_apply_le (P₁.trans P₂) A.symm t (by linarith [h₂]),
      trans_apply_gt P₁ P₂ _ (by linarith [h])]
    refine congrArg P₂ (Subtype.ext ?_)
    rw [hs]
    ring
  have hval3 : ∀ (t : unitInterval) (h : 1 / 2 < (t : ℝ)) (s : unitInterval)
      (hs : (s : ℝ) = 2 - 2 * (t : ℝ)), Λ t = A s := by
    intro t h s hs
    show ((P₁.trans P₂).trans A.symm) t = _
    rw [trans_apply_gt (P₁.trans P₂) A.symm t h, Path.symm_apply]
    simp only [Function.comp_apply]
    refine congrArg A (Subtype.ext ?_)
    simp only [unitInterval.symm]
    rw [hs]
    ring
  -- ## 5. arithmetic along the reflected pieces
  have hre_sub : ∀ z : ℂ, (star z + 1 / 2 - 1).re = z.re - 1 / 2 := by
    intro z
    simp [Complex.add_re, Complex.sub_re, Complex.conj_re]
    ring
  have hre_add : ∀ z : ℂ, (star z + 1 / 2).re = z.re + 1 / 2 := by
    intro z
    simp [Complex.add_re, Complex.conj_re]
  have him_sub : ∀ z : ℂ, (star z + 1 / 2 - 1).im = -z.im := by
    intro z
    simp [Complex.add_im, Complex.sub_im, Complex.conj_im]
  have him_add : ∀ z : ℂ, (star z + 1 / 2).im = -z.im := by
    intro z
    simp [Complex.add_im, Complex.conj_im]
  have hshift : ∀ z : ℂ, star z + 1 / 2 - 1 = star (z - 1) + 1 / 2 := by
    intro z
    rw [star_sub, star_one]
    ring
  have hγ₂re : ∀ s : ℝ, (Lray.γ₂ s).re = (Lray.γ₁ s).re + 1 / 2 := by
    intro s
    rw [Lray.anti]
    simp [Complex.add_re, Complex.conj_re]
  have hγ₂im : ∀ s : ℝ, (Lray.γ₂ s).im = -(Lray.γ₁ s).im := by
    intro s
    rw [Lray.anti]
    simp [Complex.add_im, Complex.conj_im]
  -- ## 6. the endpoints of the curve
  have hΛ0 : Λ 0 = (((x' - 1 / 2 : ℝ)) : ℂ) := Path.source Λ
  have hΛ1 : Λ 1 = (((x' + 1 / 2 : ℝ)) : ℂ) := Path.target Λ
  have hdisc : star (B 0 - 1) + 1 / 2 = (((x' - 1 / 2 : ℝ)) : ℂ) := by
    rw [hB0, star_sub, star_one, hconj_real]
    push_cast
    ring
  -- ## 7. the exit window `Re < -1`
  have hre : ∀ t : unitInterval, (Λ t).re < -1 := by
    intro t
    by_cases h₁ : (t : ℝ) ≤ 1 / 4
    · let s : unitInterval := ⟨4 * (t : ℝ), by constructor <;> linarith [t.2.1, t.2.2, h₁]⟩
      have hsv : (s : ℝ) = 4 * (t : ℝ) := rfl
      rw [hval1 t h₁ s hsv, hP1_app, hA_app, hre_sub]
      linarith [hBre s]
    · have h₁' : 1 / 4 < (t : ℝ) := not_le.mp h₁
      by_cases h₂ : (t : ℝ) ≤ 1 / 2
      · let s : unitInterval :=
          ⟨4 * (t : ℝ) - 1, by constructor <;> linarith [t.2.1, t.2.2, h₁', h₂]⟩
        have hsv : (s : ℝ) = 4 * (t : ℝ) - 1 := rfl
        rw [hval2 t h₁' h₂ s hsv, hP2_app, hγ₂re]
        linarith [hB1re (s : ℝ) s.2]
      · have h₂' : 1 / 2 < (t : ℝ) := not_le.mp h₂
        let s : unitInterval := ⟨2 - 2 * (t : ℝ), by constructor <;> linarith [t.2.1, t.2.2, h₂']⟩
        have hsv : (s : ℝ) = 2 - 2 * (t : ℝ) := rfl
        rw [hval3 t h₂' s hsv, hA_app, hre_add]
        linarith [hBre s]
  -- ## 8. off the filled Julia set
  have hKmem : ∀ t : unitInterval, fl.Ψ (Λ t) ∉ Work.EL.K c := by
    intro t
    by_cases h₁ : (t : ℝ) ≤ 1 / 4
    · let s : unitInterval := ⟨4 * (t : ℝ), by constructor <;> linarith [t.2.1, t.2.2, h₁]⟩
      have hsv : (s : ℝ) = 4 * (t : ℝ) := rfl
      rw [hval1 t h₁ s hsv, hP1_app, hA_app, hshift]
      exact hK1 s
    · have h₁' : 1 / 4 < (t : ℝ) := not_le.mp h₁
      by_cases h₂ : (t : ℝ) ≤ 1 / 2
      · let s : unitInterval :=
          ⟨4 * (t : ℝ) - 1, by constructor <;> linarith [t.2.1, t.2.2, h₁', h₂]⟩
        have hsv : (s : ℝ) = 4 * (t : ℝ) - 1 := rfl
        rw [hval2 t h₁' h₂ s hsv, hP2_app]
        exact hKγ (s : ℝ) s.2
      · have h₂' : 1 / 2 < (t : ℝ) := not_le.mp h₂
        let s : unitInterval := ⟨2 - 2 * (t : ℝ), by constructor <;> linarith [t.2.1, t.2.2, h₂']⟩
        have hsv : (s : ℝ) = 2 - 2 * (t : ℝ) := rfl
        rw [hval3 t h₂' s hsv, hA_app]
        exact hK s
  -- ## 9. inside the thin `α₂`-window
  have hwin : ∀ t : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha2 (fl.Ψ (Λ t))| <
        1 / 16384 := by
    intro t
    by_cases h₁ : (t : ℝ) ≤ 1 / 4
    · let s : unitInterval := ⟨4 * (t : ℝ), by constructor <;> linarith [t.2.1, t.2.2, h₁]⟩
      have hsv : (s : ℝ) = 4 * (t : ℝ) := rfl
      rw [hval1 t h₁ s hsv, hP1_app, hA_app, hshift]
      exact hdev1 s
    · have h₁' : 1 / 4 < (t : ℝ) := not_le.mp h₁
      by_cases h₂ : (t : ℝ) ≤ 1 / 2
      · let s : unitInterval :=
          ⟨4 * (t : ℝ) - 1, by constructor <;> linarith [t.2.1, t.2.2, h₁', h₂]⟩
        have hsv : (s : ℝ) = 4 * (t : ℝ) - 1 := rfl
        rw [hval2 t h₁' h₂ s hsv, hP2_app]
        exact hdevγ (s : ℝ) s.2
      · have h₂' : 1 / 2 < (t : ℝ) := not_le.mp h₂
        let s : unitInterval := ⟨2 - 2 * (t : ℝ), by constructor <;> linarith [t.2.1, t.2.2, h₂']⟩
        have hsv : (s : ℝ) = 2 - 2 * (t : ℝ) := rfl
        rw [hval3 t h₂' s hsv, hA_app]
        exact hdev s
  -- ## 10. the potential floor
  have hflr : ∀ t : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (Λ 0)) <
        Work.Bottcher.green c (fl.Ψ (Λ t)) := by
    intro t
    by_cases h₁ : (t : ℝ) ≤ 1 / 4
    · let s : unitInterval := ⟨4 * (t : ℝ), by constructor <;> linarith [t.2.1, t.2.2, h₁]⟩
      have hsv : (s : ℝ) = 4 * (t : ℝ) := rfl
      rw [hval1 t h₁ s hsv, hP1_app, hA_app, hshift, hΛ0]
      have h := hfloor1 s
      rw [hdisc] at h
      exact h
    · have h₁' : 1 / 4 < (t : ℝ) := not_le.mp h₁
      by_cases h₂ : (t : ℝ) ≤ 1 / 2
      · let s : unitInterval :=
          ⟨4 * (t : ℝ) - 1, by constructor <;> linarith [t.2.1, t.2.2, h₁', h₂]⟩
        have hsv : (s : ℝ) = 4 * (t : ℝ) - 1 := rfl
        rw [hval2 t h₁' h₂ s hsv, hP2_app, hΛ0]
        have h := hfloorγ (s : ℝ) s.2
        rw [hdisc] at h
        exact h
      · have h₂' : 1 / 2 < (t : ℝ) := not_le.mp h₂
        let s : unitInterval := ⟨2 - 2 * (t : ℝ), by constructor <;> linarith [t.2.1, t.2.2, h₂']⟩
        have hsv : (s : ℝ) = 2 - 2 * (t : ℝ) := rfl
        rw [hval3 t h₂' s hsv, hA_app, hΛ0]
        have h := hfloor s
        rw [hdisc] at h
        exact h
  -- ## 11. the offset-avoidance (W)
  have hslit : ∀ t : unitInterval, Λ t - Λ 0 ∈ Work.GATE2.slitAt 0 := by
    intro t
    by_cases h₁ : (t : ℝ) ≤ 1 / 4
    · -- the reflected, shifted arc `B - 1`
      let s : unitInterval := ⟨4 * (t : ℝ), by constructor <;> linarith [t.2.1, t.2.2, h₁]⟩
      have hsv : (s : ℝ) = 4 * (t : ℝ) := rfl
      have hd : Λ t - Λ 0 = star (B s) - ((x' : ℝ) : ℂ) := by
        rw [hval1 t h₁ s hsv, hP1_app, hA_app, hΛ0]
        push_cast
        ring
      rw [hd, Work.GATE2.slitAt]
      rintro ⟨him, hre'⟩
      have hz : (B s).im = 0 := by
        rw [Complex.sub_im, Complex.ofReal_im, sub_zero, hconj_im] at him
        linarith
      have hs0 : (s : ℝ) = 0 := by
        by_contra hne
        exact hsgn s (lt_of_le_of_ne s.2.1 (Ne.symm hne)) hz
      have hBs : B s = ((x' : ℝ) : ℂ) := by
        have hs : s = 0 := Subtype.ext hs0
        rw [hs, hB0]
      have hzero : star (B s) - ((x' : ℝ) : ℂ) = 0 := by
        rw [hBs, hconj_real]
        ring
      rw [hzero] at hre'
      norm_num at hre'
    · have h₁' : 1 / 4 < (t : ℝ) := not_le.mp h₁
      by_cases h₂ : (t : ℝ) ≤ 1 / 2
      · -- the second ray piece
        let s : unitInterval :=
          ⟨4 * (t : ℝ) - 1, by constructor <;> linarith [t.2.1, t.2.2, h₁', h₂]⟩
        have hsv : (s : ℝ) = 4 * (t : ℝ) - 1 := rfl
        have hd : Λ t - Λ 0 = Lray.γ₂ (s₁ - 1 + (s : ℝ)) - (((x' - 1 / 2 : ℝ)) : ℂ) := by
          rw [hval2 t h₁' h₂ s hsv, hP2_app, hΛ0]
        rw [hd, Work.GATE2.slitAt]
        rintro ⟨him, hre'⟩
        have hz : (Lray.γ₁ (s₁ - 1 + (s : ℝ))).im = 0 := by
          rw [Complex.sub_im, Complex.ofReal_im, sub_zero, hγ₂im] at him
          linarith
        exact hsgnγ (s₁ - 1 + (s : ℝ)) hz
      · -- the reflected arc `B`, reversed
        have h₂' : 1 / 2 < (t : ℝ) := not_le.mp h₂
        let s : unitInterval := ⟨2 - 2 * (t : ℝ), by constructor <;> linarith [t.2.1, t.2.2, h₂']⟩
        have hsv : (s : ℝ) = 2 - 2 * (t : ℝ) := rfl
        have hd : Λ t - Λ 0 = star (B s) - ((x' : ℝ) : ℂ) + 1 := by
          rw [hval3 t h₂' s hsv, hA_app, hΛ0]
          push_cast
          ring
        rw [hd, Work.GATE2.slitAt]
        rintro ⟨him, hre'⟩
        have hz : (B s).im = 0 := by
          rw [Complex.add_im, Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.one_im,
            hconj_im] at him
          linarith
        have hs0 : (s : ℝ) = 0 := by
          by_contra hne
          exact hsgn s (lt_of_le_of_ne s.2.1 (Ne.symm hne)) hz
        have hBs : B s = ((x' : ℝ) : ℂ) := by
          have hs : s = 0 := Subtype.ext hs0
          rw [hs, hB0]
        have hone : star (B s) - ((x' : ℝ) : ℂ) + 1 = 1 := by
          rw [hBs, hconj_real]
          ring
        rw [hone] at hre'
        norm_num at hre'
  -- ## 12. the exit loop, from the general curve lemma
  refine exitLoop_of_curve (α := Work.EL.alpha2) (x₀ := x' + 1 / 2) fl Λ.toContinuousMap ?_ ?_
    hre hKmem hwin hflr hslit
  · show Λ 0 = (((x' + 1 / 2) - 1 : ℝ) : ℂ)
    rw [hΛ0]
    push_cast
    ring
  · show Λ 1 = ((x' + 1 / 2 : ℝ) : ℂ)
    rw [hΛ1]

end Work.GATE2.EXL
