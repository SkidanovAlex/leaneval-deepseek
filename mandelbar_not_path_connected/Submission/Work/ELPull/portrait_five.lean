import Mathlib
import Submission.Work.ELPull.Defs
import Submission.Work.ELPull.landsN_image
import Submission.Work.ELPull.portrait_step
import Submission.Work.ELPull.alpha_iter_arith

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.ELPull.portrait_five` — the first five levels of the root portrait

The root-parabolic bundle `RootParabolic c` carries a simple parabolic point `z₁` of
`(Tsq c)^[5] = (Tantibar c)^[10]` together with the two root rays `α₁ = 371/1023`,
`α₂ = 404/1023`, which are the two rays landing at `z₁` (`hzero`).  This file proves that
the portrait persists along the first five iterates:

  for `j < 5`, the rays of `[0,1)` landing at `(Tantibar c)^[j] z₁` are exactly the two
  angles `T^[j] α₁` and `T^[j] α₂`.

The two inputs are

* `himg` — the image rule: a ray landing at `y` is carried to the ray of doubled angle
  landing at `Tantibar c y` (this is `Work.ELPull.landsN_image`);
* `hcount` — the orbit-portrait count (`PortraitCount`): at a preimage of a two-ray point
  the doubling map `T` is injective on the landing angles.

The proof runs around the cycle of the parabolic point in the *reverse* direction of the
dynamics, which is the direction in which `hcount` applies (it controls the preimage
`y' = (Tantibar c)^[j] z₁` of `y = (Tantibar c)^[j+1] z₁`):

* `hLand` — the image rule iterated gives the landing `T^[j] α_i ↦ (Tantibar c)^[j] z₁` for
  every `j`, with no need of the periodicity of the orbit;
* `hP0` is `hzero`; `hP5` is the same statement transported once around the cycle using
  `(Tantibar c)^[5] z₁ = z₁` and `T^[5] α₁ = α₂`, `T^[5] α₂ = α₁`;
* the step `hstep` (`Work.ELPull.portrait_step`) replaces the portrait at the preimage
  `(Tantibar c)^[j] z₁` by the portrait at `(Tantibar c)^[j+1] z₁`: it uses `hcount` for the
  two-ray hypothesis at the latter and `hLand` for the two known rays of the former, and the
  arithmetic of the root angles (`Work.ELPull.alpha_iter_arith`) for the memberships in
  `[0,1)` and the distinctness;
* applying the step to `hP5, hP4, hP3, hP2, hP1` gives the five levels.
-/

namespace Work.ELPull

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

theorem portrait_five {c : ℂ} (d : RootParabolic c)
    (himg : ∀ {θ' : ℝ} {y : ℂ}, LandsN d.hN θ' y →
      LandsN d.hN (T θ') (LeanEval.ComplexAnalysis.Tantibar c y))
    (hzero : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (LandsN d.hN θ d.z₁ ↔ θ = alpha1 ∨ θ = alpha2))
    (hcount : PortraitCount d.hN) :
    ∀ j : ℕ, j < 5 → ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (LandsN d.hN θ ((LeanEval.ComplexAnalysis.Tantibar c)^[j] d.z₁) ↔
        θ = T^[j] alpha1 ∨ θ = T^[j] alpha2) := by
  obtain ⟨harith, hT5a, hT5b⟩ := alpha_iter_arith
  -- the iterated image rule: `T^[j] α` lands at the `j`-th iterate of `z₁`
  have hLand : ∀ j : ℕ,
      LandsN d.hN ((T^[j]) alpha1) ((Tantibar c)^[j] d.z₁) ∧
      LandsN d.hN ((T^[j]) alpha2) ((Tantibar c)^[j] d.z₁) := by
    intro j
    induction j with
    | zero =>
        exact ⟨(hzero alpha1 (harith 0 (by norm_num)).1).mpr (Or.inl rfl),
               (hzero alpha2 (harith 0 (by norm_num)).2.1).mpr (Or.inr rfl)⟩
    | succ k ih =>
        refine ⟨?_, ?_⟩
        · rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
          exact himg ih.1
        · rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
          exact himg ih.2
  -- the portrait at `z₁`, and at `(Tantibar c)^[5] z₁ = z₁`
  have hP0 : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (LandsN d.hN θ d.z₁ ↔ θ = alpha1 ∨ θ = alpha2) := hzero
  have hP5 : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (LandsN d.hN θ ((Tantibar c)^[5] d.z₁) ↔
        θ = T^[5] alpha1 ∨ θ = T^[5] alpha2) := by
    intro θ hθ
    have h := hzero θ hθ
    rw [d.per.1, hT5a, hT5b]
    constructor
    · intro hl
      rcases h.mp hl with h1 | h1
      · exact Or.inr h1
      · exact Or.inl h1
    · rintro (h1 | h1)
      · exact h.mpr (Or.inr h1)
      · exact h.mpr (Or.inl h1)
  -- one step of the descent, from the `(j+1)`-st level to the `j`-th
  have hstep : ∀ j : ℕ, j ≤ 4 →
      (∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
        (LandsN d.hN θ ((Tantibar c)^[j+1] d.z₁) ↔
          θ = T^[j+1] alpha1 ∨ θ = T^[j+1] alpha2)) →
      (∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
        (LandsN d.hN θ ((Tantibar c)^[j] d.z₁) ↔
          θ = T^[j] alpha1 ∨ θ = T^[j] alpha2)) := by
    intro j hj hnext
    have hAj := harith j (by omega)
    have hAj1 := harith (j+1) (by omega)
    have hL := hLand j
    refine portrait_step (u := T^[j+1] alpha1) (v := T^[j+1] alpha2)
      (u' := T^[j] alpha1) (v' := T^[j] alpha2)
      himg hcount ?_ hAj1.1 hAj1.2.1 hAj1.2.2 hnext hAj.1 hAj.2.1 ?_ ?_ hL.1 hL.2
    · rw [Function.iterate_succ_apply']
    · rw [Function.iterate_succ_apply']
    · rw [Function.iterate_succ_apply']
  have hP4 := hstep 4 (by norm_num) hP5
  have hP3 := hstep 3 (by norm_num) hP4
  have hP2 := hstep 2 (by norm_num) hP3
  have hP1 := hstep 1 (by norm_num) hP2
  intro j hj θ hθ
  interval_cases j
  · exact hP0 θ hθ
  · exact hP1 θ hθ
  · exact hP2 θ hθ
  · exact hP3 θ hθ
  · exact hP4 θ hθ

end Work.ELPull
