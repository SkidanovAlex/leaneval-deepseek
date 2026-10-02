import Mathlib
import Submission.Work.ThomBordism.h0SignUnit
import Submission.Work.ThomBordism.coeff_pm_one_of_normalized
import Submission.Work.ThomBordism.localThomMap_cup_general

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false

/-!
# Multiplying a local Thom class by an involution of `H⁰` preserves the Thom property

Let `Z → B` be a real bundle and `τ ∈ H^n(X|_W, X|_W∖0)` a *local* Thom class over a piece `W ⊆ B`,
i.e. the local Thom map

  `Work.Thom.localThomMap Z n W τ k : H^k(W;ℤ) → H^{k+n}(X|_W, X|_W∖0)`,  `x ↦ π_W^*(x) ⌣ τ`

is bijective in every degree.  If `s ∈ H⁰(W;ℤ)` is an **involution** under the cup product
(`s ⌣ s = 1`), then the class `π_W^*(s) ⌣ τ` — that is, `Work.Thom.localThomMap Z n W τ 0 s`, a
class in degree `0 + n`, transported to degree `n` — is again a local Thom class.

The reason is `H⁰`-linearity of the local Thom map
(`Work.ThomBordism.localThomMap_cup_general`): for every `k` and every `x ∈ H^k(W;ℤ)`,

  `localThomMap Z n W (π^*(s) ⌣ τ) k x = localThomMap Z n W τ k (x ⌣ s)`,

so the new local Thom map is the composite of the old one (bijective by hypothesis) with the map
`x ↦ x ⌣ s`, which is bijective because `s` is its own inverse (`(x ⌣ s) ⌣ s = x ⌣ (s ⌣ s) = x`).

This is the step used in `Work.ThomBordism.thomClass_fibreGenerator` to normalise the coefficient
of a Thom class over a chart (`Work.ThomBordism.h0SignUnit` produces exactly such an involution).
-/

namespace Work.ThomBordism

open CategoryTheory

/-- **Cupping with an involution of `H⁰(W;ℤ)` is bijective in every degree.**  If `c ⌣ c = 1`
then the map `x ↦ x ⌣ c` on `H^k(W;ℤ)` is its own inverse, hence bijective.  (The `H⁰` statement
`Work.ThomBordism.bijective_cup_of_involution` in
`Submission/Work/ThomBordism/localThom_of_fibreGenerator_chart.lean` is the same computation,
stated there for the convenience of that file.) -/
theorem bijective_cupH'_of_involution {B : Type} [TopologicalSpace B] (W : Set B)
    (c : Work.Thom.Coh ℤ 0 ↥W)
    (hc : (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) 0 0) c c
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥W))) (k : ℕ) :
    Function.Bijective (fun x : Work.Thom.Coh ℤ k ↥W =>
      (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) k 0) x c) := by
  -- `x ↦ x ⌣ c` is its own inverse: `(x ⌣ c) ⌣ c = x ⌣ (c ⌣ c) = x ⌣ 1 = x`.
  have hinv : ∀ y : Work.Thom.Coh ℤ k ↥W,
      (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) k 0)
        ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) k 0) y c) c = y := by
    intro y
    have h1 := Work.Cohomology.cupH'_assoc ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) k 0 0 y c c
    rw [hc, Work.Cohomology.cupH'_one_right] at h1
    exact h1
  refine ⟨fun x y hxy => ?_, fun y => ⟨_, hinv y⟩⟩
  have h2 := congrArg (fun w =>
    (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) k 0) w c) hxy
  rwa [hinv x, hinv y] at h2

theorem localThom_of_involution_smul {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) {W : Set B}
    (τ : Work.Thom.PieceCoh Z W n)
    (hτ : ∀ k : ℕ, Function.Bijective (Work.Thom.localThomMap Z n W τ k))
    (s : Work.Thom.Coh ℤ 0 ↥W)
    (hs : ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) 0 0) s s)
        = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥W))) :
    ∀ k : ℕ, Function.Bijective (Work.Thom.localThomMap Z n W
      ((Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W τ 0 s)) k) := by
  intro k
  -- `H⁰`-linearity of the local Thom map: the new local Thom map is the old one composed with
  -- the cup product with `s`.
  have hfun : ⇑(Work.Thom.localThomMap Z n W
        ((Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W τ 0 s)) k)
      = ⇑(Work.Thom.localThomMap Z n W τ k) ∘
        (fun x : Work.Thom.Coh ℤ k ↥W =>
          (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) k 0) x s) := by
    funext x
    exact localThomMap_cup_general Z n W τ s k x
  rw [hfun]
  exact (hτ k).comp (bijective_cupH'_of_involution W s hs k)

end Work.ThomBordism
