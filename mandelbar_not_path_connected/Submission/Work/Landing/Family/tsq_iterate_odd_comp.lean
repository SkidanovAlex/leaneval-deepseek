import Mathlib
import Submission.Work.Landing.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Family

/-- Rotation identity for iterates of a composite: conjugating an iterate of `g ∘ f` by `g`
turns it into an iterate of `f ∘ g`:
`(g ∘ f)^[n] ∘ g = g ∘ (f ∘ g)^[n]`. -/
private lemma iterate_comp_comp {α : Type*} (f g : α → α) (n : ℕ) :
    (g ∘ f)^[n] ∘ g = g ∘ (f ∘ g)^[n] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ', Function.iterate_succ']
    simp only [Function.comp_assoc]
    rw [ih]

/-- Odd iterate of a composite.  Writing `T = g ∘ f` and `S = f ∘ g`, the iterate
`T^[2m+1] = T^[m] ∘ T ∘ T^[m]` splits at the middle occurrence of `T = g ∘ f`; the rotation
identity moves the left `T^[m]` past `g` and produces
`T^[2m+1] = (g ∘ S^[m]) ∘ (f ∘ T^[m])`. -/
private lemma iterate_odd_comp {α : Type*} (f g : α → α) (m : ℕ) :
    (g ∘ f)^[2 * m + 1] = (g ∘ (f ∘ g)^[m]) ∘ (f ∘ (g ∘ f)^[m]) := by
  have hA : (g ∘ f)^[m] ∘ g = g ∘ (f ∘ g)^[m] := iterate_comp_comp f g m
  have hm : 2 * m + 1 = m + 1 + m := by omega
  calc (g ∘ f)^[2 * m + 1]
      = (g ∘ f)^[m + 1] ∘ (g ∘ f)^[m] := by rw [hm, Function.iterate_add]
    _ = ((g ∘ f)^[m] ∘ (g ∘ f)) ∘ (g ∘ f)^[m] := by rw [Function.iterate_succ]
    _ = ((g ∘ f)^[m] ∘ g) ∘ (f ∘ (g ∘ f)^[m]) := by
          rw [← Function.comp_assoc ((g ∘ f)^[m]) g f,
              Function.comp_assoc ((g ∘ f)^[m] ∘ g) f ((g ∘ f)^[m])]
    _ = (g ∘ (f ∘ g)^[m]) ∘ (f ∘ (g ∘ f)^[m]) := by rw [hA]

/-- For odd `k`, the `k`-th iterate of the holomorphic second iterate `Tsq c = (·² + c̄)² + c`
factors through the "half" maps `z ↦ z² + c̄` and `z ↦ z² + c`, one copy of each with the
conjugated and unconjugated `k/2`-iterates inserted in the middle. -/
theorem tsq_iterate_odd_comp (c : ℂ) {k : ℕ} (hk : Odd k) :
    (Work.Landing.Tsq c)^[k] =
      (fun w : ℂ => ((Work.Landing.Tsq (star c))^[k / 2] w) ^ 2 + c) ∘
        (fun z : ℂ => ((Work.Landing.Tsq c)^[k / 2] z) ^ 2 + star c) := by
  have hk2 : k = 2 * (k / 2) + 1 := by
    have hmod : k % 2 = 1 := Nat.odd_iff.mp hk
    have h := Nat.div_add_mod k 2
    omega
  have hgen := iterate_odd_comp (fun z : ℂ => z ^ 2 + star c) (fun z : ℂ => z ^ 2 + c) (k / 2)
  have hcomp1 : (fun z : ℂ => z ^ 2 + c) ∘ (fun z : ℂ => z ^ 2 + star c) =
      Work.Landing.Tsq c := by
    funext z; simp [Work.Landing.Tsq, Function.comp]
  have hcomp2 : (fun z : ℂ => z ^ 2 + star c) ∘ (fun z : ℂ => z ^ 2 + c) =
      Work.Landing.Tsq (star c) := by
    funext z; simp [Work.Landing.Tsq, Function.comp]
  rw [hcomp1, hcomp2] at hgen
  conv_lhs => rw [hk2]
  rw [hgen]
  rfl

end Work.Landing.Family
