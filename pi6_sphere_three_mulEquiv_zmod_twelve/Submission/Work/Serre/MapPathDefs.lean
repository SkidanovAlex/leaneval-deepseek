import Mathlib
import Submission.Work.Serre.E3aDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The mapping path space: vocabulary for Step A of `Work.Serre.SerreE3a`

For `p : E → B` the **mapping path space** is

`mpath p = {x : E × C(I,B) // x.2 0 = p x.1}`,

the space of pairs `(e, γ)` where `γ` is a path in `B` starting at `p e`.  It sits in the square

```
mpath p --mpathSnd--> C(I,B)
   |                     |
 mpathFst               ev₀
   v                     v
   E -------p----------> B
```

and `mpathQ p = ev₁ ∘ mpathSnd` sends `(e,γ)` to `γ 1`.

This file collects only the definitions and the *elementary* lemmas:
`mpathHomotopyQ` (the homotopy `p ∘ mpathFst ~ mpathQ`) and the rational
homotopy invariance of `ratHomologyMap`.  The three non-trivial facts about the construction
(`mpathQ` is a Serre fibration; `mpathFst` is a homotopy equivalence; the fibre of `mpathQ`
over `p e₀` is `homotopyFibre p e₀`) are stated and proved in sibling files.
-/

open scoped Topology unitInterval
open ContinuousMap

namespace Work.Serre

noncomputable section

/-- The **mapping path space** of `p : E → B`: the space of pairs `(e, γ)` with `γ` a path in `B`
starting at `p e`. -/
def mpath {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) : Type _ :=
  {x : E × C(I, B) // x.2 0 = p x.1}

instance instTopologicalSpaceMpath {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) : TopologicalSpace (mpath p) :=
  inferInstanceAs (TopologicalSpace {x : E × C(I, B) // x.2 0 = p x.1})

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The projection `(e, γ) ↦ e` of the mapping path space. -/
def mpathFst (p : C(E, B)) : C(mpath p, E) where
  toFun x := x.1.1
  continuous_toFun := continuous_fst.comp continuous_subtype_val

/-- The projection `(e, γ) ↦ γ` of the mapping path space. -/
def mpathSnd (p : C(E, B)) : C(mpath p, C(I, B)) where
  toFun x := x.1.2
  continuous_toFun := continuous_snd.comp continuous_subtype_val

/-- The endpoint projection `q (e, γ) = γ 1` of the mapping path space. -/
def mpathQ (p : C(E, B)) : C(mpath p, B) where
  toFun x := x.1.2 1
  continuous_toFun := continuous_eval.comp ((mpathSnd p).continuous.prodMk continuous_const)

/-- The section `e ↦ (e, const (p e))` of the projection `mpathFst p`. -/
def mpathOf (p : C(E, B)) : C(E, mpath p) where
  toFun e := ⟨(e, ContinuousMap.const I (p e)), rfl⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.prodMk continuous_id ?_) _
    have h1 : Continuous fun e : E => ((ContinuousMap.fst : C(B × I, B)).curry (p e)) :=
      ((ContinuousMap.fst : C(B × I, B)).curry).continuous.comp p.continuous
    refine h1.congr ?_
    intro e
    ext s
    simp [ContinuousMap.curry_apply]

/-- **The homotopy `p ∘ mpathFst ~ mpathQ`**, given by `(e, γ, t) ↦ γ t`.  Its two ends are
`p e = γ 0` and `γ 1`. -/
def mpathHomotopyQ (p : C(E, B)) : (p.comp (mpathFst p)).Homotopy (mpathQ p) where
  toContinuousMap :=
    ⟨fun xt : I × mpath p => (mpathSnd p) xt.2 xt.1,
      continuous_eval.comp (((mpathSnd p).continuous.comp continuous_snd).prodMk continuous_fst)⟩
  map_zero_left x := x.2
  map_one_left _ := rfl

/-- `p ∘ mpathFst` and `mpathQ` are homotopic. -/
theorem mpath_homotopic (p : C(E, B)) : (p.comp (mpathFst p)).Homotopic (mpathQ p) :=
  ⟨mpathHomotopyQ p⟩

/-- **Homotopy invariance of `ratHomologyMap`.**  Homotopic maps induce equal maps on rational
singular homology in every degree. -/
theorem ratHomologyMap_eq_of_homotopic {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (n : ℕ) :
    ratHomologyMap f n = ratHomologyMap g n :=
  TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H (ModuleCat.of ℚ ℚ) n

/-! ## Reversal of paths

The fibre of `mpathQ p` over `p e₀` consists of the pairs `(e, γ)` with `γ` a path from `p e` to
`p e₀`, while the homotopy fibre `Work.RatHurewicz.homotopyFibre p e₀` consists of the pairs `(e, δ)`
with `δ` a path from `p e₀` to `p e`.  The two are identified by the reversal of paths,
`revPath`, which is a *homeomorphism* of path spaces (precomposition with the reversal of the unit
interval). -/

/-- The reversal `s ↦ 1 - s` of the unit interval, as a continuous map. -/
def revI : C(I, I) := ⟨unitInterval.symm, unitInterval.continuous_symm⟩

@[simp] theorem revI_zero : revI 0 = 1 := unitInterval.symm_zero

@[simp] theorem revI_one : revI 1 = 0 := unitInterval.symm_one

@[simp] theorem revI_comp_revI : revI.comp revI = ContinuousMap.id I := by
  ext s
  simp [revI, unitInterval.symm_symm]

/-- **Reversal of paths**, `γ ↦ γ ∘ revI`, as a continuous map `C(I,B) → C(I,B)`. -/
def revPath (B : Type) [TopologicalSpace B] : C(C(I, B), C(I, B)) where
  toFun γ := γ.comp revI
  continuous_toFun := by
    refine continuous_of_continuous_uncurry (fun γ : C(I, B) => γ.comp revI) ?_
    have h : Continuous fun p : C(I, B) × I => p.1 p.2 := continuous_eval
    have h2 : Continuous fun p : C(I, B) × I => revI p.2 :=
      revI.continuous.comp (continuous_snd : Continuous fun p : C(I, B) × I => p.2)
    refine (h.comp (Continuous.prodMk
      (continuous_fst : Continuous fun p : C(I, B) × I => p.1) h2)).congr ?_
    intro p
    rfl

theorem revPath_apply (B : Type) [TopologicalSpace B] (γ : C(I, B)) (s : I) :
    revPath B γ s = γ (revI s) := rfl

@[simp] theorem revPath_zero (B : Type) [TopologicalSpace B] (γ : C(I, B)) :
    revPath B γ 0 = γ 1 := by rw [revPath_apply, revI_zero]

@[simp] theorem revPath_one (B : Type) [TopologicalSpace B] (γ : C(I, B)) :
    revPath B γ 1 = γ 0 := by rw [revPath_apply, revI_one]

@[simp] theorem revPath_revPath (B : Type) [TopologicalSpace B] (γ : C(I, B)) :
    revPath B (revPath B γ) = γ := by
  show (γ.comp revI).comp revI = γ
  rw [ContinuousMap.comp_assoc, revI_comp_revI, ContinuousMap.comp_id]

end

end Work.Serre
