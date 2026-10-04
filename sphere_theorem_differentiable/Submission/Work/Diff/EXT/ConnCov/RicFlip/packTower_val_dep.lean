import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.TInvDefs
import Submission.Work.Diff.GE.cov2RmExt_prelim

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Value dependence of the packed tower from the invariants `PInv`

`Work.Diff.EXT.ConnCov.RicFlip.PInv g base k` (in `TInvDefs.lean`) collects the three invariants of
the packed tower: smoothness on smooth tuples, `C^∞`-linearity in every slot (two-term form), and
germ-locality at every point.

This module derives from them the *tensoriality* of the packed tower: its value at `x` depends only
on the values of the `k+3` slot fields at `x`.

* `packTower_val_dep_slot` is the single-slot statement, obtained from the value-dependence machine
  `Work.Diff.GE.field_value_dep_of_linear` (`Submission/Work/Diff/GE/cov2RmExt_prelim.lean`), whose
  two inputs are exactly `PInv`'s linearity and germ-locality clauses.
* `packTower_val_dep` is the all-slots statement, by a `Finset` induction replacing the slots one
  after the other (each step is the single-slot statement).
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ConnCov.RicFlip

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- **Value dependence in a single slot.**  If `G` is a tuple of smooth fields and `X` is a smooth
field with `X x = G i x`, then the value of the packed tower at `x` does not change when slot `i`
of `G` is replaced by `X`. -/
theorem packTower_val_dep_slot (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (h : PInv g base k)
    {G : Fin (k + 3) → (Π y : M, TangentSpace I y)}
    (hG : ∀ s, Work.Diff.EXT.ATower.SmE I M (G s)) (i : Fin (k + 3))
    {X : Π y : M, TangentSpace I y} (hX : Work.Diff.EXT.ATower.SmE I M X) (x : M)
    (hx : X x = G i x) :
    packTower g base k (Function.update G i X) x = packTower g base k G x := by
  classical
  have hsm_upd : ∀ (Y : Π y : M, TangentSpace I y), Work.Diff.EXT.ATower.SmE I M Y →
      ∀ s, Work.Diff.EXT.ATower.SmE I M ((Function.update G i Y) s) := by
    intro Y hY s
    by_cases hs : s = i
    · rw [hs, Function.update_self]; exact hY
    · rw [Function.update_of_ne hs]; exact hG s
  have hlinArg : ∀ (X₁ X₂ : Π y : M, TangentSpace I y) (f₁ f₂ : M → ℝ),
      Work.Diff.EXT.ATower.SmE I M X₁ → Work.Diff.EXT.ATower.SmE I M X₂ →
      Work.Diff.EXT.ATower.SmF I M f₁ → Work.Diff.EXT.ATower.SmF I M f₂ →
      packTower g base k (Function.update G i (f₁ • X₁ + f₂ • X₂)) x
        = f₁ x * packTower g base k (Function.update G i X₁) x
          + f₂ x * packTower g base k (Function.update G i X₂) x := by
    intro X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂
    have hh := congrFun ((h G hG).2.1 i X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂) x
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply] using hh
  have hgermArg : ∀ (X X' : Π y : M, TangentSpace I y),
      Work.Diff.EXT.ATower.SmE I M X → Work.Diff.EXT.ATower.SmE I M X' →
      X =ᶠ[𝓝 x] X' →
      packTower g base k (Function.update G i X) x = packTower g base k (Function.update G i X') x := by
    intro X X' hX' hX'' hev
    have heq' : ∀ s, (Function.update G i X) s =ᶠ[𝓝 x] (Function.update G i X') s := by
      intro s
      by_cases hs : s = i
      · rw [hs, Function.update_self, Function.update_self]; exact hev
      · rw [Function.update_of_ne hs, Function.update_of_ne hs]
        try exact Filter.EventuallyEq.refl _ _
    exact ((h (Function.update G i X) (hsm_upd X hX')).2.2 x (Function.update G i X')
      (hsm_upd X' hX'') heq').eq_of_nhds
  have hupdself : Function.update G i (G i) = G := by
    funext j
    by_cases hj : j = i
    · rw [hj, Function.update_self]
    · rw [Function.update_of_ne hj]
  have hmain := Work.Diff.GE.field_value_dep_of_linear (I := I) (M := M) x
    (F := fun Y : Π y : M, TangentSpace I y => packTower g base k (Function.update G i Y) x)
    hlinArg hgermArg (hG i) hX hx.symm
  rw [hupdself] at hmain
  exact hmain.symm

/-- **Value dependence in all slots.**  If two tuples of smooth fields have the same values at `x`,
then the packed tower takes the same value at `x` on them. -/
theorem packTower_val_dep (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (h : PInv g base k)
    {F F' : Fin (k + 3) → (Π y : M, TangentSpace I y)}
    (hF : ∀ s, Work.Diff.EXT.ATower.SmE I M (F s))
    (hF' : ∀ s, Work.Diff.EXT.ATower.SmE I M (F' s)) (x : M)
    (hv : ∀ s, F s x = F' s x) :
    packTower g base k F x = packTower g base k F' x := by
  classical
  have key : ∀ s : Finset (Fin (k + 3)), ∀ G : Fin (k + 3) → (Π y : M, TangentSpace I y),
      (∀ j, Work.Diff.EXT.ATower.SmE I M (G j)) →
      (∀ j ∈ s, G j = F' j) → (∀ j ∉ s, G j = F j) →
      packTower g base k G x = packTower g base k F x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro G hG _ h2
        rw [show G = F from funext (fun j => h2 j (Finset.notMem_empty j))]
    | insert i s hi ih =>
        intro G hG h1 h2
        have hGi : G i x = F i x := by
          rw [h1 i (Finset.mem_insert_self i s), hv i]
        have hstep : packTower g base k (Function.update G i (F i)) x
            = packTower g base k G x :=
          packTower_val_dep_slot g base k h hG i (hF i) x hGi.symm
        have hsm1 : ∀ j, Work.Diff.EXT.ATower.SmE I M ((Function.update G i (F i)) j) := by
          intro j
          by_cases hj : j = i
          · rw [hj, Function.update_self]; exact hF i
          · rw [Function.update_of_ne hj]; exact hG j
        have h1' : ∀ j ∈ s, (Function.update G i (F i)) j = F' j := by
          intro j hj
          have hji : j ≠ i := fun hc => hi (hc ▸ hj)
          rw [Function.update_of_ne hji]
          exact h1 j (Finset.mem_insert_of_mem hj)
        have h2' : ∀ j ∉ s, (Function.update G i (F i)) j = F j := by
          intro j hj
          by_cases hji : j = i
          · rw [hji, Function.update_self]
          · rw [Function.update_of_ne hji]
            exact h2 j (fun hmem => by
              rcases Finset.mem_insert.mp hmem with h | h
              · exact hji h
              · exact hj h)
        exact hstep.symm.trans (ih (Function.update G i (F i)) hsm1 h1' h2')
  have hfin := key Finset.univ F' hF' (fun j _ => rfl)
    (fun j hj => absurd (Finset.mem_univ j) hj)
  exact hfin.symm

end Work.Diff.EXT.ConnCov.RicFlip
