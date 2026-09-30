import Mathlib
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.StemsB.PiMap

/-!
# Exactness at `π₁` of the fibre sequence `π₁(F) → π₁(A) → π₁(X)`

Let `i : A → X` be a continuous map and `F = homotopyFibre i a` its homotopy fibre over `a`,
with projection `homotopyFibreFst i a : F → A`.  The purpose of this file is the degree-one
exactness statement

  `x ∈ ker (π₁(A) →^{π₁(i)} π₁(X))  ⟹  x ∈ im (π₁(F) →^{π₁(fst)} π₁(A))`,

i.e. every class in `π₁(A,a)` killed by `i` is the projection of a class on the homotopy fibre.

**Proof.**  This is the low-degree end of the long exact sequence of the fibration
`ΩX → F → A`, but it requires no fibration theory at all: the homotopy fibre is *defined* as the
space of pairs `(b, γ)` with `γ` a path in `X` from `i a` to `i b`, so a class in the kernel of
`π₁(i)` can be lifted explicitly.  Given a loop `γ` in `A` at `a` whose image under `i` is
null-homotopic, pick a null-homotopy `H : i ∘ γ ≃ const` relative to the boundary.  For each
parameter `t` the formula `s ↦ H (σ s, t)` (`σ` the reversal of the unit interval) is a path in
`X` from `i a` to `i (γ t)`; assembling these gives a loop `t ↦ (γ t, s ↦ H (σ s, t))` in the
homotopy fibre which projects *exactly* onto `γ`, hence is the required preimage.

The file is used in `Work.Serre` to reduce statements about `π₁` of a map to statements about its
homotopy fibre (`Work.RatHurewicz.RelHomotopy` fixes the conventions used for the fibre).
-/

open scoped Topology Topology.Homotopy unitInterval

open Work.StemsB

namespace Work.Serre

/-- **A class in the kernel of `π₁(i)` is the projection of a class on the homotopy fibre.**

If `x : π₁(A,a)` satisfies `π₁(i)(x) = 1`, then `x` lies in the image of

  `π₁(homotopyFibre i a) → π₁(A,a)`

induced by the first projection of the homotopy fibre.  This is the exactness at `π₁(A)` of the
fibre sequence `π₁(ΩX) → π₁(F) → π₁(A) → π₁(X)`. -/
theorem fst_eq_of_piMap_one_eq_one {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (a : A) (x : HomotopyGroup (Fin 1) A a)
    (hx : Work.StemsB.πmap i 0 a x = 1) :
    ∃ y : HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a)
        (Work.RatHurewicz.homotopyFibreBasepoint i a),
      Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a) 0
        (Work.RatHurewicz.homotopyFibreBasepoint i a) y = x := by
  -- replace `x` by an explicit loop `γ`
  obtain ⟨γ, rfl⟩ := Quotient.exists_rep x
  -- the class of `i ∘ γ` is trivial; unpack a null-homotopy `H` relative to the boundary
  rw [Work.StemsB.πmap_apply_mk, HomotopyGroup.one_def] at hx
  obtain ⟨H⟩ := Quotient.exact hx
  -- the reversal of the unit interval, on the level of continuous maps
  let rev2 : C((Fin 1 → I) × I, X) :=
    ⟨fun p => H (unitInterval.symm p.2, p.1), by
      exact H.continuous_toFun.comp
        ((unitInterval.continuous_symm.comp continuous_snd).prodMk continuous_fst)⟩
  -- `s ↦ H (σ s, y)` is a path in `X` starting at `i a` (here `y` is the loop parameter)
  have hpath_prop : ∀ y : Fin 1 → I, (rev2.curry y) 0 = i a := by
    intro y
    rw [ContinuousMap.curry_apply]
    show H (unitInterval.symm 0, y) = i a
    rw [unitInterval.symm_zero, H.apply_one]
    rfl
  let pathCM : C(Fin 1 → I, PathSpace X (i a)) :=
    ⟨fun y => ⟨rev2.curry y, hpath_prop y⟩,
      Continuous.subtype_mk rev2.curry.continuous hpath_prop⟩
  -- and it ends at `i (γ y)`, so that `(γ y, pathCM y)` is a point of the homotopy fibre
  have hbundle_prop : ∀ y : Fin 1 → I, (evalOne X (i a)) (pathCM y) = i (γ.1 y) := by
    intro y
    show (pathCM y).1 1 = i (γ.1 y)
    show (rev2.curry y) 1 = i (γ.1 y)
    rw [ContinuousMap.curry_apply]
    show H (unitInterval.symm 1, y) = i (γ.1 y)
    rw [unitInterval.symm_one, H.apply_zero]
    rfl
  let bundleCM : C(Fin 1 → I, Work.RatHurewicz.homotopyFibre i a) :=
    ⟨fun y => ⟨(γ.1.prodMk pathCM) y, hbundle_prop y⟩,
      Continuous.subtype_mk (γ.1.prodMk pathCM).continuous hbundle_prop⟩
  -- on the boundary of the cube the pair is the base point of the fibre
  have hbdd : ∀ y ∈ Cube.boundary (Fin 1),
      bundleCM y = Work.RatHurewicz.homotopyFibreBasepoint i a := by
    intro y hy
    apply Subtype.ext
    apply Prod.ext
    · show γ.1 y = a
      exact γ.2 y hy
    · apply Subtype.ext
      apply ContinuousMap.ext
      intro s
      show (rev2.curry y) s = i a
      rw [ContinuousMap.curry_apply]
      show H (unitInterval.symm s, y) = i a
      rw [H.eq_fst (unitInterval.symm s) hy]
      change i (γ.1 y) = i a
      rw [γ.2 y hy]
  refine ⟨⟦(⟨bundleCM, hbdd⟩ : Ω^ (Fin 1) (Work.RatHurewicz.homotopyFibre i a)
      (Work.RatHurewicz.homotopyFibreBasepoint i a))⟧, ?_⟩
  -- its projection under `homotopyFibreFst` is literally `γ`
  rw [Work.StemsB.πmap_apply_mk]
  apply congrArg Quotient.mk''
  apply GenLoop.ext
  intro y
  exact rfl

end Work.Serre
