import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
import Submission.Work.Serre.hZeroOfPiZero
import Submission.Work.Serre.RangeOne.rangeWhitehead

/-!
# A homotopy equivalence induces a bijection on `πₙ`, in the `piMapN` normalization

If `e : X ≃ₕ Y` is a homotopy equivalence and `x : X`, then
`Work.Serre.piMapN e.toFun n x : πₙ(X,x) → πₙ(Y, e x)` is a bijection, for every `n` (including
`n = 0`).

This is the "bijectivity of the induced map on homotopy groups" statement in the form in which the
SERRE engine consumes it (`Work.Serre.piMapN` is the unshifted-index normalization of the induced
map used throughout `Submission/Work/Serre/`, and it agrees definitionally with the
`HomotopyGroup.map` of `Submission/Work/Stems/Pi.lean`).

## Route

* For `n ≥ 1` the base points `x` and `e.invFun (e.toFun x)` differ, so the induced maps do not
  literally compose to the identity; they compose to the identity up to the base-point change
  `Work.Stems.Pinch.transport` along the paths traced by the homotopies `e.left_inv`, `e.right_inv`
  (`Work.Stems.Pinch.transport_map`).  Concretely, with `f = e.toFun`, `g = e.invFun`,

  * `Φ (g_* (f_* a)) = a` for `Φ = transport (homotopyPath e.left_inv x)`, and
  * `Ψ (f_* (g_* b)) = b` for `Ψ = transport (homotopyPath e.right_inv (f x))`.

  The first identity gives injectivity of `f_*` (`Φ` is injective, with inverse the transport
  along the reversed path) and the injectivity of `g_*`; the injectivity of `g_*` together with the
  first identity applied to `Φ (g_* b)` then gives surjectivity of `f_*`.
* For `n = 0` there is no group structure and no `transport` (the Pinch construction needs a
  nonempty index type), so the argument goes through `π₀ ≅ ZerothHomotopy`
  (`HomotopyGroup.pi0EquivZerothHomotopy`): a homotopy equivalence induces a bijection of path
  components, and `Work.Serre.h0Pi0Map_square` transports that bijection back to `π₀`.
-/

set_option linter.style.haveILetI false

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre

noncomputable section

/-! ## The two normalizations of the induced map on homotopy groups agree -/

/-- The unshifted-index map `Work.Serre.piMapN` is the `HomotopyGroup.map` of
`Submission/Work/Stems/Pi.lean` (they are the same `Quotient.map` of postcomposition with `f`). -/
theorem piMapN_eq_homotopyGroupMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) (x : X) :
    piMapN f n x = HomotopyGroup.map f := by
  funext a
  induction a using Quotient.inductionOn with
  | h γ => rfl

/-! ## The case of a nonempty index type (`n ≥ 1`) -/

/-- **A homotopy equivalence induces a bijection on `π_N`** for a nonempty (finite) index type
`N` — the form in which the base-point change `Work.Stems.Pinch.transport` is available. -/
theorem bijective_homotopyGroupMap_of_homotopyEquiv {Q X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [Fintype Q] [Nonempty Q]
    (e : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    Function.Bijective (HomotopyGroup.map (N := Q) e.toFun (x := x)) := by
  obtain ⟨h1⟩ := e.left_inv
  obtain ⟨h2⟩ := e.right_inv
  -- `Φ (g_* (f_* a)) = a`
  have key1 : ∀ a : HomotopyGroup Q X x,
      Work.Stems.Pinch.transport (N := Q) (Work.Stems.Pinch.homotopyPath h1 x)
        (HomotopyGroup.map e.invFun (HomotopyGroup.map e.toFun a)) = a := by
    intro a
    rw [← HomotopyGroup.map_comp, Work.Stems.Pinch.transport_map, HomotopyGroup.map_id]
  -- `Ψ (f_* (g_* b)) = b`
  have key2 : ∀ b : HomotopyGroup Q Y (e.toFun x),
      Work.Stems.Pinch.transport (N := Q) (Work.Stems.Pinch.homotopyPath h2 (e.toFun x))
        (HomotopyGroup.map e.toFun (HomotopyGroup.map e.invFun b)) = b := by
    intro b
    rw [← HomotopyGroup.map_comp, Work.Stems.Pinch.transport_map, HomotopyGroup.map_id]
  -- the transport along a path is injective (its inverse is the transport along the reversed path)
  have hinjΦ : Function.Injective
      (Work.Stems.Pinch.transport (N := Q) (Work.Stems.Pinch.homotopyPath h1 x)) := by
    intro u v huv
    have h := Work.Stems.Pinch.transport_symm_apply (N := Q)
      (Work.Stems.Pinch.homotopyPath h1 x) u
    rw [huv, Work.Stems.Pinch.transport_symm_apply] at h
    exact h.symm
  -- hence `g_*` is injective (it is a section of `Ψ ∘ f_*`)
  have hg_inj : Function.Injective (HomotopyGroup.map (N := Q) e.invFun (x := e.toFun x)) := by
    intro b b' hbb'
    have h : HomotopyGroup.map e.toFun (HomotopyGroup.map e.invFun b)
        = HomotopyGroup.map e.toFun (HomotopyGroup.map e.invFun b') := by rw [hbb']
    rw [← key2 b, ← key2 b', h]
  refine ⟨?_, ?_⟩
  · intro a a' haa'
    have h1' : HomotopyGroup.map e.invFun (HomotopyGroup.map e.toFun a)
        = HomotopyGroup.map e.invFun (HomotopyGroup.map e.toFun a') := by rw [haa']
    rw [← key1 a, ← key1 a', h1']
  · intro b
    refine ⟨Work.Stems.Pinch.transport (N := Q) (Work.Stems.Pinch.homotopyPath h1 x)
      (HomotopyGroup.map e.invFun b), ?_⟩
    exact hg_inj (hinjΦ (key1 _))

/-! ## The case `n = 0` (`π₀`), via path components -/

/-- **A homotopy equivalence induces a bijection of path components**, i.e. of
`ZerothHomotopy`. -/
theorem bijective_h0Pi0Map_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) : Function.Bijective (h0Pi0Map e.toFun) := by
  obtain ⟨h1⟩ := e.left_inv
  obtain ⟨h2⟩ := e.right_inv
  constructor
  · intro u v huv
    induction u using ZerothHomotopy.rec with
    | mk xu =>
      induction v using ZerothHomotopy.rec with
      | mk xv =>
        rw [h0Pi0Map_mk, h0Pi0Map_mk] at huv
        have hmap : Joined (e.invFun (e.toFun xu)) (e.invFun (e.toFun xv)) :=
          (Quotient.exact huv).map e.invFun.continuous
        have h1x : Joined xu (e.invFun (e.toFun xu)) :=
          ⟨(Work.Stems.Pinch.homotopyPath h1 xu).symm⟩
        have h1y : Joined xv (e.invFun (e.toFun xv)) :=
          ⟨(Work.Stems.Pinch.homotopyPath h1 xv).symm⟩
        exact Quotient.sound (h1x.trans (hmap.trans h1y.symm))
  · intro w
    induction w using ZerothHomotopy.rec with
    | mk y =>
      refine ⟨ZerothHomotopy.mk (e.invFun y), ?_⟩
      rw [h0Pi0Map_mk]
      exact Quotient.sound ⟨Work.Stems.Pinch.homotopyPath h2 y⟩

/-- **Degree `0`**: a homotopy equivalence induces a bijection on `π₀`, written as `piMapN · 0`. -/
theorem bijective_piMapN_zero_of_homotopyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    Function.Bijective (piMapN e.toFun 0 x) := by
  have hb : Function.Bijective (h0Pi0Map e.toFun) := bijective_h0Pi0Map_of_homotopyEquiv e
  -- `piMapN · 0` is `h0Pi0Map` conjugated by the identification `π₀ ≅ ZerothHomotopy`
  have hcomp : piMapN e.toFun 0 x =
      ⇑(HomotopyGroup.pi0EquivZerothHomotopy (X := Y) (x := e.toFun x)).symm ∘
        (h0Pi0Map e.toFun ∘ ⇑(HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x))) := by
    funext a
    apply (HomotopyGroup.pi0EquivZerothHomotopy (X := Y) (x := e.toFun x)).injective
    rw [Function.comp_apply, Function.comp_apply, Equiv.apply_symm_apply]
    exact (h0Pi0Map_square (x₀ := x) e.toFun a).symm
  rw [hcomp]
  exact (Equiv.bijective _).comp (hb.comp (Equiv.bijective _))

/-! ## The target -/

theorem rwPiMapN_bijective_of_homotopyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (q : ℕ) (x : X) :
    Function.Bijective (Work.Serre.piMapN e.toFun q x) := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    exact bijective_piMapN_zero_of_homotopyEquiv e x
  · haveI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
    have h := bijective_homotopyGroupMap_of_homotopyEquiv (Q := Fin q) e x
    rw [piMapN_eq_homotopyGroupMap]
    exact h

end

end Work.Serre
