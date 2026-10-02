import Mathlib
import Submission.Work.Serre.cubePairDefs
import Submission.Work.Serre.hZeroOfPiZero
import Submission.Work.Stems.Pinch
import Submission.Work.Stems.HomotopyGroupMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre

open scoped Topology Topology.Homotopy unitInterval
open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## Two auxiliary lemmas on the base-point change of the homotopy groups

The base-point change `Work.Stems.Pinch.transport` is the explicit "pinched loop" construction on
generalized cubes; the two lemmas below record that it commutes with postcomposition by a
continuous map (`transport_mapMap`) and, consequently, with `Work.Serre.piMapN`
(`piMapN_transport_comm`). -/

/-- **Naturality of the pinched-loop base-point change.**  Pinching a postcomposed loop along a
postcomposed path is the postcomposition of the pinched loop: at the level of the underlying
`pinchFun` this is immediate, because the `if`-condition only depends on the cube point. -/
private theorem pinch_mapLoop {N : Type*} [Fintype N] [Nonempty N]
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x y : X} (p : Path x y) (w : Ω^ N X x) :
    Work.Stems.Pinch.pinch (N := N) (p.map (f := ⇑f) f.continuous)
        (HomotopyGroup.mapLoop f w)
      = HomotopyGroup.mapLoop f (Work.Stems.Pinch.pinch (N := N) p w) := by
  apply GenLoop.ext
  intro u
  simp only [Work.Stems.Pinch.pinch_apply, HomotopyGroup.mapLoop_apply,
    Work.Stems.Pinch.pinchFun, Path.map_coe, Function.comp_apply]
  split_ifs <;> rfl

/-- **Naturality of the base-point change under a continuous map.**  The square relating the
base-point changes in `X` (along `p`) and in `Y` (along `p.map f`) with the induced maps
`π_k(X,·) → π_k(Y,·)` commutes. -/
theorem transport_mapMap {N : Type*} [Fintype N] [Nonempty N]
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x y : X} (p : Path x y) (a : HomotopyGroup N X x) :
    Work.Stems.Pinch.transport (N := N) (p.map (f := ⇑f) f.continuous)
        (HomotopyGroup.map f a)
      = HomotopyGroup.map f (Work.Stems.Pinch.transport (N := N) p a) := by
  induction a using Quotient.inductionOn with
  | h w =>
    simp only [HomotopyGroup.map_mk_mapLoop, Work.Stems.Pinch.transport_mk, pinch_mapLoop]
    try rfl

/-- The same naturality for `Work.Serre.piMapN` (which is `HomotopyGroup.map` by definition). -/
theorem piMapN_transport_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x y : X} (p : Path x y) (n : ℕ) (a : HomotopyGroup (Fin (n + 1)) X x) :
    Work.Stems.Pinch.transport (N := Fin (n + 1)) (p.map (f := ⇑f) f.continuous)
        (piMapN f (n + 1) x a)
      = piMapN f (n + 1) y (Work.Stems.Pinch.transport (N := Fin (n + 1)) p a) :=
  transport_mapMap f p a

/-- **Bijectivity of `piMapN` transfers along a path.**  If `x` and `y` are joined by a path in `X`
and `f : X → Y` induces a bijection on `π_k` at `x`, then it induces a bijection at `y`.
(For `k ≥ 1` this is the naturality of `piMapN` in the base point, i.e. the commutativity of the
square formed with the base-point changes `Work.StemsB.basepoint_transport` (equivalently
`Work.Stems.basepoint_iso`/`Pinch.transport`); for `k = 0` it follows from the description of `π₀`
as path components, e.g. via `Work.Serre.h0Pi0Map_square`/`h0Pi0Map_bijective`.) -/
theorem bijective_piMapN_of_joined {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x y : X} (h : Joined x y) (k : ℕ)
    (hk : Function.Bijective (Work.Serre.piMapN f k x)) :
    Function.Bijective (Work.Serre.piMapN f k y) := by
  obtain ⟨γ⟩ := h
  rcases k with _ | n
  · -- `k = 0`: both `π₀`'s are `ZerothHomotopy`, and `h0Pi0Map f` does not see the base point
    have hb : Function.Bijective (h0Pi0Map f) := h0Pi0Map_bijective f hk
    have hfun : Work.Serre.piMapN f 0 y =
        ⇑(HomotopyGroup.pi0EquivZerothHomotopy (X := Y) (x := f y)).symm ∘
          (h0Pi0Map f ∘ ⇑(HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := y))) := by
      funext a
      simp only [Function.comp_apply]
      exact (Equiv.eq_symm_apply
        (HomotopyGroup.pi0EquivZerothHomotopy (X := Y) (x := f y))).mpr
        (h0Pi0Map_square (x₀ := y) f a).symm
    rw [hfun]
    exact Function.Bijective.comp
      (HomotopyGroup.pi0EquivZerothHomotopy (X := Y) (x := f y)).symm.bijective
      (hb.comp (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := y)).bijective)
  · -- `k = n + 1`: the base-point changes are bijections, and the square commutes
    set TX := Work.Stems.Pinch.transport (N := Fin (n + 1)) γ with hTXdef
    set TY := Work.Stems.Pinch.transport (N := Fin (n + 1)) (γ.map (f := ⇑f) f.continuous)
      with hTYdef
    let eX : HomotopyGroup (Fin (n + 1)) X x ≃ HomotopyGroup (Fin (n + 1)) X y :=
      { toFun := TX
        invFun := Work.Stems.Pinch.transport (N := Fin (n + 1)) γ.symm
        left_inv := fun a => by
          rw [hTXdef]
          exact Work.Stems.Pinch.transport_symm_apply γ a
        right_inv := fun b => by
          rw [hTXdef]
          exact Work.Stems.Pinch.transport_symm_apply' γ b }
    let eY : HomotopyGroup (Fin (n + 1)) Y (f x) ≃ HomotopyGroup (Fin (n + 1)) Y (f y) :=
      { toFun := TY
        invFun := Work.Stems.Pinch.transport (N := Fin (n + 1))
          (γ.map (f := ⇑f) f.continuous).symm
        left_inv := fun a => by
          rw [hTYdef]
          exact Work.Stems.Pinch.transport_symm_apply _ a
        right_inv := fun b => by
          rw [hTYdef]
          exact Work.Stems.Pinch.transport_symm_apply' _ b }
    have hsq : ∀ a : HomotopyGroup (Fin (n + 1)) X x,
        TY (piMapN f (n + 1) x a) = piMapN f (n + 1) y (TX a) := by
      intro a
      rw [hTXdef, hTYdef]
      exact piMapN_transport_comm f γ n a
    have heq : piMapN f (n + 1) y = ⇑eY ∘ (piMapN f (n + 1) x ∘ ⇑eX.symm) := by
      funext b
      simp only [Function.comp_apply]
      have h := (hsq (eX.symm b)).symm
      rw [show TX (eX.symm b) = b from eX.apply_symm_apply b] at h
      exact h
    rw [heq]
    exact Function.Bijective.comp eY.bijective (hk.comp eX.symm.bijective)

end

end Work.Serre
