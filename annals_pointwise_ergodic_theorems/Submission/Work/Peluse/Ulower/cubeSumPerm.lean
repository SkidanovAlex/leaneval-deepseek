import Mathlib
import Submission.Work.Peluse.Concat.GowersDefs

/-!
# Invariance of the flat cube sum under relabeling the coordinates

`Work.Peluse.Concat.NPow t G = ‖cubeSum (fun _ => G)‖` is the `2 ^ t`-th power of the flat box norm
of `G : (Fin t → X) → ℂ`.  It is manifestly symmetric in the `t` coordinates, and this module
proves it: for any `e : Equiv.Perm (Fin t)`, replacing `G` by `v ↦ G (v ∘ e)` does not change
`NPow t G`.

This is used to convert a "blind factor inequality" proved at coordinate `0` (where the
`Fin.cons`-recursion `Concat.cubeSum_const_succ` applies) into a statement for *any* coordinate,
by transporting along the transposition of that coordinate with `0`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse.Concat

/-- Relabeling of a tuple by a permutation of the coordinate set. -/
def precomp {t : ℕ} {X : Type} (e : Equiv.Perm (Fin t)) (v : Fin t → X) : Fin t → X :=
  fun j => v (e j)

/-- `precomp e` as an equivalence (its inverse is `precomp e.symm`). -/
def precompEquiv {t : ℕ} (X : Type) (e : Equiv.Perm (Fin t)) : (Fin t → X) ≃ (Fin t → X) where
  toFun v := precomp e v
  invFun v := precomp e.symm v
  left_inv v := by
    funext j
    simp only [precomp, Equiv.apply_symm_apply]
  right_inv v := by
    funext j
    simp only [precomp, Equiv.symm_apply_apply]

/-- Relabeling a `Bool`-valued tuple by a permutation of the coordinates. -/
def compPerm {t : ℕ} (e : Equiv.Perm (Fin t)) : Equiv.Perm (Fin t → Bool) where
  toFun ω := fun j => ω (e j)
  invFun ω := fun j => ω (e.symm j)
  left_inv ω := by
    funext j
    simp only [Equiv.apply_symm_apply]
  right_inv ω := by
    funext j
    simp only [Equiv.symm_apply_apply]

/-- The mixed corner commutes with the relabeling. -/
lemma precomp_mix {t : ℕ} {X : Type} (e : Equiv.Perm (Fin t)) (ω : Fin t → Bool)
    (x0 x1 : Fin t → X) :
    precomp e (mix ω x0 x1)
      = mix (fun j => ω (e j)) (precomp e x0) (precomp e x1) := by
  funext j
  simp only [precomp, mix]

/-- The weight is invariant under relabeling the coordinates. -/
lemma weight_comp {t : ℕ} (e : Equiv.Perm (Fin t)) (ω : Fin t → Bool) :
    Work.Peluse.weight (fun j => ω (e j)) = Work.Peluse.weight ω := by
  rw [Work.Peluse.Concat.weight_eq_sum, Work.Peluse.Concat.weight_eq_sum]
  exact Fintype.sum_equiv e (fun j => if ω (e j) then (1 : ℕ) else 0)
    (fun i => if ω i then (1 : ℕ) else 0) (fun j => rfl)

/-- The cube product commutes with the relabeling. -/
lemma cubeProd_precomp {t : ℕ} {X : Type} [Fintype X] (e : Equiv.Perm (Fin t))
    (G : (Fin t → X) → ℂ) (x0 x1 : Fin t → X) :
    cubeProd (fun (_ : Fin t → Bool) => fun v => G (precomp e v)) x0 x1
      = cubeProd (fun (_ : Fin t → Bool) => G) (precomp e x0) (precomp e x1) := by
  unfold cubeProd
  refine Fintype.prod_equiv (compPerm e)
    (fun ω : Fin t → Bool => (star^[Work.Peluse.weight ω]) (G (precomp e (mix ω x0 x1))))
    (fun ω : Fin t → Bool =>
      (star^[Work.Peluse.weight ω]) (G (mix ω (precomp e x0) (precomp e x1)))) ?_
  intro ω
  show (star^[Work.Peluse.weight ω]) (G (precomp e (mix ω x0 x1)))
      = (star^[Work.Peluse.weight (fun j => ω (e j))])
          (G (mix (fun j => ω (e j)) (precomp e x0) (precomp e x1)))
  rw [weight_comp e ω, precomp_mix e ω x0 x1]

/-- **Invariance of the flat cube sum under relabeling the coordinates.** -/
theorem cubeSum_precomp {t : ℕ} {X : Type} [Fintype X] (e : Equiv.Perm (Fin t))
    (G : (Fin t → X) → ℂ) :
    cubeSum (fun (_ : Fin t → Bool) => fun v => G (precomp e v)) = cubeSum (fun _ => G) := by
  unfold cubeSum
  calc (∑ x0 : Fin t → X, ∑ x1 : Fin t → X,
          cubeProd (fun (_ : Fin t → Bool) => fun v => G (precomp e v)) x0 x1)
      = ∑ x0 : Fin t → X, ∑ x1 : Fin t → X,
          cubeProd (fun (_ : Fin t → Bool) => G) (precomp e x0) (precomp e x1) := by
        refine Finset.sum_congr rfl fun x0 _ => Finset.sum_congr rfl fun x1 _ => ?_
        exact cubeProd_precomp e G x0 x1
    _ = ∑ x0 : Fin t → X, ∑ x1 : Fin t → X,
          cubeProd (fun (_ : Fin t → Bool) => G) (precomp e x0) x1 := by
        refine Finset.sum_congr rfl fun x0 _ => ?_
        exact Fintype.sum_equiv (precompEquiv X e) _ _ (fun x1 => rfl)
    _ = ∑ x0 : Fin t → X, ∑ x1 : Fin t → X,
          cubeProd (fun (_ : Fin t → Bool) => G) x0 x1 :=
        Fintype.sum_equiv (precompEquiv X e) _ _ (fun x0 => rfl)

/-- **`NPow` is invariant under relabeling the coordinates.** -/
theorem npowPermInv {t : ℕ} {X : Type} [Fintype X] (e : Equiv.Perm (Fin t))
    (G : (Fin t → X) → ℂ) :
    Work.Peluse.Concat.NPow t (fun v : Fin t → X => G (precomp e v))
      = Work.Peluse.Concat.NPow t G := by
  unfold Work.Peluse.Concat.NPow
  rw [cubeSum_precomp e G]

end

end Work.Peluse.Ulower
