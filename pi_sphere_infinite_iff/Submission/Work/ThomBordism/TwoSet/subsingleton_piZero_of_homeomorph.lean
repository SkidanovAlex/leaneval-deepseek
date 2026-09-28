import Mathlib

/-!
# `π₀`-triviality transports along a homeomorphism

For an empty index type `N` the cube model `HomotopyGroup N X x = Ω^N X x / homotopy`
of the homotopy group is the set of path components of `X` based at `x`; in
particular `HomotopyGroup (Fin 0) X x` is *independent of the basepoint* and
Mathlib identifies it with `ZerothHomotopy X = X / Joined` via
`HomotopyGroup.pi0EquivZerothHomotopy`.

A homeomorphism `e : A ≃ₜ B` preserves the relation `Joined` (and its negation),
so it induces a bijection of path-component sets; hence the property
"`π₀` is a subsingleton" transports in either direction.  That is the content
below.  The hypothesis `e a = b` relates the two basepoints; it is not needed by
the argument (which is basepoint-free), but we substitute it so that the proof
works directly with the given basepoint.
-/

namespace Work.ThomBordism.TwoSet

open scoped Topology

theorem subsingleton_piZero_of_homeomorph {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) {a : A} {b : B} (hab : e a = b)
    (h : Subsingleton (HomotopyGroup (Fin 0) B b)) : Subsingleton (HomotopyGroup (Fin 0) A a) := by
  -- arrange that both spaces are based at the same point.
  subst hab
  -- `π₀ B = 0`: pass across the identification with the path components of `B`.
  have hZ : Subsingleton (ZerothHomotopy B) :=
    @Equiv.subsingleton _ _ (HomotopyGroup.pi0EquivZerothHomotopy (x := e a)).symm h
  -- the homeomorphism induces an injection of path-component sets `ZerothHomotopy A → ZerothHomotopy B`,
  -- because continuous maps send `Joined` points to `Joined` points and `e.symm` is continuous.
  have hZA : Subsingleton (ZerothHomotopy A) := by
    rw [subsingleton_iff]
    intro u v
    induction u using ZerothHomotopy.rec with
    | mk x =>
      induction v using ZerothHomotopy.rec with
      | mk y =>
        have hxy : ZerothHomotopy.mk (e x) = ZerothHomotopy.mk (e y) :=
          Subsingleton.elim _ _
        have hJ : Joined (e x) (e y) := (Quotient.exact hxy : Joined (e x) (e y))
        have h2 : Joined x y := by
          have h3 := hJ.map e.symm.continuous
          rwa [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply] at h3
        exact ZerothHomotopy.sound h2.somePath
  -- return to the cube model of `π₀ A`.
  exact @Equiv.subsingleton _ _ (HomotopyGroup.pi0EquivZerothHomotopy (x := a)) hZA

end Work.ThomBordism.TwoSet
