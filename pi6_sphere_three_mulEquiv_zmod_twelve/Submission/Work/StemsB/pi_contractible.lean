import Mathlib
import Submission.Work.Stems.subsingleton_of_contractible

/-!
# Homotopy groups of a contractible space are trivial

For a contractible space `X` and any `n : ℕ` and basepoint `x : X`, the `(n+1)`-st homotopy group
`π_(n+1) X x = HomotopyGroup (Fin (n+1)) X x` is a subsingleton (it is in fact the trivial group,
since `Fin (n+1)` is nonempty).

This is the statement `Work.Stems.subsingleton_of_contractible`, proved for *every* index type `N`
(no finiteness hypothesis on `N`, no separation hypothesis on `X`) in
`Submission/Work/Stems/subsingleton_of_contractible.lean`.  Its proof runs through the cone
`C X = (X × I)/(X × {1})`:

* `C X` admits a contraction *fixing the apex*, so every generalized loop at the apex is
  null-homotopic relative to the cube boundary (`cone_apex_subsingleton`);
* `X` is a retract of `C X` (`coneRetract`), built from a homotopy `H` from `id X` to the constant
  map at `x`, and postcomposition with the retraction transports homotopies of generalized loops
  back to `X` (`Work.Stems.subsingleton_of_retract`);
* the base point is moved from the apex of the cone to the image of `x` using the path
  `t ↦ [x, t]` and basepoint-change invariance of triviality
  (`Work.Stems.subsingleton_homotopyGroup_change_basepoint`).

Here we only record the specialization to the index type `Fin (n+1)` requested by the caller.
-/

namespace Work.StemsB

theorem pi_contractible {X : Type*} [TopologicalSpace X] [ContractibleSpace X] (n : ℕ) (x : X) :
    Subsingleton (HomotopyGroup (Fin (n + 1)) X x) :=
  Work.Stems.subsingleton_of_contractible (N := Fin (n + 1)) (X := X) x

end Work.StemsB
