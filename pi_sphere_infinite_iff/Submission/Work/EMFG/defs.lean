import Mathlib
import Submission.Work.PiS.Interfaces

/-!
# EMFG — the interfaces of the integral Hurewicz/finiteness chapter

`Work.PiS.EMHomologyFG` asks: every range model `X` of `K(A,m)` (`A` f.g., `m ≥ 2`) through degree
`N+1` has `H_i(X;ℤ)` finitely generated for `i ≤ N`.

The proof of `Work.EMFG.emHomologyFG` reduces the statement to its `m = 1` case:

* `EMOne A` — every range model of `K(A,1)` through `N` (with `A` f.g.) has f.g. integral homology
  in the range `N-1`;
* `P m` — the `m`-th case, for all range models of `K(A,m)` (`A` f.g., `m ≥ 2`) and all ranges.

`P m` follows from `EMOne` (`m = 2`) and from `P (m-1)` (`m ≥ 3`) by the path–loop fibration and
direction 2 of the Serre spectral sequence (`Work.PiS.SerreFGThreeForTwo`); the substance of the
chapter is `EMOne` for general finitely generated `A`.
-/

set_option autoImplicit false

namespace Work.EMFG

/-- **The `m = 1` case**: every range model of `K(A,1)` through `N` has finitely generated
integral homology through degree `N - 1`. -/
def EMOne (A : Type) [AddCommGroup A] : Prop :=
  ∀ (N : ℕ) (X : Type) [TopologicalSpace X] (x : X),
    Work.Serre.IsEMSpaceUpTo A 1 (by norm_num) N X x → Work.PiS.FGUpTo X (N - 1)

/-- **The `m`-th case** (`m ≥ 2`) of `Work.PiS.EMHomologyFG`. -/
def P (m : ℕ) (hm : 2 ≤ m) : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Module.Finite ℤ A] (N : ℕ) (X : Type) [TopologicalSpace X]
    (x : X), Work.Serre.IsEMSpaceUpTo A m (by omega) N X x → Work.PiS.FGUpTo X (N - 1)

end Work.EMFG
