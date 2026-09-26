import Submission.Helpers
import Mathlib

open OnPropertyT Submission.Helpers
open scoped BigOperators

set_option autoImplicit false

/-!
# Decidable equality on automorphisms of a finitely generated free group

Mathlib provides no `DecidableEq` instance for `MulAut (FreeGroup (Fin n))`:
the type is a subtype of the function space `FreeGroup (Fin n) → FreeGroup (Fin n)`,
and no finiteness is available there.  However an automorphism of a free group is
determined by its values on the free generators (`FreeGroup.ext_hom`), and there
are only finitely many of those:

    a = b ↔ ∀ i : Fin n, a (of i) = b (of i)        (`mulAut_eq_iff`)

This is the form in which decidability is *used*.  Note that a global
*computable* `DecidableEq` instance would be a landmine: the `Finset`
definitions of `SAutGen`/`SigmaSet`/`AutGen` in `Submission/FreeGroupAut.lean` are
elaborated with the classical instance, and a different instance would break
definitional unfolding of those definitions (this was observed and reverted).
Accordingly we register only the classical (definitionally transparent)
instance, and keep the characterisation as a lemma.
-/

namespace Submission.RouteB

/-- **Two automorphisms of `F_n` are equal iff they agree on the generators.** -/
theorem mulAut_eq_iff {n : ℕ} (a b : MulAut (FreeGroup (Fin n))) :
    a = b ↔ ∀ i : Fin n, a (FreeGroup.of i) = b (FreeGroup.of i) :=
  ⟨fun h i => by rw [h],
   fun h => by
    have hhom : (a : FreeGroup (Fin n) →* FreeGroup (Fin n))
        = (b : FreeGroup (Fin n) →* FreeGroup (Fin n)) := FreeGroup.ext_hom _ _ h
    exact MulEquiv.ext (fun x => congrFun (congrArg DFunLike.coe hhom) x)⟩

/-- The classical `DecidableEq` instance on `MulAut (FreeGroup (Fin n))`, made
available for typeclass search (definitionally the classical one, hence safe). -/
noncomputable instance instDecidableEqMulAutFreeGroup (n : ℕ) :
    DecidableEq (MulAut (FreeGroup (Fin n))) :=
  Classical.decEq _

/-- Consequently the group ring `ℝ Aut(F_n)` has decidable equality, so its
finite subsets (`Finset`, the certificate shape of the challenge statement)
are available. -/
noncomputable example (n : ℕ) : DecidableEq (MonoidAlgebra ℝ (MulAut (FreeGroup (Fin n)))) :=
  inferInstance

end Submission.RouteB
