import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.LocalReciprocityLubinTate.Eval.isAdicComplete_adjoinRoot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped ValuativeRel

namespace NK.LocalReciprocityLubinTate.Eval

universe u

open LTtorsionRing

/-- The `(π)`-adic completion of the ambient ring: `𝒪[F][T]/(f^{(n)}(T))` is adically complete,
because it is a finite free `𝒪[F]`-module and `𝒪[F]` is complete. -/
theorem isAdicComplete_ltTorsionRing {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q) :
    IsAdicComplete (adicIdeal π q n) (LTtorsionRing F π q n) := by
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (O F)) (O F) := inferInstance
  haveI : IsDiscreteValuationRing (O F) := inferInstance
  have hmono : (LTpolyIter π q n).Monic := (LubinTate.LTpolyIter_monic_degree π q n hq).1
  have hmap : (IsLocalRing.maximalIdeal (O F)).map
      (algebraMap (O F) (LTtorsionRing F π q n)) = adicIdeal π q n := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
    rfl
  rw [← hmap]
  exact (IsAdicComplete.map_algebraMap_iff (I := IsLocalRing.maximalIdeal (O F))
    (S := LTtorsionRing F π q n) (M := LTtorsionRing F π q n)).mpr
    (isAdicComplete_adjoinRoot (IsLocalRing.maximalIdeal (O F)) (LTpolyIter π q n) hmono)

/-- The ambient ring is complete for its adic topology. -/
theorem completeSpace_ltTorsionRing {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q) :
    CompleteSpace (LTtorsionRing F π q n) :=
  ((IsAdic.isAdicComplete_iff (I := adicIdeal π q n) rfl).mp
    (isAdicComplete_ltTorsionRing π hπ q n hq)).1

/-- The ambient ring is Hausdorff for its adic topology. -/
theorem t2Space_ltTorsionRing {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q) :
    T2Space (LTtorsionRing F π q n) :=
  ((IsAdic.isAdicComplete_iff (I := adicIdeal π q n) rfl).mp
    (isAdicComplete_ltTorsionRing π hπ q n hq)).2

end NK.LocalReciprocityLubinTate.Eval
