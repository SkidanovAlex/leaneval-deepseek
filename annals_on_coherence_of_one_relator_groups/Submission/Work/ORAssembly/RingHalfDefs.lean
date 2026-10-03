/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Node N14, part (2): the ring `S = D(G)` attached to a Linnell datum

Node N7 (`Submission/Work/ORLinnell`) packages the division closures of `K[G]` in `U(G)` as a
`LinnellDatum K G U`.  This file extracts from it the objects that the *delivered* ring-theoretic
nodes consume:

* `Work.ORAssembly.LinData.toU` — the `K`-algebra map `K[G] → U` (`g ↦ gen g`, scalars by
  `algebraMap`);
* `Work.ORAssembly.LinData.SAlg` — `S = D(G) = L.S` as a `K`-subalgebra of `U`;
* `Work.ORAssembly.LinData.toS` — the `K`-algebra map `K[G] → S` used by the flatness engine
  (node N9, `Work.ORFlatness`) and by the coherence criterion (node N10, `Work.ORCoherence`).

Injectivity of `toS` — i.e. `K[G] ⊆ S`, which is Linnell independence (I1) of node N5 at the
trivial subgroup — is `Work.ORAssembly.LinData.toS_injective`
(`Submission/Work/ORAssembly/Ring/toS_injective.lean`).
-/

import ChallengeDeps
import Submission.Work.ORLinnell.Main

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORAssembly

open Work.ORLinnell

variable {K : Type u} [Field K] {G : Type u} [Group G] {U : Type u} [Ring U] [Nontrivial U]
  [Algebra K U]

/-! ### The API of a `Work.ORLinnell.LinnellDatum` used by the assembly -/

namespace LinData

/-- The group part `G → U` of a Linnell datum, through the units. -/
noncomputable def genU (L : LinnellDatum K G U) : G →* U :=
  (Units.coeHom U).comp L.gen

@[simp] theorem genU_apply (L : LinnellDatum K G U) (g : G) :
    genU L g = (L.gen g : U) := rfl

/-- The `K`-algebra map `K[G] → U` attached to a Linnell datum (`single g k ↦ k • gen g`). -/
noncomputable def toU (L : LinnellDatum K G U) : MonoidAlgebra K G →ₐ[K] U :=
  MonoidAlgebra.lift K U G (genU L)

@[simp] theorem toU_single (L : LinnellDatum K G U) (g : G) (k : K) :
    toU L (MonoidAlgebra.single g k) = k • (L.gen g : U) :=
  MonoidAlgebra.lift_single (A := U) (genU L) g k

theorem toU_of (L : LinnellDatum K G U) (g : G) :
    toU L (MonoidAlgebra.of K G g) = (L.gen g : U) :=
  MonoidAlgebra.lift_of (A := U) (genU L) g

/-- The image of `K[G]` lies in `S = D(G)`. -/
theorem toU_mem_S (L : LinnellDatum K G U) (x : MonoidAlgebra K G) : toU L x ∈ L.S := by
  induction x using MonoidAlgebra.induction_on with
  | of m =>
      rw [toU_of L m]
      exact L.gen_mem ⊤ ⟨m, trivial⟩
  | add x y hx hy =>
      rw [map_add]
      exact L.S.add_mem hx hy
  | smul r x hx =>
      rw [Algebra.smul_def, map_mul, AlgHom.commutes]
      exact L.S.mul_mem (L.algebraMap_mem ⊤ r) hx

/-- `S = D(G) = L.S` as a `K`-subalgebra of `U`. -/
def SAlg (L : LinnellDatum K G U) : Subalgebra K U where
  carrier := (L.S : Set U)
  mul_mem' := fun {a b} ha hb => L.S.mul_mem ha hb
  one_mem' := L.S.one_mem
  add_mem' := fun {a b} ha hb => L.S.add_mem ha hb
  zero_mem' := L.S.zero_mem
  algebraMap_mem' := fun k => L.algebraMap_mem ⊤ k

@[simp] theorem SAlg_coe (L : LinnellDatum K G U) : (SAlg L : Set U) = L.S := rfl

/-- The `K`-algebra map `K[G] → S` attached to a Linnell datum. -/
noncomputable def toS (L : LinnellDatum K G U) : MonoidAlgebra K G →ₐ[K] ↥(SAlg L) :=
  (toU L).codRestrict (SAlg L) (fun x => toU_mem_S L x)

@[simp] theorem toS_apply_coe (L : LinnellDatum K G U) (x : MonoidAlgebra K G) :
    ((toS L x : ↥(SAlg L)) : U) = toU L x := rfl

/-- Evaluation of `toS` on a monomial. -/
@[simp] theorem toS_single_apply (L : LinnellDatum K G U) (g : G) (k : K) :
    ((toS L (MonoidAlgebra.single g k) : ↥(SAlg L)) : U) = k • (L.gen g : U) := by
  rw [toS_apply_coe, toU_single]

/-- The form of `toS` on a monomial used to identify it with the flatness engine's `φ`. -/
theorem toS_single (L : LinnellDatum K G U) (g : G) (k : K) :
    toS L (MonoidAlgebra.single g k) =
      (⟨toU L (MonoidAlgebra.single g k), toU_mem_S L _⟩ : ↥(SAlg L)) :=
  Subtype.ext rfl

end LinData

end Work.ORAssembly
