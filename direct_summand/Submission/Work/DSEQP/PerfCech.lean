/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The perfected Čech complex and its coaugmentation (node PERF)
-/
import Mathlib
import Submission.Work.DSEQP.PerfPresheaf
import Submission.Work.DSEQP.PerfUnit
import Submission.Work.DSF1.Cech.cechComplexFunctor_map_pi
import Submission.Work.DSMap.Map

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

namespace Work.DSEQP

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000

namespace PerfSetup

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of A)} {ι : Type u}

/-- The Čech index object in degree `n`. -/
noncomputable abbrev CechIdx (U : ι → X.Opens) (n : ℕ) : FormalCoproduct X.Opens :=
  unop (((FormalCoproduct.mk ι U).cech.rightOp).obj ⦋n⦌)

/-- The open of `X` attached to a Čech index. -/
noncomputable abbrev CechOp (U : ι → X.Opens) (n : ℕ) (a : (CechIdx U n).I) : X.Opens :=
  (CechIdx U n).obj a

/-- The Čech complex of the perfected structure presheaf: the complex `K` of node `PERF`. -/
noncomputable abbrev K (S : PerfSetup A p X f) (U : ι → X.Opens) :
    CochainComplex (ModuleCat.{u} S.W) ℕ :=
  (cechComplexFunctor U).obj S.perfPresheaf

/-- The value of the perfected structure presheaf at a Čech index. -/
noncomputable abbrev Kobj (S : PerfSetup A p X f) (U : ι → X.Opens) (n : ℕ)
    (a : (CechIdx U n).I) : ModuleCat.{u} S.W :=
  S.perfPresheaf.obj (op (CechOp U n a))

/-- The components of the coaugmentation `W → K⁰`. -/
noncomputable def eKfam (S : PerfSetup A p X f) (U : ι → X.Opens)
    (b : (CechIdx U 0).I) : ModuleCat.of S.W S.W ⟶ S.Kobj U 0 b :=
  ModuleCat.ofHom (Algebra.linearMap S.W (S.Psec (CechOp U 0 b)))

/-- The coaugmentation `W → K⁰`: the diagonal to the cover `U`. -/
noncomputable def eK (S : PerfSetup A p X f) (U : ι → X.Opens) :
    ModuleCat.of S.W S.W ⟶ (S.K U).X 0 :=
  Pi.lift (S.eKfam U)

/-- The components of the coaugmentation. -/
theorem eK_π (S : PerfSetup A p X f) (U : ι → X.Opens) (a : (CechIdx U 0).I) (w : S.W) :
    (Pi.π (S.Kobj U 0) a) ((S.eK U).hom w : ↥(∏ᶜ S.Kobj U 0)) = S.Wmap (CechOp U 0 a) w := by
  show (Pi.π (S.Kobj U 0) a) ((Pi.lift (S.eKfam U)) w : ↥(∏ᶜ S.Kobj U 0)) = _
  rw [← CategoryTheory.comp_apply (Pi.lift (S.eKfam U)) (Pi.π (S.Kobj U 0) a) w,
    Pi.lift_comp_π]
  rfl

end PerfSetup

end Work.DSEQP
