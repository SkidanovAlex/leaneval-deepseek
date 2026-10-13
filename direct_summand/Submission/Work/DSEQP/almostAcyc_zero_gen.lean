/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Almost acyclicity of the perfected Čech complex, degree `0` (node PERF)

The degree-`0` clause of almost acyclicity for the perfected Čech complex `S.K U` of
`Submission/Work/DSEQP/PerfCech.lean`: if `z` is a `0`-cocycle and `ϖ ∈ W = Γ(X,⊤)^{1/p^∞}`, then
`ϖ · z` lies in the image of the coaugmentation `eK : W → K⁰`.

The argument has three steps.

* `cocycle_compat`: the cocycle condition says that the coordinates of `z` agree on the pairwise
  intersections of the degree-`0` Čech opens.
* `exists_level_compat`: since the index set is finite, all coordinates of `z` and the element
  `ϖ` can be represented at one common level `N` in the perfection; then, by raising to a
  `p`-th power (multiplying the level by `p^k`), the representatives of the coordinates become
  *exactly* compatible on the intersections.
* `Wmap_eq_of_compat`: an exactly compatible family glues to a global section `t`, and the
  perfection of `t` is the required element of `W`.

The statement is used as the degree-`0` clause of `Work.DSEQP.almostAcyc_one`, the interface
`DSMap.Mix2.AlmostAcyc` of the equal-characteristic-`p` route to `#direct_summand`.
-/
import Mathlib
import Submission.Work.DSEQP.PerfAcyclic
import Submission.Work.DSEQP.glue_sections
import Submission.Work.DSEQP.sections_eq_zero_of_restrict_eq_zero
import Submission.Work.DSEQP.AcDefs
import Submission.Work.DSEQP.PerfCechZero.cocycle_compat
import Submission.Work.DSEQP.PerfCechZero.exists_level_compat
import Submission.Work.DSEQP.Wmap_eq_of_compat

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

namespace Work.DSEQP

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000

namespace PerfSetup

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime] {X : Scheme.{u}}
  [AlgebraicGeometry.IsIntegral X] {f : X ⟶ Spec (.of A)} {ι : Type u}

omit [AlgebraicGeometry.IsIntegral X] in
/-- The degree-`0` Čech open attached to a single index of the Čech nerve is the corresponding
member of the cover. -/
theorem CechOp_zero_eq (U : ι → X.Opens) (a : (CechIdx U 0).I) : CechOp U 0 a = U (a 0) := by
  show (∏ᶜ (U ∘ a) : X.Opens) = U (a 0)
  exact le_antisymm (leOfHom (Pi.π (U ∘ a) 0))
    (leOfHom (Pi.lift fun x : Fin 1 => homOfLE (by fin_cases x; exact le_refl _)))

omit [AlgebraicGeometry.IsIntegral X] in
/-- The degree-`0` Čech opens cover `X` as soon as the cover `U` does. -/
theorem iSup_CechOp_zero (U : ι → X.Opens) (hcov : iSup U = ⊤) :
    iSup (fun a : (CechIdx U 0).I => CechOp U 0 a) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hcov]
  refine iSup_le fun i => ?_
  exact le_trans (le_of_eq (CechOp_zero_eq U (fun _ : Fin 1 => i)).symm)
    (le_iSup (fun a : (CechIdx U 0).I => CechOp U 0 a) (fun _ : Fin 1 => i))

/-- Two cochains of the perfected Čech complex in degree `0` agree as soon as all their
coordinates do. -/
theorem kobj_π_ext (S : PerfSetup A p X f) (U : ι → X.Opens) {z w : (S.K U).X 0}
    (h : ∀ a, (Pi.π (S.Kobj U 0) a).hom z = (Pi.π (S.Kobj U 0) a).hom w) : z = w := by
  have hfam : S.kunpack U 0 z = S.kunpack U 0 w := by
    funext a
    rw [S.kunpack_apply, S.kunpack_apply]
    exact h a
  rw [← S.kpack_kunpack U 0 z, ← S.kpack_kunpack U 0 w, hfam]

omit [AlgebraicGeometry.IsIntegral X] in
/-- The `W`-action on the perfection of the sections over `V` is multiplication by the structure
map `Wmap V` (the `Algebra` instance `instAlgebraPsec`, unfolded). -/
theorem Psec_smul_apply (S : PerfSetup A p X f) (V : X.Opens) (c : S.W) (y : S.Psec V) :
    c • y = S.Wmap V c * y := by
  rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]

end PerfSetup

/-- **Almost acyclicity of the perfected Čech complex, degree `0`.**  A `0`-cocycle `z` of
`S.K U` becomes a coaugmentation element after multiplication by any `ϖ ∈ W`. -/
theorem almostAcyc_zero_gen (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime]
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    (S : Work.DSEQP.PerfSetup A p X f) {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hcov : iSup U = ⊤) (ϖ : Work.DSEQP.PerfSetup.W S) (z : (S.K U).X 0)
    (hz : ((S.K U).d 0 1).hom z = 0) :
    ∃ w : Work.DSEQP.PerfSetup.W S, ϖ • z = (S.eK U).hom w := by
  -- Step 1 (`cocycle_compat`): the cocycle condition makes the coordinates of `z` compatible on
  -- the pairwise intersections of the degree-`0` Čech opens.
  -- Step 2 (`exists_level_compat`): all coordinates and `ϖ` are represented at one common level
  -- `N` in the perfection, with the representatives exactly compatible.
  obtain ⟨N, lam, y, hlam, hy, hcom⟩ := PerfCechZero.exists_level_compat A p X f S U z ϖ
    (fun a b => PerfCechZero.cocycle_compat A p X f S U z hz a b)
  -- Step 3 (`Wmap_eq_of_compat`): the compatible family glues to a global section whose
  -- perfection `w ∈ W` has the prescribed coaugmentation coordinates.
  obtain ⟨w, hw⟩ := Wmap_eq_of_compat A p X f S U (PerfSetup.iSup_CechOp_zero U hcov) N lam y hcom
  -- Step 4: the coordinates of `ϖ • z` and of `(S.eK U).hom w` agree, so the two elements of
  -- `K⁰` do.
  refine ⟨w, PerfSetup.kobj_π_ext S U fun a => ?_⟩
  rw [map_smul, PerfSetup.eK_π]
  rw [← hy a, ← hlam]
  rw [PerfSetup.Psec_smul_apply S (PerfSetup.CechOp U 0 a)]
  exact (hw a).symm

end Work.DSEQP
