/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The free case `r = 1`, discharged

Node N3's global dimension bound and node N9's flatness conclusion are proved here for the
*trivial* relator, i.e. for the free groups `F(X)`, so that the residual input
`Work.ORFinal.FinalInput` needs them only for nontrivial relators.

* `Work.ORFinal.FreeCase.globalDim_le_one_free` (child of this area,
  `Submission/Work/ORFinal/FreeCase/globalDim_le_one_free.lean`): `gl.dim K[F(X)] ≤ 1`, from the
  length-one Fox resolution of the free group algebra.
* `Work.ORFinal.TorDimOne.torTwoVanishes_of_globalDim_le_one` (child of this area,
  `Submission/Work/ORFinal/TorDimOne/torTwoVanishes_of_globalDim_le_one.lean`): a ring of global
  dimension at most one has vanishing `Tor₂` against every module, in the vocabulary
  `Work.ORCoherence.TorTwoVanishes` consumed by node N10.

Together they give

* `Work.ORFinal.globalDim_le_two_free` — the free case at the bound `2` consumed by
  `Work.ORFinal.RingData.hgl` (and its `ULift` form `globalDim_le_two_free_ulift`);
* `Work.ORFinal.flatConclAt_free` / `Work.ORFinal.flatConcl_free` — `Tor₂^{K[G]}(D(G), -) = 0`
  (i.e. `Work.ORFinal.FlatConcl`) for a free group `G`, at the datum built from *any* envelope and
  any Hughes-free input — no input from nodes N6, N8, N9, N1 is needed in this case.
-/
import Submission.Work.ORFinal.RingData
import Submission.Work.ORFinal.FreeCase.globalDim_le_one_free
import Submission.Work.ORFinal.TorDimOne.torTwoVanishes_of_globalDim_le_one

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v

namespace Work.ORFinal

open Work.ORAssembly

/-- The free case of node N3 at the bound `2` used by `Work.ORFinal.RingData.hgl`. -/
theorem globalDim_le_two_free (K : Type u) [Field K] (X : Type u) [DecidableEq X] :
    Work.ORCoherence.globalDim
      (MonoidAlgebra K (PresentedGroup ({1} : Set (FreeGroup X)))) ≤ (2 : WithBot ℕ∞) :=
  le_trans (FreeCase.globalDim_le_one_free K X)
    (show ((1 : ℕ) : WithBot ℕ∞) ≤ (2 : WithBot ℕ∞) from by norm_num)

/-- The free case of node N3 in the universe of the coefficient field: `gl.dim K[ULift F(X)] ≤ 1`. -/
theorem globalDim_le_one_free_ulift (K : Type u) [Field K] {X : Type v} [DecidableEq X] :
    Work.ORCoherence.globalDim
      (MonoidAlgebra K (ULift.{u} (PresentedGroup ({1} : Set (FreeGroup X))))) ≤
        (1 : WithBot ℕ∞) :=
  Work.ORLyndon.globalDim_le_of_ringEquiv
    (MonoidAlgebra.mapDomainRingEquiv K
      (MulEquiv.ulift (α := PresentedGroup ({1} : Set (FreeGroup X)))).symm)
    (FreeCase.globalDim_le_one_free K X)

/-- The free case of node N3 at the bound `2`, in the universe of the coefficient field. -/
theorem globalDim_le_two_free_ulift (K : Type u) [Field K] {X : Type v} [DecidableEq X] :
    Work.ORCoherence.globalDim
      (MonoidAlgebra K (ULift.{u} (PresentedGroup ({1} : Set (FreeGroup X))))) ≤
        (2 : WithBot ℕ∞) :=
  le_trans (globalDim_le_one_free_ulift K (X := X))
    (show ((1 : ℕ) : WithBot ℕ∞) ≤ (2 : WithBot ℕ∞) from by norm_num)

/-- **The flatness conclusion of JL §5 at the M1 datum for a group of global dimension ≤ 1.**
For *any* envelope and *any* Hughes-free input, `Tor₂^{K[G]}(D(G), -) = 0` as soon as
`gl.dim K[G] ≤ 1`; no input from nodes N6, N8, N9 or N1 is used. -/
theorem flatConclAt_of_globalDim_le_one (K : Type u) [Field K] {G : Type u} [Group G]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) (φK : K →+* ℂ)
    (hin : Work.ORBridgeLinnell.HughesFreeInput K G E φK)
    (hgl : Work.ORCoherence.globalDim (MonoidAlgebra K G) ≤ (1 : WithBot ℕ∞)) :
    FlatConclAt K E φK hin := by
  letI := Work.ORBridgeLinnell.kAlgebra E φK
  exact TorDimOne.torTwoVanishes_of_globalDim_le_one _ hgl

/-- **The free case of `Work.ORFinal.FlatConcl`**: `Tor₂^{K[G]}(D(G), -) = 0` for
`G = ⟨Fin n | 1⟩`, the free group on `n` generators, at the canonical envelope of
`ULift ⟨Fin n | 1⟩`. -/
theorem flatConcl_free (K : Type u) [Field K] (n : ℕ) (φK : K →+* ℂ)
    (hin : Work.ORBridgeLinnell.HughesFreeInput K
      (ULift.{u, 0} (PresentedGroup ({1} : Set (FreeGroup (Fin n)))))
      (Work.ORBridgeLinnell.countableEnvelope
        (ULift.{u, 0} (PresentedGroup ({1} : Set (FreeGroup (Fin n)))))) φK) :
    FlatConcl K φK hin :=
  flatConclAt_of_globalDim_le_one K _ φK hin (globalDim_le_one_free_ulift K (X := Fin n))

/-- The free group `⟨Fin n | 1⟩ ≅ F(Fin n)` is `IsMulTorsionFree` (Mathlib's instance for free
groups, transported along the presentation isomorphism and `ULift`). -/
instance instIsMulTorsionFreeULiftTrivialRelator (n : ℕ) :
    IsMulTorsionFree (ULift.{u, 0} (PresentedGroup ({1} : Set (FreeGroup (Fin n))))) := by
  obtain ⟨e⟩ := Work.OROneRel.presentedGroup_one_iso_freeGroup (α := Fin n)
  exact Function.Injective.isMulTorsionFree
    ((e.toMonoidHom).comp
      (MulEquiv.ulift (α := PresentedGroup ({1} : Set (FreeGroup (Fin n))))).toMonoidHom)
    (e.injective.comp (MulEquiv.injective
      (MulEquiv.ulift (α := PresentedGroup ({1} : Set (FreeGroup (Fin n)))))))

/-- **The free case of the ring half of Theorem 1.1 needs node N6 only**: for a field `K` of
characteristic zero, `K[F(X)]` is coherent, from the Hughes-free input alone — neither node N3's
global dimension input for nontrivial relators nor the flatness conclusion `hTor` is used. -/
theorem ringCoherent_free_of_hughesFree (K : Type u) [Field K] [CharZero K] (n : ℕ)
    (hHF : ∀ (K : Type u) [Field K] (G : Type u) [Group G] [Countable G] (φK : K →+* ℂ),
      Work.ORBridgeLinnell.HughesFreeInput K G (Work.ORBridgeLinnell.countableEnvelope G) φK) :
    Ring.Coherent (MonoidAlgebra K (PresentedGroup ({1} : Set (FreeGroup (Fin n))))) := by
  refine Ring.Coherent.of_subfield (PresentedGroup ({1} : Set (FreeGroup (Fin n)))) K ?_
  intro S
  let F := ↥(Subfield.closure (S : Set K))
  obtain ⟨φF⟩ := fg_charZero_field_embeds_complex K S
  have hgl : Work.ORCoherence.globalDim
      (MonoidAlgebra F (ULift.{u} (PresentedGroup ({1} : Set (FreeGroup (Fin n)))))) ≤
        (2 : WithBot ℕ∞) := globalDim_le_two_free_ulift F (X := Fin n)
  have htor : FlatConcl F φF
      (hHF F (ULift.{u} (PresentedGroup ({1} : Set (FreeGroup (Fin n))))) φF) :=
    flatConcl_free F n φF _
  refine (ringCoherent_ulift_group F
    (H := PresentedGroup ({1} : Set (FreeGroup (Fin n))))).mpr ?_
  exact ringCoherent_of_ringData
    (RingData.ofEnvelope
      (Work.ORBridgeLinnell.countableEnvelope
        (ULift.{u} (PresentedGroup ({1} : Set (FreeGroup (Fin n)))))) φF
      (hHF F (ULift.{u} (PresentedGroup ({1} : Set (FreeGroup (Fin n))))) φF)
      ⊤ (by infer_instance) (by infer_instance) (by infer_instance) hgl htor)

end Work.ORFinal
