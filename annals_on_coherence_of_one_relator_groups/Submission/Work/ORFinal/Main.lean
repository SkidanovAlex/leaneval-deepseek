/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Node N14, final wiring: Theorem 1.1 of Jaikin-Zapirain--Linton

This is the entry point of `Submission/Work/ORFinal/`.  It contains

* `Work.ORFinal.nodeInputs` / `nodeInputsOf` — the group-theoretic node inputs (nodes N2, N12, N13)
  *discharged* from the delivered nodes, so the group half of Theorem 1.1 has no node-level
  hypothesis left;
* `Work.ORFinal.theorem_1_1_of_ringData` — the challenge statement from the per-presentation ring
  data `Work.ORFinal.RingData` (= `Work.ORAssembly.RingInputs` with `hinj` removed);
* `Work.ORFinal.theorem_1_1_of_hughesFree` — the challenge statement with the ring half
  *constructed* from `Work.ORFinal.FinalInput`, i.e. from (i) node N6's (I4) in the form in which
  the JZLA20 engine is stated (`Work.ORFinal.DivLoc`, locally indicable subgroups) and (ii) JL
  §5's flatness conclusion for nontrivial relators (`Work.ORFinal.FlatConcl`, nodes N3 + N8 + N9 +
  N1).  Node N4 is used as a *theorem*
  (`Work.ORLocInd.exists_normal_finiteIndex_torsionFree_locallyIndicable`), node N7's Ore-field
  statement is *derived* (`Work.ORFinal.oreFieldFrac_of_divLoc`,
  `Submission/Work/ORFinal/OreFieldOfDiv.lean`), and the free case is proved in
  `Submission/Work/ORFinal/FreeCase.lean`.

See `README.md` of this directory for the exact list of what is proved here, what is still owed and
by whom.
-/
import Submission.Work.ORFinal.NodeInputs
import Submission.Work.ORFinal.RingData
import Submission.Work.ORFinal.RingDataDiv
import Submission.Work.ORFinal.OreFieldOfDiv
import Submission.Work.ORFinal.Hypotheses
import Submission.Work.ORFinal.FreeCase
import Submission.Work.ORReductions.API

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Work.ORFinal

open Work.ORAssembly

/-! ## Theorem 1.1 from the per-presentation `RingData` -/

/-- **Theorem 1.1 of Jaikin-Zapirain--Linton, from the per-presentation ring data.**

The hypotheses are

* `hQ` — `Work.ORFinal.RingData ℚ ⟨Fin n | r⟩` for every finitely generated one-relator
  presentation, at universe `0` (this is the input of the group half);
* `hK` — `Work.ORFinal.RingData K (ULift ⟨Fin n | r⟩)` for every finitely generated one-relator
  presentation, at the universe of the coefficient field.

This is `Work.ORAssembly.theorem_1_1_of_nodes` with the group-theoretic node inputs discharged
(`Work.ORFinal.nodeInputs`) and with `RingData` in place of `RingInputs`. -/
theorem theorem_1_1_of_ringData {G : Type u} {K : Type v} [Group G] [Field K] [CharZero K]
    (hG : Group.OneRelator G)
    (hQ : ∀ (n : ℕ) (r : FreeGroup (Fin n)),
      RingData ℚ (PresentedGroup ({r} : Set (FreeGroup (Fin n)))))
    (hK : ∀ (n : ℕ) (r : FreeGroup (Fin n)),
      RingData K (ULift.{v} (PresentedGroup ({r} : Set (FreeGroup (Fin n)))))) :
    Group.Coherent G ∧ Ring.Coherent (MonoidAlgebra K G) :=
  Work.ORAssembly.theorem_1_1_of_nodes (G := G) (K := K) hG nodeInputs
    (fun n r => (hQ n r).toRingInputs) (fun n r => (hK n r).toRingInputs)

/-! ## Theorem 1.1 from the residual inputs -/

/-- The one-relator structure of `ULift ⟨Fin n | r⟩`. -/
theorem oneRelator_ulift_presentedGroup (n : ℕ) (r : FreeGroup (Fin n)) :
    Group.OneRelator (ULift.{w} (PresentedGroup ({r} : Set (FreeGroup (Fin n))))) :=
  Work.ORAssembly.OneRelator.oneRelator_ulift ⟨Fin n, r, ⟨MulEquiv.refl _⟩⟩

/-- Node N4's subgroup of a finitely generated one-relator presentation, lifted to the universe of
the coefficient field: normal, of finite index, and locally indicable. -/
theorem exists_subgroup_ulift_locallyIndicable (X : Type w) {H : Type u} [Group H]
    (h : ∃ G' : Subgroup H, G'.Normal ∧ G'.FiniteIndex ∧ Work.ORLocInd.IsTorsionFree G' ∧
      Work.ORLocInd.Group.LocallyIndicable G') :
    ∃ G'' : Subgroup (ULift.{w} H),
      G''.Normal ∧ G''.FiniteIndex ∧ Work.ORLocInd.IsTorsionFree G'' ∧
        Work.ORLocInd.Group.LocallyIndicable G'' := by
  obtain ⟨G', hN, hfin, htf, hli⟩ := h
  let K : FiniteIndexNormalSubgroup H :=
    { toSubgroup := G', isNormal' := hN, isFiniteIndex' := hfin }
  let K' : FiniteIndexNormalSubgroup (ULift.{w} H) :=
    FiniteIndexNormalSubgroup.comap (MulEquiv.ulift (α := H)).toMonoidHom K
  have hli' : Work.ORLocInd.Group.LocallyIndicable (↥(K' : Subgroup (ULift.{w} H))) :=
    Work.ORLocInd.Group.LocallyIndicable.of_injective
      ({ toFun := fun x => (⟨(MulEquiv.ulift (α := H)) x.1, x.2⟩ : ↥G')
         map_one' := by ext; simp
         map_mul' := by intro a b; ext; simp } :
          ↥(K' : Subgroup (ULift.{w} H)) →* ↥G')
      (fun a b hab => Subtype.ext (MulEquiv.injective (MulEquiv.ulift (α := H))
        (congrArg (fun z : ↥G' => (z : H)) hab))) hli
  have htf' : Work.ORLocInd.IsTorsionFree (↥(K' : Subgroup (ULift.{w} H))) :=
    Work.ORLocInd.IsTorsionFree.of_injective
      ({ toFun := fun x => (⟨(MulEquiv.ulift (α := H)) x.1, x.2⟩ : ↥G')
         map_one' := by ext; simp
         map_mul' := by intro a b; ext; simp } :
          ↥(K' : Subgroup (ULift.{w} H)) →* ↥G')
      (fun a b hab => Subtype.ext (MulEquiv.injective (MulEquiv.ulift (α := H))
        (congrArg (fun z : ↥G' => (z : H)) hab))) htf
  exact ⟨(K' : Subgroup (ULift.{w} H)), K'.isNormal', K'.isFiniteIndex', htf', hli'⟩

/-- **The `RingDataDiv` of a finitely generated one-relator presentation**, from the M1 bridge
(nodes N5 + N6, with node N7 derived), node N4, node N3 and node N9. -/
noncomputable def ringDataDivOf (K : Type w) [Field K] [CharZero K] (n : ℕ) (r : FreeGroup (Fin n))
    (φK : K →+* ℂ)
    (hdiv : DivLoc K (ULift.{w, 0} (PresentedGroup ({r} : Set (FreeGroup (Fin n))))) φK)
    (hTor : FlatConcl K φK (hughesFreeInput_of_div K
      (oneRelator_ulift_presentedGroup n r) φK hdiv))
    (hgl : Work.ORCoherence.globalDim
      (MonoidAlgebra K (ULift.{w, 0} (PresentedGroup ({r} : Set (FreeGroup (Fin n)))))) ≤
        (2 : WithBot ℕ∞)) :
    RingDataDiv K (ULift.{w, 0} (PresentedGroup ({r} : Set (FreeGroup (Fin n))))) := by
  classical
  have hs : ∃ G'' : Subgroup (ULift.{w} (PresentedGroup ({r} : Set (FreeGroup (Fin n))))),
      G''.Normal ∧ G''.FiniteIndex ∧ Work.ORLocInd.IsTorsionFree G'' ∧
        Work.ORLocInd.Group.LocallyIndicable G'' :=
    exists_subgroup_ulift_locallyIndicable (ULift.{w} Unit)
      (H := PresentedGroup ({r} : Set (FreeGroup (Fin n))))
      (Work.ORLocInd.exists_normal_finiteIndex_torsionFree_locallyIndicable
        ⟨Fin n, r, ⟨MulEquiv.refl _⟩⟩ Work.OROneRel.oneRelatorCombinatorics)
  let G'' : Subgroup (ULift.{w} (PresentedGroup ({r} : Set (FreeGroup (Fin n))))) :=
    Classical.choose hs
  have hspec := Classical.choose_spec hs
  have hN'' : G''.Normal := hspec.1
  have hfin'' : G''.FiniteIndex := hspec.2.1
  have hli'' : Work.ORLocInd.Group.LocallyIndicable G'' := hspec.2.2.2
  exact RingDataDiv.ofEnvelope (Work.ORBridgeLinnell.countableEnvelope _) φK
    (hughesFreeInput_of_div K (oneRelator_ulift_presentedGroup n r) φK hdiv)
    G'' hN'' hfin'' (hdiv G'' hli'') hgl hTor

/-- **Theorem 1.1 of Jaikin-Zapirain--Linton**, conditional on `Work.ORFinal.FinalInput`.

The ring half at every finitely generated one-relator presentation is built from

* `h0`/`hV.hdiv` — **node N6** (with node N5's envelope and node N7 derived), in the form
  in which the JZLA20 engine is stated (`Work.ORFinal.DivLoc`): the division closure `D H` of `K[H]`
  in `U(G)` is a division ring for every *locally indicable* subgroup `H`;
* `h0`/`hV.hTor` — **nodes N3 + N8 + N9 + N1** (JL §5, Theorem 5.6): the flatness conclusion
  `Tor₂^{K[G]}(D(G), -) = 0` at the datum built from the above, for *nontrivial* relators `r ≠ 1`;
  the free case is proved here (`Work.ORFinal.flatConcl_free`), and so is node N3's global
  dimension bound for the free case (`Work.ORFinal.globalDim_le_two_free`,
  `Work.ORFinal.globalDim_le_two_free_ulift`) and for every nontrivial relator
  (`Work.ORFinal.globalDim_le_two_of_ne_one`).

Node N4 is used as a **theorem**, not a hypothesis: the finite-index subgroup `G'` of the
presentation, its normality, and its being torsion free *and locally indicable* come from
`Work.ORLocInd.exists_normal_finiteIndex_torsionFree_locallyIndicable`; locally indicability turns
the `DivLoc` hypothesis into the `hdiv_G'` field of the ring data, and
`Work.ORFinal.WeakSemisimple.isSemisimpleRing_D_of_divisionOn` turns that into the semisimplicity of
`S = D(G)` — so the `IsMulTorsionFree` requirement of `Work.ORAssembly.RingInputs` never appears.

The two copies `h0` (universe `0`) and `hV` (universe `v`) are the same hypothesis at the two
universes the proof needs; universes cannot be quantified over inside a hypothesis, hence the
anchor device of `Work.ORFinal.FinalInput`. -/
theorem theorem_1_1_of_hughesFree {G : Type u} {K : Type v} [Group G] [Field K] [CharZero K]
    (hG : Group.OneRelator G) (h0 : FinalInput Unit) (hV : FinalInput (ULift.{v} Unit)) :
    Group.Coherent G ∧ Ring.Coherent (MonoidAlgebra K G) := by
  -- the ring half at `ℚ`, for every finitely generated one-relator presentation (universe 0)
  have hRingQ' : ∀ (n : ℕ) (r : FreeGroup (Fin n)),
      Ring.Coherent (MonoidAlgebra ℚ (ULift.{0} (PresentedGroup ({r} : Set (FreeGroup (Fin n)))))) := by
    intro n r
    have hgl : Work.ORCoherence.globalDim
        (MonoidAlgebra ℚ (ULift.{0} (PresentedGroup ({r} : Set (FreeGroup (Fin n)))))) ≤
          (2 : WithBot ℕ∞) := by
      by_cases hr : r = 1
      · subst hr
        exact globalDim_le_two_free_ulift ℚ (X := Fin n)
      · exact globalDim_le_two_ulift ℚ (globalDim_le_two_of_ne_one (K := ℚ) n r hr)
    have hTor : FlatConcl ℚ (algebraMap ℚ ℂ) (hughesFreeInput_of_div ℚ
        (oneRelator_ulift_presentedGroup n r) (algebraMap ℚ ℂ)
        (h0.hdiv ℚ _ (algebraMap ℚ ℂ))) := by
      by_cases hr : r = 1
      · subst hr
        exact flatConclAt_of_globalDim_le_one ℚ _ (algebraMap ℚ ℂ) _ (globalDim_le_one_free_ulift ℚ
          (X := Fin n))
      · exact h0.hTor ℚ n r hr (algebraMap ℚ ℂ) _
    exact ringCoherent_of_ringDataDiv (ringDataDivOf ℚ n r (algebraMap ℚ ℂ)
      (h0.hdiv ℚ _ (algebraMap ℚ ℂ)) hTor hgl)
  have hRingQ : ∀ (n : ℕ) (r : FreeGroup (Fin n)),
      Ring.Coherent (MonoidAlgebra ℚ (PresentedGroup ({r} : Set (FreeGroup (Fin n))))) :=
    fun n r => (ringCoherent_ulift_group ℚ
      (H := PresentedGroup ({r} : Set (FreeGroup (Fin n))))).mpr (hRingQ' n r)
  -- the group half: `FP₂(ℚ)` for the finitely generated presentations, then all one-relator groups
  have hfp : ∀ (n : ℕ) (r : FreeGroup (Fin n)),
      Work.ORDunwoody.HomologicallyCoherent (ULift.{0} ℚ)
        (PresentedGroup ({r} : Set (FreeGroup (Fin n)))) :=
    fun n r => Work.ORAssembly.homologicallyCoherent_of_coherent
      ((Work.ORAssembly.ringCoherent_ulift_coeff ℚ _).mp (hRingQ n r))
  have hcoh0 := Work.ORAssembly.groupCoherent_of_fgInputs nodeInputs hfp
  refine ⟨?_, ?_⟩
  · refine Group.Coherent.of_oneRelator_of_fg G hG ?_
    intro n r
    exact hcoh0 _ ⟨Fin n, r, ⟨MulEquiv.refl _⟩⟩
  · -- the ring half at the coefficient field `K`, reduced to its finitely generated subfields
    refine Ring.Coherent.of_oneRelator_of_fg G K hG ?_
    intro n r
    refine Ring.Coherent.of_subfield (PresentedGroup ({r} : Set (FreeGroup (Fin n)))) K ?_
    intro S
    let F := ↥(Subfield.closure (S : Set K))
    obtain ⟨φF⟩ := fg_charZero_field_embeds_complex K S
    have hgl'' : Work.ORCoherence.globalDim
        (MonoidAlgebra F (ULift.{v} (PresentedGroup ({r} : Set (FreeGroup (Fin n)))))) ≤
          (2 : WithBot ℕ∞) := by
      by_cases hr : r = 1
      · subst hr
        exact globalDim_le_two_free_ulift F (X := Fin n)
      · exact globalDim_le_two_ulift F (globalDim_le_two_of_ne_one (K := F) n r hr)
    have hTor : FlatConcl F φF (hughesFreeInput_of_div F
        (oneRelator_ulift_presentedGroup n r) φF
        (hV.hdiv F _ φF)) := by
      by_cases hr : r = 1
      · subst hr
        exact flatConclAt_of_globalDim_le_one F _ φF _ (globalDim_le_one_free_ulift F (X := Fin n))
      · exact hV.hTor F n r hr φF _
    refine (ringCoherent_ulift_group F
      (H := PresentedGroup ({r} : Set (FreeGroup (Fin n))))).mpr ?_
    exact ringCoherent_of_ringDataDiv (ringDataDivOf F n r φF
      (hV.hdiv F _ φF) hTor hgl'')

end Work.ORFinal
