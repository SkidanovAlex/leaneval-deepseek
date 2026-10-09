/-!
# NOTE (session 17): the mixed-level realisation gate is FALSE -- the assembly needs a redesign

(No declarations in this file; it records a structural finding about the `z`-construction of
`Submission/Work/SSGRoute/shafarevich_z_construction.lean`.)

## 1. What the assembly requires

`Work.SSGRoute.auxExists_of_pairing_and_realisation` (`ZConstruction/AuxAssembly.lean`) proves

    AuxPairingGate K  ->  (∀ M, AuxRealisationExt K Λ M)  ->  AuxExists K Λ S

and it applies its realisation hypothesis at `M = N`, the level of the *other* summand of the
section-4 induction (`Work.SSGRoute.z_data_of_spanning_of_aux` calls `AuxExists` with
`N = N₀ ⊔ Λ`).  The orthogonality hypothesis it feeds to the realisation is produced by the proved
p. 18 chase `Work.SSGRoute.auxDatum_orthogonal_of_productFormula`, whose dual family is relaxed at
the level **`Λ`** and at no larger level (the chase at a larger level is the retracted, false
`Work.SSGRoute.AuxOrthogonalityGate`; cf. `ZConstruction/AuxChaseVacuity.lean` for the no-go).  So the
statement actually consumed is the **mixed** one

    AuxRealisationNoInv K Λ M   ("do duals relaxed at Λ imply realisability by a class unramified at
                                  the places outside the T'-classes that are not split in M")

with `M = N ⊋ Λ` in general.  Primal conditions at `M`, dual conditions at `Λ`.

## 2. The mixed statement is false

Write `A_Λ` for the classes unramified at the finite places outside the `T'`-classes that are not
split in `Λ` (the primal space at level `Λ`), `V_Λ` / `V_M` for their localisation images in
`D = ∏_{A ∈ T'} H¹(decomp k A ⊓ G_K, 𝔽_p)`, and `W_Λ`, `W_M` for the localisations of the
`Λ`-resp. `M`-relaxed dual classes (`Work.SSGRoute.IsRelaxedDual`).  Since `Λ ≤ M` implies
`M`-split ⟹ `Λ`-split, one has `Relaxed(Λ) ⊆ Relaxed(M)`, hence `W_Λ ⊆ W_M`; Poitou--Tate at the
level `M` is `V_M = W_M^⊥`.  Now the mixed gate says: `[f] ⊥ W_Λ ⟹ [f] ∈ V_M`, i.e.
`W_Λ^⊥ ⊆ W_M^⊥`.  It is *strictly stronger* than the level-`M` realisation
(`W_M^⊥ ⊆ W_M^⊥`), and the extra content is exactly

    (*)  every `Λ`-primal class `z` (i.e. every `z ∈ A_Λ`) is orthogonal to every `M`-relaxed dual
         `b`, over the places of `T'`:  `∑_{A ∈ T'} pair (D_A ⊓ G_K) z b = 0`.

(*) is **false**, and both the proof and the counterexample are in the workspace:

* the class `z ∈ A_Λ` *is* orthogonal to every `Λ`-relaxed dual, by the **proved**
  `Work.SSGRoute.ZConstruction.relaxedSum_pair_eq_zero`; so `[z] ∈ W_Λ^⊥`;
* but `M`-relaxation only forces `b` to be *unramified* (rather than locally trivial) at the places
  that are split in `Λ` but not in `M`; nothing kills the corresponding local Tate pairing between
  the ramified values of `z` and the unramified values of `b` there.  Concretely
  (`p = 3`, `k = K = Λ = ℚ`, `M` the Galois closure of the cubic field of conductor `7`,
  `T = T' = {A₇}`, `b` = the cubic character of conductor `7`, `z` = a cubic character of conductor
  `q ≡ 1 (mod 3)` with `b(Frob_q) ≠ 1`): the product formula gives `term(7) + term(q) = 0` while the
  mixed sum is `term(7)` alone, and `term(7) ≠ 0` because `z_q` is ramified and `b_q` is the
  nontrivial unramified class, with `(H¹_nr)^⊥ = H¹_nr`.

Both formulations of the extra content were submitted to two independent reviewers this session and
were declared false in both cases: `Work.SSGRoute.RelaxedDualsAgree K Λ M` (the local-component
agreement of the two relaxed dual families, `ZConstruction/AuxRealisationLevel.lean`) and the
reciprocity statement (*) (`SSGRoute/ZConstruction/relaxedReciprocity_of_le`, review log).  Hence:

> **`AuxRealisationNoInv K Λ M` (and `AuxRealisationExt K Λ M`) is false whenever `M` strictly
> contains `Λ` and the two levels really differ at places outside the `T`-classes.**  The hypothesis
> `∀ M, AuxRealisationExt K Λ M` of `Work.SSGRoute.auxExists_of_pairing_and_realisation` is therefore
> unsatisfiable, and *that assembly can never be applied*.

## 3. Consequences, and what to do instead

* The node's obligation is still `Work.SSGRoute.MupGate` + `Work.SSGRoute.AuxExists`
  (`ZConstruction/ZDataAux.lean`), but `AuxExists` is **not** reducible to the pairing gate and the
  realisation by the present assembly.  Nothing false is asserted on disk -- every lemma above
  `AuxExists` takes it as a hypothesis, and `ZConstruction/ZDataGeneral.lean`'s
  `z_data_general_of_ramified` is still the node's single `sorry` -- so the chain is *sound*, it is
  the *decomposition* of `AuxExists` that is broken.
* Where the level `N ⊋ Λ` enters: the level step
  `Work.SSGRoute.hasZData_sum_of_level_data` (`ZConstruction/ZDataLevelStep.lean`) requires the
  auxiliary class `z₁` to satisfy `HasZData K N S' yAux z₁`, i.e. in particular to be unramified at
  the finite places outside the `S'`-classes that are not split in `N`.  That is case (b1) of its
  proof: at a place split in `N` the vanishing of `z⁰` on `G_N` kills the inertia, and at the other
  places the auxiliary class (stage `z₁`) must not add ramification.  The *primal* level `N` is thus
  forced by the level step, while the *dual* level `Λ` is forced by the chase: the two cannot be
  reconciled, and a redesign is needed.  The two natural options:
  1. weaken the level step: let the auxiliary class be required to be unramified only at the places
     that are not split in `Λ`, and handle the extra places (split in `Λ`, not in `N`) by the
     vanishing of `z⁰` on `G_N` -- this needs a new case analysis, and possibly a smaller auxiliary
     field than `N₀ ⊔ Λ`;
  2. obtain the auxiliary class *without* the level step, e.g. by the sibling lane's route
     (`Work.SSGRoute.IsYRealisation` / `exists_isYRealisation_of_localisation` in
     `SSGRoute/shafarevich_theorem13.lean`, whose `IsYRealisation` prescribes *pointwise vanishing*
     of the auxiliary class at the new places -- the restriction that this lane's gate lacks and
     whose absence is exactly the failure of (*) above); the bridge
     `Work.SSGRoute.z_data_general_of_realisation` (`ZConstruction/ZDataRealisation.lean`) is on
     disk for that purpose.
* Deliverables of this session (all sorry-free, axiom-clean, building):
  `ZConstruction/LevelKVocab.lean` (the level-`K` counting vocabulary relocated *below* the node, so
  that the level-`K` Poitou--Tate counting identity of `PT/pt_counting_identity_h1.lean` is
  consumable here) and `ZConstruction/AuxRealisationLevel.lean` (the reduction of the mixed gate to
  the unmixed one plus the named slack, together with the refutation of the slack).
-/
