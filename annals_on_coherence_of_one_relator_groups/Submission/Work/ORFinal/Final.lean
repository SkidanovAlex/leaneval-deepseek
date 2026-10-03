/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Theorem 1.1 conditional on node N6 only: `Prop 3.11` + one flatness input

This is the headline file of `Submission/Work/ORFinal/`.

## What is discharged

* **Node N6 is a theorem.**  `Work.ORDivLoc.N6EngineInput` — the input of the JZLA20 engine
  (over `ℂ`, the construction `Work.ORHughesFree.Section6.thm61Step_nonempty`) — is *proved* in
  `Work.ORFinal.n6EngineInput`.
* **The analytic input of the ring half is node ORP311's Proposition 3.11.**  From
  `∀ G, Work.ORDivLoc.Prop311OnComplexClosure G` (`h311`) and the above,
  `Work.ORFinal.hdiv_of_prop311` produces node N6's (I4) in the form the JZLA20 engine is stated in,
  `Work.ORFinal.DivLoc`; `Work.ORFinal.hughesFreeInput_of_div` (node N7 being a theorem of this
  directory) then yields the M1 bridge's `HughesFreeInput`.
* **The group half.**  `Work.ORFinal.nodeInputs` discharges every group-theoretic node (N2, N12,
  N13), so the group half of Theorem 1.1 has no hypothesis left beyond the ring half at `ℚ`.
* **The coefficient-field reduction.**  The ring half is run at universe `0` with a *real*
  coefficient field `L : Type 0` and an embedding `ψ : L →+* ℝ` (composed with `ℝ ↪ ℂ`).
  `Work.ORFinal.ringCoherent_of_charZero` (in `Submission/Work/ORFinal/RealReduction.lean`) then
  transports the conclusion to an *arbitrary* char-0 coefficient field `K`, by reducing to its
  finitely generated subfields and their real-embeddable subfields.  Without this, the
  mirror/antipode of JL Lemma 5.1′ is available only for real embeddings — see §6(b) of
  `README.md`.

## The single remaining input

`Work.ORFinal.RealTorInput` is the last hypothesis: the flatness conclusion `Tor₂ = 0` of JL §5,
Theorem 5.6, at a real coefficient field, in the *Magnus configuration* in which the delivered node
`Work.ORLyndon.magnus_torTwoVanishes` consumes it — the group is the presentation
`⟨Fin n | r⟩` itself (no `ULift`), at universe `0`.  Its proof is the T7 assembly: feed
`Work.ORLyndon.magnus_torTwoVanishes` with `hA` (nodes N8 + N1, T2/T4/T5 of this directory),
`hswap` (N1, T5) and `hchain` (N1, T6), for the Linnell datum
`Work.ORBridgeLinnell.linnellDatumOfEnvelope (countableEnvelope ⟨Fin n | r⟩) ψc hin`.

## Main results

* `Work.ORFinal.n6EngineInput` — node N6's engine input, from `thm61Step_nonempty`.
* `Work.ORFinal.hdiv_of_prop311` — `Work.ORFinal.DivLoc` from [JZLA20, Proposition 3.11].
* `Work.ORFinal.RealTorInput` — the JL §5 flatness input at a real coefficient field.
* `Work.ORFinal.ringCoherent_free_presentedGroup` — the free case `r = 1` (no flatness input).
* `Work.ORFinal.ringCoherent_presentedGroup_of_magnus` — the ring half for a Magnus configuration
  of the relator, from `RealTorInput`.
* `Work.ORFinal.theorem_1_1_of_prop311` — Theorem 1.1 from `Prop311OnComplexClosure` and
  `RealTorInput`.
-/
import Submission.Work.ORDivLoc.ToORFinal
import Submission.Work.ORHughesFree.Section6.thm61Step_nonempty
import Submission.Work.ORFinal.RealReduction
import Submission.Work.ORFinal.Main
import Submission.Work.ORFinal.Magnus.exists_magnus_data
import Submission.Work.ORLocInd.Main
import Submission.Work.OROneRel.oneRelatorCombinatorics

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe u v

namespace Work.ORFinal

open Work.ORAssembly

/-! ## Node N6 is a theorem -/

/-- **Node N6's engine input is a theorem.**  `Work.ORDivLoc.N6EngineInput` is the input taken from
the JZLA20 engine (the construction `Work.ORHughesFree.Section6.thm61Step_nonempty` over `ℂ`), and
`Work.ORHughesFree.Section6.thm61Step_nonempty` proves it. -/
theorem n6EngineInput : Work.ORDivLoc.N6EngineInput := by
  intro G₀ _ _ U _ _ _ hpos φ rkU hfaith hφ hstar hHF H₀ hfg hne
  exact Work.ORHughesFree.Section6.thm61Step_nonempty (K := ℂ) hpos φ rkU hfaith hφ hstar hHF
    H₀ hfg hne

/-- **The analytic input of the ring half, from [JZLA20, Proposition 3.11].**  From
`∀ G, Prop311OnComplexClosure G` and node N6 (a theorem, `Work.ORFinal.n6EngineInput`), node N6's
(I4) holds in the form in which the JZLA20 engine is stated: the division closure `D H` of `K[H]` in
`U(G)` is a division ring for every *locally indicable* subgroup `H ≤ G`. -/
theorem hdiv_of_prop311
    (h311 : ∀ (G : Type) [Group G] [Countable G], Work.ORDivLoc.Prop311OnComplexClosure G) :
    ∀ (K : Type) [Field K] (G : Type) [Group G] [Countable G] (φK : K →+* ℂ), DivLoc K G φK :=
  Work.ORDivLoc.finalInputUnit_hdiv h311 n6EngineInput

/-! ## The one remaining ring-half input -/

/-- **The JL §5 flatness input at a *real* coefficient field.**

For every field `L : Type 0` of characteristic zero, every embedding `ψ : L →+* ℝ` (composed with
`ℝ ↪ ℂ` to give `ψc : L →+* ℂ`), every presentation `⟨Fin n | r⟩` with `r ≠ 1` in the Magnus
configuration — `r = u ^ l` with `1 ≤ l`, `u` not a proper power, `r` cyclically reduced, a
distinguished generator `t` and the remaining set `Y` with `t ∉ Y`, every generator outside `Y`
equal to `t`, and `r ∉ ⟨Y⟩` — the flatness conclusion `Tor₂^{L[G]}(D(G), -) = 0` of JL §5,
Theorem 5.6, at the Linnell datum of the M1 bridge for `G = ⟨Fin n | r⟩`.

This is exactly the shape in which the delivered node `Work.ORLyndon.magnus_torTwoVanishes`
consumes its inputs `hA` (nodes N8 + N1), `hswap` (node N1) and `hchain` (node N1), which is why it
is stated in the Magnus configuration of the relator: the Magnus data itself is produced *outside*
this input, by `Work.ORFinal.Magnus.exists_magnus_data`, and the transport from the cyclically
reduced conjugate `r'` back to `r` is performed at the level of `Ring.Coherent` in
`Work.ORFinal.theorem_1_1_of_prop311`. -/
def RealTorInput : Prop :=
  ∀ (L : Type) [Field L] [CharZero L] (ψ : L →+* ℝ) (n : ℕ)
    (r u : FreeGroup (Fin n)) (l : ℕ) (t : Fin n) (Y : Finset (Fin n)),
    r ≠ 1 → 1 ≤ l → r = u ^ l → ¬ Work.OROneRel.IsProperPower u →
    Work.OROneRel.IsCyclicallyReducedRelator r → t ∉ Y →
    (∀ x : Fin n, x ∉ Y → x = t) →
    r ∉ Subgroup.closure (FreeGroup.of '' (Y : Set (Fin n))) →
    ∀ (hdiv : DivLoc L (PresentedGroup ({r} : Set (FreeGroup (Fin n))))
        ((algebraMap ℝ ℂ).comp ψ))
      (hin : Work.ORBridgeLinnell.HughesFreeInput L
        (PresentedGroup ({r} : Set (FreeGroup (Fin n))))
        (Work.ORBridgeLinnell.countableEnvelope
          (PresentedGroup ({r} : Set (FreeGroup (Fin n)))))
        ((algebraMap ℝ ℂ).comp ψ)),
      FlatConcl L ((algebraMap ℝ ℂ).comp ψ) hin

/-! ## The ring half at a real coefficient field -/

/-- The presentation `⟨Fin n | 1⟩` is the free group `F(Fin n)`, which is `IsMulTorsionFree`
(`Work.OROneRel.presentedGroup_one_iso_freeGroup` plus Mathlib's instance for free groups). -/
instance instIsMulTorsionFreePresentedGroupTrivialRelator (n : ℕ) :
    IsMulTorsionFree (PresentedGroup ({1} : Set (FreeGroup (Fin n)))) := by
  obtain ⟨e⟩ := Work.OROneRel.presentedGroup_one_iso_freeGroup (α := Fin n)
  exact Function.Injective.isMulTorsionFree e.toMonoidHom e.injective

/-- **The free case `r = 1`.**  For a real coefficient field `L : Type 0`, the group algebra
`L[⟨Fin n | 1⟩]` is coherent.  Node N3's `gl.dim ≤ 1` for free groups
(`Work.ORFinal.FreeCase.globalDim_le_one_free`) gives the flatness conclusion outright
(`Work.ORFinal.flatConclAt_of_globalDim_le_one`), and the division closures needed to *state* the
datum come from `hdiv`. -/
theorem ringCoherent_free_presentedGroup
    (hdiv : ∀ (K : Type) [Field K] (G : Type) [Group G] [Countable G] (φK : K →+* ℂ),
      DivLoc K G φK)
    (L : Type) [Field L] [CharZero L] (ψ : L →+* ℝ) (n : ℕ) :
    Ring.Coherent (MonoidAlgebra L (PresentedGroup ({1} : Set (FreeGroup (Fin n))))) := by
  classical
  let ψc : L →+* ℂ := (algebraMap ℝ ℂ).comp ψ
  have hdivL : DivLoc L (PresentedGroup ({1} : Set (FreeGroup (Fin n)))) ψc := hdiv L _ ψc
  let hin := hughesFreeInput_of_div L ⟨Fin n, 1, ⟨MulEquiv.refl _⟩⟩ ψc hdivL
  exact ringCoherent_of_ringData
    (RingData.ofEnvelope (Work.ORBridgeLinnell.countableEnvelope _) ψc hin
      ⊤ inferInstance inferInstance inferInstance
      (globalDim_le_two_free L (Fin n))
      (flatConclAt_of_globalDim_le_one L _ ψc hin
        (FreeCase.globalDim_le_one_free L (Fin n))))

/-- **The ring half at a real coefficient field, in the Magnus configuration of the relator.**
For `L : Type 0`, `ψ : L →+* ℝ`, and a nontrivial cyclically reduced relator `r` with the Magnus
set-up `(t, Y)`, `L[⟨Fin n | r⟩]` is coherent, from the flatness input `Work.ORFinal.RealTorInput`
and node N4.

The proof builds the `RingDataDiv` of the presentation: node N4 gives the normal finite-index
subgroup `G'` (`Work.ORLocInd.exists_normal_finiteIndex_torsionFree_locallyIndicable`), `hdiv` gives
the division-ring property of `D G'`, node N3 gives `gl.dim L[G] ≤ 2`
(`Work.ORFinal.globalDim_le_two_of_ne_one`), and `RealTorInput` gives `Tor₂ = 0`; the semisimplicity
of `D(G)` then comes from `Work.ORFinal.WeakSemisimple.isSemisimpleRing_D_of_divisionOn`, and node
N10 (`Work.ORCoherence.coherent_of_embeds_semisimple`) concludes. -/
theorem ringCoherent_presentedGroup_of_magnus
    (hM : RealTorInput)
    (hdiv : ∀ (K : Type) [Field K] (G : Type) [Group G] [Countable G] (φK : K →+* ℂ),
      DivLoc K G φK)
    (L : Type) [Field L] [CharZero L] (ψ : L →+* ℝ) (n : ℕ)
    (r u : FreeGroup (Fin n)) (l : ℕ) (t : Fin n) (Y : Finset (Fin n))
    (hr : r ≠ 1) (hl : 1 ≤ l) (hpow : r = u ^ l) (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hcr : Work.OROneRel.IsCyclicallyReducedRelator r) (htY : t ∉ Y)
    (hY : ∀ x : Fin n, x ∉ Y → x = t)
    (hnotmem : r ∉ Subgroup.closure (FreeGroup.of '' (Y : Set (Fin n)))) :
    Ring.Coherent (MonoidAlgebra L (PresentedGroup ({r} : Set (FreeGroup (Fin n))))) := by
  classical
  let ψc : L →+* ℂ := (algebraMap ℝ ℂ).comp ψ
  have hdivL : DivLoc L (PresentedGroup ({r} : Set (FreeGroup (Fin n)))) ψc := hdiv L _ ψc
  let hin := hughesFreeInput_of_div L ⟨Fin n, r, ⟨MulEquiv.refl _⟩⟩ ψc hdivL
  have hTor : FlatConcl L ψc
      (hughesFreeInput_of_div L ⟨Fin n, r, ⟨MulEquiv.refl _⟩⟩ ψc hdivL) :=
    hM L ψ n r u l t Y hr hl hpow hpp hcr htY hY hnotmem hdivL hin
  obtain ⟨G', hN', hfin', _, hli'⟩ :=
    Work.ORLocInd.exists_normal_finiteIndex_torsionFree_locallyIndicable
      ⟨Fin n, r, ⟨MulEquiv.refl _⟩⟩ Work.OROneRel.oneRelatorCombinatorics
  exact ringCoherent_of_ringDataDiv
    (RingDataDiv.ofEnvelope (Work.ORBridgeLinnell.countableEnvelope _) ψc hin
      G' hN' hfin' (hdivL G' hli')
      (globalDim_le_two_of_ne_one (K := L) n r hr) hTor)

/-! ## Theorem 1.1 from Proposition 3.11 and the flatness input -/

/-- **Theorem 1.1 of Jaikin-Zapirain--Linton, conditional on node ORP311's Proposition 3.11 and the
JL §5 flatness input** (`Work.ORFinal.RealTorInput`).

The proof:

* the ring half at `ℚ` (universe `0`) for every finitely generated one-relator presentation
  `⟨Fin n | r⟩`: for `r = 1` this is `Work.ORFinal.ringCoherent_free_presentedGroup`, and for
  `r ≠ 1` it is `Work.ORFinal.ringCoherent_presentedGroup_of_magnus` applied to the cyclically
  reduced conjugate `r'` of `r` produced by `Work.ORFinal.Magnus.exists_magnus_data`, followed by
  the transport along `⟨Fin n | r'⟩ ≃* ⟨Fin n | r⟩`;
* the group half: `FP₂(ℚ)` for the finitely generated presentations (node N11,
  `Work.ORAssembly.homologicallyCoherent_of_coherent`), promoted to all one-relator groups in
  `Type 0` by node N0's free-factor reduction (`Work.ORAssembly.groupCoherent_of_fgInputs`, which
  uses the delivered group-theoretic node inputs `Work.ORFinal.nodeInputs`), and then to `G` itself
  by `Group.Coherent.of_oneRelator_of_fg`;
* the ring half at an arbitrary char-0 field `K`: the coefficient-field reduction
  `Work.ORFinal.ringCoherent_of_charZero` (finitely generated subfields, `Work.ORFinal.RealReduction`)
  reduces to the real case at universe `0`, and `Ring.Coherent.of_oneRelator_of_fg` transports to
  `G`. -/
theorem theorem_1_1_of_hdiv {G : Type u} {K : Type v} [Group G] [Field K] [CharZero K]
    (hdiv : ∀ (K : Type) [Field K] (G : Type) [Group G] [Countable G] (φK : K →+* ℂ),
      DivLoc K G φK)
    (hM : RealTorInput) (hG : Group.OneRelator G) :
    Group.Coherent G ∧ Ring.Coherent (MonoidAlgebra K G) := by
  -- the ring half at a real coefficient field, for every finitely generated one-relator
  -- presentation
  have hreal : ∀ (L : Type) [Field L] [CharZero L] (ψ : L →+* ℝ) (n : ℕ) (r : FreeGroup (Fin n)),
      Ring.Coherent (MonoidAlgebra L (PresentedGroup ({r} : Set (FreeGroup (Fin n))))) := by
    intro L _ _ ψ n r
    by_cases hr : r = 1
    · subst hr
      exact ringCoherent_free_presentedGroup hdiv L ψ n
    · obtain ⟨r', e, l, u, t, Y, hr', hl, hpow, hpp, htY, hY, hcr, hnotmem, _⟩ :=
        Magnus.exists_magnus_data L n r hr
      refine Ring.Coherent.of_ringEquiv (MonoidAlgebra.mapDomainRingEquiv L e) ?_
      exact ringCoherent_presentedGroup_of_magnus hM hdiv L ψ n r' u l t Y
        hr' hl hpow hpp hcr htY hY hnotmem
  -- `ℚ[H]` is coherent for every finitely generated one-relator group `H`
  have hQ : ∀ (n : ℕ) (r : FreeGroup (Fin n)),
      Ring.Coherent (MonoidAlgebra ℚ (PresentedGroup ({r} : Set (FreeGroup (Fin n))))) :=
    fun n r => hreal ℚ (algebraMap ℚ ℝ) n r
  -- `FP₂(ℚ)` for the finitely generated presentations (node N11)
  have hfp : ∀ (n : ℕ) (r : FreeGroup (Fin n)),
      Work.ORDunwoody.HomologicallyCoherent (ULift.{0} ℚ)
        (PresentedGroup ({r} : Set (FreeGroup (Fin n)))) :=
    fun n r => Work.ORAssembly.homologicallyCoherent_of_coherent
      ((Work.ORAssembly.ringCoherent_ulift_coeff ℚ _).mp (hQ n r))
  have hcoh0 := Work.ORAssembly.groupCoherent_of_fgInputs nodeInputs hfp
  refine ⟨?_, ?_⟩
  · exact Group.Coherent.of_oneRelator_of_fg G hG (fun n r =>
      hcoh0 (PresentedGroup ({r} : Set (FreeGroup (Fin n)))) ⟨Fin n, r, ⟨MulEquiv.refl _⟩⟩)
  · refine Ring.Coherent.of_oneRelator_of_fg G K hG ?_
    intro n r
    refine (ringCoherent_ulift_group K (H := PresentedGroup ({r} : Set (FreeGroup (Fin n))))).mpr ?_
    exact ringCoherent_of_charZero K (X := PresentedGroup ({r} : Set (FreeGroup (Fin n))))
      (fun L _ _ ψ => hreal L ψ n r)

/-- **Theorem 1.1 of Jaikin-Zapirain--Linton, conditional on node ORP311's Proposition 3.11 and the
JL §5 flatness input** (`Work.ORFinal.RealTorInput`): the same as
`Work.ORFinal.theorem_1_1_of_hdiv`, with (I4) in the JZLA20 engine's form supplied by
`Work.ORFinal.hdiv_of_prop311`. -/
theorem theorem_1_1_of_prop311 {G : Type u} {K : Type v} [Group G] [Field K] [CharZero K]
    (h311 : ∀ (H : Type) [Group H] [Countable H], Work.ORDivLoc.Prop311OnComplexClosure H)
    (hM : RealTorInput) (hG : Group.OneRelator G) :
    Group.Coherent G ∧ Ring.Coherent (MonoidAlgebra K G) :=
  theorem_1_1_of_hdiv (hdiv_of_prop311 h311) hM hG

end Work.ORFinal
