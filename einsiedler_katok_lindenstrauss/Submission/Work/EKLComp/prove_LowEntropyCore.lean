import Mathlib
import Submission.Work.EKLComp.C8Defs
import Submission.Work.EKLCompLeaf.step0_nontrivial
import Submission.Work.EKLCompLeaf.equiv_transfer
import Submission.Work.EKLCompLeaf.fixRadon
import Submission.Work.EKLCompLeaf.measurable_nu
import Submission.Work.EKLCompLeaf.measurable_leafMass
import Submission.Work.EKLCompLeaf.scaling_F1
import Submission.Work.EKLCompLeaf.luzin_riesz_of_radon
import Submission.Work.EKLComp.prove_MaxFlow
import Submission.Work.EKLComp.prove_X3
import Submission.Work.EKLCompSym.core_general
import Submission.Work.EKLCompSetup.exists_of
import Submission.Work.EKLCompSetup.limit_pair
import Submission.Work.EKLComp.prove_MaxLeaf
import Submission.Work.EKLComp.leaf_clause_pieces
import Submission.Work.EKLCompSetup.exists_of_layer
import Submission.Work.EKLRelCross.acovariant_of_isLeafwise

/-!
# C8 — the low entropy core (`Work.EKLContract.P_LowEntropyCore`)

Assembly of EKL §4.2–4.5 on top of the analytic core `Submission.Work.EKLC8Core` and the
leafwise-measure layer.  The vocabulary (`u`, `phi`, `par`, `nuR`) lives in
`Submission.Work.EKLComp.C8Defs`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Matrix
open Work.EKLContract Work.EKLComp

set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLComp

/-! ## 4. The derived facts of the leafwise layer

The five lemmas below extract from the frozen `IsLeafwise` interface exactly the facts the
assembly of EKL §4 (§5 Steps 0–12 of `ROUTE_LEAD.md`) needs.  They are stated for the
distinguished root group `U_01` and the flow `phi`; each is proved from the fields of
`IsLeafwise` (and `(U5)`, `(U7)`, `(U8)`, `(U9)` of `P_Leafwise`) plus `Mathlib`.
-/

/-! ## 4bis. The clause-level facts of the leafwise layer

The facts extracted from `P_Leafwise` and used by the setup construction (Steps 1–4) are
proved in the sibling modules of this directory and are re-exported here:

* `Work.EKLCompLeaf.scaling_F1` — (U7) ⇒ (F1) and (F2);
* `Work.EKLCompLeaf.luzin_riesz_of_radon` — (U6) ⇒ Luzin + Riesz;
* `Work.EKLCompLeaf.measurable_nu`, `Work.EKLCompLeaf.measurable_leafMass` — measurability
  of `x ↦ ν x (A ∩ ballU R)` and of the leaf masses `leafMass ν S R x`;
* `Work.EKLCompLeaf.step0_nontrivial`, `Work.EKLCompLeaf.equiv_transfer`,
  `Work.EKLCompLeaf.fixRadon` — Steps 0, (F4) and the global Radon normalisation.
-/

/-- (U6) ⇒ Luzin + Riesz, with the finiteness hypothesis in the global form used by the
assembly. -/
theorem luzin_riesz' {μ : Measure X3} [IsProbabilityMeasure μ] [T2Space X3]
    {ν : X3 → Measure SL3} {X' : Set X3}
    (hU6 : U6clause μ ν X') (hν : ∀ x, IsFiniteMeasureOnCompacts (ν x))
    (η : ℝ) (hη : 0 < η) :
    ∃ X₁ : Set X3, IsCompact X₁ ∧ X₁ ⊆ X' ∧ 1 - η < (μ X₁).toReal ∧
      (∀ f : CompactlySupportedContinuousMap SL3 ℝ,
        ContinuousOn (fun x => ∫ g, f g ∂(ν x)) X₁) ∧
      (∀ (y y' : X3) (ys ys' : ℕ → X3), (∀ n, ys n ∈ X₁) → (∀ n, ys' n ∈ X₁) →
        Tendsto ys atTop (𝓝 y) → Tendsto ys' atTop (𝓝 y') →
        (∀ n, ν (ys n) = ν (ys' n)) → ν y = ν y') :=
  Work.EKLCompLeaf.luzin_riesz_of_radon hU6 (fun x _ => hν x) η hη

/-! ## 5. Extracting the leafwise layer from `P_Leafwise` -/

section Extract

variable {μ : Measure X3} [IsProbabilityMeasure μ]

/-- The `A`-element `t₀ = (-1,1,0)` whose `aDiag` contracts `U_01`. -/
def t0 : Fin 3 → ℝ := ![(-1 : ℝ), 1, 0]

theorem phi_eq_aDiag_t0 (τ : ℝ) : phi τ = aDiag (τ • t0) := rfl

/-- `aDiag t₀` contracts `U_01`. -/
theorem tendsto_conj_Uij_h01 (u : SL3) (hu : u ∈ (Uij h01 : Set SL3)) :
    Tendsto (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (𝓝 1) := by
  obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff h01 u).mp hu
  exact Work.EKLContract.Lemmas.horoUij_tendsto_conj t0 h01 (by norm_num [t0]) s

/-- **(U8) at `U_01`**: from `¬ CrossSection` and ergodicity, the leafwise measures have no
atom at the identity a.e. -/
theorem no_atom_of_notCrossSection {μ : Measure X3} [IsProbabilityMeasure μ]
    {ν : X3 → Measure SL3} (hErg : IsAErgodic μ)
    (hU8 : IsAErgodic μ → CrossSection μ (Uij h01) ∨ ∀ᵐ x ∂μ, ν x {1} = 0)
    (hNCS : ¬ CrossSection μ (Uij h01)) : ∀ᵐ x ∂μ, ν x {1} = 0 :=
  (hU8 hErg).elim (fun h => absurd h hNCS) id

/-- **The leafwise layer for the distinguished configuration.**  From the frozen
`P_Leafwise` one gets a system of leafwise measures for `U_01`, made finite on compacts
everywhere (`fixRadon`), together with the four clauses (U5), (U6), (U7), (U9) used by the
assembly and the no-atom consequence of (U8). -/
theorem leaf_layer (hP : P_Leafwise) (hErg : IsAErgodic μ) :
    ∃ (ν : X3 → Measure SL3) (X' : Set X3),
      IsLeafwise μ (Uij h01) ν X' ∧ (∀ x, IsFiniteMeasureOnCompacts (ν x)) ∧
      U5clause μ ν ∧ U6clause μ ν X' ∧ U7clause μ ν X' ∧ U9clause μ ν ∧
      (IsAErgodic μ → CrossSection μ (Uij h01) ∨ ∀ᵐ x ∂μ, ν x {1} = 0) := by
  classical
  obtain ⟨ν₀, X', hL⟩ := (hP μ (Uij h01) (Work.EKLContract.Lemmas.isHoro_Uij h01) t0 (hErg.1 t0)
    tendsto_conj_Uij_h01).1
  obtain ⟨hU1, hU2, hU3, hU4, hU5, hU6, hU7, hU8, hU9⟩ :=
    (hP μ (Uij h01) (Work.EKLContract.Lemmas.isHoro_Uij h01) t0 (hErg.1 t0)
      tendsto_conj_Uij_h01).2 ν₀ X' hL
  obtain ⟨hL', hfin'⟩ := Work.EKLCompLeaf.fixRadon (U := Uij h01) hL
  refine ⟨fixRadon ν₀ X', X', hL', hfin', ?_, ?_, ?_, ?_, ?_⟩
  · -- (U5): a.e. statement, transported through `fixRadon_of_mem`
    have hmem : ∀ᵐ x ∂μ, x ∈ X' := by
      rw [MeasureTheory.ae_iff]
      exact hL.conull
    filter_upwards [hU5, hmem] with x hx hmx
    rw [fixRadon_of_mem hmx]
    exact hx
  · -- (U6): pointwise on `K ⊆ X'`
    intro ε hε
    obtain ⟨K, hKc, hKX, hKμ, hKcont⟩ := hU6 ε hε
    refine ⟨K, hKc, hKX, hKμ, ?_⟩
    refine fun f => (hKcont f).congr (fun x hx => ?_)
    show (∫ g, f g ∂(fixRadon ν₀ X' x)) = ∫ g, f g ∂(ν₀ x)
    rw [fixRadon_of_mem (hKX hx)]
  · -- (U7): the same conull set `X''`, where `fixRadon` agrees with `ν₀`
    obtain ⟨X'', hX''X, hX''m, hX''μ, hX''cov⟩ := hU7 hErg.1
    refine ⟨X'', hX''X, hX''m, hX''μ, ?_⟩
    intro t x hx htx
    obtain ⟨c, hc0, hct, hcov⟩ := hX''cov t x hx htx
    refine ⟨c, hc0, hct, ?_⟩
    rw [fixRadon_of_mem (hX''X hx), fixRadon_of_mem (hX''X htx)]
    exact hcov
  · -- (U9): the a.e. statements agree because `fixRadon = ν₀` a.e.
    intro hErg' hnot
    refine hU9 hErg' 0 1 h01 rfl ?_
    intro hν0
    exact hnot (by
      have hmem : ∀ᵐ x ∂μ, x ∈ X' := by
        rw [MeasureTheory.ae_iff]
        exact hL.conull
      filter_upwards [hν0, hmem] with x hx hmx
      rw [fixRadon_of_mem hmx]
      exact hx)
  · -- (U8)
    intro hErg'
    rcases hU8 hErg' with hcs | hatom
    · exact Or.inl hcs
    · refine Or.inr ?_
      have hmem : ∀ᵐ x ∂μ, x ∈ X' := by
        rw [MeasureTheory.ae_iff]
        exact hL.conull
      filter_upwards [hatom, hmem] with x hx hmx
      rw [fixRadon_of_mem hmx]
      exact hx

end Extract

/-! ## 6. Step 12 and the assembly of the distinguished configuration -/

/-- **Step 12**: the pair produced by Steps 6–11 contradicts Step 0, using the relative
cross-section hypothesis (through the field `B_rel` of `C8Setup`). -/
theorem contradiction_of_limit_pair {μ : Measure X3} [IsProbabilityMeasure μ]
    (D : C8Setup μ) {y y' : X3} {h : SL3}
    (hy : y ∈ D.X₁) (hy' : y' ∈ D.X₁)
    (hh : h ∈ (Upar h01 h02 h21 : Set SL3)) (hne : h ≠ 1) (heq : y' = h • y)
    (hnu : D.ν y = D.ν y') : False := by
  have hyB : y ∈ D.B := (D.X₁_sub hy).2
  have hyB' : y' ∈ D.B := (D.X₁_sub hy').2
  have hyX'' : y ∈ D.X'' := (D.X₁_sub hy).1
  have hy'X'' : y' ∈ D.X'' := (D.X₁_sub hy').1
  have hU : h ∈ (Uij h01 : Set SL3) :=
    D.B_rel y hyB h hh (by rw [← heq]; exact hyB')
  obtain ⟨s, hs⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff h01 h).mp hU
  have hsu : u s = h := hs
  have hs0 : s ≠ 0 := by
    intro h0
    apply hne
    rw [← hsu, h0]
    exact u_zero
  have e1 : u s • y = y' := by rw [hsu, heq]
  have hy'' : u s • y ∈ D.X'' := by rw [e1]; exact hy'X''
  exact (D.nontriv y hyX'' s hs0 hy'') (by rw [e1, hnu])

/-- **C8 in the distinguished configuration `(a,b,c) = (0,1,2)`.** -/
theorem core_012 (hX3 : P_X3) (hP : P_Leafwise) (hML : P_MaxLeaf) (hMF : P_MaxFlow)
    {μ : Measure X3} [IsProbabilityMeasure μ] (hErg : IsAErgodic μ)
    (hRel : RelCrossSection μ (Upar h01 h02 h21) (Uij h01))
    (hNCS : ¬ CrossSection μ (Uij h01)) (hNE : NonExceptional μ h01 2) :
    IsUInvariant μ (Uij h01) := by
  haveI : T2Space X3 := hX3.1
  haveI : PolishSpace X3 := hX3.2.1
  by_contra hninv
  obtain ⟨D⟩ := Work.EKLCompSetup.exists_of hX3 hP hML hMF hErg hNCS hRel hninv
  obtain ⟨y, y', h, hy, hy', hh, hne, heq, hnu⟩ := Work.EKLCompSetup.limit_pair D hNE
  exact contradiction_of_limit_pair D hy hy' hh hne heq hnu

/-- **Component C8 from its four inputs.**  This is the signature the lead's composition
expects: `P_X3 → P_Leafwise → P_MaxLeaf → P_MaxFlow → P_LowEntropyCore`. -/
theorem lowEntropyCore_of (hX3 : P_X3) (hP : P_Leafwise) (hML : P_MaxLeaf) (hMF : P_MaxFlow) :
    P_LowEntropyCore := by
  intro μ _ hErg a b c hab hac hcb hRel hNCS hNE
  exact Work.EKLCompSym.core_general
    (fun {_} _ hErg hRel hNCS hNE => core_012 hX3 hP hML hMF hErg hRel hNCS hNE)
    hErg a b c hab hac hcb hRel hNCS hNE

/-- **Component C8 with the two still-open pillars as hypotheses.**  `P_X3`, `P_MaxFlow` are
already proved in this workspace (`Work.EKLComp.prove_X3`, `Work.EKLComp.prove_MaxFlow`), so
only `P_Leafwise` (component C5) and `P_MaxLeaf` (component C11a) remain. -/
theorem lowEntropyCore_of_two (hP : P_Leafwise) (hML : P_MaxLeaf) : P_LowEntropyCore :=
  lowEntropyCore_of Work.EKLComp.prove_X3 hP hML Work.EKLComp.prove_MaxFlow

/-! ## 6bis. The clause-level route (no (U4) needed)

Component C8 consumes the leafwise layer only through the clauses (U5), (U6), (U7), (U8), (U9)
at the distinguished root group `U_01` — the clause (U4) of `P_Leafwise` is *not* used.  We
therefore assemble the layer from the clause-level facts, which are proved for an arbitrary
horospherical `U` in the `Work.EKLRelCross` library, instead of from the whole of `P_Leafwise`.

This makes `prove_LowEntropyCore` depend on strictly less than component C5. -/

/-- **The leafwise layer for `U_01`** (clause level): an `IsLeafwise` system for
`(μ, U_01, t₀)`, together with (U5), (U6), (U7), (U8), (U9) at `U_01`.

The clauses are assembled in `Work.EKLComp.leaf_clause_pieces`: existence is Pisa Thm 6.3
(`Work.EKLC7.P_LeafwiseEx`), (U5)/(U7)/(U8) at root groups are the package
`Work.EKLC7.P_RootProps`, (U6) is Luzin (`Work.EKLRelCross.leafwise_luzin`) and (U9) is
derived from (U7) by the period argument. -/
theorem leaf01_layer (hX3 : P_X3) {μ : Measure X3} [IsProbabilityMeasure μ]
    (hErg : IsAErgodic μ) :
    ∃ (ν₀ : X3 → Measure SL3) (X' : Set X3),
      IsLeafwise μ (Uij h01) ν₀ X' ∧
      U5clause μ ν₀ ∧ U6clause μ ν₀ X' ∧ U7clause μ ν₀ X' ∧
      (IsAErgodic μ → CrossSection μ (Uij h01) ∨ ∀ᵐ x ∂μ, ν₀ x {1} = 0) ∧
      U9clause μ ν₀ := by
  obtain ⟨ν₀, X', hL₀⟩ := leafwise_exists01 hErg.1
  have hU7 : U7clause μ ν₀ X' :=
    Work.EKLRelCross.acovariant_of_isLeafwise hX3 μ (Uij h01)
      Work.EKLCompSetup.isHoro_Uij_h01 Work.EKLCompSetup.t0 (hErg.1 Work.EKLCompSetup.t0)
      Work.EKLCompSetup.tendsto_conj_Uij_h01 ν₀ X' hL₀ hErg.1
  exact leaf_layer01 hX3 hErg ν₀ X' hL₀ hU7

/-- **C8 in the configuration `(0,1,2)`, clause-level route.** -/
theorem core_012_layer (hX3 : P_X3) (hML : P_MaxLeaf) (hMF : P_MaxFlow)
    {μ : Measure X3} [IsProbabilityMeasure μ] (hErg : IsAErgodic μ)
    (hRel : RelCrossSection μ (Upar h01 h02 h21) (Uij h01))
    (hNCS : ¬ CrossSection μ (Uij h01)) (hNE : NonExceptional μ h01 2) :
    IsUInvariant μ (Uij h01) := by
  by_contra hninv
  obtain ⟨ν₀, X', hL₀, hU5, hU6, hU7, hU8, hU9⟩ := leaf01_layer hX3 hErg
  obtain ⟨D⟩ := Work.EKLCompSetup.exists_of_layer hX3 hML hMF hErg hNCS hRel hninv
    ν₀ X' hL₀ hU5 hU6 hU7 hU8 hU9
  obtain ⟨y, y', h, hy, hy', hh, hne, heq, hnu⟩ := Work.EKLCompSetup.limit_pair D hNE
  exact contradiction_of_limit_pair D hy hy' hh hne heq hnu

/-- **Component C8 from the clause-level layer and `P_MaxLeaf`.** -/
theorem lowEntropyCore_of_layer (hX3 : P_X3) (hML : P_MaxLeaf) (hMF : P_MaxFlow) :
    P_LowEntropyCore := by
  intro μ _ hErg a b c hab hac hcb hRel hNCS hNE
  exact Work.EKLCompSym.core_general
    (fun {_} _ hErg hRel hNCS hNE => core_012_layer hX3 hML hMF hErg hRel hNCS hNE)
    hErg a b c hab hac hcb hRel hNCS hNE

/-- **The frozen component C8.**

## What is proved in this file (no `sorry`)

* `leaf_layer` — the leafwise system for `U_01` extracted from `P_Leafwise` (the clauses (U5),
  (U6), (U7), (U8), (U9) of `P_Leafwise`), normalised by `fixRadon` so that it is finite on
  compacts *everywhere*;
* `luzin_riesz'` — (U6) ⇒ Luzin + Riesz with the finiteness hypothesis in global form;
* `contradiction_of_limit_pair` — Step 12 of `ROUTE_LEAD.md` §5;
* `core_012` — the whole assembly in the configuration `(a,b,c) = (0,1,2)`, from the four
  component `Prop`s and the two big delegated pieces;
* `lowEntropyCore_of` — the same in the signature the lead's composition expects,
  `P_X3 → P_Leafwise → P_MaxLeaf → P_MaxFlow → P_LowEntropyCore`;
* `lowEntropyCore_of_two` — the same with the two already-proved pillars (`prove_X3`,
  `prove_MaxFlow`) discharged;
* `leaf01_layer` — the leafwise layer at `U_01` in *clause* form (see
  `Work.EKLComp.leaf_clause_pieces`), i.e. existence (Pisa Thm 6.3, via the flower
  construction of `Work.EKLC7`) plus the clauses (U5), (U6), (U7), (U8), (U9) at `U_01`, with
  (U7) = EKL (4) = Pisa 7.16 from `Work.EKLRelCross.acovariant_of_isLeafwise`;
* `core_012_layer`, `lowEntropyCore_of_layer` — the same assembly with the clause-level layer
  in place of `P_Leafwise`, and finally
* `prove_LowEntropyCore` — the frozen component C8, proved from `prove_X3`, `prove_MaxLeaf`,
  `prove_MaxFlow` and the clause-level layer.  In particular C8 does **not** need the clause
  (U4) of `P_Leafwise` (nor the still-open `Work.EKLComp.prove_Leafwise`): it is assembled from
  the clause-level facts, which are proved for root groups in `Work.EKLC7` /
  `Work.EKLRelCross`.

All other inputs are imported from sorry-free sibling modules:

* `Work.EKLCompLeaf.{step0_nontrivial, equiv_transfer, fixRadon, measurable_nu,
  measurable_leafMass, scaling_F1, luzin_riesz_of_radon}` — the clause-level facts (Steps 0,
  (F4), (U7) ⇒ (F1), (F2), (U6) ⇒ Luzin/Riesz, measurability);
* `Work.EKLCompSetup.exists_of` — Steps 1–4 (the construction of `C8Setup`, i.e. the sets
  `X₁, X₂, 𝒳(ρ), X₃` and the flow-averaging and density bounds);
* `Work.EKLCompSetup.limit_pair` — Steps 6–11 (the shear/H-property argument and the limit
  extraction), the heart of EKL §4.4–4.5;
* `Work.EKLCompSym.core_general` — the `S₃`-symmetry reduction from `(0,1,2)` to an
  arbitrary ordered triple of distinct indices.

## Status

This file is **sorry-free**.  The component `Prop`s of the frozen contract used here are
`prove_X3` (C2), `prove_MaxLeaf` (C11a) and `prove_MaxFlow` (C11b), all proved in this
namespace; the remaining leafwise-measure input of C8 is the clause-level layer at `U_01`
assembled in `Work.EKLComp.leaf_clause_pieces`.
The theorem below is therefore the frozen component C8.  For reference, the variant taking
the whole of `P_Leafwise` instead of the clause-level layer is
`lowEntropyCore_of : P_X3 → P_Leafwise → P_MaxLeaf → P_MaxFlow → P_LowEntropyCore`. -/
theorem prove_LowEntropyCore : Work.EKLContract.P_LowEntropyCore :=
  lowEntropyCore_of_layer Work.EKLComp.prove_X3 Work.EKLComp.prove_MaxLeaf
    Work.EKLComp.prove_MaxFlow

end Work.EKLComp
