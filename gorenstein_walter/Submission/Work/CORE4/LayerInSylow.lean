import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.TMemOfSylow
import Submission.Work.CORE4.RelIndexSubgroupOfOdd
import Submission.Work.CORE4.QuotientSylowDihedral

namespace Work.CORE4

/-- Bender 1981, §4, p. 224: Bender's choice of the Sylow 2-subgroup, and the Sylow 2-subgroup of
`E(M)`.  Hypotheses: `M` is a coatom with `t = B.t ∈ E := layerIn M`, and `P ≤ M ⊓ B.H = C_M(t)`
is a `2`-subgroup with `¬ 2 ∣ P.relIndex M` (so `P ∈ Syl₂(M)`), plus the layer facts `Odd |Z(E)|`
and `E/Z(E) ≅ A₇` or `PSL(2,q)`.

Conclusion: `t ∈ P ⊓ E`; `(P ⊓ E).subgroupOf E` is a `2`-subgroup of `↥E` of odd index (a Sylow);
and it is isomorphic to `DihedralGroup n`, `n ≥ 2`.

Route.  For `t ∈ P`: `t` is a central `2`-element of the finite group `↥(M ⊓ B.H)` of order `2`, so
`⟨t⟩ ⊴ C_M(t)`; a normal `p`-subgroup lies in every Sylow (`IsPGroup.le_sylow_of_normal`), so `t`
lies in any Sylow `S` of `↥(M ⊓ B.H)` containing `P.subgroupOf (M ⊓ B.H)` (`IsPGroup.exists_le_sylow`);
that containment is an equality because both sides have cardinality the `2`-part of
`|M ⊓ B.H|` (`Sylow.card_eq_multiplicity`, `Nat.factorization_mul`, cf. the computation of
`hcardP₀` in `Submission.Work.CORE4/Case2Setup9.lean`).
For the index: `E ⊴ M` (`Work.CORE4.layerIn_subgroupOf_normal_gen`) and `E·P ≤ M`, so
`|E : E ⊓ P| = |E·P : P|` (second isomorphism theorem, `Subgroup.relIndex_mul_card`,
`Subgroup.relIndex_sup_left`), which divides the odd number `|M : P|`.  The `relIndex` in the group
`↥E` agrees with `|E : E ⊓ P|` (`Subgroup.relIndex_subgroupOf`).
For the dihedrality: `Q ⊓ Z(E) = ⊥` since a `2`-group meets the odd centre trivially, so `Q'`
embeds in `↥E ⧸ Z(E)`; its image has odd index there (the order of the centre is odd)
and is therefore a Sylow `2`-subgroup of `↥E ⧸ Z(E) ≅ A₇` or `≅ PSL(2,q)`, which
`I.toolkit.a7` (Sylow `2` of `A₇` is `DihedralGroup 4`) and `I.toolkit.l2syl` describe.
`Submission.Work.CORE2A/sylow_two_dihedral_of_quotient.lean` is a template for the last reduction
in another area (it cannot be imported: other areas redeclare the `Work.GW2` vocabulary). -/
theorem LayerInSylow (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M P : Subgroup G),
        IsCoatom M → B.t ∈ Work.GW2.layerIn M →
        IsPGroup 2 P → P ≤ M ⊓ B.H → ¬ 2 ∣ P.relIndex M →
        Odd (Nat.card ↥(Subgroup.center ↥(Work.GW2.layerIn M))) →
        (Nonempty ((↥(Work.GW2.layerIn M) ⧸ Subgroup.center ↥(Work.GW2.layerIn M)) ≃*
            alternatingGroup (Fin 7)) ∨
          ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
            Nonempty ((↥(Work.GW2.layerIn M) ⧸ Subgroup.center ↥(Work.GW2.layerIn M)) ≃*
              Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) →
        B.t ∈ P ⊓ Work.GW2.layerIn M ∧
        IsPGroup 2 ((P ⊓ Work.GW2.layerIn M).subgroupOf (Work.GW2.layerIn M)) ∧
        ¬ 2 ∣ ((P ⊓ Work.GW2.layerIn M).subgroupOf (Work.GW2.layerIn M)).relIndex ⊤ ∧
        ∃ n : ℕ, 2 ≤ n ∧
          Nonempty (((P ⊓ Work.GW2.layerIn M).subgroupOf (Work.GW2.layerIn M)) ≃*
            DihedralGroup n) := by
  intro G _ _ hctx B M P hcoat htE hP2 hPM hrel hoddZ hshape
  -- `t ∈ M` and `P ≤ M`
  have htM : B.t ∈ M := Work.CORE4.layerIn_le M htE
  have hPM' : P ≤ M := le_trans hPM inf_le_left
  -- `P` centralizes `t`, because `P ≤ M ⊓ B.H = M ⊓ C_G(t)`
  have hcent : ∀ x ∈ P, x * B.t = B.t * x := by
    intro x hx
    have hxH : x ∈ B.H := (hPM hx).2
    rwa [Subgroup.mem_centralizer_singleton_iff] at hxH
  -- `t` is an involution
  have ht2 : B.t ^ 2 = 1 := by
    have h := pow_orderOf_eq_one B.t
    rwa [B.t_order] at h
  have htP : B.t ∈ P := TMemOfSylow M P B.t htM ht2 hP2 hPM' hcent hrel
  -- `P` normalizes `E = layerIn M` (which is normal in `M`)
  have hPE : P ≤ Subgroup.normalizer ((Work.GW2.layerIn M : Subgroup G) : Set G) :=
    fun x hx => Work.CORE4.layerIn_le_normalizer M (hPM' hx)
  -- `(P ⊓ E).subgroupOf E` is a `2`-subgroup of `↥E` (transport along the inclusion)
  have hQ2 : IsPGroup 2 ((P ⊓ Work.GW2.layerIn M).subgroupOf (Work.GW2.layerIn M)) :=
    (hP2.to_le (show P ⊓ Work.GW2.layerIn M ≤ P from inf_le_left)).of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (show P ⊓ Work.GW2.layerIn M ≤ Work.GW2.layerIn M from inf_le_right)).symm
  -- ... of odd index, i.e. a Sylow `2`-subgroup of `↥E`
  have hQodd : ¬ 2 ∣ ((P ⊓ Work.GW2.layerIn M).subgroupOf (Work.GW2.layerIn M)).relIndex ⊤ :=
    RelIndexSubgroupOfOdd (Work.GW2.layerIn M) P M (Work.CORE4.layerIn_le M) hPE hPM' hrel
  refine ⟨⟨htP, htE⟩, hQ2, hQodd, ?_⟩
  -- and hence dihedral, as `↥E` has odd centre with `A₇`/`PSL(2,q)` quotient
  exact QuotientSylowDihedral I.toolkit.a7 I.toolkit.l2syl hoddZ hshape
    ((P ⊓ Work.GW2.layerIn M).subgroupOf (Work.GW2.layerIn M)) hQ2 hQodd

/-! ## How this file is proved

The proof uses the three inputs delegated for it (each proved in its own module, `sorry`-free):

* `Work.CORE4.TMemOfSylow` (`Submission/Work/CORE4/TMemOfSylow.lean`): the element `t`, which lies
  in `M` and centralizes the `2`-subgroup `P ≤ M` of odd index in `M`, lies in `P`.  (Simpler than
  the route described in the docstring above: `P ⊔ ⟨t⟩ ≤ M` is a `2`-group, so
  `Nat.card (P ⊔ ⟨t⟩) ∣ Nat.card M = P.relIndex M * Nat.card P`, and both cardinals are powers of
  `2` with `P.relIndex M` odd; hence `Nat.card (P ⊔ ⟨t⟩) ≤ Nat.card P` and `P ⊔ ⟨t⟩ = P`.)
* `Work.CORE4.RelIndexSubgroupOfOdd` (`Submission/Work/CORE4/RelIndexSubgroupOfOdd.lean`): the odd
  index of `P ⊓ E` in `E`, via the second isomorphism theorem in index form
  (`Work.CORE4.relIndex_eq_relIndex_inf_of_normal_sup_eq`, from `Case2CountSetup`).
* `Work.CORE4.QuotientSylowDihedral` (`Submission/Work/CORE4/QuotientSylowDihedral.lean`): odd index
  and `2`-group means Sylow in `↥E`; odd centre `A₇`/`PSL(2,q)` quotient means dihedral, the same
  reduction as `Submission/Work/CORE2A/sylow_two_dihedral_of_quotient.lean` (not importable here). -/

end Work.CORE4
