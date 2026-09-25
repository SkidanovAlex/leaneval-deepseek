import Mathlib
import Submission.Work.RelatorRank.ProP
import Submission.Work.RelatorRank.GeneratorRank.exists_card_frattiniQuotient_eq_two_pow
import Submission.Work.RelatorRank.GeneratorRank.le_generatorRank_of_surjective_elementaryAbelian
import Submission.Work.RelatorRank.ProPFrattini.denseGenerating_of_sup_pFrattini
import Submission.Work.RelatorRank.Abstract.genRank_eq_dGens
import Submission.Work.ProPDeficiency.nonempty_equiv_frattini_zmod_pow
import Submission.Commons.GroupTheory.PGroup.frattini_eq_pow_sup_commutator

/-!
# The generator rank of a finitely generated pro-`2` group is the rank of its Frattini quotient

**Namespace** `Work.RelatorRank.GeneratorRank`; module
`Submission.Work.RelatorRank.GeneratorRank.generatorRank_eq_log_card_frattiniQuotient`.

Burnside's basis theorem for finitely generated pro-`p` groups says that a dense generating family
of `Γ` of minimal size is obtained by lifting a basis of the elementary abelian quotient
`Γ ⧸ Φ(Γ)`, where `Φ(Γ) = pFrattini p Γ` is the `p`-Frattini subgroup.  In particular

  `GeneratorRank Γ = Nat.log 2 (Nat.card (Γ ⧸ pFrattini 2 Γ))`

whenever `Γ` is a finitely generated pro-`2` group: the quotient by the Frattini subgroup is
elementary abelian of exponent `2`, hence an `𝔽₂`-vector space, and its dimension (`= Nat.log 2` of
its cardinality) is exactly the minimal number of generators.

The proof assembles the two halves of Burnside's theorem:

* **Lower bound** (`Nat.log 2 |Γ ⧸ Φ(Γ)| ≤ GeneratorRank Γ`): the quotient
  `Γ ⧸ Φ(Γ) ⧸ frattini (Γ ⧸ Φ(Γ))` is isomorphic to the elementary abelian `2`-group of rank
  `dGens (Γ ⧸ Φ(Γ))` (`Work.ProPDeficiency.nonempty_equiv_frattini_zmod_pow`, whose Frattini-quotient
  form `frattini (Γ ⧸ Φ) = ⊥` is `Commons.GroupTheory.PGroup.frattini_eq_bot_of_elementary_abelian`),
  so `Γ` has a continuous surjection onto `(ℤ/2)^{dGens (Γ ⧸ Φ)}`; the rank of such a quotient
  cannot exceed `GeneratorRank Γ` (`GeneratorRank.le_generatorRank_of_surjective_elementaryAbelian`).
* **Upper bound** (`GeneratorRank Γ ≤ Nat.log 2 |Γ ⧸ Φ(Γ)|`): `dGens (Γ ⧸ Φ(Γ))` elements of
  `Γ ⧸ Φ(Γ)` generating it lift to `Γ`; a family whose image generates the Frattini quotient densely
  generates `Γ` (`ProPFrattini.denseGenerating_of_sup_pFrattini`, Burnside's non-generator property).

The numerical identity `Nat.log 2 |Γ ⧸ Φ(Γ)| = dGens (Γ ⧸ Φ(Γ))` is the cardinality comparison
`|Γ ⧸ Φ(Γ)| = 2 ^ dGens (Γ ⧸ Φ(Γ))` coming from the group isomorphism above, together with
`Nat.log_pow`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false

namespace Work.RelatorRank.GeneratorRank

open Work.ProPDeficiency

theorem generatorRank_eq_log_card_frattiniQuotient {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    (hp : IsProPGroup 2 Γ) (hfg : ∃ d, HasDenseGeneratingFamily Γ d) :
    GeneratorRank Γ = Nat.log 2 (Nat.card (Γ ⧸ (pFrattini 2 Γ))) := by
  classical
  set Φ : Subgroup Γ := pFrattini 2 Γ with hΦdef
  haveI hΦn : Φ.Normal := by rw [hΦdef]; exact ProPFrattini.pFrattini_normal 2
  have hΦcl : IsClosed (Φ : Set Γ) := by
    rw [hΦdef, pFrattini]
    exact Subgroup.isClosed_topologicalClosure _
  haveI hΦcli : IsClosed (Φ : Set Γ) := hΦcl
  -- a dense generating family of `Γ` and the cardinality of the Frattini quotient
  obtain ⟨d, gen, hgen⟩ := hfg
  have hfg' : ∃ d : ℕ, HasDenseGeneratingFamily Γ d := ⟨d, gen, hgen⟩
  obtain ⟨k, _hkd, hcard⟩ := exists_card_frattiniQuotient_eq_two_pow hp gen hgen
  have hcardΦ : Nat.card (Γ ⧸ Φ) = 2 ^ k := by rw [hΦdef]; exact hcard
  -- the Frattini quotient is finite, discrete, abelian and of exponent two
  haveI hfin : Finite (Γ ⧸ Φ) := by
    have hpos : 0 < Nat.card (Γ ⧸ Φ) := by rw [hcardΦ]; positivity
    exact (Nat.card_pos_iff.mp hpos).2
  haveI : T1Space (Γ ⧸ Φ) := inferInstance
  haveI : Fintype (Γ ⧸ Φ) := Fintype.ofFinite _
  haveI hdisc : DiscreteTopology (Γ ⧸ Φ) := inferInstance
  have hsq : ∀ x : Γ ⧸ Φ, x ^ 2 = 1 := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Φ x
    rw [← map_pow, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff (g ^ 2)).mpr (by rw [hΦdef]; exact pow_mem_pFrattini 2 g)
  haveI hQcomm : IsMulCommutative (Γ ⧸ Φ) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
      (by rw [hΦdef]; exact commutator_le_pFrattini 2)
  haveI hQP : IsPGroup 2 (Γ ⧸ Φ) :=
    (IsPGroup.iff_card (p := 2) (G := Γ ⧸ Φ)).mpr ⟨k, hcardΦ⟩
  -- the Frattini subgroup of an elementary abelian group is trivial, so Burnside's theorem gives
  -- `Γ ⧸ Φ(Γ) ⧸ frattini ≃* (ℤ/2)^{dGens (Γ ⧸ Φ)}`
  have hfr : frattini (Γ ⧸ Φ) = ⊥ :=
    Commons.GroupTheory.PGroup.frattini_eq_bot_of_elementary_abelian (p := 2) hsq
  obtain ⟨E₁⟩ := nonempty_equiv_frattini_zmod_pow (p := 2) hQP
  -- cardinality comparison: `k = dGens (Γ ⧸ Φ)`
  have h1 : Nat.card (Γ ⧸ Φ) = Nat.card ((Γ ⧸ Φ) ⧸ frattini (Γ ⧸ Φ)) := by
    rw [hfr]
    exact (Nat.card_congr (QuotientGroup.quotientBot (G := Γ ⧸ Φ)).toEquiv).symm
  have h2 : Nat.card ((Γ ⧸ Φ) ⧸ frattini (Γ ⧸ Φ)) = 2 ^ dGens (Γ ⧸ Φ) := by
    rw [Nat.card_congr E₁.toEquiv, Nat.card_fun, Nat.card_fin,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2), Nat.card_zmod]
  have hk : k = dGens (Γ ⧸ Φ) :=
    Nat.pow_right_injective (le_refl 2) (hcardΦ.symm.trans (h1.trans h2))
  -- lower bound: `Γ` has a continuous surjection onto `(ℤ/2)^{dGens (Γ ⧸ Φ)}`
  have hqcont1 : Continuous (QuotientGroup.mk' Φ : Γ → Γ ⧸ Φ) := by
    rw [QuotientGroup.coe_mk']
    exact QuotientGroup.continuous_mk
  have hqcont2 : Continuous (QuotientGroup.mk' (frattini (Γ ⧸ Φ)) :
      (Γ ⧸ Φ) → (Γ ⧸ Φ) ⧸ frattini (Γ ⧸ Φ)) := by
    rw [QuotientGroup.coe_mk']
    exact QuotientGroup.continuous_mk
  haveI hdisc2 : DiscreteTopology ((Γ ⧸ Φ) ⧸ frattini (Γ ⧸ Φ)) :=
    QuotientGroup.discreteTopology (isOpen_discrete _)
  have hEcont : Continuous (E₁ : ((Γ ⧸ Φ) ⧸ frattini (Γ ⧸ Φ)) →
      (Fin (dGens (Γ ⧸ Φ)) → Multiplicative (ZMod 2))) := continuous_of_discreteTopology
  let F : Γ →* (Fin (dGens (Γ ⧸ Φ)) → Multiplicative (ZMod 2)) :=
    E₁.toMonoidHom.comp ((QuotientGroup.mk' (frattini (Γ ⧸ Φ))).comp (QuotientGroup.mk' Φ))
  have hFcont : Continuous ⇑F := by
    change Continuous fun x : Γ =>
      E₁ (QuotientGroup.mk' (frattini (Γ ⧸ Φ)) (QuotientGroup.mk' Φ x))
    exact hEcont.comp (hqcont2.comp hqcont1)
  have hFsurj : Function.Surjective ⇑F :=
    E₁.surjective.comp ((QuotientGroup.mk'_surjective (frattini (Γ ⧸ Φ))).comp
      (QuotientGroup.mk'_surjective Φ))
  have hle : dGens (Γ ⧸ Φ) ≤ GeneratorRank Γ :=
    le_generatorRank_of_surjective_elementaryAbelian F hFcont hFsurj hfg'
  -- upper bound: `dGens (Γ ⧸ Φ)` generators of the Frattini quotient lift to `Γ`
  have hUnivGen : IsGeneratingSet (Finset.univ : Finset (Γ ⧸ Φ)) := by
    rw [isGeneratingSet_iff, Finset.coe_univ]
    exact Subgroup.closure_univ
  obtain ⟨S, hSgen, hScard⟩ :=
    exists_generatingSet_card_dGens (G := Γ ⧸ Φ) ⟨Finset.univ, hUnivGen⟩
  have hfam : HasGeneratingFamily (Γ ⧸ Φ) (dGens (Γ ⧸ Φ)) := by
    rw [← hScard]
    exact Work.RelatorRank.Abstract.hasGeneratingFamily_card_of_isGeneratingSet hSgen
  obtain ⟨e, he⟩ := hfam
  let gen' : Fin (dGens (Γ ⧸ Φ)) → Γ :=
    fun j => Classical.choose (QuotientGroup.mk'_surjective Φ (e j))
  have hspec : ∀ j, QuotientGroup.mk' Φ (gen' j) = e j :=
    fun j => Classical.choose_spec (QuotientGroup.mk'_surjective Φ (e j))
  have hmap : Subgroup.map (QuotientGroup.mk' Φ) (Subgroup.closure (Set.range gen')) = ⊤ := by
    rw [MonoidHom.map_closure]
    have himg : (QuotientGroup.mk' Φ) '' Set.range gen' = Set.range e := by
      ext x
      constructor
      · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
        exact ⟨j, (hspec j).symm⟩
      · rintro ⟨j, rfl⟩
        exact ⟨gen' j, ⟨j, rfl⟩, hspec j⟩
    rw [himg]
    exact he
  have hsup : Subgroup.closure (Set.range gen') ⊔ Φ = ⊤ :=
    (ProPFrattini.map_mk'_eq_top_iff Φ (Subgroup.closure (Set.range gen'))).mp hmap
  have hdense : DenseGenerating gen' := by
    refine ProPFrattini.eq_top_of_sup_pFrattini_eq_top hp
      (Subgroup.isClosed_topologicalClosure _) ?_
    rw [← hΦdef]
    exact le_antisymm le_top
      (le_trans (le_of_eq hsup.symm) (sup_le_sup_right (Subgroup.le_topologicalClosure _) Φ))
  have hge : GeneratorRank Γ ≤ dGens (Γ ⧸ Φ) :=
    generatorRank_le_of_hasDenseGeneratingFamily ⟨gen', hdense⟩
  -- conclusion
  have hEq : GeneratorRank Γ = dGens (Γ ⧸ Φ) := le_antisymm hge hle
  rw [show Nat.card (Γ ⧸ pFrattini 2 Γ) = 2 ^ k from hcard,
    Nat.log_pow (by norm_num : 1 < 2)]
  exact hEq.trans hk.symm

end Work.RelatorRank.GeneratorRank
