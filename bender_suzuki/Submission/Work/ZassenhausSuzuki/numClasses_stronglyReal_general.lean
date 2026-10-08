import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.CountingDefs
import Submission.Work.ZassenhausSuzuki.GenHypSetup
import Submission.Work.ZassenhausSuzuki.invH_mul_t_conj_iff_general
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.lemma4

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-- Removing a fixed element (here `1`) from a finite subgroup costs exactly one element. -/
private lemma card_subtype_mem_ne_one {G : Type*} [Group G] [Finite G] (K : Subgroup G) :
    Nat.card {u : G // u ∈ (K : Set G) ∧ u ≠ 1} = Nat.card ↥K - 1 := by
  have h1 : Nat.card {u : G // u ∈ (K : Set G) ∧ u ≠ 1}
      = Nat.card (((K : Set G) \ {1}) : Set G) := rfl
  rw [h1, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem (K.one_mem),
    ← Nat.card_coe_set_eq (K : Set G)]
  congr 1

/-- **Suzuki 1962, §8, p. 118 (general hypotheses).**  In a split rank-one Zassenhaus
configuration `H = Q ⋊ D` with `Q` a `2`-group — i.e. `IsSplitRankOne H Q t`, `IsZassenhaus H`
and `IsPGroup 2 Q`, *without* the extra `HasFourGroup G` and the distinguished involution
`(s * t) ^ 3 = 1` carried by `SzHyp` — the strongly real elements `x ≠ 1` with `x * x ≠ 1`
(products of two involutions which are not involutions themselves) fall into exactly
`|Q₀sub H| - 1` conjugacy classes.

This is `Work.ZassenhausSuzuki.numClasses_stronglyReal` with the unused part of the hypothesis
bundle removed: the proof never uses `HasFourGroup G` or the involution `s`; only the three
fields of `Work.ZassenhausSuzuki.GenHyp` enter.  Indeed
(`Work.ThmF.ChV12.exists_conj_eq_inv_mul_t`) every such `x` is conjugate to `u * t` for some
non-trivial `u ∈ Q₀ = Inv(H) ∪ {1}`, and conversely each such `u * t` has the required property;
`Work.ZassenhausSuzuki.invH_mul_t_conj_iff_general` (Suzuki 1962 Prop. 13) says that
`u ↦` (class of `u * t`) is injective, and `Q₀ \ {1} = Inv(H)` has `|Q₀| - 1` elements. -/
theorem numClasses_stronglyReal_general {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q) :
    Work.ZassenhausSuzuki.numClasses
        {x : G | Work.ZassenhausSuzuki.IsStronglyReal x ∧ x ≠ 1 ∧ x * x ≠ 1}
      = Nat.card ↥(Work.ThmF.Q0sub H) - 1 := by
  classical
  set X : Set G := {x : G | Work.ZassenhausSuzuki.IsStronglyReal x ∧ x ≠ 1 ∧ x * x ≠ 1}
  have hcomm := Work.ZassenhausSuzuki.invH_commute_z hsplit h2
  have hElem := Work.ThmF.L5.Q0sub_elementary (H := H) hcomm
  have hInv : ∀ u : G, u ∈ (Work.ThmF.Q0sub H : Set G) → u ≠ 1 →
      u ∈ Submission.Blueprint.involutions (H : Set G) := fun u hu hu1 => hElem.2.2 u hu hu1
  have ht_inv : t * t = 1 := by
    have h3 := pow_orderOf_eq_one t
    rw [hsplit.invol] at h3
    simpa [pow_two] using h3
  have memX : ∀ u : G, u ∈ (Work.ThmF.Q0sub H : Set G) → u ≠ 1 → (u * t) ∈ X := by
    intro u hu hu1
    refine ⟨⟨u, t, hElem.1 u hu, ht_inv, rfl⟩, ?_, ?_⟩
    · intro hcontra
      have ht_eq : t = u⁻¹ := eq_inv_of_mul_eq_one_right hcontra
      exact hsplit.not_mem (ht_eq ▸ H.inv_mem (Work.ThmF.Q0sub_le H hu))
    · exact mul_t_sq_ne_one_general ⟨hsplit, hzass, h2⟩ (hInv u hu hu1)
  let f : {u : G // u ∈ (Work.ThmF.Q0sub H : Set G) ∧ u ≠ 1} →
      {C : ConjClasses G // (C.carrier ∩ X).Nonempty} := fun u =>
    ⟨ConjClasses.mk (u.1 * t), ⟨u.1 * t, ConjClasses.mem_carrier_mk, memX u.1 u.2.1 u.2.2⟩⟩
  have hf_inj : Function.Injective f := by
    intro u u' hff
    have hmk : ConjClasses.mk (u.1 * t) = ConjClasses.mk (u'.1 * t) :=
      congrArg Subtype.val hff
    have hconj : ∃ g, g * (u.1 * t) * g⁻¹ = u'.1 * t := by
      rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hmk
      exact hmk
    exact Subtype.ext (invH_mul_t_conj_iff_general ⟨hsplit, hzass, h2⟩ u.1 u'.1
      (hInv u.1 u.2.1 u.2.2) (hInv u'.1 u'.2.1 u'.2.2) hconj)
  have hf_surj : Function.Surjective f := by
    rintro ⟨C, hC⟩
    obtain ⟨x, hxC, hxX⟩ := hC
    obtain ⟨hsr, _, hx2⟩ := hxX
    obtain ⟨u, huQ0, hu1, g, hg⟩ :=
      Work.ThmF.ChV12.exists_conj_eq_inv_mul_t hsplit.stronglyEmbedded hsplit.twoTransitive
        hsplit.invol hsplit.not_mem
        (Work.ThmF.ChV12.involution_commute_conj hcomm) hx2 hsr
    refine ⟨⟨u, Work.ThmF.Q0_le_Q0sub H huQ0, hu1⟩, ?_⟩
    have hmkx : ConjClasses.mk x = C := ConjClasses.mem_carrier_iff_mk_eq.mp hxC
    have hmku : ConjClasses.mk (u * t) = ConjClasses.mk x := by
      rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
      exact ⟨g⁻¹, by rw [← hg]; group⟩
    apply Subtype.ext
    change ConjClasses.mk (u * t) = C
    rw [hmku, hmkx]
  have key : Work.ZassenhausSuzuki.numClasses X
      = Nat.card {u : G // u ∈ (Work.ThmF.Q0sub H : Set G) ∧ u ≠ 1} := by
    change Nat.card {C : ConjClasses G // (C.carrier ∩ X).Nonempty} = _
    exact (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm
  rw [key]
  exact card_subtype_mem_ne_one (Work.ThmF.Q0sub H)

end Work.ZassenhausSuzuki
