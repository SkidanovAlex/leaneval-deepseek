import Mathlib
import Submission.Work.BSW.S3.Defs

/-!
# The normalizer of a maximal intersection of two Sylow `p`-subgroups has no normal Sylow
`p`-subgroup

This is the classical remark used by Bender in the proof of (3.7) of the Brauer–Suzuki–Wall
theorem (see `REFS/bender1974_bsw.txt`): if `X = A ⊓ B` is an intersection of two *distinct*
Sylow `p`-subgroups of maximal cardinality, then `N_G(X)` is **not** `p`-closed, i.e. it has no
normal Sylow `p`-subgroup.

The proof is the standard one.  Suppose `P ◁ N_G(X)` is a `p`-subgroup of index prime to `p`
(equivalently, the unique Sylow `p`-subgroup of `N_G(X)`).  Since `X` is a normal `p`-subgroup
of `N_G(X)`, every `p`-subgroup of `N_G(X)` lies in `P`, so in particular `N_A(X) ≤ P` and
`N_B(X) ≤ P`.  As `X ⊊ A`, the "normalizers grow" property of the `p`-group `A` gives
`X ⊊ N_A(X)`.  Extending `P` to a Sylow `p`-subgroup `U` of `G`, we find
`X ⊊ N_A(X) ≤ A ⊓ U`, so `|A ⊓ U| > |X|`; by maximality of `|X|`, this forces `U = A`
(and, the same way, `U = B`), so `A = B`, a contradiction.
-/

namespace Work.BSW.S3

/-- **Normalizers grow in a finite `p`-group.**  If `X` is a proper subgroup of a finite
`p`-group `A` (inside an ambient finite group `G`), then `X < N_A(X) = A ⊓ N_G(X)`.

This is the normalizer condition for the (nilpotent) group `A`. -/
lemma nnns_grow_normalizer {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A X : Subgroup G} (hA : IsPGroup p A) (hX : X ≤ A) (hne : X ≠ A) :
    X < A ⊓ Subgroup.normalizer (X : Set G) := by
  have hnil : Group.IsNilpotent ↥A := IsPGroup.isNilpotent hA
  have hnc : NormalizerCondition ↥A := Group.normalizerCondition_of_isNilpotent
  -- `X`, viewed inside the `p`-group `A`, is a proper subgroup
  have hHtop : X.subgroupOf A < (⊤ : Subgroup ↥A) := by
    rw [lt_top_iff_ne_top]
    intro h
    exact hne (le_antisymm hX (Subgroup.subgroupOf_eq_top.mp h))
  have hlt : X.subgroupOf A < Subgroup.normalizer ((X.subgroupOf A : Subgroup ↥A) : Set ↥A) :=
    hnc _ hHtop
  obtain ⟨w, hw1, hw2⟩ := IsConcreteLE.exists_of_lt hlt
  -- `w` is an element of `A` normalizing `X` but not lying in `X`
  have hwA : w ∈ (Subgroup.normalizer (X : Set G)).subgroupOf A := by
    rw [Subgroup.subgroupOf_normalizer_eq hX]
    exact hw1
  have hwG : (w : G) ∈ Subgroup.normalizer (X : Set G) := Subgroup.mem_subgroupOf.mp hwA
  have hwX : (w : G) ∉ X := fun h => hw2 (Subgroup.mem_subgroupOf.mpr h)
  refine lt_of_le_of_ne (le_inf hX Subgroup.le_normalizer) ?_
  intro heq
  have hmem : (w : G) ∈ A ⊓ Subgroup.normalizer (X : Set G) := ⟨w.2, hwG⟩
  rw [← heq] at hmem
  exact hwX hmem

/-- **Every `p`-subgroup of `N` lies in a normal `p`-subgroup `P` of `N` of index prime to
`p`.**  Indeed `P` is then the unique Sylow `p`-subgroup of `N`. -/
lemma nnns_pgroup_le_normal_pgroup {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {N P : Subgroup G} (hPnorm : (P.subgroupOf N).Normal) (hidx : ¬ p ∣ (P.subgroupOf N).index)
    (hPp : IsPGroup p P) :
    ∀ Q : Subgroup G, Q ≤ N → IsPGroup p Q → Q ≤ P := by
  intro Q hQN hQp
  suffices hs : Q.subgroupOf N ≤ P.subgroupOf N by
    intro q hq
    have h1 : (⟨q, hQN hq⟩ : ↥N) ∈ Q.subgroupOf N := Subgroup.mem_subgroupOf.mpr hq
    exact Subgroup.mem_subgroupOf.mp (hs h1)
  have hPsub : IsPGroup p (P.subgroupOf N) := hPp.comap_subtype
  have hPnorm' : (P.subgroupOf N).Normal := hPnorm
  -- `P.subgroupOf N` is a normal `p`-subgroup of `N`, hence lies in every Sylow of `N`; as its
  -- index in `N` is prime to `p` it *is* a Sylow of `N`.
  obtain ⟨S, hSle⟩ := IsPGroup.exists_le_sylow (hQp.comap_subtype (K := N))
  have hPS : P.subgroupOf N ≤ (S : Subgroup ↥N) := IsPGroup.le_sylow_of_normal hPsub S
  have hcard : Nat.card ↥(P.subgroupOf N) = Nat.card ↥(S : Subgroup ↥N) := by
    have h1 : Nat.card ↥(↑(hPsub.toSylow hidx) : Subgroup ↥N) =
        p ^ (Nat.card ↥N).factorization p := Sylow.card_eq_multiplicity (hPsub.toSylow hidx)
    rw [IsPGroup.toSylow_coe] at h1
    exact h1.trans (Sylow.card_eq_multiplicity S).symm
  have hPeq : (P.subgroupOf N : Subgroup ↥N) = ↑S :=
    Subgroup.eq_of_le_of_card_ge hPS (le_of_eq hcard.symm)
  exact hSle.trans (le_of_eq hPeq.symm)

/-- **Bender's remark (proof of (3.7) of the Brauer–Suzuki–Wall theorem).**  The normalizer of a
maximal (by cardinality) intersection `X = A ⊓ B` of two distinct Sylow `p`-subgroups has no
normal Sylow `p`-subgroup, i.e. is not `p`-closed. -/
theorem normalizerNoNormalSylow {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A B : Sylow p G} (hAB : A ≠ B) {X : Subgroup G}
    (hX : X = (A : Subgroup G) ⊓ (B : Subgroup G))
    (hmax : ∀ C D : Sylow p G, C ≠ D →
      Nat.card ↥((C : Subgroup G) ⊓ (D : Subgroup G)) ≤ Nat.card ↥X) :
    ¬ ∃ P : Subgroup G, P ≤ Subgroup.normalizer (X : Set G) ∧ IsPGroup p P ∧
      (P.subgroupOf (Subgroup.normalizer (X : Set G))).Normal ∧
      ¬ p ∣ (P.subgroupOf (Subgroup.normalizer (X : Set G))).index := by
  rintro ⟨P, hPle, hPp, hPnorm, hidx⟩
  set N : Subgroup G := Subgroup.normalizer (X : Set G) with hN
  -- `X` sits inside `A`, `B` and `N = N_G(X)`
  have hXA : X ≤ (A : Subgroup G) := by rw [hX]; exact inf_le_left
  have hXB : X ≤ (B : Subgroup G) := by rw [hX]; exact inf_le_right
  have hXN : X ≤ N := by rw [hN]; exact Subgroup.le_normalizer
  have hAp : IsPGroup p (A : Subgroup G) := A.isPGroup'
  have hBp : IsPGroup p (B : Subgroup G) := B.isPGroup'
  have hcardAB : Nat.card ↥(A : Subgroup G) = Nat.card ↥(B : Subgroup G) := by
    rw [Sylow.card_eq_multiplicity A, Sylow.card_eq_multiplicity B]
  -- `X` is a *proper* subgroup of `A` and of `B`
  have hneA : X ≠ (A : Subgroup G) := by
    intro h
    have hle : (A : Subgroup G) ≤ (B : Subgroup G) := by
      rw [← h]; exact hXB
    exact hAB (Sylow.ext (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardAB.symm)))
  have hneB : X ≠ (B : Subgroup G) := by
    intro h
    have hle : (B : Subgroup G) ≤ (A : Subgroup G) := by
      rw [← h]; exact hXA
    exact hAB (Sylow.ext (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardAB))).symm
  -- normalizers grow inside the `p`-groups `A` and `B`
  have hlgrow : X < (A : Subgroup G) ⊓ N := by
    rw [hN]
    exact nnns_grow_normalizer hAp hXA hneA
  have hrgrow : X < (B : Subgroup G) ⊓ N := by
    rw [hN]
    exact nnns_grow_normalizer hBp hXB hneB
  -- the subgroups `A ⊓ N` and `B ⊓ N` are `p`-groups
  have hANp : IsPGroup p ↥((A : Subgroup G) ⊓ N) :=
    IsPGroup.of_equiv (G := ↥(((A : Subgroup G) ⊓ N).subgroupOf (A : Subgroup G)))
      (hAp.to_subgroup (((A : Subgroup G) ⊓ N).subgroupOf (A : Subgroup G)))
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : (A : Subgroup G) ⊓ N ≤ (A : Subgroup G)))
  have hBNp : IsPGroup p ↥((B : Subgroup G) ⊓ N) :=
    IsPGroup.of_equiv (G := ↥(((B : Subgroup G) ⊓ N).subgroupOf (B : Subgroup G)))
      (hBp.to_subgroup (((B : Subgroup G) ⊓ N).subgroupOf (B : Subgroup G)))
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : (B : Subgroup G) ⊓ N ≤ (B : Subgroup G)))
  -- ... hence they lie in the normal Sylow `p`-subgroup `P` of `N`
  have hMleP : (A : Subgroup G) ⊓ N ≤ P :=
    nnns_pgroup_le_normal_pgroup hPnorm hidx hPp _ inf_le_right hANp
  have hM'leP : (B : Subgroup G) ⊓ N ≤ P :=
    nnns_pgroup_le_normal_pgroup hPnorm hidx hPp _ inf_le_right hBNp
  -- extend `P` to a Sylow `p`-subgroup `U` of `G`
  obtain ⟨U, hPU⟩ := IsPGroup.exists_le_sylow hPp
  have hMleAU : (A : Subgroup G) ⊓ N ≤ (A : Subgroup G) ⊓ (U : Subgroup G) :=
    le_inf inf_le_left (hMleP.trans hPU)
  have hM'leBU : (B : Subgroup G) ⊓ N ≤ (B : Subgroup G) ⊓ (U : Subgroup G) :=
    le_inf inf_le_left (hM'leP.trans hPU)
  -- `X ⊊ A ⊓ U`, which contradicts the maximality of `|X|` unless `U = A`
  have hcard_lt : Nat.card ↥X < Nat.card ↥((A : Subgroup G) ⊓ N) := by
    have hle : Nat.card ↥X ≤ Nat.card ↥((A : Subgroup G) ⊓ N) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion (le_of_lt hlgrow))
        (Subgroup.inclusion_injective _)
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge (le_of_lt hlgrow) (le_of_eq h.symm))
        (ne_of_lt hlgrow)
  have hcard_le : Nat.card ↥((A : Subgroup G) ⊓ N) ≤
      Nat.card ↥((A : Subgroup G) ⊓ (U : Subgroup G)) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hMleAU) (Subgroup.inclusion_injective _)
  have hAllt : Nat.card ↥X < Nat.card ↥((A : Subgroup G) ⊓ (U : Subgroup G)) :=
    lt_of_lt_of_le hcard_lt hcard_le
  have hUeqA : U = A := by
    by_contra hne
    have hle := hmax A U (fun h => hne h.symm)
    omega
  -- the same argument with `B` in place of `A` gives `U = B`
  have hcard_lt' : Nat.card ↥X < Nat.card ↥((B : Subgroup G) ⊓ N) := by
    have hle : Nat.card ↥X ≤ Nat.card ↥((B : Subgroup G) ⊓ N) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion (le_of_lt hrgrow))
        (Subgroup.inclusion_injective _)
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge (le_of_lt hrgrow) (le_of_eq h.symm))
        (ne_of_lt hrgrow)
  have hcard_le' : Nat.card ↥((B : Subgroup G) ⊓ N) ≤
      Nat.card ↥((B : Subgroup G) ⊓ (U : Subgroup G)) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hM'leBU) (Subgroup.inclusion_injective _)
  have hBlt : Nat.card ↥X < Nat.card ↥((B : Subgroup G) ⊓ (U : Subgroup G)) :=
    lt_of_lt_of_le hcard_lt' hcard_le'
  have hUeqB : U = B := by
    by_contra hne
    have hle := hmax B U (fun h => hne h.symm)
    omega
  exact hAB (hUeqA ▸ hUeqB)

end Work.BSW.S3
