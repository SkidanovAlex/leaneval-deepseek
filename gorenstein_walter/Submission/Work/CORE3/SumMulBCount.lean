import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic

set_option linter.style.haveILetI false

namespace Work.CORE3

open Work.GW2

/-! ## Counting bridge lemmas

The identity below compares two ways of counting involutions: a `Finset` sum and a
`Set.ncard`.  We need three elementary tool lemmas. -/

/-- A set-builder `ncard` in a finite type is a `Finset.filter`-cardinality. -/
private lemma ncard_eq_filter_card {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] :
    ({x : α | p x} : Set α).ncard = (Finset.univ.filter p).card := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

/-- Splitting a conjunctive filter into two successive filters (as a cardinality identity, so
that the two `DecidablePred` instances never have to be syntactically equal). -/
private lemma card_filter_and {α : Type} [Fintype α] (p q : α → Prop) [DecidablePred p]
    [DecidablePred q] :
    (Finset.univ.filter (fun a => p a ∧ q a)).card = ((Finset.univ.filter p).filter q).card := by
  apply Finset.card_bij (fun a _ => a)
  · intro a ha
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha
  · intro a b _ _ h; exact h
  · intro b hb
    exact ⟨b, by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hb, rfl⟩

/-- Membership in a left coset `c` of `Hh`, read through the chosen representative
`Quotient.out c`. -/
private lemma mk_eq_iff {G : Type} [Group G] (Hh : Subgroup G) (c : G ⧸ Hh) (x : G) :
    QuotientGroup.mk x = c ↔ (Quotient.out c)⁻¹ * x ∈ Hh := by
  conv_lhs => rw [← Quotient.out_eq c]
  rw [eq_comm, QuotientGroup.eq]

/-- The trivial coset is exactly `Hh`. -/
private lemma mk_eq_one_iff {G : Type} [Group G] (Hh : Subgroup G) (x : G) :
    QuotientGroup.mk x = ((1 : G) : G ⧸ Hh) ↔ x ∈ Hh := by
  rw [QuotientGroup.eq]; simp

/-- Combinatorial identity behind Bender 1981 §3 (2): summing `n * b_n` over all `n` counts the
involutions outside `Hh` (each involution of `G` lies in exactly one coset of `Hh`; those in
`Hh` are in the trivial coset, and `bCount` only counts nontrivial cosets).  Used to derive
`|J| = |J ∩ Ĥ| + Σ n b_n`. -/
theorem SumMulBCount (G : Type) [Group G] [Finite G] (Hh : Subgroup G) :
    ∑ n ∈ Finset.range (Nat.card Hh + 1), n * bCount Hh n =
      {x : G | orderOf x = 2 ∧ x ∉ Hh}.ncard := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (G ⧸ Hh) := Fintype.ofFinite (G ⧸ Hh)
  -- The number of involutions of a nontrivial coset `c` is `cosetInvCount Hh (Quotient.out c)`.
  have hfiber : ∀ c : G ⧸ Hh, c ≠ ((1 : G) : G ⧸ Hh) →
      ((Finset.univ.filter (fun x : G => orderOf x = 2 ∧ x ∉ Hh)).filter
          (fun x => QuotientGroup.mk x = c)).card = cosetInvCount Hh (Quotient.out c) := by
    intro c hc
    rw [← card_filter_and (fun x : G => orderOf x = 2 ∧ x ∉ Hh)
      (fun x => QuotientGroup.mk x = c)]
    rw [← ncard_eq_filter_card
      (fun x : G => (orderOf x = 2 ∧ x ∉ Hh) ∧ QuotientGroup.mk x = c)]
    -- `x ∉ Hh` is automatic once `x` lies in the nontrivial coset `c`.
    have h1 : ({x : G | (orderOf x = 2 ∧ x ∉ Hh) ∧ QuotientGroup.mk x = c} : Set G)
        = {x : G | orderOf x = 2 ∧ QuotientGroup.mk x = c} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨h2, -⟩, hmk⟩; exact ⟨h2, hmk⟩
      · rintro ⟨h2, hmk⟩
        exact ⟨⟨h2, fun hmem => hc (hmk.symm.trans ((mk_eq_one_iff Hh x).mpr hmem))⟩, hmk⟩
    have h2 : ({x : G | orderOf x = 2 ∧ QuotientGroup.mk x = c} : Set G)
        = {x : G | orderOf x = 2 ∧ (Quotient.out c)⁻¹ * x ∈ Hh} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      rw [mk_eq_iff]
    rw [h1, h2]
    rfl
  -- The involutions outside `Hh` are the disjoint union of the involutions of the nontrivial
  -- cosets.
  have hB : ({x : G | orderOf x = 2 ∧ x ∉ Hh} : Set G).ncard =
      ∑ c ∈ Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh)),
        cosetInvCount Hh (Quotient.out c) := by
    rw [ncard_eq_filter_card (fun x : G => orderOf x = 2 ∧ x ∉ Hh)]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x : G => QuotientGroup.mk x)
        (t := Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh))) ?hm]
    · apply Finset.sum_congr rfl
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      exact hfiber c hc
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact fun hcontra => hx.2 ((mk_eq_one_iff Hh x).mp hcontra)
  -- The left-hand side is the same sum, grouped by the number of involutions in a coset.
  have hC : (∑ n ∈ Finset.range (Nat.card Hh + 1), n * bCount Hh n) =
      ∑ c ∈ Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh)),
        cosetInvCount Hh (Quotient.out c) := by
    have hb : ∀ n, bCount Hh n =
        ((Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh))).filter
          (fun c => cosetInvCount Hh (Quotient.out c) = n)).card := by
      intro n
      calc bCount Hh n
          = ({c : G ⧸ Hh | c ≠ ((1 : G) : G ⧸ Hh) ∧
              cosetInvCount Hh (Quotient.out c) = n} : Set (G ⧸ Hh)).ncard := rfl
        _ = (Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh) ∧
              cosetInvCount Hh (Quotient.out c) = n)).card := ncard_eq_filter_card _
        _ = ((Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh))).filter
              (fun c => cosetInvCount Hh (Quotient.out c) = n)).card := card_filter_and _ _
    have hmap2 : ∀ c ∈ Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh)),
        cosetInvCount Hh (Quotient.out c) ∈ Finset.range (Nat.card Hh + 1) := by
      intro c _
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Work.CORE2A.cosetInvCount_le Hh (Quotient.out c))
    calc ∑ n ∈ Finset.range (Nat.card Hh + 1), n * bCount Hh n
        = ∑ n ∈ Finset.range (Nat.card Hh + 1),
            ∑ c ∈ (Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh))).filter
                (fun c => cosetInvCount Hh (Quotient.out c) = n),
              cosetInvCount Hh (Quotient.out c) := by
          apply Finset.sum_congr rfl
          intro n _
          rw [hb n]
          rw [Finset.sum_congr rfl (fun c hc => (Finset.mem_filter.mp hc).2)]
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ = ∑ c ∈ Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh)),
            cosetInvCount Hh (Quotient.out c) :=
          Finset.sum_fiberwise_of_maps_to hmap2 _
  rw [hC, hB]

end Work.CORE3
