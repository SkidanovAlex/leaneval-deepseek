import Mathlib
import Submission.Work.ProP.Defs
import Submission.Work.ProP.map_pCentralStep_of_surjective
import Submission.Work.ProP.card_quotient_lt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

open Work.Shrinking

universe u

/-! ## The abelian case

If `N` is a subgroup of `Q` contained in the centre (so that `N` is commutative) and
`N ^ p = N`, then `N` is trivial: the `p`-th power map is then a surjective endomorphism of the
finite `p`-group `N`, hence its iterates are surjective, so every element of `N` is a `p ^ e`-th
power where `p ^ e = Monoid.exponent N`; but every `p ^ e`-th power is `1`. -/

/-- A finite `p`-group `N` (a subgroup of `Q` lying in the centre of `Q`) with `N^p = N` is
trivial. -/
theorem powSubgroup_eq_self_eq_bot_of_le_center {p : ℕ} [Fact p.Prime] {Q : Type u} [Group Q]
    (N : Subgroup Q) [Finite ↥N] (hQ : IsPGroup p ↥N) (hZ : N ≤ Subgroup.center Q)
    (h : powSubgroup p N = N) : N = ⊥ := by
  -- `S` is the set of `p`-th powers of elements of `N`; it is a subgroup because `N` is abelian
  let S : Subgroup Q :=
    { carrier := {x | ∃ w : ↥N, (w : Q) ^ p = x}
      one_mem' := ⟨1, by simp⟩
      mul_mem' := by
        rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
        refine ⟨a * b, ?_⟩
        have hab : Commute ((a : Q)) ((b : Q)) :=
          (Subgroup.mem_center_iff.mp (hZ a.2) (b : Q)).symm
        rw [Subgroup.coe_mul, hab.mul_pow p]
      inv_mem' := by
        rintro x ⟨a, rfl⟩
        exact ⟨a⁻¹, by rw [Subgroup.coe_inv, inv_pow]⟩ }
  have hle : powSubgroup p N ≤ S := by
    rw [powSubgroup, Subgroup.closure_le]
    rintro x ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  -- `N = N^p ≤ S`: every element of `N` is a `p`-th power
  have hNS : N ≤ S := by rw [← h]; exact hle
  have hsurj : ∀ z : ↥N, ∃ w : ↥N, w ^ p = z := by
    intro z
    obtain ⟨w, hw⟩ := hNS z.2
    exact ⟨w, Subtype.ext (by simpa using hw)⟩
  -- hence every element is a `p ^ k`-th power, for every `k`
  have hiter : ∀ k : ℕ, ∀ z : ↥N, ∃ w : ↥N, w ^ (p ^ k) = z := by
    intro k
    induction k with
    | zero => intro z; exact ⟨z, by simp⟩
    | succ k ihk =>
      intro z
      obtain ⟨w, hw⟩ := hsurj z
      obtain ⟨v, hv⟩ := ihk w
      exact ⟨v, by rw [pow_succ, pow_mul, hv, hw]⟩
  obtain ⟨e, he⟩ := hQ.exists_exponent_eq_pow
  refine (Subgroup.eq_bot_iff_forall N).mpr ?_
  intro x hx
  obtain ⟨w, hw⟩ := hiter e ⟨x, hx⟩
  have h1 : w ^ (p ^ e) = 1 := by rw [← he]; exact Monoid.pow_exponent_eq_one w
  have h2 : (⟨x, hx⟩ : ↥N) = 1 := hw.symm.trans h1
  exact congrArg Subtype.val h2

/-! ## The minimal-counterexample induction -/

/-- The Nakayama property for finite `p`-groups, by strong induction on `Nat.card Q`. -/
private theorem pCentralStep_eq_self_aux (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∀ (Q : Type u) [Group Q] [Finite Q], Nat.card Q = n → IsPGroup p Q →
      ∀ (N : Subgroup Q) [N.Normal], pCentralStep p N = N → N = ⊥ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Q _ _ hcard hQ N _ hN
    by_cases hbot : N = ⊥
    · exact hbot
    -- `Q` is nontrivial, so its centre is nontrivial
    have hnt : Nontrivial Q := by
      obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
      refine ⟨a, 1, fun h => ha (Subtype.ext h)⟩
    have : Nontrivial Q := hnt
    have hZne : Subgroup.center Q ≠ ⊥ := ne_of_gt hQ.bot_lt_center
    by_cases hNZ : N ≤ Subgroup.center Q
    · -- `N` is central, hence commutative: the abelian case
      have hcomm : ⁅N, (⊤ : Subgroup Q)⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        simp only [Subgroup.coe_top, Subgroup.centralizer_univ]
        exact hNZ hx
      have hpc : powSubgroup p N = N := by
        simpa [pCentralStep, hcomm] using hN
      exact powSubgroup_eq_self_eq_bot_of_le_center N (hQ.to_subgroup N) hNZ hpc
    · -- `N` is not central; pass to a proper quotient of `Q`
      by_cases hW : N ⊓ Subgroup.center Q = ⊥
      · -- quotient by the centre
        have hcardlt : Nat.card (Q ⧸ Subgroup.center Q) < Nat.card Q :=
          card_quotient_lt (Subgroup.center Q) hZne
        have hQ' : IsPGroup p (Q ⧸ Subgroup.center Q) :=
          hQ.of_surjective (QuotientGroup.mk' (Subgroup.center Q))
            (QuotientGroup.mk'_surjective (Subgroup.center Q))
        let N' : Subgroup (Q ⧸ Subgroup.center Q) :=
          N.map (QuotientGroup.mk' (Subgroup.center Q))
        have hN'norm : N'.Normal :=
          Subgroup.Normal.map (inferInstance : N.Normal) (QuotientGroup.mk' (Subgroup.center Q))
            (QuotientGroup.mk'_surjective (Subgroup.center Q))
        have hN'map : pCentralStep p N' = N' := by
          have h1 := map_pCentralStep_of_surjective p (QuotientGroup.mk' (Subgroup.center Q))
            (QuotientGroup.mk'_surjective (Subgroup.center Q)) N
          rw [hN] at h1
          exact h1.symm
        have hN'ne : N' ≠ ⊥ := by
          intro h
          have h' : N.map (QuotientGroup.mk' (Subgroup.center Q)) = ⊥ := h
          rw [Subgroup.map_eq_bot_iff] at h'
          have hle : N ≤ Subgroup.center Q := by simpa [QuotientGroup.ker_mk'] using h'
          have : N ≤ N ⊓ Subgroup.center Q := le_inf le_rfl hle
          rw [hW] at this
          exact hbot (le_bot_iff.mp this)
        exact absurd (ih (Nat.card (Q ⧸ Subgroup.center Q)) (hcard ▸ hcardlt)
          (Q ⧸ Subgroup.center Q) rfl hQ' N' hN'map) hN'ne
      · -- quotient by `W = N ⊓ Z`; here `W ≠ ⊥` so the quotient is strictly smaller
        have hcardlt : Nat.card (Q ⧸ (N ⊓ Subgroup.center Q)) < Nat.card Q :=
          card_quotient_lt (N ⊓ Subgroup.center Q) hW
        have hQ' : IsPGroup p (Q ⧸ (N ⊓ Subgroup.center Q)) :=
          hQ.of_surjective (QuotientGroup.mk' (N ⊓ Subgroup.center Q))
            (QuotientGroup.mk'_surjective (N ⊓ Subgroup.center Q))
        let N' : Subgroup (Q ⧸ (N ⊓ Subgroup.center Q)) :=
          N.map (QuotientGroup.mk' (N ⊓ Subgroup.center Q))
        have hN'norm : N'.Normal :=
          Subgroup.Normal.map (inferInstance : N.Normal) (QuotientGroup.mk' (N ⊓ Subgroup.center Q))
            (QuotientGroup.mk'_surjective (N ⊓ Subgroup.center Q))
        have hN'map : pCentralStep p N' = N' := by
          have h1 := map_pCentralStep_of_surjective p (QuotientGroup.mk' (N ⊓ Subgroup.center Q))
            (QuotientGroup.mk'_surjective (N ⊓ Subgroup.center Q)) N
          rw [hN] at h1
          exact h1.symm
        have hN'ne : N' ≠ ⊥ := by
          intro h
          have h' : N.map (QuotientGroup.mk' (N ⊓ Subgroup.center Q)) = ⊥ := h
          rw [Subgroup.map_eq_bot_iff] at h'
          have hle : N ≤ N ⊓ Subgroup.center Q := by simpa [QuotientGroup.ker_mk'] using h'
          exact hNZ (hle.trans inf_le_right)
        exact absurd (ih (Nat.card (Q ⧸ (N ⊓ Subgroup.center Q))) (hcard ▸ hcardlt)
          (Q ⧸ (N ⊓ Subgroup.center Q)) rfl hQ' N' hN'map) hN'ne

/-- **Nakayama property for finite `p`-groups** (the strictness of the descending `p`-central
series). For a finite `p`-group `Q` and a normal subgroup `N ≤ Q`, `N^p ⁅N, Q⁆ = N` forces
`N = ⊥`.

Proof sketch (a minimal-counterexample argument; no Frattini theory is needed): strong induction
on `Nat.card Q`. Suppose `N ≠ ⊥` and `N^p ⊔ ⁅N, ⊤⁆ = N`; let `Z = Subgroup.center Q` (nontrivial
by `IsPGroup.bot_lt_center`, since `Q` is nontrivial) and `W = N ⊓ Z`.
* If `W = ⊥`: apply the induction hypothesis to `Q ⧸ Z` and `N.map (QuotientGroup.mk' Z)`. The
  hypothesis descends through the surjection because `Subgroup.map_sup`, the image of `powSubgroup`
  (`MonoidHom.map_closure`, `map_pow`) and `Subgroup.map_commutator` compute the `p`-central step
  of the image; `Nat.card (Q ⧸ Z) < Nat.card Q`; and the image is nontrivial since `N ⊓ Z = ⊥`
  with `N ≠ ⊥` forces `N.map (QuotientGroup.mk' Z) ≠ ⊥`.
* If `W ≠ ⊥` and `N ≠ W`: apply the induction hypothesis to `Q ⧸ W` and
  `N.map (QuotientGroup.mk' W)`, again nontrivial.
* If `N = W ≤ Z`: then `⁅N, ⊤⁆ = ⊥`, so `N = N^p`. Impossible for a nontrivial finite `p`-group:
  by `IsPGroup.exists_exponent_eq_pow`, `Monoid.exponent N = p ^ e` with `e ≥ 1`, and iterating
  `powSubgroup (p^i) N ≤ powSubgroup p (powSubgroup (p^{i-1}) N)` gives
  `N = powSubgroup (p^e) N ≤ ⊥` because every `x ^ (p^e) = 1`.

The reverse implication is immediate (`powSubgroup p ⊥ = ⊥` and `⁅⊥, ⊤⁆ = ⊥`). -/
theorem pCentralStep_eq_self_iff {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup p Q) (N : Subgroup Q) [N.Normal] :
    Work.Shrinking.pCentralStep p N = N ↔ N = ⊥ := by
  constructor
  · intro h
    exact pCentralStep_eq_self_aux p (Nat.card Q) Q rfl hQ N h
  · rintro rfl
    rw [pCentralStep, powSubgroup, Subgroup.commutator_bot_left, sup_bot_eq,
      Subgroup.closure_eq_bot_iff]
    rintro x ⟨y, hy, rfl⟩
    simp [Subgroup.mem_bot.mp hy]

end Work.ProP
