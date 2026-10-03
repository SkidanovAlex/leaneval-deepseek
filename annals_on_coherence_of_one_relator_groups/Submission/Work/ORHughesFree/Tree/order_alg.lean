import Mathlib
import Submission.Work.ORHughesFree.Tree.order_defs
import Submission.Work.ORHughesFree.Tree.order_le
import Submission.Work.ORHughesFree.Tree.order_good
import Submission.Work.ORHughesFree.Tree.fam_basic
import Submission.Work.ORHughesFree.Tree.fam_mul
import Submission.Work.ORHughesFree.Tree.mulMs_basic
import Submission.Work.ORHughesFree.Tree.lt_add_right
import Submission.Work.ORHughesFree.Tree.lt_mul_right
import Submission.Work.ORHughesFree.Tree.zero_mul
import Submission.Work.ORHughesFree.Tree.mul_zero

/-!
# Compatibility of the tree order with the semiring operations

We prove [JZLA20, Lemma 4.1]: the order is compatible with `+` and `*`, together with the
cancellation statements for the associated equalities.
-/

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-- `0` is the least tree. -/
theorem le_zero (x : Tree) : le (0 : Tree) x := by
  by_cases h : x = 0
  · exact Or.inl h.symm
  · refine Or.inr ?_
    rw [lt_iff_dmLT, fam_zero]
    exact ⟨0, 0, fam x, (ne_zero_iff_fam_ne_zero).mp h, rfl, rfl,
      fun a ha => absurd ha (by simp)⟩

/-- `0` is the least tree, so nothing is strictly below it. -/
theorem not_lt_zero {x : Tree} (h : lt x 0) : False :=
  lt_irrefl ((le_antisymm (le_of_lt h) (le_zero x)) ▸ h)

/-- Left strict monotonicity of the tree order. -/
theorem lt_add_left {a b c : Tree} (h : lt a b) : lt (c + a) (c + b) := by
  rw [lt_iff_dmLT] at h ⊢
  rw [fam_add, fam_add]
  obtain ⟨X, Y, Z, hZ, hM, hN, hYZ⟩ := h
  refine ⟨fam c + X, Y, Z, hZ, ?_, ?_, hYZ⟩
  · rw [hM, Multiset.add_assoc]
  · rw [hN, Multiset.add_assoc]

/-- `mulMs` is strictly monotone in its first argument. -/
theorem dmLT_mulMs_left {M N M'' : Multiset Tree} (hM'' : M'' ≠ 0) (h : dmLT lt M N) :
    dmLT lt (mulMs M'' M) (mulMs M'' N) := by
  obtain ⟨X, Y, Z, hZ, rfl, rfl, hYZ⟩ := h
  refine ⟨mulMs M'' X, mulMs M'' Y, mulMs M'' Z, ?_, ?_, ?_, ?_⟩
  · rw [mulMs_ne_zero]; exact ⟨hM'', hZ⟩
  · rw [mulMs_add_right]
  · rw [mulMs_add_right]
  · intro t ht
    obtain ⟨m, hm, y, hy, rfl⟩ := mem_mulMs.mp ht
    obtain ⟨z, hz, hyz⟩ := hYZ y hy
    exact ⟨m + z, mem_mulMs.mpr ⟨m, hm, z, hz, rfl⟩, lt_add_left hyz⟩

/-- Left strict monotonicity of the product. -/
theorem lt_mul_left {a b : Tree} (h : lt a b) {c : Tree} (hc : c ≠ 0) :
    lt (c * a) (c * b) := by
  rw [lt_iff_dmLT] at h ⊢
  rw [fam_mul, fam_mul]
  exact dmLT_mulMs_left (ne_zero_iff_fam_ne_zero.mp hc) h

/-- Composition of two strict Dershowitz–Manna inequalities. -/
theorem dmLT_trans_lt {A B C : Multiset Tree} (h1 : dmLT lt A B) (h2 : dmLT lt B C) :
    dmLT lt A C :=
  dmLT_trans (fun a _ b _ c _ hab hbc => lt_trans hab hbc) h1 h2

/-- The Dershowitz–Manna order is irreflexive. -/
theorem dmLT_irrefl' {M : Multiset Tree} : ¬ dmLT lt M M :=
  dmLT_irrefl (fun a _ b _ => lt_trichotomy a b)
    (fun a _ b _ c _ hab hbc => lt_trans hab hbc) (fun a _ => lt_irrefl)

/-- A strict Dershowitz–Manna inequality is a genuine inequality. -/
theorem dmLT_ne {A B : Multiset Tree} (h : dmLT lt A B) : A ≠ B := by
  intro he
  rw [he] at h
  exact dmLT_irrefl' h

/-- The right-hand side of a strict inequality is nonzero. -/
theorem dmLT_ne_zero_right {A B : Multiset Tree} (h : dmLT lt A B) : B ≠ 0 := by
  intro h0
  obtain ⟨X, Y, Z, hZ, -, hB, -⟩ := h
  obtain ⟨z, hz⟩ := Multiset.exists_mem_of_ne_zero hZ
  have hmem : z ∈ B := by rw [hB]; exact Multiset.mem_add.mpr (Or.inr hz)
  rw [h0] at hmem
  exact absurd hmem (by simp)

/-- Cancellation for `mulMs`: from `M ⊗ N = M' ⊗ N'` with `M ≤ M'`, `N ≤ N'` (all nonzero on the
left) we get `M = M'` and `N = N'`. -/
theorem mulMs_cancel {M M' N N' : Multiset Tree}
    (hM : M = M' ∨ dmLT lt M M') (hN : N = N' ∨ dmLT lt N N')
    (hM0 : M ≠ 0) (hN0 : N ≠ 0) (heq : mulMs M N = mulMs M' N') :
    M = M' ∧ N = N' := by
  have hMM' : M = M' := by
    by_contra hne
    have hlt : dmLT lt M M' := hM.resolve_left hne
    have hM'0 : M' ≠ 0 := dmLT_ne_zero_right hlt
    have h1 : dmLT lt (mulMs M N) (mulMs M' N) := dmLT_mulMs_right hlt hN0
    have h2 : mulMs M' N = mulMs M' N' ∨ dmLT lt (mulMs M' N) (mulMs M' N') := by
      rcases hN with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (dmLT_mulMs_left hM'0 h)
    have h3 : dmLT lt (mulMs M N) (mulMs M' N') := by
      rcases h2 with h | h
      · rw [← h]; exact h1
      · exact dmLT_trans_lt h1 h
    rw [heq] at h3
    exact dmLT_irrefl' h3
  have hNN' : N = N' := by
    by_contra hne
    have hlt : dmLT lt N N' := hN.resolve_left hne
    have hN'0 : N' ≠ 0 := dmLT_ne_zero_right hlt
    have h1 : dmLT lt (mulMs M N) (mulMs M N') := dmLT_mulMs_left hM0 hlt
    have h2 : mulMs M N' = mulMs M' N' ∨ dmLT lt (mulMs M N') (mulMs M' N') := by
      rcases hM with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (dmLT_mulMs_right h hN'0)
    have h3 : dmLT lt (mulMs M N) (mulMs M' N') := by
      rcases h2 with h | h
      · rw [← h]; exact h1
      · exact dmLT_trans_lt h1 h
    rw [heq] at h3
    exact dmLT_irrefl' h3
  exact ⟨hMM', hNN'⟩

/-- [JZLA20, Lemma 4.1(i)]: `+` is monotone. -/
theorem le_add {a b c d : Tree} (hab : le a b) (hcd : le c d) : le (a + c) (b + d) := by
  rcases hab with hab | hab
  · rcases hcd with hcd | hcd
    · exact Or.inl (by rw [hab, hcd])
    · exact Or.inr (by rw [hab]; exact lt_add_left (c := b) hcd)
  rcases hcd with hcd | hcd
  · rw [← hcd]; exact Or.inr (lt_add_right hab c)
  · exact Or.inr (lt_trans (lt_add_right hab c) (lt_add_left (c := b) hcd))

/-- [JZLA20, Lemma 4.1(i)]: `+` is strictly cancellative over a monotone pair. -/
theorem le_add_eq {a b c d : Tree} (hab : le a b) (hcd : le c d) :
    (a + c = b + d ↔ a = b ∧ c = d) := by
  constructor
  · intro heq
    have hab' : a = b := by
      by_contra hne
      have hlt : lt a b := lt_of_le_of_ne hab hne
      have h1 : lt (a + c) (b + c) := lt_add_right hlt c
      have h2 : le (b + c) (b + d) := le_add (le_refl b) hcd
      have h3 : lt (a + c) (b + d) := by
        rcases h2 with h2 | h2
        · rw [← h2]; exact h1
        · exact lt_trans h1 h2
      rw [heq] at h3
      exact lt_irrefl h3
    have hcd' : c = d := by
      by_contra hne
      have hlt : lt c d := lt_of_le_of_ne hcd hne
      have hlt' : lt (a + c) (a + d) := lt_add_left (c := a) hlt
      rw [← hab'] at heq
      rw [heq] at hlt'
      exact lt_irrefl hlt'
    exact ⟨hab', hcd'⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- [JZLA20, Lemma 4.1(ii)]: `*` is monotone. -/
theorem le_mul {a b c d : Tree} (hab : le a b) (hcd : le c d) : le (a * c) (b * d) := by
  rcases hab with hab | hab
  · rcases hcd with hcd | hcd
    · exact Or.inl (by rw [hab, hcd])
    · by_cases ha0 : a = 0
      · exact Or.inl (by rw [← hab, ha0, zero_mul, zero_mul])
      · exact Or.inr (by rw [← hab]; exact lt_mul_left hcd ha0)
  rcases hcd with hcd | hcd
  · by_cases hc0 : c = 0
    · exact Or.inl (by rw [← hcd, hc0, mul_zero, mul_zero])
    · exact Or.inr (by rw [← hcd]; exact lt_mul_right hab hc0)
  · by_cases hc0 : c = 0
    · rw [hc0, mul_zero]
      exact le_zero _
    · have hb0 : b ≠ 0 := fun hb0 => not_lt_zero (hb0 ▸ hab)
      exact Or.inr (lt_trans (lt_mul_right hab hc0) (lt_mul_left hcd hb0))

/-- [JZLA20, Lemma 4.1(ii)]: `*` is strictly cancellative over a monotone pair of nonzero
trees. -/
theorem le_mul_eq {a b c d : Tree} (ha : a ≠ 0) (hc : c ≠ 0)
    (hab : le a b) (hcd : le c d) : (a * c = b * d ↔ a = b ∧ c = d) := by
  constructor
  · intro heq
    have hM : fam a = fam b ∨ dmLT lt (fam a) (fam b) := by
      rcases hab with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr ((lt_iff_dmLT a b).mp h)
    have hN : fam c = fam d ∨ dmLT lt (fam c) (fam d) := by
      rcases hcd with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr ((lt_iff_dmLT c d).mp h)
    have hM0 : fam a ≠ 0 := (ne_zero_iff_fam_ne_zero).mp ha
    have hN0 : fam c ≠ 0 := (ne_zero_iff_fam_ne_zero).mp hc
    have heqm : mulMs (fam a) (fam c) = mulMs (fam b) (fam d) := by
      have h := congrArg fam heq
      rwa [fam_mul, fam_mul] at h
    obtain ⟨h1, h2⟩ := mulMs_cancel hM hN hM0 hN0 heqm
    exact ⟨fam_injective h1, fam_injective h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end Work.ORHughesFree.Tree
