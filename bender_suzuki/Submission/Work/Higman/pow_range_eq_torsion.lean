import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

theorem pow_range_eq_torsion {A : Type} [CommGroup A] [Finite A] {e : ℕ}
    (hexp : ∀ a : A, a ^ 2 ^ e = 1)
    (hT : ∀ j ≤ e, Nat.card {x : A | x ^ 2 ^ j = 1} = (Nat.card {x : A | x ^ 2 = 1}) ^ j)
    (hA : Nat.card A = (Nat.card {x : A | x ^ 2 = 1}) ^ e) :
    ∀ k ≤ e, ∀ y : A, (∃ x : A, x ^ 2 ^ k = y) ↔ y ^ 2 ^ (e - k) = 1 := by
  intro k hk y
  -- `N` is the 2-torsion order; hypotheses force `|A| = N^e` and `|A[2^k]| = N^k`,
  -- so the image of `x ↦ x^{2^k}` has size `N^(e-k)`, equal to that of `A[2^(e-k)]`.
  set N := Nat.card {x : A | x ^ 2 = 1} with hN
  have hNpos : 0 < N := by
    rw [hN]
    have : Nonempty {x : A | x ^ 2 = 1} := ⟨⟨1, by simp⟩⟩
    exact Nat.card_pos
  have hNkpos : 0 < N ^ k := pow_pos hNpos k
  -- first isomorphism theorem: `|ker| * |range| = |A|` for `powMonoidHom (2^k)`.
  have hcard : Nat.card ↥((powMonoidHom (α:=A) (2^k)).ker) *
      Nat.card ↥((powMonoidHom (α:=A) (2^k)).range) = Nat.card A := by
    have h := Subgroup.card_mul_index (powMonoidHom (α:=A) (2^k)).ker
    rw [Subgroup.index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (powMonoidHom (α:=A) (2^k))).toEquiv] at h
    exact h
  have hker : Nat.card ↥((powMonoidHom (α:=A) (2^k)).ker) = N ^ k := by
    rw [hN]; exact hT k hk
  have hA' : Nat.card A = N ^ e := by rw [hN]; exact hA
  have hpk : N ^ k * N ^ (e - k) = N ^ e := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  -- the range has cardinality `N^(e-k)`.
  have hrange : Nat.card ↥((powMonoidHom (α:=A) (2^k)).range) = N ^ (e - k) := by
    rw [hker, hA', ← hpk] at hcard
    exact Nat.mul_left_cancel hNkpos hcard
  have hTeq : Nat.card ↥((powMonoidHom (α:=A) (2^(e-k))).ker) = N ^ (e - k) := by
    rw [hN]; exact hT (e - k) (Nat.sub_le e k)
  -- the range lies in the `2^(e-k)`-torsion subgroup.
  have hle : (powMonoidHom (α:=A) (2^k)).range ≤ (powMonoidHom (α:=A) (2^(e-k))).ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    rw [MonoidHom.mem_range] at hz
    obtain ⟨x, rfl⟩ := hz
    change (x ^ 2 ^ k) ^ 2 ^ (e - k) = 1
    have h2 : 2 ^ k * 2 ^ (e - k) = 2 ^ e := by
      rw [← pow_add, Nat.add_sub_cancel' hk]
    rw [← pow_mul, h2]
    exact hexp x
  -- equality of subgroups, since the cardinalities agree.
  have heq : (powMonoidHom (α:=A) (2^k)).range = (powMonoidHom (α:=A) (2^(e-k))).ker := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hTeq, hrange]
  constructor
  · rintro ⟨x, hx⟩
    have hy : y ∈ (powMonoidHom (α:=A) (2^k)).range := by
      rw [MonoidHom.mem_range]; exact ⟨x, hx⟩
    rw [heq, MonoidHom.mem_ker] at hy
    exact hy
  · intro hy
    have hy' : y ∈ (powMonoidHom (α:=A) (2^(e-k))).ker := by
      rw [MonoidHom.mem_ker]; exact hy
    rw [← heq, MonoidHom.mem_range] at hy'
    exact hy'

end Work.Higman
