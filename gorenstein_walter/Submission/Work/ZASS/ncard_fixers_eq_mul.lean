import Mathlib

namespace Work.ZASS

/-- **Double counting for fixed points of elements of a set.**

Let `G` act on a finite type `X`, let `Bset ⊆ G` and `Y ⊆ X`.  Assume

* every `g ∈ Bset`, `g ≠ 1`, fixes at most one point of `Y` (`h1`), and
* for every `x ∈ Y` exactly `c` nonidentity elements of `Bset` fix `x` (`h2`).

Then the number of nonidentity elements of `Bset` fixing some point of `Y` is `|Y| * c`.

Proof: count the set `{(g,x) : g ∈ Bset, g ≠ 1, x ∈ Y, g • x = x}` in the two possible ways.
Grouping by `x` gives `|Y| * c` by `h2` (the fibres are disjoint); grouping by `g` gives the
left-hand side, because `h1` says that no element is counted twice. -/
theorem ncard_fixers_eq_mul {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    (Bset : Set G) (Y : Set X) {c : ℕ}
    (h1 : ∀ g : G, g ∈ Bset → g ≠ 1 →
      ({x : X | x ∈ Y ∧ g • x = x} : Set X).ncard ≤ 1)
    (h2 : ∀ x : X, x ∈ Y →
      ({g : G | g ∈ Bset ∧ g ≠ 1 ∧ g • x = x} : Set G).ncard = c) :
    ({g : G | g ∈ Bset ∧ g ≠ 1 ∧ ∃ x : X, x ∈ Y ∧ g • x = x} : Set G).ncard
      = Y.ncard * c := by
  classical
  set T : Y → Set G := fun x => {g : G | g ∈ Bset ∧ g ≠ 1 ∧ g • (x : X) = x} with hT
  have hUnion : ({g : G | g ∈ Bset ∧ g ≠ 1 ∧ ∃ x : X, x ∈ Y ∧ g • x = x} : Set G)
      = ⋃ x : Y, T x := by
    ext g
    constructor
    · rintro ⟨hb, hg1, x, hx, hgx⟩
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hb, hg1, hgx⟩
    · intro h
      obtain ⟨x, hb, hg1, hgx⟩ := Set.mem_iUnion.mp h
      exact ⟨hb, hg1, x, x.2, hgx⟩
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro x y hxy
    rw [Function.onFun, Set.disjoint_left]
    rintro g ⟨hb, hg1, hgx⟩ ⟨-, -, hgy⟩
    exact hxy (Subtype.ext ((Set.ncard_le_one (Set.toFinite _)).mp (h1 g hb hg1)
      (x : X) ⟨x.2, hgx⟩ (y : X) ⟨y.2, hgy⟩))
  rw [hUnion, Set.ncard_iUnion_of_finite (fun x => Set.toFinite _) hdisj]
  have hterm : ∀ x : Y, (T x).ncard = c := fun x => h2 (x : X) x.2
  haveI : Fintype Y := Fintype.ofFinite Y
  rw [finsum_eq_sum_of_fintype]
  simp only [hterm]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  congr 1
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

end Work.ZASS
