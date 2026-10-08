import Mathlib
import Submission.Work.ZassenhausTwoGroup.Feit35Aux
import Submission.Work.ZassenhausTwoGroup.Feit35Count

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Feit 1960, Lemma 3.5: the class count

Feit's Lemma 3.5 (*On a class of doubly transitive permutation groups*, Illinois J. Math. **4**
(1960), p. 182) is proved by counting conjugacy classes: it suffices to exhibit at least `q = |D|`
classes none of which meet `M = Q`, in which every element is a product of two involutions and
has order not dividing `2`.  The statement below is exactly that count in the rank-one
Zassenhaus setting (`H = Q ⋊ D`, `D = twoPoint H t`).

The argument (Feit's, made elementary by his footnote 9) counts ordered pairs `(u,v)` of
involutions of `G`, using that the involutions of `G` form a single conjugacy class
(`feit_lemma3_4`) and that each involution lies in exactly one conjugate of `Q`:

* with `I` the set of involutions, `i = |Inv(Q)|`, `Ω = G ⧸ H` and `c = |C_I(u₀)|` for an
  involution `u₀`, one has `|I| = |Ω| · i` (`feit35_invol_card`), `|G| = |Q| · q · |Ω|`
  (`feit35_card_G`) and `|I| · |C_G(u₀)| = |G|` (`feit35_invol_class_card`);
* pairs `(u,v) ∈ I × I` fall into: `uv = 1`, `uv` an involution (`|I|(c-1)` of them,
  `feit35_inv_product_pairs`), pairs with `u, v` in a common conjugate of `Q` (`|Ω| i²` of them,
  `feit35_same_conj_pairs`), and the rest, of which there are at least
  `|I|² - |Ω| i² - |I|(c-1) ≥ (q-1)|G| + |I|`;
* for a pair of the last kind, `x = u v` is nontrivial, not an involution, a product of two
  involutions, and — because `x ∈ Q^g` forces `u, v ∈ Q^g` (`feit35_product_mem_conj`) — not
  conjugate into `Q`: `x` satisfies the four conditions of the counted classes;
* the fibre of `(u,v) ↦ u v` over `x` has at most `|C_G(x)|` elements (`feit35_fiber_le`), and
  the centraliser orders sum to `|G|` on each class (`feit35_sum_centralizer_carrier`,
  `feit35_goodElem_sum`); hence the number of classes is at least
  `(|I|² - |Ω| i² - |I|(c-1)) / |G| > q - 1`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open scoped Classical

namespace Work.ZassenhausTwoGroup

theorem feit_lemma3_5_classes {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (H Q : Subgroup G) (t : G) (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hZ : Submission.Blueprint.IsZassenhaus H) (hQ2 : ¬ IsPGroup 2 Q) :
    Nat.card (Submission.Blueprint.twoPoint H t) ≤
      Nat.card {c : ConjClasses G // ∀ x ∈ c.carrier, x ≠ 1 ∧ orderOf x ≠ 2 ∧
        (∃ u v : G, orderOf u = 2 ∧ orderOf v = 2 ∧ x = u * v) ∧ ∀ g : G, g * x * g⁻¹ ∉ Q} := by
  classical
  obtain ⟨u₀, hu₀, -⟩ := feit_lemma3_4 H Q t h
  set q : ℕ := Nat.card (Submission.Blueprint.twoPoint H t) with hq
  set o : ℕ := Nat.card (G ⧸ H) with ho
  set m : ℕ := Nat.card Q with hm
  set i : ℕ := (invFinsetQ Q).card with hi_def
  set n : ℕ := (invFinset G).card with hn_def
  set c : ℕ := (centralizerInvols u₀).card with hc_def
  -- basic numerical facts
  have ho1 : o = m + 1 := by rw [ho, hm]; exact card_quotient_eq h
  have hG : Nat.card G = m * q * o := by rw [hm, hq, ho]; exact feit35_card_G h
  have hn : n = o * i := by
    rw [hn_def, hi_def]; rw [feit35_invol_card h hZ hQ2, ho]
  have hi : q ≤ i := by rw [hq, hi_def]; exact feit35_card_twoPoint_le h hZ
  have hnpos : 1 ≤ n := by
    rw [hn_def]
    exact Finset.card_pos.mpr ⟨u₀, by
      rw [invFinset, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hu₀⟩⟩
  have hnG : n ≤ Nat.card G := by
    rw [hn_def, Nat.card_eq_fintype_card]
    exact le_trans (Finset.card_filter_le _ _) (le_of_eq Finset.card_univ)
  have hclass : n * Nat.card (Subgroup.centralizer ({u₀} : Set G)) = Nat.card G := by
    rw [hn_def]; exact feit35_invol_class_card h hu₀
  have hdle : c ≤ Nat.card (Subgroup.centralizer ({u₀} : Set G)) - 1 := by
    rw [hc_def]
    have h1 : (1 : G) ∈ ((Subgroup.centralizer ({u₀} : Set G)) : Set G).toFinset := by
      rw [Set.mem_toFinset]; exact Subgroup.one_mem _
    have hsub : insert (1 : G) (centralizerInvols u₀) ⊆
        ((Subgroup.centralizer ({u₀} : Set G)) : Set G).toFinset := by
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact h1
      · rw [centralizerInvols, Finset.mem_filter] at hx
        rw [Set.mem_toFinset]
        exact hx.2.2
    have h1not : (1 : G) ∉ centralizerInvols u₀ := by
      rw [centralizerInvols, Finset.mem_filter]
      rintro ⟨-, h1, -⟩
      rw [orderOf_one] at h1
      exact absurd h1 (by norm_num)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem h1not] at hcard
    have hC : ((Subgroup.centralizer ({u₀} : Set G)) : Set G).toFinset.card =
        Nat.card (Subgroup.centralizer ({u₀} : Set G)) := by
      rw [Set.toFinset_card, Nat.card_eq_fintype_card]
      rfl
    rw [hC] at hcard
    exact Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hcard)
  have hnc : n * c ≤ Nat.card G - n := by
    have h1 : n * c ≤ n * (Nat.card (Subgroup.centralizer ({u₀} : Set G)) - 1) :=
      Nat.mul_le_mul_left n hdle
    have h2 : n * (Nat.card (Subgroup.centralizer ({u₀} : Set G)) - 1) =
        Nat.card G - n := by
      rw [Nat.mul_sub_left_distrib, mul_one, hclass]
    exact h1.trans (le_of_eq h2)
  -- the pair sets
  set Y : Finset (G × G) := ((invFinset G) ×ˢ (invFinset G)).filter
    (fun p : G × G => ¬ ∃ g : G, p.1 ∈ Submission.Blueprint.conj g Q ∧
      p.2 ∈ Submission.Blueprint.conj g Q) with hY_def
  set Y2 : Finset (G × G) := Y.filter (fun p : G × G => orderOf (p.1 * p.2) = 2)
    with hY2_def
  set Z : Finset (G × G) := Y \ Y2 with hZ_def
  set B : ℕ := (sameConjPairs Q).card with hB_def
  set A : ℕ := (invProductPairs G).card with hA_def
  set Zc : ℕ := Z.card with hZc_def
  have hsplit1 : (invFinset G ×ˢ invFinset G).card = B + Y.card := by
    have hthis := Finset.card_filter_add_card_filter_not
      (s := (invFinset G) ×ˢ (invFinset G))
      (p := fun p : G × G => ∃ g : G, p.1 ∈ Submission.Blueprint.conj g Q ∧
        p.2 ∈ Submission.Blueprint.conj g Q)
    rw [hB_def, sameConjPairs, hY_def, ← hthis]
  have hsplit2 : Y.card = Z.card + Y2.card := by
    rw [hZ_def, hY2_def]
    exact (Finset.card_sdiff_add_card_eq_card
      (Finset.filter_subset _ _)).symm
  have hC_le_A : Y2.card ≤ A := by
    rw [hA_def, invProductPairs, hY2_def]
    refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
    intro p hp
    rw [hY_def, Finset.mem_filter] at hp
    exact hp.1
  have hZge : n ^ 2 ≤ Zc + B + A := by
    have h1 : n ^ 2 = B + Y.card := by
      rw [hn_def, show (invFinset G).card ^ 2 = (invFinset G ×ˢ invFinset G).card from by
        rw [Finset.card_product]; ring, hsplit1]
    rw [h1, hsplit2, hZc_def]
    have := hC_le_A
    omega
  have hB : B = o * i ^ 2 := by
    rw [hB_def, hi_def, feit35_same_conj_pairs h hZ hQ2, ho]
  have hA : A = n * (c - 1) := by
    rw [hA_def, hn_def, hc_def]; exact feit35_inv_product_pairs h hu₀
  have hAsub : A ≤ Nat.card G - n := by
    have hcn : c - 1 + 1 = c := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by
      rw [hc_def]
      exact Finset.card_ne_zero.mpr ⟨u₀, by
        rw [centralizerInvols, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hu₀, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩⟩))
    have h1 : A + n = n * c := by
      rw [hA, ← Nat.mul_succ, show (c - 1).succ = c from by rw [Nat.succ_eq_add_one, hcn]]
    omega
  -- the good elements of `Z`
  have hgoodZ : ∀ p ∈ Z, goodPred Q (p.1 * p.2) := by
    intro p hp
    rw [hZ_def, Finset.mem_sdiff] at hp
    obtain ⟨hpY, hpY2⟩ := hp
    have hpord : orderOf (p.1 * p.2) ≠ 2 := by
      intro h
      exact hpY2 (by rw [hY2_def, Finset.mem_filter]; exact ⟨hpY, h⟩)
    rw [hY_def, Finset.mem_filter, Finset.mem_product] at hpY
    obtain ⟨⟨hp1I, hp2I⟩, hpne⟩ := hpY
    have hp1_2 : orderOf p.1 = 2 := (Finset.mem_filter.mp hp1I).2
    have hp2_2 : orderOf p.2 = 2 := (Finset.mem_filter.mp hp2I).2
    have hne1 : p.1 * p.2 ≠ 1 := by
      intro h1
      obtain ⟨g, hg⟩ := involution_mem_conj_Q h hZ hp1_2
      apply hpne
      refine ⟨g, hg, ?_⟩
      have hp2eq : p.2 = p.1 := by
        have h2 : p.2 = p.1⁻¹ := by
          have h3 := congrArg (fun z : G => p.1⁻¹ * z) h1
          simpa [mul_assoc] using h3
        rw [h2]
        exact inv_eq_of_mul_eq_one_right (by
          have h3 := pow_orderOf_eq_one p.1; rwa [hp1_2, pow_two] at h3)
      rw [hp2eq]; exact hg
    refine ⟨hne1, hpord, ⟨p.1, p.2, hp1_2, hp2_2, rfl⟩, ?_⟩
    intro g hgQ
    have hmem : p.1 * p.2 ∈ Submission.Blueprint.conj g⁻¹ Q := by
      rw [Submission.Blueprint.conj, Subgroup.mem_map]
      exact ⟨g * (p.1 * p.2) * g⁻¹, hgQ, by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    obtain ⟨h1, h2⟩ := feit35_product_mem_conj h hZ hQ2 hp1_2 hp2_2 hne1 hmem
    exact hpne ⟨g⁻¹, h1, h2⟩
  -- the fibre bound
  have hZle : Zc ≤ (goodClasses Q).card * Nat.card G := by
    rw [hZc_def]
    have hmap : Set.MapsTo (fun p : G × G => p.1 * p.2) (↑Z : Set (G × G))
        (↑(goodElem Q) : Set G) := by
      intro p hp
      rw [Finset.mem_coe] at hp ⊢
      rw [goodElem, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hgoodZ p hp⟩
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    have hle : ∀ x ∈ goodElem Q,
        (Z.filter (fun p : G × G => p.1 * p.2 = x)).card ≤
          Nat.card (Subgroup.centralizer ({x} : Set G)) := by
      intro x _
      have hsub : Z.filter (fun p : G × G => p.1 * p.2 = x) ⊆ prodFiberPairs G x := by
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpZ, hpx⟩ := hp
        rw [hZ_def, Finset.mem_sdiff, hY_def, Finset.mem_filter, Finset.mem_product] at hpZ
        rw [prodFiberPairs, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hpZ.1.1.1, hpZ.1.1.2⟩, hpx⟩
      exact (Finset.card_le_card hsub).trans (feit35_fiber_le x)
    exact (Finset.sum_le_sum hle).trans (le_of_eq (feit35_goodElem_sum Q))
  -- the arithmetic
  have hF3 : q * Nat.card G + o * i ^ 2 ≤ n ^ 2 := by
    rw [hn, hG, ho1]
    have hii : q ^ 2 ≤ i ^ 2 := Nat.pow_le_pow_left hi 2
    have key : (q : ℤ) * ((m : ℤ) * q * ((m : ℤ) + 1)) + ((m : ℤ) + 1) * (i : ℤ) ^ 2 ≤
        (((m : ℤ) + 1) * (i : ℤ)) ^ 2 := by
      have hii' : (q : ℤ) ^ 2 ≤ (i : ℤ) ^ 2 := by exact_mod_cast hii
      have hfac : (q : ℤ) * ((m : ℤ) * q * ((m : ℤ) + 1)) + ((m : ℤ) + 1) * (i : ℤ) ^ 2 =
          (((m : ℤ) + 1) * (i : ℤ)) ^ 2 -
            (m : ℤ) * ((m : ℤ) + 1) * ((i : ℤ) ^ 2 - (q : ℤ) ^ 2) := by ring
      have hnonneg : (0 : ℤ) ≤ (m : ℤ) * ((m : ℤ) + 1) * ((i : ℤ) ^ 2 - (q : ℤ) ^ 2) := by
        refine mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (by linarith)) ?_
        linarith
      rw [hfac]
      linarith
    have hcast : ((q * (m * q * (m + 1)) + (m + 1) * i ^ 2 : ℕ) : ℤ) ≤
        ((((m + 1) * i) ^ 2 : ℕ) : ℤ) := by
      push_cast
      exact key
    exact Nat.cast_le.mp hcast
  have hZgt : (q - 1) * Nat.card G < Zc := by
    have hq1 : 1 ≤ q := by
      rw [hq]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr
        ⟨⟨⟨1, Subgroup.one_mem _⟩⟩, inferInstance⟩)
    have hqq : q - 1 + 1 = q := Nat.sub_add_cancel hq1
    have hqG : (q - 1) * Nat.card G + Nat.card G = q * Nat.card G :=
      calc (q - 1) * Nat.card G + Nat.card G = (q - 1 + 1) * Nat.card G := by
            rw [Nat.add_mul, one_mul]
        _ = q * Nat.card G := by rw [hqq]
    omega
  have hlt : (q - 1) * Nat.card G < (goodClasses Q).card * Nat.card G :=
    lt_of_lt_of_le hZgt hZle
  have hqk : q ≤ (goodClasses Q).card := by
    have h1 : q - 1 < (goodClasses Q).card := Nat.lt_of_mul_lt_mul_right hlt
    have h2 : 1 ≤ q := by
      rw [hq]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr
        ⟨⟨⟨1, Subgroup.one_mem _⟩⟩, inferInstance⟩)
    omega
  -- the goal
  have hKcard : Nat.card {c : ConjClasses G // ∀ x ∈ c.carrier, x ≠ 1 ∧ orderOf x ≠ 2 ∧
      (∃ u v : G, orderOf u = 2 ∧ orderOf v = 2 ∧ x = u * v) ∧
        ∀ g : G, g * x * g⁻¹ ∉ Q} = (goodClasses Q).card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe (goodClasses Q)]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun c => (mem_goodClasses Q c).symm))
  rw [hKcard, hq]
  exact hqk

end Work.ZassenhausTwoGroup
