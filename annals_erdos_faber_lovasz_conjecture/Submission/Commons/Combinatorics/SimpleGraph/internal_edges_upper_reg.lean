import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Commons.Combinatorics.SimpleGraph

open Finset

/-- Row decomposition of the number of adjacent ordered pairs inside a product. -/
private lemma card_filter_prod {α : Type*} (s t : Finset α) (r : α → α → Prop) [DecidableRel r] :
    ((s.product t).filter (fun p => r p.1 p.2)).card = ∑ x ∈ s, (t.filter (r x)).card := by
  classical
  rw [Finset.card_filter]
  rw [show (∑ i ∈ s.product t, (if r i.1 i.2 then (1 : ℕ) else 0))
        = ∑ x ∈ s, ∑ y ∈ t, (if r x y then 1 else 0) from Finset.sum_product s t _]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.card_filter]

/-- Split the adjacent ordered pairs of `s ∪ t` into the four blocks. -/
private lemma card_filter_prod_union {α : Type*} [DecidableEq α] {s t : Finset α}
    (h : Disjoint s t) (r : α → α → Prop) [DecidableRel r] :
    (((s ∪ t).product (s ∪ t)).filter (fun p => r p.1 p.2)).card =
      ((s.product s).filter (fun p => r p.1 p.2)).card +
      ((s.product t).filter (fun p => r p.1 p.2)).card +
      ((t.product s).filter (fun p => r p.1 p.2)).card +
      ((t.product t).filter (fun p => r p.1 p.2)).card := by
  classical
  rw [card_filter_prod (s ∪ t) (s ∪ t) r]
  rw [Finset.sum_union h]
  have hsplit : ∀ x : α, ((s ∪ t).filter (r x)).card =
      (s.filter (r x)).card + (t.filter (r x)).card := by
    intro x
    rw [Finset.filter_union,
      Finset.card_union_of_disjoint
        (Disjoint.mono (Finset.filter_subset (r x) s) (Finset.filter_subset (r x) t) h)]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← card_filter_prod s s r, ← card_filter_prod s t r,
    ← card_filter_prod t s r, ← card_filter_prod t t r]
  ac_rfl

/-- If `G` is upper `(ρ,ξ)`-regular on `Fintype.card V` vertices (every pair of disjoint finsets
`S,T` with `ξN ≤ |S|`, `ξN ≤ |T|` spans at most `(ρ+ξ)|S||T|` edges, `N = Fintype.card V`), and
`0 ≤ ρ`, `0 ≤ ξ`, then for every finset `X` the number of ordered adjacent pairs inside `X` is at
most `(ρ+ξ)|X|(|X|-1) + 2ξN|X|`. -/
theorem internal_edges_upper_reg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {ρ ξ : ℝ}
    (hρ : 0 ≤ ρ) (hξ : 0 ≤ ξ)
    (hreg : ∀ S T : Finset V, Disjoint S T → ξ * (Fintype.card V : ℝ) ≤ (S.card : ℝ) →
      ξ * (Fintype.card V : ℝ) ≤ (T.card : ℝ) →
      (((S.product T).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
        (ρ + ξ) * (S.card : ℝ) * (T.card : ℝ))
    (X : Finset V) :
    (((X.product X).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
      (ρ + ξ) * (X.card : ℝ) * ((X.card : ℝ) - 1) +
        2 * ξ * (Fintype.card V : ℝ) * (X.card : ℝ) := by
  classical
  have hMN : 0 ≤ ξ * (Fintype.card V : ℝ) := mul_nonneg hξ (Nat.cast_nonneg _)
  have key : ∀ n : ℕ, ∀ Y : Finset V, Y.card = n →
      (((Y.product Y).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
        (ρ + ξ) * (Y.card : ℝ) * ((Y.card : ℝ) - 1) +
          2 * ξ * (Fintype.card V : ℝ) * (Y.card : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro Y hY
      by_cases hk : (Y.card : ℝ) ≤ 2 * (ξ * (Fintype.card V : ℝ)) + 1
      · -- Base case: the trivial `|X|(|X|-1)` bound suffices.
        by_cases hY0 : Y.card = 0
        · rw [Finset.card_eq_zero.mp hY0]
          simp
        · have hpos : 0 < Y.card := Nat.pos_of_ne_zero hY0
          have hsub : (Y.product Y).filter (fun p => G.Adj p.1 p.2) ⊆ Y.offDiag := by
            intro p hp
            rw [Finset.mem_filter] at hp
            obtain ⟨hpmem, hadj⟩ := hp
            obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpmem
            exact Finset.mem_offDiag.mpr ⟨hp1, hp2, G.ne_of_adj hadj⟩
          have hcardnat : ((Y.product Y).filter (fun p => G.Adj p.1 p.2)).card ≤
              Y.card * Y.card - Y.card := by
            calc ((Y.product Y).filter (fun p => G.Adj p.1 p.2)).card ≤ Y.offDiag.card :=
                  Finset.card_le_card hsub
              _ = Y.card * Y.card - Y.card := Finset.offDiag_card Y
          have hcardR : (((Y.product Y).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
              (Y.card : ℝ) * ((Y.card : ℝ) - 1) := by
            have h1 : (((Y.product Y).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
                ((Y.card * Y.card - Y.card : ℕ) : ℝ) := Nat.cast_le.mpr hcardnat
            have h2 : ((Y.card * Y.card - Y.card : ℕ) : ℝ) =
                (Y.card : ℝ) * ((Y.card : ℝ) - 1) := by
              rw [← Nat.mul_sub_one, Nat.cast_mul, Nat.cast_pred hpos]
            linarith [h1, h2.le]
          have hknn : 0 ≤ (Y.card : ℝ) * ((Y.card : ℝ) - 1) :=
            le_trans (Nat.cast_nonneg _) hcardR
          have hnlin : (Y.card : ℝ) * ((Y.card : ℝ) - 1) ≤
              2 * (ξ * (Fintype.card V : ℝ)) * (Y.card : ℝ) := by
            have h1 : (Y.card : ℝ) * ((Y.card : ℝ) - 1 - 2 * (ξ * (Fintype.card V : ℝ))) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith [hk])
            nlinarith [h1]
          have hextra : 0 ≤ (ρ + ξ) * (Y.card : ℝ) * ((Y.card : ℝ) - 1) := by
            nlinarith [mul_nonneg (add_nonneg hρ hξ) hknn]
          nlinarith [hcardR, hnlin, hextra]
      · -- Inductive step: split off a part of size `a = max 1 ⌈ξN⌉`.
        have hkgt : 2 * (ξ * (Fintype.card V : ℝ)) + 1 < (Y.card : ℝ) := not_le.mp hk
        have hYpos : 0 < Y.card := by
          have h0 : (0 : ℝ) < (Y.card : ℝ) := by linarith [hkgt, hMN]
          exact Nat.cast_pos.mp h0
        set a : ℕ := max 1 ⌈ξ * (Fintype.card V : ℝ)⌉₊ with ha
        have ha_ge : ξ * (Fintype.card V : ℝ) ≤ (a : ℝ) := by
          rw [ha]
          have h2 : (⌈ξ * (Fintype.card V : ℝ)⌉₊ : ℝ) ≤
              ((max 1 ⌈ξ * (Fintype.card V : ℝ)⌉₊ : ℕ) : ℝ) :=
            Nat.cast_le.mpr (le_max_right 1 (⌈ξ * (Fintype.card V : ℝ)⌉₊))
          linarith [Nat.le_ceil (ξ * (Fintype.card V : ℝ)), h2]
        have ha_le : (a : ℝ) ≤ ξ * (Fintype.card V : ℝ) + 1 := by
          rw [ha, Nat.cast_max]
          exact max_le (by push_cast; linarith [hMN]) (Nat.ceil_lt_add_one hMN).le
        have ha_pos : 1 ≤ a := by rw [ha]; exact le_max_left _ _
        have ha_lt : a < Y.card := by
          have hlt : (a : ℝ) < (Y.card : ℝ) := by linarith [ha_le, hkgt, hMN]
          exact Nat.cast_lt.mp hlt
        obtain ⟨A, hAY, hAcard⟩ :=
          Finset.exists_subset_card_eq (s := Y) (n := a) (le_of_lt ha_lt)
        set B : Finset V := Y \ A with hB
        have hBcard : B.card = Y.card - a := by
          rw [hB, Finset.card_sdiff_of_subset hAY, hAcard]
        have hBcardR : (B.card : ℝ) = (Y.card : ℝ) - (a : ℝ) := by
          rw [hBcard, Nat.cast_sub (le_of_lt ha_lt)]
        have hB_ge : ξ * (Fintype.card V : ℝ) ≤ (B.card : ℝ) := by
          rw [hBcardR]; linarith [ha_le, hkgt]
        have hdisj : Disjoint A B := by rw [hB]; exact Finset.disjoint_sdiff
        have hYAB : Y = A ∪ B := by
          rw [hB]; exact (Finset.union_sdiff_of_subset hAY).symm
        have ihA : (((A.product A).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
            (ρ + ξ) * (A.card : ℝ) * ((A.card : ℝ) - 1) +
              2 * ξ * (Fintype.card V : ℝ) * (A.card : ℝ) :=
          ih a (by rw [← hY]; exact ha_lt) A hAcard
        have hBlt : B.card < Y.card := by
          rw [hBcard]; exact Nat.sub_lt hYpos (by omega)
        have ihB : (((B.product B).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
            (ρ + ξ) * (B.card : ℝ) * ((B.card : ℝ) - 1) +
              2 * ξ * (Fintype.card V : ℝ) * (B.card : ℝ) :=
          ih B.card (by rw [← hY]; exact hBlt) B rfl
        have hAB : (((A.product B).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
            (ρ + ξ) * (A.card : ℝ) * (B.card : ℝ) :=
          hreg A B hdisj (by rw [hAcard]; exact ha_ge) hB_ge
        have hBA : (((B.product A).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
            (ρ + ξ) * (B.card : ℝ) * (A.card : ℝ) :=
          hreg B A hdisj.symm hB_ge (by rw [hAcard]; exact ha_ge)
        have hdec : (((Y.product Y).filter (fun p => G.Adj p.1 p.2)).card : ℝ) =
            (((A.product A).filter (fun p => G.Adj p.1 p.2)).card : ℝ) +
            (((A.product B).filter (fun p => G.Adj p.1 p.2)).card : ℝ) +
            (((B.product A).filter (fun p => G.Adj p.1 p.2)).card : ℝ) +
            (((B.product B).filter (fun p => G.Adj p.1 p.2)).card : ℝ) := by
          rw [hYAB, card_filter_prod_union hdisj G.Adj]
          push_cast
          ring
        have hbound : (((Y.product Y).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
            ((ρ + ξ) * (A.card : ℝ) * ((A.card : ℝ) - 1) +
                2 * ξ * (Fintype.card V : ℝ) * (A.card : ℝ)) +
            ((ρ + ξ) * (B.card : ℝ) * ((B.card : ℝ) - 1) +
                2 * ξ * (Fintype.card V : ℝ) * (B.card : ℝ)) +
            ((ρ + ξ) * (A.card : ℝ) * (B.card : ℝ)) +
            ((ρ + ξ) * (B.card : ℝ) * (A.card : ℝ)) := by
          rw [hdec]
          nlinarith [ihA, ihB, hAB, hBA]
        have hsumcard : (A.card : ℝ) + (B.card : ℝ) = (Y.card : ℝ) := by
          rw [hAcard, hBcardR]; ring
        have hSe : ((ρ + ξ) * (A.card : ℝ) * ((A.card : ℝ) - 1) +
                2 * ξ * (Fintype.card V : ℝ) * (A.card : ℝ)) +
            ((ρ + ξ) * (B.card : ℝ) * ((B.card : ℝ) - 1) +
                2 * ξ * (Fintype.card V : ℝ) * (B.card : ℝ)) +
            ((ρ + ξ) * (A.card : ℝ) * (B.card : ℝ)) +
            ((ρ + ξ) * (B.card : ℝ) * (A.card : ℝ)) =
            (ρ + ξ) * (Y.card : ℝ) * ((Y.card : ℝ) - 1) +
              2 * ξ * (Fintype.card V : ℝ) * (Y.card : ℝ) := by
          rw [← hsumcard]; ring
        linarith [hbound, hSe]
  exact key X.card X rfl

end Commons.Combinatorics.SimpleGraph