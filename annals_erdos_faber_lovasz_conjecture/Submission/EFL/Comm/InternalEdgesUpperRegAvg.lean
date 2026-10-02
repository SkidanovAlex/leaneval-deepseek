import Submission.Commons.Combinatorics.SimpleGraph.internal_edges_upper_reg
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.Order.Star.Real

/-!
# A port of `Commons.Combinatorics.SimpleGraph.internal_edges_upper_reg_avg`

Identical to the shared-commons file of the same name, re-elaborated against
*minimal* Mathlib imports so that it can be imported by the `Submission`
library (the commons file starts with the whole of Mathlib, which exports
`_root_.Hypergraph` and would make the fixed `Solution.lean` ambiguous).
-/


namespace Commons.Combinatorics.SimpleGraph

open Finset

private lemma choose_mul_choose (n m : ℕ) (hm : 1 ≤ m) :
    n.choose m * (m * (n - m)) = n * (n - 1) * ((n - 2).choose (m - 1)) := by
  have h1 : n.choose m * (n - m) = n * ((n - 1).choose m) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have h := Nat.choose_mul_succ_eq (n - 1) m
      rw [Nat.sub_add_cancel hn] at h
      rw [← h]; ring
  have h2 : (n - 1).choose m * m = (n - 1) * ((n - 2).choose (m - 1)) := by
    have h := Nat.choose_mul (n := n - 1) (k := m) (s := 1) hm
    rw [Nat.choose_one_right, Nat.choose_one_right] at h
    rw [h]
    congr 1
  calc n.choose m * (m * (n - m))
      = (n.choose m * (n - m)) * m := by ring
    _ = (n * ((n - 1).choose m)) * m := by rw [h1]
    _ = n * (((n - 1).choose m) * m) := by ring
    _ = n * ((n - 1) * ((n - 2).choose (m - 1))) := by rw [h2]
    _ = n * (n - 1) * ((n - 2).choose (m - 1)) := by ring

private lemma count_lemma {α : Type*} [DecidableEq α]
    (X : Finset α) (m : ℕ) (r : α → α → Prop) [DecidableRel r] (hirr : ∀ a, ¬ r a a) :
    ((X.powersetCard (m + 1)).sum
        (fun S => ((S ×ˢ (X \ S)).filter (fun p => r p.1 p.2)).card))
      = ((X ×ˢ X).filter (fun p => r p.1 p.2)).card * ((X.card - 2).choose m) := by
  classical
  set Q : Finset (α × α) := (X ×ˢ X).filter (fun p => r p.1 p.2) with hQ
  set R : Finset (Σ _ : α × α, Finset α) :=
    Q.sigma (fun p => (X \ {p.1, p.2}).powersetCard m) with hR
  let i : (Σ _ : Finset α, α × α) → (Σ _ : α × α, Finset α) :=
    fun a => ⟨a.2, a.1.erase a.2.1⟩
  have hcard :
      (((X.powersetCard (m + 1)).sigma (fun S => (S ×ˢ (X \ S)).filter (fun p => r p.1 p.2)))).card
        = R.card := by
    refine Finset.card_nbij i ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_coe] at ha
      rw [Finset.mem_sigma] at ha
      obtain ⟨haP, haS⟩ := ha
      rw [Finset.mem_powersetCard] at haP
      obtain ⟨hSX, hScard⟩ := haP
      rw [Finset.mem_filter, Finset.mem_product] at haS
      obtain ⟨⟨h1, h2⟩, hr⟩ := haS
      rw [hR, Finset.mem_coe, Finset.mem_sigma]
      change a.2 ∈ Q ∧ a.1.erase a.2.1 ∈ (X \ {a.2.1, a.2.2}).powersetCard m
      refine ⟨?_, ?_⟩
      · rw [hQ, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hSX h1, (Finset.mem_sdiff.mp h2).1⟩, hr⟩
      · rw [Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro x hx
          rw [Finset.mem_erase] at hx
          obtain ⟨hne, hmem⟩ := hx
          rw [Finset.mem_sdiff]
          refine ⟨hSX hmem, ?_⟩
          rw [Finset.mem_insert, Finset.mem_singleton]
          rintro (h | h)
          · exact hne h
          · subst h; exact (Finset.mem_sdiff.mp h2).2 hmem
        · rw [Finset.card_erase_of_mem h1, hScard]; omega
    · intro a ha b hb heq
      rw [Finset.mem_coe, Finset.mem_sigma] at ha
      rw [Finset.mem_coe, Finset.mem_sigma] at hb
      obtain ⟨haP, haS⟩ := ha
      obtain ⟨hbP, hbS⟩ := hb
      rw [Finset.mem_filter, Finset.mem_product] at haS hbS
      obtain ⟨⟨ha1, _⟩, _⟩ := haS
      obtain ⟨⟨hb1, _⟩, _⟩ := hbS
      have h2eq : a.2 = b.2 := congrArg Sigma.fst heq
      have hfst : a.2.1 = b.2.1 := congrArg Prod.fst h2eq
      have h1eq : a.1.erase a.2.1 = b.1.erase a.2.1 := by
        have h := congrArg Sigma.snd heq
        change a.1.erase a.2.1 = b.1.erase b.2.1 at h
        rwa [← hfst] at h
      have hA : a.1 = b.1 := by
        calc a.1 = insert a.2.1 (a.1.erase a.2.1) := (Finset.insert_erase ha1).symm
          _ = insert a.2.1 (b.1.erase a.2.1) := by rw [h1eq]
          _ = insert b.2.1 (b.1.erase b.2.1) := by rw [hfst]
          _ = b.1 := Finset.insert_erase hb1
      exact Sigma.ext hA (heq_of_eq h2eq)
    · intro b hb
      rw [hR, Finset.mem_coe, Finset.mem_sigma] at hb
      obtain ⟨hbQ, hbA⟩ := hb
      rw [hQ, Finset.mem_filter, Finset.mem_product] at hbQ
      obtain ⟨⟨hb1, hb2⟩, hbr⟩ := hbQ
      rw [Finset.mem_powersetCard] at hbA
      obtain ⟨hbAX, hbAcard⟩ := hbA
      have hb1notin : b.1.1 ∉ b.2 := fun h => (Finset.mem_sdiff.mp (hbAX h)).2 (by simp)
      have hb2notin : b.1.2 ∉ b.2 := fun h => (Finset.mem_sdiff.mp (hbAX h)).2 (by simp)
      refine ⟨(⟨insert b.1.1 b.2, b.1⟩ : Σ _ : Finset α, α × α), ?_, ?_⟩
      · rw [Finset.mem_coe, Finset.mem_sigma]
        refine ⟨?_, ?_⟩
        · rw [Finset.mem_powersetCard]
          refine ⟨?_, ?_⟩
          · intro x hx
            rw [Finset.mem_insert] at hx
            rcases hx with h | h
            · subst h; exact hb1
            · exact (Finset.mem_sdiff.mp (hbAX h)).1
          · rw [Finset.card_insert_of_notMem hb1notin, hbAcard]
        · rw [Finset.mem_filter, Finset.mem_product]
          refine ⟨⟨Finset.mem_insert_self _ _, ?_⟩, hbr⟩
          rw [Finset.mem_sdiff]
          refine ⟨hb2, ?_⟩
          rw [Finset.mem_insert]
          rintro (h | h)
          · exact (hirr b.1.1) (h ▸ hbr)
          · exact hb2notin h
      · show (⟨b.1, (insert b.1.1 b.2).erase b.1.1⟩ : Σ _ : α × α, Finset α) = b
        rw [Finset.erase_insert hb1notin]
  have hLc :
      (((X.powersetCard (m + 1)).sigma (fun S => (S ×ˢ (X \ S)).filter (fun p => r p.1 p.2)))).card
        = (X.powersetCard (m + 1)).sum
            (fun S => ((S ×ˢ (X \ S)).filter (fun p => r p.1 p.2)).card) :=
    Finset.card_sigma _ _
  have hRc : R.card = ((X ×ˢ X).filter (fun p => r p.1 p.2)).card * ((X.card - 2).choose m) := by
    rw [hR, Finset.card_sigma]
    have hterm : ∀ p ∈ Q, ((X \ {p.1, p.2}).powersetCard m).card = (X.card - 2).choose m := by
      intro p hp
      rw [Finset.card_powersetCard]
      have hpQ : p ∈ (X ×ˢ X).filter (fun p => r p.1 p.2) := by rw [← hQ]; exact hp
      rw [Finset.mem_filter, Finset.mem_product] at hpQ
      obtain ⟨⟨hp1, hp2⟩, hpr⟩ := hpQ
      have hne : p.1 ≠ p.2 := fun h => hirr p.1 (h ▸ hpr)
      have hsub : ({p.1, p.2} : Finset α) ⊆ X := by
        intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h <;> subst h <;> assumption
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_pair hne]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, hQ]
    simp
  rw [← hLc, hcard, hRc]

/-- Averaging form of the internal-edge bound.  If every pair of disjoint finsets `S,T` with
`ξN ≤ |S|`, `ξN ≤ |T|` (`N = Fintype.card V`) spans at most `(ρ+ξ)|S||T|` edges, and
`0 ≤ ρ`, `0 ≤ ξ`, then any finset `X` with `2⌈ξN⌉ ≤ |X|` has at most `(ρ+ξ)|X|²/2` edges, i.e.
the number of ordered adjacent pairs inside `X` is at most `(ρ+ξ)|X|²`. -/
theorem internal_edges_upper_reg_avg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {ρ ξ : ℝ}
    (hρ : 0 ≤ ρ) (hξ : 0 ≤ ξ)
    (hreg : ∀ S T : Finset V, Disjoint S T → ξ * (Fintype.card V : ℝ) ≤ (S.card : ℝ) →
      ξ * (Fintype.card V : ℝ) ≤ (T.card : ℝ) →
      (((S.product T).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
        (ρ + ξ) * (S.card : ℝ) * (T.card : ℝ))
    (X : Finset V) (hX : 2 * Nat.ceil (ξ * (Fintype.card V : ℝ)) ≤ X.card) :
    (((X.product X).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
      (ρ + ξ) * (X.card : ℝ) ^ 2 := by
  classical
  simp only [Finset.product_eq_sprod] at hreg ⊢
  set c : ℝ := ρ + ξ with hc
  set N : ℕ := Fintype.card V with hN
  set k : ℕ := Nat.ceil (ξ * (N : ℝ)) with hk
  have hc0 : 0 ≤ c := by rw [hc]; exact add_nonneg hρ hξ
  have hX' : 2 * k ≤ X.card := hX
  set f : ℕ := ((X ×ˢ X).filter (fun p => G.Adj p.1 p.2)).card with hf
  rcases Nat.lt_or_ge X.card 2 with hsmall | hbig
  · have hsub : (X ×ˢ X).filter (fun p => G.Adj p.1 p.2) ⊆ X.offDiag := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hp1, hp2⟩, hadj⟩ := hp
      rw [Finset.mem_offDiag]
      exact ⟨hp1, hp2, G.ne_of_adj hadj⟩
    have hle : f ≤ X.card * X.card - X.card := by
      rw [hf]
      calc ((X ×ˢ X).filter (fun p => G.Adj p.1 p.2)).card ≤ X.offDiag.card :=
            Finset.card_le_card hsub
        _ = X.card * X.card - X.card := Finset.offDiag_card X
    have hz : X.card * X.card - X.card = 0 := by
      have h3 : X.card = 0 ∨ X.card = 1 := by omega
      rcases h3 with h | h <;> rw [h]
    rw [hz] at hle
    have hf0 : (f : ℝ) = 0 := by rw [Nat.eq_zero_of_le_zero hle]; norm_num
    rw [hf0]
    exact mul_nonneg hc0 (sq_nonneg _)
  · have hNk : ξ * (N : ℝ) ≤ (k : ℝ) := by rw [hk]; exact Nat.le_ceil _
    set s : ℕ := max k 1 with hs
    have hs1 : 1 ≤ s := le_max_right _ _
    have hk_le_s : k ≤ s := le_max_left _ _
    have h_size_ge : ξ * (N : ℝ) ≤ (s : ℝ) :=
      le_trans hNk (by exact_mod_cast hk_le_s)
    have hs_eq_k : 1 ≤ k → s = k := fun h => by rw [hs]; exact max_eq_left h
    have hs_eq_1 : k = 0 → s = 1 := fun h => by rw [hs, h]; simp
    have hk_le_comp : k ≤ X.card - s := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0]; exact Nat.zero_le _
      · rw [hs_eq_k hkpos]; omega
    have hs_le_n : s ≤ X.card := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hs_eq_1 hk0]; omega
      · rw [hs_eq_k hkpos]; omega
    have hs_lt_n : s ≤ X.card - 1 := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hs_eq_1 hk0]; omega
      · rw [hs_eq_k hkpos]; omega
    have h_comp_ge : ξ * (N : ℝ) ≤ ((X.card - s : ℕ) : ℝ) :=
      le_trans hNk (by exact_mod_cast hk_le_comp)
    have hcount := count_lemma X (s - 1) G.Adj (fun a => G.loopless.irrefl a)
    rw [Nat.sub_add_cancel hs1] at hcount
    have hterm : ∀ S ∈ X.powersetCard s,
        (((S ×ˢ (X \ S)).filter (fun p => G.Adj p.1 p.2)).card : ℝ)
          ≤ c * (s : ℝ) * ((X.card - s : ℕ) : ℝ) := by
      intro S hS
      rw [Finset.mem_powersetCard] at hS
      obtain ⟨hSX, hScard⟩ := hS
      have h1 : ξ * (N : ℝ) ≤ (S.card : ℝ) := by rw [hScard]; exact h_size_ge
      have h2 : ξ * (N : ℝ) ≤ ((X \ S).card : ℝ) := by
        rw [Finset.card_sdiff_of_subset hSX, hScard]; exact h_comp_ge
      have h := hreg S (X \ S) Finset.disjoint_sdiff h1 h2
      rwa [hScard, Finset.card_sdiff_of_subset hSX, hScard] at h
    set Cb : ℕ := (X.card - 2).choose (s - 1) with hCb
    have hcast : ((((X.powersetCard s).sum
        (fun S => ((S ×ˢ (X \ S)).filter (fun p => G.Adj p.1 p.2)).card)) : ℕ) : ℝ)
        = ∑ S ∈ X.powersetCard s,
            (((S ×ˢ (X \ S)).filter (fun p => G.Adj p.1 p.2)).card : ℝ) := by
      push_cast; rfl
    have hsum_le : (∑ S ∈ X.powersetCard s,
            (((S ×ˢ (X \ S)).filter (fun p => G.Adj p.1 p.2)).card : ℝ))
        ≤ ((X.powersetCard s).card : ℝ) * (c * (s : ℝ) * ((X.card - s : ℕ) : ℝ)) := by
      have h := Finset.sum_le_sum hterm
      rw [Finset.sum_const, nsmul_eq_mul] at h
      exact h
    have hCbpos : (0 : ℝ) < (Cb : ℝ) := by
      rw [hCb]; exact_mod_cast Nat.choose_pos (by omega : s - 1 ≤ X.card - 2)
    have hbin : (X.card.choose s : ℝ) * ((s : ℝ) * ((X.card - s : ℕ) : ℝ))
        = (X.card : ℝ) * ((X.card : ℝ) - 1) * (Cb : ℝ) := by
      have h := choose_mul_choose X.card s hs1
      have h1 : ((X.card - 1 : ℕ) : ℝ) = (X.card : ℝ) - 1 := by
        rw [Nat.cast_sub (show (1:ℕ) ≤ X.card by omega), Nat.cast_one]
      have h2 : (((X.card - 2).choose (s - 1) : ℕ) : ℝ) = (Cb : ℝ) := by rw [hCb]
      have h3 := congrArg (fun x : ℕ => (x : ℝ)) h
      push_cast at h3
      rw [h1, h2] at h3
      exact h3
    have hcountR : (∑ S ∈ X.powersetCard s,
          (((S ×ˢ (X \ S)).filter (fun p => G.Adj p.1 p.2)).card : ℝ)) = (f : ℝ) * (Cb : ℝ) := by
      have hc := congrArg (fun x : ℕ => (x : ℝ)) hcount
      push_cast at hc
      simpa [hf] using hc
    have key : (f : ℝ) * (Cb : ℝ) ≤ c * ((X.card : ℝ) * ((X.card : ℝ) - 1) * (Cb : ℝ)) := by
      have h1 : (f : ℝ) * (Cb : ℝ)
          ≤ (X.card.choose s : ℝ) * (c * (s : ℝ) * ((X.card - s : ℕ) : ℝ)) := by
        rw [← hcountR]
        rw [Finset.card_powersetCard] at hsum_le
        exact hsum_le
      have h1' : (f : ℝ) * (Cb : ℝ)
          ≤ c * ((X.card.choose s : ℝ) * ((s : ℝ) * ((X.card - s : ℕ) : ℝ))) := by
        refine le_trans h1 (le_of_eq ?_)
        ring
      rwa [hbin] at h1'
    have hfin : (f : ℝ) ≤ c * ((X.card : ℝ) * ((X.card : ℝ) - 1)) := by
      nlinarith [key, hCbpos]
    calc (f : ℝ) ≤ c * ((X.card : ℝ) * ((X.card : ℝ) - 1)) := hfin
      _ ≤ c * (X.card : ℝ) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hc0
          have hx : (0:ℝ) ≤ (X.card:ℝ) := Nat.cast_nonneg X.card
          calc (X.card:ℝ) * ((X.card:ℝ) - 1) ≤ (X.card:ℝ) * (X.card:ℝ) :=
                mul_le_mul_of_nonneg_left (by linarith) hx
            _ = (X.card:ℝ) ^ 2 := by ring

end Commons.Combinatorics.SimpleGraph
