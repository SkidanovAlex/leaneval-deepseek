import Mathlib
import Submission.Work.Peluse.SwapE.Defs

/-!
# `existsSlotGood` — the slot-extraction step of the dense endgame

The endgame's average hypothesis `δ ≤ avg F` over a finite family `Ω`, together with the fact
that at most a `δ/2` proportion of the family lies outside `G` and that `F ≤ 1` everywhere,
forces some `ω ∈ G` with `F ω ≥ δ/2`.

Proof (contradiction).  Suppose `F ω < δ/2` on `G`.  Writing `n = #Ω`, `g = #G` and
`b = #(Ω \ G)`, the hypothesis on the complement gives `b ≤ (δ/2) n`, and splitting the sum
along `G ≤ Ω`,

`∑ F = ∑_{Ω\G} F + ∑_G F < b + g (δ/2) = b + (n - b)(δ/2) = n δ/2 + b (1 - δ/2)`

which is `≤ n δ/2 + b ≤ n δ` (the first inequality from `1 - δ/2 ≤ 1` and `b ≥ 0`, the second
from the hypothesis on `b`); dividing by `n > 0` gives `avg F < δ`, contradicting `havg`.  The
case `G = ∅` is the same computation read off from `b = n`: `∑ F ≤ n ≤ (δ/2) n < n δ`.
-/

namespace Work.Peluse.SwapE

theorem existsSlotGood {Ω : Type} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω] (F : Ω → ℝ)
    (G : Finset Ω) (δ : ℝ) (hδ : 0 < δ) (hF : ∀ ω, F ω ≤ 1)
    (hbad : ((Finset.univ \ G).card : ℝ) ≤ δ / 2 * (Fintype.card Ω : ℝ))
    (havg : δ ≤ Work.Peluse.LadderP.Swap.avg F) : ∃ ω ∈ G, δ / 2 ≤ F ω := by
  classical
  by_contra hcon
  push Not at hcon
  -- `n = #Ω > 0`
  have hn : (0 : ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  -- the contradiction engine: `avg F < δ` from `∑ F < n δ`
  have finish : ∑ ω : Ω, F ω < (Fintype.card Ω : ℝ) * δ → False := by
    intro htotal
    have havg_lt : Work.Peluse.LadderP.Swap.avg F < δ := by
      rw [Work.Peluse.LadderP.Swap.avg]
      have h2 : ((Fintype.card Ω : ℝ))⁻¹ * ((Fintype.card Ω : ℝ) * δ) = δ := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hn), one_mul]
      calc ((Fintype.card Ω : ℝ))⁻¹ * ∑ ω, F ω
          < ((Fintype.card Ω : ℝ))⁻¹ * ((Fintype.card Ω : ℝ) * δ) :=
            mul_lt_mul_of_pos_left htotal (inv_pos.mpr hn)
        _ = δ := h2
    linarith
  have hcard : (G.card : ℝ) + ((Finset.univ \ G).card : ℝ) = (Fintype.card Ω : ℝ) := by
    have h : G.card + (Finset.univ \ G).card = Fintype.card Ω := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
      exact Nat.add_sub_of_le (Finset.card_le_univ G)
    exact_mod_cast h
  rcases Nat.eq_zero_or_pos G.card with hg0 | hgpos
  · -- `G = ∅`: the complement is everything, so `n ≤ (δ/2) n` and `∑ F ≤ n < n δ`
    have hGempty : G = ∅ := Finset.card_eq_zero.mp hg0
    have hb_eq : ((Finset.univ \ G).card : ℝ) = (Fintype.card Ω : ℝ) := by
      have h : (Finset.univ \ G).card = Fintype.card Ω := by rw [hGempty]; simp
      exact_mod_cast h
    have hsum_le : ∑ ω : Ω, F ω ≤ (Fintype.card Ω : ℝ) := by
      have h : ∑ ω : Ω, F ω ≤ ∑ _ω : Ω, (1 : ℝ) := Finset.sum_le_sum (fun ω _ => hF ω)
      simpa using h
    have hh : (Fintype.card Ω : ℝ) ≤ δ / 2 * (Fintype.card Ω : ℝ) := by
      simpa only [hb_eq] using hbad
    have hbnd2 : ∑ ω : Ω, F ω ≤ δ / 2 * (Fintype.card Ω : ℝ) := le_trans hsum_le hh
    have hlt : δ / 2 * (Fintype.card Ω : ℝ) < (Fintype.card Ω : ℝ) * δ := by
      rw [mul_comm (δ / 2) (Fintype.card Ω : ℝ)]
      exact mul_lt_mul_of_pos_left (by linarith) hn
    exact finish (lt_of_le_of_lt hbnd2 hlt)
  · -- `G ≠ ∅`: split the sum, bound the complement by its cardinality
    have hBle : ∑ ω ∈ Finset.univ \ G, F ω ≤ ((Finset.univ \ G).card : ℝ) := by
      calc ∑ ω ∈ Finset.univ \ G, F ω ≤ ∑ ω ∈ Finset.univ \ G, (1 : ℝ) :=
            Finset.sum_le_sum (fun ω _ => hF ω)
        _ = ((Finset.univ \ G).card : ℝ) := by simp
    have hsplit : ∑ ω ∈ Finset.univ \ G, F ω + ∑ ω ∈ G, F ω = ∑ ω : Ω, F ω :=
      Finset.sum_sdiff (Finset.subset_univ G)
    obtain ⟨ω₀, hω₀⟩ := Finset.card_pos.mp hgpos
    have hGlt : ∑ ω ∈ G, F ω < (G.card : ℝ) * (δ / 2) := by
      have h := Finset.sum_lt_sum (s := G) (f := F) (g := fun _ : Ω => δ / 2)
        (fun ω hω => (hcon ω hω).le) ⟨ω₀, hω₀, hcon ω₀ hω₀⟩
      simpa using h
    have hmain : ((Finset.univ \ G).card : ℝ) + (G.card : ℝ) * (δ / 2)
        ≤ (Fintype.card Ω : ℝ) * δ := by
      have hb0 : (0 : ℝ) ≤ ((Finset.univ \ G).card : ℝ) := by positivity
      have hone : (1 - δ / 2 : ℝ) ≤ 1 := by linarith
      have hs1 : ((Finset.univ \ G).card : ℝ) * (1 - δ / 2) ≤ ((Finset.univ \ G).card : ℝ) :=
        mul_le_of_le_one_right hb0 hone
      have hg_eq : (G.card : ℝ) = (Fintype.card Ω : ℝ) - ((Finset.univ \ G).card : ℝ) := by
        linarith
      rw [hg_eq]
      nlinarith [hbad, hs1, hb0, hδ]
    have htotal : ∑ ω : Ω, F ω < (Fintype.card Ω : ℝ) * δ := by
      have hsum : ∑ ω ∈ Finset.univ \ G, F ω + ∑ ω ∈ G, F ω
          < ((Finset.univ \ G).card : ℝ) + (G.card : ℝ) * (δ / 2) :=
        add_lt_add_of_le_of_lt hBle hGlt
      rw [hsplit] at hsum
      exact lt_of_lt_of_le hsum hmain
    exact finish htotal

end Work.Peluse.SwapE
