import Mathlib
import Submission.Work.BMF.degen_closedWalkAll_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset Real

/-- Membership in a `Finset.product` (the `.product` form of `Finset.mem_product`). -/
private lemma mem_product_eq {α β : Type*} {s : Finset α} {t : Finset β} {x : α × β} :
    x ∈ s.product t ↔ x.1 ∈ s ∧ x.2 ∈ t := by
  rw [show s.product t = s ×ˢ t from rfl, Finset.mem_product]

/-- Cardinality of a `Finset.product` (the `.product` form of `Finset.card_product`). -/
private lemma card_product_eq {α β : Type*} (s : Finset α) (t : Finset β) :
    (s.product t).card = s.card * t.card := by
  rw [show s.product t = s ×ˢ t from rfl, Finset.card_product]

/-- **N5 `candSet_le`.**  The near-degenerate bicycles decompose over the edges: for each edge
`e` the two coordinates of the bicycle are independent closed walks based at `e.x₁` and `e.x₂`
each satisfying the degeneracy condition, so the count is at most the sum over the edges of the
product of the two fibre counts, and each fibre is bounded by `degen_closedWalkAll_le`. -/
theorem candSet_le (k : ℕ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ C P₀ : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ) (c Cq X L P₁ P₂ N C₀ : ℝ)
      (D : Work.BMF.QuadData k f c Cq X L P₁ P₂),
      P₀ ≤ P₁ → 0 < P₁ → 0 < L → 3 ≤ N → N ≤ P₁ ^ (ℓ - 1) → 1 / Real.log P₁ ≤ C₀ →
      ((Work.BMF.candSet D ℓ N C₀ P₁).card : ℝ) ≤
        C * (D.edges.card : ℝ) * C₀ ^ 2 * Work.BMF.pi0 P₁ ^ (4 * ℓ) / N ^ 2 := by
  obtain ⟨C₁, P₀, hC₁, hfib⟩ := degen_closedWalkAll_le k ℓ hℓ
  refine ⟨C₁ ^ 2, P₀, by positivity, ?_⟩
  intro f c Cq X L P₁ P₂ N C₀ D hP₀ hP₁ hL hN hNle hC₀
  set Q : (Fin (ℓ + 1) → GVert D) → Prop := fun W =>
      |((walkProdV D ℓ W : ℕ) : ℝ) - ((walkProdU D ℓ W : ℕ) : ℝ)| ≤ C₀ * P₁ ^ ℓ / N
    with hQdef
  have hfibx : ∀ x : ℝ,
      (((closedWalkAll D ℓ x).filter Q).card : ℝ) ≤ C₁ * C₀ * pi0 P₁ ^ (2 * ℓ) / N := by
    intro x
    have h := hfib f c Cq X L P₁ P₂ N C₀ D x hP₀ hP₁ hL hN hNle hC₀
    simpa only [hQdef] using h
  have hFnn : 0 ≤ C₁ * C₀ * pi0 P₁ ^ (2 * ℓ) / N := by
    have h := hfibx 0
    have h0 : (0 : ℝ) ≤ (((closedWalkAll D ℓ 0).filter Q).card : ℝ) := Nat.cast_nonneg _
    linarith
  have hsub : candSet D ℓ N C₀ P₁ ⊆
      D.edges.sigma (fun e => ((closedWalkAll D ℓ e.x₁).filter Q).product
        ((closedWalkAll D ℓ e.x₂).filter Q)) := by
    rintro ⟨e, ⟨W, W'⟩⟩ ht
    simp only [candSet, bikeSetAll, Finset.mem_filter, Finset.mem_sigma, mem_product_eq,
      hQdef] at ht ⊢
    tauto
  have hcard : ((candSet D ℓ N C₀ P₁).card : ℝ) ≤
      ∑ e ∈ D.edges, ((((closedWalkAll D ℓ e.x₁).filter Q).card : ℝ) *
        (((closedWalkAll D ℓ e.x₂).filter Q).card : ℝ)) := by
    calc ((candSet D ℓ N C₀ P₁).card : ℝ)
        ≤ ((D.edges.sigma (fun e => ((closedWalkAll D ℓ e.x₁).filter Q).product
            ((closedWalkAll D ℓ e.x₂).filter Q))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ = ∑ e ∈ D.edges, ((((closedWalkAll D ℓ e.x₁).filter Q).card : ℝ) *
            (((closedWalkAll D ℓ e.x₂).filter Q).card : ℝ)) := by
          rw [Finset.card_sigma, Nat.cast_sum]
          exact Finset.sum_congr rfl (fun e _ => by rw [card_product_eq, Nat.cast_mul])
  have hFF : (C₁ * C₀ * pi0 P₁ ^ (2 * ℓ) / N) * (C₁ * C₀ * pi0 P₁ ^ (2 * ℓ) / N)
      = C₁ ^ 2 * C₀ ^ 2 * pi0 P₁ ^ (4 * ℓ) / N ^ 2 := by
    have hpow : (pi0 P₁ ^ (2 * ℓ) : ℝ) ^ 2 = pi0 P₁ ^ (4 * ℓ) := by
      rw [← pow_mul]; congr 1; ring
    rw [div_mul_div_comm, ← pow_two (C₁ * C₀ * pi0 P₁ ^ (2 * ℓ)), mul_pow, mul_pow, hpow,
      ← pow_two N]
  calc ((candSet D ℓ N C₀ P₁).card : ℝ)
      ≤ ∑ e ∈ D.edges, ((((closedWalkAll D ℓ e.x₁).filter Q).card : ℝ) *
          (((closedWalkAll D ℓ e.x₂).filter Q).card : ℝ)) := hcard
    _ ≤ ∑ e ∈ D.edges,
          (C₁ * C₀ * pi0 P₁ ^ (2 * ℓ) / N) * (C₁ * C₀ * pi0 P₁ ^ (2 * ℓ) / N) := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        exact mul_le_mul (hfibx e.x₁) (hfibx e.x₂) (by positivity) hFnn
    _ = (D.edges.card : ℝ) *
          ((C₁ * C₀ * pi0 P₁ ^ (2 * ℓ) / N) * (C₁ * C₀ * pi0 P₁ ^ (2 * ℓ) / N)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = C₁ ^ 2 * (D.edges.card : ℝ) * C₀ ^ 2 * pi0 P₁ ^ (4 * ℓ) / N ^ 2 := by
        rw [hFF]; ring

end Work.BMF
