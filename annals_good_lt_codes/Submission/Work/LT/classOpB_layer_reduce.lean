import Mathlib
import Submission.Work.LT.lr_local_defs
import Submission.Work.LT.lr_walk_mean_zero
import Submission.Work.LT.sum_sub_mul_sub
import Submission.Work.LT.sum_sum_mul_right

/-!
# Reduction of the `B`-walk quadratic form to centred form

`classOpB_layer_reduce` is the algebraic step that trades the layer of the "right averaging"
operator `s₁ ↦ (g ↦ ∑_j s₁ (g * B j) / Δ)` against its centring by the means of `s₀` and `s₁`.

Write `S0 = ∑ g, s0 g`, `S1 = ∑ g, s1 g`, `n = |G|`, `X g = ∑ j, s1 (g * B j)` and
`L = ∑ g, s0 g * (X g / Δ)`.  Expanding the right-hand side with `sum_sub_mul_sub` and using
the reindexing identity `∑ g, X g = Δ * S1` (`sum_sum_mul_right`) together with
`∑ g, s0 g * X g = Δ * L` gives

  `RHS = L - S0 * S1 / n`.

Under the hypothesis `S0 + S1 = 0` this becomes `RHS = L + S0² / n ≥ L`, which is exactly the
stated inequality.  The hypothesis `Δ > 0` only guarantees that the normalising factor
`(Δ : ℝ)` is nonzero (and that the index type `Fin Δ` is the intended one).
-/

namespace Work.LT

lemma classOpB_layer_reduce {G : Type} [Group G] [Fintype G] {Δ : ℕ} (B : Fin Δ → G)
    (hΔpos : 0 < Δ) (s0 s1 : G → ℝ)
    (hm : (∑ g, s0 g) + (∑ g, s1 g) = 0) :
    (∑ g, s0 g * ((∑ j, s1 (g * B j)) / (Δ : ℝ)))
      ≤ ∑ g, (s0 g - (∑ g, s0 g) / (Fintype.card G : ℝ))
          * ((∑ j, (s1 (g * B j) - (∑ g, s1 g) / (Fintype.card G : ℝ))) / (Δ : ℝ)) := by
  classical
  set S0 : ℝ := ∑ g, s0 g with hS0
  set S1 : ℝ := ∑ g, s1 g with hS1
  set n : ℝ := (Fintype.card G : ℝ) with hn
  set a : ℝ := S0 / n with ha
  set b : ℝ := S1 / n with hb
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  have hdne : ((Δ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hΔpos)
  have hS1neg : S1 = -S0 := by linarith
  -- Centring the inner sum: `∑ j, (s1 (g * B j) - b) = X g - Δ * b`.
  have hX : ∀ g : G,
      (∑ j : Fin Δ, (s1 (g * B j) - b)) = (∑ j : Fin Δ, s1 (g * B j)) - (Δ : ℝ) * b := by
    intro g
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  -- Pull the normalisation `1 / Δ` out of the sum.
  have hR1 : (∑ g, (s0 g - a) * ((∑ j, (s1 (g * B j) - b)) / (Δ : ℝ)))
      = (1 / (Δ : ℝ)) * ∑ g, (s0 g - a) * ((∑ j, s1 (g * B j)) - (Δ : ℝ) * b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    rw [hX g]
    ring
  -- Expand the product of the two centred factors.
  have hR2 : (∑ g, (s0 g - a) * ((∑ j, s1 (g * B j)) - (Δ : ℝ) * b))
      = (∑ g, s0 g * (∑ j : Fin Δ, s1 (g * B j)))
          - a * (∑ g, (∑ j : Fin Δ, s1 (g * B j)))
          - ((Δ : ℝ) * b) * (∑ g, s0 g) + a * ((Δ : ℝ) * b) * n := by
    rw [sum_sub_mul_sub]
  -- `∑ g, s0 g * X g = Δ * L`.
  have hLHSmul : (∑ g, s0 g * (∑ j : Fin Δ, s1 (g * B j)))
      = (Δ : ℝ) * (∑ g, s0 g * ((∑ j, s1 (g * B j)) / (Δ : ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    field_simp
  -- `∑ g, X g = Δ * S1`.
  have hS1sum : (∑ g, (∑ j : Fin Δ, s1 (g * B j))) = (Δ : ℝ) * S1 := by
    rw [sum_sum_mul_right, Fintype.card_fin]
  -- The key identity: the right-hand side is the left-hand side plus `S0² / n`.
  have hkey : (∑ g, (s0 g - a) * ((∑ j, (s1 (g * B j) - b)) / (Δ : ℝ)))
      = (∑ g, s0 g * ((∑ j, s1 (g * B j)) / (Δ : ℝ))) + S0 ^ 2 / n := by
    rw [hR1, hR2, hLHSmul, hS1sum, ← hS0]
    rw [ha, hb, hS1neg]
    field_simp
    ring
  rw [hkey]
  linarith [div_nonneg (sq_nonneg S0) (le_of_lt hnpos)]

end Work.LT
