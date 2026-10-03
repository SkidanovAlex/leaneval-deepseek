import Mathlib
import Submission.Work.Peluse.LadderP.stepPSupp

/-!
# The Jensen step of the power-loss ladder

`augNormState` and `augPowState` are the *same* average — over the pairs `(h, h')` of the level-`(j+1)`
ladder — of the level-`t` box norms of `f` at the `augEnum` slots, taken once with the norms
themselves and once with their `2^t`-th powers, where `t = 2^{j+1} - 1 + n`.

Since

* `boxNormPow t Q S f = (boxNorm t Q S f) ^ (2^t)` (the two definitions of the box norm differ
  exactly by the exponent `1/2^t`), and
* the average is a *convex combination* (the weights `M₁^{-2(j+1)}` over the `M₁^{2(j+1)}` pairs sum
  to one),

the statement is Jensen's inequality for the convex function `x ↦ x^{2^t}` on `[0,∞)` applied to the
nonnegative numbers `boxNorm t (augSlots …) (symIcc N) f`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

/-- Power mean (Jensen) inequality at exponent `p` for a *uniform* average over a finite nonempty
index type: `((1/#ι) ∑ g)^p ≤ (1/#ι) ∑ g^p` for `g ≥ 0`.  This is the convexity of `x ↦ x^p` on
`[0,∞)` (`p` a natural number) applied to the convex combination with the equal weights
`(Fintype.card ι)⁻¹`. -/
private lemma pow_avg_le_avg_pow {ι : Type*} [Fintype ι] [Nonempty ι] (g : ι → ℝ)
    (hg : ∀ i, 0 ≤ g i) (p : ℕ) :
    ((Fintype.card ι : ℝ)⁻¹ * ∑ i, g i) ^ p ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, (g i) ^ p := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by
    have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr inferInstance
    positivity
  have hsum : ∑ i : ι, (Fintype.card ι : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hmem : ∀ i ∈ (Finset.univ : Finset ι), g i ∈ Set.Ici (0 : ℝ) := fun i _ => hg i
  have hj := (convexOn_pow p).map_sum_le
    (s := Set.Ici (0 : ℝ)) (f := fun x : ℝ => x ^ p)
    (t := (Finset.univ : Finset ι)) (w := fun _ : ι => (Fintype.card ι : ℝ)⁻¹) (p := g)
    (by intro i _; positivity) hsum hmem
  simp only [smul_eq_mul] at hj
  rw [← Finset.mul_sum] at hj
  conv_rhs => rw [Finset.mul_sum]
  exact hj

/-- `boxNormPow` is the `2^t`-th power of `boxNorm`: the two definitions of the box norm differ by
the exponent `1/2^t` and `boxNormPow` is a nonnegative real. -/
private lemma boxNorm_pow_eq_boxNormPow (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ)
    (g : ℤ → ℂ) : boxNorm t Q S g ^ (2 ^ t) = boxNormPow t Q S g := by
  rw [boxNorm, one_div, show (2 : ℝ) ^ t = ((2 ^ t : ℕ) : ℝ) by push_cast; ring]
  exact Real.rpow_inv_natCast_pow (by simp [boxNormPow]) (pow_ne_zero t (by norm_num))

/-- The number of pairs indexing the states, `M₁^{2(j+1)}`, and the weight `M₁^{-2(j+1)}` of each
term of `augNormState`/`augPowState` are reciprocal. -/
private lemma card_pair_eq (j M₁ : ℕ) :
    ((Fintype.card ((Fin (j+1) → Fin M₁) × (Fin (j+1) → Fin M₁)) : ℝ))⁻¹
      = ((M₁ : ℝ))⁻¹ ^ (2 * (j+1)) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [show (↑(M₁ ^ (j+1) * M₁ ^ (j+1)) : ℝ) = (↑M₁)^(j+1) * (↑M₁)^(j+1) by push_cast; ring]
  rw [mul_inv]
  conv_rhs => rw [show 2 * (j+1) = (j+1) + (j+1) by ring, pow_add, inv_pow]

/-- **The Jensen step of the ladder.**  The `2^{2^{j+1}-1+n}`-th power of the `(j+1)`-state of box
*norms* is at most the `(j+1)`-state of box-norm *powers*, both states being the same uniform average
over the pairs `(h,h')` of ladder patterns. -/
theorem augJensen (j n M₁ : ℕ) (hM₁ : 1 ≤ M₁) (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ)
    (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) (hsup : Work.Peluse.SupportIn f N) :
    (Work.Peluse.LadderP.augNormState j n M₁ c L D N f) ^ (2 ^ (2^(j+1) - 1 + n))
      ≤ Work.Peluse.LadderP.augPowState j n M₁ c L D N f := by
  haveI : Nonempty (Fin M₁) := ⟨⟨0, by omega⟩⟩
  -- the states are the uniform averages of `G p` and `(G p) ^ (2^t)`
  have hA : augNormState j n M₁ c L D N f
      = ((Fintype.card ((Fin (j+1) → Fin M₁) × (Fin (j+1) → Fin M₁)) : ℝ))⁻¹ *
        ∑ p : (Fin (j+1) → Fin M₁) × (Fin (j+1) → Fin M₁),
          boxNorm (2^(j+1)-1+n) (augSlots j n M₁ c L D p.1 p.2) (symIcc N) f := by
    rw [augNormState, card_pair_eq j M₁,
      Fintype.sum_prod_type (fun p : (Fin (j+1) → Fin M₁) × (Fin (j+1) → Fin M₁) =>
        boxNorm (2^(j+1)-1+n) (augSlots j n M₁ c L D p.1 p.2) (symIcc N) f)]
  have hB : augPowState j n M₁ c L D N f
      = ((Fintype.card ((Fin (j+1) → Fin M₁) × (Fin (j+1) → Fin M₁)) : ℝ))⁻¹ *
        ∑ p : (Fin (j+1) → Fin M₁) × (Fin (j+1) → Fin M₁),
          (boxNorm (2^(j+1)-1+n) (augSlots j n M₁ c L D p.1 p.2) (symIcc N) f)
            ^ (2^(2^(j+1)-1+n)) := by
    rw [augPowState, card_pair_eq j M₁,
      Fintype.sum_prod_type (fun p : (Fin (j+1) → Fin M₁) × (Fin (j+1) → Fin M₁) =>
        (boxNorm (2^(j+1)-1+n) (augSlots j n M₁ c L D p.1 p.2) (symIcc N) f)
          ^ (2^(2^(j+1)-1+n)))]
    congr 1
    refine Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => ?_))
    exact (boxNorm_pow_eq_boxNormPow _ _ _ _).symm
  rw [hA, hB]
  exact pow_avg_le_avg_pow
    (fun p : (Fin (j+1) → Fin M₁) × (Fin (j+1) → Fin M₁) =>
      boxNorm (2^(j+1)-1+n) (augSlots j n M₁ c L D p.1 p.2) (symIcc N) f)
    (fun p => by
      rw [boxNorm]
      exact Real.rpow_nonneg (by simp [boxNormPow]) _)
    (2^(2^(j+1)-1+n))

end

end Work.Peluse.LadderP
