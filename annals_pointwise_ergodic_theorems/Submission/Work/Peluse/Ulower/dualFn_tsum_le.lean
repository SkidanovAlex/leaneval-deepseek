import Mathlib
import Submission.Work.Peluse.Basic

/-!
# The `ℓ¹`-mass of Peluse's dual function `F₂` is at most that of `f₁`

Peluse's dual function (`Work.Peluse.dualFn`) in the case `ℓ = 2`, `m = 2`, `P₁ = X` of
Corollary 3.8 is

`F₂(x) = dualFn N P f₀ f₁ x = (1/N) ∑_{y ∈ [N]} f₀ (x - P y) · f₁ (x + y - P y)`.

If `‖f₀‖ ≤ 1` pointwise and `f₁` is finitely supported, then the `ℓ¹`-mass of `F₂` is at most the
`ℓ¹`-mass of `f₁`:

`∑'_x ‖F₂ x‖ ≤ ∑'_x ‖f₁ x‖`.

The proof is the elementary one: bound the average over `y ∈ [N]` by the average of the moduli of
the `f₁`-factors (dropping the `f₀`-factor, which has modulus `≤ 1`), interchange the sum over `x`
with the finite sum over `y`, and observe that `x ↦ x + y - P y` is a bijection of `ℤ`; the
remaining factor `(1/N) · N` is `1`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

/-- **The `ℓ¹`-mass of the dual function is at most the `ℓ¹`-mass of `f₁`.**

`(∑'_x ‖dualFn N P f₀ f₁ x‖) ≤ ∑'_x ‖f₁ x‖` whenever `1 ≤ N`, `‖f₀‖ ≤ 1` pointwise and `f₁` is
finitely supported. -/
theorem dualFn_tsum_le {N : ℕ} (hN : 1 ≤ N) (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ)
    (h0 : ∀ x : ℤ, ‖f₀ x‖ ≤ 1) (hfin : Work.Peluse.FinSuppZ f₁) :
    (∑' x : ℤ, ‖Work.Peluse.dualFn N P f₀ f₁ x‖) ≤ ∑' x : ℤ, ‖f₁ x‖ := by
  obtain ⟨M, hM⟩ := hfin
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  -- summability of the norm of `f₁`, from finite support
  have hsum_f1 : Summable (fun x : ℤ => ‖f₁ x‖) := by
    apply summable_of_ne_finset_zero (s := Finset.Icc (-(M : ℤ)) (M : ℤ))
    intro x hx
    rw [norm_eq_zero]
    apply hM
    have hx' : x < -(M : ℤ) ∨ (M : ℤ) < x := by
      rw [Finset.mem_Icc] at hx
      rcases not_and_or.mp hx with h | h
      · exact Or.inl (not_le.mp h)
      · exact Or.inr (not_le.mp h)
    have habs : (M : ℤ) < |x| := by
      rcases hx' with h | h
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        linarith
    have hcast : (M : ℤ) < (x.natAbs : ℤ) := by
      rwa [Int.natCast_natAbs]
    exact_mod_cast hcast
  -- summability of the shifted versions of `‖f₁‖`
  have hshift : ∀ y : ℕ,
      Summable (fun x : ℤ => ‖f₁ (x + ((y : ℤ) - P.eval ((y : ℤ))))‖) := by
    intro y
    have h := (Equiv.addRight ((y : ℤ) - P.eval ((y : ℤ)))).summable_iff.mpr hsum_f1
    have hfun : ((fun z : ℤ => ‖f₁ z‖) ∘ (Equiv.addRight ((y : ℤ) - P.eval ((y : ℤ)))))
        = fun x : ℤ => ‖f₁ (x + ((y : ℤ) - P.eval ((y : ℤ))))‖ := by
      ext x
      simp only [Function.comp_apply, Equiv.coe_addRight]
    rw [hfun] at h
    exact h
  -- the pointwise bound
  have hpt : ∀ x : ℤ, ‖Work.Peluse.dualFn N P f₀ f₁ x‖ ≤
      ((N : ℝ))⁻¹ * ∑ y ∈ Finset.Icc 1 N, ‖f₁ (x + ((y : ℤ) - P.eval ((y : ℤ))))‖ := by
    intro x
    have hdual : Work.Peluse.dualFn N P f₀ f₁ x =
        ((N : ℂ))⁻¹ * ∑ y ∈ Finset.Icc 1 N,
          f₀ (x - P.eval ((y : ℤ))) * f₁ (x + ((y : ℤ) - P.eval ((y : ℤ)))) := by
      rw [Work.Peluse.dualFn]
      congr 1
      refine Finset.sum_congr rfl (fun y _ => ?_)
      simp only [add_sub_assoc]
    have hbound : ‖∑ y ∈ Finset.Icc 1 N,
        f₀ (x - P.eval ((y : ℤ))) * f₁ (x + ((y : ℤ) - P.eval ((y : ℤ))))‖
        ≤ ∑ y ∈ Finset.Icc 1 N, ‖f₁ (x + ((y : ℤ) - P.eval ((y : ℤ))))‖ := by
      calc ‖∑ y ∈ Finset.Icc 1 N,
            f₀ (x - P.eval ((y : ℤ))) * f₁ (x + ((y : ℤ) - P.eval ((y : ℤ))))‖
          ≤ ∑ y ∈ Finset.Icc 1 N,
              ‖f₀ (x - P.eval ((y : ℤ))) * f₁ (x + ((y : ℤ) - P.eval ((y : ℤ))))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ y ∈ Finset.Icc 1 N, ‖f₁ (x + ((y : ℤ) - P.eval ((y : ℤ))))‖ := by
            apply Finset.sum_le_sum
            intro y _
            rw [norm_mul]
            calc ‖f₀ (x - P.eval ((y : ℤ)))‖ * ‖f₁ (x + ((y : ℤ) - P.eval ((y : ℤ))))‖
                ≤ 1 * ‖f₁ (x + ((y : ℤ) - P.eval ((y : ℤ))))‖ :=
                  mul_le_mul_of_nonneg_right (h0 _) (norm_nonneg _)
              _ = ‖f₁ (x + ((y : ℤ) - P.eval ((y : ℤ))))‖ := one_mul _
    rw [hdual, norm_mul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (le_of_lt hNpos))
  -- the upper bound is summable
  have hsumInner : Summable (fun x : ℤ =>
      ∑ y ∈ Finset.Icc 1 N, ‖f₁ (x + ((y : ℤ) - P.eval ((y : ℤ))))‖) :=
    summable_sum (fun y _ => hshift y)
  have hsumG : Summable (fun x : ℤ => ((N : ℝ))⁻¹ *
      ∑ y ∈ Finset.Icc 1 N, ‖f₁ (x + ((y : ℤ) - P.eval ((y : ℤ))))‖) :=
    hsumInner.mul_left _
  -- summability of the left-hand side
  have hsumL : Summable (fun x : ℤ => ‖Work.Peluse.dualFn N P f₀ f₁ x‖) :=
    Summable.of_nonneg_of_le (fun x => norm_nonneg _) hpt hsumG
  -- the value of the upper bound
  have hshift_tsum : ∀ y ∈ Finset.Icc 1 N,
      (∑' x : ℤ, ‖f₁ (x + ((y : ℤ) - P.eval ((y : ℤ))))‖) = ∑' x : ℤ, ‖f₁ x‖ := by
    intro y _
    have h := Equiv.tsum_eq (Equiv.addRight ((y : ℤ) - P.eval ((y : ℤ))))
      (fun z : ℤ => ‖f₁ z‖)
    simpa [Function.comp, Equiv.coe_addRight] using h
  have hGeq : (∑' x : ℤ, ((N : ℝ))⁻¹ *
      ∑ y ∈ Finset.Icc 1 N, ‖f₁ (x + ((y : ℤ) - P.eval ((y : ℤ))))‖) = ∑' x : ℤ, ‖f₁ x‖ := by
    rw [tsum_mul_left]
    rw [Summable.tsum_finsetSum (fun y _ => hshift y)]
    have h1 : (∑ y ∈ Finset.Icc 1 N,
          (∑' x : ℤ, ‖f₁ (x + ((y : ℤ) - P.eval ((y : ℤ))))‖))
        = ∑ y ∈ Finset.Icc 1 N, (∑' x : ℤ, ‖f₁ x‖) :=
      Finset.sum_congr rfl (fun y hy => hshift_tsum y hy)
    rw [h1, Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
    have h2 : (N + 1 - 1 : ℕ) = N := by omega
    rw [h2, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hNpos), one_mul]
  exact le_trans (hsumL.tsum_le_tsum hpt hsumG) (le_of_eq hGeq)

end

end Work.Peluse.Ulower
