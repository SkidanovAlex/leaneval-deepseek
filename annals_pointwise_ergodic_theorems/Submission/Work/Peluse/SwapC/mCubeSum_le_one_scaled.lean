import Mathlib
import Submission.Work.Peluse.SwapC.Basic

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-! ## The scaled box bound: `‖mCubeSum‖ ≤ |S'| / |S|`

`mCubeSum_norm_le_one` bounds the multiset box sum of a `1`-bounded family by `1`, at the price of
requiring the support set `S'` to have exactly the cardinality of the normalising set `S`.  Here the
actual support set is kept: every cube term has modulus `≤ 1`, and for fixed shifts the `x`-sum is
supported in the translate `S' - ∑_k ν_k (h' k)`, so it is bounded by `|S'|`; the normalisation
`|S|⁻¹ (|X|⁻¹)^{2d}` times the `|X|^{2d}` index pairs of `Fin d → X` leaves exactly `|S'| / |S|`.

The proof is the same chain as the private `mCubeSum_le_one_gen` of `mCubeSum_norm_le_one.lean`,
with the final arithmetic relaxed from `|S'| = |S|` to the direct factor `(|X|⁻¹)^{2d}|X|^{2d} ≤ 1`.
-/

/-- The modulus is preserved by iterated conjugation. -/
private lemma norm_star_iterate (n : ℕ) (z : ℂ) : ‖(star^[n]) z‖ = ‖z‖ := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', norm_star, ih]

/-- A cube term is a product of `2 ^ d` terms of modulus at most `1`, hence has modulus at most
`1`. -/
private lemma norm_cubeTerm_le {d : ℕ} {F : (Fin d → Bool) → ℤ → ℂ}
    (hbd : ∀ (ω : Fin d → Bool) (x : ℤ), ‖F ω x‖ ≤ 1) (h h' : Fin d → ℤ) (x : ℤ) :
    ‖∏ ω : Fin d → Bool, (star^[weight ω]) (F ω (x + cornerShift h h' ω))‖ ≤ 1 := by
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun ω _ => norm_nonneg _) (fun ω _ => ?_)
  rw [norm_star_iterate]
  exact hbd ω _

/-- For fixed increments the sum over the lower corner `x` of the cube term is bounded by the
cardinality of the support set: the `ω = 0` corner forces `x + ∑_k ν_k (h' k) ∈ S'`. -/
private lemma norm_tsum_cubeTerm_le {d : ℕ} {X : Type} {ν : Fin d → X → ℤ}
    {S' : Finset ℤ} {F : (Fin d → Bool) → ℤ → ℂ}
    (hbd : ∀ (ω : Fin d → Bool) (x : ℤ), ‖F ω x‖ ≤ 1)
    (hsup : ∀ (ω : Fin d → Bool) (x : ℤ), x ∉ S' → F ω x = 0) (h h' : Fin d → X) :
    ‖∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
        (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖
      ≤ (S'.card : ℝ) := by
  have hvanish : ∀ x : ℤ, x ∉ S'.image (fun s => s - ∑ k : Fin d, ν k (h' k)) →
      (∏ ω : Fin d → Bool, (star^[weight ω])
        (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))) = 0 := by
    intro x hx
    refine Finset.prod_eq_zero (Finset.mem_univ (fun _ : Fin d => false)) ?_
    have hw : weight (fun _ : Fin d => false) = 0 := by simp [weight]
    have hc : cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) (fun _ : Fin d => false)
        = ∑ k : Fin d, ν k (h' k) := by simp [cornerShift]
    rw [hw, hc, Function.iterate_zero_apply]
    exact hsup _ _ (fun hxc =>
      hx (Finset.mem_image.mpr ⟨x + ∑ k : Fin d, ν k (h' k), hxc, by ring⟩))
  rw [tsum_eq_sum (s := S'.image (fun s => s - ∑ k : Fin d, ν k (h' k))) hvanish]
  calc ‖∑ x ∈ S'.image (fun s => s - ∑ k : Fin d, ν k (h' k)),
        ∏ ω : Fin d → Bool, (star^[weight ω])
        (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖
      ≤ ∑ x ∈ S'.image (fun s => s - ∑ k : Fin d, ν k (h' k)),
        ‖∏ ω : Fin d → Bool, (star^[weight ω])
        (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ S'.image (fun s => s - ∑ k : Fin d, ν k (h' k)), (1 : ℝ) :=
        Finset.sum_le_sum (fun x _ => norm_cubeTerm_le hbd _ _ x)
    _ = ((S'.image (fun s => s - ∑ k : Fin d, ν k (h' k))).card : ℝ) := by simp
    _ ≤ (S'.card : ℝ) := by exact_mod_cast Finset.card_image_le

/-- Scaled normalisation arithmetic: the block
`(|X|⁻¹)^{2d} · (|X|^d · (|X|^d · |S'|))` is at most `|S'|`, because
`(|X|⁻¹)^{2d}·|X|^{2d} = ((|X|⁻¹·|X|)^d)² ≤ 1`. -/
private lemma norm_arith_scaled (n m w d : ℕ) :
    ((n : ℝ))⁻¹ * (((w : ℝ))⁻¹) ^ (2 * d) *
      (((w : ℝ)) ^ d * (((w : ℝ)) ^ d * (m : ℝ))) ≤ (m : ℝ) / (n : ℝ) := by
  have hw0 : (0 : ℝ) ≤ (w : ℝ) := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hwi0 : 0 ≤ ((w : ℝ))⁻¹ := inv_nonneg.mpr hw0
  have hA0 : 0 ≤ (((w : ℝ))⁻¹) ^ d * ((w : ℝ)) ^ d :=
    mul_nonneg (pow_nonneg hwi0 d) (pow_nonneg hw0 d)
  have hr : (((w : ℝ))⁻¹ * (w : ℝ)) ^ d ≤ 1 := by
    refine pow_le_one₀ (mul_nonneg hwi0 hw0) ?_
    rcases eq_or_ne (w : ℝ) 0 with h | h
    · rw [h]; simp
    · rw [inv_mul_cancel₀ h]
  have hAd : (((w : ℝ))⁻¹) ^ d * ((w : ℝ)) ^ d ≤ 1 := by
    rw [← mul_pow]; exact hr
  have hAA : ((((w : ℝ))⁻¹) ^ d * ((w : ℝ)) ^ d) *
      ((((w : ℝ))⁻¹) ^ d * ((w : ℝ)) ^ d) ≤ 1 := by
    have := mul_le_mul hAd hAd hA0 (by norm_num : (0 : ℝ) ≤ 1)
    simpa using this
  have hkey : (((w : ℝ))⁻¹) ^ (2 * d) * (((w : ℝ)) ^ d * (((w : ℝ)) ^ d * (m : ℝ)))
      ≤ (m : ℝ) := by
    have heq : (((w : ℝ))⁻¹) ^ (2 * d) * (((w : ℝ)) ^ d * (((w : ℝ)) ^ d * (m : ℝ)))
        = ((((w : ℝ))⁻¹) ^ d * ((w : ℝ)) ^ d) *
            ((((w : ℝ))⁻¹) ^ d * ((w : ℝ)) ^ d) * (m : ℝ) := by
      rw [show 2 * d = d + d from by omega, pow_add]
      ring
    rw [heq]
    calc ((((w : ℝ))⁻¹) ^ d * ((w : ℝ)) ^ d) *
            ((((w : ℝ))⁻¹) ^ d * ((w : ℝ)) ^ d) * (m : ℝ)
        ≤ 1 * (m : ℝ) := mul_le_mul_of_nonneg_right hAA hm0
      _ = (m : ℝ) := by ring
  have hninv0 : 0 ≤ ((n : ℝ))⁻¹ := inv_nonneg.mpr hn0
  calc ((n : ℝ))⁻¹ * (((w : ℝ))⁻¹) ^ (2 * d) *
          (((w : ℝ)) ^ d * (((w : ℝ)) ^ d * (m : ℝ)))
      = ((n : ℝ))⁻¹ * ((((w : ℝ))⁻¹) ^ (2 * d) *
          (((w : ℝ)) ^ d * (((w : ℝ)) ^ d * (m : ℝ)))) := by ring
    _ ≤ ((n : ℝ))⁻¹ * (m : ℝ) := mul_le_mul_of_nonneg_left hkey hninv0
    _ = (m : ℝ) / (n : ℝ) := by rw [div_eq_mul_inv, mul_comm]

/-- **The multiset box sum of a `1`-bounded family supported in `S'` is at most
`|S'| / |S|`.**  This is `mCubeSum_norm_le_one` with the cardinality hypothesis on the support set
removed: the support only enters through the bound `|S'|` for the `x`-sum, and the normalisation
`|S|⁻¹ (|X|⁻¹)^{2d}` cancels the `|X|^{2d}` index pairs up to the factor
`((|X|⁻¹·|X|)^d)² ≤ 1`. -/
private theorem mCubeSum_le_gen (d : ℕ) (X : Type) [Fintype X] (ν : Fin d → X → ℤ)
    (S S' : Finset ℤ) (F : (Fin d → Bool) → ℤ → ℂ)
    (hsup : ∀ (ω : Fin d → Bool) (x : ℤ), x ∉ S' → F ω x = 0)
    (hbd : ∀ (ω : Fin d → Bool) (x : ℤ), ‖F ω x‖ ≤ 1) :
    ‖mCubeSum d X ν S F‖ ≤ (S'.card : ℝ) / (S.card : ℝ) := by
  have hterm : ∀ h h' : Fin d → X,
      ‖∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
        (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖
      ≤ (S'.card : ℝ) := fun h h' => norm_tsum_cubeTerm_le hbd hsup h h'
  have hcX : ((Fintype.card (Fin d → X) : ℝ)) = ((Fintype.card X : ℝ)) ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hsum : ‖∑ h : Fin d → X, ∑ h' : Fin d → X,
        ∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
          (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖
      ≤ ((Fintype.card X : ℝ)) ^ d * (((Fintype.card X : ℝ)) ^ d * (S'.card : ℝ)) := by
    have hinner : ∀ h : Fin d → X,
        ‖∑ h' : Fin d → X, ∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
            (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖
        ≤ (Fintype.card (Fin d → X) : ℝ) * (S'.card : ℝ) := by
      intro h
      calc ‖∑ h' : Fin d → X, ∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
              (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖
          ≤ ∑ h' : Fin d → X, ‖∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
              (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _h' : Fin d → X, (S'.card : ℝ) := Finset.sum_le_sum (fun h' _ => hterm h h')
        _ = (Fintype.card (Fin d → X) : ℝ) * (S'.card : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    calc ‖∑ h : Fin d → X, ∑ h' : Fin d → X,
            ∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
              (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖
        ≤ ∑ h : Fin d → X, ‖∑ h' : Fin d → X, ∑' x : ℤ, ∏ ω : Fin d → Bool,
            (star^[weight ω])
              (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _h : Fin d → X, ((Fintype.card (Fin d → X) : ℝ) * (S'.card : ℝ)) :=
          Finset.sum_le_sum (fun h _ => hinner h)
      _ = (Fintype.card (Fin d → X) : ℝ) *
          ((Fintype.card (Fin d → X) : ℝ) * (S'.card : ℝ)) := by
          simp [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = ((Fintype.card X : ℝ)) ^ d * (((Fintype.card X : ℝ)) ^ d * (S'.card : ℝ)) := by
          rw [hcX]
  have hc0 : 0 ≤ ((S.card : ℝ))⁻¹ * (((Fintype.card X : ℝ))⁻¹) ^ (2 * d) :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _)
  calc ‖mCubeSum d X ν S F‖
      = ((S.card : ℝ))⁻¹ * (((Fintype.card X : ℝ))⁻¹) ^ (2 * d) *
        ‖∑ h : Fin d → X, ∑ h' : Fin d → X,
          ∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
            (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖ := by
        unfold mCubeSum
        simp only [norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
    _ ≤ ((S.card : ℝ))⁻¹ * (((Fintype.card X : ℝ))⁻¹) ^ (2 * d) *
        (((Fintype.card X : ℝ)) ^ d * (((Fintype.card X : ℝ)) ^ d * (S'.card : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum hc0
    _ ≤ (S'.card : ℝ) / (S.card : ℝ) := norm_arith_scaled S.card S'.card (Fintype.card X) d

/-- **A `1`-bounded function supported in `S'` has box power at most `|S'| / |S|`.**  This is the
*support-aware* form of `mCubeSum_norm_le_one`; the hypothesis `|S'| = |S|` of that statement is
replaced by the honest factor `|S'| / |S|` (the `ω = 0` corner of the cube forces the support of the
`x`-sum into a translate of `S'`, and the normalisation contributes `|S|⁻¹`). -/
theorem mCubeSum_le_one_scaled (d : ℕ) (X : Type) [Fintype X] (ν : Fin d → X → ℤ)
    (S S' : Finset ℤ) (g : ℤ → ℂ) (hS : S.card ≠ 0)
    (hsup : ∀ x : ℤ, x ∉ S' → g x = 0) (hbd : ∀ x : ℤ, ‖g x‖ ≤ 1) :
    ‖Work.Peluse.SwapC.mCubeSum d X ν S (fun _ => g)‖
      ≤ ((S'.card : ℝ)) / ((S.card : ℝ)) :=
  mCubeSum_le_gen d X ν S S' (fun _ => g)
    (fun _ x hx => hsup x hx) (fun _ x => hbd x)

end

end Work.Peluse.SwapC
