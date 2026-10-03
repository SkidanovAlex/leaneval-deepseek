import Mathlib
import Submission.Work.Peluse.SwapC.Basic

open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-! ## Auxiliary lemmas

The proof is the multiset-slot analogue of the workspace's proved
`Work.Peluse.BoxNorm.boxNormPow_le_one`, but phrased for the abstract multiset box sum
`mCubeSum d X ν S F` (arbitrary finite index type `X` and direction map `ν`), of which
`pboxSum` is the instance `X = Fin M × Fin M`, `ν k m = pdir (q₁ k) (q₂ k) m`.
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

/-- For fixed increments the sum over the lower corner `x` of the cube term is bounded by `|S|`:
the `ω = 0` corner forces `x + ∑_k ν_k (h' k) ∈ S`. -/
private lemma norm_tsum_cubeTerm_le {d : ℕ} {X : Type} {ν : Fin d → X → ℤ}
    {S : Finset ℤ} {F : (Fin d → Bool) → ℤ → ℂ}
    (hbd : ∀ (ω : Fin d → Bool) (x : ℤ), ‖F ω x‖ ≤ 1)
    (hsup : ∀ (ω : Fin d → Bool) (x : ℤ), x ∉ S → F ω x = 0) (h h' : Fin d → X) :
    ‖∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
        (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖
      ≤ (S.card : ℝ) := by
  have hvanish : ∀ x : ℤ, x ∉ S.image (fun s => s - ∑ k : Fin d, ν k (h' k)) →
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
  rw [tsum_eq_sum (s := S.image (fun s => s - ∑ k : Fin d, ν k (h' k))) hvanish]
  calc ‖∑ x ∈ S.image (fun s => s - ∑ k : Fin d, ν k (h' k)),
        ∏ ω : Fin d → Bool, (star^[weight ω])
        (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖
      ≤ ∑ x ∈ S.image (fun s => s - ∑ k : Fin d, ν k (h' k)),
        ‖∏ ω : Fin d → Bool, (star^[weight ω])
        (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ S.image (fun s => s - ∑ k : Fin d, ν k (h' k)), (1 : ℝ) :=
        Finset.sum_le_sum (fun x _ => norm_cubeTerm_le hbd _ _ x)
    _ = ((S.image (fun s => s - ∑ k : Fin d, ν k (h' k))).card : ℝ) := by simp
    _ ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_image_le

/-- Normalisation arithmetic: `(n⁻¹ · (w⁻¹)^{2d}) · (w^d · (w^d · n)) ≤ 1`
(`= (n⁻¹n)(w⁻¹w)^{2d} ≤ 1`). -/
private lemma norm_arith (n w d : ℕ) :
    ((n : ℝ))⁻¹ * (((w : ℝ))⁻¹) ^ (2 * d) *
      (((w : ℝ)) ^ d * (((w : ℝ)) ^ d * (n : ℝ))) ≤ 1 := by
  have hw0 : (0 : ℝ) ≤ (w : ℝ) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hwi0 : 0 ≤ ((w : ℝ))⁻¹ := inv_nonneg.mpr hw0
  have hr_le : ((w : ℝ))⁻¹ * (w : ℝ) ≤ 1 := by
    rcases eq_or_ne (w : ℝ) 0 with h | h
    · rw [h]; simp
    · rw [inv_mul_cancel₀ h]
  have hr0 : 0 ≤ ((w : ℝ))⁻¹ * (w : ℝ) := mul_nonneg hwi0 hw0
  have hrd : (((w : ℝ))⁻¹ * (w : ℝ)) ^ d ≤ 1 := pow_le_one₀ hr0 hr_le
  have hrd' : (((w : ℝ))⁻¹) ^ d * ((w : ℝ)) ^ d ≤ 1 := by
    rw [← mul_pow]; exact hrd
  have hrd0 : 0 ≤ (((w : ℝ))⁻¹) ^ d * ((w : ℝ)) ^ d :=
    mul_nonneg (pow_nonneg hwi0 d) (pow_nonneg hw0 d)
  have hsq : ((((w : ℝ))⁻¹) ^ d * ((w : ℝ)) ^ d) *
      ((((w : ℝ))⁻¹) ^ d * ((w : ℝ)) ^ d) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hrd' hrd0
    calc ((((w : ℝ))⁻¹) ^ d * ((w : ℝ)) ^ d) * ((((w : ℝ))⁻¹) ^ d * ((w : ℝ)) ^ d)
        ≤ (((w : ℝ))⁻¹) ^ d * ((w : ℝ)) ^ d * 1 := h
      _ = (((w : ℝ))⁻¹) ^ d * ((w : ℝ)) ^ d := by ring
      _ ≤ 1 := hrd'
  have hn_le : ((n : ℝ))⁻¹ * (n : ℝ) ≤ 1 := by
    rcases eq_or_ne (n : ℝ) 0 with h | h
    · rw [h]; simp
    · rw [inv_mul_cancel₀ h]
  have hn0' : 0 ≤ ((n : ℝ))⁻¹ * (n : ℝ) := mul_nonneg (inv_nonneg.mpr hn0) hn0
  have heq : ((n : ℝ))⁻¹ * (((w : ℝ))⁻¹) ^ (2 * d) *
        (((w : ℝ)) ^ d * (((w : ℝ)) ^ d * (n : ℝ)))
      = (((n : ℝ))⁻¹ * (n : ℝ)) *
        (((((w : ℝ))⁻¹) ^ d * ((w : ℝ)) ^ d) *
         ((((w : ℝ))⁻¹) ^ d * ((w : ℝ)) ^ d)) := by
    rw [show 2 * d = d + d from by omega, pow_add]
    ring
  rw [heq]
  have hfin := mul_le_mul hn_le hsq (mul_nonneg hrd0 hrd0) (by norm_num : (0 : ℝ) ≤ 1)
  simpa using hfin

/-- **The multiset box sum of a `1`-bounded, `S`-supported family is at most `1`.**  Each cube term
has modulus `≤ 1`, and for fixed shifts it is supported in the translate
`S - ∑_k ν_k (h' k)` of `S`; the normalisation is `|S|⁻¹ · |X|^{-2d} · |X|^{2d}`. -/
private theorem mCubeSum_le_one (d : ℕ) (X : Type) [Fintype X] (ν : Fin d → X → ℤ)
    (S : Finset ℤ) (F : (Fin d → Bool) → ℤ → ℂ)
    (hsup : ∀ (ω : Fin d → Bool) (x : ℤ), x ∉ S → F ω x = 0)
    (hbd : ∀ (ω : Fin d → Bool) (x : ℤ), ‖F ω x‖ ≤ 1) :
    ‖mCubeSum d X ν S F‖ ≤ 1 := by
  have hterm : ∀ h h' : Fin d → X,
      ‖∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
        (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖
      ≤ (S.card : ℝ) := fun h h' => norm_tsum_cubeTerm_le hbd hsup h h'
  have hcard : ((Fintype.card (Fin d → X) : ℝ)) = ((Fintype.card X : ℝ)) ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hsum : ‖∑ h : Fin d → X, ∑ h' : Fin d → X,
        ∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
          (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖
      ≤ ((Fintype.card X : ℝ)) ^ d * (((Fintype.card X : ℝ)) ^ d * (S.card : ℝ)) := by
    have hinner : ∀ h : Fin d → X,
        ‖∑ h' : Fin d → X, ∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
            (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖
        ≤ (Fintype.card (Fin d → X) : ℝ) * (S.card : ℝ) := by
      intro h
      calc ‖∑ h' : Fin d → X, ∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
              (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖
          ≤ ∑ h' : Fin d → X, ‖∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
              (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _h' : Fin d → X, (S.card : ℝ) := Finset.sum_le_sum (fun h' _ => hterm h h')
        _ = (Fintype.card (Fin d → X) : ℝ) * (S.card : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    calc ‖∑ h : Fin d → X, ∑ h' : Fin d → X,
            ∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
              (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖
        ≤ ∑ h : Fin d → X, ‖∑ h' : Fin d → X, ∑' x : ℤ, ∏ ω : Fin d → Bool,
            (star^[weight ω])
              (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _h : Fin d → X, ((Fintype.card (Fin d → X) : ℝ) * (S.card : ℝ)) :=
          Finset.sum_le_sum (fun h _ => hinner h)
      _ = (Fintype.card (Fin d → X) : ℝ) *
          ((Fintype.card (Fin d → X) : ℝ) * (S.card : ℝ)) := by
          simp [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = ((Fintype.card X : ℝ)) ^ d * (((Fintype.card X : ℝ)) ^ d * (S.card : ℝ)) := by
          rw [hcard]
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
        (((Fintype.card X : ℝ)) ^ d * (((Fintype.card X : ℝ)) ^ d * (S.card : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum hc0
    _ ≤ 1 := norm_arith S.card (Fintype.card X) d

/-- A `1`-bounded function vanishing outside the normalising set `S` has `pbox ≤ 1`; the analogue
for the multiset slots of the workspace's proved `Work.Peluse.BoxNorm.boxNormPow_le_one`.

Each cube term has modulus `≤ 1` and, for fixed shifts, is supported in the translate
`S - ∑_k pdir (q₁ k) (q₂ k) (h' k)` of `S`, so the `x`-sum is `≤ |S|`; the normalisation is
`|S|⁻¹ · M^{-4d} · M^{4d} = 1`. -/
theorem pbox_le_one (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M : ℕ) (S : Finset ℤ) (f : ℤ → ℂ)
    (hsup : ∀ x : ℤ, x ∉ S → f x = 0) (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    Work.Peluse.LadderP.Swap.pbox d q₁ q₂ M S f ≤ 1 := by
  rw [pbox_eq_mCubeSum]
  exact mCubeSum_le_one d (Fin M × Fin M) (fun k m => pdir (q₁ k) (q₂ k) m)
    S (fun _ => f) (fun _ x hx => hsup x hx) (fun _ x => hbd x)

end

end Work.Peluse.SwapC
