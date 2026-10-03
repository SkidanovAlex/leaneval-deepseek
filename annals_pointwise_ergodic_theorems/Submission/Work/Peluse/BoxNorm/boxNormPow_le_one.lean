import Mathlib
import Submission.Work.Peluse.Basic

/-!
# The box norm of a `1`-bounded, finitely supported function is at most `1`

This module proves `boxNormPow_le_one`: if `f : ℤ → ℂ` is bounded by `1` and vanishes outside the
finite set `S`, then the `2 ^ t`-th power of its Gowers box norm,
`‖f‖_{□^t_{Q₁,…,Q_t}(S)}^{2^t}` (Peluse, Definition 2.1), is at most `1`.

The proof is the elementary one: each cube term has modulus at most `1` (it is a product of `2 ^ t`
terms of modulus at most `1`), and for fixed increments `(h, h')` the cube term as a function of the
lower corner `x` is supported in the translate `S - ∑ h'_i` of `S` (the `ω = 0` corner is
`x + ∑_i h'_i`, and `f` vanishes off `S`); hence the sum over `x` is at most `|S|`.  Summing over
the `∏_i |Q_i|` choices of `h` and of `h'` and dividing by the normalisation
`|S| · (∏_i |Q_i|)^2` of `prodCubeSum` gives the bound.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.BoxNorm

/-- The modulus is preserved by iterated conjugation. -/
private lemma norm_star_iterate (n : ℕ) (z : ℂ) : ‖(star^[n]) z‖ = ‖z‖ := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', norm_star, ih]

/-- A cube term is a product of `2 ^ t` terms of modulus at most `1`, hence has modulus at most
`1`. -/
private lemma norm_cubeTerm_le {t : ℕ} {f : ℤ → ℂ} (hf : ∀ x : ℤ, ‖f x‖ ≤ 1)
    (h h' : Fin t → ℤ) (x : ℤ) :
    ‖∏ ω : Fin t → Bool, (star^[weight ω]) (f (x + cornerShift h h' ω))‖ ≤ 1 := by
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun ω _ => norm_nonneg _) (fun ω _ => ?_)
  rw [norm_star_iterate]
  exact hf _

/-- For fixed increments the sum over the lower corner `x` of the cube term is bounded by `|S|`:
the `ω = 0` corner forces `x + ∑_i h'_i ∈ S`. -/
private lemma norm_tsum_cubeTerm_le {t : ℕ} {Q : Fin t → Finset ℤ} {S : Finset ℤ} {f : ℤ → ℂ}
    (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (hsupp : ∀ x : ℤ, x ∉ S → f x = 0)
    (h h' : (i : Fin t) → {x : ℤ // x ∈ Q i}) :
    ‖∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
        (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖ ≤ (S.card : ℝ) := by
  have hvanish : ∀ x : ℤ, x ∉ S.image (fun s => s - ∑ i : Fin t, (h' i).1) →
      (∏ ω : Fin t → Bool, (star^[weight ω])
        (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))) = 0 := by
    intro x hx
    refine Finset.prod_eq_zero (Finset.mem_univ (fun _ : Fin t => false)) ?_
    have hw : weight (fun _ : Fin t => false) = 0 := by simp [weight]
    have hc : cornerShift (fun i => (h i).1) (fun i => (h' i).1) (fun _ : Fin t => false)
        = ∑ i : Fin t, (h' i).1 := by simp [cornerShift]
    rw [hw, hc, Function.iterate_zero_apply]
    apply hsupp
    intro hxc
    exact hx (Finset.mem_image.mpr ⟨x + ∑ i : Fin t, (h' i).1, hxc, by ring⟩)
  rw [tsum_eq_sum (s := S.image (fun s => s - ∑ i : Fin t, (h' i).1)) hvanish]
  calc ‖∑ x ∈ S.image (fun s => s - ∑ i : Fin t, (h' i).1),
        ∏ ω : Fin t → Bool, (star^[weight ω])
        (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖
      ≤ ∑ x ∈ S.image (fun s => s - ∑ i : Fin t, (h' i).1),
        ‖∏ ω : Fin t → Bool, (star^[weight ω])
        (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ S.image (fun s => s - ∑ i : Fin t, (h' i).1), (1:ℝ) :=
        Finset.sum_le_sum (fun x _ => norm_cubeTerm_le hf _ _ x)
    _ = ((S.image (fun s => s - ∑ i : Fin t, (h' i).1)).card : ℝ) := by simp
    _ ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_image_le

/-- For natural numbers `a i`, the product of the inverse and the product of the numbers is at most
`1` (it is `1` when no `a i` vanishes, and `0` otherwise). -/
private lemma prod_inv_mul_prod_le_one {ι : Type*} [Fintype ι] (a : ι → ℕ) :
    (∏ i, ((a i : ℝ))⁻¹) * (∏ i, (a i : ℝ)) ≤ 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_one₀ (fun i _ => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)) (fun i _ => ?_)
  rcases eq_or_ne (a i) 0 with h | h
  · simp [h]
  · rw [inv_mul_cancel₀ (by exact_mod_cast h)]

/-- The normalisation arithmetic behind the bound: `(∏ aᵢ⁻¹)² · (∏ aᵢ)² · n / n ≤ 1`. -/
private lemma inv_prod_mul_self_mul_le {ι : Type*} [Fintype ι] (a : ι → ℕ) (n : ℕ) :
    (n : ℝ)⁻¹ * (∏ i, ((a i : ℝ))⁻¹) * (∏ i, ((a i : ℝ))⁻¹) *
      ((∏ i, (a i : ℝ)) * (∏ i, (a i : ℝ)) * (n : ℝ)) ≤ 1 := by
  have hPP : (∏ i, ((a i : ℝ))⁻¹) * (∏ i, (a i : ℝ)) ≤ 1 := prod_inv_mul_prod_le_one a
  have hPinv : 0 ≤ ∏ i, ((a i : ℝ))⁻¹ :=
    Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  have hP : 0 ≤ ∏ i, (a i : ℝ) := Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hnn : (n : ℝ)⁻¹ * (n : ℝ) ≤ 1 := by
    rcases eq_or_ne (n : ℝ) 0 with h | h
    · rw [h]; simp
    · rw [inv_mul_cancel₀ h]
  have h4 : 0 ≤ (∏ i, ((a i : ℝ))⁻¹) * (∏ i, (a i : ℝ)) := mul_nonneg hPinv hP
  have hb2 : ((∏ i, ((a i : ℝ))⁻¹) * (∏ i, (a i : ℝ))) *
      ((∏ i, ((a i : ℝ))⁻¹) * (∏ i, (a i : ℝ))) ≤ 1 := by
    simpa using mul_le_mul hPP hPP h4 (by norm_num : (0:ℝ) ≤ 1)
  rw [show (n : ℝ)⁻¹ * (∏ i, ((a i : ℝ))⁻¹) * (∏ i, ((a i : ℝ))⁻¹) *
        ((∏ i, (a i : ℝ)) * (∏ i, (a i : ℝ)) * (n : ℝ))
      = ((n : ℝ)⁻¹ * (n : ℝ)) *
        (((∏ i, ((a i : ℝ))⁻¹) * (∏ i, (a i : ℝ))) *
         ((∏ i, ((a i : ℝ))⁻¹) * (∏ i, (a i : ℝ)))) by ring]
  simpa using mul_le_mul hnn hb2 (mul_nonneg h4 h4) (by norm_num : (0:ℝ) ≤ 1)

theorem boxNormPow_le_one {t : ℕ} {Q : Fin t → Finset ℤ} {S : Finset ℤ} {f : ℤ → ℂ}
    (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (hsupp : ∀ x : ℤ, x ∉ S → f x = 0) :
    Work.Peluse.boxNormPow t Q S f ≤ 1 := by
  have hterm : ∀ h h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
      ‖∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
        (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖ ≤ (S.card : ℝ) :=
    fun h h' => norm_tsum_cubeTerm_le hf hsupp h h'
  have hcard : ((Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i})) : ℝ) =
      ∏ i : Fin t, ((Q i).card : ℝ) := by
    simp only [Fintype.card_pi, Fintype.card_coe, Nat.cast_prod]
  have hsum : ‖∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
          (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖
      ≤ (∏ i : Fin t, ((Q i).card : ℝ)) * (∏ i : Fin t, ((Q i).card : ℝ)) * (S.card : ℝ) := by
    have hinner : ∀ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ‖∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
          ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
            (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖
        ≤ (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) * (S.card : ℝ) := by
      intro h
      calc ‖∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
            ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
              (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖
          ≤ ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
            ‖∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
              (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖ := norm_sum_le _ _
        _ ≤ ∑ _h' : (i : Fin t) → {x : ℤ // x ∈ Q i}, (S.card : ℝ) :=
            Finset.sum_le_sum (fun h' _ => hterm h h')
        _ = (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) * (S.card : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    calc ‖∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
          ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
          ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
            (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖
        ≤ ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
          ‖∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
            ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
              (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖ := norm_sum_le _ _
      _ ≤ ∑ _h : (i : Fin t) → {x : ℤ // x ∈ Q i},
          ((Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) * (S.card : ℝ)) :=
          Finset.sum_le_sum (fun h _ => hinner h)
      _ = (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) *
          ((Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) * (S.card : ℝ)) := by
          simp [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = (∏ i : Fin t, ((Q i).card : ℝ)) * (∏ i : Fin t, ((Q i).card : ℝ)) * (S.card : ℝ) := by
          rw [← hcard]; ring
  have hAnorm : ‖(∏ i : Fin t, ((Q i).card : ℂ)⁻¹)‖ = ∏ i : Fin t, ((Q i).card : ℝ)⁻¹ := by
    rw [norm_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [norm_inv, Complex.norm_natCast]
  unfold Work.Peluse.boxNormPow Work.Peluse.boxSumPow Work.Peluse.prodCubeSum
  set R : ℂ := ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
      ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
      ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
        (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)) with hRdef
  have hR : ‖R‖ ≤ (∏ i : Fin t, ((Q i).card : ℝ)) * (∏ i : Fin t, ((Q i).card : ℝ)) *
      (S.card : ℝ) := by
    rw [hRdef]; exact hsum
  calc ‖((S.card : ℂ))⁻¹ * (∏ i : Fin t, ((Q i).card : ℂ)⁻¹) *
        (∏ i : Fin t, ((Q i).card : ℂ)⁻¹) * R‖
      = ‖((S.card : ℂ))⁻¹‖ * ‖(∏ i : Fin t, ((Q i).card : ℂ)⁻¹)‖ *
        ‖(∏ i : Fin t, ((Q i).card : ℂ)⁻¹)‖ * ‖R‖ := by rw [norm_mul, norm_mul, norm_mul]
    _ = ((S.card : ℝ))⁻¹ * (∏ i : Fin t, ((Q i).card : ℝ)⁻¹) *
        (∏ i : Fin t, ((Q i).card : ℝ)⁻¹) * ‖R‖ := by
        rw [hAnorm, norm_inv, Complex.norm_natCast]
    _ ≤ ((S.card : ℝ))⁻¹ * (∏ i : Fin t, ((Q i).card : ℝ)⁻¹) *
        (∏ i : Fin t, ((Q i).card : ℝ)⁻¹) *
        ((∏ i : Fin t, ((Q i).card : ℝ)) * (∏ i : Fin t, ((Q i).card : ℝ)) *
          (S.card : ℝ)) := by
        refine mul_le_mul_of_nonneg_left hR ?_
        exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
          (Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg _))))
          (Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg _)))
    _ ≤ 1 := inv_prod_mul_self_mul_le (fun i : Fin t => (Q i).card) S.card

end Work.Peluse.BoxNorm
