import Mathlib
import Submission.Work.Peluse.SwapE.Defs

/-!
# `PboxLeOne` — the multiset box sum is at most one

`pboxSum d q₁ q₂ M S f` is `(S.card)⁻¹ * ((M⁴)⁻¹)^d` times the double sum, over the `M^{4d}` pairs
`(h, h')` of slot points, of the cube term

`∑' x, ∏ ω : Fin d → Bool, (star^[weight ω]) (f (x + cornerShift H H' ω))`

along the increments `H k = pdir (q₁ k) (q₂ k) (h k)`, `H' k = pdir (q₁ k) (q₂ k) (h' k)`.

The proof is the elementary one, identical in structure to
`Submission/Work/Peluse/BoxNorm/boxNormPow_le_one.lean`:

* each cube term is a product of `2 ^ d` terms of modulus at most `1`, hence has modulus at most `1`
  (`norm_prod`, `‖star^[n] z‖ = ‖z‖`);
* for fixed increments, the `ω = 0` factor is `f (x + ∑_k H'_k)`, so the integrand vanishes for
  `x ∉ S.image (fun s => s - ∑_k H'_k)`; replacing the `tsum` by that finite sum and bounding each
  term by `1` gives `‖∑' x, …‖ ≤ #(S.image …) ≤ S.card`;
* the double sum over the `M^{2d}` choices of `h` and the `M^{2d}` choices of `h'` is therefore at
  most `M^{2d} * (M^{2d} * S.card) = M^{4d} * S.card`, and the normalisation
  `(S.card)⁻¹ * (M^{4d})⁻¹` cancels it exactly.

Nothing here is specific to the multiset slots: the increments are arbitrary integers, so the two
private lemmas below are the general single-cube-term bounds for a `1`-bounded function supported in
a finite set.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapE

open Work.Peluse
open Work.Peluse.LadderP.Swap

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
  exact Finset.prod_le_one₀ (fun ω _ => norm_nonneg _)
    (fun ω _ => by rw [norm_star_iterate]; exact hf _)

/-- For fixed increments the sum over the lower corner `x` of the cube term is bounded by `|S|`:
the `ω = 0` corner is `x + ∑_i h'_i`, so the summand vanishes unless `x ∈ S - ∑_i h'_i`. -/
private lemma norm_tsum_cubeTerm_le {t : ℕ} {S : Finset ℤ} {f : ℤ → ℂ}
    (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (hsupp : ∀ x : ℤ, x ∉ S → f x = 0)
    (h h' : Fin t → ℤ) :
    ‖∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω]) (f (x + cornerShift h h' ω))‖
      ≤ (S.card : ℝ) := by
  have hvanish : ∀ x : ℤ, x ∉ S.image (fun s => s - ∑ i : Fin t, h' i) →
      (∏ ω : Fin t → Bool, (star^[weight ω]) (f (x + cornerShift h h' ω))) = 0 := by
    intro x hx
    refine Finset.prod_eq_zero (Finset.mem_univ (fun _ : Fin t => false)) ?_
    have hw : weight (fun _ : Fin t => false) = 0 := by simp [weight]
    have hc : cornerShift h h' (fun _ : Fin t => false) = ∑ i : Fin t, h' i := by
      simp [cornerShift]
    rw [hw, hc, Function.iterate_zero_apply]
    exact hsupp _ (fun hxc => hx (Finset.mem_image.mpr ⟨x + ∑ i : Fin t, h' i, hxc, by ring⟩))
  rw [tsum_eq_sum (s := S.image (fun s => s - ∑ i : Fin t, h' i)) hvanish]
  calc ‖∑ x ∈ S.image (fun s => s - ∑ i : Fin t, h' i),
        ∏ ω : Fin t → Bool, (star^[weight ω]) (f (x + cornerShift h h' ω))‖
      ≤ ∑ x ∈ S.image (fun s => s - ∑ i : Fin t, h' i),
        ‖∏ ω : Fin t → Bool, (star^[weight ω]) (f (x + cornerShift h h' ω))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _x ∈ S.image (fun s => s - ∑ i : Fin t, h' i), (1 : ℝ) :=
        Finset.sum_le_sum (fun x _ => norm_cubeTerm_le hf h h' x)
    _ = ((S.image (fun s => s - ∑ i : Fin t, h' i)).card : ℝ) := by simp
    _ ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_image_le

/-- `((m^4)⁻¹)^d * (m^2)^d * (m^2)^d = 1` for `m ≠ 0` — the normalisation arithmetic of the proof
(here `(m*m)^d = (m^2)^d`). -/
private lemma inv_pow_four_mul_pow (m : ℝ) (hm : m ≠ 0) (d : ℕ) :
    ((m^4)⁻¹)^d * ((m*m)^d * ((m*m)^d)) = 1 := by
  rw [← mul_pow, ← mul_pow, show (m*m) * (m*m) = m^4 by ring,
      inv_mul_cancel₀ (pow_ne_zero 4 hm), one_pow]

/-- **`PboxLeOne`** — for `f` supported in `symIcc N` and bounded by `1`, the value of `pbox` is at
most `1`.

Proof sketch.  `pboxSum` is `(S.card)⁻¹ * (M⁴)⁻¹^d` times a sum of `M^{4d}` terms, each of the form
`∑' x, ∏ ω, (star^[weight ω]) (f (x + cornerShift … ω))`.  In such a term the `ω = 0` factor is
`f (x + ∑_k H'_k)`, so the integrand is supported in the translate `symIcc N - ∑_k H'_k` of
`symIcc N`; pointwise it has norm at most `1` (each factor is a value of `f` up to conjugation),
hence `‖∑' x, …‖ ≤ (symIcc N).card = 2N+1`.  Multiplying by `(2N+1)⁻¹` and averaging over the
`M^{4d}` index pairs gives `‖pboxSum‖ ≤ 1`.
The sibling `Submission/Work/Peluse/BoxNorm/boxNormPow_le_one.lean`
(`norm_tsum_cubeTerm_le`, `norm_cubeTerm_le`) is the same argument for the non-multiset box sum. -/
theorem pboxLeOne : Work.Peluse.SwapE.PboxLeOne := by
  intro d q₁ q₂ M N f hM hsupp hf
  -- `f` vanishes off `symIcc N`
  have hsupp' : ∀ x : ℤ, x ∉ symIcc N → f x = 0 := by
    intro x hx
    refine hsupp x ?_
    have hx' : x < -(N : ℤ) ∨ (N : ℤ) < x := by
      have h := hx
      rw [symIcc, Finset.mem_Icc] at h
      omega
    rcases hx' with h | h
    · have h1 : (N : ℤ) < -x := by omega
      have h2 : (-x : ℤ) ≤ ((-x).natAbs : ℤ) := Int.le_natAbs
      have h3 : (N : ℤ) < ((-x).natAbs : ℤ) := lt_of_lt_of_le h1 h2
      have h4 : N < (-x).natAbs := by exact_mod_cast h3
      rwa [Int.natAbs_neg] at h4
    · have h2 : x ≤ (x.natAbs : ℤ) := Int.le_natAbs
      exact_mod_cast (lt_of_lt_of_le h h2)
  -- the single cube term
  have hterm : ∀ h h' : Fin d → Fin M × Fin M,
      ‖∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
        (f (x + cornerShift (fun k => pdir (q₁ k) (q₂ k) (h k))
                            (fun k => pdir (q₁ k) (q₂ k) (h' k)) ω))‖
        ≤ ((symIcc N).card : ℝ) :=
    fun h h' => norm_tsum_cubeTerm_le hf hsupp' (fun k => pdir (q₁ k) (q₂ k) (h k))
      (fun k => pdir (q₁ k) (q₂ k) (h' k))
  -- there are `M^{2d}` slot points in each of the two slots
  have hcard : (Fintype.card (Fin d → Fin M × Fin M) : ℝ) = ((M : ℝ) * (M : ℝ))^d := by
    rw [Fintype.card_pi]
    simp [Fintype.card_prod]
  -- the double sum over the slot points
  have hsum : ‖∑ h : Fin d → Fin M × Fin M, ∑ h' : Fin d → Fin M × Fin M,
        ∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
          (f (x + cornerShift (fun k => pdir (q₁ k) (q₂ k) (h k))
                              (fun k => pdir (q₁ k) (q₂ k) (h' k)) ω))‖
      ≤ ((M : ℝ) * (M : ℝ))^d * (((M : ℝ) * (M : ℝ))^d * ((symIcc N).card : ℝ)) := by
    calc ‖∑ h : Fin d → Fin M × Fin M, ∑ h' : Fin d → Fin M × Fin M,
          ∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
            (f (x + cornerShift (fun k => pdir (q₁ k) (q₂ k) (h k))
                                (fun k => pdir (q₁ k) (q₂ k) (h' k)) ω))‖
        ≤ ∑ h : Fin d → Fin M × Fin M,
          ‖∑ h' : Fin d → Fin M × Fin M,
            ∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
              (f (x + cornerShift (fun k => pdir (q₁ k) (q₂ k) (h k))
                                  (fun k => pdir (q₁ k) (q₂ k) (h' k)) ω))‖ := norm_sum_le _ _
      _ ≤ ∑ _h : Fin d → Fin M × Fin M,
          ((Fintype.card (Fin d → Fin M × Fin M) : ℝ) * ((symIcc N).card : ℝ)) := by
          refine Finset.sum_le_sum (fun h _ => ?_)
          calc ‖∑ h' : Fin d → Fin M × Fin M,
                ∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
                  (f (x + cornerShift (fun k => pdir (q₁ k) (q₂ k) (h k))
                                      (fun k => pdir (q₁ k) (q₂ k) (h' k)) ω))‖
              ≤ ∑ h' : Fin d → Fin M × Fin M,
                ‖∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
                  (f (x + cornerShift (fun k => pdir (q₁ k) (q₂ k) (h k))
                                      (fun k => pdir (q₁ k) (q₂ k) (h' k)) ω))‖ :=
                norm_sum_le _ _
            _ ≤ ∑ _h' : Fin d → Fin M × Fin M, ((symIcc N).card : ℝ) :=
                Finset.sum_le_sum (fun h' _ => hterm h h')
            _ = (Fintype.card (Fin d → Fin M × Fin M) : ℝ) * ((symIcc N).card : ℝ) := by
                simp [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = ((M : ℝ) * (M : ℝ))^d * (((M : ℝ) * (M : ℝ))^d * ((symIcc N).card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
  -- the normalisation cancels the count
  unfold pbox pboxSum
  set R : ℂ := ∑ h : Fin d → Fin M × Fin M, ∑ h' : Fin d → Fin M × Fin M,
      ∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
        (f (x + cornerShift (fun k => pdir (q₁ k) (q₂ k) (h k))
                            (fun k => pdir (q₁ k) (q₂ k) (h' k)) ω)) with hR
  have hRl : ‖R‖ ≤ ((M : ℝ) * (M : ℝ))^d *
      (((M : ℝ) * (M : ℝ))^d * ((symIcc N).card : ℝ)) := hsum
  calc ‖((symIcc N).card : ℂ)⁻¹ * (((M : ℂ) ^ 4)⁻¹) ^ d * R‖
      = ((symIcc N).card : ℝ)⁻¹ * (((M : ℝ)^4)⁻¹)^d * ‖R‖ := by
        rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast, norm_pow, norm_inv, norm_pow,
            Complex.norm_natCast]
    _ ≤ ((symIcc N).card : ℝ)⁻¹ * (((M : ℝ)^4)⁻¹)^d *
        (((M : ℝ) * (M : ℝ))^d * (((M : ℝ) * (M : ℝ))^d * ((symIcc N).card : ℝ))) := by
        refine mul_le_mul_of_nonneg_left hRl ?_
        exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
          (pow_nonneg (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg M) 4)) d)
    _ = 1 := by
        have hm : (M : ℝ) ≠ 0 := by positivity
        have hs : ((symIcc N).card : ℝ) ≠ 0 := by
          have : 0 < (symIcc N).card := Finset.card_pos.mpr ⟨0, by simp [symIcc]⟩
          positivity
        rw [show ((symIcc N).card : ℝ)⁻¹ * (((M : ℝ)^4)⁻¹)^d *
              (((M : ℝ) * (M : ℝ))^d * (((M : ℝ) * (M : ℝ))^d * ((symIcc N).card : ℝ)))
            = (((symIcc N).card : ℝ)⁻¹ * ((symIcc N).card : ℝ)) *
              ((((M : ℝ)^4)⁻¹)^d * (((M : ℝ) * (M : ℝ))^d * ((M : ℝ) * (M : ℝ))^d)) by ring]
        rw [inv_mul_cancel₀ hs, one_mul, inv_pow_four_mul_pow (M : ℝ) hm d]

end Work.Peluse.SwapE
