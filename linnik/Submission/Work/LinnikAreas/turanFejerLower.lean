import Mathlib
import Submission.Work.LinnikAreas.TFDefs
import Submission.Work.LinnikAreas.aZAutocorr
import Submission.Work.LinnikAreas.fejerSq
import Submission.Work.LinnikAreas.doubleSum
import Submission.Work.LinnikAreas.summable_aZ_shift

namespace Work.LinnikAreas

open scoped BigOperators

/-! ### Expansion of `Cf^2 + Sf^2` -/

lemma CfSf_sq (r θ : ℝ) (N : ℕ) (p : ℤ) :
    Cf r θ N p ^ 2 + Sf r θ N p ^ 2
      = ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
          aZ r (p + k) * aZ r (p + l) * Real.cos (((k : ℝ) - (l : ℝ)) * θ) := by
  have hC : Cf r θ N p ^ 2
      = ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
          (aZ r (p + k) * Real.cos ((k : ℝ) * θ))
            * (aZ r (p + l) * Real.cos ((l : ℝ) * θ)) := by
    rw [Cf, pow_two, Finset.sum_mul_sum]
  have hS : Sf r θ N p ^ 2
      = ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
          (aZ r (p + k) * Real.sin ((k : ℝ) * θ))
            * (aZ r (p + l) * Real.sin ((l : ℝ) * θ)) := by
    rw [Sf, pow_two, Finset.sum_mul_sum]
  rw [hC, hS, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k hk
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro l hl
  rw [show ((k : ℝ) - (l : ℝ)) * θ = (k : ℝ) * θ - (l : ℝ) * θ by ring, Real.cos_sub]
  ring

/-! ### `tildea` in terms of the autocorrelation -/

lemma tildea_eq (r θ : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (m : ℤ) :
    tildea r θ m = (r * (1 - r) / (1 + r)) * Az r m * Real.cos ((m : ℝ) * θ) := by
  have h1r : (1 : ℝ) - r ≠ 0 := by linarith
  have h2r : (1 : ℝ) + r ≠ 0 := by positivity
  rw [tildea, Az, aZAutocorr r hr0 hr1 m]
  rcases eq_or_ne m 0 with hm | hm
  · subst hm
    rw [Int.natAbs_zero, pow_zero, if_pos rfl, if_pos rfl]
    have hc : Real.cos (((0 : ℤ) : ℝ) * θ) = 1 := by
      rw [show (((0 : ℤ) : ℝ) * θ) = 0 by ring, Real.cos_zero]
    rw [hc]
    simp only [mul_one]
    field_simp
    ring
  · rw [if_neg hm, if_neg hm]
    have hpow : r * r ^ (m.natAbs - 1) = r ^ m.natAbs := by
      nth_rewrite 1 [← pow_one r]
      rw [← pow_add, show 1 + (m.natAbs - 1) = m.natAbs by omega]
    have hsc : (r * (1 - r) / (1 + r)) * ((1 + r) * r ^ (m.natAbs - 1) / (1 - r))
        = r ^ m.natAbs := by
      rw [show (r * (1 - r) / (1 + r)) * ((1 + r) * r ^ (m.natAbs - 1) / (1 - r))
            = r * r ^ (m.natAbs - 1) by field_simp]
      exact hpow
    rw [hsc, sub_zero]

/-! ### Reindexing the autocorrelation -/

lemma Az_shift (r : ℝ) (k l : ℤ) :
    Az r (k - l) = ∑' p : ℤ, aZ r (p + k) * aZ r (p + l) := by
  rw [Az]
  rw [← Equiv.tsum_eq (Equiv.subRight l) (fun p : ℤ => aZ r (p + k) * aZ r (p + l))]
  apply tsum_congr
  intro c
  rw [show (Equiv.subRight l) c = c - l from rfl]
  rw [show c - l + k = c + (k - l) by ring]
  rw [show c - l + l = c by ring]

/-! ### Fubini over the shift `p` -/

lemma sum_cos_Az_eq (r θ : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
        Real.cos (((k : ℝ) - (l : ℝ)) * θ) * Az r ((k : ℤ) - (l : ℤ)))
      = ∑' p : ℤ, (Cf r θ N p ^ 2 + Sf r θ N p ^ 2) := by
  have hAz : ∀ k l : ℕ, Az r ((k : ℤ) - (l : ℤ))
      = ∑' p : ℤ, aZ r (p + k) * aZ r (p + l) := fun k l => Az_shift r (k : ℤ) (l : ℤ)
  simp_rw [hAz]
  simp_rw [← tsum_mul_left]
  rw [← Finset.sum_product (s := Finset.range N) (t := Finset.range N)
      (f := fun q : ℕ × ℕ => ∑' p : ℤ,
        Real.cos (((q.1 : ℝ) - (q.2 : ℝ)) * θ) * (aZ r (p + q.1) * aZ r (p + q.2)))]
  rw [(Summable.tsum_finsetSum (s := (Finset.range N) ×ˢ (Finset.range N))
      (f := fun q : ℕ × ℕ => fun p : ℤ =>
        Real.cos (((q.1 : ℝ) - (q.2 : ℝ)) * θ) * (aZ r (p + q.1) * aZ r (p + q.2))) ?_).symm]
  · apply tsum_congr
    intro p
    rw [Finset.sum_product (s := Finset.range N) (t := Finset.range N)
      (f := fun q : ℕ × ℕ =>
        Real.cos (((q.1 : ℝ) - (q.2 : ℝ)) * θ) * (aZ r (p + q.1) * aZ r (p + q.2)))]
    rw [CfSf_sq]
    apply Finset.sum_congr rfl; intro k hk
    apply Finset.sum_congr rfl; intro l hl
    ring
  · intro q hq
    simp only [Finset.mem_product] at hq
    exact Summable.mul_left _ (summable_aZ_shift r hr0 hr1 (q.1 : ℤ) (q.2 : ℤ))

/-! ### `tildea` on natural pairs -/

lemma tildea_nat (r θ : ℝ) (k l : ℕ) :
    tildea r θ ((k : ℤ) - (l : ℤ))
      = (if l ≤ k then r ^ (k - l) * Real.cos (((k - l : ℕ) : ℝ) * θ)
                     else r ^ (l - k) * Real.cos (((l - k : ℕ) : ℝ) * θ))
        - (if k = l then (1 - r) / (1 + r) else 0) := by
  rw [tildea]
  rcases le_or_gt l k with hl | hlt
  · have hcast : ((k : ℤ) - (l : ℤ)) = ((k - l : ℕ) : ℤ) := by
      rw [Nat.cast_sub hl]
    rw [hcast, Int.natAbs_natCast, if_pos hl]
    rw [show ((((k - l : ℕ) : ℤ)) : ℝ) = ((k - l : ℕ) : ℝ) by push_cast; try ring]
    by_cases hkl : k = l
    · subst hkl
      simp
    · have hne : ¬ (((k - l : ℕ) : ℤ) = 0) := by omega
      rw [if_neg hne, if_neg hkl]
  · have hcast : ((k : ℤ) - (l : ℤ)) = -(((l - k : ℕ)) : ℤ) := by
      rw [Nat.cast_sub (le_of_lt hlt)]; ring
    rw [hcast, Int.natAbs_neg, Int.natAbs_natCast, if_neg (not_le.mpr hlt)]
    have hne : ¬ ((-(((l - k : ℕ)) : ℤ)) = 0) := by omega
    rw [if_neg hne, if_neg (by omega : ¬ k = l)]
    push_cast
    rw [show -(((l - k : ℕ) : ℝ)) * θ = -((((l - k : ℕ) : ℝ)) * θ) by ring, Real.cos_neg]

/-! ### The double sum computes `N * (Kfun - c)` -/

lemma Kfun_double (r θ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * (Kfun r θ N - (1 - r) / (1 + r))
      = ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, tildea r θ ((k : ℤ) - (l : ℤ)) := by
  set g : ℕ → ℝ := fun m => r ^ m * Real.cos ((m : ℝ) * θ) with hgdef
  have h1 : ∀ k l : ℕ, tildea r θ ((k : ℤ) - (l : ℤ))
      = (if l ≤ k then g (k - l) else g (l - k)) - (if k = l then (1 - r) / (1 + r) else 0) :=
    fun k l => tildea_nat r θ k l
  have hsplit : (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, tildea r θ ((k : ℤ) - (l : ℤ)))
      = (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (if l ≤ k then g (k - l) else g (l - k)))
        - (N : ℝ) * ((1 - r) / (1 + r)) := by
    simp_rw [h1]
    have hinner : ∀ k : ℕ, (∑ l ∈ Finset.range N,
          ((if l ≤ k then g (k - l) else g (l - k)) - (if k = l then (1 - r) / (1 + r) else 0)))
        = (∑ l ∈ Finset.range N, (if l ≤ k then g (k - l) else g (l - k)))
          - ∑ l ∈ Finset.range N, (if k = l then (1 - r) / (1 + r) else 0) := by
      intro k; rw [Finset.sum_sub_distrib]
    simp_rw [hinner]
    rw [Finset.sum_sub_distrib]
    have hdiag : (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
          (if k = l then (1 - r) / (1 + r) else 0)) = (N : ℝ) * ((1 - r) / (1 + r)) := by
      have hd : ∀ k ∈ Finset.range N,
          (∑ l ∈ Finset.range N, (if k = l then (1 - r) / (1 + r) else 0))
            = (1 - r) / (1 + r) := by
        intro k hk
        rw [Finset.sum_ite_eq, if_pos hk]
      rw [Finset.sum_congr rfl hd, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hdiag]
  have hdouble : (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
        (if l ≤ k then g (k - l) else g (l - k)))
      = (N : ℝ) * g 0 + 2 * ∑ m ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - m) * g m := doubleSum g N
  have hg0 : g 0 = 1 := by simp [hgdef]
  have hK : Kfun r θ N = 1 + 2 * ∑ m ∈ Finset.Icc 1 (N - 1), (1 - (m : ℝ) / N) * g m := by
    rw [Kfun]
    have hs : (∑ m ∈ Finset.Icc 1 (N - 1), (1 - (m : ℝ) / N) * r ^ m * Real.cos ((m : ℝ) * θ))
        = ∑ m ∈ Finset.Icc 1 (N - 1), (1 - (m : ℝ) / N) * g m := by
      apply Finset.sum_congr rfl; intro m hm
      simp only [hgdef]; ring
    rw [hs]
  have hstep : ∀ m : ℕ, (N : ℝ) * ((1 - (m : ℝ) / N) * g m) = ((N : ℝ) - m) * g m := by
    intro m
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    rw [← mul_assoc, show (N : ℝ) * (1 - (m : ℝ) / N) = (N : ℝ) - m by
      rw [mul_sub, mul_one, ← mul_div_assoc, mul_div_cancel_left₀ _ hN0]]
  have hK2 : (N : ℝ) * (Kfun r θ N - (1 - r) / (1 + r))
      = (N : ℝ) * 1 + 2 * ∑ m ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - m) * g m
        - (N : ℝ) * ((1 - r) / (1 + r)) := by
    rw [hK]
    rw [show (N : ℝ) * (1 + 2 * ∑ m ∈ Finset.Icc 1 (N - 1), (1 - (m : ℝ) / N) * g m
          - (1 - r) / (1 + r))
        = (N : ℝ) * 1 + 2 * ((N : ℝ) * ∑ m ∈ Finset.Icc 1 (N - 1), (1 - (m : ℝ) / N) * g m)
          - (N : ℝ) * ((1 - r) / (1 + r)) by ring]
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun x hx => hstep x)]
  have hD : (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, tildea r θ ((k : ℤ) - (l : ℤ)))
      = (N : ℝ) * 1 + 2 * ∑ m ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - m) * g m
        - (N : ℝ) * ((1 - r) / (1 + r)) := by
    rw [hsplit, hdouble, hg0]
  rw [hK2, hD]

/-! ### Main identity -/

theorem main_id (r θ : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * (Kfun r θ N - (1 - r) / (1 + r))
      = (r * (1 - r) / (1 + r)) * ∑' p : ℤ, (Cf r θ N p ^ 2 + Sf r θ N p ^ 2) := by
  rw [Kfun_double r θ N hN]
  have htilde : ∀ k l : ℕ, tildea r θ ((k : ℤ) - (l : ℤ))
      = (r * (1 - r) / (1 + r))
        * (Real.cos (((k : ℝ) - (l : ℝ)) * θ) * Az r ((k : ℤ) - (l : ℤ))) := by
    intro k l
    rw [tildea_eq r θ hr0 hr1]
    push_cast
    ring
  simp_rw [htilde]
  have step : (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
        (r * (1 - r) / (1 + r)) * (Real.cos (((k : ℝ) - (l : ℝ)) * θ) * Az r ((k : ℤ) - (l : ℤ))))
      = (r * (1 - r) / (1 + r)) * ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
        (Real.cos (((k : ℝ) - (l : ℝ)) * θ) * Az r ((k : ℤ) - (l : ℤ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k hk
    rw [Finset.mul_sum]
  rw [step, sum_cos_Az_eq r θ hr0 hr1 N]

/-! ### The target -/

theorem turanFejerLower (J : ℕ) (hJ : 1 ≤ J) {r θ : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    -(r / (1 + r)) ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * r ^ j * Real.cos ((j : ℝ) * θ) := by
  have h1r : 0 < 1 + r := by linarith
  have hKfun : Kfun r θ (J + 1)
      = 1 + 2 * ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * r ^ j * Real.cos ((j : ℝ) * θ) := by
    rw [Kfun, Nat.add_sub_cancel]
    congr 1
    congr 1
    apply Finset.sum_congr rfl; intro j hj
    push_cast
    ring
  rcases lt_or_eq_of_le hr1 with hlt | heq
  · have h0 := main_id r θ hr hlt (J + 1) (by omega)
    have hnn : 0 ≤ ∑' p : ℤ, (Cf r θ (J + 1) p ^ 2 + Sf r θ (J + 1) p ^ 2) :=
      tsum_nonneg (fun p => by positivity)
    have hcoef : 0 ≤ r * (1 - r) / (1 + r) := by
      have h : 0 ≤ 1 - r := by linarith
      positivity
    have hprod : 0 ≤ (r * (1 - r) / (1 + r))
        * ∑' p : ℤ, (Cf r θ (J + 1) p ^ 2 + Sf r θ (J + 1) p ^ 2) :=
      mul_nonneg hcoef hnn
    have hkey : 0 ≤ ((J + 1 : ℕ) : ℝ) * (Kfun r θ (J + 1) - (1 - r) / (1 + r)) := by
      rw [h0]; exact hprod
    have hpos : (0 : ℝ) < ((J + 1 : ℕ) : ℝ) := by positivity
    have hmain : (1 - r) / (1 + r) ≤ Kfun r θ (J + 1) := by
      by_contra hcon
      have hcon' : Kfun r θ (J + 1) < (1 - r) / (1 + r) := not_le.mp hcon
      nlinarith [hkey]
    rw [hKfun] at hmain
    have hc1 : (1 - r) / (1 + r) - 1 = -2 * (r / (1 + r)) := by
      have h2 : (1 : ℝ) + r ≠ 0 := by positivity
      field_simp
      ring
    linarith
  · subst heq
    have h0 := fejerSq (J + 1) (by omega) θ
    rw [hKfun] at h0
    simp only [one_pow, mul_one] at h0 ⊢
    linarith

end Work.LinnikAreas
