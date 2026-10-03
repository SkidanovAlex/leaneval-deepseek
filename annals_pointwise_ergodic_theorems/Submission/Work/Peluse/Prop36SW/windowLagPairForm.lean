import Mathlib
import Submission.Work.Peluse.TransferUp.window_pair_sum
import Submission.Work.Peluse.Prop36SW.windowLagShiftReindex
import Submission.Work.Peluse.Prop36SW.windowLagWindowReindex

/-!
# The window-lag pair form of the level-one `ℓ²` mass

For `f : ℤ → ℂ` supported in `[-M, M]` and `K ≥ 2M + 1` we compute the `ℓ²`-mass of the `K`-window
sums `W x = ∑_{1 ≤ y ≤ K} f (x + y)`:

`∑_{|x| ≤ M+K} ‖W x‖² = K ‖Σ‖² - ∑_{y,k ∈ [-M,M]} |y - k| · Re (f y · conj (f k))`,
where `Σ = ∑_{y ∈ [-M,M]} f y`.

The mechanism: `‖W x‖² = W x · conj (W x)` expands over the pairs `(y,y') ∈ [1,K]²`, the shift
`u = x + y` turns each pair-sum into the autocorrelation `∑_u f u · conj (f (u + (y'-y)))`, and the
number of pairs `(y,y') ∈ [1,K]²` realising a given difference `m = y' - y` is `K - |m|`
(`Work.Peluse.TransferUp.window_pair_sum`).  Because `|y - k| ≤ 2M ≤ K - 1` for every pair in the
support, the triangular weight `K - |k - y|` survives intact, and the sum reorganises into the
pair form with the `|y - k|` weight and the top-degree term `K ‖Σ‖²`.

This is the exact identity behind Peluse's first box-norm collapse `uNormPow_one_collapse`
(the `T_K = K‖Σ‖² - PF` step), and the source of the sharp bound `PF ≤ M ‖Σ‖²`.
-/

namespace Work.Peluse.Prop36SW

open scoped BigOperators

/-- Membership in the symmetric interval `symIcc L` is the condition `natAbs ≤ L`. -/
private lemma mem_symIcc_iff {L : ℕ} {x : ℤ} : x ∈ Work.Peluse.symIcc L ↔ x.natAbs ≤ L := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h : |x| ≤ (L : ℤ) := abs_le.mpr ⟨h1, h2⟩
    have h' : ((x.natAbs : ℕ) : ℤ) ≤ (L : ℤ) := by simpa only [Int.natCast_natAbs] using h
    exact_mod_cast h'
  · intro h
    have h' : |x| ≤ (L : ℤ) := by
      have h'' : ((x.natAbs : ℕ) : ℤ) ≤ (L : ℤ) := by exact_mod_cast h
      simpa only [Int.natCast_natAbs] using h''
    exact abs_le.mp h'

/-- **Expansion of the window mass.**  The `ℓ²`-mass of the window sums is the real part of the
double sum over the pairs `(y,y')` of the window: `‖W x‖² = W x · conj (W x)`. -/
private lemma windowSum_sq_expand {M K : ℕ} {f : ℤ → ℂ} :
    (∑ x ∈ Work.Peluse.symIcc (M + K), ‖∑ y ∈ Finset.Icc 1 K, f (x + (y : ℤ))‖ ^ 2)
      = (∑ x ∈ Work.Peluse.symIcc (M + K), ∑ y ∈ Finset.Icc 1 K, ∑ y' ∈ Finset.Icc 1 K,
            f (x + (y : ℤ)) * star (f (x + (y' : ℤ)))).re := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have h1 : (∑ y ∈ Finset.Icc 1 K, f (x + (y : ℤ))) * star (∑ y ∈ Finset.Icc 1 K, f (x + (y : ℤ)))
      = ∑ y ∈ Finset.Icc 1 K, ∑ y' ∈ Finset.Icc 1 K,
          f (x + (y : ℤ)) * star (f (x + (y' : ℤ))) := by
    rw [star_sum, Finset.sum_mul_sum]
  rw [← h1, ← Complex.normSq_eq_norm_sq, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

/-- **The final real algebra.**  Since `|k - y| ≤ 2M ≤ K - 1` for `y, k ∈ [-M, M]`, the triangular
weight `K - |k - y|` splits as `K - |k - y|` and the double sum reorganises into the pair form. -/
private lemma pairForm_alg {M K : ℕ} (hK : 2 * M + 1 ≤ K) (f : ℤ → ℂ) :
    (∑ y ∈ Work.Peluse.symIcc M, ∑ k ∈ Work.Peluse.symIcc M,
        (((K - (k - y).natAbs : ℕ)) : ℝ) * (f y * star (f k)).re)
      = (K : ℝ) * ‖∑ y ∈ Work.Peluse.symIcc M, f y‖ ^ 2
        - ∑ y ∈ Work.Peluse.symIcc M, ∑ k ∈ Work.Peluse.symIcc M,
            (((y - k).natAbs : ℝ)) * (f y * star (f k)).re := by
  have hb : ∀ y ∈ Work.Peluse.symIcc M, ∀ k ∈ Work.Peluse.symIcc M, (k - y).natAbs ≤ K := by
    intro y hy k hk
    have hy' := mem_symIcc_iff.mp hy
    have hk' := mem_symIcc_iff.mp hk
    have h1 : (k - y).natAbs ≤ k.natAbs + y.natAbs := Int.natAbs_sub_le k y
    omega
  have hR : (∑ y ∈ Work.Peluse.symIcc M, ∑ k ∈ Work.Peluse.symIcc M,
      (f y * star (f k)).re) = ‖∑ y ∈ Work.Peluse.symIcc M, f y‖ ^ 2 := by
    have h2 : (∑ y ∈ Work.Peluse.symIcc M, ∑ k ∈ Work.Peluse.symIcc M,
        (f y * star (f k)).re)
        = (∑ y ∈ Work.Peluse.symIcc M, ∑ k ∈ Work.Peluse.symIcc M,
            f y * star (f k)).re := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Complex.re_sum]
    have h1 : (∑ y ∈ Work.Peluse.symIcc M, ∑ k ∈ Work.Peluse.symIcc M,
        f y * star (f k))
        = (∑ y ∈ Work.Peluse.symIcc M, f y) * star (∑ y ∈ Work.Peluse.symIcc M, f y) := by
      rw [star_sum, Finset.sum_mul_sum]
    have h3 : ((∑ y ∈ Work.Peluse.symIcc M, f y) * star (∑ y ∈ Work.Peluse.symIcc M, f y)).re
        = ‖∑ y ∈ Work.Peluse.symIcc M, f y‖ ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [h2, h1, h3]
  have hterm : ∀ y ∈ Work.Peluse.symIcc M, ∀ k ∈ Work.Peluse.symIcc M,
      (((K - (k - y).natAbs : ℕ)) : ℝ) * (f y * star (f k)).re
        = (K : ℝ) * (f y * star (f k)).re - (((k - y).natAbs : ℝ)) * (f y * star (f k)).re := by
    intro y hy k hk
    rw [Nat.cast_sub (hb y hy k hk)]
    ring
  have hsym : ∀ y k : ℤ, (k - y).natAbs = (y - k).natAbs := by
    intro y k
    rw [show y - k = -(k - y) by ring, Int.natAbs_neg]
  have hinter : ∀ y, (∑ k ∈ Work.Peluse.symIcc M,
      ((K : ℝ) * (f y * star (f k)).re - (((k - y).natAbs : ℝ)) * (f y * star (f k)).re))
      = (∑ k ∈ Work.Peluse.symIcc M, (K : ℝ) * (f y * star (f k)).re)
        - ∑ k ∈ Work.Peluse.symIcc M, (((k - y).natAbs : ℝ)) * (f y * star (f k)).re :=
    fun y => Finset.sum_sub_distrib (s := Work.Peluse.symIcc M)
      (f := fun k => (K : ℝ) * (f y * star (f k)).re)
      (g := fun k => (((k - y).natAbs : ℝ)) * (f y * star (f k)).re)
  calc (∑ y ∈ Work.Peluse.symIcc M, ∑ k ∈ Work.Peluse.symIcc M,
        (((K - (k - y).natAbs : ℕ)) : ℝ) * (f y * star (f k)).re)
      = ∑ y ∈ Work.Peluse.symIcc M, ∑ k ∈ Work.Peluse.symIcc M,
          ((K : ℝ) * (f y * star (f k)).re - (((k - y).natAbs : ℝ)) * (f y * star (f k)).re) := by
        refine Finset.sum_congr rfl (fun y hy => Finset.sum_congr rfl (fun k hk => ?_))
        exact hterm y hy k hk
    _ = (K : ℝ) * (∑ y ∈ Work.Peluse.symIcc M, ∑ k ∈ Work.Peluse.symIcc M,
          (f y * star (f k)).re)
        - ∑ y ∈ Work.Peluse.symIcc M, ∑ k ∈ Work.Peluse.symIcc M,
            (((k - y).natAbs : ℝ)) * (f y * star (f k)).re := by
        simp only [hinter, Finset.mul_sum]
        rw [Finset.sum_sub_distrib]
    _ = (K : ℝ) * ‖∑ y ∈ Work.Peluse.symIcc M, f y‖ ^ 2
        - ∑ y ∈ Work.Peluse.symIcc M, ∑ k ∈ Work.Peluse.symIcc M,
            (((y - k).natAbs : ℝ)) * (f y * star (f k)).re := by
        rw [hR]
        congr 1
        refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun k _ => ?_))
        rw [hsym k y]

theorem windowLagPairForm {M K : ℕ} {f : ℤ → ℂ} (hsup : Work.Peluse.SupportIn f M)
    (hK : 2 * M + 1 ≤ K) :
    (∑ x ∈ Work.Peluse.symIcc (M + K), ‖∑ y ∈ Finset.Icc 1 K, f (x + (y : ℤ))‖ ^ 2)
      = (K : ℝ) * ‖∑ y ∈ Work.Peluse.symIcc M, f y‖ ^ 2
        - ∑ y ∈ Work.Peluse.symIcc M, ∑ k ∈ Work.Peluse.symIcc M,
            (((y - k).natAbs : ℝ)) * (f y * star (f k)).re := by
  -- the outer sums over `[1,K]` are rewritten as sums over the difference `m = y' - y`
  have hre : (∑ x ∈ Work.Peluse.symIcc (M + K), ∑ y ∈ Finset.Icc 1 K, ∑ y' ∈ Finset.Icc 1 K,
        f (x + (y : ℤ)) * star (f (x + (y' : ℤ))))
      = ∑ y ∈ Finset.Icc 1 K, ∑ y' ∈ Finset.Icc 1 K,
          ∑ u ∈ Work.Peluse.symIcc M, f u * star (f (u + ((y' : ℤ) - (y : ℤ)))) := by
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y' hy' => ?_)
    exact windowLagShiftReindex hsup (by have := (Finset.mem_Icc.mp hy).1; exact_mod_cast this)
      (by have := (Finset.mem_Icc.mp hy).2; exact_mod_cast this)
  -- the triangular weight `K - |m|`
  have hT : (∑ y ∈ Finset.Icc 1 K, ∑ y' ∈ Finset.Icc 1 K,
        ∑ u ∈ Work.Peluse.symIcc M, f u * star (f (u + ((y' : ℤ) - (y : ℤ)))))
      = ∑ m ∈ Finset.Icc (-(K : ℤ) + 1) ((K : ℤ) - 1),
          (((K - m.natAbs : ℕ)) : ℂ) * ∑ u ∈ Work.Peluse.symIcc M, f u * star (f (u + m)) := by
    exact Work.Peluse.TransferUp.window_pair_sum K
      (fun m => ∑ u ∈ Work.Peluse.symIcc M, f u * star (f (u + m)))
  -- reindex the pair `(m,u)` by `(y,k) = (u, u+m)`
  have hW : (∑ m ∈ Finset.Icc (-(K : ℤ) + 1) ((K : ℤ) - 1),
        (((K - m.natAbs : ℕ)) : ℂ) * ∑ u ∈ Work.Peluse.symIcc M, f u * star (f (u + m)))
      = ∑ y ∈ Work.Peluse.symIcc M, ∑ k ∈ Work.Peluse.symIcc M,
          (((K - (k - y).natAbs : ℕ)) : ℂ) * (f y * star (f k)) := by
    simp only [Finset.mul_sum]
    have hF : ∀ m u : ℤ, u + m ∉ Work.Peluse.symIcc M →
        (((K - m.natAbs : ℕ)) : ℂ) * (f u * star (f (u + m))) = 0 := by
      intro m u hmem
      have : M < (u + m).natAbs := by
        by_contra h
        exact hmem (mem_symIcc_iff.mpr (not_lt.mp h))
      rw [hsup (u + m) this, star_zero, mul_zero, mul_zero]
    have hthis := windowLagWindowReindex hK
      (fun m u => (((K - m.natAbs : ℕ)) : ℂ) * (f u * star (f (u + m)))) hF
    refine hthis.trans ?_
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [show y + (k - y) = k by ring]
  -- take real parts
  have hre2 : (∑ y ∈ Work.Peluse.symIcc M, ∑ k ∈ Work.Peluse.symIcc M,
        (((K - (k - y).natAbs : ℕ)) : ℂ) * (f y * star (f k))).re
      = ∑ y ∈ Work.Peluse.symIcc M, ∑ k ∈ Work.Peluse.symIcc M,
          (((K - (k - y).natAbs : ℕ)) : ℝ) * (f y * star (f k)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show (((K - (k - y).natAbs : ℕ)) : ℂ)
          = ((((K - (k - y).natAbs : ℕ)) : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
  rw [windowSum_sq_expand (M := M) (K := K) (f := f), hre, hT, hW, hre2, pairForm_alg hK f]

end Work.Peluse.Prop36SW
