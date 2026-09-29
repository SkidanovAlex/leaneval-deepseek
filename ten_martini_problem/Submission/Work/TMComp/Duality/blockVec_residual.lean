import Mathlib
import Submission.Work.TMComp.Duality.Defs
import Submission.Work.TMComp.Duality.blockVecAux
import Submission.Work.TMComp.Duality.blockVec_norm

/-!
# The block-vector residual estimate (Aubry duality, component C3)

For a finitely supported `u : EllTwo` (supported in the finset `s`) and `N > 0`, the
suspension operator `suspA α lam` applied to the block vector `blockVec u s N`
(`u n / N` on the `N` phase modes `m ∈ [0, N)`) has a residual controlled by the almost
Mathieu residual of `u`:

`‖(suspA α lam - E) (blockVec u s N)‖ ^ 2 ≤ 8 * (‖(amoOp α lam 0 - E) u‖ ^ 2 / N
   + 8 λ ^ 2 ‖u‖ ^ 2 / N ^ 2)`.

The proof decomposes the residual coordinatewise into the "bulk" part
`blkC N m * ((amoOp α lam 0 - E) u) n / N` and a boundary correction supported on the four
phase modes `-1, 0, N-1, N`; the two pieces are estimated by `blockVec_B_sum` and
`blockVec_K_sum`.
-/

namespace Work.TMComp.Duality

open LeanEval.Analysis.TenMartini

theorem blockVec_B_sum (α lam E : ℝ) (u : EllTwo) (s : Finset ℤ)
    (hs : ∀ n : ℤ, n ∉ s → (u : ℤ → ℂ) n = 0) {N : ℕ} (hN : 0 < N) :
    ∑ p ∈ blockFrame s N,
      ‖blkC N p.1 * (((amoOp α lam 0 - E • (1 : EllTwo →L[ℂ] EllTwo)) u : ℤ → ℂ) p.2 / (N : ℂ))‖ ^ 2
      ≤ ‖(amoOp α lam 0 - E • (1 : EllTwo →L[ℂ] EllTwo)) u‖ ^ 2 / (N : ℝ) := by
  set W : EllTwo := (amoOp α lam 0 - E • (1 : EllTwo →L[ℂ] EllTwo)) u with hW
  have hWsupp : ∀ n : ℤ, n ∉ suppFrame s → (W : ℤ → ℂ) n = 0 := by
    intro n hn
    rw [hW]
    exact amoOp_sub_support α lam E u s hs n hn
  have hsupp : ∀ p : ℤ × ℤ, p ∉ blockFrame s N →
      blockVec (W : ℤ → ℂ) (suppFrame s) N p = 0 := by
    rintro ⟨m, n⟩ hp
    rw [blockVec_coord]
    refine if_neg ?_
    rintro ⟨hm0, hmN, hn⟩
    have hp' : m ∉ Finset.Ico (-1 : ℤ) ((N : ℤ) + 1) ∨ n ∉ suppFrame s := by
      by_contra h
      push Not at h
      exact hp (by
        simp only [blockFrame, Finset.mem_product]
        exact ⟨by simpa only [Finset.mem_Ico] using h.1, h.2⟩)
    rcases hp' with h | h
    · exact h (by simp only [Finset.mem_Ico]; omega)
    · exact h hn
  have h1 : (∑ p ∈ blockFrame s N, ‖blkC N p.1 * ((W : ℤ → ℂ) p.2 / (N : ℂ))‖ ^ 2)
      = ‖blockVec (W : ℤ → ℂ) (suppFrame s) N‖ ^ 2 := by
    rw [lp_norm_sq_eq_sum (blockVec (W : ℤ → ℂ) (suppFrame s) N) (blockFrame s N) hsupp]
    apply Finset.sum_congr rfl
    rintro ⟨m, n⟩ hp
    rw [blockVec_apply W (suppFrame s) N hWsupp m n]
  exact le_of_eq (by rw [h1, blockVec_norm W (suppFrame s) hWsupp hN])


theorem blockVec_K_sum (α lam : ℝ) (u : EllTwo) (s : Finset ℤ)
    (hs : ∀ n : ℤ, n ∉ s → (u : ℤ → ℂ) n = 0) {N : ℕ} (hN : 0 < N) :
    ∑ p ∈ blockFrame s N,
      ‖((u : ℤ → ℂ) p.2 / (N : ℂ))
        * ((lam : ℂ) * ph α p.2 * (blkC N (p.1 - 1) - blkC N p.1)
           + (lam : ℂ) * ph α (-p.2) * (blkC N (p.1 + 1) - blkC N p.1))‖ ^ 2
      ≤ 16 * lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ) ^ 2 := by
  set F : ℤ × ℤ → ℝ := fun p => ‖((u : ℤ → ℂ) p.2 / (N : ℂ))
        * ((lam : ℂ) * ph α p.2 * (blkC N (p.1 - 1) - blkC N p.1)
           + (lam : ℂ) * ph α (-p.2) * (blkC N (p.1 + 1) - blkC N p.1))‖ ^ 2 with hF
  set b : ℝ := 4 * lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ) ^ 2 with hb
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hu_norm : ‖u‖ ^ 2 = ∑ n ∈ suppFrame s, ‖(u : ℤ → ℂ) n‖ ^ 2 :=
    lp_norm_sq_eq_sum u (suppFrame s) (fun n hn => hs n (fun h => hn (mem_suppFrame_of_mem s h)))
  have hFn : ∀ m n : ℤ, F (m, n) = ‖((u : ℤ → ℂ) n / (N : ℂ))
        * ((lam : ℂ) * ph α n * (blkC N (m - 1) - blkC N m)
           + (lam : ℂ) * ph α (-n) * (blkC N (m + 1) - blkC N m))‖ ^ 2 := fun m n => rfl
  have hinner : ∀ m : ℤ,
      (∑ n ∈ suppFrame s, ‖((u : ℤ → ℂ) n / (N : ℂ))
        * ((lam : ℂ) * ph α n * (blkC N (m - 1) - blkC N m)
           + (lam : ℂ) * ph α (-n) * (blkC N (m + 1) - blkC N m))‖ ^ 2) ≤ b := by
    intro m
    have hpt : ∀ n : ℤ, ‖((u : ℤ → ℂ) n / (N : ℂ))
        * ((lam : ℂ) * ph α n * (blkC N (m - 1) - blkC N m)
           + (lam : ℂ) * ph α (-n) * (blkC N (m + 1) - blkC N m))‖ ^ 2
        ≤ (4 * lam ^ 2 / (N : ℝ) ^ 2) * ‖(u : ℤ → ℂ) n‖ ^ 2 := by
      intro n
      have hA : ‖(lam : ℂ) * ph α n * (blkC N (m - 1) - blkC N m)‖ ≤ |lam| := by
        calc ‖(lam : ℂ) * ph α n * (blkC N (m - 1) - blkC N m)‖
            = |lam| * ‖blkC N (m - 1) - blkC N m‖ := by
              rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, ph_norm]; ring
          _ ≤ |lam| * 1 := mul_le_mul_of_nonneg_left (norm_blkC_sub_le_one N (m - 1) m) (abs_nonneg lam)
          _ = |lam| := mul_one _
      have hB : ‖(lam : ℂ) * ph α (-n) * (blkC N (m + 1) - blkC N m)‖ ≤ |lam| := by
        calc ‖(lam : ℂ) * ph α (-n) * (blkC N (m + 1) - blkC N m)‖
            = |lam| * ‖blkC N (m + 1) - blkC N m‖ := by
              rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, ph_norm]; ring
          _ ≤ |lam| * 1 := mul_le_mul_of_nonneg_left (norm_blkC_sub_le_one N (m + 1) m) (abs_nonneg lam)
          _ = |lam| := mul_one _
      have hsum : ‖(lam : ℂ) * ph α n * (blkC N (m - 1) - blkC N m)
           + (lam : ℂ) * ph α (-n) * (blkC N (m + 1) - blkC N m)‖ ≤ 2 * |lam| := by
        calc _ ≤ ‖(lam : ℂ) * ph α n * (blkC N (m - 1) - blkC N m)‖
              + ‖(lam : ℂ) * ph α (-n) * (blkC N (m + 1) - blkC N m)‖ := norm_add_le _ _
          _ ≤ |lam| + |lam| := add_le_add hA hB
          _ = 2 * |lam| := by ring
      have hbd : ‖((u : ℤ → ℂ) n / (N : ℂ))
          * ((lam : ℂ) * ph α n * (blkC N (m - 1) - blkC N m)
             + (lam : ℂ) * ph α (-n) * (blkC N (m + 1) - blkC N m))‖
          ≤ 2 * |lam| * ‖(u : ℤ → ℂ) n‖ / (N : ℝ) := by
        calc _ = ‖(u : ℤ → ℂ) n / (N : ℂ)‖
              * ‖(lam : ℂ) * ph α n * (blkC N (m - 1) - blkC N m)
                 + (lam : ℂ) * ph α (-n) * (blkC N (m + 1) - blkC N m)‖ := norm_mul _ _
          _ ≤ (‖(u : ℤ → ℂ) n‖ / (N : ℝ)) * (2 * |lam|) := by
              apply mul_le_mul
              · rw [norm_div, Complex.norm_natCast]
              · exact hsum
              · positivity
              · positivity
          _ = 2 * |lam| * ‖(u : ℤ → ℂ) n‖ / (N : ℝ) := by ring
      have hbd2 : ‖((u : ℤ → ℂ) n / (N : ℂ))
          * ((lam : ℂ) * ph α n * (blkC N (m - 1) - blkC N m)
             + (lam : ℂ) * ph α (-n) * (blkC N (m + 1) - blkC N m))‖ ^ 2
          ≤ (2 * |lam| * ‖(u : ℤ → ℂ) n‖ / (N : ℝ)) ^ 2 := by
        rw [pow_two, pow_two]
        exact mul_self_le_mul_self (norm_nonneg _) hbd
      calc _ ≤ (2 * |lam| * ‖(u : ℤ → ℂ) n‖ / (N : ℝ)) ^ 2 := hbd2
        _ = (4 * lam ^ 2 / (N : ℝ) ^ 2) * ‖(u : ℤ → ℂ) n‖ ^ 2 := by
              rw [div_pow, mul_pow, mul_pow, sq_abs]; ring
    calc (∑ n ∈ suppFrame s, ‖((u : ℤ → ℂ) n / (N : ℂ))
        * ((lam : ℂ) * ph α n * (blkC N (m - 1) - blkC N m)
           + (lam : ℂ) * ph α (-n) * (blkC N (m + 1) - blkC N m))‖ ^ 2)
        ≤ ∑ n ∈ suppFrame s, (4 * lam ^ 2 / (N : ℝ) ^ 2) * ‖(u : ℤ → ℂ) n‖ ^ 2 :=
          Finset.sum_le_sum (fun n _ => hpt n)
      _ = (4 * lam ^ 2 / (N : ℝ) ^ 2) * ‖u‖ ^ 2 := by
          rw [← Finset.mul_sum, hu_norm]
      _ = b := by rw [hb]; ring
  set E : Finset ℤ := Finset.Icc (-1 : ℤ) 0 ∪ Finset.Icc ((N : ℤ) - 1) (N : ℤ) with hEdef
  have hE_mem : ∀ m : ℤ, m ∈ E ↔ (-1 ≤ m ∧ m ≤ 0) ∨ ((N : ℤ) - 1 ≤ m ∧ m ≤ (N : ℤ)) := by
    intro m
    rw [hEdef]
    simp only [Finset.mem_union, Finset.mem_Icc]
  have hcard1 : (Finset.Icc (-1 : ℤ) 0).card ≤ 2 := by
    have h : Finset.Icc (-1 : ℤ) 0 ⊆ ({-1, 0} : Finset ℤ) := by
      intro m hm
      simp only [Finset.mem_Icc] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact le_trans (Finset.card_le_card h) (by decide)
  have hcard2 : (Finset.Icc ((N : ℤ) - 1) (N : ℤ)).card ≤ 2 := by
    have h : Finset.Icc ((N : ℤ) - 1) (N : ℤ) ⊆ ({(N : ℤ) - 1, (N : ℤ)} : Finset ℤ) := by
      intro m hm
      simp only [Finset.mem_Icc] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    refine le_trans (Finset.card_le_card h) ?_
    have h2 := Finset.card_insert_le ((N : ℤ) - 1) ({(N : ℤ)} : Finset ℤ)
    rw [Finset.card_singleton] at h2
    omega
  have hEcard : E.card ≤ 4 := by
    rw [hEdef]
    calc (Finset.Icc (-1 : ℤ) 0 ∪ Finset.Icc ((N : ℤ) - 1) (N : ℤ)).card
        ≤ (Finset.Icc (-1 : ℤ) 0).card + (Finset.Icc ((N : ℤ) - 1) (N : ℤ)).card :=
          Finset.card_union_le _ _
      _ ≤ 2 + 2 := add_le_add hcard1 hcard2
      _ = 4 := by norm_num
  have hEsub : E ⊆ Finset.Ico (-1 : ℤ) ((N : ℤ) + 1) := by
    intro m hm
    rw [hE_mem m] at hm
    simp only [Finset.mem_Ico]
    omega
  have hinnerE : ∀ m : ℤ, (∑ n ∈ suppFrame s, F (m, n)) ≤ b := by
    intro m
    rw [Finset.sum_congr rfl (fun n _ => hFn m n)]
    exact hinner m
  have hvanE : ∀ m ∈ Finset.Ico (-1 : ℤ) ((N : ℤ) + 1), m ∉ E →
      (∑ n ∈ suppFrame s, F (m, n)) = 0 := by
    intro m hm hmE
    have hme : ¬ ((-1 ≤ m ∧ m ≤ 0) ∨ ((N : ℤ) - 1 ≤ m ∧ m ≤ (N : ℤ))) := by
      rw [hE_mem m] at hmE; exact hmE
    have h1 : m ≠ -1 := fun h => hme (by omega)
    have h2 : m ≠ 0 := fun h => hme (by omega)
    have h3 : m ≠ (N : ℤ) - 1 := fun h => hme (by omega)
    have h4 : m ≠ (N : ℤ) := fun h => hme (by omega)
    obtain ⟨hd1, hd2⟩ := blkC_diff_vanishing N h1 h2 h3 h4
    apply Finset.sum_eq_zero
    intro n hn
    rw [hFn m n, hd1, hd2]
    simp
  have hsubE : E ×ˢ suppFrame s ⊆ blockFrame s N := by
    intro p hp
    obtain ⟨m, n⟩ := p
    rw [Finset.mem_product] at hp
    rw [blockFrame, Finset.mem_product]
    exact ⟨hEsub hp.1, hp.2⟩
  have hvanB : ∀ p ∈ blockFrame s N, p ∉ E ×ˢ suppFrame s → F p = 0 := by
    rintro ⟨m, n⟩ hp hp'
    rw [Finset.mem_product] at hp'
    have hp'' : m ∉ E ∨ n ∉ suppFrame s := by
      by_contra h; push Not at h; exact hp' ⟨h.1, h.2⟩
    rcases hp'' with h | h
    · have hme : ¬ ((-1 ≤ m ∧ m ≤ 0) ∨ ((N : ℤ) - 1 ≤ m ∧ m ≤ (N : ℤ))) := by
        rw [hE_mem m] at h; exact h
      have h1 : m ≠ -1 := fun hh => hme (by omega)
      have h2 : m ≠ 0 := fun hh => hme (by omega)
      have h3 : m ≠ (N : ℤ) - 1 := fun hh => hme (by omega)
      have h4 : m ≠ (N : ℤ) := fun hh => hme (by omega)
      obtain ⟨hd1, hd2⟩ := blkC_diff_vanishing N h1 h2 h3 h4
      rw [hFn m n, hd1, hd2]
      simp
    · have hu : (u : ℤ → ℂ) n = 0 := hs n (fun hh => h (mem_suppFrame_of_mem s hh))
      rw [hFn m n, hu]
      simp
  have hsum_sub : (∑ p ∈ E ×ˢ suppFrame s, F p) = ∑ p ∈ blockFrame s N, F p :=
    Finset.sum_subset hsubE hvanB
  rw [← hsum_sub, Finset.sum_product]
  calc (∑ m ∈ E, ∑ n ∈ suppFrame s, F (m, n))
      ≤ ∑ m ∈ E, b := Finset.sum_le_sum (fun m _ => hinnerE m)
    _ = (E.card : ℝ) * b := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 4 * b := by
        apply mul_le_mul_of_nonneg_right _ hb0
        exact_mod_cast hEcard
    _ = 16 * lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ) ^ 2 := by rw [hb]; ring


/-- The residual estimate for the block vector: the suspension residual of `blockVec u s N`
is controlled by the almost Mathieu residual of `u`. -/
theorem blockVec_residual (α lam E : ℝ) (u : LeanEval.Analysis.TenMartini.EllTwo) (s : Finset ℤ) (hs : ∀ n : ℤ, n ∉ s → (u : ℤ → ℂ) n = 0) {N : ℕ} (hN : 0 < N) : ‖(Work.TMComp.Duality.suspA α lam - E • (1 : Work.TMComp.Duality.EllTwo2 →L[ℂ] Work.TMComp.Duality.EllTwo2)) (Work.TMComp.Duality.blockVec (u : ℤ → ℂ) s N)‖ ^ 2 ≤ 8 * (‖(Work.TMComp.Duality.amoOp α lam 0 - E • (1 : LeanEval.Analysis.TenMartini.EllTwo →L[ℂ] LeanEval.Analysis.TenMartini.EllTwo)) u‖ ^ 2 / (N : ℝ) + 8 * lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ) ^ 2) := by
  set W : EllTwo := (amoOp α lam 0 - E • (1 : EllTwo →L[ℂ] EllTwo)) u with hW
  set R : EllTwo2 := (suspA α lam - E • (1 : EllTwo2 →L[ℂ] EllTwo2)) (blockVec (u : ℤ → ℂ) s N) with hR
  have hnorm : ‖R‖ ^ 2 = ∑ p ∈ blockFrame s N, ‖R p‖ ^ 2 :=
    lp_norm_sq_eq_sum ((suspA α lam - E • (1 : EllTwo2 →L[ℂ] EllTwo2)) (blockVec (u : ℤ → ℂ) s N))
      (blockFrame s N) (fun p hp => blockVec_residual_support α lam E u s hs hN p hp)
  have hSB : (∑ p ∈ blockFrame s N, ‖blkC N p.1 * ((W : ℤ → ℂ) p.2 / (N : ℂ))‖ ^ 2)
      ≤ ‖W‖ ^ 2 / (N : ℝ) := blockVec_B_sum α lam E u s hs hN
  have hSK : (∑ p ∈ blockFrame s N, ‖((u : ℤ → ℂ) p.2 / (N : ℂ))
        * ((lam : ℂ) * ph α p.2 * (blkC N (p.1 - 1) - blkC N p.1)
           + (lam : ℂ) * ph α (-p.2) * (blkC N (p.1 + 1) - blkC N p.1))‖ ^ 2)
      ≤ 16 * lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ) ^ 2 := blockVec_K_sum α lam u s hs hN
  have hstep : (∑ p ∈ blockFrame s N, ‖R p‖ ^ 2)
      ≤ 2 * (∑ p ∈ blockFrame s N, ‖blkC N p.1 * ((W : ℤ → ℂ) p.2 / (N : ℂ))‖ ^ 2)
        + 2 * (∑ p ∈ blockFrame s N, ‖((u : ℤ → ℂ) p.2 / (N : ℂ))
            * ((lam : ℂ) * ph α p.2 * (blkC N (p.1 - 1) - blkC N p.1)
               + (lam : ℂ) * ph α (-p.2) * (blkC N (p.1 + 1) - blkC N p.1))‖ ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun p _ => ?_)
    have hcoord : R p = blkC N p.1 * ((W : ℤ → ℂ) p.2 / (N : ℂ))
        + ((u : ℤ → ℂ) p.2 / (N : ℂ))
          * ((lam : ℂ) * ph α p.2 * (blkC N (p.1 - 1) - blkC N p.1)
             + (lam : ℂ) * ph α (-p.2) * (blkC N (p.1 + 1) - blkC N p.1)) := by
      obtain ⟨m, n⟩ := p
      rw [hR, hW]
      exact suspA_blockVec_coord α lam E u s hs hN m n
    rw [hcoord]
    exact norm_add_sq_le_two _ _
  rw [hnorm]
  calc (∑ p ∈ blockFrame s N, ‖R p‖ ^ 2)
      ≤ 2 * (∑ p ∈ blockFrame s N, ‖blkC N p.1 * ((W : ℤ → ℂ) p.2 / (N : ℂ))‖ ^ 2)
        + 2 * (∑ p ∈ blockFrame s N, ‖((u : ℤ → ℂ) p.2 / (N : ℂ))
            * ((lam : ℂ) * ph α p.2 * (blkC N (p.1 - 1) - blkC N p.1)
               + (lam : ℂ) * ph α (-p.2) * (blkC N (p.1 + 1) - blkC N p.1))‖ ^ 2) := hstep
    _ ≤ 2 * (‖W‖ ^ 2 / (N : ℝ)) + 2 * (16 * lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ) ^ 2) := by
        nlinarith [hSB, hSK]
    _ ≤ 8 * (‖W‖ ^ 2 / (N : ℝ) + 8 * lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ) ^ 2) := by
        have hX : 0 ≤ ‖W‖ ^ 2 / (N : ℝ) := by positivity
        have hY : 0 ≤ lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ) ^ 2 := by positivity
        have e1 : 2 * (‖W‖ ^ 2 / (N : ℝ)) + 2 * (16 * lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ) ^ 2)
            = 2 * (‖W‖ ^ 2 / (N : ℝ)) + 32 * (lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ) ^ 2) := by ring
        have e2 : 8 * (‖W‖ ^ 2 / (N : ℝ) + 8 * lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ) ^ 2)
            = 8 * (‖W‖ ^ 2 / (N : ℝ)) + 64 * (lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ) ^ 2) := by ring
        rw [e1, e2]
        linarith [hX, hY]

end Work.TMComp.Duality
