import Mathlib
import Submission.Work.RiemLib.Commons.Analysis.Convex.concaveOn_Icc_of_midpoint

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.Convex

/-- Discrete concavity lemma: if a sequence satisfies the midpoint (second-difference)
condition `a i + a (i+2) ≤ 2 a (i+1)` for all indices needed, then the endpoints are
below twice the middle value. -/
lemma seq_endpoint_le {a : ℕ → ℝ} {n : ℕ}
    (h : ∀ i, i + 2 ≤ n + n → a i + a (i + 2) ≤ 2 * a (i + 1)) :
    a 0 + a (n + n) ≤ 2 * a n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; linarith
  set d : ℕ → ℝ := fun i => a (i + 1) - a i with hd
  have hstep : ∀ i, i + 2 ≤ n + n → d (i + 1) ≤ d i := by
    intro i hi
    have := h i hi
    simp only [hd]
    linarith
  have hchain : ∀ i j, i ≤ j → j + 1 ≤ n + n → d j ≤ d i := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_refl _
    | succ m _ ih =>
        intro hj
        exact le_trans (hstep m (by omega)) (ih (by omega))
  have hsum1 : ∑ i ∈ Finset.range n, d (n + i) = a (n + n) - a n := by
    simp only [hd, Nat.add_assoc]
    rw [Finset.sum_range_sub (fun i => a (n + i)) n]
    simp
  have hsum2 : ∑ i ∈ Finset.range n, d i = a n - a 0 := by
    simp only [hd]
    rw [Finset.sum_range_sub (fun i => a i) n]
  have hle : ∑ i ∈ Finset.range n, d (n + i) ≤ ∑ i ∈ Finset.range n, d i := by
    apply Finset.sum_le_sum
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    exact hchain i (n + i) (Nat.le_add_left i n) (by omega)
  linarith

theorem concaveOn_Icc_of_local_midpoint {H : ℝ → ℝ} {T U : ℝ} (hT : 0 ≤ T) (hU : 0 < U)
    (hcont : ContinuousOn H (Set.Icc 0 T))
    (hloc : ∀ u ∈ Set.Ioc 0 U, ∀ s t : ℝ, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T →
      t - s = 2 * u → H s + H t ≤ 2 * H ((s + t) / 2)) :
    ConcaveOn ℝ (Set.Icc 0 T) H := by
  apply concaveOn_Icc_of_midpoint hT hcont
  intro x hx y hy
  have key : ∀ s t : ℝ, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T → s ≤ t →
      H s + H t ≤ 2 * H ((s + t) / 2) := by
    intro s t hs ht hst
    rcases lt_or_eq_of_le hst with hlt | heq
    · have hLpos : 0 < t - s := by linarith
      set n : ℕ := ⌈(t - s) / U⌉₊ + 1 with hn
      have hn1 : 1 ≤ n := by rw [hn]; omega
      have hnU : (t - s) ≤ (n : ℝ) * U := by
        have hceil := Nat.le_ceil ((t - s) / U)
        rw [div_le_iff₀ hU] at hceil
        rw [hn]; push_cast
        nlinarith [hceil]
      set h : ℝ := (t - s) / (2 * (n : ℝ)) with hh
      have hn0 : (0:ℝ) < 2 * (n : ℝ) := by
        have : (0:ℝ) < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
        linarith
      have hhpos : 0 < h := by
        rw [hh]; exact div_pos hLpos hn0
      have hhU : h ≤ U := by
        rw [hh, div_le_iff₀ hn0]
        have hn1R : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
        nlinarith [hnU, hn1R, hU]
      have hmul : (2 * (n : ℝ)) * h = t - s := by
        rw [hh, mul_div_cancel₀]; exact ne_of_gt hn0
      have hbound : ∀ j : ℕ, j ≤ n + n → s + (j:ℝ)*h ∈ Set.Icc 0 T := by
        intro j hj
        have hjR : (j:ℝ) ≤ ((n+n:ℕ):ℝ) := by exact_mod_cast hj
        have hjn : (j:ℝ) * h ≤ ((n+n:ℕ):ℝ) * h :=
          mul_le_mul_of_nonneg_right hjR (le_of_lt hhpos)
        have hsum : ((n+n:ℕ):ℝ) * h = t - s := by
          have hcast : ((n+n:ℕ):ℝ) = 2 * (n:ℝ) := by push_cast; ring
          rw [hcast]; exact hmul
        rw [hsum] at hjn
        constructor
        · have : 0 ≤ (j:ℝ)*h := mul_nonneg (Nat.cast_nonneg _) (le_of_lt hhpos)
          linarith [hs.1]
        · linarith [ht.2, hjn]
      set a : ℕ → ℝ := fun i => H (s + (i:ℝ) * h) with ha
      have hahyp : ∀ i, i + 2 ≤ n + n → a i + a (i + 2) ≤ 2 * a (i + 1) := by
        intro i hi
        have hmem1 : s + (i:ℝ)*h ∈ Set.Icc 0 T := hbound i (by omega)
        have hmem2 : s + ((i+2:ℕ):ℝ)*h ∈ Set.Icc 0 T := hbound (i+2) (by omega)
        have hdiff : (s + ((i+2:ℕ):ℝ)*h) - (s + (i:ℝ)*h) = 2 * h := by
          push_cast; ring
        have hloc' := hloc h ⟨hhpos, hhU⟩ (s + (i:ℝ)*h) (s + ((i+2:ℕ):ℝ)*h)
          hmem1 hmem2 hdiff
        have hmid : (s + (i:ℝ)*h + (s + ((i+2:ℕ):ℝ)*h)) / 2 = s + ((i+1:ℕ):ℝ)*h := by
          push_cast; ring
        rw [hmid] at hloc'
        simpa only [ha] using hloc'
      have hd := seq_endpoint_le (n := n) hahyp
      have ha0 : a 0 = H s := by simp only [ha]; congr 1; push_cast; ring
      have hann : a (n + n) = H t := by
        simp only [ha]; congr 1
        have hcast : ((n+n:ℕ):ℝ) = 2 * (n:ℝ) := by push_cast; ring
        rw [hcast, hmul]; ring
      have han : a n = H ((s + t) / 2) := by
        simp only [ha]; congr 1
        have hhalf : (n:ℝ) * h = (t - s)/2 := by nlinarith [hmul]
        rw [hhalf]; ring
      rw [ha0, hann, han] at hd
      exact hd
    · subst heq; ring_nf; linarith
  rcases le_total x y with hxy | hyx
  · have := key x y hx hy hxy; linarith
  · have := key y x hy hx hyx
    rw [show (y + x) / 2 = (x + y) / 2 by ring] at this
    linarith

end Commons.Analysis.Convex
