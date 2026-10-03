/-
# The van der Corput (second moment) step of `Work.KMTAreas.A4.invWeylWindow`

This module proves `Work.KMTAreas.A4.VdcStatement`: one step of van der Corput for the Weyl sum
`∑_{n ∈ [a,b]} u n` of a unimodular sequence.  The proof uses the exact second-moment identity in
the form of the workspace's `Commons.Analysis.ExponentialSums.iterated_differencing_step`

`‖∑_{x < L} w x‖² ≤ 2 ∑_{h < L} ‖∑_{x < L-h} w (x+h) conj (w x)‖`

applied to `w k = u (a+k)`, followed by the pigeonhole principle selecting the shifts `h` whose
correlation sum over the *overlap* window `ovl a b h = [a,b] ∩ ([a,b]-h)` is large relative to the
length of that window, and by the exclusion of the shifts with a short overlap.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.invWeylDefs
import Submission.Commons.Analysis.ExponentialSums.iterated_differencing_step

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Work.KMTAreas.A4

/-! ## Elementary facts about the overlap window -/

/-- For a nonnegative shift the overlap window is the interval `[a, b-h]`. -/
theorem ovl_eq_Icc_of_nonneg {a b h : ℤ} (hh : 0 ≤ h) : ovl a b h = Finset.Icc a (b - h) := by
  unfold ovl
  rw [max_eq_left (by omega), min_eq_right (by omega)]

/-- Cardinality of the overlap window at a nonnegative shift. -/
theorem card_ovl_of_nonneg {a b : ℤ} {h : ℕ} (hh : (h : ℤ) ≤ b - a) :
    (ovl a b (h : ℤ)).card = (b - a).toNat + 1 - h := by
  rw [ovl_eq_Icc_of_nonneg (by positivity), Int.card_Icc]
  have h2 : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
  have key : ((((b - a).toNat + 1 - h : ℕ) : ℤ)) = b - (h : ℤ) + 1 - a := by
    rw [Nat.cast_sub (by omega : h ≤ (b - a).toNat + 1), Nat.cast_add, Nat.cast_one, h2]
    ring
  rw [show b - (h:ℤ) + 1 - a = (((b - a).toNat + 1 - h : ℕ) : ℤ) from key.symm,
    Int.toNat_natCast]

/-- A sum over the overlap window is a sum over `range`. -/
theorem sum_ovl_eq {a b : ℤ} {h : ℕ} (hh : (h : ℤ) ≤ b - a) (f : ℤ → ℂ) :
    (∑ n ∈ ovl a b (h : ℤ), f n)
      = ∑ x ∈ Finset.range ((b - a).toNat + 1 - h), f (a + (x : ℤ)) := by
  rw [ovl_eq_Icc_of_nonneg (by positivity)]
  have h2 : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
  have key : ((b - (h : ℤ) + 1 - a).toNat) = ((b - a).toNat + 1 - h) := by
    have k2 : ((((b - a).toNat + 1 - h : ℕ) : ℤ)) = b - (h : ℤ) + 1 - a := by
      rw [Nat.cast_sub (by omega : h ≤ (b - a).toNat + 1), Nat.cast_add, Nat.cast_one, h2]
      ring
    rw [show b - (h:ℤ) + 1 - a = (((b - a).toNat + 1 - h : ℕ) : ℤ) from k2.symm,
      Int.toNat_natCast]
  rw [Int.Icc_eq_finset_map, Finset.sum_map, key]
  apply Finset.sum_congr rfl
  intro x _
  rfl

/-- The index bookkeeping `(b - a).toNat + 1 = (b + 1 - a).toNat`. -/
theorem toNat_succ_sub {a b : ℤ} (hab : a ≤ b) : (b - a).toNat + 1 = (b + 1 - a).toNat := by
  have h1 : (((b - a).toNat : ℤ)) = b - a := Int.toNat_of_nonneg (by omega)
  have h2 : (((b + 1 - a).toNat : ℤ)) = b + 1 - a := Int.toNat_of_nonneg (by omega)
  have h3 : ((((b - a).toNat + 1 : ℕ)) : ℤ) = (((b + 1 - a).toNat : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_one, h1, h2]; ring
  exact_mod_cast h3

/-! ## The van der Corput step -/

theorem invWeylVdc : VdcStatement := by
  intro a b u ε hab hε0 hε1 hε8L hu hS
  set Ln : ℕ := (b + 1 - a).toNat with hLn
  have hLnb : Ln = (b - a).toNat + 1 := by rw [hLn]; exact (toNat_succ_sub hab).symm
  have hLnZ : ((Ln : ℤ)) = b + 1 - a := by rw [hLn]; exact Int.toNat_of_nonneg (by omega)
  have hLn1 : 1 ≤ Ln := by omega
  have hLR : (Ln : ℝ) = ((b - a : ℤ) : ℝ) + 1 := by
    have h1 : ((Ln : ℤ) : ℝ) = ((b - a : ℤ) : ℝ) + 1 := by
      rw [hLnZ]; push_cast; ring
    exact_mod_cast h1
  have hL1 : (1 : ℝ) ≤ (Ln : ℝ) := by exact_mod_cast hLn1
  have hL0 : (0 : ℝ) < (Ln : ℝ) := lt_of_lt_of_le zero_lt_one hL1
  have hLnm : ∀ h : ℕ, (b - a).toNat + 1 - h = Ln - h := by intro h; rw [← hLnb]
  -- the sequence and its correlation sums
  set w : ℕ → ℂ := fun k => u (a + (k : ℤ)) with hw
  set C : ℕ → ℂ := fun h => ∑ x ∈ Finset.range (Ln - h), w (x + h) * star (w x) with hC
  have hw1 : ∀ k, ‖w k‖ = 1 := by intro k; rw [hw]; exact hu _
  -- the sum identity
  have hSsum : (∑ k ∈ Finset.range Ln, w k) = ∑ n ∈ Finset.Icc a b, u n := by
    rw [hw]
    conv_rhs => rw [Int.Icc_eq_finset_map, ← hLn, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro x _
    rfl
  have hSnorm : ε * (Ln : ℝ) ≤ ‖∑ k ∈ Finset.range Ln, w k‖ := by
    rw [hSsum, hLR]; exact hS
  -- the differencing inequality
  have hdiff : ‖∑ k ∈ Finset.range Ln, w k‖ ^ 2 ≤ 2 * ∑ h ∈ Finset.range Ln, ‖C h‖ := by
    simpa only [hC] using Commons.Analysis.ExponentialSums.iterated_differencing_step Ln w
  have hC0 : C 0 = (Ln : ℂ) := by
    simp only [hC, Nat.sub_zero, add_zero]
    have h1 : ∀ x ∈ Finset.range Ln, w x * star (w x) = (1 : ℂ) := by
      intro x _
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hw1 x]
      norm_num
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hC0norm : ‖C 0‖ = (Ln : ℝ) := by rw [hC0]; simp
  -- the pointwise bound `‖C h‖ ≤ |ovl a b h|`
  have hCle : ∀ h : ℕ, ‖C h‖ ≤ ((Ln - h : ℕ) : ℝ) := by
    intro h
    simp only [hC]
    have h1 : ∀ x ∈ Finset.range (Ln - h), ‖w (x + h) * star (w x)‖ = 1 := by
      intro x _
      rw [norm_mul, hw1, norm_star, hw1, one_mul]
    calc ‖∑ x ∈ Finset.range (Ln - h), w (x + h) * star (w x)‖
        ≤ ∑ x ∈ Finset.range (Ln - h), ‖w (x + h) * star (w x)‖ := norm_sum_le _ _
      _ = (((Ln - h : ℕ)) : ℝ) := by
          rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            mul_one]
  -- the correlation identity
  have hcorr : ∀ h : ℕ, h ≤ Ln - 1 →
      ‖C h‖ = ‖∑ n ∈ ovl a b (h : ℤ), u n * star (u (n + (h : ℤ)))‖ := by
    intro h hh
    have hhZr : (h : ℤ) ≤ b - a := by
      have h1 : ((Ln - 1 : ℕ) : ℤ) = (Ln : ℤ) - 1 := by
        rw [Nat.cast_sub hLn1, Nat.cast_one]
      have h2 : (h : ℤ) ≤ ((Ln - 1 : ℕ) : ℤ) := by exact_mod_cast hh
      rw [h1, hLnZ] at h2
      omega
    have key : (∑ n ∈ ovl a b (h : ℤ), u n * star (u (n + (h : ℤ))))
        = ∑ x ∈ Finset.range (Ln - h),
            u (a + (x : ℤ)) * star (u (a + (x : ℤ) + (h : ℤ))) := by
      rw [sum_ovl_eq hhZr, hLnm h]
    rw [key]
    simp only [hC]
    have h2 : (∑ x ∈ Finset.range (Ln - h), w (x + h) * star (w x))
        = star (∑ x ∈ Finset.range (Ln - h),
            u (a + (x : ℤ)) * star (u (a + (x : ℤ) + (h : ℤ)))) := by
      rw [star_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [star_mul, star_star]
      show u (a + ((x + h : ℕ) : ℤ)) * star (u (a + (x : ℤ))) =
        u (a + (x : ℤ) + (h : ℤ)) * star (u (a + (x : ℤ)))
      rw [show a + ((x + h : ℕ) : ℤ) = a + (x : ℤ) + (h : ℤ) by push_cast; ring]
    rw [h2, norm_star]
  -- the main lower bound
  have hmain : (3 * ε ^ 2 / 8) * (Ln : ℝ) ^ 2 ≤ ∑ h ∈ Finset.Icc 1 (Ln - 1), ‖C h‖ := by
    have h2 : (ε * (Ln : ℝ)) ^ 2 ≤ 2 * ∑ h ∈ Finset.range Ln, ‖C h‖ := by
      calc (ε * (Ln : ℝ)) ^ 2 ≤ ‖∑ k ∈ Finset.range Ln, w k‖ ^ 2 :=
            pow_le_pow_left₀ (by positivity) hSnorm 2
        _ ≤ 2 * ∑ h ∈ Finset.range Ln, ‖C h‖ := hdiff
    have hrange : (Finset.range Ln).sum (fun h => ‖C h‖)
        = ‖C 0‖ + (Finset.Icc 1 (Ln - 1)).sum (fun h => ‖C h‖) := by
      rw [show Finset.range Ln = insert 0 (Finset.Icc 1 (Ln - 1)) from by
        ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega,
        Finset.sum_insert (by simp)]
    rw [hrange, hC0norm] at h2
    have h2' : (ε * (Ln : ℝ)) ^ 2 = ε ^ 2 * (Ln : ℝ) ^ 2 := by ring
    rw [h2'] at h2
    have h4 : (Ln : ℝ) ≤ (ε ^ 2 / 8) * (Ln : ℝ) ^ 2 := by
      have h5 : 8 ≤ ε ^ 2 * (Ln : ℝ) := by rw [hLR]; exact hε8L
      nlinarith [hL0, h5]
    linarith
  -- the good set and the two bad sets
  set p1 : ℕ → Prop := fun h => (ε ^ 2 / 16) * ((Ln : ℝ) - (h : ℝ)) ≤ ‖C h‖ with hp1
  set p2 : ℕ → Prop := fun h => (ε ^ 2 / 64) * (Ln : ℝ) ≤ (Ln : ℝ) - (h : ℝ) with hp2
  set Hn : Finset ℕ := (Finset.Icc 1 (Ln - 1)).filter (fun h => p1 h ∧ p2 h) with hHn
  set A : Finset ℕ := (Finset.Icc 1 (Ln - 1)).filter (fun h => ¬ p1 h) with hAdef
  set B : Finset ℕ := (Finset.Icc 1 (Ln - 1)).filter (fun h => ¬ p2 h) with hBdef
  have hHnsub : Hn ⊆ Finset.Icc 1 (Ln - 1) := Finset.filter_subset _ _
  have hAsub : A ⊆ Finset.Icc 1 (Ln - 1) := Finset.filter_subset _ _
  have hBsub : B ⊆ Finset.Icc 1 (Ln - 1) := Finset.filter_subset _ _
  -- the shifts in `A`: the relative bound fails
  have hAle : ∑ h ∈ A, ‖C h‖ ≤ (ε ^ 2 / 16) * (Ln : ℝ) ^ 2 := by
    have h1 : ∀ h ∈ A, ‖C h‖ ≤ (ε ^ 2 / 16) * ((Ln : ℝ) - (h : ℝ)) := by
      intro h hh
      have hh' := hh
      rw [hAdef, Finset.mem_filter] at hh'
      have := hh'.2
      rw [hp1] at this
      exact le_of_lt (lt_of_not_ge this)
    calc ∑ h ∈ A, ‖C h‖ ≤ ∑ h ∈ A, (ε ^ 2 / 16) * ((Ln : ℝ) - (h : ℝ)) :=
          Finset.sum_le_sum h1
      _ = (ε ^ 2 / 16) * ∑ h ∈ A, ((Ln : ℝ) - (h : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ (ε ^ 2 / 16) * ((Ln : ℝ) * (Ln : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc ∑ h ∈ A, ((Ln : ℝ) - (h : ℝ))
              ≤ ∑ h ∈ Finset.Icc 1 (Ln - 1), ((Ln : ℝ) - (h : ℝ)) := by
                refine Finset.sum_le_sum_of_subset_of_nonneg hAsub ?_
                intro h hh _
                have h1 : (h : ℝ) ≤ (Ln : ℝ) := by
                  have := (Finset.mem_Icc.mp hh).2
                  have : h ≤ Ln := by omega
                  exact_mod_cast this
                linarith
            _ ≤ (Ln : ℝ) * (Ln : ℝ) := by
                calc ∑ h ∈ Finset.Icc 1 (Ln - 1), ((Ln : ℝ) - (h : ℝ))
                    ≤ ∑ _h ∈ Finset.Icc 1 (Ln - 1), (Ln : ℝ) := by
                      apply Finset.sum_le_sum
                      intro h hh
                      have h1 : (h : ℝ) ≤ (Ln : ℝ) := by
                        have := (Finset.mem_Icc.mp hh).2
                        have : h ≤ Ln := by omega
                        exact_mod_cast this
                      linarith
                  _ = (((Ln - 1 : ℕ)) : ℝ) * (Ln : ℝ) := by
                      have hcard : (Finset.Icc 1 (Ln - 1)).card = Ln - 1 := by
                        rw [Nat.card_Icc]; omega
                      rw [Finset.sum_const, hcard, nsmul_eq_mul]
                  _ ≤ (Ln : ℝ) * (Ln : ℝ) := by
                      have h1 : (((Ln - 1 : ℕ)) : ℝ) ≤ (Ln : ℝ) := by
                        rw [Nat.cast_sub hLn1, Nat.cast_one]; linarith
                      nlinarith [hL0, h1]
      _ = (ε ^ 2 / 16) * (Ln : ℝ) ^ 2 := by ring
  -- the shifts in `B`: the overlap is short
  have hBterm : ∀ h ∈ B, ((Ln : ℝ) - (h : ℝ)) ≤ (ε ^ 2 / 64) * (Ln : ℝ) := by
    intro h hh
    have hh' := hh
    rw [hBdef, Finset.mem_filter] at hh'
    have := hh'.2
    rw [hp2] at this
    exact le_of_lt (lt_of_not_ge this)
  have hBcast : ∀ h ∈ B, (((Ln - h : ℕ)) : ℝ) = (Ln : ℝ) - (h : ℝ) := by
    intro h hh
    have hhLn : h ≤ Ln := by
      have := (Finset.mem_Icc.mp (hBsub hh)).2
      omega
    rw [Nat.cast_sub hhLn] <;> push_cast <;> ring
  have hBinj : Set.InjOn (fun h : ℕ => Ln - h) (↑B : Set ℕ) := by
    intro x hx y hy hxy
    have hx1 : x ≤ Ln := by
      have := (Finset.mem_Icc.mp (hBsub (Finset.mem_coe.mp hx))).2; omega
    have hy1 : y ≤ Ln := by
      have := (Finset.mem_Icc.mp (hBsub (Finset.mem_coe.mp hy))).2; omega
    have hx' : (((Ln - x : ℕ)) : ℤ) = (Ln : ℤ) - (x : ℤ) := by
      rw [Nat.cast_sub hx1] <;> push_cast <;> ring
    have hy' : (((Ln - y : ℕ)) : ℤ) = (Ln : ℤ) - (y : ℤ) := by
      rw [Nat.cast_sub hy1] <;> push_cast <;> ring
    have h3 : (((Ln - x : ℕ)) : ℤ) = (((Ln - y : ℕ)) : ℤ) := by
      have h3' : Ln - x = Ln - y := hxy
      rw [h3']
    rw [hx', hy'] at h3
    omega
  have hBcard : ((B.card : ℕ) : ℝ) ≤ (ε ^ 2 / 64) * (Ln : ℝ) + 1 := by
    have himg : B.card = (B.image (fun h => Ln - h)).card :=
      (Finset.card_image_of_injOn hBinj).symm
    have hsub : B.image (fun h => Ln - h) ⊆ Finset.Icc 1 ⌈(ε ^ 2 / 64) * (Ln : ℝ)⌉₊ := by
      intro j hj
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hj
      rw [Finset.mem_Icc]
      refine ⟨?_, ?_⟩
      · have := (Finset.mem_Icc.mp (hBsub hh)).2
        omega
      · have hle : (((Ln - h : ℕ)) : ℝ) ≤ (ε ^ 2 / 64) * (Ln : ℝ) := by
          rw [hBcast h hh]
          exact hBterm h hh
        exact_mod_cast (le_trans hle (Nat.le_ceil ((ε ^ 2 / 64) * (Ln : ℝ))))
    have hcard : (B.image (fun h => Ln - h)).card ≤ ⌈(ε ^ 2 / 64) * (Ln : ℝ)⌉₊ := by
      have h1 := Finset.card_le_card hsub
      rw [Nat.card_Icc] at h1
      omega
    have h2 : ((⌈(ε ^ 2 / 64) * (Ln : ℝ)⌉₊ : ℕ) : ℝ) ≤ (ε ^ 2 / 64) * (Ln : ℝ) + 1 := by
      have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ (ε ^ 2 / 64) * (Ln : ℝ) by positivity)
      linarith
    have h3 : ((B.card : ℕ) : ℝ) ≤ ((⌈(ε ^ 2 / 64) * (Ln : ℝ)⌉₊ : ℕ) : ℝ) := by
      rw [himg]
      exact Nat.cast_le.mpr hcard
    linarith
  have hBle : ∑ h ∈ B, ‖C h‖
      ≤ (((ε ^ 2 / 64) * (Ln : ℝ)) + 1) * (((ε ^ 2 / 64) * (Ln : ℝ)) + 1) := by
    have h1 : ∀ h ∈ B, ‖C h‖ ≤ (ε ^ 2 / 64) * (Ln : ℝ) := by
      intro h hh
      refine (hCle h).trans ?_
      rw [hBcast h hh]
      exact hBterm h hh
    calc ∑ h ∈ B, ‖C h‖ ≤ ∑ _h ∈ B, ((ε ^ 2 / 64) * (Ln : ℝ)) := Finset.sum_le_sum h1
      _ = ((B.card : ℕ) : ℝ) * ((ε ^ 2 / 64) * (Ln : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (((ε ^ 2 / 64) * (Ln : ℝ)) + 1) * (((ε ^ 2 / 64) * (Ln : ℝ)) + 1) := by
          have h2 := hBcard
          have hcLn : (0 : ℝ) ≤ (ε ^ 2 / 64) * (Ln : ℝ) := by positivity
          nlinarith [h2, hcLn, hε0, hL0]
  -- the numerical bound for the `B` contribution
  have hsmall : (((ε ^ 2 / 64) * (Ln : ℝ)) + 1) * (((ε ^ 2 / 64) * (Ln : ℝ)) + 1)
      ≤ (ε ^ 2 / 16) * (Ln : ℝ) ^ 2 := by
    have h1 : 8 ≤ ε ^ 2 * (Ln : ℝ) := by rw [hLR]; exact hε8L
    have h2 : 8 ≤ ε * (Ln : ℝ) := by nlinarith [h1, hε1, hL0]
    have h3 : ε ^ 2 * (Ln : ℝ) = ε * (ε * (Ln : ℝ)) := by ring
    have h4 : ε * (ε * (Ln : ℝ)) ≤ ε * (Ln : ℝ) := by
      have h5 : (0 : ℝ) ≤ ε * (Ln : ℝ) := by positivity
      nlinarith [hε1, h5]
    have hL : (ε ^ 2 / 64) * (Ln : ℝ) + 1 ≤ (1 / 4) * (ε * (Ln : ℝ)) := by
      have h6 : (ε ^ 2 / 64) * (Ln : ℝ) = (ε * (ε * (Ln : ℝ))) / 64 := by ring
      rw [h6]
      have h7 : (0 : ℝ) < ε * (Ln : ℝ) := by positivity
      nlinarith [h4, h2]
    have hpos : (0 : ℝ) ≤ (ε ^ 2 / 64) * (Ln : ℝ) + 1 := by positivity
    have hpos2 : (0 : ℝ) ≤ (1 / 4) * (ε * (Ln : ℝ)) := by positivity
    calc ((ε ^ 2 / 64) * (Ln : ℝ) + 1) * ((ε ^ 2 / 64) * (Ln : ℝ) + 1)
        ≤ ((1 / 4) * (ε * (Ln : ℝ))) * ((1 / 4) * (ε * (Ln : ℝ))) :=
          mul_le_mul hL hL hpos hpos2
      _ = (ε ^ 2 / 16) * (Ln : ℝ) ^ 2 := by ring
  -- the complement
  have hcomp : ∑ h ∈ (Finset.Icc 1 (Ln - 1)).filter (fun h => ¬ (p1 h ∧ p2 h)), ‖C h‖
      ≤ (ε ^ 2 / 16) * (Ln : ℝ) ^ 2 + (ε ^ 2 / 16) * (Ln : ℝ) ^ 2 := by
    have hsub : (Finset.Icc 1 (Ln - 1)).filter (fun h => ¬ (p1 h ∧ p2 h)) ⊆ A ∪ B := by
      intro h hh
      rw [Finset.mem_filter] at hh
      obtain ⟨hhI, hhnot⟩ := hh
      rw [Finset.mem_union, hAdef, hBdef, Finset.mem_filter, Finset.mem_filter]
      by_cases hc : p1 h
      · exact Or.inr ⟨hhI, fun h2 => hhnot ⟨hc, h2⟩⟩
      · exact Or.inl ⟨hhI, hc⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro i _ _; positivity)) ?_
    have hunion : ∑ h ∈ A ∪ B, ‖C h‖ ≤ ∑ h ∈ A, ‖C h‖ + ∑ h ∈ B, ‖C h‖ := by
      rw [show A ∪ B = A ∪ (B \ A) from by
        ext h; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto,
        Finset.sum_union (by
          rw [Finset.disjoint_left]
          intro h hA hBA
          exact (Finset.mem_sdiff.mp hBA).2 hA)]
      have h2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset (s := B) (t := A))
        (fun i _ _ => norm_nonneg (C i))
      linarith
    linarith [hunion, hAle, hBle, hsmall]
  have hsplit : ∑ h ∈ Finset.Icc 1 (Ln - 1), ‖C h‖
      = ∑ h ∈ Hn, ‖C h‖
        + ∑ h ∈ (Finset.Icc 1 (Ln - 1)).filter (fun h => ¬ (p1 h ∧ p2 h)), ‖C h‖ := by
    rw [hHn]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hHnsum : (ε ^ 2 / 64) * (Ln : ℝ) ^ 2 ≤ ∑ h ∈ Hn, ‖C h‖ := by
    have h1 := hmain
    rw [hsplit] at h1
    have h2 := hcomp
    have h3 : (0 : ℝ) ≤ ε ^ 2 * (Ln : ℝ) ^ 2 := by positivity
    linarith
  -- conclusion
  have hmemHn : ∀ k : ℕ, k ∈ Hn ↔ k ∈ Finset.Icc 1 (Ln - 1) ∧ p1 k ∧ p2 k := by
    intro k
    rw [hHn]
    exact Finset.mem_filter
  have hle1 : ∀ k ∈ Hn, 1 ≤ k := by
    intro k hk
    exact (Finset.mem_Icc.mp ((hmemHn k).mp hk).1).1
  have hle2 : ∀ k ∈ Hn, k ≤ Ln - 1 := by
    intro k hk
    exact (Finset.mem_Icc.mp ((hmemHn k).mp hk).1).2
  have hkZ : ∀ k ∈ Hn, (k : ℤ) ≤ b - a := by
    intro k hk
    have h1 : ((Ln - 1 : ℕ) : ℤ) = (Ln : ℤ) - 1 := by rw [Nat.cast_sub hLn1, Nat.cast_one]
    have h2 : (k : ℤ) ≤ ((Ln - 1 : ℕ) : ℤ) := by exact_mod_cast hle2 k hk
    rw [h1, hLnZ] at h2
    omega
  have hp1' : ∀ k ∈ Hn, (ε ^ 2 / 16) * ((Ln : ℝ) - (k : ℝ)) ≤ ‖C k‖ := by
    intro k hk
    have h := ((hmemHn k).mp hk).2.1
    rw [hp1] at h
    exact h
  have hp2' : ∀ k ∈ Hn, (ε ^ 2 / 64) * (Ln : ℝ) ≤ (Ln : ℝ) - (k : ℝ) := by
    intro k hk
    have h := ((hmemHn k).mp hk).2.2
    rw [hp2] at h
    exact h
  have hemb : ∀ k : ℕ, Nat.castEmbedding k = (k : ℤ) := fun k => rfl
  refine ⟨Hn.image Nat.castEmbedding, ?_, ?_, ?_, ?_, ?_⟩
  · rintro h hh
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hh
    have h1 : (k : ℤ) ≠ 0 := by have := hle1 k hk; omega
    exact h1
  · rintro h hh
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hh
    rw [hemb k]
    exact ⟨by have := hle1 k hk; omega, hkZ k hk⟩
  · rintro h hh
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hh
    rw [hemb k, ← hLR, card_ovl_of_nonneg (hkZ k hk), hLnm k,
      Nat.cast_sub (by have := hle2 k hk; omega : k ≤ Ln)]
    exact hp2' k hk
  · have himgsum : ∑ h ∈ Hn.image Nat.castEmbedding, ((ovl a b h).card : ℝ)
        = ∑ k ∈ Hn, ((ovl a b (k : ℤ)).card : ℝ) := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro k _
        rw [hemb k]
      · intro x _ y _ hxy
        rw [hemb x, hemb y] at hxy
        exact_mod_cast hxy
    rw [himgsum, ← hLR]
    refine le_trans hHnsum (Finset.sum_le_sum (fun k hk => ?_))
    rw [card_ovl_of_nonneg (hkZ k hk), hLnm k]
    exact hCle k
  · rintro h hh
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hh
    rw [hemb k, card_ovl_of_nonneg (hkZ k hk), hLnm k,
      Nat.cast_sub (by have := hle2 k hk; omega : k ≤ Ln), ← hcorr k (hle2 k hk)]
    refine le_trans ?_ (hp1' k hk)
    have h0 : (0 : ℝ) ≤ (Ln : ℝ) - (k : ℝ) := by
      have h1 : (k : ℝ) ≤ (Ln : ℝ) - 1 := by
        have h2 : ((Ln - 1 : ℕ) : ℝ) = (Ln : ℝ) - 1 := by
          rw [Nat.cast_sub hLn1, Nat.cast_one]
        rw [← h2]
        exact_mod_cast hle2 k hk
      linarith
    nlinarith [h0, hε0, hε1, sq_nonneg ε]

end Work.KMTAreas.A4
