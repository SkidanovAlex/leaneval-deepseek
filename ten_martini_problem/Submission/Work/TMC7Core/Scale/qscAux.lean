import Mathlib
import Submission.Work.TMC7Core.Scale.spectral_continuity
import Submission.Work.TMC7Core.Scale.qscDefs

set_option maxHeartbeats 800000

open scoped ENNReal BigOperators
open LeanEval.Analysis.TenMartini

noncomputable section
namespace Work.TMC7Core.Scale

/-! ## Tent profiles -/

/-- The tent profile of width `Lr`, centred at `0`. -/
def qscTent (Lr : ℝ) (t : ℤ) : ℝ := max 0 (1 - |(t : ℝ)| / Lr)

theorem qscTent_nonneg (Lr : ℝ) (t : ℤ) : 0 ≤ qscTent Lr t := le_max_left _ _

theorem qscTent_le_one {Lr : ℝ} (hLr : 0 < Lr) (t : ℤ) : qscTent Lr t ≤ 1 := by
  refine max_le zero_le_one ?_
  have h : 0 ≤ |(t : ℝ)| / Lr := div_nonneg (abs_nonneg _) hLr.le
  linarith

theorem qscTent_zero {Lr : ℝ} (hLr : 0 < Lr) {t : ℤ} (h : Lr ≤ |(t : ℝ)|) :
    qscTent Lr t = 0 := by
  rw [qscTent, max_eq_left]
  have h1 : 1 ≤ |(t : ℝ)| / Lr := (one_le_div hLr).mpr h
  linarith

theorem qscTent_pos {Lr : ℝ} (hLr : 0 < Lr) {t : ℤ} (h : |(t : ℝ)| < Lr) :
    0 < qscTent Lr t := by
  refine lt_max_iff.mpr (Or.inr ?_)
  rw [sub_pos, div_lt_one hLr]
  exact h

theorem qscTent_ne_zero {Lr : ℝ} (hLr : 0 < Lr) {t : ℤ} :
    qscTent Lr t ≠ 0 ↔ |(t : ℝ)| < Lr :=
  ⟨fun h => not_le.mp fun hc => h (qscTent_zero hLr hc),
   fun h => ne_of_gt (qscTent_pos hLr h)⟩

theorem qscTent_eq {Lr : ℝ} (hLr : 0 < Lr) (t : ℤ) :
    qscTent Lr t = max 0 ((Lr - |(t : ℝ)|) / Lr) := by
  rw [qscTent]; congr 1; field_simp

theorem qsc_abs_max0_sub_le (x y : ℝ) : |max 0 x - max 0 y| ≤ |x - y| := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · rw [max_eq_right hx, max_eq_right hy]
  · rw [max_eq_right hx, max_eq_left hy, sub_zero, abs_of_nonneg hx,
      abs_of_nonneg (by linarith : 0 ≤ x - y)]
    linarith
  · rw [max_eq_left hx, max_eq_right hy, zero_sub, abs_neg, abs_of_nonneg hy,
      abs_of_nonpos (by linarith : x - y ≤ 0), neg_sub]
    linarith
  · rw [max_eq_left hx, max_eq_left hy, sub_zero, abs_zero]
    exact abs_nonneg _

theorem qscTent_abs_sub_le {Lr : ℝ} (hLr : 0 < Lr) (t : ℤ) :
    |qscTent Lr (t + 1) - qscTent Lr t| ≤ 1 / Lr := by
  have hcast : (((t + 1 : ℤ)) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
  have h := qsc_abs_max0_sub_le ((Lr - |(((t + 1 : ℤ)) : ℝ)|) / Lr) ((Lr - |(t : ℝ)|) / Lr)
  rw [qscTent_eq hLr (t + 1), qscTent_eq hLr t]
  refine h.trans ?_
  have h2 : (Lr - |(((t + 1 : ℤ)) : ℝ)|) / Lr - (Lr - |(t : ℝ)|) / Lr
      = (|(t : ℝ)| - |(((t + 1 : ℤ)) : ℝ)|) / Lr := by ring
  rw [h2, abs_div, abs_of_pos hLr]
  refine div_le_div_of_nonneg_right ?_ hLr.le
  have h4 := abs_abs_sub_abs_le_abs_sub (t : ℝ) ((t : ℝ) + 1)
  have h5 : (t : ℝ) - ((t : ℝ) + 1) = -1 := by ring
  rw [h5, abs_neg, abs_one] at h4
  push_cast
  exact h4

/-! ## Norms of finitely supported vectors -/

theorem qsc_norm_sq_eq_sum {v : EllTwo} {t : Finset ℤ} (hv : ∀ k, k ∉ t → v k = 0) :
    ‖v‖ ^ 2 = ∑ k ∈ t, ‖v k‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) v
  rw [show ((2 : ℝ≥0∞).toReal) = 2 from by norm_num] at h
  simp_rw [Real.rpow_two] at h
  rw [h, tsum_eq_sum (L := SummationFilter.unconditional ℤ)
        (f := fun k : ℤ => ‖v k‖ ^ 2) (fun b hb => by rw [hv b hb]; simp)]

theorem qsc_sum_norm_sq_comm {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : Finset ℤ)
    (G : ι → EllTwo) (hG : ∀ i k, k ∉ t → G i k = 0) :
    ∑ i ∈ s, ‖G i‖ ^ 2 = ∑ k ∈ t, ∑ i ∈ s, ‖G i k‖ ^ 2 := by
  calc ∑ i ∈ s, ‖G i‖ ^ 2
      = ∑ i ∈ s, ∑ k ∈ t, ‖G i k‖ ^ 2 :=
        Finset.sum_congr rfl (fun i _ => qsc_norm_sq_eq_sum (hG i))
    _ = ∑ k ∈ t, ∑ i ∈ s, ‖G i k‖ ^ 2 := Finset.sum_comm

/-! ## Reindexing of integer interval sums -/

theorem qsc_sum_Icc_sub (f : ℤ → ℝ) (k a b : ℤ) :
    ∑ n ∈ Finset.Icc a b, f (k - n) = ∑ m ∈ Finset.Icc (k - b) (k - a), f m := by
  refine Finset.sum_bij' (fun n _ => k - n) (fun m _ => k - m) ?_ ?_ ?_ ?_ ?_
  · intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega
  · intro m hm; simp only [Finset.mem_Icc] at hm ⊢; omega
  · intro n hn; ring
  · intro m hm; ring
  · intro n hn; rfl

/-- The coverage identity: for `|k| ≤ M` the sum over the window `[-(M+Lw), M+Lw]` of
centres of the squared tents evaluated at `k` is the constant `cL`. -/
theorem qsc_coverage_sum {Lr : ℝ} (hLr : 0 < Lr) {Lw : ℕ} (hLrdef : Lr = (Lw : ℝ))
    {M k : ℤ} (hk : |k| ≤ M) :
    ∑ n ∈ Finset.Icc (-(M + (Lw : ℤ))) (M + (Lw : ℤ)), (qscTent Lr (k - n)) ^ 2
      = ∑ m ∈ Finset.Icc (-((Lw : ℤ) - 1)) ((Lw : ℤ) - 1), (qscTent Lr m) ^ 2 := by
  have hsub : Finset.Icc (k - ((Lw : ℤ) - 1)) (k + ((Lw : ℤ) - 1))
      ⊆ Finset.Icc (-(M + (Lw : ℤ))) (M + (Lw : ℤ)) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    rw [abs_le] at hk
    omega
  have hzero : ∀ n ∈ Finset.Icc (-(M + (Lw : ℤ))) (M + (Lw : ℤ)),
      n ∉ Finset.Icc (k - ((Lw : ℤ) - 1)) (k + ((Lw : ℤ) - 1)) →
      (qscTent Lr (k - n)) ^ 2 = 0 := by
    intro n _ hn
    have hn' : ¬ (k - ((Lw : ℤ) - 1) ≤ n ∧ n ≤ k + ((Lw : ℤ) - 1)) := by
      simpa [Finset.mem_Icc] using hn
    push_neg at hn'
    have h1 : ((Lw : ℤ) : ℝ) ≤ |((k - n : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      have habs : (Lw : ℤ) ≤ |k - n| := by
        by_cases hc : n ≤ k + ((Lw : ℤ) - 1)
        · have hlt : n < k - ((Lw : ℤ) - 1) := by
            by_contra hcon
            exact (not_le.mpr (hn' (not_lt.mp hcon))) hc
          have hle : (Lw : ℤ) ≤ k - n := by omega
          exact le_trans hle (le_abs_self _)
        · push_neg at hc
          have hle : (Lw : ℤ) ≤ n - k := by omega
          rw [abs_sub_comm]
          exact le_trans hle (le_abs_self _)
      exact_mod_cast habs
    rw [qscTent_zero hLr (by rw [hLrdef]; exact h1), zero_pow (by norm_num : (2:ℕ) ≠ 0)]
  rw [← Finset.sum_subset hsub hzero]
  rw [qsc_sum_Icc_sub (fun m => (qscTent Lr m) ^ 2) k (k - ((Lw : ℤ) - 1)) (k + ((Lw : ℤ) - 1))]
  have e1 : k - (k + ((Lw : ℤ) - 1)) = -((Lw : ℤ) - 1) := by ring
  have e2 : k - (k - ((Lw : ℤ) - 1)) = ((Lw : ℤ) - 1) := by ring
  rw [e1, e2]

/-- The coverage constant is at least `Lw / 4`. -/
theorem qsc_coeff_lower {Lr : ℝ} (hLr : 0 < Lr) {Lw : ℕ} (hL : 3 ≤ Lw) (hLrdef : Lr = (Lw : ℝ)) :
    (Lw : ℝ) / 4 ≤ ∑ m ∈ Finset.Icc (-((Lw : ℤ) - 1)) ((Lw : ℤ) - 1), (qscTent Lr m) ^ 2 := by
  set N : ℕ := Lw / 2 with hN
  have hcast : (((Lw - 1 : ℕ)) : ℤ) = (Lw : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Lw)]; norm_num
  have hsub : Finset.Icc (-(N : ℤ)) (N : ℤ) ⊆ Finset.Icc (-((Lw : ℤ) - 1)) ((Lw : ℤ) - 1) := by
    intro m hm
    simp only [Finset.mem_Icc] at hm ⊢
    have h3 : N ≤ Lw - 1 := by rw [hN]; omega
    have h4 : ((N : ℕ) : ℤ) ≤ ((Lw - 1 : ℕ) : ℤ) := by exact_mod_cast h3
    rw [hcast] at h4
    omega
  have hstep1 : ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (qscTent Lr m) ^ 2
      ≤ ∑ m ∈ Finset.Icc (-((Lw : ℤ) - 1)) ((Lw : ℤ) - 1), (qscTent Lr m) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => sq_nonneg _)
  have hNle : (N : ℝ) ≤ (Lw : ℝ) / 2 := by
    have h := Nat.div_mul_le_self Lw 2
    have h2 : ((N : ℝ)) * 2 ≤ (Lw : ℝ) := by
      rw [hN]
      have h3 : (((Lw / 2 * 2 : ℕ)) : ℝ) ≤ ((Lw : ℕ) : ℝ) := by exact_mod_cast h
      simpa using h3
    linarith
  have hterm : ∀ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1/4 : ℝ) ≤ (qscTent Lr m) ^ 2 := by
    intro m hm
    simp only [Finset.mem_Icc] at hm
    have hmN : |(m : ℝ)| ≤ (N : ℝ) := by
      rw [abs_le]
      constructor
      · have h2 : ((-(N : ℤ) : ℤ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
        push_cast at h2
        linarith
      · have h2 : (m : ℝ) ≤ (((N : ℤ)) : ℝ) := by exact_mod_cast hm.2
        push_cast at h2
        linarith
    have h2 : (1:ℝ)/2 ≤ qscTent Lr m := by
      rw [qscTent]
      refine le_max_iff.mpr (Or.inr ?_)
      rw [hLrdef]
      have hLwpos : (0:ℝ) < (Lw:ℝ) := by positivity
      have hml : |(m : ℝ)| / (Lw : ℝ) ≤ 1/2 := by
        rw [div_le_iff₀ hLwpos]
        linarith [hmN, hNle]
      linarith
    nlinarith [h2]
  have hcardZ : ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℤ) = 2 * (N : ℤ) + 1 := by
    have h := Int.card_Icc_of_le (a := -(N : ℤ)) (b := (N : ℤ)) (by omega : -(N:ℤ) ≤ (N:ℤ) + 1)
    omega
  have hcardR : ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) = 2 * (N : ℝ) + 1 := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hcardZ
    push_cast at h
    exact h
  have hstep2 : (2 * (N : ℝ) + 1) / 4 ≤ ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (qscTent Lr m) ^ 2 := by
    have hcard : (Finset.Icc (-(N : ℤ)) (N : ℤ)).card • (1/4 : ℝ)
        ≤ ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (qscTent Lr m) ^ 2 := by
      rw [← Finset.sum_const]
      exact Finset.sum_le_sum hterm
    rw [nsmul_eq_mul, hcardR] at hcard
    linarith [hcard]
  have hNge : (Lw : ℝ) / 4 ≤ (2 * (N : ℝ) + 1) / 4 := by
    have h2 : (Lw : ℝ) ≤ 2 * (N : ℝ) + 1 := by
      have h3 : Lw ≤ 2 * (Lw / 2) + 1 := by omega
      rw [hN]
      calc (Lw : ℝ) ≤ ((2 * (Lw / 2) + 1 : ℕ) : ℝ) := by exact_mod_cast h3
        _ = 2 * ((Lw / 2 : ℕ) : ℝ) + 1 := by push_cast; ring
    linarith
  linarith [hstep1, hstep2, hNge]

/-! ## The abstract ratio pigeonhole -/

theorem qsc_exists_ratio_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (R : ℝ)
    (hb0 : ∀ i ∈ s, 0 ≤ b i) (hzero : ∀ i ∈ s, b i = 0 → a i = 0)
    (hbpos : 0 < ∑ i ∈ s, b i)
    (hR : (∑ i ∈ s, a i) ≤ R * ∑ i ∈ s, b i) :
    ∃ i ∈ s, 0 < b i ∧ a i ≤ R * b i := by
  by_contra hcon
  push_neg at hcon
  have hsa : ∑ i ∈ s.filter (fun i => 0 < b i), a i = ∑ i ∈ s, a i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    by_cases hb : 0 < b i
    · simp [hb]
    · have hbz : b i = 0 := le_antisymm (not_lt.mp hb) (hb0 i hi)
      rw [if_neg hb, hzero i hi hbz]
  have hsb : ∑ i ∈ s.filter (fun i => 0 < b i), b i = ∑ i ∈ s, b i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    by_cases hb : 0 < b i
    · simp [hb]
    · have hbz : b i = 0 := le_antisymm (not_lt.mp hb) (hb0 i hi)
      rw [if_neg hb, hbz]
  have hne : (s.filter (fun i => 0 < b i)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hem
    have : ∑ i ∈ s, b i = 0 := by rw [← hsb, hem]; simp
    linarith
  have hlt := Finset.sum_lt_sum_of_nonempty hne (fun i hi => by
    rw [Finset.mem_filter] at hi
    exact hcon i hi.1 hi.2)
  rw [← Finset.mul_sum, hsa, hsb] at hlt
  linarith [hR]


/-! ## Applying the shift action coordinatewise -/

theorem qsc_algebraMap_apply (E : ℝ) (v : EllTwo) (k : ℤ) :
    (algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) v k = (E : ℂ) * v k := by
  have h1 : (algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) v = (E : ℂ) • v := by
    rw [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply, one_apply_eq_self]
  rw [h1, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]

/-! ## The windowing lemma -/

theorem tent_window_alt (lam α θ E : ℝ) (H : EllTwo →L[ℂ] EllTwo)
    (hH : IsAlmostMathieuOperator α lam θ H) (hHsa : IsSelfAdjoint H)
    (hE : (E : ℂ) ∈ spectrum ℂ H) (Lw : ℕ) (hL : 3 ≤ Lw) :
    ∃ (n : ℤ) (u : EllTwo), u ≠ 0 ∧
      ‖(H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) u‖ ≤ 9 / (Lw : ℝ) * ‖u‖ ∧
      ∀ k : ℤ, u k ≠ 0 → |(k : ℝ) - (n : ℝ)| < (Lw : ℝ) := by
  set Lr : ℝ := (Lw : ℝ) with hLrdef
  have hLr : 0 < Lr := by rw [hLrdef]; positivity
  obtain ⟨φ, hφne, ⟨s, hs⟩, hφapp⟩ := fs_approx H hHsa E hE (δ := 1 / Lr) (by positivity)
  set Mb : ℤ := ∑ j ∈ s, |j| with hMb
  have hMb_ge : ∀ k ∈ s, |k| ≤ Mb := by
    intro k hk
    rw [hMb]
    exact Finset.single_le_sum (fun j _ => abs_nonneg j) hk
  set T : Finset ℤ := Finset.Icc (-(Mb + 1)) (Mb + 1) with hT
  have hTs : ∀ k : ℤ, k ∈ s → k ∈ T := by
    intro k hk
    rw [hT, Finset.mem_Icc]
    have h := hMb_ge k hk
    rw [abs_le] at h
    omega
  have hTsp1 : ∀ k : ℤ, k + 1 ∈ s → k ∈ T := by
    intro k hk
    rw [hT, Finset.mem_Icc]
    have h := hMb_ge (k + 1) hk
    rw [abs_le] at h
    constructor <;> omega
  have hTsm1 : ∀ k : ℤ, k - 1 ∈ s → k ∈ T := by
    intro k hk
    rw [hT, Finset.mem_Icc]
    have h := hMb_ge (k - 1) hk
    rw [abs_le] at h
    constructor <;> omega
  have hsT : ∀ k : ℤ, k ∉ T → φ k = 0 :=
    fun k hk => hs k (fun hmem => hk (hTs k hmem))
  have hsT1 : ∀ k : ℤ, k ∉ T → φ (k + 1) = 0 :=
    fun k hk => hs (k + 1) (fun hmem => hk (hTsp1 k hmem))
  have hsT2 : ∀ k : ℤ, k ∉ T → φ (k - 1) = 0 :=
    fun k hk => hs (k - 1) (fun hmem => hk (hTsm1 k hmem))
  have hTm : ∀ k ∈ T, |k| ≤ Mb + 1 := by
    intro k hk
    rw [hT, Finset.mem_Icc] at hk
    exact abs_le.mpr ⟨by omega, by omega⟩
  have hnotT : ∀ k : ℤ, k ∉ T → Mb + 1 < |k| := by
    intro k hk
    by_contra hcon
    have hcon' : |k| ≤ Mb + 1 := not_lt.mp hcon
    rw [abs_le] at hcon'
    exact hk (by rw [hT, Finset.mem_Icc]; exact hcon')
  -- the window of centres
  set Nf : Finset ℤ := Finset.Icc (-(Mb + 2 + (Lw : ℤ))) (Mb + 2 + (Lw : ℤ)) with hNf
  -- the residual vector
  set w : EllTwo := (H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) φ with hw
  have hw_pt : ∀ k : ℤ, w k = φ (k + 1) + φ (k - 1)
      + ((((2 * lam * Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) : ℝ)) : ℂ) - (E : ℂ)) * φ k := by
    intro k
    have h0 : ((H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) φ : EllTwo)
        = H φ - (algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) φ := sub_apply _ _ _
    have h1 : w k = (H φ : ℤ → ℂ) k - (((algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) φ) : ℤ → ℂ) k := by
      rw [hw, h0]
      exact congrFun (lp.coeFn_sub (H φ) ((algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) φ)) k
    rw [h1, qsc_algebraMap_apply, hH φ k]
    push_cast
    ring
  have hw_supp : ∀ k : ℤ, k ∉ T → w k = 0 := by
    intro k hk
    have h1 : φ (k + 1) = 0 := by
      by_contra hc
      have hmem : k + 1 ∈ s := by
        by_contra h
        exact hc (hs (k + 1) h)
      have h2 := hMb_ge (k + 1) hmem
      rw [abs_le] at h2
      have h3 : |k| ≤ Mb + 1 := abs_le.mpr ⟨by omega, by omega⟩
      have h4 := hnotT k hk
      linarith
    have h2 : φ (k - 1) = 0 := by
      by_contra hc
      have hmem : k - 1 ∈ s := by
        by_contra h
        exact hc (hs (k - 1) h)
      have h3 := hMb_ge (k - 1) hmem
      rw [abs_le] at h3
      have h4 : |k| ≤ Mb + 1 := abs_le.mpr ⟨by omega, by omega⟩
      have h5 := hnotT k hk
      linarith
    rw [hw_pt, h1, h2, hsT k hk]
    ring
  -- the tent-vector family
  have hmemψ : ∀ n : ℤ, Memℓp (fun k : ℤ => ((qscTent Lr (k - n) : ℝ) : ℂ) * φ k) 2 := by
    intro n
    refine (lp.memℓp φ).norm.mono (fun k => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (qscTent_nonneg Lr (k - n))]
    calc qscTent Lr (k - n) * ‖φ k‖ ≤ 1 * ‖φ k‖ :=
          mul_le_mul_of_nonneg_right (qscTent_le_one hLr (k - n)) (norm_nonneg _)
      _ = ‖φ k‖ := one_mul _
  let ψ : ℤ → EllTwo := fun n =>
    ⟨fun k => ((qscTent Lr (k - n) : ℝ) : ℂ) * φ k, hmemψ n⟩
  have ψ_apply : ∀ n k : ℤ, ψ n k = ((qscTent Lr (k - n) : ℝ) : ℂ) * φ k := fun n k => rfl
  have hmemd : ∀ n : ℤ, Memℓp (fun k : ℤ => ((qscTent Lr (k - n) : ℝ) : ℂ) * w k) 2 := by
    intro n
    refine (lp.memℓp w).norm.mono (fun k => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (qscTent_nonneg Lr (k - n))]
    calc qscTent Lr (k - n) * ‖w k‖ ≤ 1 * ‖w k‖ :=
          mul_le_mul_of_nonneg_right (qscTent_le_one hLr (k - n)) (norm_nonneg _)
      _ = ‖w k‖ := one_mul _
  let dvec : ℤ → EllTwo := fun n =>
    ⟨fun k => ((qscTent Lr (k - n) : ℝ) : ℂ) * w k, hmemd n⟩
  have dvec_apply : ∀ n k : ℤ, dvec n k = ((qscTent Lr (k - n) : ℝ) : ℂ) * w k := fun n k => rfl
  have hmemc : ∀ n : ℤ, Memℓp (fun k : ℤ =>
      (((qscTent Lr (k + 1 - n) - qscTent Lr (k - n) : ℝ)) : ℂ) * φ (k + 1)
      + (((qscTent Lr (k - 1 - n) - qscTent Lr (k - n) : ℝ)) : ℂ) * φ (k - 1)) 2 := by
    intro n
    apply memℓp_gen
    refine summable_of_ne_finset_zero (s := T) (f := fun k : ℤ =>
      ‖(((qscTent Lr (k + 1 - n) - qscTent Lr (k - n) : ℝ)) : ℂ) * φ (k + 1)
      + (((qscTent Lr (k - 1 - n) - qscTent Lr (k - n) : ℝ)) : ℂ) * φ (k - 1)‖ ^ ((2:ℝ≥0∞).toReal)) ?_
    intro k hk
    have h1 : φ (k + 1) = 0 := hsT1 k hk
    have h2 : φ (k - 1) = 0 := hsT2 k hk
    simp [h1, h2]
  let cvec : ℤ → EllTwo := fun n =>
    ⟨fun k => (((qscTent Lr (k + 1 - n) - qscTent Lr (k - n) : ℝ)) : ℂ) * φ (k + 1)
      + (((qscTent Lr (k - 1 - n) - qscTent Lr (k - n) : ℝ)) : ℂ) * φ (k - 1), hmemc n⟩
  have cvec_apply : ∀ n k : ℤ, cvec n k =
      (((qscTent Lr (k + 1 - n) - qscTent Lr (k - n) : ℝ)) : ℂ) * φ (k + 1)
      + (((qscTent Lr (k - 1 - n) - qscTent Lr (k - n) : ℝ)) : ℂ) * φ (k - 1) := fun n k => rfl
  have cvec_supp : ∀ n k : ℤ, k ∉ T → cvec n k = 0 := by
    intro n k hk
    have h1 : φ (k + 1) = 0 := hsT1 k hk
    have h2 : φ (k - 1) = 0 := hsT2 k hk
    rw [cvec_apply, h1, h2, mul_zero, mul_zero, add_zero]
  -- pointwise decomposition:  (H - E)(ψ n) = dvec n + cvec n
  have hdecomp : ∀ n : ℤ,
      (H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (ψ n) = dvec n + cvec n := by
    intro n
    apply lp.ext
    funext k
    have h0 : ((H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (ψ n) : EllTwo)
        = H (ψ n) - (algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (ψ n) := sub_apply _ _ _
    have hL : (((H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (ψ n)) : ℤ → ℂ) k
        = ((H (ψ n)) : ℤ → ℂ) k
          - ((((algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (ψ n))) : ℤ → ℂ) k := by
      rw [h0]
      exact congrFun (lp.coeFn_sub (H (ψ n)) ((algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (ψ n))) k
    rw [hL, qsc_algebraMap_apply, hH (ψ n) k, lp.coeFn_add, Pi.add_apply,
      dvec_apply, cvec_apply, hw_pt, ψ_apply, ψ_apply, ψ_apply]
    push_cast
    ring
  -- the coverage constant
  set cL : ℝ := ∑ m ∈ Finset.Icc (-((Lw : ℤ) - 1)) ((Lw : ℤ) - 1), (qscTent Lr m) ^ 2 with hcL
  have hcov : ∀ k : ℤ, |k| ≤ Mb + 2 → ∑ n ∈ Nf, (qscTent Lr (k - n)) ^ 2 = cL := by
    intro k hk
    rw [hcL, hNf]
    exact qsc_coverage_sum hLr hLrdef hk
  have hcL_ge : (Lw : ℝ) / 4 ≤ cL := by
    rw [hcL]; exact qsc_coeff_lower hLr hL hLrdef
  -- shifted φ sums
  have hsh : ∀ c : ℤ, ∑ k ∈ T, ‖φ (k + c)‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
    intro c
    have hsumm : Summable (fun k : ℤ => ‖φ (k + c)‖ ^ 2) := by
      have h0 : Summable (fun k : ℤ => ‖φ k‖ ^ 2) := by
        have h := (lp.memℓp φ).summable (p := 2) (by norm_num)
        rw [show ((2 : ℝ≥0∞).toReal) = 2 from by norm_num] at h
        simpa [Real.rpow_two] using h
      have h1 := (Equiv.summable_iff (Equiv.addRight c)).2 h0
      simpa only [Function.comp_def, Equiv.coe_addRight] using h1
    have hle : ∑ k ∈ T, ‖φ (k + c)‖ ^ 2 ≤ ∑' k : ℤ, ‖φ (k + c)‖ ^ 2 :=
      Summable.sum_le_tsum T (fun i _ => by positivity) hsumm
    have hts : ∑' k : ℤ, ‖φ (k + c)‖ ^ 2 = ‖φ‖ ^ 2 := by
      rw [show (∑' k : ℤ, ‖φ (k + c)‖ ^ 2)
          = ∑' k : ℤ, ‖φ ((Equiv.addRight c) k)‖ ^ 2 from by
            simp only [Equiv.coe_addRight]]
      rw [Equiv.tsum_eq (Equiv.addRight c) (fun k : ℤ => ‖φ k‖ ^ 2)]
      have h := (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) φ).symm
      rw [show ((2 : ℝ≥0∞).toReal) = 2 from by norm_num] at h
      simpa [Real.rpow_two] using h
    linarith
  -- the counting bound for the finite differences of the tents
  have hΔcount : ∀ k : ℤ, |k| ≤ Mb + 2 →
      ∑ n ∈ Nf, (qscTent Lr (k + 1 - n) - qscTent Lr (k - n)) ^ 2
        ≤ (2 * (Lw : ℝ) + 1) / (Lw : ℝ) ^ 2 := by
    intro k hk
    have hsub2 : Finset.Icc (k - (Lw : ℤ)) (k + (Lw : ℤ)) ⊆ Nf := by
      intro n hn
      rw [hNf]
      simp only [Finset.mem_Icc] at hn ⊢
      have hk' := abs_le.mp hk
      constructor <;> omega
    have hz : ∀ n ∈ Nf, n ∉ Finset.Icc (k - (Lw : ℤ)) (k + (Lw : ℤ)) →
        (qscTent Lr (k + 1 - n) - qscTent Lr (k - n)) ^ 2 = 0 := by
      intro n _ hn
      have hn' : ¬ (k - (Lw : ℤ) ≤ n ∧ n ≤ k + (Lw : ℤ)) := by
        simpa [Finset.mem_Icc] using hn
      have hbig : (Lw : ℤ) + 1 ≤ |k - n| := by
        by_cases hc : n ≤ k + (Lw : ℤ)
        · have hlt : n < k - (Lw : ℤ) := by
            by_contra hcon
            exact hn' ⟨not_lt.mp hcon, hc⟩
          have hle : (Lw : ℤ) + 1 ≤ k - n := by omega
          exact le_trans hle (le_abs_self _)
        · push_neg at hc
          have hle : (Lw : ℤ) + 1 ≤ n - k := by omega
          rw [abs_sub_comm]
          exact le_trans hle (le_abs_self _)
      have e1 : qscTent Lr (k - n) = 0 := by
        apply qscTent_zero hLr
        rw [hLrdef]
        exact_mod_cast (show (Lw : ℤ) ≤ |k - n| by omega)
      have e2 : qscTent Lr (k + 1 - n) = 0 := by
        apply qscTent_zero hLr
        rw [hLrdef]
        have hge : (Lw : ℤ) ≤ |k + 1 - n| := by
          have h1 : k + 1 - n = (k - n) + 1 := by ring
          rw [h1]
          have h2 : |k - n| ≤ |(k - n) + 1| + 1 := by
            have hh : (k - n) = ((k - n) + 1) + (-1) := by ring
            calc |k - n| = |((k - n) + 1) + (-1 : ℤ)| := congrArg abs hh
              _ ≤ |(k - n) + 1| + |(-1 : ℤ)| := abs_add_le _ _
              _ = |(k - n) + 1| + 1 := by rw [abs_neg, abs_one]
          omega
        exact_mod_cast hge
      rw [e1, e2]
      ring
    rw [← Finset.sum_subset hsub2 hz]
    have hterm : ∀ n ∈ Finset.Icc (k - (Lw : ℤ)) (k + (Lw : ℤ)),
        (qscTent Lr (k + 1 - n) - qscTent Lr (k - n)) ^ 2 ≤ 1 / (Lw : ℝ) ^ 2 := by
      intro n _
      have h1 : |qscTent Lr (k + 1 - n) - qscTent Lr (k - n)| ≤ 1 / Lr := by
        have : k + 1 - n = (k - n) + 1 := by ring
        rw [this]; exact qscTent_abs_sub_le hLr (k - n)
      calc (qscTent Lr (k + 1 - n) - qscTent Lr (k - n)) ^ 2
          = |qscTent Lr (k + 1 - n) - qscTent Lr (k - n)| ^ 2 := by rw [sq_abs]
        _ ≤ (1 / Lr) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = 1 / (Lw : ℝ) ^ 2 := by rw [hLrdef]; ring
    have hcard : ((Finset.Icc (k - (Lw : ℤ)) (k + (Lw : ℤ))).card : ℝ) = 2 * (Lw : ℝ) + 1 := by
      have h := Int.card_Icc_of_le (a := k - (Lw : ℤ)) (b := k + (Lw : ℤ))
        (by omega : k - (Lw : ℤ) ≤ k + (Lw : ℤ) + 1)
      have h2 : ((Finset.Icc (k - (Lw : ℤ)) (k + (Lw : ℤ))).card : ℤ) = 2 * (Lw : ℤ) + 1 := by omega
      have h3 := congrArg (fun z : ℤ => (z : ℝ)) h2
      push_cast at h3
      exact h3
    calc ∑ n ∈ Finset.Icc (k - (Lw : ℤ)) (k + (Lw : ℤ)),
          (qscTent Lr (k + 1 - n) - qscTent Lr (k - n)) ^ 2
        ≤ (Finset.Icc (k - (Lw : ℤ)) (k + (Lw : ℤ))).card • (1 / (Lw : ℝ) ^ 2) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ = (2 * (Lw : ℝ) + 1) / (Lw : ℝ) ^ 2 := by
          rw [nsmul_eq_mul, hcard]; ring
  -- B:  sum of the squared norms of the tent vectors
  have hBsum : ∑ n ∈ Nf, ‖ψ n‖ ^ 2 = cL * ‖φ‖ ^ 2 := by
    rw [qsc_sum_norm_sq_comm Nf T ψ (fun n k hk => by rw [ψ_apply, hsT k hk, mul_zero])]
    have hpt : ∀ k n : ℤ, ‖ψ n k‖ ^ 2 = (qscTent Lr (k - n)) ^ 2 * ‖φ k‖ ^ 2 := by
      intro k n
      rw [ψ_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (qscTent_nonneg Lr (k - n)), mul_pow]
    calc ∑ k ∈ T, ∑ n ∈ Nf, ‖ψ n k‖ ^ 2
        = ∑ k ∈ T, ∑ n ∈ Nf, (qscTent Lr (k - n)) ^ 2 * ‖φ k‖ ^ 2 :=
          Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun n _ => hpt k n))
      _ = ∑ k ∈ T, (∑ n ∈ Nf, (qscTent Lr (k - n)) ^ 2) * ‖φ k‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [← Finset.sum_mul]
      _ = ∑ k ∈ T, cL * ‖φ k‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          rw [hcov k (by have := hTm k hk; omega)]
      _ = cL * ∑ k ∈ T, ‖φ k‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ = cL * ‖φ‖ ^ 2 := by
          rw [qsc_norm_sq_eq_sum (v := φ) (t := T) (fun k hk => hsT k hk)]
  -- D:  sum of the squared norms of the diagonal vectors
  have hDsum : ∑ n ∈ Nf, ‖dvec n‖ ^ 2 = cL * ‖w‖ ^ 2 := by
    rw [qsc_sum_norm_sq_comm Nf T dvec (fun n k hk => by rw [dvec_apply, hw_supp k hk, mul_zero])]
    have hpt : ∀ k n : ℤ, ‖dvec n k‖ ^ 2 = (qscTent Lr (k - n)) ^ 2 * ‖w k‖ ^ 2 := by
      intro k n
      rw [dvec_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (qscTent_nonneg Lr (k - n)), mul_pow]
    calc ∑ k ∈ T, ∑ n ∈ Nf, ‖dvec n k‖ ^ 2
        = ∑ k ∈ T, ∑ n ∈ Nf, (qscTent Lr (k - n)) ^ 2 * ‖w k‖ ^ 2 :=
          Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun n _ => hpt k n))
      _ = ∑ k ∈ T, (∑ n ∈ Nf, (qscTent Lr (k - n)) ^ 2) * ‖w k‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [← Finset.sum_mul]
      _ = ∑ k ∈ T, cL * ‖w k‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          rw [hcov k (by have := hTm k hk; omega)]
      _ = cL * ∑ k ∈ T, ‖w k‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ = cL * ‖w‖ ^ 2 := by
          rw [qsc_norm_sq_eq_sum (v := w) (t := T) (fun k hk => hw_supp k hk)]
  -- C:  the commutator sum
  have hCk : ∀ k ∈ T, ∑ n ∈ Nf, ‖cvec n k‖ ^ 2
      ≤ 2 * ((2 * (Lw : ℝ) + 1) / (Lw : ℝ) ^ 2) * (‖φ (k + 1)‖ ^ 2 + ‖φ (k - 1)‖ ^ 2) := by
    intro k hk
    have hkm : |k| ≤ Mb + 2 := by have := hTm k hk; linarith
    have hkm1 : |k - 1| ≤ Mb + 2 := by
      have h1 : |k - 1| ≤ |k| + 1 := by
        have hh := abs_add_le k (-1 : ℤ)
        rwa [show k + (-1) = k - 1 from by ring, abs_neg, abs_one] at hh
      have h2 := hTm k hk
      linarith
    have hCpt : ∀ n : ℤ, ‖cvec n k‖ ^ 2
        ≤ 2 * ((qscTent Lr (k + 1 - n) - qscTent Lr (k - n)) ^ 2 * ‖φ (k + 1)‖ ^ 2)
          + 2 * ((qscTent Lr (k - 1 - n) - qscTent Lr (k - n)) ^ 2 * ‖φ (k - 1)‖ ^ 2) := by
      intro n
      set x : ℝ := qscTent Lr (k + 1 - n) - qscTent Lr (k - n) with hx
      set y : ℝ := qscTent Lr (k - 1 - n) - qscTent Lr (k - n) with hy
      have hsplit : cvec n k = ((x : ℂ)) * φ (k + 1) + ((y : ℂ)) * φ (k - 1) := cvec_apply n k
      rw [hsplit]
      have h4 : ‖((x : ℂ)) * φ (k + 1) + ((y : ℂ)) * φ (k - 1)‖ ^ 2
          ≤ (‖((x : ℂ)) * φ (k + 1)‖ + ‖((y : ℂ)) * φ (k - 1)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
      have h2 : ‖((x : ℂ)) * φ (k + 1)‖ ^ 2 = x ^ 2 * ‖φ (k + 1)‖ ^ 2 := by
        rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have h3 : ‖((y : ℂ)) * φ (k - 1)‖ ^ 2 = y ^ 2 * ‖φ (k - 1)‖ ^ 2 := by
        rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      nlinarith [h4, h2, h3,
        sq_nonneg (‖((x : ℂ)) * φ (k + 1)‖ - ‖((y : ℂ)) * φ (k - 1)‖)]
    calc ∑ n ∈ Nf, ‖cvec n k‖ ^ 2
        ≤ ∑ n ∈ Nf, (2 * ((qscTent Lr (k + 1 - n) - qscTent Lr (k - n)) ^ 2 * ‖φ (k + 1)‖ ^ 2)
            + 2 * ((qscTent Lr (k - 1 - n) - qscTent Lr (k - n)) ^ 2 * ‖φ (k - 1)‖ ^ 2)) :=
          Finset.sum_le_sum (fun n _ => hCpt n)
      _ = 2 * (∑ n ∈ Nf, (qscTent Lr (k + 1 - n) - qscTent Lr (k - n)) ^ 2) * ‖φ (k + 1)‖ ^ 2
            + 2 * (∑ n ∈ Nf, (qscTent Lr (k - 1 - n) - qscTent Lr (k - n)) ^ 2) * ‖φ (k - 1)‖ ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← Finset.sum_mul, ← Finset.sum_mul]
          ring
      _ ≤ 2 * ((2 * (Lw : ℝ) + 1) / (Lw : ℝ) ^ 2) * ‖φ (k + 1)‖ ^ 2
            + 2 * ((2 * (Lw : ℝ) + 1) / (Lw : ℝ) ^ 2) * ‖φ (k - 1)‖ ^ 2 := by
          have h1 := hΔcount k hkm
          have h2 := hΔcount (k - 1) hkm1
          have he : (∑ n ∈ Nf, (qscTent Lr (k - 1 - n) - qscTent Lr (k - n)) ^ 2)
              = ∑ n ∈ Nf, (qscTent Lr ((k - 1) + 1 - n) - qscTent Lr ((k - 1) - n)) ^ 2 := by
            refine Finset.sum_congr rfl (fun n _ => ?_)
            have e1 : (k - 1) + 1 - n = k - n := by ring
            have e2 : (k - 1) - n = k - 1 - n := by ring
            rw [e1, e2]; ring
          rw [← he] at h2
          have h3 : (0:ℝ) ≤ ‖φ (k + 1)‖ ^ 2 := sq_nonneg _
          have h4 : (0:ℝ) ≤ ‖φ (k - 1)‖ ^ 2 := sq_nonneg _
          have e1 := mul_le_mul_of_nonneg_right h1 h3
          have e2 := mul_le_mul_of_nonneg_right h2 h4
          linarith
      _ = 2 * ((2 * (Lw : ℝ) + 1) / (Lw : ℝ) ^ 2) * (‖φ (k + 1)‖ ^ 2 + ‖φ (k - 1)‖ ^ 2) := by ring
  have hCsum : ∑ n ∈ Nf, ‖cvec n‖ ^ 2 ≤ 4 * ((2 * (Lw : ℝ) + 1) / (Lw : ℝ) ^ 2) * ‖φ‖ ^ 2 := by
    rw [qsc_sum_norm_sq_comm Nf T cvec (fun n k hk => cvec_supp n k hk)]
    calc ∑ k ∈ T, ∑ n ∈ Nf, ‖cvec n k‖ ^ 2
        ≤ ∑ k ∈ T, 2 * ((2 * (Lw : ℝ) + 1) / (Lw : ℝ) ^ 2) * (‖φ (k + 1)‖ ^ 2 + ‖φ (k - 1)‖ ^ 2) :=
          Finset.sum_le_sum hCk
      _ = 2 * ((2 * (Lw : ℝ) + 1) / (Lw : ℝ) ^ 2)
            * ((∑ k ∈ T, ‖φ (k + 1)‖ ^ 2) + (∑ k ∈ T, ‖φ (k - 1)‖ ^ 2)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ 2 * ((2 * (Lw : ℝ) + 1) / (Lw : ℝ) ^ 2) * (‖φ‖ ^ 2 + ‖φ‖ ^ 2) := by
          have h1 := hsh 1
          have h2 : (∑ k ∈ T, ‖φ (k - 1)‖ ^ 2) ≤ ‖φ‖ ^ 2 := by
            have hh := hsh (-1)
            simpa only [sub_eq_add_neg] using hh
          have h3 : (0:ℝ) ≤ 2 * ((2 * (Lw : ℝ) + 1) / (Lw : ℝ) ^ 2) := by positivity
          have h4 : (∑ k ∈ T, ‖φ (k + 1)‖ ^ 2) + (∑ k ∈ T, ‖φ (k - 1)‖ ^ 2)
              ≤ ‖φ‖ ^ 2 + ‖φ‖ ^ 2 := by linarith
          exact mul_le_mul_of_nonneg_left h4 h3
      _ = 4 * ((2 * (Lw : ℝ) + 1) / (Lw : ℝ) ^ 2) * ‖φ‖ ^ 2 := by ring
  -- the total residual sum is bounded by the mass
  have hAsum : ∑ n ∈ Nf, ‖(H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (ψ n)‖ ^ 2
      ≤ 81 / (Lw : ℝ) ^ 2 * ∑ n ∈ Nf, ‖ψ n‖ ^ 2 := by
    have hmid : ∑ n ∈ Nf, ‖(H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (ψ n)‖ ^ 2
        ≤ 2 * cL * ‖w‖ ^ 2 + 8 * ((2 * (Lw : ℝ) + 1) / (Lw : ℝ) ^ 2) * ‖φ‖ ^ 2 := by
      have hstep : ∑ n ∈ Nf, ‖(H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (ψ n)‖ ^ 2
          ≤ 2 * (∑ n ∈ Nf, ‖dvec n‖ ^ 2) + 2 * (∑ n ∈ Nf, ‖cvec n‖ ^ 2) := by
        calc ∑ n ∈ Nf, ‖(H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (ψ n)‖ ^ 2
            ≤ ∑ n ∈ Nf, (2 * ‖dvec n‖ ^ 2 + 2 * ‖cvec n‖ ^ 2) := by
              refine Finset.sum_le_sum (fun n _ => ?_)
              rw [hdecomp n]
              have h4 : ‖dvec n + cvec n‖ ^ 2 ≤ (‖dvec n‖ + ‖cvec n‖) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
              nlinarith [h4, sq_nonneg (‖dvec n‖ - ‖cvec n‖)]
          _ = 2 * (∑ n ∈ Nf, ‖dvec n‖ ^ 2) + 2 * (∑ n ∈ Nf, ‖cvec n‖ ^ 2) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [hDsum] at hstep
      have hC' : 2 * (∑ n ∈ Nf, ‖cvec n‖ ^ 2)
          ≤ 2 * (4 * ((2 * (Lw : ℝ) + 1) / (Lw : ℝ) ^ 2) * ‖φ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hCsum (by norm_num)
      nlinarith [hstep, hC']
    rw [hBsum]
    have hLwpos : (0:ℝ) < (Lw : ℝ) := by positivity
    have hLw2pos : (0:ℝ) < (Lw : ℝ) ^ 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hLw2pos]
    have hw2 : (Lw : ℝ) ^ 2 * ‖w‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
      have h1 : ‖w‖ < (1 / Lw) * ‖φ‖ := by rw [← hLrdef]; exact hφapp
      have h4 : (Lw : ℝ) * ‖w‖ < ‖φ‖ := by
        have h5 := mul_lt_mul_of_pos_left h1 hLwpos
        rw [one_div, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hLwpos), one_mul] at h5
        exact h5
      have h2 : (0:ℝ) ≤ (Lw : ℝ) * ‖w‖ := mul_nonneg (le_of_lt hLwpos) (norm_nonneg _)
      have h3 : (0:ℝ) ≤ ‖φ‖ := norm_nonneg _
      nlinarith [h4, h2, h3]
    have hkey : 8 * (2 * (Lw : ℝ) + 1) ≤ 79 * cL := by
      have hLw3 : (3:ℝ) ≤ (Lw : ℝ) := by exact_mod_cast hL
      nlinarith [hcL_ge, hLw3]
    have hphi2 : (0:ℝ) ≤ ‖φ‖ ^ 2 := sq_nonneg _
    calc (∑ n ∈ Nf, ‖(H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (ψ n)‖ ^ 2) * (Lw : ℝ) ^ 2
        ≤ (2 * cL * ‖w‖ ^ 2 + 8 * ((2 * (Lw : ℝ) + 1) / (Lw : ℝ) ^ 2) * ‖φ‖ ^ 2) * (Lw : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hmid (le_of_lt hLw2pos)
      _ = 2 * cL * ((Lw : ℝ) ^ 2 * ‖w‖ ^ 2) + 8 * (2 * (Lw : ℝ) + 1) * ‖φ‖ ^ 2 := by
          field_simp
      _ ≤ 2 * cL * ‖φ‖ ^ 2 + 8 * (2 * (Lw : ℝ) + 1) * ‖φ‖ ^ 2 := by
          have h4 := mul_le_mul_of_nonneg_left hw2 (by linarith : (0:ℝ) ≤ 2 * cL)
          linarith
      _ ≤ 81 * cL * ‖φ‖ ^ 2 := by nlinarith [hkey, hphi2]
      _ = 81 * (cL * ‖φ‖ ^ 2) := by ring
  -- the pigeonhole
  obtain ⟨n, -, hnpos, hnle⟩ := qsc_exists_ratio_le Nf
    (fun n => ‖(H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (ψ n)‖ ^ 2)
    (fun n => ‖ψ n‖ ^ 2) (81 / (Lw : ℝ) ^ 2)
    (fun n _ => sq_nonneg _)
    (fun n _ hb => by
      have h0 : ‖ψ n‖ = 0 := by nlinarith [norm_nonneg (ψ n)]
      have hψ : ψ n = 0 := norm_eq_zero.mp h0
      rw [hψ]; simp)
    (by rw [hBsum]
        have hLwpos : (0:ℝ) < (Lw : ℝ) := by positivity
        have hcLpos : 0 < cL := by linarith [hcL_ge, hLwpos]
        exact mul_pos hcLpos (by positivity))
    hAsum
  refine ⟨n, ψ n, ?_, ?_, ?_⟩
  · intro h0
    have h1 : ‖ψ n‖ ^ 2 = 0 := by rw [h0]; simp
    linarith [hnpos, h1]
  · have hnn : (0:ℝ) ≤ 9 / (Lw : ℝ) * ‖ψ n‖ := by positivity
    have hsq : ‖(H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (ψ n)‖ ^ 2
        ≤ (9 / (Lw : ℝ) * ‖ψ n‖) ^ 2 := by
      have : (9 / (Lw : ℝ) * ‖ψ n‖) ^ 2 = 81 / (Lw : ℝ) ^ 2 * ‖ψ n‖ ^ 2 := by ring
      rw [this]; exact hnle
    exact (sq_le_sq₀ (norm_nonneg _) hnn).mp hsq
  · intro k hk
    have h1 : qscTent Lr (k - n) ≠ 0 := by
      intro hc
      exact hk (by rw [ψ_apply, hc]; simp)
    have h2 := (qscTent_ne_zero hLr).mp h1
    rw [hLrdef] at h2
    rw [Int.cast_sub] at h2
    exact h2


/-! ## The two remaining small pieces -/

/-- The frequency-perturbation bound on a window `(0, 2 Lw)`. -/
theorem perturb_win_alt (lam α α' θ : ℝ) (H H' : EllTwo →L[ℂ] EllTwo)
    (hH : IsAlmostMathieuOperator α lam θ H)
    (hH' : IsAlmostMathieuOperator α' lam θ H')
    (Lw : ℕ) (hLw : 1 ≤ Lw) (u : EllTwo)
    (hu : ∀ n : ℤ, u n ≠ 0 → 0 < (n : ℝ) ∧ (n : ℝ) < 2 * (Lw : ℝ)) :
    ‖(H' - H) u‖ ≤ 8 * Real.pi * |lam| * (Lw : ℝ) * |α - α'| * ‖u‖ := by
  have hpt : ∀ n : ℤ, ((H' - H) u) n
      = ((((2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α')) : ℝ)) : ℂ)
          - (((2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α)) : ℝ)) : ℂ)) * u n := by
    intro n
    have h0 : ((H' - H) u : EllTwo) = H' u - H u := sub_apply _ _ _
    have hL : (((H' - H) u) : ℤ → ℂ) n = ((H' u) : ℤ → ℂ) n - ((H u) : ℤ → ℂ) n := by
      rw [h0]
      exact congrFun (lp.coeFn_sub (H' u) (H u)) n
    rw [hL, hH' u n, hH u n]
    push_cast
    ring
  set M : ℝ := 8 * Real.pi * |lam| * (Lw : ℝ) * |α - α'| with hM
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have hper : ∀ n ∈ Finset.Icc (1 : ℤ) ((2 * Lw - 1 : ℕ) : ℤ),
      ‖((H' - H) u) n‖ ≤ M * ‖u n‖ := by
    intro n _
    rw [hpt n, norm_mul]
    by_cases hn : u n = 0
    · rw [hn, norm_zero, mul_zero]; positivity
    · have hnpos : (0:ℝ) < |(n : ℝ)| := by
        rcases hu n hn with ⟨h1, h2⟩
        rwa [abs_of_pos h1]
      have hnlt : |(n : ℝ)| < 2 * (Lw : ℝ) := by
        rcases hu n hn with ⟨h1, h2⟩
        rwa [abs_of_pos h1]
      have hcos : ‖((((2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α')) : ℝ)) : ℂ)
          - (((2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α)) : ℝ)) : ℂ))‖ ≤ M := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          show 2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α'))
              - 2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))
              = 2 * lam * (Real.cos (2 * Real.pi * (θ + (n : ℝ) * α'))
                - Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))) from by ring,
          abs_mul, abs_mul, show |(2:ℝ)| = 2 from by norm_num]
        rw [hM]
        have h1 : |Real.cos (2 * Real.pi * (θ + (n : ℝ) * α'))
            - Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))|
            ≤ 2 * Real.pi * |(n : ℝ)| * |α - α'| := by
          refine le_trans (Real.abs_cos_sub_cos_le _ _) ?_
          have harg : 2 * Real.pi * (θ + (n : ℝ) * α') - 2 * Real.pi * (θ + (n : ℝ) * α)
              = 2 * Real.pi * ((n : ℝ) * (α' - α)) := by ring
          rw [harg, abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
            show |(2:ℝ)| = 2 from by norm_num, abs_sub_comm]
          nlinarith
        have h5 : |Real.cos (2 * Real.pi * (θ + (n : ℝ) * α'))
            - Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))|
            ≤ 2 * Real.pi * (2 * (Lw : ℝ)) * |α - α'| := by
          refine le_trans h1 ?_
          have h6 : (0:ℝ) ≤ 2 * Real.pi * |α - α'| := by positivity
          nlinarith [hnlt, h6]
        nlinarith [h5, abs_nonneg lam, abs_nonneg (α - α')]
      exact mul_le_mul_of_nonneg_right hcos (norm_nonneg _)
  have hsupp : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) ((2 * Lw - 1 : ℕ) : ℤ) → ((H' - H) u) n = 0 := by
    intro n hn
    have hn' : ¬ (1 ≤ n ∧ n ≤ ((2 * Lw - 1 : ℕ) : ℤ)) := by
      simpa [Finset.mem_Icc] using hn
    have hu0 : u n = 0 := by
      by_contra hc
      rcases hu n hc with ⟨h1, h2⟩
      apply hn'
      constructor
      · have h3 : (0:ℤ) < n := by exact_mod_cast h1
        omega
      · have h5 : (n : ℝ) ≤ ((2 * Lw - 1 : ℕ) : ℝ) := by
          have h4 : ((2 * Lw - 1 : ℕ) : ℝ) = 2 * (Lw : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 2 * Lw)]; push_cast; ring
          rw [h4]
          have h6 : (n : ℤ) < 2 * (Lw : ℤ) := by exact_mod_cast h2
          have h7 : (n : ℤ) ≤ 2 * (Lw : ℤ) - 1 := by omega
          have h8 : ((n : ℤ) : ℝ) ≤ ((2 * (Lw : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast h7
          push_cast at h8
          linarith
        exact_mod_cast h5
    rw [hpt n, hu0, mul_zero]
  exact lp_norm_le_of_supported ((H' - H) u) u (Finset.Icc (1 : ℤ) ((2 * Lw - 1 : ℕ) : ℤ))
    hsupp M hMnn hper

/-- Covariance of the almost Mathieu operator under the shift: the residual of the shifted
vector at frequency `α` and phase `θ + k α` has the same norm as the residual at phase `θ`. -/
theorem amo_shift_alt {α lam θ E : ℝ} {k : ℤ}
    {H H' : EllTwo →L[ℂ] EllTwo}
    (hH : IsAlmostMathieuOperator α lam θ H)
    (hH' : IsAlmostMathieuOperator α lam (θ + (k : ℝ) * α) H') (v : EllTwo) :
    ‖(H' - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (shift k v)‖
      = ‖(H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) v‖ := by
  have hpt : ∀ n : ℤ, ((H' - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (shift k v)) n
      = ((H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) v) (n + k) := by
    intro n
    have h0 : ((H' - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (shift k v) : EllTwo)
        = H' (shift k v) - (algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (shift k v) := sub_apply _ _ _
    have hL : (((H' - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (shift k v)) : ℤ → ℂ) n
        = ((H' (shift k v)) : ℤ → ℂ) n
          - ((((algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (shift k v))) : ℤ → ℂ) n := by
      rw [h0]
      exact congrFun (lp.coeFn_sub (H' (shift k v))
        ((algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (shift k v))) n
    have h0' : ((H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) v : EllTwo)
        = H v - (algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) v := sub_apply _ _ _
    have hR : (((H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) v) : ℤ → ℂ) (n + k)
        = ((H v) : ℤ → ℂ) (n + k)
          - ((((algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) v)) : ℤ → ℂ) (n + k) := by
      rw [h0']
      exact congrFun (lp.coeFn_sub (H v) ((algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) v)) (n + k)
    rw [hL, hR, qsc_algebraMap_apply, qsc_algebraMap_apply, hH' (shift k v) n, hH v (n + k)]
    rw [shift_apply, shift_apply, shift_apply]
    have harg : 2 * Real.pi * (θ + (k : ℝ) * α + (n : ℝ) * α)
        = 2 * Real.pi * (θ + (((n + k : ℤ)) : ℝ) * α) := by
      congr 1
      push_cast
      ring
    rw [show n + 1 + k = n + k + 1 from by ring,
      show n - 1 + k = n + k - 1 from by ring, harg]
  have hF : (H' - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (shift k v)
      = shift k ((H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) v) := by
    apply lp.ext
    funext n
    rw [shift_apply]
    exact hpt n
  rw [hF, shift_norm]

end Work.TMC7Core.Scale
