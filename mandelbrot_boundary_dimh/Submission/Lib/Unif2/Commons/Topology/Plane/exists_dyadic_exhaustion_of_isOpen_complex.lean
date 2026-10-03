import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Order.CompletePartialOrder

/-!
# Dyadic exhaustion of an open subset of `ℂ`

We construct, for an open set `U ⊆ ℂ`, an increasing sequence of finite unions of
dyadic squares (closed cells of level `n`, side `2^{-n}`) that is contained in `U` and
that covers `U` locally: every point of `U` has a whole ball contained in some term.
-/

namespace Commons.Topology.Plane

/-- Closed dyadic cell of level `n` with index `p : ℤ × ℤ` in `ℂ`. -/
def dyadicCell (n : ℕ) (p : ℤ × ℤ) : Set ℂ :=
  {z : ℂ | (p.1 : ℝ) / 2 ^ n ≤ z.re ∧ z.re ≤ ((p.1 : ℝ) + 1) / 2 ^ n ∧
           (p.2 : ℝ) / 2 ^ n ≤ z.im ∧ z.im ≤ ((p.2 : ℝ) + 1) / 2 ^ n}

/-- The index bound for level `n` cells whose closure lies in the ball of radius `n+1`. -/
def dyadicBound (n : ℕ) : ℤ := (2:ℤ)^n * ((n:ℤ)+1) + 1

lemma dyadicCell_grid_cover (n : ℕ) (z : ℂ) : ∃ p : ℤ × ℤ, z ∈ dyadicCell n p := by
  have h2n : (0:ℝ) < (2:ℝ)^n := by positivity
  refine ⟨(⌊z.re * 2^n⌋, ⌊z.im * 2^n⌋), ?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ h2n]; exact Int.floor_le _
  · rw [le_div_iff₀ h2n]; exact le_of_lt (Int.lt_floor_add_one _)
  · rw [div_le_iff₀ h2n]; exact Int.floor_le _
  · rw [le_div_iff₀ h2n]; exact le_of_lt (Int.lt_floor_add_one _)

lemma dyadicCell_dist_le {n : ℕ} {p : ℤ × ℤ} {z w : ℂ}
    (hz : z ∈ dyadicCell n p) (hw : w ∈ dyadicCell n p) :
    dist z w ≤ Real.sqrt 2 / 2 ^ n := by
  obtain ⟨hzl, hzu, hzil, hziu⟩ := hz
  obtain ⟨hwl, hwu, hwil, hwiu⟩ := hw
  have hzu' : z.re ≤ (p.1:ℝ)/2^n + 1/2^n := by
    have h := add_div (p.1:ℝ) 1 (2^n); rw [h] at hzu; simpa using hzu
  have hwu' : w.re ≤ (p.1:ℝ)/2^n + 1/2^n := by
    have h := add_div (p.1:ℝ) 1 (2^n); rw [h] at hwu; simpa using hwu
  have hziu' : z.im ≤ (p.2:ℝ)/2^n + 1/2^n := by
    have h := add_div (p.2:ℝ) 1 (2^n); rw [h] at hziu; simpa using hziu
  have hwiu' : w.im ≤ (p.2:ℝ)/2^n + 1/2^n := by
    have h := add_div (p.2:ℝ) 1 (2^n); rw [h] at hwiu; simpa using hwiu
  have hre : |z.re - w.re| ≤ 1 / 2 ^ n := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  have him : |z.im - w.im| ≤ 1 / 2 ^ n := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  have h1 : (z.re - w.re)^2 ≤ (1/2^n)^2 := by
    rw [sq_le_sq]; simpa using hre
  have h2 : (z.im - w.im)^2 ≤ (1/2^n)^2 := by
    rw [sq_le_sq]; simpa using him
  have hsq : Complex.normSq (z - w) ≤ (Real.sqrt 2 / 2^n)^2 := by
    have hsum : (1/2^n)^2 + (1/2^n)^2 = (Real.sqrt 2 / 2^n)^2 := by
      have hdiv : (Real.sqrt 2 / 2^n)^2 = (Real.sqrt 2)^2/(2^n)^2 := by rw [div_pow]
      rw [hdiv, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      ring
    calc Complex.normSq (z - w)
        = (z.re - w.re)^2 + (z.im - w.im)^2 := by
          rw [Complex.normSq_apply]; simp [Complex.sub_re, Complex.sub_im, sq]
      _ ≤ (1/2^n)^2 + (1/2^n)^2 := add_le_add h1 h2
      _ = (Real.sqrt 2 / 2^n)^2 := hsum
  have hnorm : ‖z - w‖ ≤ Real.sqrt 2 / 2 ^ n := by
    rw [Complex.norm_def, Real.sqrt_le_iff]
    exact ⟨by positivity, hsq⟩
  rwa [Complex.dist_eq]

lemma dyadicCell_split_slice (a : ℤ) (n : ℕ) (x : ℝ)
    (h : (a:ℝ)/2^n ≤ x ∧ x ≤ ((a:ℝ)+1)/2^n) :
    (((2*a:ℤ):ℝ)/2^(n+1) ≤ x ∧ x ≤ (((2*a:ℤ):ℝ)+1)/2^(n+1)) ∨
    ((((2*a+1:ℤ)):ℝ)/2^(n+1) ≤ x ∧ x ≤ (((2*a+1:ℤ):ℝ)+1)/2^(n+1)) := by
  have hden : (0:ℝ) < (2:ℝ)^(n+1) := by positivity
  have hA : (((2*a:ℤ)):ℝ)/2^(n+1) = (a:ℝ)/2^n := by
    rw [pow_succ]
    field_simp
    push_cast; ring
  have hB : ((((2*a+1:ℤ)):ℝ)+1)/2^(n+1) = ((a:ℝ)+1)/2^n := by
    rw [pow_succ]
    field_simp
    push_cast; ring
  have hM1 : (((2*a:ℤ)):ℝ)/2^(n+1) ≤ (((2*a+1:ℤ)):ℝ)/2^(n+1) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hden)
    exact_mod_cast (show (2*a:ℤ) ≤ 2*a+1 by omega)
  rcases le_or_gt x ((((2*a+1:ℤ)):ℝ)/2^(n+1)) with hx | hx
  · left
    refine ⟨?_, ?_⟩
    · rw [hA]; exact h.1
    · have : (((2*a:ℤ):ℝ)+1)/2^(n+1) = (((2*a+1:ℤ)):ℝ)/2^(n+1) := by
        congr 1; push_cast; ring
      rw [this]; exact hx
  · right
    refine ⟨le_of_lt hx, ?_⟩
    rw [hB]; exact h.2

lemma dyadicSlice_left_subset (a : ℤ) (n : ℕ) (x : ℝ)
    (h : (((2*a:ℤ)):ℝ)/2^(n+1) ≤ x ∧ x ≤ ((((2*a:ℤ)):ℝ)+1)/2^(n+1)) :
    (a:ℝ)/2^n ≤ x ∧ x ≤ ((a:ℝ)+1)/2^n := by
  have hden : (0:ℝ) < (2:ℝ)^(n+1) := by positivity
  have hA : (((2*a:ℤ)):ℝ)/2^(n+1) = (a:ℝ)/2^n := by
    rw [pow_succ]; field_simp; push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [← hA]; exact h.1
  · have heq : (((2*a:ℤ):ℝ)+2)/2^(n+1) = ((a:ℝ)+1)/2^n := by
      rw [pow_succ]; field_simp; push_cast; ring
    have hle : ((((2*a:ℤ)):ℝ)+1)/2^(n+1) ≤ (((2*a:ℤ):ℝ)+2)/2^(n+1) :=
      div_le_div_of_nonneg_right (by linarith) (le_of_lt hden)
    calc x ≤ ((((2*a:ℤ)):ℝ)+1)/2^(n+1) := h.2
      _ ≤ (((2*a:ℤ):ℝ)+2)/2^(n+1) := hle
      _ = ((a:ℝ)+1)/2^n := heq

lemma dyadicSlice_right_subset (a : ℤ) (n : ℕ) (x : ℝ)
    (h : (((2*a+1:ℤ)):ℝ)/2^(n+1) ≤ x ∧ x ≤ ((((2*a+1:ℤ)):ℝ)+1)/2^(n+1)) :
    (a:ℝ)/2^n ≤ x ∧ x ≤ ((a:ℝ)+1)/2^n := by
  have hden : (0:ℝ) < (2:ℝ)^(n+1) := by positivity
  have hA : (((2*a:ℤ)):ℝ)/2^(n+1) = (a:ℝ)/2^n := by
    rw [pow_succ]; field_simp; push_cast; ring
  have hup : ((((2*a+1:ℤ)):ℝ)+1)/2^(n+1) = ((a:ℝ)+1)/2^n := by
    rw [pow_succ]; field_simp; push_cast; ring
  refine ⟨?_, ?_⟩
  · have hle : (((2*a:ℤ)):ℝ)/2^(n+1) ≤ (((2*a+1:ℤ)):ℝ)/2^(n+1) :=
      div_le_div_of_nonneg_right (by exact_mod_cast (show (2*a:ℤ) ≤ 2*a+1 by omega))
        (le_of_lt hden)
    calc (a:ℝ)/2^n = (((2*a:ℤ)):ℝ)/2^(n+1) := hA.symm
      _ ≤ (((2*a+1:ℤ)):ℝ)/2^(n+1) := hle
      _ ≤ x := h.1
  · rw [← hup]; exact h.2

lemma dyadicCell_child00_subset (n : ℕ) (p : ℤ × ℤ) :
    dyadicCell (n+1) (2*p.1, 2*p.2) ⊆ dyadicCell n p := by
  intro z hz
  obtain ⟨hr1, hr2, hi1, hi2⟩ := hz
  obtain ⟨h1, h2⟩ := dyadicSlice_left_subset p.1 n z.re ⟨hr1, hr2⟩
  obtain ⟨h3, h4⟩ := dyadicSlice_left_subset p.2 n z.im ⟨hi1, hi2⟩
  exact ⟨h1, h2, h3, h4⟩

lemma dyadicCell_child10_subset (n : ℕ) (p : ℤ × ℤ) :
    dyadicCell (n+1) (2*p.1+1, 2*p.2) ⊆ dyadicCell n p := by
  intro z hz
  obtain ⟨hr1, hr2, hi1, hi2⟩ := hz
  obtain ⟨h1, h2⟩ := dyadicSlice_right_subset p.1 n z.re ⟨hr1, hr2⟩
  obtain ⟨h3, h4⟩ := dyadicSlice_left_subset p.2 n z.im ⟨hi1, hi2⟩
  exact ⟨h1, h2, h3, h4⟩

lemma dyadicCell_child01_subset (n : ℕ) (p : ℤ × ℤ) :
    dyadicCell (n+1) (2*p.1, 2*p.2+1) ⊆ dyadicCell n p := by
  intro z hz
  obtain ⟨hr1, hr2, hi1, hi2⟩ := hz
  obtain ⟨h1, h2⟩ := dyadicSlice_left_subset p.1 n z.re ⟨hr1, hr2⟩
  obtain ⟨h3, h4⟩ := dyadicSlice_right_subset p.2 n z.im ⟨hi1, hi2⟩
  exact ⟨h1, h2, h3, h4⟩

lemma dyadicCell_child11_subset (n : ℕ) (p : ℤ × ℤ) :
    dyadicCell (n+1) (2*p.1+1, 2*p.2+1) ⊆ dyadicCell n p := by
  intro z hz
  obtain ⟨hr1, hr2, hi1, hi2⟩ := hz
  obtain ⟨h1, h2⟩ := dyadicSlice_right_subset p.1 n z.re ⟨hr1, hr2⟩
  obtain ⟨h3, h4⟩ := dyadicSlice_right_subset p.2 n z.im ⟨hi1, hi2⟩
  exact ⟨h1, h2, h3, h4⟩

lemma dyadicCell_mem_child {n : ℕ} {p : ℤ × ℤ} {z : ℂ} (hz : z ∈ dyadicCell n p) :
    z ∈ dyadicCell (n+1) (2*p.1, 2*p.2) ∨
    z ∈ dyadicCell (n+1) (2*p.1+1, 2*p.2) ∨
    z ∈ dyadicCell (n+1) (2*p.1, 2*p.2+1) ∨
    z ∈ dyadicCell (n+1) (2*p.1+1, 2*p.2+1) := by
  obtain ⟨hr1, hr2, hi1, hi2⟩ := hz
  rcases dyadicCell_split_slice p.1 n z.re ⟨hr1, hr2⟩ with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rcases dyadicCell_split_slice p.2 n z.im ⟨hi1, hi2⟩ with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · exact Or.inl ⟨ha, hb, hc, hd⟩
    · exact Or.inr (Or.inr (Or.inl ⟨ha, hb, hc, hd⟩))
  · rcases dyadicCell_split_slice p.2 n z.im ⟨hi1, hi2⟩ with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · exact Or.inr (Or.inl ⟨ha, hb, hc, hd⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨ha, hb, hc, hd⟩))

lemma dyadicCell_index_bound {n : ℕ} {p : ℤ × ℤ}
    (h : dyadicCell n p ⊆ Metric.ball 0 ((n:ℝ)+1)) :
    |p.1| ≤ dyadicBound n ∧ |p.2| ≤ dyadicBound n := by
  have h2n : (0:ℝ) < (2:ℝ)^n := by positivity
  let z : ℂ := ⟨(p.1:ℝ)/2^n, (p.2:ℝ)/2^n⟩
  have hzcell : z ∈ dyadicCell n p := by
    refine ⟨le_refl _, ?_, le_refl _, ?_⟩
    · exact div_le_div_of_nonneg_right (by linarith : (p.1:ℝ) ≤ (p.1:ℝ)+1) (le_of_lt h2n)
    · exact div_le_div_of_nonneg_right (by linarith : (p.2:ℝ) ≤ (p.2:ℝ)+1) (le_of_lt h2n)
  have hzball := h hzcell
  rw [Metric.mem_ball, dist_zero_right] at hzball
  have haux : ∀ (k : ℤ) (x : ℝ), x = (k:ℝ)/2^n → |x| < (n:ℝ)+1 →
      |k| ≤ dyadicBound n := by
    intro k x hx hxl
    have h1 : |(k:ℝ)|/2^n = |x| := by rw [hx, abs_div, abs_of_pos h2n]
    have h2 : |(k:ℝ)|/2^n < (n:ℝ)+1 := by rw [h1]; exact hxl
    rw [div_lt_iff₀ h2n] at h2
    have h3 : |(k:ℝ)| < (2:ℝ)^n * ((n:ℝ)+1) := by
      rw [mul_comm] at h2; linarith
    have hc : ((|k| : ℤ) : ℝ) < (((2:ℤ)^n * ((n:ℤ)+1) + 1 : ℤ) : ℝ) := by
      simp only [Int.cast_abs, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
        Int.cast_natCast, Int.cast_one]
      linarith
    have h4 : (|k| : ℤ) < (2:ℤ)^n * ((n:ℤ)+1) + 1 := by exact_mod_cast hc
    dsimp [dyadicBound]
    exact le_of_lt h4
  exact ⟨haux p.1 z.re rfl (lt_of_le_of_lt (Complex.abs_re_le_norm z) hzball),
         haux p.2 z.im rfl (lt_of_le_of_lt (Complex.abs_im_le_norm z) hzball)⟩

lemma mem_dyadicAmbientBox_of_subset_ball {n : ℕ} {q : ℤ × ℤ}
    (h : dyadicCell n q ⊆ Metric.ball 0 ((n:ℝ)+1)) :
    q ∈ (Finset.Icc (-(dyadicBound n)) (dyadicBound n) ×ˢ
         Finset.Icc (-(dyadicBound n)) (dyadicBound n)) := by
  obtain ⟨h1, h2⟩ := dyadicCell_index_bound h
  obtain ⟨ha1, ha2⟩ := abs_le.mp h1
  obtain ⟨hb1, hb2⟩ := abs_le.mp h2
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  exact ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩

theorem exists_dyadic_exhaustion_of_isOpen_complex
    (U : Set ℂ) (hU : IsOpen U) :
    ∃ K : ℕ → Set ℂ,
      (∀ n, K n ⊆ K (n + 1)) ∧ (∀ n, K n ⊆ U) ∧
      (∀ x ∈ U, ∃ n, ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ K n) ∧
      (∀ n, ∃ S : Finset (ℤ × ℤ), K n = ⋃ p ∈ S,
        {z : ℂ | (p.1 : ℝ) / 2 ^ n ≤ z.re ∧ z.re ≤ ((p.1 : ℝ) + 1) / 2 ^ n ∧
                 (p.2 : ℝ) / 2 ^ n ≤ z.im ∧ z.im ≤ ((p.2 : ℝ) + 1) / 2 ^ n}) := by
  classical
  let S : ℕ → Finset (ℤ × ℤ) := fun n =>
    (Finset.Icc (-(dyadicBound n)) (dyadicBound n) ×ˢ
     Finset.Icc (-(dyadicBound n)) (dyadicBound n)).filter
      (fun p => dyadicCell n p ⊆ U ∧ dyadicCell n p ⊆ Metric.ball 0 ((n:ℝ)+1))
  let K : ℕ → Set ℂ := fun n => ⋃ p ∈ S n, dyadicCell n p
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · intro n z hz
    simp only [K, Set.mem_iUnion] at hz
    obtain ⟨p, hp, hpz⟩ := hz
    obtain ⟨hmem, hpU, hpBall⟩ := Finset.mem_filter.mp hp
    have hballmono : Metric.ball (0:ℂ) ((n:ℝ)+1) ⊆ Metric.ball 0 (((n+1:ℕ):ℝ)+1) :=
      Metric.ball_subset_ball (by push_cast; linarith)
    rcases dyadicCell_mem_child hpz with h0 | h0 | h0 | h0
    · have hsub : dyadicCell (n+1) (2*p.1, 2*p.2) ⊆ dyadicCell n p :=
        dyadicCell_child00_subset n p
      have hqU : dyadicCell (n+1) (2*p.1, 2*p.2) ⊆ U := subset_trans hsub hpU
      have hqBall : dyadicCell (n+1) (2*p.1, 2*p.2) ⊆ Metric.ball 0 (((n+1:ℕ):ℝ)+1) :=
        subset_trans hsub (subset_trans hpBall hballmono)
      have hqS : (2*p.1, 2*p.2) ∈ S (n+1) := by
        simp only [S, Finset.mem_filter]
        exact ⟨mem_dyadicAmbientBox_of_subset_ball hqBall, hqU, hqBall⟩
      change z ∈ ⋃ p ∈ S (n+1), dyadicCell (n+1) p
      exact Set.mem_iUnion₂.mpr ⟨_, hqS, h0⟩
    · have hsub : dyadicCell (n+1) (2*p.1+1, 2*p.2) ⊆ dyadicCell n p :=
        dyadicCell_child10_subset n p
      have hqU : dyadicCell (n+1) (2*p.1+1, 2*p.2) ⊆ U := subset_trans hsub hpU
      have hqBall : dyadicCell (n+1) (2*p.1+1, 2*p.2) ⊆ Metric.ball 0 (((n+1:ℕ):ℝ)+1) :=
        subset_trans hsub (subset_trans hpBall hballmono)
      have hqS : (2*p.1+1, 2*p.2) ∈ S (n+1) := by
        simp only [S, Finset.mem_filter]
        exact ⟨mem_dyadicAmbientBox_of_subset_ball hqBall, hqU, hqBall⟩
      change z ∈ ⋃ p ∈ S (n+1), dyadicCell (n+1) p
      exact Set.mem_iUnion₂.mpr ⟨_, hqS, h0⟩
    · have hsub : dyadicCell (n+1) (2*p.1, 2*p.2+1) ⊆ dyadicCell n p :=
        dyadicCell_child01_subset n p
      have hqU : dyadicCell (n+1) (2*p.1, 2*p.2+1) ⊆ U := subset_trans hsub hpU
      have hqBall : dyadicCell (n+1) (2*p.1, 2*p.2+1) ⊆ Metric.ball 0 (((n+1:ℕ):ℝ)+1) :=
        subset_trans hsub (subset_trans hpBall hballmono)
      have hqS : (2*p.1, 2*p.2+1) ∈ S (n+1) := by
        simp only [S, Finset.mem_filter]
        exact ⟨mem_dyadicAmbientBox_of_subset_ball hqBall, hqU, hqBall⟩
      change z ∈ ⋃ p ∈ S (n+1), dyadicCell (n+1) p
      exact Set.mem_iUnion₂.mpr ⟨_, hqS, h0⟩
    · have hsub : dyadicCell (n+1) (2*p.1+1, 2*p.2+1) ⊆ dyadicCell n p :=
        dyadicCell_child11_subset n p
      have hqU : dyadicCell (n+1) (2*p.1+1, 2*p.2+1) ⊆ U := subset_trans hsub hpU
      have hqBall : dyadicCell (n+1) (2*p.1+1, 2*p.2+1) ⊆ Metric.ball 0 (((n+1:ℕ):ℝ)+1) :=
        subset_trans hsub (subset_trans hpBall hballmono)
      have hqS : (2*p.1+1, 2*p.2+1) ∈ S (n+1) := by
        simp only [S, Finset.mem_filter]
        exact ⟨mem_dyadicAmbientBox_of_subset_ball hqBall, hqU, hqBall⟩
      change z ∈ ⋃ p ∈ S (n+1), dyadicCell (n+1) p
      exact Set.mem_iUnion₂.mpr ⟨_, hqS, h0⟩
  · intro n z hz
    simp only [K, Set.mem_iUnion] at hz
    obtain ⟨p, hp, hpz⟩ := hz
    exact (Finset.mem_filter.mp hp).2.1 hpz
  · intro x hx
    obtain ⟨ε, hεpos, hεU⟩ := Metric.isOpen_iff.mp hU x hx
    obtain ⟨n, hn⟩ := exists_nat_ge (max (‖x‖ + ε) (2*Real.sqrt 2/ε))
    have hn1 : ‖x‖ + ε ≤ (n:ℝ) := le_trans (le_max_left _ _) hn
    have hn2 : 2*Real.sqrt 2/ε ≤ (n:ℝ) := le_trans (le_max_right _ _) hn
    refine ⟨n, ε/2, by positivity, ?_⟩
    have hpow_ge : (n:ℝ) + 1 ≤ (2:ℝ)^n := by
      have h : (n+1 : ℕ) ≤ 2^n := Nat.succ_le_of_lt (Nat.lt_two_pow_self)
      have h' : ((n+1 : ℕ) : ℝ) ≤ ((2^n : ℕ) : ℝ) := by exact_mod_cast h
      rw [Nat.cast_pow] at h'; push_cast at h'; exact h'
    have h2n : (0:ℝ) < (2:ℝ)^n := by positivity
    have hA : 2*Real.sqrt 2/ε ≤ (2:ℝ)^n :=
      le_trans hn2 (le_trans (by linarith : (n:ℝ) ≤ (n:ℝ)+1) hpow_ge)
    have hsl : Real.sqrt 2 ≤ (ε/2)*(2:ℝ)^n := by
      have hmul := mul_le_mul_of_nonneg_right hA (by positivity : (0:ℝ) ≤ ε/2)
      have hlhs : (2*Real.sqrt 2/ε)*(ε/2) = Real.sqrt 2 := by field_simp
      rw [hlhs] at hmul
      nlinarith [hmul]
    have hsqrt_le : Real.sqrt 2 / 2^n ≤ ε/2 := by
      rw [div_le_iff₀ h2n]; exact hsl
    intro z hz
    rw [Metric.mem_ball] at hz
    obtain ⟨p, hpz⟩ := dyadicCell_grid_cover n z
    have hdist : ∀ w ∈ dyadicCell n p, dist w x < ε := by
      intro w hw
      have h1 : dist w z ≤ Real.sqrt 2/2^n := dyadicCell_dist_le hw hpz
      have h2 : dist w x ≤ dist w z + dist z x := dist_triangle w z x
      linarith
    have hcellU : dyadicCell n p ⊆ U := fun w hw => hεU (by rw [Metric.mem_ball]; exact hdist w hw)
    have hcellBall : dyadicCell n p ⊆ Metric.ball 0 ((n:ℝ)+1) := by
      intro w hw
      rw [Metric.mem_ball, dist_zero_right]
      have h2 : dist w 0 ≤ dist w x + dist x 0 := dist_triangle w x 0
      simp only [dist_zero_right] at h2
      have h3 : dist w x < ε := hdist w hw
      linarith
    have hpS : p ∈ S n := by
      simp only [S, Finset.mem_filter]
      exact ⟨mem_dyadicAmbientBox_of_subset_ball hcellBall, hcellU, hcellBall⟩
    change z ∈ ⋃ p ∈ S n, dyadicCell n p
    exact Set.mem_iUnion₂.mpr ⟨p, hpS, hpz⟩
  · intro n
    exact ⟨S n, rfl⟩


end Commons.Topology.Plane