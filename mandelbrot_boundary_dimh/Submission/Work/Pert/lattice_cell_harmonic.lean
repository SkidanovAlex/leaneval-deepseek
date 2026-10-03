import Mathlib
import Submission.Work.Pert.LCH.harmonic_le_log
import Submission.Work.Pert.LCH.infDist_int_eq_round
import Submission.Work.Pert.LCH.layer_cake_pointwise
import Submission.Work.Pert.LCH.scalar_log_le
import Submission.Work.Pert.LCH.card_le_of_gap

set_option maxHeartbeats 4000000

namespace Work.Pert

open scoped Classical

/-- Scalar logarithmic step used at the end of the proof. -/
private lemma aux_logstep {K L X Y : ℝ} (hK : 2 * L ≤ K) (hL : 0 ≤ L)
    (hlog : Y + Real.log 2 ≤ X) : 8 * L / 3 ≤ K * (1 + X - Y) := by
  have h13 : (4 : ℝ) / 3 ≤ 1 + Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h2 : (4 : ℝ) / 3 ≤ 1 + X - Y := by linarith
  have h3 : 8 * L / 3 = 2 * L * ((4 : ℝ) / 3) := by ring
  have h4 : 2 * L * ((4 : ℝ) / 3) ≤ 2 * L * (1 + X - Y) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have h5 : 2 * L * (1 + X - Y) ≤ K * (1 + X - Y) :=
    mul_le_mul_of_nonneg_right hK (by linarith)
  linarith [h3, h4, h5]

/-- Monotonicity/gap bound: consecutive increments are at least `c₀`. -/
private lemma gap_lower {m : ℕ → ℝ} {c₀ : ℝ} {n : ℕ}
    (hstep : ∀ j < n, c₀ ≤ m (j + 1) - m j) :
    ∀ j j' : ℕ, j ≤ j' → j' < n → ((j' : ℝ) - (j : ℝ)) * c₀ ≤ m j' - m j := by
  have key : ∀ j d : ℕ, j + d < n → (d : ℝ) * c₀ ≤ m (j + d) - m j := by
    intro j d
    induction d with
    | zero => intro _; simp
    | succ e ih =>
      intro h
      have h1 : (e : ℝ) * c₀ ≤ m (j + e) - m j := ih (by omega)
      have h2 := hstep (j + e) (by omega)
      have hje : j + (e + 1) = (j + e) + 1 := by omega
      rw [hje]
      push_cast
      linarith [h1, h2]
  intro j j' hjj hjn
  have h := key j (j' - j) (by omega)
  rw [Nat.cast_sub hjj] at h
  rwa [Nat.add_sub_of_le hjj] at h

/-- Upper bound: the total increment of `m` over `j` steps is at most `j * c₁`. -/
private lemma sum_upper {m : ℕ → ℝ} {c₁ : ℝ} {n : ℕ}
    (hstep : ∀ j < n, m (j + 1) - m j ≤ c₁) :
    ∀ j, j < n → m j - m 0 ≤ (j : ℝ) * c₁ := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hkn : k < n := by omega
    have h1 := ih hkn
    have h2 := hstep k hkn
    push_cast
    linarith

/-- Counting lemma: points whose nearest-integer distance is at most `s` are
confined to cells around integers, and each cell contributes at most `2s/c₀ + 1`
points. -/
private lemma cell_count_le {m : ℕ → ℝ} {c₀ : ℝ} {n : ℕ} {s : ℝ}
    (hc0 : 0 < c₀) (hn : 1 ≤ n) (hs : 0 < s) (hs2 : s ≤ 1 / 2)
    (hstep : ∀ j < n, c₀ ≤ m (j + 1) - m j) :
    (((Finset.range n).filter
        (fun j => Metric.infDist (m j) (Set.range (fun k : ℤ => (k : ℝ))) ≤ s)).card : ℝ)
      ≤ (m (n - 1) - m 0 + 2) * (2 * s / c₀ + 1) := by
  set S : Finset ℕ := (Finset.range n).filter
    (fun j => Metric.infDist (m j) (Set.range (fun k : ℤ => (k : ℝ))) ≤ s) with hS
  set K : Finset ℤ := Finset.Icc ⌊m 0 + 1 / 2⌋ ⌊m (n - 1) + 1 / 2⌋ with hK
  have hc0' : 0 ≤ c₀ := le_of_lt hc0
  -- monotonicity of m on {0,…,n-1}
  have hmono : ∀ {i j : ℕ}, i ≤ j → j < n → m i ≤ m j := by
    intro i j hij hjn
    have h := gap_lower hstep i j hij hjn
    have hnn : (0 : ℝ) ≤ (j : ℝ) - (i : ℝ) := by
      have h' : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_le.mpr hij
      linarith
    have : (0 : ℝ) ≤ ((j : ℝ) - (i : ℝ)) * c₀ := mul_nonneg hnn hc0'
    linarith
  -- each element of S maps into K
  have hmap : ∀ j ∈ S, ⌊m j + 1 / 2⌋ ∈ K := by
    intro j hj
    simp only [hS, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjn, _⟩ := hj
    have h1 : m 0 ≤ m j := hmono (Nat.zero_le _) hjn
    have h2 : m j ≤ m (n - 1) := hmono (by omega) (by omega)
    simp only [hK, Finset.mem_Icc]
    exact ⟨Int.floor_mono (by linarith), Int.floor_mono (by linarith)⟩
  -- fiberwise bound
  have hfib : ∀ k ∈ K, ((S.filter (fun j => ⌊m j + 1 / 2⌋ = k)).card : ℝ) ≤ 2 * s / c₀ + 1 := by
    intro k hk
    have hcard : ((S.filter (fun j => ⌊m j + 1 / 2⌋ = k)).card : ℝ) ≤
        (((k : ℝ) + s) - ((k : ℝ) - s)) / c₀ + 1 := by
      apply LCH.card_le_of_gap hc0 hstep
      · intro j hj
        simp only [Finset.mem_filter] at hj
        obtain ⟨hjS, _⟩ := hj
        simp only [hS, Finset.mem_filter, Finset.mem_range] at hjS
        exact hjS.1
      · linarith
      · intro j hj
        simp only [Finset.mem_filter] at hj
        obtain ⟨hjS, hjk⟩ := hj
        simp only [hS, Finset.mem_filter, Finset.mem_range] at hjS
        obtain ⟨hjn, hjs⟩ := hjS
        have hid := LCH.infDist_int_eq_round (m j)
        have hlt : |m j - ((⌊m j + 1 / 2⌋ : ℤ) : ℝ)| ≤ s := by
          rw [← hid]; exact hjs
        rw [hjk] at hlt
        obtain ⟨hlo, hhi⟩ := abs_le.mp hlt
        exact ⟨by linarith, by linarith⟩
    have hval : (((k : ℝ) + s) - ((k : ℝ) - s)) / c₀ + 1 = 2 * s / c₀ + 1 := by
      ring
    linarith [hcard, hval]
  -- sum over fibers
  have hcard_sum : (S.card : ℝ) = ∑ k ∈ K, ((S.filter (fun j => ⌊m j + 1 / 2⌋ = k)).card : ℝ) := by
    have hfiber := Finset.card_eq_sum_card_fiberwise (s := S) (t := K)
      (f := fun j => ⌊m j + 1 / 2⌋) (by
        intro j hj
        exact hmap j (by simpa using hj))
    rw [hfiber]
    push_cast
    rfl
  -- |K| ≤ L + 2
  have hKcard : ((K.card : ℝ)) ≤ (m (n - 1) - m 0) + 2 := by
    have hfloor1 : (⌊m (n - 1) + 1 / 2⌋ : ℝ) ≤ m (n - 1) + 1 / 2 := Int.floor_le _
    have hfloor2 : m 0 + 1 / 2 - 1 < (⌊m 0 + 1 / 2⌋ : ℝ) := by
      have := Int.lt_floor_add_one (m 0 + 1 / 2)
      linarith
    have hdiff : ((⌊m (n - 1) + 1 / 2⌋ + 1 - ⌊m 0 + 1 / 2⌋ : ℤ) : ℝ) <
        (m (n - 1) - m 0) + 2 := by
      push_cast
      linarith
    rw [hK, Int.card_Icc]
    have hle : ⌊m 0 + 1 / 2⌋ ≤ ⌊m (n - 1) + 1 / 2⌋ := by
      apply Int.floor_mono
      have := hmono (i := 0) (j := n - 1) (Nat.zero_le _) (by omega)
      linarith
    have hnn : (0 : ℤ) ≤ ⌊m (n - 1) + 1 / 2⌋ + 1 - ⌊m 0 + 1 / 2⌋ := by omega
    have hcast : ((((⌊m (n - 1) + 1 / 2⌋ + 1 - ⌊m 0 + 1 / 2⌋).toNat : ℕ)) : ℝ)
        = ((⌊m (n - 1) + 1 / 2⌋ + 1 - ⌊m 0 + 1 / 2⌋ : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
    rw [hcast]
    have : ((⌊m (n - 1) + 1 / 2⌋ + 1 - ⌊m 0 + 1 / 2⌋ : ℤ) : ℝ) ≤ (m (n - 1) - m 0) + 2 :=
      le_of_lt hdiff
    exact this
  -- conclude
  have hsum_le : (S.card : ℝ) ≤ ∑ k ∈ K, (2 * s / c₀ + 1) := by
    rw [hcard_sum]
    exact Finset.sum_le_sum (fun k hk => hfib k hk)
  have hcollapse : (∑ k ∈ K, (2 * s / c₀ + 1)) = ((K.card : ℕ) : ℝ) * (2 * s / c₀ + 1) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hcollapse] at hsum_le
  have hKnn : (0 : ℝ) ≤ 2 * s / c₀ + 1 := by positivity
  calc (S.card : ℝ) ≤ (K.card : ℝ) * (2 * s / c₀ + 1) := hsum_le
    _ ≤ ((m (n - 1) - m 0) + 2) * (2 * s / c₀ + 1) :=
        mul_le_mul_of_nonneg_right hKcard hKnn

theorem lattice_cell_harmonic {m : ℕ → ℝ} {c₀ c₁ H : ℝ} {n : ℕ}
    (hc0 : 0 < c₀) (hH : 0 < H) (hc1 : c₁ < 1)
    (hstep : ∀ j < n, c₀ ≤ m (j+1) - m j ∧ m (j+1) - m j ≤ c₁) :
    (∑ j ∈ Finset.range n,
        1 / max (Metric.infDist (m j) (Set.range (fun k : ℤ => (k : ℝ)))) H)
      ≤ ((n : ℝ) * c₁ + 2) * ((2 / c₀) * (2 + Real.log (2 + 1 / H)) + 1 / H) := by
  have hstepL : ∀ j < n, c₀ ≤ m (j + 1) - m j := fun j hj => (hstep j hj).1
  have hstepU : ∀ j < n, m (j + 1) - m j ≤ c₁ := fun j hj => (hstep j hj).2
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul, zero_add]
    have h2 : 0 < (2 / c₀) * (2 + Real.log (2 + 1 / H)) + 1 / H := by
      have hp : 0 < 1 / H := one_div_pos.mpr hH
      have hl : 0 < Real.log (2 + 1 / H) := Real.log_pos (by linarith)
      have h2a : 0 < 2 + Real.log (2 + 1 / H) := by linarith
      have h2b : 0 < 2 / c₀ := by positivity
      have := mul_pos h2b h2a
      linarith
    exact mul_nonneg (by norm_num) (le_of_lt h2)
  · have hn1 : 1 ≤ n := hn
    have hc01 : c₀ ≤ c₁ := le_trans (hstepL 0 (by omega)) (hstepU 0 (by omega))
    have hc1pos : 0 < c₁ := lt_of_lt_of_le hc0 hc01
    have hm0L : m 0 ≤ m (n - 1) := by
      have h := gap_lower hstepL 0 (n - 1) (by omega) (by omega)
      simp only [Nat.cast_zero, sub_zero] at h
      have : (0 : ℝ) ≤ (((n - 1 : ℕ)) : ℝ) * c₀ := mul_nonneg (Nat.cast_nonneg _) (le_of_lt hc0)
      linarith
    have hLub : m (n - 1) - m 0 ≤ ((n - 1 : ℕ) : ℝ) * c₁ := sum_upper hstepU (n - 1) (by omega)
    have hLbA : m (n - 1) - m 0 + 2 ≤ (n : ℝ) * c₁ + 2 := by
      have hle : (((n - 1 : ℕ)) : ℝ) ≤ (n : ℝ) := by
        have : (n - 1 : ℕ) ≤ n := by omega
        exact_mod_cast this
      have := mul_le_mul_of_nonneg_right hle (le_of_lt hc1pos)
      linarith
    set A : ℝ := (n : ℝ) * c₁ + 2 with hA
    have hAcore : 2 * (n : ℝ) ≤ A * (2 / c₀) := by
      rw [hA]
      have h1 : 1 / c₁ ≤ 1 / c₀ := one_div_le_one_div_of_le hc0 hc01
      have hdiv : 2 / c₁ ≤ 2 / c₀ := by
        have h := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
        calc 2 / c₁ = 2 * (1 / c₁) := by ring
          _ ≤ 2 * (1 / c₀) := h
          _ = 2 / c₀ := by ring
      have h2 : 2 * (n : ℝ) = ((n : ℝ) * c₁) * (2 / c₁) := by
        field_simp
      rw [h2]
      calc ((n : ℝ) * c₁) * (2 / c₁) ≤ ((n : ℝ) * c₁ + 2) * (2 / c₁) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ ≤ ((n : ℝ) * c₁ + 2) * (2 / c₀) :=
            mul_le_mul_of_nonneg_left hdiv (by positivity)
    by_cases hbig : (1 : ℝ) / 8 ≤ H
    · -- ### Case A: `1/8 ≤ H`, so `1/H ≤ 8`
      have hInv : 1 / H ≤ 8 := by
        rw [div_le_iff₀ hH]
        linarith
      have hX0 : 0 ≤ 2 + Real.log (2 + 1 / H) := by
        have hp : 0 < 1 / H := one_div_pos.mpr hH
        have : 0 < Real.log (2 + 1 / H) := Real.log_pos (by linarith)
        linarith
      have hscal : (1 - c₁) * (1 / H) ≤ 2 * (2 + Real.log (2 + 1 / H)) :=
        LCH.scalar_log_le (by linarith) (one_div_pos.mpr hH) hInv
      have hsumA : (∑ j ∈ Finset.range n,
            1 / max (Metric.infDist (m j) (Set.range (fun k : ℤ => (k : ℝ)))) H)
          ≤ (n : ℝ) * (1 / H) := by
        calc (∑ j ∈ Finset.range n,
              1 / max (Metric.infDist (m j) (Set.range (fun k : ℤ => (k : ℝ)))) H)
            ≤ ∑ j ∈ Finset.range n, 1 / H :=
              Finset.sum_le_sum (fun j _ => one_div_le_one_div_of_le hH (le_max_right _ _))
          _ = (n : ℝ) * (1 / H) := by rw [Finset.sum_const, nsmul_eq_mul]; simp
      refine le_trans hsumA ?_
      have hkey : ((n : ℝ) - A) * (1 / H) ≤ A * (2 / c₀) * (2 + Real.log (2 + 1 / H)) := by
        have h1 : (n : ℝ) - A ≤ (n : ℝ) * (1 - c₁) := by rw [hA]; ring_nf; linarith
        have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt (one_div_pos.mpr hH))
        have h4 := mul_le_mul_of_nonneg_left hscal (by positivity : (0 : ℝ) ≤ (n : ℝ))
        have h5 := mul_le_mul_of_nonneg_right hAcore hX0
        have h6 : (n : ℝ) * (1 - c₁) * (1 / H) = (n : ℝ) * ((1 - c₁) * (1 / H)) := by ring
        have h7 : (2 * (n : ℝ)) * (2 + Real.log (2 + 1 / H))
            = (n : ℝ) * (2 * (2 + Real.log (2 + 1 / H))) := by ring
        linarith [h2, h4, h5, h6, h7]
      have hkey2 : (n : ℝ) * (1 / H) = ((n : ℝ) - A) * (1 / H) + A * (1 / H) := by ring
      have hkey3 : A * ((2 / c₀) * (2 + Real.log (2 + 1 / H)) + 1 / H)
          = A * (2 / c₀) * (2 + Real.log (2 + 1 / H)) + A * (1 / H) := by ring
      linarith [hkey, hkey2, hkey3]
    · -- ### Case B: `H < 1/8`
      have hHsmall : H < 1 / 8 := lt_of_not_ge hbig
      obtain ⟨M, hMle, hMlt⟩ : ∃ M : ℕ, (M : ℝ) ≤ 1 / (2 * H) ∧ 1 / (2 * H) < (M : ℝ) + 1 :=
        ⟨Nat.floor (1 / (2 * H)), Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩
      have h2Hpos : (0 : ℝ) < 2 * H := by linarith
      have h2Hne : (2 : ℝ) * H ≠ 0 := ne_of_gt h2Hpos
      have hM4 : 4 ≤ M := by
        have h4 : (4 : ℝ) < 1 / (2 * H) := by
          have h' : 4 * (2 * H) < (1 / (2 * H)) * (2 * H) := by
            rw [one_div_mul_cancel h2Hne]
            linarith
          exact lt_of_mul_lt_mul_right h' (le_of_lt h2Hpos)
        have h5 : (4 : ℝ) < (M : ℝ) + 1 := lt_trans h4 hMlt
        have h6 : (3 : ℝ) < (M : ℝ) := by linarith
        have h7 : 3 < M := by exact_mod_cast h6
        omega
      have hMH1 : (M : ℝ) * H ≤ 1 / 2 := by
        have h' : (M : ℝ) * (2 * H) ≤ 1 := by
          have h := mul_le_mul_of_nonneg_right hMle (le_of_lt h2Hpos)
          rwa [one_div_mul_cancel h2Hne] at h
        linarith
      have hMH2 : (3 : ℝ) / 8 ≤ (M : ℝ) * H := by
        have h' : 1 < ((M : ℝ) + 1) * (2 * H) := by
          have h := mul_lt_mul_of_pos_right hMlt h2Hpos
          rwa [one_div_mul_cancel h2Hne] at h
        nlinarith [h', hHsmall, hH]
      have hcastM : (((M - 1 : ℕ)) : ℝ) + 1 = (M : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ M)]
        ring
      set W : ℕ → ℝ := fun i => 1 / (((i : ℝ) + 1) * H) - 1 / (((i : ℝ) + 2) * H) with hW
      set Nn : ℕ → ℝ := fun i =>
        (((Finset.range n).filter (fun j =>
          Metric.infDist (m j) (Set.range (fun k : ℤ => (k : ℝ))) ≤ ((i : ℝ) + 2) * H)).card : ℝ)
        with hNn
      have hWi : ∀ i : ℕ, 0 ≤ W i := by
        intro i
        rw [hW]
        have h1 : (0 : ℝ) < (((i : ℝ) + 1) * H) := by positivity
        have h2 : (((i : ℝ) + 1) * H) ≤ (((i : ℝ) + 2) * H) := by linarith
        have := one_div_le_one_div_of_le h1 h2
        linarith
      have hcount : ∀ i ∈ Finset.range (M - 1),
          Nn i ≤ (m (n - 1) - m 0 + 2) * (2 * (((i : ℝ) + 2) * H) / c₀ + 1) := by
        intro i hi
        rw [hNn]
        simp only []
        simp only [Finset.mem_range] at hi
        have hiM : (i : ℝ) + 2 ≤ (M : ℝ) := by
          have : i + 2 ≤ M := by omega
          exact_mod_cast this
        have hsle : ((i : ℝ) + 2) * H ≤ 1 / 2 := by nlinarith [hMH1, hiM, hH]
        have hspos : 0 < ((i : ℝ) + 2) * H := by positivity
        exact cell_count_le hc0 hn1 hspos hsle hstepL
      have hlayer : ∀ j : ℕ,
          1 / max (Metric.infDist (m j) (Set.range (fun k : ℤ => (k : ℝ)))) H
            ≤ (∑ i ∈ Finset.range (M - 1),
                W i * (if Metric.infDist (m j) (Set.range (fun k : ℤ => (k : ℝ)))
                    ≤ ((i : ℝ) + 2) * H then (1 : ℝ) else 0))
              + 1 / ((M : ℝ) * H) := by
        intro j
        have h := LCH.layer_cake_pointwise
          (d := Metric.infDist (m j) (Set.range (fun k : ℤ => (k : ℝ)))) (H := H)
          (Metric.infDist_nonneg) hH (M - 1)
        rw [hcastM] at h
        exact h
      have hinner : ∀ i : ℕ,
          (∑ j ∈ Finset.range n, W i * (if Metric.infDist (m j) (Set.range (fun k : ℤ => (k : ℝ)))
              ≤ ((i : ℝ) + 2) * H then (1 : ℝ) else 0)) = W i * Nn i := by
        intro i
        rw [← Finset.mul_sum]
        congr 1
        rw [hNn]
        simp only []
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have h1 : (∑ j ∈ Finset.range n,
            1 / max (Metric.infDist (m j) (Set.range (fun k : ℤ => (k : ℝ)))) H)
          ≤ (∑ i ∈ Finset.range (M - 1), W i * Nn i) + (n : ℝ) * (1 / ((M : ℝ) * H)) := by
        have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range n) => hlayer j)
        rw [Finset.sum_add_distrib] at h
        have hc : (∑ j ∈ Finset.range n, 1 / ((M : ℝ) * H))
            = (n : ℝ) * (1 / ((M : ℝ) * H)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp
        rw [hc] at h
        rw [Finset.sum_comm] at h
        rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range (M - 1)) => hinner i)] at h
        exact h
      have h2 : (∑ i ∈ Finset.range (M - 1), W i * Nn i)
          ≤ (m (n - 1) - m 0 + 2) * ((2 / c₀) * (∑ i ∈ Finset.range (M - 1), 1 / ((i : ℝ) + 1))
              + (1 / H - 1 / ((M : ℝ) * H))) := by
        have hb : (∑ i ∈ Finset.range (M - 1), W i * Nn i)
            ≤ ∑ i ∈ Finset.range (M - 1),
                W i * ((m (n - 1) - m 0 + 2) * (2 * (((i : ℝ) + 2) * H) / c₀ + 1)) :=
          Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hcount i hi) (hWi i))
        have hdist : ∀ i : ℕ,
            W i * ((m (n - 1) - m 0 + 2) * (2 * (((i : ℝ) + 2) * H) / c₀ + 1))
              = W i * ((m (n - 1) - m 0 + 2) * (2 * (((i : ℝ) + 2) * H) / c₀))
                + W i * (m (n - 1) - m 0 + 2)
                * 1 := by
          intro i
          ring
        have hstep1 : (∑ i ∈ Finset.range (M - 1),
              W i * ((m (n - 1) - m 0 + 2) * (2 * (((i : ℝ) + 2) * H) / c₀ + 1)))
            = (m (n - 1) - m 0 + 2)
              * (∑ i ∈ Finset.range (M - 1), W i * (2 * (((i : ℝ) + 2) * H) / c₀ + 1)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        have hstep2 : (∑ i ∈ Finset.range (M - 1), W i * (2 * (((i : ℝ) + 2) * H) / c₀ + 1))
            = (2 / c₀) * (∑ i ∈ Finset.range (M - 1), W i * (((i : ℝ) + 2) * H))
              + (∑ i ∈ Finset.range (M - 1), W i) := by
          have e1 : ∀ i : ℕ, W i * (2 * (((i : ℝ) + 2) * H) / c₀ + 1)
              = W i * (2 * (((i : ℝ) + 2) * H) / c₀) + W i := by
            intro i; ring
          have e2 : (∑ i ∈ Finset.range (M - 1), W i * (2 * (((i : ℝ) + 2) * H) / c₀))
              = (2 / c₀) * (∑ i ∈ Finset.range (M - 1), W i * (((i : ℝ) + 2) * H)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
          rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range (M - 1)) => e1 i),
            Finset.sum_add_distrib, e2]
        have hstep3 : (∑ i ∈ Finset.range (M - 1), W i * (((i : ℝ) + 2) * H))
            = (∑ i ∈ Finset.range (M - 1), 1 / ((i : ℝ) + 1)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hW]
          have h1 : (((i : ℝ) + 1) * H) ≠ 0 := by positivity
          have h2 : (((i : ℝ) + 2) * H) ≠ 0 := by positivity
          field_simp
          ring
        have hstep4 : (∑ i ∈ Finset.range (M - 1), W i) = 1 / H - 1 / ((M : ℝ) * H) := by
          rw [hW]
          have h := Finset.sum_range_sub' (fun i : ℕ => 1 / (((i : ℝ) + 1) * H)) (M - 1)
          have h' : (∑ i ∈ Finset.range (M - 1),
                (1 / (((i : ℝ) + 1) * H) - 1 / (((i : ℝ) + 2) * H)))
              = (fun i : ℕ => 1 / (((i : ℝ) + 1) * H)) 0
                - (fun i : ℕ => 1 / (((i : ℝ) + 1) * H)) (M - 1) := by
            rw [← h]
            apply Finset.sum_congr rfl
            intro i _
            simp only [Nat.cast_add, Nat.cast_one]
            ring
          rw [h']
          simp only [hcastM, Nat.cast_zero, zero_add, one_mul]
        rw [hstep1, hstep2, hstep3, hstep4] at hb
        exact hb
      have h3 : (∑ i ∈ Finset.range (M - 1), 1 / ((i : ℝ) + 1))
          ≤ 1 + Real.log (((M - 1 : ℕ)) : ℝ) := LCH.harmonic_le_log (M - 1)
      have hLb0 : 0 ≤ m (n - 1) - m 0 + 2 := by linarith [hm0L]
      have hM1pos : (1 : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by
        have : 1 ≤ M - 1 := by omega
        exact_mod_cast this
      have hlog1 : 0 ≤ Real.log (((M - 1 : ℕ)) : ℝ) := Real.log_nonneg hM1pos
      have hlog : Real.log (((M - 1 : ℕ)) : ℝ) + Real.log 2 ≤ Real.log (2 + 1 / H) := by
        have hpos : (0 : ℝ) < ((M - 1 : ℕ) : ℝ) := by linarith
        rw [← Real.log_mul (ne_of_gt hpos) (by norm_num : (2 : ℝ) ≠ 0)]
        apply Real.log_le_log (by positivity)
        have hle : ((M - 1 : ℕ) : ℝ) ≤ (M : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ M)]
          norm_num
        have h2 : 2 * ((M : ℝ) * H) ≤ 1 := by linarith [hMH1]
        have hkey : 2 * ((M : ℝ) - 1) ≤ 2 + 1 / H := by
          have h4 : (2 + 1 / H) * H = 2 * H + 1 := by field_simp
          have h5 : (2 * ((M : ℝ) - 1)) * H ≤ (2 + 1 / H) * H := by
            rw [h4]; nlinarith [h2, hH]
          exact le_of_mul_le_mul_right h5 hH
        linarith
      have hfinal1 : (∑ i ∈ Finset.range (M - 1), W i * Nn i)
          ≤ (m (n - 1) - m 0 + 2) * ((2 / c₀) * (1 + Real.log (((M - 1 : ℕ)) : ℝ))
              + (1 / H - 1 / ((M : ℝ) * H))) := by
        refine le_trans h2 ?_
        apply mul_le_mul_of_nonneg_left _ hLb0
        have hc2 : (0 : ℝ) ≤ 2 / c₀ := by positivity
        have hsum := mul_le_mul_of_nonneg_left h3 hc2
        linarith [hsum]
      have hfinal2 : (m (n - 1) - m 0 + 2)
            * ((2 / c₀) * (1 + Real.log (((M - 1 : ℕ)) : ℝ)) + (1 / H - 1 / ((M : ℝ) * H)))
          ≤ (m (n - 1) - m 0 + 2) * ((2 / c₀) * (1 + Real.log (((M - 1 : ℕ)) : ℝ)) + 1 / H) := by
        apply mul_le_mul_of_nonneg_left _ hLb0
        have h6 : (0 : ℝ) ≤ 1 / ((M : ℝ) * H) := by positivity
        linarith
      have hfinal3 : (n : ℝ) * (1 / ((M : ℝ) * H)) ≤ 8 * (n : ℝ) / 3 := by
        have hd := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ (n : ℝ))
          (by norm_num : (0 : ℝ) < 3 / 8) hMH2
        have he : (n : ℝ) / (3 / 8) = 8 * (n : ℝ) / 3 := by ring
        have hf : (n : ℝ) * (1 / ((M : ℝ) * H)) = (n : ℝ) / ((M : ℝ) * H) := by ring
        rw [hf]
        rw [he] at hd
        exact hd
      have hfin1 : (∑ i ∈ Finset.range (M - 1), W i * Nn i) + (n : ℝ) * (1 / ((M : ℝ) * H))
          ≤ (m (n - 1) - m 0 + 2) * ((2 / c₀) * (1 + Real.log (((M - 1 : ℕ)) : ℝ)) + 1 / H)
            + 8 * (n : ℝ) / 3 := by
        linarith [hfinal1, hfinal2, hfinal3]
      have hfin2 : (m (n - 1) - m 0 + 2) * ((2 / c₀) * (1 + Real.log (((M - 1 : ℕ)) : ℝ)) + 1 / H)
            + 8 * (n : ℝ) / 3
          ≤ A * (2 / c₀) * (1 + Real.log (((M - 1 : ℕ)) : ℝ)) + A / H + 8 * (n : ℝ) / 3 := by
        have hfac : (0 : ℝ) ≤ (2 / c₀) * (1 + Real.log (((M - 1 : ℕ)) : ℝ)) + 1 / H := by
          have hc2 : (0 : ℝ) < 2 / c₀ := by positivity
          have h2b : (0 : ℝ) ≤ 1 + Real.log (((M - 1 : ℕ)) : ℝ) := by linarith
          have hp : (0 : ℝ) < 1 / H := one_div_pos.mpr hH
          exact add_nonneg (mul_nonneg (le_of_lt hc2) h2b) (le_of_lt hp)
        have hthis := mul_le_mul_of_nonneg_right hLbA hfac
        have hsplit : A * ((2 / c₀) * (1 + Real.log (((M - 1 : ℕ)) : ℝ)) + 1 / H)
            = A * (2 / c₀) * (1 + Real.log (((M - 1 : ℕ)) : ℝ)) + A / H := by ring
        linarith [hthis, hsplit]
      have hfin3 : A * (2 / c₀) * (1 + Real.log (((M - 1 : ℕ)) : ℝ)) + A / H + 8 * (n : ℝ) / 3
          ≤ A * ((2 / c₀) * (2 + Real.log (2 + 1 / H)) + 1 / H) := by
        have hE : 8 * (n : ℝ) / 3
            ≤ A * (2 / c₀) * (1 + Real.log (2 + 1 / H) - Real.log (((M - 1 : ℕ)) : ℝ)) :=
          aux_logstep hAcore (by positivity) hlog
        have hk1 : A * (2 / c₀) * (1 + Real.log (((M - 1 : ℕ)) : ℝ))
              + A * (2 / c₀) * (1 + Real.log (2 + 1 / H) - Real.log (((M - 1 : ℕ)) : ℝ))
            = A * (2 / c₀) * (2 + Real.log (2 + 1 / H)) := by ring
        have hk2 : A * ((2 / c₀) * (2 + Real.log (2 + 1 / H)) + 1 / H)
            = A * (2 / c₀) * (2 + Real.log (2 + 1 / H)) + A / H := by ring
        linarith [hE, hk1, hk2]
      exact h1.trans (hfin1.trans (hfin2.trans hfin3))

end Work.Pert
