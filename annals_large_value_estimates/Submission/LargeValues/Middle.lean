import Submission.LargeValues.MiddleHelpers
import Submission.Commons.Analysis.Metric.greedy_real_delta_separated

open LargeValueEstimates
open Asymptotics Complex
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The middle regime of Guth–Maynard Theorem 1.1, reduced to Proposition 4.1

For `N < T`, `4N^{7/10} ≤ V ≤ N^{4/5}` we prove, assuming `KeyPropStatement`
(Guth–Maynard Proposition 4.1), the bound

  `|W| ≤ C · N^{4ε} · bound N V T`

for every `ε > 0` and all `N` large enough.  The argument follows §3 of the paper:
 * split the sum over `[N,2N]` into three pieces (one of which is large at each point);
 * extract a `δ`-separated subfamily (`δ = (2N)^{6ε/5}`) by the greedy lemma;
 * subdivide into windows of length `(N/2)^{6/5}` and apply Proposition 4.1 in each window
   to the rescaled length `N_i ∈ {5N/6, N, 3N/2}` attached to the `i`-th piece.
-/

namespace Submission.LargeValues

/-- Auxiliary: the three pieces as a function on `ℕ → Finset ℝ` is not needed; the statement
below is the middle-regime reduction. -/
theorem middle_regime_bound (hKey : KeyPropStatement) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ (N : ℕ), N₀ ≤ N →
      ∀ (V T : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
        6 ≤ N → (N : ℝ) < T → 4 * (N : ℝ) ^ (7 / 10 : ℝ) ≤ V →
        V ≤ (N : ℝ) ^ (4 / 5 : ℝ) →
        (∀ n, ‖b n‖ ≤ 1) →
        (∀ t ∈ W, t ∈ Set.Icc 0 T) →
        (∀ t ∈ W, ∀ s ∈ W, t ≠ s → 1 ≤ |t - s|) →
        (∀ t ∈ W, V ≤ ‖∑ n ∈ Finset.Icc N (2 * N), b n * (n : ℂ) ^ (I * (t : ℂ))‖) →
        (W.card : ℝ) ≤ C * (N : ℝ) ^ (4 * ε) * bound N V T := by
  refine ⟨40000, by norm_num, ?_⟩
  intro ε hε
  obtain ⟨N₁, _, hKeyN⟩ := hKey ε hε 0
  refine ⟨max (2 * N₁) 64, ?_⟩
  intro N hN V T b W hN6 hNT hVlo hVhi hb hWIcc hWsep hWval
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNr : (6 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN6
  have hTpos : 0 < T := by linarith [hNpos, hNT]
  have h3N : 3 ≤ N := by omega
  -- separations and window lengths
  set δ : ℝ := (2 * (N : ℝ)) ^ (6 * ε / 5) with hδdef
  have hδ1 : 1 ≤ δ := by
    rw [hδdef]
    exact Real.one_le_rpow (by linarith) (by positivity)
  set Lw : ℝ := (N : ℝ) ^ (6 / 5 : ℝ) / 3 with hLwdef
  have hLwpos : 0 < Lw := by rw [hLwdef]; positivity
  have two_rpow_le_three : (2 : ℝ) ^ (6 / 5 : ℝ) ≤ 3 := by
    have h4 : ((2 : ℝ) ^ (6 / 5 : ℝ)) ^ 5 ≤ (3 : ℝ) ^ 5 := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (6 / 5 : ℝ)) 5,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    exact le_of_pow_le_pow_left₀ (by norm_num : (5 : ℕ) ≠ 0) (by positivity) h4
  have Lw_le : ∀ X : ℝ, (N : ℝ) / 2 ≤ X → Lw ≤ X ^ (6 / 5 : ℝ) := by
    intro X hX
    have h1 : Lw ≤ ((N : ℝ) / 2) ^ (6 / 5 : ℝ) := by
      rw [hLwdef, Real.div_rpow (by positivity) (by norm_num)]
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_pos_of_pos (by norm_num) _) two_rpow_le_three
    exact le_trans h1 (Real.rpow_le_rpow (by positivity) hX (by norm_num))
  set K : ℕ := ⌊T / Lw⌋₊ + 1 with hKdef
  -- the three "large" subsets
  set Wi : ℕ → Finset ℝ := fun i => W.filter (fun t => V / 3 ≤ ‖pieceSum N i b t‖) with hWidef
  have hJi_exists : ∀ i : ℕ, ∃ J : Finset ℝ, J ⊆ Wi i ∧
      (∀ t ∈ J, ∀ s ∈ J, t ≠ s → δ ≤ |t - s|) ∧
      (((Wi i).card : ℝ) ≤ (J.card : ℝ) * (2 * δ + 1)) := by
    intro i
    refine Commons.Analysis.Metric.greedy_real_delta_separated (Wi i) ?_ δ hδ1
    intro t ht s hs hts
    exact hWsep t (Finset.mem_of_mem_filter t ht) s (Finset.mem_of_mem_filter s hs) hts
  choose Ji hJisub hJisep hJicard using hJi_exists
  -- covering by the three pieces
  have hex_i : ∀ t ∈ W, ∃ i ∈ Finset.range 3, t ∈ Wi i := by
    intro t ht
    have hval := hWval t ht
    have hsum := sum_pieceSet N (fun n => b n * (n : ℂ) ^ (I * (t : ℂ)))
    rw [← hsum] at hval
    have hle : ‖∑ i ∈ Finset.range 3, pieceSum N i b t‖
        ≤ ∑ i ∈ Finset.range 3, ‖pieceSum N i b t‖ := norm_sum_le _ _
    by_contra hcon
    push_neg at hcon
    have hlt : ∀ i ∈ Finset.range 3, ‖pieceSum N i b t‖ < V / 3 := by
      intro i hi
      have h1 : ¬ (V / 3 ≤ ‖pieceSum N i b t‖) :=
        fun h => hcon i hi (Finset.mem_filter.mpr ⟨ht, h⟩)
      exact lt_of_not_ge h1
    have hstrict : ∑ i ∈ Finset.range 3, ‖pieceSum N i b t‖
        < ∑ i ∈ Finset.range 3, (V / 3 : ℝ) :=
      Finset.sum_lt_sum (fun i hi => le_of_lt (hlt i hi))
        ⟨0, Finset.mem_range.mpr (by norm_num), hlt 0 (Finset.mem_range.mpr (by norm_num))⟩
    have hconst : ∑ i ∈ Finset.range 3, (V / 3 : ℝ) = V := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    rw [hconst] at hstrict
    linarith [le_trans hval hle]
  have hcardW : (W.card : ℝ) ≤ ∑ i ∈ Finset.range 3, ((Wi i).card : ℝ) := by
    have hsub : W ⊆ Wi 0 ∪ Wi 1 ∪ Wi 2 := by
      intro t ht
      obtain ⟨i, hi, hti⟩ := hex_i t ht
      have hi3 : i < 3 := Finset.mem_range.mp hi
      interval_cases i
      · simp [Finset.mem_union, hti]
      · simp [Finset.mem_union, hti]
      · simp [Finset.mem_union, hti]
    have h1 : W.card ≤ (Wi 0 ∪ Wi 1 ∪ Wi 2).card := Finset.card_le_card hsub
    have h2 : (Wi 0 ∪ Wi 1 ∪ Wi 2).card ≤ (Wi 0).card + (Wi 1).card + (Wi 2).card := by
      have ha := Finset.card_union_le (Wi 0 ∪ Wi 1) (Wi 2)
      have hb := Finset.card_union_le (Wi 0) (Wi 1)
      omega
    have h3 : (((Wi 0).card : ℝ) + ((Wi 1).card : ℝ) + ((Wi 2).card : ℝ))
        = ∑ i ∈ Finset.range 3, ((Wi i).card : ℝ) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, Finset.sum_range_succ,
        show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
    rw [← h3]
    have : ((Wi 0 ∪ Wi 1 ∪ Wi 2).card : ℝ)
        ≤ ((Wi 0).card : ℝ) + ((Wi 1).card : ℝ) + ((Wi 2).card : ℝ) := by
      exact_mod_cast h2
    exact le_trans (by exact_mod_cast h1) this
  -- window index
  set winIdx : ℝ → ℕ := fun t => ⌊t / Lw⌋₊ with hwin
  have hKpos : 0 < K := by omega
  have hJifib : ∀ i : ℕ, (Ji i).card
      = ∑ j ∈ Finset.range K, ((Ji i).filter (fun t => winIdx t = j)).card := by
    intro i
    refine Finset.card_eq_sum_card_fiberwise (f := winIdx) (s := Ji i)
      (t := Finset.range K) ?_
    intro t ht
    have htW : t ∈ W := Finset.mem_of_mem_filter t (hJisub i ht)
    obtain ⟨ht0, htT⟩ := hWIcc t htW
    have hle : t / Lw ≤ T / Lw := div_le_div_of_nonneg_right htT hLwpos.le
    have hmono : ⌊t / Lw⌋₊ ≤ ⌊T / Lw⌋₊ := Nat.floor_mono hle
    simp only [Finset.mem_coe, Finset.mem_range, hwin, hKdef]
    omega
  -- KeyProp in one window for one piece
  have hcell : ∀ i ∈ Finset.range 3, ∀ j ∈ Finset.range K,
      (((Ji i).filter (fun t => winIdx t = j)).card : ℝ)
        ≤ (scaledN N i : ℝ) ^ ε * M (scaledN N i)
          * (scaledN N i : ℝ) ^ (12 / 5 : ℝ) * (V / 3) ^ (-4 : ℤ) := by
    intro i hi j hj
    have hi3 : i < 3 := Finset.mem_range.mp hi
    set Ni : ℕ := scaledN N i with hNidef
    have hb1 := scaledN_bounds N h3N hi3
    have hNr2 : (N : ℝ) / 2 ≤ (Ni : ℝ) := hb1.1
    have hNr3 : (Ni : ℝ) ≤ 2 * (N : ℝ) := hb1.2
    have hNr32 : (Ni : ℝ) ≤ 3 * (N : ℝ) / 2 := scaledN_le_three_halves N hi3
    have hNipos : (0 : ℝ) < (Ni : ℝ) := by linarith
    -- the threshold
    have hN1le : N₁ ≤ Ni := by
      have h2N1 : 2 * N₁ ≤ N := le_trans (le_max_left _ _) hN
      have hN1half : N₁ ≤ N / 2 := by omega
      have hhalf : N / 2 ≤ Ni := by
        have h1 : 2 * ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) := by
          have hd := Nat.div_mul_le_self N 2
          have h2 : ((N / 2 * 2 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hd
          simpa [mul_comm] using h2
        have hcast : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := by linarith
        exact_mod_cast le_trans hcast hNr2
      exact le_trans hN1half hhalf
    -- KeyProp hypotheses
    have h7 : (Ni : ℝ) ^ (7 / 10 : ℝ) ≤ V / 3 := by
      have h1 : (Ni : ℝ) ^ (7 / 10 : ℝ) ≤ (3 * (N : ℝ) / 2) ^ (7 / 10 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hNr32 (by norm_num)
      have h2 : (3 * (N : ℝ) / 2) ^ (7 / 10 : ℝ)
          = ((3 : ℝ) / 2) ^ (7 / 10 : ℝ) * (N : ℝ) ^ (7 / 10 : ℝ) := by
        rw [show 3 * (N : ℝ) / 2 = (3 : ℝ) / 2 * (N : ℝ) by ring,
          Real.mul_rpow (by norm_num) (by positivity)]
      have h3 : ((3 : ℝ) / 2) ^ (7 / 10 : ℝ) * (N : ℝ) ^ (7 / 10 : ℝ)
          ≤ (4 / 3) * (N : ℝ) ^ (7 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_right (le_of_lt rpow_three_halves_lt)
          (Real.rpow_nonneg (by positivity) _)
      have h4 : (4 / 3) * (N : ℝ) ^ (7 / 10 : ℝ) ≤ V / 3 := by linarith
      linarith
    have h8 : V / 3 ≤ (Ni : ℝ) ^ (4 / 5 : ℝ) := by
      have h1 : V / 3 ≤ (N : ℝ) ^ (4 / 5 : ℝ) / 3 := by linarith
      have h2 : (N : ℝ) ^ (4 / 5 : ℝ) / 3 ≤ ((N : ℝ) / 2) ^ (4 / 5 : ℝ) := by
        have h3 : ((N : ℝ) / 2) ^ (4 / 5 : ℝ)
            = ((1 : ℝ) / 2) ^ (4 / 5 : ℝ) * (N : ℝ) ^ (4 / 5 : ℝ) := by
          rw [show (N : ℝ) / 2 = (1 : ℝ) / 2 * (N : ℝ) by ring,
            Real.mul_rpow (by norm_num) (by positivity)]
        rw [h3, show (N : ℝ) ^ (4 / 5 : ℝ) / 3 = (1 / 3) * (N : ℝ) ^ (4 / 5 : ℝ) by ring]
        exact mul_le_mul_of_nonneg_right one_third_le_half_rpow
          (Real.rpow_nonneg (by positivity) _)
      have h4 : ((N : ℝ) / 2) ^ (4 / 5 : ℝ) ≤ (Ni : ℝ) ^ (4 / 5 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hNr2 (by norm_num)
      linarith
    -- transformed data
    set a : ℝ := (j : ℝ) * Lw with hadef
    set Jij : Finset ℝ := (Ji i).filter (fun t => winIdx t = j) with hJijdef
    set W' : Finset ℝ := Jij.image (fun t => t - a) with hW'def
    set b' : ℕ → ℂ := fun n => if n ∈ pieceSet N i then b n * (n : ℂ) ^ (I * (a : ℂ)) else 0
      with hb'def
    have hb'1 : ∀ n, ‖b' n‖ ≤ 1 := by
      intro n
      simp only [hb'def]
      split_ifs with hmem
      · rw [norm_mul]
        have hnp : (0 : ℝ) < (n : ℝ) := by
          have hnIcc : n ∈ Finset.Icc N (2 * N) := (Finset.mem_filter.mp hmem).1
          have hNn : N ≤ n := (Finset.mem_Icc.mp hnIcc).1
          exact_mod_cast (by omega : 0 < n)
        have hnorm : ‖(n : ℂ) ^ (I * (a : ℂ))‖ = 1 := by
          have := Complex.norm_cpow_eq_rpow_re_of_pos hnp (I * (a : ℂ))
          simpa using this
        have := hb n
        rw [hnorm, mul_one]
        exact this
      · simp
    have hJij_mem_Ji : ∀ t, t ∈ Jij → t ∈ Ji i := fun t ht => (Finset.mem_filter.mp ht).1
    have hJij_mem_W : ∀ t, t ∈ Jij → t ∈ W := fun t ht =>
      Finset.mem_of_mem_filter t (hJisub i (hJij_mem_Ji t ht))
    have hJijsep : ∀ t ∈ Jij, ∀ s ∈ Jij, t ≠ s → δ ≤ |t - s| := by
      intro t ht s hs hts
      exact hJisep i t (hJij_mem_Ji t ht) s (hJij_mem_Ji s hs) hts
    have hwin_j : ∀ t ∈ Jij, winIdx t = j := fun t ht => (Finset.mem_filter.mp ht).2
    have hW'Icc : ∀ t ∈ W', t ∈ Set.Icc 0 (M Ni) := by
      intro t ht
      rw [hW'def] at ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
      have hsW := hJij_mem_W s hs
      obtain ⟨hs0, hsT⟩ := hWIcc s hsW
      have hwj := hwin_j s hs
      have hlow : (j : ℝ) * Lw ≤ s := by
        have h1 : ((winIdx s : ℕ) : ℝ) ≤ s / Lw := Nat.floor_le (by positivity)
        have h2 : ((winIdx s : ℕ) : ℝ) = (j : ℝ) := by rw [hwj]
        rw [h2] at h1
        rw [le_div_iff₀ hLwpos] at h1
        linarith
      have hup : s < ((j : ℕ) : ℝ) * Lw + Lw := by
        have h1 : s / Lw < ((winIdx s : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
        rw [div_lt_iff₀ hLwpos] at h1
        have h2 : ((winIdx s : ℕ) : ℝ) = (j : ℝ) := by rw [hwj]
        rw [h2] at h1
        linarith
      have hLwle : Lw ≤ M Ni := by
        rw [M]
        exact Lw_le (Ni : ℝ) hNr2
      constructor
      · show (0 : ℝ) ≤ s - (j : ℝ) * Lw
        linarith [hadef]
      · show s - (j : ℝ) * Lw ≤ M Ni
        have : s - (j : ℝ) * Lw < Lw := by
          have : ((j : ℕ) : ℝ) * Lw = (j : ℝ) * Lw := by norm_num
          linarith
        linarith
    have hW'sep : ∀ t ∈ W', ∀ s ∈ W', t ≠ s → (M Ni) ^ ε ≤ |t - s| := by
      intro t ht s hs hts
      rw [hW'def] at ht hs
      obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨s₀, hs₀, hts'⟩ := Finset.mem_image.mp hs
      rw [← hts']
      have hne : t₀ ≠ s₀ := by
        intro h
        refine hts ?_
        rw [h, hts']
      have hδ := hJijsep t₀ ht₀ s₀ hs₀ hne
      have hMN : (M Ni) ^ ε ≤ δ := by
        rw [hδdef, M]
        rw [show ((Ni : ℝ) ^ (6 / 5 : ℝ)) ^ ε = (Ni : ℝ) ^ (6 / 5 * ε) by
          rw [← Real.rpow_mul (by positivity)]]
        rw [show ((2 : ℝ) * (N : ℝ)) ^ (6 * ε / 5) = ((2 : ℝ) * (N : ℝ)) ^ (6 / 5 * ε) by
          ring_nf]
        exact Real.rpow_le_rpow (by positivity) hNr3 (by positivity)
      have hdist : |t₀ - a - (s₀ - a)| = |t₀ - s₀| := by ring_nf
      rw [hdist]
      linarith
    have hW'val : ∀ t ∈ W', V / 3 ≤ ‖smoothedPoly Ni b' t‖ := by
      intro t ht
      rw [hW'def] at ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
      have hsw : s ∈ Wi i := hJisub i (hJij_mem_Ji s hs)
      have hpiece : V / 3 ≤ ‖pieceSum N i b s‖ := (Finset.mem_filter.mp hsw).2
      have heq : smoothedPoly Ni b' (s - a) = pieceSum N i b s := by
        have h := smoothedPoly_pieceSum (N := N) hN6 hi3 b (t := s) (a := a)
        simpa [hNidef, hb'def] using h
      rw [heq]
      exact hpiece
    have hkey := hKeyN Ni hN1le (V / 3) h7 h8 b' hb'1 W' hW'Icc hW'sep hW'val
    have hW'card : (W'.card : ℝ) = (Jij.card : ℝ) := by
      rw [hW'def]
      have hinj : Set.InjOn (fun t : ℝ => t - a) (Jij : Set ℝ) := by
        intro x _ y _ h
        linarith
      rw [Finset.card_image_of_injOn hinj]
    rw [hW'card] at hkey
    exact hkey
  -- ==================== aggregation ====================
  have hBterm : ∀ i ∈ Finset.range 3,
      ((scaledN N i : ℝ) ^ ε * M (scaledN N i)
        * (scaledN N i : ℝ) ^ (12 / 5 : ℝ) * (V / 3) ^ (-4 : ℤ))
      ≤ 81 * (2 : ℝ) ^ (18 / 5 : ℝ) * (N : ℝ) ^ (2 * ε) * (N : ℝ) ^ (18 / 5 : ℝ)
        * V ^ (-4 : ℤ) := by
    intro i hi
    have hi3 : i < 3 := Finset.mem_range.mp hi
    have hb1 := scaledN_bounds N h3N hi3
    have hNr2 : (N : ℝ) / 2 ≤ (scaledN N i : ℝ) := hb1.1
    have hNr3 : (scaledN N i : ℝ) ≤ 2 * (N : ℝ) := hb1.2
    have hV3inv : (V / 3) ^ (-4 : ℤ) = 81 * V ^ (-4 : ℤ) := by
      rw [zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat, div_pow]
      field_simp
      ring
    rw [hV3inv]
    have hNp : (scaledN N i : ℝ) ≤ 2 * (N : ℝ) := hNr3
    have hp1 : (scaledN N i : ℝ) ^ ε ≤ (N : ℝ) ^ (2 * ε) := by
      have h1 : (scaledN N i : ℝ) ^ ε ≤ (2 * (N : ℝ)) ^ ε :=
        Real.rpow_le_rpow (by positivity) hNr3 hε.le
      have h2 : (2 * (N : ℝ)) ^ ε = (2 : ℝ) ^ ε * (N : ℝ) ^ ε :=
        Real.mul_rpow (by norm_num) (by positivity)
      have h3 : (2 : ℝ) ^ ε ≤ (N : ℝ) ^ ε :=
        Real.rpow_le_rpow (by norm_num) (by linarith) hε.le
      have h4 : (2 : ℝ) ^ ε * (N : ℝ) ^ ε ≤ (N : ℝ) ^ ε * (N : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (by positivity) _)
      have h5 : (N : ℝ) ^ ε * (N : ℝ) ^ ε = (N : ℝ) ^ (2 * ε) := by
        rw [← Real.rpow_add (by positivity)]; ring_nf
      linarith [h1, h4, h5.le, h5.ge]
    have hc0 : 0 ≤ M (scaledN N i) * (scaledN N i : ℝ) ^ (12 / 5 : ℝ) := by
      rw [M]; positivity
    have hp2 : M (scaledN N i) * (scaledN N i : ℝ) ^ (12 / 5 : ℝ)
        ≤ (2 : ℝ) ^ (18 / 5 : ℝ) * (N : ℝ) ^ (18 / 5 : ℝ) := by
      rw [M]
      have h1 : (scaledN N i : ℝ) ^ (6 / 5 : ℝ) ≤ (2 * (N : ℝ)) ^ (6 / 5 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hNr3 (by norm_num)
      have h2 : (scaledN N i : ℝ) ^ (12 / 5 : ℝ) ≤ (2 * (N : ℝ)) ^ (12 / 5 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hNr3 (by norm_num)
      have h3 : (2 * (N : ℝ)) ^ (6 / 5 : ℝ) * (2 * (N : ℝ)) ^ (12 / 5 : ℝ)
          = (2 : ℝ) ^ (18 / 5 : ℝ) * (N : ℝ) ^ (18 / 5 : ℝ) := by
        have h34 : (2 * (N : ℝ)) ^ (6 / 5 : ℝ) * (2 * (N : ℝ)) ^ (12 / 5 : ℝ)
            = (2 * (N : ℝ)) ^ (18 / 5 : ℝ) := by
          rw [← Real.rpow_add (by positivity : (0 : ℝ) < 2 * (N : ℝ))]
          norm_num
        rw [h34, Real.mul_rpow (by norm_num) (by positivity)]
      calc (scaledN N i : ℝ) ^ (6 / 5 : ℝ) * (scaledN N i : ℝ) ^ (12 / 5 : ℝ)
          ≤ (2 * (N : ℝ)) ^ (6 / 5 : ℝ) * (2 * (N : ℝ)) ^ (12 / 5 : ℝ) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = (2 : ℝ) ^ (18 / 5 : ℝ) * (N : ℝ) ^ (18 / 5 : ℝ) := h3
    calc (scaledN N i : ℝ) ^ ε * M (scaledN N i) * (scaledN N i : ℝ) ^ (12 / 5 : ℝ)
          * (81 * V ^ (-4 : ℤ))
        = 81 * ((scaledN N i : ℝ) ^ ε * (M (scaledN N i) * (scaledN N i : ℝ) ^ (12 / 5 : ℝ))
            * V ^ (-4 : ℤ)) := by ring
      _ ≤ 81 * ((N : ℝ) ^ (2 * ε) * ((2 : ℝ) ^ (18 / 5 : ℝ) * (N : ℝ) ^ (18 / 5 : ℝ))
            * V ^ (-4 : ℤ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 81)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul hp1 hp2 hc0 (Real.rpow_nonneg (by positivity) _)
      _ = 81 * (2 : ℝ) ^ (18 / 5 : ℝ) * (N : ℝ) ^ (2 * ε) * (N : ℝ) ^ (18 / 5 : ℝ)
            * V ^ (-4 : ℤ) := by ring
  set Bmax : ℝ := 81 * (2 : ℝ) ^ (18 / 5 : ℝ) * (N : ℝ) ^ (2 * ε) * (N : ℝ) ^ (18 / 5 : ℝ)
    * V ^ (-4 : ℤ) with hBmaxdef
  have hBmax0 : 0 ≤ Bmax := by rw [hBmaxdef]; positivity
  have hJib : ∀ i ∈ Finset.range 3, ((Ji i).card : ℝ)
      ≤ (K : ℝ) * ((scaledN N i : ℝ) ^ ε * M (scaledN N i)
          * (scaledN N i : ℝ) ^ (12 / 5 : ℝ) * (V / 3) ^ (-4 : ℤ)) := by
    intro i hi
    rw [hJifib i, Nat.cast_sum]
    calc ∑ j ∈ Finset.range K, (((Ji i).filter (fun t => winIdx t = j)).card : ℝ)
        ≤ ∑ _j ∈ Finset.range K, ((scaledN N i : ℝ) ^ ε * M (scaledN N i)
            * (scaledN N i : ℝ) ^ (12 / 5 : ℝ) * (V / 3) ^ (-4 : ℤ)) :=
          Finset.sum_le_sum (fun j hj => hcell i hi j hj)
      _ = (K : ℝ) * ((scaledN N i : ℝ) ^ ε * M (scaledN N i)
            * (scaledN N i : ℝ) ^ (12 / 5 : ℝ) * (V / 3) ^ (-4 : ℤ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hstepA : (W.card : ℝ) ≤ 3 * ((K : ℝ) * Bmax * (2 * δ + 1)) := by
    have h1 : (W.card : ℝ) ≤ ∑ i ∈ Finset.range 3, ((Ji i).card : ℝ) * (2 * δ + 1) :=
      le_trans hcardW (Finset.sum_le_sum (fun i _ => hJicard i))
    have h2 : ∑ i ∈ Finset.range 3, ((Ji i).card : ℝ) * (2 * δ + 1)
        ≤ ∑ _i ∈ Finset.range 3, ((K : ℝ) * Bmax * (2 * δ + 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have h0δ : 0 ≤ 2 * δ + 1 := by linarith
      have hK0 : (0 : ℝ) ≤ (K : ℝ) := by positivity
      have hKi := hJib i hi
      have hBi := hBterm i hi
      have hBi' : (scaledN N i : ℝ) ^ ε * M (scaledN N i)
          * (scaledN N i : ℝ) ^ (12 / 5 : ℝ) * (V / 3) ^ (-4 : ℤ) ≤ Bmax := by
        rw [hBmaxdef]; exact hBi
      calc ((Ji i).card : ℝ) * (2 * δ + 1)
          ≤ ((K : ℝ) * ((scaledN N i : ℝ) ^ ε * M (scaledN N i)
              * (scaledN N i : ℝ) ^ (12 / 5 : ℝ) * (V / 3) ^ (-4 : ℤ))) * (2 * δ + 1) :=
            mul_le_mul_of_nonneg_right hKi h0δ
        _ ≤ ((K : ℝ) * Bmax) * (2 * δ + 1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBi' hK0) h0δ
        _ = (K : ℝ) * Bmax * (2 * δ + 1) := by ring
    have h3 : ∑ _i ∈ Finset.range 3, ((K : ℝ) * Bmax * (2 * δ + 1))
        = 3 * ((K : ℝ) * Bmax * (2 * δ + 1)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
    linarith [h1, h2, h3.le, h3.ge]
  have hKb : (K : ℝ) ≤ T / Lw + 2 := by
    have h1 : ((⌊T / Lw⌋₊ : ℕ) : ℝ) ≤ T / Lw := Nat.floor_le (by positivity)
    have h2 : K = ⌊T / Lw⌋₊ + 1 := hKdef
    rw [h2]; push_cast; linarith
  have hδb : δ ≤ (N : ℝ) ^ (2 * ε) := by
    rw [hδdef]
    have h1 : (2 * (N : ℝ)) ^ (6 * ε / 5) = (2 : ℝ) ^ (6 * ε / 5) * (N : ℝ) ^ (6 * ε / 5) :=
      Real.mul_rpow (by norm_num) (by positivity)
    have h2 : (2 : ℝ) ^ (6 * ε / 5) ≤ (N : ℝ) ^ (4 * ε / 5) := by
      have h3 : (2 : ℝ) ^ (6 / 5 : ℝ) ≤ ((N : ℝ) ^ (4 / 5 : ℝ)) := by
        have h4 : ((2 : ℝ) ^ (6 / 5 : ℝ)) ^ 5 ≤ (((N : ℝ) ^ (4 / 5 : ℝ)) ^ 5) := by
          rw [← Real.rpow_natCast ((2 : ℝ) ^ (6 / 5 : ℝ)) 5,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
            ← Real.rpow_natCast ((N : ℝ) ^ (4 / 5 : ℝ)) 5,
            ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (N : ℝ))]
          norm_num
          have hN4 : (6 : ℝ) ^ 4 ≤ (N : ℝ) ^ 4 := pow_le_pow_left₀ (by linarith) hNr 4
          norm_num at hN4
          linarith
        exact le_of_pow_le_pow_left₀ (by norm_num : (5 : ℕ) ≠ 0)
          (Real.rpow_nonneg (by positivity) (4 / 5 : ℝ)) h4
      calc (2 : ℝ) ^ (6 * ε / 5) = ((2 : ℝ) ^ (6 / 5 : ℝ)) ^ ε := by
            rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]; congr 1; ring
        _ ≤ ((N : ℝ) ^ (4 / 5 : ℝ)) ^ ε := Real.rpow_le_rpow (by positivity) h3 hε.le
        _ = (N : ℝ) ^ (4 * ε / 5) := by
            rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ (N:ℝ))]; congr 1; ring
    calc (2 * (N : ℝ)) ^ (6 * ε / 5)
        = (2 : ℝ) ^ (6 * ε / 5) * (N : ℝ) ^ (6 * ε / 5) := h1
      _ ≤ (N : ℝ) ^ (4 * ε / 5) * (N : ℝ) ^ (6 * ε / 5) :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (by positivity) _)
      _ = (N : ℝ) ^ (2 * ε) := by
          rw [← Real.rpow_add (by positivity)]; ring_nf
  have h2δb : (2 * δ + 1) ≤ 3 * δ := by linarith
  have hTLw : T / Lw * (N : ℝ) ^ (18 / 5 : ℝ) = 3 * T * (N : ℝ) ^ (12 / 5 : ℝ) := by
    rw [hLwdef]
    rw [show T / ((N : ℝ) ^ (6 / 5 : ℝ) / 3) * (N : ℝ) ^ (18 / 5 : ℝ)
        = 3 * T * ((N : ℝ) ^ (18 / 5 : ℝ) / (N : ℝ) ^ (6 / 5 : ℝ)) by ring]
    rw [← Real.rpow_sub (by positivity)]
    norm_num
  have h2_18_5 : (2 : ℝ) ^ (18 / 5 : ℝ) ≤ 16 := by
    calc (2 : ℝ) ^ (18 / 5 : ℝ) ≤ (2 : ℝ) ^ (4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 16 := by norm_num
  have hfin : 3 * ((K : ℝ) * Bmax * (2 * δ + 1)) ≤ 40000 * (N : ℝ) ^ (4 * ε) * bound N V T := by
    set A : ℝ := (N : ℝ) ^ (2 * ε) with hAdef
    set W4 : ℝ := (N : ℝ) ^ (4 * ε) with hW4def
    set P : ℝ := (N : ℝ) ^ (18 / 5 : ℝ) with hPdef
    set Q : ℝ := V ^ (-4 : ℤ) with hQdef
    set D : ℝ := (2 : ℝ) ^ (18 / 5 : ℝ) with hDdef
    set Ta : ℝ := 3 * T * (N : ℝ) ^ (12 / 5 : ℝ) with hTadef
    have hA0 : 0 ≤ A := by rw [hAdef]; positivity
    have hW40 : 0 ≤ W4 := by rw [hW4def]; positivity
    have hP0 : 0 ≤ P := by rw [hPdef]; positivity
    have hQ0 : 0 ≤ Q := by rw [hQdef]; positivity
    have hTa0 : 0 ≤ Ta := by rw [hTadef]; positivity
    have hAA : A * A = W4 := by
      rw [hAdef, hW4def, ← Real.rpow_add (by positivity : (0 : ℝ) < (N : ℝ))]
      congr 1; ring
    have hBe : Bmax = 81 * D * A * P * Q := by rw [hBmaxdef, hDdef, hAdef, hPdef, hQdef]
    have hDle : D ≤ 16 := by rw [hDdef]; exact h2_18_5
    have hTL : T / Lw * P = Ta := by rw [hPdef, hTadef]; exact hTLw
    have hbnd0 : 0 ≤ bound N V T := by
      unfold bound
      have h1 : 0 ≤ (N : ℝ) ^ 2 * V ^ (-2 : ℤ) := by positivity
      have h2 : 0 ≤ (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℤ) := by positivity
      have h3 : 0 ≤ T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ) := by positivity
      linarith
    have hBd : (Ta + 2 * P) * Q ≤ 3 * bound N V T := by
      have h3 : Ta * Q = 3 * (T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ)) := by
        rw [hTadef, hQdef]; ring
      have hPq : P * Q = (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℤ) := by rw [hPdef, hQdef]
      have hbnd2 : T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ)
          + (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℤ) ≤ bound N V T := by
        unfold bound
        have h1 : 0 ≤ (N : ℝ) ^ 2 * V ^ (-2 : ℤ) := by positivity
        linarith
      nlinarith [h3, hPq, hbnd2]
    have hstep1 : (K : ℝ) * Bmax * (2 * δ + 1) ≤ (T / Lw + 2) * Bmax * (3 * δ) := by
      have hTL2 : (0 : ℝ) ≤ T / Lw + 2 := by
        have := div_nonneg hTpos.le hLwpos.le; linarith
      have h0d : (0 : ℝ) ≤ 2 * δ + 1 := by linarith
      exact mul_le_mul (mul_le_mul hKb le_rfl hBmax0 hTL2) h2δb h0d
        (mul_nonneg hTL2 hBmax0)
    have hstep2 : 3 * ((T / Lw + 2) * Bmax * (3 * δ)) ≤ 9 * (T / Lw + 2) * Bmax * A := by
      have h1 : (T / Lw + 2) * Bmax * (3 * δ) ≤ (T / Lw + 2) * Bmax * (3 * A) :=
        mul_le_mul_of_nonneg_left (by linarith [hδb]) (by positivity)
      have h2 : 3 * ((T / Lw + 2) * Bmax * (3 * A)) = 9 * (T / Lw + 2) * Bmax * A := by ring
      nlinarith [h1, h2]
    have hstep3 : 9 * (T / Lw + 2) * Bmax * A ≤ 40000 * W4 * bound N V T := by
      have h1 : 9 * (T / Lw + 2) * Bmax * A = 729 * D * W4 * ((T / Lw + 2) * P) * Q := by
        rw [hBe, ← hAA]; ring
      rw [h1, show (T / Lw + 2) * P = Ta + 2 * P by rw [← hTL]; ring]
      have h2 : 729 * D ≤ 729 * 16 := by linarith [hDle]
      have h40 : 0 ≤ W4 * (Ta + 2 * P) * Q :=
        mul_nonneg (mul_nonneg hW40 (by linarith)) hQ0
      have h3 : 729 * D * W4 * (Ta + 2 * P) * Q ≤ 729 * 16 * W4 * (Ta + 2 * P) * Q := by
        nlinarith [h2, h40]
      have h4 : 729 * 16 * W4 * (Ta + 2 * P) * Q ≤ 729 * 16 * W4 * (3 * bound N V T) := by
        have h := mul_le_mul_of_nonneg_left hBd (by positivity : (0 : ℝ) ≤ 729 * 16 * W4)
        simpa only [mul_assoc] using h
      have h5 : 729 * 16 * W4 * (3 * bound N V T) ≤ 40000 * W4 * bound N V T := by
        have h6 : (729 : ℝ) * 16 * 3 ≤ 40000 := by norm_num
        nlinarith [h6, hW40, hbnd0]
      linarith [h3, h4, h5]
    linarith [hstep1, hstep2, hstep3]
  linarith [hstepA, hfin]

end Submission.LargeValues
