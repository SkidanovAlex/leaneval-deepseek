import Mathlib

open scoped BigOperators

namespace Work.KMTAreas.A4

-- The two notions below are inlined (private copies) so that this file depends only on Mathlib:
-- `Work.KMTAreas.A4.win` (from `A4/Defs.lean`) clashes with the unrelated `win M γ` of
-- `A4/lip2Defs.lean`, so it must not be exported from here.

/-- The overlap window `{n ∈ [a,b] : n + h ∈ [a,b]}` of `[a,b]` under the shift `h`. -/
private noncomputable def win (a b h : ℤ) : Finset ℤ := Finset.Icc (max a (a - h)) (min b (b - h))

/-- The conjugated correlation sum of `u` over the overlap window of the shift `h`. -/
private noncomputable def corr (a b : ℤ) (u : ℤ → ℂ) (h : ℤ) : ℂ :=
  ∑ n ∈ win a b h, u n * star (u (n + h))

private lemma mem_win {a b h n : ℤ} :
    n ∈ win a b h ↔ a ≤ n ∧ n ≤ b ∧ a ≤ n + h ∧ n + h ≤ b := by
  simp only [win, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨le_trans (le_max_left _ _) h1, le_trans h2 (min_le_left _ _),
      by have := le_trans (le_max_right a (a - h)) h1; omega,
      by have := le_trans h2 (min_le_right b (b - h)); omega⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨max_le h1 (by omega), le_min h2 (by omega)⟩

private lemma win_subset (a b h : ℤ) : win a b h ⊆ Finset.Icc a b := by
  intro n hn
  rw [mem_win] at hn
  exact Finset.mem_Icc.mpr ⟨hn.1, hn.2.1⟩

private lemma win_zero (a b : ℤ) : win a b 0 = Finset.Icc a b := by
  simp [win]

/-- The correlation sum is bounded by the number of terms, for a unimodular `u`. -/
private lemma norm_corr_le (a b : ℤ) (u : ℤ → ℂ) (hu : ∀ n : ℤ, ‖u n‖ = 1) (h : ℤ) :
    ‖corr a b u h‖ ≤ ((win a b h).card : ℝ) := by
  calc ‖corr a b u h‖ ≤ ∑ n ∈ win a b h, ‖u n * star (u (n + h))‖ := norm_sum_le _ _
    _ = ∑ _n ∈ win a b h, (1 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro n _
          rw [norm_mul, norm_star, hu n, hu (n + h)]
          norm_num
    _ = ((win a b h).card : ℝ) := by simp

/-- Summing the conjugated correlation sums `corr a b u h` over *all* admissible shifts
`h ∈ [-(b-a), b-a]` recovers the square of the modulus of the full sum of `u` over `[a,b]`:
each pair `(n, m) ∈ [a,b]²` is counted exactly once, for the shift `h = m - n`. -/
private lemma corr_sum_eq_plain (a b : ℤ) (u : ℤ → ℂ) :
    ∑ h ∈ Finset.Icc (-(b - a)) (b - a), corr a b u h
      = (∑ n ∈ Finset.Icc a b, u n) * star (∑ n ∈ Finset.Icc a b, u n) := by
  -- Rewrite each correlation sum as a sum over the whole interval with an indicator.
  have h_ext : ∀ h : ℤ, corr a b u h =
      ∑ n ∈ Finset.Icc a b, (if n ∈ win a b h then u n * star (u (n + h)) else 0) := by
    intro h
    rw [corr]
    exact ((Finset.sum_ite_mem (Finset.Icc a b) (win a b h)
      (fun n => u n * star (u (n + h)))).trans
      (by rw [Finset.inter_eq_right.mpr (win_subset a b h)])).symm
  -- For a fixed `n ∈ [a,b]`, summing over the shifts amounts to summing over `m = n + h`.
  have key : ∀ n ∈ Finset.Icc a b,
      (∑ h ∈ Finset.Icc (-(b - a)) (b - a),
        (if n ∈ win a b h then u n * star (u (n + h)) else 0))
      = ∑ m ∈ Finset.Icc a b, u n * star (u m) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hiff : ∀ h : ℤ, n ∈ win a b h ↔ h ∈ Finset.Icc (a - n) (b - n) := by
      intro h
      rw [mem_win, Finset.mem_Icc]
      omega
    have hsub : Finset.Icc (a - n) (b - n) ⊆ Finset.Icc (-(b - a)) (b - a) := by
      intro h hh
      rw [Finset.mem_Icc] at hh ⊢
      omega
    have hpt : ∀ h ∈ Finset.Icc (-(b - a)) (b - a),
        (if n ∈ win a b h then u n * star (u (n + h)) else 0)
        = (if h ∈ Finset.Icc (a - n) (b - n) then u n * star (u (n + h)) else 0) := by
      intro h _
      by_cases hp : n ∈ win a b h
      · have hq : h ∈ Finset.Icc (a - n) (b - n) := (hiff h).mp hp
        rw [if_pos hp, if_pos hq]
      · have hq : h ∉ Finset.Icc (a - n) (b - n) := fun hc => hp ((hiff h).mpr hc)
        rw [if_neg hp, if_neg hq]
    have step1 : (∑ h ∈ Finset.Icc (-(b - a)) (b - a),
        (if n ∈ win a b h then u n * star (u (n + h)) else 0))
        = ∑ h ∈ Finset.Icc (a - n) (b - n), u n * star (u (n + h)) := by
      rw [Finset.sum_congr rfl hpt, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
    have step2 : (∑ h ∈ Finset.Icc (a - n) (b - n), u n * star (u (n + h)))
        = ∑ m ∈ Finset.Icc a b, u n * star (u m) :=
      Finset.sum_bij (fun h _ => n + h)
        (by intro h hh; rw [Finset.mem_Icc] at hh ⊢; omega)
        (by intro h₁ _ h₂ _ heq; omega)
        (by intro m hm; refine ⟨m - n, ?_, by omega⟩
            rw [Finset.mem_Icc] at hm ⊢; omega)
        (by intro h _; rfl)
    rw [step1, step2]
  calc ∑ h ∈ Finset.Icc (-(b - a)) (b - a), corr a b u h
      = ∑ h ∈ Finset.Icc (-(b - a)) (b - a),
          ∑ n ∈ Finset.Icc a b, (if n ∈ win a b h then u n * star (u (n + h)) else 0) :=
        Finset.sum_congr rfl (fun h _ => h_ext h)
    _ = ∑ n ∈ Finset.Icc a b, ∑ h ∈ Finset.Icc (-(b - a)) (b - a),
          (if n ∈ win a b h then u n * star (u (n + h)) else 0) := Finset.sum_comm
    _ = ∑ n ∈ Finset.Icc a b, ∑ m ∈ Finset.Icc a b, u n * star (u m) :=
        Finset.sum_congr rfl key
    _ = (∑ n ∈ Finset.Icc a b, u n) * star (∑ n ∈ Finset.Icc a b, u n) := by
        rw [star_sum, Finset.sum_mul_sum]


private lemma vdcAbsCast (h : ℤ) : ((|h| : ℤ) : ℝ) = |(h : ℝ)| := by
  by_cases h0 : 0 ≤ h
  · rw [abs_of_nonneg h0, abs_of_nonneg (by exact_mod_cast h0 : (0:ℝ) ≤ (h:ℝ))]
  · have h0' : h < 0 := not_le.mp h0
    rw [abs_of_neg h0', abs_of_neg (by exact_mod_cast h0' : (h:ℝ) < 0)]
    push_cast
    ring

private lemma vdcWinCard (a b h : ℤ) (_hab : a ≤ b) (hh : |h| ≤ b - a) :
    ((win a b h).card : ℝ) = (((b - a : ℤ) : ℝ) + 1) - |((h : ℝ))| := by
  have hle : h ≤ b - a := le_trans (le_abs_self h) hh
  have hge : -h ≤ b - a := le_trans (neg_le_abs h) hh
  by_cases h0 : 0 ≤ h
  · have hmax : max a (a - h) = a := max_eq_left (by omega)
    have hmin : min b (b - h) = b - h := min_eq_right (by omega)
    have hcardZ : ((win a b h).card : ℤ) = b - h + 1 - a := by
      rw [win, hmax, hmin, Int.card_Icc]
      exact Int.toNat_of_nonneg (by omega)
    rw [show ((win a b h).card : ℝ) = ((b - h + 1 - a : ℤ) : ℝ) from by exact_mod_cast hcardZ,
      abs_of_nonneg (by exact_mod_cast h0 : (0:ℝ) ≤ (h:ℝ))]
    push_cast
    ring
  · have h0' : h < 0 := not_le.mp h0
    have hmax : max a (a - h) = a - h := max_eq_right (by omega)
    have hmin : min b (b - h) = b := min_eq_left (by omega)
    have hcardZ : ((win a b h).card : ℤ) = b + 1 - (a - h) := by
      rw [win, hmax, hmin, Int.card_Icc]
      exact Int.toNat_of_nonneg (by omega)
    rw [show ((win a b h).card : ℝ) = ((b + 1 - (a - h) : ℤ) : ℝ) from by exact_mod_cast hcardZ,
      abs_of_neg (by exact_mod_cast h0' : (h:ℝ) < 0)]
    push_cast
    ring

private lemma vdcSumWinCard (a b : ℤ) (hab : a ≤ b) :
    ∑ h ∈ Finset.Icc (-(b - a)) (b - a), ((win a b h).card : ℝ)
      = (((b - a : ℤ) : ℝ) + 1) ^ 2 := by
  have hAcard : ((Finset.Icc a b).card : ℝ) = ((b - a : ℤ) : ℝ) + 1 := by
    have h2 : ((Finset.Icc a b).card : ℤ) = (b - a) + 1 := by
      rw [Int.card_Icc, Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ b + 1 - a)]
      ring
    exact_mod_cast h2
  have hcorr : ∀ h : ℤ, corr a b (fun _ : ℤ => (1:ℂ)) h = (((win a b h).card : ℝ) : ℂ) := by
    intro h
    rw [corr, Finset.sum_const, nsmul_eq_mul]
    simp only [star_one, mul_one]
    exact (Complex.ofReal_natCast ((win a b h).card)).symm
  have hs : (∑ n ∈ Finset.Icc a b, (1:ℂ)) = ((((b - a : ℤ) : ℝ) + 1 : ℝ) : ℂ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [show ((Finset.Icc a b).card : ℂ) = (((Finset.Icc a b).card : ℝ) : ℂ) from
      (Complex.ofReal_natCast _).symm]
    rw [hAcard]
  have key : Complex.ofReal (∑ h ∈ Finset.Icc (-(b - a)) (b - a), ((win a b h).card : ℝ))
      = Complex.ofReal ((((b - a : ℤ) : ℝ) + 1) ^ 2) := by
    have h1 : (∑ h ∈ Finset.Icc (-(b - a)) (b - a), corr a b (fun _ : ℤ => (1:ℂ)) h)
        = (∑ n ∈ Finset.Icc a b, (1:ℂ)) * star (∑ n ∈ Finset.Icc a b, (1:ℂ)) :=
      corr_sum_eq_plain a b (fun _ : ℤ => (1:ℂ))
    have hrhs : Complex.ofReal ((((b - a : ℤ) : ℝ) + 1) ^ 2)
        = (∑ n ∈ Finset.Icc a b, (1:ℂ)) * star (∑ n ∈ Finset.Icc a b, (1:ℂ)) := by
      rw [hs, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
      congr 1
      ring
    rw [hrhs, ← h1, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun h _ => (hcorr h).symm)
  exact Complex.ofReal_injective key

private lemma vdcSumGoodJ (M : ℤ) (T : ℝ) (hT : 0 < T) :
    ∑ j ∈ (Finset.Icc (1:ℤ) M).filter (fun (j : ℤ) => (j : ℝ) < T), (j : ℝ) ≤ T ^ 2 := by
  set J : Finset ℤ := (Finset.Icc (1:ℤ) M).filter (fun (j : ℤ) => (j : ℝ) < T) with hJ
  have hfl0 : (0:ℤ) ≤ ⌊T⌋ := Int.floor_nonneg.mpr hT.le
  have hsub : J ⊆ Finset.Icc (1:ℤ) ⌊T⌋ := by
    intro j hj
    rw [hJ, Finset.mem_filter, Finset.mem_Icc] at hj
    obtain ⟨⟨hj1, _⟩, hj2⟩ := hj
    rw [Finset.mem_Icc]
    exact ⟨hj1, Int.le_floor.mpr hj2.le⟩
  have hcard : (J.card : ℝ) ≤ (⌊T⌋ : ℝ) := by
    have h1 : J.card ≤ (Finset.Icc (1:ℤ) ⌊T⌋).card := Finset.card_le_card hsub
    rw [Int.card_Icc] at h1
    rw [show (⌊T⌋ + 1 - 1 : ℤ) = ⌊T⌋ by ring] at h1
    have h3 : (((⌊T⌋).toNat : ℕ) : ℝ) = (⌊T⌋ : ℝ) := by
      rw [← Int.cast_natCast (R := ℝ) ((⌊T⌋).toNat), Int.toNat_of_nonneg hfl0]
    rw [← h3]
    exact_mod_cast h1
  calc ∑ j ∈ J, (j : ℝ) ≤ ∑ j ∈ J, (⌊T⌋ : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have h := hsub hj
        rw [Finset.mem_Icc] at h
        exact_mod_cast h.2
    _ = (J.card : ℝ) * (⌊T⌋ : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (⌊T⌋:ℝ) * (⌊T⌋:ℝ) := by
        apply mul_le_mul_of_nonneg_right hcard
        exact_mod_cast hfl0
    _ ≤ T * T := mul_self_le_mul_self (by exact_mod_cast hfl0) (Int.floor_le T)
    _ = T ^ 2 := by ring

private lemma vdcTailAbs (M : ℤ) (T : ℝ) (hT : 0 < T) :
    ∑ h ∈ (Finset.Icc (-M) M).filter (fun (h : ℤ) => h ≠ 0 ∧ ((M:ℝ)+1-|(h:ℝ)|) < T),
        ((M:ℝ)+1-|(h:ℝ)|) ≤ 2 * T ^ 2 := by
  set S : Finset ℤ := (Finset.Icc (-M) M).filter
    (fun (h : ℤ) => h ≠ 0 ∧ ((M:ℝ)+1-|(h:ℝ)|) < T) with hS
  set J : Finset ℤ := (Finset.Icc (1:ℤ) M).filter (fun (j : ℤ) => (j:ℝ) < T) with hJ
  have hmemS : ∀ h ∈ S, -M ≤ h ∧ h ≤ M ∧ h ≠ 0 ∧ ((M:ℝ)+1-|(h:ℝ)|) < T := by
    intro h hh
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hh
    exact ⟨hh.1.1, hh.1.2, hh.2.1, hh.2.2⟩
  have hpos : ∑ h ∈ S.filter (fun h => 0 < h), ((M:ℝ)+1-|(h:ℝ)|) = ∑ j ∈ J, (j:ℝ) := by
    refine Finset.sum_bij (fun (h : ℤ) (_ : h ∈ S.filter (fun h => 0 < h)) => M + 1 - h) ?_ ?_ ?_ ?_
    · intro h hh
      rw [Finset.mem_filter] at hh
      obtain ⟨hhS, hhpos⟩ := hh
      obtain ⟨hh1, hh2, hhne, hhT⟩ := hmemS h hhS
      have habs : |(h:ℝ)| = (h:ℝ) := abs_of_pos (by exact_mod_cast hhpos)
      rw [hJ, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have hcast : ((M + 1 - h : ℤ) : ℝ) = (M:ℝ) + 1 - (h:ℝ) := by push_cast; ring
      rw [hcast]
      rw [habs] at hhT
      exact hhT
    · intro h1 _ h2 _ heq; omega
    · intro j hj
      rw [hJ, Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hj2⟩, hjT⟩ := hj
      refine ⟨M + 1 - j, ?_, by ring⟩
      rw [Finset.mem_filter]
      refine ⟨?_, by omega⟩
      rw [hS, Finset.mem_filter, Finset.mem_Icc]
      have habs : |((M + 1 - j : ℤ) : ℝ)| = ((M + 1 - j : ℤ) : ℝ) :=
        abs_of_pos (by exact_mod_cast (show (0:ℤ) < M + 1 - j by omega))
      refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
      have hcast : (M:ℝ) + 1 - |((M + 1 - j : ℤ) : ℝ)| = (j:ℝ) := by
        rw [habs]; push_cast; ring
      rw [hcast]; exact hjT
    · intro h hh
      rw [Finset.mem_filter] at hh
      have habs : |(h:ℝ)| = (h:ℝ) := abs_of_pos (by exact_mod_cast hh.2)
      rw [habs]
      push_cast
      ring
  have hneg : ∑ h ∈ S.filter (fun h => ¬ 0 < h), ((M:ℝ)+1-|(h:ℝ)|) = ∑ j ∈ J, (j:ℝ) := by
    refine Finset.sum_bij (fun (h : ℤ) (_ : h ∈ S.filter (fun h => ¬ 0 < h)) => M + 1 + h) ?_ ?_ ?_ ?_
    · intro h hh
      rw [Finset.mem_filter] at hh
      obtain ⟨hhS, hhnpos⟩ := hh
      obtain ⟨hh1, hh2, hhne, hhT⟩ := hmemS h hhS
      have hneg' : h < 0 := lt_of_le_of_ne (not_lt.mp hhnpos) hhne
      have habs : |(h:ℝ)| = -(h:ℝ) := abs_of_neg (by exact_mod_cast hneg')
      rw [hJ, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have hcast : ((M + 1 + h : ℤ) : ℝ) = (M:ℝ) + 1 + (h:ℝ) := by push_cast; ring
      rw [hcast]
      rw [habs] at hhT
      linarith
    · intro h1 _ h2 _ heq; omega
    · intro j hj
      rw [hJ, Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hj2⟩, hjT⟩ := hj
      refine ⟨j - (M + 1), ?_, by ring⟩
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [hS, Finset.mem_filter, Finset.mem_Icc]
        have habs : |((j - (M + 1) : ℤ) : ℝ)| = -((j - (M + 1) : ℤ) : ℝ) :=
          abs_of_neg (by exact_mod_cast (show (j - (M + 1) : ℤ) < 0 by omega))
        refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
        have hcast : (M:ℝ) + 1 - |((j - (M + 1) : ℤ) : ℝ)| = (j:ℝ) := by
          rw [habs]; push_cast; ring
        rw [hcast]; exact hjT
      · exact not_lt.mpr (by omega : j - (M + 1) ≤ 0)
    · intro h hh
      rw [Finset.mem_filter] at hh
      have hneg' : h < 0 := lt_of_le_of_ne (not_lt.mp hh.2) (hmemS h hh.1).2.2.1
      have habs : |(h:ℝ)| = -(h:ℝ) := abs_of_neg (by exact_mod_cast hneg')
      rw [habs]
      push_cast
      ring
  have hJle := vdcSumGoodJ M T hT
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun (h : ℤ) => 0 < h)
    (fun (h : ℤ) => ((M:ℝ)+1-|(h:ℝ)|))
  rw [← hsplit]
  linarith [hpos, hneg, hJle]

private lemma vdcTail (a b : ℤ) (hab : a ≤ b) (T : ℝ) (hT : 0 < T) :
    ∑ h ∈ (Finset.Icc (-(b - a)) (b - a)).filter
        (fun (h : ℤ) => h ≠ 0 ∧ ((win a b h).card : ℝ) < T),
        ((win a b h).card : ℝ) ≤ 2 * T ^ 2 := by
  have hkey : ∀ h ∈ Finset.Icc (-(b - a)) (b - a),
      ((win a b h).card : ℝ) = (((b - a : ℤ) : ℝ) + 1) - |(h:ℝ)| := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    exact vdcWinCard a b h hab (by rw [abs_le]; exact ⟨by omega, by omega⟩)
  have hfilt : (Finset.Icc (-(b - a)) (b - a)).filter
        (fun (h : ℤ) => h ≠ 0 ∧ ((win a b h).card : ℝ) < T)
      = (Finset.Icc (-(b - a)) (b - a)).filter
        (fun (h : ℤ) => h ≠ 0 ∧ (((b - a : ℤ) : ℝ) + 1) - |(h:ℝ)| < T) := by
    apply Finset.filter_congr
    intro h hh
    rw [hkey h hh]
  rw [hfilt]
  refine le_trans (Finset.sum_le_sum (fun h hh => ?_)) (vdcTailAbs (b - a) T hT)
  rw [Finset.mem_filter] at hh
  exact le_of_eq (hkey h hh.1)

private lemma vdcArith (ε L : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hL : 2 ≤ ε ^ 2 * L) (hLpos : 0 < L) :
    L + 2 * (ε ^ 2 * L / 64) ^ 2 ≤ 5 / 8 * ε ^ 2 * L ^ 2 := by
  have h2 : ε ^ 2 ≤ 1 := by nlinarith [hε, hε1]
  have hx0 : 0 ≤ ε ^ 2 * L := by linarith
  have hkey : 1 + (ε ^ 2 * L) / 2048 ≤ 5 / 8 * (ε ^ 2 * L) := by nlinarith [hL]
  calc L + 2 * (ε ^ 2 * L / 64) ^ 2 = L * (1 + ε ^ 2 * (ε ^ 2 * L) / 2048) := by ring
    _ ≤ L * (1 + (ε ^ 2 * L) / 2048) := by
        apply mul_le_mul_of_nonneg_left _ hLpos.le
        nlinarith [h2, hx0]
    _ ≤ L * (5 / 8 * (ε ^ 2 * L)) := mul_le_mul_of_nonneg_left hkey hLpos.le
    _ = 5 / 8 * ε ^ 2 * L ^ 2 := by ring

private lemma vdcAux (a b : ℤ) (u : ℤ → ℂ) (ε L : ℝ) (hab : a ≤ b)
    (hLdef : L = ((b - a : ℤ) : ℝ) + 1) (hε : 0 < ε) (hL : 2 ≤ ε ^ 2 * L)
    (hu : ∀ n : ℤ, ‖u n‖ = 1) (hS : ε * L ≤ ‖∑ n ∈ Finset.Icc a b, u n‖) :
    ∃ H : Finset ℤ, (∀ h ∈ H, h ≠ 0) ∧
      (∀ h ∈ H, ε ^ 2 / 64 * L ≤ ((win a b h).card : ℝ)) ∧
      (ε ^ 2 / 8 * L ^ 2 ≤ ∑ h ∈ H, ((win a b h).card : ℝ)) ∧
      (∀ h ∈ H, ε ^ 2 / 4 * ((win a b h).card : ℝ) ≤ ‖corr a b u h‖) := by
  have hM0 : (0:ℤ) ≤ b - a := by omega
  have hL1 : (1:ℝ) ≤ L := by
    rw [hLdef]
    have h : (0:ℝ) ≤ ((b - a : ℤ) : ℝ) := by exact_mod_cast hM0
    linarith
  have hLpos : (0:ℝ) < L := by linarith
  have hcardab : ((Finset.Icc a b).card : ℝ) = L := by
    rw [hLdef]
    have h2 : ((Finset.Icc a b).card : ℤ) = (b - a) + 1 := by
      rw [Int.card_Icc, Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ b + 1 - a)]
      ring
    exact_mod_cast h2
  have hSnorm : ‖∑ n ∈ Finset.Icc a b, u n‖ ≤ L := by
    calc ‖∑ n ∈ Finset.Icc a b, u n‖ ≤ ∑ n ∈ Finset.Icc a b, ‖u n‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.Icc a b, (1:ℝ) := Finset.sum_congr rfl (fun n _ => hu n)
      _ = ((Finset.Icc a b).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = L := hcardab
  have heps1 : ε ≤ 1 := by
    have h1 : ε * L ≤ L := le_trans hS hSnorm
    nlinarith [hLpos, h1]
  set I : Finset ℤ := Finset.Icc (-(b - a)) (b - a) with hI
  have hcardI : ∑ h ∈ I, ((win a b h).card : ℝ) = L ^ 2 := by
    rw [hI, hLdef]
    exact vdcSumWinCard a b hab
  have hcorrSum : ∑ h ∈ I, corr a b u h
      = (∑ n ∈ Finset.Icc a b, u n) * star (∑ n ∈ Finset.Icc a b, u n) := by
    rw [hI]; exact corr_sum_eq_plain a b u
  have hS2 : ε ^ 2 * L ^ 2 ≤ ‖∑ n ∈ Finset.Icc a b, u n‖ ^ 2 := by
    have h0 : 0 ≤ ε * L := by positivity
    nlinarith [hS, h0, norm_nonneg (∑ n ∈ Finset.Icc a b, u n)]
  have hstar : ε ^ 2 * L ^ 2
      ≤ (∑ h ∈ I.filter (fun h => ε ^ 2 / 4 * ((win a b h).card : ℝ) ≤ ‖corr a b u h‖),
          ((win a b h).card : ℝ)) + ε ^ 2 / 4 * L ^ 2 := by
    have h2 : ‖∑ n ∈ Finset.Icc a b, u n‖ ^ 2 ≤ ∑ h ∈ I, ‖corr a b u h‖ := by
      rw [show ‖∑ n ∈ Finset.Icc a b, u n‖ ^ 2
          = ‖(∑ n ∈ Finset.Icc a b, u n) * star (∑ n ∈ Finset.Icc a b, u n)‖ by
            rw [norm_mul, norm_star]; ring]
      rw [← hcorrSum]
      exact norm_sum_le _ _
    have h3 : ∑ h ∈ I, ‖corr a b u h‖
        = (∑ h ∈ I.filter (fun h => ε ^ 2 / 4 * ((win a b h).card : ℝ) ≤ ‖corr a b u h‖),
              ‖corr a b u h‖)
          + ∑ h ∈ I.filter (fun h => ¬ (ε ^ 2 / 4 * ((win a b h).card : ℝ) ≤ ‖corr a b u h‖)),
              ‖corr a b u h‖ :=
      (Finset.sum_filter_add_sum_filter_not I
        (fun h => ε ^ 2 / 4 * ((win a b h).card : ℝ) ≤ ‖corr a b u h‖)
        (fun h => ‖corr a b u h‖)).symm
    have h4 : ∑ h ∈ I.filter (fun h => ε ^ 2 / 4 * ((win a b h).card : ℝ) ≤ ‖corr a b u h‖),
          ‖corr a b u h‖
        ≤ ∑ h ∈ I.filter (fun h => ε ^ 2 / 4 * ((win a b h).card : ℝ) ≤ ‖corr a b u h‖),
          ((win a b h).card : ℝ) :=
      Finset.sum_le_sum (fun h _ => norm_corr_le a b u hu h)
    have h5 : ∑ h ∈ I.filter (fun h => ¬ (ε ^ 2 / 4 * ((win a b h).card : ℝ) ≤ ‖corr a b u h‖)),
          ‖corr a b u h‖ ≤ ε ^ 2 / 4 * L ^ 2 := by
      have h6 : ∑ h ∈ I.filter (fun h => ¬ (ε ^ 2 / 4 * ((win a b h).card : ℝ) ≤ ‖corr a b u h‖)),
            ‖corr a b u h‖
          ≤ ∑ h ∈ I.filter (fun h => ¬ (ε ^ 2 / 4 * ((win a b h).card : ℝ) ≤ ‖corr a b u h‖)),
            ε ^ 2 / 4 * ((win a b h).card : ℝ) := by
        apply Finset.sum_le_sum
        intro h hh
        rw [Finset.mem_filter] at hh
        exact le_of_lt (not_le.mp hh.2)
      have h7 : ∑ h ∈ I.filter (fun h => ¬ (ε ^ 2 / 4 * ((win a b h).card : ℝ) ≤ ‖corr a b u h‖)),
            ε ^ 2 / 4 * ((win a b h).card : ℝ)
          = ε ^ 2 / 4 * ∑ h ∈ I.filter (fun h => ¬ (ε ^ 2 / 4 * ((win a b h).card : ℝ) ≤ ‖corr a b u h‖)),
            ((win a b h).card : ℝ) := by
        rw [Finset.mul_sum]
      have h8 : ∑ h ∈ I.filter (fun h => ¬ (ε ^ 2 / 4 * ((win a b h).card : ℝ) ≤ ‖corr a b u h‖)),
            ((win a b h).card : ℝ) ≤ L ^ 2 := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun h _ _ => by positivity)) ?_
        rw [hcardI]
      have h9 : ε ^ 2 / 4 * (∑ h ∈ I.filter (fun h => ¬ (ε ^ 2 / 4 * ((win a b h).card : ℝ) ≤ ‖corr a b u h‖)),
            ((win a b h).card : ℝ)) ≤ ε ^ 2 / 4 * L ^ 2 :=
        mul_le_mul_of_nonneg_left h8 (by positivity)
      linarith [h6, h7, h9]
    linarith [hS2, h2, h3, h4, h5]
  set G : Finset ℤ := I.filter (fun h => ε ^ 2 / 4 * ((win a b h).card : ℝ) ≤ ‖corr a b u h‖) with hG
  have hGsum : 3 / 4 * ε ^ 2 * L ^ 2 ≤ ∑ h ∈ G, ((win a b h).card : ℝ) := by
    rw [hG]; linarith [hstar]
  set T : ℝ := ε ^ 2 * L / 64 with hTdef
  have hTpos : 0 < T := by rw [hTdef]; positivity
  set H : Finset ℤ := G.filter (fun h => h ≠ 0 ∧ T ≤ ((win a b h).card : ℝ)) with hH
  have hHsub : H ⊆ G := Finset.filter_subset _ _
  have hsd := Finset.sum_sdiff hHsub (f := fun h => ((win a b h).card : ℝ))
  have hsub2 : G \ H ⊆ ({0} : Finset ℤ) ∪ I.filter (fun h => h ≠ 0 ∧ ((win a b h).card : ℝ) < T) := by
    intro h hh
    rw [Finset.mem_sdiff] at hh
    obtain ⟨hhG, hnotH⟩ := hh
    by_cases h0 : h = 0
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_singleton.mpr h0))
    · refine Finset.mem_union.mpr (Or.inr ?_)
      rw [Finset.mem_filter]
      refine ⟨(Finset.mem_filter.mp hhG).1, h0, ?_⟩
      by_contra hc
      rw [not_lt] at hc
      exact hnotH (by rw [hH, Finset.mem_filter]; exact ⟨hhG, h0, hc⟩)
  have hsum_le : ∑ h ∈ G \ H, ((win a b h).card : ℝ) ≤ L + 2 * T ^ 2 := by
    have h1 : ∑ h ∈ G \ H, ((win a b h).card : ℝ)
        ≤ ∑ h ∈ ({0} : Finset ℤ) ∪ (I.filter (fun h => h ≠ 0 ∧ ((win a b h).card : ℝ) < T)),
            ((win a b h).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun h _ _ => by positivity)
    have hdisj : Disjoint ({0} : Finset ℤ) (I.filter (fun h => h ≠ 0 ∧ ((win a b h).card : ℝ) < T)) := by
      rw [Finset.disjoint_singleton_left]
      intro hmem
      exact (Finset.mem_filter.mp hmem).2.1 rfl
    have h2 : ∑ h ∈ ({0} : Finset ℤ) ∪ (I.filter (fun h => h ≠ 0 ∧ ((win a b h).card : ℝ) < T)),
            ((win a b h).card : ℝ)
        ≤ ((win a b 0).card : ℝ)
          + ∑ h ∈ I.filter (fun h => h ≠ 0 ∧ ((win a b h).card : ℝ) < T), ((win a b h).card : ℝ) := by
      rw [Finset.sum_union hdisj, Finset.sum_singleton]
    have h3 : ((win a b 0).card : ℝ) = L := by rw [win_zero]; exact hcardab
    have h4 : ∑ h ∈ I.filter (fun h => h ≠ 0 ∧ ((win a b h).card : ℝ) < T), ((win a b h).card : ℝ)
        ≤ 2 * T ^ 2 := by
      rw [hI]; exact vdcTail a b hab T hTpos
    linarith [h1, h2, h3, h4]
  have harith : L + 2 * T ^ 2 ≤ 5 / 8 * ε ^ 2 * L ^ 2 := by
    rw [hTdef]; exact vdcArith ε L hε heps1 hL hLpos
  have hfinal : ε ^ 2 / 8 * L ^ 2 ≤ ∑ h ∈ H, ((win a b h).card : ℝ) := by
    linarith [hGsum, hsd, hsum_le, harith]
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · intro h hh
    exact (Finset.mem_filter.mp hh).2.1
  · intro h hh
    have h' := (Finset.mem_filter.mp hh).2.2
    rw [hTdef] at h'
    linarith
  · exact hfinal
  · intro h hh
    have hhG := (Finset.mem_filter.mp hh).1
    rw [hG, Finset.mem_filter] at hhG
    exact hhG.2

theorem vdcPlainMathlib (a b : ℤ) (u : ℤ → ℂ) (ε : ℝ) (hab : a ≤ b) (hε : 0 < ε) (hL : 2 ≤ ε ^ 2 * (((b - a : ℤ) : ℝ) + 1)) (hu : ∀ n : ℤ, ‖u n‖ = 1) (hS : ε * (((b - a : ℤ) : ℝ) + 1) ≤ ‖∑ n ∈ Finset.Icc a b, u n‖) : ∃ H : Finset ℤ, (∀ h ∈ H, h ≠ 0) ∧ (∀ h ∈ H, ε ^ 2 / 64 * (((b - a : ℤ) : ℝ) + 1) ≤ ((Finset.Icc (max a (a - h)) (min b (b - h))).card : ℝ)) ∧ (ε ^ 2 / 8 * (((b - a : ℤ) : ℝ) + 1) ^ 2 ≤ ∑ h ∈ H, ((Finset.Icc (max a (a - h)) (min b (b - h))).card : ℝ)) ∧ (∀ h ∈ H, ε ^ 2 / 4 * ((Finset.Icc (max a (a - h)) (min b (b - h))).card : ℝ) ≤ ‖∑ n ∈ Finset.Icc (max a (a - h)) (min b (b - h)), u n * star (u (n + h))‖) := by
  obtain ⟨H, h1, h2, h3, h4⟩ := vdcAux a b u ε (((b - a : ℤ) : ℝ) + 1) hab rfl hε hL hu hS
  exact ⟨H, h1, h2, h3, h4⟩

end Work.KMTAreas.A4
