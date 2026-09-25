import Mathlib.Analysis.MeanInequalitiesPow

namespace Commons.Analysis.Series

open scoped BigOperators

/-- `(x^s)^(1/s) = x` for `0 < s` and `0 ≤ x`. -/
private lemma rpow_pow_inv {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) : (x ^ s) ^ (1 / s) = x := by
  rw [← Real.rpow_mul hx s (1 / s),
    show s * (1 / s) = 1 by rw [mul_one_div, div_self (ne_of_gt hs)], Real.rpow_one]

/-- `(x^(1/s))^s = x` for `0 < s` and `0 ≤ x`. -/
private lemma rpow_inv_pow {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) : (x ^ (1 / s)) ^ s = x := by
  rw [← Real.rpow_mul hx (1 / s) s,
    show (1 / s) * s = 1 by rw [one_div, inv_mul_cancel₀ (ne_of_gt hs)], Real.rpow_one]

/-- `(x^s + y^s)^(1/s) ≤ x + y` for `1 ≤ s` and `x, y ≥ 0`. -/
private lemma rpow_sum_le_add {s x y : ℝ} (hs : 1 ≤ s) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x ^ s + y ^ s) ^ (1 / s) ≤ x + y := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have h1s0 : 0 < 1 / s := by positivity
  have hxy : 0 ≤ x + y := add_nonneg hx hy
  have h1 : x ^ s + y ^ s ≤ (x + y) ^ s := Real.add_rpow_le_rpow_add hx hy hs
  have h2 : (x ^ s + y ^ s) ^ (1 / s) ≤ ((x + y) ^ s) ^ (1 / s) :=
    Real.rpow_le_rpow (by positivity) h1 (le_of_lt h1s0)
  rw [rpow_pow_inv hs0 hxy] at h2
  exact h2

/-- From `x^s ≤ y^s` with `0 < s` and `x, y ≥ 0` conclude `x ≤ y`. -/
private lemma le_of_rpow_le_rpow {s x y : ℝ} (hs : 0 < s) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ^ s ≤ y ^ s) : x ≤ y := by
  have h1s0 : 0 < 1 / s := by positivity
  have h2 : (x ^ s) ^ (1 / s) ≤ (y ^ s) ^ (1 / s) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hx s) h (le_of_lt h1s0)
  rwa [rpow_pow_inv hs hx, rpow_pow_inv hs hy] at h2

/-- `sSup (range f) = 0` when `f` is not bounded above. -/
private lemma sSup_range_eq_zero_of_not_bddAbove {ι : Type*} {f : ι → ℝ}
    (h : ¬ BddAbove (Set.range f)) : sSup (Set.range f) = 0 := by
  rw [Real.sSup_def]
  exact dif_neg (fun hc => h hc.2)

theorem variation_shift_le (b : ℕ → ℝ) {s : ℝ} (hs : 2 < s) (n₀ : ℕ)
    (hzero : ∀ k < n₀, b k = 0) :
    (⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (∑ j ∈ Finset.range J, |b (u.1 (j + 1)) - b (u.1 j)| ^ s) ^ (1 / s))
    ≤ |b n₀| + 2 * (⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (∑ j ∈ Finset.range J, |b (n₀ + u.1 (j + 1)) - b (n₀ + u.1 j)| ^ s) ^ (1 / s)) := by
  have hs0 : 0 < s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have h1s0 : 0 < 1 / s := by positivity
  let U : Type := {u : ℕ → ℕ // StrictMono u}
  have hUne : Nonempty U := ⟨⟨id, strictMono_id⟩⟩
  let A : U → ℕ → ℝ := fun u J =>
      (∑ j ∈ Finset.range J, |b (u.1 (j + 1)) - b (u.1 j)| ^ s) ^ (1 / s)
  let Bv : U → ℕ → ℝ := fun u J =>
      (∑ j ∈ Finset.range J, |b (n₀ + u.1 (j + 1)) - b (n₀ + u.1 j)| ^ s) ^ (1 / s)
  let a : U → ℝ := fun u => ⨆ J : ℕ, A u J
  let v : U → ℝ := fun u => ⨆ J : ℕ, Bv u J
  have hAnn : ∀ (u : U) (J : ℕ), 0 ≤ A u J := by
    intro u J
    exact Real.rpow_nonneg (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) s)) _
  have hBnn : ∀ (u : U) (J : ℕ), 0 ≤ Bv u J := by
    intro u J
    exact Real.rpow_nonneg (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) s)) _
  have hB0 : ∀ u : U, Bv u 0 = 0 := by
    intro u
    show (∑ j ∈ Finset.range 0, |b (n₀ + u.1 (j + 1)) - b (n₀ + u.1 j)| ^ s) ^ (1 / s) = 0
    rw [Finset.sum_range_zero, Real.zero_rpow (ne_of_gt h1s0)]
  have hsum_mono : ∀ u : U, StrictMono (fun i => n₀ + u.1 i) := by
    intro u i j hij
    exact Nat.add_lt_add_left (u.2 hij) n₀
  have hv_eq : ∀ u : U, v u = a ⟨fun i => n₀ + u.1 i, hsum_mono u⟩ := by
    intro u
    rfl
  have hvnn : ∀ u : U, 0 ≤ v u := by
    intro u
    by_cases h : BddAbove (Set.range (Bv u))
    · have h0 : Bv u 0 = 0 := hB0 u
      have h1 : Bv u 0 ≤ sSup (Set.range (Bv u)) := le_csSup h ⟨0, rfl⟩
      rw [show v u = sSup (Set.range (Bv u)) from rfl, ← h0]
      exact h1
    · rw [show v u = sSup (Set.range (Bv u)) from rfl,
        sSup_range_eq_zero_of_not_bddAbove h]
  by_cases hb : BddAbove (Set.range a)
  · have hbV : BddAbove (Set.range v) :=
      BddAbove.mono (by rintro x ⟨u, rfl⟩; exact ⟨⟨fun i => n₀ + u.1 i, hsum_mono u⟩, (hv_eq u).symm⟩) hb
    have hVub : ∀ u : U, v u ≤ sSup (Set.range v) := fun u => le_csSup hbV ⟨u, rfl⟩
    have hVnn : 0 ≤ sSup (Set.range v) :=
      le_trans (hvnn ⟨id, strictMono_id⟩) (hVub ⟨id, strictMono_id⟩)
    have hcnn : 0 ≤ |b n₀| + 2 * sSup (Set.range v) :=
      add_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) hVnn)
    change sSup (Set.range a) ≤ |b n₀| + 2 * sSup (Set.range v)
    refine csSup_le (Set.range_nonempty a) ?_
    rintro y ⟨u, rfl⟩
    by_cases hrowb : BddAbove (Set.range (A u))
    · rw [show a u = sSup (Set.range (A u)) from rfl]
      refine csSup_le (Set.range_nonempty (A u)) ?_
      rintro y ⟨J, rfl⟩
      -- === per-row argument ===
      set M := sSup (Set.range (A u)) with hM
      have hMnn : 0 ≤ M := le_trans (hAnn u 0) (le_csSup hrowb ⟨0, rfl⟩)
      have hAub : ∀ J, A u J ≤ M := fun J => le_csSup hrowb ⟨J, rfl⟩
      have hm₀ex : ∃ j, n₀ ≤ u.1 j := ⟨n₀, u.2.id_le n₀⟩
      set m₀ := Nat.find hm₀ex with hm₀def
      have hm₀spec : n₀ ≤ u.1 m₀ := Nat.find_spec hm₀ex
      have hm₀min : ∀ j, n₀ ≤ u.1 j → m₀ ≤ j := fun j hj => Nat.find_min' hm₀ex hj
      have hbelow : ∀ j, j < m₀ → u.1 j < n₀ := by
        intro j hj
        by_contra hcon
        exact absurd (hm₀min j (not_lt.mp hcon)) (not_le.mpr hj)
      have habove : ∀ j, m₀ ≤ j → n₀ ≤ u.1 j :=
        fun j hj => le_trans hm₀spec (u.2.monotone hj)
      let z : ℕ → ℕ := fun i => u.1 (m₀ + i) - n₀
      have hz : StrictMono z := by
        intro i j hij
        simp only [z]
        have h1 : n₀ ≤ u.1 (m₀ + i) := habove _ (Nat.le_add_right _ _)
        have h2 : u.1 (m₀ + i) < u.1 (m₀ + j) := u.2 (by omega)
        omega
      have hzval : ∀ i, n₀ + z i = u.1 (m₀ + i) := by
        intro i
        simp only [z]
        exact Nat.add_sub_cancel' (habove _ (Nat.le_add_right _ _))
      let f : ℕ → ℝ := fun j => |b (u.1 (j + 1)) - b (u.1 j)| ^ s
      have hfnn : ∀ j, 0 ≤ f j := fun j => Real.rpow_nonneg (abs_nonneg _) s
      have hAeq : ∀ J, A u J = (∑ j ∈ Finset.range J, f j) ^ (1 / s) := fun J => rfl
      have hzsum : ∀ K, (Bv ⟨z, hz⟩ K) ^ s = ∑ i ∈ Finset.range K, f (m₀ + i) := by
        intro K
        show ((∑ i ∈ Finset.range K,
          |b (n₀ + z (i + 1)) - b (n₀ + z i)| ^ s) ^ (1 / s)) ^ s
            = ∑ i ∈ Finset.range K, f (m₀ + i)
        rw [rpow_inv_pow hs0 (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) s))]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [f]
        rw [hzval i, hzval (i + 1)]
        congr 1
      have hzBdd : BddAbove (Set.range (Bv ⟨z, hz⟩)) := by
        refine ⟨M, fun x hx => ?_⟩
        rcases hx with ⟨K, rfl⟩
        have hineq : (Bv ⟨z, hz⟩ K) ^ s ≤ M ^ s := by
          rw [hzsum K]
          calc ∑ i ∈ Finset.range K, f (m₀ + i) ≤ ∑ j ∈ Finset.range (m₀ + K), f j := by
                rw [Finset.sum_range_add f m₀ K]
                exact le_add_of_nonneg_left (Finset.sum_nonneg (fun j _ => hfnn j))
            _ = (A u (m₀ + K)) ^ s := by
                rw [hAeq]
                exact (rpow_inv_pow hs0 (Finset.sum_nonneg (fun j _ => hfnn j))).symm
            _ ≤ M ^ s := Real.rpow_le_rpow (hAnn u _) (hAub _) (le_of_lt hs0)
        calc Bv ⟨z, hz⟩ K = ((Bv ⟨z, hz⟩ K) ^ s) ^ (1 / s) :=
              (rpow_pow_inv hs0 (hBnn _ _)).symm
          _ ≤ (M ^ s) ^ (1 / s) :=
              Real.rpow_le_rpow (Real.rpow_nonneg (hBnn _ _) s) hineq (le_of_lt h1s0)
          _ = M := rpow_pow_inv hs0 hMnn
      have htail : Bv ⟨z, hz⟩ (J - m₀) ≤ sSup (Set.range v) :=
        le_trans (le_csSup hzBdd ⟨J - m₀, rfl⟩) (hVub ⟨z, hz⟩)
      have hzLeSq : ∀ K, (Bv ⟨z, hz⟩ K) ^ s ≤ M ^ s := by
        intro K
        rw [hzsum K]
        calc ∑ i ∈ Finset.range K, f (m₀ + i) ≤ ∑ j ∈ Finset.range (m₀ + K), f j := by
              rw [Finset.sum_range_add f m₀ K]
              exact le_add_of_nonneg_left (Finset.sum_nonneg (fun j _ => hfnn j))
          _ = (A u (m₀ + K)) ^ s := by
              rw [hAeq]
              exact (rpow_inv_pow hs0 (Finset.sum_nonneg (fun j _ => hfnn j))).symm
          _ ≤ M ^ s := Real.rpow_le_rpow (hAnn u _) (hAub _) (le_of_lt hs0)
      -- transition term bound
      have ht : |b (u.1 m₀)| ≤ |b n₀| + sSup (Set.range v) := by
        have h1 : |b (u.1 m₀)| ≤ |b n₀| + |b (u.1 m₀) - b n₀| := by
          have he : b (u.1 m₀) = b n₀ + (b (u.1 m₀) - b n₀) := by ring
          conv_lhs => rw [he]
          exact abs_add_le _ _
        have h2 : |b (u.1 m₀) - b n₀| ≤ sSup (Set.range v) := by
          by_cases hz0 : z 0 = 0
          · have hlim : u.1 m₀ = n₀ := by
              have hge := hm₀spec
              simp only [z, Nat.add_zero] at hz0
              omega
            rw [hlim, sub_self, abs_zero]
            exact hVnn
          · have hz0pos : 1 ≤ z 0 := Nat.one_le_iff_ne_zero.mpr hz0
            let w₂ : ℕ → ℕ := fun i => if i = 0 then 0 else z (i - 1)
            have hw₂0 : w₂ 0 = 0 := by simp [w₂]
            have hw₂1 : w₂ 1 = z 0 := by simp [w₂]
            have hw₂ : StrictMono w₂ := by
              intro i j hij
              by_cases hi0 : i = 0
              · subst hi0
                have hj0 : j ≠ 0 := by omega
                have hne : (if (0:ℕ) = 0 then 0 else z (0 - 1)) = 0 := if_pos rfl
                rw [show w₂ 0 = 0 from hw₂0, show w₂ j = z (j - 1) from by simp [w₂, hj0]]
                calc (0 : ℕ) < 1 := Nat.one_pos
                  _ ≤ z 0 := hz0pos
                  _ ≤ z (j - 1) := hz.monotone (by omega)
              · have hj0 : j ≠ 0 := by omega
                rw [show w₂ i = z (i - 1) from by simp [w₂, hi0],
                  show w₂ j = z (j - 1) from by simp [w₂, hj0]]
                exact hz (by omega)
            have hw2Le : ∀ K, Bv ⟨w₂, hw₂⟩ K ≤ |b (u.1 m₀) - b n₀| + M := by
              intro K
              have hle1 : (Bv ⟨w₂, hw₂⟩ K) ^ s ≤ |b (u.1 m₀) - b n₀| ^ s + M ^ s := by
                show ((∑ j ∈ Finset.range K,
                  |b (n₀ + w₂ (j + 1)) - b (n₀ + w₂ j)| ^ s) ^ (1 / s)) ^ s
                    ≤ |b (u.1 m₀) - b n₀| ^ s + M ^ s
                rw [rpow_inv_pow hs0
                  (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) s))]
                rcases Nat.eq_zero_or_pos K with hK | hK
                · rw [hK, Finset.sum_range_zero]
                  positivity
                · rw [show K = (K - 1) + 1 by omega, Finset.sum_range_succ']
                  have hg0 : |b (n₀ + w₂ (0 + 1)) - b (n₀ + w₂ 0)| ^ s
                      = |b (u.1 m₀) - b n₀| ^ s := by
                    rw [zero_add, hw₂1, hw₂0, add_zero]
                    rw [hzval 0, Nat.add_zero]
                  have hgtail : ∑ i ∈ Finset.range (K - 1),
                      |b (n₀ + w₂ (i + 1 + 1)) - b (n₀ + w₂ (i + 1))| ^ s ≤ M ^ s := by
                    have hcongr : ∑ i ∈ Finset.range (K - 1),
                        |b (n₀ + w₂ (i + 1 + 1)) - b (n₀ + w₂ (i + 1))| ^ s
                        = ∑ i ∈ Finset.range (K - 1), f (m₀ + i) := by
                      refine Finset.sum_congr rfl (fun i hi => ?_)
                      have hi1 : w₂ (i + 1) = z i := by
                        simp only [w₂]
                        rw [if_neg (by omega : i + 1 ≠ 0)]
                        congr 1
                      have hi2 : w₂ (i + 1 + 1) = z (i + 1) := by
                        simp only [w₂]
                        rw [if_neg (by omega : i + 1 + 1 ≠ 0)]
                        congr 1
                      rw [hi1, hi2]
                      simp only [f]
                      rw [hzval i, hzval (i + 1)]
                      congr 1
                    rw [hcongr, ← hzsum (K - 1)]
                    exact hzLeSq (K - 1)
                  rw [hg0]
                  linarith [hgtail]
              calc Bv ⟨w₂, hw₂⟩ K = ((Bv ⟨w₂, hw₂⟩ K) ^ s) ^ (1 / s) :=
                    (rpow_pow_inv hs0 (hBnn _ _)).symm
                _ ≤ (|b (u.1 m₀) - b n₀| ^ s + M ^ s) ^ (1 / s) :=
                    Real.rpow_le_rpow (Real.rpow_nonneg (hBnn _ _) s) hle1 (le_of_lt h1s0)
                _ ≤ |b (u.1 m₀) - b n₀| + M := rpow_sum_le_add hs1 (abs_nonneg _) hMnn
            have hw2Bdd : BddAbove (Set.range (Bv ⟨w₂, hw₂⟩)) :=
              ⟨|b (u.1 m₀) - b n₀| + M, fun x hx => by
                rcases hx with ⟨K, rfl⟩
                exact hw2Le K⟩
            have hval : Bv ⟨w₂, hw₂⟩ 1 = |b (u.1 m₀) - b n₀| := by
              show ((∑ j ∈ Finset.range 1,
                |b (n₀ + w₂ (j + 1)) - b (n₀ + w₂ j)| ^ s) ^ (1 / s)) = |b (u.1 m₀) - b n₀|
              rw [Finset.sum_range_one]
              simp only [zero_add, hw₂1, hw₂0, add_zero]
              rw [hzval 0, Nat.add_zero]
              exact rpow_pow_inv hs0 (abs_nonneg _)
            calc |b (u.1 m₀) - b n₀| = Bv ⟨w₂, hw₂⟩ 1 := hval.symm
              _ ≤ v ⟨w₂, hw₂⟩ := le_csSup hw2Bdd ⟨1, rfl⟩
              _ ≤ sSup (Set.range v) := hVub _
        linarith
      -- main decomposition
      have hsplit : ∑ j ∈ Finset.range J, f j
          = (∑ j ∈ Finset.range (min J m₀), f j)
            + ∑ j ∈ Finset.range (J - m₀), f (m₀ + j) := by
        rcases le_or_gt m₀ J with h | h
        · rw [min_eq_right h]
          conv_lhs => rw [show J = m₀ + (J - m₀) by omega]
          rw [Finset.sum_range_add]
        · rw [min_eq_left (le_of_lt h), Nat.sub_eq_zero_of_le (le_of_lt h),
            Finset.sum_range_zero, add_zero]
      have hfirst : ∑ j ∈ Finset.range (min J m₀), f j ≤ |b (u.1 m₀)| ^ s := by
        rcases eq_or_lt_of_le (min_le_right J m₀) with hK | hK
        · rw [hK]
          rcases Nat.eq_zero_or_pos m₀ with hm | hm
          · rw [hm, Finset.sum_range_zero]
            exact Real.rpow_nonneg (abs_nonneg _) s
          · rw [show m₀ = (m₀ - 1) + 1 by omega, Finset.sum_range_succ]
            have hz0 : ∑ j ∈ Finset.range (m₀ - 1), f j = 0 := by
              apply Finset.sum_eq_zero
              intro j hj
              rw [Finset.mem_range] at hj
              have h1 : u.1 (j + 1) < n₀ := hbelow (j + 1) (by omega)
              have h2 : u.1 j < n₀ := hbelow j (by omega)
              simp only [f, hzero _ h1, hzero _ h2, sub_zero, abs_zero]
              exact Real.zero_rpow (ne_of_gt hs0)
            rw [hz0, zero_add]
            have h3 : u.1 (m₀ - 1) < n₀ := hbelow (m₀ - 1) (by omega)
            simp only [f, hzero _ h3, sub_zero]
            exact le_rfl
        · have hz0 : ∑ j ∈ Finset.range (min J m₀), f j = 0 := by
            apply Finset.sum_eq_zero
            intro j hj
            rw [Finset.mem_range] at hj
            have h1 : u.1 (j + 1) < n₀ := hbelow (j + 1) (by omega)
            have h2 : u.1 j < n₀ := hbelow j (by omega)
            simp only [f, hzero _ h1, hzero _ h2, sub_zero, abs_zero]
            exact Real.zero_rpow (ne_of_gt hs0)
          rw [hz0]
          exact Real.rpow_nonneg (abs_nonneg _) s
      have htailsum : ∑ j ∈ Finset.range (J - m₀), f (m₀ + j)
          = (Bv ⟨z, hz⟩ (J - m₀)) ^ s := by
        rw [eq_comm, hzsum (J - m₀)]
      have hsumlb : ∑ j ∈ Finset.range J, f j
          ≤ |b (u.1 m₀)| ^ s + (Bv ⟨z, hz⟩ (J - m₀)) ^ s := by
        rw [hsplit, htailsum]
        linarith [hfirst]
      calc A u J = (∑ j ∈ Finset.range J, f j) ^ (1 / s) := hAeq J
        _ ≤ (|b (u.1 m₀)| ^ s + (Bv ⟨z, hz⟩ (J - m₀)) ^ s) ^ (1 / s) :=
            Real.rpow_le_rpow (Finset.sum_nonneg (fun j _ => hfnn j)) hsumlb (le_of_lt h1s0)
        _ ≤ |b (u.1 m₀)| + Bv ⟨z, hz⟩ (J - m₀) :=
            rpow_sum_le_add hs1 (abs_nonneg _) (hBnn _ _)
        _ ≤ |b (u.1 m₀)| + sSup (Set.range v) := by linarith [htail]
        _ ≤ (|b n₀| + sSup (Set.range v)) + sSup (Set.range v) := by linarith [ht]
        _ = |b n₀| + 2 * sSup (Set.range v) := by ring
    · rw [show a u = sSup (Set.range (A u)) from rfl,
        sSup_range_eq_zero_of_not_bddAbove hrowb]
      exact hcnn
  · change (⨆ u : U, a u) ≤ |b n₀| + 2 * sSup (Set.range v)
    have hzero_a : (⨆ u : U, a u) = 0 := by
      rw [show (⨆ u : U, a u) = sSup (Set.range a) from rfl]
      exact sSup_range_eq_zero_of_not_bddAbove (f := a) hb
    rw [hzero_a]
    have hVnn : 0 ≤ sSup (Set.range v) := by
      by_cases h : BddAbove (Set.range v)
      · exact le_trans (hvnn ⟨id, strictMono_id⟩) (le_csSup h ⟨_, rfl⟩)
      · rw [sSup_range_eq_zero_of_not_bddAbove (f := v) h]
    exact add_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) hVnn)

end Commons.Analysis.Series