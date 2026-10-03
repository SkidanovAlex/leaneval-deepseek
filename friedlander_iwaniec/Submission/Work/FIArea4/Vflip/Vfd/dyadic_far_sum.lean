import Mathlib

namespace Work.FIArea4.Vflip.Vfd

open Finset

/-- **Geometric tail bound.**  For `0 ≤ r < 1` and a finite set `S ⊆ ℕ` contained in
`range J` all of whose elements are `≥ c`, the sum `∑_{j ∈ S} r^j` is at most the geometric
tail `r^c / (1 - r)` starting at `c`. -/
private lemma geom_sum_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {S : Finset ℕ} {J c : ℕ}
    (hS : S ⊆ Finset.range J) (hc : ∀ j ∈ S, c ≤ j) :
    ∑ j ∈ S, r ^ j ≤ r ^ c / (1 - r) := by
  have h1r : 0 < 1 - r := by linarith
  have hsplit : ∑ j ∈ S, r ^ j = r ^ c * ∑ j ∈ S, r ^ (j - c) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [← pow_add, Nat.add_sub_cancel' (hc j hj)]
  rw [hsplit]
  have hInj : Set.InjOn (fun j => j - c) ↑S := by
    intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    simp only at hab
    have h1 := hc a ha
    have h2 := hc b hb
    omega
  have hsub : S.image (fun j => j - c) ⊆ Finset.range J := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨j, hj, rfl⟩ := hk
    rw [Finset.mem_range]
    have h := hS hj
    rw [Finset.mem_range] at h
    omega
  have hstep : ∑ k ∈ S.image (fun j => j - c), r ^ k ≤ ∑ k ∈ Finset.range J, r ^ k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => pow_nonneg hr0 k)
  have hgeom : ∑ k ∈ Finset.range J, r ^ k ≤ 1 / (1 - r) := by
    rw [geom_sum_eq (by linarith : r ≠ 1)]
    rw [show r ^ J - 1 = -(1 - r ^ J) by ring, show r - 1 = -(1 - r) by ring, neg_div_neg_eq]
    exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0 J]) h1r.le
  have hinner : ∑ j ∈ S, r ^ (j - c) ≤ 1 / (1 - r) := by
    rw [← Finset.sum_image hInj]
    exact le_trans hstep hgeom
  calc r ^ c * ∑ j ∈ S, r ^ (j - c)
      ≤ r ^ c * (1 / (1 - r)) := mul_le_mul_of_nonneg_left hinner (pow_nonneg hr0 c)
    _ = r ^ c / (1 - r) := by ring

/-- `(2^j)^{-1/2} = (2^{-1/2})^j`. -/
private lemma two_pow_half (j : ℕ) :
    ((2 : ℝ) ^ j) ^ (-(1 : ℝ) / 2) = ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ j := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have h1 : ((2 : ℝ) ^ j) ^ (-(1 : ℝ) / 2) = (2 : ℝ) ^ ((j : ℝ) * (-(1 : ℝ) / 2)) := by
    rw [← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul h2]
  have h2' : ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ j = (2 : ℝ) ^ ((j : ℝ) * (-(1 : ℝ) / 2)) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(1 : ℝ) / 2)) j]
    rw [← Real.rpow_mul h2 (-(1 : ℝ) / 2) (j : ℝ)]
    congr 1
    ring
  rw [h1, h2']

/-- The dyadic rpow factorisation `(m · 2^j)^{-1/2} = m^{-1/2} · (2^{-1/2})^j`. -/
private lemma dyadic_rpow_eq (m : ℝ) (hm : 0 < m) (j : ℕ) :
    (m * (2 : ℝ) ^ j) ^ (-(1 : ℝ) / 2) = m ^ (-(1 : ℝ) / 2) * ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ j := by
  rw [Real.mul_rpow hm.le (by positivity)]
  congr 1
  exact two_pow_half j

/-- Numerical bound `2^{-1/2} ≤ 5/6`. -/
private lemma r_half_le_five_sixth : (2 : ℝ) ^ (-(1 : ℝ) / 2) ≤ (5 : ℝ) / 6 := by
  have hsq : (2 : ℝ) ^ (-(1 : ℝ) / 2) = (Real.sqrt 2)⁻¹ := by
    rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_eq_rpow]
  have hs : (6 : ℝ) / 5 ≤ Real.sqrt 2 := by
    have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  rw [hsq]
  calc (Real.sqrt 2)⁻¹ ≤ ((6 : ℝ) / 5)⁻¹ :=
        (inv_le_inv₀ (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)).mpr hs
    _ = 5 / 6 := by norm_num

/-- Numerical bound `2^{1/2} ≤ 10 (1 - 2^{-1/2})`. -/
private lemma two_half_le : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 10 * (1 - (2 : ℝ) ^ (-(1 : ℝ) / 2)) := by
  have hr : (2 : ℝ) ^ (-(1 : ℝ) / 2) ≤ (5 : ℝ) / 6 := r_half_le_five_sixth
  have h2 : (2 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt 2 := (Real.sqrt_eq_rpow 2).symm
  have hs : Real.sqrt 2 ≤ (3 : ℝ) / 2 := by
    have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  rw [h2]; linarith

/-- **Bound for the `A`-piece.**  Over a dyadic range `S` with `2^j · 2 > Qmin` throughout,
`∑_{j ∈ S} (m · 2^j)^{-1/2} · A ≤ 10 · (m Qmin)^{-1/2} · A`. -/
private lemma Asum_le {m Qmin A : ℝ} {J : ℕ} {S : Finset ℕ}
    (hm : 0 < m) (hqmin : 0 < Qmin) (hA : 0 ≤ A)
    (hSsub : S ⊆ Finset.range J)
    (hs : ∀ j ∈ S, (2 : ℝ) ^ j * 2 > Qmin) :
    ∑ j ∈ S, (m * (2 : ℝ) ^ j) ^ (-(1 : ℝ) / 2) * A
      ≤ 10 * ((m * Qmin) ^ (-(1 : ℝ) / 2) * A) := by
  set r : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / 2) with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; exact Real.rpow_nonneg (by norm_num) _
  have hrle : r ≤ 5 / 6 := by rw [hrdef]; exact r_half_le_five_sixth
  have hr1 : r < 1 := by linarith
  have h1r : 0 < 1 - r := by linarith
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.sum_empty]
    have : 0 ≤ 10 * ((m * Qmin) ^ (-(1 : ℝ) / 2) * A) :=
      mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg (by positivity) _) hA)
    linarith
  · set c := S.min' hne with hcdef
    have hcmem : c ∈ S := Finset.min'_mem S hne
    have hcle : ∀ j ∈ S, c ≤ j := fun j hj => Finset.min'_le S j hj
    have hsum : ∑ j ∈ S, (m * (2 : ℝ) ^ j) ^ (-(1 : ℝ) / 2) = m ^ (-(1 : ℝ) / 2) * ∑ j ∈ S, r ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [hrdef]
      exact dyadic_rpow_eq m hm j
    have hgeom : ∑ j ∈ S, r ^ j ≤ r ^ c / (1 - r) := geom_sum_le hr0 hr1 hSsub hcle
    have hrc : r ^ c ≤ (Qmin / 2) ^ (-(1 : ℝ) / 2) := by
      rw [hrdef, ← two_pow_half c]
      exact Real.rpow_le_rpow_of_nonpos (by linarith)
        (by have := hs c hcmem; linarith) (by norm_num)
    have hqhalf : (Qmin / 2) ^ (-(1 : ℝ) / 2) = (2 : ℝ) ^ ((1 : ℝ) / 2) * Qmin ^ (-(1 : ℝ) / 2) := by
      rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring]
      rw [Real.div_rpow (le_of_lt hqmin) (by norm_num : (0 : ℝ) ≤ 2)]
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [div_eq_mul_inv, inv_inv]
      ring
    have hnumer : (2 : ℝ) ^ ((1 : ℝ) / 2) / (1 - r) ≤ 10 := by
      rw [div_le_iff₀ h1r]
      exact two_half_le
    have hxmq : m ^ (-(1 : ℝ) / 2) * Qmin ^ (-(1 : ℝ) / 2) = (m * Qmin) ^ (-(1 : ℝ) / 2) :=
      (Real.mul_rpow hm.le hqmin.le).symm
    have hSsum : ∑ j ∈ S, (m * (2 : ℝ) ^ j) ^ (-(1 : ℝ) / 2) ≤ 10 * (m * Qmin) ^ (-(1 : ℝ) / 2) := by
      rw [hsum]
      calc m ^ (-(1 : ℝ) / 2) * ∑ j ∈ S, r ^ j
          ≤ m ^ (-(1 : ℝ) / 2) * (r ^ c / (1 - r)) :=
            mul_le_mul_of_nonneg_left hgeom (Real.rpow_nonneg hm.le _)
        _ ≤ m ^ (-(1 : ℝ) / 2) * ((Qmin / 2) ^ (-(1 : ℝ) / 2) / (1 - r)) := by
              apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hm.le _)
              exact div_le_div_of_nonneg_right hrc h1r.le
        _ = (m ^ (-(1 : ℝ) / 2) * Qmin ^ (-(1 : ℝ) / 2)) * ((2 : ℝ) ^ ((1 : ℝ) / 2) / (1 - r)) := by
              rw [hqhalf]; ring
        _ = (m * Qmin) ^ (-(1 : ℝ) / 2) * ((2 : ℝ) ^ ((1 : ℝ) / 2) / (1 - r)) := by rw [hxmq]
        _ ≤ (m * Qmin) ^ (-(1 : ℝ) / 2) * 10 :=
              mul_le_mul_of_nonneg_left hnumer (Real.rpow_nonneg (mul_nonneg hm.le hqmin.le) _)
        _ = 10 * (m * Qmin) ^ (-(1 : ℝ) / 2) := by ring
    calc ∑ j ∈ S, (m * (2 : ℝ) ^ j) ^ (-(1 : ℝ) / 2) * A
        = (∑ j ∈ S, (m * (2 : ℝ) ^ j) ^ (-(1 : ℝ) / 2)) * A := (Finset.sum_mul _ _ _).symm
      _ ≤ (10 * (m * Qmin) ^ (-(1 : ℝ) / 2)) * A := mul_le_mul_of_nonneg_right hSsum hA
      _ = 10 * ((m * Qmin) ^ (-(1 : ℝ) / 2) * A) := by ring

/-- **Bound for the `B`-piece.**  Over a dyadic range `S` with `2^j < Qmax` throughout,
`∑_{j ∈ S} m · 2^j · B ≤ 10 · m Qmax · B`. -/
private lemma Bsum_le {m Qmax B : ℝ} {S : Finset ℕ}
    (hm : 0 < m) (hQmax : 0 < Qmax) (hB : 0 ≤ B)
    (hlt : ∀ j ∈ S, (2 : ℝ) ^ j < Qmax) :
    ∑ j ∈ S, m * (2 : ℝ) ^ j * B ≤ 10 * (m * Qmax * B) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.sum_empty]
    have h0 : 0 ≤ m * Qmax * B := mul_nonneg (mul_nonneg (le_of_lt hm) (le_of_lt hQmax)) hB
    linarith
  · set M := S.max' hne with hM
    have hMmem : M ∈ S := Finset.max'_mem S hne
    have hle : ∀ j ∈ S, j ≤ M := fun j hj => Finset.le_max' S j hj
    have hsub : S ⊆ Finset.range (M + 1) := by
      intro j hj; rw [Finset.mem_range]; have := hle j hj; omega
    have hstep : ∑ j ∈ S, (2 : ℝ) ^ j ≤ ∑ j ∈ Finset.range (M + 1), (2 : ℝ) ^ j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
    have hgeom : ∑ j ∈ Finset.range (M + 1), (2 : ℝ) ^ j = (2 : ℝ) ^ (M + 1) - 1 := by
      rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]; norm_num
    have h2M : (2 : ℝ) ^ M < Qmax := hlt M hMmem
    have hbound : ∑ j ∈ S, (2 : ℝ) ^ j ≤ 2 * Qmax := by
      rw [hgeom] at hstep
      have hp : (2 : ℝ) ^ (M + 1) = 2 * (2 : ℝ) ^ M := by rw [pow_succ]; ring
      linarith
    calc ∑ j ∈ S, m * (2 : ℝ) ^ j * B
        = m * B * ∑ j ∈ S, (2 : ℝ) ^ j := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; ring
      _ ≤ m * B * (2 * Qmax) := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = 2 * (m * Qmax * B) := by ring
      _ ≤ 10 * (m * Qmax * B) := by
          have h0 : 0 ≤ m * Qmax * B := mul_nonneg (mul_nonneg (le_of_lt hm) (le_of_lt hQmax)) hB
          linarith

/-- **Bound for the constant piece.**  If every `j ∈ S` satisfies `2^j · 2 > Qmin` and
`2^j < Qmax` with `Qmax ≤ C0 · Qmin`, then `|S| ≤ 10 (log (2 C0) + 1)`. -/
private lemma card_le {Qmin Qmax C0 : ℝ} {S : Finset ℕ}
    (hC0 : 1 ≤ C0)
    (hs : ∀ j ∈ S, (2 : ℝ) ^ j * 2 > Qmin)
    (hlt : ∀ j ∈ S, (2 : ℝ) ^ j < Qmax)
    (hratio : Qmax ≤ C0 * Qmin) :
    (S.card : ℝ) ≤ 10 * (Real.log (2 * C0) + 1) := by
  have hlog2pos : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2C0nn : 0 ≤ Real.log (2 * C0) := by
    apply Real.log_nonneg; linarith
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.card_empty]; simp only [Nat.cast_zero]
    linarith
  · set a := S.min' hne with ha
    set b := S.max' hne with hb
    have hamem : a ∈ S := Finset.min'_mem S hne
    have hbmem : b ∈ S := Finset.max'_mem S hne
    have hale : ∀ j ∈ S, a ≤ j := fun j hj => Finset.min'_le S j hj
    have hble : ∀ j ∈ S, j ≤ b := fun j hj => Finset.le_max' S j hj
    have hab : a ≤ b := hale b hbmem
    have hcard1 : S.card ≤ b - a + 1 := by
      have hsub : S ⊆ Finset.Icc a b := by
        intro j hj; rw [Finset.mem_Icc]; exact ⟨hale j hj, hble j hj⟩
      calc S.card ≤ (Finset.Icc a b).card := Finset.card_le_card hsub
        _ = b + 1 - a := Nat.card_Icc a b
        _ = b - a + 1 := by omega
    have hcardR : (S.card : ℝ) ≤ (b : ℝ) - (a : ℝ) + 1 := by
      have h := Nat.cast_le (α := ℝ).mpr hcard1
      rwa [Nat.cast_add, Nat.cast_one, Nat.cast_sub hab] at h
    have h2a : Qmin / 2 < (2 : ℝ) ^ a := by have := hs a hamem; linarith
    have hprod : (2 : ℝ) ^ b < 2 * C0 * 2 ^ a := by
      have h1 : (2 : ℝ) ^ b < Qmax := hlt b hbmem
      have h3 : C0 * Qmin < C0 * (2 * (2 : ℝ) ^ a) := by
        apply mul_lt_mul_of_pos_left _ (by linarith : (0 : ℝ) < C0)
        linarith
      nlinarith [h1, hratio, h3]
    have hlogineq : (b : ℝ) * Real.log 2 < Real.log (2 * C0) + (a : ℝ) * Real.log 2 := by
      have hpos : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
      have hltlog := Real.log_lt_log hpos hprod
      rw [Real.log_pow] at hltlog
      have e : Real.log (2 * C0 * 2 ^ a) = Real.log (2 * C0) + (a : ℝ) * Real.log 2 := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      rwa [e] at hltlog
    have hba : (b : ℝ) - (a : ℝ) < Real.log (2 * C0) / Real.log 2 := by
      have h1 : ((b : ℝ) - (a : ℝ)) * Real.log 2 < Real.log (2 * C0) := by nlinarith [hlogineq]
      exact (lt_div_iff₀ hlog2pos).mpr h1
    have hinv : 1 / Real.log 2 ≤ 10 := by
      rw [div_le_iff₀ hlog2pos]
      linarith [Real.log_two_gt_d9]
    have hfinal : Real.log (2 * C0) / Real.log 2 + 1 ≤ 10 * (Real.log (2 * C0) + 1) := by
      have hkey : Real.log (2 * C0) / Real.log 2 ≤ 10 * Real.log (2 * C0) := by
        have : Real.log (2 * C0) / Real.log 2 = (1 / Real.log 2) * Real.log (2 * C0) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hinv hlog2C0nn
      linarith
    linarith

/-- **Dyadic "far" sum estimate** (FI §12).  For a dyadic range of scales `2^j` lying in the
window `(Qmin/2, Qmax)` with `Qmax ≤ C0 · Qmin`, the sum
`Σ_j ((m·2^j)^{-1/2} A + m·2^j B + Cc)` is bounded by
`10 · ((m Qmin)^{-1/2} A + m Qmax B + (log (2 C0) + 1) Cc)`. -/
theorem dyadic_far_sum {m Qmin Qmax A B Cc C0 : ℝ} {J : ℕ}
    (hm : 0 < m) (hqmin : 0 < Qmin) (hQmax : 0 < Qmax)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hCc : 0 ≤ Cc)
    (hC0 : 1 ≤ C0) (hratio : Qmax ≤ C0 * Qmin) :
    ∑ j ∈ (Finset.range J).filter (fun j => (2 : ℝ) ^ j * 2 > Qmin ∧ (2 : ℝ) ^ j < Qmax),
        ((m * (2 : ℝ) ^ j) ^ (-(1 : ℝ) / 2) * A + m * (2 : ℝ) ^ j * B + Cc)
      ≤ 10 * ((m * Qmin) ^ (-(1 : ℝ) / 2) * A + m * Qmax * B
              + (Real.log (2 * C0) + 1) * Cc) := by
  set S : Finset ℕ :=
    (Finset.range J).filter (fun j => (2 : ℝ) ^ j * 2 > Qmin ∧ (2 : ℝ) ^ j < Qmax) with hSdef
  have hSsub : S ⊆ Finset.range J := by rw [hSdef]; exact Finset.filter_subset _ _
  have hs : ∀ j ∈ S, (2 : ℝ) ^ j * 2 > Qmin := by
    intro j hj; rw [hSdef, Finset.mem_filter] at hj; exact hj.2.1
  have hlt : ∀ j ∈ S, (2 : ℝ) ^ j < Qmax := by
    intro j hj; rw [hSdef, Finset.mem_filter] at hj; exact hj.2.2
  have hAsum := Asum_le hm hqmin hA hSsub hs
  have hBsum := Bsum_le hm hQmax hB hlt
  have hcard := card_le hC0 hs hlt hratio
  have hCsum : ∑ _j ∈ S, Cc ≤ 10 * ((Real.log (2 * C0) + 1) * Cc) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    calc (S.card : ℝ) * Cc ≤ (10 * (Real.log (2 * C0) + 1)) * Cc :=
          mul_le_mul_of_nonneg_right hcard hCc
      _ = 10 * ((Real.log (2 * C0) + 1) * Cc) := by ring
  have hdecomp : ∑ j ∈ S, ((m * (2 : ℝ) ^ j) ^ (-(1 : ℝ) / 2) * A + m * (2 : ℝ) ^ j * B + Cc)
      = (∑ j ∈ S, (m * (2 : ℝ) ^ j) ^ (-(1 : ℝ) / 2) * A)
        + (∑ j ∈ S, m * (2 : ℝ) ^ j * B) + ∑ _j ∈ S, Cc := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hdecomp]
  calc (∑ j ∈ S, (m * (2 : ℝ) ^ j) ^ (-(1 : ℝ) / 2) * A)
        + (∑ j ∈ S, m * (2 : ℝ) ^ j * B) + ∑ _j ∈ S, Cc
      ≤ 10 * ((m * Qmin) ^ (-(1 : ℝ) / 2) * A) + 10 * (m * Qmax * B)
        + 10 * ((Real.log (2 * C0) + 1) * Cc) := by
        linarith [hAsum, hBsum, hCsum]
    _ = 10 * ((m * Qmin) ^ (-(1 : ℝ) / 2) * A + m * Qmax * B
              + (Real.log (2 * C0) + 1) * Cc) := by ring

end Work.FIArea4.Vflip.Vfd
