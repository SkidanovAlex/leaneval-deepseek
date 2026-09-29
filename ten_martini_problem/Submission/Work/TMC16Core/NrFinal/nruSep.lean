import Mathlib
import Submission.Work.TMC16Core.Core.uni_nonres3_support
import Submission.Work.TMC16Core.Core.uni_nonres3_havoid
import Submission.Work.TMC16Core.Core.blk_sep_base
import Submission.Work.TMC16Core.NrFinal.sepArith

/-!
# `nruSep`: a self-contained copy of the separation estimate `NrFinal.sep`

`NrFinal.sep` is proved from the helper `sep_mbound2` (`Submission/Work/TMC16Core/NrFinal/
sep_mbound2.lean`), which is incomplete elsewhere; the copy here replaces that helper by the
self-contained numerical lemma `nru_mbound` proved below, so that the separation estimate is
available axiom-free.  The statement of `nru_sep` is verbatim the statement of
`Work.TMC16Core.NrFinal.sep`.
-/

namespace Work.TMC16Core.NrFinal

open Work.TMC16Core

private lemma nru_key_poly {v : ℝ} (hv : 1 ≤ v) : 0 ≤ 123 * v^9 - 160 * v^8 + 640 := by
  rcases le_or_gt v (4/3) with h | h
  · have hv0 : 0 ≤ v := by linarith
    have hv9 : v^9 ≤ (4/3:ℝ)^9 := pow_le_pow_left₀ hv0 h 9
    have hv98 : v^8 ≤ v^9 := by
      calc v^8 = v^8 * 1 := by ring
        _ ≤ v^8 * v := by exact mul_le_mul_of_nonneg_left hv (by positivity)
        _ = v^9 := by ring
    have h37 : (37:ℝ) * (4/3)^9 ≤ 640 := by norm_num
    have h4 : 37 * v^9 ≤ 37 * (4/3)^9 := mul_le_mul_of_nonneg_left hv9 (by norm_num)
    nlinarith [h4, h37, hv98]
  · have hv8 : 0 ≤ v^8 := by positivity
    have h160 : (0:ℝ) ≤ v^8 * (123*v - 160) := by
      apply mul_nonneg hv8; nlinarith
    nlinarith [h160]

private lemma nru_rpow_key {A : ℝ} (hA : 1 ≤ A) : (A ^ (8/9 : ℝ) - 4) / A ≤ 123/160 := by
  have hApos : 0 < A := lt_of_lt_of_le one_pos hA
  set v : ℝ := A ^ (1/9 : ℝ) with hv
  have hv1 : 1 ≤ v := by
    rw [hv]; exact Real.one_le_rpow hA (by norm_num)
  have hv9 : v^9 = A := by
    rw [hv]
    rw [← Real.rpow_mul_natCast (le_of_lt hApos) (1/9) 9]
    rw [show (1/9:ℝ) * ((9:ℕ):ℝ) = 1 by norm_num, Real.rpow_one]
  have hv8 : A ^ (8/9 : ℝ) = v^8 := by
    rw [show (8/9:ℝ) = (1/9) * ((8:ℕ):ℝ) by norm_num]
    rw [Real.rpow_mul_natCast (le_of_lt hApos) (1/9) 8, ← hv]
  rw [hv8, ← hv9]
  have hvpos : (0:ℝ) < v^9 := by positivity
  rw [div_le_iff₀ hvpos]
  have hp := nru_key_poly (v := v) hv1
  nlinarith [hp]

theorem nru_mbound {qn1 qn y T Dn : ℝ} (hqn1 : 1 ≤ qn1) (hqn : 0 < qn) (hqnle : qn ≤ qn1)
    (hT : 4 ≤ T) (hyT : T ≤ y)
    (hy : y ≤ max (Real.rpow qn1 (8/9)) (qn/20)) (hDn0 : 0 ≤ Dn) (hDn : Dn ≤ 1/qn1) :
    (y - T) * Dn ≤ 123/160 := by
  have hA : 0 < qn1 := lt_of_lt_of_le (by norm_num) hqn1
  have hyT0 : 0 ≤ y - T := by linarith
  have step1 : (y - T) * Dn ≤ (y - T) / qn1 := by
    have h := mul_le_mul_of_nonneg_left hDn hyT0
    rwa [mul_one_div] at h
  have step2 : (y - T) / qn1 ≤ (max (Real.rpow qn1 (8/9)) (qn/20) - 4) / qn1 := by
    apply div_le_div_of_nonneg_right _ hA.le
    linarith
  have step3 : (max (Real.rpow qn1 (8/9)) (qn/20) - 4) / qn1 ≤ 123/160 := by
    rcases le_total (qn/20) (Real.rpow qn1 (8/9)) with h | h
    · rw [max_eq_left h]
      exact nru_rpow_key hqn1
    · rw [max_eq_right h]
      have h1 : (qn/20 - 4) / qn1 ≤ (qn/20) / qn1 := by
        apply div_le_div_of_nonneg_right _ hA.le; linarith
      have h2 : (qn/20) / qn1 = qn / (20 * qn1) := by ring
      have h3 : qn / (20 * qn1) ≤ 1/20 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hqnle]
      linarith
  linarith [step1, step2, step3]


theorem nru_sep {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n s a' b' m : ℕ} {y : ℤ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) → Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    (hn : 2 ≤ n) (hL : 1 ≤ q (n - 1)) (hs : 1 ≤ s) (hab : a' + b' = s)
    (hy1 : 1 ≤ y)
    (hyΔ : (y : ℝ) * Δ n ≤ 3 / 4)
    (hym : (m : ℤ) * (q n : ℤ) ≤ y) (hym' : y < ((m : ℤ) + 1) * (q n : ℤ))
    (hnres : ∀ ℓ : ℤ, (s : ℤ) * (q (n - 1) : ℤ) ≤ |y - (ℓ : ℤ) * (q n : ℤ)|)
    (hsL : (2 * (s : ℤ)) * (q (n - 1) : ℤ) < (q n : ℤ))
    {d k : ℤ} (hd : d ∈ Work.TMC16Core.Core.Dnr q n s a' b' y)
    (hk : k ∈ Work.TMC16Core.Core.Dnr q n s a' b' y) (hne : d ≠ k) :
    1 / (32 * (q n : ℝ)) ≤ Work.TMC16Core.fracDist (((k - d : ℤ) : ℝ) * α) := by
  classical
  have hTn : 2 * s * q (n - 1) ≤ q n := by
    have h : (2 * (s : ℤ)) * ((q (n - 1) : ℕ) : ℤ) ≤ ((q n : ℕ) : ℤ) := le_of_lt hsL
    exact_mod_cast h
  have hy0 : (0 : ℤ) ≤ y := by omega
  have hyTz : (s : ℤ) * (q (n - 1) : ℤ) ≤ y := by
    have h := hnres 0
    rw [zero_mul, sub_zero, abs_of_nonneg hy0] at h
    exact h
  have hypos : (0 : ℤ) < y := by omega
  obtain ⟨N, hNz⟩ : ∃ N : ℕ, (N : ℤ) = |k - d| := ⟨_, Int.natCast_natAbs (k - d)⟩
  have hkd_ne : k - d ≠ 0 := by intro h; exact hne (by omega)
  have hNpos : 0 < N := by
    have : (0 : ℤ) < (N : ℤ) := by rw [hNz]; exact abs_pos.mpr hkd_ne
    omega
  have hfd : Work.TMC16Core.fracDist (((k - d : ℤ) : ℝ) * α) = Work.TMC16Core.fracDist ((N : ℝ) * α) := by
    rw [Core.fracDist_int_abs]
    congr 1
    have h1 : ((((k - d).natAbs : ℕ) : ℤ)) = (N : ℤ) := by rw [hNz, Int.natCast_natAbs]
    have h2 : ((((k - d).natAbs : ℕ) : ℝ)) = (N : ℝ) := by exact_mod_cast h1
    rw [h2]
  rw [hfd]
  by_cases hsmall : N < q n
  · have hge := Core.emod_sub_ge hqpos hmono hΔpos hΔeq hΔup hΔlo hbest (n := n) (t := (N : ℤ))
      (by omega) (by exact_mod_cast hsmall)
    have hcast2 : (((N : ℤ) : ℝ) * α) = (N : ℝ) * α := by push_cast; ring
    rw [hcast2] at hge
    have hle : 1 / (32 * (q n : ℝ)) ≤ 1 / (2 * (q n : ℝ)) := by
      have hqnR : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hqpos n
      rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
    linarith
  · push_neg at hsmall
    -- ================= cross structure =================
    have hk12 : k ∈ Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ))) ((a' : ℤ) * (q (n - 1) : ℤ) - 1) ∨
        k ∈ Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ)) (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1) := by
      have h := hk; rw [Core.Dnr] at h; exact Finset.mem_union.mp h
    have hd12 : d ∈ Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ))) ((a' : ℤ) * (q (n - 1) : ℤ) - 1) ∨
        d ∈ Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ)) (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1) := by
      have h := hd; rw [Core.Dnr] at h; exact Finset.mem_union.mp h
    have ha's : ((a' : ℤ)) ≤ (s : ℤ) := by have := hab; omega
    have hb's : ((b' : ℤ)) ≤ (s : ℤ) := by have := hab; omega
    have hcross : (k ∈ Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ)) (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1) ∧
        d ∈ Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ))) ((a' : ℤ) * (q (n - 1) : ℤ) - 1)) ∨
      (k ∈ Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ))) ((a' : ℤ) * (q (n - 1) : ℤ) - 1) ∧
        d ∈ Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ)) (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1)) := by
      rcases hk12 with hk1 | hk2 <;> rcases hd12 with hd1 | hd2
      · exfalso; have h := Core.Dnr_inter1_diff_lt hk1 hd1 hTn ha's; rw [← hNz] at h; omega
      · exact Or.inr ⟨hk1, hd2⟩
      · exact Or.inl ⟨hk2, hd1⟩
      · exfalso; have h := Core.Dnr_inter2_diff_lt hk2 hd2 hTn hb's; rw [← hNz] at h; omega
    have ha1 : 1 ≤ a' := by
      rcases hcross with ⟨_, hI⟩ | ⟨hI, _⟩
      · by_contra hcon; push_neg at hcon
        have h0 : a' = 0 := by omega
        rw [h0, Finset.mem_Icc] at hI
        simp only [Nat.cast_zero, zero_mul, neg_zero] at hI; omega
      · by_contra hcon; push_neg at hcon
        have h0 : a' = 0 := by omega
        rw [h0, Finset.mem_Icc] at hI
        simp only [Nat.cast_zero, zero_mul, neg_zero] at hI; omega
    have hb1 : 1 ≤ b' := by
      rcases hcross with ⟨hI, _⟩ | ⟨_, hI⟩
      · by_contra hcon; push_neg at hcon
        have h0 : b' = 0 := by omega
        rw [h0] at hI
        simp only [Nat.cast_zero, zero_mul] at hI
        rw [Finset.mem_Icc] at hI; omega
      · by_contra hcon; push_neg at hcon
        have h0 : b' = 0 := by omega
        rw [h0] at hI
        simp only [Nat.cast_zero, zero_mul] at hI
        rw [Finset.mem_Icc] at hI; omega
    have hspos : 2 ≤ s := by omega
    have hL2 : 2 ≤ q (n - 1) := by
      have hn1 : 1 ≤ n - 1 := by omega
      have hm' : q 1 ≤ q (n - 1) := hmono.monotone hn1
      have hp : 1 ≤ q 0 := hqpos 0
      have hlt : q 0 < q 1 := hmono (by norm_num)
      omega
    have hs2z : (2 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hspos
    have hL0z : (0 : ℤ) ≤ (q (n - 1) : ℤ) := by positivity
    have hT4z : (4 : ℤ) ≤ (s : ℤ) * (q (n - 1) : ℤ) := by
      have hL2z : (2 : ℤ) ≤ (q (n - 1) : ℤ) := by exact_mod_cast hL2
      nlinarith [hs2z, hL2z]
    have h4Llt : (4 : ℤ) * (q (n - 1) : ℤ) < (q n : ℤ) := by
      nlinarith [hsL, hs2z, hL0z]
    have h4Lle : (4 : ℝ) * (q (n - 1) : ℝ) ≤ (q n : ℝ) := by
      have := le_of_lt h4Llt; exact_mod_cast this
    -- N range
    have hsumz : ((s : ℤ) * (q (n - 1) : ℤ)) =
        (a' : ℤ) * (q (n - 1) : ℤ) + (b' : ℤ) * (q (n - 1) : ℤ) := by
      have h := hab; rw [← h]; push_cast; ring
    have hNrange : y - (s : ℤ) * (q (n - 1) : ℤ) + 1 ≤ (N : ℤ) ∧
        (N : ℤ) ≤ y + (s : ℤ) * (q (n - 1) : ℤ) - 1 := by
      rcases hcross with ⟨hkI2, hdI1⟩ | ⟨hkI1, hdI2⟩
      · rw [Finset.mem_Icc] at hkI2 hdI1
        have hpos : 0 < k - d := by linarith [hkI2.1, hdI1.2, hyTz]
        rw [hNz, abs_of_pos hpos]
        constructor <;> linarith [hkI2.1, hkI2.2, hdI1.1, hdI1.2, hsumz]
      · rw [Finset.mem_Icc] at hkI1 hdI2
        have hpos : 0 < d - k := by linarith [hdI2.1, hkI1.2, hyTz]
        rw [hNz, abs_of_neg (by linarith : k - d < 0)]
        constructor <;> linarith [hkI1.1, hkI1.2, hdI2.1, hdI2.2, hsumz]
    -- ================= decomposition =================
    set M0 : ℤ := y / (q n : ℤ) with hM0
    set t0 : ℤ := y % (q n : ℤ) with ht0
    have hqnZ : (0 : ℤ) < (q n : ℤ) := by exact_mod_cast hqpos n
    have hdecy : y = M0 * (q n : ℤ) + t0 := by rw [hM0, ht0, Int.ediv_mul_add_emod]
    have ht0nn : 0 ≤ t0 := by rw [ht0]; exact Int.emod_nonneg y (ne_of_gt hqnZ)
    have ht0lt : t0 < (q n : ℤ) := by rw [ht0]; exact Int.emod_lt_of_pos y hqnZ
    have hM0nn : 0 ≤ M0 := by rw [hM0]; exact Int.ediv_nonneg (by omega) (le_of_lt hqnZ)
    have ht0ge : (s : ℤ) * (q (n - 1) : ℤ) ≤ t0 := by
      have h := hnres M0
      rw [show y - M0 * (q n : ℤ) = t0 from by omega, abs_of_nonneg ht0nn] at h
      exact h
    have ht0le : t0 ≤ (q n : ℤ) - (s : ℤ) * (q (n - 1) : ℤ) := by
      have h := hnres (M0 + 1)
      have hEq : y - (M0 + 1) * (q n : ℤ) = t0 - (q n : ℤ) := by rw [hdecy]; ring
      rw [hEq, abs_of_nonpos (by omega)] at h
      omega
    set σ : ℤ := (N : ℤ) - M0 * (q n : ℤ) with hσ
    have hσeq : σ = (N : ℤ) - y + t0 := by rw [hσ]; omega
    have hNr1 : y - (s : ℤ) * (q (n - 1) : ℤ) + 1 ≤ (N : ℤ) := hNrange.1
    have hNr2 : (N : ℤ) ≤ y + (s : ℤ) * (q (n - 1) : ℤ) - 1 := hNrange.2
    have hσ1 : 1 ≤ σ := by rw [hσeq]; omega
    have hσlt : σ < (q n : ℤ) := by rw [hσeq]; omega
    have hNdec : (N : ℤ) = M0 * (q n : ℤ) + σ := by rw [hσ]; ring
    -- fracDist(N α) >= fracDist(σ α) - M0 Δ n
    have hdec2 : Work.TMC16Core.fracDist ((σ : ℝ) * α) - (M0 : ℝ) * Δ n ≤
        Work.TMC16Core.fracDist ((N : ℝ) * α) := by
      have hNcast : ((N : ℤ) : ℝ) = (σ : ℝ) + (M0 : ℝ) * (q n : ℝ) := by
        rw [hNdec]; push_cast; ring
      have h1 : (N : ℝ) * α = (σ : ℝ) * α + (M0 : ℝ) * ((q n : ℝ) * α) := by
        rw [show (N : ℝ) = ((N : ℤ) : ℝ) from by push_cast; ring, hNcast]; ring
      have h2 := Core.le_fracDist_add ((σ : ℝ) * α) ((M0 : ℝ) * ((q n : ℝ) * α))
      rw [← h1] at h2
      have h3 : Work.TMC16Core.fracDist ((M0 : ℝ) * ((q n : ℝ) * α)) ≤ (M0 : ℝ) * Δ n := by
        have h := Core.fracDist_zmul_le M0 ((q n : ℝ) * α)
        rw [← hΔeq n] at h
        rwa [abs_of_nonneg (by exact_mod_cast hM0nn)] at h
      linarith [h2, h3]
    -- M0 * Δ n <= (123/160)/qn
    have hM0le : (M0 : ℝ) ≤ ((y : ℝ) - (s : ℝ) * (q (n - 1) : ℝ)) / (q n : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hqpos n)]
      have hZ : (M0 : ℤ) * (q n : ℤ) ≤ y - (s : ℤ) * (q (n - 1) : ℤ) := by
        nlinarith [hdecy, ht0ge]
      exact_mod_cast hZ
    have hMD : (M0 : ℝ) * Δ n ≤ (123 / 160) / (q n : ℝ) := by
      have hDn0 : (0 : ℝ) ≤ Δ n := le_of_lt (hΔpos n)
      have hT0 : (0 : ℝ) ≤ (s : ℝ) * (q (n - 1) : ℝ) := by positivity
      have hmb : ((y : ℝ) - (s : ℝ) * (q (n - 1) : ℝ)) * Δ n ≤ 123 / 160 := by
        nlinarith [hyΔ, hDn0, hT0]
      have h1 : (M0 : ℝ) * Δ n ≤ (((y : ℝ) - (s : ℝ) * (q (n - 1) : ℝ)) / (q n : ℝ)) * Δ n :=
        mul_le_mul_of_nonneg_right hM0le hDn0
      rw [div_mul_eq_mul_div] at h1
      have h2 : ((y : ℝ) - (s : ℝ) * (q (n - 1) : ℝ)) * Δ n / (q n : ℝ) ≤
          (123 / 160) / (q n : ℝ) :=
        div_le_div_of_nonneg_right hmb (by exact_mod_cast (hqpos n).le)
      linarith [h1, h2]
    -- ================= two cases on σ =================
    rcases lt_or_ge σ ((q (n - 1) : ℤ)) with hσgt | hσL
    · -- Case σ < L : fracDist(σ α) ≥ 1/(2L)
      have hσnat' : ((σ.toNat : ℕ) : ℤ) = σ := Int.toNat_of_nonneg (by omega)
      have hσcastR : ((σ.toNat : ℕ) : ℝ) = (σ : ℝ) := by exact_mod_cast hσnat'
      have hwin : 1 / (2 * (q (n - 1) : ℝ)) ≤ Work.TMC16Core.fracDist ((σ : ℝ) * α) := by
        rw [← hσcastR]
        have hz : σ.toNat < q (n - 1) := by
          have h1 : ((σ.toNat : ℕ) : ℤ) < (q (n - 1) : ℤ) := by rw [hσnat']; exact hσgt
          omega
        by_cases h0 : q 0 ≤ σ.toNat
        · exact Core.fracDist_window_ge hqpos hmono hΔlo hbest h0 hz
        · push_neg at h0
          have hbk := Core.blk_sep_base hqpos hmono hΔpos hΔeq hΔup hΔlo hbest σ.toNat (by omega) h0
          have hqle : ((q 0 : ℕ) : ℝ) ≤ ((q (n - 1) : ℕ) : ℝ) := by
            exact_mod_cast (hmono.monotone (by omega : 0 ≤ n - 1))
          calc 1 / (2 * (q (n - 1) : ℝ)) ≤ 1 / (2 * (q 0 : ℝ)) := by
                apply one_div_le_one_div_of_le (by have := hqpos 0; positivity)
                linarith
            _ ≤ _ := hbk
      have hMD1 : (M0 : ℝ) * Δ n ≤ 1 / (q n : ℝ) := by
        have h2 : (123 / 160) / (q n : ℝ) ≤ 1 / (q n : ℝ) :=
          div_le_div_of_nonneg_right (by norm_num) (by exact_mod_cast (hqpos n).le)
        linarith [hMD, h2]
      have hLpos : (0 : ℝ) < (q (n - 1) : ℝ) := by exact_mod_cast hL
      have harith : 1 / (32 * (q n : ℝ)) ≤ 1 / (2 * (q (n - 1) : ℝ)) - (M0 : ℝ) * Δ n :=
        arithB2 (by exact_mod_cast hqpos n) hLpos h4Lle hMD1
      linarith [harith, hwin, hdec2]
    · -- Case σ ≥ L : fracDist(σ α) ≥ Δ(n-1)
      have hσnat' : ((σ.toNat : ℕ) : ℤ) = σ := Int.toNat_of_nonneg (by omega)
      have hσcastR : ((σ.toNat : ℕ) : ℝ) = (σ : ℝ) := by exact_mod_cast hσnat'
      have hbestσ : Δ (n - 1) ≤ Work.TMC16Core.fracDist ((σ : ℝ) * α) := by
        have h1 : q (n - 1) ≤ σ.toNat := by
          have hh : (q (n - 1) : ℤ) ≤ (σ.toNat : ℤ) := by rw [hσnat']; exact hσL
          omega
        have h2 : σ.toNat < q ((n - 1) + 1) := by
          rw [show n - 1 + 1 = n from by omega]
          have hh : ((σ.toNat : ℕ) : ℤ) < (q n : ℤ) := by rw [hσnat']; exact hσlt
          omega
        have := hbest (n - 1) σ.toNat h1 h2
        rwa [hσcastR] at this
      have hlo' : 1 / ((q n : ℝ) + (q (n - 1) : ℝ)) ≤ Δ (n - 1) := by
        have h := hΔlo (n - 1)
        rw [show n - 1 + 1 = n from by omega] at h
        exact le_of_lt h
      have harith : 1 / (32 * (q n : ℝ)) ≤ 1 / ((q n : ℝ) + (q (n - 1) : ℝ)) - (M0 : ℝ) * Δ n :=
        arithA2 (by exact_mod_cast hqpos n) (by exact_mod_cast (hqpos (n - 1)).le) h4Lle hMD
      linarith [harith, hlo', hbestσ, hdec2]

end Work.TMC16Core.NrFinal
