import Mathlib
import Submission.Work.GM.S3.Gen.cs_defs
import Submission.Work.GM.S3.Gen.exists_level

namespace Work.GM.S3.Gen

open Finset
open scoped BigOperators

noncomputable section

/-!
# Covering a triple of the truncation cube by its own dyadic cell

This file proves `Work.GM.S3.Gen.cs_cover`: for `N` large, every triple `u` with nonzero
coordinates, all coordinates of modulus `≤ Klev N δ`, and with the *second* coordinate of maximal
modulus (`|u₁| ≤ |u₂|`, `|u₃| ≤ |u₂|`), has its cell index `csGcell N δ u` in the family
`cellFam N δ (δ/2) (cellJ N δ)` and belongs to the corresponding cell `csCell`.

The mathematics is the standard dyadic covering of `(0, Klev]`:

* each coordinate `|u_i|` lies in `[1, Klev]`, hence in exactly one window
  `Mdy (csLev |u_i|) < |u_i| ≤ 2 Mdy (csLev |u_i|)` (and the level is `< cellJ`);
* since `csLev` is antitone in the coordinate, the second level is the smallest one
  (`j ≤ i`, `j ≤ k`);
* the window of the second coordinate gives `Mdy j ≥ |u₂|/2 ≥ 1/2`, whence
  `N · Bdy N δ (δ/2) j ≥ N/(4 (M N)^{δ/2}) = N^{1-3δ/5}/4 ≥ 32` for `N ≥ 128^{10}` (using
  `δ ≤ 3/2`);
* the windows themselves give the `idx1`/`idxM` memberships defining `csCell`.
-/

/-- The defining property of the level of a point `x ∈ (0, Klev]`: the window
`(Mdy (csLev x), 2 Mdy (csLev x)]` contains `x`. -/
theorem csLev_spec {N : ℕ} {δ : ℝ} (hN : 1 ≤ N) {x : ℝ} (hx : 0 < x)
    (hxK : x ≤ Klev N δ) :
    Mdy N δ (csLev N δ x) < x ∧ x ≤ 2 * Mdy N δ (csLev N δ x) := by
  have hKpos : 0 < Klev N δ := csKlev_pos hN δ
  have hKxpos : 0 < Klev N δ / x := div_pos hKpos hx
  set y := Real.logb 2 (Klev N δ / x) with hy
  have hyge : 0 ≤ y := by
    rw [hy]
    apply Real.logb_nonneg (by norm_num)
    rw [le_div_iff₀ hx]; linarith
  have hfloorle : (Nat.floor y : ℝ) ≤ y := Nat.floor_le hyge
  have hy_eq : (2:ℝ) ^ y = Klev N δ / x := by
    rw [hy]; exact Real.rpow_logb (by norm_num) (by norm_num) hKxpos
  have hL : csLev N δ x = Nat.floor y + 1 := by rw [csLev, hy]
  constructor
  · have hylt : y < (Nat.floor y : ℝ) + 1 := Nat.lt_floor_add_one y
    have hlt : (2:ℝ) ^ y < (2:ℝ) ^ ((Nat.floor y : ℝ) + 1) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) hylt
    rw [hy_eq] at hlt
    have hMain : Klev N δ < x * (2:ℝ) ^ (Nat.floor y + 1) := by
      have h1 : Klev N δ < x * (2:ℝ) ^ ((Nat.floor y : ℝ) + 1) :=
        lt_of_lt_of_eq ((div_lt_iff₀ hx).mp hlt) (mul_comm _ _)
      have h2 : (2:ℝ) ^ ((Nat.floor y : ℝ) + 1) = (2:ℝ) ^ (Nat.floor y + 1 : ℕ) := by
        rw [← Real.rpow_natCast (2:ℝ) (Nat.floor y + 1), Nat.cast_add, Nat.cast_one]
      rwa [h2] at h1
    show Klev N δ / (2:ℝ) ^ (csLev N δ x) < x
    rw [hL]
    exact (div_lt_iff₀ (by positivity : (0:ℝ) < (2:ℝ) ^ (Nat.floor y + 1))).mpr hMain
  · have h1 : (2:ℝ) ^ (Nat.floor y) ≤ Klev N δ / x := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hfloorle
      rwa [Real.rpow_natCast (2:ℝ) (Nat.floor y), hy_eq] at h
    have h2 : (2:ℝ) ^ (Nat.floor y) * x ≤ Klev N δ := by
      rwa [le_div_iff₀ hx] at h1
    have h3 : x ≤ Klev N δ / (2:ℝ) ^ (Nat.floor y) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ) ^ (Nat.floor y))]
      rw [mul_comm]; exact h2
    have h4 : 2 * Mdy N δ (csLev N δ x) = Klev N δ / (2:ℝ) ^ (Nat.floor y) := by
      rw [Mdy, hL, pow_succ]
      field_simp
    calc x ≤ Klev N δ / (2:ℝ) ^ (Nat.floor y) := h3
      _ = 2 * Mdy N δ (csLev N δ x) := h4.symm

/-- `csLev` is antitone in the coordinate: a larger coordinate has a smaller (or equal) level. -/
theorem csLev_mono {N : ℕ} {δ : ℝ} (hN : 1 ≤ N) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    csLev N δ y ≤ csLev N δ x := by
  have hK := csKlev_pos hN δ
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hKy : 0 < Klev N δ / y := div_pos hK hy
  have hKx : 0 < Klev N δ / x := div_pos hK hx
  have hdiv : Klev N δ / y ≤ Klev N δ / x :=
    div_le_div_of_nonneg_left (le_of_lt hK) hx hxy
  have hlog : Real.logb 2 (Klev N δ / y) ≤ Real.logb 2 (Klev N δ / x) :=
    (Real.logb_le_logb (by norm_num) hKy hKx).mpr hdiv
  simp only [csLev]
  exact Nat.add_le_add_right (Nat.floor_mono hlog) 1

/-- `Mdy` is antitone in the level. -/
theorem Mdy_anti {N : ℕ} {δ : ℝ} (hN : 1 ≤ N) {i j : ℕ} (hij : i ≤ j) :
    Mdy N δ j ≤ Mdy N δ i := by
  have hK := csKlev_pos hN δ
  have hpow : (2:ℝ) ^ i ≤ (2:ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hij
  simp only [Mdy]
  exact div_le_div_of_nonneg_left (le_of_lt hK) (by positivity) hpow

/-- One dyadic step of `Mdy` costs a factor two. -/
theorem two_mul_Mdy_le {N : ℕ} {δ : ℝ} (hN : 1 ≤ N) {i j : ℕ} (hij : i < j) :
    2 * Mdy N δ j ≤ Mdy N δ i := by
  have hK := csKlev_pos hN δ
  have hpow : (2:ℝ) ^ i ≤ (2:ℝ) ^ (j - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hjpow : (2:ℝ) ^ j = 2 * (2:ℝ) ^ (j - 1) := by
    conv_lhs => rw [show j = (j - 1) + 1 by omega]
    rw [pow_succ']
  rw [Mdy, Mdy, hjpow]
  rw [show 2 * (Klev N δ / (2 * (2:ℝ) ^ (j - 1))) = Klev N δ / (2:ℝ) ^ (j - 1) by field_simp]
  exact div_le_div_of_nonneg_left (le_of_lt hK) (by positivity) hpow

/-- The level is the *unique* index `j` whose window contains `x`. -/
theorem csLev_unique {N : ℕ} {δ : ℝ} (hN : 1 ≤ N) {x : ℝ} (hx : 0 < x)
    (hxK : x ≤ Klev N δ) {j : ℕ} (hj1 : Mdy N δ j < x) (hj2 : x ≤ 2 * Mdy N δ j) :
    csLev N δ x = j := by
  obtain ⟨h1, h2⟩ := csLev_spec hN hx hxK
  rcases lt_trichotomy (csLev N δ x) j with h | h | h
  · have key : 2 * Mdy N δ j ≤ Mdy N δ (csLev N δ x) := two_mul_Mdy_le hN h
    linarith
  · exact h
  · have key : 2 * Mdy N δ (csLev N δ x) ≤ Mdy N δ j := two_mul_Mdy_le hN h
    linarith

/-- Every level of a point of `[1, Klev]` is a valid index of the family (`< cellJ`). -/
theorem csLev_lt_cellJ {N : ℕ} {δ : ℝ} (hN : 1 ≤ N) (hδ : 0 < δ) {x : ℝ}
    (hx1 : 1 ≤ x) (hxK : x ≤ Klev N δ) : csLev N δ x < cellJ N δ := by
  obtain ⟨j, hj, hj1, hj2⟩ := exists_level N δ hδ hx1 hxK
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  rw [csLev_unique hN hx hxK hj1 hj2]
  exact hj

/-- **The covering lemma.**  A triple of the truncation cube whose second coordinate is maximal
belongs to the cell of its own dyadic levels, which is a cell of `cellFam`. -/
theorem cs_cover :
    ∀ δ : ℝ, 0 < δ → δ ≤ 3 / 2 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ u : ℤ × ℤ × ℤ,
      u.1 ≠ 0 → u.2.1 ≠ 0 → u.2.2 ≠ 0 →
      |(u.1 : ℝ)| ≤ Work.GM.S3.Gen.Klev N δ → |(u.2.1 : ℝ)| ≤ Work.GM.S3.Gen.Klev N δ →
      |(u.2.2 : ℝ)| ≤ Work.GM.S3.Gen.Klev N δ →
      |(u.1 : ℝ)| ≤ |(u.2.1 : ℝ)| → |(u.2.2 : ℝ)| ≤ |(u.2.1 : ℝ)| →
      Work.GM.S3.Gen.csGcell N δ u ∈
          Work.GM.S3.Gen.cellFam N δ (δ / 2) (Work.GM.S3.Gen.cellJ N δ) ∧
        u ∈ Work.GM.S3.Gen.csCell N δ (Work.GM.S3.Gen.csGcell N δ u).1
          (Work.GM.S3.Gen.csGcell N δ u).2.1 (Work.GM.S3.Gen.csGcell N δ u).2.2 := by
  intro δ hδ hδ32
  refine ⟨128 ^ 10, ?_⟩
  intro N hN u hu1 hu2 hu3 hb1 hb2 hb3 hle1 hle3
  have hN1 : 1 ≤ N := le_trans (by norm_num : 1 ≤ 128 ^ 10) hN
  -- each coordinate has modulus `≥ 1`
  have hge1 : (1:ℝ) ≤ |(u.1 : ℝ)| := by
    have h := Int.one_le_abs hu1
    have h' : ((1:ℤ):ℝ) ≤ ((|u.1| : ℤ) : ℝ) := by exact_mod_cast h
    rwa [Int.cast_abs, Int.cast_one] at h'
  have hge2 : (1:ℝ) ≤ |(u.2.1 : ℝ)| := by
    have h := Int.one_le_abs hu2
    have h' : ((1:ℤ):ℝ) ≤ ((|u.2.1| : ℤ) : ℝ) := by exact_mod_cast h
    rwa [Int.cast_abs, Int.cast_one] at h'
  have hge3 : (1:ℝ) ≤ |(u.2.2 : ℝ)| := by
    have h := Int.one_le_abs hu3
    have h' : ((1:ℤ):ℝ) ≤ ((|u.2.2| : ℤ) : ℝ) := by exact_mod_cast h
    rwa [Int.cast_abs, Int.cast_one] at h'
  have hx1pos : 0 < |(u.1 : ℝ)| := lt_of_lt_of_le zero_lt_one hge1
  have hx2pos : 0 < |(u.2.1 : ℝ)| := lt_of_lt_of_le zero_lt_one hge2
  have hx3pos : 0 < |(u.2.2 : ℝ)| := lt_of_lt_of_le zero_lt_one hge3
  -- the dyadic window of each coordinate
  have hspec1 : Mdy N δ (csLev N δ |(u.1 : ℝ)|) < |(u.1 : ℝ)| ∧
      |(u.1 : ℝ)| ≤ 2 * Mdy N δ (csLev N δ |(u.1 : ℝ)|) := csLev_spec hN1 hx1pos hb1
  have hspec2 : Mdy N δ (csLev N δ |(u.2.1 : ℝ)|) < |(u.2.1 : ℝ)| ∧
      |(u.2.1 : ℝ)| ≤ 2 * Mdy N δ (csLev N δ |(u.2.1 : ℝ)|) := csLev_spec hN1 hx2pos hb2
  have hspec3 : Mdy N δ (csLev N δ |(u.2.2 : ℝ)|) < |(u.2.2 : ℝ)| ∧
      |(u.2.2 : ℝ)| ≤ 2 * Mdy N δ (csLev N δ |(u.2.2 : ℝ)|) := csLev_spec hN1 hx3pos hb3
  change (csLev N δ |(u.1 : ℝ)|, (csLev N δ |(u.2.1 : ℝ)|, csLev N δ |(u.2.2 : ℝ)|)) ∈
      cellFam N δ (δ / 2) (cellJ N δ) ∧
    u ∈ csCell N δ (csLev N δ |(u.1 : ℝ)|) (csLev N δ |(u.2.1 : ℝ)|) (csLev N δ |(u.2.2 : ℝ)|)
  set i := csLev N δ |(u.1 : ℝ)| with hi
  set j := csLev N δ |(u.2.1 : ℝ)| with hj
  set k := csLev N δ |(u.2.2 : ℝ)| with hk
  have hs1 : Mdy N δ i < |(u.1 : ℝ)| ∧ |(u.1 : ℝ)| ≤ 2 * Mdy N δ i := by rw [hi]; exact hspec1
  have hs2 : Mdy N δ j < |(u.2.1 : ℝ)| ∧ |(u.2.1 : ℝ)| ≤ 2 * Mdy N δ j := by rw [hj]; exact hspec2
  have hs3 : Mdy N δ k < |(u.2.2 : ℝ)| ∧ |(u.2.2 : ℝ)| ≤ 2 * Mdy N δ k := by rw [hk]; exact hspec3
  have hiJ : i < cellJ N δ := by rw [hi]; exact csLev_lt_cellJ hN1 hδ hge1 hb1
  have hjJ : j < cellJ N δ := by rw [hj]; exact csLev_lt_cellJ hN1 hδ hge2 hb2
  have hkJ : k < cellJ N δ := by rw [hk]; exact csLev_lt_cellJ hN1 hδ hge3 hb3
  have hji : j ≤ i := by rw [hi, hj]; exact csLev_mono hN1 hx1pos hle1
  have hjk : j ≤ k := by rw [hk, hj]; exact csLev_mono hN1 hx3pos hle3
  -- the smoothing condition of `cellFam`
  have hroot : (128:ℝ) ≤ (N:ℝ) ^ (1 / 10 : ℝ) := by
    have hNR : (128:ℝ) ^ 10 ≤ (N:ℝ) := by
      have h' : ((128 ^ 10 : ℕ) : ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
      rwa [Nat.cast_pow, Nat.cast_ofNat] at h'
    have h1 : (((128:ℝ) ^ 10) ^ (1 / 10 : ℝ)) ≤ (N:ℝ) ^ (1 / 10 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hNR (by norm_num)
    have h2 : (((128:ℝ) ^ 10) ^ (1 / 10 : ℝ)) = (128:ℝ) := by
      rw [← Real.rpow_natCast (128:ℝ) 10, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 128)]
      rw [show ((10:ℕ):ℝ) * (1 / 10) = 1 by norm_num, Real.rpow_one]
    rwa [h2] at h1
  have hexp : (1:ℝ) / 10 ≤ 1 - 3 * δ / 5 := by linarith
  have hmono : (N:ℝ) ^ (1 / 10 : ℝ) ≤ (N:ℝ) ^ (1 - 3 * δ / 5) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1 : (1:ℝ) ≤ N) hexp
  have hfin : 32 ≤ (1:ℝ) / 4 * (N:ℝ) ^ (1 - 3 * δ / 5) := by
    nlinarith [hroot, hmono]
  have hMN : (Submission.LargeValues.M N) ^ (δ / 2) = (N:ℝ) ^ (3 * δ / 5) := by
    rw [Submission.LargeValues.M, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ N)]
    congr 1
    ring
  have hred : (N:ℝ) / (4 * (Submission.LargeValues.M N) ^ (δ / 2)) =
      (1:ℝ) / 4 * (N:ℝ) ^ (1 - 3 * δ / 5) := by
    rw [hMN, Real.rpow_sub (by positivity : (0:ℝ) < N) 1 (3 * δ / 5), Real.rpow_one]
    field_simp
  have hkey2 : (N:ℝ) / (4 * (Submission.LargeValues.M N) ^ (δ / 2)) ≤
      (N:ℝ) * Bdy N δ (δ / 2) j := by
    have hMdy_lb : (1:ℝ) / 2 ≤ Mdy N δ j := by linarith [hge2, hs2.2]
    rw [Bdy, ← mul_div_assoc]
    rw [show (N:ℝ) / (4 * (Submission.LargeValues.M N) ^ (δ / 2)) =
        (N:ℝ) * ((1:ℝ) / 2) / (2 * (Submission.LargeValues.M N) ^ (δ / 2)) by ring]
    have hden : (0:ℝ) ≤ 2 * (Submission.LargeValues.M N) ^ (δ / 2) := by
      have hX : (0:ℝ) < (Submission.LargeValues.M N) ^ (δ / 2) :=
        Real.rpow_pos_of_pos (Submission.LargeValues.M_pos hN1) _
      linarith
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hMdy_lb (by positivity)) hden
  have hBdy : 32 ≤ (N:ℝ) * Bdy N δ (δ / 2) j := by
    have h := hkey2
    rw [hred] at h
    linarith [hfin, h]
  refine ⟨?_, ?_⟩
  · rw [cellFam]
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [Finset.mem_product, Finset.mem_product, Finset.mem_range, Finset.mem_range,
        Finset.mem_range]
      exact ⟨hiJ, hjJ, hkJ⟩
    · exact ⟨hji, hjk, hBdy⟩
  · rw [mem_csCell]
    refine ⟨?_, ?_, ?_⟩
    · rw [idx1, Finset.mem_filter]
      refine ⟨Finset.mem_Icc.mpr (abs_le.mp ?_), hs1.1⟩
      rw [Int.le_floor, Int.cast_abs]
      exact hs1.2
    · rw [idxM, Finset.mem_filter]
      refine ⟨Finset.mem_Icc.mpr (abs_le.mp ?_), hs2.1⟩
      rw [Int.le_floor, Int.cast_abs]
      exact hs2.2
    · rw [idxM, Finset.mem_filter]
      refine ⟨Finset.mem_Icc.mpr (abs_le.mp ?_), hs3.1⟩
      rw [Int.le_floor, Int.cast_abs]
      exact hs3.2

end

end Work.GM.S3.Gen
