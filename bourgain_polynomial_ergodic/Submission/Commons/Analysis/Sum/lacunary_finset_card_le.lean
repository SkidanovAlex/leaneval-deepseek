import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.Sum

open Finset

/-- Auxiliary logarithm estimate: if `0 < u`, `1 < c` and `c * u ≤ v`, then
`log (u / a) + log c ≤ log (v / a)` for any `a > 0`. -/
private lemma log_div_gap {a c u v : ℝ} (ha : 0 < a) (hc : 1 < c)
    (hu : 0 < u) (huv : c * u ≤ v) :
    Real.log (u / a) + Real.log c ≤ Real.log (v / a) := by
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have huapos : 0 < u / a := div_pos hu ha
  have hvpos : 0 < v := lt_of_lt_of_le (mul_pos hcpos hu) huv
  have hvapos : 0 < v / a := div_pos hvpos ha
  have huv' : u * c ≤ v := by nlinarith [huv]
  have h1 : u / a * c ≤ v / a := by
    have : u / a * c = u * c / a := by ring
    rw [this]
    exact div_le_div_of_nonneg_right huv' ha.le
  have h2 : Real.log (u / a * c) ≤ Real.log (v / a) :=
    Real.log_le_log (mul_pos huapos hcpos) h1
  rwa [Real.log_mul (ne_of_gt huapos) (ne_of_gt hcpos)] at h2

/-- A lacunary counting estimate: a finite set `s` of positive reals contained in
`[a, b]` such that any two distinct elements satisfy `c * x ≤ y` whenever `x < y`
has at most `log (b / a) / log c + 1` elements, for `a > 0` and `c > 1`.

The proof maps `x` to `⌊log (x / a) / log c⌋₊`: this map is injective on `s`
(because a multiplicative gap of `c` gives an additive gap of `1` after taking
logarithms) and takes values in `{0, …, ⌊log (b / a) / log c⌋}`. -/
lemma card_le_of_mul_gap {s : Finset ℝ} {a b c : ℝ}
    (ha : 0 < a) (hb : a ≤ b) (hc : 1 < c)
    (hbound : ∀ x ∈ s, a ≤ x ∧ x ≤ b)
    (hgap : ∀ x ∈ s, ∀ y ∈ s, x < y → c * x ≤ y) :
    (s.card : ℝ) ≤ Real.log (b / a) / Real.log c + 1 := by
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hlcpos : 0 < Real.log c := Real.log_pos hc
  have hba1 : 1 ≤ b / a := (one_le_div ha).mpr hb
  have hlbanonneg : 0 ≤ Real.log (b / a) := Real.log_nonneg hba1
  have hratio : 0 ≤ Real.log (b / a) / Real.log c := div_nonneg hlbanonneg hlcpos.le
  let f : ℝ → ℕ := fun x => ⌊Real.log (x / a) / Real.log c⌋₊
  have hpos_of_mem : ∀ x ∈ s, 0 < x := fun x hx => lt_of_lt_of_le ha (hbound x hx).1
  have hxa1 : ∀ x ∈ s, 1 ≤ x / a := fun x hx => (one_le_div ha).mpr (hbound x hx).1
  have hlog_nonneg : ∀ x ∈ s, 0 ≤ Real.log (x / a) / Real.log c := by
    intro x hx
    exact div_nonneg (Real.log_nonneg (hxa1 x hx)) hlcpos.le
  have hmem : ∀ x ∈ s, f x ∈ Finset.range (⌊Real.log (b / a) / Real.log c⌋₊ + 1) := by
    intro x hx
    rw [Finset.mem_range]
    have hle1 : x / a ≤ b / a := div_le_div_of_nonneg_right (hbound x hx).2 ha.le
    have hposxa : 0 < x / a := lt_of_lt_of_le zero_lt_one (hxa1 x hx)
    have hlev : Real.log (x / a) / Real.log c ≤ Real.log (b / a) / Real.log c :=
      div_le_div_of_nonneg_right (Real.log_le_log hposxa hle1) hlcpos.le
    show f x < _
    simp only [f]
    exact lt_of_le_of_lt (Nat.floor_mono hlev) (Nat.lt_succ_self _)
  have hinj : Set.InjOn f ↑s := by
    intro x hx y hy hxy
    rcases lt_trichotomy x y with hlt | heq | hgt
    · exfalso
      have hcx : c * x ≤ y := hgap x hx y hy hlt
      have hloggap := log_div_gap ha hc (hpos_of_mem x hx) hcx
      have hfx : (f x : ℝ) ≤ Real.log (x / a) / Real.log c := by
        simp only [f]; exact Nat.floor_le (hlog_nonneg x hx)
      have hvx : (f x : ℝ) + 1 ≤ Real.log (y / a) / Real.log c := by
        have h2 : Real.log (x / a) / Real.log c + 1
            = (Real.log (x / a) + Real.log c) / Real.log c := by field_simp
        calc (f x : ℝ) + 1 ≤ Real.log (x / a) / Real.log c + 1 := by linarith [hfx]
          _ = (Real.log (x / a) + Real.log c) / Real.log c := h2
          _ ≤ Real.log (y / a) / Real.log c := div_le_div_of_nonneg_right hloggap hlcpos.le
      have hstep : f x + 1 ≤ f y := by
        show f x + 1 ≤ ⌊Real.log (y / a) / Real.log c⌋₊
        apply Nat.le_floor
        push_cast
        exact hvx
      omega
    · exact heq
    · exfalso
      have hcy : c * y ≤ x := hgap y hy x hx hgt
      have hloggap := log_div_gap ha hc (hpos_of_mem y hy) hcy
      have hfy : (f y : ℝ) ≤ Real.log (y / a) / Real.log c := by
        simp only [f]; exact Nat.floor_le (hlog_nonneg y hy)
      have hvy : (f y : ℝ) + 1 ≤ Real.log (x / a) / Real.log c := by
        have h2 : Real.log (y / a) / Real.log c + 1
            = (Real.log (y / a) + Real.log c) / Real.log c := by field_simp
        calc (f y : ℝ) + 1 ≤ Real.log (y / a) / Real.log c + 1 := by linarith [hfy]
          _ = (Real.log (y / a) + Real.log c) / Real.log c := h2
          _ ≤ Real.log (x / a) / Real.log c := div_le_div_of_nonneg_right hloggap hlcpos.le
      have hstep : f y + 1 ≤ f x := by
        show f y + 1 ≤ ⌊Real.log (x / a) / Real.log c⌋₊
        apply Nat.le_floor
        push_cast
        exact hvy
      omega
  have hcard_eq : (s.image f).card = s.card := Finset.card_image_of_injOn hinj
  have hsub : s.image f ⊆ Finset.range (⌊Real.log (b / a) / Real.log c⌋₊ + 1) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hmem y hy
  have hcard_le : s.card ≤ ⌊Real.log (b / a) / Real.log c⌋₊ + 1 := by
    rw [← hcard_eq]
    simpa using Finset.card_le_card hsub
  have hfloor : (⌊Real.log (b / a) / Real.log c⌋₊ : ℝ) ≤ Real.log (b / a) / Real.log c :=
    Nat.floor_le hratio
  calc (s.card : ℝ) ≤ ((⌊Real.log (b / a) / Real.log c⌋₊ + 1 : ℕ) : ℝ) := by
        exact_mod_cast hcard_le
    _ = (⌊Real.log (b / a) / Real.log c⌋₊ : ℝ) + 1 := by push_cast; ring
    _ ≤ Real.log (b / a) / Real.log c + 1 := by linarith

/-- In a finite lacunary set `D` of positive reals (any two elements differ by a factor
at least `Λ > 1`), the number of `N ∈ D` with `X < A * N ^ d ≤ Y` is at most
`log (Y / X) / log (Λ ^ d) + 1`. -/
theorem lacunary_finset_card_le
    {Λ : ℝ} (hΛ : 1 < Λ) (d : ℕ) (hd : 1 ≤ d) (A : ℝ) (hA : 0 < A)
    (D : Finset ℝ) (hpos : ∀ N ∈ D, 0 < N)
    (hlac : ∀ M ∈ D, ∀ N ∈ D, M < N → Λ * M ≤ N)
    (X Y : ℝ) (hX : 0 < X) (hXY : X < Y) :
    ((D.filter (fun N => X < A * N ^ d ∧ A * N ^ d ≤ Y)).card : ℝ)
      ≤ Real.log (Y / X) / Real.log (Λ ^ d) + 1 := by
  have hd_ne : d ≠ 0 := by omega
  have hΛpos : 0 < Λ := lt_trans zero_lt_one hΛ
  have hcd : 1 < Λ ^ d := one_lt_pow₀ hΛ hd_ne
  set S : Finset ℝ := D.filter (fun N => X < A * N ^ d ∧ A * N ^ d ≤ Y) with hS
  set s : Finset ℝ := S.image (fun N => A * N ^ d) with hs
  have hSD : ∀ N ∈ S, N ∈ D := by
    intro N hN; rw [hS, Finset.mem_filter] at hN; exact hN.1
  have hinj : Set.InjOn (fun N => A * N ^ d) ↑S := by
    intro M hM N hN hMN
    have hMpos : 0 < M := hpos M (hSD M hM)
    have hNpos : 0 < N := hpos N (hSD N hN)
    have hpow : M ^ d = N ^ d := mul_left_cancel₀ (ne_of_gt hA) hMN
    exact (pow_left_strictMonoOn₀ hd_ne).injOn (le_of_lt hMpos) (le_of_lt hNpos) hpow
  have hcard_s : s.card = S.card := by
    rw [hs]; exact Finset.card_image_of_injOn hinj
  have hbound : ∀ x ∈ s, X ≤ x ∧ x ≤ Y := by
    intro x hx
    rw [hs, Finset.mem_image] at hx
    obtain ⟨N, hN, rfl⟩ := hx
    rw [hS, Finset.mem_filter] at hN
    exact ⟨le_of_lt hN.2.1, hN.2.2⟩
  have hgap : ∀ x ∈ s, ∀ y ∈ s, x < y → (Λ ^ d) * x ≤ y := by
    intro x hx y hy hxy
    rw [hs, Finset.mem_image] at hx hy
    obtain ⟨M, hM, rfl⟩ := hx
    obtain ⟨N, hN, rfl⟩ := hy
    rw [hS, Finset.mem_filter] at hM hN
    have hMD : M ∈ D := hM.1
    have hND : N ∈ D := hN.1
    have hMpos : 0 < M := hpos M hMD
    have hNpos : 0 < N := hpos N hND
    have hMN : M < N := by
      rcases lt_or_ge M N with h | h
      · exact h
      · exfalso
        have hle : N ^ d ≤ M ^ d := pow_le_pow_left₀ (le_of_lt hNpos) h d
        have hle' : A * N ^ d ≤ A * M ^ d := mul_le_mul_of_nonneg_left hle (le_of_lt hA)
        linarith [hxy]
    have hlac' : Λ * M ≤ N := hlac M hMD N hND hMN
    have hpowle : (Λ * M) ^ d ≤ N ^ d :=
      pow_le_pow_left₀ (le_of_lt (mul_pos hΛpos hMpos)) hlac' d
    have h1 : Λ ^ d * M ^ d ≤ N ^ d := by
      calc Λ ^ d * M ^ d = (Λ * M) ^ d := by rw [mul_pow]
        _ ≤ N ^ d := hpowle
    calc Λ ^ d * (A * M ^ d) = A * (Λ ^ d * M ^ d) := by ring
      _ ≤ A * N ^ d := mul_le_mul_of_nonneg_left h1 (le_of_lt hA)
  have hmain := card_le_of_mul_gap (s := s) hX (le_of_lt hXY) hcd hbound hgap
  rw [hcard_s] at hmain
  exact hmain

end Commons.Analysis.Sum