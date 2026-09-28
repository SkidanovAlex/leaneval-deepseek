import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.Sig2.num_lattices_of
import Submission.Work.HP.minkowski_upper
import Submission.Work.HP.ballCount_le_pow_rk
import Submission.Work.HP.Sig2.schmidt_bound
import Submission.Work.HP.kwin_spec
import Submission.Work.HP.prim_lat_window_finite
import Submission.Work.HP.MDEstimates.rpow_shell_sum
import Submission.Work.HP.MDEstimates.rpow_caseB_sum
import Submission.Work.HP.MDEstimates.log_pow_factor
import Submission.Work.Q44Geom.Basic
import Submission.Work.Q44Geom.good_count
import Submission.Work.Q44Geom.bad_count

set_option autoImplicit false
noncomputable section
open Finset

namespace Work.HP.MDEstimates

/-! ## Dyadic windows -/

/-- The dyadic window exponents `(⌈log₂ λ₁⌉, ⌈log₂ λ₂⌉, ⌈log₂ λ₃⌉)` of a lattice. -/
def widx (L : Submodule ℤ (Fin 5 → ℤ)) : ℕ × ℕ × ℕ :=
  (kwin 3 L 0, kwin 3 L 1, kwin 3 L 2)

/-- The triple `(k₀,k₁,k₂)` read as a function on `Fin 3`. -/
def kfun (k : ℕ × ℕ × ℕ) : Fin 3 → ℕ := ![k.1, k.2.1, k.2.2]

/-- `2 ^ (k₀+k₁+k₂)`, the dyadic volume of a window. -/
def wpow (k : ℕ × ℕ × ℕ) : ℝ := (2:ℝ)^k.1 * (2:ℝ)^k.2.1 * (2:ℝ)^k.2.2

/-- `2 ^ (k₀+k₁)`. -/
def wpow2 (k : ℕ × ℕ × ℕ) : ℝ := (2:ℝ)^k.1 * (2:ℝ)^k.2.1

/-- Monotonicity of a product of three nonnegative factors. -/
lemma prod_fin_three_mono {f g : Fin 3 → ℝ} (h0 : 0 ≤ f 0) (h1 : 0 ≤ f 1) (h2 : 0 ≤ f 2)
    (hg0 : 0 ≤ g 0) (hg1 : 0 ≤ g 1) (hg2 : 0 ≤ g 2)
    (e0 : f 0 ≤ g 0) (e1 : f 1 ≤ g 1) (e2 : f 2 ≤ g 2) :
    (∏ j : Fin 3, f j) ≤ ∏ j : Fin 3, g j := by
  rw [Fin.prod_univ_three, Fin.prod_univ_three]
  exact mul_le_mul (mul_le_mul e0 e1 h1 hg0) e2 h2 (mul_nonneg hg0 hg1)

lemma kwin_eq_kfun {L : Submodule ℤ (Fin 5 → ℤ)} {k : ℕ × ℕ × ℕ} (h : widx L = k) (j : Fin 3) :
    kwin 3 L j = kfun k j := by
  rw [← h]
  fin_cases j <;> rfl

lemma wpow_eq_prod (k : ℕ × ℕ × ℕ) : wpow k = ∏ j : Fin 3, (2:ℝ)^(kfun k j) := by
  simp [wpow, kfun, Fin.prod_univ_three]

lemma wpow_eq_two (k : ℕ × ℕ × ℕ) : wpow k = (2:ℝ)^(k.1 + k.2.1 + k.2.2) := by
  simp only [wpow]
  rw [← pow_add, ← pow_add]

lemma wpow2_eq_two (k : ℕ × ℕ × ℕ) : wpow2 k = (2:ℝ)^(k.1 + k.2.1) := by
  simp only [wpow2]
  rw [← pow_add]

lemma wpow_widx (L : Submodule ℤ (Fin 5 → ℤ)) :
    wpow (widx L) = ∏ j : Fin 3, (2:ℝ)^(kwin 3 L j) := by
  rw [wpow_eq_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [← kwin_eq_kfun (h := rfl) j]

lemma wpow2_widx (L : Submodule ℤ (Fin 5 → ℤ)) :
    wpow2 (widx L) = (2:ℝ)^(kwin 3 L 0) * (2:ℝ)^(kwin 3 L 1) := rfl

lemma wpow_pos (k : ℕ × ℕ × ℕ) : 0 < wpow k := by
  rw [wpow]; positivity

lemma wpow2_pos (k : ℕ × ℕ × ℕ) : 0 < wpow2 k := by
  rw [wpow2]; positivity

lemma wpow_split (k : ℕ × ℕ × ℕ) : wpow k = wpow2 k * (2:ℝ)^k.2.2 := rfl

lemma wpow_rpow_three (k : ℕ × ℕ × ℕ) :
    (wpow k) ^ ((3:ℝ)/2) = (2:ℝ)^(((3:ℝ)/2) * ((k.1 + k.2.1 + k.2.2 : ℕ) : ℝ)) := by
  rw [wpow_eq_two, ← Real.rpow_natCast (2:ℝ) (k.1 + k.2.1 + k.2.2),
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

lemma rpow_combine_A {ρ a c : ℝ} (hρ : 0 < ρ) :
    c * ρ ^ ((7:ℝ)/2) * (a / ρ)^2 = (c * a^2) * ρ ^ ((3:ℝ)/2) := by
  have h1 : (a / ρ)^2 = a^2 * ρ ^ (-(2:ℝ)) := by
    have hρ2 : ρ ^ (-(2:ℝ)) = (ρ * ρ)⁻¹ := by
      rw [show (-(2:ℝ)) = (-(1:ℝ)) + (-(1:ℝ)) by norm_num, Real.rpow_add hρ,
        Real.rpow_neg hρ.le 1, Real.rpow_one]
      ring
    rw [hρ2]
    ring
  rw [h1, show ((3:ℝ)/2) = ((7:ℝ)/2) + (-(2:ℝ)) by norm_num, Real.rpow_add hρ]
  ring

lemma rpow_combine_B {q t a c : ℝ} (hq : 0 < q) (ht : 0 < t) :
    c * (q * t) ^ ((7:ℝ)/2) * (a / q)^2 = (c * a^2) * q ^ ((3:ℝ)/2) * t ^ ((7:ℝ)/2) := by
  rw [Real.mul_rpow hq.le ht.le]
  have h1 : (a / q)^2 = a^2 * q ^ (-(2:ℝ)) := by
    have hq2 : q ^ (-(2:ℝ)) = (q * q)⁻¹ := by
      rw [show (-(2:ℝ)) = (-(1:ℝ)) + (-(1:ℝ)) by norm_num, Real.rpow_add hq,
        Real.rpow_neg hq.le 1, Real.rpow_one]
      ring
    rw [hq2]
    ring
  rw [h1, show ((3:ℝ)/2) = ((7:ℝ)/2) + (-(2:ℝ)) by norm_num, Real.rpow_add hq]
  ring

/-! ## The two pointwise bounds for the ball count -/

lemma ballCount_le_winA (L : Submodule ℤ (Fin 5 → ℤ)) (Ks Z : ℝ) (hKs1 : 0 ≤ Ks)
    (hKs : ∀ T : ℝ, 1 ≤ T →
      (ballCount L T : ℝ) ≤ Ks * ∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1))
    (hZ : 1 ≤ Z) (hrk : rk L = 3) (h1 : lam L 1 ≤ Z) (h2 : lam L 2 ≤ Z) (h3 : lam L 3 ≤ Z) :
    (ballCount L Z : ℝ) ≤ 512 * Ks * Z ^ 3 / wpow (widx L) := by
  have hsch := hKs Z hZ
  obtain ⟨-, hkB, -, -⟩ := kwin_spec (Fin 5) 3 L (by norm_num) hrk
  have hfac : ∀ j : Fin 3, Z / lam L (j.1 + 1) + 1 ≤ 4 * Z / (2:ℝ)^(kwin 3 L j) := by
    intro j
    have htj : (2:ℝ)^(kwin 3 L j) ≤ 2 * lam L (j.1 + 1) := hkB j
    have hlampos : 0 < lam L (j.1 + 1) := lam_pos L (by omega) (by rw [hrk]; exact j.2)
    have hlamZ : lam L (j.1 + 1) ≤ Z := by
      fin_cases j
      · simpa using h1
      · simpa using h2
      · simpa using h3
    have hden : 0 < (2:ℝ)^(kwin 3 L j) := pow_pos (by norm_num) _
    have hid : Z / lam L (j.1 + 1) + 1 = (Z + lam L (j.1 + 1)) / lam L (j.1 + 1) :=
      div_add_one (ne_of_gt hlampos)
    have key : (Z + lam L (j.1 + 1)) * (2:ℝ)^(kwin 3 L j) ≤ 4 * Z * lam L (j.1 + 1) := by
      nlinarith [htj, hlamZ, hlampos]
    calc Z / lam L (j.1 + 1) + 1 = (Z + lam L (j.1 + 1)) / lam L (j.1 + 1) := hid
      _ ≤ 4 * Z / (2:ℝ)^(kwin 3 L j) := (div_le_div_iff₀ hlampos hden).mpr key
  have hposj : ∀ j : Fin 3, 0 ≤ Z / lam L (j.1 + 1) + 1 := by
    intro j
    have hlampos : 0 < lam L (j.1 + 1) := lam_pos L (by omega) (by rw [hrk]; exact j.2)
    have h1' : 0 ≤ Z / lam L (j.1 + 1) := div_nonneg (le_trans zero_le_one hZ) hlampos.le
    linarith
  have hposk : ∀ j : Fin 3, 0 ≤ 4 * Z / (2:ℝ)^(kwin 3 L j) := by
    intro j
    exact div_nonneg (by linarith) (pow_pos (by norm_num) _).le
  have hprodle : (∏ j : Fin 3, (Z / lam L (j.1 + 1) + 1))
      ≤ ∏ j : Fin 3, (4 * Z / (2:ℝ)^(kwin 3 L j)) :=
    prod_fin_three_mono (hposj 0) (hposj 1) (hposj 2)
      (hposk 0) (hposk 1) (hposk 2) (hfac 0) (hfac 1) (hfac 2)
  have hprodeq : (∏ j : Fin 3, (4 * Z / (2:ℝ)^(kwin 3 L j))) = 64 * Z^3 / wpow (widx L) := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← wpow_widx L]
    ring
  have hprod : (∏ i ∈ Finset.range (rk L), (Z / lam L (i + 1) + 1))
      = ∏ j : Fin 3, (Z / lam L (j.1 + 1) + 1) := by
    rw [hrk]
    exact (Fin.prod_univ_eq_prod_range (fun i => Z / lam L (i + 1) + 1) 3).symm
  have hρpos : 0 < wpow (widx L) := wpow_pos _
  have hkey : Ks * (64 * Z^3 / wpow (widx L)) ≤ 512 * Ks * Z^3 / wpow (widx L) := by
    have h1 : Ks * (64 * Z^3) ≤ 512 * Ks * Z^3 := by
      nlinarith [mul_nonneg hKs1 (by positivity : (0:ℝ) ≤ Z^3)]
    have h2 : Ks * (64 * Z^3) / wpow (widx L) ≤ 512 * Ks * Z^3 / wpow (widx L) := by
      rw [div_le_div_iff₀ hρpos hρpos]
      exact mul_le_mul_of_nonneg_right h1 hρpos.le
    calc Ks * (64 * Z^3 / wpow (widx L)) = Ks * (64 * Z^3) / wpow (widx L) := by ring
      _ ≤ 512 * Ks * Z^3 / wpow (widx L) := h2
  calc (ballCount L Z : ℝ) ≤ Ks * ∏ i ∈ Finset.range (rk L), (Z / lam L (i + 1) + 1) := hsch
    _ = Ks * ∏ j : Fin 3, (Z / lam L (j.1 + 1) + 1) := by rw [hprod]
    _ ≤ Ks * (64 * Z^3 / wpow (widx L)) :=
        mul_le_mul_of_nonneg_left (hprodle.trans (le_of_eq hprodeq)) hKs1
    _ ≤ 512 * Ks * Z^3 / wpow (widx L) := hkey

lemma ballCount_le_winB (L : Submodule ℤ (Fin 5 → ℤ)) (Ks Z : ℝ) (hKs1 : 0 ≤ Ks)
    (hKs : ∀ T : ℝ, 1 ≤ T →
      (ballCount L T : ℝ) ≤ Ks * ∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1))
    (hZ : 1 ≤ Z) (hrk : rk L = 3) (h1 : lam L 1 ≤ Z) (h2 : lam L 2 ≤ Z) (h3 : Z < lam L 3) :
    (ballCount L Z : ℝ) ≤ 256 * Ks * Z ^ 2 / wpow2 (widx L) := by
  have hsch := hKs Z hZ
  obtain ⟨-, hkB, -, -⟩ := kwin_spec (Fin 5) 3 L (by norm_num) hrk
  have hfac : ∀ j : Fin 3, j ≠ 2 → Z / lam L (j.1 + 1) + 1 ≤ 4 * Z / (2:ℝ)^(kwin 3 L j) := by
    intro j hj
    have htj : (2:ℝ)^(kwin 3 L j) ≤ 2 * lam L (j.1 + 1) := hkB j
    have hlampos : 0 < lam L (j.1 + 1) := lam_pos L (by omega) (by rw [hrk]; exact j.2)
    have hlamZ : lam L (j.1 + 1) ≤ Z := by
      fin_cases j
      · simpa using h1
      · simpa using h2
      · exact absurd rfl hj
    have hden : 0 < (2:ℝ)^(kwin 3 L j) := pow_pos (by norm_num) _
    have hid : Z / lam L (j.1 + 1) + 1 = (Z + lam L (j.1 + 1)) / lam L (j.1 + 1) :=
      div_add_one (ne_of_gt hlampos)
    have key : (Z + lam L (j.1 + 1)) * (2:ℝ)^(kwin 3 L j) ≤ 4 * Z * lam L (j.1 + 1) := by
      nlinarith [htj, hlamZ, hlampos]
    calc Z / lam L (j.1 + 1) + 1 = (Z + lam L (j.1 + 1)) / lam L (j.1 + 1) := hid
      _ ≤ 4 * Z / (2:ℝ)^(kwin 3 L j) := (div_le_div_iff₀ hlampos hden).mpr key
  have hposj : ∀ j : Fin 3, 0 ≤ Z / lam L (j.1 + 1) + 1 := by
    intro j
    have hlampos : 0 < lam L (j.1 + 1) := lam_pos L (by omega) (by rw [hrk]; exact j.2)
    have h1' : 0 ≤ Z / lam L (j.1 + 1) := div_nonneg (le_trans zero_le_one hZ) hlampos.le
    linarith
  have hfac2 : Z / lam L 3 + 1 ≤ 2 := by
    have hlampos : 0 < lam L 3 := lam_pos L (by norm_num) (by omega)
    have hle1 : Z / lam L 3 ≤ 1 := by
      rw [div_le_iff₀ hlampos]
      simpa using le_of_lt h3
    linarith
  have hprod : (∏ i ∈ Finset.range (rk L), (Z / lam L (i + 1) + 1))
      = ∏ j : Fin 3, (Z / lam L (j.1 + 1) + 1) := by
    rw [hrk]
    exact (Fin.prod_univ_eq_prod_range (fun i => Z / lam L (i + 1) + 1) 3).symm
  have hmain : (∏ j : Fin 3, (Z / lam L (j.1 + 1) + 1)) ≤ 32 * Z^2 / wpow2 (widx L) := by
    rw [Fin.prod_univ_three]
    have e0 : Z / lam L ((0:Fin 3).1 + 1) + 1 ≤ 4 * Z / (2:ℝ)^(kwin 3 L 0) := hfac 0 (by decide)
    have e1 : Z / lam L ((1:Fin 3).1 + 1) + 1 ≤ 4 * Z / (2:ℝ)^(kwin 3 L 1) := hfac 1 (by decide)
    have e2 : Z / lam L ((2:Fin 3).1 + 1) + 1 ≤ 2 := hfac2
    have step : (Z / lam L ((0:Fin 3).1 + 1) + 1) * (Z / lam L ((1:Fin 3).1 + 1) + 1)
        * (Z / lam L ((2:Fin 3).1 + 1) + 1)
        ≤ (4 * Z / (2:ℝ)^(kwin 3 L 0)) * (4 * Z / (2:ℝ)^(kwin 3 L 1)) * 2 :=
      mul_le_mul (mul_le_mul e0 e1 (hposj 1) (by positivity)) e2 (hposj 2) (by positivity)
    refine step.trans ?_
    rw [show (4 * Z / (2:ℝ)^(kwin 3 L 0)) * (4 * Z / (2:ℝ)^(kwin 3 L 1)) * 2
        = 32 * Z^2 / wpow2 (widx L) by
      rw [wpow2_widx L, div_mul_div_comm]
      ring]
  have hq : 0 < wpow2 (widx L) := wpow2_pos _
  have hkey : Ks * (32 * Z^2) / wpow2 (widx L) ≤ 256 * Ks * Z^2 / wpow2 (widx L) := by
    have h1 : Ks * (32 * Z^2) ≤ 256 * Ks * Z^2 := by
      nlinarith [mul_nonneg hKs1 (by positivity : (0:ℝ) ≤ Z^2)]
    rw [div_le_div_iff₀ hq hq]
    exact mul_le_mul_of_nonneg_right h1 hq.le
  calc (ballCount L Z : ℝ) ≤ Ks * ∏ i ∈ Finset.range (rk L), (Z / lam L (i + 1) + 1) := hsch
    _ = Ks * ∏ j : Fin 3, (Z / lam L (j.1 + 1) + 1) := by rw [hprod]
    _ ≤ Ks * (32 * Z^2 / wpow2 (widx L)) := mul_le_mul_of_nonneg_left hmain hKs1
    _ = Ks * (32 * Z^2) / wpow2 (widx L) := by ring
    _ ≤ 256 * Ks * Z^2 / wpow2 (widx L) := hkey

/-! ## The main estimate -/

theorem latS_sum_irred :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z Δ : ℝ), 1 ≤ Z → 1 ≤ Δ →
      ∀ (c : Mon 4 4 → ℤ), Irreducible (formOf 4 4 c) →
      ∀ (T : Finset (Submodule ℤ (Fin 5 → ℤ))),
        (∀ L ∈ T, IsPrimLat L ∧ rk L = 3 ∧ detL L ≤ Δ + 1 ∧ lam L 1 ≤ Z ∧ lam L 2 ≤ Z
          ∧ c ∈ vanishOn L) →
        (∑ L ∈ T, (ballCount L Z : ℝ) ^ 2)
          ≤ C * (Z ^ 4 * Δ ^ ((7 : ℝ) / 2) + Z ^ 6 * Δ ^ ((3 : ℝ) / 2))
              * Real.log (2 * Δ) ^ 2 := by
  classical
  obtain ⟨Ks, hKs0, hKs⟩ := Sig2.schmidt_bound (ι := Fin 5)
  obtain ⟨Kmk0, hKmk0pos, hKmk0⟩ := minkowski_upper (Fin 5)
  obtain ⟨Cg, hCg0, hCg⟩ := Work.Q44Geom.good_count
  obtain ⟨Cb, hCb0, hCb⟩ := Work.Q44Geom.bad_count
  set CS : ℝ := Cg + Cb with hCSdef
  have hCS0 : 0 < CS := by rw [hCSdef]; linarith
  set KM : ℝ := max Kmk0 1 with hKMdef
  have hKM1 : 1 ≤ KM := le_max_right _ _
  have hKMpos : 0 < KM := lt_of_lt_of_le zero_lt_one hKM1
  have hmink : ∀ L : Submodule ℤ (Fin 5 → ℤ),
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ KM * detL L := fun L =>
    (hKmk0 L).trans (mul_le_mul_of_nonneg_right (le_max_left Kmk0 1) (detL_nonneg L))
  obtain ⟨Cfac, hCfac0, hCfac⟩ := log_pow_factor KM hKM1
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2sq : (0:ℝ) < (Real.log 2)^2 := pow_pos hlog2 2
  refine ⟨CS * ((512*Ks)^2 * (3 * Cfac^2) + (256*Ks)^2 * (100*Cfac) / (Real.log 2)^2) + 1, ?_, ?_⟩
  · have h1 : 0 < (512*Ks)^2 * (3 * Cfac^2) :=
      mul_pos (pow_pos (by linarith [hKs0]) 2) (mul_pos (by norm_num) (pow_pos hCfac0 2))
    have h2 : 0 < (256*Ks)^2 * (100*Cfac) / (Real.log 2)^2 :=
      div_pos (mul_pos (pow_pos (by linarith [hKs0]) 2) (mul_pos (by norm_num) hCfac0)) hlog2sq
    have h3 : 0 < (512*Ks)^2 * (3 * Cfac^2) + (256*Ks)^2 * (100*Cfac) / (Real.log 2)^2 := by
      linarith
    have h4 := mul_pos hCS0 h3
    linarith
  · intro Z Δ hZ hΔ c hc T hT
    have hc0 : formOf 4 4 c ≠ 0 := hc.ne_zero
    set M0 : ℝ := 8 * KM * (Δ + 1) with hM0def
    have hM0ge1 : 1 ≤ M0 := by rw [hM0def]; nlinarith [hKM1, hΔ]
    set N : ℕ := ⌈Real.logb 2 M0⌉₊ with hNdef
    have hNfac := hCfac Δ N hΔ (le_of_eq (by rw [hNdef, hM0def]))
    have hlogfac : ((N:ℝ) + 2)^2 ≤ Cfac * (Real.log (2*Δ))^2 := hNfac.1
    have hpow15 : (2:ℝ)^(((3:ℝ)/2)*(N:ℝ)) ≤ Cfac * Δ^((3:ℝ)/2) := hNfac.2.1
    have hpow35 : (2:ℝ)^(((7:ℝ)/2)*(N:ℝ)) ≤ Cfac * Δ^((7:ℝ)/2) := hNfac.2.2
    -- the index set of dyadic windows
    set KI : Finset (ℕ × ℕ × ℕ) := ((Finset.range (N + 1)).product
        ((Finset.range (N + 1)).product (Finset.range (N + 1)))).filter
        (fun k => k.1 + k.2.1 + k.2.2 ≤ N) with hKIdef
    -- every lattice of `T` has its window in `KI`
    have hwinmem : ∀ L ∈ T, widx L ∈ KI := by
      intro L hL
      obtain ⟨hLp, hLrk, hLdet, hL1, hL2, hLv⟩ := hT L hL
      obtain ⟨hkA, hkB, hkmono, hksum⟩ := kwin_spec (Fin 5) 3 L (by norm_num) hLrk
      have hprod : (∏ j : Fin 3, (2:ℝ)^(kwin 3 L j)) ≤ M0 := by
        have h2 : (∏ j : Fin 3, (2:ℝ)^(kwin 3 L j)) ≤ 8 * (lam L 1 * lam L 2 * lam L 3) := by
          have n0 : (0:ℝ) ≤ (2:ℝ)^(kwin 3 L 0) := (pow_pos (by norm_num) _).le
          have n1 : (0:ℝ) ≤ (2:ℝ)^(kwin 3 L 1) := (pow_pos (by norm_num) _).le
          have n2 : (0:ℝ) ≤ (2:ℝ)^(kwin 3 L 2) := (pow_pos (by norm_num) _).le
          have m0 : (0:ℝ) ≤ 2 * lam L ((0:Fin 3).1 + 1) := by
            have hp : (0:ℝ) < lam L ((0:Fin 3).1 + 1) :=
              lam_pos L (by omega) (by rw [hLrk]; exact (0:Fin 3).2)
            linarith
          have m1 : (0:ℝ) ≤ 2 * lam L ((1:Fin 3).1 + 1) := by
            have hp : (0:ℝ) < lam L ((1:Fin 3).1 + 1) :=
              lam_pos L (by omega) (by rw [hLrk]; exact (1:Fin 3).2)
            linarith
          have m2 : (0:ℝ) ≤ 2 * lam L ((2:Fin 3).1 + 1) := by
            have hp : (0:ℝ) < lam L ((2:Fin 3).1 + 1) :=
              lam_pos L (by omega) (by rw [hLrk]; exact (2:Fin 3).2)
            linarith
          refine le_trans (prod_fin_three_mono (f := fun j => (2:ℝ)^(kwin 3 L j))
            (g := fun j => 2 * lam L (j.1 + 1)) n0 n1 n2 m0 m1 m2 (hkB 0) (hkB 1) (hkB 2)) ?_
          rw [Fin.prod_univ_three]
          simp only [Fin.val_zero, Fin.val_one', Fin.val_two, Nat.reduceAdd]
          exact le_of_eq (by ring)
        have h4 : lam L 1 * lam L 2 * lam L 3 ≤ KM * detL L := by
          have h := hmink L
          rw [hLrk] at h
          have h5 : (∏ j ∈ Finset.range 3, lam L (j + 1)) = lam L 1 * lam L 2 * lam L 3 := by
            rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
            simp
          rwa [h5] at h
        have h6 : KM * detL L ≤ KM * (Δ + 1) := mul_le_mul_of_nonneg_left hLdet hKMpos.le
        have h7 : (8:ℝ) * (KM * (Δ + 1)) = M0 := by rw [hM0def]; ring
        linarith
      have hsumN : (∑ j : Fin 3, kwin 3 L j) ≤ N := by
        have h := hksum M0 hM0ge1 hprod
        rwa [← hNdef] at h
      have hk0 : kwin 3 L 0 ≤ N :=
        le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ _)) hsumN
      have hk1 : kwin 3 L 1 ≤ N :=
        le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ _)) hsumN
      have hk2 : kwin 3 L 2 ≤ N :=
        le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ _)) hsumN
      have hsumN' : (widx L).1 + (widx L).2.1 + (widx L).2.2 ≤ N := by
        rw [Fin.sum_univ_three] at hsumN
        simpa [widx] using hsumN
      rw [hKIdef, Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
          Finset.mem_range.mpr (by omega)⟩⟩, hsumN'⟩
    -- the counting bound on each window
    have hfib : ∀ k ∈ KI, ((T.filter (fun L => widx L = k)).card : ℝ) ≤ CS * (wpow k) ^ ((7:ℝ)/2) := by
      intro k hk
      by_cases hmon : k.1 ≤ k.2.1 ∧ k.2.1 ≤ k.2.2
      · obtain ⟨hm01, hm12⟩ := hmon
        set σ : Fin 3 → ℝ := fun j => (2:ℝ) ^ (kfun k j) with hσdef
        have hσ1 : 1 ≤ σ 0 := one_le_pow₀ (by norm_num)
        have hσ01 : σ 0 ≤ σ 1 := by
          simp only [hσdef, kfun, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
          exact pow_le_pow_right₀ (by norm_num) hm01
        have hσ12 : σ 1 ≤ σ 2 := by
          simp only [hσdef, kfun, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.tail_cons]
          exact pow_le_pow_right₀ (by norm_num) hm12
        -- the window is contained in the counting set `Sset c σ`
        have hSset_fin : (Work.Q44Geom.Sset c σ).Finite :=
          (prim_lat_window_finite (Fin 5) 3 σ (fun j => one_le_pow₀ (by norm_num))).subset
            (fun L hL => ⟨hL.1, hL.2.1, hL.2.2.1⟩)
        have hsub : (↑(T.filter (fun L => widx L = k)) : Set (Submodule ℤ (Fin 5 → ℤ)))
            ⊆ Work.Q44Geom.Sset c σ := by
          intro L hL
          rw [Finset.mem_coe, Finset.mem_filter] at hL
          obtain ⟨hLT, hLk⟩ := hL
          obtain ⟨hLp, hLrk, -, -, -, hLv⟩ := hT L hLT
          refine ⟨hLp, hLrk, ?_, hLv⟩
          intro j
          have h1 : lam L (j.1 + 1) ≤ (2:ℝ) ^ (kwin 3 L j) :=
            (kwin_spec (Fin 5) 3 L (by norm_num) hLrk).1 j
          have h2 : kwin 3 L j = kfun k j := kwin_eq_kfun hLk j
          rwa [h2] at h1
        have hcard2 : ((T.filter (fun L => widx L = k)).card : ℝ)
            ≤ ((Work.Q44Geom.Sset c σ).ncard : ℝ) := by
          have h2 : (T.filter (fun L => widx L = k)).card ≤ (Work.Q44Geom.Sset c σ).ncard := by
            have h2' := Set.ncard_le_ncard hsub hSset_fin
            rwa [Set.ncard_coe_finset] at h2'
          exact_mod_cast h2
        have hσpow : σ 0 * σ 1 * σ 2 = wpow k := by
          rw [wpow_eq_prod, Fin.prod_univ_three]
        -- split the counting set into the good and the bad lattices
        set G : Set (Submodule ℤ (Fin 5 → ℤ)) :=
          {L | L ∈ Work.Q44Geom.Sset c σ ∧ Work.Q44Geom.goodPair c σ L} with hGdef
        set B : Set (Submodule ℤ (Fin 5 → ℤ)) :=
          {L | L ∈ Work.Q44Geom.Sset c σ ∧ ¬ Work.Q44Geom.goodPair c σ L} with hBdef
        have hGfin : G.Finite := hSset_fin.subset (fun L hL => hL.1)
        have hBfin : B.Finite := hSset_fin.subset (fun L hL => hL.1)
        have hcover : Work.Q44Geom.Sset c σ ⊆ G ∪ B := by
          intro L hL
          by_cases hg : Work.Q44Geom.goodPair c σ L
          · exact Or.inl ⟨hL, hg⟩
          · exact Or.inr ⟨hL, hg⟩
        have hcardS : ((Work.Q44Geom.Sset c σ).ncard : ℝ) ≤ (G.ncard : ℝ) + (B.ncard : ℝ) := by
          have h1 := Set.ncard_le_ncard hcover (hGfin.union hBfin)
          have h2 := Set.ncard_union_le G B
          have h3 : (G ∪ B).ncard ≤ G.ncard + B.ncard := h2
          exact_mod_cast le_trans h1 h3
        have hGcard : (G.ncard : ℝ) ≤ Cg * (σ 0)^4 * (σ 1)^4 :=
          hCg c hc0 hc σ hσ1 hσ01
        have hBcard : (B.ncard : ℝ) ≤ Cb * (σ 0)^3 * (σ 1)^5 * (σ 2)^2 :=
          hCb c hc0 hc σ hσ1 hσ01 hσ12
        have hArith1 : (σ 0)^4 * (σ 1)^4 ≤ (wpow k) ^ ((7:ℝ)/2) := by
          rw [← hσpow]
          exact Work.Q44Geom.arith_1 hσ1 hσ01 hσ12
        have hArith4 : (σ 0)^3 * (σ 1)^5 * (σ 2)^2 ≤ (wpow k) ^ ((7:ℝ)/2) := by
          rw [← hσpow]
          exact Work.Q44Geom.arith_4 hσ1 hσ01 hσ12
        have hG' : Cg * (σ 0)^4 * (σ 1)^4 = Cg * ((σ 0)^4 * (σ 1)^4) := by ring
        have hB'' : Cb * (σ 0)^3 * (σ 1)^5 * (σ 2)^2
            = Cb * ((σ 0)^3 * (σ 1)^5 * (σ 2)^2) := by ring
        have hGB : (G.ncard : ℝ) + (B.ncard : ℝ)
            ≤ Cg * ((σ 0)^4 * (σ 1)^4) + Cb * ((σ 0)^3 * (σ 1)^5 * (σ 2)^2) := by
          rw [hG'] at hGcard
          rw [hB''] at hBcard
          exact add_le_add hGcard hBcard
        have hfin : Cg * ((σ 0)^4 * (σ 1)^4) + Cb * ((σ 0)^3 * (σ 1)^5 * (σ 2)^2)
            ≤ Cg * (wpow k) ^ ((7:ℝ)/2) + Cb * (wpow k) ^ ((7:ℝ)/2) :=
          add_le_add (mul_le_mul_of_nonneg_left hArith1 hCg0.le)
            (mul_le_mul_of_nonneg_left hArith4 hCb0.le)
        calc ((T.filter (fun L => widx L = k)).card : ℝ)
            ≤ ((Work.Q44Geom.Sset c σ).ncard : ℝ) := hcard2
          _ ≤ (G.ncard : ℝ) + (B.ncard : ℝ) := hcardS
          _ ≤ Cg * ((σ 0)^4 * (σ 1)^4) + Cb * ((σ 0)^3 * (σ 1)^5 * (σ 2)^2) := hGB
          _ ≤ Cg * (wpow k) ^ ((7:ℝ)/2) + Cb * (wpow k) ^ ((7:ℝ)/2) := hfin
          _ = CS * (wpow k) ^ ((7:ℝ)/2) := by rw [hCSdef]; ring
      · push_neg at hmon
        have hempty : T.filter (fun L => widx L = k) = ∅ := by
          rw [← Finset.not_nonempty_iff_eq_empty]
          rintro ⟨L, hL⟩
          simp only [Finset.mem_filter] at hL
          obtain ⟨hLT, hLk⟩ := hL
          obtain ⟨-, hLrk, -, -, -, -⟩ := hT L hLT
          have hmn := (kwin_spec (Fin 5) 3 L (by norm_num) hLrk).2.2.1
          have h01 : kwin 3 L 0 ≤ kwin 3 L 1 := hmn (by decide)
          have h12 : kwin 3 L 1 ≤ kwin 3 L 2 := hmn (by decide)
          have e0 : k.1 = kwin 3 L 0 := by rw [← hLk]; rfl
          have e1 : k.2.1 = kwin 3 L 1 := by rw [← hLk]; rfl
          have e2 : k.2.2 = kwin 3 L 2 := by rw [← hLk]; rfl
          omega
        rw [hempty, Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg hCS0.le (Real.rpow_nonneg (wpow_pos k).le _)
    -- the pointwise charge bounds
    have hchargeA : ∀ L ∈ T, lam L 3 ≤ Z →
        (ballCount L Z : ℝ) ≤ 512 * Ks * Z^3 / wpow (widx L) := by
      intro L hL h3
      obtain ⟨-, hLrk, -, hL1, hL2, -⟩ := hT L hL
      exact ballCount_le_winA L Ks Z hKs0.le (hKs L) hZ hLrk hL1 hL2 h3
    have hchargeB : ∀ L ∈ T, Z < lam L 3 →
        (ballCount L Z : ℝ) ≤ 256 * Ks * Z^2 / wpow2 (widx L) := by
      intro L hL h3
      obtain ⟨-, hLrk, -, hL1, hL2, -⟩ := hT L hL
      exact ballCount_le_winB L Ks Z hKs0.le (hKs L) hZ hLrk hL1 hL2 h3
    -- the fibre decomposition
    have hsplit : (∑ L ∈ T, (ballCount L Z : ℝ) ^ 2)
        = ∑ k ∈ KI, ∑ L ∈ T.filter (fun L => widx L = k), (ballCount L Z : ℝ) ^ 2 :=
      (Finset.sum_fiberwise_of_maps_to hwinmem (fun L => (ballCount L Z : ℝ) ^ 2)).symm
    rw [hsplit]
    -- per-window bound
    have hbound : ∀ k ∈ KI,
        (∑ L ∈ T.filter (fun L => widx L = k), (ballCount L Z : ℝ) ^ 2)
          ≤ CS * (wpow k) ^ ((7:ℝ)/2) *
              (((512*Ks) * Z^3 / wpow k)^2 + ((256*Ks) * Z^2 / wpow2 k)^2) := by
      intro k hk
      have hcardF := hfib k hk
      have hA : (∑ L ∈ (T.filter (fun L => widx L = k)).filter (fun L => lam L 3 ≤ Z),
            (ballCount L Z : ℝ) ^ 2)
          ≤ (CS * (wpow k) ^ ((7:ℝ)/2)) * ((512*Ks) * Z^3 / wpow k)^2 := by
        have hcard : ((((T.filter (fun L => widx L = k)).filter
            (fun L => lam L 3 ≤ Z)).card : ℕ) : ℝ) ≤ CS * (wpow k) ^ ((7:ℝ)/2) := by
          refine le_trans ?_ hcardF
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        have hpt : ∀ L ∈ (T.filter (fun L => widx L = k)).filter (fun L => lam L 3 ≤ Z),
            (ballCount L Z : ℝ) ^ 2 ≤ ((512*Ks) * Z^3 / wpow k)^2 := by
          intro L hL
          rw [Finset.mem_filter] at hL
          obtain ⟨hLF, hL3⟩ := hL
          rw [Finset.mem_filter] at hLF
          obtain ⟨hLT, hLk⟩ := hLF
          have hb := hchargeA L hLT hL3
          rw [hLk] at hb
          exact pow_le_pow_left₀ (by positivity) hb 2
        calc (∑ L ∈ (T.filter (fun L => widx L = k)).filter (fun L => lam L 3 ≤ Z),
              (ballCount L Z : ℝ) ^ 2)
            ≤ ∑ _L ∈ (T.filter (fun L => widx L = k)).filter (fun L => lam L 3 ≤ Z),
                ((512*Ks) * Z^3 / wpow k)^2 := Finset.sum_le_sum hpt
          _ = ((((T.filter (fun L => widx L = k)).filter (fun L => lam L 3 ≤ Z)).card : ℕ) : ℝ)
                * ((512*Ks) * Z^3 / wpow k)^2 := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (CS * (wpow k) ^ ((7:ℝ)/2)) * ((512*Ks) * Z^3 / wpow k)^2 :=
              mul_le_mul_of_nonneg_right hcard (by positivity)
      have hB : (∑ L ∈ (T.filter (fun L => widx L = k)).filter (fun L => ¬ lam L 3 ≤ Z),
            (ballCount L Z : ℝ) ^ 2)
          ≤ (CS * (wpow k) ^ ((7:ℝ)/2)) * ((256*Ks) * Z^2 / wpow2 k)^2 := by
        have hcard : ((((T.filter (fun L => widx L = k)).filter
            (fun L => ¬ lam L 3 ≤ Z)).card : ℕ) : ℝ) ≤ CS * (wpow k) ^ ((7:ℝ)/2) := by
          refine le_trans ?_ hcardF
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        have hpt : ∀ L ∈ (T.filter (fun L => widx L = k)).filter (fun L => ¬ lam L 3 ≤ Z),
            (ballCount L Z : ℝ) ^ 2 ≤ ((256*Ks) * Z^2 / wpow2 k)^2 := by
          intro L hL
          rw [Finset.mem_filter] at hL
          obtain ⟨hLF, hL3⟩ := hL
          rw [Finset.mem_filter] at hLF
          obtain ⟨hLT, hLk⟩ := hLF
          have hb := hchargeB L hLT (not_le.mp hL3)
          rw [hLk] at hb
          exact pow_le_pow_left₀ (by positivity) hb 2
        calc (∑ L ∈ (T.filter (fun L => widx L = k)).filter (fun L => ¬ lam L 3 ≤ Z),
              (ballCount L Z : ℝ) ^ 2)
            ≤ ∑ _L ∈ (T.filter (fun L => widx L = k)).filter (fun L => ¬ lam L 3 ≤ Z),
                ((256*Ks) * Z^2 / wpow2 k)^2 := Finset.sum_le_sum hpt
          _ = ((((T.filter (fun L => widx L = k)).filter (fun L => ¬ lam L 3 ≤ Z)).card : ℕ) : ℝ)
                * ((256*Ks) * Z^2 / wpow2 k)^2 := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (CS * (wpow k) ^ ((7:ℝ)/2)) * ((256*Ks) * Z^2 / wpow2 k)^2 :=
              mul_le_mul_of_nonneg_right hcard (by positivity)
      calc (∑ L ∈ T.filter (fun L => widx L = k), (ballCount L Z : ℝ) ^ 2)
          = (∑ L ∈ (T.filter (fun L => widx L = k)).filter (fun L => lam L 3 ≤ Z),
                (ballCount L Z : ℝ) ^ 2)
            + (∑ L ∈ (T.filter (fun L => widx L = k)).filter (fun L => ¬ lam L 3 ≤ Z),
                (ballCount L Z : ℝ) ^ 2) :=
              (Finset.sum_filter_add_sum_filter_not _ (fun L => lam L 3 ≤ Z) _).symm
        _ ≤ (CS * (wpow k) ^ ((7:ℝ)/2)) * ((512*Ks) * Z^3 / wpow k)^2
            + (CS * (wpow k) ^ ((7:ℝ)/2)) * ((256*Ks) * Z^2 / wpow2 k)^2 := add_le_add hA hB
        _ = CS * (wpow k) ^ ((7:ℝ)/2) *
              (((512*Ks) * Z^3 / wpow k)^2 + ((256*Ks) * Z^2 / wpow2 k)^2) := by ring
    -- the two dyadic sums
    have hshell : (∑ k ∈ KI, (wpow k) ^ ((3:ℝ)/2))
        ≤ 3 * ((N:ℝ) + 2)^2 * (2:ℝ)^(((3:ℝ)/2) * (N:ℝ)) := by
      have hcongr : (∑ k ∈ KI, (wpow k) ^ ((3:ℝ)/2))
          = ∑ k ∈ KI, (2:ℝ)^(((3:ℝ)/2) * ((k.1 + k.2.1 + k.2.2 : ℕ) : ℝ)) :=
        Finset.sum_congr rfl (fun k _ => wpow_rpow_three k)
      rw [hcongr]
      exact rpow_shell_sum KI N (fun k hk => (Finset.mem_filter.mp hk).2)
    have hcaseB : (∑ k ∈ KI, ((2:ℝ)^k.1 * (2:ℝ)^k.2.1) ^ ((3:ℝ)/2)
          * ((2:ℝ)^k.2.2) ^ ((7:ℝ)/2))
        ≤ 100 * (2:ℝ)^(((7:ℝ)/2) * (N:ℝ)) := by
      rw [hKIdef]
      exact rpow_caseB_sum N
    have hterm1 : ∀ k : ℕ × ℕ × ℕ, CS * (wpow k) ^ ((7:ℝ)/2) * ((512*Ks) * Z^3 / wpow k)^2
        = (CS * (512*Ks)^2 * Z^6) * (wpow k) ^ ((3:ℝ)/2) := by
      intro k
      rw [rpow_combine_A (hρ := wpow_pos k)]
      ring
    have hterm2 : ∀ k : ℕ × ℕ × ℕ, CS * (wpow k) ^ ((7:ℝ)/2) * ((256*Ks) * Z^2 / wpow2 k)^2
        = (CS * (256*Ks)^2 * Z^4) *
            (((2:ℝ)^k.1 * (2:ℝ)^k.2.1) ^ ((3:ℝ)/2) * ((2:ℝ)^k.2.2) ^ ((7:ℝ)/2)) := by
      intro k
      have hq : (0:ℝ) < (2:ℝ)^k.1 * (2:ℝ)^k.2.1 := mul_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)
      have ht : (0:ℝ) < (2:ℝ)^k.2.2 := pow_pos (by norm_num) _
      rw [wpow_split k]
      simp only [wpow2]
      rw [rpow_combine_B (hq := hq) (ht := ht)]
      ring
    calc (∑ k ∈ KI, ∑ L ∈ T.filter (fun L => widx L = k), (ballCount L Z : ℝ) ^ 2)
        ≤ ∑ k ∈ KI, CS * (wpow k) ^ ((7:ℝ)/2) *
              (((512*Ks) * Z^3 / wpow k)^2 + ((256*Ks) * Z^2 / wpow2 k)^2) :=
            Finset.sum_le_sum hbound
      _ = (∑ k ∈ KI, CS * (wpow k) ^ ((7:ℝ)/2) * ((512*Ks) * Z^3 / wpow k)^2)
            + (∑ k ∈ KI, CS * (wpow k) ^ ((7:ℝ)/2) * ((256*Ks) * Z^2 / wpow2 k)^2) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ = (CS * (512*Ks)^2 * Z^6) * (∑ k ∈ KI, (wpow k) ^ ((3:ℝ)/2))
            + (CS * (256*Ks)^2 * Z^4) *
                (∑ k ∈ KI, ((2:ℝ)^k.1 * (2:ℝ)^k.2.1) ^ ((3:ℝ)/2)
                  * ((2:ℝ)^k.2.2) ^ ((7:ℝ)/2)) := by
          rw [Finset.sum_congr rfl (fun k _ => hterm1 k),
            Finset.sum_congr rfl (fun k _ => hterm2 k)]
          rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ (CS * (512*Ks)^2 * Z^6) * (3 * ((N:ℝ) + 2)^2 * (2:ℝ)^(((3:ℝ)/2) * (N:ℝ)))
            + (CS * (256*Ks)^2 * Z^4) * (100 * (2:ℝ)^(((7:ℝ)/2) * (N:ℝ))) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hshell (by positivity)
          · exact mul_le_mul_of_nonneg_left hcaseB (by positivity)
      _ ≤ (CS * (512*Ks)^2 * Z^6) * (3 * (Cfac * (Real.log (2*Δ))^2) * (Cfac * Δ^((3:ℝ)/2)))
            + (CS * (256*Ks)^2 * Z^4) * (100 * (Cfac * Δ^((7:ℝ)/2))) := by
          apply add_le_add
          · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine mul_le_mul (mul_le_mul_of_nonneg_left hlogfac (by norm_num)) hpow15
              (by positivity) (by positivity)
          · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left hpow35 (by norm_num)
      _ ≤ (CS * ((512*Ks)^2 * (3 * Cfac^2) + (256*Ks)^2 * (100*Cfac) / (Real.log 2)^2) + 1)
            * (Z^4 * Δ^((7:ℝ)/2) + Z^6 * Δ^((3:ℝ)/2)) * (Real.log (2*Δ))^2 := by
          have hlogge : (Real.log 2)^2 ≤ (Real.log (2*Δ))^2 := by
            have h1 : Real.log 2 ≤ Real.log (2*Δ) := Real.log_le_log (by norm_num) (by linarith)
            exact pow_le_pow_left₀ hlog2.le h1 2
          have hΔ0 : (0:ℝ) < Δ := by linarith
          have hΔa : (0:ℝ) ≤ Δ^((3:ℝ)/2) := Real.rpow_nonneg hΔ0.le _
          have hΔb : (0:ℝ) ≤ Δ^((7:ℝ)/2) := Real.rpow_nonneg hΔ0.le _
          have hZ0 : (0:ℝ) < Z := by linarith
          have hZ6 : (0:ℝ) ≤ Z^6 := pow_nonneg hZ0.le 6
          have hZ4 : (0:ℝ) ≤ Z^4 := pow_nonneg hZ0.le 4
          have hL0 : (0:ℝ) ≤ (Real.log (2*Δ))^2 := sq_nonneg _
          have hAeq : (CS * (512*Ks)^2 * Z^6) *
                (3 * (Cfac * (Real.log (2*Δ))^2) * (Cfac * Δ^((3:ℝ)/2)))
              = CS * (512*Ks)^2 * (3 * Cfac^2)
                * (Z^6 * Δ^((3:ℝ)/2) * (Real.log (2*Δ))^2) := by ring
          have hBeq : (CS * (256*Ks)^2 * Z^4) * (100 * (Cfac * Δ^((7:ℝ)/2)))
              = CS * (256*Ks)^2 * (100 * Cfac) * (Z^4 * Δ^((7:ℝ)/2)) := by ring
          rw [hAeq, hBeq]
          have hA : CS * (512*Ks)^2 * (3 * Cfac^2) * (Z^6 * Δ^((3:ℝ)/2) * (Real.log (2*Δ))^2)
              ≤ (CS * ((512*Ks)^2 * (3 * Cfac^2)
                    + (256*Ks)^2 * (100*Cfac) / (Real.log 2)^2) + 1)
                * (Z^6 * Δ^((3:ℝ)/2) * (Real.log (2*Δ))^2) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (mul_nonneg hZ6 hΔa) hL0)
            have h1 : (0:ℝ) ≤ (256*Ks)^2 * (100*Cfac) / (Real.log 2)^2 :=
              div_nonneg (by positivity) hlog2sq.le
            have h2b : CS * ((512*Ks)^2 * (3*Cfac^2))
                ≤ CS * ((512*Ks)^2 * (3 * Cfac^2) + (256*Ks)^2 * (100*Cfac) / (Real.log 2)^2) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h1) hCS0.le
            linarith [h2b]
          have hBB : CS * (256*Ks)^2 * (100 * Cfac) * (Z^4 * Δ^((7:ℝ)/2))
              ≤ (CS * ((512*Ks)^2 * (3 * Cfac^2)
                    + (256*Ks)^2 * (100*Cfac) / (Real.log 2)^2) + 1)
                * (Z^4 * Δ^((7:ℝ)/2) * (Real.log (2*Δ))^2) := by
            have hle : CS * (256*Ks)^2 * (100*Cfac) / (Real.log 2)^2
                ≤ CS * ((512*Ks)^2 * (3 * Cfac^2)
                  + (256*Ks)^2 * (100*Cfac) / (Real.log 2)^2) + 1 := by
              have heq : CS * (256*Ks)^2 * (100*Cfac) / (Real.log 2)^2
                  = CS * ((256*Ks)^2 * (100*Cfac) / (Real.log 2)^2) := by ring
              have h2 : (0:ℝ) ≤ CS * ((512*Ks)^2 * (3*Cfac^2)) :=
                mul_nonneg hCS0.le (by positivity)
              have h3 : CS * ((256*Ks)^2 * (100*Cfac) / (Real.log 2)^2)
                  ≤ CS * ((512*Ks)^2 * (3 * Cfac^2))
                    + CS * ((256*Ks)^2 * (100*Cfac) / (Real.log 2)^2) := le_add_of_nonneg_left h2
              rw [heq, mul_add]
              linarith [h3]
            have h2 : CS * (256*Ks)^2 * (100*Cfac)
                ≤ (CS * ((512*Ks)^2 * (3 * Cfac^2)
                    + (256*Ks)^2 * (100*Cfac) / (Real.log 2)^2) + 1) * (Real.log 2)^2 := by
              rw [div_le_iff₀ hlog2sq] at hle
              linarith
            have hw : (0:ℝ) ≤ Z^4 * Δ^((7:ℝ)/2) := mul_nonneg hZ4 hΔb
            calc CS * (256*Ks)^2 * (100*Cfac) * (Z^4 * Δ^((7:ℝ)/2))
                ≤ ((CS * ((512*Ks)^2 * (3 * Cfac^2)
                      + (256*Ks)^2 * (100*Cfac) / (Real.log 2)^2) + 1) * (Real.log 2)^2)
                  * (Z^4 * Δ^((7:ℝ)/2)) := mul_le_mul_of_nonneg_right h2 hw
              _ ≤ ((CS * ((512*Ks)^2 * (3 * Cfac^2)
                      + (256*Ks)^2 * (100*Cfac) / (Real.log 2)^2) + 1) * (Real.log (2*Δ))^2)
                  * (Z^4 * Δ^((7:ℝ)/2)) := by
                  refine mul_le_mul_of_nonneg_right ?_ hw
                  exact mul_le_mul_of_nonneg_left hlogge (by positivity)
              _ = (CS * ((512*Ks)^2 * (3 * Cfac^2)
                      + (256*Ks)^2 * (100*Cfac) / (Real.log 2)^2) + 1)
                  * (Z^4 * Δ^((7:ℝ)/2) * (Real.log (2*Δ))^2) := by ring
          have hexp : (CS * ((512*Ks)^2 * (3 * Cfac^2)
                  + (256*Ks)^2 * (100*Cfac) / (Real.log 2)^2) + 1)
                * (Z^4 * Δ^((7:ℝ)/2) + Z^6 * Δ^((3:ℝ)/2)) * (Real.log (2*Δ))^2
              = (CS * ((512*Ks)^2 * (3 * Cfac^2)
                    + (256*Ks)^2 * (100*Cfac) / (Real.log 2)^2) + 1)
                  * (Z^6 * Δ^((3:ℝ)/2) * (Real.log (2*Δ))^2)
                + (CS * ((512*Ks)^2 * (3 * Cfac^2)
                    + (256*Ks)^2 * (100*Cfac) / (Real.log 2)^2) + 1)
                  * (Z^4 * Δ^((7:ℝ)/2) * (Real.log (2*Δ))^2) := by ring
          rw [hexp]
          exact add_le_add hA hBB

end Work.HP.MDEstimates
