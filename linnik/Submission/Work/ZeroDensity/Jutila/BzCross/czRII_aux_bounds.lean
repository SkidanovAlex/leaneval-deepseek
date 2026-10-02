import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.czReindexDefs
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzHarmDecayHere
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.SumDivisorsIccSwap
import Submission.Work.ZeroDensity.Jutila.SigmaHalfAvg
import Submission.Work.LinnikAreas.Density4.sum_inv_mul_sqrt_le

namespace Work.ZeroDensity.Jutila.BzCross

open Finset
open Work.ZeroDensity.Jutila

noncomputable section

set_option maxHeartbeats 1600000

/-- Real (de la Vallée Poussin) envelope `exp (-(c √(log x)))`. -/
def czEpsR (c : ℝ) (x : ℝ) : ℝ := Real.exp (-(c * Real.sqrt (Real.log x)))

lemma Dc_eq_epsR (c : ℝ) (n : ℕ) : Dc c n = czEpsR c (n : ℝ) := rfl

lemma czEpsR_pos (c : ℝ) (x : ℝ) : 0 < czEpsR c x := Real.exp_pos _

lemma czEpsR_nonneg (c : ℝ) (x : ℝ) : 0 ≤ czEpsR c x := (Real.exp_pos _).le

lemma czEpsR_anti {c : ℝ} (hc : 0 ≤ c) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    czEpsR c y ≤ czEpsR c x := by
  rw [czEpsR, czEpsR, Real.exp_le_exp]
  have hlog : Real.log x ≤ Real.log y := Real.log_le_log hx hxy
  have hsqrt : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log y) := Real.sqrt_le_sqrt hlog
  have h2 : c * Real.sqrt (Real.log x) ≤ c * Real.sqrt (Real.log y) :=
    mul_le_mul_of_nonneg_left hsqrt hc
  linarith only [h2]

lemma czEpsR_one {c : ℝ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : czEpsR c x = 1 := by
  rw [czEpsR]
  have h : Real.log x ≤ 0 := Real.log_nonpos hx0 hx1
  rw [Real.sqrt_eq_zero_of_nonpos h, mul_zero, neg_zero, Real.exp_zero]

lemma sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hsq : (Real.sqrt a + Real.sqrt b) ^ 2 = a + b + 2 * (Real.sqrt a * Real.sqrt b) := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]; ring
  rw [hsq]
  nlinarith only [Real.sqrt_nonneg a, Real.sqrt_nonneg b]

lemma sqrt_le_sqrt_add {x y : ℝ} (h : y ≤ x) :
    Real.sqrt x ≤ Real.sqrt y + Real.sqrt (x - y) := by
  rcases le_total 0 y with hy | hy
  · have hxy : 0 ≤ x - y := by linarith only [h]
    have h2 := sqrt_add_le (x - y) y hxy hy
    rw [show x - y + y = x by ring] at h2
    linarith only [h2]
  · have h1 : Real.sqrt x ≤ Real.sqrt (x - y) := Real.sqrt_le_sqrt (by linarith only [hy])
    rw [Real.sqrt_eq_zero_of_nonpos hy, zero_add]
    exact h1

lemma Dc_floor_le_epsR_half {c : ℝ} (hc : 0 ≤ c) {x : ℝ} (hx : 0 ≤ x) :
    Dc c ⌊x⌋₊ ≤ czEpsR c (x / 2) := by
  by_cases h : x ≤ 2
  · rw [czEpsR_one (by linarith only [hx] : (0:ℝ) ≤ x / 2) (by linarith only [h] : x / 2 ≤ 1)]
    exact Dc_le_one hc _
  · push Not at h
    have hx2 : 0 < x / 2 := by linarith only [h]
    have hge : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
      have hlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      have h2 : x / 2 < x - 1 := by linarith only [h]
      linarith only [h, hlt]
    have hmono := czEpsR_anti hc hx2 hge
    rw [← Dc_eq_epsR c ⌊x⌋₊] at hmono
    exact hmono

/-! ## Dyadic bookkeeping -/

lemma sum_Icc_pow2_blocks (g : ℕ → ℝ) (n : ℕ) :
    ∑ r ∈ Finset.Icc (1:ℕ) ((2:ℕ) ^ n), g r
      = g 1 + ∑ j ∈ Finset.range n, ∑ r ∈ Finset.Ioc ((2:ℕ) ^ j) ((2:ℕ) ^ (j + 1)), g r := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hunion : Finset.Icc (1:ℕ) (2 ^ (n + 1))
        = Finset.Icc (1:ℕ) ((2:ℕ) ^ n) ∪ Finset.Ioc (2 ^ n) (2 ^ (n + 1)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      constructor
      · intro hx
        by_cases h : x ≤ 2 ^ n
        · exact Or.inl ⟨hx.1, h⟩
        · push Not at h
          exact Or.inr ⟨h, hx.2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · have hle : 2 ^ n ≤ 2 ^ (n + 1) := by rw [pow_succ]; omega
          exact ⟨h1, le_trans h2 hle⟩
        · exact ⟨by omega, h2⟩
    have hdisj : Disjoint (Finset.Icc (1:ℕ) ((2:ℕ) ^ n)) (Finset.Ioc (2 ^ n) (2 ^ (n + 1))) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      simp only [Finset.mem_Icc] at hx
      simp only [Finset.mem_Ioc] at hy
      omega
    rw [hunion, Finset.sum_union hdisj, ih, Finset.sum_range_succ]
    abel

lemma sum_sq_le_cube (M : ℕ) :
    ∑ m ∈ Finset.Icc (1:ℕ) M, (m : ℝ) ^ 2 ≤ (M : ℝ) ^ 3 := by
  calc ∑ m ∈ Finset.Icc (1:ℕ) M, (m : ℝ) ^ 2
      ≤ ∑ _m ∈ Finset.Icc (1:ℕ) M, (M : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro m hm
        have hmM : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).2
        exact pow_le_pow_left₀ (Nat.cast_nonneg m) hmM 2
    _ = (M : ℝ) * (M : ℝ) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
        norm_num
    _ = (M : ℝ) ^ 3 := by ring

/-! ## The dyadic geometric bound -/

theorem czGeomDecay :
    ∃ K : ℝ, 0 < K ∧ ∀ (a : ℝ) (n : ℕ), 0 < a →
      (∑ j ∈ Finset.range (n + 1), (2 : ℝ) ^ j * czEpsR 1 (a * 2 ^ j))
        ≤ K * (2 : ℝ) ^ n * czEpsR 1 (a * 2 ^ n) := by
  set γ : ℝ := Real.sqrt (Real.log 2) with hγ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le1 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
  have hγ0 : 0 ≤ γ := by rw [hγ]; exact Real.sqrt_nonneg _
  have hγle1 : γ ≤ 1 := by
    rw [hγ]
    calc Real.sqrt (Real.log 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hlog2le1
      _ = 1 := Real.sqrt_one
  have hγhalf : γ / 2 < Real.log 2 := by
    have h : (1 : ℝ) / 2 < Real.log 2 := by linarith only [Real.log_two_gt_d9, hlog2]
    linarith only [hγle1, h]
  set ρ : ℝ := Real.exp (γ / 2) / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hρ1 : ρ < 1 := by
    rw [hρ, div_lt_one (by norm_num : (0 : ℝ) < 2)]
    have h := Real.exp_lt_exp.mpr hγhalf
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at h
  refine ⟨Real.exp (γ / 2) * (1 - ρ)⁻¹, by positivity, ?_⟩
  intro a n ha
  have ha0 : 0 < a := ha
  have hstep : ∀ j ∈ Finset.range (n + 1),
      (2 : ℝ) ^ j * czEpsR 1 (a * 2 ^ j)
        ≤ ((2 : ℝ) ^ n * czEpsR 1 (a * 2 ^ n))
            * ((1 / 2 : ℝ) ^ (n - j) * Real.exp (γ * Real.sqrt (((n - j : ℕ)) : ℝ))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjn : j ≤ n := by omega
    have haj : 0 < a * (2 : ℝ) ^ j := by positivity
    have hpow : (2 : ℝ) ^ j = (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ (n - j) := by
      have h1 : (2 : ℝ) ^ n = (2 : ℝ) ^ j * (2 : ℝ) ^ (n - j) := by
        rw [← pow_add]; congr 1; omega
      rw [h1, mul_assoc, ← mul_pow]
      norm_num
    have hlogdiff : Real.log (a * (2 : ℝ) ^ n) - Real.log (a * (2 : ℝ) ^ j)
        = (((n - j : ℕ)) : ℝ) * Real.log 2 := by
      rw [Real.log_mul ha0.ne' (pow_ne_zero n (by norm_num : (2:ℝ) ≠ 0)),
          Real.log_mul ha0.ne' (pow_ne_zero j (by norm_num : (2:ℝ) ≠ 0)),
          Real.log_pow, Real.log_pow, Nat.cast_sub hjn]
      ring
    have hle0 : Real.log (a * (2 : ℝ) ^ j) ≤ Real.log (a * (2 : ℝ) ^ n) :=
      Real.log_le_log haj (by
        apply mul_le_mul_of_nonneg_left _ ha0.le
        exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hjn)
    have hsub : Real.sqrt (Real.log (a * (2 : ℝ) ^ n)) - Real.sqrt (Real.log (a * (2 : ℝ) ^ j))
        ≤ γ * Real.sqrt (((n - j : ℕ)) : ℝ) := by
      have h1 := sqrt_le_sqrt_add (x := Real.log (a * (2 : ℝ) ^ n))
        (y := Real.log (a * (2 : ℝ) ^ j)) hle0
      rw [hlogdiff] at h1
      have h2 : Real.sqrt ((((n - j : ℕ)) : ℝ) * Real.log 2)
          = γ * Real.sqrt (((n - j : ℕ)) : ℝ) := by
        rw [Real.sqrt_mul (by positivity), hγ]; ring
      rw [h2] at h1
      linarith only [h1]
    have henv : czEpsR 1 (a * 2 ^ j)
        ≤ czEpsR 1 (a * 2 ^ n) * Real.exp (γ * Real.sqrt (((n - j : ℕ)) : ℝ)) := by
      rw [czEpsR, czEpsR, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith only [hsub]
    calc (2 : ℝ) ^ j * czEpsR 1 (a * 2 ^ j)
        = (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ (n - j) * czEpsR 1 (a * 2 ^ j) := by rw [hpow]
      _ ≤ (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ (n - j)
            * (czEpsR 1 (a * 2 ^ n) * Real.exp (γ * Real.sqrt (((n - j : ℕ)) : ℝ))) :=
          mul_le_mul_of_nonneg_left henv (by positivity)
      _ = (2 : ℝ) ^ n * czEpsR 1 (a * 2 ^ n)
            * ((1 / 2 : ℝ) ^ (n - j) * Real.exp (γ * Real.sqrt (((n - j : ℕ)) : ℝ))) := by ring
  have hterm : ∀ m ∈ Finset.range (n + 1),
      (1 / 2 : ℝ) ^ m * Real.exp (γ * Real.sqrt ((m : ℕ) : ℝ)) ≤ Real.exp (γ / 2) * ρ ^ m := by
    intro m _
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hsqrt : Real.sqrt ((m : ℕ) : ℝ) ≤ ((m : ℝ) + 1) / 2 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      nlinarith only [sq_nonneg (Real.sqrt ((m:ℕ):ℝ) - 1), Real.sq_sqrt hm0, Real.sqrt_nonneg ((m:ℕ):ℝ), hm0]
    have hexp : Real.exp (γ * Real.sqrt ((m : ℕ) : ℝ))
        ≤ Real.exp (γ / 2) * Real.exp (γ / 2) ^ m := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith only [hsqrt, hγ0]
    calc (1 / 2 : ℝ) ^ m * Real.exp (γ * Real.sqrt ((m : ℕ) : ℝ))
        ≤ (1 / 2 : ℝ) ^ m * (Real.exp (γ / 2) * Real.exp (γ / 2) ^ m) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = Real.exp (γ / 2) * ρ ^ m := by
          rw [hρ, show Real.exp (γ/2)/2 = Real.exp (γ/2) * (1/2:ℝ) by ring, mul_pow]
          ring
  have hinner : (∑ j ∈ Finset.range (n + 1),
        ((1 / 2 : ℝ) ^ (n - j) * Real.exp (γ * Real.sqrt (((n - j : ℕ)) : ℝ))))
      ≤ Real.exp (γ / 2) * (1 - ρ)⁻¹ := by
    have hcongr : (∑ j ∈ Finset.range (n + 1),
          ((1 / 2 : ℝ) ^ (n - j) * Real.exp (γ * Real.sqrt (((n - j : ℕ)) : ℝ))))
        = ∑ m ∈ Finset.range (n + 1),
          ((1 / 2 : ℝ) ^ m * Real.exp (γ * Real.sqrt (((m : ℕ)) : ℝ))) := by
      rw [← Finset.sum_range_reflect
        (fun i : ℕ => ((1 / 2 : ℝ) ^ i * Real.exp (γ * Real.sqrt (((i : ℕ)) : ℝ)))) (n + 1)]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have he : n - j = (n + 1) - 1 - j := by omega
      rw [he]
    rw [hcongr]
    calc (∑ m ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ m * Real.exp (γ * Real.sqrt ((m : ℕ) : ℝ)))
        ≤ ∑ m ∈ Finset.range (n + 1), Real.exp (γ / 2) * ρ ^ m := Finset.sum_le_sum hterm
      _ = Real.exp (γ / 2) * ∑ m ∈ Finset.range (n + 1), ρ ^ m := by rw [Finset.mul_sum]
      _ ≤ Real.exp (γ / 2) * (1 - ρ)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          rw [Finset.range_eq_Ico]
          have h := geom_sum_Ico_le_of_lt_one (x := ρ) (m := 0) (n := n + 1) hρ0.le hρ1
          simpa using h
  calc (∑ j ∈ Finset.range (n + 1), (2 : ℝ) ^ j * czEpsR 1 (a * 2 ^ j))
      ≤ ∑ j ∈ Finset.range (n + 1),
          ((2 : ℝ) ^ n * czEpsR 1 (a * 2 ^ n))
            * ((1 / 2 : ℝ) ^ (n - j) * Real.exp (γ * Real.sqrt (((n - j : ℕ)) : ℝ))) :=
        Finset.sum_le_sum hstep
    _ = ((2 : ℝ) ^ n * czEpsR 1 (a * 2 ^ n))
          * ∑ j ∈ Finset.range (n + 1),
              ((1 / 2 : ℝ) ^ (n - j) * Real.exp (γ * Real.sqrt (((n - j : ℕ)) : ℝ))) := by
        rw [Finset.mul_sum]
    _ ≤ ((2 : ℝ) ^ n * czEpsR 1 (a * 2 ^ n)) * (Real.exp (γ / 2) * (1 - ρ)⁻¹) :=
        mul_le_mul_of_nonneg_left hinner (mul_nonneg (by positivity) (czEpsR_nonneg 1 _))
    _ = (Real.exp (γ / 2) * (1 - ρ)⁻¹) * (2 : ℝ) ^ n * czEpsR 1 (a * 2 ^ n) := by ring

/-! ## Scale comparison `w·R/(4y) ↔ czT` -/

lemma Dc_czTmax_le {w y : ℝ} {r : ℕ} (hw : 0 < w) (hwy : w ≤ y) (hr : 1 ≤ r)
    (hry : (r : ℝ) < y) :
    Dc 1 ⌊w / ((⌊y / (r : ℝ)⌋₊ : ℝ) + 1)⌋₊ ≤ czEpsR 1 (w / (4 * y) * (r : ℝ)) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hy0 : (0 : ℝ) < y := by linarith only [hry, hr0]
  by_cases hbig : 4 * y / w ≤ (r : ℝ)
  · have hden : (⌊y / (r : ℝ)⌋₊ : ℝ) + 1 ≤ 2 * y / (r : ℝ) := by
      have h1 : (⌊y / (r : ℝ)⌋₊ : ℝ) ≤ y / (r : ℝ) := Nat.floor_le (div_nonneg hy0.le hr0.le)
      have h2 : (1 : ℝ) ≤ y / (r : ℝ) := by rw [le_div_iff₀ hr0]; linarith only [hry]
      have h3 : y / (r : ℝ) + y / (r : ℝ) = 2 * y / (r : ℝ) := by ring
      linarith only [h1, h2, h3]
    have hdiv : w / (2 * y / (r : ℝ)) ≤ w / ((⌊y / (r : ℝ)⌋₊ : ℝ) + 1) :=
      div_le_div_of_nonneg_left hw.le (by positivity) hden
    have hwr : w / (2 * y / (r : ℝ)) = w * (r : ℝ) / (2 * y) := by field_simp; try ring
    rw [hwr] at hdiv
    have hfloor : w * (r : ℝ) / (2 * y) - 1 < (⌊w / ((⌊y / (r : ℝ)⌋₊ : ℝ) + 1)⌋₊ : ℝ) := by
      have h := Nat.lt_floor_add_one (w / ((⌊y / (r : ℝ)⌋₊ : ℝ) + 1))
      linarith only [hdiv, h]
    have hβr : w / (4 * y) * (r : ℝ) ≤ w * (r : ℝ) / (2 * y) - 1 := by
      have h1 : (1 : ℝ) ≤ w * (r : ℝ) / (4 * y) := by
        rw [le_div_iff₀ (by positivity)]
        have h2 := mul_le_mul_of_nonneg_right hbig hw.le
        rw [div_mul_cancel₀ _ (ne_of_gt hw)] at h2
        linarith only [h2]
      have h3 : w / (4 * y) * (r : ℝ) = w * (r : ℝ) / (4 * y) := by ring
      have h4 : w * (r : ℝ) / (2 * y) = 2 * (w * (r : ℝ) / (4 * y)) := by ring
      rw [h3, h4]; linarith only [h1]
    rw [Dc_eq_epsR]
    exact czEpsR_anti (by norm_num : (0:ℝ) ≤ 1) (by positivity)
      (le_of_lt (lt_of_le_of_lt hβr hfloor))
  · push Not at hbig
    have hβr1 : w / (4 * y) * (r : ℝ) < 1 := by
      have h1 : w / (4 * y) * (r : ℝ) = w * (r : ℝ) / (4 * y) := by ring
      rw [h1, div_lt_one (by positivity)]
      have h2 := mul_lt_mul_of_pos_right hbig hw
      rw [div_mul_cancel₀ _ (ne_of_gt hw)] at h2
      linarith only [h2]
    rw [czEpsR_one (by positivity : (0:ℝ) ≤ w / (4*y) * (r:ℝ)) hβr1.le]
    exact Dc_le_one (by norm_num) _

theorem czEpsScaleBound :
    ∃ K : ℝ, 0 < K ∧ ∀ (w y : ℝ) (N q : ℕ), 1 ≤ w → w ≤ y →
      czEpsR 1 (w * (czR w N q : ℝ) / (4 * y)) ≤ K * Dc 1 (czT y N q) := by
  refine ⟨Real.exp (Real.sqrt (Real.log 8)), Real.exp_pos _, ?_⟩
  intro w y N q hw hwy
  have hw0 : (0 : ℝ) < w := by linarith only [hw]
  have hy0 : (0 : ℝ) < y := by linarith only [hw, hwy]
  rcases Nat.eq_zero_or_pos q with hq0 | hq1
  · subst hq0
    have hR : czR w N 0 = 0 := by simp [czR]
    have hT : czT y N 0 = 0 := by simp [czT]
    rw [hR, hT]
    have harg : w * ((0:ℕ):ℝ) / (4 * y) = 0 := by push_cast; ring
    rw [harg]
    have h1 : czEpsR 1 (0:ℝ) = 1 := czEpsR_one le_rfl (by norm_num)
    rw [h1, Dc_eq_epsR]
    have h2 : czEpsR 1 (((0:ℕ)):ℝ) = 1 := by
      rw [show (((0:ℕ)):ℝ) = (0:ℝ) by norm_num]
      exact czEpsR_one le_rfl (by norm_num)
    rw [h2, mul_one, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (Real.sqrt_nonneg _)
  · have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq1
    have hRle : (czR w N q : ℝ) ≤ (N : ℝ) / ((q : ℝ) * w) :=
      Nat.floor_le (div_nonneg (Nat.cast_nonneg N) (by positivity))
    have hTle : (czT y N q : ℝ) ≤ (N : ℝ) / ((q : ℝ) * y) :=
      Nat.floor_le (div_nonneg (Nat.cast_nonneg N) (by positivity))
    have hRge : (N : ℝ) / ((q : ℝ) * w) - 1 ≤ (czR w N q : ℝ) := by
      have h := Nat.lt_floor_add_one ((N : ℝ) / ((q : ℝ) * w))
      have he : (⌊(N : ℝ) / ((q : ℝ) * w)⌋₊ : ℝ) = (czR w N q : ℝ) := rfl
      rw [he] at h; linarith only [h]
    have hkey : ((czT y N q : ℝ) - w / y) / 4 ≤ w * (czR w N q : ℝ) / (4 * y) := by
      have h2 : w * ((N : ℝ) / ((q : ℝ) * w) - 1) / (4 * y)
          ≤ w * (czR w N q : ℝ) / (4 * y) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hRge hw0.le
      have h3 : w * ((N : ℝ) / ((q : ℝ) * w) - 1) / (4 * y)
          = (N : ℝ) / ((q : ℝ) * y) / 4 - w / (4 * y) := by
        field_simp; try ring
      have e1 : (czT y N q : ℝ) - w / y ≤ (N : ℝ) / ((q : ℝ) * y) - w / y := by
        linarith only [hTle]
      have e4 : ((N : ℝ) / ((q : ℝ) * y) - w / y) / 4
          = (N : ℝ) / ((q : ℝ) * y) / 4 - w / (4 * y) := by ring
      linarith only [h2, h3, e1, e4, hTle]
    by_cases hcase : (4:ℝ) ≤ (czT y N q : ℝ)
    · have hA : (czT y N q : ℝ) / 8 ≤ w * (czR w N q : ℝ) / (4 * y) := by
        have h5 : (czT y N q : ℝ) / 8 ≤ ((czT y N q : ℝ) - w / y) / 4 := by
          have h6 : w / y ≤ (czT y N q : ℝ) / 2 := by
            have hwy1 : w / y ≤ 1 := by rw [div_le_one hy0]; exact hwy
            linarith only [hcase, hwy1]
          linarith only [h6]
        linarith only [hkey, h5]
      have hT8 : (0:ℝ) < (czT y N q : ℝ)/8 := by linarith only [hcase]
      have hmono : czEpsR 1 (w * (czR w N q : ℝ) / (4 * y))
          ≤ czEpsR 1 ((czT y N q : ℝ) / 8) :=
        czEpsR_anti (by norm_num : (0:ℝ) ≤ 1) hT8 hA
      refine hmono.trans ?_
      have hTpos : (0:ℝ) < (czT y N q : ℝ) := by linarith only [hcase]
      have hsplit : Real.sqrt (Real.log (czT y N q : ℝ))
          - Real.sqrt (Real.log ((czT y N q : ℝ) / 8)) ≤ Real.sqrt (Real.log 8) := by
        have hlog8 : Real.log ((czT y N q : ℝ)) - Real.log ((czT y N q : ℝ) / 8) = Real.log 8 := by
          rw [← Real.log_div (ne_of_gt hTpos) (by positivity)]
          congr 1
          field_simp
        have hloglt : Real.log ((czT y N q : ℝ) / 8) ≤ Real.log (czT y N q : ℝ) :=
          Real.log_le_log (by positivity) (by linarith only [hcase])
        have h1 := sqrt_le_sqrt_add hloglt
        rw [hlog8] at h1
        linarith only [h1]
      rw [czEpsR, Dc_eq_epsR, czEpsR, ← Real.exp_add, Real.exp_le_exp]
      linarith only [hsplit]
    · push Not at hcase
      have hcT4 : czT y N q < 4 := by exact_mod_cast hcase
      have hT3 : (czT y N q : ℝ) ≤ 3 := by
        have : czT y N q ≤ 3 := by omega
        exact_mod_cast this
      have hle : czEpsR 1 (w * (czR w N q : ℝ) / (4 * y)) ≤ 1 := by
        rw [czEpsR, Real.exp_le_one_iff]
        exact neg_nonpos.mpr (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      refine hle.trans ?_
      have hlog3 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      have hlogT : Real.log (czT y N q : ℝ) ≤ Real.log 3 := by
        rcases Nat.eq_zero_or_pos (czT y N q) with h | h
        · rw [h, Nat.cast_zero, Real.log_zero]; exact hlog3
        · exact Real.log_le_log (by exact_mod_cast h) hT3
      have hle2 : Real.sqrt (Real.log (czT y N q : ℝ)) ≤ Real.sqrt (Real.log 3) :=
        Real.sqrt_le_sqrt hlogT
      have h38 : Real.sqrt (Real.log 3) ≤ Real.sqrt (Real.log 8) :=
        Real.sqrt_le_sqrt (Real.log_le_log (by norm_num) (by norm_num))
      rw [Dc_eq_epsR, czEpsR, ← Real.exp_add]
      calc (1:ℝ) = Real.exp 0 := (Real.exp_zero).symm
        _ ≤ Real.exp (Real.sqrt (Real.log 8) + -(1 * Real.sqrt (Real.log (czT y N q : ℝ)))) :=
            Real.exp_le_exp.mpr (by linarith only [hle2, h38])

/-! ## The `σ`-weighted dyadic sum -/

lemma czSigEpsSum {Kg β Ksig : ℝ} (hKg : 0 < Kg) (hβ : 0 < β) (hKsig : 0 ≤ Ksig)
    (hgeom : ∀ (a : ℝ) (n : ℕ), 0 < a →
      (∑ j ∈ Finset.range (n + 1), (2 : ℝ) ^ j * czEpsR 1 (a * 2 ^ j))
        ≤ Kg * (2 : ℝ) ^ n * czEpsR 1 (a * 2 ^ n))
    (hsig : ∀ n : ℕ,
      (∑ r ∈ Finset.Icc (1:ℕ) n, ∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) ≤ Ksig * (n : ℝ))
    (R : ℕ) :
    (∑ r ∈ Finset.Icc (1:ℕ) R, (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * czEpsR 1 (β * (r : ℝ)))
      ≤ 4 * Ksig * Kg * ((R : ℝ) * czEpsR 1 (β * (R : ℝ))) + 1 := by
  rcases Nat.eq_zero_or_pos R with h0 | hR1
  · subst h0
    rw [show Finset.Icc (1:ℕ) (0:ℕ) = ∅ from Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add]
    norm_num
  · set J : ℕ := Nat.log 2 R + 1 with hJ
    have hRJ : R ≤ 2 ^ J := by
      rw [hJ]
      have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) R
      rw [Nat.succ_eq_add_one] at h
      omega
    have hJl : 2 ^ J ≤ 2 * R := by
      rw [hJ, pow_succ]
      have h1 : 2 ^ Nat.log 2 R ≤ R := Nat.pow_log_le_self 2 (by omega)
      omega
    have hext : (∑ r ∈ Finset.Icc (1:ℕ) R,
          (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * czEpsR 1 (β * (r : ℝ)))
        ≤ ∑ r ∈ Finset.Icc (1:ℕ) ((2:ℕ) ^ J),
          (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * czEpsR 1 (β * (r : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro r hr
        rw [Finset.mem_Icc] at hr ⊢
        exact ⟨hr.1, le_trans hr.2 hRJ⟩
      · intro r _ _
        exact mul_nonneg (Finset.sum_nonneg (fun d _ => by positivity)) (Real.exp_nonneg _)
    refine hext.trans ?_
    have hblock := sum_Icc_pow2_blocks
      (fun r => (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * czEpsR 1 (β * (r : ℝ))) J
    rw [hblock]
    have h1term : (∑ d ∈ (1:ℕ).divisors, 1 / Real.sqrt (d : ℝ)) * czEpsR 1 (β * ((1:ℕ) : ℝ)) ≤ 1 := by
      have hdiv : (1:ℕ).divisors = {1} := by decide
      rw [hdiv, Finset.sum_singleton]
      have h1 : (1:ℝ) / Real.sqrt (((1:ℕ)):ℝ) = 1 := by norm_num
      rw [h1, one_mul, czEpsR, Real.exp_le_one_iff]
      exact neg_nonpos.mpr (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    have hblocks : (∑ j ∈ Finset.range J,
          ∑ r ∈ Finset.Ioc ((2:ℕ) ^ j) ((2:ℕ) ^ (j + 1)),
            (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * czEpsR 1 (β * (r : ℝ)))
        ≤ 2 * Ksig * Kg * ((2:ℝ)^J * czEpsR 1 (β * ((2:ℝ)^J))) := by
      have hb : (∑ j ∈ Finset.range J,
            ∑ r ∈ Finset.Ioc ((2:ℕ) ^ j) ((2:ℕ) ^ (j + 1)),
              (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * czEpsR 1 (β * (r : ℝ)))
          ≤ ∑ j ∈ Finset.range J, (Ksig * (2:ℝ)^(j+1)) * czEpsR 1 (β * ((2:ℝ)^j)) := by
        apply Finset.sum_le_sum
        intro j _
        calc ∑ r ∈ Finset.Ioc ((2:ℕ) ^ j) ((2:ℕ) ^ (j + 1)),
              (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * czEpsR 1 (β * (r : ℝ))
            ≤ ∑ r ∈ Finset.Ioc ((2:ℕ) ^ j) ((2:ℕ) ^ (j + 1)),
                (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * czEpsR 1 (β * ((2:ℝ)^j)) := by
              apply Finset.sum_le_sum
              intro r hr
              have hrge : ((2:ℝ)^j) ≤ (r:ℝ) := by
                rw [Finset.mem_Ioc] at hr
                exact_mod_cast (le_of_lt hr.1)
              have h2 : β * ((2:ℝ)^j) ≤ β * (r:ℝ) :=
                mul_le_mul_of_nonneg_left hrge hβ.le
              exact mul_le_mul_of_nonneg_left
                (czEpsR_anti (by norm_num : (0:ℝ) ≤ 1) (by positivity) h2) (by positivity)
          _ = (∑ r ∈ Finset.Ioc ((2:ℕ) ^ j) ((2:ℕ) ^ (j + 1)), ∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
                * czEpsR 1 (β * ((2:ℝ)^j)) := by rw [Finset.sum_mul]
          _ ≤ (Ksig * (2:ℝ)^(j+1)) * czEpsR 1 (β * ((2:ℝ)^j)) := by
              apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
              calc (∑ r ∈ Finset.Ioc ((2:ℕ) ^ j) ((2:ℕ) ^ (j + 1)), ∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
                  ≤ ∑ r ∈ Finset.Icc (1:ℕ) ((2:ℕ) ^ (j+1)), ∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ) := by
                    apply Finset.sum_le_sum_of_subset_of_nonneg
                    · intro r hr
                      rw [Finset.mem_Ioc] at hr
                      rw [Finset.mem_Icc]
                      exact ⟨by omega, hr.2⟩
                    · intro r _ _
                      exact Finset.sum_nonneg (fun d _ => by positivity)
                _ ≤ Ksig * ((2:ℝ)^(j+1)) := by
                    have := hsig (2^(j+1))
                    simpa using this
      refine hb.trans ?_
      have hfac : (∑ j ∈ Finset.range J, (Ksig * (2:ℝ)^(j+1)) * czEpsR 1 (β * ((2:ℝ)^j)))
          = Ksig * 2 * (∑ j ∈ Finset.range J, (2:ℝ)^j * czEpsR 1 (β * ((2:ℝ)^j))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [pow_succ]; ring
      rw [hfac]
      have hg : (∑ j ∈ Finset.range J, (2:ℝ)^j * czEpsR 1 (β * ((2:ℝ)^j)))
          ≤ Kg * (2:ℝ)^J * czEpsR 1 (β * ((2:ℝ)^J)) := by
        have h1 : (∑ j ∈ Finset.range J, (2:ℝ)^j * czEpsR 1 (β * ((2:ℝ)^j)))
            ≤ ∑ j ∈ Finset.range (J + 1), (2:ℝ)^j * czEpsR 1 (β * ((2:ℝ)^j)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro j hj; rw [Finset.mem_range] at hj ⊢; omega
          · intro j _ _; exact mul_nonneg (by positivity) (czEpsR_nonneg 1 _)
        have h := hgeom β J hβ
        linarith only [h1, h]
      calc Ksig * 2 * (∑ j ∈ Finset.range J, (2:ℝ)^j * czEpsR 1 (β * ((2:ℝ)^j)))
          ≤ Ksig * 2 * (Kg * (2:ℝ)^J * czEpsR 1 (β * ((2:ℝ)^J))) :=
            mul_le_mul_of_nonneg_left hg (by positivity)
        _ = 2 * Ksig * Kg * ((2:ℝ)^J * czEpsR 1 (β * ((2:ℝ)^J))) := by ring
    have h2Jpos : (0:ℝ) < ((2:ℝ)^J) := by positivity
    have hRpos : (0:ℝ) < (R:ℝ) := by exact_mod_cast hR1
    have hrel : (2:ℝ)^J * czEpsR 1 (β * ((2:ℝ)^J)) ≤ 2 * ((R:ℝ) * czEpsR 1 (β * (R:ℝ))) := by
      have hle : β * (R:ℝ) ≤ β * ((2:ℝ)^J) := by
        apply mul_le_mul_of_nonneg_left _ hβ.le
        exact_mod_cast hRJ
      have hmono : czEpsR 1 (β * ((2:ℝ)^J)) ≤ czEpsR 1 (β * (R:ℝ)) :=
        czEpsR_anti (by norm_num : (0:ℝ) ≤ 1) (by positivity) hle
      have hle2 : ((2:ℝ)^J) ≤ 2 * (R:ℝ) := by exact_mod_cast hJl
      have heq : (2:ℝ)^J = ((2:ℝ)^J) := by push_cast; ring
      rw [heq]
      have hstep : ((2:ℝ)^J) * czEpsR 1 (β * ((2:ℝ)^J))
          ≤ (2 * (R:ℝ)) * czEpsR 1 (β * (R:ℝ)) :=
        mul_le_mul hle2 hmono (Real.exp_nonneg _) (by positivity)
      linarith only [hstep]
    have hfin : (∑ j ∈ Finset.range J,
          ∑ r ∈ Finset.Ioc ((2:ℕ) ^ j) ((2:ℕ) ^ (j + 1)),
            (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * czEpsR 1 (β * (r : ℝ)))
        ≤ 4 * Ksig * Kg * ((R:ℝ) * czEpsR 1 (β * (R:ℝ))) := by
      have h2 : (2 * Ksig * Kg) * ((2:ℝ)^J * czEpsR 1 (β * ((2:ℝ)^J)))
          ≤ (2 * Ksig * Kg) * (2 * ((R:ℝ) * czEpsR 1 (β * (R:ℝ)))) :=
        mul_le_mul_of_nonneg_left hrel (by positivity)
      have h3 : (2 * Ksig * Kg) * (2 * ((R:ℝ) * czEpsR 1 (β * (R:ℝ))))
          = 4 * Ksig * Kg * ((R:ℝ) * czEpsR 1 (β * (R:ℝ))) := by ring
      linarith only [hblocks, h2, h3]
    linarith only [h1term, hfin]

/-! ## The three sum estimates -/

theorem claim1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) → (N : ℝ) < w * y →
      (∑ q ∈ Finset.Icc (1:ℕ) (czQ y N), (1 : ℝ) / q * Dc 1 (czR w N q)) ≤ C := by
  obtain ⟨C, hC, hCd⟩ := Work.ZeroDensity.Jutila.LzDiffAux.CzHarmDecayHere 1 one_pos
  refine ⟨C, hC, ?_⟩
  intro w y N hw hwy hyN hNwy
  have hw0 : (0:ℝ) < w := by linarith only [hw]
  have hy0 : (0:ℝ) < y := by linarith only [hw, hwy]
  set A : ℝ := (N:ℝ) / w with hA
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have h1 : (1:ℝ) ≤ (N:ℝ) := le_trans (le_trans hw hwy) hyN
    linarith only [hw, hwy, hyN]
  have hApos : 0 < A := by rw [hA]; exact div_pos hNpos hw0
  have hQA : ((czQ y N : ℕ) : ℝ) ≤ A := by
    have h1 : ((czQ y N : ℕ) : ℝ) ≤ (N:ℝ) / y := by
      rw [czQ]; exact Nat.floor_le (div_nonneg (Nat.cast_nonneg N) hy0.le)
    have h2 : (N:ℝ) / y ≤ (N:ℝ) / w := div_le_div_of_nonneg_left (Nat.cast_nonneg N) hw0 hwy
    rw [hA]; linarith only [h1, h2]
  have hpt : ∀ q ∈ Finset.Icc (1:ℕ) (czQ y N),
      (1 : ℝ) / q * Dc 1 (czR w N q) ≤ (1 : ℝ) / q * czEpsR 1 ((A / 2) / q) := by
    intro q hq
    have hq0 : (0:ℝ) < (q:ℝ) := by
      have := (Finset.mem_Icc.mp hq).1
      exact_mod_cast (by omega : 0 < q)
    have hAq : czR w N q = ⌊A / q⌋₊ := by
      simp only [czR]
      congr 1
      rw [hA, div_div, mul_comm (q:ℝ) w]
    rw [hAq]
    have hx0 : 0 ≤ A / q := by positivity
    have h1 := Dc_floor_le_epsR_half (c := 1) (by norm_num : (0:ℝ) ≤ 1) hx0
    have h2 : (A / q) / 2 = (A / 2) / q := by ring
    rw [h2] at h1
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  calc (∑ q ∈ Finset.Icc (1:ℕ) (czQ y N), (1 : ℝ) / q * Dc 1 (czR w N q))
      ≤ ∑ q ∈ Finset.Icc (1:ℕ) (czQ y N), (1 : ℝ) / q * czEpsR 1 ((A / 2) / q) :=
        Finset.sum_le_sum hpt
    _ ≤ C := hCd (A / 2) (czQ y N) (by positivity) (by linarith only [hQA])

theorem claim2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ) (q : ℕ), 1 ≤ w → w ≤ y → (N : ℝ) < w * y →
      (∑ r ∈ Finset.Icc (1:ℕ) (czR w N q),
        (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
        * Dc 1 (czTmax w y N q r))
        ≤ C * (y / w + (czR w N q : ℝ) * Dc 1 (czT y N q)) := by
  obtain ⟨Kg, hKg, hgeom⟩ := czGeomDecay
  obtain ⟨Ks, hKs, hscale⟩ := czEpsScaleBound
  obtain ⟨Kσ, hKσ, hsig0⟩ := SigmaHalfAvg
  have hsig : ∀ n : ℕ,
      (∑ r ∈ Finset.Icc (1:ℕ) n, ∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) ≤ Kσ * (n:ℝ) :=
    fun n => hsig0 n
  refine ⟨Kσ + 4 * Kσ * Kg * Ks + 1, by positivity, ?_⟩
  intro w y N q hw hwy hNwy
  have hw0 : (0:ℝ) < w := by linarith only [hw]
  have hy0 : (0:ℝ) < y := by linarith only [hw, hwy]
  by_cases hq0 : q = 0
  · subst hq0
    have hR : czR w N 0 = 0 := by simp [czR]
    rw [hR, show Finset.Icc (1:ℕ) 0 = ∅ from Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    have hnn : (0:ℝ) ≤ y / w + (0 : ℝ) * Dc 1 (czT y N 0) :=
      add_nonneg (div_nonneg hy0.le hw0.le) (by simp)
    have : (0:ℝ) ≤ (Kσ + 4 * Kσ * Kg * Ks + 1) * (y / w + (0 : ℝ) * Dc 1 (czT y N 0)) :=
      mul_nonneg (by positivity) hnn
    linarith only [this]
  · have hq1 : 1 ≤ q := by omega
    have hq0' : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
    set β : ℝ := w / (4 * y) with hβdef
    have hβ0 : 0 < β := by rw [hβdef]; positivity
    have hRlt : (czR w N q : ℝ) < y := by
      have h1 : (czR w N q : ℝ) ≤ (N:ℝ) / ((q:ℝ) * w) :=
        Nat.floor_le (div_nonneg (Nat.cast_nonneg N) (by positivity))
      have h2 : (N:ℝ) / ((q:ℝ) * w) < y := by
        rw [div_lt_iff₀ (by positivity)]
        have heq : y * ((q:ℝ) * w) = (w * y) * (q:ℝ) := by ring
        rw [heq]
        have hq1' : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
        have hA : (N:ℝ) ≤ (N:ℝ) * (q:ℝ) := by
          have hh := mul_le_mul_of_nonneg_left hq1' (Nat.cast_nonneg N)
          simpa using hh
        have hB := mul_lt_mul_of_pos_right hNwy hq0'
        linarith only [hA, hB]
      linarith only [h1, h2]
    have hpt : ∀ r ∈ Finset.Icc (1:ℕ) (czR w N q),
        (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * Dc 1 (czTmax w y N q r)
          ≤ (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
            * (Dc 1 (czT y N q) + czEpsR 1 (β * (r:ℝ))) := by
      intro r hr
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      have hrle : (r:ℝ) ≤ (czR w N q : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hr).2
      have hry : (r:ℝ) < y := lt_of_le_of_lt hrle hRlt
      have hsecond := Dc_czTmax_le hw0 hwy hr1 hry
      have hβeq : β * (r:ℝ) = w / (4 * y) * (r:ℝ) := by rw [hβdef]
      have hb : Dc 1 (czTmax w y N q r) ≤ Dc 1 (czT y N q) + czEpsR 1 (β * (r:ℝ)) := by
        have hcz : czTmax w y N q r = min (czT y N q) ⌊w / ((⌊y / (r:ℝ)⌋₊ : ℝ) + 1)⌋₊ := rfl
        rw [hcz]
        rcases le_total (czT y N q) ⌊w / ((⌊y / (r:ℝ)⌋₊ : ℝ) + 1)⌋₊ with h | h
        · rw [min_eq_left h]
          exact le_add_of_nonneg_right (Real.exp_nonneg _)
        · rw [min_eq_right h, hβeq]
          exact le_trans hsecond (le_add_of_nonneg_left (Dc_pos 1 _).le)
      exact mul_le_mul_of_nonneg_left hb (Finset.sum_nonneg (fun d _ => by positivity))
    have hsigR : (∑ r ∈ Finset.Icc (1:ℕ) (czR w N q), ∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
        ≤ Kσ * (czR w N q : ℝ) := hsig (czR w N q)
    have hsum2 : (∑ r ∈ Finset.Icc (1:ℕ) (czR w N q),
          (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * czEpsR 1 (β * (r:ℝ)))
        ≤ 4 * Kσ * Kg * ((czR w N q : ℝ) * czEpsR 1 (β * (czR w N q : ℝ))) + 1 :=
      czSigEpsSum hKg hβ0 hKσ.le hgeom hsig (czR w N q)
    have hscaleR : czEpsR 1 (β * (czR w N q : ℝ)) ≤ Ks * Dc 1 (czT y N q) := by
      have h := hscale w y N q hw hwy
      have heq : β * (czR w N q : ℝ) = w * (czR w N q : ℝ) / (4 * y) := by rw [hβdef]; ring
      rw [heq]; exact h
    calc (∑ r ∈ Finset.Icc (1:ℕ) (czR w N q),
          (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * Dc 1 (czTmax w y N q r))
        ≤ ∑ r ∈ Finset.Icc (1:ℕ) (czR w N q),
            (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
              * (Dc 1 (czT y N q) + czEpsR 1 (β * (r:ℝ))) :=
          Finset.sum_le_sum hpt
      _ = Dc 1 (czT y N q)
            * (∑ r ∈ Finset.Icc (1:ℕ) (czR w N q), ∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
            + (∑ r ∈ Finset.Icc (1:ℕ) (czR w N q),
                (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * czEpsR 1 (β * (r:ℝ))) := by
          rw [show (∑ r ∈ Finset.Icc (1:ℕ) (czR w N q),
                (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
                  * (Dc 1 (czT y N q) + czEpsR 1 (β * (r:ℝ))))
              = ∑ r ∈ Finset.Icc (1:ℕ) (czR w N q),
                  ((∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * Dc 1 (czT y N q)
                    + (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * czEpsR 1 (β * (r:ℝ))) from by
                apply Finset.sum_congr rfl; intro r _; ring]
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro r _
          ring
      _ ≤ (Kσ + 4 * Kσ * Kg * Ks + 1)
            * (y / w + (czR w N q : ℝ) * Dc 1 (czT y N q)) := by
          have hDcT : 0 ≤ Dc 1 (czT y N q) := (Dc_pos 1 _).le
          have hRnn : (0:ℝ) ≤ (czR w N q : ℝ) := Nat.cast_nonneg _
          have hyw : 1 ≤ y / w := by rw [le_div_iff₀ hw0]; linarith only [hwy]
          have h1 : Dc 1 (czT y N q)
              * (∑ r ∈ Finset.Icc (1:ℕ) (czR w N q), ∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
              ≤ Dc 1 (czT y N q) * (Kσ * (czR w N q : ℝ)) :=
            mul_le_mul_of_nonneg_left hsigR hDcT
          have hmul : (czR w N q : ℝ) * czEpsR 1 (β * (czR w N q : ℝ))
              ≤ (czR w N q : ℝ) * (Ks * Dc 1 (czT y N q)) :=
            mul_le_mul_of_nonneg_left hscaleR hRnn
          have hmul2 : 4 * Kσ * Kg * ((czR w N q : ℝ) * czEpsR 1 (β * (czR w N q : ℝ)))
              ≤ 4 * Kσ * Kg * ((czR w N q : ℝ) * (Ks * Dc 1 (czT y N q))) :=
            mul_le_mul_of_nonneg_left hmul (by positivity)
          have hmid : Dc 1 (czT y N q) * (Kσ * (czR w N q : ℝ))
              + (4 * Kσ * Kg * ((czR w N q : ℝ) * (Ks * Dc 1 (czT y N q))) + 1)
              ≤ (Kσ + 4 * Kσ * Kg * Ks + 1)
                * (y / w + (czR w N q : ℝ) * Dc 1 (czT y N q)) := by
            have hRD : (0:ℝ) ≤ (czR w N q : ℝ) * Dc 1 (czT y N q) := mul_nonneg hRnn hDcT
            have hexp : (Kσ + 4 * Kσ * Kg * Ks + 1)
                * (y / w + (czR w N q : ℝ) * Dc 1 (czT y N q))
              = (Kσ + 4 * Kσ * Kg * Ks + 1) * (y / w)
                + (Kσ + 4 * Kσ * Kg * Ks + 1) * ((czR w N q : ℝ) * Dc 1 (czT y N q)) := by ring
            have hL : Dc 1 (czT y N q) * (Kσ * (czR w N q : ℝ))
                + (4 * Kσ * Kg * ((czR w N q : ℝ) * (Ks * Dc 1 (czT y N q))) + 1)
              = (Kσ + 4 * Kσ * Kg * Ks) * ((czR w N q : ℝ) * Dc 1 (czT y N q)) + 1 := by ring
            rw [hexp, hL]
            have hb4 : (0:ℝ) ≤ 4 * Kσ * Kg * Ks :=
              mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hKσ.le) hKg.le) hKs.le
            have hbig : (0:ℝ) ≤ Kσ + 4 * Kσ * Kg * Ks := by linarith only [hb4, hKσ.le, hKσ]
            have hby : (1:ℝ) ≤ (Kσ + 4 * Kσ * Kg * Ks + 1) * (y / w) := by nlinarith only [hyw, hbig, hKσ, hb4]
            have h2 : (0:ℝ) ≤ (Kσ + 4 * Kσ * Kg * Ks + 1) * ((czR w N q : ℝ) * Dc 1 (czT y N q)) :=
              mul_nonneg (by linarith only [hKσ, hb4]) hRD
            have h3 : (Kσ + 4 * Kσ * Kg * Ks) * ((czR w N q : ℝ) * Dc 1 (czT y N q))
                ≤ (Kσ + 4 * Kσ * Kg * Ks + 1) * ((czR w N q : ℝ) * Dc 1 (czT y N q)) :=
              mul_le_mul_of_nonneg_right (by linarith only []) hRD
            linarith only [hby, h2, h3, hRD]
          linarith only [h1, hsum2, hmul2, hmid]

theorem claim3 :
    ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ) (q : ℕ), 1 ≤ w → w ≤ y → (N : ℝ) < w * y →
      (∑ r ∈ Finset.Icc (1:ℕ) (czR w N q),
        (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
        * (((czTmax w y N q r : ℝ) / w) ^ 2))
        ≤ C * ((czR w N q : ℝ) ^ 3 / y ^ 2) := by
  refine ⟨6, by norm_num, ?_⟩
  intro w y N q hw hwy hNwy
  have hw0 : (0:ℝ) < w := by linarith only [hw]
  have hy0 : (0:ℝ) < y := by linarith only [hw, hwy]
  have hsigSq : (∑ r ∈ Finset.Icc (1:ℕ) (czR w N q),
        (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * (r:ℝ)^2)
      ≤ 6 * ((czR w N q : ℝ))^3 := by
    have hstep0 : (∑ r ∈ Finset.Icc (1:ℕ) (czR w N q),
          (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * (r:ℝ)^2)
        = ∑ r ∈ Finset.Icc (1:ℕ) (czR w N q), ∑ d ∈ r.divisors,
            (1 / Real.sqrt (d : ℝ)) * (r:ℝ)^2 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_mul]
    rw [hstep0, Work.ZeroDensity.Jutila.LzDiffAux.SumDivisorsIccSwap
        (fun d t => (1 / Real.sqrt (d : ℝ)) * (t : ℝ) ^ 2) (czR w N q)]
    calc ∑ d ∈ Finset.Icc (1:ℕ) (czR w N q), ∑ m ∈ Finset.Icc (1:ℕ) (czR w N q / d),
          (1 / Real.sqrt (d : ℝ)) * (((d * m : ℕ) : ℝ)) ^ 2
        = ∑ d ∈ Finset.Icc (1:ℕ) (czR w N q), (1 / Real.sqrt (d : ℝ)) * (d : ℝ) ^ 2
            * (∑ m ∈ Finset.Icc (1:ℕ) (czR w N q / d), (m : ℝ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro d _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m _
          push_cast; ring
      _ ≤ ∑ d ∈ Finset.Icc (1:ℕ) (czR w N q), (1 / Real.sqrt (d : ℝ)) * (d : ℝ) ^ 2
            * (((czR w N q / d : ℕ)) : ℝ) ^ 3 := by
          apply Finset.sum_le_sum
          intro d _
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact sum_sq_le_cube (czR w N q / d)
      _ ≤ ∑ d ∈ Finset.Icc (1:ℕ) (czR w N q), ((czR w N q : ℝ))^3
            * (1 / ((d : ℝ) * Real.sqrt (d : ℝ))) := by
          apply Finset.sum_le_sum
          intro d hd
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
          have hsd : (Real.sqrt (d:ℝ))^2 = (d:ℝ) := Real.sq_sqrt hd0.le
          have hcast : (((czR w N q / d : ℕ)) : ℝ) ≤ (czR w N q : ℝ) / (d:ℝ) := Nat.cast_div_le
          have hcube : ((((czR w N q / d : ℕ)) : ℝ)) ^ 3 ≤ ((czR w N q : ℝ) / (d:ℝ)) ^ 3 :=
            pow_le_pow_left₀ (by positivity) hcast 3
          calc (1 / Real.sqrt (d : ℝ)) * (d : ℝ) ^ 2 * ((((czR w N q / d : ℕ)) : ℝ)) ^ 3
              ≤ (1 / Real.sqrt (d : ℝ)) * (d : ℝ) ^ 2 * ((czR w N q : ℝ) / (d:ℝ)) ^ 3 :=
                mul_le_mul_of_nonneg_left hcube (by positivity)
            _ = ((czR w N q : ℝ))^3 * (1 / ((d : ℝ) * Real.sqrt (d : ℝ))) := by
                have hd0' : (d:ℝ) ≠ 0 := ne_of_gt hd0
                have hs0 : Real.sqrt (d:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd0)
                field_simp
                try nlinarith [hsd]
      _ = ((czR w N q : ℝ))^3 * ∑ d ∈ Finset.Icc (1:ℕ) (czR w N q),
            1 / ((d : ℝ) * Real.sqrt (d : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ ((czR w N q : ℝ))^3 * 6 :=
          mul_le_mul_of_nonneg_left (Work.LinnikAreas.Density4.sum_inv_mul_sqrt_le (czR w N q))
            (by positivity)
      _ = 6 * ((czR w N q : ℝ))^3 := by ring
  have hpt : ∀ r ∈ Finset.Icc (1:ℕ) (czR w N q),
      (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * (((czTmax w y N q r : ℝ) / w) ^ 2)
        ≤ (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * ((r:ℝ) / y) ^ 2 := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hr0 : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hTle : (czTmax w y N q r : ℝ) ≤ w * (r:ℝ) / y := by
      have h1 : (czTmax w y N q r : ℝ)
          ≤ (⌊w / ((⌊y / (r:ℝ)⌋₊ : ℝ) + 1)⌋₊ : ℝ) := by
        have h := min_le_right (czT y N q) ⌊w / ((⌊y / (r:ℝ)⌋₊ : ℝ) + 1)⌋₊
        unfold czTmax
        exact_mod_cast h
      have h2 : (⌊w / ((⌊y / (r:ℝ)⌋₊ : ℝ) + 1)⌋₊ : ℝ)
          ≤ w / ((⌊y / (r:ℝ)⌋₊ : ℝ) + 1) := Nat.floor_le (by positivity)
      have h3 : w / ((⌊y / (r:ℝ)⌋₊ : ℝ) + 1) ≤ w * (r:ℝ) / y := by
        have hden : y / (r:ℝ) ≤ (⌊y / (r:ℝ)⌋₊ : ℝ) + 1 := by
          have hh := Nat.lt_floor_add_one (y / (r:ℝ))
          linarith only [hh]
        have hdenpos : 0 < (⌊y / (r:ℝ)⌋₊ : ℝ) + 1 := by positivity
        rw [div_le_div_iff₀ hdenpos hy0]
        have h4 : y ≤ ((⌊y / (r:ℝ)⌋₊ : ℝ) + 1) * (r:ℝ) := by
          have h5 := mul_le_mul_of_nonneg_right hden hr0.le
          rw [div_mul_cancel₀] at h5
          · linarith only [h5]
          · exact ne_of_gt hr0
        nlinarith only [h4, hw0.le, hw]
      linarith only [h1, h2, h3]
    have hTy : (czTmax w y N q r : ℝ) * y ≤ w * (r:ℝ) := by
      have hh := mul_le_mul_of_nonneg_right hTle hy0.le
      rw [div_mul_cancel₀ _ (ne_of_gt hy0)] at hh
      linarith only [hh]
    have hle : ((czTmax w y N q r : ℝ) / w) ^ 2 ≤ ((r:ℝ) / y) ^ 2 := by
      have h1 : (czTmax w y N q r : ℝ) / w ≤ (r:ℝ) / y := by
        rw [div_le_div_iff₀ hw0 hy0]; linarith only [hTy]
      have h2 : (0:ℝ) ≤ (czTmax w y N q r : ℝ) / w := by positivity
      have h3 : (0:ℝ) ≤ (r:ℝ) / y := by positivity
      nlinarith only [h1, h2, h3]
    exact mul_le_mul_of_nonneg_left hle (Finset.sum_nonneg (fun d _ => by positivity))
  calc (∑ r ∈ Finset.Icc (1:ℕ) (czR w N q),
        (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * (((czTmax w y N q r : ℝ) / w) ^ 2))
      ≤ ∑ r ∈ Finset.Icc (1:ℕ) (czR w N q),
          (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * ((r:ℝ) / y) ^ 2 :=
        Finset.sum_le_sum hpt
    _ = (1 / y^2) * (∑ r ∈ Finset.Icc (1:ℕ) (czR w N q),
          (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * (r:ℝ)^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        field_simp; try ring
    _ ≤ (1 / y^2) * (6 * ((czR w N q : ℝ))^3) :=
        mul_le_mul_of_nonneg_left hsigSq (by positivity)
    _ = 6 * ((czR w N q : ℝ) ^ 3 / y ^ 2) := by ring

theorem czRII_aux_bounds :
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  (∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N:ℝ) → (N:ℝ) < w*y →
      (∑ q ∈ Finset.Icc 1 (Work.ZeroDensity.Jutila.czQ y N), (1:ℝ)/q
        * Work.ZeroDensity.Jutila.Dc c (Work.ZeroDensity.Jutila.czR w N q)) ≤ C)
  ∧ (∀ (w y : ℝ) (N : ℕ) (q : ℕ), 1 ≤ w → w ≤ y → (N:ℝ) < w*y →
      (∑ r ∈ Finset.Icc 1 (Work.ZeroDensity.Jutila.czR w N q),
        (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
        * Work.ZeroDensity.Jutila.Dc c (Work.ZeroDensity.Jutila.BzCross.czTmax w y N q r))
        ≤ C * (y/w + (Work.ZeroDensity.Jutila.czR w N q : ℝ)
            * Work.ZeroDensity.Jutila.Dc c (Work.ZeroDensity.Jutila.czT y N q)))
  ∧ (∀ (w y : ℝ) (N : ℕ) (q : ℕ), 1 ≤ w → w ≤ y → (N:ℝ) < w*y →
      (∑ r ∈ Finset.Icc 1 (Work.ZeroDensity.Jutila.czR w N q),
        (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
        * (((Work.ZeroDensity.Jutila.BzCross.czTmax w y N q r : ℝ)/w)^2))
        ≤ C * ((Work.ZeroDensity.Jutila.czR w N q : ℝ)^3/y^2)) := by
  obtain ⟨C1, hC1, h1⟩ := claim1
  obtain ⟨C2, hC2, h2⟩ := claim2
  obtain ⟨C3, hC3, h3⟩ := claim3
  refine ⟨max (max C1 C2) C3 + 1, 1, by positivity, one_pos, ?_, ?_, ?_⟩
  · intro w y N hw hwy hyN hNwy
    refine le_trans (h1 w y N hw hwy hyN hNwy) ?_
    have hC1le : C1 ≤ max (max C1 C2) C3 + 1 := by
      have hh : C1 ≤ max (max C1 C2) C3 := le_trans (le_max_left C1 C2) (le_max_left _ C3)
      linarith only [hh]
    linarith only [hC1le]
  · intro w y N q hw hwy hNwy
    refine le_trans (h2 w y N q hw hwy hNwy) ?_
    have hnn : (0:ℝ) ≤ y/w + (czR w N q : ℝ) * Dc 1 (czT y N q) :=
      add_nonneg (div_nonneg (by linarith only [hw, hwy] : (0:ℝ) ≤ y) (by linarith only [hw] : (0:ℝ) ≤ w))
        (mul_nonneg (Nat.cast_nonneg _) (Dc_pos 1 _).le)
    have hC2le : C2 ≤ max (max C1 C2) C3 + 1 := by
      have hh : C2 ≤ max (max C1 C2) C3 := le_trans (le_max_right C1 C2) (le_max_left _ C3)
      linarith only [hh]
    exact mul_le_mul_of_nonneg_right hC2le hnn
  · intro w y N q hw hwy hNwy
    refine le_trans (h3 w y N q hw hwy hNwy) ?_
    have hnn : (0:ℝ) ≤ ((czR w N q : ℝ) ^ 3 / y ^ 2) := by positivity
    have hC3le : C3 ≤ max (max C1 C2) C3 + 1 := by
      have hh : C3 ≤ max (max C1 C2) C3 := le_max_right _ C3
      linarith only [hh]
    exact mul_le_mul_of_nonneg_right hC3le hnn

end

end Work.ZeroDensity.Jutila.BzCross
