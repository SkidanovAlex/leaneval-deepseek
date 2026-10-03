import Mathlib
import Submission.Work.FIChain.s3RemMaj
import Submission.Work.FIChain.s3Rem_fibre_pt_le
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.zc_sharp_bounds
import Submission.Work.FIChain.Yc_lower_sharp

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The scale facts

`Cm = ⌊(zc x B)^{1-η}⌋`.  With `η = 1/32` and `√x/2 ≤ zc ≤ 2√x` (`zc_sharp_bounds`) one has
`Cm ≍ x^{(5/16)·(31/32)} = x^{155/512} > x^{3/10}`, whence `x/Cm ≤ ⌈x^{7/10}⌉` — this is the
`(R′)`-level condition of `s3Rem_fibre_pt_le`. -/

lemma Cm_ge_rpow (B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (x : ℝ) ^ ((3 : ℝ) / 10) ≤ ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ) := by
  filter_upwards [zc_sharp_bounds B hB, Filter.eventually_ge_atTop 16,
    Work.FITop.FI_ev_rpow_ge_nat ((7 : ℝ) / 2560) (by norm_num)
      ((2 : ℝ) ^ ((63 : ℝ) / 32))] with x hsh hx16 hp
  obtain ⟨hlo, -⟩ := hsh
  have hx16'' : (16 : ℕ) ≤ x := by simpa using hx16
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (le_trans (by norm_num : (1:ℕ) ≤ 16) hx16'')
  have hx16' : (16 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx16''
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have h2le : (2 : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ) / 16) := by
    have h2pow : (2 : ℝ) ≤ (2 : ℝ) ^ ((5 : ℝ) / 4) := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (1 : ℝ) ≤ (5 : ℝ) / 4)
      simpa using h
    have h16 : (16 : ℝ) ^ ((5 : ℝ) / 16) = (2 : ℝ) ^ ((5 : ℝ) / 4) := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      norm_num
    calc (2 : ℝ) ≤ (2 : ℝ) ^ ((5 : ℝ) / 4) := h2pow
      _ = (16 : ℝ) ^ ((5 : ℝ) / 16) := h16.symm
      _ ≤ (x : ℝ) ^ ((5 : ℝ) / 16) := Real.rpow_le_rpow (by norm_num) hx16' (by norm_num)
  have hη : (0 : ℝ) < 1 - etac := by norm_num [etac]
  have hstep1 : ((x : ℝ) ^ ((5 : ℝ) / 16) / 2) ^ (1 - etac) ≤ (zc x B) ^ (1 - etac) :=
    Real.rpow_le_rpow (by positivity) hlo hη.le
  have hstep2 : ((x : ℝ) ^ ((5 : ℝ) / 16) / 2) ^ (1 - etac)
      = (x : ℝ) ^ ((155 : ℝ) / 512) / (2 : ℝ) ^ ((31 : ℝ) / 32) := by
    have h1 : (1 - etac : ℝ) = 31 / 32 := by norm_num [etac]
    have h2 : (5 : ℝ) / 16 * ((31 : ℝ) / 32) = (155 : ℝ) / 512 := by norm_num
    rw [h1, Real.div_rpow (x := (x : ℝ) ^ ((5 : ℝ) / 16)) (y := (2 : ℝ))
        (by positivity) (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul (x := (x : ℝ)) hxpos.le ((5 : ℝ) / 16) ((31 : ℝ) / 32), h2]
  have hstep4 : (x : ℝ) ^ ((3 : ℝ) / 10) * 2
      ≤ (x : ℝ) ^ ((155 : ℝ) / 512) / (2 : ℝ) ^ ((31 : ℝ) / 32) := by
    have hkey : (x : ℝ) ^ ((155 : ℝ) / 512)
        = (x : ℝ) ^ ((3 : ℝ) / 10) * (x : ℝ) ^ ((7 : ℝ) / 2560) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      norm_num
    have h2p : (2 : ℝ) ^ ((63 : ℝ) / 32) / (2 : ℝ) ^ ((31 : ℝ) / 32) = 2 := by
      rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      have h3 : (63 : ℝ) / 32 - (31 : ℝ) / 32 = 1 := by norm_num
      rw [h3, Real.rpow_one]
    rw [hkey]
    calc (x : ℝ) ^ ((3 : ℝ) / 10) * 2
        = (x : ℝ) ^ ((3 : ℝ) / 10)
            * ((2 : ℝ) ^ ((63 : ℝ) / 32) / (2 : ℝ) ^ ((31 : ℝ) / 32)) := by rw [h2p]
      _ = ((x : ℝ) ^ ((3 : ℝ) / 10) * (2 : ℝ) ^ ((63 : ℝ) / 32))
            / (2 : ℝ) ^ ((31 : ℝ) / 32) := by ring
      _ ≤ ((x : ℝ) ^ ((3 : ℝ) / 10) * (x : ℝ) ^ ((7 : ℝ) / 2560))
            / (2 : ℝ) ^ ((31 : ℝ) / 32) := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (x : ℝ) ^ ((3 : ℝ) / 10) * (x : ℝ) ^ ((7 : ℝ) / 2560)
            / (2 : ℝ) ^ ((31 : ℝ) / 32) := rfl
  have hstep3 : (zc x B) ^ (1 - etac) - 1 ≤ ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one ((zc x B) ^ (1 - etac))
    linarith
  have hx3 : (1 : ℝ) ≤ (x : ℝ) ^ ((3 : ℝ) / 10) :=
    Real.one_le_rpow (le_trans (by norm_num : (1 : ℝ) ≤ 16) hx16') (by norm_num)
  have hstep5 : (x : ℝ) ^ ((3 : ℝ) / 10)
      ≤ (x : ℝ) ^ ((155 : ℝ) / 512) / (2 : ℝ) ^ ((31 : ℝ) / 32) - 1 := by linarith
  linarith [hstep1, hstep2, hstep3, hstep5]

lemma x_div_Cm_le (B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (x : ℝ) / ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ)
        ≤ ((⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℕ) : ℝ) := by
  filter_upwards [Cm_ge_rpow B hB, Filter.eventually_ge_atTop 2] with x hCm hx2
  have hx2' : (2 : ℕ) ≤ x := by simpa using hx2
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (le_trans (by norm_num : (1:ℕ) ≤ 2) hx2')
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  set Cm : ℕ := ⌊(zc x B) ^ (1 - etac)⌋₊ with hCmdef
  have hCm1 : (1 : ℝ) ≤ (Cm : ℝ) :=
    le_trans (Real.one_le_rpow hx1 (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 10)) hCm
  have hCmpos : (0 : ℝ) < (Cm : ℝ) := lt_of_lt_of_le zero_lt_one hCm1
  have hxp : (0 : ℝ) < (x : ℝ) ^ ((3 : ℝ) / 10) := Real.rpow_pos_of_pos hxpos _
  have h2 : (x : ℝ) / (Cm : ℝ) ≤ (x : ℝ) / (x : ℝ) ^ ((3 : ℝ) / 10) :=
    div_le_div_of_nonneg_left hxpos.le hxp hCm
  have h3 : (x : ℝ) / (x : ℝ) ^ ((3 : ℝ) / 10) = (x : ℝ) ^ ((7 : ℝ) / 10) := by
    rw [div_eq_iff (ne_of_gt hxp), ← Real.rpow_add hxpos]
    have h4 : (7 : ℝ) / 10 + 3 / 10 = 1 := by norm_num
    rw [h4, Real.rpow_one]
  rw [h3] at h2
  exact le_trans h2 (Nat.le_ceil _)

/-! ## 2. The `y`-average is free, and the crude bound on the majorant -/

/-- Crude bound on the level integral of the majorant: `|∫_1^U s3RemMaj /u| ≤ 4·Ã(x)·(U+1)`. -/
lemma remMaj_int_abs_le (x Cm ℓ : ℕ) (z sz U : ℝ) (hU0 : 0 ≤ U)
    (hℓz : (ℓ : ℝ) * z ≤ (x : ℝ))
    (hU : U ≤ (x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ))) :
    |∫ u in (1 : ℝ)..U, s3RemMaj x Cm ℓ z sz u / u| ≤ 4 * AcountAtilC x * (U + 1) := by
  have hAnn : 0 ≤ AcountAtilC x := AcountAtilC_nonneg x
  rcases lt_or_ge U 1 with hU1 | hU1
  · have h0 : (∫ u in (1 : ℝ)..U, s3RemMaj x Cm ℓ z sz u / u) = 0 :=
      intervalIntegral_eq_zero_of_forall_lt_one
        (fun u : ℝ => s3RemMaj x Cm ℓ z sz u / u) hU1 (fun u hu => by
          have hfl : ⌊u⌋₊ = 0 := Nat.floor_eq_zero.mpr hu
          rw [s3RemMaj, hfl]
          simp)
    rw [h0, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hAnn) (by linarith)
  · have h1 : ‖∫ u in (1 : ℝ)..U, s3RemMaj x Cm ℓ z sz u / u‖
        ≤ 4 * AcountAtilC x * |U - 1| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro u hu
      rw [Real.norm_eq_abs]
      have hu1 : (1 : ℝ) ≤ u := by
        rcases Set.mem_uIoc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · linarith
        · linarith
      have huU : u ≤ U := by
        rcases Set.mem_uIoc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · linarith
        · linarith
      have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
      have hux : (ℓ : ℝ) * (Cm : ℝ) * u ≤ (x : ℝ) := by
        have h2' : u ≤ (x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)) := le_trans huU hU
        rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) ℓ) with h | h
        · rw [← h]
          simp
        rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) Cm) with hc | hc
        · rw [← hc]
          simp
        have hpos : 0 < (ℓ : ℝ) * (Cm : ℝ) := mul_pos h hc
        have h3 := (le_div_iff₀ hpos).mp h2'
        linarith
      have hm1 : ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊ ≤ x :=
        le_trans (Nat.floor_mono (min_le_right _ _)) (by simp)
      have hm2 : ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊ ≤ x :=
        le_trans (Nat.floor_mono (max_le hℓz hux)) (by simp)
      have hterm : ∀ d ∈ Finset.Icc 1 ⌊u⌋₊,
          |(|cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊|
            + |cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|)|
            ≤ 4 * AcountAtilC x := by
        intro d _
        rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))]
        have e1 := AcountAtilC_mono_nat hm1
        have e2 := AcountAtilC_mono_nat hm2
        have h1 := abs_cfR_le (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
        have h2 := abs_cfR_le (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊
        linarith
      have hcard : (Finset.Icc 1 ⌊u⌋₊).card ≤ ⌊u⌋₊ := card_Icc_one_le ⌊u⌋₊
      have hfl : ((⌊u⌋₊ : ℕ) : ℝ) ≤ u := Nat.floor_le (le_of_lt hu0)
      have hmaj : |s3RemMaj x Cm ℓ z sz u| ≤ 4 * AcountAtilC x * u := by
        rw [s3RemMaj]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        calc (∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
              |(|cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊|
                + |cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|)|)
            ≤ ∑ _d ∈ Finset.Icc 1 ⌊u⌋₊, (4 * AcountAtilC x) := Finset.sum_le_sum hterm
          _ = ((Finset.Icc 1 ⌊u⌋₊).card : ℝ) * (4 * AcountAtilC x) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ((⌊u⌋₊ : ℕ) : ℝ) * (4 * AcountAtilC x) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              exact_mod_cast hcard
          _ ≤ u * (4 * AcountAtilC x) :=
              mul_le_mul_of_nonneg_right hfl (by positivity)
          _ = 4 * AcountAtilC x * u := by ring
      rw [abs_div, abs_of_pos hu0, div_le_iff₀ hu0]
      linarith [hmaj]
    rw [Real.norm_eq_abs] at h1
    have h4 : |U - 1| ≤ U + 1 := by
      rw [abs_sub_le_iff]
      constructor <;> linarith
    calc |∫ u in (1 : ℝ)..U, s3RemMaj x Cm ℓ z sz u / u|
        ≤ 4 * AcountAtilC x * |U - 1| := h1
      _ ≤ 4 * AcountAtilC x * (U + 1) :=
            mul_le_mul_of_nonneg_left h4 (mul_nonneg (by norm_num) hAnn)

/-- **The `y`-average is free**: the `y`-dependence of `s3RemPlus` is only the divisor cut
`sy = sc·y`, so `∫_{Yc}^{e·Yc} |s3RemPlus …| /y ≤ remMajU …`. -/
lemma rem_yavg_le (lam : ℕ → ℝ) (B : ℝ) (x Cm : ℕ) (z : ℝ)
    (hlam : ∀ ν : ℕ, |lam ν| ≤ 1)
    (hCm1 : 1 ≤ Cm) (hscz : (Cm : ℝ) ≤ sc x B * z) (hYcpos : 0 < Yc x B) :
    (∫ y in Yc x B..(Real.exp 1 * Yc x B),
        |s3RemPlus lam x z (sc x B * y) (sc x B * z) Cm| / y) ≤ remMajU x Cm (sc x B) z := by
  have hab : Yc x B ≤ Real.exp 1 * Yc x B :=
    le_mul_of_one_le_left hYcpos.le (Real.one_le_exp (by norm_num))
  rw [intervalIntegral.integral_of_le hab]
  have hInt : Integrable (fun y : ℝ => remMajU x Cm (sc x B) z / y)
      (volume.restrict (Set.Ioc (Yc x B) (Real.exp 1 * Yc x B))) :=
    integrable_const_div_Ioc _ _ _ hYcpos
  refine le_trans (MeasureTheory.integral_mono_of_nonneg ?_ hInt ?_) ?_
  · exact eventually_restrict_Ioc (fun y hy =>
      div_nonneg (abs_nonneg _) (le_of_lt (lt_trans hYcpos hy.1)))
  · exact eventually_restrict_Ioc (fun y hy =>
      div_le_div_of_nonneg_right
        (abs_s3RemPlus_le_remMajU lam x Cm (sc x B) z (sc x B * y) hlam hCm1 hscz)
        (le_of_lt (lt_trans hYcpos hy.1)))
  · rw [← intervalIntegral.integral_of_le hab, intervalIntegral_const_div_eq,
      intervalIntegral_const_div_exp 1 (Yc x B) hYcpos, mul_one]

/-- Crude bound for the `z`-majorant, used for the integrability bookkeeping. -/
lemma remMajU_le_crude (x Cm : ℕ) (scf z : ℝ) (hCm1 : 1 ≤ Cm) (hz0 : 0 ≤ z)
    (hscf0 : 0 ≤ scf) :
    remMajU x Cm scf z ≤ 4 * AcountAtilC x * ((x : ℝ) + 1) * ((x : ℝ) ^ 3 + 1) := by
  have hAnn : 0 ≤ AcountAtilC x := AcountAtilC_nonneg x
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hCnn : (0 : ℝ) ≤ 4 * AcountAtilC x * ((x : ℝ) + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) hAnn) (by linarith)
  rw [remMajU]
  have hstep : ∀ ℓ ∈ Finset.Icc 1 x,
      (if (ℓ : ℝ) * z ≤ (x : ℝ) ∧ (ℓ : ℝ) ≤ ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) then
        ((ℓ.divisors.card : ℝ)) ^ 2 *
          max (∫ u in (1 : ℝ)..(min ((scf * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
            s3RemMaj x Cm ℓ z (scf * z) u / u) 0
       else 0) ≤ ((ℓ.divisors.card : ℝ)) ^ 2 * (4 * AcountAtilC x * ((x : ℝ) + 1)) := by
    intro ℓ hℓ
    rw [Finset.mem_Icc] at hℓ
    by_cases h : (ℓ : ℝ) * z ≤ (x : ℝ) ∧ (ℓ : ℝ) ≤ ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ)
    · rw [if_pos h]
      have hℓ1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ.1
      have hlc : (1 : ℝ) ≤ (ℓ : ℝ) * (Cm : ℝ) := by
        calc (1 : ℝ) = 1 * 1 := by ring
          _ ≤ (ℓ : ℝ) * (Cm : ℝ) :=
              mul_le_mul hℓ1 (by exact_mod_cast hCm1) zero_le_one (by linarith)
      have hU : min ((scf * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))
          ≤ (x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)) := min_le_right _ _
      have hℓz : (ℓ : ℝ) * z ≤ (x : ℝ) := h.1
      have hU0 : (0 : ℝ) ≤ min ((scf * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ))) :=
        le_min (div_nonneg (mul_nonneg hscf0 hz0) (by linarith))
          (div_nonneg (Nat.cast_nonneg x) (by linarith))
      have hint := remMaj_int_abs_le x Cm ℓ z (scf * z) _ hU0 hℓz hU
      have hmaxle : max (∫ u in (1 : ℝ)..(min ((scf * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
            s3RemMaj x Cm ℓ z (scf * z) u / u) 0 ≤ 4 * AcountAtilC x * ((x : ℝ) + 1) := by
        refine max_le ?_ (by linarith)
        refine le_trans (le_abs_self _) ?_
        refine le_trans hint ?_
        have hsub : (x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)) + 1 ≤ (x : ℝ) + 1 := by
          have h1 : (x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)) ≤ (x : ℝ) := by
            rw [div_le_iff₀ (by linarith : (0 : ℝ) < (ℓ : ℝ) * (Cm : ℝ))]
            nlinarith
          linarith
        have h4 : (0 : ℝ) ≤ 4 * AcountAtilC x := mul_nonneg (by norm_num) hAnn
        nlinarith [h4]
      exact mul_le_mul_of_nonneg_left hmaxle (by positivity)
    · rw [if_neg h]
      exact mul_nonneg (by positivity) hCnn
  refine le_trans (Finset.sum_le_sum hstep) ?_
  have hA : ∀ ℓ ∈ Finset.Icc 1 x, ((ℓ.divisors.card : ℝ)) ^ 2 ≤ (x : ℝ) ^ 2 := by
    intro ℓ hℓ
    rw [Finset.mem_Icc] at hℓ
    have hcard : (ℓ.divisors.card : ℝ) ≤ (ℓ : ℝ) := by
      have := Nat.card_divisors_le_self ℓ
      exact_mod_cast this
    have hℓx : (ℓ : ℝ) ≤ (x : ℝ) := by exact_mod_cast hℓ.2
    calc ((ℓ.divisors.card : ℝ)) ^ 2 ≤ ((ℓ : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hcard 2
      _ ≤ (x : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hℓx 2
  have hsum2 : ∑ ℓ ∈ Finset.Icc 1 x, ((ℓ.divisors.card : ℝ)) ^ 2 ≤ (x : ℝ) ^ 3 := by
    calc ∑ ℓ ∈ Finset.Icc 1 x, ((ℓ.divisors.card : ℝ)) ^ 2
        ≤ ∑ _ℓ ∈ Finset.Icc 1 x, (x : ℝ) ^ 2 := Finset.sum_le_sum hA
      _ = ((Finset.Icc 1 x).card : ℝ) * (x : ℝ) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (x : ℝ) * (x : ℝ) ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact_mod_cast card_Icc_one_le x
      _ = (x : ℝ) ^ 3 := by ring
  calc ∑ ℓ ∈ Finset.Icc 1 x, ((ℓ.divisors.card : ℝ)) ^ 2 * (4 * AcountAtilC x * ((x : ℝ) + 1))
      = (∑ ℓ ∈ Finset.Icc 1 x, ((ℓ.divisors.card : ℝ)) ^ 2)
          * (4 * AcountAtilC x * ((x : ℝ) + 1)) := by rw [Finset.sum_mul]
    _ ≤ (x : ℝ) ^ 3 * (4 * AcountAtilC x * ((x : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hsum2 hCnn
    _ ≤ 4 * AcountAtilC x * ((x : ℝ) + 1) * ((x : ℝ) ^ 3 + 1) := by
        have h : (x : ℝ) ^ 3 * (4 * AcountAtilC x * ((x : ℝ) + 1))
            = (4 * AcountAtilC x * ((x : ℝ) + 1)) * (x : ℝ) ^ 3 := by ring
        rw [h]
        exact mul_le_mul_of_nonneg_left (by linarith [pow_nonneg hxnn 3]) hCnn

/-! ## 3. The per-`ℓ` summand and the interchanges -/

/-- The `ℓ`-th summand of `remMajU`. -/
def remTerm (x Cm : ℕ) (scf : ℝ) (ℓ : ℕ) (z : ℝ) : ℝ :=
  if ((ℓ : ℝ) * z ≤ (x : ℝ)) ∧ ((ℓ : ℝ) ≤ ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ)) then
    ((ℓ.divisors.card : ℝ)) ^ 2 *
      max (∫ u in (1 : ℝ)..(min ((scf * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
        s3RemMaj x Cm ℓ z (scf * z) u / u) 0
   else 0

lemma remMajU_eq_sum_remTerm (x Cm : ℕ) (scf z : ℝ) :
    remMajU x Cm scf z = ∑ ℓ ∈ Finset.Icc 1 x, remTerm x Cm scf ℓ z := rfl

lemma measurable_remTerm (x Cm : ℕ) (scf : ℝ) (ℓ : ℕ) :
    Measurable (fun z : ℝ => remTerm x Cm scf ℓ z / z) := by
  have hfun : (fun z : ℝ => remTerm x Cm scf ℓ z / z) =
      (fun z : ℝ => (if ((ℓ : ℝ) * z ≤ (x : ℝ)) ∧
          ((ℓ : ℝ) ≤ ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ)) then
        ((ℓ.divisors.card : ℝ)) ^ 2 *
          max (∫ u in (1 : ℝ)..(min ((scf * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
            s3RemMaj x Cm ℓ z (scf * z) u / u) 0
       else 0) / z) := by funext z; rfl
  rw [hfun]
  refine Measurable.div ?_ measurable_id
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_le (by fun_prop : Measurable (fun z : ℝ => (ℓ : ℝ) * z))
      measurable_const).inter (measurableSet_le measurable_const
        (by fun_prop : Measurable (fun _ : ℝ => ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ))))
  · refine measurable_const.mul ?_
    exact (measurable_s3RemMajU x Cm ℓ scf).max measurable_const

lemma abs_remTerm_le (x Cm : ℕ) (scf z : ℝ) (ℓ : ℕ) (hCm1 : 1 ≤ Cm) (hℓ1 : 1 ≤ ℓ)
    (hz0 : 0 ≤ z) (hscf0 : 0 ≤ scf) :
    |remTerm x Cm scf ℓ z| ≤ ((ℓ.divisors.card : ℝ)) ^ 2 * (4 * AcountAtilC x * ((x : ℝ) + 1)) := by
  have hAnn : 0 ≤ AcountAtilC x := AcountAtilC_nonneg x
  have hCnn : (0 : ℝ) ≤ 4 * AcountAtilC x * ((x : ℝ) + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) hAnn) (by linarith)
  have hℓ1R : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ1
  have hCml : (1 : ℝ) ≤ (Cm : ℝ) := by exact_mod_cast hCm1
  have hpos : (0 : ℝ) < (ℓ : ℝ) * (Cm : ℝ) := by
    calc (0 : ℝ) < 1 * 1 := by norm_num
      _ ≤ (ℓ : ℝ) * (Cm : ℝ) := mul_le_mul hℓ1R hCml zero_le_one (by linarith)
  by_cases h : (ℓ : ℝ) * z ≤ (x : ℝ) ∧ (ℓ : ℝ) ≤ ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ)
  · rw [remTerm, if_pos h]
    rw [abs_of_nonneg (mul_nonneg (by positivity) (le_max_right _ _))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans (max_le (le_abs_self _) (abs_nonneg _)) ?_
    have hU : min ((scf * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))
        ≤ (x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)) := min_le_right _ _
    have hU0 : (0 : ℝ) ≤ min ((scf * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ))) :=
      le_min (div_nonneg (mul_nonneg hscf0 hz0) (by linarith))
        (div_nonneg (Nat.cast_nonneg x) hpos.le)
    have hint := remMaj_int_abs_le x Cm ℓ z (scf * z) _ hU0 h.1 hU
    refine le_trans hint ?_
    have hsub : (x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)) + 1 ≤ (x : ℝ) + 1 := by
      have h1 : (x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)) ≤ (x : ℝ) := by
        have h2 : (1 : ℝ) ≤ (ℓ : ℝ) * (Cm : ℝ) := by
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ (ℓ : ℝ) * (Cm : ℝ) := mul_le_mul hℓ1R hCml zero_le_one (by linarith)
        have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
        rw [div_le_iff₀ hpos]
        nlinarith
      linarith
    have h4 : (0 : ℝ) ≤ 4 * AcountAtilC x := mul_nonneg (by norm_num) hAnn
    nlinarith [h4]
  · rw [remTerm, if_neg h, abs_zero]
    exact mul_nonneg (by positivity) hCnn

/-- `∫_a^b c/y dy` is interval integrable for `0 < a ≤ b`. -/
lemma intervalIntegrable_const_div (c a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun y : ℝ => c / y) volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (integrable_const_div_Ioc c a b ha)

lemma intervalIntegrable_remTerm (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) (hCm1 : 1 ≤ Cm) (hℓ1 : 1 ≤ ℓ)
    (hsc0 : 0 ≤ sc x B) (hzcp : 0 < zc x B) (hzle : zc x B ≤ Real.exp 1 * zc x B) :
    IntervalIntegrable (fun z : ℝ => remTerm x Cm (sc x B) ℓ z / z) volume
      (zc x B) (Real.exp 1 * zc x B) := by
  refine IntervalIntegrable.mono_fun'
    (intervalIntegrable_const_div (((ℓ.divisors.card : ℝ)) ^ 2 * (4 * AcountAtilC x * ((x : ℝ) + 1)))
      (zc x B) (Real.exp 1 * zc x B) hzcp hzle) ?_ ?_
  · exact ((measurable_remTerm x Cm (sc x B) ℓ).aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  · rw [Set.uIoc_of_le hzle]
    refine eventually_restrict_Ioc (fun z hz => ?_)
    have hz0 : 0 < z := lt_of_lt_of_le hzcp hz.1.le
    change ‖remTerm x Cm (sc x B) ℓ z / z‖
        ≤ ((ℓ.divisors.card : ℝ)) ^ 2 * (4 * AcountAtilC x * ((x : ℝ) + 1)) / z
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hz0]
    rw [div_le_div_iff_of_pos_right hz0]
    exact abs_remTerm_le x Cm (sc x B) z ℓ hCm1 hℓ1 hz0.le hsc0

lemma remMajU_zavg_eq_sum (x Cm : ℕ) (B : ℝ) (hCm1 : 1 ≤ Cm)
    (hsc0 : 0 ≤ sc x B) (hzcp : 0 < zc x B) (hzle : zc x B ≤ Real.exp 1 * zc x B) :
    (∫ z in zc x B..(Real.exp 1 * zc x B), remMajU x Cm (sc x B) z / z)
      = ∑ ℓ ∈ Finset.Icc 1 x,
          ∫ z in zc x B..(Real.exp 1 * zc x B), remTerm x Cm (sc x B) ℓ z / z := by
  have hfun : (fun z : ℝ => remMajU x Cm (sc x B) z / z)
      = fun z : ℝ => ∑ ℓ ∈ Finset.Icc 1 x, remTerm x Cm (sc x B) ℓ z / z := by
    funext z
    rw [remMajU_eq_sum_remTerm, Finset.sum_div]
  rw [hfun]
  exact intervalIntegral.integral_finsetSum (s := Finset.Icc 1 x)
    (fun ℓ hℓ => intervalIntegrable_remTerm x Cm B ℓ hCm1 (Finset.mem_Icc.mp hℓ).1 hsc0 hzcp hzle)

lemma sc_pos (x : ℕ) (B : ℝ) : 0 < sc x B := by rw [sc]; positivity

lemma eventually_restrict_Icc {a b : ℝ} {P : ℝ → Prop} (h : ∀ y ∈ Set.Icc a b, P y) :
    ∀ᵐ y ∂(volume.restrict (Set.Icc a b)), P y :=
  (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall h)

/-- `|∫_1^{U} s3RemMaj /u| ≤ 4·Ã(x)·(x+1)` in the `(1.7)`-range. -/
lemma abs_int_maj_le (x Cm ℓ : ℕ) (B : ℝ) (z : ℝ) (hCm1 : 1 ≤ Cm) (hℓ1 : 1 ≤ ℓ)
    (hz0 : 0 ≤ z) (hℓz : (ℓ : ℝ) * z ≤ (x : ℝ)) :
    |∫ u in (1 : ℝ)..(min ((sc x B * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
        s3RemMaj x Cm ℓ z (sc x B * z) u / u| ≤ 4 * AcountAtilC x * ((x : ℝ) + 1) := by
  have hAnn : 0 ≤ AcountAtilC x := AcountAtilC_nonneg x
  have hCmpos : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hCm1)
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hℓ1)
  have hsc0 : (0 : ℝ) ≤ sc x B := (sc_pos x B).le
  have hU : min ((sc x B * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))
      ≤ (x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)) := min_le_right _ _
  have hU0 : (0 : ℝ) ≤ min ((sc x B * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ))) :=
    le_min (div_nonneg (mul_nonneg hsc0 hz0) hCmpos.le)
      (div_nonneg (Nat.cast_nonneg x) (mul_nonneg (Nat.cast_nonneg ℓ) hCmpos.le))
  have hint := remMaj_int_abs_le x Cm ℓ z (sc x B * z) _ hU0 hℓz hU
  refine le_trans hint ?_
  have h2 : (1 : ℝ) ≤ (ℓ : ℝ) * (Cm : ℝ) := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (ℓ : ℝ) * (Cm : ℝ) :=
          mul_le_mul (by exact_mod_cast hℓ1) (by exact_mod_cast hCm1) zero_le_one (by linarith)
  have hsub : (x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)) + 1 ≤ (x : ℝ) + 1 := by
    have h3 : (x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)) ≤ (x : ℝ) := by
      rw [div_le_iff₀ (mul_pos hℓpos hCmpos)]
      nlinarith
    linarith
  have h4 : (0 : ℝ) ≤ 4 * AcountAtilC x := mul_nonneg (by norm_num) hAnn
  nlinarith [h4]

/-- The `z`-majorant of the `ℓ`-th term of `remMajU`: its level integral with the `ℓz ≤ x`
indicator (`G (ℓz) (ℓu) = 1_{ℓz≤x}·s3RemMaj`). -/
def remMaj1 (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) (z : ℝ) : ℝ :=
  if (ℓ : ℝ) * z ≤ (x : ℝ) then
    (∫ u in (1 : ℝ)..(min ((sc x B * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
      s3RemMaj x Cm ℓ z (sc x B * z) u / u)
  else 0

lemma remMaj1_nonneg (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) (z : ℝ)
    (hzcp : 0 < zc x B) (hCm1 : 1 ≤ Cm) (hℓ1 : 1 ≤ ℓ)
    (hℓle : (ℓ : ℝ) ≤ ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ))
    (hCmzc : (Cm : ℝ) ≤ sc x B * zc x B) (hz : z ∈ Set.Icc (zc x B) (Real.exp 1 * zc x B)) :
    0 ≤ remMaj1 x Cm B ℓ z := by
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hℓ1)
  have hCmpos : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hCm1)
  have hsc0 : (0 : ℝ) ≤ sc x B := (sc_pos x B).le
  have hz0 : 0 < z := lt_of_lt_of_le hzcp hz.1
  simp only [remMaj1]
  by_cases hx : (ℓ : ℝ) * z ≤ (x : ℝ)
  · rw [if_pos hx]
    refine intervalIntegral.integral_nonneg ?_ (fun u hu => ?_)
    · refine le_min ?_ ?_
      · rw [le_div_iff₀ hCmpos, one_mul]
        calc (Cm : ℝ) ≤ sc x B * zc x B := hCmzc
          _ ≤ sc x B * z := mul_le_mul_of_nonneg_left hz.1 hsc0
      · rw [le_div_iff₀ (mul_pos hℓpos hCmpos)]
        have h4 : (ℓ : ℝ) ≤ (x : ℝ) / (Cm : ℝ) :=
          le_trans hℓle (Nat.floor_le (div_nonneg (Nat.cast_nonneg x) hCmpos.le))
        rw [le_div_iff₀ hCmpos] at h4
        linarith
    · exact div_nonneg (by rw [s3RemMaj]; exact Finset.sum_nonneg (fun d _ => by positivity))
        (le_of_lt (lt_of_lt_of_le zero_lt_one hu.1))
  · rw [if_neg hx]

/-- **The pointwise domination by the substituted integrand** for `ℓ ≤ ⌊x/Cm⌋`: the `max` of
`remTerm` is dropped because the level integral is nonnegative (`ℓ Cm ≤ x ≤ sc·z·Cm`). -/
lemma remTerm_le_remMaj1 (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) (hCm1 : 1 ≤ Cm) (hℓ1 : 1 ≤ ℓ)
    (hℓle : (ℓ : ℝ) ≤ ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ))
    (hCmzc : (Cm : ℝ) ≤ sc x B * zc x B) (hzcp : 0 < zc x B)
    {z : ℝ} (hz : z ∈ Set.Icc (zc x B) (Real.exp 1 * zc x B)) :
    remTerm x Cm (sc x B) ℓ z / z ≤ ((ℓ.divisors.card : ℝ)) ^ 2 * (remMaj1 x Cm B ℓ z / z) := by
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hℓ1)
  have hCmpos : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hCm1)
  have hsc0 : (0 : ℝ) ≤ sc x B := (sc_pos x B).le
  have hz0 : 0 < z := lt_of_lt_of_le hzcp hz.1
  have hτnn : (0 : ℝ) ≤ ((ℓ.divisors.card : ℝ)) ^ 2 := by positivity
  by_cases hx : (ℓ : ℝ) * z ≤ (x : ℝ)
  · have hU1 : (1 : ℝ) ≤ min ((sc x B * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ))) := by
      refine le_min ?_ ?_
      · rw [le_div_iff₀ hCmpos, one_mul]
        calc (Cm : ℝ) ≤ sc x B * zc x B := hCmzc
          _ ≤ sc x B * z := mul_le_mul_of_nonneg_left hz.1 hsc0
      · rw [le_div_iff₀ (mul_pos hℓpos hCmpos)]
        have h4 : (ℓ : ℝ) ≤ (x : ℝ) / (Cm : ℝ) :=
          le_trans hℓle (Nat.floor_le (div_nonneg (Nat.cast_nonneg x) hCmpos.le))
        rw [le_div_iff₀ hCmpos] at h4
        linarith
    have hI : 0 ≤ ∫ u in (1 : ℝ)..(min ((sc x B * z) / (Cm : ℝ))
          ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))), s3RemMaj x Cm ℓ z (sc x B * z) u / u := by
      refine intervalIntegral.integral_nonneg hU1 (fun u hu => ?_)
      exact div_nonneg (by rw [s3RemMaj]; exact Finset.sum_nonneg (fun d _ => by positivity))
        (le_of_lt (lt_of_lt_of_le zero_lt_one hu.1))
    rw [remTerm, if_pos ⟨hx, hℓle⟩, max_eq_left hI, remMaj1, if_pos hx]
    exact le_of_eq (by ring)
  · rw [remTerm, if_neg (fun h => hx h.1), remMaj1, if_neg hx]
    simp

lemma measurable_remMaj1 (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) :
    Measurable (fun z : ℝ => remMaj1 x Cm B ℓ z) := by
  simp only [remMaj1]
  exact Measurable.ite (measurableSet_le (by fun_prop : Measurable (fun z : ℝ => (ℓ : ℝ) * z))
    measurable_const) (measurable_s3RemMajU x Cm ℓ (sc x B)) measurable_const

lemma intervalIntegrable_remMaj1 (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) (hCm1 : 1 ≤ Cm) (hℓ1 : 1 ≤ ℓ)
    (hzcp : 0 < zc x B) (hzle : zc x B ≤ Real.exp 1 * zc x B) :
    IntervalIntegrable (fun z : ℝ => remMaj1 x Cm B ℓ z / z) volume (zc x B)
      (Real.exp 1 * zc x B) := by
  have hAnn : 0 ≤ AcountAtilC x := AcountAtilC_nonneg x
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hA : (0 : ℝ) ≤ 4 * AcountAtilC x * ((x : ℝ) + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) hAnn) (by linarith)
  have hZc : 0 < Zc x B := by
    have h := hzcp
    rw [zc] at h
    exact_mod_cast h
  have hzc1 : (1 : ℝ) ≤ zc x B := by
    rw [zc]
    exact_mod_cast hZc
  set Cst : ℝ := (4 * AcountAtilC x * ((x : ℝ) + 1)) * Real.exp 1 * zc x B with hCst
  have hexp1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hCstnn : 0 ≤ Cst := by
    rw [hCst]
    exact mul_nonneg (mul_nonneg hA (Real.exp_pos 1).le) (le_of_lt hzcp)
  refine IntervalIntegrable.mono_fun'
    (intervalIntegrable_const_div Cst (zc x B) (Real.exp 1 * zc x B) hzcp hzle) ?_ ?_
  · exact ((measurable_remMaj1 x Cm B ℓ).div measurable_id).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  · rw [Set.uIoc_of_le hzle]
    refine eventually_restrict_Ioc (fun z hz => ?_)
    have hz0 : 0 < z := lt_of_lt_of_le hzcp hz.1.le
    change ‖remMaj1 x Cm B ℓ z / z‖ ≤ Cst / z
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hz0, div_le_div_iff_of_pos_right hz0]
    rw [hCst]
    simp only [remMaj1]
    by_cases hx : (ℓ : ℝ) * z ≤ (x : ℝ)
    · rw [if_pos hx]
      have h1 : |∫ u in (1 : ℝ)..(min ((sc x B * z) / (Cm : ℝ))
            ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))), s3RemMaj x Cm ℓ z (sc x B * z) u / u|
          ≤ 4 * AcountAtilC x * ((x : ℝ) + 1) := abs_int_maj_le x Cm ℓ B z hCm1 hℓ1 hz0.le hx
      have h2 : 4 * AcountAtilC x * ((x : ℝ) + 1)
          ≤ (4 * AcountAtilC x * ((x : ℝ) + 1)) * Real.exp 1 * zc x B := by
        have h3 : (1 : ℝ) ≤ Real.exp 1 * zc x B := by
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ Real.exp 1 * zc x B := mul_le_mul hexp1 hzc1 zero_le_one (by linarith)
        nlinarith [hA, h3]
      linarith
    · rw [if_neg hx, abs_zero]
      exact hCstnn

/-- **The `§8.4` substitution for a single `ℓ`**: with `v = ℓ z`, `w = ℓ u` the two `(1.7)`-scales
become `ℓ`-free and the `z`-integral over `[zc, e zc]` is transported to `[ℓ zc, ℓ e zc]`. -/
lemma remTerm_zavg_le_sub (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) (hCm1 : 1 ≤ Cm) (hℓ1 : 1 ≤ ℓ)
    (hℓle : (ℓ : ℝ) ≤ ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ))
    (hCmzc : (Cm : ℝ) ≤ sc x B * zc x B)
    (hzcp : 0 < zc x B) (hzle : zc x B ≤ Real.exp 1 * zc x B) :
    (∫ z in zc x B..(Real.exp 1 * zc x B), remTerm x Cm (sc x B) ℓ z / z)
      ≤ ((ℓ.divisors.card : ℝ)) ^ 2 *
        ∫ v in ((ℓ : ℝ) * zc x B)..((ℓ : ℝ) * (Real.exp 1 * zc x B)),
          ∫ w in (ℓ : ℝ)..(min (sc x B * v / (Cm : ℝ)) ((x : ℝ) / (Cm : ℝ))),
            (if v ≤ (x : ℝ) then s3RemSub x Cm ℓ (sc x B) v w else 0) / (v * w) := by
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hℓ1)
  have hCmpos : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hCm1)
  set U : ℝ → ℝ := fun z => min ((sc x B * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))
    with hUdef
  set G : ℝ → ℝ → ℝ := fun v w => if v ≤ (x : ℝ) then s3RemSub x Cm ℓ (sc x B) v w else 0
    with hGdef
  have hG_maj : ∀ z u : ℝ, G ((ℓ : ℝ) * z) ((ℓ : ℝ) * u)
      = (if (ℓ : ℝ) * z ≤ (x : ℝ) then s3RemMaj x Cm ℓ z (sc x B * z) u else 0) := by
    intro z u
    simp only [hGdef]
    by_cases h : (ℓ : ℝ) * z ≤ (x : ℝ)
    · rw [if_pos h, if_pos h]
      exact s3RemSub_mul x Cm ℓ (sc x B) z u hℓpos
    · rw [if_neg h, if_neg h]
  have hMaj_eq : ∀ z : ℝ, remMaj1 x Cm B ℓ z
      = ∫ u in (1 : ℝ)..(U z), G ((ℓ : ℝ) * z) ((ℓ : ℝ) * u) / u := by
    intro z
    have hcongr : (∫ u in (1 : ℝ)..(U z), G ((ℓ : ℝ) * z) ((ℓ : ℝ) * u) / u)
        = ∫ u in (1 : ℝ)..(U z),
            (if (ℓ : ℝ) * z ≤ (x : ℝ) then s3RemMaj x Cm ℓ z (sc x B * z) u else 0) / u := by
      refine intervalIntegral.integral_congr (fun u _ => by rw [hG_maj z u])
    rw [hcongr]
    simp only [remMaj1, hUdef]
    by_cases h : (ℓ : ℝ) * z ≤ (x : ℝ)
    · rw [if_pos h]
      refine intervalIntegral.integral_congr (fun u _ => by simp only [if_pos h])
    · rw [if_neg h]
      have hz0 : (fun u : ℝ =>
          (if (ℓ : ℝ) * z ≤ (x : ℝ) then s3RemMaj x Cm ℓ z (sc x B * z) u else 0) / u)
          = fun _ : ℝ => (0 : ℝ) := by
        funext u
        rw [if_neg h, zero_div]
      rw [hz0, intervalIntegral.integral_zero]
  have hmono : (∫ z in zc x B..(Real.exp 1 * zc x B), remTerm x Cm (sc x B) ℓ z / z)
      ≤ ∫ z in zc x B..(Real.exp 1 * zc x B), ((ℓ.divisors.card : ℝ)) ^ 2 *
          (remMaj1 x Cm B ℓ z / z) := by
    refine intervalIntegral.integral_mono_ae_restrict hzle
      (intervalIntegrable_remTerm x Cm B ℓ hCm1 hℓ1 (sc_pos x B).le hzcp hzle)
      ((intervalIntegrable_remMaj1 x Cm B ℓ hCm1 hℓ1 hzcp hzle).const_mul
        (((ℓ.divisors.card : ℝ)) ^ 2)) ?_
    exact eventually_restrict_Icc (fun z hz =>
      remTerm_le_remMaj1 x Cm B ℓ hCm1 hℓ1 hℓle hCmzc hzcp hz)
  have hlim : ∀ v : ℝ, (ℓ : ℝ) * U (v / (ℓ : ℝ))
      = min (sc x B * v / (Cm : ℝ)) ((x : ℝ) / (Cm : ℝ)) := by
    intro v
    rw [hUdef]
    exact s3SplitU_mul x Cm ℓ (sc x B) v hℓpos hCmpos
  calc (∫ z in zc x B..(Real.exp 1 * zc x B), remTerm x Cm (sc x B) ℓ z / z)
      ≤ ∫ z in zc x B..(Real.exp 1 * zc x B), ((ℓ.divisors.card : ℝ)) ^ 2 *
          (remMaj1 x Cm B ℓ z / z) := hmono
    _ = ((ℓ.divisors.card : ℝ)) ^ 2 *
          ∫ z in zc x B..(Real.exp 1 * zc x B), remMaj1 x Cm B ℓ z / z :=
        intervalIntegral.integral_const_mul _ _
    _ = ((ℓ.divisors.card : ℝ)) ^ 2 *
          ∫ z in zc x B..(Real.exp 1 * zc x B),
            ∫ u in (1 : ℝ)..(U z), G ((ℓ : ℝ) * z) ((ℓ : ℝ) * u) / (z * u) := by
        congr 1
        refine intervalIntegral.integral_congr (fun z _ => ?_)
        rw [hMaj_eq z, ← intervalIntegral.integral_div]
        refine intervalIntegral.integral_congr (fun u _ => ?_)
        field_simp
    _ = ((ℓ.divisors.card : ℝ)) ^ 2 *
          ∫ v in ((ℓ : ℝ) * zc x B)..((ℓ : ℝ) * (Real.exp 1 * zc x B)),
            ∫ w in (ℓ : ℝ)..((ℓ : ℝ) * U (v / (ℓ : ℝ))), G v w / (v * w) := by
        congr 1
        exact zavg_two_subst (F := G) (a := zc x B) (b := Real.exp 1 * zc x B) (U := U)
          (ℓ := (ℓ : ℝ)) hℓpos
    _ = ((ℓ.divisors.card : ℝ)) ^ 2 *
          ∫ v in ((ℓ : ℝ) * zc x B)..((ℓ : ℝ) * (Real.exp 1 * zc x B)),
            ∫ w in (ℓ : ℝ)..(min (sc x B * v / (Cm : ℝ)) ((x : ℝ) / (Cm : ℝ))),
              G v w / (v * w) := by
        congr 1
        refine intervalIntegral.integral_congr (fun v _ => ?_)
        rw [hlim v]

/-! ## 4. The `ℓ`-sums restricted to `Icc 1 ⌊x/Cm⌋₊`, and the joint integrand -/

/-- `remMajU` is unchanged when the `ℓ`-sum is restricted to `Icc 1 ⌊x/Cm⌋₊` (for `ℓ > ⌊x/Cm⌋₊`
`remTerm` vanishes by its own indicator). -/
lemma remMajU_eq_sum_remTerm' (x Cm : ℕ) (scf z : ℝ) (hCm1 : 1 ≤ Cm) :
    remMajU x Cm scf z = ∑ ℓ ∈ Finset.Icc 1 (⌊(x : ℝ) / (Cm : ℝ)⌋₊), remTerm x Cm scf ℓ z := by
  rw [remMajU_eq_sum_remTerm]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro ℓ hℓ
    rw [Finset.mem_Icc] at hℓ ⊢
    have hCmpos : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hCm1)
    have h2 : ⌊(x : ℝ) / (Cm : ℝ)⌋₊ ≤ x := by
      have h3 := Nat.floor_le (div_nonneg (Nat.cast_nonneg x) hCmpos.le)
      have h4 : (x : ℝ) / (Cm : ℝ) ≤ (x : ℝ) := by
        rw [div_le_iff₀ hCmpos]
        nlinarith [Nat.cast_nonneg (α := ℝ) x, (by exact_mod_cast hCm1 : (1 : ℝ) ≤ (Cm : ℝ))]
      exact_mod_cast le_trans h3 h4
    exact ⟨hℓ.1, le_trans hℓ.2 h2⟩
  · intro ℓ hℓ hnot
    rw [remTerm, if_neg]
    intro hcon
    exact hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hℓ).1, by
      have : (ℓ : ℝ) ≤ (⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℝ) := hcon.2
      exact_mod_cast this⟩)

/-- The `ℓ`-summed substituted integrand with the `ℓ`-indicators; to be bounded pointwise by the
`(R′)` fibre bound `Work.FIChain.s3Rem_fibre_pt_le`. -/
def Ksub (x Cm : ℕ) (B : ℝ) (v w : ℝ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc 1 x,
    (if (ℓ : ℝ) * zc x B ≤ v ∧ v ≤ (ℓ : ℝ) * (Real.exp 1 * zc x B) ∧ (ℓ : ℝ) ≤ w ∧
        v ≤ (x : ℝ) then
      ((ℓ.divisors.card : ℝ)) ^ 2 * s3RemSub x Cm ℓ (sc x B) v w
     else 0)

/-- The `d`-sum of one `s3RemSub` is dominated by the corresponding slice of the full `(ℓ,d)`-sum
appearing in `Work.FIChain.s3Rem_fibre_pt_le`. -/
lemma s3RemSub_mul_le_fibre (x Cm ℓ : ℕ) (B : ℝ) (v w : ℝ) (hℓ1 : 1 ≤ ℓ) (hw0 : 0 ≤ w)
    (hwle : w ≤ (x : ℝ)) :
    ((ℓ.divisors.card : ℝ)) ^ 2 * s3RemSub x Cm ℓ (sc x B) v w
      ≤ ∑ d ∈ Finset.Icc 1 x,
          (if ℓ * d ≤ ⌊w⌋₊ then ((ℓ.divisors.card : ℝ)) ^ 2 *
            (|cfR (ℓ * d) ⌊min (sc x B * v) (x : ℝ)⌋₊|
              + |cfR (ℓ * d) ⌊max v ((Cm : ℝ) * w)⌋₊|) else 0) := by
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ1
  rw [s3RemSub, Finset.mul_sum]
  have hsub : Finset.Icc 1 ⌊w / (ℓ : ℝ)⌋₊ ⊆ Finset.Icc 1 x := by
    intro d hd
    rw [Finset.mem_Icc] at hd ⊢
    refine ⟨hd.1, ?_⟩
    have h1 : (d : ℝ) ≤ w / (ℓ : ℝ) :=
      le_trans (by exact_mod_cast hd.2) (Nat.floor_le (by positivity))
    have h2 := (le_div_iff₀ hℓpos).mp h1
    have hℓ1R : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ1
    have h3 : ((d : ℕ) : ℝ) ≤ (x : ℝ) :=
      by nlinarith [h2, hwle, hℓ1R, Nat.cast_nonneg (α := ℝ) d]
    exact_mod_cast h3
  have hcongr : ∀ d ∈ Finset.Icc 1 ⌊w / (ℓ : ℝ)⌋₊,
      ((ℓ.divisors.card : ℝ)) ^ 2 *
          (|cfR (ℓ * d) ⌊min (sc x B * v) (x : ℝ)⌋₊| + |cfR (ℓ * d) ⌊max v ((Cm : ℝ) * w)⌋₊|)
        = (if ℓ * d ≤ ⌊w⌋₊ then ((ℓ.divisors.card : ℝ)) ^ 2 *
            (|cfR (ℓ * d) ⌊min (sc x B * v) (x : ℝ)⌋₊|
              + |cfR (ℓ * d) ⌊max v ((Cm : ℝ) * w)⌋₊|) else 0) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    rw [if_pos]
    have h1 : (d : ℝ) ≤ w / (ℓ : ℝ) :=
      le_trans (by exact_mod_cast hd.2) (Nat.floor_le (by positivity))
    have h2 := (le_div_iff₀ hℓpos).mp h1
    have h3 : ((ℓ * d : ℕ) : ℝ) ≤ w := by push_cast; linarith
    exact_mod_cast (Nat.le_floor h3)
  calc ∑ d ∈ Finset.Icc 1 ⌊w / (ℓ : ℝ)⌋₊,
        ((ℓ.divisors.card : ℝ)) ^ 2 *
          (|cfR (ℓ * d) ⌊min (sc x B * v) (x : ℝ)⌋₊| + |cfR (ℓ * d) ⌊max v ((Cm : ℝ) * w)⌋₊|)
      = ∑ d ∈ Finset.Icc 1 ⌊w / (ℓ : ℝ)⌋₊,
          (if ℓ * d ≤ ⌊w⌋₊ then ((ℓ.divisors.card : ℝ)) ^ 2 *
            (|cfR (ℓ * d) ⌊min (sc x B * v) (x : ℝ)⌋₊|
              + |cfR (ℓ * d) ⌊max v ((Cm : ℝ) * w)⌋₊|) else 0) :=
        Finset.sum_congr rfl hcongr
    _ ≤ ∑ d ∈ Finset.Icc 1 x,
          (if ℓ * d ≤ ⌊w⌋₊ then ((ℓ.divisors.card : ℝ)) ^ 2 *
            (|cfR (ℓ * d) ⌊min (sc x B * v) (x : ℝ)⌋₊|
              + |cfR (ℓ * d) ⌊max v ((Cm : ℝ) * w)⌋₊|) else 0) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => ?_)
        by_cases hd : ℓ * d ≤ ⌊w⌋₊
        · rw [if_pos hd]; positivity
        · rw [if_neg hd]

/-- **The pointwise `(R′)` bound** on `Ksub`: for `v ≤ x`, `0 ≤ w ≤ x/Cm` the `ℓ`-summed
substituted integrand is at most `2·Ã(x)·(log x)^{-3}`. -/
lemma Ksub_le (Xf x Cm : ℕ) (B : ℝ) (v w : ℝ)
    (hf : ∀ x : ℕ, Xf ≤ x → ∀ N m₁ m₂ : ℕ,
      N ≤ ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ → m₁ ≤ x → m₂ ≤ x →
      ∀ w : ℕ → ℝ, (∀ ℓ : ℕ, 0 ≤ w ℓ) →
        (∀ ℓ : ℕ, w ℓ ≤ ((ℓ.divisors.card : ℝ)) ^ 2) →
      (∑ ℓ ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 x,
          (if ℓ * d ≤ N then w ℓ *
            (|cfR (ℓ * d) m₁| + |cfR (ℓ * d) m₂|) else 0))
        ≤ 2 * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(3 : ℤ)))
    (hXf : Xf ≤ x) (hwx : ⌊w⌋₊ ≤ ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊) (hvx : v ≤ (x : ℝ))
    (hCmw : (Cm : ℝ) * w ≤ (x : ℝ)) (hw0 : 0 ≤ w) (hwle : w ≤ (x : ℝ)) :
    Ksub x Cm B v w ≤ 2 * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(3 : ℤ)) := by
  have hm1 : ⌊min (sc x B * v) (x : ℝ)⌋₊ ≤ x :=
    le_trans (Nat.floor_mono (min_le_right _ _)) (by simp)
  have hm2 : ⌊max v ((Cm : ℝ) * w)⌋₊ ≤ x :=
    le_trans (Nat.floor_mono (max_le hvx hCmw)) (by simp)
  refine le_trans ?_ (hf x hXf ⌊w⌋₊ _ _ hwx hm1 hm2
    (fun ℓ => ((ℓ.divisors.card : ℝ)) ^ 2) (fun ℓ => by positivity) (fun ℓ => le_refl _))
  rw [Ksub]
  refine Finset.sum_le_sum (fun ℓ hℓ => ?_)
  rw [Finset.mem_Icc] at hℓ
  by_cases hcond : (ℓ : ℝ) * zc x B ≤ v ∧ v ≤ (ℓ : ℝ) * (Real.exp 1 * zc x B) ∧
      (ℓ : ℝ) ≤ w ∧ v ≤ (x : ℝ)
  · rw [if_pos hcond]
    exact s3RemSub_mul_le_fibre x Cm ℓ B v w hℓ.1 hw0 hwle
  · rw [if_neg hcond]
    exact Finset.sum_nonneg (fun d _ => by positivity)

end

end Work.FIChain
