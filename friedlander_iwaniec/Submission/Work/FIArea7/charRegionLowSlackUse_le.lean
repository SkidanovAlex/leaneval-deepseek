import Mathlib
import Submission.Work.FIArea7.Area7Regions6b
import Submission.Work.FIArea7.Area7Char6
import Submission.Work.FIArea7.WUniOmega6Pull6CharLow_aux
import Submission.Work.FIArea7.uniCharTermRegion_le
import Submission.Work.FIArea7.uniCharTermRegionUse_le

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Private copies of the region-I mass bound, denominator `2K+L_0+2`

These are the private lemmas of `Submission.Work.FIArea7.charRegionLowSlack_le` (which prove the
mass bound `sum_{(b,e)} (1/b)·sqrt(4be) <= 2X·sqrt(Z+1)` for the threshold `4be(2K+L_0+2) <= N^{d_1}`
and `Z = N^{d_1}/(2K+L_0+2)`), copied verbatim since they are `private` there. -/

private lemma useC_inv_sqrt_le_sub (x : ℝ) (hx : 1 ≤ x) :
    (Real.sqrt x)⁻¹ ≤ 2 * (Real.sqrt x - Real.sqrt (x - 1)) := by
  have hxm1 : (0:ℝ) ≤ x - 1 := by linarith
  have hsx_pos : (0:ℝ) < Real.sqrt x := Real.sqrt_pos_of_pos (by linarith)
  have hsum_pos : (0:ℝ) < Real.sqrt x + Real.sqrt (x-1) := by
    have := Real.sqrt_nonneg (x-1); linarith
  have h1 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have h2 : Real.sqrt (x-1) * Real.sqrt (x-1) = x-1 := Real.mul_self_sqrt hxm1
  have hprod : (Real.sqrt x - Real.sqrt (x-1)) * (Real.sqrt x + Real.sqrt (x-1)) = 1 := by
    nlinarith [h1, h2]
  have hdiff : Real.sqrt x - Real.sqrt (x-1) = (Real.sqrt x + Real.sqrt (x-1))⁻¹ :=
    eq_inv_of_mul_eq_one_left hprod
  rw [hdiff]
  rw [show (2:ℝ) * (Real.sqrt x + Real.sqrt (x-1))⁻¹
        = 2 / (Real.sqrt x + Real.sqrt (x-1)) by rw [div_eq_mul_inv]]
  rw [inv_eq_one_div]
  rw [div_le_div_iff₀ hsx_pos hsum_pos]
  have : Real.sqrt (x-1) ≤ Real.sqrt x := Real.sqrt_le_sqrt (by linarith)
  linarith

/-- `∑_{n=1}^{N} 1/√n ≤ 2√N`, by summing the telescoping inequality. -/
private lemma useC_sum_Icc_inv_sqrt_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (Real.sqrt ((n:ℝ)))⁻¹) ≤ 2 * Real.sqrt (N:ℝ) := by
  set f : ℕ → ℝ := fun n => 2 * Real.sqrt (n:ℝ) with hf
  have hb : ∀ n ∈ Finset.Icc 1 N, (Real.sqrt ((n:ℝ)))⁻¹ ≤ f n - f (n-1) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : 1 ≤ n := hn.1
    have hx : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    have h := useC_inv_sqrt_le_sub (n:ℝ) hx
    simp only [hf]
    have hcast : ((n-1 : ℕ) : ℝ) = (n:ℝ) - 1 := by
      rw [Nat.cast_sub hn1]; norm_num
    rw [hcast]
    linarith
  calc ∑ n ∈ Finset.Icc 1 N, (Real.sqrt ((n:ℝ)))⁻¹
      ≤ ∑ n ∈ Finset.Icc 1 N, (f n - f (n-1)) := Finset.sum_le_sum hb
    _ = ∑ k ∈ Finset.range N, (f (k+1) - f k) := by
        rw [show Finset.Icc 1 N = Finset.Ico 1 (N+1) from by
              ext k; simp [Finset.mem_Icc, Finset.mem_Ico]]
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have h1 : (1 + k : ℕ) = k + 1 := by omega
        have h2 : (k + 1 : ℕ) - 1 = k := by omega
        rw [h1, h2]
    _ = f N - f 0 := Finset.sum_range_sub f N
    _ = 2 * Real.sqrt (N:ℝ) := by simp [hf]

/-- `(1/b)·√(4be) = 2√e/√b` for `b ≥ 1`: the Möbius weight times the Cauchy–Schwarz factor. -/
private lemma useC_weight_eq_two_sqrt (b e : ℕ) (hb : 1 ≤ b) :
    (1/(b:ℝ)) * Real.sqrt (4 * (b:ℝ) * (e:ℝ))
      = 2 * Real.sqrt (e:ℝ) * (Real.sqrt (b:ℝ))⁻¹ := by
  have hb0 : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hsb : Real.sqrt (b:ℝ) * Real.sqrt (b:ℝ) = (b:ℝ) := Real.mul_self_sqrt hb0.le
  have hsbne : Real.sqrt (b:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos hb0)
  have h1 : Real.sqrt (4 * (b:ℝ) * (e:ℝ))
      = 2 * (Real.sqrt (b:ℝ) * Real.sqrt (e:ℝ)) := by
    rw [show (4:ℝ) * (b:ℝ) * (e:ℝ) = 4 * ((b:ℝ) * (e:ℝ)) by ring]
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), Real.sqrt_mul hb0.le]
    rw [show Real.sqrt (4:ℝ) = 2 by norm_num]
  rw [h1]
  have hinv : (1/(b:ℝ)) = (Real.sqrt (b:ℝ))⁻¹ * (Real.sqrt (b:ℝ))⁻¹ := by
    conv_lhs => rw [one_div, ← hsb, mul_inv]
  rw [hinv]
  calc (Real.sqrt (b:ℝ))⁻¹ * (Real.sqrt (b:ℝ))⁻¹
        * (2 * (Real.sqrt (b:ℝ) * Real.sqrt (e:ℝ)))
      = 2 * Real.sqrt (e:ℝ) * ((Real.sqrt (b:ℝ))⁻¹ * Real.sqrt (b:ℝ))
        * (Real.sqrt (b:ℝ))⁻¹ := by ring
    _ = 2 * Real.sqrt (e:ℝ) * (Real.sqrt (b:ℝ))⁻¹ := by
        rw [inv_mul_cancel₀ hsbne]; ring

/-- `2√e·2√(Z/(4e)) = 2√Z` for `Z ≥ 0`, `e > 0`. -/
private lemma useC_two_sqrt_mul_sqrt_div_four (Z e : ℝ) (hZ : 0 ≤ Z) (he : 0 < e) :
    2 * Real.sqrt e * (2 * Real.sqrt (Z / (4 * e))) = 2 * Real.sqrt Z := by
  have hkey : e * (Z / (4 * e)) = Z / 4 := by
    rw [← mul_div_assoc, mul_comm e Z, mul_div_mul_right Z 4 (ne_of_gt he)]
  have h1 : Real.sqrt e * Real.sqrt (Z / (4 * e)) = Real.sqrt (Z / 4) := by
    rw [← Real.sqrt_mul he.le, hkey]
  have h2 : Real.sqrt (Z / 4) = Real.sqrt Z / 2 := by
    rw [Real.sqrt_div hZ, show Real.sqrt (4:ℝ) = 2 by norm_num]
  calc 2 * Real.sqrt e * (2 * Real.sqrt (Z / (4 * e)))
      = 4 * (Real.sqrt e * Real.sqrt (Z / (4 * e))) := by ring
    _ = 4 * (Real.sqrt Z / 2) := by rw [h1, h2]
    _ = 2 * Real.sqrt Z := by ring

/-- **The per-`e` fibre bound, with the angular-mode slack.**  For `e ≥ 1` and `T ≥ 0`, the
`b`-sum of the weight `(1/b)√(4be)` over the `b ≤ B` with `4be(2K+L₀+2) ≤ T` is at most
`2√(T/(2K+L₀+2))`. -/
private lemma useC_inner_le {B K L₀ e : ℕ} {T : ℝ} (he : 1 ≤ e) (hT : 0 ≤ T) :
    (∑ b ∈ Finset.Icc 1 B,
        (if 4 * (b:ℝ) * (e:ℝ) * (2*(K:ℝ)+(L₀:ℝ)+2) ≤ T
          then (1/(b:ℝ)) * Real.sqrt (4 * (b:ℝ) * (e:ℝ)) else 0))
      ≤ 2 * Real.sqrt (T / (2*(K:ℝ)+(L₀:ℝ)+2)) := by
  have hDpos : (0:ℝ) < 2*(K:ℝ)+(L₀:ℝ)+2 := by positivity
  have he1 : (1:ℝ) ≤ (e:ℝ) := by exact_mod_cast he
  have he0 : (0:ℝ) < (e:ℝ) := by linarith
  have h4e : (0:ℝ) < 4*(e:ℝ) := by linarith
  have hZnn : (0:ℝ) ≤ T/(2*(K:ℝ)+(L₀:ℝ)+2) := div_nonneg hT hDpos.le
  have hMnn : (0:ℝ) ≤ T/(2*(K:ℝ)+(L₀:ℝ)+2)/(4*(e:ℝ)) := div_nonneg hZnn h4e.le
  rw [← Finset.sum_filter]
  set A : Finset ℕ := (Finset.Icc 1 B).filter
      (fun b => 4 * (b:ℝ) * (e:ℝ) * (2*(K:ℝ)+(L₀:ℝ)+2) ≤ T) with hA
  have hterm : ∀ b ∈ A,
      (1/(b:ℝ)) * Real.sqrt (4 * (b:ℝ) * (e:ℝ))
        ≤ 2 * Real.sqrt (e:ℝ) * (Real.sqrt (b:ℝ))⁻¹ := by
    intro b hb
    have hb1 : 1 ≤ b := by
      rw [hA, Finset.mem_filter, Finset.mem_Icc] at hb
      exact hb.1.1
    exact le_of_eq (useC_weight_eq_two_sqrt b e hb1)
  have hsub : A ⊆ Finset.Icc 1 ⌊T/(2*(K:ℝ)+(L₀:ℝ)+2)/(4*(e:ℝ))⌋₊ := by
    intro b hb
    rw [hA, Finset.mem_filter, Finset.mem_Icc] at hb
    obtain ⟨⟨hb1, -⟩, hbc⟩ := hb
    refine Finset.mem_Icc.mpr ⟨hb1, ?_⟩
    apply Nat.le_floor
    rw [le_div_iff₀ h4e, le_div_iff₀ hDpos]
    nlinarith [hbc]
  calc ∑ b ∈ A, (1/(b:ℝ)) * Real.sqrt (4 * (b:ℝ) * (e:ℝ))
      ≤ ∑ b ∈ A, 2 * Real.sqrt (e:ℝ) * (Real.sqrt (b:ℝ))⁻¹ := Finset.sum_le_sum hterm
    _ = 2 * Real.sqrt (e:ℝ) * ∑ b ∈ A, (Real.sqrt (b:ℝ))⁻¹ := by rw [Finset.mul_sum]
    _ ≤ 2 * Real.sqrt (e:ℝ)
          * (2 * Real.sqrt ((⌊T/(2*(K:ℝ)+(L₀:ℝ)+2)/(4*(e:ℝ))⌋₊ : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∑ b ∈ A, (Real.sqrt (b:ℝ))⁻¹
            ≤ ∑ b ∈ Finset.Icc 1 ⌊T/(2*(K:ℝ)+(L₀:ℝ)+2)/(4*(e:ℝ))⌋₊,
                (Real.sqrt (b:ℝ))⁻¹ :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ => by positivity)
          _ ≤ 2 * Real.sqrt ((⌊T/(2*(K:ℝ)+(L₀:ℝ)+2)/(4*(e:ℝ))⌋₊ : ℕ) : ℝ) :=
              useC_sum_Icc_inv_sqrt_le _
    _ ≤ 2 * Real.sqrt (e:ℝ)
          * (2 * Real.sqrt (T/(2*(K:ℝ)+(L₀:ℝ)+2)/(4*(e:ℝ)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.sqrt_le_sqrt (Nat.floor_le hMnn)
    _ = 2 * Real.sqrt (T/(2*(K:ℝ)+(L₀:ℝ)+2)) :=
        useC_two_sqrt_mul_sqrt_div_four (T/(2*(K:ℝ)+(L₀:ℝ)+2)) (e:ℝ) hZnn he0

/-- **The `(b,e)`-mass of region I of the (17.10) main term, with angular-mode slack.**  Region I
is the set of pairs `(b,e) ∈ [1, uniB Pa] × [1,X]` with `4·b·e·(2K+L₀+2) ≤ N^{δ₁}`; its total
mass `∑ (1/b)·√(4be)` costs at most `2X·√(Z+1)` with `Z = N^{δ₁}/(2K+L₀+2)`. -/
private theorem useRegionLowWeightSum_le (Pa : Work.FITop.Params) (X K L₀ : ℕ) (δ₁ : ℝ) :
    (∑ p ∈ ((Finset.Icc 1 (Work.FIArea7.uniB Pa)).product (Finset.Icc 1 X)).filter
        (fun p : ℕ × ℕ => 4 * (p.1:ℝ) * (p.2:ℝ) * (2*(K:ℝ)+(L₀:ℝ)+2) ≤ Pa.N ^ δ₁),
      (1/(p.1:ℝ)) * Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ)))
    ≤ 2 * (X:ℝ) * Real.sqrt (Pa.N ^ δ₁ / (2*(K:ℝ)+(L₀:ℝ)+2) + 1) := by
  have hNpos : (0:ℝ) < Pa.N := by linarith [Pa.hN1]
  have hT0 : (0:ℝ) ≤ Pa.N ^ δ₁ := (Real.rpow_pos_of_pos hNpos δ₁).le
  rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product, Finset.sum_comm]
  set Z : ℝ := Pa.N ^ δ₁ / (2*(K:ℝ)+(L₀:ℝ)+2) with hZdef
  have hZnn : 0 ≤ Z := by
    rw [hZdef]
    exact div_nonneg hT0 (by positivity)
  have hstep : ∀ e ∈ Finset.Icc 1 X,
      (∑ b ∈ Finset.Icc 1 (Work.FIArea7.uniB Pa),
        (if 4 * (b:ℝ) * (e:ℝ) * (2*(K:ℝ)+(L₀:ℝ)+2) ≤ Pa.N ^ δ₁
          then (1/(b:ℝ)) * Real.sqrt (4 * (b:ℝ) * (e:ℝ)) else 0))
      ≤ 2 * Real.sqrt (Z + 1) := by
    intro e he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    refine le_trans (useC_inner_le (K := K) (L₀ := L₀) (B := Work.FIArea7.uniB Pa)
      (T := Pa.N ^ δ₁) (e := e) he1 hT0) ?_
    rw [← hZdef]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by norm_num)
  refine le_trans (Finset.sum_le_sum hstep) ?_
  · rw [Finset.sum_const, nsmul_eq_mul]
    simp only [Nat.card_Icc, Nat.add_sub_cancel]
    exact le_of_eq (by ring)


theorem charRegionLowSlackUse_le : ∃ C : ℝ, 0 < C ∧
  ∀ {Pa : Work.FITop.Params} {X K L₀ : ℕ} {u : GaussianInt → ℂ} {δ₁ c₁ : ℝ},
    1 ≤ K → 0 < δ₁ → 0 < c₁ →
    (∀ (Q : ℕ) [NeZero Q] (k : ℤ) (χ : AddChar (Additive (Work.FIArea7.GaussUnit Q)) ℂ),
        (Q : ℝ) * (|(k : ℝ)| + (L₀ : ℝ) + 2) ≤ Pa.N ^ δ₁ → |(k : ℝ)| ≤ 2 * (K : ℝ) →
        ‖Work.FIArea7.uniSChar Pa Q (fun _ => 1) u k χ‖ ≤ c₁ * Pa.N ^ (1 - δ₁)) →
    ‖Work.FIArea7.charRegionLow6 Pa X K L₀ δ₁ u (fun _ => 1)‖
      ≤ C * c₁ ^ 2 * Pa.N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
          * ((X : ℝ) * Real.sqrt (Pa.N ^ δ₁ / (2 * (K : ℝ) + (L₀ : ℝ) + 2) + 1)
              + (Pa.N ^ δ₁ / (2 * (K : ℝ) + (L₀ : ℝ) + 2) + 1) ^ ((3 : ℝ) / 2)) := by
  refine ⟨100, by norm_num, ?_⟩
  intro Pa X K L₀ u δ₁ c₁ hK hδ hc hhyp
  set H : ℝ := 2 * Real.log 2 + Real.log 4 + ∑ k ∈ Work.FIArea7.evenFreq K, (1 / ((|k| : ℤ) : ℝ)) with hH
  set bnd : ℝ := c₁ ^ 2 * Pa.N ^ (2 - 2 * δ₁) with hbnd
  set Z : ℝ := Pa.N ^ δ₁ / (2 * (K:ℝ) + (L₀:ℝ) + 2) with hZ
  have hN1 : (1:ℝ) ≤ Pa.N := Pa.hN1
  have hNpos : (0:ℝ) < Pa.N := lt_of_lt_of_le zero_lt_one hN1
  have hA0 : 0 ≤ Pa.N ^ δ₁ := Real.rpow_nonneg (le_of_lt hNpos) _
  have hDpos : 0 < 2*(K:ℝ)+(L₀:ℝ)+2 := by positivity
  have hZ0 : 0 ≤ Z := by rw [hZ]; exact div_nonneg hA0 (le_of_lt hDpos)
  have hZ1 : 0 ≤ Z + 1 := by linarith
  have hbnd0 : 0 ≤ bnd := by
    rw [hbnd]; exact mul_nonneg (sq_nonneg c₁) (Real.rpow_nonneg (le_of_lt hNpos) _)
  have hH0 : 0 ≤ H := by
    rw [hH]
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h3 : 0 ≤ ∑ k ∈ Work.FIArea7.evenFreq K, (1 / ((|k| : ℤ) : ℝ)) := by
      refine Finset.sum_nonneg (fun k hk => ?_)
      have hk0 : k ≠ 0 := by
        rw [Work.FIArea7.evenFreq, Finset.mem_filter] at hk; exact hk.2.1
      have hkpos : (0:ℤ) < |k| := abs_pos.mpr hk0
      have hkposR : (0:ℝ) < ((|k| : ℤ) : ℝ) := by exact_mod_cast hkpos
      exact div_nonneg zero_le_one (le_of_lt hkposR)
    linarith
  have hHle : H ≤ 25 * Real.log ((K:ℝ)+2) := by
    rw [hH]
    have hlog2le1 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]; norm_num
    have hlogm : Real.log (2 * (K : ℝ) + 2) = Real.log 2 + Real.log ((K : ℝ) + 1) := by
      rw [show (2 * (K : ℝ) + 2) = 2 * ((K : ℝ) + 1) from by ring,
        Real.log_mul (by norm_num) (by positivity)]
    have hlogK : Real.log 2 ≤ Real.log ((K : ℝ) + 2) :=
      Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) K])
    have hlogK1 : Real.log ((K : ℝ) + 1) ≤ Real.log ((K : ℝ) + 2) :=
      Real.log_le_log (by linarith [Nat.cast_nonneg (α := ℝ) K]) (by linarith)
    have hHa := Work.FIArea7.sum_inv_abs_evenFreq_le K
    rw [hlogm] at hHa
    rw [hlog4]
    nlinarith [hHa, hlog2le1, Real.log_two_gt_d9, hlogK, hlogK1]
  have hlog1 : 1 ≤ Real.log ((K:ℝ) + 2) := by
    have h13 : (1:ℝ) ≤ Real.log 3 := by
      have := Real.log_le_log (Real.exp_pos 1) (le_of_lt Real.exp_one_lt_three)
      rwa [Real.log_exp] at this
    have h3 : (3:ℝ) ≤ (K:ℝ) + 2 := by
      have : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
      linarith
    exact le_trans h13 (Real.log_le_log (by norm_num) h3)
  have hlog0 : 0 ≤ Real.log ((K:ℝ)+2) := le_trans zero_le_one hlog1
  -- the two halves of the estimate
  have h1 : ‖Work.FIArea7.charRegionLow6 Pa X K L₀ δ₁ u (fun _ => 1)‖
      ≤ 2 * ∑ p ∈ ((Finset.Icc 1 (Work.FIArea7.uniB Pa)) ×ˢ (Finset.Icc 1 X)).filter
          (fun p : ℕ × ℕ => 4 * (p.1:ℝ) * (p.2:ℝ) * (2*(K:ℝ)+(L₀:ℝ)+2) ≤ Pa.N ^ δ₁),
          ‖Work.FIArea7.uniCharTerm Pa p.1 p.2 u K (fun _ => 1)‖ := by
    rw [Work.FIArea7.charRegionLow6, norm_mul, show ‖(2:ℂ)‖ = 2 from by norm_num]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
  have h2 : ∑ p ∈ ((Finset.Icc 1 (Work.FIArea7.uniB Pa)) ×ˢ (Finset.Icc 1 X)).filter
          (fun p : ℕ × ℕ => 4 * (p.1:ℝ) * (p.2:ℝ) * (2*(K:ℝ)+(L₀:ℝ)+2) ≤ Pa.N ^ δ₁),
          ‖Work.FIArea7.uniCharTerm Pa p.1 p.2 u K (fun _ => 1)‖
      ≤ H * bnd * (∑ p ∈ ((Finset.Icc 1 (Work.FIArea7.uniB Pa)) ×ˢ (Finset.Icc 1 X)).filter
          (fun p : ℕ × ℕ => 4 * (p.1:ℝ) * (p.2:ℝ) * (2*(K:ℝ)+(L₀:ℝ)+2) ≤ Pa.N ^ δ₁),
          (1/(p.1:ℝ)) * Real.sqrt (4*(p.1:ℝ)*(p.2:ℝ))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun p hp => ?_)
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, hp2⟩, hpred⟩ := hp
    have hb : 1 ≤ p.1 := (Finset.mem_Icc.mp hp1).1
    have he : 1 ≤ p.2 := (Finset.mem_Icc.mp hp2).1
    have key := Work.FIArea7.uniCharTermRegionUse_le Pa K L₀ u (fun _ => 1) δ₁ c₁ hδ hc hhyp hb he hpred
    calc ‖Work.FIArea7.uniCharTerm Pa p.1 p.2 u K (fun _ => 1)‖
        ≤ (1/(p.1:ℝ)) * (2*Real.log 2 + Real.log 4 + ∑ k ∈ Work.FIArea7.evenFreq K, (1/((|k|:ℤ):ℝ)))
            * Real.sqrt (4*(p.1:ℝ)*(p.2:ℝ)) * (c₁^2 * Pa.N^(2-2*δ₁)) := key
      _ = H * bnd * ((1/(p.1:ℝ)) * Real.sqrt (4*(p.1:ℝ)*(p.2:ℝ))) := by rw [hH, hbnd]; ring
  have h4 : (∑ p ∈ ((Finset.Icc 1 (Work.FIArea7.uniB Pa)) ×ˢ (Finset.Icc 1 X)).filter
          (fun p : ℕ × ℕ => 4 * (p.1:ℝ) * (p.2:ℝ) * (2*(K:ℝ)+(L₀:ℝ)+2) ≤ Pa.N ^ δ₁),
          (1/(p.1:ℝ)) * Real.sqrt (4*(p.1:ℝ)*(p.2:ℝ)))
      ≤ 2 * (X:ℝ) * Real.sqrt (Z + 1) := by
    have hh := useRegionLowWeightSum_le Pa X K L₀ δ₁
    rw [hZ]
    exact hh
  have hW0 : 0 ≤ (X:ℝ) * Real.sqrt (Z+1) := mul_nonneg (Nat.cast_nonneg X) (Real.sqrt_nonneg _)
  have hrpow0 : 0 ≤ (Z+1) ^ ((3:ℝ)/2) := Real.rpow_nonneg hZ1 _
  have hbr0 : 0 ≤ (X:ℝ) * Real.sqrt (Z+1) + (Z+1)^((3:ℝ)/2) := by linarith
  have hlogsq : Real.log ((K:ℝ)+2) ≤ (Real.log ((K:ℝ)+2))^2 := by
    nlinarith [hlog1, hlog0, mul_nonneg hlog0 (sub_nonneg.mpr hlog1)]
  calc ‖Work.FIArea7.charRegionLow6 Pa X K L₀ δ₁ u (fun _ => 1)‖
      ≤ 2 * (∑ p ∈ ((Finset.Icc 1 (Work.FIArea7.uniB Pa)) ×ˢ (Finset.Icc 1 X)).filter
          (fun p : ℕ × ℕ => 4 * (p.1:ℝ) * (p.2:ℝ) * (2*(K:ℝ)+(L₀:ℝ)+2) ≤ Pa.N ^ δ₁),
          ‖Work.FIArea7.uniCharTerm Pa p.1 p.2 u K (fun _ => 1)‖) := h1
    _ ≤ 2 * (H * bnd * (∑ p ∈ ((Finset.Icc 1 (Work.FIArea7.uniB Pa)) ×ˢ (Finset.Icc 1 X)).filter
          (fun p : ℕ × ℕ => 4 * (p.1:ℝ) * (p.2:ℝ) * (2*(K:ℝ)+(L₀:ℝ)+2) ≤ Pa.N ^ δ₁),
          (1/(p.1:ℝ)) * Real.sqrt (4*(p.1:ℝ)*(p.2:ℝ)))) := by
          exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ ≤ 2 * (H * bnd * (2 * (X:ℝ) * Real.sqrt (Z + 1))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left h4 (mul_nonneg hH0 hbnd0)
    _ = 4 * H * bnd * ((X:ℝ) * Real.sqrt (Z + 1)) := by ring
    _ ≤ 4 * (25 * Real.log ((K:ℝ)+2)) * bnd * ((X:ℝ) * Real.sqrt (Z + 1)) := by
          apply mul_le_mul_of_nonneg_right _ hW0
          apply mul_le_mul_of_nonneg_right _ hbnd0
          exact mul_le_mul_of_nonneg_left hHle (by norm_num)
    _ = 100 * Real.log ((K:ℝ)+2) * bnd * ((X:ℝ) * Real.sqrt (Z + 1)) := by ring
    _ ≤ 100 * Real.log ((K:ℝ)+2) * bnd * ((X:ℝ) * Real.sqrt (Z + 1) + (Z+1)^((3:ℝ)/2)) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (by norm_num) hlog0) hbnd0)
          linarith [hrpow0]
    _ ≤ 100 * (Real.log ((K:ℝ)+2))^2 * bnd
          * ((X:ℝ) * Real.sqrt (Z + 1) + (Z+1)^((3:ℝ)/2)) := by
          apply mul_le_mul_of_nonneg_right _ hbr0
          apply mul_le_mul_of_nonneg_right _ hbnd0
          exact mul_le_mul_of_nonneg_left hlogsq (by norm_num)
    _ = 100 * c₁ ^ 2 * Pa.N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
              * ((X : ℝ) * Real.sqrt (Pa.N ^ δ₁ / (2 * (K : ℝ) + (L₀ : ℝ) + 2) + 1)
                  + (Pa.N ^ δ₁ / (2 * (K : ℝ) + (L₀ : ℝ) + 2) + 1) ^ ((3 : ℝ) / 2)) := by
          rw [hbnd, hZ]; ring

end

end Work.FIArea7
