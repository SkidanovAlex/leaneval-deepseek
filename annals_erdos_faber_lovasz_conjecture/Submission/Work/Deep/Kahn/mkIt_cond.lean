import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.IterDefs
import Submission.Work.Deep.Kahn.GrowthBound

/-!
# `Work.Deep.Kahn.mkIt_cond`: the concrete parameters `mkIt C ε Dk` satisfy `It.Cond`

This file proves that for every `C ≥ 2`, `0 < ε ≤ 1` and every `Dk` at least the double
exponential `exp (exp (10^10 (1 + C + 1/ε + C/ε)))`, the numerical data `mkIt C ε Dk` of
`Submission/Work/Deep/Kahn/IterDefs.lean` satisfies `It.Cond Dm` for every
`Dm ≤ ((C + η⁻¹ + 1/ε + 1)^1000 + 10^1000)`.

The content is elementary real arithmetic: every numerical condition of `It.Cond` is
either immediate from the definition of `mkIt`, or has the form "an exponential dominates
a fixed power of `log Dk`", which is reduced here to the Mathlib bound
`Real.log_le_rpow_div : Real.log x ≤ x ^ μ / μ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Work.Deep.Kahn

lemma mkIt_log_le_two_rpow (x : ℝ) (hx : 0 ≤ x) : Real.log x ≤ 2 * x ^ ((1:ℝ)/2) := by
  have h := Real.log_le_rpow_div (x := x) hx (show (0:ℝ) < (1:ℝ)/2 by norm_num)
  have h2 : x ^ ((1:ℝ)/2) / ((1:ℝ)/2) = 2 * x ^ ((1:ℝ)/2) := by
    rw [div_eq_mul_inv]; ring
  rwa [h2] at h

lemma mkIt_rpow_half_le_of_le_sq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ≤ b^2) :
    a ^ ((1:ℝ)/2) ≤ b := by
  calc a ^ ((1:ℝ)/2) ≤ (b^2) ^ ((1:ℝ)/2) := Real.rpow_le_rpow ha h (by norm_num)
    _ = b := by
        rw [← Real.rpow_natCast b 2, ← Real.rpow_mul hb]
        norm_num

lemma mkIt_two_mul_pow_le_exp (L : ℝ) (hL : (10:ℝ)^10 ≤ L) :
    (2*L)^(2001:ℕ) ≤ Real.exp (L/2) := by
  have h2L : (0:ℝ) < 2*L := by norm_num; linarith
  have hnum : (2:ℝ) * 8004^2 ≤ 10^10 := by norm_num
  have hX : (2*L)^((1:ℝ)/2) ≤ L/8004 := by
    apply mkIt_rpow_half_le_of_le_sq <;> try positivity
    nlinarith only [hL, hnum, h2L]
  have hlog : Real.log (2*L) ≤ 2 * (2*L)^((1:ℝ)/2) := mkIt_log_le_two_rpow _ (by positivity)
  have hkey : (2001:ℝ) * Real.log (2*L) ≤ L/2 := by
    have h1 : (2001:ℝ) * Real.log (2*L) ≤ 2001 * (2 * (2*L)^((1:ℝ)/2)) := by
      nlinarith only [hlog]
    have h2 : (2001:ℝ) * (2 * (2*L)^((1:ℝ)/2)) ≤ 2001 * (2 * (L/8004)) := by
      nlinarith only [hX]
    have h3 : (2001:ℝ) * (2 * (L/8004)) = L/2 := by ring
    linarith only [h1, h2, h3]
  rw [← Real.log_le_iff_le_exp (pow_pos h2L 2001), Real.log_pow]
  exact hkey

lemma mkIt_Cond_mono {it : It} {Dm Dm' : ℝ} (h : it.Cond Dm') (hle : Dm ≤ Dm') : it.Cond Dm := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23⟩ := h
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
    le_trans hle h19, h20,h21,h22,h23⟩

theorem mkIt_cond_max (C : ℕ) (hC : 2 ≤ C) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (Dk : ℝ)
    (hDk : Real.exp (Real.exp (10 ^ 10 * (1 + (C : ℝ) + ε⁻¹ + (C : ℝ) * ε⁻¹))) ≤ Dk) :
    (mkIt C ε Dk).Cond (((C : ℝ) + (mkIt C ε Dk).η⁻¹ + ε⁻¹ + 1) ^ (1000 : ℕ) + 10 ^ 1000) := by
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log Dk := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = 1 + (C : ℝ) + ε⁻¹ + (C : ℝ) * ε⁻¹ := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = mkK C ε Dk := ⟨_, rfl⟩
  rw [← hsdef] at hDk
  -- ---------- basic facts ----------
  have hC0 : (0:ℝ) ≤ C := by positivity
  have hC2 : (2:ℝ) ≤ C := by exact_mod_cast hC
  have hCpos : (0:ℝ) < C := by linarith only [hC2]
  have hεinv0 : (0:ℝ) < ε⁻¹ := inv_pos.mpr hε0
  have hεinv1 : 1 ≤ ε⁻¹ := (one_le_inv₀ hε0).mpr hε1
  have hs6 : 6 ≤ s := by
    rw [hsdef]
    have hm : (2:ℝ) ≤ (C:ℝ) * ε⁻¹ := by
      have h := mul_le_mul hC2 hεinv1 (by norm_num : (0:ℝ) ≤ 1) hC0
      linarith only [h]
    linarith only [hC2, hεinv1, hm]
  have hCs : (C:ℝ) ≤ s := by
    rw [hsdef]; linarith only [hεinv0.le, mul_nonneg hC0 hεinv0.le]
  have hεinvs : ε⁻¹ ≤ s := by
    rw [hsdef]; linarith only [hC0, mul_nonneg hC0 hεinv0.le]
  have hCεs : (C:ℝ) * ε⁻¹ ≤ s := by rw [hsdef]; linarith only [hεinv0.le, hC0]
  have hexpin : 1 ≤ Real.exp (10^10 * s) := Real.one_le_exp (by positivity)
  have hexpin2 : Real.exp 1 ≤ Real.exp (Real.exp (10^10 * s)) := Real.exp_le_exp.mpr hexpin
  have hDk2 : 2 ≤ Dk := by
    have h3 : (2:ℝ) ≤ Real.exp 1 := by have hh := Real.add_one_le_exp 1; linarith only [hh]
    linarith only [hDk, hexpin2, h3]
  have hDk0 : 0 < Dk := by linarith only [hDk2]
  have hexpL : Real.exp L = Dk := by rw [hLdef]; exact Real.exp_log hDk0
  have hLbig : 10^10 * s ≤ L := by
    have h1 : Real.exp (10^10 * s) ≤ Real.log Dk := by
      have h := Real.log_le_log (Real.exp_pos (Real.exp (10^10 * s))) hDk
      rwa [Real.log_exp] at h
    have h2 : 10^10 * s ≤ Real.exp (10^10 * s) := self_le_exp (by positivity)
    linarith only [h1, h2, hLdef]
  have hL10 : (10:ℝ)^10 ≤ L := by linarith only [hLbig, hs6]
  have hL0 : (0:ℝ) < L := by linarith only [hL10]
  have hLs : s ≤ L / 10^10 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 10^10)]; linarith only [hLbig]
  have hCL : (C:ℝ) ≤ L := by linarith only [hCs, hLs, hL10]
  have hεinvL : ε⁻¹ ≤ L := by linarith only [hεinvs, hLs, hL10]
  have hεinvL10 : ε⁻¹ ≤ L / 10^10 := le_trans hεinvs hLs
  -- K
  have hKval : K = ⌈L⌉₊ + ⌈10^6 * ((C:ℝ) + 1) / ε⌉₊ + 10^6 := by
    rw [hKdef]; unfold mkK; rw [hLdef]
  have hK1 : 1 ≤ K := by rw [hKval]; omega
  have hK2 : 2 ≤ K := by rw [hKval]; omega
  have hKpos : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK1
  have hK1' : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK1
  have hKceil1 : (⌈L⌉₊ : ℝ) ≤ L + 1 := le_of_lt (Nat.ceil_lt_add_one hL0.le)
  have hKceil2 : (⌈10^6 * ((C:ℝ)+1)/ε⌉₊ : ℝ) ≤ 10^6 * ((C:ℝ)+1)/ε + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have hKfac : 10^6 * ((C:ℝ)+1)/ε ≤ 10^6 * s := by
    have h1 : 10^6 * ((C:ℝ)+1)/ε = 10^6 * (ε⁻¹ + (C:ℝ)*ε⁻¹) := by
      rw [div_eq_mul_inv]; ring
    rw [h1, hsdef]; nlinarith only [hεinv0.le, hC0]
  have hKlow : 10^6 * ((C:ℝ)+1)/ε ≤ (K:ℝ) := by
    have h1 : (⌈10^6 * ((C:ℝ)+1)/ε⌉₊ : ℝ) ≤ (K:ℝ) := by
      have h2 : ⌈10^6 * ((C:ℝ)+1)/ε⌉₊ ≤ K := by rw [hKval]; omega
      exact_mod_cast h2
    linarith only [Nat.le_ceil (10^6 * ((C:ℝ)+1)/ε), h1]
  have hKbig : (K:ℝ) ≤ 2 * L := by
    have h1 : (K:ℝ) ≤ (L + 1) + (10^6 * s + 1) + 10^6 := by
      rw [hKval]; push_cast
      linarith only [hKceil1, hKceil2, hKfac]
    have h2 : (10:ℝ)^6 + 2 ≤ 10^6 * s := by linarith only [hs6]
    linarith only [h1, h2, hLs, hL10]
  -- Di0
  have hfloor_lt : Dk < (⌊Dk⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Dk
  have hDi0ge : Dk / 2 ≤ (⌊Dk⌋₊ : ℝ) := by linarith only [hfloor_lt, hDk2]
  have hDi01 : 1 ≤ ⌊Dk⌋₊ := (Nat.one_le_floor_iff Dk).mpr (by linarith only [hDk2] : (1:ℝ) ≤ Dk)
  have hDi01' : (1:ℝ) ≤ (⌊Dk⌋₊ : ℝ) := by exact_mod_cast hDi01
  -- mkIt field values
  have hbK : (mkIt C ε Dk).K = K := by rw [mkIt_K]; exact hKdef.symm
  have hbη : (mkIt C ε Dk).η = ε / (10^6 * (K:ℝ)) := by rw [mkIt_η, ← hKdef]
  have hbγ : (mkIt C ε Dk).γ = ε / (4 * (K:ℝ)) := by rw [mkIt_γ, ← hKdef]
  have hbT : (mkIt C ε Dk).T = ⌈64 * (C:ℝ) * (K:ℝ) / (ε * (1 + ε))⌉₊ + 1 := by
    rw [mkIt_T, ← hKdef]
  have hbDi0 : (mkIt C ε Dk).Di0 = ⌊Dk⌋₊ := by rw [mkIt_Di0]
  have hbΛ0 : (mkIt C ε Dk).Λ0 = ⌈(1 + ε) * (⌊Dk⌋₊ : ℝ)⌉₊ := by rw [mkIt_Λ0]
  have hbDlow : (mkIt C ε Dk).Dlow
      = (⌊Dk⌋₊:ℝ) * Real.exp (-(34*(C:ℝ)/ε + 4)) / (20*(C:ℝ)) := by
    rw [It.Dlow_eq, mkIt_Di0, mkIt_C, mkIt_ε]
  have hbηinv : (mkIt C ε Dk).η⁻¹ = 10^6 * (K:ℝ) / ε := by
    rw [hbη, inv_div]
  -- ---------- the deep numeric bounds ----------
  have hpow2001 : (2*L)^(2001:ℕ) ≤ Real.exp (L/2) := mkIt_two_mul_pow_le_exp L hL10
  have hL2_le_pow : L^2 ≤ (2*L)^2001 := by
    have h1 : L^2 ≤ (2*L)^2 := by nlinarith only [hL10]
    have h2 : (2*L)^2 ≤ (2*L)^2001 :=
      pow_le_pow_right₀ (by linarith only [hL10] : (1:ℝ) ≤ 2*L) (by norm_num)
    linarith only [h1, h2]
  have hC_le_L2 : (C:ℝ) ≤ L^2 := by nlinarith only [hCL, hL10]
  have hεinv_le_L2 : ε⁻¹ ≤ L^2 := by nlinarith only [hεinvL, hL10]
  have hL2_ge1 : (1:ℝ) ≤ L^2 := by nlinarith only [hL10]
  have hηinv_le_L2 : (mkIt C ε Dk).η⁻¹ ≤ L^2 := by
    rw [hbηinv]
    have h1 : 10^6 * (K:ℝ) * ε⁻¹ ≤ 10^6 * (2*L) * (L/10^10) := by
      have h2 : (K:ℝ) * ε⁻¹ ≤ (2*L) * (L/10^10) :=
        mul_le_mul hKbig hεinvL10 hεinv0.le (by linarith only [hL10] : (0:ℝ) ≤ 2*L)
      nlinarith only [h2]
    have h3 : (10:ℝ)^6 * (2*L) * (L/10^10) = L^2/5000 := by ring
    have h4 : L^2/5000 ≤ L^2 := by nlinarith only [hL2_ge1]
    rw [div_eq_mul_inv]
    linarith only [h1, h3, h4]
  have hK_le_L2 : (K:ℝ) ≤ L^2 := by nlinarith only [hKbig, hL10]
  have hP_le : (C:ℝ) + (mkIt C ε Dk).η⁻¹ + ε⁻¹ + 1 ≤ 4 * L^2 := by
    nlinarith only [hC_le_L2, hηinv_le_L2, hεinv_le_L2, hL2_ge1]
  have h40C : 40 * (C:ℝ) ≤ Real.exp (L/4) := by
    have h1 : 40 * (C:ℝ) ≤ L/4 := by nlinarith only [hCs, hLs, hL10]
    have h2 : L/4 ≤ Real.exp (L/4) := self_le_exp (by positivity)
    linarith only [h1, h2]
  have hexp34 : Real.exp (34 * (C:ℝ) / ε + 4) ≤ Real.exp (L/4) := by
    apply Real.exp_le_exp.mpr
    have h1 : 34 * (C:ℝ) / ε + 4 ≤ 38 * s := by
      rw [div_eq_mul_inv]; nlinarith only [hCεs, hεinv1, hs6]
    have h2 : 38 * s ≤ L/4 := by nlinarith only [hLs, hL10]
    linarith only [h1, h2]
  have hexp_split : Real.exp (L/4) * Real.exp (L/4) = Real.exp (L/2) := by
    rw [← Real.exp_add]; ring_nf
  have hmain : 40 * (C:ℝ) * Real.exp (34 * (C:ℝ) / ε + 4) ≤ Real.exp (L/2) := by
    calc 40 * (C:ℝ) * Real.exp (34*(C:ℝ)/ε + 4)
        ≤ Real.exp (L/4) * Real.exp (L/4) :=
          mul_le_mul h40C hexp34 (Real.exp_nonneg _) (by positivity)
      _ = Real.exp (L/2) := hexp_split
  have hDlow_ge_exp : Real.exp (L/2) ≤ (mkIt C ε Dk).Dlow := by
    have hExpL : Dk = Real.exp (L/2) * Real.exp (L/2) := by
      rw [← hexpL, ← Real.exp_add]; ring_nf
    have hEmid : Real.exp (-(34*(C:ℝ)/ε + 4)) = (Real.exp (34*(C:ℝ)/ε + 4))⁻¹ := Real.exp_neg _
    have hmain' : 40 * (C:ℝ) ≤ Real.exp (L/2) * (Real.exp (34*(C:ℝ)/ε + 4))⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
      linarith only [hmain]
    have hstep1 : (Dk/2) * Real.exp (-(34*(C:ℝ)/ε + 4)) / (20*(C:ℝ))
        ≤ (⌊Dk⌋₊:ℝ) * Real.exp (-(34*(C:ℝ)/ε + 4)) / (20*(C:ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hDi0ge (Real.exp_nonneg _)
    have hstep2 : Real.exp (L/2) ≤ (Dk/2) * Real.exp (-(34*(C:ℝ)/ε + 4)) / (20*(C:ℝ)) := by
      rw [hExpL, hEmid, le_div_iff₀ (by positivity : (0:ℝ) < 20*(C:ℝ))]
      have hu2 : (0:ℝ) ≤ Real.exp (L/2)/2 := by positivity
      have h1 := mul_le_mul_of_nonneg_left hmain' hu2
      have h2 : (Real.exp (L/2)/2) * (40*(C:ℝ)) = Real.exp (L/2) * (20*(C:ℝ)) := by ring
      have h3 : (Real.exp (L/2)/2) * (Real.exp (L/2) * (Real.exp (34*(C:ℝ)/ε+4))⁻¹)
          = (Real.exp (L/2) * Real.exp (L/2) / 2) * (Real.exp (34*(C:ℝ)/ε+4))⁻¹ := by ring
      linarith only [h1, h2, h3]
    rw [hbDlow]
    exact le_trans hstep2 hstep1
  -- ---------- assembly ----------
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [mkIt_C]; exact hC
  · rw [mkIt_ε]; exact hε0
  · rw [mkIt_ε]; exact hε1
  · rw [hbK]; exact hK2
  · rw [hbη]; exact div_pos hε0 (mul_pos (by norm_num) hKpos)
  · rw [hbγ]; exact div_pos hε0 (mul_pos (by norm_num) hKpos)
  · rw [hbDi0]; exact hDi01
  · rw [hbΛ0]
    have hh : (1:ℝ) ≤ (1 + ε) * (⌊Dk⌋₊:ℝ) := by nlinarith only [hDi01', hε1, hε0]
    have h2 : (1:ℝ) ≤ ((⌈(1 + ε) * (⌊Dk⌋₊:ℝ)⌉₊ : ℕ) : ℝ) :=
      le_trans hh (Nat.le_ceil ((1 + ε) * (⌊Dk⌋₊:ℝ)))
    exact_mod_cast h2
  · rw [mkIt_C, mkIt_ε, hbK]
    calc (16:ℝ) * (C:ℝ) ≤ 10^6 * ((C:ℝ)+1) := by linarith only [hC0]
      _ = 10^6 * ((C:ℝ)+1) * 1 := by ring
      _ ≤ 10^6 * ((C:ℝ)+1) * ((1+ε)/ε) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [le_div_iff₀ hε0]; linarith only [hε0]
      _ = (1+ε) * (10^6 * ((C:ℝ)+1)/ε) := by rw [div_eq_mul_inv]; ring
      _ ≤ (1+ε) * (K:ℝ) := mul_le_mul_of_nonneg_left hKlow (by linarith only [hε0])
  · rw [mkIt_C, mkIt_ε, hbK]
    calc 2 * (2 * (C:ℝ) - 1) ≤ 10^6 * ((C:ℝ)+1) := by linarith only [hC0]
      _ ≤ ε * (10^6 * ((C:ℝ)+1)/ε) := by
            rw [div_eq_mul_inv]
            have hεε : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε0.ne'
            nlinarith only [hεε]
      _ ≤ ε * (K:ℝ) := mul_le_mul_of_nonneg_left hKlow hε0.le
  · rw [hbη, hbK]
    have hEq : 16 * (ε / (10^6 * (K:ℝ))) * (K:ℝ) = 16 * ε / 10^6 := by
      have hKne : (K:ℝ) ≠ 0 := hKpos.ne'
      field_simp
    rw [hEq, div_le_iff₀ (by norm_num : (0:ℝ) < 10^6)]
    nlinarith only [hε1, hε0]
  · rw [hbη, hbγ]
    have hEq2 : 32 * (ε / (10^6 * (K:ℝ))) = (32*ε) / (10^6 * (K:ℝ)) := by ring
    rw [hEq2, div_le_iff₀ (by positivity : (0:ℝ) < 10^6 * (K:ℝ)), div_mul_eq_mul_div,
      le_div_iff₀ (by positivity : (0:ℝ) < 4 * (K:ℝ))]
    nlinarith only [hε0, hKpos]
  · rw [mkIt_C, mkIt_ε, mkIt_b]
  · rw [mkIt_C, mkIt_ε, It.γ₁_eq, hbγ, hbT]
    obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = 64 * (C:ℝ) * (K:ℝ) / (ε * (1 + ε)) := ⟨_, rfl⟩
    rw [← hxdef]
    have hkey : 8 * (C:ℝ) / (1 + ε) = x * (ε / (4 * (K:ℝ)) / 2) := by
      rw [hxdef, div_eq_mul_inv]; field_simp; ring
    have hstep : 8 * (C:ℝ) / (1 + ε) ≤ 1 + ((⌈x⌉₊ : ℕ) : ℝ) * (ε / (4 * (K:ℝ)) / 2) := by
      have h1 : x * (ε / (4 * (K:ℝ)) / 2) ≤ ((⌈x⌉₊ : ℕ) : ℝ) * (ε / (4 * (K:ℝ)) / 2) :=
        mul_le_mul_of_nonneg_right (Nat.le_ceil x) (by positivity)
      linarith only [hkey, h1]
    have hbern : 1 + ((⌈x⌉₊ + 1 : ℕ) : ℝ) * (ε / (4 * (K:ℝ)) / 2)
        ≤ (1 + ε / (4 * (K:ℝ)) / 2) ^ (⌈x⌉₊ + 1) :=
      one_add_mul_le_pow (show (-2:ℝ) ≤ ε / (4 * (K:ℝ)) / 2 by
        have hh : (0:ℝ) ≤ ε / (4 * (K:ℝ)) / 2 := by positivity
        linarith only [hh]) (⌈x⌉₊ + 1)
    have hcast : (((⌈x⌉₊ + 1 : ℕ)) : ℝ) = ((⌈x⌉₊ : ℕ) : ℝ) + 1 := by push_cast; ring
    have hnn : 0 ≤ ε / (4 * (K:ℝ)) / 2 := by positivity
    calc 8 * (C:ℝ) / (1 + ε)
        ≤ 1 + ((⌈x⌉₊ : ℕ) : ℝ) * (ε / (4 * (K:ℝ)) / 2) := hstep
      _ ≤ 1 + (((⌈x⌉₊ + 1 : ℕ)) : ℝ) * (ε / (4 * (K:ℝ)) / 2) := by
            rw [hcast]; nlinarith only [hnn]
      _ ≤ (1 + ε / (4 * (K:ℝ)) / 2) ^ (⌈x⌉₊ + 1) := hbern
  · rw [mkIt_ε, hbDi0, hbΛ0]
    exact Nat.le_ceil _
  · rw [mkIt_C, hbDi0, hbΛ0]
    have h1 := Nat.ceil_lt_add_one (show (0:ℝ) ≤ (1+ε) * (⌊Dk⌋₊:ℝ) by positivity)
    nlinarith only [h1, hDi01', hC2, hε1]
  · rw [hbDi0, hbK]
    have h1 : Real.log ((⌊Dk⌋₊:ℝ)) ≤ Real.log Dk :=
      Real.log_le_log (by positivity) (Nat.floor_le hDk0.le)
    have h2 : Real.log Dk = L := hLdef.symm
    have h3 : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil L
    have h4 : (⌈L⌉₊ : ℝ) ≤ (K:ℝ) := by
      have h5 : ⌈L⌉₊ ≤ K := by rw [hKval]; omega
      exact_mod_cast h5
    linarith only [h1, h2, h3, h4]
  · rw [hbη, mkIt_b, mkIt_C, mkIt_ε, hbT]
    obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = 64 * (C:ℝ) * (K:ℝ) / (ε * (1 + ε)) := ⟨_, rfl⟩
    rw [← hxdef]
    have hcast : (((⌈x⌉₊ + 1 : ℕ)) : ℝ) = ((⌈x⌉₊ : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hTup : ((⌈x⌉₊ : ℕ) : ℝ) + 1 ≤ x + 2 := by
      have hh := Nat.ceil_lt_add_one (show (0:ℝ) ≤ x by rw [hxdef]; positivity)
      linarith only [hh]
    have hfac0 : 0 ≤ 8 * (ε / (10^6 * (K:ℝ))) := by positivity
    have hb1 : 8 * (ε / (10^6 * (K:ℝ))) * (((⌈x⌉₊ : ℕ) : ℝ) + 1)
        ≤ 8 * (ε / (10^6 * (K:ℝ))) * (x + 2) := mul_le_mul_of_nonneg_left hTup hfac0
    have hb2 : 8 * (ε / (10^6 * (K:ℝ))) * (x + 2)
        = 512 * (C:ℝ) / (10^6 * (1 + ε)) + 16 * ε / (10^6 * (K:ℝ)) := by
      rw [hxdef, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      have hKne : (K:ℝ) ≠ 0 := hKpos.ne'
      field_simp
      try ring
    have hb3 : 512 * (C:ℝ) / (10^6 * (1 + ε)) ≤ 2 * (C:ℝ) / ε := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 10^6 * (1 + ε)), div_mul_eq_mul_div,
        le_div_iff₀ hε0]
      nlinarith only [hε1, hC0, hε0]
    have hb4 : 16 * ε / (10^6 * (K:ℝ)) ≤ 3 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 10^6 * (K:ℝ))]
      nlinarith only [hε1, hε0, hK1']
    have hstep1 : 8 * (ε / (10^6 * (K:ℝ))) * (((⌈x⌉₊ : ℕ) : ℝ) + 1) ≤ 2 * (C:ℝ)/ε + 3 := by
      calc 8 * (ε / (10^6 * (K:ℝ))) * (((⌈x⌉₊ : ℕ) : ℝ) + 1)
          ≤ 8 * (ε / (10^6 * (K:ℝ))) * (x + 2) := hb1
        _ = 512 * (C:ℝ)/(10^6 * (1+ε)) + 16 * ε/(10^6 * (K:ℝ)) := hb2
        _ ≤ 2 * (C:ℝ)/ε + 3 := add_le_add hb3 hb4
    calc 8 * (ε / (10^6 * (K:ℝ))) * (((⌈x⌉₊ : ℕ) : ℝ) + 1) + (32 * (C:ℝ) / ε + 1)
        ≤ (2 * (C:ℝ) / ε + 3) + (32 * (C:ℝ)/ε + 1) := add_le_add hstep1 (le_refl _)
      _ = 34 * (C:ℝ)/ε + 4 := by ring
  · have hbase0 : (0:ℝ) ≤ (C:ℝ) + (mkIt C ε Dk).η⁻¹ + ε⁻¹ + 1 := by
      have h : (0:ℝ) ≤ (mkIt C ε Dk).η⁻¹ := by rw [hbηinv]; positivity
      linarith only [hC0, h, hεinv0.le]
    have ha : ((C:ℝ) + (mkIt C ε Dk).η⁻¹ + ε⁻¹ + 1)^1000 ≤ (4*L^2)^1000 :=
      pow_le_pow_left₀ hbase0 hP_le 1000
    have hb : (10:ℝ)^1000 ≤ (4*L^2)^1000 := by
      have hh : (10:ℝ) ≤ 4*L^2 := by nlinarith only [hL10]
      exact pow_le_pow_left₀ (by norm_num) hh 1000
    have hA : (4*L^2)^1000 = (2*L)^2000 := by
      have hh : (4*L^2) = (2*L)^2 := by ring
      rw [hh, ← pow_mul]
    calc ((C:ℝ) + (mkIt C ε Dk).η⁻¹ + ε⁻¹ + 1) ^ (1000:ℕ) + 10 ^ 1000
        ≤ (4*L^2)^1000 + (4*L^2)^1000 := add_le_add ha hb
      _ = 2 * (2*L)^2000 := by rw [hA]; ring
      _ ≤ (2*L)^2000 * (2*L) := by
            have h2 : (2:ℝ) ≤ 2*L := by linarith only [hL10]
            calc 2 * (2*L)^2000 ≤ (2*L) * (2*L)^2000 :=
                  mul_le_mul_of_nonneg_right h2 (pow_nonneg (by linarith only [hL10]) 2000)
              _ = (2*L)^2000 * (2*L) := by ring
      _ = (2*L)^2001 := by rw [← pow_succ]
      _ ≤ Real.exp (L/2) := hpow2001
      _ ≤ (mkIt C ε Dk).Dlow := hDlow_ge_exp
  · have hbase : ((mkIt C ε Dk).C : ℝ) + ((mkIt C ε Dk).K : ℝ) + (mkIt C ε Dk).η⁻¹ ≤ 4*L^2 := by
      rw [mkIt_C, hbK]
      nlinarith only [hC_le_L2, hK_le_L2, hηinv_le_L2, hL2_ge1]
    have hbase0 : (0:ℝ) ≤ ((mkIt C ε Dk).C : ℝ) + ((mkIt C ε Dk).K : ℝ) + (mkIt C ε Dk).η⁻¹ := by
      rw [mkIt_C, hbK]
      have h : (0:ℝ) ≤ (mkIt C ε Dk).η⁻¹ := by rw [hbηinv]; positivity
      linarith only [hC0, hKpos.le, h]
    calc ((mkIt C ε Dk).C + ((mkIt C ε Dk).K : ℝ) + (mkIt C ε Dk).η⁻¹)^9
        ≤ (4*L^2)^9 := pow_le_pow_left₀ hbase0 hbase 9
      _ = (2*L)^18 := by
            have hh : (4*L^2) = (2*L)^2 := by ring
            rw [hh, ← pow_mul]
      _ ≤ (2*L)^2001 := pow_le_pow_right₀ (by linarith only [hL10] : (1:ℝ) ≤ 2*L) (by norm_num)
      _ ≤ Real.exp (L/2) := hpow2001
      _ ≤ (mkIt C ε Dk).Dlow := hDlow_ge_exp
  · rw [hbK]
    have h1 : Real.sqrt ((K:ℝ)) ≤ Real.sqrt (2*L) := Real.sqrt_le_sqrt hKbig
    have h2 : 2 * Real.sqrt (2*L) ≤ L/2 := by
      have h3 : Real.sqrt (2*L) ≤ L/4 := by
        rw [Real.sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        nlinarith only [hL10]
      linarith only [h3]
    have h4 : 2 * Real.sqrt ((K:ℝ)) ≤ L/2 := by linarith only [h1, h2]
    calc Real.exp (2 * Real.sqrt ((K:ℝ))) ≤ Real.exp (L/2) := Real.exp_le_exp.mpr h4
      _ ≤ (mkIt C ε Dk).Dlow := hDlow_ge_exp
  · rw [hbK]
    have h1 : 16 * (K:ℝ) ≤ L^2 := by nlinarith only [hKbig, hL10]
    linarith only [h1, hL2_le_pow, hpow2001, hDlow_ge_exp]
  · linarith only [hηinv_le_L2, hL2_le_pow, hpow2001, hDlow_ge_exp]

theorem mkIt_cond (C : ℕ) (hC : 2 ≤ C) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ Dk : ℝ, Real.exp (Real.exp (10 ^ 10 * (1 + (C : ℝ) + ε⁻¹ + (C : ℝ) * ε⁻¹))) ≤ Dk →
      ∀ Dm : ℝ,
        Dm ≤ ((C : ℝ) + (mkIt C ε Dk).η⁻¹ + ε⁻¹ + 1) ^ (1000 : ℕ) + 10 ^ 1000 →
        (mkIt C ε Dk).Cond Dm := by
  intro Dk hDk Dm hDm
  exact mkIt_Cond_mono (mkIt_cond_max C hC ε hε0 hε1 Dk hDk) hDm

end Work.Deep.Kahn
