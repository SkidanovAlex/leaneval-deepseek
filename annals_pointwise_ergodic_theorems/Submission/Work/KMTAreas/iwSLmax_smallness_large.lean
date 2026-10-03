/-
# The smallness of `2 r · 2^k · (iwSLmax ρ l)^{2r(iwD ρ + 1)}` on the major arcs

The major-arc hypothesis `GoodMajorArcs ρ C_ρ l k` of the Ionescu–Wainger analysis reads
`k ≤ -C_ρ · 2^{ρ l}`, so `2^k` decays like `2^{-C_ρ 2^{ρ l}}`, whereas the denominator
products attached to the major-arc petals grow only like
`(iwSLmax ρ l)^{2r(iwD ρ + 1)}` with

  `log₂ (iwSLmax ρ l) = O(l · 2^{ρ l / 2})`   (subexponential!),

by `Work.KMTAreas.iwSLmax_subexp_bound`.  For *any* fixed `C_ρ > 0` the exponential decay
therefore eventually dominates the subexponential growth, which is the content of this file:
there is `l₀` such that for all `l ≥ l₀` and all major-arc scales `k`

  `2r · 2^k · (iwSLmax ρ l)^{2r(iwD ρ+1)} < 1/2`.

The exponential-beats-linear input is the abstract lemma
`Work.Analysis.Asymptotics.pow_dominates_linear`.
-/
import Mathlib
import Submission.Work.Analysis.IonescuWainger.Symbol
import Submission.Work.KMTAreas.iwSLmax_subexp_bound
import Submission.Work.Analysis.Asymptotics.pow_dominates_linear

set_option autoImplicit false

namespace Work.KMTAreas

open Work.Analysis.IonescuWainger

theorem iwSLmax_smallness_large (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : ℕ) (hr : 2 ≤ r)
    {Cρ : ℝ} (hCρ : 0 < Cρ) :
    ∃ l₀ : ℕ, ∀ l : ℕ, l₀ ≤ l → ∀ k : ℤ,
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k →
      2 * (r : ℝ) * (2 : ℝ) ^ k *
        ((Work.KMTAreas.iwSLmax ρ l : ℕ) : ℝ) ^
          (2 * r * (Work.Analysis.IonescuWainger.iwD ρ + 1)) < 1 / 2 := by
  set n : ℕ := 2 * r * (Work.Analysis.IonescuWainger.iwD ρ + 1) with hn
  set D : ℝ := ((Work.Analysis.IonescuWainger.iwD ρ : ℕ) : ℝ) with hD
  set E : ℝ := (n : ℝ) with hE
  have ha1 : 1 < (2:ℝ)^(ρ/2) := by
    have h := (Real.rpow_lt_rpow_left_iff (x := (2:ℝ)) (by norm_num : (1:ℝ) < 2)).mpr
      (show (0:ℝ) < ρ/2 by linarith)
    rwa [Real.rpow_zero] at h
  obtain ⟨N₀, hN₀⟩ :=
    Work.Analysis.Asymptotics.pow_dominates_linear ((2:ℝ)^(ρ/2)) ha1
      (D * (2 + ρ) * E / Cρ) ((Real.logb 2 (2*(r:ℝ)) + 2) / Cρ)
  refine ⟨N₀, fun l hl k hk => ?_⟩
  set t : ℝ := (2:ℝ) ^ (ρ * (l:ℝ) / 2) with ht
  set T : ℝ := (2:ℝ) ^ (ρ * (l:ℝ)) with hT
  have hA1 : 1 ≤ 2*(r:ℝ) := by
    have hr' : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    linarith
  have hApos : 0 < 2*(r:ℝ) := by linarith
  have htpos : 0 < t := by rw [ht]; positivity
  have ht1 : 1 ≤ t := by rw [ht]; exact Real.one_le_rpow (by norm_num) (by positivity)
  have htt : T = t * t := by
    rw [hT, ht, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1; ring
  have hSpos : 0 < ((Work.KMTAreas.iwSLmax ρ l : ℕ) : ℝ) := by
    have h1 : 1 ≤ Work.KMTAreas.iwSLmax ρ l :=
      le_trans (le_trans (by norm_num) (Work.KMTAreas.two_le_iwQ0 ρ hρ l)) (le_max_left _ _)
    exact_mod_cast h1
  have hS : ((Work.KMTAreas.iwSLmax ρ l : ℕ) : ℝ) ≤ (2:ℝ) ^ (D * (2 + ρ) * ((l:ℝ)+1) * t) := by
    simpa only [hD, ht] using iwSLmax_subexp_bound ρ hρ l
  have hSn : ((Work.KMTAreas.iwSLmax ρ l : ℕ) : ℝ) ^ n ≤
      (2:ℝ) ^ (D * (2 + ρ) * ((l:ℝ)+1) * t * E) := by
    refine (pow_le_pow_left₀ hSpos.le hS n).trans (le_of_eq ?_)
    calc ((2:ℝ) ^ (D * (2 + ρ) * ((l:ℝ)+1) * t)) ^ n
        = ((2:ℝ) ^ (D * (2 + ρ) * ((l:ℝ)+1) * t)) ^ ((n:ℝ)) := (Real.rpow_natCast _ _).symm
      _ = (2:ℝ) ^ (D * (2 + ρ) * ((l:ℝ)+1) * t * (n:ℝ)) :=
          (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) _ _).symm
      _ = (2:ℝ) ^ (D * (2 + ρ) * ((l:ℝ)+1) * t * E) := by rw [hE]
  have hk' : (k:ℝ) ≤ -(Cρ*T) := by
    have h := hk
    unfold Work.Analysis.IonescuWainger.GoodMajorArcs at h
    rw [← neg_mul]
    exact h
  have h2k : (2:ℝ)^k ≤ (2:ℝ)^(-(Cρ*T)) := by
    rw [show (2:ℝ)^k = (2:ℝ)^((k:ℝ)) from (Real.rpow_intCast (2:ℝ) k).symm]
    exact (Real.rpow_le_rpow_left_iff (x := (2:ℝ)) (by norm_num)).mpr hk'
  -- the threshold supplied by `pow_dominates_linear`, multiplied by `Cρ`
  have hCρt : D * (2 + ρ) * E * ((l:ℝ)+1) + (Real.logb 2 (2*(r:ℝ)) + 2) ≤ Cρ * t := by
    have h := hN₀ l hl
    have hat : ((2:ℝ)^(ρ/2))^l = t := by
      rw [ht]
      calc ((2:ℝ)^(ρ/2))^l = ((2:ℝ)^(ρ/2))^((l:ℝ)) := (Real.rpow_natCast _ _).symm
        _ = (2:ℝ)^((ρ/2) * (l:ℝ)) := (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) _ _).symm
        _ = (2:ℝ)^(ρ * (l:ℝ) / 2) := by congr 1; ring
    rw [hat] at h
    have hmul := mul_le_mul_of_nonneg_left h hCρ.le
    have hsimp : Cρ * ((D * (2 + ρ) * E / Cρ) * ((l:ℝ)+1) + (Real.logb 2 (2*(r:ℝ)) + 2) / Cρ)
        = D * (2 + ρ) * E * ((l:ℝ)+1) + (Real.logb 2 (2*(r:ℝ)) + 2) := by
      field_simp
    rwa [hsimp] at hmul
  have hexp : Real.logb 2 (2*(r:ℝ)) + -(Cρ*T) + D*(2+ρ)*((l:ℝ)+1)*t*E < -1 := by
    have hL0 : 0 ≤ Real.logb 2 (2*(r:ℝ)) + 2 := by
      have h := Real.logb_nonneg (b := 2) (by norm_num) hA1
      linarith
    have hkey : Real.logb 2 (2*(r:ℝ)) + 2 ≤ Cρ * t - D*(2+ρ)*E*((l:ℝ)+1) := by linarith
    have hukey : 0 ≤ Cρ * t - D*(2+ρ)*E*((l:ℝ)+1) := le_trans hL0 hkey
    have hu_le : Cρ * t - D*(2+ρ)*E*((l:ℝ)+1)
        ≤ t * (Cρ * t - D*(2+ρ)*E*((l:ℝ)+1)) := by
      have hh := mul_le_mul_of_nonneg_right ht1 hukey
      simpa using hh
    have htu : Real.logb 2 (2*(r:ℝ)) + 2 ≤ t * (Cρ * t - D*(2+ρ)*E*((l:ℝ)+1)) :=
      le_trans hkey hu_le
    have hfinal : Real.logb 2 (2*(r:ℝ)) + -(Cρ*T) + D*(2+ρ)*((l:ℝ)+1)*t*E
        = Real.logb 2 (2*(r:ℝ)) - t * (Cρ * t - D*(2+ρ)*E*((l:ℝ)+1)) := by
      rw [htt]; ring
    rw [hfinal]
    linarith
  calc 2 * (r:ℝ) * (2:ℝ)^k * ((Work.KMTAreas.iwSLmax ρ l : ℕ) : ℝ) ^ n
      = (2:ℝ)^(Real.logb 2 (2*(r:ℝ))) * (2:ℝ)^k * ((Work.KMTAreas.iwSLmax ρ l : ℕ) : ℝ) ^ n := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) hApos]
    _ ≤ (2:ℝ)^(Real.logb 2 (2*(r:ℝ))) * (2:ℝ)^(-(Cρ*T)) * (2:ℝ)^(D*(2+ρ)*((l:ℝ)+1)*t*E) := by
        gcongr
    _ = (2:ℝ)^(Real.logb 2 (2*(r:ℝ)) + -(Cρ*T) + D*(2+ρ)*((l:ℝ)+1)*t*E) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    _ < (2:ℝ)^(-(1:ℝ)) := (Real.rpow_lt_rpow_left_iff (x := (2:ℝ)) (by norm_num)).mpr hexp
    _ = 1/2 := by rw [Real.rpow_neg_one]; norm_num

end Work.KMTAreas
