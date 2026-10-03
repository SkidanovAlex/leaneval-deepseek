import Mathlib
import Submission.Work.KMTAreas.A7.fiberVarSamplingCoreG
import Submission.Work.KMTAreas.A7.lacunaryBumpGlue
import Submission.Work.KMTAreas.A7.eLpNorm_iwConv_le_of_IWLqBound
import Submission.Work.KMTAreas.A7.isLqMultiplierBound_modulated_etaCut
import Submission.Work.KMTAreas.A7.kmtProj_lp_bound_uniform
import Submission.Work.KMTAreas.A7.liftCollapse
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTAreas.A7

noncomputable section

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## Auxiliary facts -/

/-- Translation invariance of the `ℓ^p` seminorm on `ℤ` (counting measure). -/
theorem eLpNorm_comp_sub_right (g : ℤ → ℂ) (p : ENNReal) (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (s : ℤ) :
    eLpNorm (fun x : ℤ => g (x - s)) p Measure.count = eLpNorm g p Measure.count := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpt,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpt]
  congr 1
  rw [lintegral_count, lintegral_count]
  exact (Equiv.subRight s).tsum_eq (fun y : ℤ => ‖g y‖ₑ ^ p.toReal)

/-- `fourier (T := 1) n x` is the character `ee (n x)`. -/
theorem fourier_coe_eq_ee (n : ℤ) (x : ℝ) :
    fourier (T := 1) n (x : Circ) = Work.KMTAreas.A7.ee ((n : ℝ) * x) := by
  rw [fourier_coe_apply]
  rw [Work.KMTAreas.A7.ee]
  congr 1
  push_cast
  ring

/-- The narrowness of the bump `mStarF u` at the scale `-(2u)`. -/
theorem mStarF_support_le (u : ℕ) (x : ℝ) (hx : Work.KMTAreas.A7.mStarF u x ≠ 0) :
    |x| ≤ (2 : ℝ) ^ (-(2 * (u : ℤ))) := by
  have h := etaCut_ne_zero_mem_realArc (-(2 * (u : ℤ)))
    (by simpa [Work.KMTAreas.A7.mStarF] using hx)
  rw [realArc, Set.mem_Icc] at h
  rw [abs_le]
  exact h

/-- For `1 ≤ u` one has `2^{-2u} ≤ 1/4`. -/
theorem two_zpow_le_quarter (u : ℕ) (hu : 1 ≤ u) :
    (2 : ℝ) ^ (-(2 * (u : ℤ))) ≤ 1 / 4 := by
  have h2 : (2 : ℝ) ^ (-(2 * (u : ℤ))) ≤ (2 : ℝ) ^ (-(2 : ℤ)) := by
    refine zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ?_
    have hu2 : (2 : ℤ) ≤ 2 * (u : ℤ) := by
      have : (1 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu
      omega
    omega
  have h3 : (2 : ℝ) ^ (-(2 : ℤ)) = 1 / 4 := by norm_num
  rw [h3] at h2
  exact h2

/-! ## The Ionescu--Wainger multiplier bound at an arbitrary exponent for a narrow symbol -/

/-- Exponent arithmetic for the even index `r = max 2 ⌈max p (p/(p-1))/2⌉₊`. -/
theorem keyArith (p : ℝ) (hp : 1 < p) (r : ℕ) (hr : r = max 2 ⌈max p (p / (p - 1)) / 2⌉₊) :
    2 ≤ r ∧ 1 < 2 * (r : ℝ) / (2 * (r : ℝ) - 1) ∧
      2 * (r : ℝ) / (2 * (r : ℝ) - 1) < 2 * (r : ℝ) ∧
      2 * (r : ℝ) / (2 * (r : ℝ) - 1) ≤ p ∧ p ≤ 2 * (r : ℝ) := by
  have hden : 0 < p - 1 := by linarith
  have hr2 : 2 ≤ r := by rw [hr]; exact le_max_left _ _
  have hle : ((⌈max p (p / (p - 1)) / 2⌉₊ : ℕ) : ℝ) ≤ (r : ℝ) := by
    rw [hr]
    exact_mod_cast le_max_right (2 : ℕ) _
  have hceil : max p (p / (p - 1)) / 2 ≤ (r : ℝ) :=
    (Nat.le_ceil (max p (p / (p - 1)) / 2)).trans hle
  have hmax : max p (p / (p - 1)) ≤ 2 * (r : ℝ) := by linarith
  have h2r : (2 : ℝ) ≤ 2 * (r : ℝ) := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
    linarith
  have hpos : 0 < 2 * (r : ℝ) - 1 := by linarith
  refine ⟨hr2, ?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hpos]
    linarith
  · rw [div_lt_iff₀ hpos]
    have hr2R : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
    nlinarith [hr2R]
  · have hq : p / (p - 1) ≤ 2 * (r : ℝ) := le_trans (le_max_right _ _) hmax
    rw [div_le_iff₀ hden] at hq
    rw [div_le_iff₀ hpos]
    nlinarith
  · exact le_trans (le_max_left _ _) hmax

/-- The Ionescu--Wainger multiplier bound at an arbitrary exponent `1 < p < ∞` for a narrow
Schwartz symbol, from the continuous multiplier bound at the single even exponent
`2r`, `r = max 2 ⌈max p (p/(p-1))/2⌉₊`, for the symbol and its conjugate. -/
theorem iwLqBound_narrow_bump (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∃ Cρ : ℝ, 0 < Cρ ∧
      ∀ (l : ℕ) (k : ℤ) (Φ : SchwartzMap ℝ ℂ) (M : NNReal),
        GoodMajorArcs ρ Cρ l k → (2 : ℝ) ^ k < 1 / 2 →
        (∀ x : ℝ, (Φ : ℝ → ℂ) x ≠ 0 → x ∈ realArc k) →
        IsLqMultiplierBound (ENNReal.ofReal (2 * ((max 2 ⌈max p (p / (p - 1)) / 2⌉₊ : ℕ) : ℝ)))
            (Φ : ℝ → ℂ) M →
        IsLqMultiplierBound (ENNReal.ofReal (2 * ((max 2 ⌈max p (p / (p - 1)) / 2⌉₊ : ℕ) : ℝ)))
            (fun x : ℝ => star ((Φ : ℝ → ℂ) x)) M →
        IWLqBound (iwArithFreqs ρ l) (periodize (Φ : ℝ → ℂ)) (ENNReal.ofReal p)
          (Real.toNNReal (C * M)) := by
  obtain ⟨Cρg, hCρg, hgap⟩ := Work.KMTAreas.iwEvenMultiplierGapUniform ρ hρ hρ1
  set r : ℕ := max 2 ⌈max p (p / (p - 1)) / 2⌉₊ with hr
  obtain ⟨hr2, hgt1, hlt, hlo, hhi⟩ := keyArith p hp r hr
  obtain ⟨Cg, hCg, hbound⟩ := hgap r hr2
  have h2rpos : (0 : ℝ) < 2 * (r : ℝ) := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
    linarith
  have hofreal2r : ENNReal.ofReal (2 * (r : ℝ)) = (((2 * r : ℕ)) : ENNReal) := by
    rw [show 2 * (r : ℝ) = ((2 * r : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  have hkeyeq : (2 * ((max 2 ⌈max p (p / (p - 1)) / 2⌉₊ : ℕ) : ℝ)) = 2 * (r : ℝ) := by rw [hr]
  refine ⟨(Cg : ℝ), by exact_mod_cast hCg, Cρg, hCρg, ?_⟩
  intro l k Φ M hgood hk hnarrow hmult1 hmult2
  have hup : IWLqBound (iwArithFreqs ρ l) (periodize (Φ : ℝ → ℂ)) (ENNReal.ofReal (2 * (r : ℝ)))
      (Cg * M) := by
    have hm : IsLqMultiplierBound (((2 * r : ℕ)) : ENNReal) (Φ : ℝ → ℂ) M := by
      rw [← hofreal2r, ← hkeyeq]
      exact hmult1
    have h := hbound l k hgood Φ hnarrow M hm
    rwa [← hofreal2r] at h
  have hstar : IWLqBound (iwArithFreqs ρ l) (periodize (fun x : ℝ => star ((Φ : ℝ → ℂ) x)))
      (ENNReal.ofReal (2 * (r : ℝ))) (Cg * M) := by
    have hm : IsLqMultiplierBound (((2 * r : ℕ)) : ENNReal)
        ((Work.KMTAreas.A7.starSchwartz Φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) M := by
      rw [Work.KMTAreas.A7.starSchwartz_coe, ← hofreal2r, ← hkeyeq]
      exact hmult2
    have hnarrowS : ∀ x : ℝ, (Work.KMTAreas.A7.starSchwartz Φ : ℝ → ℂ) x ≠ 0 → x ∈ realArc k := by
      intro x hx
      refine hnarrow x ?_
      rw [Work.KMTAreas.A7.starSchwartz_apply] at hx
      exact fun h => hx (by rw [h, star_zero])
    have h := hbound l k hgood (Work.KMTAreas.A7.starSchwartz Φ) hnarrowS M hm
    rw [Work.KMTAreas.A7.starSchwartz_coe] at h
    rwa [← hofreal2r] at h
  have hlow : IWLqBound (iwArithFreqs ρ l) (periodize (Φ : ℝ → ℂ))
      (ENNReal.ofReal (2 * (r : ℝ) / (2 * (r : ℝ) - 1))) (Cg * M) := by
    have hq1 : 1 < (ENNReal.ofReal (2 * (r : ℝ))).toReal := by
      rw [ENNReal.toReal_ofReal h2rpos.le]
      linarith
    have hdual := IWLqBound_of_dual (iwArithFreqs ρ l)
      (periodize (fun x : ℝ => star ((Φ : ℝ → ℂ) x))) hstar hq1
    rw [ENNReal.toReal_ofReal h2rpos.le] at hdual
    have hsym : (fun ξ : Circ => star (periodize (fun x : ℝ => star ((Φ : ℝ → ℂ) x)) ξ))
        = periodize (Φ : ℝ → ℂ) := funext fun ξ => Work.KMTAreas.A7.periodize_star (Φ : ℝ → ℂ) ξ
    rwa [hsym] at hdual
  have hdenpos : (0 : ℝ) < 2 * (r : ℝ) - 1 := by linarith
  have hapos : (0 : ℝ) < 2 * (r : ℝ) / (2 * (r : ℝ) - 1) := div_pos h2rpos hdenpos
  obtain ⟨hθ0, hθ1, hθeq⟩ :=
    interpTheta_mem (a := 2 * (r : ℝ) / (2 * (r : ℝ) - 1))
      (b := 2 * (r : ℝ)) (p := p) hapos hlt hlo hhi
  have hmain := iwLqBound_of_pair (A := iwArithFreqs ρ l)
    (Ψ := periodize (Φ : ℝ → ℂ)) (q₀ := 2 * (r : ℝ) / (2 * (r : ℝ) - 1)) (q₁ := 2 * (r : ℝ))
    (C₀ := Cg) (C₁ := Cg) (a := 1) (M := M)
    (by simpa using hlow) (by simpa using hup) hgt1 (by linarith) hθ0 hθ1
    (lt_trans zero_lt_one hp) hθeq one_ne_zero
  have hconst : Real.toNNReal ((Cg : ℝ) * (M : ℝ)) = Cg * M := by
    apply NNReal.coe_inj.mp
    rw [Real.coe_toNNReal _ (by positivity), NNReal.coe_mul]
  refine hmain.mono ?_
  have hCe : Cg ^ (1 - interpTheta (2 * (r : ℝ) / (2 * (r : ℝ) - 1)) (2 * (r : ℝ)) p) *
      Cg ^ (interpTheta (2 * (r : ℝ) / (2 * (r : ℝ) - 1)) (2 * (r : ℝ)) p) = Cg := by
    rw [← NNReal.rpow_add (ne_of_gt hCg),
      show 1 - interpTheta (2 * (r : ℝ) / (2 * (r : ℝ) - 1)) (2 * (r : ℝ)) p +
        interpTheta (2 * (r : ℝ) / (2 * (r : ℝ) - 1)) (2 * (r : ℝ)) p = 1 by ring,
      NNReal.rpow_one]
  rw [show (Cg ^ (1 - interpTheta (2 * (r : ℝ) / (2 * (r : ℝ) - 1)) (2 * (r : ℝ)) p) *
        Cg ^ (interpTheta (2 * (r : ℝ) / (2 * (r : ℝ) - 1)) (2 * (r : ℝ)) p)) * 1 * M = Cg * M
      by rw [hCe, mul_one], hconst]

/-! ## The single-scale fibre bound -/

end

end Work.KMTAreas.A7Hi
