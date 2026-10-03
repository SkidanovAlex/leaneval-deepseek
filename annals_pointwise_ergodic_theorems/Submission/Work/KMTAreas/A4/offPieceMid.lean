/-
# The "mid-range" piece of the off-diagonal decay of the Ionescu--Wainger projections

For `k ≤ 0` and `jj ≥ 0` the rescaled cutoff `η_{≤jj}` equals `1` on the interval
`[-2^{jj-1}, 2^{jj-1}]`.  Hence the difference

  `λ_k - η_{≤jj} · λ_k`   (`λ_k = 𝓕⁻ η_{≤k}`),

vanishes on that interval and is dominated by `|λ_k|` everywhere, so its `L¹`-mass is nothing but
the tail integral of `|λ_k|` beyond the scale `2^{jj-1}`:

  `∫ ‖λ_k(x) - η_{≤jj}(x) λ_k(x)‖ dx ≤ ∫⁻_{2^{jj-1} ≤ |x|} ‖λ_k(x)‖ dx`.

The tail estimate `offLamTail` for `i = 0` bounds the right hand side by
`C · (max (2^k · 2^{jj-1}) 1)^{-N}`, which is the claim.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.offDecayDefs
import Submission.Work.KMTAreas.A4.offLamTail

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A4

open MeasureTheory
open scoped ENNReal

/-- The set `{x : ℝ | r ≤ |x|}` is the union of the two closed half-lines `{x | r ≤ x}` and
`{x | x ≤ -r}` (for `0 ≤ r`). -/
theorem absSet_eq_Ici_union_Iic {r : ℝ} (hr : 0 ≤ r) :
    {x : ℝ | r ≤ |x|} = Set.Ici r ∪ Set.Iic (-r) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Ici, Set.mem_Iic]
  constructor
  · intro h
    rcases le_total 0 x with hx | hx
    · exact Or.inl (by rwa [abs_of_nonneg hx] at h)
    · exact Or.inr (by rw [abs_of_nonpos hx] at h; linarith)
  · rintro (h | h)
    · exact h.trans (le_abs_self x)
    · rw [abs_of_nonpos (by linarith)]
      linarith

theorem offPieceMid (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (k jj : ℤ), k ≤ 0 → 0 ≤ jj →
    ∫ x : ℝ, ‖(Work.KMTAreas.A4.lam k - Work.KMTAreas.A4.mS (Work.KMTAreas.A4.bmp jj)
        (Work.KMTAreas.A4.lam k) : SchwartzMap ℝ ℂ) x‖
      ≤ C * (max ((2 : ℝ) ^ k * (2 : ℝ) ^ (jj - 1)) 1) ^ (-(N : ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := offLamTail 0 N
  refine ⟨C, hCpos, fun k jj _ _ => ?_⟩
  have hcpos : (0 : ℝ) < (2 : ℝ) ^ (jj - 1) := zpow_pos (by norm_num) (jj - 1)
  -- the pointwise description of the difference
  have hpt : ∀ x : ℝ, (lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) x
      = (lam k) x * (1 - (bmp jj) x) := by
    intro x
    show (lam k) x - (bmp jj) x * (lam k) x = (lam k) x * (1 - (bmp jj) x)
    ring
  -- the difference vanishes on the interval where `η_{≤jj}` equals `1`
  have hzero : ∀ x : ℝ, ¬ ((2 : ℝ) ^ (jj - 1) ≤ |x|) →
      (lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) x = 0 := by
    intro x hx
    have hbx : (bmp jj) x = 1 := bmp_one_of_le jj (le_of_lt (not_le.mp hx))
    rw [hpt x, hbx]
    ring
  -- the difference is dominated by `|λ_k|`
  have hle : ∀ x : ℝ, ‖(lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) x‖ ≤ ‖(lam k) x‖ := by
    intro x
    rw [hpt x, norm_mul]
    calc ‖(lam k) x‖ * ‖1 - (bmp jj) x‖ ≤ ‖(lam k) x‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_one_sub_bmp_le jj x) (norm_nonneg _)
      _ = ‖(lam k) x‖ := mul_one _
  -- integrability of the norm of the difference
  have hInt : Integrable (fun x : ℝ =>
      ‖(lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) x‖) := by
    simpa using (SchwartzMap.integrable (lam k - mS (bmp jj) (lam k))).norm
  have hnn : 0 ≤ᵐ[volume] (fun x : ℝ =>
      ‖(lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) x‖) :=
    Filter.Eventually.of_forall fun x => norm_nonneg _
  -- the integral is the `toReal` of the corresponding lower Lebesgue integral
  have hof : ENNReal.ofReal (∫ x : ℝ,
        ‖(lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) x‖)
      = ∫⁻ x : ℝ, ‖(lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) x‖ₑ := by
    rw [ofReal_integral_eq_lintegral_ofReal hInt hnn]
    exact lintegral_congr fun x => ofReal_norm _
  have hIntegral : (∫⁻ x : ℝ,
        ‖(lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) x‖ₑ).toReal
      = ∫ x : ℝ, ‖(lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) x‖ := by
    rw [← hof, ENNReal.toReal_ofReal (integral_nonneg fun x => norm_nonneg _)]
  -- the tail estimate for the lintegral
  have htail : ∫⁻ x : ℝ, ‖(lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) x‖ₑ
      ≤ ∫⁻ x : ℝ in {x : ℝ | (2 : ℝ) ^ (jj - 1) ≤ |x|}, ‖(lam k) x‖ₑ := by
    have hset : {x : ℝ | (2 : ℝ) ^ (jj - 1) ≤ |x|}
        = Set.Ici ((2 : ℝ) ^ (jj - 1)) ∪ Set.Iic (-((2 : ℝ) ^ (jj - 1))) :=
      absSet_eq_Ici_union_Iic hcpos.le
    have hms : MeasurableSet
        (Set.Ici ((2 : ℝ) ^ (jj - 1)) ∪ Set.Iic (-((2 : ℝ) ^ (jj - 1)))) :=
      measurableSet_Ici.union measurableSet_Iic
    have hind : (fun x : ℝ => ‖(lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) x‖ₑ)
        = (Set.Ici ((2 : ℝ) ^ (jj - 1)) ∪
            Set.Iic (-((2 : ℝ) ^ (jj - 1)))).indicator
            (fun x : ℝ => ‖(lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) x‖ₑ) := by
      funext x
      by_cases hx : x ∈ (Set.Ici ((2 : ℝ) ^ (jj - 1)) ∪
          Set.Iic (-((2 : ℝ) ^ (jj - 1))))
      · simp [hx]
      · have hnot : ¬ ((2 : ℝ) ^ (jj - 1) ≤ |x|) :=
          fun hcon => hx (by rw [← hset]; exact hcon)
        simp [hx, hzero x hnot]
    rw [hind, lintegral_indicator hms, ← hset]
    apply setLIntegral_mono (continuous_enorm.comp (lam k).continuous).measurable
    intro x _
    have hb := ENNReal.ofReal_le_ofReal (hle x)
    simpa [ofReal_norm] using hb
  have hboundtail : ∫⁻ x : ℝ in {x : ℝ | (2 : ℝ) ^ (jj - 1) ≤ |x|}, ‖(lam k) x‖ₑ
      ≤ ENNReal.ofReal (C * (max ((2 : ℝ) ^ k * (2 : ℝ) ^ (jj - 1)) 1) ^ (-(N : ℝ))) := by
    have h := hC k ((2 : ℝ) ^ (jj - 1)) hcpos.le
    have hfun : (fun x : ℝ => ‖iteratedDeriv 0
          ((Work.KMTAreas.A7.etaMult_K k : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖ₑ)
        = fun x : ℝ => ‖(lam k) x‖ₑ := by
      funext x
      rw [iteratedDeriv_zero, lam_eq_etaMult_K k]
    rw [hfun] at h
    simpa using h
  have hne : (∫⁻ x : ℝ in {x : ℝ | (2 : ℝ) ^ (jj - 1) ≤ |x|}, ‖(lam k) x‖ₑ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hboundtail
  have hmaxnonneg : (0 : ℝ) ≤ max ((2 : ℝ) ^ k * (2 : ℝ) ^ (jj - 1)) 1 :=
    le_trans zero_le_one (le_max_right _ 1)
  have hnonneg : 0 ≤ C * (max ((2 : ℝ) ^ k * (2 : ℝ) ^ (jj - 1)) 1) ^ (-(N : ℝ)) :=
    mul_nonneg hCpos.le (Real.rpow_nonneg hmaxnonneg _)
  calc ∫ x : ℝ, ‖(lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) x‖
      = (∫⁻ x : ℝ,
          ‖(lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) x‖ₑ).toReal := hIntegral.symm
    _ ≤ (∫⁻ x : ℝ in {x : ℝ | (2 : ℝ) ^ (jj - 1) ≤ |x|}, ‖(lam k) x‖ₑ).toReal :=
        ENNReal.toReal_mono hne htail
    _ ≤ (ENNReal.ofReal
          (C * (max ((2 : ℝ) ^ k * (2 : ℝ) ^ (jj - 1)) 1) ^ (-(N : ℝ)))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hboundtail
    _ = C * (max ((2 : ℝ) ^ k * (2 : ℝ) ^ (jj - 1)) 1) ^ (-(N : ℝ)) :=
        ENNReal.toReal_ofReal hnonneg

end Work.KMTAreas.A4
