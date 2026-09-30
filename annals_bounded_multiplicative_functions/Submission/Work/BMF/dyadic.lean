import Mathlib
import Submission.Work.BMF.parseval_kernels
import Submission.Work.BMF.dirPoly_bound
import Submission.Work.BMF.dyadic_annulus
import Submission.Work.BMF.dyadic_cover
import Submission.Work.BMF.tail_integrable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The dyadic decomposition of the frequency integral

For a bounded sequence `a` the weighted frequency integral
`∫ ‖dirPoly a X t‖² · min 1 (min (t² (h₂/X)²) ((X/h₁)²/t²)) dt`
is dominated by a constant times the low-frequency integral
`∫_{-(X/h₁)}^{X/h₁} ‖dirPoly a X t‖²`
plus the dyadic supremum `⨆_{T ≥ X/h₁} (X/h₁)/T · ∫_{-(2T)}^{2T} ‖dirPoly a X t‖²`.

The weight is at most `min 1 (R²/t²)` with `R = X/h₁`: on `|t| ≤ R` it is at most `1`, and on the
`k`-th dyadic annulus `2^k R < |t| ≤ 2^{k+1} R` it is at most `4^{-k}`, so each annulus costs at
most `(1/4)^k · ∫_{-2^{k+1}R}^{2^{k+1}R} F ≤ 2^{-k} · sup_T (R/T)∫_{-(2T)}^{2T} F`; summing the
geometric series gives the factor `2`.
-/

namespace Work.BMF

open MeasureTheory Set Filter

noncomputable section

/-- The two-sided dyadic annulus `2^k R < |t| ≤ 2^(k+1) R`.  The negative half is `Ico` so that
the endpoint `-R` (which is *not* in `{t | R < |t|}`) is excluded. -/
def dyadicAnnulus (R : ℝ) (k : ℕ) : Set ℝ :=
  Set.Ioc ((2 : ℝ) ^ k * R) ((2 : ℝ) ^ (k + 1) * R) ∪
    Set.Ico (-((2 : ℝ) ^ (k + 1) * R)) (-((2 : ℝ) ^ k * R))

/-- **Dyadic summation.**  If `F` is a nonnegative bounded measurable function and every `T ≥ R`
satisfies `(R/T) * ∫_{-(2T)}^{2T} F ≤ S`, then the frequency tail
`∫_{R < |t|} F t · R²/t² dt` is at most `2 S`. -/
theorem dyadicTail_le (F : ℝ → ℝ) (hFnn : ∀ t, 0 ≤ F t) (hFmeas : Measurable F)
    (K : ℝ) (hK : ∀ t, F t ≤ K) (R S : ℝ) (hR : 0 < R) (hS : 0 ≤ S)
    (hsup : ∀ T : ℝ, R ≤ T → R / T * (∫ t in (-(2 * T))..(2 * T), F t) ≤ S) :
    ∫ t in {t : ℝ | R < |t|}, F t * (R ^ 2 / t ^ 2) ≤ 2 * S := by
  have hcov' : (⋃ k : ℕ, dyadicAnnulus R k) = {t : ℝ | R < |t|} := by
    simpa [dyadicAnnulus] using (dyadic_cover R hR).1
  have hdisj' : Pairwise (Function.onFun Disjoint (dyadicAnnulus R)) := by
    intro k l hkl
    exact (dyadic_cover R hR).2 hkl
  have hmeasA : ∀ k : ℕ, MeasurableSet (dyadicAnnulus R k) := fun k =>
    measurableSet_Ioc.union measurableSet_Ico
  have hInt : IntegrableOn (fun t : ℝ => F t * (R ^ 2 / t ^ 2))
      (⋃ k : ℕ, dyadicAnnulus R k) := by
    rw [hcov']
    exact tail_integrable F hFnn hFmeas K hK R hR
  have hterm : ∀ k : ℕ, ∫ t in dyadicAnnulus R k, F t * (R ^ 2 / t ^ 2)
      ≤ (1 / 2 : ℝ) ^ k * S := by
    intro k
    have h := dyadic_annulus F hFnn hFmeas K hK R S hR hS hsup k
    simpa [dyadicAnnulus] using h
  have hkey : ∫ t in {t : ℝ | R < |t|}, F t * (R ^ 2 / t ^ 2)
      = ∑' k : ℕ, ∫ t in dyadicAnnulus R k, F t * (R ^ 2 / t ^ 2) := by
    rw [← hcov']
    exact MeasureTheory.integral_iUnion hmeasA hdisj' hInt
  have hnn : ∀ k : ℕ, 0 ≤ ∫ t in dyadicAnnulus R k, F t * (R ^ 2 / t ^ 2) := fun k =>
    MeasureTheory.setIntegral_nonneg_of_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (hFnn t) (by positivity))
  have hgeom : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k * S) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_right S
  have hsum : Summable (fun k : ℕ => ∫ t in dyadicAnnulus R k, F t * (R ^ 2 / t ^ 2)) :=
    Summable.of_nonneg_of_le hnn hterm hgeom
  rw [hkey]
  calc ∑' k : ℕ, ∫ t in dyadicAnnulus R k, F t * (R ^ 2 / t ^ 2)
      ≤ ∑' k : ℕ, (1 / 2 : ℝ) ^ k * S := Summable.tsum_le_tsum hterm hsum hgeom
    _ = 2 * S := by
        rw [tsum_mul_right, tsum_geometric_two]

theorem dyadic :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ), (∀ n, ‖a n‖ ≤ 1) →
      ∀ (X h₁ h₂ : ℝ), 1 ≤ X → 1 ≤ h₁ → h₁ ≤ h₂ → h₂ ≤ X / (Real.log X) ^ (1/5 : ℝ) →
      (∫ t : ℝ, ‖Work.BMF.dirPoly a X t‖^2 * min 1 (min (t^2 * (h₂/X)^2) ((X/h₁)^2 / t^2)))
        ≤ C * ((Real.log X) ^ (-(2/15:ℝ)) +
            (∫ t in (-(X/h₁))..(X/h₁), ‖Work.BMF.dirPoly a X t‖^2)
            + ⨆ (T : {T : ℝ // X/h₁ ≤ T}), (X/h₁)/T * (∫ t in (-(2*T))..(2*T), ‖Work.BMF.dirPoly a X t‖^2)) := by
  refine ⟨3, by norm_num, fun a ha X h₁ h₂ hX h₁1 h12 h2log => ?_⟩
  set R : ℝ := X / h₁ with hRdef
  set F : ℝ → ℝ := fun t => ‖dirPoly a X t‖ ^ 2 with hFdef
  set S : ℝ := ⨆ (T : {T : ℝ // R ≤ T}), R / T * (∫ t in (-(2 * T))..(2 * T), F t) with hSdef
  show ∫ t : ℝ, F t * min 1 (min (t ^ 2 * (h₂ / X) ^ 2) (R ^ 2 / t ^ 2)) ≤
      3 * ((Real.log X) ^ (-(2/15:ℝ)) + (∫ t in (-R)..R, F t) + S)
  have hRpos : 0 < R := by rw [hRdef]; exact div_pos (by linarith) (by linarith)
  have hFcont : Continuous F := by
    rw [hFdef]
    exact (((dirPoly_bound a ha X).1).norm).pow 2
  have hFmeas : Measurable F := hFcont.measurable
  have hFnn : ∀ t, 0 ≤ F t := fun t => by rw [hFdef]; positivity
  set K : ℝ := (∑ n ∈ natIcc X (4 * X), (1 : ℝ) / (n : ℝ)) ^ 2 with hKdef
  have hKbound : ∀ t, F t ≤ K := by
    intro t
    have h1 : ‖dirPoly a X t‖ ≤ ∑ n ∈ natIcc X (4 * X), (1 : ℝ) / (n : ℝ) :=
      (dirPoly_bound a ha X).2 t
    have hc : 0 ≤ ∑ n ∈ natIcc X (4 * X), (1 : ℝ) / (n : ℝ) :=
      Finset.sum_nonneg fun n _ => by positivity
    rw [hFdef, hKdef]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hSbdd : BddAbove (Set.range
      (fun T : {T : ℝ // R ≤ T} => R / T * (∫ t in (-(2 * T))..(2 * T), F t))) := by
    refine ⟨4 * R * K, ?_⟩
    rintro _ ⟨T, rfl⟩
    have hTpos : 0 < (T : ℝ) := lt_of_lt_of_le hRpos T.2
    have hle1 : (∫ t in (-(2 * T))..(2 * T), F t) ≤ 4 * (T : ℝ) * K := by
      have hle : (∫ t in (-(2 * T))..(2 * T), F t) ≤ ∫ t in (-(2 * T))..(2 * T), K :=
        intervalIntegral.integral_mono (by linarith) (hFcont.intervalIntegrable _ _)
          intervalIntegrable_const (fun t => hKbound t)
      rw [intervalIntegral.integral_const, smul_eq_mul] at hle
      calc (∫ t in (-(2 * T))..(2 * T), F t) ≤ (2 * (T : ℝ) - (-(2 * (T : ℝ)))) * K := hle
        _ = 4 * (T : ℝ) * K := by ring
    calc R / T * (∫ t in (-(2 * T))..(2 * T), F t) ≤ R / T * (4 * (T : ℝ) * K) :=
          mul_le_mul_of_nonneg_left hle1 (div_nonneg hRpos.le hTpos.le)
      _ = 4 * R * K := by
          field_simp
  have hSupper : ∀ T : {T : ℝ // R ≤ T},
      R / T * (∫ t in (-(2 * T))..(2 * T), F t) ≤ S := by
    intro T
    rw [hSdef]
    exact le_ciSup hSbdd T
  have hsup : ∀ T : ℝ, R ≤ T → R / T * (∫ t in (-(2 * T))..(2 * T), F t) ≤ S :=
    fun T hT => hSupper ⟨T, hT⟩
  have hSnn : 0 ≤ S := by
    have h := hSupper ⟨R, le_refl R⟩
    have h0 : 0 ≤ R / R * (∫ t in (-(2 * R))..(2 * R), F t) :=
      mul_nonneg (by positivity)
        (intervalIntegral.integral_nonneg (by linarith) (fun u _ => hFnn u))
    linarith
  -- integrability of the two pieces of the majorant
  have hIntF : IntegrableOn F (Set.Icc (-R) R) := by
    have hint : IntervalIntegrable F volume (-R) R := hFcont.intervalIntegrable _ _
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp hint
  have hIntT : IntegrableOn (fun t : ℝ => F t * (R ^ 2 / t ^ 2)) {t : ℝ | R < |t|} :=
    tail_integrable F hFnn hFmeas K hKbound R hRpos
  have hmeasT : MeasurableSet {t : ℝ | R < |t|} :=
    measurableSet_lt measurable_const measurable_id.abs
  have hIntMaj : Integrable (fun t : ℝ =>
      (Set.Icc (-R) R).indicator F t + ({t : ℝ | R < |t|}).indicator
        (fun t => F t * (R ^ 2 / t ^ 2)) t) :=
    (hIntF.integrable_indicator measurableSet_Icc).add
      (hIntT.integrable_indicator hmeasT)
  -- pointwise domination of the weight by the two pieces
  have hw_nn : ∀ t : ℝ, 0 ≤ min 1 (min (t ^ 2 * (h₂ / X) ^ 2) (R ^ 2 / t ^ 2)) := fun t =>
    le_min (by norm_num) (le_min (by positivity) (by positivity))
  have hpt : ∀ t : ℝ, F t * min 1 (min (t ^ 2 * (h₂ / X) ^ 2) (R ^ 2 / t ^ 2))
      ≤ (Set.Icc (-R) R).indicator F t
        + ({t : ℝ | R < |t|}).indicator (fun t => F t * (R ^ 2 / t ^ 2)) t := by
    intro t
    have hIcc : t ∈ Set.Icc (-R) R ↔ |t| ≤ R := by rw [Set.mem_Icc, abs_le]
    by_cases h : |t| ≤ R
    · have hnot : t ∉ {t : ℝ | R < |t|} := by simp [h]
      rw [Set.indicator_of_mem (hIcc.mpr h), Set.indicator_of_notMem hnot, add_zero]
      have hmin : min 1 (min (t ^ 2 * (h₂ / X) ^ 2) (R ^ 2 / t ^ 2)) ≤ 1 := min_le_left _ _
      nlinarith [hFnn t]
    · have hnot : t ∉ Set.Icc (-R) R := fun hm => h (hIcc.mp hm)
      rw [Set.indicator_of_notMem hnot,
        Set.indicator_of_mem (s := {t : ℝ | R < |t|}) (lt_of_not_ge h), zero_add]
      have hmin : min 1 (min (t ^ 2 * (h₂ / X) ^ 2) (R ^ 2 / t ^ 2)) ≤ R ^ 2 / t ^ 2 :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      exact mul_le_mul_of_nonneg_left hmin (hFnn t)
  have hle1 : ∫ t : ℝ, F t * min 1 (min (t ^ 2 * (h₂ / X) ^ 2) (R ^ 2 / t ^ 2))
      ≤ ∫ t : ℝ, ((Set.Icc (-R) R).indicator F t
        + ({t : ℝ | R < |t|}).indicator (fun t => F t * (R ^ 2 / t ^ 2)) t) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t => mul_nonneg (hFnn t) (hw_nn t)) hIntMaj
      (Filter.Eventually.of_forall fun t => hpt t)
  have hIcc_eq : ∫ t in Set.Icc (-R) R, F t = ∫ t in (-R)..R, F t := by
    rw [intervalIntegral.integral_of_le (show -R ≤ R by linarith)]
    exact MeasureTheory.integral_Icc_eq_integral_Ioc
  have hsplit : ∫ t : ℝ, ((Set.Icc (-R) R).indicator F t
        + ({t : ℝ | R < |t|}).indicator (fun t => F t * (R ^ 2 / t ^ 2)) t)
      = (∫ t in (-R)..R, F t) + ∫ t in {t : ℝ | R < |t|}, F t * (R ^ 2 / t ^ 2) := by
    rw [MeasureTheory.integral_add (hIntF.integrable_indicator measurableSet_Icc)
      (hIntT.integrable_indicator hmeasT)]
    rw [MeasureTheory.integral_indicator measurableSet_Icc,
      MeasureTheory.integral_indicator hmeasT, hIcc_eq]
  have htail : ∫ t in {t : ℝ | R < |t|}, F t * (R ^ 2 / t ^ 2) ≤ 2 * S :=
    dyadicTail_le F hFnn hFmeas K hKbound R S hRpos hSnn hsup
  have hB0 : 0 ≤ ∫ t in (-R)..R, F t :=
    intervalIntegral.integral_nonneg (by linarith) (fun u _ => hFnn u)
  have hlog : 0 ≤ (Real.log X) ^ (-(2/15:ℝ)) :=
    Real.rpow_nonneg (Real.log_nonneg hX) _
  calc ∫ t : ℝ, F t * min 1 (min (t ^ 2 * (h₂ / X) ^ 2) (R ^ 2 / t ^ 2))
      ≤ ∫ t : ℝ, ((Set.Icc (-R) R).indicator F t
          + ({t : ℝ | R < |t|}).indicator (fun t => F t * (R ^ 2 / t ^ 2)) t) := hle1
    _ = (∫ t in (-R)..R, F t) + ∫ t in {t : ℝ | R < |t|}, F t * (R ^ 2 / t ^ 2) := hsplit
    _ ≤ (∫ t in (-R)..R, F t) + 2 * S := by linarith
    _ ≤ 3 * ((Real.log X) ^ (-(2/15:ℝ)) + (∫ t in (-R)..R, F t) + S) := by linarith

end

end Work.BMF
