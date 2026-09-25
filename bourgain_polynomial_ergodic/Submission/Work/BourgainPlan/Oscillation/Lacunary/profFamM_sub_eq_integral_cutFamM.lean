import Mathlib
import Submission.Work.BourgainPlan.Oscillation.Lacunary.dilProfDefs

namespace Work.BourgainPlan.Oscillation.Lacunary

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-!
# The Fubini identification behind the dilation-profile reduction

`profFamM H₁ r f T ρ i x` is the `mu01`-integral of `θ ↦ r θ · H₁ (⌊ρ^i⌋ θ) · P(θ) · e(xθ)`,
where `H₁ u = -∫_{t∈(0,1]} Hd t · 1_{u ≤ t} dt`.  Writing the indicator `1_{⌊ρ^i⌋ θ ≤ t}` as
`1_{θ ≤ t/⌊ρ^i⌋}` and swapping the `θ`- and `t`-integrals (Fubini) exhibits the difference of two
dilation profiles as the `t`-integral of the *cut* family `cutFamM`, which is exactly the lemma
`profFamM_sub_eq_integral_cutFamM`.
-/

/-- The lacunary scale `⌊ρ^i⌋` is a positive real when `ρ > 1`. -/
lemma lacScale_pos_real (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) : 0 < (lacScale ρ i : ℝ) := by
  have h1 : 1 ≤ ρ ^ i := one_le_pow₀ hρ.le
  have h2 : 1 ≤ lacScale ρ i := by
    rw [lacScale]; exact (Nat.one_le_floor_iff (ρ ^ i)).mpr h1
  exact_mod_cast h2

/-- The `θ`-integrand of the cut family, with the indicator written as `N · θ ≤ t`. -/
def oscBs (r P E : ℝ → ℂ) (N t : ℝ) : ℝ → ℂ :=
  fun θ => (r θ * (if N * θ ≤ t then (1:ℂ) else 0)) * (P θ * E θ)

/-- The joint `(θ,t)`-integrand of the Fubini step. -/
def oscGs (Hd r P E : ℝ → ℂ) (N : ℝ) (θ t : ℝ) : ℂ :=
  Hd t * oscBs r P E N t θ

lemma measurable_oscBs {r P E : ℝ → ℂ} (hr : Measurable r) (hP : Measurable P)
    (hE : Measurable E) (N : ℝ) : Measurable (fun p : ℝ × ℝ => oscBs r P E N p.2 p.1) := by
  have h1 : Measurable fun p : ℝ × ℝ => (if N * p.1 ≤ p.2 then (1:ℂ) else 0) :=
    Measurable.ite (measurableSet_le (measurable_const.mul measurable_fst) measurable_snd)
      measurable_const measurable_const
  exact ((hr.comp measurable_fst).mul h1).mul ((hP.comp measurable_fst).mul (hE.comp measurable_fst))

lemma measurable_oscGs {Hd r P E : ℝ → ℂ} (hHd : Measurable Hd) (hr : Measurable r)
    (hP : Measurable P) (hE : Measurable E) (N : ℝ) :
    Measurable (Function.uncurry (oscGs Hd r P E N)) := by
  have h : Measurable (fun p : ℝ × ℝ => Hd p.2 * oscBs r P E N p.2 p.1) :=
    (hHd.comp measurable_snd).mul (measurable_oscBs hr hP hE N)
  exact h

lemma norm_oscBs_le {r P E : ℝ → ℂ} {cap S : ℝ} (hrb : ∀ θ, ‖r θ‖ ≤ cap)
    (hPb : ∀ θ, ‖P θ‖ ≤ S) (hEb : ∀ θ, ‖E θ‖ = 1) (N t θ : ℝ) :
    ‖oscBs r P E N t θ‖ ≤ cap * S := by
  have hcap : 0 ≤ cap := le_trans (norm_nonneg _) (hrb 0)
  have hS : 0 ≤ S := le_trans (norm_nonneg _) (hPb 0)
  simp only [oscBs]
  calc ‖(r θ * (if N * θ ≤ t then (1:ℂ) else 0)) * (P θ * E θ)‖
      = ‖r θ‖ * ‖(if N * θ ≤ t then (1:ℂ) else 0)‖ * (‖P θ‖ * ‖E θ‖) := by
        simp only [norm_mul]
    _ ≤ cap * 1 * (S * 1) := by
        refine mul_le_mul ?_ ?_ ?_ ?_
        · refine mul_le_mul (hrb θ) ?_ (norm_nonneg _) hcap
          split <;> simp
        · refine mul_le_mul (hPb θ) ?_ (norm_nonneg _) hS
          rw [hEb θ]
        · positivity
        · simpa using hcap
    _ = cap * S := by ring

lemma norm_oscGs_le {Hd r P E : ℝ → ℂ} {N cap M S : ℝ} (hM : 0 ≤ M)
    (hrb : ∀ θ, ‖r θ‖ ≤ cap) (hPb : ∀ θ, ‖P θ‖ ≤ S) (hEb : ∀ θ, ‖E θ‖ = 1)
    (θ t : ℝ) (hHdt : ‖Hd t‖ ≤ M) : ‖oscGs Hd r P E N θ t‖ ≤ M * (cap * S) := by
  simp only [oscGs]
  calc ‖Hd t * oscBs r P E N t θ‖
      = ‖Hd t‖ * ‖oscBs r P E N t θ‖ := norm_mul _ _
    _ ≤ M * (cap * S) :=
        mul_le_mul hHdt (norm_oscBs_le hrb hPb hEb N t θ) (norm_nonneg _) hM

lemma ae_norm_Hd_le {Hd : ℝ → ℂ} {M : ℝ} (hHdb : ∀ t ∈ Set.Ioc (0:ℝ) 1, ‖Hd t‖ ≤ M) :
    ∀ᵐ t ∂mu01, ‖Hd t‖ ≤ M := by
  rw [mu01, ae_restrict_iff' measurableSet_Ioc]
  exact Filter.Eventually.of_forall fun t ht => hHdb t ht

lemma integrable_oscGs {Hd r P E : ℝ → ℂ} {cap M S : ℝ} (hM : 0 ≤ M) (hHd : Measurable Hd)
    (hr : Measurable r) (hP : Measurable P) (hE : Measurable E) (hrb : ∀ θ, ‖r θ‖ ≤ cap)
    (hPb : ∀ θ, ‖P θ‖ ≤ S) (hEb : ∀ θ, ‖E θ‖ = 1)
    (hHdb : ∀ t ∈ Set.Ioc (0:ℝ) 1, ‖Hd t‖ ≤ M) (N : ℝ) :
    Integrable (Function.uncurry (oscGs Hd r P E N)) (mu01.prod mu01) := by
  refine Integrable.of_bound (measurable_oscGs hHd hr hP hE N).aestronglyMeasurable
    (M * (cap * S)) ?_
  have hprod : mu01.prod mu01
      = (volume.prod volume).restrict (Set.Ioc (0:ℝ) 1 ×ˢ Set.Ioc (0:ℝ) 1) := by
    rw [mu01, Measure.prod_restrict]
  rw [hprod, ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)]
  refine Filter.Eventually.of_forall fun p hp => ?_
  rw [Set.mem_prod] at hp
  simpa only [Function.uncurry] using norm_oscGs_le hM hrb hPb hEb p.1 p.2 (hHdb p.2 hp.2)

lemma integrable_Hd_mul_oscBs {Hd r P E : ℝ → ℂ} {cap M S : ℝ} (hM : 0 ≤ M) (hHd : Measurable Hd)
    (hr : Measurable r) (hP : Measurable P) (hE : Measurable E) (hrb : ∀ θ, ‖r θ‖ ≤ cap)
    (hPb : ∀ θ, ‖P θ‖ ≤ S) (hEb : ∀ θ, ‖E θ‖ = 1)
    (hHdb : ∀ t ∈ Set.Ioc (0:ℝ) 1, ‖Hd t‖ ≤ M) (N : ℝ) :
    Integrable (fun t => Hd t * (∫ θ, oscBs r P E N t θ ∂mu01)) mu01 := by
  refine (integrable_oscGs hM hHd hr hP hE hrb hPb hEb hHdb N).integral_prod_right.congr ?_
  filter_upwards with t
  show (∫ θ, Hd t * oscBs r P E N t θ ∂mu01) = Hd t * ∫ θ, oscBs r P E N t θ ∂mu01
  rw [integral_const_mul]

/-- **One-sided Fubini identity.**  For a positive scale `N`, the dilation-profile average of `H₁`
against the weight `r` and the trigonometric data `P · E` equals minus the `t`-integral of the cut
family. -/
lemma profFam_int_eq_neg_integral_oscBs {cap M S : ℝ} (hM : 0 ≤ M) {Hd H₁ r P E : ℝ → ℂ}
    (hHd : Measurable Hd) (hr : Measurable r) (hP : Measurable P) (hE : Measurable E)
    (hrb : ∀ θ, ‖r θ‖ ≤ cap) (hPb : ∀ θ, ‖P θ‖ ≤ S) (hEb : ∀ θ, ‖E θ‖ = 1)
    (hH₁ : ∀ u : ℝ, 0 < u → H₁ u = -∫ t in (0:ℝ)..1, Hd t * (if u ≤ t then (1:ℂ) else 0))
    (hHdb : ∀ t ∈ Set.Ioc (0:ℝ) 1, ‖Hd t‖ ≤ M) (N : ℝ) (hN : 0 < N) :
    (∫ θ, (r θ * H₁ (N * θ)) * P θ * E θ ∂mu01)
      = -∫ t, Hd t * (∫ θ, oscBs r P E N t θ ∂mu01) ∂mu01 := by
  have hpt : (fun θ => (r θ * H₁ (N * θ)) * P θ * E θ) =ᵐ[mu01]
      (fun θ => -∫ t, oscGs Hd r P E N θ t ∂mu01) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    have hθpos : 0 < θ := hθ.1
    have hu : 0 < N * θ := mul_pos hN hθpos
    have hInt : (∫ t, oscGs Hd r P E N θ t ∂mu01)
        = -(r θ * (P θ * E θ)) * H₁ (N * θ) := by
      rw [show (∫ t, oscGs Hd r P E N θ t ∂mu01)
          = ∫ t, (r θ * (P θ * E θ)) * (Hd t * (if N * θ ≤ t then (1:ℂ) else 0)) ∂mu01 from by
            apply integral_congr_ae
            filter_upwards with t
            simp only [oscGs, oscBs]
            ring]
      rw [integral_const_mul]
      have h2 : (∫ t, Hd t * (if N * θ ≤ t then (1:ℂ) else 0) ∂mu01) = -H₁ (N * θ) := by
        rw [hH₁ (N * θ) hu, intervalIntegral_eq_mu01, neg_neg]
      rw [h2]
      ring
    rw [hInt]
    ring
  rw [integral_congr_ae hpt, integral_neg,
    integral_integral_swap (integrable_oscGs hM hHd hr hP hE hrb hPb hEb hHdb N), neg_inj]
  apply integral_congr_ae
  filter_upwards with t
  show (∫ θ, Hd t * oscBs r P E N t θ ∂mu01) = Hd t * ∫ θ, oscBs r P E N t θ ∂mu01
  rw [integral_const_mul]

theorem profFamM_sub_eq_integral_cutFamM (ρ : ℝ) (hρ : 1 < ρ) (cap M : ℝ) (hcap : 0 ≤ cap)
    (hM : 0 ≤ M) (Hd H₁ r : ℝ → ℂ) (f : ℤ → ℂ) (T : Finset ℤ) (hHd : Measurable Hd)
    (hr : Measurable r) (hrb : ∀ θ, ‖r θ‖ ≤ cap)
    (hH₁ : ∀ u : ℝ, 0 < u → H₁ u = -∫ t in (0:ℝ)..1, Hd t * (if u ≤ t then (1:ℂ) else 0))
    (hHdb : ∀ t ∈ Set.Ioc (0:ℝ) 1, ‖Hd t‖ ≤ M) (i i' : ℕ) (x : ℤ) :
    Work.BourgainPlan.Oscillation.Lacunary.profFamM H₁ r f T ρ i x
        - Work.BourgainPlan.Oscillation.Lacunary.profFamM H₁ r f T ρ i' x
      = -∫ t, Hd t * (Work.BourgainPlan.Oscillation.Lacunary.cutFamM t r f T ρ i x
          - Work.BourgainPlan.Oscillation.Lacunary.cutFamM t r f T ρ i' x)
        ∂Work.BourgainPlan.Oscillation.Lacunary.mu01 := by
  set Ni : ℝ := (lacScale ρ i : ℝ) with hNi_def
  set Ni' : ℝ := (lacScale ρ i' : ℝ) with hNi'_def
  have hNi : 0 < Ni := by rw [hNi_def]; exact lacScale_pos_real ρ hρ i
  have hNi' : 0 < Ni' := by rw [hNi'_def]; exact lacScale_pos_real ρ hρ i'
  set P : ℝ → ℂ := trigP T f with hP_def
  set E : ℝ → ℂ := Echar x with hE_def
  set S : ℝ := ∑ j ∈ T, ‖f j‖ with hS_def
  have hPb : ∀ θ, ‖P θ‖ ≤ S := by intro θ; rw [hP_def, hS_def]; exact norm_trigP_le T f θ
  have hEb : ∀ θ, ‖E θ‖ = 1 := by intro θ; rw [hE_def]; exact norm_Echar x θ
  have hPm : Measurable P := by rw [hP_def]; exact measurable_trigP T f
  have hEm : Measurable E := by rw [hE_def]; exact (continuous_Echar x).measurable
  -- the two one-sided Fubini identities
  have hmain_i : profFamM H₁ r f T ρ i x
      = -∫ t, Hd t * (∫ θ, oscBs r P E Ni t θ ∂mu01) ∂mu01 := by
    change (∫ θ, (r θ * H₁ (Ni * θ)) * P θ * E θ ∂mu01) = _
    exact profFam_int_eq_neg_integral_oscBs hM hHd hr hPm hEm hrb hPb hEb hH₁ hHdb Ni hNi
  have hmain_i' : profFamM H₁ r f T ρ i' x
      = -∫ t, Hd t * (∫ θ, oscBs r P E Ni' t θ ∂mu01) ∂mu01 := by
    change (∫ θ, (r θ * H₁ (Ni' * θ)) * P θ * E θ ∂mu01) = _
    exact profFam_int_eq_neg_integral_oscBs hM hHd hr hPm hEm hrb hPb hEb hH₁ hHdb Ni' hNi'
  -- the cut family is the `oscBs`-integral
  have hcut_i : ∀ t : ℝ, (∫ θ, oscBs r P E Ni t θ ∂mu01) = cutFamM t r f T ρ i x := by
    intro t
    apply integral_congr_ae
    filter_upwards with θ
    simp only [oscBs]
    have hiff : (Ni * θ ≤ t) ↔ (θ ≤ t / Ni) := by rw [le_div_iff₀ hNi, mul_comm]
    by_cases h : Ni * θ ≤ t
    · rw [if_pos h, if_pos (hiff.mp h)]; ring
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]; ring
  have hcut_i' : ∀ t : ℝ, (∫ θ, oscBs r P E Ni' t θ ∂mu01) = cutFamM t r f T ρ i' x := by
    intro t
    apply integral_congr_ae
    filter_upwards with θ
    simp only [oscBs]
    have hiff : (Ni' * θ ≤ t) ↔ (θ ≤ t / Ni') := by rw [le_div_iff₀ hNi', mul_comm]
    by_cases h : Ni' * θ ≤ t
    · rw [if_pos h, if_pos (hiff.mp h)]; ring
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]; ring
  have hInt_i : Integrable (fun t => Hd t * (∫ θ, oscBs r P E Ni t θ ∂mu01)) mu01 :=
    integrable_Hd_mul_oscBs hM hHd hr hPm hEm hrb hPb hEb hHdb Ni
  have hInt_i' : Integrable (fun t => Hd t * (∫ θ, oscBs r P E Ni' t θ ∂mu01)) mu01 :=
    integrable_Hd_mul_oscBs hM hHd hr hPm hEm hrb hPb hEb hHdb Ni'
  have step : (∫ t, Hd t * (∫ θ, oscBs r P E Ni t θ ∂mu01) ∂mu01)
      - (∫ t, Hd t * (∫ θ, oscBs r P E Ni' t θ ∂mu01) ∂mu01)
      = ∫ t, Hd t * (cutFamM t r f T ρ i x - cutFamM t r f T ρ i' x) ∂mu01 := by
    rw [← integral_sub hInt_i hInt_i']
    apply integral_congr_ae
    filter_upwards with t
    rw [hcut_i t, hcut_i' t]
    ring
  rw [hmain_i, hmain_i', ← step]
  ring

end

end Work.BourgainPlan.Oscillation.Lacunary
