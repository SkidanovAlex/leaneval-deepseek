import Submission.ThreePages
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# The lower bound on ∫ log ρ_n dμ (`EnergyDeliver`)

`ρ_n(x) = min_{1≤i≤n} |x − α_{n,i}|` (roots `α_{n,i}`, `1≤i≤n`; see
`Submission/ThreePages.lean`), `μ = muS` = the Serre probability measure on
`[aSerre,bSerre]` (atom-free, 1/2-Hölder).  Prove:

    ∃ C > 0, ∀ n ≥ 2,  −C·log(n+2) ≤ ∫_ℝ log(ρ_n x) dμ(x).

## Route used here

* Step 0: `log ∘ rho` is integrable (dominated by the finite sum of
  `|log|x − α_i||`, each integrable by `PotentialContinuity.logAbs_integrable`).
* Step 1: for any `δ > 0`, the mass of `{x | ρ_n(x) ≤ r}` is at most
  `n·Cmu·√(2r)` (`0 ≤ r`): `{ρ ≤ r} ⊆ ⋃_k ball(α_k, r)` and
  `ThreePages.Mball_le`.
* Step 2: pointwise `log ρ_n(x) ≥ log δ − h(x)` with
  `h(x) = max (log δ − log ρ_n(x)) 0`.
* Step 3: real layer cake (`Integral.integral_eq_integral_meas_le`):
  `∫h = ∫_{t>0} μ.real {a | t ≤ h a}`; for `t>0`,
  `{a | t ≤ h a} ⊆ {a | ρ_n(a) ≤ δ·e^{-t}}`, so
  `∫h ≤ ∫_{t>0} n·Cmu·√(2δe^{-t}) = 2·n·Cmu·√(2δ)`.
* Step 4: choose `δ := ((Csp·n)⁻¹)²/3` with the spacing constant `Csp ≥ 1`
  from `Quantile.exists_spacing` (only the bound `Csp ≥ 1` is used); then
  `n·√(2δ) ≤ 1`, `log δ = −2log(Csp·n) − log 3`, and the claim follows with
  `C := 2 + (2·log Csp + log 3 + 2·Cmu)/log 4`.
-/

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory
open scoped Real BigOperators

namespace Submission.EnergyDeliver

open Submission.Quantile
open Submission.PotentialContinuity
open Submission.SerreExample
open Submission.ThreePages
open Submission.PotentialDefs

/-- `rho n` is continuous in `x` (it is 1-Lipschitz). -/
lemma rho_continuous (n : ℕ) : Continuous (fun x : ℝ => rho n x) := by
  by_cases hn : 1 ≤ n
  · have hlip : LipschitzWith 1 (fun x : ℝ => rho n x) := by
      rw [lipschitzWith_iff_dist_le_mul]
      intro x y
      rw [Real.dist_eq, Real.dist_eq]
      norm_num
      have h1 : rho n x ≤ rho n y + |x - y| := by
        rcases exists_index_rho n hn y with ⟨j, hj, hrj⟩
        calc
          rho n x ≤ |x - alpha n j| := rho_le_root hn x hj
          _ = |x - y + (y - alpha n j)| := by congr 1; ring
          _ ≤ |x - y| + |y - alpha n j| := abs_add_le _ _
          _ = rho n y + |x - y| := by rw [hrj]; ring
      have h2 : rho n y ≤ rho n x + |x - y| := by
        rcases exists_index_rho n hn x with ⟨i, hi, hri⟩
        calc
          rho n y ≤ |y - alpha n i| := rho_le_root hn y hi
          _ = |y - x + (x - alpha n i)| := by congr 1; ring
          _ ≤ |y - x| + |x - alpha n i| := abs_add_le _ _
          _ = rho n x + |x - y| := by
            rw [abs_sub_comm, ← hri]
            ring
      have hxy1 : rho n x - rho n y ≤ |x - y| := by linarith
      have hxy2 : rho n y - rho n x ≤ |x - y| := by linarith
      exact abs_le.mpr ⟨by linarith, hxy1⟩
    exact hlip.continuous
  · have hn0 : n = 0 := by omega
    subst n
    have hconst : (fun x : ℝ => rho 0 x) = fun _ : ℝ => 0 := by
      funext x
      unfold rho
      have hnot : ¬ (Finset.Icc 1 0).Nonempty := by
        intro h
        rcases h with ⟨j, hj⟩
        simp at hj
      rw [dif_neg hnot]
    rw [hconst]
    exact continuous_const

/-- `rho n x` is measurable in `x`. -/
lemma rho_measurable (n : ℕ) : Measurable (fun x : ℝ => rho n x) :=
  (rho_continuous n).measurable

/-- `|log ρ_n(x)| ≤ ∑_{i=1}^n |log|x − α_i||`. -/
lemma abs_log_rho_le_sum {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    |Real.log (rho n x)| ≤ ∑ i ∈ Finset.Icc 1 n, |Real.log (|x - alpha n i|)| := by
  rcases exists_index_rho n hn x with ⟨i0, hi0, hrho⟩
  rw [hrho]
  exact Finset.single_le_sum (s := Finset.Icc 1 n)
    (f := fun i : ℕ => |Real.log (|x - alpha n i|)|) (fun i hi => abs_nonneg _) hi0

/-- A finite sum of integrable functions (w.r.t. `muS`) is integrable. -/
lemma integrable_finset_sum {ι : Type*} [DecidableEq ι] (f : ι → ℝ → ℝ) (s : Finset ι)
    (hf : ∀ i ∈ s, MeasureTheory.Integrable (f i) muS) :
    MeasureTheory.Integrable (fun x : ℝ => ∑ i ∈ s, f i x) muS := by
  classical
  exact (Finset.induction_on (motive := fun t : Finset ι => t ⊆ s →
      MeasureTheory.Integrable (fun x : ℝ => ∑ i ∈ t, f i x) muS) s
    (by
      intro hts
      simp)
    (by
      intro a t hat ih hsubs
      have hfun : (fun x : ℝ => ∑ i ∈ insert a t, f i x)
          = fun x : ℝ => f a x + (∑ i ∈ t, f i x) := by
        funext x
        rw [Finset.sum_insert hat]
      rw [hfun]
      exact ((hf a (hsubs (Finset.mem_insert_self a t))).add
        (ih (fun i hi => hsubs (Finset.mem_insert_of_mem hi)))))
    (by intro i hi; exact hi))

/-- `x ↦ Real.log (ρ_n(x))` is integrable w.r.t. `muS`. -/
lemma log_rho_integrable {n : ℕ} (hn : 1 ≤ n) :
    MeasureTheory.Integrable (fun x : ℝ => Real.log (rho n x)) muS := by
  let g : ℝ → ℝ := fun x => ∑ i ∈ Finset.Icc 1 n, |Real.log (|x - alpha n i|)|
  have hg : MeasureTheory.Integrable g muS := by
    dsimp [g]
    exact integrable_finset_sum (f := fun i : ℕ => fun x : ℝ => |Real.log (|x - alpha n i|)|)
      (Finset.Icc 1 n) (by
        intro i hi
        simpa [abs_sub_comm] using (logAbs_integrable (alpha n i)))
  refine MeasureTheory.Integrable.mono' hg ?_ ?_
  · exact (Real.measurable_log.comp (rho_measurable n)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun x => ?_)
    simpa [g, Real.norm_eq_abs] using (abs_log_rho_le_sum hn x)

/-- `x ↦ max (log δ − log ρ_n(x)) 0` is integrable. -/
lemma h_integrable {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) :
    MeasureTheory.Integrable
      (fun x : ℝ => max (Real.log δ - Real.log (rho n x)) 0) muS := by
  let b : ℝ → ℝ := fun x => |Real.log δ| + |Real.log (rho n x)|
  have hb_int : MeasureTheory.Integrable b muS := by
    dsimp [b]
    exact (MeasureTheory.integrable_const |Real.log δ|).add
      (MeasureTheory.Integrable.abs (log_rho_integrable hn))
  have hf_meas : Measurable
      (fun x : ℝ => max (Real.log δ - Real.log (rho n x)) 0) := by
    have hlogrho_meas : Measurable (fun x : ℝ => Real.log (rho n x)) :=
      Real.measurable_log.comp (rho_measurable n)
    have hsub_meas : Measurable (fun x : ℝ => Real.log δ - Real.log (rho n x)) := by
      fun_prop
    exact Measurable.max hsub_meas (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ)))
  refine MeasureTheory.Integrable.mono' hb_int hf_meas.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  have htri : |Real.log δ - Real.log (rho n x)| ≤ |Real.log δ| + |Real.log (rho n x)| := by
    have h := abs_add_le (Real.log δ) (-Real.log (rho n x))
    simpa [sub_eq_add_neg, abs_neg] using h
  have hmx : max (Real.log δ - Real.log (rho n x)) 0 ≤ |Real.log δ - Real.log (rho n x)| := by
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hnn : 0 ≤ max (Real.log δ - Real.log (rho n x)) 0 := le_max_right _ _
  have h1 : |max (Real.log δ - Real.log (rho n x)) 0| ≤ |Real.log δ| + |Real.log (rho n x)| := by
    rw [abs_of_nonneg hnn]
    exact le_trans hmx htri
  simpa [b, Real.norm_eq_abs] using h1

/-- Mass of the `r`-neighbourhood of the root set:
`μ {x | ρ_n(x) ≤ r} ≤ n · Cmu · √(2r)` for `0 ≤ r`. -/
lemma real_measure_rho_le_mul {n : ℕ} (hn : 1 ≤ n) (r : ℝ) (hr : 0 ≤ r) :
    (muS {x : ℝ | rho n x ≤ r}).toReal ≤
      (n : ℝ) * Cmu * Real.sqrt (2 * r) := by
  classical
  let balls : ℕ → Set ℝ := fun i => Set.Icc (alpha n i - r) (alpha n i + r)
  have hsub : {x : ℝ | rho n x ≤ r} ⊆ ⋃ i ∈ Finset.Icc 1 n, balls i := by
    intro x hx
    rcases exists_index_rho n hn x with ⟨i0, hi0, hrho⟩
    refine Set.mem_iUnion₂.mpr ⟨i0, ?_, ?_⟩
    · simpa using hi0
    · have hle : |x - alpha n i0| ≤ r := by
        rw [← hrho]
        exact hx
      rw [Set.mem_Icc]
      rcases abs_le.mp hle with ⟨h1, h2⟩
      constructor <;> nlinarith
  calc
    (muS {x : ℝ | rho n x ≤ r}).toReal
        ≤ (muS (⋃ i ∈ Finset.Icc 1 n, balls i)).toReal := by
          exact Quantile.toReal_mono hsub
    _ ≤ (∑ i ∈ Finset.Icc 1 n, muS (balls i)).toReal := by
          apply (ENNReal.toReal_le_toReal ?_ ?_).2
          · exact measure_biUnion_finset_le (Finset.Icc 1 n) balls
          · exact (muS_lt_top _).ne
          · exact ne_of_lt (ENNReal.sum_lt_top.mpr (by
              intro i hi
              exact muS_lt_top (balls i)))
    _ = ∑ i ∈ Finset.Icc 1 n, (muS (balls i)).toReal := by
          exact ENNReal.toReal_sum (by intro i hi; exact (muS_lt_top (balls i)).ne)
    _ ≤ ∑ i ∈ Finset.Icc 1 n, (Cmu * Real.sqrt (2 * r)) := by
          exact Finset.sum_le_sum (by
            intro i hi
            simpa [balls, Mball] using (Mball_le (alpha n i) r hr))
    _ = (n : ℝ) * (Cmu * Real.sqrt (2 * r)) := by
          have hcard : (Finset.Icc 1 n).card = n := by
            rw [Nat.card_Icc]
            omega
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ = (n : ℝ) * Cmu * Real.sqrt (2 * r) := by ring

/-- `√(e^{-t}) = e^{-t/2}` (ThreePages). -/
lemma sqrt_exp_neg_deliver (t : ℝ) : Real.sqrt (Real.exp (-t)) = Real.exp (-t / 2) := by
  exact sqrt_exp_neg t

/-- The `μ`-average of `h(x) = max (log δ − log ρ_n x) 0` is at most
`2·n·Cmu·√(2δ)` (layer cake + mass bound on the sublevel sets). -/
lemma integral_h_bound {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) (hδ0 : 0 < δ) :
    (∫ x : ℝ, max (Real.log δ - Real.log (rho n x)) 0 ∂muS) ≤
      2 * (n : ℝ) * Cmu * Real.sqrt (2 * δ) := by
  let h : ℝ → ℝ := fun x => max (Real.log δ - Real.log (rho n x)) 0
  have hh_int : MeasureTheory.Integrable (fun x : ℝ => h x) muS := by
    simpa [h] using (h_integrable hn δ)
  have hh_nn : 0 ≤ᵐ[muS] (fun x : ℝ => h x) :=
    MeasureTheory.ae_of_all muS (by intro x; dsimp [h]; exact le_max_right _ _)
  let f1 : ℝ → ℝ := fun t => (muS {a : ℝ | t ≤ h a}).toReal
  have hLC : (∫ x : ℝ, h x ∂muS) = (∫ t : ℝ in Set.Ioi 0, f1 t) := by
    calc
      (∫ x : ℝ, h x ∂muS)
          = (∫ t : ℝ in Set.Ioi 0, muS.real {a : ℝ | t ≤ h a}) := by
            rw [MeasureTheory.Integrable.integral_eq_integral_meas_le (μ := muS)
              (f := fun x : ℝ => h x) hh_int hh_nn]
      _ = (∫ t : ℝ in Set.Ioi 0, f1 t) := by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            dsimp [f1]
            rw [MeasureTheory.Measure.real_def]
  have htail : ∀ t : ℝ, 0 < t →
      f1 t ≤ (n : ℝ) * Cmu * Real.sqrt (2 * (δ * Real.exp (-t))) := by
    intro t ht0
    have hsub : {a : ℝ | t ≤ h a} ⊆ {a : ℝ | rho n a ≤ δ * Real.exp (-t)} := by
      intro a ha
      dsimp [h] at ha
      have hx : t ≤ Real.log δ - Real.log (rho n a) := by
        by_contra hbad
        have hlt : Real.log δ - Real.log (rho n a) < t := lt_of_not_ge hbad
        have hmaxlt : max (Real.log δ - Real.log (rho n a)) 0 < t := max_lt hlt ht0
        have hcon : False := by linarith
        exact hcon
      have hlogrho_le : Real.log (rho n a) ≤ Real.log δ - t := by linarith
      change rho n a ≤ δ * Real.exp (-t)
      by_cases hr : 0 < rho n a
      · have hleexp : rho n a ≤ Real.exp (Real.log δ - t) :=
          (Real.log_le_iff_le_exp hr).mp hlogrho_le
        have he : Real.exp (Real.log δ - t) = δ * Real.exp (-t) := by
          calc
            Real.exp (Real.log δ - t) = Real.exp (Real.log δ + -t) := by
              rw [sub_eq_add_neg]
            _ = Real.exp (Real.log δ) * Real.exp (-t) := Real.exp_add _ _
            _ = δ * Real.exp (-t) := by rw [Real.exp_log hδ0]
        rwa [he] at hleexp
      · have hr0 : rho n a = 0 := by
          have hle0 : rho n a ≤ 0 := le_of_not_gt hr
          exact le_antisymm hle0 (rho_nonneg a)
        rw [hr0]
        exact mul_nonneg (le_of_lt hδ0) (Real.exp_pos (-t)).le
    have hmono : (muS {a : ℝ | t ≤ h a}).toReal ≤
        (muS {a : ℝ | rho n a ≤ δ * Real.exp (-t)}).toReal :=
      Quantile.toReal_mono hsub
    have hmass : (muS {a : ℝ | rho n a ≤ δ * Real.exp (-t)}).toReal ≤
        (n : ℝ) * Cmu * Real.sqrt (2 * (δ * Real.exp (-t))) :=
      real_measure_rho_le_mul (n := n) hn (δ * Real.exp (-t))
        (mul_nonneg (le_of_lt hδ0) (Real.exp_pos (-t)).le)
    dsimp [f1]
    exact le_trans hmono hmass
  let e : ℝ → ℝ := fun t => (n : ℝ) * Cmu * Real.sqrt (2 * δ) * Real.exp (-t / 2)
  have heq_sqrt : ∀ t : ℝ, (n : ℝ) * Cmu * Real.sqrt (2 * (δ * Real.exp (-t))) = e t := by
    intro t
    have hsq : Real.sqrt (2 * (δ * Real.exp (-t))) = Real.sqrt (2 * δ) * Real.exp (-t / 2) := by
      calc
        Real.sqrt (2 * (δ * Real.exp (-t)))
            = Real.sqrt ((2 * δ) * Real.exp (-t)) := by congr 1; ring
        _ = Real.sqrt (2 * δ) * Real.sqrt (Real.exp (-t)) :=
              Real.sqrt_mul (mul_nonneg (by norm_num) (le_of_lt hδ0)) (Real.exp (-t))
        _ = Real.sqrt (2 * δ) * Real.exp (-t / 2) := by rw [sqrt_exp_neg_deliver t]
    dsimp [e]
    rw [hsq]
    ring
  have hbase : MeasureTheory.IntegrableOn (fun s : ℝ => Real.exp (-s / 2)) (Set.Ioi 0) volume := by
    have hident : (fun s : ℝ => Real.exp (-s / 2)) = fun s : ℝ => Real.exp (-(1 / 2 : ℝ) * s) := by
      funext s
      congr 1
      ring
    rw [hident]
    exact integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) 0
  have he_int : MeasureTheory.IntegrableOn e (Set.Ioi 0) volume := by
    change MeasureTheory.Integrable (fun t : ℝ => e t) (volume.restrict (Set.Ioi 0))
    dsimp [e]
    exact hbase.const_mul ((n : ℝ) * Cmu * Real.sqrt (2 * δ))
  have hf1_nn : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] f1 := by
    exact MeasureTheory.ae_of_all (volume.restrict (Set.Ioi 0))
      (fun t => ENNReal.toReal_nonneg)
  have hf1_le : ∀ t : ℝ, 0 < t → f1 t ≤ e t := by
    intro t ht
    rw [← heq_sqrt t]
    exact htail t ht
  have hf1_le_ae : f1 ≤ᵐ[volume.restrict (Set.Ioi 0)] e := by
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2
      (MeasureTheory.ae_of_all volume (fun t => hf1_le t))
  have hmono2 : (∫ t : ℝ in Set.Ioi 0, f1 t) ≤ (∫ t : ℝ in Set.Ioi 0, e t) := by
    simpa using (MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict (Set.Ioi 0)) (f := f1) (g := e) hf1_nn he_int hf1_le_ae)
  have hE : (∫ t : ℝ in Set.Ioi 0, Real.exp (-t / 2)) = 2 := by
    have hφ : (fun s : ℝ => Real.exp (-s / 2)) = fun s : ℝ => Real.exp (-(1 / 2 : ℝ) * s) := by
      funext s
      congr 1
      ring
    rw [hφ]
    rw [integral_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) 0]
    norm_num
  have hval : (∫ t : ℝ in Set.Ioi 0, e t) = 2 * (n : ℝ) * Cmu * Real.sqrt (2 * δ) := by
    dsimp [e]
    rw [MeasureTheory.integral_const_mul]
    rw [hE]
    ring
  have hres : (∫ x : ℝ, h x ∂muS) ≤ 2 * (n : ℝ) * Cmu * Real.sqrt (2 * δ) := by
    calc
      (∫ x : ℝ, h x ∂muS) = (∫ t : ℝ in Set.Ioi 0, f1 t) := hLC
      _ ≤ (∫ t : ℝ in Set.Ioi 0, e t) := hmono2
      _ = 2 * (n : ℝ) * Cmu * Real.sqrt (2 * δ) := hval
  simpa [h] using hres

/-- For `0 < δ`, the average of `log ρ_n` is at least `log δ − 2n·Cmu·√(2δ)`. -/
lemma integral_log_rho_ge (n : ℕ) (hn2 : 2 ≤ n) (δ : ℝ) (hδ0 : 0 < δ) :
    Real.log δ - 2 * (n : ℝ) * Cmu * Real.sqrt (2 * δ) ≤
      ∫ x : ℝ, Real.log (rho n x) ∂muS := by
  have hn1 : 1 ≤ n := by omega
  let h : ℝ → ℝ := fun x => max (Real.log δ - Real.log (rho n x)) 0
  have hpt : ∀ᵐ x ∂muS, Real.log δ - h x ≤ Real.log (rho n x) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    dsimp [h]
    by_cases ha : Real.log δ - Real.log (rho n x) ≤ 0
    · have hmax : max (Real.log δ - Real.log (rho n x)) 0 = 0 := max_eq_right ha
      rw [hmax]
      linarith
    · have hpos : 0 < Real.log δ - Real.log (rho n x) := lt_of_not_ge ha
      have hmax : max (Real.log δ - Real.log (rho n x)) 0 =
          Real.log δ - Real.log (rho n x) := max_eq_left (le_of_lt hpos)
      rw [hmax]
      linarith
  have hh_int : MeasureTheory.Integrable (fun x : ℝ => h x) muS := by
    simpa [h] using (h_integrable hn1 δ)
  have hlog_int : MeasureTheory.Integrable (fun x : ℝ => Real.log (rho n x)) muS :=
    log_rho_integrable hn1
  have hmain_ineq : (∫ x : ℝ, Real.log δ - h x ∂muS) ≤
      (∫ x : ℝ, Real.log (rho n x) ∂muS) := by
    exact MeasureTheory.integral_mono_ae
      ((MeasureTheory.integrable_const (Real.log δ)).sub hh_int) hlog_int hpt
  have hconst : (∫ x : ℝ, Real.log δ - h x ∂muS) = Real.log δ - (∫ x : ℝ, h x ∂muS) := by
    rw [MeasureTheory.integral_sub (MeasureTheory.integrable_const (Real.log δ)) hh_int]
    rw [MeasureTheory.integral_const]
    simp
  have hhb : (∫ x : ℝ, h x ∂muS) ≤ 2 * (n : ℝ) * Cmu * Real.sqrt (2 * δ) := by
    simpa [h] using (integral_h_bound (n := n) hn1 δ hδ0)
  have hcalc1 : Real.log δ - 2 * (n : ℝ) * Cmu * Real.sqrt (2 * δ) ≤
      Real.log δ - (∫ x : ℝ, h x ∂muS) := by linarith
  have htmp : Real.log δ - (∫ x : ℝ, h x ∂muS) ≤
      (∫ x : ℝ, Real.log (rho n x) ∂muS) := by
    rw [← hconst]
    exact hmain_ineq
  exact le_trans hcalc1 htmp

/-- `n·√(2δ) ≤ 1` for `δ = ((Csp·n)⁻¹)²/3`, `Csp ≥ 1`, `n ≥ 2`. -/
lemma n_sqrt_two_delta_le_one (Csp δ : ℝ) (n : ℕ) (hCsp : 1 ≤ Csp) (hn : 2 ≤ n)
    (hδ : δ = ((Csp * (n : ℝ))⁻¹ ^ 2) / 3) :
    (n : ℝ) * Real.sqrt (2 * δ) ≤ 1 := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hCsp0 : 0 < Csp := by linarith
  have h2δ : 2 * δ ≤ (Csp * (n : ℝ))⁻¹ ^ 2 := by
    rw [hδ]
    have hx0 : 0 ≤ (Csp * (n : ℝ))⁻¹ ^ 2 := by positivity
    have hc : 2 * (((Csp * (n : ℝ))⁻¹ ^ 2) / 3) = ((Csp * (n : ℝ))⁻¹ ^ 2) * (2 / 3) := by ring
    rw [hc]
    nlinarith
  have hsqrtle : Real.sqrt (2 * δ) ≤ Real.sqrt ((Csp * (n : ℝ))⁻¹ ^ 2) := by
    exact Real.sqrt_le_sqrt h2δ
  have hsqid : Real.sqrt ((Csp * (n : ℝ))⁻¹ ^ 2) = (Csp * (n : ℝ))⁻¹ := by
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg (inv_nonneg.mpr (mul_nonneg (le_of_lt hCsp0) (le_of_lt hn0)))]
  have hsq : Real.sqrt (2 * δ) ≤ (Csp * (n : ℝ))⁻¹ := by
    rwa [hsqid] at hsqrtle
  have hmul := mul_le_mul_of_nonneg_left hsq (le_of_lt hn0)
  have hcancel : (n : ℝ) * (Csp * (n : ℝ))⁻¹ = Csp⁻¹ := by
    field_simp [hn0.ne', hCsp0.ne']
  rw [hcancel] at hmul
  have hle : Csp⁻¹ ≤ 1 := by
    rw [← one_div]
    exact (div_le_iff₀ hCsp0).2 (by simpa using hCsp)
  exact le_trans hmul hle

/-- `log δ = −2log Csp − 2log n − log 3` for `δ = ((Csp·n)⁻¹)²/3`. -/
lemma log_delta (Csp : ℝ) (n : ℕ) (δ : ℝ) (hCsp0 : 0 < Csp) (hn0 : 0 < (n : ℝ))
    (hδ : δ = ((Csp * (n : ℝ))⁻¹ ^ 2) / 3) :
    Real.log δ = -2 * Real.log Csp - 2 * Real.log (n : ℝ) - Real.log 3 := by
  have hcspn0 : (Csp * (n : ℝ)) ≠ 0 := by
    exact mul_ne_zero (ne_of_gt hCsp0) (ne_of_gt hn0)
  calc
    Real.log δ = Real.log (((Csp * (n : ℝ))⁻¹ ^ 2) / 3) := by rw [hδ]
    _ = Real.log ((Csp * (n : ℝ))⁻¹ ^ 2) - Real.log 3 := by
          rw [Real.log_div (pow_ne_zero 2 (inv_ne_zero hcspn0)) (by norm_num : (3 : ℝ) ≠ 0)]
    _ = 2 * Real.log ((Csp * (n : ℝ))⁻¹) - Real.log 3 := by rw [Real.log_pow]; norm_num
    _ = 2 * (-Real.log (Csp * (n : ℝ))) - Real.log 3 := by rw [Real.log_inv]
    _ = -2 * Real.log (Csp * (n : ℝ)) - Real.log 3 := by ring
    _ = -2 * (Real.log Csp + Real.log (n : ℝ)) - Real.log 3 := by
          rw [Real.log_mul (ne_of_gt hCsp0) (ne_of_gt hn0)]
    _ = -2 * Real.log Csp - 2 * Real.log (n : ℝ) - Real.log 3 := by ring

/-- `eq:deliver_me` (see EnergyHalf.lean). -/
theorem deliver_me :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      -C * Real.log ((n : ℝ) + 2) ≤
        ∫ x : ℝ, Real.log (rho n x) ∂muS := by
  rcases Quantile.exists_spacing with ⟨Csp, hCsp1, _hspacing⟩
  let B : ℝ := 2 * Real.log Csp + Real.log 3 + 2 * Cmu
  have hCsp0 : 0 < Csp := by linarith
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    have h1 : 0 ≤ 2 * Real.log Csp := mul_nonneg (by norm_num) (Real.log_nonneg hCsp1)
    have h2 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ (3 : ℝ))
    have h3 : 0 ≤ 2 * Cmu := mul_nonneg (by norm_num) (le_of_lt Cmu_pos)
    linarith
  refine ⟨2 + B / Real.log 4, ?_, ?_⟩
  · have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < (4 : ℝ))
    have hdiv : 0 ≤ B / Real.log 4 := div_nonneg hB_nonneg (le_of_lt hlog4)
    linarith
  · intro n hn2
    let L2 : ℝ := Real.log ((n : ℝ) + 2)
    let δ : ℝ := ((Csp * (n : ℝ))⁻¹ ^ 2) / 3
    have hn0R : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hδ0 : 0 < δ := by
      dsimp [δ]
      positivity
    have hδ1 : δ ≤ 1 := by
      have hge2 : 2 ≤ Csp * (n : ℝ) := by
        have hnR2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
        nlinarith [hCsp1, hnR2]
      have hinv : (Csp * (n : ℝ))⁻¹ ≤ (1 / 2 : ℝ) := by
        have hpos2 : (0 : ℝ) < 2 := by norm_num
        have hpos : 0 < Csp * (n : ℝ) := mul_pos hCsp0 hn0R
        simpa [one_div] using ((inv_le_inv₀ hpos hpos2).mpr hge2)
      have hpow : ((Csp * (n : ℝ))⁻¹) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
        exact pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt (mul_pos hCsp0 hn0R))) hinv 2
      have hle3 : ((Csp * (n : ℝ))⁻¹ ^ 2) ≤ 3 := by nlinarith
      dsimp [δ]
      exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr (by simpa using hle3)
    have hgeo := integral_log_rho_ge n hn2 δ hδ0
    let M : ℝ := 2 * (n : ℝ) * Cmu * Real.sqrt (2 * δ)
    have hgeoM : Real.log δ - M ≤ (∫ x : ℝ, Real.log (rho n x) ∂muS) := by
      simpa [M] using hgeo
    have hn_sqrt : (n : ℝ) * Real.sqrt (2 * δ) ≤ 1 :=
      n_sqrt_two_delta_le_one Csp δ n hCsp1 hn2 (by rfl)
    have hMle : M ≤ 2 * Cmu := by
      dsimp [M]
      calc
        2 * (n : ℝ) * Cmu * Real.sqrt (2 * δ)
            = (2 * Cmu) * ((n : ℝ) * Real.sqrt (2 * δ)) := by ring
        _ ≤ (2 * Cmu) * 1 :=
              mul_le_mul_of_nonneg_left hn_sqrt (mul_nonneg (by norm_num) (le_of_lt Cmu_pos))
        _ = 2 * Cmu := by ring
    have hlogd : Real.log δ = -2 * Real.log Csp - 2 * Real.log (n : ℝ) - Real.log 3 :=
      log_delta Csp n δ hCsp0 hn0R (by rfl)
    have hlognn : Real.log (n : ℝ) ≤ L2 := by
      dsimp [L2]
      exact Real.log_le_log hn0R (by linarith)
    have hBbig' : -2 * L2 - B ≤ Real.log δ - M := by
      rw [hlogd]
      dsimp [B]
      nlinarith [hMle, hlognn]
    have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < (4 : ℝ))
    have hL2pos : 0 < L2 := by
      dsimp [L2]
      exact Real.log_pos (by nlinarith : (1 : ℝ) < (n : ℝ) + 2)
    have hL4le : Real.log 4 ≤ L2 := by
      dsimp [L2]
      exact log_np2_ge_log4 hn2
    have hratio : 1 ≤ L2 / Real.log 4 := (one_le_div hlog4pos).mpr hL4le
    have hBratio : B ≤ (B / Real.log 4) * L2 := by
      calc
        B = B * 1 := by ring
        _ ≤ B * (L2 / Real.log 4) := mul_le_mul_of_nonneg_left hratio hB_nonneg
        _ = (B / Real.log 4) * L2 := by ring
    have hmain1 : -(2 + B / Real.log 4) * L2 ≤ Real.log δ - M := by
      calc
        -(2 + B / Real.log 4) * L2 = -2 * L2 - (B / Real.log 4) * L2 := by ring
        _ ≤ -2 * L2 - B := by linarith
        _ ≤ Real.log δ - M := hBbig'
    have hfinal : -(2 + B / Real.log 4) * Real.log ((n : ℝ) + 2) ≤
        (∫ x : ℝ, Real.log (rho n x) ∂muS) := by
      simpa [L2] using (le_trans hmain1 hgeoM)
    simpa using hfinal

end Submission.EnergyDeliver
