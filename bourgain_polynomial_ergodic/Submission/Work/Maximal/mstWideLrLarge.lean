import Mathlib
import Submission.Work.Maximal.mstWide_defs
import Submission.Work.Maximal.mstWideModel_modSeq
import Submission.Work.Maximal.mstWideLat_defs
import Submission.Work.Maximal.mstModelFn_modSeq_gen
import Submission.Work.Maximal.mstModSeq_period_emod
import Submission.Work.Maximal.mstWideLat_curve
import Submission.Work.Maximal.mstWideLat_apply_int
import Submission.Work.Maximal.lintegral_count_eq_sum_range_emod
import Submission.Work.Maximal.wideLat_class_bound
import Submission.Work.Maximal.mstWideLrAux
import Submission.Work.BourgainPlan.Maximal.mstMaximal_single
import Submission.Work.BourgainPlan.Maximal.mstG_gauss_delta
import Submission.Work.BourgainPlan.Maximal.opMul_modSeq
import Submission.Work.Maximal.opMul_apply_eq_integral

/-!
# The large-scale half of the maximal bound for the wide level model

This module proves `Work.Maximal.mstWideModel_lr_large`: for `s` above the torsion threshold (i.e.
whenever every arc `β ∈ mstAnnulus l s` satisfies `fourier (mstQ' s) β = 1`), the dyadic maximal
function of the wide level-`s` model is `ℓʳ`-bounded with constant
`(K · ♯Tc · C_lat)^r · ♯Tc · (C_pig · log (s+2))^r`.

The proof is the residue-class decomposition of `ℤ` modulo `Q = mstQ' s`:

* `lintegral_count_eq_sum_range_emod` splits the counting integral into the `Q` classes;
* on each class, MST's folding identity (`mstModelFn_modSeq_gen`) writes the model value at
  `Q x + m` as the *single* wide-bump multiplier applied to the folded input `F_m = mstModSeq …`;
* `mstWideLat_curve` turns the supremum over the dyadic scales into the average of the
  band-limited interpolant `mstWideLat` along the polynomial curve, and `wideLat_class_bound`
  (the curve/Hardy–Littlewood bound together with the sampling principle `hlattice`) converts it
  back into the *values* of the interpolant on the lattice;
* `mstWideLat_unfold` (from `mstWideLrAux`) identifies those values with the values of the weighted
  arc-sum operator `mstWidePiG`, whose `ℓʳ`-bound with the `log (s+2)` loss is `hPiG` (MST (79)).
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Maximal

open Work.BourgainPlan.IonescuWainger
open Work.BourgainPlan.Maximal

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

/-- The large-scale (`s` above the torsion threshold) maximal bound for the wide level model. -/
theorem mstWideModel_lr_large (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (l : ℕ)
    {χ : ℝ} (η : ℝ → ℂ)
    (hηc : ContDiff ℝ 2 η) (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    (hϱml : ∀ s : ℕ, MeasureTheory.MemLp (mstWideBump P χ η s) ⊤ haarT)
    (hΩml : ∀ k s : ℕ, MeasureTheory.MemLp (mstWideModel P l χ η k s) ⊤ haarT)
    {r : ℝ} (hr : 1 < r) (hr2 : r < 2)
    (K : ℝ) (hKpos : 0 < K) (Tc : Finset ℝ)
    (hTc : ∀ (n : ℕ) (ψ : ℝ → ENNReal), Measurable ψ → ∀ x : ℝ,
      ∫⁻ u in Set.Ioc 0 1, ψ (x - Polynomial.eval (2 ^ n * u) (Polynomial.map (Int.castRingHom ℝ) P))
        ≤ ENNReal.ofReal K * ∑ c ∈ Tc, Commons.Analysis.Maximal.hlMax ψ (x - c))
    (C_lat : ℝ) (hC_lat : 0 < C_lat)
    (hlattice : ∀ (H : ℝ → ℂ) (δ : ℝ), 0 < δ → MeasureTheory.Integrable H →
      (∀ ξ : ℝ, δ < |ξ| → FourierTransform.fourier H ξ = 0) →
      ∀ (Q : ℕ), 1 ≤ Q → δ * (Q : ℝ) ≤ 1 / 4 → ∀ (m : ℤ) (c : ℝ),
        (∑' x : ℤ, (mstHlMax (fun y : ℝ => ENNReal.ofReal ‖H y‖)
            ((Q : ℝ) * (x : ℝ) + (m : ℝ) - c)) ^ r)
          ≤ ENNReal.ofReal (C_lat ^ r) *
            ∑' x : ℤ, ENNReal.ofReal (‖H ((Q : ℝ) * (x : ℝ) + (m : ℝ))‖ ^ r))
    (C_pig : ℝ) (hC_pig : 0 < C_pig)
    (hPiG : ∀ (s : ℕ) (hπ : MeasureTheory.MemLp (mstWidePiG P l χ η s) ⊤ haarT) (g : ℤ →₀ ℂ),
      MeasureTheory.eLpNorm (fun m : ℤ => ‖opMul (hπ.toLp (mstWidePiG P l χ η s)) (⇑g)
          (memℓp_finsupp g) m‖ₑ) (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C_pig * Real.log ((s : ℝ) + 2))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count)
    (s : ℕ) (hQE : ∀ β ∈ mstAnnulus l s, fourier (((mstQ' s : ℕ)) : ℤ) β = 1)
    (g : ℤ →₀ ℂ) :
    ∫⁻ n : ℤ, (⨆ k : ℕ, ‖opMul (mstWideModelCls P l χ η k s (hΩml k s)) (⇑g)
        (memℓp_finsupp g) n‖ₑ) ^ r ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((K * (Tc.card : ℝ) * C_lat) ^ r * (Tc.card : ℝ)
          * (C_pig * Real.log ((s : ℝ) + 2)) ^ r)
        * ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ ^ r ∂MeasureTheory.Measure.count := by
  classical
  have hηsup' : ∀ x : ℝ, 1 / 2 < |x| → η x = 0 := fun x hx => hηsup x hx.le
  have hlogpos : 0 < Real.log ((s:ℝ) + 2) :=
    Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) s] : (1:ℝ) < (s:ℝ) + 2)
  have hbase : 0 ≤ C_pig * Real.log ((s:ℝ) + 2) := mul_nonneg hC_pig.le hlogpos.le
  set Q : ℕ := mstQ' s with hQdef
  have hQpos : 0 < Q := by rw [hQdef]; exact mstQ'_pos s
  have hQ1 : 1 ≤ Q := hQpos
  have hQE' : ∀ β ∈ mstAnnulus l s, fourier (Q : ℤ) β = 1 := by
    intro β hβ
    rw [hQdef]
    exact hQE β hβ
  have hsymm : ∀ k : ℕ,
      MeasureTheory.MemLp (fun ξ : Circ => star (mstProf P (2 ^ k) ξ)
        * mstWideBump P χ η s ξ) ⊤ haarT := by
    intro k
    have h1 : MeasureTheory.MemLp (fun ξ : Circ => mstProf P (2 ^ k) ξ) ⊤ haarT :=
      (memLp_mst_symbols P (2 ^ k) 1 η hηc.continuous).2.1
    exact MeasureTheory.MemLp.mul h1.star (hϱml s)
  have hπ : MeasureTheory.MemLp (mstWidePiG P l χ η s) ⊤ haarT := by
    have h := memLp_arcSymbolW (fun β : Circ => β) (fun β : Circ => star (mstG P β))
      (mstAnnulus l s) (φ := fun ζ : Circ => (1 : ℂ) * mstWideBump P χ η s ζ)
      (by simpa only [one_mul] using hϱml s)
    simpa only [mstWidePiG, mstModelFn] using h
  set V : ℤ → ℂ := fun n => opMul (hπ.toLp (mstWidePiG P l χ η s)) (⇑g)
    (memℓp_finsupp g) n with hVdef
  set A : ℕ → Lp ℂ ⊤ haarT := fun k => (hsymm k).toLp
    (fun ξ : Circ => star (mstProf P (2 ^ k) ξ) * mstWideBump P χ η s ξ) with hAdef
  set Fm : ℤ → ℤ → ℂ := fun m n =>
    mstModSeq (fun β : Circ => star (mstG P β)) (mstAnnulus l s) (⇑g) m n with hFmdef
  have hFml : ∀ m : ℤ, Memℓp (Fm m) 2 := fun m => memℒp_mstModSeq (memℓp_finsupp g) m
  have hFmsupp : ∀ (m n : ℤ), n ∉ g.support → Fm m n = 0 := by
    intro m n hn
    simp only [hFmdef, mstModSeq_apply]
    rw [show (⇑g : ℤ → ℂ) n = 0 from by simpa using Finsupp.notMem_support_iff.mp hn]
    ring
  -- the model value at `Q x + m` is the single-mode value applied to the folded input `Fm m`
  have hmodel : ∀ (k : ℕ) (x m : ℤ), 0 ≤ m → m < (Q : ℤ) →
      opMul (mstWideModelCls P l χ η k s (hΩml k s)) (⇑g) (memℓp_finsupp g) ((Q : ℤ) * x + m)
        = opMul (A k) (Fm m) (hFml m) ((Q : ℤ) * x + m) := by
    intro k x m hm0 hmlt
    rw [show mstWideModelCls P l χ η k s (hΩml k s)
        = (hΩml k s).toLp (mstModelFn (fun β : Circ => star (mstG P β))
            (fun ξ : Circ => star (mstProf P (2 ^ k) ξ)) (mstWideBump P χ η s)
            (mstAnnulus l s)) from rfl]
    have hfold := mstModelFn_modSeq_gen (fun β : Circ => star (mstG P β))
      (fun ξ : Circ => star (mstProf P (2 ^ k) ξ)) (mstWideBump P χ η s) (mstAnnulus l s)
      (⇑g) (memℓp_finsupp g) (hΩml k s) (hsymm k) ((Q : ℤ) * x + m)
    rw [hfold]
    have hper : mstModSeq (fun β : Circ => star (mstG P β)) (mstAnnulus l s) (⇑g)
        ((Q : ℤ) * x + m) = Fm m := by
      rw [show mstModSeq (fun β : Circ => star (mstG P β)) (mstAnnulus l s) (⇑g)
            ((Q : ℤ) * x + m)
          = mstModSeq (fun β : Circ => star (mstG P β)) (mstAnnulus l s) (⇑g)
              (((Q : ℤ) * x + m) % (Q : ℤ)) from
            mstModSeq_period_emod hQpos hQE' (⇑g) ((Q : ℤ) * x + m)]
      rw [show (Q : ℤ) * x + m = m + Q * x by ring, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt hm0 hmlt]
    rw [opMul_congr_seq hper (memℒp_mstModSeq (memℓp_finsupp g) ((Q : ℤ) * x + m))
      (hFml m)]
  -- the curve-bound input for the class bound, per residue `m`
  have hcurve : ∀ (m : ℤ), ∀ (k : ℕ) (n : ℤ),
      ‖opMul (A k) (Fm m) (hFml m) n‖ₑ ≤
        ∫⁻ u in Set.Ioc (0:ℝ) 1, ‖mstWideLat P χ η s (Fm m) g.support
          (-(n : ℝ) - Polynomial.eval (((2 : ℝ) ^ k) * u)
            (Polynomial.map (Int.castRingHom ℝ) P))‖ₑ := by
    intro m k n
    have hc := mstWideLat_curve P χ η s (Fm m) g.support hηc hηsup' (hFmsupp m) (hFml m)
      (2 ^ k) n (hsymm k)
    have hpow : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := Nat.cast_pow 2 k
    rw [hAdef, hc, hpow]
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact MeasureTheory.enorm_integral_le_lintegral_enorm _
  -- the arithmetic for the lattice condition
  have hδQ' : (1 / (2 * mstWideC P s)) * (Q : ℝ) ≤ 1 / 4 := by
    rw [hQdef]
    exact mstWideC_mul_Q_le P hd s
  -- the residue classes of `Q` in `ℤ`
  have hmod : ∀ (x m : ℤ), ((Q : ℤ) * x + m) % (Q : ℤ) = m % (Q : ℤ) := by
    intro x m
    rw [show (Q : ℤ) * x + m = m + (Q : ℤ) * x by ring]
    exact Int.add_mul_emod_self_left m (Q : ℤ) x
  -- decompose `ℤ` into residue classes mod `Q`
  have hclass : ∀ m ∈ Finset.range Q,
      ∫⁻ x : ℤ, (⨆ k : ℕ, ‖opMul (mstWideModelCls P l χ η k s (hΩml k s)) (⇑g)
          (memℓp_finsupp g) ((Q : ℤ) * x + (m : ℤ))‖ₑ) ^ r ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((K * (Tc.card : ℝ) * C_lat) ^ r * (Tc.card : ℝ)) *
            ∫⁻ x : ℤ, ENNReal.ofReal (‖V ((Q : ℤ) * x + (m : ℤ))‖ ^ r)
              ∂MeasureTheory.Measure.count := by
    intro m hm
    have hm' : m < Q := Finset.mem_range.mp hm
    have hm0 : (0:ℤ) ≤ (m:ℤ) := Int.natCast_nonneg m
    have hmlt : (m:ℤ) < (Q:ℤ) := by exact_mod_cast hm'
    have hpoint : ∀ x : ℤ,
        (⨆ k : ℕ, ‖opMul (mstWideModelCls P l χ η k s (hΩml k s)) (⇑g)
          (memℓp_finsupp g) ((Q : ℤ) * x + (m : ℤ))‖ₑ) ^ r
          = (⨆ k : ℕ, ‖opMul (A k) (Fm (m:ℤ)) (hFml (m:ℤ))
              ((Q : ℤ) * x + (m : ℤ))‖ₑ) ^ r := by
      intro x
      congr 1
      refine iSup_congr fun k => ?_
      exact congrArg (fun z : ℂ => ‖z‖ₑ) (hmodel k x (m:ℤ) hm0 hmlt)
    have hmain := wideLat_class_bound P hd χ η s (Fm (m:ℤ)) g.support (hFml (m:ℤ)) hηc hηsup'
      hr hr2 K hKpos Tc hTc A (hcurve (m:ℤ)) C_lat hC_lat hlattice
      (fun k => mstWideLat P χ η s (Fm (m:ℤ)) g.support (-(k:ℝ)))
      (fun j => by
        show mstWideLat P χ η s (Fm (m:ℤ)) g.support (j:ℝ)
          = mstWideLat P χ η s (Fm (m:ℤ)) g.support (-(((-j : ℤ)) : ℝ))
        rw [Int.cast_neg, neg_neg])
      Q hQ1 hδQ' (m:ℤ)
    have hmain' : ∫⁻ x : ℤ, (⨆ k : ℕ, ‖opMul (A k) (Fm (m:ℤ)) (hFml (m:ℤ))
            ((Q : ℤ) * x + (m : ℤ))‖ₑ) ^ r ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((K * (Tc.card : ℝ) * C_lat) ^ r * (Tc.card : ℝ)) *
            ∫⁻ x : ℤ, ENNReal.ofReal
              (‖mstWideLat P χ η s (Fm (m:ℤ)) g.support
                (-(((Q : ℤ) * x + (m : ℤ) : ℤ) : ℝ))‖ ^ r)
              ∂MeasureTheory.Measure.count := hmain
    have hunf : ∀ x : ℤ, mstWideLat P χ η s (Fm (m:ℤ)) g.support
          (-(((Q : ℤ) * x + (m : ℤ) : ℤ) : ℝ)) = V ((Q : ℤ) * x + (m : ℤ)) := by
      intro x
      exact mstWideLat_unfold P l χ η s g hQpos hQE' hηc hηsup' (hϱml s) hπ (m:ℤ)
        ((Q : ℤ) * x + (m : ℤ)) (hmod x (m:ℤ))
    calc ∫⁻ x : ℤ, (⨆ k : ℕ, ‖opMul (mstWideModelCls P l χ η k s (hΩml k s)) (⇑g)
            (memℓp_finsupp g) ((Q : ℤ) * x + (m : ℤ))‖ₑ) ^ r ∂MeasureTheory.Measure.count
        = ∫⁻ x : ℤ, (⨆ k : ℕ, ‖opMul (A k) (Fm (m:ℤ)) (hFml (m:ℤ))
            ((Q : ℤ) * x + (m : ℤ))‖ₑ) ^ r ∂MeasureTheory.Measure.count := by
          rw [lintegral_congr hpoint]
      _ ≤ ENNReal.ofReal ((K * (Tc.card : ℝ) * C_lat) ^ r * (Tc.card : ℝ)) *
            ∫⁻ x : ℤ, ENNReal.ofReal
              (‖mstWideLat P χ η s (Fm (m:ℤ)) g.support
                (-(((Q : ℤ) * x + (m : ℤ) : ℤ) : ℝ))‖ ^ r)
              ∂MeasureTheory.Measure.count := hmain'
      _ = ENNReal.ofReal ((K * (Tc.card : ℝ) * C_lat) ^ r * (Tc.card : ℝ)) *
            ∫⁻ x : ℤ, ENNReal.ofReal (‖V ((Q : ℤ) * x + (m : ℤ))‖ ^ r)
              ∂MeasureTheory.Measure.count := by
          congr 1
          refine lintegral_congr (fun x => ?_)
          exact congrArg (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ r)) (hunf x)
  -- assemble the residue classes
  rw [lintegral_count_eq_sum_range_emod hQpos
    (fun n : ℤ => (⨆ k : ℕ, ‖opMul (mstWideModelCls P l χ η k s (hΩml k s)) (⇑g)
      (memℓp_finsupp g) n‖ₑ) ^ r)]
  calc ∑ m ∈ Finset.range Q, ∫⁻ x : ℤ, (⨆ k : ℕ,
          ‖opMul (mstWideModelCls P l χ η k s (hΩml k s)) (⇑g)
            (memℓp_finsupp g) ((Q : ℤ) * x + (m : ℤ))‖ₑ) ^ r
          ∂MeasureTheory.Measure.count
        ≤ ∑ m ∈ Finset.range Q, ENNReal.ofReal ((K * (Tc.card : ℝ) * C_lat) ^ r
            * (Tc.card : ℝ)) *
            ∫⁻ x : ℤ, ENNReal.ofReal (‖V ((Q : ℤ) * x + (m : ℤ))‖ ^ r)
              ∂MeasureTheory.Measure.count := Finset.sum_le_sum hclass
      _ = ENNReal.ofReal ((K * (Tc.card : ℝ) * C_lat) ^ r * (Tc.card : ℝ)) *
            ∫⁻ n : ℤ, ENNReal.ofReal (‖V n‖ ^ r) ∂MeasureTheory.Measure.count := by
          rw [← Finset.mul_sum,
            lintegral_count_eq_sum_range_emod hQpos (fun n : ℤ => ENNReal.ofReal (‖V n‖ ^ r))]
      _ ≤ ENNReal.ofReal ((K * (Tc.card : ℝ) * C_lat) ^ r * (Tc.card : ℝ)) *
            (ENNReal.ofReal ((C_pig * Real.log ((s:ℝ)+2)) ^ r) *
              ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ ^ r ∂MeasureTheory.Measure.count) := by
          gcongr
          rw [show (∫⁻ n : ℤ, ENNReal.ofReal (‖V n‖ ^ r) ∂MeasureTheory.Measure.count)
              = ∫⁻ n : ℤ, ‖V n‖ₑ ^ r ∂MeasureTheory.Measure.count from
            lintegral_congr (fun n => by
              rw [show ‖V n‖ₑ = ENNReal.ofReal ‖V n‖ by simp,
                ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith : (0:ℝ) ≤ r)])]
          rw [← eLpNorm_rpow_eq_lintegral_count (by linarith : (0:ℝ) < r) V]
          calc (MeasureTheory.eLpNorm V (ENNReal.ofReal r) MeasureTheory.Measure.count) ^ r
              ≤ (ENNReal.ofReal (C_pig * Real.log ((s : ℝ) + 2))
                  * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r)
                    MeasureTheory.Measure.count) ^ r :=
                ENNReal.monotone_rpow_of_nonneg (by linarith : (0:ℝ) ≤ r) (by
                  have h := hPiG s hπ g
                  rwa [MeasureTheory.eLpNorm_enorm _ AEStronglyMeasurable.of_discrete] at h)
            _ = ENNReal.ofReal ((C_pig * Real.log ((s : ℝ) + 2)) ^ r)
                  * (MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r)
                    MeasureTheory.Measure.count) ^ r := by
                rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : (0:ℝ) ≤ r),
                  ENNReal.ofReal_rpow_of_nonneg hbase (by linarith : (0:ℝ) ≤ r)]
            _ = ENNReal.ofReal ((C_pig * Real.log ((s : ℝ) + 2)) ^ r)
                  * ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ ^ r ∂MeasureTheory.Measure.count := by
                rw [eLpNorm_rpow_eq_lintegral_count (by linarith : (0:ℝ) < r) (⇑g)]
      _ = (ENNReal.ofReal ((K * (Tc.card : ℝ) * C_lat) ^ r * (Tc.card : ℝ))
            * ENNReal.ofReal ((C_pig * Real.log ((s:ℝ)+2)) ^ r))
            * ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ ^ r ∂MeasureTheory.Measure.count := by ring
      _ = ENNReal.ofReal ((K * (Tc.card : ℝ) * C_lat) ^ r * (Tc.card : ℝ)
            * (C_pig * Real.log ((s:ℝ)+2)) ^ r)
            * ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ ^ r ∂MeasureTheory.Measure.count := by
          have h1 : (0:ℝ) ≤ (K * (Tc.card : ℝ) * C_lat) ^ r * (Tc.card : ℝ) :=
            mul_nonneg (Real.rpow_nonneg (by positivity) r) (Nat.cast_nonneg _)
          have h2 : (0:ℝ) ≤ (C_pig * Real.log ((s:ℝ)+2)) ^ r := Real.rpow_nonneg hbase r
          rw [← ENNReal.ofReal_mul h1]

end

end Work.Maximal
