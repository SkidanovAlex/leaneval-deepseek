import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.lam_Dz_sq_le
import Submission.Work.FTS.PhiStar.Honesty.CptApp.LamAux.chiR_dzIter_boundAux
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.SmoothErr
import Submission.Work.FTS.FinalClock.ZopIterLeibniz
import Submission.Work.FTS.LocData.DzIter_mul_smoothQuad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp.Est

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Support of the iterated radial derivatives of the truncated moment

`mu n F = chiR n * lam n F` vanishes on the two open half-lines `(-∞, 1/n)` and `(2n, ∞)`
(`chiR_eq_zero_of_le`, `chiR_eq_zero_of_ge`).  Since every `D_z`-iterate is a composition of
`Zop u = z ∂_z` (`Work.Spaces.Zop`) and `Zop` respects equality on open sets
(`Work.FTS.FinalClock.Zop_congr_open`), the vanishing propagates to all iterates. -/

theorem Zop_iterate_eqOn_zero {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ}
    (hf : ∀ z ∈ U, f z = 0) : ∀ b : ℕ, ∀ z ∈ U, Work.Spaces.Zop^[b] f z = 0 := by
  intro b
  induction b with
  | zero => intro z hz; exact hf z hz
  | succ b ih =>
    intro z hz
    rw [Function.iterate_succ_apply']
    have h := Work.FTS.FinalClock.Zop_congr_open hU (A := Work.Spaces.Zop^[b] f)
      (B := fun _ => (0 : ℝ)) ih
    rw [h hz]
    simp [Work.Spaces.Zop]

theorem DzIter_mu_eq_zero_of_lt {n m : ℕ} (hn : 1 ≤ n) (F : ℝ → ℝ → ℝ) {z : ℝ}
    (hz : z < 1 / (n : ℝ)) :
    Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0 = 0 := by
  have hslice := congrFun (Work.FTS.LocData.Zop_iterate_slice m
    (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') 0) z
  rw [hslice]
  refine Zop_iterate_eqOn_zero isOpen_Iio
    (f := fun z => Work.FTS.PhiStar.Honesty.CptApp.mu n F z) ?_ m z hz
  intro z' hz'
  simp only [Work.FTS.PhiStar.Honesty.CptApp.mu]
  rw [Work.FTS.PhiStar.Honesty.CptApp.chiR_eq_zero_of_le hn (le_of_lt hz'), zero_mul]

theorem DzIter_mu_eq_zero_of_gt {n m : ℕ} (hn : 1 ≤ n) (F : ℝ → ℝ → ℝ) {z : ℝ}
    (hz : 2 * (n : ℝ) < z) :
    Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0 = 0 := by
  have hslice := congrFun (Work.FTS.LocData.Zop_iterate_slice m
    (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') 0) z
  rw [hslice]
  refine Zop_iterate_eqOn_zero isOpen_Ioi
    (f := fun z => Work.FTS.PhiStar.Honesty.CptApp.mu n F z) ?_ m z hz
  intro z' hz'
  simp only [Work.FTS.PhiStar.Honesty.CptApp.mu]
  rw [Work.FTS.PhiStar.Honesty.CptApp.chiR_eq_zero_of_ge hn (le_of_lt hz'), zero_mul]

/-- **Integrability of one summand of the moment factor.**  The function
`z ↦ w(z)² (D_z^m (mu n F) z)²` is integrable on `(0,∞)`: `mu n F` and all its `D_z`-iterates are
supported in the compact interval `[1/n, 2n] ⊂ (0,∞)`, where the function is continuous (`mu n F`
is `C^∞` on `(0,∞)` by `EstAux.contDiffOn_mu`, the iterates preserve that by
`Work.FTS.FinalClock.Zop_contDiffOn_iter`) and `w` is bounded. -/
theorem integrableOn_mu_dzIter_sq_aux (n m : ℕ) (F : ℝ → ℝ → ℝ) (hn : 1 ≤ n)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Spaces.w z) ^ 2
        * (Work.Spaces.DzIter m
            (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have ha : 0 < 1 / (n : ℝ) := by positivity
  have hsub : Set.Icc (1 / (n : ℝ)) (2 * (n : ℝ)) ⊆ Set.Ioi (0 : ℝ) :=
    fun z hz => Set.mem_Ioi.mpr (lt_of_lt_of_le ha hz.1)
  -- the `D_z`-iterates of `mu n F` are `Zop`-iterates of `mu n F`
  have hslice : (fun z : ℝ => Work.Spaces.DzIter m
      (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0)
      = (Work.Spaces.Zop^[m] (fun z => Work.FTS.PhiStar.Honesty.CptApp.mu n F z)) := by
    funext z
    exact congrFun (Work.FTS.LocData.Zop_iterate_slice m
      (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') 0) z
  have hXc : ContinuousOn (fun z : ℝ => Work.Spaces.DzIter m
      (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) (Set.Ioi (0 : ℝ)) := by
    rw [hslice]
    exact (Work.FTS.FinalClock.Zop_contDiffOn_iter isOpen_Ioi m 0
      (Work.FTS.PhiStar.Honesty.CptApp.EstAux.contDiffOn_mu hsm hn m)).continuousOn
  have hwc : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    simp only [Work.Spaces.w]
    refine ContinuousOn.pow ?_ 2
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuousOn_const.add continuousOn_id).pow 2
    · exact continuousOn_id.pow 2
    · intro z hz
      exact pow_ne_zero 2 (ne_of_gt hz)
  have hcont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2
      * (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2)
      (Set.Ioi (0 : ℝ)) := hwc.mul (hXc.pow 2)
  have hk : MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2
      * (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2)
      (Set.Icc (1 / (n : ℝ)) (2 * (n : ℝ))) MeasureTheory.volume :=
    ContinuousOn.integrableOn_compact isCompact_Icc (hcont.mono hsub)
  have hzero : MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2
      * (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2)
      (Set.Ioi (0 : ℝ) \ Set.Icc (1 / (n : ℝ)) (2 * (n : ℝ))) MeasureTheory.volume := by
    refine MeasureTheory.integrableOn_zero.congr_fun ?_
      (measurableSet_Ioi.diff measurableSet_Icc)
    intro z hz
    rcases not_and_or.mp hz.2 with h | h
    · have h0 := DzIter_mu_eq_zero_of_lt (m := m) hn F (not_le.mp h)
      show (0 : ℝ) = (Work.Spaces.w z) ^ 2
        * (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2
      rw [h0]
      ring
    · have h0 := DzIter_mu_eq_zero_of_gt (m := m) hn F (not_le.mp h)
      show (0 : ℝ) = (Work.Spaces.w z) ^ 2
        * (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2
      rw [h0]
      ring
  have hK : MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2
      * (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2)
      (Set.Icc (1 / (n : ℝ)) (2 * (n : ℝ)) ∩ Set.Ioi (0 : ℝ)) MeasureTheory.volume :=
    hk.mono_set Set.inter_subset_left
  have hunion : MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2
      * (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2)
      ((Set.Icc (1 / (n : ℝ)) (2 * (n : ℝ)) ∩ Set.Ioi (0 : ℝ))
        ∪ (Set.Ioi (0 : ℝ) \ Set.Icc (1 / (n : ℝ)) (2 * (n : ℝ)))) MeasureTheory.volume :=
    hK.union hzero
  exact hunion.mono_set (fun z hz => by
    by_cases h : z ∈ Set.Icc (1 / (n : ℝ)) (2 * (n : ℝ))
    · exact Or.inl ⟨h, hz⟩
    · exact Or.inr ⟨hz, h⟩)

/-! ## The estimate -/

/-- The `z`-integral of the moment factor is bounded by `C·(2/n)^{2+η}·ℋ^k`-energy.

The moment factor at scale `n` is `w(z)^2 · ∑_{m ≤ k} (D_z^m μ z)^2` with `μ = chiR n · lam n F`
(`Work.FTS.PhiStar.Honesty.CptApp.mu`).  Each summand is integrable on `(0,∞)`
(`integrableOn_mu_dzIter_sq_aux`), so the `lintegral` of the sum splits into the `k+1` `lintegral`s
of the summands, each of which equals `ofReal` of the corresponding Bochner integral
(`MeasureTheory.ofReal_integral_eq_lintegral_ofReal`).  Each of those integrals is bounded by
`C_lam·(2/n)^{2+η}·HkSq α k F` by `Work.FTS.PhiStar.Honesty.CptApp.lam_Dz_sq_le`. -/
theorem lintegral_momentFactor_le (k : ℕ) {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α k F)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal ((Work.Spaces.w z) ^ 2
          * ∑ m ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2))
        ≤ ENNReal.ofReal (C * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F) := by
  obtain ⟨C₀, hC₀, hlam⟩ := Work.FTS.PhiStar.Honesty.CptApp.lam_Dz_sq_le (α := α) (k := k) hsm hF hFs
  refine ⟨((k : ℝ) + 1) * C₀, mul_nonneg (by positivity) hC₀, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hp0 : 0 ≤ (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) :=
    Real.rpow_nonneg (by positivity) _
  have hH0 : 0 ≤ Work.Spaces.HkSq α k F := Work.Spaces.HkSq_nonneg α k F
  -- the two forms of the `D_z`-iterate of `mu` are definitionally equal
  have hAB : ∀ (m : ℕ) (z : ℝ),
      Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0
      = Work.Spaces.DzIter m
          (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
            * Work.FTS.PhiStar.Honesty.CptApp.lam n F z) z 0 := fun m z => rfl
  -- integrability of every summand
  have hint : ∀ m : ℕ, MeasureTheory.Integrable
      (fun z : ℝ => (Work.Spaces.w z) ^ 2
        * (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ))) :=
    fun m => integrableOn_mu_dzIter_sq_aux n m F hn1 hsm
  -- a.e. strong measurability of every `ofReal`-summand
  have hmeas : ∀ m ∈ Finset.range (k + 1), AEMeasurable
      (fun z : ℝ => ENNReal.ofReal ((Work.Spaces.w z) ^ 2
        * (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ))) :=
    fun m _ => ENNReal.measurable_ofReal.comp_aemeasurable
      (hint m).aestronglyMeasurable.aemeasurable
  -- the bound for a single summand
  have hstep : ∀ m ∈ Finset.range (k + 1),
      (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal ((Work.Spaces.w z) ^ 2
        * (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2))
      ≤ ENNReal.ofReal (C₀ * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F) := by
    intro m hm
    have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hb := hlam n hn m hmk 0
    have hnonneg : 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ))]
        (fun z : ℝ => (Work.Spaces.w z) ^ 2
          * (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2) :=
      Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint m) hnonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    calc MeasureTheory.integral
          (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ)))
          (fun z : ℝ => (Work.Spaces.w z) ^ 2
            * (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2)
        = MeasureTheory.integral
            (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ)))
            (fun z : ℝ => (Work.Spaces.DzIter m
                (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                  * Work.FTS.PhiStar.Honesty.CptApp.lam n F z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          show (Work.Spaces.w z) ^ 2
              * (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2
            = (Work.Spaces.DzIter m
                (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                  * Work.FTS.PhiStar.Honesty.CptApp.lam n F z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2
          rw [hAB m z]
          ring
      _ ≤ C₀ * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F := hb
  -- split `ofReal` of the sum and integrate termwise
  calc (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal ((Work.Spaces.w z) ^ 2
          * ∑ m ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2))
      = ∫⁻ z in Set.Ioi (0 : ℝ), ∑ m ∈ Finset.range (k + 1), ENNReal.ofReal ((Work.Spaces.w z) ^ 2
          * (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2) := by
        refine MeasureTheory.lintegral_congr fun z => ?_
        rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
        exact fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    _ = ∑ m ∈ Finset.range (k + 1), ∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal ((Work.Spaces.w z) ^ 2
          * (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2) :=
        MeasureTheory.lintegral_finsetSum' _ hmeas
    _ ≤ ∑ _m ∈ Finset.range (k + 1),
          ENNReal.ofReal (C₀ * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F) :=
        Finset.sum_le_sum hstep
    _ = ENNReal.ofReal ((((k : ℝ) + 1) * C₀) * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
          * Work.Spaces.HkSq α k F) := by
        have hc0 : 0 ≤ C₀ * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F :=
          mul_nonneg (mul_nonneg hC₀ hp0) hH0
        calc ∑ _m ∈ Finset.range (k + 1),
              ENNReal.ofReal (C₀ * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)
            = ((k : ℝ≥0∞) + 1)
                * ENNReal.ofReal (C₀ * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
                    * Work.Spaces.HkSq α k F) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
          _ = ENNReal.ofReal ((k : ℝ) + 1)
                * ENNReal.ofReal (C₀ * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
                    * Work.Spaces.HkSq α k F) := by
              rw [ENNReal.ofReal_add (Nat.cast_nonneg k) zero_le_one, ENNReal.ofReal_natCast,
                ENNReal.ofReal_one]
          _ = ENNReal.ofReal (((k : ℝ) + 1)
                * (C₀ * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)) :=
              (ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)).symm
          _ = ENNReal.ofReal ((((k : ℝ) + 1) * C₀) * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
                * Work.Spaces.HkSq α k F) := by
              congr 1
              ring

end Work.FTS.PhiStar.Honesty.CptApp.Est
