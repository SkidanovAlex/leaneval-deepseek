import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EpsEngine.PerzTools.mixed_intervalIntegral_eq_gen_restricted
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.SmoothErr
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.StrongEps.L12.LocUnifTendsto
import Submission.Work.FTS.StrongEps.LocUnif.D5.deriv_slot_lintegral_bounds
import Submission.Work.FTS.StrongEps.LocUnif.D5.rounds
import Submission.Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimExtract.limExtract_bounds10_const
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.wt_bddAbove_of_compact
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EpsEngine.HkMem_intervalIntegralPerz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

/-- **The interval integral of an `ℋ^k`-family, in the per-`z` form.**  See
`Submission/Work/FTS/EpsEngine/PerzTools/{Basic,Exchange,Main}.lean` for the development:

* `PerzTools/Basic.lean` — the elementary measure theory, the two interface statements
  (`CarathTheta`, `ExchMixed`) and the joint measurability of the family;
* `PerzTools/Exchange.lean` — the exchange identity at a point, the pointwise Cauchy–Schwarz
  (averaging) bound and the measurability of the primitive's `ℋ^k`-integrand;
* `PerzTools/Main.lean` — the chain `HkIntegrand α k (∫_s H s) ≤ (b-a) ∫_s HkIntegrand α k (H s)`
  integrated in `(s,z,θ)` (Tonelli against `hjoint`), giving both the per-`z` integrability and the
  norm bound;
* the two interface statements are discharged by
  `PerzTools.aesm_uncurry_restricted_theta` and
  `PerzTools.mixed_intervalIntegral_eq_gen_restricted`. -/
theorem HkMem_intervalIntegralPerz {α B : ℝ} {k : ℕ} {T a b : ℝ} {H : ℝ → ℝ → ℝ → ℝ}
    (hab : a ≤ b) (hT : 0 ≤ T) (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmem : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α k (H s))
    (hbd : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkNorm α k (H s) ≤ B)
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Work.Spaces.HkIntegrand α k (H p.1) p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))))
    (hsup : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C)
    (hperz : ∀ z ∈ Work.Spaces.Iz, ∃ Cz : ℝ,
      ∀ s ∈ Set.Icc (0 : ℝ) T,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (H s) z θ) ≤ Cz) :
    Work.Spaces.HkMem α k (fun z θ => ∫ s in a..b, H s z θ) ∧
      Work.Spaces.HkNorm α k (fun z θ => ∫ s in a..b, H s z θ) ≤ B * (b - a) := by
  exact Work.FTS.EpsEngine.PerzTools.intervalIntegral_perz_aux
    Work.FTS.EpsEngine.PerzTools.aesm_uncurry_restricted_theta
    Work.FTS.EpsEngine.PerzTools.mixed_intervalIntegral_eq_gen_restricted
    hab hT haT hbT hsm hmem hbd hmeas hjoint hsup hperz

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.EpsEngine.PerzPrim.intervalIntegral_perz_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.PerzPrim

theorem intervalIntegral_perz_le {α : ℝ} {k : ℕ} {T τ Cz z : ℝ} {H : ℝ → ℝ → ℝ → ℝ}
    (hτ0 : 0 ≤ τ) (hτT : τ ∈ Set.Icc 0 T) (hT : 0 ≤ T)
    (hsm : ∀ s ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmem : ∀ s ∈ Set.Icc 0 T, Work.Spaces.HkMem α k (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hsup : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C)
    (hperz : ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (H s) z θ) ≤ Cz)
    (hCz : 0 ≤ Cz) (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Spaces.HkIntegrand α k
          (fun z θ => ∫ s in (0 : ℝ)..τ, H s z θ) z θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => ∫ s in (0 : ℝ)..τ, H s z θ) z θ) ≤ τ ^ 2 * Cz := by
  classical
  set G : ℝ → ℝ → ℝ := fun z θ => ∫ s in (0 : ℝ)..τ, H s z θ with hG
  have hT0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have hsub : Set.uIoc (0 : ℝ) τ ⊆ Set.Icc (0 : ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hτ0] at ht
    exact ⟨le_trans le_rfl ht.1.le, le_trans ht.2 hτT.2⟩
  have hcar : Work.FTS.EpsEngine.PerzTools.CarathTheta :=
    Work.FTS.EpsEngine.PerzTools.aesm_uncurry_restricted_theta
  have hexch : Work.FTS.EpsEngine.PerzTools.ExchMixed :=
    Work.FTS.EpsEngine.PerzTools.mixed_intervalIntegral_eq_gen_restricted
  have hAESM : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.HkIntegrand α k G z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EpsEngine.PerzTools.aesm_slice_HkIntegrand_primitive
      (T := T) (a := (0 : ℝ)) (b := τ) (α := α) (k := k) (H := H)
      hcar hexch hT0 hτT hτ0 hsm hmeas hsup hz
  have hnn : ∀ θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α k G z θ :=
    fun θ => Work.Spaces.HkIntegrand_nonneg α k G z θ
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α k G 0 θ) = fun _ => (0 : ℝ) :=
      funext fun θ => Work.FTS.EpsEngine.PerzTools.HkIntegrand_fst_zero α k G θ
    rw [hzero]
    refine ⟨MeasureTheory.integrableOn_zero, ?_⟩
    simp only [MeasureTheory.integral_zero]
    exact mul_nonneg (sq_nonneg τ) hCz
  · -- the honest case `0 < z`
    have key : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ)
          ≤ ENNReal.ofReal τ * (∫⁻ s in Set.uIoc (0 : ℝ) τ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ)) := by
      have hIθ : MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))
          = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
        MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
      rw [← hIθ]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hq : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzpos, hθ⟩
      have hcv := Work.FTS.EpsEngine.PerzTools.cv_bound (T := T) (a := (0 : ℝ)) (b := τ)
        (α := α) (k := k) (H := H) hexch hT0 hτT hτ0 hsm hmeas hsup hq
      have hconv : (∫ s in (0 : ℝ)..τ, Work.Spaces.HkIntegrand α k (H s) z θ)
          = ∫ s in Set.uIoc (0 : ℝ) τ, Work.Spaces.HkIntegrand α k (H s) z θ := by
        rw [intervalIntegral.integral_of_le hτ0, Set.uIoc_of_le hτ0]
      calc ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ)
          ≤ ENNReal.ofReal ((τ - 0) * ∫ s in (0 : ℝ)..τ,
              Work.Spaces.HkIntegrand α k (H s) z θ) :=
            ENNReal.ofReal_le_ofReal hcv
        _ = ENNReal.ofReal τ * ENNReal.ofReal
              (∫ s in (0 : ℝ)..τ, Work.Spaces.HkIntegrand α k (H s) z θ) := by
            rw [sub_zero, ENNReal.ofReal_mul hτ0]
        _ ≤ ENNReal.ofReal τ * (∫⁻ s in Set.uIoc (0 : ℝ) τ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ)) := by
            refine mul_le_mul_right ?_ _
            rw [hconv]
            exact Work.FTS.EpsEngine.PerzTools.ofReal_integral_le_lintegral_ofReal
              (fun s => Work.Spaces.HkIntegrand_nonneg α k (H s) z θ)
    have step2 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal τ
          * (∫⁻ s in Set.uIoc (0 : ℝ) τ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ)))
        = ENNReal.ofReal τ * ∫⁻ s in Set.uIoc (0 : ℝ) τ,
            ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ) := by
      rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      symm
      refine MeasureTheory.lintegral_lintegral_swap
        (μ := MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) τ))
        (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun s θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ)) ?_
      have h3 := Work.FTS.EpsEngine.PerzTools.perz_aesm_HkIntegrand
        (T := T) (α := α) (k := k) (H := H) hcar hsm hmeas hzpos
      exact ((h3.mono_measure
        (MeasureTheory.Measure.prod_mono (MeasureTheory.Measure.restrict_mono hsub le_rfl)
          le_rfl)).aemeasurable).ennreal_ofReal
    have step3 : (∫⁻ s in Set.uIoc (0 : ℝ) τ, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ))
        ≤ ∫⁻ s in Set.uIoc (0 : ℝ) τ, ENNReal.ofReal Cz := by
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with s hs
      have hsT : s ∈ Set.Icc (0 : ℝ) T := hsub hs
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hmem s hsT).1 z hz)
        (Filter.Eventually.of_forall
          (fun θ => Work.Spaces.HkIntegrand_nonneg α k (H s) z θ))]
      exact ENNReal.ofReal_le_ofReal (hperz s hsT)
    have step4 : (∫⁻ s in Set.uIoc (0 : ℝ) τ, ENNReal.ofReal Cz)
        = ENNReal.ofReal Cz * ENNReal.ofReal τ := by
      rw [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ,
        Real.volume_uIoc, sub_zero, abs_of_nonneg hτ0]
    have hzFin : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ))
        ≤ ENNReal.ofReal (τ ^ 2 * Cz) := by
      calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ))
          ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal τ * (∫⁻ s in Set.uIoc (0 : ℝ) τ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ)) :=
            MeasureTheory.lintegral_mono_ae key
        _ = ENNReal.ofReal τ * ∫⁻ s in Set.uIoc (0 : ℝ) τ, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ) := step2
        _ ≤ ENNReal.ofReal τ * ∫⁻ s in Set.uIoc (0 : ℝ) τ, ENNReal.ofReal Cz :=
            mul_le_mul_right step3 _
        _ = ENNReal.ofReal τ * (ENNReal.ofReal Cz * ENNReal.ofReal τ) := by rw [step4]
        _ = ENNReal.ofReal (τ ^ 2 * Cz) := by
            rw [← ENNReal.ofReal_mul hCz, ← ENNReal.ofReal_mul hτ0]
            congr 1
            ring
    have hInt : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Spaces.HkIntegrand α k G z θ) Work.Spaces.Iθ :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hAESM
        (Filter.Eventually.of_forall hnn)).mp
        (ne_of_lt (lt_of_le_of_lt hzFin ENNReal.ofReal_lt_top))
    refine ⟨hInt, ?_⟩
    have h2 : ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k G z θ)
        ≤ ENNReal.ofReal (τ ^ 2 * Cz) := by
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
        (Filter.Eventually.of_forall hnn)]
      exact hzFin
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg τ) hCz)).mp h2

end Work.FTS.EpsEngine.PerzPrim
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.lintegral_momentFactor_le =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.HkMem_K_slots_of_vanishing_family =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The general-level (`K`) honesty transfer for the three elliptic slots

This file proves `Work.FTS.PhiStar.Honesty.HkMem_K_slots_of_vanishing_family`: the level-`K`
generalisation of `Work.FTS.ClassC.HkMem_seven_slots_of_vanishing_family`.  For a datum `Ψ`
which is `C^∞` on the open quadrant, whose *pure radial* slots `D_z^l ∂_θ^m Ψ` (`l ≤ K + 2`,
`m ≤ 2`) are honestly in `ℋ⁰` (singular `η`-weight), and whose angular slots of order
`3 ≤ t ≤ K + 2` are integrable against the *vanishing* weights `sin(2θ)^{2t-4-γ}`, the three
derivatives

  `z²∂_z²Ψ`,   `∂_θ²Ψ`,   `z∂_z∂_θ²Ψ`

lie in `ℋ^K`.

The proof has the same layers as the level-`7` instance:

1. the grid majorant `vanGridK α Ψ K` (`Submission.Work.FTS.PhiStar.Honesty.VanGridK`) and its
   integrability `vanGridK_integrable` from the two families `hσ`, `hV`;
2. the per-slot domination `HkIntegrand_K_le_of_bounds` — the arithmetic re-sum of the pointwise
   reduction `HkIntegrand_le_pure_vanishing`, using that every pure slot and every vanishing
   slot is `≤ 4 · vanGridK`;
3. the six per-slot bounds (the `z²∂_z²Ψ` pair is delegated, the other four are proved below);
4. the assembly `HkMem_K_of_gridK` via `HkMem_of_majorant_ae`.
-/

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory

/-! ## The four remaining per-slot bounds -/

/-- The pure-`z` slot `HkIntegrand α 0 (D_z^j ∂_θ²Ψ)`, `j ≤ K`, is the summand
`(l,m) = (j,2)` of the first block of the grid majorant, hence dominated by `4 · vanGridK`. -/
theorem HkIntegrand_zero_DzIter_pthIter_two_le_K {α : ℝ} {K : ℕ}
    (hγ : Work.Spaces.gam α ≤ 3 / 2) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ j : ℕ, j ≤ K → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ)) z θ
        ≤ 4 * vanGridK α Ψ K z θ := by
  intro j _hj z _hz θ hθ
  have hmem := hkIntegrand_le_vanGridK (α := α) (Ψ := Ψ) (K := K) (r := 2) (l := j)
    (by norm_num) (by omega) z θ hθ
  have hnn : 0 ≤ vanGridK α Ψ K z θ := vanGridK_nonneg α Ψ K z ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  linarith

/-- The vanishing slot of `∂_θ²Ψ` is *literally* the `(t,l) = (r+2, j)` summand of the grid
majorant, because `∂_θ^r∂_θ²Ψ = ∂_θ^{r+2}Ψ` and `2(r+2) - 4 - γ = 2r - γ`. -/
theorem vig_pthIter_two_le_K {α : ℝ} {K : ℕ} (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ j r : ℕ, 1 ≤ r → r + j ≤ K → ∀ z : ℝ, 0 < z →
      ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.FTS.ClassC.vig α (Work.Spaces.pthIter 2 Ψ) r j z θ
        ≤ 4 * vanGridK α Ψ K z θ := by
  intro j r _hr _hrj z _hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have h2 : Work.FTS.ClassC.vig α (Work.Spaces.pthIter 2 Ψ) r j
      = Work.FTS.ClassC.hVint α Ψ (r + 2) j := by
    funext z' θ'
    rw [Work.FTS.ClassC.vig, Work.FTS.ClassC.hVint,
      show Work.Spaces.pthIter r (Work.Spaces.pthIter 2 Ψ)
        = Work.Spaces.pthIter (r + 2) Ψ from
        (Work.FTS.ClassC.seven_pthIter_add r 2 Ψ).symm]
    congr 2
    push_cast
    ring
  rw [h2]
  have h1 := hVint_le_vanGridK (α := α) (Ψ := Ψ) (K := K) (t := r + 2) (l := j)
    (by omega) (by omega) (by omega) z θ hθ
  have h2' : 0 ≤ vanGridK α Ψ K z θ := vanGridK_nonneg α Ψ K z hθI
  linarith

/-- `D_z^j` composed with one further `D_z` is `D_z^{j+1}`. -/
private theorem DzIter_Dz_eq_aux_K (j : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (Work.Spaces.Dz f) = Work.Spaces.DzIter (j + 1) f := by
  induction j with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ (n := n) (f := Work.Spaces.Dz f), ih,
        ← Work.Spaces.DzIter_succ (n := n + 1) (f := f)]

/-- The pure-`z` slot `HkIntegrand α 0 (D_z^j (z ∂_z∂_θ²Ψ))` is the summand `(l,m) = (j+1,2)`
of the first block of the grid majorant (`z ∂_z∂_θ²Ψ = D_z∂_θ²Ψ`). -/
theorem HkIntegrand_zero_DzIter_Dz_pthIter_two_le_K {α : ℝ} {K : ℕ}
    (hγ : Work.Spaces.gam α ≤ 3 / 2) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ j : ℕ, j ≤ K → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 0
          (Work.Spaces.DzIter j
            (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) z θ
        ≤ 4 * vanGridK α Ψ K z θ := by
  intro j _hj z _hz θ hθ
  have harg : Work.Spaces.DzIter j
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)
      = Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 Ψ) :=
    DzIter_Dz_eq_aux_K j (Work.Spaces.pthIter 2 Ψ)
  rw [harg]
  have hmem := hkIntegrand_le_vanGridK (α := α) (Ψ := Ψ) (K := K) (r := 2) (l := j + 1)
    (by norm_num) (by omega) z θ hθ
  have hnn : 0 ≤ vanGridK α Ψ K z θ := vanGridK_nonneg α Ψ K z ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  linarith

/-- The vanishing slot of `z ∂_z∂_θ²Ψ = D_z∂_θ²Ψ`: on the open quadrant
`∂_θ^r(D_z∂_θ²Ψ) = D_z∂_θ^{r+2}Ψ`, so the slot is *literally* `hVint α Ψ (r+2) (j+1)`, a
summand of the grid majorant. -/
theorem vig_Dz_pthIter_two_le_K {α : ℝ} {K : ℕ} (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ j r : ℕ, 1 ≤ r → r + j ≤ K → ∀ z : ℝ, 0 < z →
      ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.FTS.ClassC.vig α
          (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) r j z θ
        ≤ 4 * vanGridK α Ψ K z θ := by
  intro j r hr _hrj z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- `∂_θ^r (z ∂_z∂_θ²Ψ) = D_z ∂_θ^{r+2}Ψ` on the open quadrant
  have hcongr : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pthIter r (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z θ
        = Work.Spaces.DzIter 1 (Work.Spaces.pthIter (r + 2) Ψ) z θ := by
    intro z' θ' hz' hθ' hπ'
    have h0 := Work.FTS.ClassC.seven_pthIter_DzIter_eqOn_Q0
      (f := Work.Spaces.pthIter 2 Ψ) (Work.FTS.ClassC.SmoothOpen_pthIter_classC hΨ 2) r 1
      z' θ' hz' hθ' hπ'
    rw [← Work.FTS.ClassC.seven_pthIter_add r 2 Ψ] at h0
    exact h0
  have hD : Work.Spaces.DzIter j
        (Work.Spaces.pthIter r
          (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) z θ
      = Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter (r + 2) Ψ) z θ := by
    have h2 := Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
      (F := Work.Spaces.pthIter r
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ))
      (G := Work.Spaces.DzIter 1 (Work.Spaces.pthIter (r + 2) Ψ)) hcongr j z θ hz hθ.1 hθ.2
    rw [h2, Work.FTS.ClassC.seven_DzIter_add j 1 (Work.Spaces.pthIter (r + 2) Ψ)]
  have heq : Work.FTS.ClassC.vig α
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) r j z θ
      = Work.FTS.ClassC.hVint α Ψ (r + 2) (j + 1) z θ := by
    simp only [Work.FTS.ClassC.vig, Work.FTS.ClassC.hVint]
    rw [hD]
    have hexp : 2 * ((r + 2 : ℕ) : ℝ) - 4 - Work.Spaces.gam α
        = 2 * (r : ℝ) - Work.Spaces.gam α := by
      push_cast
      ring
    rw [hexp]
  rw [heq]
  have h1 := hVint_le_vanGridK (α := α) (Ψ := Ψ) (K := K) (t := r + 2) (l := j + 1)
    (by omega) (by omega) (by omega) z θ hθ
  have h2' : 0 ≤ vanGridK α Ψ K z θ := vanGridK_nonneg α Ψ K z hθI
  linarith

/-! ## The assembly engine -/

/-- **The assembly step.**  If the grid majorant `vanGridK α Ψ K` is integrable on the angular
interval and in the outer `z`-variable, and if for a function `f` (smooth on the open quadrant)
every pure radial level-`0` slot and every vanishing-weight angular slot of level `K` is
dominated on the open quadrant by `4 · vanGridK α Ψ K`, then `f ∈ ℋ^K`. -/
theorem HkMem_K_of_gridK {α : ℝ} {K : ℕ} (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {Ψ f : ℝ → ℝ → ℝ}
    (hG : (∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ => vanGridK α Ψ K z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
          vanGridK α Ψ K z θ) Work.Spaces.Iz)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (h0 : ∀ j : ℕ, j ≤ K → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ ≤ 4 * vanGridK α Ψ K z θ)
    (h1 : ∀ j r : ℕ, 1 ≤ r → r + j ≤ K → ∀ z : ℝ, 0 < z →
      ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.FTS.ClassC.vig α f r j z θ ≤ 4 * vanGridK α Ψ K z θ) :
    Work.Spaces.HkMem α K f := by
  set C : ℝ := 4 * ((K : ℝ) + 1)
    + 4 * (K : ℝ) * Work.FTS.ClassC.vanSum α hα hγ f hsm K with hC
  have hLnn : 0 ≤ C := by
    rw [hC]
    have hv := Work.FTS.ClassC.vanSum_nonneg α hα hγ f hsm K
    have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    nlinarith
  refine Work.FTS.EllipticEst.HkMem_of_majorant_ae
    (M := fun z θ => C * vanGridK α Ψ K z θ)
    α K (hsm.continuousOn_HkIntegrand α K) ?_ ?_ ?_
  · intro z hz
    exact (hG.1 z hz).const_mul C
  · refine MeasureTheory.IntegrableOn.congr_fun (hG.2.const_mul C) (fun z _ => ?_)
      measurableSet_Ici
    exact (MeasureTheory.integral_const_mul C _).symm
  · intro z hz
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun θ hθ => ?_
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      rw [Work.FTS.LocData.HkIntegrand_zero_fst]
      exact mul_nonneg hLnn
        (vanGridK_nonneg α Ψ K 0 ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    · exact HkIntegrand_K_le_of_bounds hα hγ hsm
        (fun z θ hθ' => vanGridK_nonneg α Ψ K z ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩)
        h0 h1 hzpos hθ

/-! ## The target -/

theorem HkMem_K_slots_of_vanishing_family (K : ℕ) {α : ℝ} (hα : 0 < α)
    (hγ : Work.Spaces.gam α ≤ 3 / 2) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hσ : ∀ l m : ℕ, l ≤ K + 2 → m ≤ 2 →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)))
    (hV : ∀ t l : ℕ, 3 ≤ t → t ≤ K + 2 → l ≤ K + 2 →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
          (Work.Spaces.DzIter l (Work.Spaces.pthIter t Ψ) z θ * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter l (Work.Spaces.pthIter t Ψ) z θ * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iz) :
    Work.Spaces.HkMem α K (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ∧
      Work.Spaces.HkMem α K (Work.Spaces.pthIter 2 Ψ) ∧
      Work.Spaces.HkMem α K (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) := by
  have hG := vanGridK_integrable (α := α) (K := K) (Ψ := Ψ) hσ hV
  refine ⟨?_, ?_, ?_⟩
  · -- conjunct 1: the smoothing family `z²∂_z²Ψ`
    exact HkMem_K_of_gridK hα hγ hG ((hΨ.pzIter 2).zsq_mul)
      (fun j hj => HkIntegrand_zero_DzIter_zsqPz2_le_K hγ hΨ j hj)
      (fun j r hr hrj => vig_zsqPz2_le_K hγ hΨ j r hr hrj)
  · -- conjunct 2: `∂_θ²Ψ`
    exact HkMem_K_of_gridK hα hγ hG
      (Work.FTS.ClassC.SmoothOpen_pthIter_classC hΨ 2)
      (fun j hj => HkIntegrand_zero_DzIter_pthIter_two_le_K hγ hΨ j hj)
      (fun j r hr hrj => vig_pthIter_two_le_K hγ hΨ j r hr hrj)
  · -- conjunct 3: `z ∂_z∂_θ²Ψ = D_z∂_θ²Ψ`
    exact HkMem_K_of_gridK hα hγ hG
      ((Work.FTS.ClassC.SmoothOpen_pthIter_classC hΨ 2).Dz)
      (fun j hj => HkIntegrand_zero_DzIter_Dz_pthIter_two_le_K hγ hΨ j hj)
      (fun j r hr hrj => vig_Dz_pthIter_two_le_K hγ hΨ j r hr hrj)

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12.L12_tendsto_locUnif_cont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.L12

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Continuity of the level-`0` integrand of a difference -/



/-! ## Integrability of the angular slices -/


/-! ## Integrability of the `L₁₂`-density -/



/-! ## Additivity of `L₁₂` on the continuous `ℋ⁴`-class -/


/-! ## The theorem -/


end Work.FTS.StrongEps.L12
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.blocks.HQo_mixed_abs_le_on_compact_uniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! ## The `α`-uniform Morrey bound on compacts for the open class `HQo α 6`

`Work.FTS.StrongEps.HQo_mixed_abs_le_on_compact` gives, for each *fixed* `α ∈ (0,1]`, a
constant `C = C(α,K)` with `|D_z^bD_θ^a f| ≤ C · HkNorm α 6 f` on a compact `K ⊆ Q0`.  The
block needed here is the *uniform* version: one constant `C = C(K)` valid simultaneously for
all `α ∈ (0,1]` and all `f`.  The only place where uniformity could fail is the pair of
`L²`-bounds for the cut-off products `χ · D_z^bD_θ^a f`, which are taken from
`Work.FTS.StrongEps.HQoAux.cut_slot_L2_bounds_uniform`: the existing
`Work.FTS.StrongEps.HQoAux.cut_slot_L2_bounds` with its constants pulled out in front of `α`
and `f` (they were already independent of both, since they come from
`Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds`, whose constant is `α`-free).
Everything after that -- the box, the cut-off, Morrey and the averaging lemma -- is
`α`-independent and is copied from the per-`α` proof. -/

namespace Work.FTS.StrongEps.blocks

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The `α`-uniform Morrey bound on compacts for the open class `HQo α 6`.**

For a compact `K ⊆ Q0 = (0,∞) × (0,π/2)` there is a single constant `C = C(K)` such that for
every `α ∈ (0,1]`, every `f : Fn` with `HQo α 6 f` and every slot `D_z^bD_θ^a f` with
`a + b ≤ 4`, the pointwise bound `|D_z^bD_θ^a f z θ| ≤ C · HkNorm α 6 f` holds on `K`.

This is the `α`-uniform refinement of `Work.FTS.StrongEps.HQo_mixed_abs_le_on_compact` (whose
constant is allowed to depend on `α`).  The argument is the same 2-dimensional Sobolev/Morrey
mechanism: a compact subset of the open quadrant sits in a box whose two-fold enlargement still
lies in `Q0`, a `C²` cut-off `χ` supported in the enlargement is `1` on the box, the products
`χ · D_z^bD_θ^a f` are `C²` with compact support, their `L²`-norms of order `0` and `2` are
dominated by `HkNorm α 6 f`, and Morrey's inequality `W^{2,2}(ℝ²) ⊂ C^{0,1/2}` together with
the averaging lemma converts that into a pointwise bound.  Uniformity in `α` is exactly the
statement `Work.FTS.StrongEps.HQoAux.cut_slot_L2_bounds_uniform`: the box, the cut-off, the
two `L²`-constants, Morrey's constant `Cm` and the averaging constant do not mention `α` or
`f`. -/
theorem HQo_mixed_abs_le_on_compact_uniform {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (f : Work.FTS.Galerkin.Fn),
      Work.FTS.VocabO.HQo α 6 f → ∀ (b a : ℕ), a + b ≤ 4 → ∀ z θ : ℝ, (z, θ) ∈ K →
      |Work.Spaces.mixed b a f z θ| ≤ C * Work.Spaces.HkNorm α 6 f := by
  rcases Set.eq_empty_or_nonempty K with hKe | hne
  · subst hKe
    exact ⟨1, one_pos, fun α ha ha1 f hf b a hab z θ hp => absurd hp (by simp)⟩
  · -- ## A box `[zlo,zhi] × [tlo,thi]` containing `K`, with a two-fold enlargement in `Q0`
    obtain ⟨zlo, zhi, tlo, thi, hzlopos, hzlole, htlopos, htlole, hthilt, hKbox⟩ :=
      Work.FTS_EllLimOK.box_of_compact_inside_Q0 hK hKQ hne
    have hthipi : thi < Real.pi / 2 := hthilt
    -- the enlarged box
    have hzlo'pos : 0 < zlo / 2 := by linarith
    have hzlo'lt : zlo / 2 < zlo := by linarith
    have hzhi'lt : zhi < zhi + 1 := by linarith
    have hzlo'le : zlo / 2 ≤ zhi + 1 := by linarith
    have htlo'pos : 0 < tlo / 2 := by linarith
    have htlo'lt : tlo / 2 < tlo := by linarith
    have hthi'lt : thi < (thi + Real.pi / 2) / 2 := by linarith [Real.pi_pos]
    have hthi'pi : (thi + Real.pi / 2) / 2 < Real.pi / 2 := by linarith
    have hboxsub : Set.Icc (zlo / 2) (zhi + 1) ×ˢ Set.Icc (tlo / 2) ((thi + Real.pi / 2) / 2)
        ⊆ Work.FTS.EllipticEst.Q0 := by
      rintro ⟨z, θ⟩ ⟨hz, hθ⟩
      exact Work.FTS.EllipticEst.mem_Q0.mpr
        ⟨by linarith [hz.1], by linarith [hθ.1], by linarith [hθ.2]⟩
    -- ## the cut-off
    obtain ⟨χ, M, hMpos, hχsm, hχcs, hχnn, hχle1, hχone, hχzero, hM1, hM2⟩ :=
      Work.FTS.StrongLWP.Sobolev.EqcAux.exists_cutoff_rect_C2
        (a := zlo) (b := zhi) (c := tlo) (d := thi)
        (a' := zlo / 2) (b' := zhi + 1) (c' := tlo / 2) (d' := (thi + Real.pi / 2) / 2)
        hzlo'pos hzlo'lt hzlole hzhi'lt htlo'pos htlo'lt htlole hthi'lt hthi'pi
    have hχ2 : ContDiff ℝ 2 χ := by simpa using hχsm 2
    -- ## the two `L²`-bounds for `χ · D_z^bD_θ^a f`, with constants independent of `α` and `f`
    obtain ⟨C1, C2, hC1pos, hC2pos, hL2⟩ :=
      Work.FTS.StrongEps.HQoAux.cut_slot_L2_bounds_uniform hzlo'pos hzlo'le
        htlo'pos hthi'pi hχ2 hχnn hχle1 hχzero hM1 hM2
    -- ## Morrey's inequality and its averaging form
    obtain ⟨Cm, hCmpos, hMor⟩ := Work.FTS.StrongLWP.Sobolev.holder_half_of_W22_real
    refine ⟨Cm * (Real.sqrt C1 + Real.sqrt C2) + Real.sqrt C1 / 2 + 1, by positivity, ?_⟩
    intro α hα hα1 f hf b a hab z θ hzθ
    -- the slot, cut off
    set G : ℝ → ℝ → ℝ := Work.Spaces.mixed b a f with hGdef
    set v : ℝ × ℝ → ℝ := fun x => χ x * Function.uncurry G x with hvdef
    have hG2 : ContDiffOn ℝ 2 (Function.uncurry G) Work.FTS.EllipticEst.Q0 := by
      have h := (hf.1.mixed b a).of_le Work.FTS.StrongEps.LocUnif.two_le_smoothOrder
      simpa only [hGdef] using h
    have hv2 : ContDiff ℝ 2 v := by
      have h := Work.FTS.StrongEps.LocUnif.contDiff_two_mul_of_contDiffOn_two
        (χ := χ) (g := Function.uncurry G)
        (s := Set.Icc (zlo / 2) (zhi + 1) ×ˢ Set.Icc (tlo / 2) ((thi + Real.pi / 2) / 2))
        (U := Work.FTS.EllipticEst.Q0)
        (isClosed_Icc.prod isClosed_Icc) hboxsub Work.FTS.EllipticEst.isOpen_Q0 hχ2 hχzero hG2
      simpa only [hvdef] using h
    have hv1 : ContDiff ℝ 1 v := hv2.of_le (by norm_num)
    have hvcs : HasCompactSupport v := by
      have h := Work.FTS.StrongLWP.Sobolev.eqc_hasCompactSupport_mul
        (χ := χ) (g := Function.uncurry G) hχcs
      simpa only [hvdef] using h
    obtain ⟨hL2val, hL2hess⟩ := hL2 α hα f hf.1 hf.2 b a hab
    have hL2val' : (∫ x : ℝ × ℝ, (v x) ^ 2) ≤ C1 * Work.Spaces.HkSq α 6 f := by
      simpa only [hvdef, hGdef] using hL2val
    have hL2hess' : (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)
        ≤ C2 * Work.Spaces.HkSq α 6 f := by
      simpa only [hvdef, hGdef] using hL2hess
    have hMnn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
    have hMnorm : Real.sqrt (Work.Spaces.HkSq α 6 f) = Work.Spaces.HkNorm α 6 f := rfl
    have hs1 : Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
        ≤ Real.sqrt C1 * Work.Spaces.HkNorm α 6 f := by
      calc Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
          ≤ Real.sqrt (C1 * Work.Spaces.HkSq α 6 f) := Real.sqrt_le_sqrt hL2val'
        _ = Real.sqrt C1 * Real.sqrt (Work.Spaces.HkSq α 6 f) := Real.sqrt_mul hC1pos.le _
        _ = Real.sqrt C1 * Work.Spaces.HkNorm α 6 f := by rw [hMnorm]
    have hs2 : Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)
        ≤ Real.sqrt C2 * Work.Spaces.HkNorm α 6 f := by
      calc Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)
          ≤ Real.sqrt (C2 * Work.Spaces.HkSq α 6 f) := Real.sqrt_le_sqrt hL2hess'
        _ = Real.sqrt C2 * Real.sqrt (Work.Spaces.HkSq α 6 f) := Real.sqrt_mul hC2pos.le _
        _ = Real.sqrt C2 * Work.Spaces.HkNorm α 6 f := by rw [hMnorm]
    -- the Hölder modulus of `v`, from Morrey
    have hmod : ∀ p q : ℝ × ℝ, |v p - v q|
        ≤ (Cm * (Real.sqrt C1 + Real.sqrt C2) * Work.Spaces.HkNorm α 6 f)
            * Real.sqrt (dist p q) := by
      intro p q
      have h := hMor v hv2 hvcs p q
      have hd0 : 0 ≤ dist p q := dist_nonneg
      have hspow : Real.sqrt (dist p q) = dist p q ^ (1 / 2 : ℝ) :=
        Real.sqrt_eq_rpow (dist p q)
      have hstep : Cm * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
            + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)) * dist p q ^ (1 / 2 : ℝ)
          ≤ (Cm * (Real.sqrt C1 + Real.sqrt C2) * Work.Spaces.HkNorm α 6 f)
            * Real.sqrt (dist p q) := by
        rw [← hspow]
        have hsum : Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
              + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)
            ≤ (Real.sqrt C1 + Real.sqrt C2) * Work.Spaces.HkNorm α 6 f := by
          have := add_le_add hs1 hs2
          linarith
        calc Cm * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
              + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)) * Real.sqrt (dist p q)
            ≤ Cm * ((Real.sqrt C1 + Real.sqrt C2) * Work.Spaces.HkNorm α 6 f)
                * Real.sqrt (dist p q) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hsum (le_of_lt hCmpos)) (Real.sqrt_nonneg _)
          _ = (Cm * (Real.sqrt C1 + Real.sqrt C2) * Work.Spaces.HkNorm α 6 f)
                * Real.sqrt (dist p q) := by ring
      exact h.trans hstep
    have hsup := Work.FTS.StrongLWP.Sobolev.HolderHalf.sup_le_of_holder hv1 hvcs
      (Cm * (Real.sqrt C1 + Real.sqrt C2) * Work.Spaces.HkNorm α 6 f)
      (by positivity) hmod (z, θ)
    -- the cut-off is `1` at the point
    have hpk : (z, θ) ∈ Set.Icc zlo zhi ×ˢ Set.Icc tlo thi := hKbox hzθ
    have hχp : χ (z, θ) = 1 := hχone z hpk.1 θ hpk.2
    have hvp : v (z, θ) = Work.Spaces.mixed b a f z θ := by
      simp only [hvdef, hGdef, Function.uncurry, hχp, one_mul]
    calc |Work.Spaces.mixed b a f z θ|
        = |v (z, θ)| := by rw [hvp]
      _ ≤ Cm * (Real.sqrt C1 + Real.sqrt C2) * Work.Spaces.HkNorm α 6 f
            + Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2) / 2 := hsup
      _ ≤ Cm * (Real.sqrt C1 + Real.sqrt C2) * Work.Spaces.HkNorm α 6 f
            + Real.sqrt C1 * Work.Spaces.HkNorm α 6 f / 2 := by linarith
      _ ≤ (Cm * (Real.sqrt C1 + Real.sqrt C2) + Real.sqrt C1 / 2 + 1)
            * Work.Spaces.HkNorm α 6 f := by nlinarith [hMnn]

end Work.FTS.StrongEps.blocks
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary angular facts -/

/-- `sin(2θ) ≤ 2·min θ (π/2-θ)` for `θ ∈ (0,π/2)`. -/
theorem sin_two_le_two_min {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Real.sin (2 * θ) ≤ 2 * min θ (π / 2 - θ) := by
  have h1 : Real.sin (2 * θ) ≤ 2 * θ := by
    have h := Real.sin_le (by linarith [hθ.1] : (0 : ℝ) ≤ 2 * θ)
    linarith [h]
  have h2 : Real.sin (2 * θ) ≤ 2 * (π / 2 - θ) := by
    have hπ : 0 ≤ Real.pi - 2 * θ := by linarith [hθ.2]
    have h := Real.sin_le hπ
    have heq : Real.sin (2 * θ) = Real.sin (Real.pi - 2 * θ) := by
      rw [Real.sin_pi_sub]
    rw [heq]
    linarith [h]
  rcases le_total θ (π / 2 - θ) with h | h
  · rwa [min_eq_left h]
  · rwa [min_eq_right h]

/-- `m(θ) ≤ m(θ)^β` for `θ ∈ (0,π/2)` and `β ≤ 1` (the `min` is at most `π/4 ≤ 1`). -/
theorem min_rpow_ge_self {β θ : ℝ} (hβ : β ≤ 1) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    min θ (π / 2 - θ) ≤ (min θ (π / 2 - θ)) ^ β := by
  have hm0 : 0 < min θ (π / 2 - θ) := lt_min hθ.1 (by linarith [hθ.2])
  have hm1 : min θ (π / 2 - θ) ≤ 1 := by
    rcases le_total θ (π / 2 - θ) with h | h
    · rw [min_eq_left h]; nlinarith [hθ.2, Real.pi_lt_four]
    · rw [min_eq_right h]; nlinarith [h, Real.pi_lt_four]
  calc min θ (π / 2 - θ) = (min θ (π / 2 - θ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (min θ (π / 2 - θ)) ^ β :=
        Real.rpow_le_rpow_of_exponent_ge hm0 hm1 hβ

/-- `x ≤ x^β` for `0 < x ≤ 1` and `β ≤ 1`. -/
theorem self_le_rpow {β x : ℝ} (hβ : β ≤ 1) (hx0 : 0 < x) (hx1 : x ≤ 1) : x ≤ x ^ β := by
  calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
    _ ≤ x ^ β := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hβ

/-- `tan θ ≤ 2θ` for `θ ∈ (0,π/4]`. -/
theorem tan_le_two_mul {θ : ℝ} (hθ0 : 0 < θ) (hθ4 : θ ≤ Real.pi / 4) :
    Real.tan θ ≤ 2 * θ := by
  have hcos : (1 : ℝ) / 2 ≤ Real.cos θ := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := θ)
    have h2 : θ ^ 2 ≤ (Real.pi / 4) ^ 2 := by nlinarith [hθ4, hθ0]
    nlinarith [h1, h2, Real.pi_lt_four, Real.pi_pos, sq_nonneg θ]
  have hcpos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [hθ4, Real.pi_pos]⟩
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hcpos]
  nlinarith [Real.sin_le (le_of_lt hθ0), hcos, hθ0]

/-- `(1-sin θ)/cos θ ≤ cos θ` on `(0,π/2)`. -/
theorem one_sub_sin_div_cos_le {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (1 - Real.sin θ) / Real.cos θ ≤ Real.cos θ := by
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩
  rw [div_le_iff₀ hc]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- `cos θ ≤ π/2 - θ` on `(0,π/2)`. -/
theorem cos_le_pi_div_two_sub {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Real.cos θ ≤ Real.pi / 2 - θ := by
  have h := Real.sin_le (show (0 : ℝ) ≤ Real.pi / 2 - θ by linarith [hθ.2])
  rwa [Real.sin_pi_div_two_sub] at h

/-- The two one-sided Gronwall bounds of `vopRated` combine into `|f θ| ≤ 2K·min θ (π/2-θ)`. -/
theorem vop_two_sided_le_min {K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ}
    (h1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |f θ| ≤ K * (Real.sin θ / Real.cos θ))
    (h2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |f θ| ≤ K * ((1 - Real.sin θ) / Real.cos θ)) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |f θ| ≤ 2 * K * min θ (π / 2 - θ) := by
  intro θ hθ
  rcases le_total θ (π / 2 - θ) with h | h
  · rw [min_eq_left h]
    have hθ4 : θ ≤ Real.pi / 4 := by linarith
    have hb := h1 θ hθ
    have ht := tan_le_two_mul hθ.1 hθ4
    have htan : Real.sin θ / Real.cos θ ≤ 2 * θ := by
      rwa [← Real.tan_eq_sin_div_cos]
    calc |f θ| ≤ K * (Real.sin θ / Real.cos θ) := hb
      _ ≤ K * (2 * θ) := mul_le_mul_of_nonneg_left htan hK
      _ = 2 * K * θ := by ring
  · rw [min_eq_right h]
    have hb := h2 θ hθ
    have hle := one_sub_sin_div_cos_le hθ
    have hcos := cos_le_pi_div_two_sub hθ
    have hpos : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    calc |f θ| ≤ K * ((1 - Real.sin θ) / Real.cos θ) := hb
      _ ≤ K * Real.cos θ := mul_le_mul_of_nonneg_left hle hK
      _ ≤ K * (Real.pi / 2 - θ) := mul_le_mul_of_nonneg_left hcos hK
      _ ≤ 2 * K * (Real.pi / 2 - θ) := by nlinarith [hK, hpos]

/-- `D_z^j` is linear in the function: `D_z^j (f + g) = D_z^j f + D_z^j g` on the open
quadrant, for `f, g` smooth there. -/
theorem dzIter_add_eqOn {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ j : ℕ, ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Spaces.DzIter j (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.DzIter j f z θ + Work.Spaces.DzIter j g z θ := by
  intro j
  induction j with
  | zero => intro z hz θ hθ; rfl
  | succ k ih =>
      intro z hz θ hθ
      have hdf : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter k f z' θ) z :=
        (((hf.DzIter k).curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero)
          |>.differentiableAt (isOpen_Ioi.mem_nhds hz)
      have hdg : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter k g z' θ) z :=
        (((hg.DzIter k).curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero)
          |>.differentiableAt (isOpen_Ioi.mem_nhds hz)
      have hev : (fun z' => Work.Spaces.DzIter k (fun z θ => f z θ + g z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter k f z' θ + Work.Spaces.DzIter k g z' θ) :=
        Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz)
          (fun z' hz' => ih z' hz' θ hθ)
      show z * deriv (fun z' => Work.Spaces.DzIter k (fun z θ => f z θ + g z θ) z' θ) z
        = z * deriv (fun z' => Work.Spaces.DzIter k f z' θ) z
          + z * deriv (fun z' => Work.Spaces.DzIter k g z' θ) z
      rw [hev.deriv_eq]
      change z * deriv ((fun z' => Work.Spaces.DzIter k f z' θ)
        + fun z' => Work.Spaces.DzIter k g z' θ) z = _
      rw [deriv_add hdf hdg]
      ring

/-! ## The `V`-slot jets of `Φ̃` are bounded by `Xn₆` -/

end Work.FTS_EllLimOK.ProducerH.BoxAux
end
end
