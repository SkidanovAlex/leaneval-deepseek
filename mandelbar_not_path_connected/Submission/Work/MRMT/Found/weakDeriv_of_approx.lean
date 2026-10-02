/-
Copyright: Work.MRMT (mandelbar) subproject.

# Weak Wirtinger derivatives as limits of pointwise Wirtinger derivatives

Let `fn : ℕ → ℂ → ℂ` be `C¹`, converging locally uniformly to `f`, and suppose the pointwise
Wirtinger derivatives `∂(fn n)` converge to `D` and `∂̄(fn n)` converge to `E` in `L²` on every
compact set.  Then `D` and `E` are the weak (distributional) `∂`- and `∂̄`-derivatives of `f`:
`Work.MRMT.IsDzDeriv f D ∧ Work.MRMT.IsDbarDeriv f E`.

The proof is the standard "integration by parts and pass to the limit" argument.  For every test
function `φ` and every `n`, integration by parts for the `C¹` function `fn n` gives

`∫ z, fn n z * ∂φ z = -∫ z, ∂(fn n) z * φ z`

(`Work.MRMT.Beltrami.integral_mul_dz_eq_neg`; the `∂̄` version is
`Work.MRMT.QC.integral_mul_dzbar_eq_neg`).  The left-hand side converges to `∫ z, f z * ∂φ z`
because `fn n → f` uniformly on the compact support of `∂φ`, and the right-hand side converges to
`-∫ z, D z * φ z` because `∂(fn n) → D` in `L²` of that compact set and `φ` is bounded there
(`Work.MRMT.Found.PLWD2.pairing_tendsto_of_eLpNorm`).  Uniqueness of limits identifies the two.

The passage to the limit is phrased once for an abstract "differential operator" `T` and then
specialised to `T = ∂` and `T = ∂̄`.
-/
import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.PLWD2.pairing_tendsto_of_eLpNorm
import Submission.Work.MRMT.Found.PLWD2.eLpNorm_mul_sub_tendsto
import Submission.Work.MRMT.Beltrami.integral_mul_dz_eq_neg
import Submission.Work.MRMT.QC.integral_mul_dzbar_eq_neg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

set_option linter.style.haveILetI false

namespace Work.MRMT.Found

/-! ## Elementary facts about `∂` and `∂̄` -/

/-- `∂` is continuous for a `C¹` function. -/
theorem continuous_dz_of_contDiff_one {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g) :
    Continuous (Work.MRMT.dz g) := by
  have h : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  unfold Work.MRMT.dz
  simp only [div_eq_mul_inv]
  exact ((h.clm_apply continuous_const).sub
    (continuous_const.mul (h.clm_apply continuous_const))).mul_const _

/-- `∂̄` is continuous for a `C¹` function. -/
theorem continuous_dzbar_of_contDiff_one {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g) :
    Continuous (Work.MRMT.dzbar g) := by
  have h : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  unfold Work.MRMT.dzbar
  simp only [div_eq_mul_inv]
  exact ((h.clm_apply continuous_const).add
    (continuous_const.mul (h.clm_apply continuous_const))).mul_const _

/-- `∂ψ` vanishes outside the (closed) support of `ψ`. -/
theorem support_dz_subset_tsupport (ψ : ℂ → ℂ) :
    Function.support (Work.MRMT.dz ψ) ⊆ tsupport ψ := by
  intro z hz
  by_contra h
  apply hz
  have h0 : fderiv ℝ ψ z = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq (notMem_tsupport_iff_eventuallyEq.mp h)]
    simp
  rw [Work.MRMT.dz, h0]
  simp

/-- `∂̄ψ` vanishes outside the (closed) support of `ψ`. -/
theorem support_dzbar_subset_tsupport (ψ : ℂ → ℂ) :
    Function.support (Work.MRMT.dzbar ψ) ⊆ tsupport ψ := by
  intro z hz
  by_contra h
  apply hz
  have h0 : fderiv ℝ ψ z = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq (notMem_tsupport_iff_eventuallyEq.mp h)]
    simp
  rw [Work.MRMT.dzbar, h0]
  simp

/-! ## Uniform convergence on a compact support -/

/-- Uniform convergence on a compact set `K` passes to the integrals against a function `ψ` whose
support lies in `K`. -/
theorem tendsto_integral_sub_mul_of_tendstoUniformlyOn {F : ℕ → ℂ → ℂ} {f ψ : ℂ → ℂ}
    {K : Set ℂ} (hK : IsCompact K) (hunif : TendstoUniformlyOn F f atTop K)
    (hψsupp : Function.support ψ ⊆ K) (hψcont : ContinuousOn ψ K) :
    Tendsto (fun n => ∫ z, (F n z - f z) * ψ z) atTop (nhds 0) := by
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hψcont
  set C : ℝ := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hCbound : ∀ z ∈ K, ‖ψ z‖ ≤ C := fun z hz => (hC₀ z hz).trans (le_max_left _ _)
  have hvol : 0 ≤ ((volume : Measure ℂ) K).toReal := ENNReal.toReal_nonneg
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / (C * ((volume : Measure ℂ) K).toReal + 1) with hδdef
  have hden : 0 < C * ((volume : Measure ℂ) K).toReal + 1 := by
    linarith [mul_nonneg hC0 hvol]
  have hδpos : 0 < δ := by
    rw [hδdef]; exact div_pos hε hden
  have hδsmall : δ * C * ((volume : Measure ℂ) K).toReal < ε := by
    have h1 : C * ((volume : Measure ℂ) K).toReal
        / (C * ((volume : Measure ℂ) K).toReal + 1) < 1 := by
      rw [div_lt_one hden]; linarith
    have h2 : δ * C * ((volume : Measure ℂ) K).toReal
        = ε * (C * ((volume : Measure ℂ) K).toReal
            / (C * ((volume : Measure ℂ) K).toReal + 1)) := by
      rw [hδdef]; field_simp
    rw [h2]
    calc ε * (C * ((volume : Measure ℂ) K).toReal
          / (C * ((volume : Measure ℂ) K).toReal + 1)) < ε * 1 :=
          mul_lt_mul_of_pos_left h1 hε
      _ = ε := mul_one ε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((Metric.tendstoUniformlyOn_iff.mp hunif) δ hδpos)
  refine ⟨N, fun n hn => ?_⟩
  have hzero : ∀ z ∉ K, (F n z - f z) * ψ z = 0 := by
    intro z hz
    have hz' : ψ z = 0 := by
      by_contra h
      exact hz (hψsupp (Function.mem_support.mpr h))
    simp [hz']
  rw [dist_eq_norm, sub_zero, (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm]
  calc ‖∫ z in K, (F n z - f z) * ψ z‖
      ≤ (δ * C) * ((volume : Measure ℂ) K).toReal := by
        refine norm_setIntegral_le_of_norm_le_const hK.measure_lt_top (fun z hz => ?_)
        rw [norm_mul]
        refine mul_le_mul (le_of_lt ?_) (hCbound z hz) (norm_nonneg _) (le_of_lt hδpos)
        have hz' := hN n hn z hz
        rwa [dist_eq_norm, norm_sub_rev] at hz'
    _ = δ * C * ((volume : Measure ℂ) K).toReal := by ring
    _ < ε := hδsmall

/-- An `L²` function on a compact set is integrable there (finite measure). -/
theorem integrableOn_of_memLp_two {g : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hg : MemLp g 2 (volume.restrict K)) : IntegrableOn g K volume := by
  haveI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact memLp_one_iff_integrable.mp (hg.mono_exponent (by norm_num))

/-! ## The abstract limit lemma -/

/-- **Weak derivatives are limits of pointwise derivatives.**  Let `T` be a "differential
operator" (in the applications `∂` or `∂̄`), let `fn` be continuous `ℂ → ℂ`-functions converging
locally uniformly to `f`, and suppose that

* `T ψ` is continuous with support contained in the support of `ψ`, for smooth compactly supported
  `ψ`;
* `T (fn n) → D` in `L²` on every compact set;
* integration by parts holds: `∫ z, fn n z * T ψ z = -∫ z, T (fn n) z * ψ z` for every smooth
  compactly supported `ψ`.

Then `D` is the weak `T`-derivative of `f`. -/
theorem weakDeriv_limit_generic
    {T : (ℂ → ℂ) → (ℂ → ℂ)} {fn : ℕ → ℂ → ℂ} {f D : ℂ → ℂ}
    (hfn : ∀ n, Continuous (fn n))
    (hfcont : Continuous f)
    (hconv : TendstoLocallyUniformly fn f atTop)
    (hTfn : ∀ n, Continuous (T (fn n)))
    (hTψc : ∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → Continuous (T ψ))
    (hTψsupp : ∀ ψ : ℂ → ℂ, Function.support (T ψ) ⊆ tsupport ψ)
    (hD : ∀ K : Set ℂ, IsCompact K →
      Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun z => T (fn n) z - D z) 2
        (MeasureTheory.volume.restrict K)) Filter.atTop (nhds 0))
    (hIBP : ∀ (n : ℕ) (ψ : ℂ → ℂ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      ∫ z, fn n z * T ψ z = -∫ z, T (fn n) z * ψ z) :
    LocallyIntegrable f volume ∧ LocallyIntegrable D volume ∧
      ∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        Integrable (fun z => f z * T ψ z) ∧ Integrable (fun z => D z * ψ z) ∧
        ∫ z, f z * T ψ z = -∫ z, D z * ψ z := by
  classical
  -- `T (fn n)` is `L²` on every compact set
  have hmemLp : ∀ (K : Set ℂ), IsCompact K → ∀ n,
      MemLp (fun z => T (fn n) z) 2 (volume.restrict K) := by
    intro K hK n
    haveI : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hTfn n).continuousOn
    refine MeasureTheory.MemLp.of_bound ((hTfn n).aestronglyMeasurable.restrict) (max C 0) ?_
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact (hC z hz).trans (le_max_left _ _)
  -- `D` is `L²` on every compact set, hence locally integrable
  have hDmemLp : ∀ (K : Set ℂ) (hK : IsCompact K),
      MemLp D 2 (volume.restrict K) := by
    intro K hK
    exact Work.MRMT.Found.PLWD2.memLp_of_tendsto_eLpNorm_two_sub (u := fun n => T (fn n))
      (fun n => hmemLp K hK n) (hD K hK)
  refine ⟨hfcont.locallyIntegrable, ?_, ?_⟩
  · intro x
    exact ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x zero_lt_one,
      integrableOn_of_memLp_two (isCompact_closedBall x 1) (hDmemLp _ (isCompact_closedBall x 1))⟩
  · intro ψ hψcd hψcs
    have hKc : IsCompact (tsupport ψ) := hψcs
    have hKmeas : MeasurableSet (tsupport ψ) := hKc.isClosed.measurableSet
    have hψc : Continuous ψ := hψcd.continuous
    have hTψcont : Continuous (T ψ) := hTψc ψ hψcd hψcs
    have hsuppT : Function.support (T ψ) ⊆ tsupport ψ := hTψsupp ψ
    -- integrability of `g * T ψ` for `g` continuous on the compact support of `ψ`
    have hint : ∀ {g : ℂ → ℂ}, ContinuousOn g (tsupport ψ) →
        Integrable (fun z => g z * T ψ z) := by
      intro g hg
      refine (integrableOn_iff_integrable_of_support_subset (s := tsupport ψ) ?_).mp ?_
      · exact (Function.support_mul_subset_right g (T ψ)).trans hsuppT
      · exact (hg.mul hTψcont.continuousOn).integrableOn_compact hKc
    have hintf : Integrable (fun z => f z * T ψ z) := hint hfcont.continuousOn
    -- the `f`-side limit
    have hunif : TendstoUniformlyOn fn f atTop (tsupport ψ) :=
      (tendstoLocallyUniformly_iff_forall_isCompact.mp hconv) (tsupport ψ) hKc
    have hdiff : Tendsto (fun n => ∫ z, (fn n z - f z) * T ψ z) atTop (nhds 0) :=
      tendsto_integral_sub_mul_of_tendstoUniformlyOn hKc hunif hsuppT hTψcont.continuousOn
    have hlimf : Tendsto (fun n => ∫ z, fn n z * T ψ z) atTop (nhds (∫ z, f z * T ψ z)) := by
      have heq : (fun n => ∫ z, (fn n z - f z) * T ψ z)
          = fun n => (∫ z, fn n z * T ψ z) - (∫ z, f z * T ψ z) := by
        funext n
        rw [← integral_sub (hint (hfn n).continuousOn) hintf]
        congr 1
        funext z
        ring
      rw [heq] at hdiff
      exact tendsto_sub_nhds_zero_iff.mp hdiff
    -- the `D`-side limit
    have hlimD : Tendsto (fun n => ∫ z, T (fn n) z * ψ z) atTop (nhds (∫ z, D z * ψ z)) :=
      Work.MRMT.Found.PLWD2.pairing_tendsto_of_eLpNorm hKc hψc (subset_tsupport ψ)
        (fun n => hmemLp (tsupport ψ) hKc n) (hD (tsupport ψ) hKc)
    have hlimD' : Tendsto (fun n => ∫ z, fn n z * T ψ z) atTop (nhds (-∫ z, D z * ψ z)) := by
      have h := hlimD.neg
      have heq : (fun n => -∫ z, T (fn n) z * ψ z) = fun n => ∫ z, fn n z * T ψ z := by
        funext n
        rw [hIBP n ψ hψcd hψcs]
      rwa [heq] at h
    -- integrability of `D * ψ`
    have hDψ : Integrable (fun z => D z * ψ z) := by
      haveI : IsFiniteMeasure (volume.restrict (tsupport ψ)) :=
        isFiniteMeasure_restrict.mpr hKc.measure_lt_top.ne
      have hψmem : MemLp ψ 2 (volume.restrict (tsupport ψ)) := by
        obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hψc.continuousOn
        refine MeasureTheory.MemLp.of_bound (hψc.aestronglyMeasurable.restrict) (max C 0) ?_
        filter_upwards [ae_restrict_mem hKmeas] with z hz
        exact (hC z hz).trans (le_max_left _ _)
      have hInt : Integrable (fun z => D z * ψ z) (volume.restrict (tsupport ψ)) :=
        (hDmemLp (tsupport ψ) hKc).integrable_mul hψmem
      refine (integrableOn_iff_integrable_of_support_subset (s := tsupport ψ) ?_).mp hInt
      exact (Function.support_mul_subset_right D ψ).trans (subset_tsupport ψ)
    exact ⟨hintf, hDψ, tendsto_nhds_unique hlimf hlimD'⟩

/-! ## The theorem -/

theorem weakDeriv_of_approx {fn : ℕ → ℂ → ℂ} {f D E : ℂ → ℂ}
    (hfc : ∀ n, ContDiff ℝ 1 (fn n))
    (hconv : TendstoLocallyUniformly fn f atTop)
    (hD : ∀ K : Set ℂ, IsCompact K →
      Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun z => Work.MRMT.dz (fn n) z - D z) 2
        (MeasureTheory.volume.restrict K)) Filter.atTop (nhds 0))
    (hE : ∀ K : Set ℂ, IsCompact K →
      Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun z => Work.MRMT.dzbar (fn n) z - E z) 2
        (MeasureTheory.volume.restrict K)) Filter.atTop (nhds 0)) :
    Work.MRMT.IsDzDeriv f D ∧ Work.MRMT.IsDbarDeriv f E := by
  have hfn : ∀ n, Continuous (fn n) := fun n => (hfc n).continuous
  have hfcont : Continuous f := hconv.continuous (Eventually.of_forall hfn).frequently
  have hdz := weakDeriv_limit_generic (T := Work.MRMT.dz) (fn := fn) (f := f) (D := D)
    hfn hfcont hconv (fun n => continuous_dz_of_contDiff_one (hfc n))
    (fun ψ h1 _ => continuous_dz_of_contDiff_one h1)
    (fun ψ => support_dz_subset_tsupport ψ)
    hD (fun n ψ h1 h2 => Work.MRMT.Beltrami.integral_mul_dz_eq_neg (hfc n) h1 h2)
  have hdzbar := weakDeriv_limit_generic (T := Work.MRMT.dzbar) (fn := fn) (f := f) (D := E)
    hfn hfcont hconv (fun n => continuous_dzbar_of_contDiff_one (hfc n))
    (fun ψ h1 _ => continuous_dzbar_of_contDiff_one h1)
    (fun ψ => support_dzbar_subset_tsupport ψ)
    hE (fun n ψ h1 h2 => Work.MRMT.QC.integral_mul_dzbar_eq_neg (hfc n) h1 h2)
  have htop : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) := by simp
  exact ⟨⟨hdz.1, hdz.2.1,
            fun φ => hdz.2.2 (φ : ℂ → ℂ) (φ.contDiff.of_le htop) φ.hasCompactSupport⟩,
         ⟨hdzbar.1, hdzbar.2.1,
            fun φ => hdzbar.2.2 (φ : ℂ → ℂ) (φ.contDiff.of_le htop) φ.hasCompactSupport⟩⟩

end Work.MRMT.Found
