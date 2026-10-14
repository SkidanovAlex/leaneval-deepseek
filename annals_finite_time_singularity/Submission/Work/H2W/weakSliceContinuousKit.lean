import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceBounds
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.QDefs
import Submission.Work.H2W.momentChainAe
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2W

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2
local notation "sEta" => Work.FTS.EllipticEst.sEta

variable {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}

/-! ## 1. `ContinuousOn` on `[0, π/2]` from the two one-sided endpoint limits -/

theorem continuousWithinAt_Icc_of_tendsto_Ioi {f : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (h : Filter.Tendsto f (𝓝[>] a) (𝓝 c)) (hv : f a = c) :
    ContinuousWithinAt f (Set.Icc a b) a := by
  rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE hab, hv]
  rw [Filter.tendsto_def]
  intro V hV
  have hVc : c ∈ V := mem_of_mem_nhds hV
  obtain ⟨δ, hδ, hsub⟩ := (nhdsGT_basis a).eventually_iff.1 (h.eventually hV)
  refine mem_of_superset ((mem_nhdsGE_iff_exists_Ico_subset).2 ⟨δ, hδ, subset_rfl⟩) ?_
  intro x hx
  rw [Set.mem_Ico] at hx
  rw [Set.mem_preimage]
  rcases eq_or_lt_of_le hx.1 with h' | h'
  · rw [← h', hv]; exact hVc
  · exact hsub ⟨h', hx.2⟩

theorem continuousWithinAt_Icc_of_tendsto_Iio {f : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (h : Filter.Tendsto f (𝓝[<] b) (𝓝 c)) (hv : f b = c) :
    ContinuousWithinAt f (Set.Icc a b) b := by
  rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE hab, hv]
  rw [Filter.tendsto_def]
  intro V hV
  have hVc : c ∈ V := mem_of_mem_nhds hV
  obtain ⟨δ, hδ, hsub⟩ := (nhdsLT_basis b).eventually_iff.1 (h.eventually hV)
  obtain ⟨δ', hδ1, hδ2⟩ := exists_between hδ
  refine mem_of_superset ((mem_nhdsLE_iff_exists_Icc_subset).2 ⟨δ', hδ2, subset_rfl⟩) ?_
  intro x hx
  rw [Set.mem_Icc] at hx
  rw [Set.mem_preimage]
  rcases eq_or_lt_of_le hx.2 with h' | h'
  · rw [h', hv]; exact hVc
  · exact hsub ⟨lt_of_lt_of_le hδ1 hx.1, h'⟩

theorem continuousOn_Icc_of_limits {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)))
    (h1 : Filter.Tendsto f (𝓝[<] (Real.pi / 2)) (𝓝 (f (Real.pi / 2)))) :
    ContinuousOn f (Set.Icc 0 (Real.pi / 2)) := by
  intro x hx
  rw [Set.mem_Icc] at hx
  rcases eq_or_lt_of_le hx.1 with h' | h'
  · subst h'
    exact continuousWithinAt_Icc_of_tendsto_Ioi (by positivity) h0 rfl
  · rcases eq_or_lt_of_le hx.2 with h'' | h''
    · subst h''
      exact continuousWithinAt_Icc_of_tendsto_Iio (by positivity) h1 rfl
    · exact ((hf.continuousWithinAt (show x ∈ Set.Ioo 0 (Real.pi / 2) from ⟨h', h''⟩)).continuousAt
        (isOpen_Ioo.mem_nhds (show x ∈ Set.Ioo 0 (Real.pi / 2) from ⟨h', h''⟩))).continuousWithinAt

/-! ## 2. Slice bounds from `weakSliceBounds` -/

theorem sq_add_three_le (x y w : ℝ) : (x + y + w) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + w ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - w), sq_nonneg (x - w)]

theorem sq_add_le_two (x y : ℝ) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (x - y)]

theorem sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ sEta θ :=
  Work.FTS.EllipticEst.remov.ws_sEta_nonneg hθ


/-- **`v²` is integrable** for a slice bounded pointwise on the closed interval. -/
theorem slice_sq_integrableOn_of_bound {v : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (haesm : MeasureTheory.AEStronglyMeasurable v (MeasureTheory.volume.restrict Iθ))
    (hbd : ∀ θ ∈ Iθ, |v θ| ≤ M) :
    MeasureTheory.IntegrableOn (fun θ => (v θ) ^ 2) Iθ := by
  refine Integrable.mono' (g := fun _ : ℝ => M ^ 2)
    (MeasureTheory.integrableOn_const Work.FTS.EllipticEst.remov.ws_vol_Iθ_ne_top)
    (haesm.pow 2) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  have h1 : |v θ| ≤ M := hbd θ hθ
  have h2 : (v θ) ^ 2 ≤ M ^ 2 := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact h2

/-- **`v² · sEta` is integrable** for a slice bounded pointwise on the open interval. -/
theorem slice_sq_mul_sEta_integrableOn {v : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (haesm : MeasureTheory.AEStronglyMeasurable v (MeasureTheory.volume.restrict Iθ))
    (hbd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |v θ| ≤ M) :
    MeasureTheory.IntegrableOn (fun θ => (v θ) ^ 2 * sEta θ) Iθ := by
  have hsEta_aesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => sEta θ)
      (MeasureTheory.volume.restrict Iθ) :=
    Work.FTS.EllipticEst.remov.ws_sEta_integrableOn.aestronglyMeasurable
  refine Integrable.mono' (g := fun θ => M ^ 2 * sEta θ)
    (Work.FTS.EllipticEst.remov.ws_sEta_integrableOn.const_mul (M ^ 2))
    ((haesm.pow 2).mul hsEta_aesm) ?_
  filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
  have h1 : |v θ| ≤ M := hbd θ hθ
  have h2 : (v θ) ^ 2 ≤ M ^ 2 := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  have h3 : 0 ≤ sEta θ := sEta_nonneg_Iθ (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) h3)]
  exact mul_le_mul_of_nonneg_right h2 h3

/-! ## 4. The slice form of the equation -/

/-- `F` is `C^∞` on the open quadrant: it agrees there with `bslOp α Ψ`. -/
theorem smoothOpen_source (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    Work.FTS.EllipticEst.SmoothOpen F :=
  Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
      (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth))
    (fun z θ hz hθ hθ' => h.eq z hz θ hθ hθ')

/-- **The slice form of the equation**: on the open angular interval,
`Lzero1 (Φ z ·) θ = G z θ + α²z²∂_z²Φ(z,θ) + α(5+α)·D_zΦ(z,θ)`. -/
theorem Lzero1_slice_eq {G Φ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (heq : ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Φ z θ = G z θ)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.EllipticEst.Lzero1 (fun t => Φ z t) θ
      = G z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Φ z θ)
        + (α * (5 + α)) * Work.Spaces.DzIter 1 Φ z θ := by
  have hb := Work.Elliptic.bslOp_apply α Φ z θ
  have hL : Work.FTS.EllipticEst.Lzero1 (fun t => Φ z t) θ = Work.Elliptic.Lzero Φ z θ := rfl
  have hDz : Work.Spaces.DzIter 1 Φ z θ = z * Work.Spaces.pz Φ z θ := rfl
  rw [hL]
  have hthis := heq θ hθ.1 hθ.2
  rw [hb] at hthis
  rw [hDz]
  linarith [hthis]

/-! ## 5. Moment conditions in the shape needed for the identity -/


/-- From `F_*(D_z f) = F_*(D_z²f) = 0` conclude `∫_θ ∂_z²f(z,θ) sinθcos²θ dθ = 0`
(using `z²∂_z²f = D_z²f - D_zf` on the open quadrant). -/
theorem moment_pzIter2_of_moment_Dz2 {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {z : ℝ} (hz : 0 < z)
    (hDzI : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.DzIter 1 f z θ * sg θ) Iθ)
    (hAI : MeasureTheory.IntegrableOn (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 f z θ) * sg θ) Iθ)
    (h1 : Work.Elliptic.Fstar (Work.Spaces.DzIter 1 f) z = 0)
    (h2 : Work.Elliptic.Fstar (Work.Spaces.DzIter 2 f) z = 0) :
    (∫ θ in Iθ, Work.Spaces.pzIter 2 f z θ * sg θ) = 0 := by
  have hae : (fun θ => Work.Spaces.DzIter 2 f z θ * sg θ)
      =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ => Work.Spaces.DzIter 1 f z θ * sg θ + (z ^ 2 * Work.Spaces.pzIter 2 f z θ) * sg θ) := by
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    have hz2 := Work.H2W.MomentAe.zsq_pzIter2_eq hf hz hθ
    have hz2' : z ^ 2 * Work.Spaces.pzIter 2 f z θ
        = Work.Spaces.DzIter 2 f z θ - Work.Spaces.DzIter 1 f z θ := by
      simpa only [show Work.Spaces.Dz f = Work.Spaces.DzIter 1 f from rfl] using hz2
    show Work.Spaces.DzIter 2 f z θ * sg θ
      = Work.Spaces.DzIter 1 f z θ * sg θ + (z ^ 2 * Work.Spaces.pzIter 2 f z θ) * sg θ
    rw [show Work.Spaces.DzIter 2 f z θ
        = Work.Spaces.DzIter 1 f z θ + z ^ 2 * Work.Spaces.pzIter 2 f z θ from by
      rw [hz2']
      ring]
    ring
  have hsplit : (∫ θ in Iθ, Work.Spaces.DzIter 2 f z θ * sg θ)
      = (∫ θ in Iθ, Work.Spaces.DzIter 1 f z θ * sg θ)
        + (∫ θ in Iθ, (z ^ 2 * Work.Spaces.pzIter 2 f z θ) * sg θ) := by
    rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_add hDzI hAI]
  have h1' : (∫ θ in Iθ, Work.Spaces.DzIter 1 f z θ * sg θ) = 0 := by
    simpa only [Work.Elliptic.Fstar] using h1
  have hAzero : (∫ θ in Iθ, (z ^ 2 * Work.Spaces.pzIter 2 f z θ) * sg θ) = 0 := by
    have hleft : (∫ θ in Iθ, Work.Spaces.DzIter 2 f z θ * sg θ) = 0 := by
      simpa only [Work.Elliptic.Fstar] using h2
    rw [hleft, h1', zero_add] at hsplit
    exact hsplit.symm
  have hcf : (∫ θ in Iθ, (z ^ 2 * Work.Spaces.pzIter 2 f z θ) * sg θ)
      = z ^ 2 * (∫ θ in Iθ, Work.Spaces.pzIter 2 f z θ * sg θ) := by
    rw [show (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 f z θ) * sg θ)
        = fun θ => z ^ 2 * (Work.Spaces.pzIter 2 f z θ * sg θ) from by funext θ; ring,
      MeasureTheory.integral_const_mul]
  rw [hcf] at hAzero
  exact (mul_eq_zero.mp hAzero).resolve_left (pow_ne_zero 2 hz.ne')

/-! ## 6. The moment identity of a slice -/

/-- **The angular moment of `Lzero1` on a slice vanishes.**  All the analytic content is in the
hypotheses: the slice equation, the honesty of the three pieces and the three vanishing moments. -/
theorem sliceLzero1_moment {G Φ : ℝ → ℝ → ℝ} {z : ℝ} (hα : 0 < α) (hz : 0 < z)
    (heq : ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Φ z θ = G z θ)
    (hGint : MeasureTheory.IntegrableOn (fun θ => G z θ * sg θ) Iθ)
    (hAint : MeasureTheory.IntegrableOn (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Φ z θ) * sg θ) Iθ)
    (hLint : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Φ z t) θ * sg θ) Iθ)
    (hmG : Work.Elliptic.Fstar G z = 0)
    (hmDz : (∫ θ in Iθ, Work.Spaces.DzIter 1 Φ z θ * sg θ) = 0)
    (hmA : (∫ θ in Iθ, (z ^ 2 * Work.Spaces.pzIter 2 Φ z θ) * sg θ) = 0) :
    (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => Φ z t) θ * sg θ) = 0 := by
  have hae : (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Φ z t) θ * sg θ)
      =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ => G z θ * sg θ + α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 Φ z θ) * sg θ)
        + (α * (5 + α)) * (Work.Spaces.DzIter 1 Φ z θ * sg θ)) := by
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    rw [Lzero1_slice_eq (hθ := hθ) heq]
    ring
  have hDzint : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 1 Φ z θ * sg θ) Iθ := by
    have h1 : MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Φ z t) θ * sg θ
          - (G z θ * sg θ + α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 Φ z θ) * sg θ))) Iθ :=
      hLint.sub (hGint.add (hAint.const_mul _))
    refine (h1.const_mul ((α * (5 + α))⁻¹)).congr ?_
    filter_upwards [hae] with θ hθ
    rw [hθ]
    have hcoef : α * (5 + α) ≠ 0 := by
      have : 0 < α * (5 + α) := by positivity
      exact ne_of_gt this
    field_simp
    ring
  have hkey : (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => Φ z t) θ * sg θ)
      = (∫ θ in Iθ, G z θ * sg θ)
        + α ^ 2 * (∫ θ in Iθ, (z ^ 2 * Work.Spaces.pzIter 2 Φ z θ) * sg θ)
        + (α * (5 + α)) * (∫ θ in Iθ, Work.Spaces.DzIter 1 Φ z θ * sg θ) := by
    rw [MeasureTheory.integral_congr_ae hae]
    have hI1 : MeasureTheory.IntegrableOn
        (fun θ => G z θ * sg θ
          + α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 Φ z θ) * sg θ)) Iθ :=
      hGint.add (hAint.const_mul (α ^ 2))
    have hI2 : MeasureTheory.IntegrableOn
        (fun θ => (α * (5 + α)) * (Work.Spaces.DzIter 1 Φ z θ * sg θ)) Iθ :=
      hDzint.const_mul (α * (5 + α))
    have hsplit1 := MeasureTheory.integral_add
      (f := fun θ => G z θ * sg θ
        + α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 Φ z θ) * sg θ))
      (g := fun θ => (α * (5 + α)) * (Work.Spaces.DzIter 1 Φ z θ * sg θ)) hI1 hI2
    have hsplit2 := MeasureTheory.integral_add
      (f := fun θ => G z θ * sg θ)
      (g := fun θ => α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 Φ z θ) * sg θ))
      hGint (hAint.const_mul (α ^ 2))
    rw [hsplit1, hsplit2, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hmG' : (∫ θ in Iθ, G z θ * sg θ) = 0 := by
    simpa only [Work.Elliptic.Fstar] using hmG
  rw [hkey, hmG', hmA, hmDz]
  ring

/-! ## 7. The endpoint limits of a slice -/

/-- **The two one-sided endpoint limits of a slice vanish.** -/
theorem slice_limits_of {G Φ : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hSmooth : Work.FTS.EllipticEst.SmoothOpen Φ)
    (hz0 : ∀ z, Φ z 0 = 0) (hzp : ∀ z, Φ z (Real.pi / 2) = 0)
    (h2 : ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Φ z θ') t) θ) ^ 2 * sEta θ) Iθ)
    (hL : ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 (fun t => Φ z t) θ) ^ 2 * sEta θ) Iθ)
    (hu : ∀ z, 0 < z → MeasureTheory.IntegrableOn (fun θ => (Φ z θ) ^ 2) Iθ)
    (hmom : ∀ z, 0 < z →
      (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => Φ z t) θ * sg θ) = 0) :
    ∀ z, 0 < z →
      Filter.Tendsto (fun θ => Φ z θ) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Filter.Tendsto (fun θ => Φ z θ) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  intro z hz
  have hall : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => Φ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun n => contDiffOn_iff_forall_nat_le.mp (hSmooth.curry_θ hz) n le_top
  refine ⟨Work.FTS.EllipticEst.remov.SourceBound.sliceTendstoZeroOfMoment _
      (hall 2) (h2 z hz) (hL z hz) (hu z hz) (hmom z hz), ?_⟩
  exact (Work.FTS.EllipticEst.H2W.weakSliceLimits _ hall (hz0 z) (hzp z)
    (h2 z hz) (hL z hz)).2.2.1

/-! ## 8. The `D_z`-slice vanishes at the endpoints -/

/-- The `D_z`-slice of `Ψ` vanishes at `θ = 0`. -/
theorem dz_zero_at_zero (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    Work.Spaces.Dz Ψ z 0 = 0 := by
  have hfun : (fun z' => Ψ z' 0) = fun _ => (0 : ℝ) := by
    funext z'; exact h.zero z'
  have hz0 : Work.Spaces.pz Ψ z 0 = 0 := by
    show deriv (fun z' => Ψ z' 0) z = 0
    rw [hfun, deriv_const]
  show Work.Spaces.Dz Ψ z 0 = 0
  rw [show Work.Spaces.Dz Ψ z 0 = z * Work.Spaces.pz Ψ z 0 from rfl, hz0, mul_zero]

/-- The `D_z`-slice of `Ψ` vanishes at `θ = π/2`. -/
theorem dz_zero_at_pi_half (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    Work.Spaces.Dz Ψ z (Real.pi / 2) = 0 := by
  have hfun : (fun z' => Ψ z' (Real.pi / 2)) = fun _ => (0 : ℝ) := by
    funext z'; exact h.pi_half z'
  have hzp : Work.Spaces.pz Ψ z (Real.pi / 2) = 0 := by
    show deriv (fun z' => Ψ z' (Real.pi / 2)) z = 0
    rw [hfun, deriv_const]
  show Work.Spaces.Dz Ψ z (Real.pi / 2) = 0
  rw [show Work.Spaces.Dz Ψ z (Real.pi / 2) = z * Work.Spaces.pz Ψ z (Real.pi / 2) from rfl,
    hzp, mul_zero]

/-! ## 9. The slice data of the weak class -/

/-- **The sum of two `sEta`-square-integrable slices is `sEta`-square-integrable.** -/
theorem slice_add_sq_integrableOn {u v : ℝ → ℝ}
    (hu : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * sEta θ) Iθ)
    (hv : MeasureTheory.IntegrableOn (fun θ => (v θ) ^ 2 * sEta θ) Iθ)
    (haesm : MeasureTheory.AEStronglyMeasurable (fun θ => u θ + v θ)
      (MeasureTheory.volume.restrict Iθ)) :
    MeasureTheory.IntegrableOn (fun θ => (u θ + v θ) ^ 2 * sEta θ) Iθ := by
  have hsEta_aesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => sEta θ)
      (MeasureTheory.volume.restrict Iθ) :=
    Work.FTS.EllipticEst.remov.ws_sEta_integrableOn.aestronglyMeasurable
  refine Integrable.mono'
    (g := fun θ => 2 * ((u θ) ^ 2 * sEta θ) + 2 * ((v θ) ^ 2 * sEta θ))
    ((hu.const_mul 2).add (hv.const_mul 2)) ((haesm.pow 2).mul hsEta_aesm) ?_
  filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
  have h3 : 0 ≤ sEta θ := sEta_nonneg_Iθ (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) h3)]
  calc (u θ + v θ) ^ 2 * sEta θ
      ≤ (2 * ((u θ) ^ 2 + (v θ) ^ 2)) * sEta θ :=
        mul_le_mul_of_nonneg_right (sq_add_le_two (u θ) (v θ)) h3
    _ = 2 * ((u θ) ^ 2 * sEta θ) + 2 * ((v θ) ^ 2 * sEta θ) := by ring

/-- **The `D_z`-iterates of `Ψ` up to order `3` are `sEta`-square-integrable on the slice.** -/
theorem DzIter_sq_integrableOn (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ}
    (hz : 0 < z) :
    ∀ j ≤ 3, MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter j Ψ z θ) ^ 2 * sEta θ) Iθ := by
  obtain ⟨M, hMnn, hMbd⟩ :=
    Work.FTS.EllipticEst.remov.SourceBound.weakSliceBounds (α := α) (k := 2) le_rfl h z hz
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.H2W.MomentAe.smoothOpen_zsq hΨ
  obtain ⟨-, -, -, -, h5, -, -, -⟩ :=
    Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots (α := α) (k := 2) le_rfl h z hz
  have h0 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 0 Ψ z θ) ^ 2 * sEta θ) Iθ :=
    slice_sq_mul_sEta_integrableOn hMnn
      (Work.FTS.EllipticEst.remov.ws_aesm_slice hΨ hz)
      (fun θ hθ => (hMbd θ (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)).1)
  have h1 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 1 Ψ z θ) ^ 2 * sEta θ) Iθ := by
    refine slice_sq_mul_sEta_integrableOn (M := |z| * M) (by positivity)
      (Work.FTS.EllipticEst.remov.ws_aesm_slice (Work.FTS.EllipticEst.SmoothOpen.DzIter hΨ 1) hz) ?_
    intro θ hθ
    have hb := (hMbd θ (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)).2.2.1
    show |Work.Spaces.DzIter 1 Ψ z θ| ≤ |z| * M
    rw [show Work.Spaces.DzIter 1 Ψ z θ = z * Work.Spaces.pz Ψ z θ from rfl, abs_mul]
    exact mul_le_mul_of_nonneg_left hb (abs_nonneg z)
  have hA2 : MeasureTheory.IntegrableOn
      (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * sEta θ) Iθ := by
    refine (h5.const_mul (z ^ 4)).congr (Filter.Eventually.of_forall fun θ => ?_)
    ring
  have hAesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (MeasureTheory.volume.restrict Iθ) :=
    Work.FTS.EllipticEst.remov.ws_aesm_slice hAso hz
  have h2 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 2 Ψ z θ) ^ 2 * sEta θ) Iθ := by
    have hae : (fun θ => (Work.Spaces.DzIter 2 Ψ z θ) ^ 2 * sEta θ)
        =ᵐ[MeasureTheory.volume.restrict Iθ]
        (fun θ => (Work.Spaces.DzIter 1 Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * sEta θ) := by
      filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      have hz2 := Work.H2W.MomentAe.zsq_pzIter2_eq hΨ hz hθ
      have hz2' : z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
          = Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.DzIter 1 Ψ z θ := by
        simpa only [show Work.Spaces.Dz Ψ = Work.Spaces.DzIter 1 Ψ from rfl] using hz2
      rw [show Work.Spaces.DzIter 2 Ψ z θ
          = Work.Spaces.DzIter 1 Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ from by
        rw [hz2']; ring]
    refine (slice_add_sq_integrableOn h1 hA2 ?_).congr hae.symm
    exact ((Work.FTS.EllipticEst.remov.ws_aesm_slice
      (Work.FTS.EllipticEst.SmoothOpen.DzIter hΨ 1) hz).add hAesm)
  have h3 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 3 Ψ z θ) ^ 2 * sEta θ) Iθ := by
    have hA1 : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
          * sEta θ) Iθ :=
      Work.FTS.EllipticEst.remov.ws_slot_slice hAso h.memA 1 (by omega) hz
    have hae : (fun θ => (Work.Spaces.DzIter 3 Ψ z θ) ^ 2 * sEta θ)
        =ᵐ[MeasureTheory.volume.restrict Iθ]
        (fun θ => (Work.Spaces.DzIter 2 Ψ z θ
          + Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2 * sEta θ) := by
      filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      have hz3' : Work.Spaces.DzIter 3 Ψ z θ
          = Work.Spaces.DzIter 2 Ψ z θ
            + Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
        have h := Work.H2W.MomentAe.DzIter_zsq_pzIter2_eq hΨ 1 hz hθ
        rw [show Work.Spaces.DzIter 3 Ψ z θ = Work.Spaces.DzIter (1 + 2) Ψ z θ from rfl,
          show Work.Spaces.DzIter 2 Ψ z θ = Work.Spaces.DzIter (1 + 1) Ψ z θ from rfl]
        linarith [h]
      rw [hz3']
    refine (slice_add_sq_integrableOn h2 hA1 ?_).congr hae.symm
    exact ((Work.FTS.EllipticEst.remov.ws_aesm_slice
      (Work.FTS.EllipticEst.SmoothOpen.DzIter hΨ 2) hz).add
      (Work.FTS.EllipticEst.remov.ws_aesm_slice
        (Work.FTS.EllipticEst.SmoothOpen.DzIter hAso 1) hz))
  intro j hj
  interval_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- **`(Lzero1 (Ψ z ·))²·sEta` is integrable**, from the slice form of the equation. -/
theorem psi_Lzero1_sq (hα : 0 < α) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ) ^ 2 * sEta θ) Iθ := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.H2W.MomentAe.smoothOpen_zsq hΨ
  obtain ⟨-, -, -, -, h5, -, h7, -⟩ :=
    Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots (α := α) (k := 2) le_rfl h z hz
  have h1 := DzIter_sq_integrableOn h hz 1 (by norm_num)
  have hA2 : MeasureTheory.IntegrableOn
      (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * sEta θ) Iθ := by
    refine (h5.const_mul (z ^ 4)).congr (Filter.Eventually.of_forall fun θ => ?_)
    ring
  have hsEta_aesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => sEta θ)
      (MeasureTheory.volume.restrict Iθ) :=
    Work.FTS.EllipticEst.remov.ws_sEta_integrableOn.aestronglyMeasurable
  have hsum_int : MeasureTheory.IntegrableOn
      (fun θ => (F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + (α * (5 + α)) * Work.Spaces.DzIter 1 Ψ z θ) ^ 2 * sEta θ) Iθ := by
    refine Integrable.mono'
      (g := fun θ => 3 * ((F z θ) ^ 2 * sEta θ)
        + 3 * ((α ^ 2) ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * sEta θ))
        + 3 * ((α * (5 + α)) ^ 2 * ((Work.Spaces.DzIter 1 Ψ z θ) ^ 2 * sEta θ)))
      ?_ ?_ ?_
    · refine ((h7.const_mul 3).add ((hA2.const_mul ((α ^ 2) ^ 2)).const_mul 3)).add
        ((h1.const_mul ((α * (5 + α)) ^ 2)).const_mul 3)
    · refine (((Work.FTS.EllipticEst.remov.ws_aesm_slice (smoothOpen_source h) hz).add
        ((Work.FTS.EllipticEst.remov.ws_aesm_slice hAso hz).const_mul (α ^ 2))).add
        ((Work.FTS.EllipticEst.remov.ws_aesm_slice
          (Work.FTS.EllipticEst.SmoothOpen.DzIter hΨ 1) hz).const_mul (α * (5 + α)))).pow 2
        |>.mul hsEta_aesm
    · filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      have h3 : 0 ≤ sEta θ := sEta_nonneg_Iθ (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) h3)]
      have hb := sq_add_three_le (F z θ) (α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        ((α * (5 + α)) * Work.Spaces.DzIter 1 Ψ z θ)
      calc (F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + (α * (5 + α)) * Work.Spaces.DzIter 1 Ψ z θ) ^ 2 * sEta θ
          ≤ 3 * ((F z θ) ^ 2 + (α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) ^ 2
              + ((α * (5 + α)) * Work.Spaces.DzIter 1 Ψ z θ) ^ 2) * sEta θ :=
            mul_le_mul_of_nonneg_right hb h3
        _ = 3 * ((F z θ) ^ 2 * sEta θ)
            + 3 * ((α ^ 2) ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * sEta θ))
            + 3 * ((α * (5 + α)) ^ 2 * ((Work.Spaces.DzIter 1 Ψ z θ) ^ 2 * sEta θ)) := by ring
  have hae : (fun θ => (Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ) ^ 2 * sEta θ)
      =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ => (F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + (α * (5 + α)) * Work.Spaces.DzIter 1 Ψ z θ) ^ 2 * sEta θ) := by
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    rw [Lzero1_slice_eq (hθ := hθ) (fun θ hθ hθ' => h.eq z hz θ hθ hθ')]
  exact hsum_int.congr hae.symm

/-- **`Lzero1 (Ψ z ·)` is a.e. strongly measurable** on the angular slice. -/
theorem psi_Lzero1_aesm (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ)
      (MeasureTheory.volume.restrict Iθ) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.H2W.MomentAe.smoothOpen_zsq hΨ
  refine (((Work.FTS.EllipticEst.remov.ws_aesm_slice (smoothOpen_source h) hz).add
      ((Work.FTS.EllipticEst.remov.ws_aesm_slice hAso hz).const_mul (α ^ 2))).add
      ((Work.FTS.EllipticEst.remov.ws_aesm_slice
        (Work.FTS.EllipticEst.SmoothOpen.DzIter hΨ 1) hz).const_mul (α * (5 + α)))).congr ?_
  filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
  exact (Lzero1_slice_eq (hθ := hθ) (fun θ hθ hθ' => h.eq z hz θ hθ hθ')).symm

/-- **The two endpoint limits of the slice `θ ↦ Ψ z θ` vanish.** -/
theorem psi_slice_limits (hα : 0 < α) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ z, 0 < z →
      Filter.Tendsto (fun θ => Ψ z θ) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Filter.Tendsto (fun θ => Ψ z θ) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hFso : Work.FTS.EllipticEst.SmoothOpen F := smoothOpen_source h
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.H2W.MomentAe.smoothOpen_zsq hΨ
  refine slice_limits_of (G := F) (Φ := Ψ) hα hΨ h.zero h.pi_half ?_ ?_ ?_ ?_
  · -- `(u'')² · sEta`
    intro z hz
    obtain ⟨-, -, h3, -, -, -, -, -⟩ :=
      Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots (α := α) (k := 2) le_rfl h z hz
    refine h3.congr (Filter.Eventually.of_forall fun θ => ?_)
    show (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ
      = (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ) ^ 2 * sEta θ
    rfl
  · exact fun z hz => psi_Lzero1_sq hα h hz
  · -- `u²`
    intro z hz
    obtain ⟨M, hMnn, hMbd⟩ :=
      Work.FTS.EllipticEst.remov.SourceBound.weakSliceBounds (α := α) (k := 2) le_rfl h z hz
    exact slice_sq_integrableOn_of_bound hMnn (Work.FTS.EllipticEst.remov.ws_aesm_slice hΨ hz)
      (fun θ hθ => (hMbd θ hθ).1)
  · -- the moment identity
    intro z hz
    obtain ⟨-, -, -, -, h5, -, h7, -⟩ :=
      Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots (α := α) (k := 2) le_rfl h z hz
    have hA2 : MeasureTheory.IntegrableOn
        (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * sEta θ) Iθ := by
      refine (h5.const_mul (z ^ 4)).congr (Filter.Eventually.of_forall fun θ => ?_)
      ring
    have hDzI2 : MeasureTheory.IntegrableOn
        (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * sg θ) Iθ :=
      (Work.FTS.EllipticEst.remov.ws_absMoment
        (Work.FTS.EllipticEst.remov.ws_aesm_slice hAso hz) hA2).1
    have hDzI1 : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.DzIter 1 Ψ z θ * sg θ) Iθ :=
      (Work.FTS.EllipticEst.remov.ws_absMoment
        (Work.FTS.EllipticEst.remov.ws_aesm_slice
          (Work.FTS.EllipticEst.SmoothOpen.DzIter hΨ 1) hz)
        (DzIter_sq_integrableOn h hz 1 (by norm_num))).1
    have hGint : MeasureTheory.IntegrableOn (fun θ => F z θ * sg θ) Iθ :=
      (Work.FTS.EllipticEst.remov.ws_absMoment
        (Work.FTS.EllipticEst.remov.ws_aesm_slice hFso hz) h7).1
    have hLint : MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ * sg θ) Iθ :=
      (Work.FTS.EllipticEst.remov.ws_absMoment (psi_Lzero1_aesm h hz)
        (psi_Lzero1_sq hα h hz)).1
    have hA2eq : (∫ θ in Iθ, Work.Spaces.pzIter 2 Ψ z θ * sg θ) = 0 :=
      moment_pzIter2_of_moment_Dz2 hΨ hz hDzI1 hDzI2
        (Work.H2W.MomentAe.Fstar_DzIter_le_Psi α F Ψ h 1 (by norm_num) z hz)
        (Work.H2W.MomentAe.Fstar_DzIter_le_Psi α F Ψ h 2 (by norm_num) z hz)
    have hmA : (∫ θ in Iθ, (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * sg θ) = 0 := by
      rw [show (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * sg θ)
          = fun θ => z ^ 2 * (Work.Spaces.pzIter 2 Ψ z θ * sg θ) from by funext θ; ring,
        MeasureTheory.integral_const_mul, hA2eq, mul_zero]
    have hmDz : (∫ θ in Iθ, Work.Spaces.DzIter 1 Ψ z θ * sg θ) = 0 := by
      simpa only [Work.Elliptic.Fstar] using
        (Work.H2W.MomentAe.Fstar_DzIter_le_Psi α F Ψ h 1 (by norm_num) z hz)
    exact sliceLzero1_moment (G := F) (Φ := Ψ) hα hz
      (fun θ hθ hθ' => h.eq z hz θ hθ hθ') hGint hDzI2 hLint (h.orthF z hz) hmDz hmA

/-! ## 10. The slice data of `D_zΨ` -/

/-- **`(∂_θ²(D_zΨ)_z)²·sEta` is integrable**, from the `i = 1` slot of `∂_θ²Ψ`. -/
theorem dzpsi_second_sq (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Work.Spaces.DzIter 1 Ψ z θ') t) θ) ^ 2
        * sEta θ) Iθ := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  obtain ⟨-, -, -, h4, -, -, -, -⟩ :=
    Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots (α := α) (k := 2) le_rfl h z hz
  refine (h4.const_mul (z ^ 2)).congr ?_
  filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
  have hQ : ((z, θ) : ℝ × ℝ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hsec : deriv (fun t => deriv (fun θ' => Work.Spaces.DzIter 1 Ψ z θ') t) θ
      = z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ := by
    rw [show deriv (fun t => deriv (fun θ' => Work.Spaces.DzIter 1 Ψ z θ') t) θ
        = Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ from rfl]
    rw [show Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
        = Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ from
      Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ 1 hQ]
    rfl
  rw [hsec]
  ring

/-- **`(Lzero1 (D_zΨ z ·))²·sEta` is integrable**, from `TT.bslOp_DzIter_eq`. -/
theorem dzpsi_Lzero1_sq (hα : 0 < α) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.DzIter 1 Ψ z t) θ) ^ 2
        * sEta θ) Iθ := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSΦ : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ) := hΨ.DzIter 1
  obtain ⟨-, -, -, -, -, -, -, h8⟩ :=
    Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots (α := α) (k := 2) le_rfl h z hz
  have hd2 := DzIter_sq_integrableOn h hz 2 (by norm_num)
  have hd3 := DzIter_sq_integrableOn h hz 3 (by norm_num)
  -- the second summand, `z²∂_z²Φ = D_z³Ψ - D_z²Ψ`
  have hA2 : MeasureTheory.IntegrableOn
      (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 * sEta θ) Iθ := by
    have hae : (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
          * sEta θ)
        =ᵐ[MeasureTheory.volume.restrict Iθ]
        (fun θ => (Work.Spaces.DzIter 3 Ψ z θ - Work.Spaces.DzIter 2 Ψ z θ) ^ 2 * sEta θ) := by
      filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      have hz2 := Work.H2W.MomentAe.zsq_pzIter2_eq hSΦ hz hθ
      have hz2' : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
          = Work.Spaces.DzIter 3 Ψ z θ - Work.Spaces.DzIter 2 Ψ z θ := by
        have h := Work.H2W.MomentAe.zsq_pzIter2_eq hSΦ hz hθ
        rw [show Work.Spaces.DzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
              = Work.Spaces.DzIter 3 Ψ z θ from rfl,
            show Work.Spaces.Dz (Work.Spaces.DzIter 1 Ψ) z θ
              = Work.Spaces.DzIter 2 Ψ z θ from rfl] at h
        exact h
      rw [hz2']
    have hd2neg : MeasureTheory.IntegrableOn
        (fun θ => (- Work.Spaces.DzIter 2 Ψ z θ) ^ 2 * sEta θ) Iθ := by
      refine hd2.congr (Filter.Eventually.of_forall fun θ => ?_)
      ring
    have hsum := slice_add_sq_integrableOn hd3 hd2neg
      ((Work.FTS.EllipticEst.remov.ws_aesm_slice
        (Work.FTS.EllipticEst.SmoothOpen.DzIter hΨ 3) hz).add
        (Work.FTS.EllipticEst.remov.ws_aesm_slice
          (Work.FTS.EllipticEst.SmoothOpen.DzIter hΨ 2) hz).neg)
    exact hsum.congr hae.symm
  have hsEta_aesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => sEta θ)
      (MeasureTheory.volume.restrict Iθ) :=
    Work.FTS.EllipticEst.remov.ws_sEta_integrableOn.aestronglyMeasurable
  have heqΦ : ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α (Work.Spaces.DzIter 1 Ψ) z θ = Work.Spaces.DzIter 1 F z θ :=
    fun θ hθ hθ' =>
      Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 1 h.smooth h.eq z hz θ hθ hθ'
  have hsum_int : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter 1 F z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
        + (α * (5 + α)) * Work.Spaces.DzIter 2 Ψ z θ) ^ 2 * sEta θ) Iθ := by
    refine Integrable.mono'
      (g := fun θ => 3 * ((Work.Spaces.DzIter 1 F z θ) ^ 2 * sEta θ)
        + 3 * ((α ^ 2) ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
            * sEta θ))
        + 3 * ((α * (5 + α)) ^ 2 * ((Work.Spaces.DzIter 2 Ψ z θ) ^ 2 * sEta θ)))
      ?_ ?_ ?_
    · refine ((h8.const_mul 3).add ((hA2.const_mul ((α ^ 2) ^ 2)).const_mul 3)).add
        ((hd2.const_mul ((α * (5 + α)) ^ 2)).const_mul 3)
    · refine (((Work.FTS.EllipticEst.remov.ws_aesm_slice
          (Work.FTS.EllipticEst.SmoothOpen.DzIter (smoothOpen_source h) 1) hz).add
        ((Work.FTS.EllipticEst.remov.ws_aesm_slice
          (Work.H2W.MomentAe.smoothOpen_zsq hSΦ) hz).const_mul (α ^ 2))).add
        ((Work.FTS.EllipticEst.remov.ws_aesm_slice
          (Work.FTS.EllipticEst.SmoothOpen.DzIter hΨ 2) hz).const_mul (α * (5 + α)))).pow 2
        |>.mul hsEta_aesm
    · filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      have h3 : 0 ≤ sEta θ := sEta_nonneg_Iθ (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) h3)]
      have hb := sq_add_three_le (Work.Spaces.DzIter 1 F z θ)
        (α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ))
        ((α * (5 + α)) * Work.Spaces.DzIter 2 Ψ z θ)
      calc (Work.Spaces.DzIter 1 F z θ
            + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
            + (α * (5 + α)) * Work.Spaces.DzIter 2 Ψ z θ) ^ 2 * sEta θ
          ≤ 3 * ((Work.Spaces.DzIter 1 F z θ) ^ 2
              + (α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)) ^ 2
              + ((α * (5 + α)) * Work.Spaces.DzIter 2 Ψ z θ) ^ 2) * sEta θ :=
            mul_le_mul_of_nonneg_right hb h3
        _ = 3 * ((Work.Spaces.DzIter 1 F z θ) ^ 2 * sEta θ)
            + 3 * ((α ^ 2) ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
                * sEta θ))
            + 3 * ((α * (5 + α)) ^ 2 * ((Work.Spaces.DzIter 2 Ψ z θ) ^ 2 * sEta θ)) := by ring
  have hae : (fun θ => (Work.FTS.EllipticEst.Lzero1
        (fun t => Work.Spaces.DzIter 1 Ψ z t) θ) ^ 2 * sEta θ)
      =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ => (Work.Spaces.DzIter 1 F z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
        + (α * (5 + α)) * Work.Spaces.DzIter 2 Ψ z θ) ^ 2 * sEta θ) := by
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    rw [Lzero1_slice_eq (hθ := hθ) heqΦ]
    rfl
  exact hsum_int.congr hae.symm

/-- **`Lzero1 (D_zΨ z ·)` is a.e. strongly measurable.** -/
theorem dzpsi_Lzero1_aesm (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.DzIter 1 Ψ z t) θ)
      (MeasureTheory.volume.restrict Iθ) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSΦ : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ) := hΨ.DzIter 1
  have heqΦ : ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α (Work.Spaces.DzIter 1 Ψ) z θ = Work.Spaces.DzIter 1 F z θ :=
    fun θ hθ hθ' =>
      Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 1 h.smooth h.eq z hz θ hθ hθ'
  refine (((Work.FTS.EllipticEst.remov.ws_aesm_slice
        (Work.FTS.EllipticEst.SmoothOpen.DzIter (smoothOpen_source h) 1) hz).add
      ((Work.FTS.EllipticEst.remov.ws_aesm_slice
        (Work.H2W.MomentAe.smoothOpen_zsq hSΦ) hz).const_mul (α ^ 2))).add
      ((Work.FTS.EllipticEst.remov.ws_aesm_slice
        (Work.FTS.EllipticEst.SmoothOpen.DzIter hΨ 2) hz).const_mul (α * (5 + α)))).congr ?_
  filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
  exact (Lzero1_slice_eq (hθ := hθ) heqΦ).symm

/-- **The two endpoint limits of the slice `θ ↦ D_zΨ z θ` vanish.** -/
theorem dzpsi_slice_limits (hα : 0 < α) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ z, 0 < z →
      Filter.Tendsto (fun θ => Work.Spaces.Dz Ψ z θ) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Filter.Tendsto (fun θ => Work.Spaces.Dz Ψ z θ) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSΦ : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ) := hΨ.DzIter 1
  have heqΦ : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α (Work.Spaces.DzIter 1 Ψ) z θ = Work.Spaces.DzIter 1 F z θ :=
    fun z hz θ hθ hθ' =>
      Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 1 h.smooth h.eq z hz θ hθ hθ'
  have hGint : ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 1 F z θ * sg θ) Iθ := by
    intro z hz
    obtain ⟨-, -, -, -, -, -, -, h8⟩ :=
      Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots (α := α) (k := 2) le_rfl h z hz
    exact (Work.FTS.EllipticEst.remov.ws_absMoment
      (Work.FTS.EllipticEst.remov.ws_aesm_slice
        (Work.FTS.EllipticEst.SmoothOpen.DzIter (smoothOpen_source h) 1) hz) h8).1
  refine slice_limits_of (G := Work.Spaces.DzIter 1 F) (Φ := Work.Spaces.DzIter 1 Ψ) hα hSΦ
    (fun z => dz_zero_at_zero h z) (fun z => dz_zero_at_pi_half h z) ?_ ?_ ?_ ?_
  · intro z hz
    refine (dzpsi_second_sq h hz).congr (Filter.Eventually.of_forall fun θ => ?_)
    rfl
  · exact fun z hz => dzpsi_Lzero1_sq hα h hz
  · intro z hz
    obtain ⟨M, hMnn, hMbd⟩ :=
      Work.FTS.EllipticEst.remov.SourceBound.weakSliceBounds (α := α) (k := 2) le_rfl h z hz
    refine slice_sq_integrableOn_of_bound (M := |z| * M) (by positivity)
      (Work.FTS.EllipticEst.remov.ws_aesm_slice hSΦ hz) ?_
    intro θ hθ
    have hb := (hMbd θ hθ).2.2.1
    show |Work.Spaces.DzIter 1 Ψ z θ| ≤ |z| * M
    rw [show Work.Spaces.DzIter 1 Ψ z θ = z * Work.Spaces.pz Ψ z θ from rfl, abs_mul]
    exact mul_le_mul_of_nonneg_left hb (abs_nonneg z)
  · intro z hz
    obtain ⟨-, -, -, -, -, -, -, h8⟩ :=
      Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots (α := α) (k := 2) le_rfl h z hz
    have hd2 := DzIter_sq_integrableOn h hz 2 (by norm_num)
    have hd3 := DzIter_sq_integrableOn h hz 3 (by norm_num)
    have hd2neg : MeasureTheory.IntegrableOn
        (fun θ => (- Work.Spaces.DzIter 2 Ψ z θ) ^ 2 * sEta θ) Iθ := by
      refine hd2.congr (Filter.Eventually.of_forall fun θ => ?_)
      ring
    -- `∫ (z²∂_z²Φ)·sg = 0`, via `z²∂_z²Φ = D_z³Ψ - D_z²Ψ`
    have hA2 : MeasureTheory.IntegrableOn
        (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 * sEta θ) Iθ := by
      have hae : (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
            * sEta θ)
          =ᵐ[MeasureTheory.volume.restrict Iθ]
          (fun θ => (Work.Spaces.DzIter 3 Ψ z θ - Work.Spaces.DzIter 2 Ψ z θ) ^ 2 * sEta θ) := by
        filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
        have hz2 := Work.H2W.MomentAe.zsq_pzIter2_eq hSΦ hz hθ
        have hz2' : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
            = Work.Spaces.DzIter 3 Ψ z θ - Work.Spaces.DzIter 2 Ψ z θ := by
          have h := Work.H2W.MomentAe.zsq_pzIter2_eq hSΦ hz hθ
          rw [show Work.Spaces.DzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
                = Work.Spaces.DzIter 3 Ψ z θ from rfl,
              show Work.Spaces.Dz (Work.Spaces.DzIter 1 Ψ) z θ
                = Work.Spaces.DzIter 2 Ψ z θ from rfl] at h
          exact h
        rw [hz2']
      have hsum := slice_add_sq_integrableOn hd3 hd2neg
        ((Work.FTS.EllipticEst.remov.ws_aesm_slice
          (Work.FTS.EllipticEst.SmoothOpen.DzIter hΨ 3) hz).add
          (Work.FTS.EllipticEst.remov.ws_aesm_slice
            (Work.FTS.EllipticEst.SmoothOpen.DzIter hΨ 2) hz).neg)
      exact hsum.congr hae.symm
    have hA2int : MeasureTheory.IntegrableOn
        (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) * sg θ) Iθ :=
      (Work.FTS.EllipticEst.remov.ws_absMoment
        (Work.FTS.EllipticEst.remov.ws_aesm_slice
          (Work.H2W.MomentAe.smoothOpen_zsq hSΦ) hz) hA2).1
    have hd2int : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.DzIter 2 Ψ z θ * sg θ) Iθ :=
      (Work.FTS.EllipticEst.remov.ws_absMoment
        (Work.FTS.EllipticEst.remov.ws_aesm_slice
          (Work.FTS.EllipticEst.SmoothOpen.DzIter hΨ 2) hz) hd2).1
    have hd3int : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.DzIter 3 Ψ z θ * sg θ) Iθ :=
      (Work.FTS.EllipticEst.remov.ws_absMoment
        (Work.FTS.EllipticEst.remov.ws_aesm_slice
          (Work.FTS.EllipticEst.SmoothOpen.DzIter hΨ 3) hz) hd3).1
    have hA2eq : (∫ θ in Iθ, (z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
        * sg θ) = 0 := by
      have hae : (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) * sg θ)
          =ᵐ[MeasureTheory.volume.restrict Iθ]
          (fun θ => Work.Spaces.DzIter 3 Ψ z θ * sg θ
            - Work.Spaces.DzIter 2 Ψ z θ * sg θ) := by
        filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
        have hz2 := Work.H2W.MomentAe.zsq_pzIter2_eq hSΦ hz hθ
        have hz2' : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
            = Work.Spaces.DzIter 3 Ψ z θ - Work.Spaces.DzIter 2 Ψ z θ := by
          have h := Work.H2W.MomentAe.zsq_pzIter2_eq hSΦ hz hθ
          rw [show Work.Spaces.DzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
                = Work.Spaces.DzIter 3 Ψ z θ from rfl,
              show Work.Spaces.Dz (Work.Spaces.DzIter 1 Ψ) z θ
                = Work.Spaces.DzIter 2 Ψ z θ from rfl] at h
          exact h
        rw [hz2']
        ring
      rw [MeasureTheory.integral_congr_ae hae,
        MeasureTheory.integral_sub hd3int hd2int]
      have hD3 : (∫ θ in Iθ, Work.Spaces.DzIter 3 Ψ z θ * sg θ) = 0 := by
        simpa only [Work.Elliptic.Fstar] using
          (Work.H2W.MomentAe.Fstar_DzIter_le_Psi α F Ψ h 3 (by norm_num) z hz)
      have hD2 : (∫ θ in Iθ, Work.Spaces.DzIter 2 Ψ z θ * sg θ) = 0 := by
        simpa only [Work.Elliptic.Fstar] using
          (Work.H2W.MomentAe.Fstar_DzIter_le_Psi α F Ψ h 2 (by norm_num) z hz)
      rw [hD3, hD2, sub_zero]
    have hLint : MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.DzIter 1 Ψ z t) θ * sg θ) Iθ :=
      (Work.FTS.EllipticEst.remov.ws_absMoment (dzpsi_Lzero1_aesm h hz)
        (dzpsi_Lzero1_sq hα h hz)).1
    have hDz2eq : (∫ θ in Iθ, Work.Spaces.DzIter 1 (Work.Spaces.DzIter 1 Ψ) z θ * sg θ) = 0 := by
      have h := Work.H2W.MomentAe.Fstar_DzIter_le_Psi α F Ψ h 2 (by norm_num) z hz
      rw [show Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) z
          = Work.Elliptic.Fstar (Work.Spaces.DzIter 1 (Work.Spaces.DzIter 1 Ψ)) z from rfl] at h
      simpa only [Work.Elliptic.Fstar] using h
    exact sliceLzero1_moment (G := Work.Spaces.DzIter 1 F) (Φ := Work.Spaces.DzIter 1 Ψ) hα hz
      (heqΦ z hz) (hGint z hz) hA2int hLint
      (Work.FTS.EllipticEst.remov.Fstar_DzIter_one_of_two_le (α := α) le_rfl h z hz) hDz2eq hA2eq


/-! ## 11. The kit -/

theorem weakSliceContinuousKit (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ z, 0 < z →
      ContinuousOn (fun θ => Ψ z θ) (Set.Icc 0 (Real.pi / 2)) ∧
      ContinuousOn (fun θ => Work.Spaces.Dz Ψ z θ) (Set.Icc 0 (Real.pi / 2)) := by
  intro z hz
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSΦ : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ) := hΨ.DzIter 1
  obtain ⟨h0, h1⟩ := psi_slice_limits hα h z hz
  obtain ⟨k0, k1⟩ := dzpsi_slice_limits hα h z hz
  constructor
  · refine continuousOn_Icc_of_limits ((hΨ.curry_θ hz).continuousOn) ?_ ?_
    · rw [h.zero z]; exact h0
    · rw [h.pi_half z]; exact h1
  · refine continuousOn_Icc_of_limits ?_ ?_ ?_
    · exact (Work.FTS.EllipticEst.remov.ws_contDiffOn_slice hSΦ hz).continuousOn
    · rw [dz_zero_at_zero h z]; exact k0
    · rw [dz_zero_at_pi_half h z]; exact k1

end Work.H2W
