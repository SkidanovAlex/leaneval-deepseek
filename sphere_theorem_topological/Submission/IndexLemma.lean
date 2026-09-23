import Submission.GlobalBM
import Submission.SecondVar2
import Submission.Commons.Analysis.Calculus.exists_lt_of_hasDerivAt_deriv_neg

/-!
# The index form of a minimising geodesic is non-negative

Let `γ` be a unit-speed *minimising* geodesic on `[0,L]` (i.e. `d(γ 0, γ L) = L`) and let `η` be a
coordinate field along it with `η 0 = η L = 0` (a variation with fixed endpoints).  This file proves
that the **index form** is non-negative:

`0 ≤ ∫₀^L indexIntegrand`,   i.e.   `∫⟨η, R(η,γ')γ'⟩ ≤ ∫‖Dη‖²`,

the classical statement that a minimising geodesic has non-negative second variation.  It is the
input of every comparison argument (Toponogov's hinge theorem, Klingenberg's shortening of closed
geodesics, the absence of interior conjugate points on a minimising geodesic).

## Proof

Consider the straight-line chart family `Ψ(s,t) = u t + s • η t` (the quadratic family of
`Submission/SecondVar2` with `ζ = 0`) and its energy `E(s) = fam2Energy … s`.

* `E(0) = L`, because `γ` is unit speed (`fam2Energy_eq_fam2G`).
* `E(s) ≥ E(0)`: the curve `Ψ(s,·)` joins `γ 0` to `γ L` (the endpoints are fixed because
  `η 0 = η L = 0`), so its length is `≥ d(γ 0, γ L) = L`; by Cauchy–Schwarz the energy dominates
  `(length)²/L = L`.  This is `Submission.GlobalBM.edist_piece_le`.
* `E'(0) = 0` and `E''(0) = -2 ∫ indexIntegrand` (the straight-line second variation formula,
  `Submission.SecondVar2.fam2Energy_second_deriv`, whose boundary terms vanish since
  `A = ζ + Γ(η,η) = Γ(η,η)` vanishes where `η` does).
* If `∫ indexIntegrand > 0` then `E''(0) < 0`, so the one-sided second-derivative test
  (`Commons.Analysis.Calculus.exists_lt_of_hasDerivAt_deriv_neg`) gives `E(s) < E(0)` for small
  `s > 0` — contradiction.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory
open Submission.Geodesic
open Submission.Jacobi
open Submission.ChartCurv
open Submission.SecondVariation
open Submission.ChartConnection
open Submission.CurvatureVec
open Submission.IndexForm
open Submission.IndexForm2
open Submission.BonnetMyers
open Submission.SecondVar2
open Submission.GlobalBM

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.IndexLemma

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-- **The index form of a minimising geodesic is non-positive** (equivalently, the index form
`-2 ∫ indexIntegrand` of the second variation is non-negative).

`(u,w)` is a unit-speed chart geodesic on `[0,L]` whose endpoints are at distance `L`, and `η` is a
variation field with `η 0 = η L = 0`; then `∫ indexIntegrand ≤ 0`. -/
theorem indexIntegral_nonpos_of_minimizing
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) (x₀ : M)
    {u w η e w' : ℝ → E} {L : ℝ} (hL : 0 < L)
    {A₀ B₀ : ℝ} (hA₀ : A₀ ≤ 0) (hB₀ : L ≤ B₀)
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t) (heC : ContinuousOn e (Icc 0 L))
    (hgeo : ∀ t ∈ Icc 0 L, w' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 0)
    (hunit : ∀ t ∈ Icc 0 L,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1)
    (hη0 : η 0 = 0) (hηL : η L = 0)
    (hstay_u : ∀ t ∈ Icc 0 L, u t ∈ (extChartAt I x₀).target)
    {a₁ a₂ : ℝ} (ha₁ : a₁ < 0) (ha₂ : 0 < a₂)
    (hstay : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc A₀ B₀,
      fam2 u η (fun _ => 0) s t ∈ (extChartAt I x₀).target)
    (hmin : Manifold.riemannianEDist I ((extChartAt I x₀).symm (u 0))
      ((extChartAt I x₀).symm (u L)) = ENNReal.ofReal L) :
    ∫ t in (0 : ℝ)..L, indexIntegrand cov x₀ u η w e t ≤ 0 := by
  set z : ℝ → E := fun _ => 0 with hzdef
  have hz_deriv : ∀ t ∈ Icc (0 : ℝ) L, HasDerivAt z (0 : E) t := fun t _ => hasDerivAt_const t 0
  have hzC : ContinuousOn (fun _ : ℝ => (0 : E)) (Icc 0 L) := continuousOn_const
  have hstay' : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc A₀ B₀,
      fam2 u η z s t ∈ (extChartAt I x₀).target := by
    intro s hs t ht
    simpa only [hzdef] using hstay s hs t ht
  set Efun : ℝ → ℝ := fun s => fam2Energy (I := I) x₀ u η z w e z L s with hEdef
  -- the family at the endpoints
  have hb1 : ∀ s : ℝ, fam2 u η z s 0 = u 0 := by
    intro s; simp only [fam2, hzdef, smul_zero, add_zero, hη0]
  have hb2 : ∀ s : ℝ, fam2 u η z s L = u L := by
    intro s; simp only [fam2, hzdef, smul_zero, add_zero, hηL]
  -- `E(0) = L`
  have hE0 : Efun 0 = L := by
    have h1 : Efun 0 = ∫ t in (0 : ℝ)..L,
        chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) := by
      simp only [hEdef]
      rw [fam2Energy_eq_fam2G]
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      simp only [fam2G, fam2T, fam2, fam2Curve, hzdef, zero_smul, add_zero, zero_div,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    rw [h1, intervalIntegral.integral_congr
      (fun t ht => hunit t (by rwa [uIcc_of_le hL.le] at ht)),
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  -- `E(s) ≥ E(0)`
  have hEge : ∀ s ∈ Ioo a₁ a₂, Efun 0 ≤ Efun s := by
    intro s hs
    have hle := GlobalBM.edist_piece_le (I := I) (cov := cov) hmet
      (x₀ := x₀) (u := u) (η := η) (ζ := z) (w := w) (e := e) (ζ' := z) (w' := w')
      (L₀ := L) (s := s) hL hu hw hη hz_deriv heC hzC
      (fun t ht => hstay' s ⟨hs.1.le, hs.2.le⟩ t (Icc_subset_Icc hA₀ hB₀ ht))
    simp only [fam2Curve, hb1 s, hb2 s] at hle
    rw [hmin] at hle
    have h2 : L ≤ Real.sqrt (L * Efun s) := by
      have h3 := (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg (L * Efun s))).mp hle
      simpa only [hEdef] using h3
    have hEnn : 0 ≤ Efun s := by
      change 0 ≤ fam2Energy (I := I) x₀ u η z w e z L s
      rw [fam2Energy_eq_fam2G]
      exact intervalIntegral.integral_nonneg hL.le
        (fun t _ => Submission.Minimal.chartGram_self_nonneg (I := I) x₀ _ _)
    have h4 : L * L ≤ L * Efun s := by
      have h5 : L ^ 2 ≤ (Real.sqrt (L * Efun s)) ^ 2 := pow_le_pow_left₀ hL.le h2 2
      rw [Real.sq_sqrt (mul_nonneg hL.le hEnn)] at h5
      calc L * L = L ^ 2 := by ring
        _ ≤ L * Efun s := h5
    have h8 : L ≤ Efun s := le_of_mul_le_mul_left h4 hL
    rw [hE0]
    exact h8
  -- the first derivative at `0` is `0`
  have hElocalmin : IsLocalMin Efun 0 :=
    Filter.eventually_iff_exists_mem.mpr
      ⟨Ioo a₁ a₂, isOpen_Ioo.mem_nhds ⟨ha₁, ha₂⟩, fun s hs => hEge s hs⟩
  have hE1 : HasDerivAt Efun (0 : ℝ) 0 := by
    have h := fam2Energy_hasDerivAt (I := I) (cov := cov) hmet x₀ hL.le
      (ζ := z) (ζ' := z)
      (a₁ := a₁) (a₂ := a₂) (δ₁ := a₁ / 2) (δ₂ := a₂ / 2) (s₀ := 0)
      (by linarith) (by linarith) (by linarith) (by linarith)
      hu hw hη hz_deriv heC hzC hA₀ hB₀ hstay'
    have h' : HasDerivAt Efun (2 * ∫ t in (0 : ℝ)..L,
        chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η z 0 t)
          (fam2DsT (cov := cov) x₀ u η z w e z 0 t) (fam2T w e z 0 t)) 0 := h
    have hd : deriv Efun 0 = 0 := hElocalmin.deriv_eq_zero
    have hval : 2 * (∫ t in (0 : ℝ)..L,
        chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η z 0 t)
          (fam2DsT (cov := cov) x₀ u η z w e z 0 t) (fam2T w e z 0 t)) = 0 := by
      rw [← h'.deriv, hd]
    rwa [hval] at h'
  -- the second derivative at `0`
  have hE2 : HasDerivAt (deriv Efun)
      (-2 * ∫ t in (0 : ℝ)..L, indexIntegrand cov x₀ u η w e t) 0 := by
    have h := fam2Energy_second_deriv (I := I) (cov := cov) hmet htor x₀ (ζ := z) (ζ' := z)
      (w := w) (e := e) (w' := w') hL ha₁ ha₂ hu hw hη hz_deriv heC hzC hgeo hA₀ hB₀ hstay' hstay_u
    have hA0 : fam2A (cov := cov) x₀ u η z 0 = 0 := by
      simp only [fam2A, hzdef, hη0, chrB_zero_snd, chrB_zero_fst, add_zero]
    have hAL : fam2A (cov := cov) x₀ u η z L = 0 := by
      simp only [fam2A, hzdef, hηL, chrB_zero_snd, chrB_zero_fst, add_zero]
    refine h.congr_deriv ?_
    rw [hA0, hAL]
    simp
  -- conclusion
  by_contra hcon
  rw [not_le] at hcon
  have hneg : -2 * (∫ t in (0 : ℝ)..L, indexIntegrand cov x₀ u η w e t) < 0 := by linarith
  obtain ⟨δ, hδpos, hδ⟩ :=
    Commons.Analysis.Calculus.exists_lt_of_hasDerivAt_deriv_neg hE1 hE2 hneg
  have hspos : 0 < min δ a₂ / 2 := by positivity
  have hsδ : min δ a₂ / 2 < δ := by
    have h1 : min δ a₂ ≤ δ := min_le_left _ _
    linarith
  have hsmem : min δ a₂ / 2 ∈ Ioo a₁ a₂ := by
    refine ⟨by linarith, ?_⟩
    have h1 : min δ a₂ ≤ a₂ := min_le_right _ _
    linarith
  have h1 := hδ (min δ a₂ / 2) hspos hsδ
  have h2 := hEge (min δ a₂ / 2) hsmem
  linarith

end

end Submission.IndexLemma
