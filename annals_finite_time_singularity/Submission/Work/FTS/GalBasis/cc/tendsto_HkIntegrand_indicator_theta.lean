/-
# `Work.FTS.GalBasis.cc.tendsto_HkIntegrand_indicator_theta`

The `θ`-shrinking lemma of the `ℋ⁴`-density argument: if `s : ℕ → Set ℝ` is a decreasing
sequence of measurable subsets of `Iθ` whose intersection is empty (every `θ ∈ Iθ` is
eventually excluded), then the `ℋ⁴`-mass of `f` carried by `s N`,

  `thetaShrinkInt α f (s N) = ∫_{Iz} ∫_{Iθ} HkIntegrand α 4 f z θ · 1_{s N}(θ)`

tends to `0`.

The proof is a dominated convergence on the product measure
`μ = (volume.restrict Iz).prod (volume.restrict Iθ)`: the integrands
`p ↦ HkIntegrand α 4 f p.1 p.2 · 1_{s N}(p.2)` are dominated by the (integrable, by `HkMem`)
function `p ↦ HkIntegrand α 4 f p.1 p.2`, and they converge pointwise to `0` because for almost
every `θ ∈ Iθ` the antitonicity of `s` makes `1_{s N}(θ) = 0` for all large `N`.  Fubini
(`MeasureTheory.integral_prod`) identifies the product integral with the iterated integral
defining `thetaShrinkInt`.
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.GalBasis.cc.ShrinkDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

/-- In a decreasing sequence of sets, `s N ⊆ s M` whenever `M ≤ N`. -/
theorem antitone_chain {s : ℕ → Set ℝ} (hanti : ∀ N : ℕ, s (N + 1) ⊆ s N) :
    ∀ {N M : ℕ}, M ≤ N → s N ⊆ s M := by
  intro N
  induction N with
  | zero =>
      intro M hM
      obtain rfl : M = 0 := Nat.le_zero.mp hM
      exact subset_rfl
  | succ N ih =>
      intro M hM
      rcases lt_or_ge M (N + 1) with hlt | hge
      · exact (hanti N).trans (ih (Nat.lt_succ_iff.mp hlt))
      · obtain rfl : M = N + 1 := le_antisymm hM hge
        exact subset_rfl

theorem tendsto_HkIntegrand_indicator_theta {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) {s : ℕ → Set ℝ}
    (hmeas : ∀ N : ℕ, MeasurableSet (s N)) (hsub : ∀ N : ℕ, s N ⊆ Work.Spaces.Iθ)
    (hanti : ∀ N : ℕ, s (N + 1) ⊆ s N)
    (hlim : ∀ θ ∈ Work.Spaces.Iθ, ∃ N : ℕ, θ ∉ s N) :
    Filter.Tendsto (fun N : ℕ => thetaShrinkInt α f (s N)) Filter.atTop (nhds 0) := by
  have hIz : MeasurableSet Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]; exact measurableSet_Ici
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  set μz : Measure ℝ := volume.restrict Work.Spaces.Iz with hμz
  set μθ : Measure ℝ := volume.restrict Work.Spaces.Iθ with hμθ
  set HH : ℝ × ℝ → ℝ := fun p => Work.Spaces.HkIntegrand α 4 f p.1 p.2 with hHH
  set GG : ℕ → ℝ × ℝ → ℝ :=
    fun N p => HH p * (s N).indicator (fun _ => (1 : ℝ)) p.2 with hGG
  -- Measurability of the integrand on the product measure.
  have hHmeas : AEStronglyMeasurable HH (μz.prod μθ) := by
    rw [hμz, hμθ, hHH]
    exact Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      (hsm.continuousOn_HkIntegrand α 4)
  -- Integrability of the angular slices.
  have hHmemθ : ∀ᵐ z ∂μz, Integrable (fun θ => HH (z, θ)) μθ := by
    rw [hμz, hμθ]
    filter_upwards [MeasureTheory.ae_restrict_mem hIz] with z hz
    have h1 : Integrable (fun θ => Work.Spaces.HkIntegrand α 4 f z θ)
        (volume.restrict Work.Spaces.Iθ) := hmem.1 z hz
    simpa only [hHH] using h1
  -- Integrability of the norm of the inner integral.
  have hHmemZ : Integrable (fun z => ∫ θ, ‖HH (z, θ)‖ ∂μθ) μz := by
    rw [hμz, hμθ]
    have h1 : Integrable (fun z => ∫ θ, Work.Spaces.HkIntegrand α 4 f z θ
        ∂(volume.restrict Work.Spaces.Iθ)) (volume.restrict Work.Spaces.Iz) := hmem.2
    refine h1.congr (Filter.Eventually.of_forall fun z => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [hHH]
    rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 4 f z θ)]
  -- Integrability of the integrand on the product.
  have hHint : Integrable HH (μz.prod μθ) :=
    (MeasureTheory.integrable_prod_iff hHmeas).mpr ⟨hHmemθ, hHmemZ⟩
  -- Measurability of the truncated integrands.
  have hGGmeas : ∀ N, AEStronglyMeasurable (GG N) (μz.prod μθ) := by
    intro N
    have hind : AEStronglyMeasurable
        (fun p : ℝ × ℝ => (s N).indicator (fun _ => (1 : ℝ)) p.2) (μz.prod μθ) :=
      ((Measurable.indicator measurable_const (hmeas N)).comp measurable_snd).aestronglyMeasurable
    have h : AEStronglyMeasurable
        (fun p : ℝ × ℝ => HH p * (s N).indicator (fun _ => (1 : ℝ)) p.2)
        (μz.prod μθ) := hHmeas.mul hind
    exact h
  -- Domination of the truncated integrands.
  have hGGbound : ∀ N, ∀ᵐ p ∂μz.prod μθ, ‖GG N p‖ ≤ HH p := by
    intro N
    filter_upwards with p
    have hHp : 0 ≤ HH p := by
      simp only [hHH]; exact Work.Spaces.HkIntegrand_nonneg α 4 f p.1 p.2
    by_cases hp : p.2 ∈ s N
    · have hval : GG N p = HH p := by
        simp only [hGG, Set.indicator_of_mem hp, mul_one]
      rw [hval, Real.norm_of_nonneg hHp]
    · have hval : GG N p = 0 := by
        simp only [hGG, Set.indicator_of_notMem hp, mul_zero]
      rw [hval, norm_zero]
      exact hHp
  have hGGint : ∀ N, Integrable (GG N) (μz.prod μθ) :=
    fun N => Integrable.mono' hHint (hGGmeas N) (hGGbound N)
  -- Pointwise (a.e.) convergence to zero.
  have hGlim : ∀ᵐ p ∂μz.prod μθ, Tendsto (fun N => GG N p) Filter.atTop (nhds (0 : ℝ)) := by
    have hMeq : μz.prod μθ
        = (volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
      rw [hμz, hμθ]; exact MeasureTheory.Measure.prod_restrict _ _
    rw [hMeq]
    filter_upwards [MeasureTheory.ae_restrict_mem (hIz.prod hIθ)] with p hp
    obtain ⟨-, hθ⟩ := hp
    obtain ⟨N₀, hN₀⟩ := hlim p.2 hθ
    refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
    have hnotmem : p.2 ∉ s N := fun hmem => hN₀ (antitone_chain hanti hN hmem)
    simp only [hGG, Set.indicator_of_notMem hnotmem, mul_zero]
  -- Dominated convergence on the product measure.
  have hDCT : Tendsto (fun N => ∫ p, GG N p ∂(μz.prod μθ)) Filter.atTop (nhds 0) := by
    have h := MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := μz.prod μθ) (F := GG) (f := fun _ : ℝ × ℝ => (0 : ℝ))
      HH hGGmeas hHint hGGbound hGlim
    simpa using h
  -- Fubini identifies the product integral with `thetaShrinkInt`.
  refine hDCT.congr' (Filter.Eventually.of_forall fun N => ?_)
  have hterm : ∫ p, GG N p ∂(μz.prod μθ) = thetaShrinkInt α f (s N) := by
    rw [MeasureTheory.integral_prod (GG N) (hGGint N), hμz, hμθ]
    simp only [thetaShrinkInt, hGG, hHH]
  exact hterm

end Work.FTS.GalBasis.cc
