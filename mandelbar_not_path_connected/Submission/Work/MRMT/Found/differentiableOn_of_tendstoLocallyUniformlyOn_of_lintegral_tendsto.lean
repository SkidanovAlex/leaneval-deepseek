/-
Copyright: Work.MRMT (mandelbar) subproject.

# Locally uniform limits on an open set with vanishing `∂̄` are holomorphic

Let `V ⊆ ℂ` be open, `Gn : ℕ → ℂ → ℂ` locally Lipschitz on `V`, converging locally uniformly
*on `V`* to `G`, and suppose that the `L¹`-size of the pointwise Wirtinger derivative `∂̄ (Gn n)`
on every compact subset of `V` tends to `0`.  Then `G` is holomorphic on `V`.

This is the `On V` variant of
`Work.MRMT.Found.differentiableOn_of_tendstoLocallyUniformly_of_lintegral_tendsto`: the only
difference is that the convergence hypothesis is `TendstoLocallyUniformlyOn Gn G atTop V`
rather than the global `TendstoLocallyUniformly Gn G atTop`.  The proof is the same one, using
that `TendstoLocallyUniformlyOn` on an *open* set is equivalent to uniform convergence on every
compact subset (`tendstoLocallyUniformlyOn_iff_forall_isCompact`).
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.differentiableOn_of_tendstoLocallyUniformly_of_lintegral_tendsto

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

theorem differentiableOn_of_tendstoLocallyUniformlyOn_of_lintegral_tendsto {V : Set ℂ} (hV : IsOpen V)
    {G : ℂ → ℂ} {Gn : ℕ → ℂ → ℂ} (hGn : ∀ n, LocallyLipschitzOn V (Gn n))
    (hconv : TendstoLocallyUniformlyOn Gn G Filter.atTop V)
    (h0 : ∀ L : Set ℂ, IsCompact L → L ⊆ V →
      Filter.Tendsto (fun n => Work.MRMT.Found.lintegralAbsDbar (Gn n) L) Filter.atTop (nhds 0)) :
    DifferentiableOn ℂ G V := by
  -- a locally uniform limit of functions continuous on `V` is continuous on `V`
  have hGcont : ContinuousOn G V :=
    hconv.continuousOn ((Eventually.of_forall fun n => (hGn n).continuousOn).frequently)
  -- it suffices to know that the weak `∂̄` of `G` vanishes on `V` (Weyl's lemma)
  refine Work.MRMT.QC.differentiableOn_of_isDbarDerivOn_zero hV hGcont ?_
  refine ⟨hGcont.locallyIntegrableOn hV.measurableSet, locallyIntegrableOn_zero, ?_⟩
  intro φ hφ
  set K : Set ℂ := tsupport (φ : ℂ → ℂ) with hKdef
  have hK : IsCompact K := φ.hasCompactSupport
  -- `∂̄φ` is supported in `K`
  have hψsupp : Function.support (dzbar (φ : ℂ → ℂ)) ⊆ K := by
    rw [hKdef]; exact Work.MRMT.QC.support_dzbar_subset _
  have hψcont : Continuous (dzbar (φ : ℂ → ℂ)) :=
    Work.MRMT.QC.continuous_dzbar_of_contDiff' φ.contDiff (by simp)
  -- integrability of `g * ∂̄φ` for `g` continuous on `K` (compact support)
  have hint : ∀ {g : ℂ → ℂ}, ContinuousOn g K → Integrable (fun z => g z * dzbar (φ : ℂ → ℂ) z) := by
    intro g hg
    refine (integrableOn_iff_integrable_of_support_subset (s := K) ?_).mp ?_
    · exact (Function.support_mul_subset_right _ _).trans hψsupp
    · exact (hg.mul hψcont.continuousOn).integrableOn_compact hK
  constructor
  · exact hint (hGcont.mono hφ)
  constructor
  · simp only [zero_mul]
    exact integrable_zero ℂ ℂ _
  · -- the pairing `∫ G ∂̄φ` is the limit of the pairings `∫ Gn ∂̄φ`
    have hunif : TendstoUniformlyOn Gn G atTop K :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hV).mp hconv K hφ hK
    have hlim : Tendsto (fun n => ∫ z, Gn n z * dzbar (φ : ℂ → ℂ) z) atTop
        (nhds (∫ z, G z * dzbar (φ : ℂ → ℂ) z)) := by
      have hd := tendsto_integral_sub_mul_of_tendstoUniformlyOn_aux hK hunif hψsupp
        hψcont.continuousOn
      have hGnint : ∀ n, Integrable (fun z => Gn n z * dzbar (φ : ℂ → ℂ) z) :=
        fun n => hint ((hGn n).continuousOn.mono hφ)
      have hGint : Integrable (fun z => G z * dzbar (φ : ℂ → ℂ) z) := hint (hGcont.mono hφ)
      have hEq : (fun n => ∫ z, (Gn n z - G z) * dzbar (φ : ℂ → ℂ) z)
          = fun n => (∫ z, Gn n z * dzbar (φ : ℂ → ℂ) z)
              - (∫ z, G z * dzbar (φ : ℂ → ℂ) z) := by
        funext n
        rw [← integral_sub (hGnint n) hGint]
        exact integral_congr_ae (Eventually.of_forall fun z => by ring)
      rw [hEq] at hd
      exact tendsto_sub_nhds_zero_iff.mp hd
    -- each pairing is minus the integral of `∂̄(Gn n) φ`, which tends to `0` by hypothesis
    have hzero : Tendsto (fun n => ∫ z, dzbar (Gn n) z * φ z) atTop (nhds 0) := by
      obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ‖φ z‖ ≤ C := by
        obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn φ.continuous.continuousOn
        exact ⟨max C 0, le_max_right _ _, fun z hz => (hC z hz).trans (le_max_left _ _)⟩
      have h := tendsto_integral_dzbar_mul_of_lintegralAbsDbar_tendsto_zero_aux hK hC0 hC
        (h0 K hK hφ)
      have heq : (fun n => ∫ z in K, dzbar (Gn n) z * φ z)
          = fun n => ∫ z, dzbar (Gn n) z * φ z := by
        funext n
        exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
          rw [hKdef] at hz
          simp [image_eq_zero_of_notMem_tsupport hz])
      rw [heq] at h
      exact h
    have hIBP : ∀ n, ∫ z, Gn n z * dzbar (φ : ℂ → ℂ) z = - ∫ z, dzbar (Gn n) z * φ z :=
      fun n => integral_dzbar_eq_neg_of_locallyLipschitzOn_aux hV (hGn n) φ hφ
    have hzero2 : Tendsto (fun n => ∫ z, Gn n z * dzbar (φ : ℂ → ℂ) z) atTop (nhds 0) := by
      have hneg : Tendsto (fun n => -∫ z, dzbar (Gn n) z * φ z) atTop (nhds 0) := by
        simpa using hzero.neg
      rwa [funext fun n => (hIBP n).symm] at hneg
    have hfinal := tendsto_nhds_unique hlim hzero2
    rw [hfinal]
    simp

end Work.MRMT.Found
