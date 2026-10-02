/-
Copyright: Work.MRMT (mandelbar) subproject.

# Locally uniform limits with vanishing `∂̄` are holomorphic

Let `V ⊆ ℂ` be open, `Gn : ℕ → ℂ → ℂ` locally Lipschitz on `V`, converging locally uniformly to
`G`, and suppose that the `L¹`-size of the pointwise Wirtinger derivative `∂̄ (Gn n)` on every
compact subset of `V` tends to `0`.  Then `G` is holomorphic on `V`.

The proof has three ingredients:

* a locally uniform limit of functions continuous on `V` is continuous on `V`;
* for a locally Lipschitz function on `V`, integration by parts against a test function supported
  in `V` computes the distributional `∂̄` as the pointwise `∂̄` (the locally Lipschitz hypothesis
  is turned into a Lipschitz hypothesis on an *open* set containing the support, and then into a
  globally Lipschitz extension);
* the pairing `∫ (∂̄ Gn) φ` is controlled by `∫⁻ ‖∂̄ Gn‖`, which tends to `0`.

The conclusion then follows from Weyl's lemma in its weak form
(`Work.MRMT.QC.differentiableOn_of_isDbarDerivOn_zero`).
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.QC.isQCOn_of_lipschitz
import Submission.Work.MRMT.QC.differentiableOn_of_isDbarDerivOn_zero

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

/-! ## Auxiliary lemmas -/

/-- If `a n → 0` in `ℝ≥0∞`, then `(a n).toReal → 0`. -/
theorem tendsto_toReal_of_tendsto_nhds_zero_aux {a : ℕ → ℝ≥0∞}
    (h : Tendsto a atTop (nhds 0)) : Tendsto (fun n => (a n).toReal) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := by
    rw [ENNReal.ofReal_pos]; linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h.eventually (eventually_lt_nhds hpos))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  calc (a n).toReal ≤ (ENNReal.ofReal (ε / 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hN n hn).le
    _ = ε / 2 := ENNReal.toReal_ofReal (by linarith)
    _ < ε := by linarith

/-- A function which is locally Lipschitz on an open set `V` is Lipschitz on some *open* set `U`
containing a given compact subset `K ⊆ V`. -/
theorem exists_open_lipschitzOnWith_of_locallyLipschitzOn_of_isCompact_aux {g : ℂ → ℂ}
    {V K : Set ℂ} (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hg : LocallyLipschitzOn V g) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ U ⊆ V ∧ ∃ C : NNReal, LipschitzOnWith C g U := by
  obtain ⟨δ, hδpos, hδ⟩ := hK.exists_cthickening_subset_open hV hKV
  have hδhalf : (0 : ℝ) < δ / 2 := by linarith
  have hsub : Metric.cthickening (δ / 2) K ⊆ V :=
    (Metric.cthickening_mono (by linarith : δ / 2 ≤ δ) K).trans hδ
  have hK'c : IsCompact (Metric.cthickening (δ / 2) K) := hK.cthickening
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK'c (hg.mono hsub)
  refine ⟨interior (Metric.cthickening (δ / 2) K), isOpen_interior, ?_,
    interior_subset.trans hsub, C, hC.mono interior_subset⟩
  intro z hz
  rw [mem_interior_iff_mem_nhds]
  refine Filter.mem_of_superset (Metric.ball_mem_nhds z hδhalf) ?_
  intro y hy
  exact Metric.mem_cthickening_of_dist_le y z (δ / 2) K hz (le_of_lt hy)

/-- Integration by parts for a function which is locally Lipschitz on an open set `V`, against a
test function supported in `V`: the distributional `∂̄` is the pointwise Wirtinger derivative. -/
theorem integral_dzbar_eq_neg_of_locallyLipschitzOn_aux {g : ℂ → ℂ} {V : Set ℂ}
    (hV : IsOpen V) (hg : LocallyLipschitzOn V g) (ψ : 𝓓(⊤, ℂ))
    (hψ : tsupport (ψ : ℂ → ℂ) ⊆ V) :
    ∫ z, g z * dzbar (ψ : ℂ → ℂ) z = - ∫ z, dzbar g z * ψ z := by
  obtain ⟨U, hU, hKU, -, C, hC⟩ :=
    exists_open_lipschitzOnWith_of_locallyLipschitzOn_of_isCompact_aux hV ψ.hasCompactSupport hψ hg
  obtain ⟨C', G, hG, hEq⟩ := Work.MRMT.QC.exists_lipschitzWith_eqOn_of_lipschitzOnWith hC
  exact Work.MRMT.QC.integral_dzbar_eq_neg hU hC hC.continuousOn hG hEq ψ hKU

/-- The pairing of `∂̄ g` against a function bounded by `C` on a compact set `L` is controlled by
the `L¹`-size `∫⁻_L ‖∂̄ g‖` of `∂̄ g`; hence if the latter tends to `0`, so does the pairing. -/
theorem tendsto_integral_dzbar_mul_of_lintegralAbsDbar_tendsto_zero_aux {L : Set ℂ}
    (hL : IsCompact L) {φ : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C) (hφC : ∀ z ∈ L, ‖φ z‖ ≤ C)
    {gn : ℕ → ℂ → ℂ}
    (h0 : Tendsto (fun n => lintegralAbsDbar (gn n) L) atTop (nhds 0)) :
    Tendsto (fun n => ∫ z in L, dzbar (gn n) z * φ z) atTop (nhds 0) := by
  have hLm : MeasurableSet L := hL.isClosed.measurableSet
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero'
    (g := fun n => C * (lintegralAbsDbar (gn n) L).toReal)
    (Eventually.of_forall fun n => norm_nonneg (∫ z in L, dzbar (gn n) z * φ z)) ?_ ?_
  · filter_upwards [h0.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ≥0∞) < 1))]
      with n hn
    have hne : lintegralAbsDbar (gn n) L ≠ ⊤ := ne_top_of_lt hn
    have h1 : ‖∫ z in L, dzbar (gn n) z * φ z‖
        ≤ (∫⁻ z in L, ENNReal.ofReal ‖dzbar (gn n) z * φ z‖).toReal := by
      simpa using (norm_integral_le_lintegral_norm (μ := (volume : Measure ℂ).restrict L)
        (fun z => dzbar (gn n) z * φ z))
    have h2 : (∫⁻ z in L, ENNReal.ofReal ‖dzbar (gn n) z * φ z‖)
        ≤ ENNReal.ofReal C * lintegralAbsDbar (gn n) L := by
      calc ∫⁻ z in L, ENNReal.ofReal ‖dzbar (gn n) z * φ z‖
          ≤ ∫⁻ z in L, ENNReal.ofReal (C * ‖dzbar (gn n) z‖) := by
            refine lintegral_mono_ae ?_
            rw [ae_restrict_iff' hLm]
            exact Eventually.of_forall fun z hz => ENNReal.ofReal_le_ofReal (by
              rw [norm_mul, mul_comm (‖dzbar (gn n) z‖)]
              exact mul_le_mul_of_nonneg_right (hφC z hz) (norm_nonneg (dzbar (gn n) z)))
        _ = ENNReal.ofReal C * lintegralAbsDbar (gn n) L := by
            rw [lintegral_congr fun z => ENNReal.ofReal_mul hC]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            rfl
    calc ‖∫ z in L, dzbar (gn n) z * φ z‖
        ≤ (∫⁻ z in L, ENNReal.ofReal ‖dzbar (gn n) z * φ z‖).toReal := h1
      _ ≤ (ENNReal.ofReal C * lintegralAbsDbar (gn n) L).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hne) h2
      _ = C * (lintegralAbsDbar (gn n) L).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]
  · simpa using (tendsto_toReal_of_tendsto_nhds_zero_aux h0).const_mul C

/-- Uniform convergence on a compact set passes to the integrals against a function `ψ` whose
support lies in that compact set. -/
theorem tendsto_integral_sub_mul_of_tendstoUniformlyOn_aux {F : ℕ → ℂ → ℂ} {f ψ : ℂ → ℂ}
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

/-! ## The main theorem -/

theorem differentiableOn_of_tendstoLocallyUniformly_of_lintegral_tendsto {V : Set ℂ} (hV : IsOpen V)
    {G : ℂ → ℂ} {Gn : ℕ → ℂ → ℂ} (hGn : ∀ n, LocallyLipschitzOn V (Gn n))
    (hconv : TendstoLocallyUniformly Gn G Filter.atTop)
    (h0 : ∀ L : Set ℂ, IsCompact L → L ⊆ V →
      Filter.Tendsto (fun n => lintegralAbsDbar (Gn n) L) Filter.atTop (nhds 0)) :
    DifferentiableOn ℂ G V := by
  -- a locally uniform limit of functions continuous on `V` is continuous on `V`
  have hGcont : ContinuousOn G V :=
    (hconv.tendstoLocallyUniformlyOn (s := V)).continuousOn
      ((Eventually.of_forall fun n => (hGn n).continuousOn).frequently)
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
      (tendstoLocallyUniformly_iff_forall_isCompact.mp hconv) K hK
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
