import Submission.IndexForm
import Submission.ChartCurvCont

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second variation of the energy

This file continues `Submission/IndexForm.lean`.  There we proved the **first variation** of the
energy of the straight-line variation `Ψ(s,t) = u t + s • η t`:
`E'(s) = -2 ∫_0^L ⟪η, ∇_t T⟫ dt`.  Here we differentiate once more to obtain the **second
variation** and the **index form**.

## Contents

* `continuousOn_dB_comp`: joint continuity of `dB` composed with continuous data (an ingredient
  of the continuity of the second-variation integrand);
* `continuousOn_famK'`: joint continuity of `famK'` (the `s`-derivative of the first-variation
  integrand);
* `famK_hasDerivAt`: differentiation of `∫_0^L famK(s,t) dt` in `s`, hence the second derivative of
  the energy;
* `famEnergyDeriv` and `famEnergy_second_deriv`: the second derivative of the energy at `s₀`.
-/

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory
open Submission.Geodesic
open Submission.Jacobi
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.ChartCurvCont
open Submission.CurvatureVec
open Submission.SecondVariation
open Submission.ChartBounds
open Submission.Distance
open Submission.IndexForm
open Commons.Geometry.Manifold.VectorBundle.CovariantDerivative
open Commons.Geometry.Manifold.Tangent

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace Submission.IndexForm2

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

noncomputable section

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-- **Joint continuity of `dB` composed with continuous data.** -/
lemma continuousOn_dB_comp [ContMDiffCovariantDerivative cov ∞] {x₀ : M} {A B : Set ℝ}
    {c : ℝ × ℝ → M} {V Aa Bb : ℝ × ℝ → E}
    (hc : ContinuousOn c (A ×ˢ B)) (hV : ContinuousOn V (A ×ˢ B))
    (hA : ContinuousOn Aa (A ×ˢ B)) (hB : ContinuousOn Bb (A ×ˢ B))
    (hmem : ∀ q ∈ A ×ˢ B, c q ∈ (chartAt H x₀).source) :
    ContinuousOn (fun q : ℝ × ℝ => dB cov x₀ (c q) (V q) (Aa q) (Bb q)) (A ×ˢ B) := by
  rw [show (fun q : ℝ × ℝ => dB cov x₀ (c q) (V q) (Aa q) (Bb q))
      = (fun q' : M × E × E × E => dB cov x₀ q'.1 q'.2.1 q'.2.2.1 q'.2.2.2)
        ∘ fun q : ℝ × ℝ => (c q, V q, Aa q, Bb q) from rfl]
  exact (continuousOn_dB_prod (cov := cov) (I := I) x₀).comp'
    (hc.prodMk (hV.prodMk (hA.prodMk hB))) (fun q hq => ⟨hmem q hq, trivial⟩)

/-- **Joint continuity of `famK'`** (the `s`-derivative of the first-variation integrand)
on a rectangle where the family stays in the chart. -/
lemma continuousOn_famK' [ContMDiffCovariantDerivative cov ∞] {x₀ : M}
    {u η w e w' e' : ℝ → E} {A B : Set ℝ}
    (hu : ContinuousOn u B) (hη : ContinuousOn η B) (hw : ContinuousOn w B)
    (he : ContinuousOn e B) (hw' : ContinuousOn w' B) (he' : ContinuousOn e' B)
    (hmem : ∀ q ∈ A ×ˢ B, fam u η q.1 q.2 ∈ (extChartAt I x₀).target)
    (hmsrc : ∀ q ∈ A ×ˢ B,
      famCurve (I := I) x₀ u η q.1 q.2 ∈ (chartAt H x₀).source) :
    ContinuousOn (fun q : ℝ × ℝ => famK' cov x₀ u η w e w' e' q.1 q.2) (A ×ˢ B) := by
  have hc := continuousOn_famCurve_prod (x₀ := x₀) hu hη hmem
  have hη' : ContinuousOn (fun q : ℝ × ℝ => η q.2) (A ×ˢ B) :=
    hη.comp' continuousOn_snd (fun q hq => hq.2)
  have he'c : ContinuousOn (fun q : ℝ × ℝ => e q.2) (A ×ˢ B) :=
    he.comp' continuousOn_snd (fun q hq => hq.2)
  have he'c' : ContinuousOn (fun q : ℝ × ℝ => e' q.2) (A ×ˢ B) :=
    he'.comp' continuousOn_snd (fun q hq => hq.2)
  have hP := continuousOn_famP_prod (A := A) (B := B) hw he
  have hD := continuousOn_covDtP (cov := cov) (x₀ := x₀) hu hη hw he hw' he' hmem hmsrc
  have h1 : ContinuousOn (fun q : ℝ × ℝ =>
      chartGram (I := I) x₀ (famCurve (I := I) x₀ u η q.1 q.2)
        (chrB cov x₀ (famCurve (I := I) x₀ u η q.1 q.2) (η q.2) (η q.2))
        (covDtP cov x₀ u η w e w' e' q.1 q.2)) (A ×ˢ B) :=
    continuousOn_chartGram_comp (x₀ := x₀) hc
      (continuousOn_chrB_comp (cov := cov) (x₀ := x₀) hc hη' hη' hmsrc) hD hmsrc
  have hdb : ContinuousOn (fun q : ℝ × ℝ => dB cov x₀ (famCurve (I := I) x₀ u η q.1 q.2)
      (η q.2) (famP w e q.1 q.2) (famP w e q.1 q.2)) (A ×ˢ B) :=
    continuousOn_dB_comp (cov := cov) (x₀ := x₀) hc hη' hP hP hmsrc
  have hc1 : ContinuousOn (fun q : ℝ × ℝ => chrB cov x₀ (famCurve (I := I) x₀ u η q.1 q.2)
      (e q.2) (famP w e q.1 q.2)) (A ×ˢ B) :=
    continuousOn_chrB_comp (cov := cov) (x₀ := x₀) hc he'c hP hmsrc
  have hc2 : ContinuousOn (fun q : ℝ × ℝ => chrB cov x₀ (famCurve (I := I) x₀ u η q.1 q.2)
      (famP w e q.1 q.2) (e q.2)) (A ×ˢ B) :=
    continuousOn_chrB_comp (cov := cov) (x₀ := x₀) hc hP he'c hmsrc
  have hc3 : ContinuousOn (fun q : ℝ × ℝ => chrB cov x₀ (famCurve (I := I) x₀ u η q.1 q.2)
      (covDtP cov x₀ u η w e w' e' q.1 q.2) (η q.2)) (A ×ˢ B) :=
    continuousOn_chrB_comp (cov := cov) (x₀ := x₀) hc hD hη' hmsrc
  have hbody : ContinuousOn (fun q : ℝ × ℝ =>
      e' q.2 + (dB cov x₀ (famCurve (I := I) x₀ u η q.1 q.2) (η q.2)
          (famP w e q.1 q.2) (famP w e q.1 q.2)
        + chrB cov x₀ (famCurve (I := I) x₀ u η q.1 q.2) (e q.2) (famP w e q.1 q.2)
        + chrB cov x₀ (famCurve (I := I) x₀ u η q.1 q.2) (famP w e q.1 q.2) (e q.2))
        + chrB cov x₀ (famCurve (I := I) x₀ u η q.1 q.2)
            (covDtP cov x₀ u η w e w' e' q.1 q.2) (η q.2)) (A ×ˢ B) :=
    (he'c'.add ((hdb.add hc1).add hc2)).add hc3
  have h2 : ContinuousOn (fun q : ℝ × ℝ =>
      chartGram (I := I) x₀ (famCurve (I := I) x₀ u η q.1 q.2) (η q.2)
        (e' q.2 + (dB cov x₀ (famCurve (I := I) x₀ u η q.1 q.2) (η q.2)
            (famP w e q.1 q.2) (famP w e q.1 q.2)
          + chrB cov x₀ (famCurve (I := I) x₀ u η q.1 q.2) (e q.2) (famP w e q.1 q.2)
          + chrB cov x₀ (famCurve (I := I) x₀ u η q.1 q.2) (famP w e q.1 q.2) (e q.2))
          + chrB cov x₀ (famCurve (I := I) x₀ u η q.1 q.2)
              (covDtP cov x₀ u η w e w' e' q.1 q.2) (η q.2))) (A ×ˢ B) :=
    continuousOn_chartGram_comp (x₀ := x₀) hc hη' hbody hmsrc
  have hfun : (fun q : ℝ × ℝ => famK' cov x₀ u η w e w' e' q.1 q.2)
      = fun q : ℝ × ℝ =>
          (chartGram (I := I) x₀ (famCurve (I := I) x₀ u η q.1 q.2)
              (chrB cov x₀ (famCurve (I := I) x₀ u η q.1 q.2) (η q.2) (η q.2))
              (covDtP cov x₀ u η w e w' e' q.1 q.2)
            + chartGram (I := I) x₀ (famCurve (I := I) x₀ u η q.1 q.2) (η q.2)
              (e' q.2 + (dB cov x₀ (famCurve (I := I) x₀ u η q.1 q.2) (η q.2)
                  (famP w e q.1 q.2) (famP w e q.1 q.2)
                + chrB cov x₀ (famCurve (I := I) x₀ u η q.1 q.2) (e q.2) (famP w e q.1 q.2)
                + chrB cov x₀ (famCurve (I := I) x₀ u η q.1 q.2) (famP w e q.1 q.2) (e q.2))
                + chrB cov x₀ (famCurve (I := I) x₀ u η q.1 q.2)
                    (covDtP cov x₀ u η w e w' e' q.1 q.2) (η q.2))) := by
    funext q
    rw [famK']
  rw [hfun]
  exact h1.add h2

/-- **Differentiation in `s` of `∫_0^L famK(s,t) dt`** — the second differentiation of the energy
of the straight-line variation. -/
theorem famK_hasDerivAt [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (x₀ : M)
    {L : ℝ} (hL : 0 ≤ L) {u η w e w' e' : ℝ → E}
    {a₁ a₂ δ₁ δ₂ s₀ : ℝ} (ha₁ : a₁ < δ₁) (ha₂ : δ₂ < a₂)
    (h₁ : δ₁ < s₀) (h₂ : s₀ < δ₂)
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t) (he : ∀ t ∈ Icc 0 L, HasDerivAt e (e' t) t)
    (hwc : ContinuousOn w' (Icc 0 L)) (hec : ContinuousOn e' (Icc 0 L))
    (hstay : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (-1) (L+2),
      fam u η s t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun s => ∫ t in (0 : ℝ)..L, famK cov x₀ u η w e w' e' s t)
      (∫ t in (0 : ℝ)..L, famK' cov x₀ u η w e w' e' s₀ t) s₀ := by
  have huC : ContinuousOn u (Icc 0 L) := HasDerivAt.continuousOn hu
  have hwC : ContinuousOn w (Icc 0 L) := HasDerivAt.continuousOn hw
  have hηC : ContinuousOn η (Icc 0 L) := HasDerivAt.continuousOn hη
  have heC : ContinuousOn e (Icc 0 L) := HasDerivAt.continuousOn he
  have ht_sub : Icc (0 : ℝ) L ⊆ Icc (-1 : ℝ) (L+2) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsubs : Icc δ₁ δ₂ ⊆ Icc a₁ a₂ := Icc_subset_Icc ha₁.le ha₂.le
  have hs_mem : ∀ q ∈ Icc δ₁ δ₂ ×ˢ Icc 0 L,
      fam u η q.1 q.2 ∈ (extChartAt I x₀).target :=
    fun q hq => hstay q.1 (hsubs hq.1) q.2 (ht_sub hq.2)
  have hs_nhds : ∀ {s : ℝ}, a₁ < s → s < a₂ →
      ∀ t ∈ Icc 0 L, ∀ᶠ s' in 𝓝 s, fam u η s' t ∈ (extChartAt I x₀).target :=
    fun hs₁ hs₂ t ht => Filter.mem_of_superset (Icc_mem_nhds hs₁ hs₂)
      (fun s' hs' => hstay s' hs' t (ht_sub ht))
  have hs₀I : s₀ ∈ Icc δ₁ δ₂ := ⟨le_of_lt h₁, le_of_lt h₂⟩
  let K : ℝ → ℝ → ℝ := fun s t => famK cov x₀ u η w e w' e' s t
  let K' : ℝ → ℝ → ℝ := fun s t => famK' cov x₀ u η w e w' e' s t
  have hsrc : ∀ q ∈ Icc δ₁ δ₂ ×ˢ Icc 0 L,
      famCurve (I := I) x₀ u η q.1 q.2 ∈ (chartAt H x₀).source :=
    fun q hq => mem_source_chartCurve (I := I) (x₀ := x₀) (hs_mem q hq)
  have hKcont_ : ContinuousOn (fun q : ℝ × ℝ => famK cov x₀ u η w e w' e' q.1 q.2)
      (Icc δ₁ δ₂ ×ˢ Icc 0 L) :=
    continuousOn_famK (cov := cov) (x₀ := x₀) huC hηC hwC heC hwc hec hs_mem hsrc
  have hK'cont_ : ContinuousOn (fun q : ℝ × ℝ => famK' cov x₀ u η w e w' e' q.1 q.2)
      (Icc δ₁ δ₂ ×ˢ Icc 0 L) :=
    continuousOn_famK' (cov := cov) (x₀ := x₀) huC hηC hwC heC hwc hec hs_mem hsrc
  have hKcont : ContinuousOn (fun q : ℝ × ℝ => K q.1 q.2) (Icc δ₁ δ₂ ×ˢ uIcc 0 L) := by
    rw [Set.uIcc_of_le hL]; exact hKcont_
  have hK'cont : ContinuousOn (fun q : ℝ × ℝ => K' q.1 q.2) (Icc δ₁ δ₂ ×ˢ uIcc 0 L) := by
    rw [Set.uIcc_of_le hL]; exact hK'cont_
  have hderiv : ∀ s ∈ Icc δ₁ δ₂, ∀ t ∈ uIcc 0 L,
      HasDerivAt (fun s' : ℝ => K s' t) (K' s t) s := by
    intro s hs t ht
    have htI : t ∈ Icc 0 L := by rw [Set.uIcc_of_le hL] at ht; exact ht
    have hs₁ : a₁ < s := lt_of_lt_of_le ha₁ hs.1
    have hs₂ : s < a₂ := lt_of_le_of_lt hs.2 ha₂
    exact hasDerivAt_famK_s (cov := cov) (hmet := hmet) x₀
      (hstay s ⟨hs₁.le, hs₂.le⟩ t (ht_sub htI)) (hs_nhds hs₁ hs₂ t htI)
  exact Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuousOn_uIcc
    (F := K) (F' := K') h₁ h₂ hKcont hK'cont hderiv

/-- The **first derivative of the energy** as an explicit function of `s` (the right-hand side of
the first variation formula). -/
noncomputable def famEnergyDeriv (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (x₀ : M) (u η w e w' e' : ℝ → E) (L s : ℝ) : ℝ :=
  -2 * ∫ t in (0 : ℝ)..L, famK cov x₀ u η w e w' e' s t

/-- **The second derivative of the energy**: `E''(s₀) = -2 ∫_0^L famK'(s₀,t) dt`. -/
theorem famEnergy_second_deriv [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (x₀ : M)
    {L : ℝ} (hL : 0 ≤ L) {u η w e w' e' : ℝ → E}
    {a₁ a₂ δ₁ δ₂ s₀ : ℝ} (ha₁ : a₁ < δ₁) (ha₂ : δ₂ < a₂)
    (h₁ : δ₁ < s₀) (h₂ : s₀ < δ₂)
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t) (he : ∀ t ∈ Icc 0 L, HasDerivAt e (e' t) t)
    (hwc : ContinuousOn w' (Icc 0 L)) (hec : ContinuousOn e' (Icc 0 L))
    (hstay : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (-1) (L+2),
      fam u η s t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun s => famEnergyDeriv cov x₀ u η w e w' e' L s)
      (-2 * ∫ t in (0 : ℝ)..L, famK' cov x₀ u η w e w' e' s₀ t) s₀ :=
  (famK_hasDerivAt (cov := cov) (hmet := hmet) x₀ hL ha₁ ha₂ h₁ h₂ hu hw hη he hwc hec hstay)
    |>.const_mul (-2)

end

end Submission.IndexForm2
