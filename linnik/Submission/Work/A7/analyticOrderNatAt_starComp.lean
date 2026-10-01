import Mathlib

open Filter
open scoped ComplexConjugate Topology

namespace Work.A7

/-- Complex conjugation (as the star ring endomorphism of `ℂ`) preserves analyticity:
`conj ∘ f ∘ conj` is analytic at `z` iff `f` is analytic at `conj z`. -/
private lemma analyticAt_starComp_iff (f : ℂ → ℂ) (z : ℂ) :
    AnalyticAt ℂ (fun s => (starRingEnd ℂ) (f ((starRingEnd ℂ) s))) z ↔
      AnalyticAt ℂ f ((starRingEnd ℂ) z) := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt,
      Complex.analyticAt_iff_eventually_differentiableAt]
  have h1 : (∀ᶠ s in 𝓝 z, DifferentiableAt ℂ (fun s => (starRingEnd ℂ) (f ((starRingEnd ℂ) s))) s)
      ↔ ∀ᶠ s in 𝓝 z, DifferentiableAt ℂ f ((starRingEnd ℂ) s) := by
    apply eventually_congr
    filter_upwards with s
    exact differentiableAt_conj_conj_iff
  rw [h1]
  have hh := Homeomorph.map_nhds_eq ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toHomeomorph) z
  rw [show ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toHomeomorph z) = (starRingEnd ℂ) z by simp] at hh
  rw [← hh, eventually_map]
  simp

/-- Two functions are eventually equal near `c` iff their `conj ∘ · ∘ conj` conjugates are
eventually equal near `conj c`. -/
private lemma eventuallyEq_starComp_iff (f F : ℂ → ℂ) (c : ℂ) :
    Filter.EventuallyEq (nhds ((starRingEnd ℂ) c))
        (fun s => (starRingEnd ℂ) (f ((starRingEnd ℂ) s)))
        (fun s => (starRingEnd ℂ) (F ((starRingEnd ℂ) s)))
      ↔ Filter.EventuallyEq (nhds c) f F := by
  constructor
  · intro h
    have hT : Tendsto (starRingEnd ℂ) (𝓝 c) (𝓝 ((starRingEnd ℂ) c)) :=
      Complex.continuous_conj.continuousAt.tendsto
    have h2 := h.comp_tendsto hT
    filter_upwards [h2] with t ht
    rw [Function.comp_apply, Function.comp_apply] at ht
    exact star_inj.mp (by simpa using ht)
  · intro h
    have hT : Tendsto (starRingEnd ℂ) (𝓝 ((starRingEnd ℂ) c)) (𝓝 c) := by
      simpa using (Complex.continuous_conj.continuousAt (x := (starRingEnd ℂ) c)).tendsto
    have h1 := h.comp_tendsto hT
    simpa [Function.comp_def] using h1.fun_comp (starRingEnd ℂ)

/-- Analyticity version of `conj ∘ · ∘ conj`, at the conjugated point. -/
private lemma analyticAt_starComp_iff' (G : ℂ → ℂ) (z : ℂ) :
    AnalyticAt ℂ (fun s => (starRingEnd ℂ) (G ((starRingEnd ℂ) s))) ((starRingEnd ℂ) z) ↔
      AnalyticAt ℂ G z := by
  have h := analyticAt_starComp_iff G ((starRingEnd ℂ) z)
  rw [show (starRingEnd ℂ) ((starRingEnd ℂ) z) = z from Complex.conj_conj z] at h
  exact h

/-- Eventually-equal version of `conj ∘ · ∘ conj`, at the conjugated point. -/
private lemma eventuallyEq_starComp_iff' (f F : ℂ → ℂ) (z : ℂ) :
    Filter.EventuallyEq (nhds z) (fun s => (starRingEnd ℂ) (f ((starRingEnd ℂ) s)))
        (fun s => (starRingEnd ℂ) (F ((starRingEnd ℂ) s)))
      ↔ Filter.EventuallyEq (nhds ((starRingEnd ℂ) z)) f F := by
  have h := eventuallyEq_starComp_iff f F ((starRingEnd ℂ) z)
  rw [show (starRingEnd ℂ) ((starRingEnd ℂ) z) = z from Complex.conj_conj z] at h
  exact h

/-- Conjugation is an order-preserving involution on the vanishing order of analytic functions. -/
private lemma analyticOrderAt_starComp (f : ℂ → ℂ) (z : ℂ) :
    analyticOrderAt (fun s => (starRingEnd ℂ) (f ((starRingEnd ℂ) s))) z
      = analyticOrderAt f ((starRingEnd ℂ) z) := by
  refine ENat.eq_of_forall_natCast_le_iff (fun n => ?_)
  by_cases hf : AnalyticAt ℂ f ((starRingEnd ℂ) z)
  · have hg : AnalyticAt ℂ (fun s => (starRingEnd ℂ) (f ((starRingEnd ℂ) s))) z :=
      (analyticAt_starComp_iff f z).mpr hf
    rw [natCast_le_analyticOrderAt hg, natCast_le_analyticOrderAt hf]
    constructor
    · rintro ⟨G, hGa, hGeq⟩
      refine ⟨fun t => (starRingEnd ℂ) (G ((starRingEnd ℂ) t)),
        (analyticAt_starComp_iff' G z).mpr hGa, ?_⟩
      refine (eventuallyEq_starComp_iff' f
        (fun t => (t - (starRingEnd ℂ) z) ^ n • (starRingEnd ℂ) (G ((starRingEnd ℂ) t))) z).mp ?_
      filter_upwards [hGeq] with s hs
      rw [hs]
      simp [map_mul, map_pow, map_sub]
    · rintro ⟨H, hHa, hHeq⟩
      refine ⟨fun s => (starRingEnd ℂ) (H ((starRingEnd ℂ) s)),
        (analyticAt_starComp_iff H z).mpr hHa, ?_⟩
      have hHeq' : Filter.EventuallyEq (nhds ((starRingEnd ℂ) z)) f
          (fun t => (t - (starRingEnd ℂ) z) ^ n • H t) := hHeq
      filter_upwards [hHeq'.comp_tendsto
        (Complex.continuous_conj.continuousAt (x := z)).tendsto] with s hs
      rw [Function.comp_apply, Function.comp_apply] at hs
      rw [hs]
      simp [map_mul, map_pow, map_sub]
  · have hg : ¬ AnalyticAt ℂ (fun s => (starRingEnd ℂ) (f ((starRingEnd ℂ) s))) z :=
      fun h => hf ((analyticAt_starComp_iff f z).mp h)
    rw [analyticOrderAt_of_not_analyticAt hg, analyticOrderAt_of_not_analyticAt hf]

theorem analyticOrderNatAt_starComp (f : ℂ → ℂ) (z : ℂ) :
    analyticOrderNatAt (fun s => (starRingEnd ℂ) (f ((starRingEnd ℂ) s))) z
      = analyticOrderNatAt f ((starRingEnd ℂ) z) := by
  simp only [analyticOrderNatAt, analyticOrderAt_starComp]

end Work.A7
