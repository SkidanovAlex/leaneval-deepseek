import Mathlib
import Submission.Work.Wilkies.CG.C4a.Spec
import Submission.Work.WilE7.FrontierCS.analyticOnNhd_jacDet
import Submission.Work.WilE7.FrontierCS.jacDet_ne_zero_iff
import Submission.Work.WilE7.FrontierCS.eventually_ne_of_range_top
import Submission.Work.WilE7.FrontierCS.analyticAt_sqSum_detSq
import Submission.Work.WilE7.FrontierCS.no_arc_nondegenerate_zeros

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.FrontierCS

/-- **N1 (crux).** Nondegenerate zeros of an entire square system do not accumulate at the origin.

Let `S = {e ≠ 0 | g e = 0 and dg(e) is onto}`.  We show `0 ∉ closure S` from curve selection
`CurveSel j` for real-analytic sets in `ℝ^j`.

Suppose `0 ∈ closure S`.  Then `g 0 = 0` (the zero set of `g` is closed).  Two cases:

* `dg(0)` is onto: then `0` is a *nondegenerate* zero, so by the inverse function theorem `g` is
  injective near `0` and `0` is isolated in `{g = 0}` — contradicting `0 ∈ closure S`
  (`eventually_ne_of_range_top`).

* `dg(0)` is not onto: then `0` is not a point of the basic semianalytic set
  `B = {Σ gᵢ² = 0, (jacDet g)² > 0}` (`jacDet_ne_zero_iff`), while `S ⊆ B` and `0 ∈ closure S`,
  so curve selection (`CurveSel j`) applied to `B` produces an analytic arc `γ` with `γ 0 = 0`
  and `γ s ∈ B` for `s ∈ (0,ε)`.  Along that arc `γ s ≠ 0`, `g (γ s) = 0` and `dg(γ s)` is onto
  for every `s ∈ (0,ε)`, which is impossible (`no_arc_nondegenerate_zeros`): such an arc would
  have `g ∘ γ ≡ 0`, hence `0 = (g ∘ γ)'(s) = dg(γ s)(γ'(s))` with `dg(γ s)` injective, forcing
  `γ' ≡ 0`, so `γ` is constant on `(0,ε)` and by continuity equals `γ 0 = 0` there. -/
theorem nondegZeros_not_accum {j : ℕ} (hCS : WilkiesDesign.CG.C4a.CurveSel j)
    {g : (Fin j → ℝ) → (Fin j → ℝ)} (hg : AnalyticOnNhd ℝ g Set.univ) :
    (0 : Fin j → ℝ) ∉ closure {e | e ≠ 0 ∧ g e = 0 ∧ (fderiv ℝ g e).range = ⊤} := by
  intro hmem
  have hg0at : AnalyticAt ℝ g 0 := hg 0 (Set.mem_univ 0)
  have hgcont : Continuous g := continuousOn_univ.mp hg.continuousOn
  -- the origin is a zero of `g`
  have hg0 : g 0 = 0 := by
    have hZ : IsClosed {e : Fin j → ℝ | g e = 0} := isClosed_eq hgcont continuous_const
    have hmem' : (0 : Fin j → ℝ) ∈ closure {e : Fin j → ℝ | g e = 0} :=
      closure_mono (fun e he => he.2.1) hmem
    simpa using hZ.closure_subset hmem'
  by_cases hrank : (fderiv ℝ g 0).range = ⊤
  · -- Case A: `0` is a nondegenerate zero, hence isolated in the zero set.
    obtain ⟨U, hUmem, hUp⟩ :=
      (eventually_nhdsWithin_iff.mp (eventually_ne_of_range_top hg0at hrank)).exists_mem
    obtain ⟨V, hVU, hVopen, h0V⟩ := mem_nhds_iff.mp hUmem
    obtain ⟨e, heV, heS⟩ := (mem_closure_iff_nhds.mp hmem) V (hVopen.mem_nhds h0V)
    exact (hUp e (hVU heV) (by simpa using heS.1)) (by simp [heS.2.1, hg0])
  · -- Case B: `0` is not nondegenerate; curve selection produces an arc avoiding `0`.
    have hdet0 : ((Matrix.of fun (a l : Fin j) => fderiv ℝ g 0 (Pi.single l 1) a).det) = 0 := by
      by_contra h
      exact hrank ((jacDet_ne_zero_iff g 0).mp h)
    set F : (Fin j → ℝ) → ℝ := fun e => ∑ i, (g e i) ^ 2 with hF
    set σ : Fin 1 → (Fin j → ℝ) → ℝ :=
      fun _ e => ((Matrix.of fun (a l : Fin j) => fderiv ℝ g e (Pi.single l 1) a).det) ^ 2 with hσ
    have hσeval : ∀ e : Fin j → ℝ,
        σ 0 e = ((Matrix.of fun (a l : Fin j) => fderiv ℝ g e (Pi.single l 1) a).det) ^ 2 := by
      intro e
      simp only [hσ]
    have hFunif := analyticAt_sqSum_detSq hg
    have hFan : AnalyticAt ℝ F 0 := by rw [hF]; exact hFunif.1
    have hσan : ∀ i : Fin 1, AnalyticAt ℝ (σ i) 0 := by
      intro i
      rw [hσ]
      exact hFunif.2
    -- `0` lies in the closure of the basic semianalytic set of nondegenerate zeros
    have hBmem : (0 : Fin j → ℝ) ∈ closure (WilkiesDesign.CG.C4a.BasicSA F σ) := by
      refine closure_mono ?_ hmem
      intro e he
      refine ⟨?_, ?_⟩
      · rw [hF]
        simp [he.2.1]
      · intro i
        rw [hσ]
        exact sq_pos_of_ne_zero ((jacDet_ne_zero_iff g e).mpr he.2.2)
    obtain ⟨γ, hγan, hγ0, ε, hε, hγmem⟩ := hCS 1 F σ 0 hFan hσan hBmem
    refine no_arc_nondegenerate_zeros hg hγan hγ0 ⟨ε, hε, ?_⟩
    intro s hs
    have hBs : γ s ∈ WilkiesDesign.CG.C4a.BasicSA F σ := hγmem s hs
    have hFs : F (γ s) = 0 := hBs.1
    have hσs : 0 < σ 0 (γ s) := hBs.2 0
    -- the arc avoids the origin, since `0` is not in the basic semianalytic set
    have hγs_ne : γ s ≠ 0 := by
      intro hzero
      have h1 : 0 < σ 0 (0 : Fin j → ℝ) := by simpa [hzero] using hσs
      rw [hσeval] at h1
      rw [hdet0] at h1
      norm_num at h1
    -- and `g` vanishes along the arc
    have hgγ : g (γ s) = 0 := by
      rw [hF] at hFs
      have h2 : ∀ i, (g (γ s) i) ^ 2 = 0 := by
        intro i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (g (γ s) i))).mp hFs i
          (Finset.mem_univ i)
      funext i
      exact (sq_eq_zero_iff.mp (h2 i))
    -- and the differential of `g` is onto there
    have hrk : (fderiv ℝ g (γ s)).range = ⊤ := by
      refine (jacDet_ne_zero_iff g (γ s)).mp ?_
      have hne : σ 0 (γ s) ≠ 0 := ne_of_gt hσs
      rw [hσeval] at hne
      intro h
      exact hne (by rw [h]; norm_num)
    exact ⟨hγs_ne, hgγ, hrk⟩

end Work.WilE7.FrontierCS
