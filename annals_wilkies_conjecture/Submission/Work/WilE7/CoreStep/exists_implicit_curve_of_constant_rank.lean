import Mathlib
import Submission.Work.WilE7.Auxiliary.analyticLevelSetChart
import Submission.Work.WilE7.DimAPI.exists_coordProj_surj_of_le_finrank
import Submission.Work.WilE9G.Sard.analyticLevelSetChartLocal
import Submission.Work.WilE7.DimAPI.criticalLevelSetLocallyConstAt
import Submission.Work.WilE7.DimAPI.eventually_ker_comp_fderiv_eq
import Submission.Work.WilE7.DimAPI.coordProj_fderiv_ker_eventually
import Submission.Work.WilE7.DimAPI.fderiv_gamma_mem_ker
import Submission.Work.WilE7.CoreStep.eventually_eq_zero_of_proj_eq_zero
import Submission.Work.WilE7.CoreStep.fderiv_chart_eq_self

namespace Work.WilE7.CoreStep

open Filter
open scoped Topology

/-- **Implicit curve of a constant-rank analytic map.**

Let `ψ : ℝ^q → ℝⁿ` be analytic on a neighbourhood `W` of the origin, with `ψ 0 = 0` and with
`fderiv ψ w` of constant rank `q - 1` for all `w ∈ W`.  Then every vector `v` in the kernel of
`fderiv ψ 0` is the velocity at the origin of a curve lying in the zero set of `ψ`.

The proof reduces `ψ` to a submersion `G = π ∘ ψ`, where `π : ℝⁿ → ℝ^{q-1}` is a linear
projection that is injective on the range of `fderiv ψ 0` (which has dimension `q - 1`); such a
`π` exists by `exists_coordProj_surj_of_le_finrank`.  The rank hypothesis guarantees that on a
neighbourhood of the origin `ker (fderiv G y) = ker (fderiv ψ y)`, so the vanishing of `G`
forces the vanishing of `ψ` (this is `eventually_eq_zero_of_proj_eq_zero`).  The level set
`{G = 0}` is, near `0`, the image of an analytic chart `γ` of the submersion `G`
(`analyticLevelSetChartLocal`), and the differential of `γ` at `0` is the inclusion of
`ker (fderiv G 0)` (`fderiv_chart_eq_self`).  Hence `c t := γ (t • v)` is the required curve. -/
theorem exists_implicit_curve_of_constant_rank {q n : ℕ} (hq : 1 ≤ q)
    (ψ : (Fin q → ℝ) → (Fin n → ℝ)) (W : Set (Fin q → ℝ)) (hW : W ∈ nhds (0 : Fin q → ℝ))
    (hψ : ∀ w ∈ W, AnalyticAt ℝ ψ w)
    (hrank : ∀ w ∈ W, Module.finrank ℝ (fderiv ℝ ψ w).range = q - 1)
    (h0 : ψ 0 = 0) (v : Fin q → ℝ) (hv : fderiv ℝ ψ 0 v = 0) :
    ∃ c : ℝ → (Fin q → ℝ), c 0 = 0 ∧ HasDerivAt c v 0 ∧
      ∀ᶠ t in nhds (0 : ℝ), ψ (c t) = 0 := by
  have h0W : (0 : Fin q → ℝ) ∈ W := mem_of_mem_nhds hW
  have hrank0 : Module.finrank ℝ (fderiv ℝ ψ 0).range = q - 1 := hrank 0 h0W
  by_cases hv0 : v = 0
  · -- The degenerate case: the constant curve at the origin.
    refine ⟨fun _ => 0, rfl, ?_, ?_⟩
    · subst hv0
      simpa using (hasDerivAt_const (0 : ℝ) (0 : Fin q → ℝ))
    · filter_upwards with t
      simpa using h0
  · -- A coordinate projection `π : ℝⁿ → ℝ^{q-1}` injective on `range (fderiv ψ 0)`.
    obtain ⟨e, he⟩ := Work.WilE7.DimAPI.exists_coordProj_surj_of_le_finrank
      (M := q) (n := n) (m := q - 1) (fderiv ℝ ψ 0).toLinearMap (by rw [hrank0])
    set π : (Fin n → ℝ) →L[ℝ] (Fin (q - 1) → ℝ) := Work.WilE7.DimAPI.coordProjCLM e with hπdef
    have hπ_surj : Function.Surjective fun w : Fin q → ℝ => π ((fderiv ℝ ψ 0) w) := by
      intro y
      obtain ⟨w, hw⟩ := he y
      refine ⟨w, ?_⟩
      funext i
      simp only [Work.WilE7.DimAPI.coordProjCLM_apply]
      exact congrFun hw i
    have hπ_surj' : Function.Surjective ⇑(π.comp (fderiv ℝ ψ 0)) := hπ_surj
    -- The submersion `G = π ∘ ψ`.
    set G : (Fin q → ℝ) → (Fin (q - 1) → ℝ) := fun y => π (ψ y) with hGdef
    have hG_an : AnalyticAt ℝ G 0 := by
      have h := (π.analyticAt (ψ 0)).comp (hψ 0 h0W)
      simpa only [hGdef, Function.comp_def] using h
    have hG0 : G 0 = 0 := by simp [hGdef, h0]
    have hfdG0 : fderiv ℝ G 0 = π.comp (fderiv ℝ ψ 0) := by
      have hd : DifferentiableAt ℝ ψ 0 := (hψ 0 h0W).differentiableAt
      have h := (π.hasFDerivAt (x := ψ 0)).comp 0 hd.hasFDerivAt
      simpa only [hGdef, Function.comp_def] using h.fderiv
    have hGsurj : (fderiv ℝ G 0).range = ⊤ := by
      rw [hfdG0]
      exact LinearMap.range_eq_top.mpr hπ_surj'
    -- The analytic chart of the level set `{G = 0}` through the origin.
    obtain ⟨C, γ, V, U, hCid, hVopen, hUopen, h0V, hpU, hγ0, hγan, hγU, hGγ, hCγ, hγC⟩ :=
      Work.WilE9G.Sard.analyticLevelSetChartLocal G 0 hG_an hGsurj
    have hCγ' : ∀ v ∈ V, C (γ v) = v := by
      intro w hw
      simpa using hCγ w hw
    -- Vanishing of `G` forces vanishing of `ψ` near the origin.
    have hzero : ∀ᶠ y in nhds (0 : Fin q → ℝ), G y = 0 → ψ y = 0 := by
      have h := Work.WilE7.CoreStep.eventually_eq_zero_of_proj_eq_zero hq ψ W hW hψ hrank h0 π
        hπ_surj
      simpa only [hGdef] using h
    -- The curve `c t = γ (t • v)`.
    have hvker : (fderiv ℝ G 0) v = 0 := by
      rw [hfdG0, ContinuousLinearMap.comp_apply, hv, map_zero]
    let vker : (fderiv ℝ G 0).ker := ⟨v, LinearMap.mem_ker.mpr hvker⟩
    let c : ℝ → (Fin q → ℝ) := fun t => γ (t • vker)
    have hfd_γ : ∀ u : (fderiv ℝ G 0).ker, (fderiv ℝ γ 0) u = (u : Fin q → ℝ) :=
      Work.WilE7.CoreStep.fderiv_chart_eq_self G C γ V hG_an hγ0 hγan hCid hVopen h0V hGγ hCγ'
    have hderiv_γ : (fderiv ℝ γ 0) vker = v := by
      simpa only [vker] using hfd_γ vker
    refine ⟨c, ?_, ?_, ?_⟩
    · show γ (0 • vker) = 0
      rw [zero_smul, hγ0]
    · have hs : HasDerivAt (fun t : ℝ => t • vker) vker 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const vker
      have hγfd : HasFDerivAt γ (fderiv ℝ γ 0) ((0 : ℝ) • vker) := by
        simpa using hγan.differentiableAt.hasFDerivAt
      have hcomp := hγfd.comp_hasDerivAt 0 hs
      rw [hderiv_γ] at hcomp
      simpa only [c, Function.comp_def] using hcomp
    · have hcont : Continuous fun t : ℝ => t • vker := continuous_id.smul continuous_const
      have htend : Tendsto (fun t : ℝ => t • vker) (nhds 0)
          (nhds (0 : (fderiv ℝ G 0).ker)) := by
        have h := hcont.continuousAt (x := (0 : ℝ))
        simpa using h.tendsto
      have hVe : ∀ᶠ t in nhds (0 : ℝ), t • vker ∈ V :=
        htend.eventually (hVopen.mem_nhds h0V)
      have hγtend : Tendsto (fun t : ℝ => γ (t • vker)) (nhds 0) (nhds (0 : Fin q → ℝ)) := by
        have h2 : Tendsto γ (nhds (0 : (fderiv ℝ G 0).ker)) (nhds (0 : Fin q → ℝ)) := by
          have h := hγan.continuousAt.tendsto
          rwa [hγ0] at h
        exact h2.comp htend
      filter_upwards [hVe, hγtend.eventually hzero] with t htV ht0
      have hGt : G (γ (t • vker)) = 0 := by
        simpa only [hG0] using hGγ (t • vker) htV
      exact ht0 hGt

end Work.WilE7.CoreStep
