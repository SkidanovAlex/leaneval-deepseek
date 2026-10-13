import Mathlib
import Submission.Work.WilE7.CoreStep.FibreEndDefs
import Submission.Work.WilE7.DecompDefs
import Submission.Work.WilE7.DimAPI.range_fderiv_good_eq_top
import Submission.Work.WilE7.DimAPI.jac_eq_fderiv
import Submission.Work.WilE7.DimAPI.ProjRankAux
import Submission.Work.WilE7.Dim.image_mem_nhds_of_surj_fderiv
import Submission.Work.WilE9.Ift.AppendCLM

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.CoreStep

open WilkiesDesign WilkiesDesign.E

/-- The `(n, m)` composite `π_{n+1} ∘ absPt` as a continuous linear map. -/
def topPrLin (n m : ℕ) :
    (Fin (0 + (n + (m + 1))) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ((projTopLin n m).comp (absPtLin (n + (m + 1)))).toContinuousLinearMap

@[simp] theorem topPrLin_apply (n m : ℕ) (w : Fin (0 + (n + (m + 1))) → ℝ) :
    topPrLin n m w = projTop n m (Work.WilE7.MainDesign.absPt w) := by
  show ((projTopLin n m).comp (absPtLin (n + (m + 1)))) w
    = projTop n m (Work.WilE7.MainDesign.absPt w)
  rw [LinearMap.comp_apply, absPtLin_apply, projTopLin_apply]

/-- **A `Good` absolute stratum whose `π_{n+1}`-tangential rank is maximal is a local submersion
for `π_{n+1}`.**

At a point `z` of a `Good` stratum `T : Stratum 0 (n + (m+1))` where the composite of the tangent
space `ker (jac T z)` with `π_{n+1} ∘ absPt` is all of `ℝ^{n+1}`, the projection `π_{n+1}` maps
`absSet T` onto a neighbourhood of `π_{n+1}(absPt z)`.

The proof is the usual open-mapping argument.  The defining-equation map `G w = (a ↦ h_a(w))` of
`T` is analytic at `z`, `G z = 0` and `fderiv ℝ G z` is onto (`Stratum.Good`); the map
`Φ w = append (G w) (A w - A z)` with `A = π_{n+1} ∘ absPt` therefore has analytic germ at `z` and
surjective differential there: the first component accounts for the `G`-directions, and the second
for the `(n+1)` directions of `ker (jac T z)` supplied by the hypothesis.  Hence `Φ` is open at `z`
(`Work.WilE7.Dim.image_mem_nhds_of_surj_fderiv`), so every small `v` is `A w` for some `w` near `z`
with `G w = 0`; `Stratum.Good` upgrades `G w = 0` to `w ∈ T.X.set`, and `A w = π_{n+1}(absPt w)`. -/
theorem locSubmersion_of_finrank {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : T.Good) {z : Fin (0 + (n + (m + 1))) → ℝ} (hz : z ∈ T.X.set)
    (hfull : Module.finrank ℝ
      ((LinearMap.ker (Work.WilE7.MainDesign.jac T z)).map
        ((Work.WilE7.CoreStep.projTopLin n m).comp (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))))
      = n + 1) :
    ∃ U ∈ nhds (Work.WilE7.CoreStep.projTop n m (Work.WilE7.MainDesign.absPt z)),
      U ⊆ Work.WilE7.CoreStep.projTop n m '' Work.WilE7.MainDesign.absSet T := by
  classical
  -- ## Setup
  let G : (Fin (0 + (n + (m + 1))) → ℝ) → (Fin T.j → ℝ) :=
    fun w a => eaEval T.X.c (T.h a) w
  let L : (Fin (0 + (n + (m + 1))) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
    (projTopLin n m).comp (absPtLin (n + (m + 1)))
  let A : (Fin (0 + (n + (m + 1))) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) := L.toContinuousLinearMap
  have hA_apply : ∀ w, A w = projTop n m (Work.WilE7.MainDesign.absPt w) :=
    fun w => topPrLin_apply n m w
  -- ## Basic properties of `G`
  have hGan : ∀ w, AnalyticAt ℝ G w :=
    fun w => AnalyticAt.pi (fun a => Work.WilE5.Strat.analyticAt_eaEval T.X.c (T.h a) w)
  have hGz : G z = 0 := funext fun a => Work.WilE5.Stratum.good_eqs hT hz a
  have hGtop : (fderiv ℝ G z).range = ⊤ :=
    Work.WilE7.DimAPI.range_fderiv_good_eq_top T hT hz
  let J : (Fin (0 + (n + (m + 1))) → ℝ) →ₗ[ℝ] (Fin T.j → ℝ) :=
    (fderiv ℝ G z : (Fin (0 + (n + (m + 1))) → ℝ) →L[ℝ] (Fin T.j → ℝ))
  have hjac : ((Work.WilE7.MainDesign.jac T z :
        (Fin (0 + (n + (m + 1))) → ℝ) →ₗ[ℝ] (Fin T.j → ℝ))) = J := by
    show (Work.WilE7.MainDesign.jac T z : (Fin (0 + (n + (m + 1))) → ℝ) →ₗ[ℝ] (Fin T.j → ℝ))
      = ↑(fderiv ℝ G z)
    exact Work.WilE7.DimAPI.jac_eq_fderiv T z
  have hkerEq : LinearMap.ker (Work.WilE7.MainDesign.jac T z)
      = LinearMap.ker J := by
    rw [hjac]
  -- ## The kernel condition
  have hkerL : (LinearMap.ker (Work.WilE7.MainDesign.jac T z)).map L = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [hfull, Module.finrank_fin_fun]
  -- ## `Φ = append (G ·) (A · - A z)`
  let Φ : (Fin (0 + (n + (m + 1))) → ℝ) → (Fin (T.j + (n + 1)) → ℝ) :=
    fun w => Work.WilE9.Ift.appendCLM T.j (n + 1) (G w, A w - A z)
  have hΦz : Φ z = 0 := by
    show Work.WilE9.Ift.appendCLM T.j (n + 1) (G z, A z - A z) = 0
    rw [hGz, sub_self, Work.WilE9.Ift.appendCLM_apply]
    funext i
    cases i using Fin.addCases with
    | left a => simp
    | right b => simp
  have hΦan : AnalyticAt ℝ Φ z := by
    have h1 : AnalyticAt ℝ (fun w => (G w, A w - A z)) z :=
      (hGan z).prod ((A.analyticAt z).sub (analyticAt_const (v := A z) (x := z)))
    have h2 : AnalyticAt ℝ (fun p : (Fin T.j → ℝ) × (Fin (n + 1) → ℝ) =>
        Work.WilE9.Ift.appendCLM T.j (n + 1) p) (G z, A z - A z) :=
      (Work.WilE9.Ift.appendCLM T.j (n + 1)).analyticAt _
    have h3 := AnalyticAt.comp (f := fun w => (G w, A w - A z)) (x := z) h2 h1
    simpa [Φ, Function.comp_def] using h3
  have hstr : HasStrictFDerivAt Φ
      ((Work.WilE9.Ift.appendCLM T.j (n + 1)).comp ((fderiv ℝ G z).prod A)) z := by
    have h1 : HasStrictFDerivAt (fun w => (G w, A w - A z)) ((fderiv ℝ G z).prod A) z := by
      have h := ((hGan z).hasStrictFDerivAt).prodMk
        (A.hasStrictFDerivAt.sub (hasStrictFDerivAt_const (A z) z))
      simpa using h
    have h2 := (Work.WilE9.Ift.appendCLM T.j (n + 1)).hasStrictFDerivAt.comp z h1
    simpa [Φ, Function.comp_def] using h2
  -- ## `fderiv Φ z` is surjective
  have hsurjG : Function.Surjective (fderiv ℝ G z) := by
    intro u
    have hu : u ∈ (fderiv ℝ G z).range := by rw [hGtop]; exact Submodule.mem_top
    exact LinearMap.mem_range.mp hu
  have hsurj_prod : Function.Surjective ((fderiv ℝ G z).prod A) := by
    intro t
    obtain ⟨w₁, hw₁⟩ := hsurjG t.1
    have hy : t.2 - A w₁ ∈ (LinearMap.ker (Work.WilE7.MainDesign.jac T z)).map L := by
      rw [hkerL]; exact Submodule.mem_top
    obtain ⟨w₂, hw₂ker, hw₂L⟩ := Submodule.mem_map.mp hy
    have hw₂A : A w₂ = t.2 - A w₁ := by
      rw [show A w₂ = L w₂ from rfl, hw₂L]
    have hmem : w₂ ∈ LinearMap.ker J := by
      rw [← hkerEq]; exact hw₂ker
    have hw₂kerG : (fderiv ℝ G z) w₂ = 0 := LinearMap.mem_ker.mp hmem
    have h1 : (fderiv ℝ G z) (w₁ + w₂) = t.1 := by
      rw [map_add, hw₁, hw₂kerG, add_zero]
    have h2 : A (w₁ + w₂) = t.2 := by
      rw [map_add, hw₂A]; abel
    refine ⟨w₁ + w₂, ?_⟩
    rw [ContinuousLinearMap.prod_apply]
    exact Prod.ext h1 h2
  have hApp_surj : Function.Surjective (Work.WilE9.Ift.appendCLM T.j (n + 1)) := by
    intro t
    refine ⟨(t ∘ Fin.castAdd (n + 1), t ∘ Fin.natAdd T.j), ?_⟩
    rw [Work.WilE9.Ift.appendCLM_apply]
    funext i
    cases i using Fin.addCases with
    | left a => rw [Fin.append_left]; rfl
    | right b => rw [Fin.append_right]; rfl
  have hsurj : Function.Surjective (fderiv ℝ Φ z) := by
    have hΦder : fderiv ℝ Φ z
        = (Work.WilE9.Ift.appendCLM T.j (n + 1)).comp ((fderiv ℝ G z).prod A) :=
      hstr.hasFDerivAt.fderiv
    rw [hΦder]
    intro t
    obtain ⟨s, hs⟩ := hApp_surj t
    obtain ⟨w, hw⟩ := hsurj_prod s
    exact ⟨w, by rw [ContinuousLinearMap.comp_apply, hw, hs]⟩
  -- ## `Good` upgrades `G w = 0` to membership near `z`
  have hloc : ∀ᶠ w in 𝓝 z, G w = 0 → w ∈ T.X.set := by
    filter_upwards [Work.WilE5.Stratum.good_local hT hz] with w hw hG0
    refine hw (funext fun i => Fin.elim0 i) fun a => ?_
    have := congrFun hG0 a
    simpa using this
  -- ## Openness of `Φ` at `z`
  obtain ⟨U₀, hU₀sub, hU₀open, hU₀z⟩ := mem_nhds_iff.mp hloc
  have hmem : Φ '' U₀ ∈ 𝓝 (0 : Fin (T.j + (n + 1)) → ℝ) := by
    have h := Work.WilE7.Dim.image_mem_nhds_of_surj_fderiv hΦan hsurj U₀ (hU₀open.mem_nhds hU₀z)
    rwa [hΦz] at h
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hmem
  -- ## Extract an `(n+1)`-dimensional slice
  have hcont : Continuous (fun y : Fin (n + 1) → ℝ => Fin.append (0 : Fin T.j → ℝ) y) := by
    have h1 : (fun y : Fin (n + 1) → ℝ => Fin.append (0 : Fin T.j → ℝ) y)
        = fun y => (Work.WilE9.Ift.appendCLM T.j (n + 1)) (0, y) := by
      funext y; rw [Work.WilE9.Ift.appendCLM_apply]
    rw [h1]
    exact (Work.WilE9.Ift.appendCLM T.j (n + 1)).continuous.comp
      (continuous_const.prodMk continuous_id)
  have happ0 : Fin.append (0 : Fin T.j → ℝ) (0 : Fin (n + 1) → ℝ) = 0 := by
    funext i
    cases i using Fin.addCases with
    | left a => simp
    | right b => simp
  have hball : Metric.ball (0 : Fin (T.j + (n + 1)) → ℝ) ε ∈
      𝓝 ((fun y : Fin (n + 1) → ℝ => Fin.append (0 : Fin T.j → ℝ) y) 0) := by
    have h0 : (fun y : Fin (n + 1) → ℝ => Fin.append (0 : Fin T.j → ℝ) y) 0
        = (0 : Fin (T.j + (n + 1)) → ℝ) := happ0
    rw [h0]; exact Metric.ball_mem_nhds _ hεpos
  have hpre := hcont.continuousAt.preimage_mem_nhds hball
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hpre
  -- ## Conclusion
  refine ⟨Metric.ball (projTop n m (Work.WilE7.MainDesign.absPt z)) δ,
    Metric.ball_mem_nhds _ hδpos, ?_⟩
  intro v hv
  have hy : v - A z ∈ Metric.ball (0 : Fin (n + 1) → ℝ) δ := by
    rw [hA_apply z]
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hv
  obtain ⟨w, hwU, hwΦ⟩ := hε (hδ hy)
  have hwΦ' : Fin.append (G w) (A w - A z) = Fin.append (0 : Fin T.j → ℝ) (v - A z) := by
    have h1 : Φ w = Fin.append (G w) (A w - A z) :=
      Work.WilE9.Ift.appendCLM_apply T.j (n + 1) (G w) (A w - A z)
    have h0 := hwΦ
    rw [h1] at h0
    simpa using h0
  have hGw : G w = 0 := by
    funext a
    have hh := congrFun hwΦ' (Fin.castAdd (n + 1) a)
    rw [Fin.append_left, Fin.append_left] at hh
    exact hh
  have hAw : A w = v := by
    have hsub : A w - A z = v - A z := by
      funext i
      have hh := congrFun hwΦ' (Fin.natAdd T.j i)
      rw [Fin.append_right, Fin.append_right] at hh
      exact hh
    funext i
    have hh := congrFun hsub i
    simp only [Pi.sub_apply] at hh
    linarith
  have hwset : w ∈ T.X.set := hU₀sub hwU hGw
  refine ⟨Work.WilE7.MainDesign.absPt w, ⟨w, hwset, rfl⟩, ?_⟩
  rw [← hA_apply w, hAw]

end Work.WilE7.CoreStep
