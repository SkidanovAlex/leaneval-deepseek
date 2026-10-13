/-
  G2, local ingredient: **ball coverage of a `Good` absolute stratum under a tangent-surjective
  linear map**.

  `S : Stratum 0 M` is an absolute stratum of `ℝ^(0+M)` with `S.j` defining equations `h`; it is
  `Good` at `z ∈ S.X.set`, so `h z = 0`, the full Jacobian `jac S z` is onto `ℝ^(S.j)`
  (`range_fderiv_good_eq_top`), and the level set `{h = 0}` coincides with `S.X.set` near `z`
  (`good_local`).  `A : ℝ^(0+M) → ℝ^r` is any linear map whose restriction to the tangent space
  `ker (jac S z)` is onto `ℝ^r` (the hypothesis `(ker (jac S z)).map A = ⊤`).

  Then `A` maps `S.X.set ∩ U` onto a neighbourhood of `A z` for every neighbourhood `U` of `z` —
  i.e. `A` restricted to the stratum is a *local submersion* at `z`.

  The proof is the usual open-mapping argument, exactly as in `locSubmersion_of_finrank` and
  `not_dimLE_of_projRank`: the equation map `G w = (a ↦ h_a(w))` of `S` is analytic at `z` with
  `G z = 0` and surjective differential; the map
  `Φ w = append (G w) (A w - A z) : ℝ^(0+M) → ℝ^(S.j + r)`
  is therefore analytic at `z` with surjective differential there (the first block accounts for the
  `G`-directions, the second for the `r` directions of `ker (jac S z)` supplied by the hypothesis),
  hence open at `z` (`Work.WilE7.Dim.image_mem_nhds_of_surj_fderiv`).  Every small `y` is thus
  `Φ w` for some `w` near `z`; the first block gives `G w = 0`, which `Good` upgrades to
  `w ∈ S.X.set`, and the second block gives `A w = A z + y`, i.e. `A w = y`.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.not_dimLE_of_projRank
import Submission.Work.WilE7.CoreStep.locSubmersion_of_finrank

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E

theorem g2_ball_coverage {M r : ℕ} (S : WilkiesDesign.E.Stratum 0 M)
    (hS : S.Good) (z : Fin (0 + M) → ℝ) (hz : z ∈ S.X.set)
    (A : (Fin (0 + M) → ℝ) →ₗ[ℝ] (Fin r → ℝ))
    (hA : (LinearMap.ker (Work.WilE7.MainDesign.jac S z)).map A = ⊤)
    (U : Set (Fin (0 + M) → ℝ)) (hU : U ∈ nhds z) :
    ∃ δ > 0, Metric.ball (A z) δ ⊆ A '' (S.X.set ∩ U) := by
  classical
  -- `A` is continuous (finite dimension); `Φ` below needs a continuous linear map.
  let Ac : (Fin (0 + M) → ℝ) →L[ℝ] (Fin r → ℝ) := LinearMap.toContinuousLinearMap A
  have hAc_apply : ∀ w, Ac w = A w := fun _ => rfl
  have hAck : (LinearMap.ker (Work.WilE7.MainDesign.jac S z)).map
      (Ac : (Fin (0 + M) → ℝ) →ₗ[ℝ] (Fin r → ℝ)) = ⊤ := hA
  -- ## The defining-equation map of the stratum
  let G : (Fin (0 + M) → ℝ) → (Fin S.j → ℝ) := fun w a => eaEval S.X.c (S.h a) w
  have hGan : ∀ w, AnalyticAt ℝ G w :=
    fun w => AnalyticAt.pi (fun a => Work.WilE5.Strat.analyticAt_eaEval S.X.c (S.h a) w)
  have hGz : G z = 0 := funext fun a => Work.WilE5.Stratum.good_eqs hS hz a
  have hGtop : (fderiv ℝ G z).range = ⊤ :=
    Work.WilE7.DimAPI.range_fderiv_good_eq_top S hS hz
  let J : (Fin (0 + M) → ℝ) →ₗ[ℝ] (Fin S.j → ℝ) :=
    (fderiv ℝ G z : (Fin (0 + M) → ℝ) →L[ℝ] (Fin S.j → ℝ))
  have hjac : ((Work.WilE7.MainDesign.jac S z :
        (Fin (0 + M) → ℝ) →ₗ[ℝ] (Fin S.j → ℝ))) = J :=
    Work.WilE7.DimAPI.jac_eq_fderiv S z
  have hkerEq : LinearMap.ker (Work.WilE7.MainDesign.jac S z) = LinearMap.ker J := by
    rw [hjac]
  -- ## The auxiliary map `Φ w = append (G w) (A w - A z)`
  let Φ : (Fin (0 + M) → ℝ) → (Fin (S.j + r) → ℝ) :=
    fun w => Work.WilE9.Ift.appendCLM S.j r (G w, Ac w - Ac z)
  have hΦz : Φ z = 0 := by
    show Work.WilE9.Ift.appendCLM S.j r (G z, Ac z - Ac z) = 0
    rw [hGz, sub_self, Work.WilE9.Ift.appendCLM_apply]
    funext i
    cases i using Fin.addCases with
    | left a => simp
    | right b => simp
  have hΦan : AnalyticAt ℝ Φ z := by
    have h1 : AnalyticAt ℝ (fun w => (G w, Ac w - Ac z)) z :=
      (hGan z).prod ((Ac.analyticAt z).sub (analyticAt_const (v := Ac z) (x := z)))
    have h2 : AnalyticAt ℝ (fun p : (Fin S.j → ℝ) × (Fin r → ℝ) =>
        Work.WilE9.Ift.appendCLM S.j r p) (G z, Ac z - Ac z) :=
      (Work.WilE9.Ift.appendCLM S.j r).analyticAt _
    have h3 := AnalyticAt.comp (f := fun w => (G w, Ac w - Ac z)) (x := z) h2 h1
    simpa [Φ, Function.comp_def] using h3
  have hstr : HasStrictFDerivAt Φ
      ((Work.WilE9.Ift.appendCLM S.j r).comp ((fderiv ℝ G z).prod Ac)) z := by
    have h1 : HasStrictFDerivAt (fun w : (Fin (0 + M) → ℝ) => (G w, Ac w - Ac z))
        ((fderiv ℝ G z).prod Ac) z := by
      have h := ((hGan z).hasStrictFDerivAt).prodMk
        (Ac.hasStrictFDerivAt.sub (hasStrictFDerivAt_const (Ac z) z))
      simpa using h
    have h2 := (Work.WilE9.Ift.appendCLM S.j r).hasStrictFDerivAt.comp z h1
    simpa [Φ, Function.comp_def] using h2
  -- ## `fderiv Φ z` is surjective
  have hsurjG : Function.Surjective (fderiv ℝ G z) := by
    intro u
    have hu : u ∈ (fderiv ℝ G z).range := by rw [hGtop]; exact Submodule.mem_top
    exact LinearMap.mem_range.mp hu
  have hsurj_prod : Function.Surjective ((fderiv ℝ G z).prod Ac) := by
    intro t
    obtain ⟨w₁, hw₁⟩ := hsurjG t.1
    have hy : t.2 - Ac w₁ ∈ (LinearMap.ker (Work.WilE7.MainDesign.jac S z)).map
        (Ac : (Fin (0 + M) → ℝ) →ₗ[ℝ] (Fin r → ℝ)) := by
      rw [hAck]; exact Submodule.mem_top
    obtain ⟨w₂, hw₂ker, hw₂L⟩ := Submodule.mem_map.mp hy
    have hw₂A : Ac w₂ = t.2 - Ac w₁ := by
      rw [show Ac w₂ = (Ac : (Fin (0 + M) → ℝ) →ₗ[ℝ] (Fin r → ℝ)) w₂ from rfl, hw₂L]
    have hmem : w₂ ∈ LinearMap.ker J := by
      rw [← hkerEq]; exact hw₂ker
    have hw₂kerG : (fderiv ℝ G z) w₂ = 0 := LinearMap.mem_ker.mp hmem
    have h1 : (fderiv ℝ G z) (w₁ + w₂) = t.1 := by
      rw [map_add, hw₁, hw₂kerG, add_zero]
    have h2 : Ac (w₁ + w₂) = t.2 := by
      rw [map_add, hw₂A]; abel
    refine ⟨w₁ + w₂, ?_⟩
    rw [ContinuousLinearMap.prod_apply]
    exact Prod.ext h1 h2
  have hApp_surj : Function.Surjective (Work.WilE9.Ift.appendCLM S.j r) := by
    intro t
    refine ⟨(t ∘ Fin.castAdd r, t ∘ Fin.natAdd S.j), ?_⟩
    rw [Work.WilE9.Ift.appendCLM_apply]
    funext i
    cases i using Fin.addCases with
    | left a => rw [Fin.append_left]; rfl
    | right b => rw [Fin.append_right]; rfl
  have hsurj : Function.Surjective (fderiv ℝ Φ z) := by
    have hΦder : fderiv ℝ Φ z
        = (Work.WilE9.Ift.appendCLM S.j r).comp ((fderiv ℝ G z).prod Ac) :=
      hstr.hasFDerivAt.fderiv
    rw [hΦder]
    intro t
    obtain ⟨s, hs⟩ := hApp_surj t
    obtain ⟨w, hw⟩ := hsurj_prod s
    exact ⟨w, by rw [ContinuousLinearMap.comp_apply, hw, hs]⟩
  -- ## `Good` upgrades `G w = 0` to membership near `z`
  have hloc : ∀ᶠ w in 𝓝 z, G w = 0 → w ∈ S.X.set := by
    filter_upwards [Work.WilE5.Stratum.good_local hS hz] with w hw hG0
    refine hw (funext fun i => Fin.elim0 i) fun a => ?_
    have := congrFun hG0 a
    simpa using this
  -- ## Openness of `Φ` at `z`, inside `U`
  have hboth : ∀ᶠ w in 𝓝 z, (G w = 0 → w ∈ S.X.set) ∧ w ∈ U := hloc.and hU
  obtain ⟨V, hVsub, hVopen, hVz⟩ := mem_nhds_iff.mp hboth
  have hmem : Φ '' V ∈ 𝓝 (0 : Fin (S.j + r) → ℝ) := by
    have h := Work.WilE7.Dim.image_mem_nhds_of_surj_fderiv hΦan hsurj V (hVopen.mem_nhds hVz)
    rwa [hΦz] at h
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hmem
  -- ## Extract the `r`-dimensional slice
  have hcont : Continuous (fun y : Fin r → ℝ => Fin.append (0 : Fin S.j → ℝ) y) := by
    have h1 : (fun y : Fin r → ℝ => Fin.append (0 : Fin S.j → ℝ) y)
        = fun y => (Work.WilE9.Ift.appendCLM S.j r) (0, y) := by
      funext y; rw [Work.WilE9.Ift.appendCLM_apply]
    rw [h1]
    exact (Work.WilE9.Ift.appendCLM S.j r).continuous.comp
      (continuous_const.prodMk continuous_id)
  have happ0 : Fin.append (0 : Fin S.j → ℝ) (0 : Fin r → ℝ) = 0 := by
    funext i
    cases i using Fin.addCases with
    | left a => simp
    | right b => simp
  have hball : Metric.ball (0 : Fin (S.j + r) → ℝ) ε ∈
      𝓝 ((fun y : Fin r → ℝ => Fin.append (0 : Fin S.j → ℝ) y) 0) := by
    have h0 : (fun y : Fin r → ℝ => Fin.append (0 : Fin S.j → ℝ) y) 0
        = (0 : Fin (S.j + r) → ℝ) := happ0
    rw [h0]; exact Metric.ball_mem_nhds _ hεpos
  have hpre := hcont.continuousAt.preimage_mem_nhds hball
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hpre
  -- ## Conclusion
  refine ⟨δ, hδpos, ?_⟩
  intro v hv
  have hv' : v ∈ Metric.ball (Ac z) δ := by
    rw [hAc_apply z]; exact hv
  have hy : v - Ac z ∈ Metric.ball (0 : Fin r → ℝ) δ := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hv'
  obtain ⟨w, hwV, hwΦ⟩ := hε (hδ hy)
  have hwΦ' : Fin.append (G w) (Ac w - Ac z) = Fin.append (0 : Fin S.j → ℝ) (v - Ac z) := by
    have h1 : Φ w = Fin.append (G w) (Ac w - Ac z) :=
      Work.WilE9.Ift.appendCLM_apply S.j r (G w) (Ac w - Ac z)
    have h0 := hwΦ
    rw [h1] at h0
    simpa using h0
  have hGw : G w = 0 := by
    funext a
    have hh := congrFun hwΦ' (Fin.castAdd r a)
    rw [Fin.append_left, Fin.append_left] at hh
    exact hh
  have hAw : Ac w - Ac z = v - Ac z := by
    funext i
    have hh := congrFun hwΦ' (Fin.natAdd S.j i)
    rw [Fin.append_right, Fin.append_right] at hh
    exact hh
  have hwA : Ac w = v := by
    funext i
    have hh := congrFun hAw i
    simp only [Pi.sub_apply] at hh
    linarith
  refine ⟨w, ⟨(hVsub hwV).1 hGw, (hVsub hwV).2⟩, ?_⟩
  rw [← hAc_apply w]
  exact hwA

end Work.WilE7.Endgame
