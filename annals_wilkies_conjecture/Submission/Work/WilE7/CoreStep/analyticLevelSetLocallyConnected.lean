import Mathlib
import Submission.Work.WilE7.fiber_germ_subset_component
import Submission.Work.WilE7.CoreStep.finrankOneAnalyticIsolatedZero

/-!
# An analytic level set of codimension one is locally connected to its component

Let `G : ℝ^{m+1} → ℝ^k` and `Ψ : ℝ^{m+1} → ℝ^m` be analytic, with `Ψ` submersive at `p`, and suppose
that the level set `{G = G p}` is contained in the fibre `{Ψ = Ψ p}` (hypothesis `hcon`).  Let `Z`
be a set which is contained in `{G = G p}` (`hZeq`) and which, near `p`, contains `{G = G p}`
(`hZgerm`).  Then, near `p`, every point of `Z` lies in the connected component of `p` in `Z`.

The proof is the implicit function theorem applied to `Ψ`: near `p` the fibre `{Ψ = Ψ p}` is the
image of a neighbourhood `V` of `0` in the one-dimensional space `ker (dΨ)_p` under an analytic map
`γ` (with `γ 0 = p`), with a continuous "inverse" `σ`: every point of the fibre close to `p` is
`γ (σ ·)`.

Since the level set of `G` is contained in the fibre, the whole question is the behaviour of the
analytic map `v ↦ G (γ v)` on the one-dimensional space `ker (dΨ)_p` (which vanishes at `0`, as
`γ 0 = p`).  By the principle of isolated zeros in one dimension
(`Work.WilE7.CoreStep.finrankOneAnalyticIsolatedZero`) there are two cases:

* either `G (γ v) = G p` for all `v` close to `0`, and then the preconnected chart piece
  `γ '' ball 0 δ` consists entirely of points of `Z`, so it is a connected subset of `Z`
  containing both `p` and (by the chart) every nearby point of `Z`;
* or `G (γ v) = G p` forces `v = 0`, and then every nearby point of `Z` (which lies in the fibre,
  by `hcon`) is `γ (σ ·)` with `G (γ (σ ·)) = G p`, hence equal to `γ 0 = p`.
-/

namespace Work.WilE7.CoreStep

open scoped Topology
open Filter Set

noncomputable section

theorem analyticLevelSetLocallyConnected {m k : ℕ}
    {G : (Fin (m+1) → ℝ) → (Fin k → ℝ)} {Ψ : (Fin (m+1) → ℝ) → (Fin m → ℝ)}
    {p : Fin (m+1) → ℝ} {Z : Set (Fin (m+1) → ℝ)}
    (hGan : ∀ y, AnalyticAt ℝ G y) (hΨan : ∀ y, AnalyticAt ℝ Ψ y)
    (hcon : ∀ y, G y = G p → Ψ y = Ψ p)
    (hsurj : (fderiv ℝ Ψ p).range = ⊤)
    (hZeq : ∀ y ∈ Z, G y = G p)
    (hZgerm : ∀ᶠ y in nhds p, G y = G p → y ∈ Z) :
    ∃ U ∈ nhds p, ∀ y ∈ U, y ∈ Z → y ∈ connectedComponentIn Z p := by
  classical
  -- the analytic chart of the fibre `{Ψ = Ψ p}` near `p`
  obtain ⟨γ, σ, V, U, hVo, hUo, h0V, hpU, hγ0, hγan, hγcont, hσcont, hσp, hVg, hσγ⟩ :=
    fgAnalyticChart Ψ p hΨan hsurj
  -- `p` lies in `Z`
  have hpZ : p ∈ Z := hZgerm.self_of_nhds rfl
  -- a ball around `p` on which the level set `{G = G p}` is contained in `Z`
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.mem_nhds_iff.mp hZgerm
  -- the kernel of the differential of `Ψ` at `p` is one-dimensional
  have hfin : Module.finrank ℝ ((fderiv ℝ Ψ p).ker) = 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker ((fderiv ℝ Ψ p).toLinearMap)
    rw [hsurj] at h1
    simp at h1
    omega
  -- the composed map `v ↦ G (γ v)` is analytic at `0` on this kernel
  have hf_an : AnalyticAt ℝ (fun v : (fderiv ℝ Ψ p).ker => G (γ v)) 0 := by
    have h1 : AnalyticAt ℝ (G ∘ γ) 0 := AnalyticAt.comp (hGan (γ 0)) hγan
    simpa [Function.comp_def] using h1
  -- the one-dimensional dichotomy for it
  have hdich : (∀ᶠ v in 𝓝 (0 : (fderiv ℝ Ψ p).ker), G (γ v) = G p) ∨
      ∃ δ : ℝ, 0 < δ ∧ ∀ v : (fderiv ℝ Ψ p).ker, ‖v‖ < δ → G (γ v) = G p → v = 0 := by
    have h := finrankOneAnalyticIsolatedZero hfin
      (f := fun v : (fderiv ℝ Ψ p).ker => G (γ v)) hf_an
    simpa [hγ0] using h
  rcases hdich with hev | ⟨δ, hδpos, hδ⟩
  · -- Case 1: `G` is constant along the fibre germ; the chart piece lies in `Z`
    have hall : ∀ᶠ v in 𝓝 (0 : (fderiv ℝ Ψ p).ker),
        G (γ v) = G p ∧ γ v ∈ Metric.ball p ρ ∧ v ∈ V := by
      filter_upwards [hev, (hγan.continuousAt (x := 0)).preimage_mem_nhds
        (by rw [hγ0]; exact Metric.ball_mem_nhds p hρpos), hVo.mem_nhds h0V] with v h1 h2 h3
      exact ⟨h1, h2, h3⟩
    obtain ⟨δ', hδ'pos, hδ'⟩ := Metric.mem_nhds_iff.mp hall
    have hballV : Metric.ball (0 : (fderiv ℝ Ψ p).ker) δ' ⊆ V :=
      fun v hv => (hδ' hv).2.2
    have hSpre : IsPreconnected (γ '' Metric.ball (0 : (fderiv ℝ Ψ p).ker) δ') :=
      (convex_ball (0 : (fderiv ℝ Ψ p).ker) δ').isPreconnected.image γ (hγcont.mono hballV)
    have hSZ : γ '' Metric.ball (0 : (fderiv ℝ Ψ p).ker) δ' ⊆ Z := by
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨hGv, hγv, -⟩ := hδ' hv
      exact hρ hγv hGv
    have hpS : p ∈ γ '' Metric.ball (0 : (fderiv ℝ Ψ p).ker) δ' :=
      ⟨0, Metric.mem_ball_self hδ'pos, hγ0⟩
    have hScomp : γ '' Metric.ball (0 : (fderiv ℝ Ψ p).ker) δ' ⊆ connectedComponentIn Z p :=
      hSpre.subset_connectedComponentIn hpS hSZ
    have hσnb : σ ⁻¹' Metric.ball (0 : (fderiv ℝ Ψ p).ker) δ' ∈ 𝓝 p := by
      have h := (hσcont.continuousAt (x := p)).preimage_mem_nhds
        (Metric.ball_mem_nhds (σ p) hδ'pos)
      rwa [hσp] at h
    refine ⟨U ∩ σ ⁻¹' Metric.ball (0 : (fderiv ℝ Ψ p).ker) δ',
      Filter.inter_mem (hUo.mem_nhds hpU) hσnb, ?_⟩
    intro y hy hyZ
    obtain ⟨hyU, hyball⟩ := hy
    have hgy : G y = G p := hZeq y hyZ
    obtain ⟨-, hγσy⟩ := hσγ y hyU (hcon y hgy)
    rw [← hγσy]
    exact hScomp ⟨σ y, hyball, rfl⟩
  · -- Case 2: the level set of `G` meets the fibre germ only at `p`
    have hσnb : σ ⁻¹' Metric.ball (0 : (fderiv ℝ Ψ p).ker) δ ∈ 𝓝 p := by
      have h := (hσcont.continuousAt (x := p)).preimage_mem_nhds
        (Metric.ball_mem_nhds (σ p) hδpos)
      rwa [hσp] at h
    refine ⟨U ∩ σ ⁻¹' Metric.ball (0 : (fderiv ℝ Ψ p).ker) δ,
      Filter.inter_mem (hUo.mem_nhds hpU) hσnb, ?_⟩
    intro y hy hyZ
    obtain ⟨hyU, hyball⟩ := hy
    have hgy : G y = G p := hZeq y hyZ
    obtain ⟨-, hγσy⟩ := hσγ y hyU (hcon y hgy)
    have hnorm : ‖σ y‖ < δ := by
      simpa [dist_zero_right] using Metric.mem_ball.mp hyball
    have hzero : σ y = 0 := by
      refine hδ (σ y) hnorm ?_
      rw [hγσy]
      exact hgy
    rw [← hγσy, hzero, hγ0]
    exact mem_connectedComponentIn hpZ

end

end Work.WilE7.CoreStep
