import Mathlib
import Submission.Work.WilE7.DimAPI.criticalLevelSetLocallyConstAt
import Submission.Work.WilE7.DimAPI.eventually_ker_comp_fderiv_eq

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology

namespace Work.WilE7.CoreStep

/-- **Vanishing of `ψ` where a constant-rank projection vanishes.**

Let `ψ : ℝ^q → ℝⁿ` be analytic on a neighbourhood `W` of the origin, with `ψ 0 = 0` and with
`fderiv ψ w` of constant rank `q - 1` for all `w ∈ W`.  Let `π : ℝⁿ → ℝ^{q-1}` be a linear map
whose composition with `fderiv ψ 0` is surjective.  Then, near the origin, `π (ψ y) = 0` forces
`ψ y = 0`.

The reduced map `g = π ∘ ψ` is a submersion at the origin (its differential is `π ∘ dψ_0`, which
is surjective by hypothesis), and since `fderiv ψ` has constant rank `q - 1 = dim ℝ^{q-1}` near
`0`, the kernel of `dg_y = π ∘ dψ_y` agrees with the kernel of `dψ_y` there
(`eventually_ker_comp_fderiv_eq`).  Hence the vanishing of `dg_y` on a vector forces the vanishing
of `dψ_y` on it, and `criticalLevelSetLocallyConstAt` shows that every coordinate function of `ψ`
is constant along the level set `{g = 0}` near `0`; since `ψ 0 = 0` and `g 0 = 0`, this gives the
claim. -/
theorem eventually_eq_zero_of_proj_eq_zero {q n : ℕ} (hq : 1 ≤ q)
    (ψ : (Fin q → ℝ) → (Fin n → ℝ)) (W : Set (Fin q → ℝ)) (hW : W ∈ nhds (0 : Fin q → ℝ))
    (hψ : ∀ w ∈ W, AnalyticAt ℝ ψ w)
    (hrank : ∀ w ∈ W, Module.finrank ℝ (fderiv ℝ ψ w).range = q - 1)
    (h0 : ψ 0 = 0) (π : (Fin n → ℝ) →L[ℝ] (Fin (q - 1) → ℝ))
    (hπ : Function.Surjective fun w : Fin q → ℝ => π (fderiv ℝ ψ 0 w)) :
    ∀ᶠ y in nhds (0 : Fin q → ℝ), π (ψ y) = 0 → ψ y = 0 := by
  classical
  have _hq : 1 ≤ q := hq
  have h0W : (0 : Fin q → ℝ) ∈ W := mem_of_mem_nhds hW
  have hψ0 : AnalyticAt ℝ ψ 0 := hψ 0 h0W
  have hrank_ev : ∀ᶠ y in nhds (0 : Fin q → ℝ),
      Module.finrank ℝ (fderiv ℝ ψ y).range = q - 1 :=
    Filter.eventually_of_mem hW fun y hy => hrank y hy
  have han_ev : ∀ᶠ y in nhds (0 : Fin q → ℝ), AnalyticAt ℝ ψ y :=
    Filter.eventually_of_mem hW fun y hy => hψ y hy
  -- The reduced map `g = π ∘ ψ`.
  let g : (Fin q → ℝ) → (Fin (q - 1) → ℝ) := fun y => π (ψ y)
  have hg_an : AnalyticAt ℝ g 0 := by
    have h := (π.analyticAt (ψ 0)).comp hψ0
    simpa only [g, Function.comp_def] using h
  have hfd_g_ev : ∀ᶠ y in nhds (0 : Fin q → ℝ),
      fderiv ℝ g y = π.comp (fderiv ℝ ψ y) := by
    filter_upwards [han_ev] with y hyan
    have h1 : HasFDerivAt ψ (fderiv ℝ ψ y) y := hyan.differentiableAt.hasFDerivAt
    have h2 : HasFDerivAt (fun w : Fin n → ℝ => π w) π (ψ y) := π.hasFDerivAt
    have h3 := h2.comp y h1
    simpa only [g, Function.comp_def] using h3.fderiv
  have hfd_g_0 : fderiv ℝ g 0 = π.comp (fderiv ℝ ψ 0) := by
    have h1 : HasFDerivAt ψ (fderiv ℝ ψ 0) 0 := hψ0.differentiableAt.hasFDerivAt
    have h2 : HasFDerivAt (fun w : Fin n → ℝ => π w) π (ψ 0) := π.hasFDerivAt
    have h3 := h2.comp 0 h1
    simpa only [g, Function.comp_def] using h3.fderiv
  have hsurj_g : (fderiv ℝ g 0).range = ⊤ := by
    rw [hfd_g_0]
    exact LinearMap.range_eq_top.mpr hπ
  -- The kernel of `fderiv ℝ g` agrees with that of `fderiv ℝ ψ` near `0`.
  have hker := Work.WilE7.DimAPI.eventually_ker_comp_fderiv_eq ψ 0 hψ0 hrank_ev π hπ
  -- Criticality for every coordinate function of `ψ`.
  have hcrit : ∀ j : Fin n, ∀ᶠ y in nhds (0 : Fin q → ℝ),
      g y = 0 → ∀ v, (fderiv ℝ g y) v = 0 →
        (fderiv ℝ (fun y : Fin q → ℝ => ψ y j) y) v = 0 := by
    intro j
    filter_upwards [hker, hfd_g_ev, han_ev] with y hyker hyfd hyan
    intro _hgy v hv
    rw [hyfd] at hv
    have hvmem : v ∈ (fderiv ℝ ψ y).ker := by
      have hmem : v ∈ (π.comp (fderiv ℝ ψ y)).ker := hv
      rwa [hyker] at hmem
    have hψv0 : (fderiv ℝ ψ y) v = 0 := hvmem
    have hgd : fderiv ℝ (fun y : Fin q → ℝ => ψ y j) y
        = (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ ψ y) :=
      fderiv_apply hyan.differentiableAt j
    rw [hgd]
    show (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) ((fderiv ℝ ψ y) v) = 0
    rw [hψv0, map_zero]
  -- Each coordinate of `ψ` is constant (equal to `ψ 0`) on the level set `{g = 0}` near `0`.
  have hconst : ∀ j : Fin n, ∀ᶠ y in nhds (0 : Fin q → ℝ),
      g y = 0 → ψ y j = ψ 0 j := by
    intro j
    have hF : AnalyticAt ℝ (fun y : Fin q → ℝ => ψ y j) 0 :=
      ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).analyticAt (ψ 0)).comp hψ0
    exact Work.WilE7.DimAPI.criticalLevelSetLocallyConstAt g (fun y : Fin q → ℝ => ψ y j) 0
      hg_an hF hsurj_g (hcrit j)
  filter_upwards [Filter.eventually_all.mpr hconst] with y hy
  intro hgy
  funext j
  rw [hy j hgy, congrFun h0 j]

end Work.WilE7.CoreStep
