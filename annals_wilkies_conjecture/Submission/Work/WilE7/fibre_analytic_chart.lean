import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.fiber_germ_subset_component
import Submission.Work.WilE7.eventually_mem_fiber_of_good
import Submission.Work.WilE7.Nondrop.analyticLevelSetChartRange
import Submission.Work.WilE7.coordShrink_calculus
import Submission.Work.WilE7.coordShrink_norm_le
import Submission.Work.WilE7.exists_ker_equiv

noncomputable section

open Filter Topology Set
open scoped Topology

namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-- **An analytic chart of the fibre of a `Good` stratum.**  If `S` is a `Good` stratum of `ℝ^{p+q}` and `z ∈ S.X.set`, then in the fibre of `S.X.set` over `x = projFirst p q z` there is, near `y = projSnd p q z`, the image of an analytic map `γ : (Fin (q - S.j) → ℝ) → (Fin q → ℝ)` with `γ 0 = y`, injective differential at `0`, and with the image (near `0`) contained in `S.X.set`.  I.e. each fibre of a `Good` stratum is, near each of its points, an immersed manifold of dimension `q - S.j`, parametrised inside the stratum itself.

Proof route: `S.Good` gives `rank ∂_y S.h = S.j` at `z`, hence the fibre map `y ↦ (eaEval S.X.c (S.h a) (Fin.append x y))_a` has surjective derivative at `y`; the Implicit Function Theorem chart `Work.WilE7.fgAnalyticChart` (sorry-free, in `Submission.Work.WilE7.fiber_germ_subset_component`) provides an analytic parametrisation `γ₀` of the kernel of the derivative with `γ₀ 0 = y` inside the level set of the fibre map, and `dγ₀ 0` is injective.  Its analyticity is only at `0` (and on a neighbourhood `V` of `0`); to get the global `∀ s, AnalyticAt ℝ γ s` clause, precompose with a bounded globally analytic shrinking map `ψ` with `ψ 0 = 0` and `dψ 0` invertible and with image in a ball on which `γ₀` is analytic (e.g. `ψ v = (ε/2) • v / (1 + ‖v‖²)` for small `ε > 0`); `fderiv (γ₀ ∘ ψ) 0 = fderiv γ₀ 0 ∘ fderiv ψ 0` stays injective.  Finally `S.Good`'s third clause (`Work.WilE7.eventually_mem_fiber_of_good`) turns "level set" into "in the fibre" near `y`. -/
theorem fibre_analytic_chart {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (hGood : S.Good)
    (z : Fin (p + q) → ℝ) (hz : z ∈ S.X.set) :
    ∃ (γ : (Fin (q - S.j) → ℝ) → (Fin q → ℝ)),
      γ 0 = WilkiesDesign.E.projSnd p q z ∧ (∀ s, AnalyticAt ℝ γ s) ∧
      Function.Injective (fun t : Fin (q - S.j) → ℝ => fderiv ℝ γ (0 : Fin (q - S.j) → ℝ) t) ∧
      Filter.Eventually (fun s : Fin (q - S.j) → ℝ =>
        Fin.append (WilkiesDesign.E.projFirst p q z) (γ s) ∈ S.X.set) (nhds 0) := by
  classical
  set x : Fin p → ℝ := projFirst p q z with hx
  set y : Fin q → ℝ := projSnd p q z with hy
  have hsplit : Fin.append x y = z := by rw [hx, hy, append_projFirst_projSnd]
  have hzS : Fin.append x y ∈ S.X.set := by rw [hsplit]; exact hz
  have hgy : fgFibreMap S x y = 0 := by
    funext a
    have h := Work.WilE5.Stratum.good_eqs hGood hz a
    rw [← hsplit] at h
    simpa [fgFibreMap] using h
  have hgan : ∀ w : Fin q → ℝ, AnalyticAt ℝ (fgFibreMap S x) w :=
    fun w => analyticAt_fgFibreMap S x w
  have hsurj : (fderiv ℝ (fgFibreMap S x) y).range = ⊤ :=
    range_fderiv_fgFibreMap S hGood x y hzS
  obtain ⟨γ₀, V, U, χ, hVo, hUo, h0V, hyU, hγ₀0, hγ₀an, hγ₀VU, hγ₀sol, hγ₀surj, hγ₀injOn,
    hγ₀range, hχan, hχinv⟩ :=
    Nondrop.analyticLevelSetChartRange (fgFibreMap S x) y hgan hsurj
  -- ### Step 1: the differential of the implicit-function chart is injective
  have hχγ : χ ∘ γ₀ =ᶠ[𝓝 (0 : (fderiv ℝ (fgFibreMap S x) y).ker)] id := by
    filter_upwards [hVo.mem_nhds h0V] with v hv
    have h1 := hχinv (γ₀ v) (hγ₀VU v hv) (hγ₀sol v hv)
    exact hγ₀injOn h1.1 hv h1.2
  have hγ₀d_inj :
      Function.Injective (fderiv ℝ γ₀ (0 : (fderiv ℝ (fgFibreMap S x) y).ker)) := by
    have hcomp : fderiv ℝ (χ ∘ γ₀) (0 : (fderiv ℝ (fgFibreMap S x) y).ker)
        = (fderiv ℝ χ (γ₀ 0)) ∘SL (fderiv ℝ γ₀ 0) :=
      fderiv_comp (x := (0 : (fderiv ℝ (fgFibreMap S x) y).ker))
        (f := γ₀) (g := χ) (by rw [hγ₀0]; exact hχan.differentiableAt)
        hγ₀an.differentiableAt
    have hone : fderiv ℝ (χ ∘ γ₀) (0 : (fderiv ℝ (fgFibreMap S x) y).ker) = 1 := by
      rw [Filter.EventuallyEq.fderiv_eq hχγ]
      exact (hasFDerivAt_id (𝕜 := ℝ) (0 : (fderiv ℝ (fgFibreMap S x) y).ker)).fderiv
    have hchain : (fderiv ℝ χ (γ₀ 0)) ∘SL (fderiv ℝ γ₀ 0) = 1 := by
      rw [← hcomp]; exact hone
    have hpoint : ∀ u : (fderiv ℝ (fgFibreMap S x) y).ker,
        (fderiv ℝ χ (γ₀ 0)) ((fderiv ℝ γ₀ 0) u) = u := by
      intro u
      have h := congrArg (fun f : (fderiv ℝ (fgFibreMap S x) y).ker →L[ℝ]
          (fderiv ℝ (fgFibreMap S x) y).ker => f u) hchain
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] using h
    intro u v huv
    calc u = (fderiv ℝ χ (γ₀ 0)) ((fderiv ℝ γ₀ 0) u) := (hpoint u).symm
      _ = (fderiv ℝ χ (γ₀ 0)) ((fderiv ℝ γ₀ 0) v) := by rw [huv]
      _ = v := hpoint v
  -- ### Step 2: a topological linear equivalence of the fibre kernel with `ℝ^{q - S.j}`
  obtain ⟨e₀⟩ := exists_ker_equiv (fderiv ℝ (fgFibreMap S x) y) hsurj
  let E : (Fin (q - S.j) → ℝ) →L[ℝ] (fderiv ℝ (fgFibreMap S x) y).ker := e₀
  -- ### Step 3: radii -- a ball inside `V` and a ball of analyticity of `γ₀`, and a
  -- radius `δ` controlled by the continuity of `E`
  obtain ⟨r₁, hr₁pos, hr₁⟩ :=
    Metric.isOpen_iff.mp hVo (0 : (fderiv ℝ (fgFibreMap S x) y).ker) h0V
  obtain ⟨r₂, hr₂pos, hr₂⟩ := Metric.eventually_nhds_iff.mp hγ₀an.eventually_analyticAt
  have hE0 : E 0 = 0 := map_zero E
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∀ w : Fin (q - S.j) → ℝ, ‖w‖ < δ → ‖E w‖ < min r₁ r₂ := by
    have hcont : ContinuousAt E (0 : Fin (q - S.j) → ℝ) := E.continuous.continuousAt
    have hball : Metric.ball (0 : (fderiv ℝ (fgFibreMap S x) y).ker) (min r₁ r₂) ∈ 𝓝 (E 0) := by
      rw [hE0]
      exact Metric.ball_mem_nhds 0 (lt_min hr₁pos hr₂pos)
    have hpre : {w : Fin (q - S.j) → ℝ |
        E w ∈ Metric.ball (0 : (fderiv ℝ (fgFibreMap S x) y).ker) (min r₁ r₂)}
          ∈ 𝓝 (0 : Fin (q - S.j) → ℝ) := hcont hball
    rw [Metric.mem_nhds_iff] at hpre
    obtain ⟨δ, hδpos, hδ⟩ := hpre
    refine ⟨δ, hδpos, fun w hw => ?_⟩
    have hw' : w ∈ Metric.ball (0 : Fin (q - S.j) → ℝ) δ := by
      rwa [Metric.mem_ball, dist_eq_norm, sub_zero]
    have hthis : E w ∈ Metric.ball (0 : (fderiv ℝ (fgFibreMap S x) y).ker) (min r₁ r₂) :=
      hδ hw'
    rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hthis
  -- ### Step 4: the globally analytic shrinking map and the parametrisation `γ = γ₀ ∘ Ψ`
  have hcs1 : coordShrink (q - S.j) δ (0 : Fin (q - S.j) → ℝ) = 0 :=
    (coordShrink_calculus (q - S.j) δ hδpos).1
  have hcs_an : ∀ s : Fin (q - S.j) → ℝ, AnalyticAt ℝ (coordShrink (q - S.j) δ) s :=
    (coordShrink_calculus (q - S.j) δ hδpos).2.1
  have hcs_fd : fderiv ℝ (coordShrink (q - S.j) δ) (0 : Fin (q - S.j) → ℝ) = δ • 1 :=
    (coordShrink_calculus (q - S.j) δ hδpos).2.2
  have hnorm : ∀ v : Fin (q - S.j) → ℝ, ‖coordShrink (q - S.j) δ v‖ ≤ δ / 2 :=
    fun v => coordShrink_norm_le (q - S.j) δ hδpos.le v
  set Ψ : (Fin (q - S.j) → ℝ) → (fderiv ℝ (fgFibreMap S x) y).ker :=
    fun v => E (coordShrink (q - S.j) δ v) with hΨdef
  have hΨapply : ∀ v, Ψ v = E (coordShrink (q - S.j) δ v) := fun v => by rw [hΨdef]
  have hΨ0 : Ψ 0 = 0 := by rw [hΨapply 0, hcs1, map_zero]
  have hΨan : ∀ s, AnalyticAt ℝ Ψ s := by
    intro s
    rw [hΨdef]
    exact (E.analyticAt (coordShrink (q - S.j) δ s)).comp (hcs_an s)
  have hΨdist : ∀ s : Fin (q - S.j) → ℝ,
      dist (Ψ s) (0 : (fderiv ℝ (fgFibreMap S x) y).ker) < min r₁ r₂ := by
    intro s
    rw [dist_zero_right, hΨapply s]
    exact hδ _ (lt_of_le_of_lt (hnorm s) (by linarith))
  have hΨderiv : fderiv ℝ Ψ (0 : Fin (q - S.j) → ℝ)
      = E ∘SL (δ • (1 : (Fin (q - S.j) → ℝ) →L[ℝ] (Fin (q - S.j) → ℝ))) := by
    have hcomp : fderiv ℝ Ψ (0 : Fin (q - S.j) → ℝ)
        = (fderiv ℝ (fun w : Fin (q - S.j) → ℝ => E w) (coordShrink (q - S.j) δ 0))
          ∘SL (fderiv ℝ (coordShrink (q - S.j) δ) 0) := by
      rw [hΨdef]
      exact fderiv_comp (x := (0 : Fin (q - S.j) → ℝ))
        (f := coordShrink (q - S.j) δ) (g := fun w : Fin (q - S.j) → ℝ => E w)
        ((ContinuousLinearMap.hasFDerivAt E (x := coordShrink (q - S.j) δ 0)).differentiableAt)
        ((hcs_an 0).differentiableAt)
    have hEfd : fderiv ℝ (fun w : Fin (q - S.j) → ℝ => E w) (coordShrink (q - S.j) δ 0) = E :=
      (ContinuousLinearMap.hasFDerivAt E (x := coordShrink (q - S.j) δ 0)).fderiv
    rw [hcomp, hEfd, hcs_fd]
  have hΨd_inj : Function.Injective (fderiv ℝ Ψ (0 : Fin (q - S.j) → ℝ)) := by
    rw [hΨderiv]
    intro u v huv
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply] at huv
    have h1 : δ • u = δ • v := e₀.injective huv
    have h2 : u - v = 0 := by
      have h3 : δ • (u - v) = 0 := by rw [smul_sub, h1, sub_self]
      rcases smul_eq_zero.mp h3 with h | h
      · exact absurd h hδpos.ne'
      · exact h
    exact sub_eq_zero.mp h2
  set γ : (Fin (q - S.j) → ℝ) → (Fin q → ℝ) := γ₀ ∘ Ψ with hγdef
  have hγapply : ∀ v, γ v = γ₀ (Ψ v) := fun v => by rw [hγdef, Function.comp_apply]
  have hγ0 : γ 0 = y := by rw [hγapply 0, hΨ0, hγ₀0]
  have hγan : ∀ s, AnalyticAt ℝ γ s := by
    intro s
    rw [hγdef]
    exact (hr₂ (lt_of_lt_of_le (hΨdist s) (min_le_right r₁ r₂))).comp (hΨan s)
  have hγderiv : fderiv ℝ γ (0 : Fin (q - S.j) → ℝ)
      = (fderiv ℝ γ₀ 0) ∘SL (fderiv ℝ Ψ 0) := by
    have hcomp : fderiv ℝ (γ₀ ∘ Ψ) (0 : Fin (q - S.j) → ℝ)
        = (fderiv ℝ γ₀ (Ψ 0)) ∘SL (fderiv ℝ Ψ 0) :=
      fderiv_comp (x := (0 : Fin (q - S.j) → ℝ)) (f := Ψ) (g := γ₀)
        (by rw [hΨ0]; exact hγ₀an.differentiableAt) ((hΨan 0).differentiableAt)
    rw [hΨ0] at hcomp
    rw [hγdef]
    exact hcomp
  have hfinj : Function.Injective
      (fun t : Fin (q - S.j) → ℝ => fderiv ℝ γ (0 : Fin (q - S.j) → ℝ) t) := by
    rw [show (fun t : Fin (q - S.j) → ℝ => fderiv ℝ γ (0 : Fin (q - S.j) → ℝ) t)
        = fun t => (fderiv ℝ γ₀ 0) ((fderiv ℝ Ψ 0) t) from by
          funext t; rw [hγderiv, ContinuousLinearMap.comp_apply]]
    exact hγ₀d_inj.comp hΨd_inj
  -- ### Step 5: near `0` the parametrisation lands in the stratum
  have hmain : ∀ᶠ s : Fin (q - S.j) → ℝ in 𝓝 0, Fin.append x (γ s) ∈ S.X.set := by
    have hVev : ∀ᶠ s : Fin (q - S.j) → ℝ in 𝓝 0, Ψ s ∈ V :=
      (hΨan 0).continuousAt.eventually (by rw [hΨ0]; exact hVo.mem_nhds h0V)
    have hγy : ∀ᶠ s : Fin (q - S.j) → ℝ in 𝓝 0,
        (∀ a, eaEval S.X.c (S.h a) (Fin.append x (γ s)) = 0) →
          γ s ∈ fiber S.X.set x := by
      have hcont : Tendsto γ (𝓝 0) (𝓝 y) := by
        have h' : Tendsto γ (𝓝 0) (𝓝 (γ 0)) := (hγan 0).continuousAt
        rwa [hγ0] at h'
      exact hcont.eventually (eventually_mem_fiber_of_good S hGood x y hzS)
    filter_upwards [hVev, hγy] with s hsV hs
    apply hs
    intro a
    have h1 : fgFibreMap S x (γ s) = 0 := by
      rw [hγapply s, hγ₀sol (Ψ s) hsV, hgy]
    exact congrFun h1 a
  exact ⟨γ, hγ0.trans hy, hγan, hfinj, by simpa only [hx] using hmain⟩

end Work.WilE7
