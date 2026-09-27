import Mathlib
import Submission.Work.Drive.N2.saddleChartLayer
import Submission.Work.Drive.N2.im_sq_eq_of_flow_closedODE
import Submission.Work.Drive.N2.anchorModelFacts
import Submission.Work.Drive.N2.saddlePack
import Submission.Work.Drive.N2.levelBoundsOfJourney
import Submission.Work.Drive.N2.sepClosedModelBall
import Submission.Work.Drive.N2.saddleCollarRow
import Submission.Work.Drive.N2.levelRateOnChart
import Submission.Work.Drive.N2.swlLanding
-- NOTE (H8, 2026-09-27): `Work.Drive.N2.footMap` was reaching this file only through the
-- (now removed) transitive import `sepClosedModelBall`/`anchorModelFacts` → `levelSeparatingMap`;
-- the explicit import makes the dependency honest.
import Submission.Work.Drive.N2.footMapDefs

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set

set_option backward.isDefEq.respectTransparency false

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ## The two `Z`-coordinates agree up to the real scalar `lam0` -/

section Coord

variable {f : M → ℝ} {p : M} {D : WindowDatum f p}
variable {φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))} {Zs Z : M → ℂ}
variable {lam0 : ℝ}

/-- `Zs = lam0 · Z` turns into `(Z y)² = (Zs y)² / lam0²`. -/
lemma swl_sq_eq_sq_div {y : M} (h : Zs y = (lam0 : ℂ) * Z y) (h0 : lam0 ≠ 0) :
    (Z y) ^ 2 = (Zs y) ^ 2 / (lam0 : ℂ) ^ 2 := by
  rw [h, mul_pow]
  field_simp
  rw [mul_div_cancel_right₀ _ (by exact_mod_cast h0 : ((lam0 : ℂ)) ≠ 0)]

/-- The imaginary part of `(Z ·)²`, scaled. -/
lemma swl_im_sq_eq_div {y : M} (h : Zs y = (lam0 : ℂ) * Z y) :
    ((Zs y) ^ 2).im = lam0 ^ 2 * ((Z y) ^ 2).im := by
  have hsq : (Zs y) ^ 2 = ((lam0 ^ 2 : ℝ) : ℂ) * (Z y) ^ 2 := by
    rw [h, mul_pow, ← Complex.ofReal_pow]
  rw [hsq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

end Coord



/-! ## Basic facts: continuity at source points, closures of the model balls -/

section Basic

variable {f : M → ℝ} {p : M} {D : WindowDatum f p}

/-- **`f` is continuous at every point of every chart source** (the chart pins `f` there). -/
lemma swl_continuousAt_of_mem_source {y : M} {i : Fin D.N} (hy : y ∈ (D.φ i).source) :
    ContinuousAt f y := by
  have hnhds : (D.φ i).source ∈ 𝓝 y := (D.φ i).open_source.mem_nhds hy
  have hφc : ContinuousAt (fun z : M => D.φ i z) y :=
    (D.hφ i).continuousOn.continuousAt hnhds
  have h1 : Continuous fun u : EuclideanSpace ℝ (Fin 2) => (u 0 : ℝ) := by fun_prop
  have h2 : Continuous fun u : EuclideanSpace ℝ (Fin 2) => (u 1 : ℝ) := by fun_prop
  have hc : Continuous fun u : EuclideanSpace ℝ (Fin 2) =>
      D.s₁ i * (u 0) ^ 2 + D.s₂ i * (u 1) ^ 2 :=
    (continuous_const.mul (h1.pow 2)).add (continuous_const.mul (h2.pow 2))
  have hQc : ContinuousAt (fun z : M =>
      D.s₁ i * (D.φ i z 0) ^ 2 + D.s₂ i * (D.φ i z 1) ^ 2) y :=
    hc.continuousAt.comp hφc
  have hev : f =ᶠ[𝓝 y] (fun z : M =>
      f (D.x i) + (D.s₁ i * (D.φ i z 0) ^ 2 + D.s₂ i * (D.φ i z 1) ^ 2)) := by
    filter_upwards [hnhds] with z hz
    rw [D.hval i z hz, chartQ]
  exact (hQc.const_add (f (D.x i))).congr_of_eventuallyEq hev

/-- The model ball of a chart at radius `r ≤ ρ i` has its closure inside the chart source. -/
lemma swl_closure_modelBall_subset_source {i : Fin D.N} {r : ℝ} (hr : r ≤ D.ρ i) :
    closure (modelBall (D.φ i) r) ⊆ (D.φ i).source := by
  refine (closure_mono ?_).trans (D.hCcl i).2
  intro y hy
  exact D.hCop i ⟨hy.1, lt_of_lt_of_le hy.2 hr⟩

/-- A closure point of the model ball of a chart lies in the chart source. -/
lemma swl_mem_source_of_mem_closure_modelBall {i : Fin D.N} {r : ℝ} (hr : r ≤ D.ρ i)
    {y : M} (hy : y ∈ closure (modelBall (D.φ i) r)) : y ∈ (D.φ i).source :=
  swl_closure_modelBall_subset_source hr hy

/-- `f` is continuous at the closure points of the model balls. -/
lemma swl_continuousAt_of_mem_closure_modelBall {i : Fin D.N} {r : ℝ} (hr : r ≤ D.ρ i)
    {y : M} (hy : y ∈ closure (modelBall (D.φ i) r)) : ContinuousAt f y :=
  swl_continuousAt_of_mem_source (swl_mem_source_of_mem_closure_modelBall hr hy)

end Basic

/-! ## Norm relations between the two charts, and openness of the model balls -/

section Norms

variable {f : M → ℝ} {p : M} {D : WindowDatum f p}
variable {φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))} {Zs Z : M → ℂ}
variable {lam0 : ℝ}

/-- The model ball of a chart of the datum is open. -/
lemma swl_isOpen_modelBall (i : Fin D.N) (r : ℝ) : IsOpen (modelBall (D.φ i) r) := by
  have h : modelBall (D.φ i) r = (D.φ i).source ∩ (D.φ i) ⁻¹' Metric.ball 0 r := by
    ext z
    simp [modelBall, Metric.mem_ball, dist_zero_right]
  rw [h]
  exact (D.φ i).isOpen_inter_preimage Metric.isOpen_ball

/-- The complex coordinate of a chart preserves norms. -/
lemma swl_norm_chartZ_eq {ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))} {y : M}
    {w : ℂ} (hw : w = (ψ y 0 : ℂ) + (ψ y 1 : ℂ) * Complex.I) : ‖w‖ = ‖ψ y‖ := by
  have h1 : w = chartZ ψ y := by rw [hw, chartZ_apply]
  rw [h1, cl_chartZ_eq_chartZLM, cl_norm_chartZLM]

/-- `Zs` has the norm of the `φ'`-coordinate. -/
lemma swl_norm_Zs_eq {y : M} (hZs : ∀ y : M, Zs y = (φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I) :
    ‖Zs y‖ = ‖φ' y‖ := swl_norm_chartZ_eq (hZs y)

/-- The two charts of the pack have the same coordinate norms. -/
lemma swl_norm_chart_eq {y : M} (hsrc : φ'.source = (D.φ D.j).source)
    (hball : ∀ r : ℝ, modelBall φ' r = modelBall (D.φ D.j) r)
    (hy : y ∈ φ'.source) : ‖φ' y‖ = ‖D.φ D.j y‖ := by
  have hyj : y ∈ (D.φ D.j).source := by rw [← hsrc]; exact hy
  refine le_antisymm ?_ ?_
  · by_contra h
    push_neg at h
    obtain ⟨r, hr1, hr2⟩ := exists_between h
    have h1 : y ∈ modelBall (D.φ D.j) r := ⟨hyj, hr1⟩
    rw [← hball r] at h1
    exact absurd h1.2 (not_lt.mpr hr2.le)
  · by_contra h
    push_neg at h
    obtain ⟨r, hr1, hr2⟩ := exists_between h
    have h1 : y ∈ modelBall φ' r := ⟨hy, hr1⟩
    rw [hball r] at h1
    exact absurd h1.2 (not_lt.mpr hr2.le)

/-- The norm of the scaled coordinate in terms of the chart norm. -/
lemma swl_norm_Z_eq {y : M} (hsrc : φ'.source = (D.φ D.j).source)
    (hball : ∀ r : ℝ, modelBall φ' r = modelBall (D.φ D.j) r)
    (hZs : ∀ y : M, Zs y = (φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I)
    {hZrel : ∀ y : M, Zs y = (lam0 : ℂ) * Z y} (hlam0pos : 0 < lam0) (hy : y ∈ φ'.source) :
    ‖Z y‖ = ‖D.φ D.j y‖ / lam0 := by
  have h1 : ‖Zs y‖ = ‖φ' y‖ := swl_norm_Zs_eq hZs
  have hnorm : ‖((lam0 : ℂ))‖ = lam0 := by
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (le_of_lt hlam0pos)]
  have h2 : lam0 * ‖Z y‖ = ‖Zs y‖ := by
    rw [hZrel y, norm_mul, hnorm]
  calc ‖Z y‖ = lam0 * ‖Z y‖ / lam0 := by field_simp
    _ = ‖Zs y‖ / lam0 := by rw [h2]
    _ = ‖φ' y‖ / lam0 := by rw [h1]
    _ = ‖D.φ D.j y‖ / lam0 := by rw [swl_norm_chart_eq hsrc hball hy]

/-- A point of the closure of a model ball of the datum has chart norm at most the radius. -/
lemma swl_norm_le_of_mem_closure_modelBall {i : Fin D.N} {r : ℝ} (hr : r ≤ D.ρ i) {y0 : M}
    (hy : y0 ∈ closure (modelBall (D.φ i) r)) : ‖D.φ i y0‖ ≤ r := by
  by_contra hcon
  push_neg at hcon
  have hsrc : y0 ∈ (D.φ i).source := swl_closure_modelBall_subset_source hr hy
  have hnhds_src : (D.φ i).source ∈ 𝓝 y0 := (D.φ i).open_source.mem_nhds hsrc
  have hcont : ContinuousAt (fun z : M => D.φ i z) y0 :=
    (D.hφ i).continuousOn.continuousAt hnhds_src
  have hnhds : {z : M | r < ‖D.φ i z‖} ∈ 𝓝 y0 :=
    hcont.norm.preimage_mem_nhds (isOpen_Ioi.mem_nhds hcon)
  obtain ⟨z, hzU, hzs⟩ := (mem_closure_iff_nhds.mp hy) _ (Filter.inter_mem hnhds_src hnhds)
  exact absurd hzU.2 (not_lt.mpr hzs.2.le)

end Norms

/-! ## The landing row (box condition) -/

/-- **The landing row.**  A point `x` in the value window whose invariant is bounded below by the
entry bound reaches the anchor level under the flow. -/
theorem landingOfBox_self {f : M → ℝ} {p : M} {D : WindowDatum f p}
    (hsgn : D.s₁ D.j = - D.s₂ D.j)
    (φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (Zs : M → ℂ) (lam0 : ℝ)
    (hlam0 : lam0 = D.ρ D.j / 8)
    (hsrc : φ'.source = (D.φ D.j).source)
    (hball : ∀ r : ℝ, modelBall φ' r = modelBall (D.φ D.j) r)
    (hZs : ∀ y : M, Zs y = (φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + ((Zs y) ^ 2).re)
    (hODE : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      HasDerivAt (fun σ : ℝ => φ' (D.Φ (σ, y)) 0)
        (chartMult lam0 (‖φ' (D.Φ (t, y))‖ ^ 2) * ((1 : ℝ) * φ' (D.Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => φ' (D.Φ (σ, y)) 1)
        (chartMult lam0 (‖φ' (D.Φ (t, y))‖ ^ 2) * ((-1 : ℝ) * φ' (D.Φ (t, y)) 1)) t)
    (him : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      ((Zs (D.Φ (t, y))) ^ 2).im = ((Zs y) ^ 2).im)
    {η c₀ : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hc₀ : 1 < c₀)
    (hsep : (D.ρ D.j / 8) ^ 2 * η < 2 * D.ηd)
    {x : M}
    (hbox : x ∉ modelBall (D.φ D.j) (D.ρ D.j) ∨
      c₀ * lam0 ^ 2 ≤ |((Zs x) ^ 2).im|)
    (hband : f x ∈ Set.Ioo (f p - lam0 ^ 2 * η) (f p + lam0 ^ 2 * η)) :
    f (D.Φ (f p - lam0 ^ 2 * η - f x, x)) = f p - lam0 ^ 2 * η :=
  swlLandingOfBox D hsgn φ' Zs lam0 hlam0 hsrc hball hZs hlev hODE him hη hη' hc₀ hsep hbox hband

/-! ## The target -/

theorem saddleWindow_legality {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hsgn : D.s₁ D.j = - D.s₂ D.j)
    {η δ c₀ : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1 / 10)
    (hc₀ : 2 - 2 * δ < c₀) (hc₀' : c₀ < 2)
    (hsep : (D.ρ D.j / 8) ^ 2 * η < 2 * D.ηd) :
    ∃ (φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (Zs Z : M → ℂ) (lam0 a : ℝ),
      0 < lam0 ∧ lam0 = D.ρ D.j / 8 ∧ a = f p - lam0 ^ 2 * η ∧
      φ'.source = (D.φ D.j).source ∧
      (∀ r : ℝ, Work.Drive.N2.modelBall φ' r = Work.Drive.N2.modelBall (D.φ D.j) r) ∧
      (∀ y : M, Zs y = (φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I) ∧
      (∀ y : M, Zs y = (lam0 : ℂ) * Z y) ∧
      ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z (D.φ D.j).source ∧
      Set.InjOn Z (D.φ D.j).source ∧
      (∀ x ∈ (D.φ D.j).source,
        Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ ℂ) Z x)) ∧
      (∀ y ∈ (D.φ D.j).source, f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re) ∧
      (∀ y ∈ (D.φ D.j).source, f y = f p + ((Zs y) ^ 2).re) ∧
      (∀ x : M, (x ∉ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) ∨
          c₀ ≤ |((Z x) ^ 2).im|) →
        f x ∈ Set.Ioo a (a + 2 * lam0 ^ 2 * η) →
        f (Work.Drive.N2.footMap D.Φ f a x) = a) ∧
      (∀ x : M, x ∈ (D.φ D.j).source → Z x ∈ Work.Drive.N2.saddleCollar η δ →
        Work.Drive.N2.footMap D.Φ f a x ∈ (D.φ D.j).source ∧
        f (Work.Drive.N2.footMap D.Φ f a x) = a ∧
        Z (Work.Drive.N2.footMap D.Φ f a x) = Work.Drive.N2.saddlePsi η δ (Z x)) := by
  obtain ⟨φ', Zs, Z, lam0, hlam0pos, hlam0, hsrc, hball, hZs, hZrel, hZsm, hZinj, hZimm,
    hlevZ, hlevZs, hODE, him⟩ := Work.Drive.N2.saddlePack D hsgn
  refine ⟨φ', Zs, Z, lam0, f p - lam0 ^ 2 * η, hlam0pos, hlam0, rfl, hsrc, hball, hZs, hZrel,
    hZsm, hZinj, hZimm, hlevZ, hlevZs, ?_, ?_⟩
  · intro x hbox hband
    have hlam0ne : lam0 ≠ 0 := ne_of_gt hlam0pos
    have hbox' : x ∉ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) ∨
        c₀ * lam0 ^ 2 ≤ |((Zs x) ^ 2).im| := by
      rcases hbox with h | h
      · exact Or.inl h
      · refine Or.inr ?_
        have h1 : ((Zs x) ^ 2).im = lam0 ^ 2 * ((Z x) ^ 2).im := swl_im_sq_eq_div (hZrel x)
        rw [h1, abs_mul, abs_of_nonneg (sq_nonneg lam0)]
        have h2 : c₀ * lam0 ^ 2 = lam0 ^ 2 * c₀ := by ring
        rw [h2]
        exact mul_le_mul_of_nonneg_left h (sq_nonneg lam0)
    have hband' : f x ∈ Set.Ioo (f p - lam0 ^ 2 * η) (f p + lam0 ^ 2 * η) := by
      have h : (f p - lam0 ^ 2 * η) + 2 * lam0 ^ 2 * η = f p + lam0 ^ 2 * η := by ring
      simpa [h] using hband
    have h := landingOfBox_self (D := D) hsgn φ' Zs lam0 hlam0 hsrc hball hZs hlevZs hODE him
      hη hη' (by linarith) hsep hbox' hband'
    simpa [Work.Drive.N2.footMap] using h
  · intro x hxsrc hcol
    have hxsrc' : x ∈ φ'.source := by rw [hsrc]; exact hxsrc
    have hlev' : ∀ y ∈ φ'.source, f y = f p + ((Zs y) ^ 2).re :=
      fun y hy => hlevZs y (by rw [← hsrc]; exact hy)
    have h := saddleCollarRow (D := D) hsgn φ' Zs Z lam0 hlam0 hsrc hball hZs hZrel hlev'
      hODE him hη hη' hδ hδ' hsep hxsrc' hcol
    refine ⟨?_, h.2.1, h.2.2⟩
    rw [← hsrc]
    exact h.1

end Work.Drive.N2
