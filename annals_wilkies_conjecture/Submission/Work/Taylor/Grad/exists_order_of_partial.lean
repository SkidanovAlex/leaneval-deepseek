import Mathlib
import Submission.Work.WilE3.Taylor.Grad.PolarDefs
import Submission.Work.WilE3.API.hasFDerivAt_eaEval
import Submission.Work.WilE3.eaEval_analytic
import Submission.Work.Taylor.Grad.grad_eaEval

/-!
  annals_wilkies_conjecture, AREA Taylor / Grad: **some partial derivative has finite order along
  the arc**.

  Let `γ` be an analytic arc through `y = γ 0` with `Φ y = 0` and `Φ (γ t) > 0` for all small
  `t > 0`.  Then not all of the partial derivatives `∂ᵢΦ` can vanish to infinite order along `γ`:
  if they did, then `t ↦ Φ (γ t)` would be eventually constant (its derivative, given by the
  one-variable chain rule, would vanish on a neighbourhood of `0`), hence constantly equal to
  `Φ y = 0`, contradicting `Φ (γ t) > 0`.

  Consequently some `∂ᵢΦ ∘ γ` has a *finite* vanishing order, which is exactly what the
  `HasLoj`/`badSeq` order bookkeeping of area Taylor consumes: a partial derivative that is not
  identically zero near `0` may be factored as `t ^ n` times a unit, and the estimates compare the
  orders of `Φ ∘ γ` and of the gradient `∇Φ ∘ γ`.
-/

set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped Topology

namespace Work.Taylor.Grad

/-- **One-variable chain rule along a curve, in `deriv` form.**  If `γ` is differentiable at `t`
with tangent vector `deriv γ t`, then the derivative of `s ↦ eaEval c Φ (γ s)` at `t` is the
contraction of the symbolic gradient `∑ᵢ ∂ᵢΦ (γ t) • projᵢ` with that tangent vector. -/
lemma deriv_eaEval_comp {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (Φ : WilkiesDesign.E.EAPoly k r) (γ : ℝ → Fin k → ℝ) {t : ℝ}
    (h : HasDerivAt γ (deriv γ t) t) :
    deriv (fun s : ℝ => WilkiesDesign.E.eaEval c Φ (γ s)) t
      = (∑ i : Fin k, WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i Φ) (γ t) •
          (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)) (deriv γ t) := by
  have h2 : HasFDerivAt (fun z : Fin k → ℝ => WilkiesDesign.E.eaEval c Φ z)
      (∑ i : Fin k, WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i Φ) (γ t) •
        (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)) (γ t) :=
    Work.WilE3.API.hasFDerivAt_eaEval c Φ (γ t)
  simpa [Function.comp_def] using (h2.comp_hasDerivAt t h).deriv

theorem exists_order_of_partial {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (Φ : WilkiesDesign.E.EAPoly k r) (y : Fin k → ℝ) (γ : ℝ → Fin k → ℝ)
    (hγ : AnalyticAt ℝ γ 0) (hγ0 : γ 0 = y) (hy : WilkiesDesign.E.eaEval c Φ y = 0)
    (hpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < WilkiesDesign.E.eaEval c Φ (γ t)) :
    ∃ (i : Fin k) (n : ℕ),
      analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i Φ) (γ t)) 0
        = n := by
  -- Suppose, for contradiction, that *every* partial derivative vanishes to infinite order.
  by_contra hcon
  have hcon' : ∀ (i : Fin k) (n : ℕ),
      analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i Φ) (γ t)) 0
        ≠ (n : ℕ∞) := fun i n hn => hcon ⟨i, n, hn⟩
  have htop : ∀ i : Fin k,
      analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i Φ) (γ t)) 0
        = ⊤ := by
    intro i
    by_contra h
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
    exact hcon' i n hn.symm
  -- Infinite order means: the function vanishes on a neighbourhood of `0`.
  have hzero : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i : Fin k,
      WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i Φ) (γ t) = 0 :=
    Filter.eventually_all.mpr fun i => analyticOrderAt_eq_top.mp (htop i)
  -- Hence `t ↦ Φ (γ t)` has vanishing derivative near `0` (one-variable chain rule).
  have hderiv : ∀ᶠ t in 𝓝 (0 : ℝ),
      deriv (fun s : ℝ => WilkiesDesign.E.eaEval c Φ (γ s)) t = 0 := by
    filter_upwards [hγ.eventually_analyticAt, hzero] with t ht hz
    rw [deriv_eaEval_comp c Φ γ ht.differentiableAt.hasDerivAt]
    simp [hz]
  -- Combine with the analyticity of `γ`, and extract a ball on which everything holds.
  have hboth : ∀ᶠ t in 𝓝 (0 : ℝ),
      (deriv (fun s : ℝ => WilkiesDesign.E.eaEval c Φ (γ s)) t = 0) ∧
      (∀ i : Fin k, WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i Φ) (γ t) = 0) ∧
      AnalyticAt ℝ γ t := hderiv.and (hzero.and hγ.eventually_analyticAt)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hboth
  -- On that ball, `t ↦ Φ (γ t)` is differentiable with vanishing derivative, hence constant.
  have hpre : IsPreconnected (Metric.ball (0 : ℝ) δ) := by
    exact Metric.isPreconnected_ball (x := (0 : ℝ)) (r := δ)
  have hopen : IsOpen (Metric.ball (0 : ℝ) δ) := Metric.isOpen_ball
  have hdiff : DifferentiableOn ℝ (fun s : ℝ => WilkiesDesign.E.eaEval c Φ (γ s))
      (Metric.ball (0 : ℝ) δ) := by
    intro t ht
    have hγt : AnalyticAt ℝ γ t := (hδ ht).2.2
    exact ((Work.WilE3.eaEval_analytic c Φ (γ t)).comp hγt).differentiableAt.differentiableWithinAt
  have heq : Set.EqOn (deriv (fun s : ℝ => WilkiesDesign.E.eaEval c Φ (γ s))) 0
      (Metric.ball (0 : ℝ) δ) := by
    intro t ht
    exact (hδ ht).1
  have h0mem : (0 : ℝ) ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_zero]
    exact hδpos
  have hconst : ∀ t ∈ Metric.ball (0 : ℝ) δ,
      WilkiesDesign.E.eaEval c Φ (γ t) = WilkiesDesign.E.eaEval c Φ (γ 0) := by
    intro t ht
    exact IsOpen.is_const_of_deriv_eq_zero hopen hpre hdiff heq ht h0mem
  -- The positivity on the right of `0` contradicts the constancy.
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhdsWithin_iff.mp hpos
  set t₀ : ℝ := min δ ε / 2 with ht₀def
  have hmin : 0 < min δ ε := lt_min hδpos hεpos
  have ht₀pos : 0 < t₀ := by rw [ht₀def]; linarith
  have ht₀lt : t₀ < min δ ε := by rw [ht₀def]; linarith
  have ht₀δ : t₀ < δ := lt_of_lt_of_le ht₀lt (min_le_left _ _)
  have ht₀ε : t₀ < ε := lt_of_lt_of_le ht₀lt (min_le_right _ _)
  have ht₀ballδ : t₀ ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht₀pos]; exact ht₀δ
  have ht₀ballε : t₀ ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht₀pos]; exact ht₀ε
  have hone : 0 < WilkiesDesign.E.eaEval c Φ (γ t₀) :=
    hε ⟨ht₀ballε, Set.mem_Ioi.mpr ht₀pos⟩
  have hzero₀ : WilkiesDesign.E.eaEval c Φ (γ t₀) = 0 := by
    calc WilkiesDesign.E.eaEval c Φ (γ t₀) = WilkiesDesign.E.eaEval c Φ (γ 0) :=
          hconst t₀ ht₀ballδ
      _ = WilkiesDesign.E.eaEval c Φ y := by rw [hγ0]
      _ = 0 := hy
  linarith

end Work.Taylor.Grad
