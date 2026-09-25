import Mathlib
import Submission.Work.NN.Core.TelTwoDF.exists_complexification_hol_open
import Submission.Work.NN.Core.TelTwoDF.fibrePrimitiveAux
import Submission.Work.NN.Core.TelTwoDF.intervalIntegral_analyticOn

/-!
# The local fibre-wise `∂̄`-Poincaré lemma for real analytic data

`Work.NN.Core.TelTwoDF.exists_analytic_fibre_dbar_primitive`: a real analytic function `E` on an
open set `Ω ⊆ ℂⁿ × ℂ` has, near every point `q ∈ Ω`, a real analytic fibre-wise `∂̄`-primitive `A`
on a neighbourhood `U ∋ q` with

  `E r = ∂̄_w (A (r.1, ·)) r.2`   for all `r ∈ U`.

The proof combines
* `exists_complexification_hol_open`: the holomorphic complexification `Φ` of `E` at `q`, with
  `Φ (r, conj (r.2 - q.2)) = E r` near `q`;
* `analyticOn_fibrePrimitive` below: real analyticity of the primitive
  `A r = conj (r.2 - q.2) * ∫₀¹ Φ (r, t * conj (r.2 - q.2)) dt`;
* `dbarC_fibrePrimitive` (`fibrePrimitiveAux`): `∂̄_w A = Φ (·, conj (· - q.2)) = E`.
-/

namespace Work.NN.Core.TelTwoDF

open Set Metric
open scoped Topology

noncomputable section

/-- **Real analyticity of the fibre primitive.**
If `Φ` is real analytic on `V` and the fibre segment `t ↦ (x, t * conj (x.2 - c))` stays in `V`
for `t ∈ (-1, 2)` and `x ∈ U`, then `x ↦ conj (x.2 - c) * ∫₀¹ Φ (x, t * conj (x.2 - c)) dt` is
real analytic on `U`. -/
theorem analyticOn_fibrePrimitive {n : ℕ} {Φ : ((Fin n → ℂ) × ℂ) × ℂ → ℂ}
    {V : Set (((Fin n → ℂ) × ℂ) × ℂ)} {c : ℂ}
    {U : Set ((Fin n → ℂ) × ℂ)} (hU : IsOpen U)
    (hΦ : AnalyticOn ℝ Φ V)
    (hmaps : ∀ x ∈ U, ∀ t ∈ Set.Ioo (-1 : ℝ) 2,
      (((x.1, x.2), t * star (x.2 - c)) : ((Fin n → ℂ) × ℂ) × ℂ) ∈ V) :
    AnalyticOn ℝ (fun x : (Fin n → ℂ) × ℂ =>
      star (x.2 - c) * ∫ t in (0:ℝ)..1, Φ ((x.1, x.2), t * star (x.2 - c))) U := by
  have hsub2 : AnalyticOn ℝ (fun z : ((Fin n → ℂ) × ℂ) × ℝ => z.1.2 - c)
      (U ×ˢ Set.Ioo (-1 : ℝ) 2) := by
    have hs : AnalyticOn ℝ (fun z : ((Fin n → ℂ) × ℂ) × ℝ => z.1.2)
        (U ×ˢ Set.Ioo (-1 : ℝ) 2) :=
      ContinuousLinearMap.analyticOn
        ((ContinuousLinearMap.snd ℝ (Fin n → ℂ) ℂ).comp
          (ContinuousLinearMap.fst ℝ ((Fin n → ℂ) × ℂ) ℝ)) _
    exact hs.sub analyticOn_const
  have hst : AnalyticOn ℝ (fun z : ((Fin n → ℂ) × ℂ) × ℝ => star (z.1.2 - c))
      (U ×ˢ Set.Ioo (-1 : ℝ) 2) :=
    (ContinuousLinearMap.analyticOn ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) Set.univ).comp
      hsub2 (fun z _ => Set.mem_univ _)
  have hφ : AnalyticOn ℝ (fun z : ((Fin n → ℂ) × ℂ) × ℝ =>
      (((z.1.1, z.1.2), (z.2 : ℂ) * star (z.1.2 - c)) : ((Fin n → ℂ) × ℂ) × ℂ))
      (U ×ˢ Set.Ioo (-1 : ℝ) 2) := by
    refine AnalyticOn.prod ?_ ?_
    · exact ContinuousLinearMap.analyticOn (ContinuousLinearMap.fst ℝ ((Fin n → ℂ) × ℂ) ℝ) _
    · refine AnalyticOn.mul ?_ hst
      exact ContinuousLinearMap.analyticOn
        ((Complex.ofRealCLM).comp (ContinuousLinearMap.snd ℝ ((Fin n → ℂ) × ℂ) ℝ)) _
  have hF : AnalyticOn ℝ (fun z : ((Fin n → ℂ) × ℂ) × ℝ =>
      Φ ((z.1.1, z.1.2), (z.2 : ℂ) * star (z.1.2 - c))) (U ×ˢ Set.Ioo (-1 : ℝ) 2) :=
    hΦ.comp hφ (fun z hz => hmaps z.1 hz.1 z.2 hz.2)
  have hF' : AnalyticOn ℝ (fun z : ((Fin n → ℂ) × ℂ) × ℝ =>
      Φ ((z.1.1, z.1.2), (z.2 : ℂ) * star (z.1.2 - c)))
      (U ×ˢ Set.Ioo (0 - 1 : ℝ) (1 + 1)) := by
    have hEq : (U ×ˢ Set.Ioo (0 - 1 : ℝ) (1 + 1)) = (U ×ˢ Set.Ioo (-1 : ℝ) 2) := by
      congr 1
      ext t
      simp only [Set.mem_Ioo]
      constructor <;> intro h <;> constructor <;> linarith
    rw [hEq]; exact hF
  have hG : AnalyticOn ℝ (fun x : (Fin n → ℂ) × ℂ =>
      ∫ t in (0:ℝ)..1, Φ ((x.1, x.2), t * star (x.2 - c))) U :=
    intervalIntegral_analyticOn (a := (0:ℝ)) (b := 1) (ε := 1)
      (F := fun z : ((Fin n → ℂ) × ℂ) × ℝ => Φ ((z.1.1, z.1.2), (z.2 : ℂ) * star (z.1.2 - c)))
      hU (by norm_num) (by norm_num) hF'
  have hsub : AnalyticOn ℝ (fun x : (Fin n → ℂ) × ℂ => x.2 - c) U := by
    have hs : AnalyticOn ℝ (fun x : (Fin n → ℂ) × ℂ => x.2) U :=
      ContinuousLinearMap.analyticOn (ContinuousLinearMap.snd ℝ (Fin n → ℂ) ℂ) U
    exact hs.sub analyticOn_const
  have hstar2 : AnalyticOn ℝ (fun x : (Fin n → ℂ) × ℂ => star (x.2 - c)) U :=
    (ContinuousLinearMap.analyticOn ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) Set.univ).comp
      hsub (fun z _ => Set.mem_univ _)
  exact hstar2.mul hG

theorem exists_analytic_fibre_dbar_primitive {n : ℕ} {Ω : Set ((Fin n → ℂ) × ℂ)}
    (hΩ : IsOpen Ω) {E : ((Fin n → ℂ) × ℂ) → ℂ} (hE : AnalyticOn ℝ E Ω)
    {q : (Fin n → ℂ) × ℂ} (hq : q ∈ Ω) :
    ∃ U : Set ((Fin n → ℂ) × ℂ), IsOpen U ∧ q ∈ U ∧ U ⊆ Ω ∧
      ∃ A : ((Fin n → ℂ) × ℂ) → ℂ, AnalyticOn ℝ A U ∧
        ∀ r ∈ U, E r = Work.CR.Flat.dbarC (fun w : ℂ => A (r.1, w)) r.2 := by
  obtain ⟨Φ, ρ, hρpos, hΦan, hΦval, hΦhol⟩ := exists_complexification_hol_open hΩ hE hq
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := Metric.isOpen_iff.mp hΩ q hq
  set δ : ℝ := min δ₀ ρ / 2 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; have := lt_min hδ₀pos hρpos; linarith
  have hδδ₀ : δ ≤ δ₀ := by
    rw [hδdef]; have := min_le_left δ₀ ρ; linarith
  have hδρ : δ < ρ := by
    rw [hδdef]; have := min_le_right δ₀ ρ; linarith
  refine ⟨Metric.ball q δ, Metric.isOpen_ball, Metric.mem_ball_self hδpos, ?_, ?_⟩
  · intro x hx
    exact hδ₀sub (Metric.ball_subset_ball hδδ₀ hx)
  · refine ⟨fun x : (Fin n → ℂ) × ℂ =>
        star (x.2 - q.2) * ∫ t in (0:ℝ)..1, Φ ((x.1, x.2), t * star (x.2 - q.2)), ?_, ?_⟩
    · have hmaps : ∀ x ∈ Metric.ball q δ, ∀ t ∈ Set.Ioo (-1 : ℝ) 2,
          (((x.1, x.2), t * star (x.2 - q.2)) : ((Fin n → ℂ) × ℂ) × ℂ) ∈
            (Ω ∩ Metric.ball q (2 * ρ)) ×ˢ Metric.ball (0 : ℂ) (2 * ρ) := by
        intro x hx t ht
        have hxδ : dist x q < δ := hx
        have hxΩ : x ∈ Ω := hδ₀sub (Metric.ball_subset_ball hδδ₀ hx)
        refine ⟨⟨hxΩ, ?_⟩, ?_⟩
        · rw [Metric.mem_ball]; show dist x q < 2 * ρ; linarith
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        have htd : |t| < 2 := by
          rw [abs_lt]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
        have hxd : ‖x.2 - q.2‖ < ρ := by
          have h1 : dist x.2 q.2 ≤ dist x q := by
            rw [Prod.dist_eq]; exact le_max_right _ _
          rw [dist_eq_norm] at h1
          linarith
        have hn : ‖(t : ℂ) * star (x.2 - q.2)‖ = |t| * ‖x.2 - q.2‖ := by
          rw [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
        rw [hn]
        nlinarith [abs_nonneg t, norm_nonneg (x.2 - q.2)]
      exact analyticOn_fibrePrimitive (U := Metric.ball q δ)
        (V := (Ω ∩ Metric.ball q (2 * ρ)) ×ˢ Metric.ball (0 : ℂ) (2 * ρ))
        (c := q.2) Metric.isOpen_ball hΦan hmaps
    · intro r hr
      have hrδ : dist r q < δ := hr
      have hr2ρ : dist r q < 2 * ρ := by linarith
      have hτ : ‖star (r.2 - q.2)‖ < ρ := by
        have h1 : dist r.2 q.2 ≤ dist r q := by
          rw [Prod.dist_eq]; exact le_max_right _ _
        rw [dist_eq_norm] at h1
        rw [norm_star]
        linarith
      rw [← hΦval r hr2ρ]
      exact (dbarC_fibrePrimitive (z := r.1) (w₀ := r.2) (c := q.2) (hΦhol r hr2ρ) hτ).symm
end

end Work.NN.Core.TelTwoDF
