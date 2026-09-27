import Mathlib
import Submission.Work.Embedding.deriv_two_norm_sq_line

namespace Work.Embedding

open Metric Set

/-- A point of the segment between `c` and `c + d` lies in any ball containing both endpoints. -/
lemma distSq_segment_mem_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u₀ : E} {ρ : ℝ} {c d : E}
    (hc : c ∈ Metric.ball u₀ ρ) (hcd : c + d ∈ Metric.ball u₀ ρ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    c + t • d ∈ Metric.ball u₀ ρ := by
  have h1 : (1 - t) • c + t • (c + d) ∈ Metric.ball u₀ ρ :=
    (convex_ball u₀ ρ) hc hcd (by linarith [ht.2]) (by linarith [ht.1]) (by ring)
  have heq : (1 - t) • c + t • (c + d) = c + t • d := by
    rw [smul_add, ← add_assoc, ← add_smul, sub_add_cancel, one_smul]
  rw [heq] at h1
  exact h1

/-- The squared distance to a `C²` map is continuous along a segment whose endpoints lie in the
ball. -/
lemma continuousOn_distSq_segment {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ψ : E → F} {u₀ : E} {ρ : ℝ} (_hρ : 0 < ρ) {w : F} {c d : E}
    (hψ : ∀ u ∈ Metric.ball u₀ ρ, ContDiffAt ℝ 2 ψ u)
    (hc : c ∈ Metric.ball u₀ ρ) (hcd : c + d ∈ Metric.ball u₀ ρ) :
    ContinuousOn (fun t : ℝ => ‖w - ψ (c + t • d)‖ ^ 2) (Icc 0 1) := by
  intro t ht
  have hmem : c + t • d ∈ Metric.ball u₀ ρ := distSq_segment_mem_ball hc hcd ht
  have hlin : ContinuousAt (fun s : ℝ => c + s • d) t := by fun_prop
  have hcomp : ContinuousAt (fun s : ℝ => ψ (c + s • d)) t :=
    ContinuousAt.comp (x := t) (f := fun s : ℝ => c + s • d) (g := ψ)
      ((hψ _ hmem).continuousAt) hlin
  have hout : ContinuousAt (fun s : ℝ => ‖w - ψ (c + s • d)‖ ^ 2) t :=
    (((continuousAt_const).sub hcomp).norm).pow 2
  simpa using hout.continuousWithinAt

/-- **Pointwise second-order estimate.**  At every point `u` of the ball and for every nonzero
direction `d`, the second-order quantity
`‖Dψ u d‖² - ⟪w - ψ u, D²ψ u (d,d)⟫` is positive.  This is the algebraic core of the strict
convexity estimate: the lower bound `κ` on `Dψ` beats the upper bound `C` on `D²ψ`, because
`‖w - ψ u‖ < δ + Lρ`. -/
lemma distSq_secondOrder_pos {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ψ : E → F} {u₀ : E} {ρ κ C L δ : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) (hC : 0 < C) (hL : 0 < L)
    (hδρ : δ + L * ρ < κ ^ 2 / C)
    (hκ' : ∀ u ∈ Metric.ball u₀ ρ, ∀ d : E, κ * ‖d‖ ≤ ‖fderiv ℝ ψ u d‖)
    (hC' : ∀ u ∈ Metric.ball u₀ ρ, ∀ d₁ d₂ : E,
      ‖(fderiv ℝ (fderiv ℝ ψ) u) d₁ d₂‖ ≤ C * ‖d₁‖ * ‖d₂‖)
    (hLip : ∀ u ∈ Metric.ball u₀ ρ, ∀ v ∈ Metric.ball u₀ ρ, ‖ψ u - ψ v‖ ≤ L * ‖u - v‖)
    {w : F} (hw : ‖w - ψ u₀‖ < δ)
    {u : E} (hu : u ∈ Metric.ball u₀ ρ) {d : E} (hd : d ≠ 0) :
    0 < 2 * (‖fderiv ℝ ψ u d‖ ^ 2 -
      inner ℝ (w - ψ u) ((fderiv ℝ (fderiv ℝ ψ) u) d d)) := by
  have hu₀ : u₀ ∈ Metric.ball u₀ ρ := Metric.mem_ball_self hρ
  have hdist : ‖u₀ - u‖ < ρ := by
    have h := hu
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at h
    exact h
  -- bound on `‖w - ψ u‖`
  have hA : ‖w - ψ u‖ < δ + L * ρ := by
    have hsplit : w - ψ u = (w - ψ u₀) + (ψ u₀ - ψ u) := by abel
    have h1 : ‖w - ψ u‖ ≤ ‖w - ψ u₀‖ + ‖ψ u₀ - ψ u‖ := by
      rw [hsplit]; exact norm_add_le _ _
    have h2 : ‖ψ u₀ - ψ u‖ ≤ L * ‖u₀ - u‖ := hLip u₀ hu₀ u hu
    have h3 : L * ‖u₀ - u‖ < L * ρ := mul_lt_mul_of_pos_left hdist hL
    linarith
  -- bound on the inner product
  have hinner : inner ℝ (w - ψ u) ((fderiv ℝ (fderiv ℝ ψ) u) d d)
      ≤ (δ + L * ρ) * (C * ‖d‖ * ‖d‖) := by
    refine le_trans (real_inner_le_norm _ _) ?_
    refine le_trans (mul_le_mul_of_nonneg_left (hC' u hu d d) (norm_nonneg _)) ?_
    exact mul_le_mul_of_nonneg_right hA.le (by positivity)
  -- lower bound on `‖Dψ u d‖²`
  have hsq : κ ^ 2 * ‖d‖ ^ 2 ≤ ‖fderiv ℝ ψ u d‖ ^ 2 := by
    have h1 := hκ' u hu d
    have h2 : 0 ≤ κ * ‖d‖ := mul_nonneg hκ.le (norm_nonneg _)
    nlinarith [norm_nonneg (fderiv ℝ ψ u d)]
  have hkey : (δ + L * ρ) * C < κ ^ 2 := by
    have h := mul_lt_mul_of_pos_right hδρ hC
    rwa [div_mul_cancel₀ _ hC.ne'] at h
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hd2 : 0 < ‖d‖ ^ 2 := by positivity
  have hprod : (δ + L * ρ) * (C * ‖d‖ * ‖d‖) < κ ^ 2 * ‖d‖ ^ 2 := by
    nlinarith [hd2, hkey]
  have hlt : (δ + L * ρ) * (C * ‖d‖ * ‖d‖) < ‖fderiv ℝ ψ u d‖ ^ 2 :=
    lt_of_lt_of_le hprod hsq
  have hpos : 0 < ‖fderiv ℝ ψ u d‖ ^ 2 -
      inner ℝ (w - ψ u) ((fderiv ℝ (fderiv ℝ ψ) u) d d) :=
    sub_pos.mpr (lt_of_le_of_lt hinner hlt)
  linarith

/-- Second derivative of the squared distance along a segment is positive at every point of the
segment. -/
lemma distSq_secondDeriv_pos_segment {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ψ : E → F} {u₀ : E} {ρ κ C L δ : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) (hC : 0 < C) (hL : 0 < L)
    (hδρ : δ + L * ρ < κ ^ 2 / C)
    (hψ : ∀ u ∈ Metric.ball u₀ ρ, ContDiffAt ℝ 2 ψ u)
    (hκ' : ∀ u ∈ Metric.ball u₀ ρ, ∀ d : E, κ * ‖d‖ ≤ ‖fderiv ℝ ψ u d‖)
    (hC' : ∀ u ∈ Metric.ball u₀ ρ, ∀ d₁ d₂ : E,
      ‖(fderiv ℝ (fderiv ℝ ψ) u) d₁ d₂‖ ≤ C * ‖d₁‖ * ‖d₂‖)
    (hLip : ∀ u ∈ Metric.ball u₀ ρ, ∀ v ∈ Metric.ball u₀ ρ, ‖ψ u - ψ v‖ ≤ L * ‖u - v‖)
    {w : F} (hw : ‖w - ψ u₀‖ < δ)
    {c d : E} (hc : c ∈ Metric.ball u₀ ρ) (hcd : c + d ∈ Metric.ball u₀ ρ) (hd : d ≠ 0) :
    ∀ t ∈ Icc (0 : ℝ) 1, 0 < deriv^[2] (fun t : ℝ => ‖w - ψ (c + t • d)‖ ^ 2) t := by
  intro t ht
  have hmem : c + t • d ∈ Metric.ball u₀ ρ := distSq_segment_mem_ball hc hcd ht
  rw [deriv_two_norm_sq_line ψ w c d t (hψ _ hmem)]
  exact distSq_secondOrder_pos hρ hκ hC hL hδρ hκ' hC' hLip hw hmem hd

/-- **Strict convexity along a segment.**  With the bounds of the theorem, the squared distance
function is strictly convex along the segment from `c` to `c + d`. -/
lemma distSq_segment_strict_ineq {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ψ : E → F} {u₀ : E} {ρ κ C L δ : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) (hC : 0 < C) (hL : 0 < L)
    (hδρ : δ + L * ρ < κ ^ 2 / C)
    (hψ : ∀ u ∈ Metric.ball u₀ ρ, ContDiffAt ℝ 2 ψ u)
    (hκ' : ∀ u ∈ Metric.ball u₀ ρ, ∀ d : E, κ * ‖d‖ ≤ ‖fderiv ℝ ψ u d‖)
    (hC' : ∀ u ∈ Metric.ball u₀ ρ, ∀ d₁ d₂ : E,
      ‖(fderiv ℝ (fderiv ℝ ψ) u) d₁ d₂‖ ≤ C * ‖d₁‖ * ‖d₂‖)
    (hLip : ∀ u ∈ Metric.ball u₀ ρ, ∀ v ∈ Metric.ball u₀ ρ, ‖ψ u - ψ v‖ ≤ L * ‖u - v‖)
    {w : F} (hw : ‖w - ψ u₀‖ < δ)
    {c d : E} (hc : c ∈ Metric.ball u₀ ρ) (hcd : c + d ∈ Metric.ball u₀ ρ) (hd : d ≠ 0)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    ‖w - ψ (a • c + b • (c + d))‖ ^ 2 <
      a * ‖w - ψ c‖ ^ 2 + b * ‖w - ψ (c + d)‖ ^ 2 := by
  have hcont := continuousOn_distSq_segment (F := F) (w := w) hρ hψ hc hcd
  have hpos := distSq_secondDeriv_pos_segment hρ hκ hC hL hδρ hψ hκ' hC' hLip hw hc hcd hd
  have hcvx : StrictConvexOn ℝ (Icc (0 : ℝ) 1)
      (fun t : ℝ => ‖w - ψ (c + t • d)‖ ^ 2) :=
    strictConvexOn_of_deriv2_pos' (convex_Icc (0 : ℝ) 1) hcont hpos
  obtain ⟨_, hcvx'⟩ := hcvx
  have h := hcvx' (by norm_num : (0 : ℝ) ∈ Icc 0 1) (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    (by norm_num : (0 : ℝ) ≠ 1) ha hb hab
  have hkey : a • c + b • (c + d) = c + b • d := by
    rw [smul_add, ← add_assoc, ← add_smul, hab, one_smul]
  have h' : ‖w - ψ (c + b • d)‖ ^ 2 <
      a * ‖w - ψ c‖ ^ 2 + b * ‖w - ψ (c + d)‖ ^ 2 := by
    simpa [smul_eq_mul] using h
  rwa [← hkey] at h'

/-- **Core convexity estimate.**  If `ψ : E → F` is `C²` on the ball `ball u₀ ρ`, if `Dψ` is
uniformly bounded below by `κ` (`κ‖d‖ ≤ ‖Dψ u d‖`), if the second derivative of `ψ` is bounded by
`C` on the ball, and if `ψ` is `L`-Lipschitz on the ball, then for every `w` with
`‖w - ψ u₀‖ < δ`, where `δ + Lρ < κ²/C`, the function `u ↦ ‖w - ψ u‖²` is *strictly convex* on the
ball `ball u₀ ρ`.  (Consequently it has at most one minimum there.) -/
theorem strictConvexOn_norm_sub_of_bounds {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ψ : E → F} {u₀ : E} {ρ κ C L δ : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) (hC : 0 < C) (hL : 0 < L)
    (hδρ : δ + L * ρ < κ ^ 2 / C)
    (hψ : ∀ u ∈ Metric.ball u₀ ρ, ContDiffAt ℝ 2 ψ u)
    (hκ' : ∀ u ∈ Metric.ball u₀ ρ, ∀ d : E, κ * ‖d‖ ≤ ‖fderiv ℝ ψ u d‖)
    (hC' : ∀ u ∈ Metric.ball u₀ ρ, ∀ d₁ d₂ : E,
      ‖(fderiv ℝ (fderiv ℝ ψ) u) d₁ d₂‖ ≤ C * ‖d₁‖ * ‖d₂‖)
    (hLip : ∀ u ∈ Metric.ball u₀ ρ, ∀ v ∈ Metric.ball u₀ ρ, ‖ψ u - ψ v‖ ≤ L * ‖u - v‖) :
    ∀ w : F, ‖w - ψ u₀‖ < δ →
      StrictConvexOn ℝ (Metric.ball u₀ ρ) (fun u => ‖w - ψ u‖ ^ 2) := by
  intro w hw
  refine ⟨convex_ball u₀ ρ, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hd : y - x ≠ 0 := by
    rw [sub_ne_zero]
    exact hxy.symm
  have hxdy : x + (y - x) ∈ Metric.ball u₀ ρ := by
    have h : x + (y - x) = y := by abel
    rw [h]
    exact hy
  have h := distSq_segment_strict_ineq hρ hκ hC hL hδρ hψ hκ' hC' hLip hw hx hxdy hd ha hb hab
  have e1 : x + (y - x) = y := by abel
  rw [e1] at h
  exact h

end Work.Embedding
