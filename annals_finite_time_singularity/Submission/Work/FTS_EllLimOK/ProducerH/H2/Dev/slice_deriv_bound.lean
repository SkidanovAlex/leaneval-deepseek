import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Basic
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDeriv.second_theta_deriv_le_Xn6
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDeriv.slice_package_bounds
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.Trace
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgRate
import Submission.Work.FTS_RegExport.RXT.landau_1d

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2.Dev

/-!
# `H2/Dev/slice_deriv_bound` — the pointwise slice data of `E g` on a box

For a stream function `E g` carrying the level-`8` existence class (the hypothesis `Ctx α Ce E`),
and for a box `[a₀,b₀] × (0,π/2)` with `0 < a₀ ≤ b₀`, we bound the angular slice
`S := fun θ => E g z θ` uniformly in `g` and in `z ∈ [a₀,b₀]`:

* `|∂_θS| ≤ C₂ · Xn₆(g)` (the *first* angular derivative, uniformly on the whole strip);
* `|S| ≤ C₂ · Xn₆(g) · θ` and `|S| ≤ C₂ · Xn₆(g) · (π/2 − θ)` (the two endpoint rates).

The last two clauses are the `j = 0` instance of `BoxAux.psiDz_rate` (the min-rate of the radial
iterates of `E g`).  The first clause is *not* a consequence of the min-rate alone: it is the
one-dimensional Landau inequality of `FTS_RegExport.RXT.landau_1d`, applied on the interval
`[θ, θ + min θ (π/2−θ)/2]`, where the min-rate bounds the *value* of `S` by `3·C·δ` and
`SecondDeriv.second_theta_deriv_le_Xn6` bounds `∂_θ²S` by `K·Xn₆(g)`; with `δ := min θ (π/2−θ)/2`
this gives `|∂_θS θ| ≤ 2·(3Cδ)/δ + K·Xn₆(g)·δ/2 ≤ (6C + K·π/8)·Xn₆(g)`.
-/

/-- **The one-dimensional Landau bound on the angular strip.**  If `S` is `C²` on `(0,π/2)`,
`|S| ≤ C · min(θ, π/2−θ)` there and `|S''| ≤ B`, then `|S'| ≤ 6C + B·π/8` on `(0,π/2)`.

Proof: at a point `θ`, put `δ := min θ (π/2−θ)/2` and apply the second-order Landau inequality
`landau_1d` on `[θ, θ+δ]`, where `|S| ≤ 3Cδ` (because `min(y,π/2−y) ≤ 3δ` on that interval). -/
theorem deriv_le_of_min_rate {S : ℝ → ℝ} {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hS : ContDiffOn ℝ 2 S (Set.Ioo 0 (Real.pi / 2)))
    (h1 : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      |S t| ≤ C * min t (Real.pi / 2 - t))
    (h2 : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi / 2), |deriv (deriv S) t| ≤ B) :
    ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      |deriv S θ| ≤ 6 * C + B * (Real.pi / 8) := by
  intro θ hθ
  have hθ1 : 0 < θ := hθ.1
  have hθ2 : θ < Real.pi / 2 := hθ.2
  set d : ℝ := min θ (Real.pi / 2 - θ) / 2 with hd_def
  have hdpos : 0 < d := by
    rw [hd_def]
    have : 0 < min θ (Real.pi / 2 - θ) := lt_min hθ1 (by linarith)
    linarith
  have hdle : d ≤ Real.pi / 4 := by
    rw [hd_def]
    have hmin_le : min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 :=
      le_trans (min_le_left _ _) (by linarith)
    linarith
  -- the interval `[θ, θ+d]` sits inside the open strip
  have hright : d < Real.pi / 2 - θ := by
    rw [hd_def]
    have hmin_le : min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 - θ := min_le_right _ _
    linarith
  have hsub : ∀ y ∈ Set.Icc θ (θ + d), y ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := by
    intro y hy
    exact ⟨by linarith [hy.1], by linarith [hy.2, hright]⟩
  -- the value bound on the interval: `min (y) (π/2−y) ≤ 3d`
  have hmin_le : ∀ y ∈ Set.Icc θ (θ + d), min y (Real.pi / 2 - y) ≤ 3 * d := by
    intro y hy
    rcases le_total θ (Real.pi / 2 - θ) with hcase | hcase
    · have hd' : d = θ / 2 := by rw [hd_def, min_eq_left hcase]
      have : y ≤ 3 * d := by rw [hd'] at hy ⊢; linarith [hy.2]
      exact le_trans (min_le_left _ _) this
    · have hd' : d = (Real.pi / 2 - θ) / 2 := by rw [hd_def, min_eq_right hcase]
      have : Real.pi / 2 - y ≤ 3 * d := by rw [hd'] at hy ⊢; linarith [hy.1]
      exact le_trans (min_le_right _ _) this
  have h0 : ∀ y ∈ Set.Icc θ (θ + d), |S y| ≤ 3 * C * d := by
    intro y hy
    calc |S y| ≤ C * min y (Real.pi / 2 - y) := h1 y (hsub y hy)
      _ ≤ C * (3 * d) := mul_le_mul_of_nonneg_left (hmin_le y hy) hC
      _ = 3 * C * d := by ring
  -- differentiability data on the interval
  have hd1 : ∀ y ∈ Set.Icc θ (θ + d), HasDerivAt S (deriv S y) y := by
    intro y hy
    have hy' := hsub y hy
    have hc : ContDiffAt ℝ 2 S y := hS.contDiffAt (isOpen_Ioo.mem_nhds hy')
    exact (hc.differentiableAt (by norm_num)).hasDerivAt
  have hd2 : ∀ y ∈ Set.Icc θ (θ + d), HasDerivAt (deriv S) (deriv (deriv S) y) y := by
    intro y hy
    have hy' := hsub y hy
    have hc : ContDiffAt ℝ 2 S y := hS.contDiffAt (isOpen_Ioo.mem_nhds hy')
    have hc1 : ContDiffAt ℝ 1 (deriv S) y := hc.derivWithin (m := 1) (by norm_num)
    exact (hc1.differentiableAt (by norm_num)).hasDerivAt
  have h2' : ∀ y ∈ Set.Icc θ (θ + d), |deriv (deriv S) y| ≤ B :=
    fun y hy => h2 y (hsub y hy)
  have hkey := Work.FTS_RegExport.RXT.landau_1d (h := S) (x := θ) (δ := d) (M₀ := 3 * C * d) (M₂ := B)
    hdpos hd1 hd2 h0 h2'
  -- `hkey : |deriv S θ| ≤ 2·(3Cd)/d + B·d/2`
  have harith : 2 * (3 * C * d) / d + B * d / 2 ≤ 6 * C + B * (Real.pi / 8) := by
    have hone : 2 * (3 * C * d) / d = 6 * C := by
      field_simp
      ring
    rw [hone]
    have htwo : B * d / 2 ≤ B * (Real.pi / 8) := by
      have hπ : Real.pi / 4 = 2 * (Real.pi / 8) := by ring
      nlinarith [hdle, hB, hdpos]
    linarith
  linarith [hkey, harith]

theorem slice_deriv_bound {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.ProducerH.H2.Ctx α Ce E)
    {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab : a₀ ≤ b₀) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      ∀ z ∈ Set.Icc a₀ b₀,
        (∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
          |deriv (fun θ' => (E g) z θ') θ| ≤ C₂ * Work.FTS.StrongGlobal.Xn6 α g) ∧
        (∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
          |(E g) z θ| ≤ C₂ * Work.FTS.StrongGlobal.Xn6 α g * θ) ∧
        (∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
          |(E g) z θ| ≤ C₂ * Work.FTS.StrongGlobal.Xn6 α g * (Real.pi / 2 - θ)) := by
  obtain ⟨K, hK, hKb⟩ :=
    Work.FTS_EllLimOK.ProducerH.SecondDeriv.second_theta_deriv_le_Xn6 hα hα4 hE ha₀ hab
  obtain ⟨C₁, hC₁, hC₁b⟩ :=
    Work.FTS_EllLimOK.ProducerH.BoxAux.psiDz_rate hα hα4 hE ha₀ hab
  refine ⟨1 + 6 * C₁ + K * (Real.pi / 8) + C₁, ?_, ?_⟩
  · have hπ8 : 0 < Real.pi / 8 := by positivity
    nlinarith [hC₁, mul_pos hK hπ8]
  intro g hg z hz
  have hz0 : 0 < z := lt_of_lt_of_le ha₀ hz.1
  have hX : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g :=
    Work.FTS_EllLimOK.ProducerH.H2.Xn6_nonneg α g
  -- the angular slice of `E g` is `C²` on the open strip
  have hS2 : ContDiffOn ℝ 2 (fun θ' => (E g) z θ') (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.SmoothOpen.curry_θ ((hE g hg).1.2.1) hz0).of_le (by norm_num)
  -- the min-rate of the slice (`BoxAux.psiDz_rate`, the `j = 0` instance)
  have hrate : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      |(E g) z t| ≤ C₁ * Work.FTS.StrongGlobal.Xn6 α g * min t (Real.pi / 2 - t) := by
    intro t ht
    have h := hC₁b g hg 0 (by norm_num) z hz t ht
    simpa using h
  -- the second angular derivative bound (`SecondDeriv.second_theta_deriv_le_Xn6`)
  have hsec : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      |deriv (deriv (fun θ' => (E g) z θ')) t| ≤ K * Work.FTS.StrongGlobal.Xn6 α g :=
    fun t ht => hKb g hg z hz t ht
  refine ⟨?_, ?_, ?_⟩
  · -- the first angular derivative, by the Landau bound at the step `min θ (π/2−θ)/2`
    intro θ hθ
    have hkey := deriv_le_of_min_rate (S := fun θ' => (E g) z θ')
      (C := C₁ * Work.FTS.StrongGlobal.Xn6 α g) (B := K * Work.FTS.StrongGlobal.Xn6 α g)
      (mul_nonneg hC₁.le hX) (mul_nonneg hK.le hX) hS2 hrate hsec θ hθ
    calc |deriv (fun θ' => (E g) z θ') θ|
        ≤ 6 * (C₁ * Work.FTS.StrongGlobal.Xn6 α g)
            + (K * Work.FTS.StrongGlobal.Xn6 α g) * (Real.pi / 8) := hkey
      _ = (6 * C₁ + K * (Real.pi / 8)) * Work.FTS.StrongGlobal.Xn6 α g := by ring
      _ ≤ (1 + 6 * C₁ + K * (Real.pi / 8) + C₁) * Work.FTS.StrongGlobal.Xn6 α g := by
          apply mul_le_mul_of_nonneg_right _ hX
          linarith
  · -- the `θ`-rate at the lower endpoint
    intro θ hθ
    have hmin : min θ (Real.pi / 2 - θ) ≤ θ := min_le_left _ _
    have hCX : 0 ≤ C₁ * Work.FTS.StrongGlobal.Xn6 α g := mul_nonneg hC₁.le hX
    have hπ8 : 0 < Real.pi / 8 := by positivity
    have hC2 : C₁ ≤ 1 + 6 * C₁ + K * (Real.pi / 8) + C₁ := by
      nlinarith [mul_pos hK hπ8]
    calc |(E g) z θ| ≤ C₁ * Work.FTS.StrongGlobal.Xn6 α g * min θ (Real.pi / 2 - θ) :=
          hrate θ hθ
      _ ≤ C₁ * Work.FTS.StrongGlobal.Xn6 α g * θ :=
          mul_le_mul_of_nonneg_left hmin hCX
      _ ≤ (1 + 6 * C₁ + K * (Real.pi / 8) + C₁) * Work.FTS.StrongGlobal.Xn6 α g * θ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hX) (le_of_lt hθ.1)
  · -- the `π/2 − θ`-rate at the upper endpoint
    intro θ hθ
    have hmin : min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 - θ := min_le_right _ _
    have hCX : 0 ≤ C₁ * Work.FTS.StrongGlobal.Xn6 α g := mul_nonneg hC₁.le hX
    have hπ8 : 0 < Real.pi / 8 := by positivity
    have hC2 : C₁ ≤ 1 + 6 * C₁ + K * (Real.pi / 8) + C₁ := by
      nlinarith [mul_pos hK hπ8]
    calc |(E g) z θ| ≤ C₁ * Work.FTS.StrongGlobal.Xn6 α g * min θ (Real.pi / 2 - θ) :=
          hrate θ hθ
      _ ≤ C₁ * Work.FTS.StrongGlobal.Xn6 α g * (Real.pi / 2 - θ) :=
          mul_le_mul_of_nonneg_left hmin hCX
      _ ≤ (1 + 6 * C₁ + K * (Real.pi / 8) + C₁) * Work.FTS.StrongGlobal.Xn6 α g
            * (Real.pi / 2 - θ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hX)
            (by linarith [hθ.2])

end Work.FTS_EllLimOK.ProducerH.H2.Dev
