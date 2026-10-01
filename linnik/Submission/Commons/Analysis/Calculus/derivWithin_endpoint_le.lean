import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Calculus

open Set Filter Metric
open scoped Topology

/-- A function `g` which is Lipschitz on an open interval `(a,b)` has a limit at the left
endpoint `a` (approached from the right), provided the target space is complete. -/
lemma tendsto_nhdsGT_of_lipschitzOn_Ioo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g : ℝ → E} {a b : ℝ} (hab : a < b) {C : ℝ} (hC : 0 ≤ C)
    (hlip : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, dist (g x) (g y) ≤ C * |x - y|) :
    ∃ l, Tendsto g (𝓝[>] a) (𝓝 l) := by
  have hnebot : (𝓝[>] a).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have hCδ_lt : ∀ ε : ℝ, 0 < ε → C * min ((b - a)/2) (ε / (2*(C+1))) < ε := by
    intro ε hε
    have h1 : min ((b - a)/2) (ε / (2*(C+1))) ≤ ε / (2*(C+1)) := min_le_right _ _
    have h2 : C * min ((b - a)/2) (ε / (2*(C+1))) ≤ C * (ε / (2*(C+1))) :=
      mul_le_mul_of_nonneg_left h1 hC
    have hpos : (0:ℝ) < 2*(C+1) := by linarith
    have h3 : C * (ε / (2*(C+1))) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ hpos]
      nlinarith [hε, hC]
    linarith
  have hcauchy : Cauchy ((𝓝[>] a).map g) := by
    rw [Metric.cauchy_iff]
    refine ⟨hnebot.map g, ?_⟩
    intro ε hε
    set δ : ℝ := min ((b - a)/2) (ε / (2*(C + 1))) with hδdef
    have hδpos : 0 < δ := lt_min (by linarith) (by positivity)
    have hδlea : a + δ ≤ b := by
      have : δ ≤ (b - a)/2 := min_le_left _ _
      linarith
    have hCδ : C * δ < ε := hCδ_lt ε hε
    refine ⟨g '' (Set.Ioo a (a + δ)), ?_, ?_⟩
    · rw [Filter.mem_map]
      apply mem_of_superset (Ioo_mem_nhdsGT (by linarith : a < a + δ))
      intro x hx
      exact ⟨x, hx, rfl⟩
    · rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
      have hu' : u ∈ Set.Ioo a b := ⟨hu.1, lt_of_lt_of_le hu.2 hδlea⟩
      have hv' : v ∈ Set.Ioo a b := ⟨hv.1, lt_of_lt_of_le hv.2 hδlea⟩
      have hdist : dist (g u) (g v) ≤ C * |u - v| := hlip u hu' v hv'
      have huv : |u - v| < δ := by
        rw [abs_lt]
        exact ⟨by linarith [hu.1, hv.2], by linarith [hu.2, hv.1]⟩
      have hb : C * |u - v| ≤ C * δ := mul_le_mul_of_nonneg_left (le_of_lt huv) hC
      linarith [hdist, hb, hCδ]
  obtain ⟨l, hl⟩ := CompleteSpace.complete hcauchy
  exact ⟨l, hl⟩

/-- A function `g` which is Lipschitz on an open interval `(a,b)` has a limit at the right
endpoint `b` (approached from the left), provided the target space is complete. -/
lemma tendsto_nhdsLT_of_lipschitzOn_Ioo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g : ℝ → E} {a b : ℝ} (hab : a < b) {C : ℝ} (hC : 0 ≤ C)
    (hlip : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, dist (g x) (g y) ≤ C * |x - y|) :
    ∃ l, Tendsto g (𝓝[<] b) (𝓝 l) := by
  have hnebot : (𝓝[<] b).NeBot := nhdsWithin_Iio_neBot le_rfl
  have hCδ_lt : ∀ ε : ℝ, 0 < ε → C * min ((b - a)/2) (ε / (2*(C+1))) < ε := by
    intro ε hε
    have h1 : min ((b - a)/2) (ε / (2*(C+1))) ≤ ε / (2*(C+1)) := min_le_right _ _
    have h2 : C * min ((b - a)/2) (ε / (2*(C+1))) ≤ C * (ε / (2*(C+1))) :=
      mul_le_mul_of_nonneg_left h1 hC
    have hpos : (0:ℝ) < 2*(C+1) := by linarith
    have h3 : C * (ε / (2*(C+1))) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ hpos]
      nlinarith [hε, hC]
    linarith
  have hcauchy : Cauchy ((𝓝[<] b).map g) := by
    rw [Metric.cauchy_iff]
    refine ⟨hnebot.map g, ?_⟩
    intro ε hε
    set δ : ℝ := min ((b - a)/2) (ε / (2*(C + 1))) with hδdef
    have hδpos : 0 < δ := lt_min (by linarith) (by positivity)
    have hδlea : a ≤ b - δ := by
      have : δ ≤ (b - a)/2 := min_le_left _ _
      linarith
    have hCδ : C * δ < ε := hCδ_lt ε hε
    refine ⟨g '' (Set.Ioo (b - δ) b), ?_, ?_⟩
    · rw [Filter.mem_map]
      apply mem_of_superset (Ioo_mem_nhdsLT (by linarith : b - δ < b))
      intro x hx
      exact ⟨x, hx, rfl⟩
    · rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
      have hu' : u ∈ Set.Ioo a b := ⟨lt_of_le_of_lt hδlea hu.1, hu.2⟩
      have hv' : v ∈ Set.Ioo a b := ⟨lt_of_le_of_lt hδlea hv.1, hv.2⟩
      have hdist : dist (g u) (g v) ≤ C * |u - v| := hlip u hu' v hv'
      have huv : |u - v| < δ := by
        rw [abs_lt]
        exact ⟨by linarith [hu.1, hv.2], by linarith [hv.1, hu.2]⟩
      have hb : C * |u - v| ≤ C * δ := mul_le_mul_of_nonneg_left (le_of_lt huv) hC
      linarith [hdist, hb, hCδ]
  obtain ⟨l, hl⟩ := CompleteSpace.complete hcauchy
  exact ⟨l, hl⟩

/-- The right-sided neighbourhood filter of `0` agrees with the one through the open interval
`(0, x₀)` when `x₀ > 0`. -/
lemma nhdsGT_eq_nhds_Ioo {x₀ : ℝ} (hx₀ : 0 < x₀) :
    𝓝[>] (0:ℝ) = 𝓝[Set.Ioo 0 x₀] 0 := by
  exact nhdsWithin_eq_nhdsWithin' (s := Set.Iio x₀) (Iio_mem_nhds hx₀)
    (by ext x; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo]; tauto)

/-- The left-sided neighbourhood filter of `x₀` agrees with the one through the open interval
`(0, x₀)` when `x₀ > 0`. -/
lemma nhdsLT_eq_nhds_Ioo {x₀ : ℝ} (hx₀ : 0 < x₀) :
    𝓝[<] x₀ = 𝓝[Set.Ioo 0 x₀] x₀ := by
  exact nhdsWithin_eq_nhdsWithin' (s := Set.Ioi 0) (Ioi_mem_nhds hx₀)
    (by ext x; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo]; tauto)

theorem derivWithin_endpoint_le {x₀ B : ℝ} (hx₀ : 0 < x₀) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) :
    ‖derivWithin f (Set.Ioi 0) 0‖ ≤ ‖f 0‖ / x₀ + B * x₀ ∧
    ‖derivWithin f (Set.Iio x₀) x₀‖ ≤ ‖f 0‖ / x₀ + B * x₀ := by
  have hBnn : 0 ≤ B := by
    have h := hBnd (x₀/2) ⟨by linarith, by linarith⟩
    have h2 : (0:ℝ) ≤ ‖iteratedDeriv 2 f (x₀/2)‖ := norm_nonneg _
    linarith
  have hfx₀ : f x₀ = 0 := hvan x₀ le_rfl
  -- Differentiability of `f` on the open interval.
  have hdiffOn : DifferentiableOn ℝ f (Set.Ioo 0 x₀) := hf2.differentiableOn (by norm_num)
  have hderiv : ∀ t ∈ Set.Ioo (0:ℝ) x₀, HasDerivAt f (deriv f t) t := by
    intro t ht
    exact ((hf2.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by norm_num)).hasDerivAt
  -- Identification of the second derivative with `iteratedDeriv 2 f`.
  have hd2 : ∀ t, deriv (deriv f) t = iteratedDeriv 2 f t := by
    intro t
    have h : iteratedDeriv 2 f = deriv (deriv f) := by
      rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [← h]
  -- Lipschitz bound for `deriv f` on the open interval.
  have hkey : ∀ {u v : ℝ}, u ∈ Set.Ioo 0 x₀ → v ∈ Set.Ioo 0 x₀ → u ≤ v →
      ‖deriv f u - deriv f v‖ ≤ B * |u - v| := by
    intro u v hu hv huv
    have hdiff' : ∀ x ∈ Set.Icc u v, DifferentiableAt ℝ (deriv f) x := by
      intro x hx
      have hxIoo : x ∈ Set.Ioo 0 x₀ := ⟨lt_of_lt_of_le hu.1 hx.1, lt_of_le_of_lt hx.2 hv.2⟩
      have hcx : ContDiffAt ℝ 2 f x := hf2.contDiffAt (isOpen_Ioo.mem_nhds hxIoo)
      exact (hcx.derivWithin (m := 1) (n := 2) (by norm_num)).differentiableAt (by norm_num)
    have hbnd' : ∀ x ∈ Set.Icc u v, ‖deriv (deriv f) x‖ ≤ B := by
      intro x hx
      have hxIoo : x ∈ Set.Ioo 0 x₀ := ⟨lt_of_lt_of_le hu.1 hx.1, lt_of_le_of_lt hx.2 hv.2⟩
      rw [hd2 x]
      exact hBnd x hxIoo
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv f) hdiff' hbnd'
        (convex_Icc u v) (left_mem_Icc.mpr huv) (right_mem_Icc.mpr huv)
    rw [norm_sub_rev, Real.norm_eq_abs, abs_sub_comm] at h
    exact h
  have hLip : ∀ u ∈ Set.Ioo 0 x₀, ∀ v ∈ Set.Ioo 0 x₀,
      dist (deriv f u) (deriv f v) ≤ B * |u - v| := by
    intro u hu v hv
    rw [dist_eq_norm]
    rcases le_total u v with huv | huv
    · exact hkey hu hv huv
    · have h := hkey hv hu huv
      rwa [norm_sub_rev, abs_sub_comm]
  -- Limits of `deriv f` at the two endpoints.
  obtain ⟨L₀, hL₀⟩ := tendsto_nhdsGT_of_lipschitzOn_Ioo (a := 0) (b := x₀) hx₀ hBnn hLip
  obtain ⟨L₁, hL₁⟩ := tendsto_nhdsLT_of_lipschitzOn_Ioo (a := 0) (b := x₀) hx₀ hBnn hLip
  -- Continuity of `f` from the relevant sides.
  have hcont0 : ContinuousWithinAt f (Set.Ioo 0 x₀) 0 :=
    (hcont 0 ⟨le_refl 0, le_of_lt hx₀⟩).mono Ioo_subset_Icc_self
  have hcontx₀ : ContinuousWithinAt f (Set.Ioo 0 x₀) x₀ :=
    (hcont x₀ ⟨le_of_lt hx₀, le_refl x₀⟩).mono Ioo_subset_Icc_self
  -- Derivatives within at the endpoints.
  have hDW0 : derivWithin f (Set.Ioi 0) 0 = L₀ :=
    (HasDerivWithinAt.mono
      (hasDerivWithinAt_Ici_of_tendsto_deriv hdiffOn hcont0 (Ioo_mem_nhdsGT hx₀) hL₀)
      Ioi_subset_Ici_self).derivWithin (uniqueDiffWithinAt_Ioi 0)
  have hDWx₀ : derivWithin f (Set.Iio x₀) x₀ = L₁ :=
    (HasDerivWithinAt.mono
      (hasDerivWithinAt_Iic_of_tendsto_deriv hdiffOn hcontx₀ (Ioo_mem_nhdsLT hx₀) hL₁)
      Iio_subset_Iic_self).derivWithin (uniqueDiffWithinAt_Iio x₀)
  -- Second-order Taylor bounds on fully interior intervals.
  have hT2 : ∀ α ∈ Set.Ioo 0 x₀, ∀ β ∈ Set.Ioo 0 x₀, α ≤ β →
      ‖f β - f α - (β - α) • deriv f α‖ ≤ B * (β - α)^2 := by
    intro α hα β hβ hαβ
    have hmain := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun u => f u - f α - (u - α) • deriv f α)
      (f' := fun x => deriv f x - deriv f α)
      (a := α) (b := β) (C := B * (β - α))
      (by
        intro x hx
        have hxIoo : x ∈ Set.Ioo 0 x₀ := ⟨lt_of_lt_of_le hα.1 hx.1, lt_of_le_of_lt hx.2 hβ.2⟩
        have hA : HasDerivWithinAt (fun u : ℝ => f u - f α) (deriv f x) (Set.Icc α β) x :=
          ((hderiv x hxIoo).sub_const (f α)).hasDerivWithinAt
        have hB : HasDerivWithinAt (fun u : ℝ => (u - α) • deriv f α) (deriv f α) (Set.Icc α β) x := by
          have hh := ((hasDerivAt_id x).sub_const α).smul_const (deriv f α)
          simpa using hh.hasDerivWithinAt
        exact hA.sub hB)
      (by
        intro x hx
        have hxmem : x ∈ Set.Ioo 0 x₀ := ⟨lt_of_lt_of_le hα.1 hx.1, lt_trans hx.2 hβ.2⟩
        have h1 : ‖deriv f x - deriv f α‖ ≤ B * |x - α| := by
          simpa [dist_eq_norm] using hLip x hxmem α hα
        have h2 : |x - α| ≤ β - α := by
          rw [abs_of_nonneg (by linarith [hx.1])]
          linarith [hx.2]
        calc ‖deriv f x - deriv f α‖ ≤ B * |x - α| := h1
          _ ≤ B * (β - α) := mul_le_mul_of_nonneg_left h2 hBnn)
      β (right_mem_Icc.mpr hαβ)
    have hαval : f α - f α - (α - α) • deriv f α = 0 := by simp
    rw [hαval, sub_zero] at hmain
    calc ‖f β - f α - (β - α) • deriv f α‖ ≤ B * (β - α) * (β - α) := hmain
      _ = B * (β - α)^2 := by ring
  have hT2' : ∀ α ∈ Set.Ioo 0 x₀, ∀ β ∈ Set.Ioo 0 x₀, α ≤ β →
      ‖f β - f α - (β - α) • deriv f β‖ ≤ B * (β - α)^2 := by
    intro α hα β hβ hαβ
    have hmain := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun u => f u - f β - (u - β) • deriv f β)
      (f' := fun x => deriv f x - deriv f β)
      (a := α) (b := β) (C := B * (β - α))
      (by
        intro x hx
        have hxIoo : x ∈ Set.Ioo 0 x₀ := ⟨lt_of_lt_of_le hα.1 hx.1, lt_of_le_of_lt hx.2 hβ.2⟩
        have hA : HasDerivWithinAt (fun u : ℝ => f u - f β) (deriv f x) (Set.Icc α β) x :=
          ((hderiv x hxIoo).sub_const (f β)).hasDerivWithinAt
        have hB : HasDerivWithinAt (fun u : ℝ => (u - β) • deriv f β) (deriv f β) (Set.Icc α β) x := by
          have hh := ((hasDerivAt_id x).sub_const β).smul_const (deriv f β)
          simpa using hh.hasDerivWithinAt
        exact hA.sub hB)
      (by
        intro x hx
        have hxmem : x ∈ Set.Ioo 0 x₀ := ⟨lt_of_lt_of_le hα.1 hx.1, lt_trans hx.2 hβ.2⟩
        have h1 : ‖deriv f x - deriv f β‖ ≤ B * |x - β| := by
          simpa [dist_eq_norm] using hLip x hxmem β hβ
        have h2 : |x - β| ≤ β - α := by
          rw [abs_of_nonpos (by linarith [hx.2])]
          linarith [hx.1]
        calc ‖deriv f x - deriv f β‖ ≤ B * |x - β| := h1
          _ ≤ B * (β - α) := mul_le_mul_of_nonneg_left h2 hBnn)
      β (right_mem_Icc.mpr hαβ)
    have hβval : f β - f β - (β - β) • deriv f β = 0 := by simp
    rw [hβval, zero_sub, norm_neg] at hmain
    have hform : f α - f β - (α - β) • deriv f β
        = -(f β - f α - (β - α) • deriv f β) := by
      rw [show α - β = -(β - α) by ring, neg_smul]
      abel
    rw [hform, norm_neg] at hmain
    calc ‖f β - f α - (β - α) • deriv f β‖ ≤ B * (β - α) * (β - α) := hmain
      _ = B * (β - α)^2 := by ring
  -- (I) : bound on `f t - f 0 - t L₀`
  have hI : ∀ t ∈ Set.Ioo 0 x₀, ‖f t - f 0 - t • L₀‖ ≤ B * t^2 := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hfα : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 (f 0)) := by
      rw [nhdsGT_eq_nhds_Ioo hx₀]; exact hcont0
    have htα : Tendsto (fun α : ℝ => α) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hsub : Tendsto (fun α : ℝ => t - α) (𝓝[>] (0:ℝ)) (𝓝 t) := by
      have h := (tendsto_const_nhds (x := t)).sub htα
      simpa using h
    have hscaled : Tendsto (fun α : ℝ => (t - α) • deriv f α) (𝓝[>] (0:ℝ)) (𝓝 (t • L₀)) :=
      hsub.smul hL₀
    have hleft : Tendsto (fun α : ℝ => ‖f t - f α - (t - α) • deriv f α‖) (𝓝[>] (0:ℝ))
        (𝓝 ‖f t - f 0 - t • L₀‖) :=
      (((tendsto_const_nhds (x := f t)).sub hfα).sub hscaled).norm
    have hright : Tendsto (fun α : ℝ => B * (t - α)^2) (𝓝[>] (0:ℝ)) (𝓝 (B * t^2)) := by
      have hc : Continuous (fun α : ℝ => B * (t - α)^2) := by fun_prop
      have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using h
    refine le_of_tendsto_of_tendsto hleft hright ?_
    filter_upwards [Ioo_mem_nhdsGT ht0] with α hα
    exact hT2 α ⟨hα.1, lt_trans hα.2 ht.2⟩ t ht (le_of_lt hα.2)
  -- Bounding `L₀`.
  have hL0bound : ‖L₀‖ ≤ ‖f x₀ - f 0‖ / x₀ + B * x₀ := by
    have hlim : ‖f x₀ - f 0 - x₀ • L₀‖ ≤ B * x₀^2 := by
      have hfβ : Tendsto f (𝓝[<] x₀) (𝓝 (f x₀)) := by
        rw [nhdsLT_eq_nhds_Ioo hx₀]; exact hcontx₀
      have htx₀ : Tendsto (fun t : ℝ => t) (𝓝[<] x₀) (𝓝 x₀) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hleft : Tendsto (fun t : ℝ => ‖f t - f 0 - t • L₀‖) (𝓝[<] x₀)
          (𝓝 ‖f x₀ - f 0 - x₀ • L₀‖) :=
        ((hfβ.sub_const (f 0)).sub (htx₀.smul (tendsto_const_nhds (x := L₀)))).norm
      have hright : Tendsto (fun t : ℝ => B * t^2) (𝓝[<] x₀) (𝓝 (B * x₀^2)) := by
        have hc : Continuous (fun t : ℝ => B * t^2) := by fun_prop
        have h := (hc.tendsto x₀).mono_left (nhdsWithin_le_nhds (s := Set.Iio x₀))
        simpa using h
      refine le_of_tendsto_of_tendsto hleft hright ?_
      filter_upwards [Ioo_mem_nhdsLT hx₀] with t ht
      exact hI t ht
    have h2 : ‖x₀ • L₀ - (f x₀ - f 0)‖ ≤ B * x₀^2 := by
      rw [norm_sub_rev]; exact hlim
    have h3 : ‖x₀ • L₀‖ ≤ ‖x₀ • L₀ - (f x₀ - f 0)‖ + ‖f x₀ - f 0‖ := by
      calc ‖x₀ • L₀‖ = ‖(x₀ • L₀ - (f x₀ - f 0)) + (f x₀ - f 0)‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have h4 : ‖x₀ • L₀‖ = x₀ * ‖L₀‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hx₀]
    have h5 : x₀ * ‖L₀‖ ≤ ‖f x₀ - f 0‖ + B * x₀^2 := by
      rw [← h4]; linarith
    have h6 : ‖L₀‖ * x₀ ≤ ‖f x₀ - f 0‖ + B * x₀^2 := by rw [mul_comm]; exact h5
    calc ‖L₀‖ ≤ (‖f x₀ - f 0‖ + B * x₀^2) / x₀ := (le_div_iff₀ hx₀).mpr h6
      _ = ‖f x₀ - f 0‖ / x₀ + B * x₀ := by field_simp
  -- (II) : bound on `f x₀ - f α - (x₀-α) L₁`
  have hII : ∀ α ∈ Set.Ioo 0 x₀, ‖f x₀ - f α - (x₀ - α) • L₁‖ ≤ B * (x₀ - α)^2 := by
    intro α hα
    have hαx : α < x₀ := hα.2
    have hfβ : Tendsto f (𝓝[<] x₀) (𝓝 (f x₀)) := by
      rw [nhdsLT_eq_nhds_Ioo hx₀]; exact hcontx₀
    have hβid : Tendsto (fun β : ℝ => β) (𝓝[<] x₀) (𝓝 x₀) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hscaled : Tendsto (fun β : ℝ => (β - α) • deriv f β) (𝓝[<] x₀) (𝓝 ((x₀ - α) • L₁)) :=
      (hβid.sub (tendsto_const_nhds (x := α))).smul hL₁
    have hleft : Tendsto (fun β : ℝ => ‖f β - f α - (β - α) • deriv f β‖) (𝓝[<] x₀)
        (𝓝 ‖f x₀ - f α - (x₀ - α) • L₁‖) :=
      ((hfβ.sub_const (f α)).sub hscaled).norm
    have hright : Tendsto (fun β : ℝ => B * (β - α)^2) (𝓝[<] x₀) (𝓝 (B * (x₀ - α)^2)) := by
      have hc : Continuous (fun β : ℝ => B * (β - α)^2) := by fun_prop
      have h := (hc.tendsto x₀).mono_left (nhdsWithin_le_nhds (s := Set.Iio x₀))
      simpa using h
    refine le_of_tendsto_of_tendsto hleft hright ?_
    filter_upwards [Ioo_mem_nhdsLT hαx] with β hβ
    exact hT2' α hα β ⟨lt_trans hα.1 hβ.1, hβ.2⟩ (le_of_lt hβ.1)
  have hL1bound : ‖L₁‖ ≤ ‖f x₀ - f 0‖ / x₀ + B * x₀ := by
    have hlim : ‖f x₀ - f 0 - x₀ • L₁‖ ≤ B * x₀^2 := by
      have hfα : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 (f 0)) := by
        rw [nhdsGT_eq_nhds_Ioo hx₀]; exact hcont0
      have hαid : Tendsto (fun α : ℝ => α) (𝓝[>] (0:ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hscaled : Tendsto (fun α : ℝ => (x₀ - α) • L₁) (𝓝[>] (0:ℝ)) (𝓝 (x₀ • L₁)) := by
        have h := ((tendsto_const_nhds (x := x₀)).sub hαid).smul (tendsto_const_nhds (x := L₁))
        simpa using h
      have hleft : Tendsto (fun α : ℝ => ‖f x₀ - f α - (x₀ - α) • L₁‖) (𝓝[>] (0:ℝ))
          (𝓝 ‖f x₀ - f 0 - x₀ • L₁‖) :=
        (((tendsto_const_nhds (x := f x₀)).sub hfα).sub hscaled).norm
      have hright : Tendsto (fun α : ℝ => B * (x₀ - α)^2) (𝓝[>] (0:ℝ)) (𝓝 (B * x₀^2)) := by
        have hc : Continuous (fun α : ℝ => B * (x₀ - α)^2) := by fun_prop
        have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
        simpa using h
      refine le_of_tendsto_of_tendsto hleft hright ?_
      filter_upwards [Ioo_mem_nhdsGT hx₀] with α hα
      exact hII α hα
    have h2 : ‖x₀ • L₁ - (f x₀ - f 0)‖ ≤ B * x₀^2 := by
      rw [norm_sub_rev]; exact hlim
    have h3 : ‖x₀ • L₁‖ ≤ ‖x₀ • L₁ - (f x₀ - f 0)‖ + ‖f x₀ - f 0‖ := by
      calc ‖x₀ • L₁‖ = ‖(x₀ • L₁ - (f x₀ - f 0)) + (f x₀ - f 0)‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have h4 : ‖x₀ • L₁‖ = x₀ * ‖L₁‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hx₀]
    have h5 : x₀ * ‖L₁‖ ≤ ‖f x₀ - f 0‖ + B * x₀^2 := by
      rw [← h4]; linarith
    have h6 : ‖L₁‖ * x₀ ≤ ‖f x₀ - f 0‖ + B * x₀^2 := by rw [mul_comm]; exact h5
    calc ‖L₁‖ ≤ (‖f x₀ - f 0‖ + B * x₀^2) / x₀ := (le_div_iff₀ hx₀).mpr h6
      _ = ‖f x₀ - f 0‖ / x₀ + B * x₀ := by field_simp
  constructor
  · rw [hDW0]
    calc ‖L₀‖ ≤ ‖f x₀ - f 0‖ / x₀ + B * x₀ := hL0bound
      _ = ‖f 0‖ / x₀ + B * x₀ := by rw [hfx₀, zero_sub, norm_neg]
  · rw [hDWx₀]
    calc ‖L₁‖ ≤ ‖f x₀ - f 0‖ / x₀ + B * x₀ := hL1bound
      _ = ‖f 0‖ / x₀ + B * x₀ := by rw [hfx₀, zero_sub, norm_neg]

end Commons.Analysis.Calculus