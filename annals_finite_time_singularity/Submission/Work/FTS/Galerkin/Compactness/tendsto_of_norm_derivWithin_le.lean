import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Galerkin.Compactness

/-- **A curve with exponentially decaying derivative converges** (the paper's step
"`|∂_τ g|_{ℋ³} ≤ Cα² exp(-c τ)` for all `τ ≥ 0`, hence `g` has a unique limit as `τ → ∞`"). In a
complete normed space, if `u` has right derivative `u'` on `[0,∞)` with `‖u' t‖ ≤ K exp(-c t)`
(`c > 0`), then `u` converges at `+∞`.

Intended proof: the mean value inequality on `[τ,σ]` gives
`‖u σ - u τ‖ ≤ ∫_τ^σ ‖u'‖ ≤ (K/c)(exp(-cτ) - exp(-cσ)) → 0` as `τ,σ → ∞`, so `u` is Cauchy at
`atTop`; conclude by completeness. -/
theorem tendsto_of_norm_derivWithin_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (u : ℝ → E) (u' : ℝ → E) (K : ℝ) (c : ℝ) (hc : 0 < c)
    (hder : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt u (u' t) (Set.Ici 0) t)
    (hb : ∀ t : ℝ, 0 ≤ t → ‖u' t‖ ≤ K * Real.exp (-(c * t))) :
    ∃ L : E, Filter.Tendsto u Filter.atTop (nhds L) := by
  -- ## Step 1: the mean-value estimate on `[τ, σ]`, `0 ≤ τ ≤ σ`
  --
  -- The comparison function is the exact integral bound `τ ↦ (K/c)(e^{-cτ} - e^{-ct})`, whose
  -- derivative is `K e^{-ct}`; the "fencing theorem"
  -- `image_norm_le_of_norm_deriv_right_le_deriv_boundary` then gives
  -- `‖u σ - u τ‖ ≤ (K/c)(e^{-cτ} - e^{-cσ})`.
  have hkey : ∀ τ σ : ℝ, 0 ≤ τ → τ ≤ σ →
      ‖u σ - u τ‖ ≤ K / c * (Real.exp (-(c * τ)) - Real.exp (-(c * σ))) := by
    intro τ σ hτ hτσ
    have hcont : ContinuousOn u (Set.Icc τ σ) := fun x hx =>
      ((hder x (le_trans hτ hx.1)).continuousWithinAt).mono (fun y hy => le_trans hτ hy.1)
    have hf : ContinuousOn (fun t : ℝ => u t - u τ) (Set.Icc τ σ) :=
      hcont.sub continuousOn_const
    have hf' : ∀ x ∈ Set.Ico τ σ,
        HasDerivWithinAt (fun t : ℝ => u t - u τ) (u' x) (Set.Ici x) x := by
      intro x hx
      have hx0 : 0 ≤ x := le_trans hτ hx.1
      exact ((hder x hx0).mono (fun y hy => le_trans hx0 hy)).sub_const (u τ)
    have hB : ∀ t : ℝ,
        HasDerivAt (fun t : ℝ => K / c * (Real.exp (-(c * τ)) - Real.exp (-(c * t))))
          (K * Real.exp (-(c * t))) t := by
      intro t
      have hlin : HasDerivAt (fun t : ℝ => -(c * t)) (-c) t := by
        have h := ((hasDerivAt_id t).const_mul c).neg
        convert h using 1
        · funext y; simp
        · ring
      have h1 : HasDerivAt (fun t : ℝ => Real.exp (-(c * t)))
          (Real.exp (-(c * t)) * (-c)) t := by
        simpa [Function.comp_def] using (Real.hasDerivAt_exp (-(c * t))).comp t hlin
      have h2 := (h1.const_sub (Real.exp (-(c * τ)))).const_mul (K / c)
      have h3 : ((K / c) * (-(Real.exp (-(c * t)) * (-c)))) = K * Real.exp (-(c * t)) := by
        field_simp
      rw [← h3]
      exact h2
    have ha : ‖(fun t : ℝ => u t - u τ) τ‖ ≤
        K / c * (Real.exp (-(c * τ)) - Real.exp (-(c * τ))) := by
      simp
    have hres := image_norm_le_of_norm_deriv_right_le_deriv_boundary hf hf' ha hB
      (fun x hx => hb x (le_trans hτ hx.1))
    exact hres (Set.right_mem_Icc.mpr hτσ)
  -- ## Step 2: the one-sided Lipschitz bound with the exponentially decaying majorant
  have hstep : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      ‖u b - u a‖ ≤ |K / c| * Real.exp (-(c * a)) := by
    intro a b ha hab
    refine (hkey a b ha hab).trans ?_
    rcases le_or_gt 0 (K / c) with hK | hK
    · rw [abs_of_nonneg hK]
      refine mul_le_mul_of_nonneg_left ?_ hK
      linarith [Real.exp_pos (-(c * b))]
    · rw [abs_of_neg hK]
      have hexp : Real.exp (-(c * b)) ≤ Real.exp (-(c * a)) := by
        rw [Real.exp_le_exp]; nlinarith
      refine (mul_nonpos_of_nonpos_of_nonneg hK.le (by linarith)).trans
        (mul_nonneg (neg_nonneg.mpr hK.le) (Real.exp_pos _).le)
  have hmin : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      ‖u b - u a‖ ≤ |K / c| * Real.exp (-(c * min a b)) := by
    intro a b ha hb'
    rcases le_total a b with hab | hba
    · rw [min_eq_left hab]; exact hstep a b ha hab
    · rw [min_eq_right hba, norm_sub_rev]; exact hstep b a hb' hba
  -- ## Step 3: the majorant tends to `0`, so `u` is Cauchy at `atTop`
  have htend : Filter.Tendsto (fun t : ℝ => |K / c| * Real.exp (-(c * t)))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => Real.exp (-(c * t))) Filter.atTop (nhds 0) := by
      have hcpos : Filter.Tendsto (fun t : ℝ => c * t) Filter.atTop Filter.atTop :=
        (Filter.tendsto_const_mul_atTop_of_pos hc).mpr Filter.tendsto_id
      simpa [Function.comp_def] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hcpos
    simpa using h1.const_mul |K / c|
  have hcauchy : Cauchy (Filter.atTop.map u) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, ?_⟩
    intro ε hε
    rw [Metric.tendsto_atTop] at htend
    obtain ⟨M, hM⟩ := htend ε hε
    have hMε : |K / c| * Real.exp (-(c * M)) < ε := by
      have := hM M le_rfl
      rwa [Real.dist_eq, sub_zero,
        abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)] at this
    refine ⟨u '' Set.Ici (max M 0), Filter.image_mem_map (Filter.mem_atTop (max M 0)), ?_⟩
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    have haM : M ≤ a := le_trans (le_max_left _ _) ha
    have hbM : M ≤ b := le_trans (le_max_left _ _) hb
    have ha0 : 0 ≤ a := le_trans (le_max_right _ _) ha
    have hb0 : 0 ≤ b := le_trans (le_max_right _ _) hb
    have hexp : Real.exp (-(c * min a b)) ≤ Real.exp (-(c * M)) := by
      rw [Real.exp_le_exp]; nlinarith [le_min haM hbM]
    calc dist (u a) (u b) = ‖u b - u a‖ := by rw [dist_eq_norm, norm_sub_rev]
      _ ≤ |K / c| * Real.exp (-(c * min a b)) := hmin a b ha0 hb0
      _ ≤ |K / c| * Real.exp (-(c * M)) := mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
      _ < ε := hMε
  -- ## Step 4: completeness
  exact cauchy_map_iff_exists_tendsto.mp hcauchy

end Work.FTS.Galerkin.Compactness
