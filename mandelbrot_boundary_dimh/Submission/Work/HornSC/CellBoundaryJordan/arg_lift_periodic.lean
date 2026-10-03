import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour

/-!
# Argument lifts of a closed curve

A continuous, `1`-periodic, nowhere vanishing curve `f : ℝ → ℂ` admits a continuous *lift*
`θ : ℝ → ℂ` through `exp` (`arg_lift_periodic`), whose shift by `1` is a constant integer multiple
of `2πi`.  Consequently (`hasArg_iff_arg_lift`) the curve has a continuous `1`-periodic argument in
the sense of `HasArgPeriodic` exactly when that lift is periodic.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set Filter

open scoped Topology

/-- **A continuous argument lift always exists.** -/
theorem arg_lift_periodic {f : ℝ → ℂ} (hf : Continuous f) (hper : ∀ t, f (t + 1) = f t)
    (hnz : ∀ t, f t ≠ 0) :
    ∃ m : ℤ, ∃ θ : ℝ → ℂ, Continuous θ ∧ (∀ t, Complex.exp (θ t) = f t) ∧
      ∀ t, θ (t + 1) = θ t + (m : ℂ) * (2 * Real.pi * Complex.I) := by
  -- the covering map `exp : ℂ → ℂ ∖ {0}`
  set p : ℂ → {z : ℂ // z ≠ 0} := fun z => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ :
    {z : ℂ // z ≠ 0}) with hp
  have hcov : IsCoveringMap p := Complex.isCoveringMap_exp
  -- the target continuous map
  set F : C(ℝ, {z : ℂ // z ≠ 0}) :=
    ⟨fun t => (⟨f t, hnz t⟩ : {z : ℂ // z ≠ 0}), hf.subtype_mk _⟩ with hF
  have hFval : ∀ t, F t = (⟨f t, hnz t⟩ : {z : ℂ // z ≠ 0}) := fun t => rfl
  have he₀ : p (Complex.log (f 0)) = F 0 := by
    apply Subtype.ext
    simp only [hp, hFval, ContinuousMap.coe_mk]
    exact Complex.exp_log (hnz 0)
  obtain ⟨G, hG, -⟩ := hcov.existsUnique_continuousMap_lifts F 0 (Complex.log (f 0)) he₀
  obtain ⟨hG0, hGlift⟩ := hG
  -- `G` is the lift we want
  have hGexp : ∀ t, Complex.exp (G t) = f t := by
    intro t
    have h : p (G t) = F t := by
      have h' := congrFun hGlift t
      simpa only [Function.comp_apply] using h'
    have h2 := congrArg (fun z : {z : ℂ // z ≠ 0} => (z : ℂ)) h
    simpa [hFval, hp] using h2
  have h10 : f 1 = f 0 := by simpa using hper 0
  -- the drift is a multiple of `2πi`
  obtain ⟨m, hm⟩ : ∃ m : ℤ, G 1 - G 0 = (m : ℂ) * (2 * Real.pi * Complex.I) := by
    have h1 : Complex.exp (G 1) = Complex.exp (G 0) := by rw [hGexp 1, hGexp 0, h10]
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
    exact ⟨n, by rw [hn]; ring⟩
  refine ⟨m, fun t => G t, G.continuous, hGexp, ?_⟩
  -- the difference `D t = (G (t+1) - G t) - (G 1 - G 0)` vanishes
  have hDexp : ∀ t, Complex.exp ((G (t + 1) - G t) - (G 1 - G 0)) = 1 := by
    intro t
    rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_sub]
    rw [hGexp (t + 1), hGexp t, hGexp 1, hGexp 0, hper t, h10]
    rw [div_self (hnz t), div_self (hnz 0), div_one]
  have hDcont : Continuous fun t : ℝ => (G (t + 1) - G t) - (G 1 - G 0) :=
    ((G.continuous.comp (continuous_id.add continuous_const)).sub G.continuous).sub continuous_const
  have hDzero : ∀ t, (G (t + 1) - G t) - (G 1 - G 0) = 0 := by
    have hD0 : (G (0 + 1) - G 0) - (G 1 - G 0) = 0 := by
      rw [zero_add]; ring
    have hSclosed : IsClosed {t : ℝ | (G (t + 1) - G t) - (G 1 - G 0) = 0} :=
      isClosed_eq hDcont continuous_const
    have hSopen : IsOpen {t : ℝ | (G (t + 1) - G t) - (G 1 - G 0) = 0} := by
      rw [isOpen_iff_mem_nhds]
      intro t ht
      have hU : Metric.ball (0 : ℂ) (2 * Real.pi) ∈ 𝓝 (0 : ℂ) :=
        Metric.ball_mem_nhds _ (by linarith [Real.pi_pos])
      have hpre : (fun s : ℝ => (G (s + 1) - G s) - (G 1 - G 0)) ⁻¹'
          (Metric.ball (0 : ℂ) (2 * Real.pi)) ∈ 𝓝 t :=
        hDcont.continuousAt.preimage_mem_nhds (by rw [ht]; exact hU)
      refine Filter.mem_of_superset hpre (fun s hs => ?_)
      have hs' : ‖(G (s + 1) - G s) - (G 1 - G 0)‖ < 2 * Real.pi := by
        simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using hs
      show (G (s + 1) - G s) - (G 1 - G 0) = 0
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (hDexp s)
      rw [hn] at hs' ⊢
      have him : (((n : ℂ) * (2 * Real.pi * Complex.I))).im = (n : ℝ) * (2 * Real.pi) := by
        rw [Complex.mul_im]
        simp
      have habs : |(n : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
        have h1 : |(((n : ℂ) * (2 * Real.pi * Complex.I))).im| ≤
            ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ := Complex.abs_im_le_norm _
        rw [him, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h1
        exact lt_of_le_of_lt h1 hs'
      have hn0 : n = 0 := by
        have h3 : (0 : ℝ) < 2 * Real.pi := by positivity
        have h2 : |(n : ℝ)| < 1 := by nlinarith [Real.pi_pos]
        by_contra hnne
        have h4 : (1 : ℝ) ≤ |(n : ℝ)| := by
          have := Int.one_le_abs hnne
          exact_mod_cast this
        linarith
      rw [hn0]
      simp
    rcases isPreconnected_univ.subset_or_subset hSopen hSclosed.isOpen_compl disjoint_compl_right
      (by rw [union_compl_self]) with h | h
    · exact fun t => h (mem_univ t)
    · exfalso
      exact h (mem_univ 0) hD0
  intro t
  show G (t + 1) = G t + (m : ℂ) * (2 * Real.pi * Complex.I)
  have h := hDzero t
  rw [sub_eq_zero] at h
  rw [sub_eq_iff_eq_add.mp h, hm]
  ring

end Work.HornSC.CellBoundaryJordan
