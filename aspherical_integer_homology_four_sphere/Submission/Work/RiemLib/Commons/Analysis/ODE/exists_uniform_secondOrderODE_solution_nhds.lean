import Mathlib
import Submission.Work.RiemLib.Commons.Analysis.ODE.exists_uniform_secondOrderODE_solution_in_open

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.ODE

open Set Metric

/-- **Uniform local existence with a neighbourhood of initial data.**

Let `U` be an open subset of `E × E` containing `(p₀, 0)`, and let `G : E × E → E` be `C¹` at
every point of `U` with `G (p₀, 0) = 0`.  Then there is `ρ > 0` and an open neighbourhood `W` of
`(p₀, 0)` with `W ⊆ U` such that for *every* initial position `q.1` with `q ∈ W` and *every* initial
velocity `w` with `‖w‖ ≤ ρ`, the second-order ODE `u'' = G (u, u')` has a solution with `u 0 = q.1`,
`u' 0 = w`, defined on the whole fixed interval `Set.Ioo (-2) 2` and taking all its values in `U`.

This strengthens `exists_uniform_secondOrderODE_solution_in_open` by also allowing the initial
*position* to vary in a neighbourhood of `p₀`.  The proof reduces to
`exists_solution_on_Ioo_of_lipschitzOnWith_ball` applied to the first-order system
`F z = (z.2, G z)`: since `F (p₀,0) = 0`, the Gronwall estimate confines any solution starting
inside the ball of radius `η` around `(p₀,0)` to the ball of radius `3η * exp (2K)`, and choosing
`η = R / (4 * exp (2K))` keeps this below the ball of radius `R` on which `F` is Lipschitz and
which is contained in `U`. -/
theorem exists_uniform_secondOrderODE_solution_nhds {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {G : E × E → E} {U : Set (E × E)} {p₀ : E}
    (hU : IsOpen U) (hp₀ : (p₀, (0 : E)) ∈ U)
    (hG : ∀ z ∈ U, ContDiffAt ℝ 1 G z) (hG0 : G (p₀, 0) = 0) :
    ∃ ρ > (0 : ℝ), ∃ W : Set (E × E), IsOpen W ∧ (p₀, (0 : E)) ∈ W ∧ W ⊆ U ∧
      ∀ q ∈ W, ∀ w : E, ‖w‖ ≤ ρ → ∃ u v : ℝ → E,
        u 0 = q.1 ∧ v 0 = w ∧
        (∀ t ∈ Set.Ioo (-2 : ℝ) 2, (u t, v t) ∈ U) ∧
        (∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt u (v t) t) ∧
        (∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt v (G (u t, v t)) t) := by
  set z₀ : E × E := (p₀, (0 : E)) with hz₀def
  set F : E × E → E × E := fun z => (z.2, G z) with hFdef
  have hz₀U : z₀ ∈ U := by rw [hz₀def]; exact hp₀
  have hF0 : F z₀ = 0 := by
    simp only [hFdef]
    ext
    · simp [hz₀def]
    · rw [hz₀def]; exact hG0
  have hFcont : ContDiffAt ℝ 1 F z₀ := by
    rw [hFdef]
    exact (contDiffAt_snd (𝕜 := ℝ) (n := 1) (p := z₀)).prodMk (hG z₀ hz₀U)
  obtain ⟨K, s, hs, hK⟩ := hFcont.exists_lipschitzOnWith
  obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀U)
  set R : ℝ := min ε δ₁ / 2 with hRdef
  have hR : 0 < R := by
    rw [hRdef]
    have := lt_min hε hδ₁
    linarith
  have hRsub : closedBall z₀ R ⊆ U := by
    intro x hx
    apply hεsub
    exact closedBall_subset_ball (by rw [hRdef]; have := min_le_left ε δ₁; linarith) hx
  have hLip : LipschitzOnWith K F (closedBall z₀ R) :=
    hK.mono (fun x hx =>
      hδ₁sub (closedBall_subset_ball (by rw [hRdef]; have := min_le_right ε δ₁; linarith) hx))
  set η : ℝ := R / (4 * Real.exp ((K : ℝ) * 2)) with hηdef
  have hηpos : 0 < η := by rw [hηdef]; positivity
  have hη_le_R : η ≤ R := by
    rw [hηdef, div_le_iff₀ (by positivity)]
    have he1 : (1 : ℝ) ≤ Real.exp ((K : ℝ) * 2) := Real.one_le_exp (by positivity)
    nlinarith [hR, he1]
  refine ⟨η, hηpos, ball z₀ η, isOpen_ball, ?_, ?_, ?_⟩
  · simpa [hz₀def] using mem_ball_self (x := z₀) hηpos
  · intro x hx
    exact hRsub (closedBall_subset_closedBall hη_le_R (ball_subset_closedBall hx))
  · intro q hq w hw
    have hqdist : ‖q - z₀‖ < η := by rw [← dist_eq_norm]; exact hq
    have hq1 : ‖q.1 - p₀‖ < η := by
      have h : q.1 - p₀ = (q - z₀).1 := by simp [hz₀def]
      rw [h]
      exact lt_of_le_of_lt (norm_fst_le _) hqdist
    have hnorm : ‖(q.1, w) - z₀‖ ≤ ‖q.1 - p₀‖ + ‖w‖ := by
      have h : (q.1, w) - z₀ = (q.1 - p₀, w) := by ext <;> simp [hz₀def]
      rw [h, Prod.norm_def]
      exact max_le (le_add_of_nonneg_right (norm_nonneg w))
        (le_add_of_nonneg_left (norm_nonneg _))
    have hy : ‖(q.1, w) - z₀‖ * Real.exp ((K : ℝ) * 2) < R := by
      have h1 : ‖(q.1, w) - z₀‖ ≤ 3 * η := by linarith [hnorm, hq1, hw]
      have hηe : η * Real.exp ((K : ℝ) * 2) = R / 4 := by
        rw [hηdef]
        field_simp
      have h2 : (3 * η) * Real.exp ((K : ℝ) * 2) = 3 * R / 4 := by
        rw [mul_assoc, hηe]; ring
      have h3 : ‖(q.1, w) - z₀‖ * Real.exp ((K : ℝ) * 2)
          ≤ (3 * η) * Real.exp ((K : ℝ) * 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      linarith [h3, h2, hR]
    obtain ⟨z, hz0, hzd, hzball⟩ :=
      exists_solution_on_Ioo_of_lipschitzOnWith_ball hR hF0 hLip (T := 2) (by norm_num) hy
    refine ⟨fun t => (z t).1, fun t => (z t).2, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using congrArg Prod.fst hz0
    · simpa using congrArg Prod.snd hz0
    · intro t ht
      simpa using hRsub (hzball t ht)
    · intro t ht
      have h := HasFDerivAt.comp_hasDerivAt (f := z) t
        (hasFDerivAt_fst (𝕜 := ℝ) (E := E) (F := E) (p := z t)) (hzd t ht)
      simpa [hFdef, Function.comp_def] using h
    · intro t ht
      have h := HasFDerivAt.comp_hasDerivAt (f := z) t
        (hasFDerivAt_snd (𝕜 := ℝ) (E := E) (F := E) (p := z t)) (hzd t ht)
      simpa [hFdef, Function.comp_def] using h

end Commons.Analysis.ODE
