import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4c.norm_sub_le_of_hasDerivAt_off_finset

set_option autoImplicit false
set_option linter.unusedVariables false

open Filter
open scoped Topology

namespace Work.WilG4c

/-- **Differentiability at `u` from a derivative bound off a "ray-thin" set.**

`g : ℝ^N → F` is continuous on the ball `B(u,ρ)` and differentiable at every point of that ball
other than `u` and the points of `S`; its Fréchet derivative tends to `L` along the
`S`-complement.  If `S` is thin in the sense that the set of `x` whose segment `[u,x]` meets `S`
infinitely often has empty interior, then `g` is differentiable at `u` with derivative `L`.

The proof is the classical one.  For a point `x ∉ B` the segment `[u,x]` meets `S` only finitely
often, so the mean value inequality with finitely many exceptional points
(`norm_sub_le_of_hasDerivAt_off_finset`) applied along `t ↦ u + t • (x - u)` gives
`‖g x - g u - L (x - u)‖ ≤ (ε/2) ‖x - u‖`.  The residual `φ x = g x - g u - L (x - u)` is continuous
on the ball, so the set where `‖φ x‖ ≤ ε ‖x - u‖` holds is closed; since it contains the dense
`B`-complement, it contains a whole neighbourhood of `u`. -/
theorem hasFDerivAt_of_dense_tendsto_fderiv {N : ℕ} (hN : 1 ≤ N) {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : (Fin N → ℝ) → F} {u : Fin N → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    {S : Set (Fin N → ℝ)}
    (hS : interior {x : Fin N → ℝ | {t : ℝ | t ∈ Set.Ioc (0 : ℝ) 1 ∧ u + t • (x - u) ∈ S}.Infinite} = ∅)
    (hcont : ContinuousOn g (Metric.ball u ρ))
    (hdiff : ∀ x ∈ Metric.ball u ρ, x ≠ u → x ∉ S → DifferentiableAt ℝ g x)
    {L : (Fin N → ℝ) →L[ℝ] F}
    (h : ∀ ε > 0, ∃ δ > 0, ∀ x, x ≠ u → x ∉ S → dist x u < δ → ‖fderiv ℝ g x - L‖ < ε) :
    HasFDerivAt g L u := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  -- the derivative bound with `ε/2` on the `S`-complement
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := h (ε / 2) (by linarith)
  set δ : ℝ := min δ₀ (ρ / 2) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀pos (by linarith)
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδρ : δ ≤ ρ := le_trans (min_le_right _ _) (by linarith)
  -- the "bad ray" set
  set B : Set (Fin N → ℝ) :=
    {x : Fin N → ℝ | {t : ℝ | t ∈ Set.Ioc (0 : ℝ) 1 ∧ u + t • (x - u) ∈ S}.Infinite} with hBdef
  have hBdense : Dense Bᶜ := by
    rw [hBdef]
    exact interior_eq_empty_iff_dense_compl.mp hS
  -- the residual
  set φ : (Fin N → ℝ) → F := fun x => g x - g u - L (x - u) with hφdef
  -- the mean value bound for the good ("not bad ray") points
  have mvt : ∀ z, z ∉ B → z ≠ u → dist z u < δ → ‖φ z‖ ≤ (ε / 2) * ‖z - u‖ := by
    intro z hzB hzu hzdu
    have hzB' : ¬ ({t : ℝ | t ∈ Set.Ioc (0 : ℝ) 1 ∧ u + t • (z - u) ∈ S}.Infinite) := by
      rw [hBdef] at hzB
      exact hzB
    have hzfin : {t : ℝ | t ∈ Set.Ioc (0 : ℝ) 1 ∧ u + t • (z - u) ∈ S}.Finite :=
      Set.not_infinite.mp hzB'
    set T : Finset ℝ := hzfin.toFinset with hTdef
    have hTcoe : (T : Set ℝ) = {t : ℝ | t ∈ Set.Ioc (0 : ℝ) 1 ∧ u + t • (z - u) ∈ S} :=
      hzfin.coe_toFinset
    set ψ : ℝ → F := fun t => g (u + t • (z - u)) - L (u + t • (z - u)) with hψdef
    have hcurve : Continuous fun t : ℝ => u + t • (z - u) := by
      exact continuous_const.add (continuous_id.smul continuous_const)
    have hcurve_mem : Set.MapsTo (fun t : ℝ => u + t • (z - u)) (Set.Icc 0 1) (Metric.ball u ρ) := by
      intro t ht
      have h1 : u + t • (z - u) - u = t • (z - u) := by abel
      rw [Metric.mem_ball, dist_eq_norm, h1, norm_smul, Real.norm_eq_abs]
      calc |t| * ‖z - u‖ ≤ 1 * ‖z - u‖ :=
            mul_le_mul_of_nonneg_right (by rw [abs_of_nonneg ht.1]; exact ht.2) (norm_nonneg _)
        _ = ‖z - u‖ := one_mul _
        _ = dist z u := by rw [dist_eq_norm]
        _ < δ := hzdu
        _ ≤ ρ := hδρ
    have hψcont : ContinuousOn ψ (Set.Icc 0 1) := by
      have h1 : ContinuousOn (fun t : ℝ => g (u + t • (z - u))) (Set.Icc 0 1) :=
        hcont.comp hcurve.continuousOn hcurve_mem
      have h2 : ContinuousOn (fun t : ℝ => L (u + t • (z - u))) (Set.Icc 0 1) :=
        (L.continuous.comp hcurve).continuousOn
      rw [hψdef]
      exact h1.sub h2
    -- the exceptional set is `T`, where the segment meets `S`
    have hw_S : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → t ∉ (T : Set ℝ) →
        u + t • (z - u) ∉ S := by
      intro t ht htT hcon
      rw [hTcoe] at htT
      exact htT ⟨⟨ht.1, ht.2.le⟩, hcon⟩
    have hw_ne : ∀ t : ℝ, 0 < t → (u + t • (z - u)) ≠ u := by
      intro t ht h
      have h1 : t • (z - u) = 0 := by
        have h2 : u + t • (z - u) = u + 0 := by rw [add_zero]; exact h
        exact add_left_cancel h2
      exact (smul_ne_zero (ne_of_gt ht) (sub_ne_zero.mpr hzu)) h1
    have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, t ∉ (T : Set ℝ) →
        HasDerivAt ψ ((fderiv ℝ g (u + t • (z - u)) - L) (z - u)) t := by
      intro t ht htT
      have hwS : u + t • (z - u) ∉ S := hw_S t ht htT
      have hwne : u + t • (z - u) ≠ u := hw_ne t ht.1
      have hwball : u + t • (z - u) ∈ Metric.ball u ρ :=
        hcurve_mem ⟨ht.1.le, ht.2.le⟩
      have hgAt : HasFDerivAt g (fderiv ℝ g (u + t • (z - u))) (u + t • (z - u)) :=
        (hdiff _ hwball hwne hwS).hasFDerivAt
      have hcurve_deriv : HasDerivAt (fun s : ℝ => u + s • (z - u)) (z - u) t := by
        have h1 : HasDerivAt (fun s : ℝ => s • (z - u)) (z - u) t := by
          simpa using (hasDerivAt_id t).smul_const (z - u)
        simpa using h1.const_add u
      have hcomp : HasDerivAt (fun s : ℝ => g (u + s • (z - u)))
          ((fderiv ℝ g (u + t • (z - u))) (z - u)) t :=
        hgAt.comp_hasDerivAt t hcurve_deriv
      have hlin : HasDerivAt (fun s : ℝ => L (u + s • (z - u))) (L (z - u)) t :=
        (ContinuousLinearMap.hasFDerivAt L).comp_hasDerivAt t hcurve_deriv
      have hsub := hcomp.sub hlin
      have hval : (fderiv ℝ g (u + t • (z - u))) (z - u) - L (z - u)
          = (fderiv ℝ g (u + t • (z - u)) - L) (z - u) := by rw [sub_apply]
      rw [hval] at hsub
      rw [hψdef]
      exact hsub
    have hbound : ∀ t ∈ Set.Ioo (0 : ℝ) 1, t ∉ (T : Set ℝ) →
        ‖(fderiv ℝ g (u + t • (z - u)) - L) (z - u)‖ ≤ (ε / 2) * ‖z - u‖ := by
      intro t ht htT
      have hwS : u + t • (z - u) ∉ S := hw_S t ht htT
      have hwne : u + t • (z - u) ≠ u := hw_ne t ht.1
      have hwdist : dist (u + t • (z - u)) u < δ := by
        have h1 : u + t • (z - u) - u = t • (z - u) := by abel
        rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
        calc t * ‖z - u‖ ≤ 1 * ‖z - u‖ := mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg _)
          _ = ‖z - u‖ := one_mul _
          _ = dist z u := by rw [dist_eq_norm]
          _ < δ := hzdu
      have hb : ‖fderiv ℝ g (u + t • (z - u)) - L‖ < ε / 2 :=
        hδ₀ _ hwne hwS (lt_of_lt_of_le hwdist hδδ₀)
      calc ‖(fderiv ℝ g (u + t • (z - u)) - L) (z - u)‖
          ≤ ‖fderiv ℝ g (u + t • (z - u)) - L‖ * ‖z - u‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (ε / 2) * ‖z - u‖ := mul_le_mul_of_nonneg_right hb.le (norm_nonneg _)
    have hmvt := norm_sub_le_of_hasDerivAt_off_finset T ψ
      (fun t => (fderiv ℝ g (u + t • (z - u)) - L) (z - u)) ((ε / 2) * ‖z - u‖) 0 1
      (by norm_num) hψcont hderiv hbound
    have hψ1 : ψ 1 = g z - L z := by rw [hψdef]; simp
    have hψ0 : ψ 0 = g u - L u := by rw [hψdef]; simp
    rw [hψ1, hψ0] at hmvt
    have hgoal : φ z = (g z - L z) - (g u - L u) := by
      show g z - g u - L (z - u) = (g z - L z) - (g u - L u)
      rw [map_sub]
      abel
    rw [hgoal]
    simpa using hmvt
  -- the residual is continuous on the ball
  have key : ∀ x, dist x u < δ → ‖φ x‖ ≤ ε * ‖x - u‖ := by
    intro x hxdu
    rcases eq_or_ne x u with rfl | hxu
    · simp [hφdef]
    · by_contra hcon
      push Not at hcon
      have hxρ : x ∈ Metric.ball u ρ := Metric.mem_ball.mpr (lt_of_lt_of_le hxdu hδρ)
      have hcontφ : ContinuousAt φ x := by
        have hg : ContinuousAt g x := hcont.continuousAt (Metric.isOpen_ball.mem_nhds hxρ)
        have hL : ContinuousAt (fun y : Fin N → ℝ => L (y - u)) x :=
          (L.continuous.comp (continuous_id.sub continuous_const)).continuousAt
        rw [hφdef]
        exact (hg.sub continuousAt_const).sub hL
      have hcont_f : ContinuousAt (fun y : Fin N → ℝ => ‖φ y‖ - ε * ‖y - u‖) x := by
        have h1 : ContinuousAt (fun y : Fin N → ℝ => ‖φ y‖) x := hcontφ.norm
        have h2 : ContinuousAt (fun y : Fin N → ℝ => ε * ‖y - u‖) x :=
          (continuous_const.mul (continuous_id.sub continuous_const).norm).continuousAt
        exact h1.sub h2
      have hpos : 0 < ‖φ x‖ - ε * ‖x - u‖ := sub_pos.mpr hcon
      obtain ⟨r, hrpos, hr⟩ :=
        (Metric.continuousAt_iff.mp hcont_f) (‖φ x‖ - ε * ‖x - u‖) hpos
      set W : Set (Fin N → ℝ) := (Metric.ball x r ∩ Metric.ball u δ) \ {u} with hWdef
      have hWopen : IsOpen W := by
        rw [hWdef]
        exact (Metric.isOpen_ball.inter Metric.isOpen_ball).sdiff isClosed_singleton
      have hWne : W.Nonempty := by
        refine ⟨x, ⟨⟨Metric.mem_ball_self hrpos, Metric.mem_ball.mpr hxdu⟩, ?_⟩⟩
        simp only [Set.mem_singleton_iff]
        exact hxu
      obtain ⟨z, hzB, hzW⟩ := hBdense.exists_mem_open hWopen hWne
      rw [hWdef] at hzW
      obtain ⟨⟨hzx, hzu⟩, hzne⟩ := hzW
      have hznotB : z ∉ B := by simpa using hzB
      have hzu' : z ≠ u := by
        simpa only [Set.mem_singleton_iff] using hzne
      have hzdu : dist z u < δ := Metric.mem_ball.mp hzu
      have hzbound : ‖φ z‖ ≤ (ε / 2) * ‖z - u‖ := mvt z hznotB hzu' hzdu
      have hfz : 0 < ‖φ z‖ - ε * ‖z - u‖ := by
        have hdist : dist (‖φ z‖ - ε * ‖z - u‖) (‖φ x‖ - ε * ‖x - u‖)
            < ‖φ x‖ - ε * ‖x - u‖ := hr (Metric.mem_ball.mp hzx)
        rw [Real.dist_eq] at hdist
        have habs := (abs_lt.mp hdist).1
        linarith
      have hhalf : ε / 2 ≤ ε := by linarith
      have hle : ‖φ z‖ ≤ ε * ‖z - u‖ :=
        le_trans hzbound (mul_le_mul_of_nonneg_right hhalf (norm_nonneg _))
      linarith
  filter_upwards [Metric.ball_mem_nhds u hδpos] with x hx
  rw [Metric.mem_ball] at hx
  have := key x hx
  simpa [hφdef] using this

end Work.WilG4c
