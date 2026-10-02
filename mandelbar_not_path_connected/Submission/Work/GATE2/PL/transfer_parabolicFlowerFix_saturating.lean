import Mathlib
import Submission.Work.FatouCoordFix.FlowerFix.TransferFix

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PL

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open Work.FatouCoordFix.FlowerFix

/-- The transport of `Work.FatouCoordFix.FlowerFix.transfer_parabolicFlowerFix`
(`Submission/Work/FatouCoordFix/FlowerFix/TransferFix.lean`) along the affine chart
`u ↦ z₀ + lam * u`, with the extra information that the saturation of the source Fatou
coordinate on `h.Pg` is inherited by the transferred flower's `φa` on `fl.Pg` (with the same `X`).
The proof is a copy of the body of `transfer_parabolicFlowerFix`, which builds the flower with the
explicit fields `Pa' = trChart z₀ lam '' h.Pa`, `Pg' = trChart z₀ lam '' h.Pg` and
`φa' = fun z => h.φa (trChartInv z₀ lam z)`; only the final conjunct is new. -/
theorem transfer_parabolicFlowerFix_saturating {F g f gU : ℂ → ℂ} {z₀ lam : ℂ} {δ : ℝ}
    (hlam : lam ≠ 0)
    (hg_anti : ∀ z : ℂ, DifferentiableAt ℂ (fun z => star (g z)) z)
    (hFf : ∀ u : ℂ, F (z₀ + lam * u) = z₀ + lam * f u)
    (hGg : ∀ u : ℂ, g (z₀ + lam * u) = z₀ + lam * gU u)
    (hδ : 0 < δ)
    (h : Work.FatouCoordFix.ParabolicFlowerFix f gU 0)
    (hPa_small : h.Pa ⊆ Metric.ball 0 (δ / ‖lam‖))
    (hPg_small : h.Pg ⊆ Metric.ball 0 (δ / ‖lam‖))
    (hsat : ∃ X : ℝ, ∀ w : ℂ, X < w.re → ∃ z ∈ h.Pg, h.φa z = w) :
    ∃ fl : Work.FatouCoordFix.ParabolicFlowerFix F g z₀,
      fl.Pa ⊆ Metric.ball z₀ δ ∧ fl.Pg ⊆ Metric.ball z₀ δ ∧
      ∃ X : ℝ, ∀ w : ℂ, X < w.re → ∃ z ∈ fl.Pg, fl.φa z = w := by
  have hFf' : ∀ u : ℂ, F (trChart z₀ lam u) = trChart z₀ lam (f u) := fun u => hFf u
  have hGg' : ∀ u : ℂ, g (trChart z₀ lam u) = trChart z₀ lam (gU u) := fun u => hGg u
  have hnorm : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  refine ⟨⟨{
    Pa := trChart z₀ lam '' h.Pa
    φa := fun z => h.φa (trChartInv z₀ lam z)
    Ψ := fun w => trChart z₀ lam (h.Ψ w)
    isOpen_Pa := ?_
    isPreconnected_Pa := ?_
    z₀_not_mem := ?_
    mapsTo_Pa := ?_
    tendsto_Pa := ?_
    enters_Pa := ?_
    φa_fatou := ?_
    Ψ_diff := ?_
    Ψ_shift := ?_
    Ψ_anti := ?_
    Ψ_small := ?_
    Ψ_inj := ?_
    Ψ_ends := ?_
    cover := ?_ }, trChart z₀ lam '' h.Pg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  -- `Pa` is open, being the preimage of the open `Pa` of `h` under the continuous inverse chart
  · rw [show trChart z₀ lam '' h.Pa = trChartInv z₀ lam ⁻¹' h.Pa from by
        ext z; exact mem_trChart_image hlam]
    exact h.isOpen_Pa.preimage (continuous_trChartInv z₀ lam)
  -- `Pa` is preconnected, being the image of the preconnected `Pa` of `h`
  · exact h.isPreconnected_Pa.image _ (continuous_trChart z₀ lam).continuousOn
  -- the centre of the flower of `h` is `0`, which is not in `h.Pa`
  · intro hmem
    rw [mem_trChart_image hlam] at hmem
    have h0 : trChartInv z₀ lam z₀ = 0 := by simp [trChartInv]
    rw [h0] at hmem
    exact h.z₀_not_mem hmem
  · rintro z ⟨u, hu, rfl⟩
    rw [hFf']
    exact ⟨f u, h.mapsTo_Pa hu, rfl⟩
  -- orbits in the new petal converge to `z₀`, by continuity of the chart
  · rintro z ⟨u, hu, rfl⟩
    have hiter : ∀ n : ℕ, F^[n] (trChart z₀ lam u) = trChart z₀ lam (f^[n] u) :=
      fun n => iterate_trChart hFf' u n
    have h1 : Tendsto (fun v : ℂ => trChart z₀ lam v) (nhds 0) (nhds (trChart z₀ lam 0)) :=
      (continuous_trChart z₀ lam).tendsto 0
    have h2 : trChart z₀ lam (0 : ℂ) = z₀ := by simp [trChart]
    rw [h2] at h1
    exact Tendsto.congr (fun n => (hiter n).symm) (h1.comp (h.tendsto_Pa u hu))
  -- an orbit converging to `z₀` and avoiding it is, in the chart, an orbit converging to `0`
  -- and avoiding it, hence eventually enters the petal
  · intro z hzlim hzne
    set u := trChartInv z₀ lam z with hu
    have hz_eq : z = trChart z₀ lam u := by rw [hu]; exact (trChart_trChartInv hlam z).symm
    have hiter : ∀ n : ℕ, F^[n] z = trChart z₀ lam (f^[n] u) := by
      intro n; rw [hz_eq]; exact iterate_trChart hFf' u n
    have hlim : Tendsto (fun n : ℕ => f^[n] u) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => trChartInv z₀ lam (F^[n] z)) atTop
          (nhds (trChartInv z₀ lam z₀)) :=
        ((continuous_trChartInv z₀ lam).tendsto z₀).comp hzlim
      have h2 : trChartInv z₀ lam z₀ = 0 := by simp [trChartInv]
      rw [h2] at h1
      refine Tendsto.congr (fun n => ?_) h1
      rw [hiter n, trChartInv_trChart hlam]
    have hne' : ∀ n : ℕ, f^[n] u ≠ 0 := by
      intro n h0
      refine hzne n ?_
      rw [hiter n, h0]
      simp [trChart]
    obtain ⟨n, hn⟩ := h.enters_Pa u hlim hne'
    exact ⟨n, by rw [hiter n]; exact ⟨f^[n] u, hn, rfl⟩⟩
  · refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · exact fun z _ => (hg_anti z).differentiableWithinAt
    · exact h.φa_fatou.1.2.1.comp (differentiable_trChartInv z₀ lam).differentiableOn
        (fun z hz => (mem_trChart_image hlam).mp hz)
    · intro z hz
      obtain ⟨u, hu, rfl⟩ := hz
      show h.φa (trChartInv z₀ lam (g (trChart z₀ lam u))) =
        star (h.φa (trChartInv z₀ lam (trChart z₀ lam u))) + 1 / 2
      rw [hGg', trChartInv_trChart hlam, trChartInv_trChart hlam]
      exact h.φa_fatou.1.2.2 u hu
    · intro a ha b hb hab
      have h1 := h.φa_fatou.2 ((mem_trChart_image hlam).mp ha)
        ((mem_trChart_image hlam).mp hb) hab
      have h2 := congrArg (trChart z₀ lam) h1
      rwa [trChart_trChartInv hlam, trChart_trChartInv hlam] at h2
  · exact (differentiable_trChart z₀ lam).comp h.Ψ_diff
  · intro w
    rw [h.Ψ_shift, hFf']
  · intro w
    rw [h.Ψ_anti, ← hGg']
  · intro ε hε
    obtain ⟨R, hR⟩ := h.Ψ_small (ε / ‖lam‖) (div_pos hε hnorm)
    refine ⟨R, fun w hw => ⟨?_, ?_⟩⟩
    · intro hcontra
      have h1 : trChartInv z₀ lam (trChart z₀ lam (h.Ψ w)) = trChartInv z₀ lam z₀ :=
        congrArg (trChartInv z₀ lam) hcontra
      rw [trChartInv_trChart hlam] at h1
      have h0 : trChartInv z₀ lam z₀ = 0 := by simp [trChartInv]
      rw [h0] at h1
      exact (hR w hw).1 h1
    · have h2 : ‖h.Ψ w‖ < ε / ‖lam‖ := by simpa using (hR w hw).2
      have hlt : ‖h.Ψ w‖ * ‖lam‖ < ε := (lt_div_iff₀ hnorm).mp h2
      show ‖trChart z₀ lam (h.Ψ w) - z₀‖ < ε
      rw [trChart_apply]
      calc ‖z₀ + lam * h.Ψ w - z₀‖ = ‖lam * h.Ψ w‖ := by rw [add_sub_cancel_left]
        _ = ‖lam‖ * ‖h.Ψ w‖ := norm_mul lam (h.Ψ w)
        _ = ‖h.Ψ w‖ * ‖lam‖ := mul_comm _ _
        _ < ε := hlt
  · obtain ⟨R₀, hR₀⟩ := h.Ψ_inj
    exact ⟨R₀, fun a ha b hb hab => hR₀ ha hb (trChart_injective hlam hab)⟩
  · obtain ⟨R₀, hR₀⟩ := h.Ψ_ends
    exact ⟨R₀, fun w hw hwim => ⟨h.Ψ w, hR₀ w hw hwim, rfl⟩⟩
  -- the covering property rescales by `‖lam‖`
  · intro R
    obtain ⟨r, hr_pos, hr⟩ := h.cover R
    refine ⟨‖lam‖ * r, mul_pos hnorm hr_pos, ?_⟩
    intro z hz0 hzlt
    set u := trChartInv z₀ lam z with hu
    have hu_norm : ‖u‖ = ‖z - z₀‖ / ‖lam‖ := by rw [hu]; simp only [trChartInv, norm_div]
    have hu_pos : 0 < ‖u‖ := by rw [hu_norm]; exact div_pos hz0 hnorm
    have hu_lt : ‖u‖ < r := by
      rw [hu_norm]
      exact (div_lt_iff₀ hnorm).mpr (by rw [mul_comm]; exact hzlt)
    have hmem := hr u (by simpa using hu_pos) (by simpa using hu_lt)
    rcases hmem with hu_Pa | ⟨w, hw, hwΨ⟩
    · exact Or.inl ⟨u, hu_Pa, by rw [hu]; exact trChart_trChartInv hlam z⟩
    · exact Or.inr ⟨w, hw, by rw [hwΨ]; rw [hu]; exact trChart_trChartInv hlam z⟩
  -- ## the extra fields of the repaired flower: the `g`-invariant half-petal `Pg`
  · -- `Pg ⊆ Pa`
    exact Set.image_mono h.Pg_sub
  · -- openness of the image
    rw [show trChart z₀ lam '' h.Pg = trChartInv z₀ lam ⁻¹' h.Pg from by
        ext z; exact mem_trChart_image hlam]
    exact h.isOpen_Pg.preimage (continuous_trChartInv z₀ lam)
  · -- nonemptiness
    exact h.Pg_nonempty.image _
  · -- preconnectedness
    exact h.isPreconnected_Pg.image _ (continuous_trChart z₀ lam).continuousOn
  · -- `F`-invariance
    rintro z ⟨u, hu, rfl⟩
    rw [hFf']
    exact ⟨f u, h.mapsTo_F_Pg hu, rfl⟩
  · -- `g`-invariance
    rintro z ⟨u, hu, rfl⟩
    rw [hGg']
    exact ⟨gU u, h.mapsTo_g_Pg hu, rfl⟩
  · -- entry: an orbit converging to `z₀` enters the half-petal
    intro z hzlim hzne
    set u := trChartInv z₀ lam z with hu
    have hz_eq : z = trChart z₀ lam u := by rw [hu]; exact (trChart_trChartInv hlam z).symm
    have hiter : ∀ n : ℕ, F^[n] z = trChart z₀ lam (f^[n] u) := by
      intro n; rw [hz_eq]; exact iterate_trChart hFf' u n
    have hlim : Tendsto (fun n : ℕ => f^[n] u) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => trChartInv z₀ lam (F^[n] z)) atTop
          (nhds (trChartInv z₀ lam z₀)) :=
        ((continuous_trChartInv z₀ lam).tendsto z₀).comp hzlim
      have h2 : trChartInv z₀ lam z₀ = 0 := by simp [trChartInv]
      rw [h2] at h1
      refine Tendsto.congr (fun n => ?_) h1
      rw [hiter n, trChartInv_trChart hlam]
    have hne' : ∀ n : ℕ, f^[n] u ≠ 0 := by
      intro n h0
      refine hzne n ?_
      rw [hiter n, h0]
      simp [trChart]
    obtain ⟨n, hn⟩ := h.enters_Pg u hlim hne'
    exact ⟨n, by rw [hiter n]; exact ⟨f^[n] u, hn, rfl⟩⟩
  · -- the Abel equation for the second return map
    rintro z ⟨u, hu, rfl⟩
    show h.φa (trChartInv z₀ lam (F (trChart z₀ lam u))) =
      h.φa (trChartInv z₀ lam (trChart z₀ lam u)) + 1
    rw [hFf', trChartInv_trChart hlam, trChartInv_trChart hlam]
    exact h.φa_shift u hu
  -- ## the image of the flower lives in the ball of radius `δ` around `z₀`
  · rintro z ⟨u, hu, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm, trChart_apply, add_sub_cancel_left, norm_mul]
    have h1 : ‖u‖ < δ / ‖lam‖ := by
      have := hPa_small hu
      rwa [Metric.mem_ball, dist_zero_right] at this
    rw [mul_comm]
    exact (lt_div_iff₀ hnorm).mp h1
  · rintro z ⟨u, hu, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm, trChart_apply, add_sub_cancel_left, norm_mul]
    have h1 : ‖u‖ < δ / ‖lam‖ := by
      have := hPg_small hu
      rwa [Metric.mem_ball, dist_zero_right] at this
    rw [mul_comm]
    exact (lt_div_iff₀ hnorm).mp h1
  -- ## saturation transfers with the *same* threshold `X`
  · obtain ⟨X, hX⟩ := hsat
    refine ⟨X, fun w hw => ?_⟩
    obtain ⟨u, hu, huφ⟩ := hX w hw
    refine ⟨trChart z₀ lam u, ⟨u, hu, rfl⟩, ?_⟩
    show h.φa (trChartInv z₀ lam (trChart z₀ lam u)) = w
    rw [trChartInv_trChart hlam, huφ]

end Work.GATE2.PL
