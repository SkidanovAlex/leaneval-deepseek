import Mathlib
import Submission.Work.MRMT.Found.norm_symm_sub_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

/-!
# Local uniform convergence of the inverses, from a uniform `1/‖z‖` decay

Let `Φₙ : ℂ ≃ₜ ℂ` be homeomorphisms of the plane whose displacement decays like `Cₙ/‖z‖`
outside the ball of radius `R`: `‖Φₙ z - z‖ ≤ Cₙ / ‖z‖` for `‖z‖ ≥ R`, with `Cₙ ≥ 0` and
`Cₙ → 0`.  If `Φₙ → id` locally uniformly, then also `Φₙ⁻¹ → id` locally uniformly.

The decay hypothesis is what pins the preimages down: for `w` in a compact set `K ⊆ B(0, ρ)`
and `z = Φₙ⁻¹ w`, the triangle inequality gives
`‖z‖ ≤ ‖w‖ + ‖Φₙ z - z‖ ≤ ρ + Cₙ / ‖z‖ ≤ ρ + Cₙ / R`,
so once `Cₙ ≤ R` the preimage `z` lies in the fixed ball `B(0, S)`, `S = max R (ρ + 2)`.
On that ball `Φₙ → id` uniformly, hence `‖Φₙ⁻¹ w - w‖ = ‖z - Φₙ z‖` is small uniformly.
-/

open Filter Metric

theorem tendstoLocallyUniformly_symm_of_decay {Φs : ℕ → ℂ ≃ₜ ℂ} {Cs : ℕ → ℝ} {R : ℝ}
    (hR : 1 ≤ R) (hC : ∀ n : ℕ, 0 ≤ Cs n)
    (hdec : ∀ (n : ℕ) (z : ℂ), R ≤ ‖z‖ → ‖Φs n z - z‖ ≤ Cs n / ‖z‖)
    (hCtend : Filter.Tendsto Cs Filter.atTop (nhds 0))
    (hΦ : TendstoLocallyUniformly (fun n => (Φs n : ℂ → ℂ)) id Filter.atTop) :
    TendstoLocallyUniformly (fun n => ((Φs n).symm : ℂ → ℂ)) id Filter.atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨ρ, hρ⟩ := hK.isBounded.exists_norm_le
  set S : ℝ := max R (ρ + 2) with hSdef
  have hRpos : (0 : ℝ) < R := by linarith
  have hSR : R ≤ S := le_max_left _ _
  have hSρ : ρ + 2 ≤ S := le_max_right _ _
  have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.mp hΦ)
      (Metric.closedBall 0 S) (isCompact_closedBall 0 S)
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  -- Eventually the decay constant is at most `R`.
  have hint : ∀ᶠ n in Filter.atTop, Cs n ≤ R := by
    have h0 : ∀ᶠ n in Filter.atTop, Cs n < R := (tendsto_order.mp hCtend).2 R hRpos
    filter_upwards [h0] with n hn
    exact le_of_lt hn
  filter_upwards [hunif ε hε, hint] with n hn1 hn2
  intro w hw
  have hwρ : ‖w‖ ≤ ρ := hρ w hw
  set z : ℂ := ((Φs n).symm : ℂ → ℂ) w with hzdef
  have hFz : (Φs n : ℂ → ℂ) z = w := by
    rw [hzdef]; exact (Φs n).apply_symm_apply w
  -- The preimage `z` stays in the fixed ball of radius `S`.
  have hzS : ‖z‖ ≤ S := by
    rcases le_or_gt R ‖z‖ with hge | hlt
    · have hd := hdec n z hge
      have hwz : ‖w - z‖ = ‖(Φs n : ℂ → ℂ) z - z‖ := by rw [hFz]
      have h3 : ‖z‖ ≤ ‖w‖ + ‖w - z‖ := by
        have h4 : w - (w - z) = z := by ring
        calc ‖z‖ = ‖w - (w - z)‖ := by rw [h4]
          _ ≤ ‖w‖ + ‖w - z‖ := norm_sub_le _ _
      have hdiv : Cs n / ‖z‖ ≤ Cs n / R :=
        div_le_div_of_nonneg_left (hC n) hRpos hge
      have hdiv1 : Cs n / R ≤ 1 := by rw [div_le_one hRpos]; exact hn2
      linarith
    · linarith
  have hzmem : z ∈ Metric.closedBall (0 : ℂ) S := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hzS
  have hdist : dist z ((Φs n : ℂ → ℂ) z) < ε := hn1 z hzmem
  rw [hFz, dist_eq_norm] at hdist
  simp only [id_eq]
  rw [dist_comm, dist_eq_norm]
  exact hdist

end Work.FBif
