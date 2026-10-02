import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open Filter Metric
open scoped Topology

theorem tendstoLocallyUniformly_of_equicontinuous_pointwise {g : ℕ → ℂ → ℂ} {ψ : ℂ → ℂ}
    (heq : ∀ N : ℝ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧
      ∀ n : ℕ, ∀ u v : ℂ, ‖v‖ ≤ N → ‖u - v‖ < δ → ‖g n u - g n v‖ < ε)
    (hpt : ∀ w : ℂ, Filter.Tendsto (fun n => g n w) Filter.atTop (nhds (ψ w))) :
    Continuous ψ ∧ TendstoLocallyUniformly g ψ Filter.atTop := by
  -- A limit of quantities all of which are `< ε` is `≤ ε`.
  have hlim : ∀ (y c : ℂ) (ε : ℝ), 0 < ε → (∀ n : ℕ, ‖g n y - g n c‖ < ε) →
      ‖ψ y - ψ c‖ ≤ ε := by
    intro y c ε _ h
    have ht : Tendsto (fun n : ℕ => ‖g n y - g n c‖) atTop (nhds ‖ψ y - ψ c‖) :=
      ((hpt y).sub (hpt c)).norm
    exact le_of_tendsto ht (Eventually.of_forall fun n => (h n).le)
  -- Continuity of the limit.
  have hcont : Continuous ψ := by
    rw [Metric.continuous_iff]
    intro x ε hε
    obtain ⟨δ, hδpos, -, hδ⟩ := heq (‖x‖ + 1) (ε / 2) (by linarith)
    refine ⟨δ, hδpos, fun y hy => ?_⟩
    have hb : ∀ n : ℕ, ‖g n y - g n x‖ < ε / 2 := fun n =>
      hδ n y x (by linarith [norm_nonneg x]) (by simpa [dist_eq_norm] using hy)
    have hle := hlim y x (ε / 2) (by linarith) hb
    rw [dist_eq_norm]
    linarith
  refine ⟨hcont, ?_⟩
  -- Locally uniform convergence: it suffices to get it on every compact set.
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- A bound for the norms of the points of `K`.
  obtain ⟨N, hN⟩ : ∃ N : ℝ, ∀ x ∈ K, ‖x‖ ≤ N := by
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hK.isBounded
    refine ⟨r, fun x hx => ?_⟩
    have h := hr hx
    rw [Metric.mem_closedBall] at h
    simpa [dist_eq_norm] using h
  set η : ℝ := ε / 3 with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  obtain ⟨δ, hδpos, -, hδ⟩ := heq N η hηpos
  -- Cover `K` by finitely many balls of radius `δ`.
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun c : ℂ => ball c δ)
    (fun c _ => ball_mem_nhds c hδpos)
  -- Pointwise convergence holds simultaneously on the finitely many centres.
  have hfin : ∀ᶠ n in atTop, ∀ c ∈ t, dist (g n c) (ψ c) < η := by
    rw [Finset.eventually_all]
    intro c _
    exact (Metric.tendsto_nhds.mp (hpt c)) η hηpos
  filter_upwards [hfin] with n hn
  intro x hx
  rw [dist_comm]
  obtain ⟨c, hct, hxc⟩ := Set.mem_iUnion₂.mp (hcover hx)
  have hcK : c ∈ K := htK c hct
  have hxc' : ‖x - c‖ < δ := by simpa [dist_eq_norm] using hxc
  have h1 : dist (g n x) (g n c) < η := by
    simpa [dist_eq_norm] using hδ n x c (hN c hcK) hxc'
  have h2 : dist (g n c) (ψ c) < η := hn c hct
  have h3 : dist (ψ c) (ψ x) ≤ η := by
    have hb : ∀ m : ℕ, ‖g m x - g m c‖ < η := fun m => hδ m x c (hN c hcK) hxc'
    have := hlim x c η hηpos hb
    rw [dist_eq_norm, norm_sub_rev]
    exact this
  have htri := dist_triangle4 (g n x) (g n c) (ψ c) (ψ x)
  have h3η : (3 : ℝ) * η = ε := by rw [hη]; ring
  linarith

end Work.MRMT.Found
