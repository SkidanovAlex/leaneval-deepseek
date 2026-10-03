import Mathlib
import Submission.Work.Parab.inversion.deriv_ne_zero_of_injOn

/-!
# A uniform lower bound for `‖deriv (H β) w‖` on a compact parameter set

Let `H : ℂ → ℂ → ℂ` be jointly continuous on `Λ × Ω` (`Λ` compact, `Ω` open) and suppose that
for every `β ∈ Λ` the map `H β` is holomorphic on `Ω` and *injective* on `Ω`.  Then `‖deriv (H β) w‖`
is bounded below by a positive constant, uniformly for `β ∈ Λ` and `w ∈ S`, `S ⊆ Ω` compact.

The mathematical content of the proof is:

* for fixed `β`, injectivity plus holomorphy gives `deriv (H β) w ≠ 0` for *every* `w ∈ Ω`
  (`Work.Parab.inversion.deriv_ne_zero_of_injOn`);
* joint continuity of `(β, w) ↦ H β w` makes `β ↦ H β` continuous for the topology of locally
  uniform convergence on `Ω` (compactness of `Λ`);
* hence `β ↦ deriv (H β)` is again locally uniformly convergent
  (`TendstoLocallyUniformlyOn.deriv`), i.e. `(β, w) ↦ deriv (H β) w` is continuous on `Λ × Ω`;
* a continuous, everywhere positive function on the compact set `Λ × S` attains a positive minimum.
-/

namespace Work.L62

namespace DerivULB

open Filter Set Metric
open scoped Topology

/-- Joint continuity of `(β, w) ↦ H β w` on `Λ × Ω` makes `β ↦ H β` continuous at every `β₀ ∈ Λ`
for the topology of locally uniform convergence on the open set `Ω`. -/
theorem tendstoLocallyUniformlyOn_family {Ω Λ : Set ℂ} {H : ℂ → ℂ → ℂ}
    (hΩo : IsOpen Ω) (hΛc : IsCompact Λ)
    (hcont : ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2) (Λ ×ˢ Ω)) :
    ∀ β₀ ∈ Λ, TendstoLocallyUniformlyOn (fun β => H β) (H β₀) (𝓝[Λ] β₀) Ω := by
  intro β₀ hβ₀
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hΩo]
  intro K hKΩ hKc
  exact ((hΛc.prod hKc).uniformContinuousOn_of_continuous
    (hcont.mono (Set.prod_mono_right hKΩ))).tendstoUniformlyOn hβ₀

/-- The derivative family inherits the locally uniform convergence (`Weierstrass`). -/
theorem tendstoLocallyUniformlyOn_deriv_family {Ω Λ : Set ℂ} {H : ℂ → ℂ → ℂ}
    (hΩo : IsOpen Ω) (hΛc : IsCompact Λ)
    (hHdiff : ∀ β ∈ Λ, DifferentiableOn ℂ (H β) Ω)
    (hcont : ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2) (Λ ×ˢ Ω)) :
    ∀ β₀ ∈ Λ, TendstoLocallyUniformlyOn (fun β => deriv (H β)) (deriv (H β₀)) (𝓝[Λ] β₀) Ω := by
  intro β₀ hβ₀
  exact (tendstoLocallyUniformlyOn_family hΩo hΛc hcont β₀ hβ₀).deriv
    (Filter.eventually_of_mem self_mem_nhdsWithin (fun β hβ => hHdiff β hβ)) hΩo

/-- The two-variable map `(β, w) ↦ deriv (H β) w` is continuous on `Λ × Ω`. -/
theorem continuousOn_deriv_family {Ω Λ : Set ℂ} {H : ℂ → ℂ → ℂ}
    (hΩo : IsOpen Ω) (hΛc : IsCompact Λ)
    (hHdiff : ∀ β ∈ Λ, DifferentiableOn ℂ (H β) Ω)
    (hcont : ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2) (Λ ×ˢ Ω)) :
    ContinuousOn (fun p : ℂ × ℂ => deriv (H p.1) p.2) (Λ ×ˢ Ω) := by
  rw [Metric.continuousOn_iff]
  intro p hp ε hε
  obtain ⟨hβΛ, hzΩ⟩ := hp
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hΩo.mem_nhds hzΩ)
  have hKΩ : Metric.closedBall p.2 (r / 2) ⊆ Ω := by
    intro w hw
    rw [Metric.mem_closedBall] at hw
    exact hball (by rw [Metric.mem_ball]; linarith)
  have hKc : IsCompact (Metric.closedBall p.2 (r / 2)) := isCompact_closedBall _ _
  have hUS : TendstoUniformlyOn (fun β => deriv (H β)) (deriv (H p.1)) (𝓝[Λ] p.1)
      (Metric.closedBall p.2 (r / 2)) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩo).mp
      (tendstoLocallyUniformlyOn_deriv_family hΩo hΛc hHdiff hcont p.1 hβΛ)
      (Metric.closedBall p.2 (r / 2)) hKΩ hKc
  have hev : ∀ᶠ β in 𝓝[Λ] p.1,
      ∀ w ∈ Metric.closedBall p.2 (r / 2), dist (deriv (H p.1) w) (deriv (H β) w) < ε / 2 :=
    (Metric.tendstoUniformlyOn_iff.mp hUS) (ε / 2) (by linarith)
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.mem_nhdsWithin_iff.mp (Filter.eventually_iff.mp hev)
  have hc2 : ContinuousOn (deriv (H p.1)) Ω := ((hHdiff p.1 hβΛ).deriv hΩo).continuousOn
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.continuousOn_iff.mp hc2 p.2 hzΩ (ε / 2) (by linarith)
  refine ⟨min δ₁ (min δ₂ (r / 2)), lt_min hδ₁pos (lt_min hδ₂pos (by linarith)), ?_⟩
  intro a ha had
  obtain ⟨haΛ, haΩ⟩ := ha
  rw [Prod.dist_eq] at had
  have ha1 : dist a.1 p.1 < δ₂ :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) had)
      (le_trans (min_le_right δ₁ (min δ₂ (r / 2))) (min_le_left δ₂ (r / 2)))
  have ha2δ₁ : dist a.2 p.2 < δ₁ :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) had) (min_le_left _ _)
  have ha2r : dist a.2 p.2 < r / 2 :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) had)
      (le_trans (min_le_right δ₁ (min δ₂ (r / 2))) (min_le_right δ₂ (r / 2)))
  have ha2K : a.2 ∈ Metric.closedBall p.2 (r / 2) := by
    rw [Metric.mem_closedBall]; exact le_of_lt ha2r
  have h1 : dist (deriv (H p.1) a.2) (deriv (H a.1) a.2) < ε / 2 :=
    hδ₂ ⟨by rw [Metric.mem_ball]; exact ha1, haΛ⟩ a.2 ha2K
  have h2 : dist (deriv (H p.1) a.2) (deriv (H p.1) p.2) < ε / 2 :=
    hδ₁ a.2 haΩ ha2δ₁
  calc dist (deriv (H a.1) a.2) (deriv (H p.1) p.2)
      ≤ dist (deriv (H a.1) a.2) (deriv (H p.1) a.2)
        + dist (deriv (H p.1) a.2) (deriv (H p.1) p.2) := dist_triangle _ _ _
    _ = dist (deriv (H p.1) a.2) (deriv (H a.1) a.2)
        + dist (deriv (H p.1) a.2) (deriv (H p.1) p.2) := by rw [dist_comm]
    _ < ε := by linarith

end DerivULB

set_option linter.unusedVariables false in
theorem deriv_uniform_lower_bound {Ω Λ S : Set ℂ} {H : ℂ → ℂ → ℂ}
    (hΩo : IsOpen Ω) (hΛc : IsCompact Λ) (hSc : IsCompact S) (hSΩ : S ⊆ Ω)
    (hS0 : (0 : ℂ) ∉ S)
    (hHdiff : ∀ β ∈ Λ, DifferentiableOn ℂ (H β) Ω)
    (hfix : ∀ β ∈ Λ, H β 0 = 0) (hinj : ∀ β ∈ Λ, Set.InjOn (H β) Ω)
    (hcont : ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2) (Λ ×ˢ Ω)) :
    ∃ d : ℝ, 0 < d ∧ ∀ β ∈ Λ, ∀ w ∈ S, d ≤ ‖deriv (H β) w‖ := by
  by_cases hne : (Λ ×ˢ S).Nonempty
  · have hΦc : ContinuousOn (fun p : ℂ × ℂ => ‖deriv (H p.1) p.2‖) (Λ ×ˢ S) :=
      ((DerivULB.continuousOn_deriv_family hΩo hΛc hHdiff hcont).mono
        (Set.prod_mono_right hSΩ)).norm
    obtain ⟨p, hp, hmin⟩ := (hΛc.prod hSc).exists_isMinOn hne hΦc
    refine ⟨‖deriv (H p.1) p.2‖, ?_, ?_⟩
    · exact norm_pos_iff.mpr (Work.Parab.inversion.deriv_ne_zero_of_injOn hΩo
        (hHdiff p.1 hp.1) (hinj p.1 hp.1) p.2 (hSΩ hp.2))
    · intro β hβ w hw
      exact (Filter.eventually_principal.mp hmin) (β, w) (Set.mem_prod.mpr ⟨hβ, hw⟩)
  · refine ⟨1, one_pos, ?_⟩
    intro β hβ w hw
    exact absurd ⟨(β, w), Set.mem_prod.mpr ⟨hβ, hw⟩⟩ hne

end Work.L62
