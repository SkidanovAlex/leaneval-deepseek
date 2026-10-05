import Mathlib
import Submission.Work.RPV.V
import Submission.Work.RPV.Defs
import Submission.Work.RPB.B4.periodic_deriv
import Submission.Work.RPB.B5.chartLev_inverse
import Submission.Work.RPB.B5.chord_linear_bound
import Submission.Work.RPB.B5.deriv_slice_eq_fderivWithin
import Submission.Work.RPB.B5.contDiffOn_uproj_comp
import Submission.Work.RPB.B5.exists_add_int_mul_mem_Icc

/-!
# B5: the reduced coordinate of the `ρ`-chart converges to the curve as `σ → 0`

Given the `ρ`-chart `W` of the chord annulus and the inverse chart `rho` (with
`K₀ (W τ t (rho τ t σ)) + 1 = -σ`), the reduced coordinate
`σ ↦ Work.RPV.uproj (W τ t (rho τ t σ))` is a `C¹` perturbation of the curve `σ = 0`, uniformly in
`τ ∈ [0,1]` and in `t ∈ ℝ`, with `2π`-periodicity in `t`:

* `uproj (W τ t (rho τ t 0)) = √2 · CI.c τ t` by hypothesis,
* `rho τ t σ → 0` uniformly in `(τ, t)` as `σ → 0` (compactness on a fundamental domain plus
  `2π`-periodicity in `t`), so the composite `uproj (W τ t (rho τ t σ))` is `C¹` on the slab
  `[0,1] × ℝ × (-δ,δ)` (this uses that `W`,`rho` are only `C¹` on the slab `(-ε,ε)` in the last
  variable);
* on that slab the map
  `(τ,t,σ) ↦ (uproj (W τ t (rho τ t σ)), ∂_t uproj (W τ · (rho τ · σ)) t)` is continuous, hence
  uniformly continuous on the compact `[0,1] × [0,2π] × [-δ,δ]`; combined with periodicity this
  gives the estimate for all `t`.

The main technical tools are delegated: `Work.RPB.B5.contDiffOn_uproj_comp` (the composite is
`C¹`), `Work.RPB.B5.deriv_slice_eq_fderivWithin` (the `t`-derivative is the within-`slab`
differential in the `t`-direction), and `Work.RPB.B5.exists_add_int_mul_mem_Icc` (reduction of `t`
modulo `2π`).
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- The slab `[0,1] × ℝ × (-δ,δ)`, the domain of the composite chart. -/
abbrev slab (δ : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ

/-- The map `x ↦ fderivWithin ℝ f s x v` (fixed direction `v`) is continuous on a set with unique
derivatives. -/
private lemma continuousOn_fderivWithin_apply_const' {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → G}
    {s : Set E} (h : ContDiffOn ℝ 1 f s) (hs : UniqueDiffOn ℝ s) (v : E) :
    ContinuousOn (fun x => fderivWithin ℝ f s x v) s :=
  (h.continuousOn_fderivWithin hs le_rfl).clm_apply continuousOn_const

/-- **Uniform `C¹` closeness at `σ = 0`.**  If `F` is `C¹` on the slab `[0,1] × ℝ × (-δ₁,δ₁)` and
`2π`-periodic in its second ("time") variable, then the family `σ ↦ F (τ,t,σ)`, together with its
`t`-derivative, is uniformly close to `σ = 0` on `[0,1] × ℝ`. -/
private lemma close_of_periodic {F : ℝ × (ℝ × ℝ) → ℂ} {δ₁ : ℝ} (hδ₁ : 0 < δ₁)
    (hFcd : ContDiffOn ℝ 1 F (slab δ₁))
    (hper : ∀ τ σ t, F (τ, t + 2 * Real.pi, σ) = F (τ, t, σ)) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₁ ∧
      ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ σ : ℝ, |σ| ≤ δ → ∀ t : ℝ,
        ‖F (τ, t, σ) - F (τ, t, 0)‖ < η ∧
        ‖deriv (fun u : ℝ => F (τ, u, σ)) t - deriv (fun u : ℝ => F (τ, u, 0)) t‖ < η := by
  intro η hη
  have hSunique : UniqueDiffOn ℝ (slab δ₁) :=
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)).prod
      (uniqueDiffOn_univ.prod (uniqueDiffOn_Ioo (-δ₁) δ₁))
  have hGcont : ContinuousOn
      (fun z : ℝ × (ℝ × ℝ) => fderivWithin ℝ F (slab δ₁) z (0, 1, 0)) (slab δ₁) :=
    continuousOn_fderivWithin_apply_const' hFcd hSunique (0, 1, 0)
  set K : Set (ℝ × (ℝ × ℝ)) :=
    Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2 * Real.pi) ×ˢ Set.Icc (-(δ₁ / 2)) (δ₁ / 2) with hK
  have hKc : IsCompact K := by
    rw [hK]
    exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKsub : K ⊆ slab δ₁ := by
    intro z hz
    rw [hK] at hz
    obtain ⟨h1, h2, h3⟩ := hz
    rw [Set.mem_Icc] at h3
    exact ⟨h1, trivial,
      by rw [Set.mem_Ioo]; exact ⟨by linarith [h3.1], by linarith [h3.2]⟩⟩
  have hFcontK : ContinuousOn F K := hFcd.continuousOn.mono hKsub
  obtain ⟨γ₁, hγ₁pos, hγ₁⟩ :=
    Metric.uniformContinuousOn_iff.mp (hKc.uniformContinuousOn_of_continuous hFcontK) η hη
  have hGcontK : ContinuousOn
      (fun z : ℝ × (ℝ × ℝ) => fderivWithin ℝ F (slab δ₁) z (0, 1, 0)) K := hGcont.mono hKsub
  obtain ⟨γ₂, hγ₂pos, hγ₂⟩ :=
    Metric.uniformContinuousOn_iff.mp (hKc.uniformContinuousOn_of_continuous hGcontK) η hη
  refine ⟨min (δ₁ / 2) (min (γ₁ / 2) (γ₂ / 2)),
    lt_min (by linarith) (lt_min (by linarith) (by linarith)), ?_, ?_⟩
  · exact le_trans (min_le_left _ _) (by linarith)
  · intro τ hτ σ hσ t
    obtain ⟨t₀, n, ht₀, htn⟩ := exists_add_int_mul_mem_Icc t (2 * Real.pi) (by positivity)
    have hσδ : |σ| ≤ δ₁ / 2 := le_trans hσ (min_le_left _ _)
    have hσγ₁ : |σ| ≤ γ₁ / 2 := le_trans hσ (le_trans (min_le_right _ _) (min_le_left _ _))
    have hσγ₂ : |σ| ≤ γ₂ / 2 := le_trans hσ (le_trans (min_le_right _ _) (min_le_right _ _))
    have hσlt : |σ| < δ₁ := lt_of_le_of_lt hσδ (by linarith)
    have hσS : σ ∈ Set.Ioo (-δ₁) δ₁ := by
      rw [Set.mem_Ioo]; exact ⟨(abs_lt.mp hσlt).1, (abs_lt.mp hσlt).2⟩
    have hσmemK : σ ∈ Set.Icc (-(δ₁ / 2)) (δ₁ / 2) := by
      rw [Set.mem_Icc]
      exact ⟨by linarith [(abs_le.mp hσδ).1], by linarith [(abs_le.mp hσδ).2]⟩
    have hm1 : (τ, (t₀, σ)) ∈ K := by rw [hK]; exact ⟨hτ, ht₀, hσmemK⟩
    have hm2 : (τ, (t₀, 0)) ∈ K := by
      rw [hK]
      exact ⟨hτ, ht₀, by rw [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩⟩
    have hdistK : dist (τ, (t₀, σ)) (τ, (t₀, 0)) = |σ| := by
      have heq : ((τ, (t₀, σ)) : ℝ × (ℝ × ℝ)) - (τ, (t₀, 0)) = (0, ((0 : ℝ), σ)) := by
        ext <;> simp
      rw [dist_eq_norm, heq, Prod.norm_def, Prod.norm_def]
      simp
    have hclos1 : ‖F (τ, t₀, σ) - F (τ, t₀, 0)‖ < η := by
      have h := hγ₁ (τ, (t₀, σ)) hm1 (τ, (t₀, 0)) hm2
        (by rw [hdistK]; exact lt_of_le_of_lt hσγ₁ (by linarith))
      simpa [dist_eq_norm] using h
    have hclos2 : ‖(fderivWithin ℝ F (slab δ₁) (τ, t₀, σ)) (0, 1, 0)
        - (fderivWithin ℝ F (slab δ₁) (τ, t₀, 0)) (0, 1, 0)‖ < η := by
      have h := hγ₂ (τ, (t₀, σ)) hm1 (τ, (t₀, 0)) hm2
        (by rw [hdistK]; exact lt_of_le_of_lt hσγ₂ (by linarith))
      simpa [dist_eq_norm] using h
    have hS3 : (τ, (t₀, 0)) ∈ slab δ₁ :=
      ⟨hτ, trivial, by rw [Set.mem_Ioo]; exact ⟨by linarith, by linarith⟩⟩
    have hperF : Function.Periodic (fun s : ℝ => F (τ, s, σ)) (2 * Real.pi) := fun s => hper τ σ s
    have hperF0 : Function.Periodic (fun s : ℝ => F (τ, s, 0)) (2 * Real.pi) := fun s => hper τ 0 s
    have hFtσ : F (τ, t, σ) = F (τ, t₀, σ) := by
      rw [htn]; exact (hperF.int_mul n) t₀
    have hFt0 : F (τ, t, 0) = F (τ, t₀, 0) := by
      rw [htn]; exact (hperF0.int_mul n) t₀
    have hd1 : deriv (fun u : ℝ => F (τ, u, σ)) t
        = (fderivWithin ℝ F (slab δ₁) (τ, t, σ)) (0, 1, 0) :=
      deriv_slice_eq_fderivWithin (A := Set.Icc (0:ℝ) 1) (B := Set.Ioo (-δ₁) δ₁) (F := F)
        hFcd hτ hσS
    have hd2 : deriv (fun u : ℝ => F (τ, u, σ)) t₀
        = (fderivWithin ℝ F (slab δ₁) (τ, t₀, σ)) (0, 1, 0) :=
      deriv_slice_eq_fderivWithin (A := Set.Icc (0:ℝ) 1) (B := Set.Ioo (-δ₁) δ₁) (F := F)
        hFcd hτ hσS
    have hd3 : deriv (fun u : ℝ => F (τ, u, 0)) t₀
        = (fderivWithin ℝ F (slab δ₁) (τ, t₀, 0)) (0, 1, 0) :=
      deriv_slice_eq_fderivWithin (A := Set.Icc (0:ℝ) 1) (B := Set.Ioo (-δ₁) δ₁) (F := F)
        hFcd hτ hS3.2.2
    have hpslice : deriv (fun u : ℝ => F (τ, u, σ)) t = deriv (fun u : ℝ => F (τ, u, σ)) t₀ := by
      have hperd := Work.RPB.B4.periodic_deriv (fun u : ℝ => F (τ, u, σ)) (2 * Real.pi) hperF
      rw [htn]
      exact (hperd.int_mul n) t₀
    have hG1 : (fderivWithin ℝ F (slab δ₁) (τ, t, σ)) (0, 1, 0)
        = (fderivWithin ℝ F (slab δ₁) (τ, t₀, σ)) (0, 1, 0) := by
      rw [← hd1, ← hd2]; exact hpslice
    refine ⟨?_, ?_⟩
    · rw [hFtσ, hFt0]; exact hclos1
    · have hperd0 : deriv (fun u : ℝ => F (τ, u, 0)) t = deriv (fun u : ℝ => F (τ, u, 0)) t₀ := by
        have hperd := Work.RPB.B4.periodic_deriv (fun u : ℝ => F (τ, u, 0)) (2 * Real.pi) hperF0
        rw [htn]
        exact (hperd.int_mul n) t₀
      rw [show deriv (fun u : ℝ => F (τ, u, σ)) t
            = (fderivWithin ℝ F (slab δ₁) (τ, t₀, σ)) (0, 1, 0) from by rw [hd1, hG1],
        show deriv (fun u : ℝ => F (τ, u, 0)) t
            = (fderivWithin ℝ F (slab δ₁) (τ, t₀, 0)) (0, 1, 0) from by rw [hperd0, hd3]]
      exact hclos2

theorem chart_uproj_close (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (rho : ℝ → ℝ → ℝ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hWc : ContDiffOn ℝ 1 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
        (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ε) ε))
    (hrhoc : ContDiffOn ℝ 1 (fun z : ℝ × (ℝ × ℝ) => rho z.1 z.2.1 z.2.2)
        (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ε) ε))
    (hrho0 : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, rho τ t 0 = 0)
    (hrhop : ∀ τ t σ, rho τ (t + 2 * Real.pi) σ = rho τ t σ)
    (hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ))
    (hW0 : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ,
        Work.RPV.uproj (W τ t (rho τ t 0)) = (Real.sqrt 2 : ℂ) * CI.c τ t) :
    ∀ η : ℝ, 0 < η → ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ σ : ℝ, |σ| ≤ ε' → ∀ t : ℝ,
        ‖Work.RPV.uproj (W τ t (rho τ t σ)) - (Real.sqrt 2 : ℂ) * CI.c τ t‖ < η ∧
        ‖deriv (fun u => Work.RPV.uproj (W τ u (rho τ u σ))) t
          - deriv (fun u => (Real.sqrt 2 : ℂ) * CI.c τ u) t‖ < η := by
  intro η hη
  let F : ℝ × (ℝ × ℝ) → ℂ :=
    fun z => Work.RPV.uproj (W z.1 z.2.1 (rho z.1 z.2.1 z.2.2))
  -- `F` is `2π`-periodic in the time variable
  have hFper : ∀ τ σ t, F (τ, t + 2 * Real.pi, σ) = F (τ, t, σ) := by
    intro τ σ t
    change Work.RPV.uproj (W τ (t + 2 * Real.pi) (rho τ (t + 2 * Real.pi) σ))
      = Work.RPV.uproj (W τ t (rho τ t σ))
    rw [hWper τ t (rho τ (t + 2 * Real.pi) σ), hrhop τ t σ, Work.RPV.uproj_Tk]
  -- `F (τ,t,0)` is the limit curve
  have hFeq0 : ∀ τ ∈ Set.Icc (0:ℝ) 1,
      (fun u : ℝ => F (τ, u, 0)) = (fun u : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ u) := by
    intro τ hτ
    funext u
    change Work.RPV.uproj (W τ u (rho τ u 0)) = (Real.sqrt 2 : ℂ) * CI.c τ u
    exact hW0 τ hτ u
  -- `rho τ t σ → 0` uniformly as `σ → 0`
  have hρsmall : ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ ε ∧
      ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ σ : ℝ, |σ| ≤ δ₁ → ∀ t : ℝ, |rho τ t σ| < ε / 2 := by
    have hRcont : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => rho z.1 z.2.1 z.2.2) (slab ε) :=
      hrhoc.continuousOn
    have hKc : IsCompact
        (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2 * Real.pi) ×ˢ Set.Icc (-(ε / 2)) (ε / 2)) :=
      isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    have hKsub : (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2 * Real.pi)
        ×ˢ Set.Icc (-(ε / 2)) (ε / 2)) ⊆ slab ε := by
      intro z hz
      obtain ⟨h1, h2, h3⟩ := hz
      rw [Set.mem_Icc] at h3
      exact ⟨h1, trivial,
        by rw [Set.mem_Ioo]; exact ⟨by linarith [h3.1], by linarith [h3.2]⟩⟩
    obtain ⟨γ, hγpos, hγ⟩ := Metric.uniformContinuousOn_iff.mp
      (hKc.uniformContinuousOn_of_continuous (hRcont.mono hKsub)) (ε / 2) (by linarith)
    refine ⟨min (γ / 2) (ε / 2), lt_min (by linarith) (by linarith),
      le_trans (min_le_right _ _) (by linarith [hε]), ?_⟩
    intro τ hτ σ hσ t
    obtain ⟨t₀, n, ht₀, htn⟩ := exists_add_int_mul_mem_Icc t (2 * Real.pi) (by positivity)
    have hperf : Function.Periodic (fun s : ℝ => rho τ s σ) (2 * Real.pi) := fun s => hrhop τ s σ
    have h1 : rho τ t σ = rho τ t₀ σ := by
      rw [htn]; exact (hperf.int_mul n) t₀
    have hσle : |σ| ≤ ε / 2 := le_trans hσ (min_le_right _ _)
    have hσmem : σ ∈ Set.Icc (-(ε / 2)) (ε / 2) := by
      rw [Set.mem_Icc]
      exact ⟨by linarith [(abs_le.mp hσle).1], by linarith [(abs_le.mp hσle).2]⟩
    have hm1 : (τ, (t₀, σ)) ∈ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2 * Real.pi)
        ×ˢ Set.Icc (-(ε / 2)) (ε / 2)) := ⟨hτ, ht₀, hσmem⟩
    have hm2 : (τ, (t₀, 0)) ∈ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2 * Real.pi)
        ×ˢ Set.Icc (-(ε / 2)) (ε / 2)) :=
      ⟨hτ, ht₀, by rw [Set.mem_Icc]; exact ⟨by linarith [hε], by linarith [hε]⟩⟩
    have hdist : dist (τ, (t₀, σ)) (τ, (t₀, 0)) = |σ| := by
      have heq : ((τ, (t₀, σ)) : ℝ × (ℝ × ℝ)) - (τ, (t₀, 0)) = (0, ((0 : ℝ), σ)) := by
        ext <;> simp
      rw [dist_eq_norm, heq, Prod.norm_def, Prod.norm_def]
      simp
    have hγ' := hγ (τ, (t₀, σ)) hm1 (τ, (t₀, 0)) hm2
      (by rw [hdist]; exact lt_of_le_of_lt (le_trans hσ (min_le_left _ _)) (by linarith))
    have h0 : rho τ t₀ 0 = 0 := hrho0 τ hτ t₀
    rw [Real.dist_eq, h0, sub_zero] at hγ'
    rw [h1]; exact hγ'
  obtain ⟨δ₁, hδ₁pos, hδ₁ε, hρbnd⟩ := hρsmall
  -- the composite is `C¹` on the δ₁-slab
  have hFcd : ContDiffOn ℝ 1 F (slab δ₁) :=
    contDiffOn_uproj_comp (W := W) (rho := rho) (ε := ε) (δ := δ₁) hδ₁ε hWc hrhoc
      (fun τ hτ σ hσ t => lt_of_lt_of_le (hρbnd τ hτ σ (le_of_lt hσ) t) (by linarith))
  -- uniform closeness of `F` and `∂_t F` at `σ = 0`
  have hclose := close_of_periodic (F := F) hδ₁pos hFcd hFper
  obtain ⟨δ, hδpos, hδδ₁, hδb⟩ := hclose η hη
  refine ⟨δ, hδpos, le_trans hδδ₁ hδ₁ε, ?_⟩
  intro τ hτ σ hσ t
  obtain ⟨hb1, hb2⟩ := hδb τ hτ σ hσ t
  refine ⟨?_, ?_⟩
  · change ‖F (τ, t, σ) - (Real.sqrt 2 : ℂ) * CI.c τ t‖ < η
    rw [show (Real.sqrt 2 : ℂ) * CI.c τ t = F (τ, t, 0) from by
      change (Real.sqrt 2 : ℂ) * CI.c τ t = Work.RPV.uproj (W τ t (rho τ t 0))
      rw [← hW0 τ hτ t]]
    exact hb1
  · change ‖deriv (fun u : ℝ => F (τ, u, σ)) t
        - deriv (fun u : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ u) t‖ < η
    rw [show deriv (fun u : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ u) t
          = deriv (fun u : ℝ => F (τ, u, 0)) t from by rw [← hFeq0 τ hτ]]
    exact hb2

end Work.RPB.B5
