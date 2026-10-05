import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.chartLev_inverse
import Submission.Work.RPB.B5.chordSurf_rhoChart_full
import Submission.Work.RPB.B5.halfChordSmooth
import Submission.Work.RPB.B5.slabExtendPeriodic
import Submission.Work.RPB.B5.slabUniformInverseStrong
import Submission.Work.RPB.B5.C12.slabGlobalExtendPeriodic_C12
import Submission.Work.RPB.B5.C12.slabInverseContDiffOn_C12
import Submission.Work.RPB.B5.C12.chordSurf_rhoChart_full_C12

/-!
# `Work.RPB.B5.chart_C12`: the `ρ`-chart and its level inverse in `C¹²`

This file strengthens `Work.RPB.B5.chordSurf_rhoChart_full` (which produces the `ρ = r²`-chart
`W` of the chord annulus at order `8`) and `Work.RPB.B5.chartLev_inverse_strong` (the level
inverse `rho` at order `8`) to order `12`, as needed by the collar construction
(`Work.RPB.B5.collar_exists`), where one derivative is lost in passing from the collar shape to
its area and another in integrating.

The proof is a mechanical rerun of the `C⁸` chain at order `12`:

* `Work.RPB.B5.C12.chordSurf_rhoChart_full_C12` — the chart `W` at order `12`,
* `Work.RPB.B5.C12.slabGlobalExtendPeriodic_C12` — the Seeley extension of the level function,
* `Work.RPB.B5.C12.slabInverseContDiffOn_C12` — the inverse function theorem on a slab at order
  `12`,
* and here: the assembled uniform inversion `slabUniformInverseStrong_C12`, the level inverse
  `chartLev_inverse_strong_C12` and the final packaged statement `chart_C12`.
-/

open RectangularPegProblem
open Manifold Complex Real
open Set Filter
open scoped ContDiff Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-! ## `C¹²` smoothness of the level function of a chart -/

lemma contDiff_K0_add_one_infty :
    ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun x : Work.RPV.PS => Work.RPV.K0 x + 1) := by
  simp only [Work.RPV.K0]
  fun_prop

lemma chartLev_contDiffOn_C12 {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρ₀ : ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2) (chartBox ρ₀)) :
    ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => chartLev W z.1 z.2.1 z.2.2) (chartBox ρ₀) :=
  (ContDiff.comp_contDiffOn (contDiff_K0_add_one_infty.of_le (by simp)) hW).congr
    (fun _ _ => rfl)

lemma chartLev_slice_contDiffOn_C12 {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρ₀ : ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2) (chartBox ρ₀))
    (τ t : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffOn ℝ 12 (fun ρ : ℝ => chartLev W τ t ρ) (Set.Ioo (-ρ₀) ρ₀) :=
  ((chartLev_contDiffOn_C12 hW).comp
    (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
    (fun _ hρ => ⟨hτ, Set.mem_univ _, hρ⟩)).congr (fun _ _ => rfl)

/-! ## The uniform inversion at order 12 -/

theorem slabUniformInverseStrong_C12 (S : ℝ → ℝ → ℝ → ℝ) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀)
    (hS : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2)
        (Set.Ioo (-1) 2 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hper : ∀ τ t ρ, S τ (t + 2 * Real.pi) ρ = S τ t ρ)
    (h0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, S τ t 0 = 0)
    (hδ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, 0 < deriv (fun ρ => S τ t ρ) 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ ρ₀ ∧ ∃ rho : ℝ → ℝ → ℝ → ℝ,
      ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => rho z.1 z.2.1 z.2.2)
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ε) ε) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, rho τ t 0 = 0) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ σ ∈ Set.Ioo (-ε) ε,
        rho τ t σ ∈ Set.Ioo (-ρ₀) ρ₀) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ σ ∈ Set.Ioo (-ε) ε,
        S τ t (rho τ t σ) = σ) ∧
      (∀ τ t σ, rho τ (t + 2 * Real.pi) σ = rho τ t σ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ ρ ∈ Set.Ioo (-ε) ε,
        rho τ t (S τ t ρ) = ρ) := by
  obtain ⟨S', hS'12, hS'per, hS'0, hS'agree⟩ :=
    C12.slabGlobalExtendPeriodic_C12 S ρ₀ hρ₀ hS hper h0
  have hS'8 : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => S' z.1 z.2.1 z.2.2) :=
    hS'12.of_le (by norm_num)
  -- Derivative positivity at `ρ = 0` for the globalized family, on `[0,1]`.
  have hS'δ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, 0 < deriv (fun ρ => S' τ t ρ) 0 := by
    intro τ hτ t
    have hmem : Set.Ioo (-(ρ₀ / 2)) (ρ₀ / 2) ∈ nhds (0 : ℝ) :=
      isOpen_Ioo.mem_nhds (by constructor <;> linarith)
    have hev : (fun ρ => S' τ t ρ) =ᶠ[nhds (0 : ℝ)] (fun ρ => S τ t ρ) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      exact ⟨Set.Ioo (-(ρ₀ / 2)) (ρ₀ / 2), hmem, fun ρ hρ => by
        rw [Set.mem_Ioo] at hρ
        exact hS'agree τ hτ t ρ (by rw [abs_lt]; exact hρ)⟩
    rw [hev.deriv_eq]
    exact hδ τ hτ t
  obtain ⟨ε₀', hε₀', δ, hδ0, M, hM0, hbound⟩ := slabDerivBounds S' hS'8 hS'per hS'δ
  -- Shrink the positivity radius so that `(-ε₀,ε₀) ⊆ (-ρ₀/2, ρ₀/2)`, where `S' = S`.
  set ε₀ : ℝ := min ε₀' (ρ₀ / 2) with hε₀def
  have hε₀0 : 0 < ε₀ := lt_min hε₀' (by linarith)
  have hε₀le : ε₀ ≤ ε₀' := min_le_left _ _
  have hε₀le2 : ε₀ ≤ ρ₀ / 2 := min_le_right _ _
  have hbound' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ ρ ∈ Set.Icc (-ε₀) ε₀,
      δ ≤ deriv (fun ρ => S' τ t ρ) ρ ∧ |deriv (fun ρ => S' τ t ρ) ρ| ≤ M := by
    intro τ hτ t ρ hρ
    exact hbound τ hτ t ρ ⟨le_trans (neg_le_neg hε₀le) hρ.1, le_trans hρ.2 hε₀le⟩
  have hderivfn : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ ρ ∈ Set.Icc (-ε₀) ε₀,
      δ ≤ deriv (fun ρ => S' τ t ρ) ρ := fun τ hτ t ρ hρ => (hbound' τ hτ t ρ hρ).1
  have hM := slabMonoExistsUnique S' hS'8 hS'0 δ ε₀ hδ0 hε₀0 hderivfn
  have hcover : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ σ ∈ Set.Ioo (-(δ*ε₀)) (δ*ε₀),
      ∃! ρ, ρ ∈ Set.Ioo (-ε₀) ε₀ ∧ S' τ t ρ = σ :=
    fun τ hτ t σ hσ => (hM τ hτ t).2.2.2 σ (abs_lt.mpr hσ)
  have hderivne : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ ρ ∈ Set.Ioo (-ε₀) ε₀,
      deriv (fun ρ => S' τ t ρ) ρ ≠ 0 := by
    intro τ hτ t ρ hρ
    have h := (hbound' τ hτ t ρ (Set.Ioo_subset_Icc_self hρ)).1
    intro hc; rw [hc] at h; linarith
  have hcd := C12.slabInverseContDiffOn_C12 S' hS'12 ε₀ δ hε₀0 hδ0 hderivne hcover
  -- The uniform interval, also capped by `ε₀` (for the right-inverse identity) and by `ρ₀ / 2`.
  set ε : ℝ := min (δ * ε₀) (min (ρ₀ / 2) ε₀) with hεdef
  have hεpos : 0 < ε := lt_min (mul_pos hδ0 hε₀0) (lt_min (by linarith) hε₀0)
  have hεle : ε ≤ ρ₀ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεle2 : ε ≤ δ * ε₀ := min_le_left _ _
  have hεle3 : ε ≤ ε₀ := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨ε, hεpos, le_trans hεle (by linarith), ?_⟩
  refine ⟨fun τ t σ => Work.RPB.B3.inverseR S' ε₀ τ t σ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    refine hcd.mono ?_
    intro z hz
    have hz' := hz
    simp only [Set.mem_prod, Set.mem_Icc, Set.mem_univ, Set.mem_Ioo, true_and] at hz'
    exact Set.mem_prod.mpr ⟨hz'.1, Set.mem_prod.mpr
      ⟨trivial, Set.Ioo_subset_Ioo (by linarith [hεle2]) (by linarith [hεle2]) hz'.2⟩⟩
  · -- vanishes at zero
    intro τ hτ t
    refine Work.RPB.B3.inverseR_eq (S := S') (ε₀ := ε₀) (τ := τ) (t := t)
      (σ := 0) (ρ := 0) ⟨by linarith, by linarith⟩ (hS'0 τ t) ?_
    intro ρ' hρ' hS'ρ'
    have hmono := (hM τ hτ t).1
    have h0mem : (0 : ℝ) ∈ Set.Icc (-ε₀) ε₀ := ⟨by linarith, by linarith⟩
    exact hmono.injOn (Set.Ioo_subset_Icc_self hρ') h0mem (by rw [hS'ρ', hS'0 τ t])
  · -- value bound `rho ∈ (-ρ₀, ρ₀)`
    intro τ hτ t σ hσ
    have hσlt : |σ| < δ * ε₀ := lt_of_lt_of_le (abs_lt.mpr hσ) hεle2
    have hex : ∃ ρ, ρ ∈ Set.Ioo (-ε₀) ε₀ ∧ S' τ t ρ = σ :=
      ExistsUnique.exists ((hM τ hτ t).2.2.2 σ hσlt)
    exact Set.Ioo_subset_Ioo (by linarith [hε₀le2]) (by linarith [hε₀le2])
      (Work.RPB.B3.inverseR_spec hex).1
  · -- left inverse property `S τ t (rho τ t σ) = σ`
    intro τ hτ t σ hσ
    have hσlt : |σ| < δ * ε₀ := lt_of_lt_of_le (abs_lt.mpr hσ) hεle2
    have hex : ∃ ρ, ρ ∈ Set.Ioo (-ε₀) ε₀ ∧ S' τ t ρ = σ :=
      ExistsUnique.exists ((hM τ hτ t).2.2.2 σ hσlt)
    obtain ⟨hmem, heq⟩ := Work.RPB.B3.inverseR_spec hex
    rw [← hS'agree τ hτ t _ (by
      rw [abs_lt]
      exact ⟨by linarith [hmem.1, hε₀le2], by linarith [hmem.2, hε₀le2]⟩)]
    exact heq
  · -- periodicity in `t`, for every `τ`
    intro τ t σ
    exact inverseR_periodic S' ε₀ hS'per τ t σ
  · -- right inverse property `rho τ t (S τ t ρ) = ρ`
    intro τ hτ t ρ hρ
    have hρabs : |ρ| < ρ₀ / 2 := by
      rw [abs_lt]
      exact ⟨by linarith [hρ.1, hεle], by linarith [hρ.2, hεle]⟩
    have hρmem : ρ ∈ Set.Ioo (-ε₀) ε₀ := by
      rw [abs_lt] at hρabs
      exact ⟨by linarith [hρ.1, hεle3], by linarith [hρ.2, hεle3]⟩
    have hSρ : S' τ t ρ = S τ t ρ := hS'agree τ hτ t ρ hρabs
    refine Work.RPB.B3.inverseR_eq (S := S') (ε₀ := ε₀) (τ := τ) (t := t)
      (σ := S τ t ρ) (ρ := ρ) hρmem hSρ ?_
    intro ρ' hρ' hS'ρ'
    have hmono := (hM τ hτ t).1
    exact hmono.injOn (Set.Ioo_subset_Icc_self hρ') (Set.Ioo_subset_Icc_self hρmem)
      (by rw [hS'ρ', hSρ])

/-! ## The level inverse at order 12 -/

theorem chartLev_inverse_strong_C12 (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ) (ρ₀ : ℝ)
    (hρ₀ : 0 < ρ₀) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ))
    (hchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ ρ₀ ∧ ∃ rho : ℝ → ℝ → ℝ → ℝ,
      ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => rho z.1 z.2.1 z.2.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ε) ε) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, rho τ t 0 = 0) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-ε) ε,
        rho τ t σ ∈ Set.Ioo (-ρ₀) ρ₀) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-ε) ε,
        Work.RPV.K0 (W τ t (rho τ t σ)) + 1 = -σ) ∧
      (∀ τ t σ, rho τ (t + 2 * Real.pi) σ = rho τ t σ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ ρ ∈ Set.Ioo (-ε) ε,
        rho τ t (-(Work.RPV.K0 (W τ t ρ) + 1)) = ρ) := by
  obtain ⟨hc, hc_sm, _hc_even, _hc_per, hc_zero, hc_half⟩ :=
    halfChordSmooth CI.c CI.smooth CI.per
  obtain ⟨F, hF_sm, hF_eq, hF_per⟩ :=
    slabExtendPeriodic (fun τ t ρ => chartLev W τ t ρ) 12 ρ₀ hρ₀ 1 one_pos
      (chartLev_contDiffOn_C12 hW) (fun τ t ρ => chartLev_per hper τ t ρ)
  have htwo : (1 : ℝ) + 1 = 2 := by norm_num
  rw [htwo] at hF_sm
  obtain ⟨ε, hε0, hερ₀, rhoS, hrhoS_sm, hrhoS_zero, hrhoS_range, hrhoS_inv,
      hrhoS_per, hrhoS_left⟩ :=
    slabUniformInverseStrong_C12 F ρ₀ hρ₀ hF_sm hF_per
      (fun τ hτ t => by
        rw [hF_eq τ hτ t 0 ⟨by linarith, hρ₀⟩]
        exact chartLev_zero hρ₀ hc hc_sm hc_half hchord τ t
          ((chartLev_slice_contDiffOn_C12 hW τ t hτ).of_le (by norm_num)) hτ)
      (fun τ hτ t => by
        have hderiv_eq : deriv (fun ρ => F τ t ρ) 0
            = deriv (fun ρ => chartLev W τ t ρ) 0 := by
          apply Filter.EventuallyEq.deriv_eq
          have hmem : Set.Ioo (-ρ₀) ρ₀ ∈ 𝓝 (0 : ℝ) :=
            isOpen_Ioo.mem_nhds ⟨by linarith, hρ₀⟩
          filter_upwards [hmem] with ρ hρ
          exact hF_eq τ hτ t ρ hρ
        rw [hderiv_eq, chartLev_deriv_zero hρ₀ hc hc_sm hc_zero hc_half hchord τ t
          ((chartLev_slice_contDiffOn_C12 hW τ t hτ).of_le (by norm_num)) hτ]
        exact pow_pos (norm_pos_iff.mpr (CI.imm τ hτ t)) 2)
  refine ⟨ε, hε0, hερ₀, fun τ t σ => rhoS τ t (-σ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness of the sign flip
    have hg : ContDiff ℝ 12 (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.1, -z.2.2))) := by fun_prop
    have hmap : Set.MapsTo (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.1, -z.2.2)))
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ε) ε)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ε) ε) := by
      rintro ⟨τ, t, σ⟩ ⟨hτ, -, hσ⟩
      rw [Set.mem_Ioo] at hσ
      exact ⟨hτ, trivial, by rw [Set.mem_Ioo]; exact ⟨by linarith [hσ.2], by linarith [hσ.1]⟩⟩
    exact (hrhoS_sm.comp hg.contDiffOn hmap).congr (fun _ _ => rfl)
  · -- vanishes at zero
    intro τ hτ t
    simpa using hrhoS_zero τ hτ t
  · -- value bound
    intro τ hτ t σ hσ
    rw [Set.mem_Ioo] at hσ
    exact hrhoS_range τ hτ t (-σ)
      (by rw [Set.mem_Ioo]; exact ⟨by linarith [hσ.2], by linarith [hσ.1]⟩)
  · -- level equation
    intro τ hτ t σ hσ
    rw [Set.mem_Ioo] at hσ
    have hσ' : -σ ∈ Set.Ioo (-ε) ε := by
      rw [Set.mem_Ioo]; exact ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    have hmem : rhoS τ t (-σ) ∈ Set.Ioo (-ρ₀) ρ₀ := hrhoS_range τ hτ t (-σ) hσ'
    have h1 : F τ t (rhoS τ t (-σ)) = -σ := hrhoS_inv τ hτ t (-σ) hσ'
    have h2 : F τ t (rhoS τ t (-σ)) = chartLev W τ t (rhoS τ t (-σ)) :=
      hF_eq τ hτ t (rhoS τ t (-σ)) hmem
    show chartLev W τ t (rhoS τ t (-σ)) = -σ
    rw [← h2, h1]
  · -- periodicity in `t`
    intro τ t σ
    show rhoS τ (t + 2 * Real.pi) (-σ) = rhoS τ t (-σ)
    exact hrhoS_per τ t (-σ)
  · -- two-sided inverse
    intro τ hτ t ρ hρ
    rw [Set.mem_Ioo] at hρ
    have hmem : ρ ∈ Set.Ioo (-ρ₀) ρ₀ :=
      ⟨by linarith [hρ.1, hερ₀], by linarith [hρ.2, hερ₀]⟩
    show rhoS τ t (-(-(chartLev W τ t ρ))) = ρ
    rw [neg_neg, ← hF_eq τ hτ t ρ hmem]
    exact hrhoS_left τ hτ t ρ hρ

/-! ## The final statement -/

theorem chart_C12 (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) :
    ∃ ρ₀ : ℝ, Real.pi ^ 2 / 4 < ρ₀ ∧ ∃ W : ℝ → ℝ → ℝ → Work.RPV.PS,
      ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) ∧
      (∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ)) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r) ∧
      (∃ ε : ℝ, 0 < ε ∧ ε ≤ ρ₀ ∧ ∃ rho : ℝ → ℝ → ℝ → ℝ,
        ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => rho z.1 z.2.1 z.2.2)
          (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ε) ε) ∧
        (∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, rho τ t 0 = 0) ∧
        (∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-ε) ε,
          rho τ t σ ∈ Set.Ioo (-ρ₀) ρ₀) ∧
        (∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-ε) ε,
          Work.RPV.K0 (W τ t (rho τ t σ)) + 1 = -σ) ∧
        (∀ τ t σ, rho τ (t + 2 * Real.pi) σ = rho τ t σ) ∧
        (∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, ∀ ρ ∈ Set.Ioo (-ε) ε,
          rho τ t (-(Work.RPV.K0 (W τ t ρ) + 1)) = ρ)) := by
  obtain ⟨ρ₀, hρ₀, W, hW, hchord, hper, _⟩ := C12.chordSurf_rhoChart_full_C12 CI a ha
  have hρ₀pos : 0 < ρ₀ := lt_trans (by positivity) hρ₀
  refine ⟨ρ₀, hρ₀, W, hW, hper, ?_, ?_⟩
  · -- the identification with the chord surface, now on the open range
    intro τ hτ t r hr
    exact hchord τ hτ t r ⟨hr.1, le_of_lt hr.2⟩
  · -- the level inverse
    obtain ⟨ε, hε0, hερ₀, rho, hrho_sm, hrho_zero, hrho_range, hrho_inv, hrho_per, hrho_left⟩ :=
      chartLev_inverse_strong_C12 CI a ρ₀ hρ₀pos W hW hper
        (fun τ hτ t r hr => hchord τ hτ t r ⟨hr.1, le_of_lt hr.2⟩)
    exact ⟨ε, hε0, hερ₀, rho, hrho_sm, hrho_zero, hrho_range, hrho_inv, hrho_per,
      fun τ hτ t ρ hρ => by
        have h := hrho_left τ hτ t ρ hρ
        simpa only [chartLev] using h⟩

end Work.RPB.B5

end
