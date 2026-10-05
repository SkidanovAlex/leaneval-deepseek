import Mathlib
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.kappa_shape_basic
import Submission.Work.RPB.B5.kappa_shape_geom_small
import Submission.Work.RPB.B5.kdiagM_signedArea

/-!
# B5: area law and embeddedness of the normalised collar `kgam` for `σ ≥ 0`

This file proves `Work.RPB.B5.kappa_collar_area_emb`: for small enough `δ` the normalised collar
`kgam CI W ρh δ k τ σ` has signed area `2π(1+σ)`, non-vanishing `t`-derivative and is injective up
to the period `2π`, for every `τ ∈ [0,1]` and every `σ ≥ 0`.

The proof splits at `σ = δ`:

* **near region** `σ ∈ [0, δ]`.  Here `kappa_shape_geom_small` gives `0 < karS`, the non-vanishing
  derivative and the injectivity of the *glued shape* `kshape`.  The normalised collar is
  `kgam = kdiagM (kg) ∘ kshape` with `kg = 2π(1+σ)/karS ≠ 0`; the real-linear map `kdiagM (kg)`
  scales the signed area by `kg` (`kdiagM_signedArea`) and, being injective, preserves both the
  non-vanishing derivative and injectivity modulo `2π`.

* **far region** `σ ≥ δ`.  Here `kshape = kfsh`, `karS = 2π(1+σ)` and `kg = 1`, so
  `kgam = kshape = kfsh = krd σ • CI.c (krpf δ σ * τ) (· + kphc δ k σ)`, a rescaled, phase shifted
  curve of the isotopy; its area, non-vanishing derivative and injectivity modulo `2π` come
  directly from `CurveIsotopy.area`/`CurveIsotopy.imm`/`CurveIsotopy.inj`.

The two auxiliary facts about `kfsh` are proved at the head of the file.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff Topology Interval

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-! ## Auxiliary facts about the far family `kfsh` -/

/-- The `t`-slice of the curve isotopy is `C¹`. -/
theorem kae_contDiff_CI_slice (CI : Work.RPV.CurveIsotopy) (τ : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => CI.c τ t) := by
  have h0 : ContDiff ℝ 1 (fun z : ℝ × ℝ => CI.c z.1 z.2) := CI.smooth.of_le (by norm_num)
  simpa [Function.comp_def] using h0.comp ((contDiff_const (c := τ)).prodMk contDiff_id)

/-- The `t`-derivative of the far family is never zero (for `σ ≥ 0`). -/
theorem kfsh_deriv_ne (CI : Work.RPV.CurveIsotopy) {δ : ℝ} (k : ℤ) {τ σ t : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hσ : 0 ≤ σ) :
    deriv (fun s : ℝ => kfsh CI δ k τ σ s) t ≠ 0 := by
  have hτ' : krpf δ σ * τ ∈ Set.Icc (0 : ℝ) 1 := ksb_krpf_mul_mem_Icc hτ
  have hA : (krd σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (krd_pos hσ))
  have hcd : DifferentiableAt ℝ (fun s : ℝ => CI.c (krpf δ σ * τ) (s + kphc δ k σ)) t :=
    ((kae_contDiff_CI_slice CI (krpf δ σ * τ)).comp
      (contDiff_id.add contDiff_const)).contDiffAt.differentiableAt (by norm_num)
  have hfun : (fun s : ℝ => kfsh CI δ k τ σ s)
      = fun s => (krd σ : ℂ) * CI.c (krpf δ σ * τ) (s + kphc δ k σ) := rfl
  rw [hfun, deriv_const_mul _ hcd, deriv_comp_add_const]
  exact mul_ne_zero hA (CI.imm _ hτ' _)

/-- The far family is injective modulo the period `2π` (for `σ ≥ 0`). -/
theorem kfsh_inj (CI : Work.RPV.CurveIsotopy) {δ : ℝ} (k : ℤ) {τ σ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hσ : 0 ≤ σ) {t t' : ℝ}
    (h : kfsh CI δ k τ σ t = kfsh CI δ k τ σ t') : ∃ m : ℤ, t' = t + 2 * Real.pi * m := by
  have hτ' : krpf δ σ * τ ∈ Set.Icc (0 : ℝ) 1 := ksb_krpf_mul_mem_Icc hτ
  have hA : (krd σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (krd_pos hσ))
  have h2 : CI.c (krpf δ σ * τ) (t + kphc δ k σ) = CI.c (krpf δ σ * τ) (t' + kphc δ k σ) := by
    have h3 := h
    simp only [kfsh] at h3
    exact mul_left_cancel₀ hA h3
  obtain ⟨m, hm⟩ := CI.inj _ hτ' _ _ h2
  exact ⟨m, by linarith [hm]⟩

/-! ## The main statement -/

theorem kappa_collar_area_emb (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (κ : ℝ) (hκ : 0 < κ)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ))
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ)
    (hρhper : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ)
    (k : ℤ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ κ ∧
      ∀ δ ∈ Set.Ioo (0 : ℝ) δ₀, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, 0 ≤ σ →
        Work.RPB.signedArea (Work.RPB.B5.kgam CI W ρh δ k τ σ) = 2 * Real.pi * (1 + σ) ∧
        (∀ t : ℝ, deriv (fun s : ℝ => Work.RPB.B5.kgam CI W ρh δ k τ σ s) t ≠ 0) ∧
        (∀ t t' : ℝ, Work.RPB.B5.kgam CI W ρh δ k τ σ t
            = Work.RPB.B5.kgam CI W ρh δ k τ σ t' →
          ∃ m : ℤ, t' = t + 2 * Real.pi * m) := by
  classical
  obtain ⟨δ₀, hδ₀pos, hδ₀κ, hgeom⟩ :=
    kappa_shape_geom_small CI a ha ρ₀ hρ₀ W ρh κ hκ hW hWchord hWper hρh hρh0 hρhv hρhl
      hρhper k
  refine ⟨δ₀, hδ₀pos, hδ₀κ, ?_⟩
  intro δ hδ τ hτ σ hσ
  obtain ⟨hδpos, hδlt⟩ := hδ
  rcases le_total σ δ with hσδ | hσle
  · -- ## near region `σ ∈ [0, δ]`
    obtain ⟨hkS, hd, hinj⟩ := hgeom δ ⟨hδpos, hδlt⟩ τ hτ σ ⟨hσ, hσδ⟩
    have hkg : kg CI W ρh δ k τ σ = 2 * Real.pi * (1 + σ) / karS CI W ρh δ k τ σ := rfl
    have hkg_ne : kg CI W ρh δ k τ σ ≠ 0 := by
      rw [hkg]
      have hnum : 0 < 2 * Real.pi * (1 + σ) := by nlinarith [Real.pi_pos, hσ]
      exact div_ne_zero (ne_of_gt hnum) (ne_of_gt hkS)
    refine ⟨?_, ?_, ?_⟩
    · -- the area law
      have hfun : kgam CI W ρh δ k τ σ
          = fun t => kdiagM (kg CI W ρh δ k τ σ) (kshape CI W ρh δ k τ σ t) := by
        funext t
        rw [kgam]
      rw [hfun, kdiagM_signedArea]
      rw [show Work.RPB.signedArea (fun t : ℝ => kshape CI W ρh δ k τ σ t)
            = karS CI W ρh δ k τ σ from rfl, hkg]
      exact div_mul_cancel₀ _ (ne_of_gt hkS)
    · -- the derivative does not vanish
      intro t
      have hdiff : DifferentiableAt ℝ (fun s : ℝ => kshape CI W ρh δ k τ σ s) t := by
        by_contra hc
        exact hd t (deriv_zero_of_not_differentiableAt hc)
      have hg : deriv (fun s : ℝ => kgam CI W ρh δ k τ σ s) t
          = kdiagM (kg CI W ρh δ k τ σ)
              (deriv (fun s : ℝ => kshape CI W ρh δ k τ σ s) t) := by
        have hfun : (fun s : ℝ => kgam CI W ρh δ k τ σ s)
            = fun s => kdiagM (kg CI W ρh δ k τ σ) (kshape CI W ρh δ k τ σ s) := by
          funext s
          rw [kgam]
        rw [hfun]
        exact ksb_deriv_kdiagM_comp (kg CI W ρh δ k τ σ)
          (fun s : ℝ => kshape CI W ρh δ k τ σ s) hdiff
      rw [hg]
      intro hzero
      have h0 : kdiagM (kg CI W ρh δ k τ σ) (0 : ℂ) = 0 := by
        simp [kdiagM]
      rw [← h0] at hzero
      exact hd t (ksb_kdiagM_inj hkg_ne hzero)
    · -- injectivity modulo `2π`
      intro t t' h
      have h2 : kshape CI W ρh δ k τ σ t = kshape CI W ρh δ k τ σ t' := by
        apply ksb_kdiagM_inj hkg_ne
        simpa only [kgam] using h
      exact hinj t t' h2
  · -- ## far region `σ ≥ δ`
    have hfar : ∀ t : ℝ, kgam CI W ρh δ k τ σ t = kshape CI W ρh δ k τ σ t :=
      fun t => ksb_kgam_far CI W ρh hδpos k hτ hσle t
    have hsh : ∀ t : ℝ, kshape CI W ρh δ k τ σ t = kfsh CI δ k τ σ t :=
      fun t => ksb_kshape_eq_kfsh CI W ρh hδpos hσle k τ t
    refine ⟨?_, ?_, ?_⟩
    · -- the area law
      have hfun : kgam CI W ρh δ k τ σ = kshape CI W ρh δ k τ σ := funext hfar
      rw [hfun, show Work.RPB.signedArea (fun t : ℝ => kshape CI W ρh δ k τ σ t)
            = karS CI W ρh δ k τ σ from rfl]
      exact ksb_karS_far CI W ρh hδpos k hτ hσle
    · -- the derivative does not vanish
      intro t
      have e1 : deriv (fun s : ℝ => kgam CI W ρh δ k τ σ s) t
          = deriv (fun s : ℝ => kfsh CI δ k τ σ s) t := by
        rw [show (fun s : ℝ => kgam CI W ρh δ k τ σ s)
              = (fun s : ℝ => kshape CI W ρh δ k τ σ s) from funext hfar,
          show (fun s : ℝ => kshape CI W ρh δ k τ σ s)
              = (fun s : ℝ => kfsh CI δ k τ σ s) from funext hsh]
      rw [e1]
      exact kfsh_deriv_ne CI k hτ hσ
    · -- injectivity modulo `2π`
      intro t t' h
      have h2 : kfsh CI δ k τ σ t = kfsh CI δ k τ σ t' := by
        rw [← hsh t, ← hsh t', ← hfar t, ← hfar t']
        exact h
      exact kfsh_inj CI k hτ hσ h2

end Work.RPB.B5
