import Mathlib
import Submission.Work.BW.PLDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped ENNReal

namespace Work.BW

/-- Prékopa–Leindler tensorizes: from the inequality for both factors one gets it for the
product measure.  The factor `μ` is the one that is integrated out (no Prékopa–Leindler
needed for it), the factor `ν` has to satisfy the inequality itself. -/
theorem PLm.tensor {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Add X] [SMul ℝ X] [Add Y] [SMul ℝ Y] {μ : Measure X} [SFinite μ] {ν : Measure Y}
    (hin : PLm μ) (hout : PLm ν) : PLm (ν.prod μ) := by
  intro f g m hf hg hm lam h0 h1 hhyp
  have hunc_f : Function.uncurry (fun s x => f (s, x)) = f := by
    funext p; obtain ⟨s, x⟩ := p; rfl
  have hunc_g : Function.uncurry (fun s x => g (s, x)) = g := by
    funext p; obtain ⟨s, x⟩ := p; rfl
  have hunc_m : Function.uncurry (fun s x => m (s, x)) = m := by
    funext p; obtain ⟨s, x⟩ := p; rfl
  set φ : Y → ℝ≥0∞ := fun s => ∫⁻ x, f (s, x) ∂μ with hφdef
  set ψ : Y → ℝ≥0∞ := fun s => ∫⁻ x, g (s, x) ∂μ with hψdef
  set θ : Y → ℝ≥0∞ := fun s => ∫⁻ x, m (s, x) ∂μ with hθdef
  have hφm : Measurable φ :=
    Measurable.lintegral_prod_right (ν := μ) (f := fun s x => f (s, x))
      (by rw [hunc_f]; exact hf)
  have hψm : Measurable ψ :=
    Measurable.lintegral_prod_right (ν := μ) (f := fun s x => g (s, x))
      (by rw [hunc_g]; exact hg)
  have hθm : Measurable θ :=
    Measurable.lintegral_prod_right (ν := μ) (f := fun s x => m (s, x))
      (by rw [hunc_m]; exact hm)
  have hhyp' : ∀ s t : Y, φ s ^ lam * ψ t ^ (1 - lam) ≤ θ (lam • s + (1 - lam) • t) := by
    intro s t
    have h1' : Measurable fun x : X => f (s, x) :=
      hf.comp (Measurable.prodMk measurable_const measurable_id)
    have h2' : Measurable fun x : X => g (t, x) :=
      hg.comp (Measurable.prodMk measurable_const measurable_id)
    have h3' : Measurable fun x : X => m (lam • s + (1 - lam) • t, x) :=
      hm.comp (Measurable.prodMk measurable_const measurable_id)
    have key := hin (fun x => f (s, x)) (fun x => g (t, x))
      (fun x => m (lam • s + (1 - lam) • t, x)) h1' h2' h3' h0 h1 ?_
    · simpa [hφdef, hψdef, hθdef] using key
    · intro x y
      have hxy := hhyp (s, x) (t, y)
      simpa [Prod.smul_mk, Prod.mk_add_mk] using hxy
  have key := hout φ ψ θ hφm hψm hθm h0 h1 hhyp'
  have e1 : ∫⁻ s, φ s ∂ν = ∫⁻ z, f z ∂(ν.prod μ) := by
    rw [hφdef]
    exact (lintegral_prod f hf.aemeasurable).symm
  have e2 : ∫⁻ s, ψ s ∂ν = ∫⁻ z, g z ∂(ν.prod μ) := by
    rw [hψdef]
    exact (lintegral_prod g hg.aemeasurable).symm
  have e3 : ∫⁻ s, θ s ∂ν = ∫⁻ z, m z ∂(ν.prod μ) := by
    rw [hθdef]
    exact (lintegral_prod m hm.aemeasurable).symm
  rwa [e1, e2, e3] at key

/-- Transporting Prékopa–Leindler along a measure-preserving "affine" measurable equivalence. -/
theorem PLm.transport {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Add X] [SMul ℝ X] [Add Y] [SMul ℝ Y] {μ : Measure X} {ν : Measure Y}
    (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (hlin : ∀ (c : ℝ) (x y : X), e (c • x + (1 - c) • y) = c • e x + (1 - c) • e y)
    (h : PLm ν) : PLm μ := by
  intro f g m hf hg hm lam h0 h1 hhyp
  set F : Y → ℝ≥0∞ := fun p => f (e.symm p) with hFdef
  set G : Y → ℝ≥0∞ := fun p => g (e.symm p) with hGdef
  set M : Y → ℝ≥0∞ := fun p => m (e.symm p) with hMdef
  have hFm : Measurable F := hf.comp e.symm.measurable
  have hGm : Measurable G := hg.comp e.symm.measurable
  have hMm : Measurable M := hm.comp e.symm.measurable
  have harg : ∀ p q : Y, e.symm (lam • p + (1 - lam) • q)
      = lam • e.symm p + (1 - lam) • e.symm q := by
    intro p q
    apply e.injective
    calc e (e.symm (lam • p + (1 - lam) • q)) = lam • p + (1 - lam) • q := e.apply_symm_apply _
      _ = e (lam • e.symm p + (1 - lam) • e.symm q) := by
            rw [hlin, e.apply_symm_apply, e.apply_symm_apply]
  have hhyp' : ∀ p q : Y, F p ^ lam * G q ^ (1 - lam) ≤ M (lam • p + (1 - lam) • q) := by
    intro p q
    have hxy := hhyp (e.symm p) (e.symm q)
    simpa [hFdef, hGdef, hMdef, harg p q] using hxy
  have key := h F G M hFm hGm hMm h0 h1 hhyp'
  have e1 : ∫⁻ p, F p ∂ν = ∫⁻ x, f x ∂μ := by
    rw [← he.lintegral_comp hFm]
    exact lintegral_congr fun x => by simp [hFdef]
  have e2 : ∫⁻ p, G p ∂ν = ∫⁻ x, g x ∂μ := by
    rw [← he.lintegral_comp hGm]
    exact lintegral_congr fun x => by simp [hGdef]
  have e3 : ∫⁻ p, M p ∂ν = ∫⁻ x, m x ∂μ := by
    rw [← he.lintegral_comp hMm]
    exact lintegral_congr fun x => by simp [hMdef]
  rwa [e1, e2, e3] at key

/-- `Fin.cons` is linear. -/
theorem cons_smul_add {n : ℕ} (c : ℝ) (a a' : ℝ) (b b' : Fin n → ℝ) :
    Fin.cons (c * a + (1 - c) * a') (c • b + (1 - c) • b')
      = c • Fin.cons a b + (1 - c) • Fin.cons a' b' := by
  funext j
  exact Fin.cases (by simp [Fin.cons_zero]) (fun i => by simp [Fin.cons_succ]) j

/-- The measurable equivalence `piFinSuccAbove` (at `0`) is linear. -/
theorem piFinSuccAbove_linear (n : ℕ) (c : ℝ) (x y : Fin (n+1) → ℝ) :
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0 (c • x + (1 - c) • y)
      = c • MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0 x
        + (1 - c) • MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0 y := by
  have h1 : ∀ z : Fin (n+1) → ℝ,
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0 z = (z 0, Fin.tail z) := by
    intro z
    rw [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_zero]
    rfl
  rw [h1, h1, h1]
  apply Prod.ext
  · simp [Pi.add_apply, Pi.smul_apply, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul]
  · funext j
    show (c • x + (1 - c) • y) (Fin.succ j)
      = c * x (Fin.succ j) + (1 - c) * y (Fin.succ j)
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

end Work.BW
