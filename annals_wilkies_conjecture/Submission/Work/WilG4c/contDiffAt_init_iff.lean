import Mathlib

namespace Work.WilG4c

/-! ### The continuous linear maps attached to the `(init, last)` splitting

`initCLM n` is the continuous linear map `ℝ^{n+1} →L[ℝ] ℝ^n` given by `Fin.init`, and
`snocZeroCLM n` is its continuous linear section `v ↦ Fin.snoc v 0`.  Both are used to transport
`ContDiffAt` across the (smooth) affine retraction `v ↦ Fin.snoc v c`. -/

private noncomputable def initCLM (n : ℕ) : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin n =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) (Fin.castSucc i)

private lemma initCLM_apply (n : ℕ) (w : Fin (n + 1) → ℝ) : initCLM n w = Fin.init w := by
  funext i
  simp only [initCLM, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
  rfl

private noncomputable def snocZeroCLM (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin (n + 1) =>
    Fin.lastCases (0 : (Fin n → ℝ) →L[ℝ] ℝ)
      (fun j : Fin n => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j) i

private lemma snocZeroCLM_apply (n : ℕ) (v : Fin n → ℝ) :
    snocZeroCLM n v = Fin.snoc v 0 := by
  funext i
  simp only [snocZeroCLM, ContinuousLinearMap.pi_apply]
  cases i using Fin.lastCases with
  | last => simp
  | cast j => simp

/-- **`ContDiffAt` transfers through the coordinate projection `Fin.init`.**  The padded function
`w ↦ g (Fin.init w)` (which ignores the last coordinate of `w : Fin (n+1) → ℝ`) is `C^k` at `y`
exactly when `g` is `C^k` at `Fin.init y`.

Suggested proof: `Fin.init` is the first component of the continuous linear equivalence
`Φ : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin n → ℝ) × ℝ`, `Φ w = (Fin.init w, w (Fin.last n))`, whose
inverse is `(v,t) ↦ Fin.snoc v t` (so `Φ.symm (Φ y) = y` by `Fin.snoc_init_self`).  Then
`g ∘ Fin.init = (g ∘ Prod.fst) ∘ Φ`, so `ContinuousLinearEquiv.contDiffAt_comp_iff` transfers
regularity between `g ∘ Fin.init` and `g ∘ Prod.fst`; the remaining step
`ContDiffAt (g ∘ Prod.fst) (Fin.init y, y (Fin.last n)) ↔ ContDiffAt g (Fin.init y)` is
composition with the continuous linear map `Prod.fst` (one direction) and with the smooth affine
map `v ↦ (v, y (Fin.last n))` (the other).  (The `⟸` direction is just `ContDiffWithinAt.comp_continuousLinearMap`.) -/
theorem contDiffAt_init_iff {n : ℕ} (g : (Fin n → ℝ) → ℝ) (k : ℕ) (y : Fin (n + 1) → ℝ) :
    ContDiffAt ℝ k (fun w : Fin (n + 1) → ℝ => g (Fin.init w)) y ↔
      ContDiffAt ℝ k g (Fin.init y) := by
  constructor
  · -- `⟹`: compose with the smooth affine section `v ↦ Fin.snoc v (y (Fin.last n))`.
    intro h
    set c := y (Fin.last n)
    set cv : Fin (n + 1) → ℝ := Fin.snoc (0 : Fin n → ℝ) c with hcv
    set ψ : (Fin n → ℝ) → (Fin (n + 1) → ℝ) := fun v => Fin.snoc v c with hψ
    have hψ_eq : ψ = fun v : Fin n → ℝ => snocZeroCLM n v + cv := by
      funext v
      rw [hψ, snocZeroCLM_apply n v, hcv]
      ext i
      cases i using Fin.lastCases with
      | last => simp
      | cast j => simp
    have h1 : ContDiffAt ℝ (k : WithTop ℕ∞) (fun v : Fin n → ℝ => snocZeroCLM n v)
        (Fin.init y) := (ContinuousLinearMap.contDiff (snocZeroCLM n)).contDiffAt
    have h2 : ContDiffAt ℝ (k : WithTop ℕ∞) (fun _ : Fin n → ℝ => cv) (Fin.init y) :=
      contDiffAt_const (c := cv)
    have hψ_smooth : ContDiffAt ℝ (k : WithTop ℕ∞) ψ (Fin.init y) := by
      rw [hψ_eq]
      exact h1.add h2
    have hF : ContDiffAt ℝ (k : WithTop ℕ∞) (fun w => g (Fin.init w)) (ψ (Fin.init y)) := by
      have hpt : ψ (Fin.init y) = y := by rw [hψ]; exact Fin.snoc_init_self y
      rw [hpt]; exact h
    have hcomp :=
      ContDiffAt.comp (f := ψ) (g := fun w => g (Fin.init w)) (Fin.init y) hF hψ_smooth
    have heq : (fun w : Fin (n + 1) → ℝ => g (Fin.init w)) ∘ ψ = g := by
      funext v
      simp only [Function.comp_apply]
      rw [hψ, Fin.init_snoc]
    rw [heq] at hcomp
    exact hcomp
  · -- `⟸`: compose with the continuous linear map `Fin.init`.
    intro h
    have hg : ContDiffAt ℝ (k : WithTop ℕ∞) g (initCLM n y) := by
      rw [initCLM_apply n y]; exact h
    have hclm : ContDiffAt ℝ (k : WithTop ℕ∞) (initCLM n) y :=
      (ContinuousLinearMap.contDiff (initCLM n)).contDiffAt
    have hcomp := hg.comp y hclm
    have heq : g ∘ (initCLM n) = fun w : Fin (n + 1) → ℝ => g (Fin.init w) := by
      funext w
      simp only [Function.comp_apply]
      rw [initCLM_apply n w]
    rw [heq] at hcomp
    exact hcomp

end Work.WilG4c
