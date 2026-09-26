import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.LayerCont.Arc.Defs

/-!
# The `S`-dictionary between the layer and its "hatted" version

`Kaxis_Kfun_S_smul` (`LayerCont/Arc/Defs.lean`) says
`K^{(d)}(S•σ, i t) = -σ^{d/2} K̂^{(d)}(σ, i t)` (this is `K̂ = -K|^τ_{d/2}S`), and the model
transform is by definition of `Ĝ = -σ^{-d/2}𝒢(S•σ)`.  Since `layerLow`, `layerTrunc` and
`highPart` are built from `Kaxis`, `Aexp` and `G` alone (linearly in `G`), the whole layer
transforms the same way:

  `paperLayer (Gcusp) ℓ d (S•σ) r = -σ^{d/2} · paperLayerK (Khat ℓ d) (Ghat ℓ d) r σ`.

This reduces the second clause of `layer_line_decay`
(`‖paperLayer (S•τ) r · τ^{-d/2}‖`) to a bound on the hatted layer at `τ` itself.
-/

noncomputable section

open UpperHalfPlane
open scoped Topology Manifold

namespace Work.CKFinal

/-- `-σ^{d/2} Ĝ_{ij}(σ) = 𝒢_{ij}(S • σ)`. -/
lemma neg_zpow_mul_Ghat (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (i j : Fin 2)
    (σ : UpperHalfPlane) :
    -((σ : ℂ) ^ ((d : ℤ) / 2)) * Ghat ℓ d i j σ
      = Work.Asymptotics.Gcusp ℓ d i j (ModularGroup.S • σ) := by
  have hσ : (σ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero σ
  rw [Ghat]
  rw [show -((σ : ℂ) ^ ((d : ℤ) / 2))
        * (-((σ : ℂ) ^ (-((d : ℤ) / 2)))
            * Work.Asymptotics.Gcusp ℓ d i j (ModularGroup.S • σ))
      = ((σ : ℂ) ^ ((d : ℤ) / 2) * (σ : ℂ) ^ (-((d : ℤ) / 2)))
        * Work.Asymptotics.Gcusp ℓ d i j (ModularGroup.S • σ) from by ring]
  rw [← zpow_add₀ hσ]
  simp

/-- `Aexp 𝒢 (S•σ) t = -σ^{d/2} Aexp Ĝ σ t`. -/
lemma Aexp_S_smul (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (σ : UpperHalfPlane) (t : ℝ) :
    Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) (ModularGroup.S • σ) t
      = -((σ : ℂ) ^ ((d : ℤ) / 2)) * Work.Asymptotics.Aexp (Ghat ℓ d) σ t := by
  simp only [Work.Asymptotics.Aexp, ← neg_zpow_mul_Ghat ℓ d 0 0 σ,
    ← neg_zpow_mul_Ghat ℓ d 0 1 σ, ← neg_zpow_mul_Ghat ℓ d 1 0 σ,
    ← neg_zpow_mul_Ghat ℓ d 1 1 σ]
  ring

/-- `highPart 𝒢 (S•σ) r = -σ^{d/2} highPart Ĝ σ r` (linearity in `G`). -/
lemma highPart_S_smul (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (σ : UpperHalfPlane) (r : ℝ) :
    Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) (ModularGroup.S • σ) r
      = -((σ : ℂ) ^ ((d : ℤ) / 2)) * Work.Asymptotics.highPart (Ghat ℓ d) σ r := by
  simp only [Work.Asymptotics.highPart, ← neg_zpow_mul_Ghat ℓ d 0 0 σ,
    ← neg_zpow_mul_Ghat ℓ d 0 1 σ, ← neg_zpow_mul_Ghat ℓ d 1 0 σ,
    ← neg_zpow_mul_Ghat ℓ d 1 1 σ]
  ring


/-- `layerLowK` in terms of `Kaxis` (the `Kax` junk convention is only used on the boundary). -/
lemma layerLowK_kaxis (K : ℍ → ℍ → ℂ) (r : ℝ) (τ : UpperHalfPlane) :
    layerLowK K r τ = Work.Asymptotics.sinSqC r
      * ∫ t in (0 : ℝ)..1, Work.Kernels.Kaxis K τ t * Work.Asymptotics.gaussWeight r t := by
  rw [layerLowK]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [Kax_eq_Kaxis]

/-- `layerTruncK` in terms of `Kaxis`. -/
lemma layerTruncK_kaxis (K : ℍ → ℍ → ℂ) (G : Fin 2 → Fin 2 → ℍ → ℂ) (r : ℝ)
    (τ : UpperHalfPlane) :
    layerTruncK K G r τ = Work.Asymptotics.sinSqC r
      * ∫ t in Set.Ici (1 : ℝ), (Work.Kernels.Kaxis K τ t - Work.Asymptotics.Aexp G τ t)
          * Work.Asymptotics.gaussWeight r t := by
  rw [layerTruncK]
  congr 1
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun t _ => ?_
  rw [Kax_eq_Kaxis]

/-- `layerLow` transforms with the `S`-factor. -/
lemma layerLow_S_smul (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (σ : UpperHalfPlane) (r : ℝ) :
    Work.Asymptotics.layerLow ℓ d (ModularGroup.S • σ) r
      = -((σ : ℂ) ^ ((d : ℤ) / 2)) * layerLowK (Work.Kernels.Khat ℓ d) r σ := by
  have hint : (∫ t in (0 : ℝ)..1,
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (ModularGroup.S • σ) t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      = -((σ : ℂ) ^ ((d : ℤ) / 2))
        * ∫ t in (0 : ℝ)..1, Work.Kernels.Kaxis (Work.Kernels.Khat ℓ d) σ t
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [Work.LayerCont.Arc.Kaxis_Kfun_S_smul ℓ d hd σ t]
    ring
  rw [layerLowK_kaxis]
  simp only [Work.Asymptotics.layerLow, Work.Asymptotics.sinSq, Work.Asymptotics.sinSqC,
    Work.Asymptotics.gaussWeight]
  rw [hint]
  ring

/-- `layerTrunc` transforms with the `S`-factor. -/
lemma layerTrunc_S_smul (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (σ : UpperHalfPlane) (r : ℝ) :
    Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d (ModularGroup.S • σ) r
      = -((σ : ℂ) ^ ((d : ℤ) / 2))
          * layerTruncK (Work.Kernels.Khat ℓ d) (Ghat ℓ d) r σ := by
  have hint : (∫ t in Set.Ici (1 : ℝ),
        (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (ModularGroup.S • σ) t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) (ModularGroup.S • σ) t)
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      = -((σ : ℂ) ^ ((d : ℤ) / 2))
        * ∫ t in Set.Ici (1 : ℝ),
            (Work.Kernels.Kaxis (Work.Kernels.Khat ℓ d) σ t
              - Work.Asymptotics.Aexp (Ghat ℓ d) σ t)
              * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun t _ => ?_
    rw [Work.LayerCont.Arc.Kaxis_Kfun_S_smul ℓ d hd σ t, Aexp_S_smul ℓ d σ t]
    ring
  rw [layerTruncK_kaxis]
  simp only [Work.Asymptotics.layerTrunc, Work.Asymptotics.sinSq, Work.Asymptotics.sinSqC,
    Work.Asymptotics.gaussWeight]
  rw [hint]
  ring

/-- **The `S`-dictionary of the layer.** -/
theorem paperLayer_S_smul (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (σ : UpperHalfPlane) (r : ℝ) :
    Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d (ModularGroup.S • σ) r
      = -((σ : ℂ) ^ ((d : ℤ) / 2)) * paperLayerK (Work.Kernels.Khat ℓ d) (Ghat ℓ d) r σ := by
  rw [Work.Asymptotics.paperLayer, paperLayerK, layerLow_S_smul ℓ d hd σ r,
    layerTrunc_S_smul ℓ d hd σ r, highPart_S_smul ℓ d σ r]
  ring

end Work.CKFinal
