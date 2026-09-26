import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

namespace Commons.Analysis.Normed

theorem isInvertible_of_det_columns
    {c₁₁ c₁₂ c₂₁ c₂₂ : ℝ} {D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (hc₁ : D (1, 0) = (c₁₁, c₁₂)) (hc₂ : D (0, 1) = (c₂₁, c₂₂))
    (hdet : c₁₁ * c₂₂ - c₁₂ * c₂₁ ≠ 0) : D.IsInvertible := by
  set d : ℝ := c₁₁ * c₂₂ - c₁₂ * c₂₁ with hd
  have hdne : d ≠ 0 := by simpa [hd] using hdet
  have hLin : ∀ x : ℝ × ℝ, D x = (c₁₁ * x.1 + c₂₁ * x.2, c₁₂ * x.1 + c₂₂ * x.2) := by
    intro x
    calc
      D x = D (x.1 • (1, 0) + x.2 • (0, 1)) := by congr 1; ext <;> simp
      _ = x.1 • D (1, 0) + x.2 • D (0, 1) := by rw [map_add, map_smul, map_smul]
      _ = x.1 • (c₁₁, c₁₂) + x.2 • (c₂₁, c₂₂) := by rw [hc₁, hc₂]
      _ = (c₁₁ * x.1 + c₂₁ * x.2, c₁₂ * x.1 + c₂₂ * x.2) := by
        ext <;> simp <;> ring_nf
  let pre : (ℝ × ℝ) → (ℝ × ℝ) := fun z =>
    ((c₂₂ * z.1 - c₂₁ * z.2) / d, (c₁₁ * z.2 - c₁₂ * z.1) / d)
  have hpre : ∀ z : ℝ × ℝ, pre (D z) = z := by
    intro z
    dsimp [pre]
    rw [hLin]
    ext <;> field_simp [hd, hdne] <;> ring
  have hsurj : Function.Surjective D := by
    intro y
    refine ⟨pre y, ?_⟩
    dsimp [pre]
    rw [hLin]
    ext <;> field_simp [hd, hdne] <;> ring
  have hinj : Function.Injective D := by
    intro x y hxy
    have : pre (D x) = pre (D y) := by rw [hxy]
    simpa [hpre] using this
  have hbi : Function.Bijective D := ⟨hinj, hsurj⟩
  let e : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) :=
    LinearEquiv.ofBijective D.toLinearMap (by
      simpa [Function.Bijective, Function.Injective, Function.Surjective] using hbi)
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  simp [e]

end Commons.Analysis.Normed