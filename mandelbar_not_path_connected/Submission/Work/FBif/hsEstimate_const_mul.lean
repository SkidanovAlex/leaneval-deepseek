import Mathlib
import Submission.Work.FBif.Glue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

/-- Scaling the perturbation `q` by a positive real `lam` merely rescales the perturbation
parameter: `perturb c (lam·q) ε = perturb c q (ε·lam)`. -/
theorem perturb_const_mul (c : ℂ) (q : ℂ → ℂ) (lam ε : ℝ) :
    perturb c (fun z => (lam : ℂ) * q z) ε = perturb c q (ε * lam) := by
  funext z
  simp only [perturb]
  push_cast
  ring

theorem hsEstimate_const_mul {c z₁ : ℂ} {q : ℂ → ℂ} (h : Work.FBif.HSEstimate c z₁ q)
    {lam : ℝ} (hlam : 0 < lam) :
    Work.FBif.HSEstimate c z₁ (fun z => (lam : ℂ) * q z) := by
  obtain ⟨δ, hδ, ε₀, hε₀, hq⟩ := h
  refine ⟨δ, hδ, ε₀ / lam, div_pos hε₀ hlam, fun ε hε hlt => ?_⟩
  have hεlam : 0 < ε * lam := mul_pos hε hlam
  have hlt' : ε * lam < ε₀ := by
    have h1 : ε * lam < (ε₀ / lam) * lam := mul_lt_mul_of_pos_right hlt hlam
    rwa [div_mul_cancel₀ ε₀ (ne_of_gt hlam)] at h1
  rw [perturb_const_mul]
  exact hq (ε * lam) hεlam hlt'

end Work.FBif
