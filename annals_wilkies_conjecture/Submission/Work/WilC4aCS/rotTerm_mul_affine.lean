import Mathlib
import Submission.Work.WilC4aCS.Defs

namespace Work.WilC4aCS

theorem rotTerm_mul_affine {m : ℕ} (ψ : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ) (k a b : Fin m)
    (hψ : AnalyticAt ℝ ψ x) :
    Work.WilC4aCS.rotTerm (fun y : Fin m → ℝ => ψ y * (1 + y k)) x a b
      = (1 + x k) * Work.WilC4aCS.rotTerm ψ x a b
        + ψ x * (x a * (Pi.single k (1 : ℝ) : Fin m → ℝ) b
          - x b * (Pi.single k (1 : ℝ) : Fin m → ℝ) a) := by
  -- Evaluate the directional derivative of the product `ψ · (1 + ·ₖ)` by the product rule.
  have key : ∀ v : Fin m → ℝ,
      fderiv ℝ (fun y : Fin m → ℝ => ψ y * (1 + y k)) x v
        = (1 + x k) * fderiv ℝ ψ x v + ψ x * v k := by
    intro v
    have hA : HasFDerivAt (fun y : Fin m → ℝ => (1 : ℝ) + y k)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) k) x := by
      simpa using (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) k)).hasFDerivAt
        (x := x)).const_add (1 : ℝ)
    have hmul := hψ.differentiableAt.hasFDerivAt.mul hA
    rw [show (fun y : Fin m → ℝ => ψ y * (1 + y k)) = (ψ * fun y => 1 + y k) from rfl]
    rw [hmul.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply]
    ring
  -- Symmetry of `Pi.single`, matching the two orders the goal uses.
  have hb : ∀ i j : Fin m, (Pi.single i (1 : ℝ) : Fin m → ℝ) j
      = (Pi.single j (1 : ℝ) : Fin m → ℝ) i := by
    intro i j; simp [Pi.single_apply, eq_comm]
  simp only [rotTerm, ddir, key, hb]
  ring

end Work.WilC4aCS
