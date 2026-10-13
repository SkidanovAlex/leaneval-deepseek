import Mathlib
import Submission.Work.DSM1p.Family.flat_closure

namespace Work.DSM1p.Family

/-- Every stage `R[X₁,…,X_d] ⧸ (X_i ^ p^n - x_i)` of the multi-parameter root tower is a finite
`R`-module: the classes of the monomials with exponent `< p^n` in each variable span it, which is
the surjectivity part of `mvPolyQuotFree`. -/
theorem stage_finite_root (R : Type*) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)
    (hp : p ≠ 0) (n : ℕ) : Module.Finite R (Work.DSM1p.FamTower R p x n) := by
  have hN : p ^ n ≠ 0 := pow_ne_zero n hp
  have hsurj : Function.Surjective
      (stageMap (R := R) (d := d) (p ^ n) x) := by
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨redShift (p ^ n) x hN ((AddMonoidAlgebra.coeffLinearEquiv R) r), ?_⟩
    rw [stageMap_apply]
    exact (mk_red (p ^ n) x hN r).symm
  exact Module.Finite.of_surjective (σ := RingHom.id R)
    (M := RedIdx d (p ^ n) →₀ R) (P := Work.DSM1p.FamTower R p x n)
    (f := stageMap (R := R) (d := d) (p ^ n) x) hsurj

end Work.DSM1p.Family
