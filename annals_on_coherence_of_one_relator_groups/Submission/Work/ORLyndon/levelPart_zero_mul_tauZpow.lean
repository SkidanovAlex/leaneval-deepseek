import Mathlib
import Submission.Work.ORLyndon.powDefs
import Submission.Work.ORLyndon.topPart_mul

namespace Work.ORLyndon

theorem levelPart_zero_mul_tauZpow {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t : α) {r u : FreeGroup α} {l : ℕ} {hpow : r = u ^ l}
    {hσ : Work.OROneRel.sigma t u = 1} {N : ℤ} {b : MonoidAlgebra K (OneRelatorGroup r)} :
    Work.ORLyndon.levelPart t r u l hpow hσ 0
        (MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ (-N)) *
          Work.ORLyndon.levelPart t r u l hpow hσ N b) =
      MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ (-N)) *
        Work.ORLyndon.levelPart t r u l hpow hσ N b := by
  classical
  -- The level of the class of `t` is `1`, so the level of `τ ^ (-N)` is `-N`.
  have hsigma : Work.OROneRel.sigma t (FreeGroup.of t) = Multiplicative.ofAdd (1 : ℤ) := by
    rw [Work.OROneRel.sigma, FreeGroup.lift_apply_of]
    simp
  have htau : ∀ N : ℤ, Work.ORLyndon.levelOf t r u l hpow hσ
      ((presentRho r (FreeGroup.of t)) ^ (-N)) = Multiplicative.ofAdd (-N) := by
    intro N
    rw [map_zpow, Work.ORLyndon.levelOf_presentRho, hsigma]
    rw [← ofAdd_zsmul]
    simp
  -- If every nonzero coefficient of `a` sits at level `k`, then `a` is its own `k`-th level part.
  have hself : ∀ (k : ℤ) (a : MonoidAlgebra K (OneRelatorGroup r)),
      (∀ g, a.coeff g ≠ 0 → Work.ORLyndon.levelOf t r u l hpow hσ g = Multiplicative.ofAdd k) →
      Work.ORLyndon.levelPart t r u l hpow hσ k a = a := by
    intro k a h
    ext g
    rw [Work.ORLyndon.levelPart_coeff]
    by_cases hlev : Work.ORLyndon.levelOf t r u l hpow hσ g = Multiplicative.ofAdd k
    · rw [if_pos hlev]
    · rw [if_neg hlev]
      have h0 : a.coeff g = 0 := by
        by_contra hc
        exact hlev (h g hc)
      rw [h0]
  set τ : OneRelatorGroup r := presentRho r (FreeGroup.of t) with hτ
  -- Every monomial of `τ ^ (-N) * levelPart N b` has level exactly `0`.
  refine hself 0 (MonoidAlgebra.of K (OneRelatorGroup r) (τ ^ (-N)) *
    Work.ORLyndon.levelPart t r u l hpow hσ N b) ?_
  intro g hg
  have h1 : (Work.ORLyndon.levelPart t r u l hpow hσ N b).coeff ((τ ^ (-N))⁻¹ * g) ≠ 0 := by
    intro h0
    apply hg
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_apply, h0, mul_zero]
  have hmem := Finsupp.mem_support_iff.mpr h1
  have hlev1 := Work.ORLyndon.levelPart_mem_support t r u l hpow hσ N b hmem
  have hlevτ : Work.ORLyndon.levelOf t r u l hpow hσ (τ ^ (-N)) = Multiplicative.ofAdd (-N) := by
    rw [hτ]
    exact htau N
  calc Work.ORLyndon.levelOf t r u l hpow hσ g
      = Work.ORLyndon.levelOf t r u l hpow hσ (τ ^ (-N) * ((τ ^ (-N))⁻¹ * g)) := by
        rw [mul_inv_cancel_left]
    _ = Work.ORLyndon.levelOf t r u l hpow hσ (τ ^ (-N)) *
          Work.ORLyndon.levelOf t r u l hpow hσ ((τ ^ (-N))⁻¹ * g) := map_mul _ _ _
    _ = Multiplicative.ofAdd (-N) * Multiplicative.ofAdd N := by rw [hlevτ, hlev1]
    _ = Multiplicative.ofAdd (-N + N) := (ofAdd_add (-N) N).symm
    _ = Multiplicative.ofAdd 0 := by rw [neg_add_cancel]

end Work.ORLyndon
