import Mathlib
import Submission.Work.ORLyndon.powDefs

/-!
# The top level part of a non-zero element

Let `G = ⟨α | r⟩` with `r = u ^ l` and `σ_t u = 1`, so that the `t`-exponent sum descends to the
level map `Work.ORLyndon.levelOf t r u l hpow hσ : G →* Multiplicative ℤ`.

If `b : K[G]` is non-zero, then the levels occurring in its (finite, non-empty) support have a
maximum `N`, and the `N`-th level part of `b` is non-zero: it retains exactly the terms of `b`
attained at the top level.

Proof.  Non-vanishing of `b` says that `b.coeff.support` is non-empty, so the image of the support
under `g ↦ (levelOf … g).toAdd` is a non-empty finite set of integers; let `N` be its maximum
(`Finset.exists_max_image`), attained at some `g₀` in the support.  Every element of the support
then has level `≤ N`, and the `N`-th level part is non-zero because its coefficient at `g₀` is
`b.coeff g₀ ≠ 0`: the level of `g₀` is *exactly* `Multiplicative.ofAdd N` by construction of `N`,
so the filter defining `levelPart` keeps the term `g₀`.
-/

set_option autoImplicit false

namespace Work.ORLyndon

theorem exists_levelPart_max_ne_zero {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t : α) {r u : FreeGroup α} {l : ℕ} {hpow : r = u ^ l}
    {hσ : Work.OROneRel.sigma t u = 1} {b : MonoidAlgebra K (OneRelatorGroup r)}
    (hb : b ≠ 0) :
    ∃ N : ℤ, Work.ORLyndon.levelPart t r u l hpow hσ N b ≠ 0 ∧
      ∀ g ∈ b.coeff.support, (Work.ORLyndon.levelOf t r u l hpow hσ g).toAdd ≤ N := by
  classical
  -- the support of a non-zero element is non-empty
  have hne : b.coeff.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hb (MonoidAlgebra.ext (by rw [Finsupp.support_eq_empty.mp h, MonoidAlgebra.coeff_zero]))
  -- the levels occurring in the support attain a maximum
  obtain ⟨g₀, hg₀, hmax⟩ := Finset.exists_max_image b.coeff.support
    (fun g => (Work.ORLyndon.levelOf t r u l hpow hσ g).toAdd) hne
  refine ⟨(Work.ORLyndon.levelOf t r u l hpow hσ g₀).toAdd, ?_, fun g hg => hmax g hg⟩
  -- the top level part keeps the term `g₀`
  intro hzero
  have hcoeff := Work.ORLyndon.levelPart_coeff t r u l hpow hσ
    (Work.ORLyndon.levelOf t r u l hpow hσ g₀).toAdd b g₀
  rw [hzero] at hcoeff
  simp at hcoeff
  exact (Finsupp.mem_support_iff.mp hg₀) hcoeff.symm

end Work.ORLyndon
