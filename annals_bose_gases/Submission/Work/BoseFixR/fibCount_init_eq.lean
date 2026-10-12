import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Finsupp.Single
import Submission.Work.BoseFixR.FibrePeelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.fibCount_init_eq` — the fibre count of the initial segment

The companion of `fibCount_snoc_eq`: if `σ : Fin (n+1) → ι` has fibre counts `α`, then the
initial segment `Fin.init σ` has fibre counts `α.update (σ (Fin.last n)) (α (σ (Fin.last n)) - 1)`
— one particle is removed from the fibre of the last value.
-/

namespace Work.BoseFixR

theorem fibCount_init_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (α : ι →₀ ℕ)
    (σ : Fin (n+1) → ι) (hσ : ∀ i, fibCount σ i = α i) (i : ι) :
    fibCount (Fin.init σ) i = (α.update (σ (Fin.last n)) (α (σ (Fin.last n)) - 1)) i := by
  have h := fibCount_init_add σ i
  rw [hσ i] at h
  rw [fibCount_update]
  by_cases hik : i = σ (Fin.last n)
  · simp only [if_pos hik] at h
    simp only [if_pos hik]
    have : α (σ (Fin.last n)) = α i := by rw [hik]
    rw [this]
    omega
  · simp only [if_neg hik] at h
    simp only [if_neg hik]
    omega

end Work.BoseFixR
