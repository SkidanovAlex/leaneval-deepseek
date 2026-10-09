import Mathlib
import Submission.Work.SSGRoute.prop5.dimensionSubgroup_conv
import Submission.Work.SSGRoute.prop5.magnusCore_instance
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The dimension subgroup theorem for free groups (Magnus, 1935)

For a free group `F = FreeGroup X` with augmentation ideal `Δ ⊆ ℤ[F]`, the `k`-th *dimension
subgroup* `F ∩ (1 + Δ^k)` equals the `k`-th term `γ_k` of the lower central series.

The proof is an induction on `k`.  Two ingredients enter.

* `magRingHom_eq_one_of_mem_augIdeal_pow` (this workspace, `dimensionSubgroup_conv`): the Magnus
  map factors through `ℤ[F] ⧸ Δ^k`, so `single g 1 - 1 ∈ Δ^k` forces the Magnus image of `g`
  modulo `fil X k` to be trivial (and, taking the truncation level to be `k+1` in the induction
  step, trivial modulo `fil X (k+1)`).
* `magnusCore_instance` (`prop5/magnusCore_instance.lean`): the "hard half" of the Magnus
  embedding theorem (Magnus/Witt), which detects the lower central series: an element of `γ_k`
  whose Magnus image is congruent to `1` modulo `fil X (k+1)` lies in `γ_{k+1}`.
-/

namespace Work.SSGRoute.prop5

theorem dimensionSubgroup_free (X : Type) (k : ℕ) (g : FreeGroup X)
    (h : MonoidAlgebra.single g (1 : ℤ) - 1 ∈
        (Ideal.span (Set.range (fun g' : FreeGroup X => MonoidAlgebra.single g' (1 : ℤ) - 1))) ^ k) :
    g ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1) := by
  have aux : ∀ k : ℕ, ∀ g : FreeGroup X,
      MonoidAlgebra.single g (1 : ℤ) - 1 ∈ (augIdeal X) ^ k →
      g ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1) := by
    intro k
    induction k with
    | zero => intro g _; exact Subgroup.mem_top g
    | succ k ih =>
        intro g hg
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0
          exact Subgroup.mem_top g
        · -- one step of the lower central series, using the induction hypothesis at level `k`
          have hg' : MonoidAlgebra.single g (1 : ℤ) - 1 ∈ (augIdeal X) ^ k :=
            augIdeal_pow_antitone X k hg
          have hγ : g ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1) := ih g hg'
          -- the Magnus image of `g` vanishes modulo `fil X (k+1)`
          have hmag : ((magnus X (k + 1) g : (FreeAssoc X ⧸ fil X (k + 1))ˣ) :
              FreeAssoc X ⧸ fil X (k + 1)) - 1 ∈ filq X (k + 1) ((k - 1) + 2) := by
            rw [magRingHom_eq_one_of_mem_augIdeal_pow (k + 1) (by omega) g hg]
            simp
          have hcore := magnusCore_instance X (k + 1) (k - 1) (by omega) g hγ hmag
          simpa [Nat.sub_add_cancel hkpos] using hcore
  exact aux k g (by simpa [augIdeal] using h)

end Work.SSGRoute.prop5
