/-
# The lower central factors of a free group are torsion free

This is the "pure" statement used in Shafarevich's theorem on solvable Galois groups (and its
prime-2 correction): the lower central factors `γ_k/γ_{k+1}` of a free group have no torsion.

The classical proof is the Magnus embedding: the truncated Magnus map

`magnus X N : FreeGroup X → (FreeAssoc X ⧸ fil X N)ˣ`

has an associated graded piece that is computed by the free Lie ring; the "hard half" of the
Magnus embedding theorem (Witt's theorem that the free Lie ring is faithful) says that the
leading term of the Magnus image detects the next term of the lower central series.  That is the
statement `mcore.magnusCore` proved in `Submission/Work/SSGRoute/prop5/lowerCentralSeriesCore.lean`.

Given it, the torsion statement is short: if `x ∈ γ_{j-1}` and `x^n ∈ γ_j` with `n > 0`, then the
leading term of `x^n` at truncation `j+1` vanishes, so `n • (magLead (j+1) x) = 0` and, the
filtration piece `filq X (j+1) j` being torsion free (`filq_nsmul_mem`), the leading term of `x`
itself vanishes; the "hard half" then gives `x ∈ γ_j`.
-/
import Mathlib
import Submission.Work.SSGRoute.prop5.magnusFramework
import Submission.Work.SSGRoute.prop5.magnus_mem_one_add
import Submission.Work.SSGRoute.prop5.magnus_unitCongr_isolated
import Submission.Work.SSGRoute.prop5.lowerCentralSeriesCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5

/-- **Tensor-freeness of the lower central factors of a free group.**

If `x ∈ γ_{j-1}` (Mathlib indexing: `lowerCentralSeries (j-1)`) and `x ^ n ∈ γ_j` for some
`n > 0`, then already `x ∈ γ_j`. -/
theorem lowerCentralSeries_torsionFree (X : Type) [Fintype X] (j : ℕ) (hj : 1 ≤ j)
    (x : FreeGroup X) (hx : x ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1))
    (n : ℕ) (hn : 0 < n)
    (hxn : x ^ n ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j) :
    x ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := by
  -- the `n`-th power of the Magnus image of `x` is `≡ 1` modulo `fil j`
  have hmem : (((magnus X (j + 1) x) ^ n : (FreeAssoc X ⧸ fil X (j + 1))ˣ) :
      FreeAssoc X ⧸ fil X (j + 1)) - 1 ∈ filq X (j + 1) (j - 1 + 2) := by
    have hunit : ((magnus X (j + 1) x) ^ n : (FreeAssoc X ⧸ fil X (j + 1))ˣ)
        = magnus X (j + 1) (x ^ n) := (map_pow (magnus X (j + 1)) x n).symm
    rw [hunit]
    change magLead (j + 1) (x ^ n) ∈ filq X (j + 1) (j - 1 + 2)
    rw [magLead_eq_zero_of_mem_succ (X := X) j hxn]
    exact Submodule.zero_mem _
  -- isolatedness of the congruence filtration at the Magnus image
  have hzero : magLead (j + 1) x = 0 := by
    have hres := magnus_unitCongr_isolated X (j + 1) (j - 1) n (by omega) hn x hx hmem
    rw [show j - 1 + 2 = j + 1 from by omega] at hres
    exact mem_filq_self_eq_zero' (X := X) (N := j + 1) hres
  -- the "hard half" of the Magnus embedding theorem
  exact mcore.mem_Gam_iff.mp (mcore.magnusCore_aux X j hj x (mcore.mem_Gam_iff.mpr hx) hzero)

end Work.SSGRoute.prop5
