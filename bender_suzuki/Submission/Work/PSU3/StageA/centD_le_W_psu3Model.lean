import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.Model.psu3_isSplitRankOne

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.centD_le_W_psu3Model` — the conclusion `V ≤ W` in the model `PSU(3,2ⁿ)`

A verified instance of the conclusion of `Work.PSU3.StageA.centD_le_W_of_PSU3Hyp`, for the group
the root case of the whole area is about: `PSU(3,2ⁿ)` with its Borel `B̄ = psu3B n`, unipotent
radical `Ū = psu3U n` and Weyl element `w̄ = psu3Weyl n` (so `Q = Ū`, `t = w̄`,
`D = twoPoint B̄ w̄ = T̄ = psu3T n`, `Submission.Work.PSU3.Model.twoPoint_psu3B_psu3Weyl`).

The model's two-point stabiliser `T̄` is the image of `suTS n ≤ SU(3,2ⁿ)`, i.e. of the maximal
torus of diagonal matrices `diag(a, a^{q-1}, a^{-q})`, `a ∈ (GF(q²))ˣ` (`Submission.PSU3.suT`):
a *homomorphic image of the abelian group* `(GF(q²))ˣ` (`suTg_mul`), hence abelian.  So `V ⊆ D`
commutes with every element of `D ⊇ Kset B̄ w̄`, i.e. `V ⊆ W` there — and in particular `W ≠ ⊥`
(the two-point stabiliser of a non-Zassenhaus model has `V ≠ 1`).

This also settles a claim recorded in `Submission/Work/PSU3/StageB/centralizer_oddResidual_isPSU3_v2.lean`
(that `PSU(3,8)` has `V = Z/3`, `W = 1`, `D = Z/7 ⋊ Z/3`): the model's `D = T̄` is the image of a
*cyclic* group and is abelian, so `W = V` there, not `1`.
-/

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- The maximal torus `suT n` of diagonal matrices `diag(a, a^{q-1}, a^{-q})` is abelian: it is the
image of the abelian group `(GF(q²))ˣ` under `a ↦ suTg n a`, which is multiplicative. -/
theorem suT_comm {n : ℕ} {A B : GL (Fin 3) (Submission.PSU3.F n)}
    (hA : A ∈ Submission.PSU3.suT n) (hB : B ∈ Submission.PSU3.suT n) : A * B = B * A := by
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  calc Submission.PSU3.suTg n a * Submission.PSU3.suTg n b
      = Submission.PSU3.suTg n (a * b) := Submission.PSU3.suTg_mul n a b
    _ = Submission.PSU3.suTg n (b * a) := by congr 1; exact mul_comm a b
    _ = Submission.PSU3.suTg n b * Submission.PSU3.suTg n a :=
        (Submission.PSU3.suTg_mul n b a).symm

/-- `T = suTS n` (the torus inside `SU(3,2ⁿ)`) is abelian. -/
theorem suTS_comm {n : ℕ} {x y : ↥(Submission.PSU3.SU3 n)}
    (hx : x ∈ Submission.PSU3.suTS n) (hy : y ∈ Submission.PSU3.suTS n) : x * y = y * x := by
  apply Subtype.ext
  exact suT_comm (Subgroup.mem_subgroupOf.mp hx) (Subgroup.mem_subgroupOf.mp hy)

/-- `T̄ = psu3T n` (the maximal torus of `PSU(3,2ⁿ)`) is abelian, being the image of `T`. -/
theorem psu3T_comm {n : ℕ} {X Y : PSU3Model n}
    (hX : X ∈ Submission.PSU3.psu3T n) (hY : Y ∈ Submission.PSU3.psu3T n) : X * Y = Y * X := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hX
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hY
  rw [← map_mul, ← map_mul, suTS_comm hx hy]

/-- **`V ≤ W` in the model `PSU(3,2ⁿ)`**: `centD B̄ w̄ ≤ W B̄ w̄`, i.e. `C_D(t) = C_V(K)` there. -/
theorem centD_le_W_psu3Model (n : ℕ) :
    Submission.Blueprint.centD (Submission.PSU3.psu3B n) (Submission.PSU3.psu3Weyl n) ≤
      Work.ThmF.W (Submission.PSU3.psu3B n) (Submission.PSU3.psu3Weyl n) := by
  intro v hv
  rw [Work.ThmF.W, Subgroup.mem_inf]
  refine ⟨hv, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  -- both `v` and `k` lie in `D = twoPoint B̄ w̄ = psu3T n`, which is abelian
  have hvT : v ∈ Submission.PSU3.psu3T n := by
    rw [← Work.PSU3.Model.twoPoint_psu3B_psu3Weyl n]
    exact (Subgroup.mem_inf.mp hv).1
  have hkT : k ∈ Submission.PSU3.psu3T n := by
    rw [← Work.PSU3.Model.twoPoint_psu3B_psu3Weyl n]
    exact Work.ThmF.Kset_subset (Submission.PSU3.psu3B n) (Submission.PSU3.psu3Weyl n) hk
  exact (psu3T_comm hvT hkT).symm

end Work.PSU3.StageA
