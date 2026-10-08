import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs
import Submission.Work.ZassenhausSuzuki.Odd.isCZ_basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.Odd

/-- Membership in `FinsetCZ` is exactly `IsCZ`. -/
theorem mem_FinsetCZ_iff {G : Type} [Group G] [Finite G] {A : Subgroup G} :
    A ∈ FinsetCZ (G := G) ↔ IsCZ A := by
  classical
  simp only [FinsetCZ, Finset.mem_filter, Finset.mem_univ, true_and]

theorem eq_of_mem_FinsetCZ {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Work.ZassenhausSuzuki.Odd.SzOddHyp H Q t) {A B : Subgroup G}
    (hA : A ∈ Work.ZassenhausSuzuki.Odd.FinsetCZ (G := G))
    (hB : B ∈ Work.ZassenhausSuzuki.Odd.FinsetCZ (G := G)) {x : G}
    (hxA : x ∈ A) (hxB : x ∈ B) (hx1 : x ≠ 1) : A = B := by
  have hAeq : Subgroup.centralizer ({x} : Set G) = A :=
    ((isCZ_basic h ((mem_FinsetCZ_iff).mp hA)).2.2 x hxA hx1).2
  have hBeq : Subgroup.centralizer ({x} : Set G) = B :=
    ((isCZ_basic h ((mem_FinsetCZ_iff).mp hB)).2.2 x hxB hx1).2
  rw [← hAeq, hBeq]

end Work.ZassenhausSuzuki.Odd
