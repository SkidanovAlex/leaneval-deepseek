import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.CharCore.Main
import Submission.Work.Hering.AppVII.part2
import Submission.Work.NormalComplement.AppVII.CoprimeBrauerLift
import Submission.Work.NormalComplement.AppVII.IsExtraspecialTransfer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi Appendix VII, Part 2: the modular fixed point theorem

Given `A = Q ⋊ P` with `Q` extraspecial of order `q ^ (2m+1)` (`q` an odd prime, `m ≥ 1`),
`|P| = p` prime, `p ∤ |Q|`, `C_Q(P) = Z(Q)` and `⁅P,Q⁆ = Q`, and an irreducible `F̄_r[A]`-module
`V` (`r ∤ |A|`) on which `Z(Q)` acts non-trivially, there is a non-zero `P`-fixed vector.

This is the source's Part 1 step 5 + Part 2: the coprime Brauer lifting
(`coprime_brauer_lift`) turns `V` into an ordinary irreducible character `χ` of `A` whose kernel
does not contain `Z(Q)` and whose restriction to `P` does not contain the trivial character;
`Work.Hering.AppVII.part2` (Peterfalvi's Part 2, proved) says that every such `χ` *does* contain
the trivial character of `P`.
-/

namespace Work.NormalComplement.AppVII

/-- The centralizer of a subgroup `Q` inside `Q` is the image of the centre of `Q`. -/
theorem inf_centralizer_self_eq_center_map {A : Type*} [Group A] (Q : Subgroup A) :
    Q ⊓ Subgroup.centralizer (Q : Set A) = (Subgroup.center ↥Q).map Q.subtype := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxQ, hxC⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hxQ⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr fun y => ?_
    apply Subtype.ext
    simpa using Subgroup.mem_centralizer_iff.mp hxC (y : A) y.2
  · rintro x ⟨z, hz, rfl⟩
    refine ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz (⟨y, hy⟩ : ↥Q))
    simpa using h

theorem SimpleFixedPoint {A : Type*} [Group A] [Fintype A] (Q P : Subgroup A) [Fintype ↥Q]
    [Fintype ↥P] (hQn : Q.Normal)
    (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (hqodd : Odd q)
    (hcardP : Nat.card ↥P = p) (hpQ : ¬ p ∣ Nat.card ↥Q)
    (hQcard : Nat.card ↥Q = q ^ (2 * m + 1)) (hm : 1 ≤ m)
    (hQext : Work.PGroup.IsExtraspecial q (⊤ : Subgroup ↥Q))
    (hCQ : Q ⊓ Subgroup.centralizer (P : Set A) = (Subgroup.center ↥Q).map Q.subtype)
    (hcomm : ⁅P, Q⁆ = Q)
    {r : ℕ} [Fact r.Prime] (hrA : Nat.Coprime r (Nat.card A))
    {V : Type*} [AddCommGroup V] [Module (AlgebraicClosure (ZMod r)) V]
    [Module.Finite (AlgebraicClosure (ZMod r)) V]
    (ρ : Representation (AlgebraicClosure (ZMod r)) A V) [ρ.IsIrreducible]
    (hZ : ¬ (Subgroup.center ↥Q).map Q.subtype ≤ ρ.ker) :
    ∃ v : V, v ≠ 0 ∧ ∀ s ∈ P, ρ s v = v := by
  classical
  by_contra hcon
  -- `hcon` says: the only `P`-fixed vector is `0`
  have hP : ∀ v : V, (∀ c ∈ P, ρ c v = v) → v = 0 := by
    intro v hv
    by_contra hv0
    exact hcon ⟨v, hv0, hv⟩
  -- Brauer lifting: an ordinary irreducible character with the same kernel and restriction data
  obtain ⟨χ, hχ, hZnontrivial, hsumP⟩ :=
    coprime_brauer_lift hrA ρ P ((Subgroup.center ↥Q).map Q.subtype) hP hZ
  -- `z` can be taken inside `Q ⊓ C_A(Q)`
  obtain ⟨z, hzZ, hzχ⟩ := hZnontrivial
  have hzQ : z ∈ Q := Subgroup.map_subtype_le _ hzZ
  obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.mp hzZ
  have hzcent : z ∈ Subgroup.centralizer (Q : Set A) := by
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [← hcz]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc (⟨y, hy⟩ : ↥Q))
  have hZpart : ∃ z ∈ Q ⊓ Subgroup.centralizer (Q : Set A), χ z ≠ χ 1 :=
    ⟨z, ⟨hzQ, hzcent⟩, hzχ⟩
  have hcp : Q ⊓ Subgroup.centralizer (P : Set A) = Q ⊓ Subgroup.centralizer (Q : Set A) := by
    rw [hCQ, inf_centralizer_self_eq_center_map Q]
  -- Peterfalvi's Part 2 contradicts the lifting
  exact Work.Hering.AppVII.part2 Q P hQn hinf hsup hq ((IsExtraspecialTransfer Q).mp hQext)
    hQcard hqodd hp hcardP hpQ hcomm hcp hχ hZpart hsumP

end Work.NormalComplement.AppVII
