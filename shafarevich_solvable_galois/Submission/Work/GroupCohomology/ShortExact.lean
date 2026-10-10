import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.GroupCohomology.Inflation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w x

namespace Work.GroupCohomology

/-- `H⁰(G, A) = A^G`, the invariants of the `G`-module `A`. -/
abbrev H0 (G : Type u) (A : Type v) [Group G] [AddCommGroup A] [DistribMulAction G A] :
    AddSubgroup A :=
  invariants G A

/-- An equivariant additive map `A →+ B` of `G`-modules induces a map on invariants. -/
def mapH0 (G : Type u) {A : Type v} {B : Type w} [Group G] [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction G A] [DistribMulAction G B] (φ : A →+ B) (hφ : IsEquivariant G φ) :
    H0 G A →+ H0 G B where
  toFun a := ⟨φ (a : A), fun g => by rw [← hφ g (a : A), a.2 g]⟩
  map_zero' := by ext; simp
  map_add' a a' := by ext; simp

/-- A short exact sequence of `G`-modules `0 → A --iota--> B --pi--> C → 0`. -/
structure ShortExactSeq (G : Type u) (A : Type v) (B : Type w) (C : Type x) [Group G]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C] where
  /-- the inclusion `A → B` -/
  iota : A →+ B
  /-- the projection `B → C` -/
  pi : B →+ C
  iota_equivariant : IsEquivariant G iota
  pi_equivariant : IsEquivariant G pi
  iota_injective : Function.Injective iota
  pi_surjective : Function.Surjective pi
  range_iota_eq_ker_pi : iota.range = pi.ker

namespace ShortExactSeq

variable {G : Type u} {A : Type v} {B : Type w} {C : Type x} [Group G]
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]

variable (S : ShortExactSeq G A B C)

theorem pi_iota (a : A) : S.pi (S.iota a) = 0 := by
  rw [← AddMonoidHom.mem_ker, ← S.range_iota_eq_ker_pi]
  exact AddMonoidHom.mem_range.mpr ⟨a, rfl⟩

theorem pi_comp_iota : S.pi.comp S.iota = 0 := by
  ext a
  exact S.pi_iota a

/-- `pi` is surjective, so every element of `C` has a lift. -/
theorem exists_lift (c : C) : ∃ b : B, S.pi b = c := S.pi_surjective c

/-- An element of `ker pi` has a (unique) preimage in `A`. -/
theorem exists_preimage {b : B} (hb : b ∈ S.pi.ker) : ∃ a : A, S.iota a = b := by
  rw [← S.range_iota_eq_ker_pi] at hb
  exact AddMonoidHom.mem_range.mp hb

theorem preimage_unique {b : B} {a a' : A} (ha : S.iota a = b) (ha' : S.iota a' = b) : a = a' :=
  S.iota_injective (by rw [ha, ha'])

end ShortExactSeq

end Work.GroupCohomology
