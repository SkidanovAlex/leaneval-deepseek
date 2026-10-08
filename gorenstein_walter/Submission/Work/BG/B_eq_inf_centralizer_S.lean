import Mathlib
import Submission.Work.BG.kappaExists

namespace Work.BG

/-- The centralizer of a two-element set is the intersection of the centralizers of the
elements: `C_G{a,b} = C_G(a) ⊓ C_G(b)`. -/
theorem centralizer_pair_eq_inf {G : Type} [Group G] (a b : G) :
    Subgroup.centralizer ({a, b} : Set G) =
      Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) := by
  apply le_antisymm
  · intro x hx
    have h1 : a * x = x * a :=
      (Subgroup.mem_centralizer_iff (g := x) (s := ({a, b} : Set G))).mp hx a (by simp)
    have h2 : b * x = x * b :=
      (Subgroup.mem_centralizer_iff (g := x) (s := ({a, b} : Set G))).mp hx b (by simp)
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr h1.symm,
      Subgroup.mem_centralizer_singleton_iff.mpr h2.symm⟩
  · intro x hx
    show x ∈ Subgroup.centralizer ({a, b} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | rfl
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hx.1).symm
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm

/-- `D.B` is exactly the intersection of the centralizer of the Sylow `2`-subgroup `S`
with `D.U`: since `D.B = (U ⊓ C(t₁)) ⊓ (U ⊓ C(t₂))`, `S = ⟨t₁, t₂⟩` and
`C(S) = C(t₁) ⊓ C(t₂)`, the two are equal as elements of the (commutative, idempotent)
lattice of subgroups. -/
theorem B_eq_inf_centralizer_S {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    D.B = Subgroup.centralizer ((D.S : Subgroup G) : Set G) ⊓ D.U := by
  rw [S_eq_closure D, Subgroup.centralizer_closure]
  rw [centralizer_pair_eq_inf]
  simp only [Work.GW2.BGData.B, Work.GW2.BGData.B1, Work.GW2.BGData.B2]
  ac_rfl

end Work.BG
