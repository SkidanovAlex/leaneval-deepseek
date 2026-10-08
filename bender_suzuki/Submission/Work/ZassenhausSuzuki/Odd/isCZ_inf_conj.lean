import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs
import Submission.Work.ZassenhausSuzuki.Odd.isCZ_basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Non-conjugate members of the Bender–Suzuki family `ℱ` intersect trivially

`isCZ_inf_conj`: two members `A`, `B` of `ℱ` (centralisers of non-identity strongly real
elements that are not involutions) either meet trivially, or `A` and `B` are `G`-conjugate.

The proof is immediate from `isCZ_basic`, which says that *every* non-identity element `a`
of a member `A ∈ ℱ` is strongly real with `C_G(a) = A`: a non-trivial `a ∈ A ⊓ B` therefore
satisfies `A = C_G(a) = B`.
-/

namespace Work.ZassenhausSuzuki.Odd

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

theorem isCZ_inf_conj (h : Work.ZassenhausSuzuki.Odd.SzOddHyp H Q t)
    {A B : Subgroup G} (hA : Work.ZassenhausSuzuki.Odd.IsCZ A)
    (hB : Work.ZassenhausSuzuki.Odd.IsCZ B) :
    A ⊓ B = ⊥ ∨ ∃ g : G, B = Submission.Blueprint.conj g A := by
  rcases eq_or_ne (A ⊓ B) ⊥ with hbot | hne
  · exact Or.inl hbot
  · right
    -- A non-trivial element of the intersection realizes both centralisers
    have hex : ∃ a : G, a ∈ A ⊓ B ∧ a ≠ 1 := by
      by_contra hc
      push Not at hc
      exact hne ((Subgroup.eq_bot_iff_forall _).mpr (fun x hx => hc x hx))
    obtain ⟨a, ha, ha1⟩ := hex
    have haA : a ∈ A := (Subgroup.mem_inf.mp ha).1
    have haB : a ∈ B := (Subgroup.mem_inf.mp ha).2
    have hcA : Subgroup.centralizer ({a} : Set G) = A :=
      ((isCZ_basic h hA).2.2 a haA ha1).2
    have hcB : Subgroup.centralizer ({a} : Set G) = B :=
      ((isCZ_basic h hB).2.2 a haB ha1).2
    have hAB : A = B := by rw [← hcA, hcB]
    refine ⟨1, ?_⟩
    rw [← hAB, Submission.Blueprint.conj, map_one]
    exact (Subgroup.map_id A).symm

end Work.ZassenhausSuzuki.Odd
