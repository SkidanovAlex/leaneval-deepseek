import Mathlib
import Submission.Work.BSW.Char.Setup

namespace Work.BSW.Char

/-- Bender's condition (iii) in the form of the odd-order closure's TI-subsets: the set
`K# = K ∖ {1}` of nonidentity elements of `K` is a TI-subset with normalizer bound `C_G(t)`.
(`OddOrder.GroupTheory.IsTISubset A L` means `∀ g, (∃ a ∈ A, g * a * g⁻¹ ∈ A) → g ∈ L`; here
`a ≠ 1` and the TI condition `K ⊓ K^g = ⊥` off `C_G(t)` give `g ∈ C_G(t)`.)
This makes the Brauer–Suzuki isometry
`OddOrder.RepresentationTheory.ClassFunction.inner_induce_eq_of_isTISubset` applicable to class
functions of `C_G(t)` supported on `K#`, as in Bender §2 (p. 230). -/
theorem isTISubset_Kdiff {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) :
    OddOrder.GroupTheory.IsTISubset ((K : Set G) \ {1})
      (Subgroup.centralizer ({t} : Set G)) := by
  intro g ha
  obtain ⟨a, haK, hgaK⟩ := ha
  -- If `g` were outside `C_G(t)`, condition (iii) would force `K ⊓ K^g = ⊥`.
  by_contra hg
  have hbot : K ⊓ Work.GW2.conjSub g K = ⊥ := Work.BSW.TI h g hg
  -- But `g a g⁻¹` lies in `K` (given) and in `K^g` (image of `a`), a nontrivial overlap.
  have hmem : g * a * g⁻¹ ∈ (K ⊓ Work.GW2.conjSub g K : Subgroup G) :=
    ⟨hgaK.1, ⟨a, haK.1, rfl⟩⟩
  rw [hbot] at hmem
  have hx : g * a * g⁻¹ = 1 := Subgroup.mem_bot.mp hmem
  have ha1 : a = 1 := by
    have h1 : g⁻¹ * (g * a * g⁻¹) * g = a := by group
    rw [hx] at h1
    simpa using h1.symm
  exact haK.2 (Set.mem_singleton_iff.mpr ha1)

end Work.BSW.Char
