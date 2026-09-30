import Mathlib
import Submission.Work.Pi6.HALG.defs
import Submission.Work.Pi6.HALG.addCyclic_of_card_twelve
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.HALG

open CategoryTheory

noncomputable section

/-! ## Two technical lemmas about `mulTwo`

`mulTwo M` is the endomorphism "multiplication by `2`" of an abelian group `M` (an object of
`ModuleCat ℤ`).  We record that it really is `x ↦ x + x`, and that its range therefore agrees with
the range of the additive endomorphism `nsmulAddMonoidHom 2`.  This is the only place where the
`ℤ`-module structure on `↥M` and its underlying additive structure have to be compared. -/

/-- Multiplication by `2` on an object of `ModuleCat ℤ` is the map `x ↦ x + x`. -/
lemma mulTwo_hom_eq_add_self (M : ModuleCat ℤ) (x : ↥M) : (mulTwo M).hom x = x + x := by
  show ((2 : ℤ) • 𝟙 M).hom x = x + x
  rw [show (2 : ℤ) • (𝟙 M : M ⟶ M) = 𝟙 M + 𝟙 M from two_zsmul _]
  simp

/-- The range of `mulTwo M`, as an additive subgroup, is the subgroup of twice-elements, i.e. the
range of `nsmulAddMonoidHom 2`. -/
lemma range_mulTwo_toAddSubgroup (M : ModuleCat ℤ) :
    (LinearMap.range (mulTwo M).hom).toAddSubgroup
      = (nsmulAddMonoidHom (α := ↥M) 2).range := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, LinearMap.mem_range, AddMonoidHom.mem_range,
    nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [two_nsmul, ← mulTwo_hom_eq_add_self]; exact hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [mulTwo_hom_eq_add_self, ← two_nsmul]; exact hy⟩

/-- **HALG step 6: `H₆(Z;ℤ)` is cyclic (given `|H₆(Z;ℤ)| = 12`, `|H₆(Z;𝔽₂)| = 2`, `H₅(Z;ℤ) = 0`).**

Write `Submission/Work/Pi6/HALG/cyclicZ.lean` (module `Submission.Work.Pi6.HALG.cyclicZ`), namespace
`Work.Pi6.HALG`.  Imports: `Submission.Work.Pi6.Interfaces`, `Submission.Work.Pi6.HALG.defs`,
`Submission.Work.Pi6.HALG.addCyclic_of_card_twelve`.

Route.  `hB2` at `n = 5` gives the short exact sequence
`0 → H₆(X;ℤ)/2H₆(X;ℤ) → H₆(X;𝔽₂) → H₅(X;ℤ)[2] → 0`; `h5` makes the last term trivial, so the first
map is a bijection and `Nat.card ↥(twoCok (HR ℤ X 6)) = 2` (from `hmod2`).  The quotient
`↥(twoCok (HR ℤ X 6)) = ↥(HR ℤ X 6) ⧸ LinearMap.range (mulTwo (HR ℤ X 6)).hom` is the same
quotient as `↥(HR ℤ X 6) ⧸ (nsmulAddMonoidHom 2).range` (the two subgroups have the same elements:
`(mulTwo M).hom x = 2 • x`), so `Nat.card (G ⧸ (nsmulAddMonoidHom 2).range) = 2` for
`G = ↥(HR ℤ X 6)`; conclude with `Work.Pi6.HALG.addCyclic_of_card_twelve` and `hcard`. -/
theorem cyclicZ (hB2 : Work.Pi6.HALG.BocksteinTwo) (X : Type) [TopologicalSpace X]
    (hcard : Nat.card ↥(Work.Pi6.HR ℤ X 6) = 12)
    (hmod2 : Nat.card ↥(Work.Pi6.HR (ZMod 2) X 6) = 2)
    (h5 : Subsingleton ↥(Work.Pi6.HR ℤ X 5)) :
    IsAddCyclic (Work.Pi6.HR ℤ X 6) := by
  obtain ⟨i, p, hspec⟩ := hB2
  obtain ⟨hinj, hex, _hsurj⟩ := hspec X 5
  -- the target `H₅(X;ℤ)[2]` of the Bockstein sequence is trivial by `h5`
  have hle : ∀ a b : ↥(twoKer (Work.Pi6.HR ℤ X 5)), a = b :=
    fun a b => Subtype.ext (h5.allEq a.1 b.1)
  -- hence `p` is the zero map and, by exactness, `i` is surjective
  have hsurji : Function.Surjective (i X 5) := by
    intro y
    have hy : y ∈ LinearMap.ker (p X 5) := by
      rw [LinearMap.mem_ker]
      exact hle (p X 5 y) 0
    rw [LinearMap.exact_iff.mp hex] at hy
    simpa using hy
  -- so `i` is a bijection and `H₆(X;ℤ)/2H₆(X;ℤ)` has two elements
  have hbij : Nat.card ↥(twoCok (Work.Pi6.HR ℤ X 6)) = 2 := by
    rw [← hmod2]
    exact Nat.card_congr (Equiv.ofBijective (i X 5) ⟨hinj, hsurji⟩)
  -- rewrite the quotient `twoCok` in terms of `nsmulAddMonoidHom`
  have hquot : Nat.card
      (↥(Work.Pi6.HR ℤ X 6) ⧸
        (nsmulAddMonoidHom (α := ↥(Work.Pi6.HR ℤ X 6)) 2).range) = 2 := by
    have h' : Nat.card (↥(Work.Pi6.HR ℤ X 6) ⧸
        (LinearMap.range (mulTwo (Work.Pi6.HR ℤ X 6)).hom).toAddSubgroup) = 2 := hbij
    rw [range_mulTwo_toAddSubgroup (Work.Pi6.HR ℤ X 6)] at h'
    exact h'
  exact addCyclic_of_card_twelve ↥(Work.Pi6.HR ℤ X 6) hcard hquot

end

end Work.Pi6.HALG
