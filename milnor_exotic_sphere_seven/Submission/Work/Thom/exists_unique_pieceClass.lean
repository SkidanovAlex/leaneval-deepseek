import Mathlib
import Submission.Work.Thom.thomClass_of_finite_cover
import Submission.Work.Thom.pdCohMap_finInter_eq_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

/-- **Existence and uniqueness of a Thom class detected by a finite open cover.**

The finite-cover Thom class theorem `Work.Thom.thomClass_of_finite_cover` produces a class over
`⋃ k, U k` restricting to the prescribed classes `c S hS` on the pieces `finInter U S`.  This module
upgrades existence to existence *and* uniqueness: if two classes over the union have the same
restrictions to every piece, their difference restricts to `0` on every piece, hence vanishes by
`Work.Thom.pdCohMap_finInter_eq_zero` (which uses the low-degree vanishing hypothesis `hlowU`).
So the class over the union is canonical. -/
theorem exists_unique_pieceClass {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι)
    (n : ℕ) (hn : 1 ≤ n) (N : ℕ) (U : Fin N → Set B) (hU : ∀ k, IsOpen (U k))
    (c : ∀ S : Finset (Fin N), S.Nonempty → Work.Thom.PieceCoh Z (Work.Thom.finInter U S) n)
    (hc : ∀ (S : Finset (Fin N)) (hS : S.Nonempty) (j : ℕ),
      Function.Bijective (Work.Thom.localThomMap Z n (Work.Thom.finInter U S) (c S hS) j))
    (hcompat : ∀ (S T : Finset (Fin N)) (hS : S.Nonempty) (hT : T.Nonempty) (hST : S ⊆ T),
      (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (Work.Thom.finInter U S)) (Z.proj ⁻¹' (Work.Thom.finInter U T))
        (Set.preimage_mono (Work.Thom.finInter_mono hST)) n).hom (c S hS) = c T hT)
    (hlowU : ∀ A : Finset (Finset (Fin N)), (∀ S ∈ A, S.Nonempty) → A.Nonempty →
      Subsingleton (Work.Thom.PieceCoh Z (⋃ S ∈ A, Work.Thom.finInter U S) (n - 1))) :
    ∃! cU : Work.Thom.PieceCoh Z (⋃ k, U k) n,
      (∀ j : ℕ, Function.Bijective (Work.Thom.localThomMap Z n (⋃ k, U k) cU j)) ∧
      (∀ (S : Finset (Fin N)) (hS : S.Nonempty),
        (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' (⋃ k, U k)) (Z.proj ⁻¹' (Work.Thom.finInter U S))
          (Set.preimage_mono (Work.Thom.finInter_nonempty_subset_iUnion hS)) n).hom cU
          = c S hS) := by
  -- Existence: the finite-cover Thom class theorem.
  obtain ⟨cU, hcU, hresU⟩ :=
    Work.Thom.thomClass_of_finite_cover Z n hn N U hU c hc hcompat hlowU
  refine ⟨cU, ⟨hcU, hresU⟩, ?_⟩
  -- Uniqueness: a class agreeing with `cU` on every piece equals `cU`.
  intro y hy
  obtain ⟨-, hyres⟩ := hy
  have hdiff : y - cU = 0 := by
    apply Work.Thom.pdCohMap_finInter_eq_zero Z n N U hU hlowU (y - cU)
    intro S hS
    rw [map_sub, hresU S hS, hyres S hS, sub_self]
  exact sub_eq_zero.mp hdiff

end Work.Thom
