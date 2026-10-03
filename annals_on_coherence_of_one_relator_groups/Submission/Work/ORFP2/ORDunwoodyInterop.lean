/-
# Interoperability with node N13 (`Work.ORDunwoody`)

Node N13 of the route design (JL §4) works with its own copies of the vocabulary of this area:
`Work.ORDunwoody.IsFP2`, `Work.ORDunwoody.AbelianizationTensorVanishes`,
`Work.ORDunwoody.HomologicallyCoherent` and the hypothesis `Work.ORDunwoody.BieriStrebel`.

The lemmas below identify those with `Work.ORFP2.IsFP2`, `Work.ORFP2.H1Vanishes`,
`Work.ORFP2.HomologicallyCoherent` and `Work.ORFP2.HasFP2Extension`, so that the theorems proved
in this directory can be used to discharge the N13 hypotheses.
-/
import Submission.Work.ORFP2.Basic
import Submission.Work.ORDunwoody.FP2

set_option autoImplicit false

universe u

namespace Work.ORFP2

open MonoidAlgebra

/-- `Work.ORFP2.augIdeal` and `Work.ORDunwoody.augmentationIdeal` are the same ideal. -/
theorem augIdeal_eq_augmentationIdeal (k : Type*) [CommRing k] (G : Type*) [Group G] :
    augIdeal k G = Work.ORDunwoody.augmentationIdeal k G := by
  simp only [augIdeal, Work.ORDunwoody.augmentationIdeal, MonoidAlgebra.of_apply]

/-- The two formalisations of `FP₂` over `k` agree. -/
theorem isFP2_iff_ORDunwoody (k : Type*) [CommRing k] (G : Type*) [Group G] :
    IsFP2 k G ↔ Work.ORDunwoody.IsFP2 k G := by
  rw [IsFP2, Work.ORDunwoody.IsFP2, augIdeal_eq_augmentationIdeal]

/-- The two formalisations of `N_ab ⊗_ℤ k = 0` agree (they are the same definition). -/
theorem h1Vanishes_iff_ORDunwoody (k : Type*) [CommRing k] (N : Type*) [Group N] :
    H1Vanishes k N ↔ Work.ORDunwoody.AbelianizationTensorVanishes k N :=
  Iff.rfl

/-- The two formalisations of homological coherence agree. -/
theorem homologicallyCoherent_iff_ORDunwoody (k : Type*) [CommRing k] (G : Type*) [Group G] :
    HomologicallyCoherent k G ↔ Work.ORDunwoody.HomologicallyCoherent k G := by
  rw [HomologicallyCoherent, Work.ORDunwoody.HomologicallyCoherent]
  refine forall_congr' fun H => ?_
  rw [isFP2_iff_ORDunwoody]


/-- `Work.ORFP2.HasFP2Extension` is the right hand side of the Bieri–Strebel lemma in the form used
by node N13 (all groups in the universe of `k`). -/
theorem hasFP2Extension_iff_ORDunwoody (k : Type u) [CommRing k] (G : Type u) [Group G] :
    HasFP2Extension.{u, u, u} k G ↔
      ∃ (H : Type u) (_ : Group H) (π : H →* G),
        Function.Surjective π ∧ Group.IsFinitelyPresented H ∧
          Work.ORDunwoody.AbelianizationTensorVanishes k π.ker :=
  Iff.rfl

end Work.ORFP2
