/-
# Node N11: `FP₂` transfer and the Bieri–Strebel lemma — assembled statements

This file assembles the two deliverables of node N11 of the route design for
`annals_on_coherence_of_one_relator_groups`:

* **Transfer of `FP₂` to finitely generated subgroups.** If `k[G]` is coherent (as a ring, i.e.
  every finitely generated left ideal is finitely presented) then every finitely generated
  subgroup of `G` is of type `FP₂` over `k`.  In the form requested by the design,
  `Ring.Coherent ℚ[G] → ∀ H ≤ G, H.FG → IsFP2 ℚ H`, see `homologicallyCoherent_of_coherent`.

* **Bieri–Strebel Lemma 2.1** (= JL Lemma 4.3): `G` is of type `FP₂` over `k` if and only if
  there is a short exact sequence `1 → N → E → G → 1` with `E` finitely presented and
  `N_ab ⊗_ℤ k = 0`; see `isFP2_iff_hasFP2Extension`.
-/
import ChallengeDeps
import Submission.Work.ORFP2.Basic
import Submission.Work.ORFP2.FreeGroupAugIdealBasisInst
import Submission.Work.ORFP2.IsFP2_of_coherent_monoidAlgebra
import Submission.Work.ORFP2.IsFP2_of_extension
import Submission.Work.ORFP2.exists_extension_of_isFP2

set_option autoImplicit false

universe u v

namespace Work.ORFP2

open MonoidAlgebra

/-- **Bieri–Strebel [BS78, Lemma 2.1] = JL Lemma 4.3, `⟸` direction.**
If `G` is the quotient of a finitely presented group `E` by a normal subgroup `N` with
`N_ab ⊗_ℤ k = 0`, then `G` is of type `FP₂` over `k`. -/
theorem isFP2_of_extension' (k : Type u) [CommRing k] [Nontrivial k] {G : Type v} [Group G]
    {E : Type v} [Group E] (f : E →* G) (hf : Function.Surjective f)
    (hE : Group.IsFinitelyPresented E) (hN : H1Vanishes k (MonoidHom.ker f)) : IsFP2 k G :=
  IsFP2_of_extension.{u, v, v, u} k (freeGroupAugIdealBasis_inst.{u} k) G E f hf hE hN

/-- **Bieri–Strebel [BS78, Lemma 2.1] = JL Lemma 4.3, `⟹` direction.**
A group of type `FP₂` over `k` is the quotient of a finitely presented group by a normal
subgroup `N` with `N_ab ⊗_ℤ k = 0`. -/
theorem exists_extension_of_isFP2' (k : Type u) [CommRing k] [Nontrivial k] {G : Type v} [Group G]
    (h : IsFP2 k G) : HasFP2Extension.{u, v, v} k G :=
  exists_extension_of_isFP2.{u, v, u, v} k (freeGroupAugIdealBasis_inst.{u} k) G h

/-- **Bieri–Strebel [BS78, Lemma 2.1] = JL Lemma 4.3**: for a commutative ring `k` with `1 ≠ 0`,
a group `G` is of type `FP₂` over `k` if and only if there is a short exact sequence
`1 → N → E → G → 1` with `E` finitely presented and `N_ab ⊗_ℤ k = 0`. -/
theorem isFP2_iff_hasFP2Extension (k : Type u) [CommRing k] [Nontrivial k] (G : Type v) [Group G] :
    IsFP2 k G ↔ HasFP2Extension.{u, v, v} k G :=
  ⟨fun h => exists_extension_of_isFP2' k h,
    fun h => by
      obtain ⟨E, _, f, hf, hfp, hN⟩ := h
      exact isFP2_of_extension' k f hf hfp hN⟩

/-- **Transfer of `FP₂` to finitely generated subgroups.**  If `k[G]` is coherent then every
finitely generated subgroup of `G` is of type `FP₂` over `k`. -/
theorem IsFP2_of_coherent (k : Type*) [CommRing k] (G : Type*) [Group G] (H : Subgroup G)
    (hH : H.FG) (h : Ring.Coherent (MonoidAlgebra k G)) : IsFP2 k H :=
  IsFP2_of_coherent_monoidAlgebra k G H hH fun I hI => h I hI

/-- The transfer of `FP₂` to finitely generated subgroups, in the form of the paper's notion of
homological coherence. -/
theorem homologicallyCoherent_of_coherent (k : Type*) [CommRing k] (G : Type*) [Group G]
    (h : Ring.Coherent (MonoidAlgebra k G)) : HomologicallyCoherent k G :=
  fun H hH => IsFP2_of_coherent k G H hH h

/-- **Node N11, deliverable 1** (the `ℚ` case of the transfer).  Coherence of `ℚ[G]` implies that
every finitely generated subgroup of `G` is of type `FP₂` over `ℚ`. -/
theorem homologicallyCoherent_rat_of_coherent (G : Type*) [Group G]
    (h : Ring.Coherent (MonoidAlgebra ℚ G)) : HomologicallyCoherent ℚ G :=
  homologicallyCoherent_of_coherent ℚ G h

/-- **Node N11, deliverable 1, the form stated in the route design**:
`Ring.Coherent ℚ[G] → ∀ H.FG, IsFP2 ℚ H`. -/
theorem IsFP2_rat_of_coherent (G : Type*) [Group G] (H : Subgroup G) (hH : H.FG)
    (h : Ring.Coherent (MonoidAlgebra ℚ G)) : IsFP2 ℚ H :=
  IsFP2_of_coherent ℚ G H hH h

end Work.ORFP2
