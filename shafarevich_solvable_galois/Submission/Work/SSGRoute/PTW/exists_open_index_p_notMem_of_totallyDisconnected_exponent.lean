import Mathlib.GroupTheory.Frattini
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Submission.Commons.GroupTheory.PGroup.frattini_eq_pow_sup_commutator
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTW

/-- **Open index-`p` subgroups separate points of a compact totally disconnected abelian group of
exponent `p`.**  A compact Hausdorff totally disconnected group has a neighbourhood basis of `1` by
open subgroups (`ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`).  Given `q ≠ 1`, pick
an open normal subgroup `H ∌ q`.  The quotient `Q ⧸ H` is a finite abelian group of exponent `p`,
i.e. a finite `𝔽_p`-vector space; its Frattini subgroup is trivial
(`Commons.GroupTheory.PGroup.frattini_eq_bot_of_elementary_abelian`), so some maximal subgroup
excludes `qH`, and a maximal subgroup of a finite elementary abelian `p`-group has index `p`
(`Commons.GroupTheory.PGroup.natCard_quotient_coatom_eq_prime`).  Pulling it back along the quotient
map gives the desired open index-`p` subgroup. -/
theorem exists_open_index_p_notMem_of_totallyDisconnected_exponent
    (Q : Type*) [CommGroup Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q] (p : ℕ) [Fact p.Prime]
    (hexp : ∀ q : Q, q ^ p = 1) (q : Q) (hq : q ≠ 1) :
    ∃ U : Subgroup Q, IsOpen (U : Set Q) ∧ U.index = p ∧ q ∉ U := by
  -- an open normal subgroup avoiding `q`
  obtain ⟨H, hHsub⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (U := {x : Q | x ≠ q}) isOpen_compl_singleton (by simpa using hq.symm)
  have hHq : q ∉ (H : Subgroup Q) := fun hc => hHsub hc rfl
  haveI : DiscreteTopology (Q ⧸ (H : Subgroup Q)) := QuotientGroup.discreteTopology H.isOpen'
  haveI : Finite (Q ⧸ (H : Subgroup Q)) :=
    Subgroup.quotient_finite_of_isOpen _ H.isOpen'
  have hexpM : ∀ m : Q ⧸ (H : Subgroup Q), m ^ p = 1 := by
    intro m
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (H : Subgroup Q) m
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [hexp g]; exact (H : Subgroup Q).one_mem
  have hqbar : (QuotientGroup.mk q : Q ⧸ (H : Subgroup Q)) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]; exact hHq
  -- a maximal subgroup of the finite elementary abelian quotient avoiding the image of `q`
  have hdir : frattini (Q ⧸ (H : Subgroup Q)) = ⊥ :=
    Commons.GroupTheory.PGroup.frattini_eq_bot_of_elementary_abelian hexpM
  have hnotin : (QuotientGroup.mk q : Q ⧸ (H : Subgroup Q)) ∉ frattini (Q ⧸ (H : Subgroup Q)) := by
    rw [hdir]; exact hqbar
  obtain ⟨K, hKcoat, hKq⟩ : ∃ K : Subgroup (Q ⧸ (H : Subgroup Q)),
      IsCoatom K ∧ (QuotientGroup.mk q : Q ⧸ (H : Subgroup Q)) ∉ K := by
    by_contra hcon
    apply hnotin
    rw [frattini, Order.radical]
    simp only [Subgroup.mem_iInf, Set.mem_ofPred_eq]
    intro K hK
    by_contra hKq
    exact hcon ⟨K, hK, hKq⟩
  -- its index is `p`
  have hP : IsPGroup p (Q ⧸ (H : Subgroup Q)) :=
    isPGroup_iff_pow_pow_eq_one.mpr (fun g => ⟨1, by simpa using hexpM g⟩)
  have hcard : Nat.card ((Q ⧸ (H : Subgroup Q)) ⧸ K) = p :=
    Commons.GroupTheory.PGroup.natCard_quotient_coatom_eq_prime hP hKcoat
  have hKindex : K.index = p := by rw [Subgroup.index_eq_card, hcard]
  refine ⟨K.comap (QuotientGroup.mk' (H : Subgroup Q)), ?_, ?_, ?_⟩
  · exact (show IsOpen (K : Set (Q ⧸ (H : Subgroup Q))) from isOpen_discrete _).preimage
      QuotientGroup.continuous_mk
  · rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective (H : Subgroup Q)),
      hKindex]
  · intro hc
    exact hKq (by rw [Subgroup.mem_comap, QuotientGroup.mk'_apply] at hc; exact hc)

end Work.SSGRoute.PTW
