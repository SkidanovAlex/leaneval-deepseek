import Mathlib
import Submission.Work.ORLocInd.LI.locallyIndicable_multiplicativeInt
import Submission.Work.ORLocInd.LI.locallyIndicable_prod

namespace Work.ORLocInd.Howie

/-- A non-trivial homomorphism into the infinite cyclic group can be corrected to a surjection:
the image of `ψ` is a non-trivial subgroup of `Multiplicative ℤ`, hence infinite cyclic, and an
infinite cyclic group is isomorphic to `Multiplicative ℤ`.

Concretely, if `ψ : G →* Multiplicative ℤ` is non-trivial then `ψ.range ≠ ⊥`; a non-trivial
subgroup of the torsion-free group `Multiplicative ℤ` is infinite (`infinite_zpowers`,
`not_isOfFinOrder_of_isMulTorsionFree`), and a subgroup of the cyclic group `Multiplicative ℤ` is
cyclic (`Subgroup.isCyclic`).  The isomorphism `intCyclicMulEquiv : Multiplicative ℤ ≃* ψ.range`
then turns `ψ.rangeRestrict : G →* ψ.range` into a surjection `G →* Multiplicative ℤ`. -/
theorem exists_surjective_of_ne_one {G : Type*} [Group G] (ψ : G →* Multiplicative ℤ)
    (h : ∃ g : G, ψ g ≠ 1) : ∃ χ : G →* Multiplicative ℤ, Function.Surjective χ := by
  obtain ⟨g, hg⟩ := h
  -- the image of `ψ` is non-trivial
  have hne : ψ.range ≠ ⊥ := by
    intro hbot
    have hmem : ψ g ∈ ψ.range := MonoidHom.mem_range.mpr ⟨g, rfl⟩
    rw [hbot] at hmem
    exact hg (by simpa using hmem)
  -- a non-trivial subgroup of `Multiplicative ℤ` is infinite
  have hinf : Infinite ψ.range := by
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hx' : ((x : ψ.range) : Multiplicative ℤ) ≠ 1 := by simpa using hx
    have hinf' : ((Subgroup.zpowers (x : Multiplicative ℤ) : Set (Multiplicative ℤ))).Infinite :=
      Set.infinite_coe_iff.mp (infinite_zpowers.mpr (not_isOfFinOrder_of_isMulTorsionFree hx'))
    have hle : ((Subgroup.zpowers (x : Multiplicative ℤ) : Set (Multiplicative ℤ))) ⊆
        (ψ.range : Set (Multiplicative ℤ)) := Subgroup.zpowers_le.mpr x.2
    exact Set.infinite_coe_iff.mpr (Set.Infinite.mono hle hinf')
  -- `ψ.range`, being a subgroup of the cyclic group `Multiplicative ℤ`, is cyclic, hence (being
  -- infinite) isomorphic to `Multiplicative ℤ`; compose this isomorphism with `ψ.rangeRestrict`.
  let e : ψ.range ≃* Multiplicative ℤ := (@intCyclicMulEquiv ψ.range hinf _ _).symm
  exact ⟨e.toMonoidHom.comp ψ.rangeRestrict,
    e.surjective.comp (MonoidHom.rangeRestrict_surjective ψ)⟩

end Work.ORLocInd.Howie
