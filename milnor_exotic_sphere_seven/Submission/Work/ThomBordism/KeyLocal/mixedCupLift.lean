import Submission.Work.ThomBordism.KeyLocal.tubeSets
import Submission.Work.Serre.relRelCupOpen_mixedCup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory

/-!
# The point-relative lift of the mixed cup

The last mile computes the class `mixedCup 8 k w U` of the Thom pair `(ν, ν∖0)`, where the tangential
factor `w = π^*(relToAbs o)` is the pullback of an *absolute* class.  To be able to use the
relative–relative cup (and hence pieces (T1), (T2), (PR) and (GM) of the plan), one must know that
`mixedCup w U` is the *restriction* of a class on the pair relative to the *point* `0_x`:

  `relRelCupOpen (proj⁻¹{x}ᶜ) (ν∖0) (π^*o) U  ∈ H^{8+k}(ν, (proj⁻¹{x}ᶜ) ∪ (ν∖0))`,

whose restriction to the pair `(ν, ν∖0)` (via `Or.inr`) is `mixedCup (relToAbs (π^*o)) U`.  This is
exactly the two-relative cup / mixed cup comparison `Work.Serre.relRelCupOpen_mixedCup` combined with
the naturality of `relToAbs` (`Work.Thom.relCohMap_relToAbs`) and the set identity

  `{p | proj p ≠ x} ∪ {p | ‖vec p‖ ≠ 0} = {p | p ≠ 0_x}`
-/

namespace Work.ThomBordism.KeyLocal

noncomputable section

open Work.Tubular Work.ThomBordism.PontryaginThom

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The punctured-at-`x` stalk of the normal total space is open. -/
theorem isOpen_normalPunctAt (E : EmbeddingData V (8 + k)) (x : V.pt) :
    IsOpen (normalPunctAt E x) := by
  have h : normalPunctAt E x = NormalTotal.proj ⁻¹' ({x}ᶜ : Set V.pt) := rfl
  rw [h]
  exact isClosed_singleton.isOpen_compl.preimage (NormalTotal.continuous_proj E)

/-- **The union of the punctured stalk and the complement of the zero section is the complement of
the single point `0_x`.** -/
theorem normalPunctAt_union_normalNonzero (E : EmbeddingData V (8 + k)) (x : V.pt) :
    normalPunctAt E x ∪ normalNonzero E
      = {p : NormalTotal E | p ≠ zeroSectionNormal E x} := by
  ext p
  simp only [normalPunctAt, normalNonzero, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (h | h)
    · intro hcon
      exact h (by rw [hcon]; rfl)
    · intro hcon
      refine h ?_
      rw [hcon]
      simp [normalNorm]
  · intro hp
    by_contra h
    rw [not_or] at h
    obtain ⟨h1, h2⟩ := h
    apply hp
    have h1' : p.proj = x := not_not.mp h1
    have h2' : p.vec = 0 := by
      have h2'' : normalNorm E p = 0 := not_not.mp h2
      simpa [normalNorm, NormalTotal.vec] using norm_eq_zero.mp h2''
    apply NormalTotal.ext
    show (p.1.1, p.1.2) = (x, (0 : Work.Tubular.Euc (8 + k)))
    rw [show p.1.1 = x from h1']
    rw [show p.1.2 = 0 from h2']

/-- **The point-relative lift of the mixed cup.**

For any tangential relative class `o` of the pair `(V, V∖x)` and any class `U` of the Thom pair
`(ν, ν∖0)`, the relative–relative cup of `π^*o` and `U`, computed in the pair relative to the union
of the punctured stalk and the complement of the zero section (which is the complement of the single
point `0_x`, `normalPunctAt_union_normalNonzero`), restricts along `(ν, ν∖0) → (ν, (π⁻¹{x})ᶜ ∪ (ν∖0))`
to the mixed cup of the *absolute* class `π^*(relToAbs o)` and `U`. -/
theorem mixedCup_restrict_relRelCup (E : EmbeddingData V (8 + k)) (x : V.pt)
    (o : Work.Thom.RelCoh ℤ 8 V.pt (FrameSigns.punct V x))
    (U : Work.Thom.RelCoh ℤ k (TopCat.of (NormalTotal E)) (normalNonzero E)) :
    (Work.Thom.relCohMap (ContinuousMap.id (NormalTotal E)) (normalNonzero E)
        (normalPunctAt E x ∪ normalNonzero E)
        (fun z hz => Or.inr hz) ℤ (8 + k)).hom
      (Work.Whitney.relRelCupOpen (normalPunctAt E x) (normalNonzero E)
        (isOpen_normalPunctAt E x) (isOpen_normalNonzero E) 8 k
        ((Work.Thom.relCohMap
            (⟨NormalTotal.proj, NormalTotal.continuous_proj E⟩ :
              C(NormalTotal E, V.pt)) (normalPunctAt E x) (FrameSigns.punct V x)
            (fun p hp => hp) ℤ 8).hom o) U)
      = Work.Cohomology.mixedCup (TopCat.of (NormalTotal E)) (normalNonzero E) 8 k
          ((Work.Thom.CohMap
            (⟨NormalTotal.proj, NormalTotal.continuous_proj E⟩ :
              C(NormalTotal E, V.pt)) ℤ 8).hom
            ((Work.Thom.relToAbs ℤ (FrameSigns.punct V x) 8).hom o)) U := by
  classical
  have hnat := Work.Thom.relCohMap_relToAbs_apply
    (⟨NormalTotal.proj, NormalTotal.continuous_proj E⟩ : C(NormalTotal E, V.pt))
    (normalPunctAt E x) (FrameSigns.punct V x) (fun p hp => hp) ℤ 8 o
  rw [Work.Serre.relRelCupOpen_mixedCup (normalPunctAt E x) (normalNonzero E)
    (isOpen_normalPunctAt E x) (isOpen_normalNonzero E) 8 k
    ((Work.Thom.relCohMap
        (⟨NormalTotal.proj, NormalTotal.continuous_proj E⟩ :
          C(NormalTotal E, V.pt)) (normalPunctAt E x) (FrameSigns.punct V x)
        (fun p hp => hp) ℤ 8).hom o) U, ← hnat]
  rfl

end

end Work.ThomBordism.KeyLocal
