import Mathlib
import Submission.Work.ThomBordism.Grassmann.p1RatAux
import Submission.Work.ThomBordism.Grassmann.p1RatPuncture
import Submission.Work.Gen.ChernGenerator
import Submission.Work.Gen.ChernGeneratorTwo
import Submission.Work.Gen.TautDualPuncture
import Submission.Work.Thom.realification_homeo
import Submission.Work.Thom.complexPullback
import Submission.Work.Thom.coreMorphism
import Submission.Work.Thom.comapAux
import Submission.Work.Thom.Continuous
import Submission.Work.Thom.IsoPunct

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The bundle `O(1) ⊕ O(-1)` over `ℂP²` and the two-set cover of its punctured total space

This module fixes the vocabulary of the crux `Work.ThomBordism.Grassmann.chernReducedRatNeZero`:
the complex rank-`2` bundle

`chernRedE = O(1) ⊕ O(-1) = Work.Whitney.whitneySum (Work.Gen.tautDual 2) (Work.Gen.tautLine 2)`

over `ℂP²`, its realification `chernRedW`, the punctured total space `chernRedX = chernRedW ∖ 0`
(of real dimension `8`), and the two open pieces

* `chernRedU = {p | coord0 p ≠ 0}`  ("the first summand does not vanish"),
* `chernRedV = {p | coord1 p ≠ 0}`  ("the second summand does not vanish")

of the two-set Mayer–Vietoris cover `chernRedU ∪ chernRedV = chernRedX`.

The main algebraic content of the crux is that `H⁴(chernRedX; ℤ) = 0`, which the Mayer–Vietoris
sequence of this cover reduces to `H⁴(chernRedU) = H⁴(chernRedV) = H⁴(chernRedU ∩ chernRedV) = 0`.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

/-- The tautological dual line bundle `O(1)` over `ℂP²`. -/
abbrev chernRedL₁ : VectorBundleCore ℂ (Work.Projective.CP 2) (EuclideanSpace ℂ (Fin 1)) (Fin 3) :=
  Work.Gen.tautDual 2

/-- The tautological line bundle `O(-1)` over `ℂP²`. -/
abbrev chernRedL₂ : VectorBundleCore ℂ (Work.Projective.CP 2) (EuclideanSpace ℂ (Fin 1)) (Fin 3) :=
  Work.Gen.tautLine 2

/-- **The complex rank-`2` bundle `O(1) ⊕ O(-1)` over `ℂP²`.** -/
abbrev chernRedE :
    VectorBundleCore ℂ (Work.Projective.CP 2) (EuclideanSpace ℂ (Fin 2)) (Fin 3 × Fin 3) :=
  Work.Whitney.whitneySum chernRedL₁ chernRedL₂

/-- The underlying real rank-`4` bundle of `chernRedE`. -/
abbrev chernRedW :
    RealBundle (Work.Projective.CP 2) (EuclideanSpace ℂ (Fin 2)) (Fin 3 × Fin 3) :=
  Work.Thom.realification chernRedE

/-- The fibre of `chernRedW` at a point, as an element of the standard fibre `ℂ²`. -/
abbrev chernRedFib (p : chernRedW.TotalSpace) : EuclideanSpace ℂ (Fin 2) := p.2

/-- The first coordinate of the fibre of `chernRedW`. -/
def chernRedCoord0 (p : chernRedW.TotalSpace) : ℂ := chernRedFib p 0

/-- The second coordinate of the fibre of `chernRedW`. -/
def chernRedCoord1 (p : chernRedW.TotalSpace) : ℂ := chernRedFib p 1

/-- **The punctured total space** `E ∖ 0` of `chernRedW`. -/
abbrev chernRedX : Set chernRedW.TotalSpace := Work.Thom.zeroComplement chernRedW

/-- **The first piece of the cover**: the points of `E ∖ 0` where the first summand does not
vanish. -/
def chernRedU : Set ↥chernRedX := {p | chernRedCoord0 p.1 ≠ 0}

/-- **The second piece of the cover**: the points of `E ∖ 0` where the second summand does not
vanish. -/
def chernRedV : Set ↥chernRedX := {p | chernRedCoord1 p.1 ≠ 0}

/-! ## Elementary properties of the coordinates -/

@[simp] theorem chernRedCoord0_apply (p : chernRedW.TotalSpace) :
    chernRedCoord0 p = chernRedFib p 0 := rfl

@[simp] theorem chernRedCoord1_apply (p : chernRedW.TotalSpace) :
    chernRedCoord1 p = chernRedFib p 1 := rfl

theorem chernRedU_mem_iff (p : ↥chernRedX) :
    p ∈ chernRedU ↔ chernRedCoord0 p.1 ≠ 0 := Iff.rfl

theorem chernRedV_mem_iff (p : ↥chernRedX) :
    p ∈ chernRedV ↔ chernRedCoord1 p.1 ≠ 0 := Iff.rfl

/-- Membership in the punctured total space, in terms of the fibre coordinates. -/
theorem chernRedX_mem_iff (p : ↥chernRedX) : chernRedFib p.1 ≠ 0 := p.2

/-- Two points of the total space with the same base and the same fibre are equal. -/
theorem chernRed_eq_of_fib {p q : chernRedW.TotalSpace} (h1 : p.1 = q.1)
    (h2 : chernRedFib p = chernRedFib q) : p = q := by
  obtain ⟨b, v⟩ := p
  obtain ⟨b', v'⟩ := q
  simp only at h1
  subst h1
  simp only [chernRedFib] at h2
  subst h2
  rfl

/-- The fibre vector is zero iff both coordinates vanish. -/
theorem chernRedFib_eq_zero_iff (p : chernRedW.TotalSpace) :
    chernRedFib p = 0 ↔ chernRedCoord0 p = 0 ∧ chernRedCoord1 p = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [chernRedCoord0_apply, h]; rfl
    · rw [chernRedCoord1_apply, h]; rfl
  · rintro ⟨h0, h1⟩
    ext i; fin_cases i
    · exact h0
    · exact h1

/-- **The cover**: every point of `E ∖ 0` lies in one of the two pieces. -/
theorem chernRedU_union_chernRedV : chernRedU ∪ chernRedV = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  by_cases h : chernRedCoord0 p.1 ≠ 0
  · exact Or.inl h
  · refine Or.inr fun h1 => ?_
    exact p.2 ((chernRedFib_eq_zero_iff p.1).2 ⟨not_not.mp h, h1⟩)

end

end Work.ThomBordism.Grassmann
