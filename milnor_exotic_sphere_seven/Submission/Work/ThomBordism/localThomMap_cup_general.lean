import Mathlib
import Submission.Work.Thom.Glue
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Thom.MixedCup
import Submission.Work.StemsB.collarSqMixed

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory

namespace Work.ThomBordism

/-!
# The local Thom map is linear over `H⁰(W;ℤ)` in every degree

The local Thom map `Work.Thom.localThomMap Z n W τ : H^k(W;ℤ) → H^{k+n}(X|_W, X|_W∖0)`
of a piece class `τ` is multiplicative: multiplying the *piece class* `τ` by a degree-zero class
`c ∈ H⁰(W;ℤ)` and then applying the Thom map in degree `k` is the same as applying the Thom map of
`τ` to `x ⌣ c`.  The case `k = 0` is `Work.Thom.localThomMap_cup_zero`
(`Submission/Work/Thom/localThomMap_cup_zero.lean`); here we generalise it to every degree `k`.

The mathematical content is the associativity of the (mixed, absolute ⌣ relative) cup product
`x ⌣ (c ⌣ τ) = (x ⌣ c) ⌣ τ` together with the fact that `c` has degree `0`.  On the cochain level
it is `Work.Cohomology.cupAssoc`, transported through the degree bookkeeping that the
definitionally-present cast `Nat.zero_add n` forces.
-/

/-- **Associativity of the mixed cup product in a degree-zero factor, in every degree.**

For an absolute class `a` of degree `k`, an absolute class `b` of degree `0` and a relative class
`z`,

`a ⌣ (b ⌣ z) = (a ⌣ b) ⌣ z`,

where the inner relative class `b ⌣ z` sits in degree `0 + n` and is transported to degree `n`
along `h : 0 + n = n`.  This is the general-degree form of
`Work.Thom.mixedCupC_zero_cast_assoc` (the case `k = 0`). -/
theorem mixedCupC_zero_cast_assoc_gen {B : Type} [TopologicalSpace B] (A : Set B) (k n : ℕ)
    (h : 0 + n = n) (a : Work.Thom.Coh ℤ k B) (b : Work.Thom.Coh ℤ 0 B)
    (z : Work.Thom.RelCoh ℤ n B A) :
    (Work.Thom.mixedCupC ℤ A k n) a (h ▸ ((Work.Thom.mixedCupC ℤ A 0 n) b z))
      = (Work.Thom.mixedCupC ℤ A k n)
          (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of B)) k 0 a b) z := by
  obtain ⟨α, hα, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of B)) k a
  obtain ⟨β, hβ, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of B)) 0 b
  obtain ⟨ζ, hζ, rfl⟩ := Work.Cohomology.exists_relClassOf ℤ (TopCat.of B) A n z
  simp only [Work.Thom.mixedCupC_eq_mixedCup]
  obtain ⟨hmem1, hcoc1, h1⟩ :=
    Work.Cohomology.mixedCup_apply (TopCat.of B) A 0 n β ζ hβ hζ
  rw [h1]
  let u1 : Work.Cohomology.relKern ℤ (TopCat.of B) A (0 + n) :=
    ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of B)) β ζ.1, hmem1⟩
  have hu1 : Work.Cohomology.relDiffLM ℤ (TopCat.of B) A (0+n) u1 = 0 := hcoc1
  have hu1' : Work.Cohomology.relDiffLM ℤ (TopCat.of B) A n
      (((Work.Cohomology.relComplex ℤ (TopCat.of B) A).XIsoOfEq h).hom u1) = 0 := by
    rw [← Work.Cohomology.relComplex_d_apply]
    exact Work.Thom.cocycle_transport_K (K := Work.Cohomology.relComplex ℤ (TopCat.of B) A)
      h u1 (by rw [Work.Cohomology.relComplex_d_apply]; exact hu1)
  have hcast : (h ▸ Work.Cohomology.relClassOf ℤ (TopCat.of B) A u1 hu1 :
      Work.Thom.RelCoh ℤ n B A)
      = Work.Cohomology.relClassOf ℤ (TopCat.of B) A
          (((Work.Cohomology.relComplex ℤ (TopCat.of B) A).XIsoOfEq h).hom u1) hu1' :=
    Work.Thom.relClassOf_cast h u1 hu1 hu1'
  rw [hcast]
  obtain ⟨hmem2, hcoc2, h2⟩ := Work.Cohomology.mixedCup_apply (TopCat.of B) A k n α
    (((Work.Cohomology.relComplex ℤ (TopCat.of B) A).XIsoOfEq h).hom u1) hα hu1'
  rw [h2]
  rw [Work.Cohomology.cupH'_apply' ℤ (TopCat.toSSet.obj (TopCat.of B)) α β hα hβ]
  obtain ⟨hmem3, hcoc3, h3⟩ := Work.Cohomology.mixedCup_apply (TopCat.of B) A k n
    (Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of B)) α β) ζ
    (Work.Cohomology.cochainDiff_cup_of_cocycles ℤ (TopCat.toSSet.obj (TopCat.of B)) α β hα hβ) hζ
  rw [h3]
  have hcoch : Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of B)) α
        ((((Work.Cohomology.relComplex ℤ (TopCat.of B) A).XIsoOfEq h).hom u1).1)
      = Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of B))
          (Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of B)) α β) ζ.1 := by
    rw [Work.Thom.relComplex_XIsoOfEq_coe h u1]
    rw [show u1.1 = Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of B)) β ζ.1 from rfl]
    rw [Work.Thom.cup_cast_right (m := k) (α := α) (h := h)
      (h' := congrArg (fun t => k + t) h)
      (β := Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of B)) β ζ.1)]
    rw [← Work.Cohomology.cupAssoc ℤ (TopCat.toSSet.obj (TopCat.of B)) α β ζ.1]
    rw [Work.Thom.eqRec_comp (P := fun t => Work.Cohomology.Cochain ℤ
        (TopCat.toSSet.obj (TopCat.of B)) t) (Nat.add_assoc k 0 n)
      (congrArg (fun t => k + t) h)
      (Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of B))
        (Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of B)) α β) ζ.1)]
  exact Work.Cohomology.relClassOf_congr ℤ (TopCat.of B) A hcoc2 hcoc3 (Subtype.ext hcoch)

theorem localThomMap_cup_general {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ) (W : Set B)
    (τ : Work.Thom.PieceCoh Z W n) (c : Work.Thom.Coh ℤ 0 ↥W) (k : ℕ)
    (x : Work.Thom.Coh ℤ k ↥W) :
    Work.Thom.localThomMap Z n W
        ((Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W τ 0 c)) k x
      = Work.Thom.localThomMap Z n W τ k
          (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) k 0 x c) := by
  simp only [Work.Thom.localThomMap_apply]
  have key2 : (ModuleCat.Hom.hom (Work.Thom.CohMap (Work.Thom.pieceProj Z W) ℤ k))
        (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) k 0 x c)
      = Work.Cohomology.cupH' ℤ
          (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) k 0
          ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.Thom.pieceProj Z W) ℤ k)) x)
          ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.Thom.pieceProj Z W) ℤ 0)) c) :=
    Work.Cohomology.cupNaturalH ℤ (TopCat.ofHom (Work.Thom.pieceProj Z W)) k 0 x c
  rw [key2]
  exact mixedCupC_zero_cast_assoc_gen
    ((Subtype.val : ↥(Z.proj ⁻¹' W) → Z.TotalSpace) ⁻¹' Work.Thom.zeroComplement Z)
    k n (Nat.zero_add n) _ _ τ

end Work.ThomBordism
