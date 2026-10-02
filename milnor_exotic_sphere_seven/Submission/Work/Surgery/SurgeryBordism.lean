import Submission.Work.Bordism.Invariance
import Submission.Work.Surgery.ThreeConnected

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Surgery bordisms and the numerical equivalence of surgery

The surgical proof of the dimension-`8` Hirzebruch congruence compares the numbers
`(σ, p₁², p₂)` of a manifold with those of a `3`-connected manifold *bordant* to it.  The three
numbers are bordism invariants of `Submission/Work/Bordism/`:

* the signature `Work.Bordism.sigma_eq_of_bordant` (which needs Poincaré duality on the two closed
  pieces and the middle-dimensional Lefschetz duality `Work.Bordism.HalfDimension` for the bordism),
* the Pontryagin numbers `Work.Bordism.p₁SqNumber_eq_of_bordant`,
  `Work.Bordism.p₂Number_eq_of_bordant` (which need the classes on the bordism whose restrictions to
  the two boundary pieces are the classes of the pieces).

This file packages those inputs once, as a `SurgeryBordism`, and records the resulting **numerical
equivalence** — the relation in which the surgical route proceeds: two closed oriented
`8`-manifolds are *numerically equivalently* related by a surgery bordism when their three numbers
agree.

## Main definitions

* `Work.Surgery.numberTriple` — the triple `(σ, p₁², p₂) ∈ ℚ × ℚ × ℚ` of a closed oriented
  `8`-manifold with its Pontryagin classes;
* `Work.Surgery.SameNumbers` — equality of the three numbers (numerical equivalence);
* `Work.Surgery.SurgeryBordism` — a bordism with Pontryagin data, finite-dimensional middle
  cohomology, nondegenerate middle forms and the Lefschetz-duality input `HalfDimension`, i.e.
  exactly the data under which the three numbers are bordism invariants.

## Main results

* `Work.Surgery.SurgeryBordism.numbers_eq` — the three numbers agree along a surgery bordism;
* `Work.Surgery.sameNumbers_of_pontryaginBordism` — the same, stated with the model's classes;
* `Work.Surgery.SameNumbers.refl/symm/trans` — numerical equivalence is an equivalence relation;
* `Work.Surgery.numbersInSpan8_congr` — the statements `NumbersInSpan8` only depend on the numbers.
-/

open scoped Manifold Topology ContDiff
open CategoryTheory

namespace Work.Surgery

open Work.Bordism Work.SignatureBordism Work.Cohomology

noncomputable section

variable {X Y : TopCat.{0}}

/-- **The triple of numbers** `(σ, p₁², p₂)` of a closed oriented `8`-manifold together with the
`p₁`- and `p₂`-classes of its tangent bundle, rationalised. -/
def numberTriple (X : TopCat.{0}) (c : (chainC ℤ (TopCat.toSSet.obj X)).homology 8)
    (p₁ : (cochainC ℤ (TopCat.toSSet.obj X)).homology 4)
    (p₂ : (cochainC ℤ (TopCat.toSSet.obj X)).homology 8) : ℚ × ℚ × ℚ :=
  ((sigma 4 (TopCat.toSSet.obj X) c : ℚ),
    (p₁SqNumber (TopCat.toSSet.obj X) c p₁ : ℚ),
    (p₂Number (TopCat.toSSet.obj X) c p₂ : ℚ))

/-- **Numerical equivalence**: two closed oriented `8`-manifolds (with their Pontryagin classes)
have the same signature, `p₁²`-number and `p₂`-number.  This is the relation in which the surgical
route to the dimension-`8` congruence proceeds: surgery below the middle dimension changes the
manifold but not its numbers.

It is recorded as the three componentwise equalities, rather than as an equality of the triples, so
that it can be manipulated without unfolding the definitions of the three numbers. -/
structure SameNumbers (X : TopCat.{0}) (Y : TopCat.{0})
    (c : (chainC ℤ (TopCat.toSSet.obj X)).homology 8)
    (d : (chainC ℤ (TopCat.toSSet.obj Y)).homology 8)
    (p₁ : (cochainC ℤ (TopCat.toSSet.obj X)).homology 4)
    (q₁ : (cochainC ℤ (TopCat.toSSet.obj Y)).homology 4)
    (p₂ : (cochainC ℤ (TopCat.toSSet.obj X)).homology 8)
    (q₂ : (cochainC ℤ (TopCat.toSSet.obj Y)).homology 8) : Prop where
  /-- the signatures agree -/
  sig_eq : sigma 4 (TopCat.toSSet.obj X) c = sigma 4 (TopCat.toSSet.obj Y) d
  /-- the `p₁²`-numbers agree -/
  p1sq_eq : p₁SqNumber (TopCat.toSSet.obj X) c p₁ = p₁SqNumber (TopCat.toSSet.obj Y) d q₁
  /-- the `p₂`-numbers agree -/
  p2_eq : p₂Number (TopCat.toSSet.obj X) c p₂ = p₂Number (TopCat.toSSet.obj Y) d q₂

/-- The equality of the number triples that numerical equivalence amounts to. -/
theorem numberTriple_eq_of_sameNumbers {c d p₁ q₁ p₂ q₂}
    (h : SameNumbers X Y c d p₁ q₁ p₂ q₂) :
    numberTriple X c p₁ p₂ = numberTriple Y d q₁ q₂ := by
  have h₁ : (sigma 4 (TopCat.toSSet.obj X) c : ℚ) = (sigma 4 (TopCat.toSSet.obj Y) d : ℚ) := by
    exact_mod_cast h.sig_eq
  have h₂ : (p₁SqNumber (TopCat.toSSet.obj X) c p₁ : ℚ)
      = (p₁SqNumber (TopCat.toSSet.obj Y) d q₁ : ℚ) := by
    exact_mod_cast h.p1sq_eq
  have h₃ : (p₂Number (TopCat.toSSet.obj X) c p₂ : ℚ)
      = (p₂Number (TopCat.toSSet.obj Y) d q₂ : ℚ) := by
    exact_mod_cast h.p2_eq
  unfold numberTriple
  exact Prod.ext h₁ (Prod.ext h₂ h₃)

theorem SameNumbers.refl (X : TopCat.{0}) (c : (chainC ℤ (TopCat.toSSet.obj X)).homology 8)
    (p₁ : (cochainC ℤ (TopCat.toSSet.obj X)).homology 4)
    (p₂ : (cochainC ℤ (TopCat.toSSet.obj X)).homology 8) :
    SameNumbers X X c c p₁ p₁ p₂ p₂ :=
  ⟨rfl, rfl, rfl⟩

theorem SameNumbers.symm {c d p₁ q₁ p₂ q₂} (h : SameNumbers X Y c d p₁ q₁ p₂ q₂) :
    SameNumbers Y X d c q₁ p₁ q₂ p₂ :=
  ⟨h.sig_eq.symm, h.p1sq_eq.symm, h.p2_eq.symm⟩

theorem SameNumbers.trans {Z : TopCat.{0}} {c d e p₁ q₁ r₁ p₂ q₂ r₂}
    (h₁ : SameNumbers X Y c d p₁ q₁ p₂ q₂) (h₂ : SameNumbers Y Z d e q₁ r₁ q₂ r₂) :
    SameNumbers X Z c e p₁ r₁ p₂ r₂ :=
  ⟨h₁.sig_eq.trans h₂.sig_eq, h₁.p1sq_eq.trans h₂.p1sq_eq, h₁.p2_eq.trans h₂.p2_eq⟩

/-- Membership of the number triple in the span of the two generator triples only depends on the
numbers: this is the bridge between numerical equivalence and `NumbersInSpan8`. -/
theorem numbersInSpan8_congr {c d p₁ q₁ p₂ q₂} (h : SameNumbers X Y c d p₁ q₁ p₂ q₂)
    (hX : NumbersInSpan8 (TopCat.toSSet.obj X) c p₁ p₂) :
    NumbersInSpan8 (TopCat.toSSet.obj Y) d q₁ q₂ := by
  unfold NumbersInSpan8 at hX ⊢
  exact (congrArg (fun t : ℚ × ℚ × ℚ =>
    t ∈ Submodule.span ℚ ({cp4Tuple, cp2cp2Tuple} : Set (ℚ × ℚ × ℚ)))
    (numberTriple_eq_of_sameNumbers h)).mp hX

/-! ## Surgery bordisms -/

/-- **A surgery bordism**: a bordism between closed oriented `8`-manifolds, together with the
Pontryagin classes on the bordism (whose restrictions to the two boundary pieces are the classes of
the pieces) and the duality inputs for the signature.  This is exactly the geometric data under
which the three numbers `(σ, p₁², p₂)` are bordism invariants. -/
structure SurgeryBordism (M N : ClosedOriented 8) extends PontryaginBordism M N where
  /-- the middle cohomology of `M` is finite dimensional (so that the signature is defined) -/
  finM : FiniteDimensional ℚ (ratCohomology 4 (TopCat.toSSet.obj M.X))
  /-- the middle cohomology of `N` is finite dimensional -/
  finN : FiniteDimensional ℚ (ratCohomology 4 (TopCat.toSSet.obj N.X))
  /-- Poincaré duality on `M`: the middle intersection form is nondegenerate -/
  ndM : Nondegenerate (midForm (k := 4) M)
  /-- Poincaré duality on `N` -/
  ndN : Nondegenerate (midForm (k := 4) N)
  /-- the middle-dimensional Lefschetz duality of the bordism (`HalfDimension`) -/
  half : HalfDimension 4 (PontryaginBordism.toBordism toPontryaginBordism)

namespace SurgeryBordism

variable {M N : ClosedOriented 8} (h : SurgeryBordism M N)

/-- **The three numbers agree along a surgery bordism**: `(σ, p₁², p₂)(M) = (σ, p₁², p₂)(N)`,
with the Pontryagin classes of the bordism on both sides. -/
theorem numbers_eq :
    numberTriple M.X M.c h.p₁M h.p₂M = numberTriple N.X N.c h.p₁N h.p₂N := by
  haveI := h.finM
  haveI := h.finN
  have hnum := PontryaginBordism.full_numbers_eq h.toPontryaginBordism h.ndM h.ndN h.half
  have h₁ : (sigma 4 (TopCat.toSSet.obj M.X) M.c : ℚ)
      = (sigma 4 (TopCat.toSSet.obj N.X) N.c : ℚ) := by
    exact_mod_cast congrArg (fun t : ℤ × ℤ × ℤ => t.1) hnum
  have h₂ : (p₁SqNumber (TopCat.toSSet.obj M.X) M.c h.p₁M : ℚ)
      = (p₁SqNumber (TopCat.toSSet.obj N.X) N.c h.p₁N : ℚ) := by
    exact_mod_cast congrArg (fun t : ℤ × ℤ × ℤ => t.2.1) hnum
  have h₃ : (p₂Number (TopCat.toSSet.obj M.X) M.c h.p₂M : ℚ)
      = (p₂Number (TopCat.toSSet.obj N.X) N.c h.p₂N : ℚ) := by
    exact_mod_cast congrArg (fun t : ℤ × ℤ × ℤ => t.2.2) hnum
  unfold numberTriple
  exact Prod.ext h₁ (Prod.ext h₂ h₃)

end SurgeryBordism

/-- **The numerical equivalence supplied by a surgery bordism**: if the Pontryagin classes carried
by the bordism are the classes of the model at both ends, then `M` and `N` have the same three
numbers. -/
theorem sameNumbers_of_pontryaginBordism {M N : ClosedOriented 8} (h : SurgeryBordism M N)
    {p₁M : (cochainC ℤ (TopCat.toSSet.obj M.X)).homology 4}
    {p₂M : (cochainC ℤ (TopCat.toSSet.obj M.X)).homology 8}
    {p₁N : (cochainC ℤ (TopCat.toSSet.obj N.X)).homology 4}
    {p₂N : (cochainC ℤ (TopCat.toSSet.obj N.X)).homology 8}
    (h₁M : h.p₁M = p₁M) (h₂M : h.p₂M = p₂M) (h₁N : h.p₁N = p₁N) (h₂N : h.p₂N = p₂N) :
    SameNumbers M.X N.X M.c N.c p₁M p₁N p₂M p₂N := by
  have hnum := h.numbers_eq
  unfold numberTriple at hnum
  rw [h₁M, h₂M, h₁N, h₂N] at hnum
  exact ⟨Int.cast_injective (α := ℚ) (congrArg (fun t : ℚ × ℚ × ℚ => t.1) hnum),
    Int.cast_injective (α := ℚ) (congrArg (fun t : ℚ × ℚ × ℚ => t.2.1) hnum),
    Int.cast_injective (α := ℚ) (congrArg (fun t : ℚ × ℚ × ℚ => t.2.2) hnum)⟩

end

end Work.Surgery
