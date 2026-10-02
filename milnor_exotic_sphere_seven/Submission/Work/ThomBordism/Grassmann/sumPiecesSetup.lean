import Mathlib
import Submission.Work.ThomBordism.Grassmann.zeroComplementSum
import Submission.Work.Thom.thomClassOf
import Submission.Work.Thom.bijective_proj_zeroComplement_gen
import Submission.Work.LerayHirsch.nonempty_homeo_projSpace_bundleComap_subtype
import Submission.Work.Thom.realification_homeo
import Submission.Work.Thom.coreMorphism
import Submission.Work.Thom.LineGeom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The pieces of the zero complement of a Whitney sum: set-up

This module fixes the vocabulary used by
`Work.ThomBordism.Grassmann.subsingleton_zeroComplementSumPieces`.  For complex vector bundles
`A` (rank `a`) and `C` (rank `b`) over a common base `B` (gluing data with finite index types), it
introduces

* the realifications `sumAR A = realification A`, `sumCR C = realification C`, the sum
  `sumW A C = realification (whitneySum A C)` and the two pieces `pieceFst`, `pieceSnd` of
  `zeroComplement (sumW A C)` (from `Submission/Work/ThomBordism/Grassmann/zeroComplementSum.lean`);

* the pullback `sumZ1c A C = bundleComap C (bundleProj (sumAR A))` of `C` to the total space of the
  realified `A`, its realification `sumZ1 A C`, the restriction `sumZc A C` to the punctured total
  space `sumBaseA A = zeroComplement (sumAR A)`, its realification `sumZ A C`, and the piece
  `sumP A C` of `zeroComplement (sumZ1 A C)` over `sumBaseA A`;

* the five maps of total spaces `sumFstFn`, `sumSndFn` (the two coordinate projections of the sum),
  `sumIncl₁`, `sumIncl₂` (the two coordinate inclusions) and the pair
  `sumPhi`/`sumPsi` identifying the total space of the pullback with the sum;

* the fibre-coordinate functions `sumFibA`, `sumFibC`, `sumFibZ1`, `sumFibW` (needed because the
  fibre `Z.Fiber x` of a gluing-data bundle is only *definitionally* the model fibre, so rewriting
  in the model fibre needs a name of the right type).

All the statements here are elementary; the continuity of the five maps is proved in the companion
modules of the caller.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {a b : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]

/-! ## The bundles -/

/-- The realification of `A`. -/
abbrev sumAR (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁) :
    RealBundle B (EuclideanSpace ℂ (Fin a)) ι₁ :=
  Work.Thom.realification A

/-- The realification of `C`. -/
abbrev sumCR (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    RealBundle B (EuclideanSpace ℂ (Fin b)) ι₂ :=
  Work.Thom.realification C

/-- The Whitney sum `A ⊕ C`. -/
abbrev sumWc (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (a + b))) (ι₁ × ι₂) :=
  Work.Whitney.whitneySum A C

/-- The realification of the Whitney sum `A ⊕ C`. -/
abbrev sumW (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    RealBundle B (EuclideanSpace ℂ (Fin (a + b))) (ι₁ × ι₂) :=
  Work.Thom.realification (sumWc A C)

/-- The punctured total space of the realification of `A`: the base of the third piece. -/
abbrev sumBaseA (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁) : Set (sumAR A).TotalSpace :=
  Work.Thom.zeroComplement (sumAR A)

/-- The punctured total space of the realification of `C`. -/
abbrev sumBaseC (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) : Set (sumCR C).TotalSpace :=
  Work.Thom.zeroComplement (sumCR C)

/-- The pullback of `C` to the whole total space of the realified `A`. -/
abbrev sumZ1c (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    VectorBundleCore ℂ (sumAR A).TotalSpace (EuclideanSpace ℂ (Fin b)) ι₂ :=
  Work.Thom.bundleComap C (Work.Thom.bundleProj (sumAR A))

/-- The realification of `sumZ1c`. -/
abbrev sumZ1 (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    RealBundle (sumAR A).TotalSpace (EuclideanSpace ℂ (Fin b)) ι₂ :=
  Work.Thom.realification (sumZ1c A C)

/-- The pullback of `C` to the punctured total space of the realified `A`. -/
abbrev sumZc (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    VectorBundleCore ℂ ↥(sumBaseA A) (EuclideanSpace ℂ (Fin b)) ι₂ :=
  Work.Thom.bundleComap (sumZ1c A C) (Work.Thom.subtypeMap (sumBaseA A))

/-- The realification of `sumZc`: the rank-`2b` real bundle over `sumBaseA` whose zero complement
is the intersection of the two pieces. -/
abbrev sumZ (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    RealBundle ↥(sumBaseA A) (EuclideanSpace ℂ (Fin b)) ι₂ :=
  Work.Thom.realification (sumZc A C)

/-- The piece of `zeroComplement (sumZ1 A C)` over the punctured first summand. -/
def sumP (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Set ↥(Work.Thom.zeroComplement (sumZ1 A C)) :=
  {x | x.1.proj ∈ sumBaseA A}

/-! ## The fibre coordinates -/

/-- The fibre coordinate of the realified `A`. -/
def sumFibA (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (p : (sumAR A).TotalSpace) : EuclideanSpace ℂ (Fin a) := p.2

/-- The fibre coordinate of the realified `C`. -/
def sumFibC (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (p : (sumCR C).TotalSpace) : EuclideanSpace ℂ (Fin b) := p.2

/-- The fibre coordinate of `sumZ1`. -/
def sumFibZ1 (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (p : (sumZ1c A C).TotalSpace) : EuclideanSpace ℂ (Fin b) := p.2

/-- The fibre coordinate of the realified sum. -/
def sumFibW (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (p : (sumW A C).TotalSpace) : EuclideanSpace ℂ (Fin (a + b)) := p.2

/-- The fibre coordinate of a point of the punctured total space. -/
def sumFibPA (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (q : ↥(sumBaseA A)) : EuclideanSpace ℂ (Fin a) := q.1.2

/-- The fibre coordinate of a point of the punctured total space. -/
def sumFibPC (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (q : ↥(sumBaseC C)) : EuclideanSpace ℂ (Fin b) := q.1.2

@[simp] theorem sumFibA_mk (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (x : B) (v : EuclideanSpace ℂ (Fin a)) :
    sumFibA A (⟨x, v⟩ : (sumAR A).TotalSpace) = v := rfl

@[simp] theorem sumFibC_mk (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (x : B) (v : EuclideanSpace ℂ (Fin b)) :
    sumFibC C (⟨x, v⟩ : (sumCR C).TotalSpace) = v := rfl

@[simp] theorem sumFibW_mk (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (x : B) (v : EuclideanSpace ℂ (Fin (a + b))) :
    sumFibW A C (⟨x, v⟩ : (sumW A C).TotalSpace) = v := rfl

@[simp] theorem sumFibZ1_mk (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (x : (sumAR A).TotalSpace) (v : EuclideanSpace ℂ (Fin b)) :
    sumFibZ1 A C (⟨x, v⟩ : (sumZ1c A C).TotalSpace) = v := rfl

@[simp] theorem sumFibPA_mk (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (q : ↥(sumBaseA A)) : sumFibPA A q = q.1.2 := rfl

/-- The non-vanishing, in the model fibre, of the fibre coordinate of a point of `sumBaseA`. -/
theorem sumFibPA_ne_zero (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (q : ↥(sumBaseA A)) : sumFibPA A q ≠ 0 :=
  (Work.Thom.mem_zeroComplement_mk (Z := sumAR A) q.1.1 q.1.2).mp q.2

/-- The non-vanishing, in the model fibre, of the fibre coordinate of a point of `sumBaseC`. -/
theorem sumFibPC_ne_zero (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (q : ↥(sumBaseC C)) : sumFibPC C q ≠ 0 :=
  (Work.Thom.mem_zeroComplement_mk (Z := sumCR C) q.1.1 q.1.2).mp q.2

/-! ## The five maps -/

/-- The first-coordinate projection of the sum, as a map of total spaces. -/
def sumFstFn (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    (sumW A C).TotalSpace → (sumAR A).TotalSpace :=
  fun p => ⟨p.1, fstAB a b (sumFibW A C p)⟩

/-- The second-coordinate projection of the sum, as a map of total spaces. -/
def sumSndFn (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    (sumW A C).TotalSpace → (sumCR C).TotalSpace :=
  fun p => ⟨p.1, sndAB a b (sumFibW A C p)⟩

/-- The first-coordinate inclusion into the sum, with second coordinate `0`. -/
def sumIncl₁ (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    (sumAR A).TotalSpace → (sumW A C).TotalSpace :=
  fun p => ⟨p.1, Work.Whitney.sumFibreC a b (sumFibA A p, 0)⟩

/-- The second-coordinate inclusion into the sum, with first coordinate `0`. -/
def sumIncl₂ (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    (sumCR C).TotalSpace → (sumW A C).TotalSpace :=
  fun p => ⟨p.1, Work.Whitney.sumFibreC a b (0, sumFibC C p)⟩

/-- The identification of the total space of the pullback with the total space of the sum. -/
def sumPhi (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    (sumZ1c A C).TotalSpace → (sumW A C).TotalSpace :=
  fun p => ⟨p.1.1, Work.Whitney.sumFibreC a b (sumFibA A p.1, sumFibZ1 A C p)⟩

/-- The inverse identification, as a map of total spaces. -/
def sumPsi (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    (sumW A C).TotalSpace → (sumZ1c A C).TotalSpace :=
  fun p => ⟨⟨p.1, fstAB a b (sumFibW A C p)⟩, sndAB a b (sumFibW A C p)⟩

@[simp] theorem sumFstFn_apply (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (p : (sumW A C).TotalSpace) :
    sumFstFn A C p = (⟨p.1, fstAB a b (sumFibW A C p)⟩ : (sumAR A).TotalSpace) := rfl

@[simp] theorem sumSndFn_apply (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (p : (sumW A C).TotalSpace) :
    sumSndFn A C p = (⟨p.1, sndAB a b (sumFibW A C p)⟩ : (sumCR C).TotalSpace) := rfl

@[simp] theorem sumIncl₁_apply (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (p : (sumAR A).TotalSpace) :
    sumIncl₁ A C p =
      (⟨p.1, Work.Whitney.sumFibreC a b (sumFibA A p, 0)⟩ : (sumW A C).TotalSpace) := rfl

@[simp] theorem sumIncl₂_apply (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (p : (sumCR C).TotalSpace) :
    sumIncl₂ A C p =
      (⟨p.1, Work.Whitney.sumFibreC a b (0, sumFibC C p)⟩ : (sumW A C).TotalSpace) := rfl

@[simp] theorem sumPhi_apply (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (p : (sumZ1c A C).TotalSpace) :
    sumPhi A C p =
      (⟨p.1.1, Work.Whitney.sumFibreC a b (sumFibA A p.1, sumFibZ1 A C p)⟩ :
        (sumW A C).TotalSpace) := rfl

@[simp] theorem sumPsi_apply (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (p : (sumW A C).TotalSpace) :
    sumPsi A C p = (⟨⟨p.1, fstAB a b (sumFibW A C p)⟩, sndAB a b (sumFibW A C p)⟩ :
      (sumZ1c A C).TotalSpace) := rfl

theorem sumFstFn_sumIncl₁ (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (p : (sumAR A).TotalSpace) : sumFstFn A C (sumIncl₁ A C p) = p := by
  rw [sumFstFn_apply, sumIncl₁_apply, sumFibW_mk, fstAB_sumFibreC]
  obtain ⟨x, v⟩ := p
  rfl

theorem sumSndFn_sumIncl₂ (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (p : (sumCR C).TotalSpace) : sumSndFn A C (sumIncl₂ A C p) = p := by
  rw [sumSndFn_apply, sumIncl₂_apply, sumFibW_mk, sndAB_sumFibreC]
  obtain ⟨x, v⟩ := p
  rfl

theorem sumFstFn_sumPhi (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (p : (sumZ1c A C).TotalSpace) : sumFstFn A C (sumPhi A C p) = p.1 := by
  rw [sumFstFn_apply, sumPhi_apply, sumFibW_mk, fstAB_sumFibreC]
  rfl

theorem sumSndFn_sumPhi (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (p : (sumZ1c A C).TotalSpace) : sumSndFn A C (sumPhi A C p) = ⟨p.1.1, sumFibZ1 A C p⟩ := by
  rw [sumSndFn_apply, sumPhi_apply, sumFibW_mk, sndAB_sumFibreC]

theorem sumPsi_sumPhi (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (p : (sumZ1c A C).TotalSpace) : sumPsi A C (sumPhi A C p) = p := by
  simp only [sumPsi_apply, sumPhi_apply, sumFibW_mk]
  rw [fstAB_sumFibreC, sndAB_sumFibreC]
  obtain ⟨x, v⟩ := p
  rfl

theorem sumPhi_sumPsi (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (p : (sumW A C).TotalSpace) : sumPhi A C (sumPsi A C p) = p := by
  simp only [sumPhi_apply, sumPsi_apply]
  simp only [sumFibA, sumFibZ1]
  rw [sumFibreC_fstAB_sndAB]
  obtain ⟨x, v⟩ := p
  rfl


/-! ## The piece maps of the first and the second summand -/

/-- The projection of the first piece `pieceFst` onto the punctured total space of `A`. -/
def sumFstPiece (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    ↥(pieceFst A C) → ↥(sumBaseA A) :=
  fun p => ⟨⟨p.1.1.1, fstAB a b p.1.1.2⟩, p.2⟩

/-- The inclusion of the punctured total space of `A` into the first piece, with second
coordinate `0`. -/
def sumFstSec (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    ↥(sumBaseA A) → ↥(pieceFst A C) :=
  fun q => ⟨⟨⟨q.1.1, Work.Whitney.sumFibreC a b (sumFibPA A q, 0)⟩,
      by
        show Work.Whitney.sumFibreC a b (sumFibPA A q, 0) ≠ 0
        intro h
        exact sumFibPA_ne_zero A q ((sumFibreC_eq_zero_iff a b).mp h).1⟩,
    by
      show fstAB a b (Work.Whitney.sumFibreC a b (sumFibPA A q, 0)) ≠ 0
      rw [fstAB_sumFibreC]
      exact sumFibPA_ne_zero A q⟩

/-- The projection of the second piece `pieceSnd` onto the punctured total space of `C`. -/
def sumSndPiece (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    ↥(pieceSnd A C) → ↥(sumBaseC C) :=
  fun p => ⟨⟨p.1.1.1, sndAB a b p.1.1.2⟩, p.2⟩

/-- The inclusion of the punctured total space of `C` into the second piece, with first
coordinate `0`. -/
def sumSndSec (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    ↥(sumBaseC C) → ↥(pieceSnd A C) :=
  fun q => ⟨⟨⟨q.1.1, Work.Whitney.sumFibreC a b (0, sumFibPC C q)⟩,
      by
        show Work.Whitney.sumFibreC a b (0, sumFibPC C q) ≠ 0
        intro h
        exact sumFibPC_ne_zero C q ((sumFibreC_eq_zero_iff a b).mp h).2⟩,
    by
      show sndAB a b (Work.Whitney.sumFibreC a b (0, sumFibPC C q)) ≠ 0
      rw [sndAB_sumFibreC]
      exact sumFibPC_ne_zero C q⟩

/-- The projection of the first piece is a left inverse of the first-section inclusion. -/
theorem sumFstPiece_sumFstSec (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (q : ↥(sumBaseA A)) : sumFstPiece A C (sumFstSec A C q) = q := by
  apply Subtype.ext
  show sumFstFn A C (sumIncl₁ A C q.1) = q.1
  exact sumFstFn_sumIncl₁ A C q.1

/-- The projection of the second piece is a left inverse of the second-section inclusion. -/
theorem sumSndPiece_sumSndSec (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (q : ↥(sumBaseC C)) : sumSndPiece A C (sumSndSec A C q) = q := by
  apply Subtype.ext
  show sumSndFn A C (sumIncl₂ A C q.1) = q.1
  exact sumSndFn_sumIncl₂ A C q.1

end

end Work.ThomBordism.Grassmann
