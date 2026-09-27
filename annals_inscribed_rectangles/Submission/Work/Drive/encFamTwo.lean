import Mathlib
import Submission.Work.Drive.encodedFamily
import Submission.Work.Drive.TParity.Basic

/-!
# The corrected ends-clause family (Repair A of `ENCODED_FAMILY_STATUS.md` §7.1) and the
# frozen-block defect (`ENCODED_GENERIC_DEAD.md`)

`Work.Drive.exists_homotopy_meet3Hyp_encoded` (`Drive/encodedGeneric.lean`, lead's §2.1) was planned to
be proved by running the localised parametric Sard (`Work.Drive.localSard_family_in_open`) on a family
of *reparametrised* encoded triples.  Two defects were found for the family `Work.Drive.encShearFam`:

* **Defect A** (`ENCODED_FAMILY_STATUS.md` §7.1): the two plane blocks share a single level-twist
  parameter, so the second and third level coordinates of the parameter derivative of `chartDiff3`
  are equal at a meet and the image lands in a hyperplane of `ℝ⁸`.  **Repair A**: give the two plane
  blocks independent twists `r₁`, `r₂`.  That is the family `encFamTwo` of this file, with parameter
  `(p, q₁, q₂, r₁, r₂) ∈ 𝔼⁴ × 𝔼⁴ × 𝔼⁴ × ℝ × ℝ`.
* **Defect B** (`ENCODED_GENERIC_DEAD.md`): *no* family of this shape can satisfy the Sard's richness
  `hrich`, because the block-0 chain is a homotopy with **fixed ends** and therefore has *zero*
  parameter derivative on the two end slices `x 2 ∈ {0,1}`.  This file proves the elementary half of
  that statement (`encShearFam0_eq_of_betaG_eq_zero` and its consequence for `encFamTwo`), and the
  full certificate lives in `Drive/encFamTwoDefect.lean`.

The definitions are those of `Drive/encodedFamily.lean`, with `encShearS` replaced by two independent
twists.  Nothing here changes `encShearFam`: the two families coexist, `encFamTwo` being the one the
Repair-A design proposes.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## 1. The parameter of the corrected family -/

/-- The parameter `(p, q₁, q₂, r₁, r₂)` of the corrected ends-clause family: one class perturbation,
one shear per plane block and two **independent** level twists (Repair A). -/
abbrev EncPar :=
  EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) × ℝ × ℝ

/-- The class-perturbation parameter. -/
def encP (t : EncPar) : EuclideanSpace ℝ (Fin 4) := t.1

/-- The shear parameter of the first plane block. -/
def encQ₁ (t : EncPar) : EuclideanSpace ℝ (Fin 4) := t.2.1

/-- The shear parameter of the second plane block. -/
def encQ₂ (t : EncPar) : EuclideanSpace ℝ (Fin 4) := t.2.2.1

/-- The level-twist parameter of the first plane block. -/
def encR₁ (t : EncPar) : ℝ := t.2.2.2.1

/-- The level-twist parameter of the second plane block. -/
def encR₂ (t : EncPar) : ℝ := t.2.2.2.2

/-- The parameter with all coordinates zero. -/
def encZero : EncPar := ((0 : EuclideanSpace ℝ (Fin 4)), 0, 0, (0 : ℝ), 0)

@[simp] lemma encP_encZero : encP encZero = 0 := rfl
@[simp] lemma encQ₁_encZero : encQ₁ encZero = 0 := rfl
@[simp] lemma encQ₂_encZero : encQ₂ encZero = 0 := rfl
@[simp] lemma encR₁_encZero : encR₁ encZero = 0 := rfl
@[simp] lemma encR₂_encZero : encR₂ encZero = 0 := rfl

/-! ## 2. The family -/

/-- **The corrected family of encoded triples** (Repair A): the class-perturbed homotopy block at the
constant level `c₀`, and the two plane blocks with a shear of the parameter square and an independent
twist of the level. -/
def encFamTwo (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ) (t : EncPar) :
    Fin 3 → EuclideanSpace ℝ (Fin 3) → Projectivization ℝ (Eucl 3) × ℝ :=
  fun k x =>
    if k = 0 then encShearFam0 H c₀ (encP t) x
    else if k = 1 then (A (shear (encQ₁ t) (pt2 (x 0) (x 1))), thetaS (encR₁ t) (x 2))
    else (B (shear (encQ₂ t) (pt2 (x 0) (x 1))), thetaS (encR₂ t) (x 2))

@[simp] lemma encFamTwo_apply_zero (H A B c₀ t) (x : EuclideanSpace ℝ (Fin 3)) :
    encFamTwo H A B c₀ t 0 x = encShearFam0 H c₀ (encP t) x := by
  simp [encFamTwo]

@[simp] lemma encFamTwo_apply_one (H A B c₀ t) (x : EuclideanSpace ℝ (Fin 3)) :
    encFamTwo H A B c₀ t 1 x =
      (A (shear (encQ₁ t) (pt2 (x 0) (x 1))), thetaS (encR₁ t) (x 2)) := by
  simp [encFamTwo]

@[simp] lemma encFamTwo_apply_two (H A B c₀ t) (x : EuclideanSpace ℝ (Fin 3)) :
    encFamTwo H A B c₀ t 2 x =
      (B (shear (encQ₂ t) (pt2 (x 0) (x 1))), thetaS (encR₂ t) (x 2)) := by
  simp [encFamTwo]

/-- **At the zero parameter the family is the encoded triple of `H`.** -/
theorem encFamTwo_zero (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ) :
    encFamTwo H A B c₀ encZero
      = encodedChains (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, pt2 (x 0) (x 1))) A B c₀ := by
  funext k x
  fin_cases k <;>
    simp [encFamTwo, encShearFam0, encodedChains, encZero, encP, encQ₁, encQ₂, encR₁, encR₂]

/-- **The family is seam-invariant** whenever the three constituting maps are.  The two twists act on
the level coordinate `x 2`, which `seamInv` fixes, so the argument is that of
`Work.Drive.encShearFam_seam` with two independent twists. -/
theorem encFamTwo_seam (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ) (t : EncPar)
    (hH : ∀ (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y → H (s, seamInv2 y) = H (s, y))
    (hA : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → A (seamInv2 y) = A y)
    (hB : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → B (seamInv2 y) = B y)
    {k : Fin 3} {x : EuclideanSpace ℝ (Fin 3)} (hx : onSeam x) :
    encFamTwo H A B c₀ t k (seamInv x) = encFamTwo H A B c₀ t k x := by
  have hy : onSeam2 (pt2 (x 0) (x 1)) := hx
  have h2 : (seamInv x) 2 = x 2 := seamInv_apply_two x
  have hpt : seamInv2 (pt2 (x 0) (x 1)) = pt2 (1 - x 0) (1 - x 1) := by
    ext i; fin_cases i <;> simp [pt2, seamInv2]
  have hseam_shear : ∀ (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)),
      onSeam2 y → onSeam2 (shear q y) := by
    intro q y hy'
    rcases hy' with h | h | h | h
    · exact Or.inl (by simp [shear_apply_zero, hb, h])
    · exact Or.inr (Or.inl (by simp [shear_apply_zero, hb, h]))
    · exact Or.inr (Or.inr (Or.inl (by simp [shear_apply_one, hb, h])))
    · exact Or.inr (Or.inr (Or.inr (by simp [shear_apply_one, hb, h])))
  have hH' : H (x 2, pt2 (1 - x 0) (1 - x 1)) = H (x 2, pt2 (x 0) (x 1)) := by
    rw [← hpt, hH (x 2) _ hy]
  have hA' : A (shear (encQ₁ t) (pt2 (1 - x 0) (1 - x 1)))
      = A (shear (encQ₁ t) (pt2 (x 0) (x 1))) := by
    rw [← hpt, shear_seam (encQ₁ t) (hy := hy),
      hA _ (hseam_shear (encQ₁ t) _ hy)]
  have hB' : B (shear (encQ₂ t) (pt2 (1 - x 0) (1 - x 1)))
      = B (shear (encQ₂ t) (pt2 (x 0) (x 1))) := by
    rw [← hpt, shear_seam (encQ₂ t) (hy := hy),
      hB _ (hseam_shear (encQ₂ t) _ hy)]
  fin_cases k <;> simp [encFamTwo, encShearFam0, h2, hpt, hH', hA', hB']

/-! ## 3. The frozen-block defect -/

/-- **The block-0 chain of the family is constant in the class perturbation parameter wherever the
bump `betaG` vanishes.**  Since `betaG s = 0` for `s ∉ (0,1)`, this is the case at *every* point whose
block-0 time coordinate is outside the open unit interval — in particular on the two end slices
`x 2 ∈ {0, 1}`. -/
lemma encShearFam0_eq_of_betaG_eq_zero (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (c₀ : ℝ) {x : EuclideanSpace ℝ (Fin 3)} (hx : betaG (x 2) = 0)
    (p p' : EuclideanSpace ℝ (Fin 4)) :
    encShearFam0 H c₀ p' x = encShearFam0 H c₀ p x := by
  simp [encShearFam0, hx]

/-- **The block-0 chain of `encFamTwo` is independent of the whole parameter** wherever the bump
vanishes at its time coordinate. -/
lemma encFamTwo_block0_eq_of_betaG_eq_zero
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ)
    {y : Amb 8} (hy : betaG ((TParity.bPartC 0 y) 2) = 0) (t t' : EncPar) :
    encFamTwo H A B c₀ t' 0 (TParity.bPartC 0 y)
      = encFamTwo H A B c₀ t 0 (TParity.bPartC 0 y) := by
  rw [encFamTwo_apply_zero, encFamTwo_apply_zero]
  exact encShearFam0_eq_of_betaG_eq_zero H c₀ hy _ _

/-- The same for the original family `encShearFam`: its block `0` is the same object. -/
lemma encShearFam_block0_eq_of_betaG_eq_zero
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ)
    {y : Amb 8} (hy : betaG ((TParity.bPartC 0 y) 2) = 0)
    (t t' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) × ℝ) :
    encShearFam H A B c₀ t' 0 (TParity.bPartC 0 y)
      = encShearFam H A B c₀ t 0 (TParity.bPartC 0 y) := by
  rw [encShearFam_apply_zero, encShearFam_apply_zero]
  exact encShearFam0_eq_of_betaG_eq_zero H c₀ hy _ _

end

end Work.Drive
