/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TwLinkV
import Submission.Work.MotK.KleinTwLink
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A4: the affine charts of the T-twisted Crauder--Katz link

The link lives on the two hyperplanes `H_s = {v₀ = 0}` (source) and `H_t = {w₀ = 0}` (target) of
the Klein `ℙ⁴`, with the affine charts `v₄ = 1`, `w₄ = 1` and coordinates

  `chart3 : Fin 5 → K[x₀,x₁,x₂]`,  `chart3 = ![0, x₀, x₁, x₂, 1]`.

This file provides

* the `K`-rational point `kleinPointT a b h = (1, 0, 1, b/(a·h), 0)` of the twisted quadric
  `{q = 0}` (with `p₀ = 1 ≠ 0`, so that `p ∉ H_s` and the projection `π_p : ℙ⁴ ⤏ H_s` is defined);
* the two dehomogenised divisor polynomials
  `GambT = kleinTwFhom  a b h p chart3`  (source, degree 11, carries `zP`) and
  `FambT = kleinTwGhomV a b h p chart3`  (target, degree 8, carries the `F₂`-class prime);
* the **homogeneity of the link equations** in their vector argument,
  `kleinTwFhom  (λ v) = λ^11 · kleinTwFhom v`,
  `kleinTwGhomV (λ w) = λ^8  · kleinTwGhomV w`,
  which convert the projective (homogeneous) unit conditions of `TwLinkV` into statements about the
  affine charts: for a vector `v` with `v₄ ≠ 0`,
  `kleinTwFhom p v = v₄^11 · GambT (v₁/v₄, …, v₃/v₄)` and similarly for `kleinTwGhomV`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK

variable {R : Type*} [CommRing R]

/-! ## Homogeneity of the link equations in the coordinate vector -/

theorem kleinTwStereo_smul (a b h c : R) (p v : Fin 5 → R) :
    kleinTwStereo a b h p (fun i => c * v i) = fun i => c ^ 2 * kleinTwStereo a b h p v i := by
  funext i
  simp only [kleinTwStereo, kleinTwBilin, kleinTwQ, kleinTwP0, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply]
  first | refl_ring1 | ring

/-- **Homogeneity of the source equation**: `F_hom(p, λv) = λ^11 F_hom(p, v)`. -/
theorem kleinTwFhom_smul (a b h c : R) (p v : Fin 5 → R) :
    kleinTwFhom a b h p (fun i => c * v i) = c ^ 11 * kleinTwFhom a b h p v := by
  rw [kleinTwFhom, kleinTwBilin_smul_right', kleinTwStereo_smul]
  have h := kleinTwS_homog a b h (c ^ 2) (kleinTwStereo a b h p v)
  rw [h, kleinTwFhom]
  first | refl_ring1 | ring

/-- **Homogeneity of the target equation**: `G_hom(p, λw) = λ^8 G_hom(p, w)`. -/
theorem kleinTwGhomV_smul (a b h c : R) (p w : Fin 5 → R) :
    kleinTwGhomV a b h p (fun i => c * w i) = c ^ 8 * kleinTwGhomV a b h p w := by
  have hR := kleinTwR_homog a b h c w
  rw [kleinTwGhomV, hR, kleinTwBilin_smul_right',
    kleinTwSDualV_homog a b h c w, kleinTwGhomV]
  first | refl_ring1 | ring

/-! ## The affine charts -/

variable (K : Type*) [CommRing K]

/-- The affine chart `v₄ = 1` of the hyperplane `H = {v₀ = 0}` of the Klein `ℙ⁴`, with
coordinates `(v₁,v₂,v₃) ↦ (x₀,x₁,x₂)`: `chart3 = ![0, x₀, x₁, x₂, 1]`. -/
noncomputable def chart3 : Fin 5 → MvPolynomial (Fin 3) K :=
  ![0, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 1]

/-- A `K`-rational point of the twisted quadric `{q = 0}` with non-zero first coordinate:
`p = (1, 0, 1, b/(a·h), 0)`.  (It exists as soon as `a·h ≠ 0`, which holds under `D.Good` and
`h ≠ 0`.) -/
def kleinPointT {K : Type*} [Field K] (a b h : K) : Fin 5 → K
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => b / (a * h)
  | 4 => 0

section Affine

variable {K : Type*} [Field K]

/-- The constant point `kleinPointT`, as a vector in the polynomial ring. -/
noncomputable def pRa (a b h : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  fun i => MvPolynomial.C (kleinPointT a b h i)

@[simp] theorem pRa_apply (a b h : K) (i : Fin 5) :
    pRa a b h i = MvPolynomial.C (kleinPointT a b h i) := rfl

/-- The twisted quadric evaluated on constant coordinates. -/
theorem kleinTwQ_C (a b h : K) (p : Fin 5 → K) :
    kleinTwQ (MvPolynomial.C a : MvPolynomial (Fin 3) K) (MvPolynomial.C b) (MvPolynomial.C h)
        (fun i => (MvPolynomial.C (p i) : MvPolynomial (Fin 3) K))
      = MvPolynomial.C (kleinTwQ a b h p) := by
  simp only [kleinTwQ, kleinTwP0, map_mul, map_pow, map_neg, map_add, map_sub]

/-- **`kleinPointT` lies on the twisted quadric.** -/
theorem kleinTwQ_kleinPointT (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    kleinTwQ a b h (kleinPointT a b h) = 0 := by
  simp only [kleinTwQ, kleinTwP0, kleinPointT]
  field_simp
  first | refl_ring1 | ring

/-- The point `p` is a point of the twisted quadric also in the polynomial ring. -/
theorem kleinTwQ_pRa (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    kleinTwQ (MvPolynomial.C a : MvPolynomial (Fin 3) K) (MvPolynomial.C b) (MvPolynomial.C h)
      (pRa a b h) = 0 := by
  rw [show pRa a b h = fun i => (MvPolynomial.C (kleinPointT a b h i) :
      MvPolynomial (Fin 3) K) from rfl, kleinTwQ_C, kleinTwQ_kleinPointT a b h ha hh,
    MvPolynomial.C_0]

/-- **The source divisor of the affine T-twisted link**: `F_hom` dehomogenised to the chart
`{v₀ = 0, v₄ = 1}`, at the rational point `kleinPointT`. -/
noncomputable def GambT (a b h : K) : MvPolynomial (Fin 3) K :=
  kleinTwFhom (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (pRa a b h) (chart3 K)

/-- **The target divisor of the affine T-twisted link**: `G_hom` dehomogenised to the chart
`{w₀ = 0, w₄ = 1}`, at the rational point `kleinPointT`. -/
noncomputable def FambT (a b h : K) : MvPolynomial (Fin 3) K :=
  kleinTwGhomV (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (pRa a b h) (chart3 K)

/-- **The first unit condition of the affine T-twisted link** (the chart-level form of
`kleinTwLinkUnitV`): with `f = kleinTwP ∘ kleinTwStereo`,

  `G_hom (f (chart)) = -s(y)^2 · b(p, chart) · GambT`.

This is the identity `Φ(F) = unit · G` of the certificate, read in the chart ring
`K[x₀,x₁,x₂]`; the remaining bookkeeping — converting the left-hand side into `FambT` evaluated at
the affine coordinates of `f`, the denominator `f₄` being cleared by the homogeneity
`kleinTwGhomV_smul` — is the rest of the A4 step. -/
theorem GambT_unit (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    kleinTwGhomV (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
        (kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (pRa a b h) (chart3 K)))
      = -(kleinTwS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
              (pRa a b h) (chart3 K))) ^ 2
          * kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
              (pRa a b h) (chart3 K)
          * GambT a b h :=
  kleinTwLinkUnitV (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (pRa a b h) (chart3 K) (kleinTwQ_pRa a b h ha hh)

/-- **The second unit condition of the affine T-twisted link** (the chart-level form of
`kleinTwFhom_kleinTwR`): the inverse map is `kleinTwR`, so

  `F_hom (kleinTwR (chart)) = -b(p, R chart)^5 · s'(chart)^2 · FambT`.

The hypothesis is that the inverse map is regular at the chart, `kleinTwR (chart) ₀ ≠ 0` (this is
what I4', hence `kleinTwFhom_kleinTwR`, needs). -/
theorem FambT_unit (a b h : K)
    (hw : kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chart3 K) 0 ≠ 0) :
    kleinTwFhom (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
        (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chart3 K))
      = -(kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
            (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chart3 K))) ^ 5
          * (kleinTwSDualV (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
              (chart3 K)) ^ 2
          * FambT a b h :=
  kleinTwFhom_kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
    (chart3 K)
    (by
      rw [show chart3 K = ![0, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 1]
        from rfl]
      exact kleinTwQ_kleinTwR_of_zero (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (chart3 K) rfl)
    hw

end Affine

end Work.MotK
