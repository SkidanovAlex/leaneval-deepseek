import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Translation
import Submission.Work.MotC2.AffPlace
import Submission.Work.MotC2.InfAux
import Submission.Work.MotC2.PoleT
import Submission.Work.MotC2.infPlace_nonunit_eq_infW_mul
import Submission.Work.MotC2.IsRatPlaceMap
import Submission.Work.MotC2.TransPlaceCoeffs
import Submission.Work.MotC2.DVRMaximal
import Submission.Work.MotC2Cls.Setup
import Submission.Work.MotC2Cls.infPlace_le_of_notMem_genX
import Submission.Work.MotC2.TransXFormula
import Submission.Work.MotC2.TransYFormula
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open WeierstrassCurve.Affine

namespace Work.MotC2

variable {L : Type*} [Field L]

/-- `1/x` regarded as an element of the chart-at-infinity coordinate ring. -/
private noncomputable def infUring (E : WeierstrassCurve L) : infCoordRing E :=
  ⟨infU E, InfAux.infU_mem_infCoordRing E⟩

/-- `y/x²` regarded as an element of the chart-at-infinity coordinate ring. -/
private noncomputable def infWring (E : WeierstrassCurve L) : infCoordRing E :=
  ⟨infW E, InfAux.infW_mem_infCoordRing E⟩

private lemma infUring_val (E : WeierstrassCurve L) : ((infUring E : infCoordRing E) : Func E) = infU E :=
  rfl

private lemma infWring_val (E : WeierstrassCurve L) : ((infWring E : infCoordRing E) : Func E) = infW E :=
  rfl

/-- The ideal `(1/x, y/x²)` of the local ring at infinity. -/
private noncomputable def infPlaceJ (E : WeierstrassCurve L) : Ideal ↥(infPlace E) :=
  Ideal.span {⟨infU E, InfAux.mem_infPlace_of_mem E (infUring E)⟩,
    ⟨infW E, InfAux.mem_infPlace_of_mem E (infWring E)⟩}

private lemma infPlaceJ_u (E : WeierstrassCurve L) :
    (⟨infU E, InfAux.mem_infPlace_of_mem E (infUring E)⟩ : ↥(infPlace E)) ∈ infPlaceJ E :=
  Ideal.subset_span (Set.mem_insert _ _)

private lemma infPlaceJ_w (E : WeierstrassCurve L) :
    (⟨infW E, InfAux.mem_infPlace_of_mem E (infWring E)⟩ : ↥(infPlace E)) ∈ infPlaceJ E :=
  Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

private lemma infCoordRing_smul_eq_mul' (E : WeierstrassCurve L) (a : infCoordRing E) (x : Func E) :
    a • x = (a : Func E) * x := by
  rw [Subalgebra.smul_def, Algebra.smul_def]
  simp

/-- The elements of the submodule `infIdeal E ⊆ L(E)` lie in the local ring `infPlace E`. -/
private lemma infIdeal_subset_infPlace (E : WeierstrassCurve L) :
    (infIdeal E : Set (Func E)) ⊆ (infPlace E : Set (Func E)) := by
  rw [infIdeal]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact InfAux.mem_infPlace_of_mem E (infUring E)
      · exact InfAux.mem_infPlace_of_mem E (infWring E)
  | zero => exact (infPlace E).zero_mem
  | add y z hy hz ihy ihz => exact (infPlace E).add_mem ihy ihz
  | smul a y hy ihy =>
      rw [infCoordRing_smul_eq_mul' E a y]
      exact (infPlace E).mul_mem (InfAux.mem_infPlace_of_mem E a) ihy

/-- The ideal `(1/x, y/x²) ⊆ infPlace E` contains the image of the submodule `infIdeal E`. -/
private lemma infIdeal_le_infPlaceJ (E : WeierstrassCurve L) {x : Func E} (hx : x ∈ infIdeal E) :
    (⟨x, infIdeal_subset_infPlace E hx⟩ : ↥(infPlace E)) ∈ infPlaceJ E := by
  have hx' : x ∈ infIdeal E := hx
  rw [infIdeal, Submodule.mem_span_pair] at hx'
  obtain ⟨a, b, hab⟩ := hx'
  have h1 : (⟨x, infIdeal_subset_infPlace E hx⟩ : ↥(infPlace E)) =
      (⟨a, InfAux.mem_infPlace_of_mem E a⟩ : ↥(infPlace E)) *
          (⟨infU E, InfAux.mem_infPlace_of_mem E (infUring E)⟩ : ↥(infPlace E)) +
        (⟨b, InfAux.mem_infPlace_of_mem E b⟩ : ↥(infPlace E)) *
          (⟨infW E, InfAux.mem_infPlace_of_mem E (infWring E)⟩ : ↥(infPlace E)) := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add]
    rw [← hab]
    rw [infCoordRing_smul_eq_mul' E a (infU E), infCoordRing_smul_eq_mul' E b (infW E)]
  rw [h1]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (infPlaceJ_u E))
    (Ideal.mul_mem_left _ _ (infPlaceJ_w E))

/-- `1 ∉ (1/x, y/x²)` in the local ring at infinity. -/
private lemma one_notMem_infPlaceJ (E : WeierstrassCurve L) :
    (1 : ↥(infPlace E)) ∉ infPlaceJ E := by
  intro hmem
  rw [infPlaceJ, Ideal.mem_span_pair] at hmem
  obtain ⟨xu, xw, hx⟩ := hmem
  have hxK : (xu : Func E) * infU E + (xw : Func E) * infW E = 1 := by
    have h := congrArg (fun y : ↥(infPlace E) => (y : Func E)) hx
    simpa using h
  obtain ⟨A, B, hB, hAB⟩ := (InfAux.infPlace_mem_iff E (xu : Func E)).mp xu.2
  obtain ⟨C, D, hD, hCD⟩ := (InfAux.infPlace_mem_iff E (xw : Func E)).mp xw.2
  have hAB' : (xu : Func E) * (B : Func E) = (A : Func E) := hAB
  have hCD' : (xw : Func E) * (D : Func E) = (C : Func E) := hCD
  have hprime : (InfAux.infIdealR E).IsPrime := InfAux.instIsPrimeInfIdealR E
  have hBDnot : (B * D : infCoordRing E) ∉ InfAux.infIdealR E := fun h =>
    (hprime.mem_or_mem h).elim hB hD
  have hBD : ((B * D : infCoordRing E) : Func E) ∈ infIdeal E := by
    have key : ((B * D : infCoordRing E) : Func E) =
        ((A * D : infCoordRing E) : Func E) * infU E +
          ((C * B : infCoordRing E) : Func E) * infW E := by
      push_cast
      rw [← hAB', ← hCD']
      linear_combination (norm := first | refl_ring1 | ring1) (-((B : Func E) * (D : Func E))) * hxK
    rw [key]
    refine Submodule.add_mem _ ?_ ?_
    · have h : (⟨A * D, mul_mem A.2 D.2⟩ : infCoordRing E) • infU E ∈ infIdeal E :=
        Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      rwa [infCoordRing_smul_eq_mul' E ⟨A * D, mul_mem A.2 D.2⟩ (infU E)] at h
    · have h : (⟨C * B, mul_mem C.2 B.2⟩ : infCoordRing E) • infW E ∈ infIdeal E :=
        Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      rwa [infCoordRing_smul_eq_mul' E ⟨C * B, mul_mem C.2 B.2⟩ (infW E)] at h
  exact hBDnot ((InfAux.mem_infIdealR_iff E (B * D)).mp hBD)

/-! ## The chart element `1 - a·u` -/

private lemma one_sub_mul_infU_mem_infCoordRing (E : WeierstrassCurve L) (a : L) :
    (1 - algebraMap L (Func E) a * infU E) ∈ infCoordRing E :=
  Subalgebra.sub_mem _ (Subalgebra.one_mem _)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) (InfAux.infU_mem_infCoordRing E))

private lemma one_sub_mul_infU_notMem_infIdealR (E : WeierstrassCurve L) (a : L) :
    (⟨1 - algebraMap L (Func E) a * infU E, one_sub_mul_infU_mem_infCoordRing E a⟩ :
      infCoordRing E) ∉ InfAux.infIdealR E := by
  intro hmem
  have hone : (1 : infCoordRing E) ∈ InfAux.infIdealR E := by
    have hsub : (1 : infCoordRing E) -
        (⟨1 - algebraMap L (Func E) a * infU E, one_sub_mul_infU_mem_infCoordRing E a⟩ :
          infCoordRing E) ∈ InfAux.infIdealR E := by
      have heq : (1 : infCoordRing E) -
          (⟨1 - algebraMap L (Func E) a * infU E, one_sub_mul_infU_mem_infCoordRing E a⟩ :
            infCoordRing E) =
          algebraMap L (infCoordRing E) a * infUring E := by
        apply Subtype.ext
        simp only [Subalgebra.coe_sub, Subalgebra.coe_one, Subalgebra.coe_mul,
          Subalgebra.coe_algebraMap]
        rw [infUring_val]
        first | refl_ring1 | ring
      rw [heq]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))
    rw [show (1 : infCoordRing E) = (1 : infCoordRing E) -
        (⟨1 - algebraMap L (Func E) a * infU E, one_sub_mul_infU_mem_infCoordRing E a⟩ :
          infCoordRing E) +
        (⟨1 - algebraMap L (Func E) a * infU E, one_sub_mul_infU_mem_infCoordRing E a⟩ :
          infCoordRing E) by ring]
    exact Ideal.add_mem _ hsub hmem
  exact InfAux.one_notMem_infIdealR E hone

private lemma inv_one_sub_mul_infU_mem_infPlace (E : WeierstrassCurve L) (a : L) :
    (1 - algebraMap L (Func E) a * infU E)⁻¹ ∈ infPlace E :=
  InfAux.inv_mem_infPlace_of_notMem E (one_sub_mul_infU_notMem_infIdealR E a)

private lemma one_sub_mul_infU_ne_zero (E : WeierstrassCurve L) (a : L) :
    1 - algebraMap L (Func E) a * infU E ≠ 0 := by
  intro h0
  refine one_sub_mul_infU_notMem_infIdealR E a ?_
  rw [show (⟨1 - algebraMap L (Func E) a * infU E,
      one_sub_mul_infU_mem_infCoordRing E a⟩ : infCoordRing E) = 0 from Subtype.ext h0]
  exact Ideal.zero_mem _

/-! ## The two explicit formulae, in the form needed below -/

private lemma transX_sigma_mem_infIdeal (E : WeierstrassCurve L) (a b : L) :
    algebraMap L (Func E) (lamCoeff E a b) * infU E +
        algebraMap L (Func E) (kapCoeff E a b) * infU E ^ 2 -
        algebraMap L (Func E) (muCoeff E a b) * infW E ∈ infIdeal E := by
  rw [infIdeal, Submodule.mem_span_pair]
  refine ⟨(algebraMap L (infCoordRing E) (lamCoeff E a b) +
      algebraMap L (infCoordRing E) (kapCoeff E a b) * infUring E : infCoordRing E),
    (-algebraMap L (infCoordRing E) (muCoeff E a b) : infCoordRing E), ?_⟩
  rw [infCoordRing_smul_eq_mul' E _ (infU E), infCoordRing_smul_eq_mul' E _ (infW E)]
  simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_neg,
    Subalgebra.coe_algebraMap, infUring_val]
  first | refl_ring1 | ring

private lemma transY_sigma_mem_infIdeal (E : WeierstrassCurve L) (a b : L) :
    algebraMap L (Func E)
        (3 * a * muCoeff E a b - E.a₁ * lamCoeff E a b + muCoeff E a b * E.a₂) * infU E
      + algebraMap L (Func E)
        (b * lamCoeff E a b + muCoeff E a b * E.a₄ + E.a₁ * a * lamCoeff E a b
          - E.a₁ * kapCoeff E a b - 3 * a ^ 2 * muCoeff E a b) * infU E ^ 2
      + algebraMap L (Func E)
        (muCoeff E a b * E.a₆ + b * kapCoeff E a b + E.a₁ * a * kapCoeff E a b
          + a ^ 3 * muCoeff E a b) * infU E ^ 3
      - algebraMap L (Func E) (lamCoeff E a b) * infW E
      - algebraMap L (Func E)
        (kapCoeff E a b + muCoeff E a b * E.a₃ + muCoeff E a b * b
          + E.a₁ * a * muCoeff E a b) * infU E * infW E ∈ infIdeal E := by
  rw [infIdeal, Submodule.mem_span_pair]
  refine ⟨(algebraMap L (infCoordRing E)
        (3 * a * muCoeff E a b - E.a₁ * lamCoeff E a b + muCoeff E a b * E.a₂)
      + algebraMap L (infCoordRing E)
        (b * lamCoeff E a b + muCoeff E a b * E.a₄ + E.a₁ * a * lamCoeff E a b
          - E.a₁ * kapCoeff E a b - 3 * a ^ 2 * muCoeff E a b) * infUring E
      + algebraMap L (infCoordRing E)
        (muCoeff E a b * E.a₆ + b * kapCoeff E a b + E.a₁ * a * kapCoeff E a b
          + a ^ 3 * muCoeff E a b) * infUring E ^ 2
      - algebraMap L (infCoordRing E)
        (kapCoeff E a b + muCoeff E a b * E.a₃ + muCoeff E a b * b
          + E.a₁ * a * muCoeff E a b) * infWring E : infCoordRing E),
    (-algebraMap L (infCoordRing E) (lamCoeff E a b) : infCoordRing E), ?_⟩
  rw [infCoordRing_smul_eq_mul' E _ (infU E), infCoordRing_smul_eq_mul' E _ (infW E)]
  simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_neg,
    Subalgebra.coe_pow, Subalgebra.coe_algebraMap, infUring_val, infWring_val]
  first | refl_ring1 | ring

/-! ## The translated coordinates lie in the local ring at infinity -/

private lemma transX_sub_mem_infPlace (E : WeierstrassCurve L) [E.IsElliptic] [DecidableEq L]
    (a b : L) (h : Nonsingular E a b) :
    (transX E (Point.some a b h) - algebraMap L (Func E) a) ∈ infPlace E := by
  have hformula := TransXFormula L E a b h
  have hsq : ((1 - algebraMap L (Func E) a * infU E) ^ 2)⁻¹ ∈ infPlace E := by
    rw [← inv_pow]
    exact pow_mem (inv_one_sub_mul_infU_mem_infPlace E a) 2
  have hsigma : algebraMap L (Func E) (lamCoeff E a b) * infU E +
      algebraMap L (Func E) (kapCoeff E a b) * infU E ^ 2 -
      algebraMap L (Func E) (muCoeff E a b) * infW E ∈ infPlace E :=
    infIdeal_subset_infPlace E (transX_sigma_mem_infIdeal E a b)
  have hEq : transX E (Point.some a b h) - algebraMap L (Func E) a =
      (algebraMap L (Func E) (lamCoeff E a b) * infU E +
        algebraMap L (Func E) (kapCoeff E a b) * infU E ^ 2 -
        algebraMap L (Func E) (muCoeff E a b) * infW E) *
        ((1 - algebraMap L (Func E) a * infU E) ^ 2)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero 2 (one_sub_mul_infU_ne_zero E a))]
    exact hformula
  rw [hEq]
  exact mul_mem hsigma hsq

private lemma transY_sub_mem_infPlace (E : WeierstrassCurve L) [E.IsElliptic] [DecidableEq L]
    (a b : L) (h : Nonsingular E a b) :
    (transY E (Point.some a b h) - algebraMap L (Func E) b) ∈ infPlace E := by
  have hformula := TransYFormula L E a b h
  have hcube : ((1 - algebraMap L (Func E) a * infU E) ^ 3)⁻¹ ∈ infPlace E := by
    rw [← inv_pow]
    exact pow_mem (inv_one_sub_mul_infU_mem_infPlace E a) 3
  have hsigma : algebraMap L (Func E)
        (3 * a * muCoeff E a b - E.a₁ * lamCoeff E a b + muCoeff E a b * E.a₂) * infU E
      + algebraMap L (Func E)
        (b * lamCoeff E a b + muCoeff E a b * E.a₄ + E.a₁ * a * lamCoeff E a b
          - E.a₁ * kapCoeff E a b - 3 * a ^ 2 * muCoeff E a b) * infU E ^ 2
      + algebraMap L (Func E)
        (muCoeff E a b * E.a₆ + b * kapCoeff E a b + E.a₁ * a * kapCoeff E a b
          + a ^ 3 * muCoeff E a b) * infU E ^ 3
      - algebraMap L (Func E) (lamCoeff E a b) * infW E
      - algebraMap L (Func E)
        (kapCoeff E a b + muCoeff E a b * E.a₃ + muCoeff E a b * b
          + E.a₁ * a * muCoeff E a b) * infU E * infW E ∈ infPlace E :=
    infIdeal_subset_infPlace E (transY_sigma_mem_infIdeal E a b)
  have hEq : transY E (Point.some a b h) - algebraMap L (Func E) b =
      (algebraMap L (Func E)
          (3 * a * muCoeff E a b - E.a₁ * lamCoeff E a b + muCoeff E a b * E.a₂) * infU E
        + algebraMap L (Func E)
          (b * lamCoeff E a b + muCoeff E a b * E.a₄ + E.a₁ * a * lamCoeff E a b
            - E.a₁ * kapCoeff E a b - 3 * a ^ 2 * muCoeff E a b) * infU E ^ 2
        + algebraMap L (Func E)
          (muCoeff E a b * E.a₆ + b * kapCoeff E a b + E.a₁ * a * kapCoeff E a b
            + a ^ 3 * muCoeff E a b) * infU E ^ 3
        - algebraMap L (Func E) (lamCoeff E a b) * infW E
        - algebraMap L (Func E)
          (kapCoeff E a b + muCoeff E a b * E.a₃ + muCoeff E a b * b
            + E.a₁ * a * muCoeff E a b) * infU E * infW E) *
        ((1 - algebraMap L (Func E) a * infU E) ^ 3)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero 3 (one_sub_mul_infU_ne_zero E a))]
    exact hformula
  rw [hEq]
  exact mul_mem hsigma hcube

private lemma transX_mem_infPlace (E : WeierstrassCurve L) [E.IsElliptic] [DecidableEq L]
    (a b : L) (h : Nonsingular E a b) : transX E (Point.some a b h) ∈ infPlace E := by
  have hsub := transX_sub_mem_infPlace E a b h
  rw [show transX E (Point.some a b h) =
      (transX E (Point.some a b h) - algebraMap L (Func E) a) + algebraMap L (Func E) a by ring]
  exact add_mem hsub (Subalgebra.algebraMap_mem _ _)

private lemma transY_mem_infPlace (E : WeierstrassCurve L) [E.IsElliptic] [DecidableEq L]
    (a b : L) (h : Nonsingular E a b) : transY E (Point.some a b h) ∈ infPlace E := by
  have hsub := transY_sub_mem_infPlace E a b h
  rw [show transY E (Point.some a b h) =
      (transY E (Point.some a b h) - algebraMap L (Func E) b) + algebraMap L (Func E) b by ring]
  exact add_mem hsub (Subalgebra.algebraMap_mem _ _)

private lemma infPlaceJ_mul_mem (E : WeierstrassCurve L) {x : Func E} (hx : x ∈ infIdeal E)
    {y : Func E} (hy : y ∈ infPlace E) :
    (⟨x * y, mul_mem (infIdeal_subset_infPlace E hx) hy⟩ : ↥(infPlace E)) ∈ infPlaceJ E := by
  have hxJ : (⟨x, infIdeal_subset_infPlace E hx⟩ : ↥(infPlace E)) ∈ infPlaceJ E :=
    infIdeal_le_infPlaceJ E hx
  have h := Ideal.mul_mem_left (infPlaceJ E) (⟨y, hy⟩ : ↥(infPlace E)) hxJ
  rwa [show (⟨y, hy⟩ : ↥(infPlace E)) * (⟨x, infIdeal_subset_infPlace E hx⟩ : ↥(infPlace E)) =
      (⟨x * y, mul_mem (infIdeal_subset_infPlace E hx) hy⟩ : ↥(infPlace E)) from
    Subtype.ext (mul_comm y x)] at h

private lemma transX_sub_mem_infPlaceJ (E : WeierstrassCurve L) [E.IsElliptic] [DecidableEq L]
    (a b : L) (h : Nonsingular E a b) :
    (⟨transX E (Point.some a b h) - algebraMap L (Func E) a,
        transX_sub_mem_infPlace E a b h⟩ : ↥(infPlace E)) ∈ infPlaceJ E := by
  have hformula := TransXFormula L E a b h
  have hsigma := transX_sigma_mem_infIdeal E a b
  have hsq : ((1 - algebraMap L (Func E) a * infU E) ^ 2)⁻¹ ∈ infPlace E := by
    rw [← inv_pow]
    exact pow_mem (inv_one_sub_mul_infU_mem_infPlace E a) 2
  have hEq : transX E (Point.some a b h) - algebraMap L (Func E) a =
      (algebraMap L (Func E) (lamCoeff E a b) * infU E +
        algebraMap L (Func E) (kapCoeff E a b) * infU E ^ 2 -
        algebraMap L (Func E) (muCoeff E a b) * infW E) *
        ((1 - algebraMap L (Func E) a * infU E) ^ 2)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero 2 (one_sub_mul_infU_ne_zero E a))]
    exact hformula
  rw [show (⟨transX E (Point.some a b h) - algebraMap L (Func E) a,
      transX_sub_mem_infPlace E a b h⟩ : ↥(infPlace E)) =
      (⟨algebraMap L (Func E) (lamCoeff E a b) * infU E +
          algebraMap L (Func E) (kapCoeff E a b) * infU E ^ 2 -
          algebraMap L (Func E) (muCoeff E a b) * infW E,
        infIdeal_subset_infPlace E hsigma⟩ : ↥(infPlace E)) *
      ⟨((1 - algebraMap L (Func E) a * infU E) ^ 2)⁻¹, hsq⟩ from Subtype.ext hEq]
  exact infPlaceJ_mul_mem E hsigma hsq

private lemma transY_sub_mem_infPlaceJ (E : WeierstrassCurve L) [E.IsElliptic] [DecidableEq L]
    (a b : L) (h : Nonsingular E a b) :
    (⟨transY E (Point.some a b h) - algebraMap L (Func E) b,
        transY_sub_mem_infPlace E a b h⟩ : ↥(infPlace E)) ∈ infPlaceJ E := by
  have hformula := TransYFormula L E a b h
  have hsigma := transY_sigma_mem_infIdeal E a b
  have hcube : ((1 - algebraMap L (Func E) a * infU E) ^ 3)⁻¹ ∈ infPlace E := by
    rw [← inv_pow]
    exact pow_mem (inv_one_sub_mul_infU_mem_infPlace E a) 3
  have hEq : transY E (Point.some a b h) - algebraMap L (Func E) b =
      (algebraMap L (Func E)
          (3 * a * muCoeff E a b - E.a₁ * lamCoeff E a b + muCoeff E a b * E.a₂) * infU E
        + algebraMap L (Func E)
          (b * lamCoeff E a b + muCoeff E a b * E.a₄ + E.a₁ * a * lamCoeff E a b
            - E.a₁ * kapCoeff E a b - 3 * a ^ 2 * muCoeff E a b) * infU E ^ 2
        + algebraMap L (Func E)
          (muCoeff E a b * E.a₆ + b * kapCoeff E a b + E.a₁ * a * kapCoeff E a b
            + a ^ 3 * muCoeff E a b) * infU E ^ 3
        - algebraMap L (Func E) (lamCoeff E a b) * infW E
        - algebraMap L (Func E)
          (kapCoeff E a b + muCoeff E a b * E.a₃ + muCoeff E a b * b
            + E.a₁ * a * muCoeff E a b) * infU E * infW E) *
        ((1 - algebraMap L (Func E) a * infU E) ^ 3)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero 3 (one_sub_mul_infU_ne_zero E a))]
    exact hformula
  rw [show (⟨transY E (Point.some a b h) - algebraMap L (Func E) b,
      transY_sub_mem_infPlace E a b h⟩ : ↥(infPlace E)) =
      (⟨algebraMap L (Func E)
          (3 * a * muCoeff E a b - E.a₁ * lamCoeff E a b + muCoeff E a b * E.a₂) * infU E
        + algebraMap L (Func E)
          (b * lamCoeff E a b + muCoeff E a b * E.a₄ + E.a₁ * a * lamCoeff E a b
            - E.a₁ * kapCoeff E a b - 3 * a ^ 2 * muCoeff E a b) * infU E ^ 2
        + algebraMap L (Func E)
          (muCoeff E a b * E.a₆ + b * kapCoeff E a b + E.a₁ * a * kapCoeff E a b
            + a ^ 3 * muCoeff E a b) * infU E ^ 3
        - algebraMap L (Func E) (lamCoeff E a b) * infW E
        - algebraMap L (Func E)
          (kapCoeff E a b + muCoeff E a b * E.a₃ + muCoeff E a b * b
            + E.a₁ * a * muCoeff E a b) * infU E * infW E,
        infIdeal_subset_infPlace E hsigma⟩ : ↥(infPlace E)) *
      ⟨((1 - algebraMap L (Func E) a * infU E) ^ 3)⁻¹, hcube⟩ from Subtype.ext hEq]
  exact infPlaceJ_mul_mem E hsigma hcube

/-! ## The evaluation map `L[E] → L(E)` at the translated point -/

private noncomputable def psi (E : WeierstrassCurve L) [E.IsElliptic] [DecidableEq L]
    (a b : L) (h : Nonsingular E a b) : Coord E →ₐ[L] Func E :=
  (transAlgEquiv E (Point.some a b h)).toAlgHom.comp
    (IsScalarTower.toAlgHom L (Coord E) (Func E))

private lemma psi_apply (E : WeierstrassCurve L) [E.IsElliptic] [DecidableEq L]
    (a b : L) (h : Nonsingular E a b) (r : Coord E) :
    psi E a b h r = (transAlgEquiv E (Point.some a b h)).toAlgHom
      (algebraMap (Coord E) (Func E) r) := rfl

private lemma psi_coordX (E : WeierstrassCurve L) [E.IsElliptic] [DecidableEq L]
    (a b : L) (h : Nonsingular E a b) :
    psi E a b h (coordX E) = transX E (Point.some a b h) := by
  change (transAlgEquiv E (Point.some a b h)) (genX E) = transX E (Point.some a b h)
  rw [transAlgEquiv_apply]
  exact phi_genX E (Point.some a b h)

private lemma psi_coordY (E : WeierstrassCurve L) [E.IsElliptic] [DecidableEq L]
    (a b : L) (h : Nonsingular E a b) :
    psi E a b h (coordY E) = transY E (Point.some a b h) := by
  change (transAlgEquiv E (Point.some a b h)) (genY E) = transY E (Point.some a b h)
  rw [transAlgEquiv_apply]
  exact phi_genY E (Point.some a b h)

private lemma psi_sub_algebraMap (E : WeierstrassCurve L) [E.IsElliptic] [DecidableEq L]
    (a b : L) (h : Nonsingular E a b) (c : L) :
    psi E a b h (algebraMap L (Coord E) c) = algebraMap L (Func E) c :=
  (psi E a b h).commutes c

private lemma psi_mem_infPlace (E : WeierstrassCurve L) [E.IsElliptic] [DecidableEq L]
    (a b : L) (h : Nonsingular E a b) (r : Coord E) : psi E a b h r ∈ infPlace E := by
  have hle : Subalgebra.map (psi E a b h) ⊤ ≤ infPlace E := by
    rw [show (⊤ : Subalgebra L (Coord E)) = Algebra.adjoin L ({coordX E, coordY E} : Set (Coord E))
        from (adjoin_coordX_coordY E).symm, AlgHom.map_adjoin]
    refine Algebra.adjoin_le_iff.mpr ?_
    rintro _ ⟨y, (rfl | rfl), rfl⟩
    · rw [psi_coordX E a b h]; exact transX_mem_infPlace E a b h
    · rw [psi_coordY E a b h]; exact transY_mem_infPlace E a b h
  exact hle (Subalgebra.mem_map.mpr ⟨r, trivial, rfl⟩)

private lemma psi_mem_infPlaceJ_iff (E : WeierstrassCurve L) [E.IsElliptic] [DecidableEq L]
    (a b : L) (h : Nonsingular E a b) (r : Coord E) :
    (⟨psi E a b h r, psi_mem_infPlace E a b h r⟩ : ↥(infPlace E)) ∈ infPlaceJ E ↔
      r ∈ affPlaceIdeal E a b := by
  haveI : IsNonsingularPoint E a b := ⟨h⟩
  let ΨI : Coord E →ₐ[L] ↥(infPlace E) :=
    (psi E a b h).codRestrict (infPlace E) (psi_mem_infPlace E a b h)
  have hΨI : ∀ r : Coord E,
      ΨI.toRingHom r = (⟨psi E a b h r, psi_mem_infPlace E a b h r⟩ : ↥(infPlace E)) :=
    fun r => rfl
  have hIle : affPlaceIdeal E a b ≤ Ideal.comap ΨI.toRingHom (infPlaceJ E) := by
    rw [affPlaceIdeal,
      show CoordinateRing.XYIdeal E a (Polynomial.C b) =
        Ideal.span {CoordinateRing.XClass E a, CoordinateRing.YClass E (Polynomial.C b)}
        from rfl]
    refine Ideal.span_le.mpr ?_
    rintro x (rfl | rfl)
    · have hx : psi E a b h (CoordinateRing.XClass E a) =
          transX E (Point.some a b h) - algebraMap L (Func E) a := by
        rw [XClass_eq_coordX_sub, map_sub, psi_coordX, psi_sub_algebraMap]
      change (⟨psi E a b h (CoordinateRing.XClass E a),
          psi_mem_infPlace E a b h (CoordinateRing.XClass E a)⟩ : ↥(infPlace E)) ∈ infPlaceJ E
      exact (show (⟨psi E a b h (CoordinateRing.XClass E a),
            psi_mem_infPlace E a b h (CoordinateRing.XClass E a)⟩ : ↥(infPlace E)) =
          (⟨transX E (Point.some a b h) - algebraMap L (Func E) a,
            transX_sub_mem_infPlace E a b h⟩ : ↥(infPlace E)) from Subtype.ext hx) ▸
        transX_sub_mem_infPlaceJ E a b h
    · have hx : psi E a b h (CoordinateRing.YClass E (Polynomial.C b)) =
          transY E (Point.some a b h) - algebraMap L (Func E) b := by
        rw [YClass_eq_coordY_sub, map_sub, psi_coordY, psi_sub_algebraMap]
      change (⟨psi E a b h (CoordinateRing.YClass E (Polynomial.C b)),
          psi_mem_infPlace E a b h (CoordinateRing.YClass E (Polynomial.C b))⟩ :
            ↥(infPlace E)) ∈ infPlaceJ E
      exact (show (⟨psi E a b h (CoordinateRing.YClass E (Polynomial.C b)),
            psi_mem_infPlace E a b h (CoordinateRing.YClass E (Polynomial.C b))⟩ :
              ↥(infPlace E)) =
          (⟨transY E (Point.some a b h) - algebraMap L (Func E) b,
            transY_sub_mem_infPlace E a b h⟩ : ↥(infPlace E)) from Subtype.ext hx) ▸
        transY_sub_mem_infPlaceJ E a b h
  have hne : Ideal.comap ΨI.toRingHom (infPlaceJ E) ≠ ⊤ := by
    intro htop
    have h1 : (1 : Coord E) ∈ Ideal.comap ΨI.toRingHom (infPlaceJ E) := by rw [htop]; trivial
    have h2 : ΨI (1 : Coord E) ∈ infPlaceJ E := Ideal.mem_comap.mp h1
    have h3 : (1 : ↥(infPlace E)) ∈ infPlaceJ E := by
      rwa [show ΨI (1 : Coord E) = 1 from map_one ΨI] at h2
    exact one_notMem_infPlaceJ E h3
  have hcomap : Ideal.comap ΨI.toRingHom (infPlaceJ E) = affPlaceIdeal E a b :=
    (Ideal.IsMaximal.eq_of_le (affPlaceIdeal_isMaximal E a b) hne hIle).symm
  have key : ((⟨psi E a b h r, psi_mem_infPlace E a b h r⟩ : ↥(infPlace E)) ∈ infPlaceJ E) ↔
      (ΨI.toRingHom r ∈ infPlaceJ E) := by
    rw [hΨI]
  rw [key, ← hcomap]
  exact ⟨fun h' => Ideal.mem_comap.mpr h', fun h' => Ideal.mem_comap.mp h'⟩

/-! ## The main computation -/

private lemma map_le_infPlace (E : WeierstrassCurve L) [E.IsElliptic] [DecidableEq L]
    (a b : L) (h : Nonsingular E a b) :
    Subalgebra.map (transAlgEquiv E (Point.some a b h)).toAlgHom (affPlaceAt E a b) ≤
      infPlace E := by
  rw [affPlaceAt_eq_adjoin, AlgHom.map_adjoin]
  refine Algebra.adjoin_le_iff.mpr ?_
  rintro x ⟨y, hy, rfl⟩
  rcases hy with hy | ⟨r, hr, rfl⟩
  · obtain ⟨r, rfl⟩ := hy
    exact psi_mem_infPlace E a b h r
  · have hnot : (⟨psi E a b h r, psi_mem_infPlace E a b h r⟩ : ↥(infPlace E)) ∉ infPlaceJ E :=
      fun hJ => hr ((psi_mem_infPlaceJ_iff E a b h r).mp hJ)
    have hunit : ∃ g : Func E, g ∈ infPlace E ∧ psi E a b h r * g = 1 := by
      by_contra hnon
      obtain ⟨g, hg, heq⟩ := infPlace_nonunit_eq_infW_mul L E (psi E a b h r)
        (psi_mem_infPlace E a b h r) hnon
      have hJ : (⟨psi E a b h r, psi_mem_infPlace E a b h r⟩ : ↥(infPlace E)) ∈ infPlaceJ E := by
        have hmem := Ideal.mul_mem_left (infPlaceJ E) (⟨g, hg⟩ : ↥(infPlace E)) (infPlaceJ_w E)
        rwa [show (⟨g, hg⟩ : ↥(infPlace E)) *
            (⟨infW E, InfAux.mem_infPlace_of_mem E (infWring E)⟩ : ↥(infPlace E)) =
            (⟨psi E a b h r, psi_mem_infPlace E a b h r⟩ : ↥(infPlace E)) from
          Subtype.ext (by rw [Subalgebra.coe_mul]; exact (mul_comm g (infW E)).trans heq.symm)] at hmem
      exact hnot hJ
    obtain ⟨g, hg, hg1⟩ := hunit
    have hge : g = (psi E a b h r)⁻¹ := (inv_eq_of_mul_eq_one_right hg1).symm
    show (transAlgEquiv E (Point.some a b h)).toAlgHom
      ((algebraMap (Coord E) (Func E) r)⁻¹) ∈ infPlace E
    rw [map_inv₀]
    rw [show (transAlgEquiv E (Point.some a b h)).toAlgHom (algebraMap (Coord E) (Func E) r) =
        psi E a b h r from rfl, ← hge]
    exact hg

private lemma genX_notMem_infPlace (E : WeierstrassCurve L) : genX E ∉ infPlace E := by
  intro hx
  obtain ⟨A, B, hB, hAB⟩ := (InfAux.infPlace_mem_iff E (genX E)).mp hx
  have hu : infU E ≠ 0 := inv_ne_zero (genX_ne_zero E)
  have hxinv : genX E = (infU E)⁻¹ := by
    show genX E = ((genX E)⁻¹)⁻¹
    exact (inv_inv (genX E)).symm
  have hA : (B : Func E) = infU E * (A : Func E) := by
    have h : (infU E)⁻¹ * (B : Func E) = (A : Func E) := by
      rw [← hxinv]; exact hAB
    have h2 : infU E * ((infU E)⁻¹ * (B : Func E)) = infU E * (A : Func E) := by rw [h]
    rwa [← mul_assoc, mul_inv_cancel₀ hu, one_mul] at h2
  have hBeq : B = infUring E * A := Subtype.ext (by rw [Subalgebra.coe_mul, infUring_val]; exact hA)
  have hBmem : B ∈ InfAux.infIdealR E := by
    rw [hBeq, InfAux.infIdealR_eq_span, mul_comm]
    refine Ideal.mul_mem_left _ A (Ideal.subset_span ?_)
    rw [Set.mem_insert_iff]
    exact Or.inl (Subtype.ext rfl)
  exact hB hBmem

/-
Statement corrected following both reviewers: with the convention `transAlgEquiv E Q = phi E Q`
satisfying `(phi E Q f) (R) = f (R + Q)` (`phi_genX`, `transX`), one has
`map (phi T) (O_R) = O_{R - T}`, hence the two conjuncts below (translate the place at `P` to the
point at infinity, and back).

Route.  Both are the same computation, done on the generators of `affPlaceAt E a b` respectively of
`infPlace E`:
* `affPlaceAt E a b` is generated over `L` by the images of `Coord E` and the inverses of the
  elements outside `XYIdeal E a (C b)` (`AffPlace`); `phi E Q` fixes `L` and sends `Coord E` into
  itself hmm -- actually it sends `genX E ↦ transX E Q`, `genY E ↦ transY E Q` (`phi_genX`,
  `phi_genY`), which are the affine coordinates of a translate, so their images are regular at `O`
  exactly when the original functions are regular at `Q`; use `nonsingular_add`/`slope`-formulas or
  directly that a function of `R` is regular at `R = O` iff, after translating, it is regular at
  `R + Q = Q`.
* The reverse direction follows with `transAlgEquiv_add` and `transAlgEquiv E (0) = 1`
  (`transAlgEquiv_zero`, `Point.add_neg_cancel`), or by the same computation with `Q` replaced by
  `-Q`.
Remember `Point.neg_some` for the coordinates of `- (some a b h)`.
-/
theorem TransPlace (L : Type*) [Field L] [DecidableEq L] (E : WeierstrassCurve L) [E.IsElliptic]
    (a b : L) (h : WeierstrassCurve.Affine.Nonsingular E a b) :
    Subalgebra.map
        (Work.MotC2.transAlgEquiv E (WeierstrassCurve.Affine.Point.some a b h)).toAlgHom
        (Work.MotC2.affPlaceAt E a b) = Work.MotC2.infPlace E ∧
      Subalgebra.map
        (Work.MotC2.transAlgEquiv E
          (- WeierstrassCurve.Affine.Point.some a b h)).toAlgHom
        (Work.MotC2.infPlace E) = Work.MotC2.affPlaceAt E a b := by
  have hmain : Subalgebra.map
      (transAlgEquiv E (Point.some a b h)).toAlgHom (affPlaceAt E a b) = infPlace E := by
    refine le_antisymm (map_le_infPlace E a b h) ?_
    have hxnot : genX E ∉ Subalgebra.map
        (transAlgEquiv E (Point.some a b h)).toAlgHom (affPlaceAt E a b) := by
      intro hx
      exact genX_notMem_infPlace E (map_le_infPlace E a b h hx)
    have hS : IsRatPlace E (Subalgebra.map
        (transAlgEquiv E (Point.some a b h)).toAlgHom (affPlaceAt E a b)) :=
      IsRatPlaceMap L E (transAlgEquiv E (Point.some a b h)) (affPlaceAt E a b)
        (AffPlace L E a b h).1
    exact MotC2Cls.infPlace_le_of_notMem_genX E _ hS hxnot
  refine ⟨hmain, ?_⟩
  have hcomp : (transAlgEquiv E (- Point.some a b h)).toAlgHom.comp
      (transAlgEquiv E (Point.some a b h)).toAlgHom = AlgHom.id L (Func E) := by
    have h3 := transAlgEquiv_add E (- Point.some a b h) (Point.some a b h)
    rw [neg_add_cancel, transAlgEquiv_zero] at h3
    refine AlgHom.ext fun x => ?_
    change ((transAlgEquiv E (- Point.some a b h)) *
      (transAlgEquiv E (Point.some a b h))) x = x
    rw [← h3]
    rfl
  have h2 := congrArg (Subalgebra.map (transAlgEquiv E (- Point.some a b h)).toAlgHom) hmain
  rw [Subalgebra.map_map, hcomp, Subalgebra.map_id] at h2
  exact h2.symm

end Work.MotC2
