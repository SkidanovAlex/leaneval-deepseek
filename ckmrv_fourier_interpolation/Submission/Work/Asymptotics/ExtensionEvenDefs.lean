/-
# The finite "second-basis" reductions of CKMRV Proposition 3.2(1) at even weight

This file collects the definitions and elementary algebraic lemmas underlying the finite checks
of the propagation argument (CKMRV, proof of Proposition 3.2(1)), together with the interface
(`Work.Asymptotics.CarryOk`) that the case-by-case checks are stated against.

## The finite check

`rowDiffP x i = M'_i x - ∑ j, σ'(x)_{ij} M'_j` is the error vector of the reduction of `M'_i x`
in the second basis `M' = (I, T⁻¹, STS, S, ST⁻¹, TS)`; it lies in the ideal
`𝓘 = (T-I)²R + S(T-I)²R + (z-1)R`.  For the seven neighbours `ν` of `𝓕̄` and each of the six
rows `i`, the check is that `rowDiffP (of ν) i` can be written, **modulo the collapse ideal**
`(z-1)R`, as `(T-I)² a + S(T-I)² b` with `a`, `b` each either `0` or a single group element whose
translate of `O_F` lands in `O` (`SafePair`, `SafePairS`).

## Main definitions

* `Work.Asymptotics.ofOpt` : `Option X → R`, `none ↦ 0`, `some γ ↦ of γ`.
* `Work.Asymptotics.SafeF`, `Work.Asymptotics.SafeThick` : the finitely many group elements
  whose translates of `O_F` are known to lie in `O`.
* `Work.Asymptotics.SafePair`, `Work.Asymptotics.SafePairS` : the compatibility of a carry with
  the propagation hypothesis `Propagates`.
* `Work.Asymptotics.CarryOk` : the algebraic part of the check.
-/
import Mathlib
import Submission.Work.Asymptotics.PropagateMpDefs
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.Asymptotics.carryP_exists
import Submission.Work.Asymptotics.exists_neighbour_nbdh_of_Propagates
import Submission.Work.Asymptotics.defects_of_local_agreement
import Submission.Work.Asymptotics.upperHalfPlane_subset_iUnion_smul_closure_DomainF

noncomputable section

open Work.Kernels Work.Residues
open scoped MatrixGroups

namespace Work.Asymptotics

abbrev X := Matrix.SpecialLinearGroup (Fin 2) ℤ

/-! ## Scalar-multiple normal forms -/

lemma two_smulC (x : R) : (2:ℂ) • x = x + x := by
  rw [Algebra.smul_def, map_ofNat, two_mul]

lemma neg_two_smulC (x : R) : (-2:ℂ) • x = -(x + x) := by
  rw [show (-2:ℂ) = -(2:ℂ) from by norm_num, neg_smul, two_smulC]

lemma neg_one_smulC (x : R) : (-1:ℂ) • x = -x := by
  rw [show (-1:ℂ) = -(1:ℂ) from by norm_num, neg_smul, one_smul]

/-! ## Differences of opposite monomials lie in the collapse ideal -/

lemma single_sub_single_neg_mem (g : X) (c : ℂ) :
    (MonoidAlgebra.single g c - MonoidAlgebra.single (-g) c : R) ∈ augIdeal := by
  have h : (MonoidAlgebra.single (-g) c : R) = Rneg * MonoidAlgebra.single g c := by
    rw [Rneg, MonoidAlgebra.single_mul_single]
    congr 1
    · rw [neg_one_mul]
    · rw [one_mul]
  rw [h]
  have h2 : (MonoidAlgebra.single g c - Rneg * MonoidAlgebra.single g c : R)
      = (1 - Rneg) * MonoidAlgebra.single g c := by noncomm_ring
  rw [h2, show (1 - Rneg : R) = -(Rneg - 1) from by noncomm_ring, neg_mul]
  exact Submodule.neg_mem _ (Rneg_sub_one_mul_mem _)

lemma single_neg_sub_single_mem (g : X) (c : ℂ) :
    (MonoidAlgebra.single (-g) c - MonoidAlgebra.single g c : R) ∈ augIdeal := by
  rw [← neg_sub]
  exact Submodule.neg_mem _ (single_sub_single_neg_mem g c)

/-- `of (-γ) = Rneg * of γ`. -/
lemma of_neg_of (γ : X) :
    (MonoidAlgebra.of ℂ X (-γ) : R) = Rneg * MonoidAlgebra.of ℂ X γ := by
  rw [show (Rneg : R) = MonoidAlgebra.single (-1 : X) 1 from rfl]
  rw [show (MonoidAlgebra.of ℂ X γ : R) = MonoidAlgebra.single γ 1 from by
    rw [MonoidAlgebra.of_apply]]
  rw [show (MonoidAlgebra.of ℂ X (-γ) : R) = MonoidAlgebra.single (-γ) (1:ℂ) from by
    rw [MonoidAlgebra.of_apply]]
  rw [MonoidAlgebra.single_mul_single]
  congr 1
  · rw [neg_mul, one_mul]
  · rw [one_mul]

lemma of_sub_of_neg_mem_augIdeal (g : X) :
    (MonoidAlgebra.of ℂ X g - MonoidAlgebra.of ℂ X (-g) : R) ∈ augIdeal := by
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.of_apply]
  exact single_sub_single_neg_mem g 1

/-! ## The expansion of `(T-I)²` and `S(T-I)²` on monomials -/

lemma T2_mul_single (α : X) (c : ℂ) :
    (R_T - 1)^2 * MonoidAlgebra.single α c =
      MonoidAlgebra.single (ModularGroup.T * ModularGroup.T * α) c
        - MonoidAlgebra.single (ModularGroup.T * α) c
        - MonoidAlgebra.single (ModularGroup.T * α) c
        + MonoidAlgebra.single α c := by
  rw [R_T]
  rw [show (MonoidAlgebra.single ModularGroup.T (1:ℂ) - 1)^2
      = MonoidAlgebra.single ModularGroup.T (1:ℂ) * MonoidAlgebra.single ModularGroup.T (1:ℂ)
        - MonoidAlgebra.single ModularGroup.T (1:ℂ) - MonoidAlgebra.single ModularGroup.T (1:ℂ)
        + 1 from by noncomm_ring]
  rw [add_mul, sub_mul, sub_mul, one_mul, MonoidAlgebra.single_mul_single,
    MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single]
  simp only [one_mul]

lemma RS_T2_mul_single (α : X) (c : ℂ) :
    R_S * (R_T - 1)^2 * MonoidAlgebra.single α c =
      MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * ModularGroup.T * α)) c
        - MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * α)) c
        - MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * α)) c
        + MonoidAlgebra.single (ModularGroup.S * α) c := by
  rw [mul_assoc, T2_mul_single, mul_add, mul_sub, mul_sub, R_S, MonoidAlgebra.single_mul_single,
    MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single]
  simp only [one_mul]

lemma T2_mul_of (α : X) :
    (R_T - 1)^2 * (MonoidAlgebra.of ℂ X α : R) =
      MonoidAlgebra.single (ModularGroup.T * ModularGroup.T * α) 1
        - MonoidAlgebra.single (ModularGroup.T * α) 1
        - MonoidAlgebra.single (ModularGroup.T * α) 1
        + MonoidAlgebra.single α 1 := by
  rw [show (MonoidAlgebra.of ℂ X α : R) = MonoidAlgebra.single α 1 from by
    rw [MonoidAlgebra.of_apply]]
  exact T2_mul_single α 1

lemma RS_T2_mul_of (α : X) :
    R_S * (R_T - 1)^2 * (MonoidAlgebra.of ℂ X α : R) =
      MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * ModularGroup.T * α)) 1
        - MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * α)) 1
        - MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * α)) 1
        + MonoidAlgebra.single (ModularGroup.S * α) 1 := by
  rw [show (MonoidAlgebra.of ℂ X α : R) = MonoidAlgebra.single α 1 from by
    rw [MonoidAlgebra.of_apply]]
  exact RS_T2_mul_single α 1

/-! ## The six `σ_R` values on the neighbours' letters -/

lemma of_T : (MonoidAlgebra.of ℂ X (ModularGroup.T : X) : R) = R_T := by
  rw [MonoidAlgebra.of_apply]

lemma of_S : (MonoidAlgebra.of ℂ X (ModularGroup.S : X) : R) = R_S := by
  rw [MonoidAlgebra.of_apply]

lemma sigmaR_R_Tinv : sigmaR R_Tinv = Work.Modular.sigmaTinv := by
  have h1 : R_Tinv * R_T = (1 : R) := by
    rw [R_Tinv, R_T, MonoidAlgebra.single_mul_single, inv_mul_cancel, mul_one,
      MonoidAlgebra.one_def]
  have h2 : sigmaR R_Tinv * Work.Modular.sigmaT = 1 := by
    rw [← Work.Residues.sigmaR_R_T, ← map_mul, h1, map_one]
  have h3 : sigmaR R_Tinv = (sigmaR R_Tinv * Work.Modular.sigmaT) * Work.Modular.sigmaTinv := by
    rw [mul_assoc, Work.Modular.sigmaT_mul_sigmaTinv, mul_one]
  rw [h3, h2, one_mul]

lemma sigmaR_of_TS : sigmaR (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S))
    = Work.Modular.sigmaT * Work.Modular.sigmaS := by
  rw [show (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S) : R) = R_T * R_S from by
    rw [map_mul, MonoidAlgebra.of_apply, MonoidAlgebra.of_apply]]
  rw [map_mul, Work.Residues.sigmaR_R_T, Work.Residues.sigmaR_R_S]

lemma sigmaR_of_STinv : sigmaR (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T⁻¹))
    = Work.Modular.sigmaS * Work.Modular.sigmaTinv := by
  rw [show (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T⁻¹) : R) = R_S * R_Tinv from by
    rw [map_mul, MonoidAlgebra.of_apply, MonoidAlgebra.of_apply]]
  rw [map_mul, Work.Residues.sigmaR_R_S, sigmaR_R_Tinv]

lemma sigmaR_of_TSTinv :
    sigmaR (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))
    = Work.Modular.sigmaT * Work.Modular.sigmaS * Work.Modular.sigmaTinv := by
  rw [show (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) : R)
      = (R_T * R_S) * R_Tinv from by
    rw [map_mul, map_mul, MonoidAlgebra.of_apply, MonoidAlgebra.of_apply,
      MonoidAlgebra.of_apply]]
  rw [map_mul, map_mul, Work.Residues.sigmaR_R_T, Work.Residues.sigmaR_R_S, sigmaR_R_Tinv]

/-! ## The carry interface -/

/-- `none ↦ 0`, `some γ ↦ of γ`: the two possible shapes of a carry. -/
def ofOpt : Option X → R
  | none => 0
  | some γ => MonoidAlgebra.of ℂ X γ

@[simp] lemma ofOpt_none : ofOpt (none : Option X) = 0 := rfl
@[simp] lemma ofOpt_some (γ : X) : ofOpt (some γ) = MonoidAlgebra.of ℂ X γ := rfl

/-- The group elements whose translates of `O_F` are known to lie in `O`: the six basis
elements `M'_j` and the single point `M'_i ν`. -/
def SafeF (ν : X) (i : Fin 6) : Finset X :=
  insert (Mp i * ν) (Finset.univ.image Mp)

/-- `SafeF` together with its negatives: the negative of a group element acts on `ℍ` by the same
Möbius transformation, and at even weight it acts by the same slash operator. -/
def SafeThick (ν : X) (i : Fin 6) : Finset X :=
  Finset.univ.image Mp ∪ (Finset.univ.image Mp).image (fun δ => -δ)
    ∪ {Mp i * ν} ∪ {-(Mp i * ν)}

/-- The safe set is unchanged by `ν ↦ -ν`. -/
lemma SafeThick_neg (ν : X) (i : Fin 6) : SafeThick (-ν) i = SafeThick ν i := by
  rw [SafeThick, SafeThick, mul_neg, neg_neg]
  ac_rfl

/-- The `(T-I)²`-carry is compatible with the propagation hypothesis: its support consists of
group elements that map `O_F`'s relevant points into `O`. -/
def SafePair (ν : X) (i : Fin 6) (a : Option X) : Prop :=
  ∀ γ : X, a = some γ →
    ({γ, ModularGroup.T * γ, ModularGroup.T * ModularGroup.T * γ} : Finset X) ⊆ SafeThick ν i

/-- The `S(T-I)²`-carry is compatible with the propagation hypothesis. -/
def SafePairS (ν : X) (i : Fin 6) (b : Option X) : Prop :=
  ∀ γ : X, b = some γ →
    ({ModularGroup.S * γ, ModularGroup.S * (ModularGroup.T * γ),
      ModularGroup.S * (ModularGroup.T * ModularGroup.T * γ)} : Finset X) ⊆ SafeThick ν i

/-- The algebraic content of the finite check for the neighbour `ν` at row `i`: the error vector
of the second basis is carried by `(T-I)² a + S(T-I)² b` modulo the collapse ideal. -/
def CarryOk (ν : X) (i : Fin 6) (a b : Option X) : Prop :=
  rowDiffP (MonoidAlgebra.of ℂ X ν) i
    - ((R_T - 1)^2 * ofOpt a + R_S * (R_T - 1)^2 * ofOpt b) ∈ augIdeal

end Work.Asymptotics
