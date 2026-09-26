/-
# Spanning of `R/𝓘_odd` by the six elements `M' = (1, T⁻¹, STS, S, ST⁻¹, TS)`

This file proves `Work.Asymptotics.spanning_Mp_idealIOdd`: for every `γ ∈ SL(2,ℤ)` the
group-algebra element `ofSL γ` is congruent modulo the odd-weight defect ideal

  `𝓘_odd = (T-I)²R + S(T-I)²R + (1+z)R`   (`z = -I`)

to a `ℂ`-linear combination of the six elements `MpElem i = single (Mp i) 1`,
`Mp = (1, T⁻¹, STS, S, ST⁻¹, TS)`.

The proof reduces an arbitrary element of `R` modulo `𝓘_odd` along the *right* action of `R`
(under which `𝓘_odd`, a right ideal, is closed): writing `wᵢ = MpElem i`, the class of
`wᵢ * S` and of `wᵢ * T` in `R ⧸ 𝓘_odd` is again a `ℂ`-linear combination of the six classes
(the twelve computations `spMp_case*` below).  Since `R` is generated as a `ℂ`-algebra by
`S` and `T` (`Work.Residues.adjoin_R_S_R_T_eq_top`), the set of `x` whose class lies in the
span of the six is all of `R`.

The twelve base computations read `[S] = w₃`, `[T] = 2w₀ - w₁`, `[T⁻¹S] = 2w₃ - w₅`,
`[STz] = -2w₃ + w₄`, `[S²] = -w₀`, `[ST⁻¹S] = -2w₀ - w₂`, `[Tz] = -2w₀ + w₁`,
`[STST] = 2w₃ - w₅`, `[ST] = 2w₃ - w₄`, `[TST] = 2w₀ + w₂`, together with the two exact
identities `T⁻¹T = 1` and `S T⁻¹ T = S`.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainTiling
import Submission.Work.Asymptotics.OddIdeal
import Submission.Work.Residues.Basic
import Submission.Work.Residues.adjoin_R_S_R_T_eq_top

noncomputable section

set_option maxHeartbeats 2000000

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics

open Work.Kernels

/-! ## The six elements as monomials -/

lemma spMp_MpElem_zero : MpElem 0 = (1 : R) := by
  show MonoidAlgebra.single (Mp 0) (1 : ℂ) = 1
  rw [show Mp 0 = (1 : SL(2,ℤ)) from by decide]
  exact MonoidAlgebra.one_def.symm

lemma spMp_MpElem_one : MpElem 1 = R_Tinv := by
  show MonoidAlgebra.single (Mp 1) (1 : ℂ) = R_Tinv
  rw [show Mp 1 = (ModularGroup.T)⁻¹ from by decide]

lemma spMp_MpElem_two : MpElem 2 = R_S * R_T * R_S := by
  show MonoidAlgebra.single (Mp 2) (1 : ℂ) = R_S * R_T * R_S
  rw [show Mp 2 = ModularGroup.S * ModularGroup.T * ModularGroup.S from by decide]
  simp only [R_S, R_T, MonoidAlgebra.single_mul_single, mul_one]

lemma spMp_MpElem_three : MpElem 3 = R_S := by
  show MonoidAlgebra.single (Mp 3) (1 : ℂ) = R_S
  rw [show Mp 3 = ModularGroup.S from by decide]

lemma spMp_MpElem_four : MpElem 4 = R_S * R_Tinv := by
  show MonoidAlgebra.single (Mp 4) (1 : ℂ) = R_S * R_Tinv
  rw [show Mp 4 = ModularGroup.S * (ModularGroup.T)⁻¹ from by decide]
  simp only [R_S, R_Tinv, MonoidAlgebra.single_mul_single, mul_one]

lemma spMp_MpElem_five : MpElem 5 = R_T * R_S := by
  show MonoidAlgebra.single (Mp 5) (1 : ℂ) = R_T * R_S
  rw [show Mp 5 = ModularGroup.T * ModularGroup.S from by decide]
  simp only [R_S, R_T, MonoidAlgebra.single_mul_single, mul_one]

/-! ## Elementary group-algebra identities -/

lemma spMp_R_T_mul_R_Tinv : R_T * R_Tinv = (1 : R) := by
  rw [R_T, R_Tinv, MonoidAlgebra.single_mul_single, mul_one]
  rw [mul_inv_cancel]
  exact MonoidAlgebra.one_def.symm

lemma spMp_R_Tinv_mul_R_T : R_Tinv * R_T = (1 : R) := by
  rw [R_T, R_Tinv, MonoidAlgebra.single_mul_single, mul_one]
  rw [inv_mul_cancel]
  exact MonoidAlgebra.one_def.symm

lemma spMp_Rneg_comm (x : R) : Rneg * x = x * Rneg := Work.Residues.Rneg_comm x

lemma spMp_mul_Rneg (x : R) : x * Rneg = Rneg * x := (Work.Residues.Rneg_comm x).symm

lemma spMp_R_S_mul_R_S : R_S * R_S = Rneg := Work.Residues.R_S_mul_R_S_eq

lemma spMp_two_comm (x : R) : (2 : R) * x = x * (2 : R) := by
  have h : (2 : R) = algebraMap ℂ R (2 : ℂ) := (map_ofNat (algebraMap ℂ R) 2).symm
  rw [h, Algebra.commutes]

lemma spMp_two_smul (x : R) : (2 : ℂ) • x = (2 : R) * x := by
  rw [Algebra.smul_def, map_ofNat]

lemma spMp_mul_algebraMap (y : R) (c : ℂ) : y * algebraMap ℂ R c = c • y := by
  rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]

/-- `(S*T)² = T⁻¹*S`, from the group relation `(ST)³ = z`. -/
lemma spMp_STST : R_S * R_T * R_S * R_T = R_Tinv * R_S := by
  simp only [R_S, R_T, R_Tinv, MonoidAlgebra.single_mul_single, mul_one]
  congr 1
  decide

/-- `(T*S)² = S*T⁻¹`, the conjugate of the group relation `(ST)³ = z`. -/
lemma spMp_TSTS : R_T * R_S * R_T * R_S = R_S * R_Tinv := by
  simp only [R_S, R_T, R_Tinv, MonoidAlgebra.single_mul_single, mul_one]
  congr 1
  decide

/-- `S*T⁻¹*S = z * (T*S*T)`: the group element `S T⁻¹ S` is `-TST`. -/
lemma spMp_STiS : R_S * R_Tinv * R_S = Rneg * (R_T * R_S * R_T) := by
  simp only [Rneg, R_S, R_T, R_Tinv, MonoidAlgebra.single_mul_single, mul_one]
  congr 1
  decide

/-! ## Membership in `𝓘_odd` -/

lemma spMp_mem_T2 (x : R) : (R_T - 1) ^ 2 * x ∈ idealIOdd :=
  IdealI_le_idealIOdd (Work.Kernels.mem_span2.mpr ⟨x, 0, by rw [mul_zero, add_zero]⟩)

lemma spMp_mem_ST2 (x : R) : R_S * (R_T - 1) ^ 2 * x ∈ idealIOdd :=
  IdealI_le_idealIOdd (Work.Kernels.mem_span2.mpr ⟨0, x, by rw [mul_zero, zero_add]⟩)

lemma spMp_mem_aug (x : R) : (Rneg + 1) * x ∈ idealIOdd :=
  augIdealOdd_le_idealIOdd (augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd x)

/-! ## The Taylor expansions of `(T-I)²` -/

lemma spMp_T2_expand (x : R) : (R_T - 1) ^ 2 * x = R_T * (R_T * x) - 2 * (R_T * x) + x := by
  noncomm_ring

lemma spMp_T2_mul_RTi : (R_T - 1) ^ 2 * R_Tinv = R_T - 2 * (1 : R) + R_Tinv := by
  rw [spMp_T2_expand, spMp_R_T_mul_R_Tinv]
  noncomm_ring

lemma spMp_Tinv_eq : R_Tinv = 2 * (1 : R) - R_T + (R_T - 1) ^ 2 * R_Tinv := by
  rw [spMp_T2_mul_RTi]
  noncomm_ring

lemma spMp_S_T2_Tinv : R_S * (R_T - 1) ^ 2 * R_Tinv = R_S * R_T - 2 * R_S + R_S * R_Tinv := by
  have h1 : R_S * (R_T - 1) ^ 2 * R_Tinv
      = R_S * (R_T * (R_T * R_Tinv)) - 2 * (R_S * (R_T * R_Tinv)) + R_S * R_Tinv := by
    rw [show (R_T - 1) ^ 2 = R_T * R_T - 2 * R_T + 1 by noncomm_ring]
    noncomm_ring
  rw [h1, spMp_R_T_mul_R_Tinv]
  noncomm_ring

/-- `S(T-I)²T⁻¹ = (T*S)² - 2S + ST`, i.e. `= T*S*T*S - 2S + S*T`. -/
lemma spMp_i_eq :
    R_S * (R_T - 1) ^ 2 * R_Tinv = R_T * R_S * R_T * R_S - 2 * R_S + R_S * R_T := by
  rw [spMp_S_T2_Tinv, spMp_TSTS]
  noncomm_ring

/-- `(S(T-I)²T⁻¹)*S = S*T*S - 2*z + z*(T*S*T)`. -/
lemma spMp_i_mul_S :
    (R_S * (R_T - 1) ^ 2 * R_Tinv) * R_S
      = R_S * R_T * R_S - 2 * Rneg + Rneg * (R_T * R_S * R_T) := by
  have h1 : (R_S * (R_T - 1) ^ 2 * R_Tinv) * R_S
      = R_S * R_T * R_S - 2 * (R_S * R_S) + (R_S * R_Tinv) * R_S := by
    rw [spMp_S_T2_Tinv]
    noncomm_ring
  rw [h1, spMp_R_S_mul_R_S, spMp_STiS]

/-! ## The span of the six elements -/

/-- The `ℂ`-span of `wᵢ = MpElem i`, `i : Fin 6`. -/
abbrev spMpSpan : Submodule ℂ R := Submodule.span ℂ (Set.range MpElem)

lemma spMp_mem_spMpSpan (i : Fin 6) : MpElem i ∈ spMpSpan :=
  Submodule.subset_span ⟨i, rfl⟩

lemma spMp_two_mul_mem_spMpSpan (i : Fin 6) : (2 : R) * MpElem i ∈ spMpSpan := by
  rw [← spMp_two_smul]
  exact Submodule.smul_mem _ 2 (spMp_mem_spMpSpan i)

/-! ## The twelve base computations -/

lemma spMp_case0S : MpElem 0 * R_S ∈ spMpSpan ⊔ idealIOdd := by
  rw [spMp_MpElem_zero, one_mul, ← spMp_MpElem_three]
  exact Submodule.mem_sup_left (spMp_mem_spMpSpan 3)

lemma spMp_case1S : MpElem 1 * R_S ∈ spMpSpan ⊔ idealIOdd := by
  have key : MpElem 1 * R_S
      = (R_T - 1) ^ 2 * (R_Tinv * R_S) + ((2 : R) * MpElem 3 - MpElem 5) := by
    rw [spMp_MpElem_one, spMp_MpElem_three, spMp_MpElem_five, spMp_T2_expand]
    rw [← mul_assoc R_T R_Tinv R_S, spMp_R_T_mul_R_Tinv, one_mul]
    noncomm_ring
  have hv : (2 : R) * MpElem 3 - MpElem 5 ∈ spMpSpan :=
    Submodule.sub_mem _ (spMp_two_mul_mem_spMpSpan 3) (spMp_mem_spMpSpan 5)
  rw [key]
  exact Submodule.add_mem _ (Submodule.mem_sup_right (spMp_mem_T2 (R_Tinv * R_S)))
    (Submodule.mem_sup_left hv)

lemma spMp_case2S : MpElem 2 * R_S ∈ spMpSpan ⊔ idealIOdd := by
  have hSTS : R_S * R_T * R_S * R_S = Rneg * (R_S * R_T) := by
    rw [show R_S * R_T * R_S * R_S = R_S * R_T * (R_S * R_S) by noncomm_ring,
      spMp_R_S_mul_R_S, spMp_mul_Rneg]
  have hST : R_S * R_T = R_S * (R_T - 1) ^ 2 * R_Tinv + (2 * R_S - R_S * R_Tinv) := by
    rw [spMp_S_T2_Tinv]
    noncomm_ring
  have key : MpElem 2 * R_S
      = ((Rneg + 1) * (R_S * R_T) - R_S * (R_T - 1) ^ 2 * R_Tinv)
        + (-((2 : R) * MpElem 3) + MpElem 4) := by
    rw [spMp_MpElem_two, spMp_MpElem_three, spMp_MpElem_four, hSTS, hST]
    noncomm_ring
  have hξ : (Rneg + 1) * (R_S * R_T) - R_S * (R_T - 1) ^ 2 * R_Tinv ∈ idealIOdd :=
    Submodule.sub_mem _ (spMp_mem_aug (R_S * R_T)) (spMp_mem_ST2 R_Tinv)
  have hv : -((2 : R) * MpElem 3) + MpElem 4 ∈ spMpSpan :=
    Submodule.add_mem _ (Submodule.neg_mem _ (spMp_two_mul_mem_spMpSpan 3)) (spMp_mem_spMpSpan 4)
  rw [key]
  exact Submodule.add_mem _ (Submodule.mem_sup_right hξ) (Submodule.mem_sup_left hv)

lemma spMp_case3S : MpElem 3 * R_S ∈ spMpSpan ⊔ idealIOdd := by
  have key : MpElem 3 * R_S = (Rneg + 1) * (1 : R) + (-MpElem 0) := by
    rw [spMp_MpElem_three, spMp_MpElem_zero, spMp_R_S_mul_R_S]
    noncomm_ring
  rw [key]
  exact Submodule.add_mem _ (Submodule.mem_sup_right (spMp_mem_aug 1))
    (Submodule.neg_mem _ (Submodule.mem_sup_left (spMp_mem_spMpSpan 0)))

lemma spMp_case4S : MpElem 4 * R_S ∈ spMpSpan ⊔ idealIOdd := by
  have h1 : R_S * R_Tinv * R_S
      = 2 * Rneg - R_S * R_T * R_S + (R_S * (R_T - 1) ^ 2 * R_Tinv) * R_S := by
    conv_lhs => rw [spMp_Tinv_eq]
    rw [show R_S * (2 * (1 : R) - R_T + (R_T - 1) ^ 2 * R_Tinv) * R_S
        = 2 * (R_S * R_S) - R_S * R_T * R_S + (R_S * (R_T - 1) ^ 2 * R_Tinv) * R_S by
      noncomm_ring]
    rw [spMp_R_S_mul_R_S]
  have key : MpElem 4 * R_S
      = ((R_S * (R_T - 1) ^ 2 * R_Tinv) * R_S + (Rneg + 1) * (2 : R))
        + (-((2 : R) * MpElem 0) - MpElem 2) := by
    rw [spMp_MpElem_four, spMp_MpElem_zero, spMp_MpElem_two, h1]
    rw [spMp_two_comm Rneg]
    noncomm_ring
  have hX : (R_S * (R_T - 1) ^ 2 * R_Tinv) * R_S ∈ idealIOdd := by
    rw [mul_assoc]
    exact spMp_mem_ST2 (R_Tinv * R_S)
  have hξ : (R_S * (R_T - 1) ^ 2 * R_Tinv) * R_S + (Rneg + 1) * (2 : R) ∈ idealIOdd :=
    Submodule.add_mem _ hX (spMp_mem_aug 2)
  have hv : -((2 : R) * MpElem 0) - MpElem 2 ∈ spMpSpan :=
    Submodule.sub_mem _ (Submodule.neg_mem _ (spMp_two_mul_mem_spMpSpan 0)) (spMp_mem_spMpSpan 2)
  rw [key]
  exact Submodule.add_mem _ (Submodule.mem_sup_right hξ) (Submodule.mem_sup_left hv)

lemma spMp_case5S : MpElem 5 * R_S ∈ spMpSpan ⊔ idealIOdd := by
  have hTz : R_T * R_S * R_S = Rneg * R_T := by
    rw [show R_T * R_S * R_S = R_T * (R_S * R_S) by noncomm_ring, spMp_R_S_mul_R_S,
      spMp_mul_Rneg]
  have key : MpElem 5 * R_S
      = ((Rneg + 1) * R_T - (R_T - 1) ^ 2 * R_Tinv) + (-((2 : R) * MpElem 0) + MpElem 1) := by
    rw [spMp_MpElem_five, spMp_MpElem_zero, spMp_MpElem_one, hTz, spMp_T2_mul_RTi]
    noncomm_ring
  have hv : -((2 : R) * MpElem 0) + MpElem 1 ∈ spMpSpan :=
    Submodule.add_mem _ (Submodule.neg_mem _ (spMp_two_mul_mem_spMpSpan 0)) (spMp_mem_spMpSpan 1)
  rw [key]
  exact Submodule.add_mem _
    (Submodule.sub_mem _ (Submodule.mem_sup_right (spMp_mem_aug R_T))
      (Submodule.mem_sup_right (spMp_mem_T2 R_Tinv)))
    (Submodule.mem_sup_left hv)

lemma spMp_case0T : MpElem 0 * R_T ∈ spMpSpan ⊔ idealIOdd := by
  have key : MpElem 0 * R_T
      = (R_T - 1) ^ 2 * R_Tinv + ((2 : R) * MpElem 0 - MpElem 1) := by
    rw [spMp_MpElem_zero, spMp_MpElem_one, one_mul, spMp_T2_mul_RTi]
    noncomm_ring
  have hv : (2 : R) * MpElem 0 - MpElem 1 ∈ spMpSpan :=
    Submodule.sub_mem _ (spMp_two_mul_mem_spMpSpan 0) (spMp_mem_spMpSpan 1)
  rw [key]
  exact Submodule.add_mem _ (Submodule.mem_sup_right (spMp_mem_T2 R_Tinv))
    (Submodule.mem_sup_left hv)

lemma spMp_case1T : MpElem 1 * R_T ∈ spMpSpan ⊔ idealIOdd := by
  rw [spMp_MpElem_one, spMp_R_Tinv_mul_R_T, ← spMp_MpElem_zero]
  exact Submodule.mem_sup_left (spMp_mem_spMpSpan 0)

lemma spMp_case2T : MpElem 2 * R_T ∈ spMpSpan ⊔ idealIOdd := by
  have key : MpElem 2 * R_T
      = (R_T - 1) ^ 2 * (R_Tinv * R_S) + ((2 : R) * MpElem 3 - MpElem 5) := by
    rw [spMp_MpElem_two, spMp_MpElem_three, spMp_MpElem_five, spMp_STST, spMp_T2_expand]
    rw [← mul_assoc R_T R_Tinv R_S, spMp_R_T_mul_R_Tinv, one_mul]
    noncomm_ring
  have hv : (2 : R) * MpElem 3 - MpElem 5 ∈ spMpSpan :=
    Submodule.sub_mem _ (spMp_two_mul_mem_spMpSpan 3) (spMp_mem_spMpSpan 5)
  rw [key]
  exact Submodule.add_mem _ (Submodule.mem_sup_right (spMp_mem_T2 (R_Tinv * R_S)))
    (Submodule.mem_sup_left hv)

lemma spMp_case3T : MpElem 3 * R_T ∈ spMpSpan ⊔ idealIOdd := by
  have key : MpElem 3 * R_T
      = R_S * (R_T - 1) ^ 2 * R_Tinv + ((2 : R) * MpElem 3 - MpElem 4) := by
    rw [spMp_MpElem_three, spMp_MpElem_four, spMp_S_T2_Tinv]
    noncomm_ring
  have hv : (2 : R) * MpElem 3 - MpElem 4 ∈ spMpSpan :=
    Submodule.sub_mem _ (spMp_two_mul_mem_spMpSpan 3) (spMp_mem_spMpSpan 4)
  rw [key]
  exact Submodule.add_mem _ (Submodule.mem_sup_right (spMp_mem_ST2 R_Tinv))
    (Submodule.mem_sup_left hv)

lemma spMp_case4T : MpElem 4 * R_T ∈ spMpSpan ⊔ idealIOdd := by
  have h : R_S * R_Tinv * R_T = R_S := by
    rw [mul_assoc, spMp_R_Tinv_mul_R_T, mul_one]
  rw [spMp_MpElem_four, h, ← spMp_MpElem_three]
  exact Submodule.mem_sup_left (spMp_mem_spMpSpan 3)

lemma spMp_case5T : MpElem 5 * R_T ∈ spMpSpan ⊔ idealIOdd := by
  have key : MpElem 5 * R_T
      = (-((R_S * (R_T - 1) ^ 2 * R_Tinv) * R_S) + (Rneg + 1) * (R_T * R_S * R_T)
          - (Rneg + 1) * (2 : R)) + ((2 : R) * MpElem 0 + MpElem 2) := by
    rw [spMp_MpElem_five, spMp_MpElem_zero, spMp_MpElem_two, spMp_i_mul_S]
    rw [← spMp_mul_Rneg (R_T * R_S * R_T), add_mul, add_mul,
      ← spMp_mul_Rneg (R_T * R_S * R_T), ← spMp_two_comm Rneg]
    noncomm_ring
  have hX : (R_S * (R_T - 1) ^ 2 * R_Tinv) * R_S ∈ idealIOdd := by
    rw [mul_assoc]
    exact spMp_mem_ST2 (R_Tinv * R_S)
  have hY : (Rneg + 1) * (R_T * R_S * R_T) ∈ idealIOdd := spMp_mem_aug (R_T * R_S * R_T)
  have hZ : (Rneg + 1) * (2 : R) ∈ idealIOdd := spMp_mem_aug 2
  have hξ : -((R_S * (R_T - 1) ^ 2 * R_Tinv) * R_S) + (Rneg + 1) * (R_T * R_S * R_T)
      - (Rneg + 1) * (2 : R) ∈ idealIOdd := by
    rw [sub_eq_add_neg]
    exact Submodule.add_mem _
      (Submodule.add_mem _ (Submodule.neg_mem _ hX) hY) (Submodule.neg_mem _ hZ)
  have hv : (2 : R) * MpElem 0 + MpElem 2 ∈ spMpSpan :=
    Submodule.add_mem _ (spMp_two_mul_mem_spMpSpan 0) (spMp_mem_spMpSpan 2)
  rw [key]
  exact Submodule.add_mem _ (Submodule.mem_sup_right hξ) (Submodule.mem_sup_left hv)

/-! ## Closure under right multiplication by `S` and by `T` -/

lemma spMp_caseS (i : Fin 6) : MpElem i * R_S ∈ spMpSpan ⊔ idealIOdd := by
  fin_cases i
  · exact spMp_case0S
  · exact spMp_case1S
  · exact spMp_case2S
  · exact spMp_case3S
  · exact spMp_case4S
  · exact spMp_case5S

lemma spMp_caseT (i : Fin 6) : MpElem i * R_T ∈ spMpSpan ⊔ idealIOdd := by
  fin_cases i
  · exact spMp_case0T
  · exact spMp_case1T
  · exact spMp_case2T
  · exact spMp_case3T
  · exact spMp_case4T
  · exact spMp_case5T

lemma spMp_mul_R_S_mem {y : R} (hy : y ∈ spMpSpan ⊔ idealIOdd) :
    y * R_S ∈ spMpSpan ⊔ idealIOdd := by
  obtain ⟨v, hv, ξ, hξ, hsum⟩ := Submodule.mem_sup.mp hy
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
  have h1 : v * R_S ∈ spMpSpan ⊔ idealIOdd := by
    rw [← hc, Finset.sum_mul]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ (spMp_caseS i)
  have h2 : ξ * R_S ∈ idealIOdd := idealIOdd_mul_mem hξ R_S
  rw [← hsum, add_mul]
  exact Submodule.add_mem _ h1 (Submodule.mem_sup_right h2)

lemma spMp_mul_R_T_mem {y : R} (hy : y ∈ spMpSpan ⊔ idealIOdd) :
    y * R_T ∈ spMpSpan ⊔ idealIOdd := by
  obtain ⟨v, hv, ξ, hξ, hsum⟩ := Submodule.mem_sup.mp hy
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
  have h1 : v * R_T ∈ spMpSpan ⊔ idealIOdd := by
    rw [← hc, Finset.sum_mul]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ (spMp_caseT i)
  have h2 : ξ * R_T ∈ idealIOdd := idealIOdd_mul_mem hξ R_T
  rw [← hsum, add_mul]
  exact Submodule.add_mem _ h1 (Submodule.mem_sup_right h2)

/-! ## The algebra of elements reducing into the span -/

/-- The `ℂ`-subalgebra of elements of `R` which map the span of the six elements, modulo
`𝓘_odd`, into itself by right multiplication. -/
private def spMpD : Subalgebra ℂ R where
  carrier := {x : R | ∀ y : R, y ∈ spMpSpan ⊔ idealIOdd → y * x ∈ spMpSpan ⊔ idealIOdd}
  mul_mem' := by
    intro x z hx hz y hy
    rw [← mul_assoc]
    exact hz (y * x) (hx y hy)
  one_mem' := by
    intro y hy
    rwa [mul_one]
  add_mem' := by
    intro x z hx hz y hy
    rw [mul_add]
    exact Submodule.add_mem _ (hx y hy) (hz y hy)
  zero_mem' := by
    intro y _
    rw [mul_zero]
    exact Submodule.zero_mem _
  algebraMap_mem' := by
    intro c y hy
    rw [spMp_mul_algebraMap]
    exact Submodule.smul_mem _ c hy

lemma spMp_all_mem (x : R) : x ∈ spMpSpan ⊔ idealIOdd := by
  have hle : Algebra.adjoin ℂ ({R_S, R_T} : Set R) ≤ spMpD := by
    rw [Algebra.adjoin_le_iff]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · intro y hy
      exact spMp_mul_R_S_mem hy
    · intro y hy
      exact spMp_mul_R_T_mem hy
  have htop : spMpD = ⊤ := by
    rw [eq_top_iff, ← Work.Residues.adjoin_R_S_R_T_eq_top]
    exact hle
  have hx : x ∈ spMpD := by rw [htop]; trivial
  have h1 : (1 : R) ∈ spMpSpan ⊔ idealIOdd := by
    rw [← spMp_MpElem_zero]
    exact Submodule.mem_sup_left (spMp_mem_spMpSpan 0)
  have h := hx 1 h1
  rwa [one_mul] at h

/-! ## The theorem -/

theorem spanning_Mp_idealIOdd (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ c : Fin 6 → ℂ,
      Work.Asymptotics.ofSL γ - ∑ i, c i • Work.Asymptotics.MpElem i ∈
        Work.Asymptotics.idealIOdd := by
  have h := spMp_all_mem (ofSL γ)
  obtain ⟨v, hv, ξ, hξ, hsum⟩ := Submodule.mem_sup.mp h
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
  refine ⟨c, ?_⟩
  have : ofSL γ - ∑ i, c i • MpElem i = ξ := by
    rw [hc, ← hsum]
    abel
  rw [this]
  exact hξ

end Work.Asymptotics
