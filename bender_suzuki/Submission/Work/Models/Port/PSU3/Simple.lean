/-
**Simplicity of `PSU(3,2^n)`** for `n ≥ 2`.

This file completes the `PSU(3,2^n)` family of the Bender–Suzuki classification.  The main
result is

* `isSimpleGroup_PSU3Model (n) (hn : 2 ≤ n) : IsSimpleGroup (PSU3Model n)`.

The proof follows the classical route:

1.  `PSU(3,2^n)` acts faithfully and 2-transitively on the coset space `PSU3Model n ⧸ psu3B n`,
    where `psu3B n` is the image of the Borel subgroup `B = U ⋊ T` of `SU(3,2^n)`.  The
    2-transitivity comes from the Bruhat decomposition `SU(3,2^n) = B ∪ B w B`
    (`suSg_bruhat_cover`) and the general double-coset lemma
    `coset_multiplyPretransitive_two_of_two_doubleCosets`.  Faithfulness is the triviality of the
    normal core `core(B̄) = 1` (`normalCore_psu3B_eq_bot`).

2.  `core(B̄) = 1` is deduced from the corresponding statement for `SU(3,2^n)`: an element `x` of
    `core(B)` lies in `T` and centralises `U`; a torus element centralising `U` is a scalar
    matrix, hence lies in the kernel of `SU(3,2^n) → PSU(3,2^n)`, so it becomes trivial in
    `PSU(3,2^n)`.

3.  `PSU(3,2^n)` is perfect (`isPerfect_PSU3Model`).

4.  `[B̄,B̄] ≤ Ū`:  the commutator of the Borel lies in `U` because `T` is abelian and normalises
    `U` (`commutator_suB_le_suU`), and the image of this in `PSU(3,2^n)` is computed in
    `commutator_psu3B_le`.

5.  If `1 ≠ N ⊴ PSU(3,2^n)` then 2-transitivity makes `N` transitive on `PSU3Model n ⧸ psu3B n`,
    so `N ⊔ B̄ = ⊤`.  Hence
    `PSU(3,2^n) = [PSU(3,2^n), PSU(3,2^n)] ≤ N ⊔ [B̄,B̄] ≤ N ⊔ Ū`,
    using `commutator_le_sup_commutator_of_sup_eq_top`.  Therefore `PSU(3,2^n) ⧸ N` is a perfect
    quotient of the `2`-group `Ū`, hence a perfect finite `2`-group, hence trivial: `N = ⊤`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.Main
import Submission.Work.Models.Port.PSU3.Perfect
import Submission.Work.Models.Port.PSU3.Sylow
import Submission.Work.Models.Port.Commons.GroupTheory.Commutator.commutator_le_of_eq_sup_of_le_normalizer_of_commutator_le
import Submission.Work.Models.Port.Commons.GroupTheory.IsPGroup.subsingleton_of_isPerfect
import Submission.Work.Models.Port.Commons.GroupTheory.MulAut.toMonoidHom_mulAut_conj_apply
import Submission.Work.Models.Port.Commons.GroupTheory.Commutator.commutator_le_sup_commutator_of_sup_eq_top
import Submission.Work.Models.Port.Commons.GroupTheory.GroupAction.faithfulSMul_quotient_iff
import Submission.Work.Models.Port.Commons.GroupTheory.GroupAction.isPretransitive_normalSubgroup_of_faithful_twoTransitive
import Submission.Work.Models.Port.Commons.GroupTheory.GroupAction.coset_multiplyPretransitive_two_of_two_doubleCosets

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Matrix LeanEval.GroupTheory.Defs
open scoped MatrixGroups commutatorElement Pointwise

namespace Submission.PSU3

/-! ## `[B,B] ≤ U` -/

/-- The torus is abelian, so its commutator subgroup is trivial. -/
lemma commutator_suT_le_bot (n : ℕ) : ⁅suT n, suT n⁆ ≤ ⊥ := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [Subgroup.mem_bot, commutatorElement_def]
  have h1 : suTg n a * suTg n b = suTg n b * suTg n a := by
    rw [suTg_mul, suTg_mul]
    exact congrArg (suTg n) (mul_comm a b)
  calc suTg n a * suTg n b * (suTg n a)⁻¹ * (suTg n b)⁻¹
      = suTg n b * suTg n a * (suTg n a)⁻¹ * (suTg n b)⁻¹ := by rw [h1]
    _ = 1 := by group

/-- Every commutator of two elements of the Borel lies in `U`. -/
theorem commutator_suB_le_suU (n : ℕ) : ⁅suB n, suB n⁆ ≤ suU n := by
  refine Commons.GroupTheory.Commutator.commutator_le_of_eq_sup_of_le_normalizer_of_commutator_le
    (suU n) (suT n) (suB n) rfl (suB_le_normalizer_suU n) ?_
  exact le_trans (commutator_suT_le_bot n) bot_le

/-! ## Uniqueness of the `U·T` decomposition -/

/-- If `u ∈ U` conjugates `t ∈ T` into `T`, then `u` centralizes `t`. -/
lemma suU_conj_suT_mem_suT (n : ℕ) {u t : GL (Fin 3) (F n)} (hu : u ∈ suU n) (ht : t ∈ suT n)
    (h : u * t * u⁻¹ ∈ suT n) : u * t * u⁻¹ = t := by
  obtain ⟨b, c, hc, rfl⟩ := hu
  obtain ⟨a, rfl⟩ := ht
  have hcommU : suUg n b c * suTg n a * (suUg n b c)⁻¹ * (suTg n a)⁻¹ ∈ suU n := by
    have hconj : suTg n a * (suUg n b c)⁻¹ * (suTg n a)⁻¹ ∈ suU n :=
      suU_conj_mem n a ((suU n).inv_mem ⟨b, c, hc, rfl⟩)
    have heq : suUg n b c * suTg n a * (suUg n b c)⁻¹ * (suTg n a)⁻¹
        = suUg n b c * (suTg n a * (suUg n b c)⁻¹ * (suTg n a)⁻¹) := by group
    rw [heq]
    exact (suU n).mul_mem ⟨b, c, hc, rfl⟩ hconj
  have hcommT : suUg n b c * suTg n a * (suUg n b c)⁻¹ * (suTg n a)⁻¹ ∈ suT n :=
    (suT n).mul_mem h ((suT n).inv_mem ⟨a, rfl⟩)
  have h1 : suUg n b c * suTg n a * (suUg n b c)⁻¹ * (suTg n a)⁻¹ = 1 := by
    have hbot : suUg n b c * suTg n a * (suUg n b c)⁻¹ * (suTg n a)⁻¹
        ∈ (⊥ : Subgroup (GL (Fin 3) (F n))) := by
      rw [← suU_inf_suT n]
      exact ⟨hcommU, hcommT⟩
    simpa using hbot
  calc suUg n b c * suTg n a * (suUg n b c)⁻¹
      = (suUg n b c * suTg n a * (suUg n b c)⁻¹ * (suTg n a)⁻¹) * suTg n a := by group
    _ = suTg n a := by rw [h1, one_mul]

/-! ## A torus element centralizing `U` is a scalar -/

lemma suTg_centralizing_suU_is_scalar (n : ℕ) (hn : 1 ≤ n) (a : (F n)ˣ)
    (h : ∀ v ∈ suU n, suTg n a * v * (suTg n a)⁻¹ = v) :
    suTg n a = Matrix.GeneralLinearGroup.scalar (Fin 3) a := by
  have ha0 : (a : F n) ≠ 0 := Units.ne_zero a
  have e1 : suTg n a * suUg n 0 1 * (suTg n a)⁻¹ = suUg n 0 1 :=
    h _ ⟨0, 1, su_cond_zero_one n, rfl⟩
  rw [suTg_conj_suUg] at e1
  have hAq : (a : F n) ^ (2 ^ n + 1) = 1 := by
    have h2 := (suUg_inj n e1).2
    rw [pow_succ']
    simpa using h2
  obtain ⟨c₁, hc₁⟩ := Commons.FieldTheory.FiniteField.trace_surjective_galoisField_even n hn
    (1 : F n) (by simp)
  have hcond₁ : c₁ + c₁ ^ (2 ^ n) = (1 : F n) ^ (2 ^ n + 1) := by simpa using hc₁
  have e2 : suTg n a * suUg n 1 c₁ * (suTg n a)⁻¹ = suUg n 1 c₁ := h _ ⟨1, c₁, hcond₁, rfl⟩
  rw [suTg_conj_suUg] at e2
  have hB : (a : F n) * ((a : F n) ^ (2 ^ n - 1))⁻¹ = 1 := by
    have h1 := (suUg_inj n e2).1
    simpa using h1
  have h1 : (a : F n) ^ (2 ^ n - 1) = (a : F n) :=
    ((mul_inv_eq_one₀ (pow_ne_zero _ ha0)).mp hB).symm
  have h2 : ((a : F n) ^ (2 ^ n))⁻¹ = (a : F n) := by
    have h3 : (a : F n) ^ (2 ^ n) = (a : F n)⁻¹ := by
      have h4 : (a : F n) ^ (2 ^ n) * (a : F n) = 1 := by
        rw [← pow_succ]; exact hAq
      exact (mul_eq_one_iff_eq_inv₀ ha0).mp h4
    rw [h3, inv_inv]
  apply Units.ext
  rw [suTg_coe, Matrix.GeneralLinearGroup.coe_scalar, suTmat, Matrix.scalar_apply,
    Matrix.diagonal_eq_diagonal_iff]
  intro i
  fin_cases i <;> simp [h1, h2]

/-! ## The normal core of the Borel of `SU(3,2^n)` -/

lemma normalCore_subgroupOf_le_suT (n : ℕ) (hn : 1 ≤ n) {x : ↥(SU3 n)}
    (hx : x ∈ ((suB n).subgroupOf (SU3 n)).normalCore) : (x : GL (Fin 3) (F n)) ∈ suT n := by
  have hmemB : (x : GL (Fin 3) (F n)) ∈ suB n :=
    Subgroup.mem_subgroupOf.mp (Subgroup.normalCore_le _ hx)
  have hmemW : (x : GL (Fin 3) (F n)) ∈ (suB n).map (MulAut.conj (suSg n)).toMonoidHom := by
    set W : ↥(SU3 n) := ⟨suSg n, suSg_mem_SU3 n⟩ with hW
    have hx2 : x ∈ ((suB n).subgroupOf (SU3 n)).map (MulEquiv.toMonoidHom (MulAut.conj W)) := by
      rw [Subgroup.normalCore_eq_iInf_map_conj] at hx
      exact (iInf_le (fun g => ((suB n).subgroupOf (SU3 n)).map
        (MulEquiv.toMonoidHom (MulAut.conj g))) W) hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx2
    refine Subgroup.mem_map.mpr ⟨(y : GL (Fin 3) (F n)), Subgroup.mem_subgroupOf.mp hy, ?_⟩
    rw [Commons.GroupTheory.MulAut.toMonoidHom_mulAut_conj_apply]
    rw [← hyx]
    show suSg n * (y : GL (Fin 3) (F n)) * (suSg n)⁻¹ =
      ((W * y * W⁻¹ : ↥(SU3 n)) : GL (Fin 3) (F n))
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rfl
  rw [← suB_inf_map_conj_suSg n]
  exact ⟨hmemB, hmemW⟩

/-- Every element of the normal core of the Borel centralizes `U`. -/
lemma normalCore_subgroupOf_commute_suU (n : ℕ) (hn : 1 ≤ n) {x : ↥(SU3 n)}
    (hx : x ∈ ((suB n).subgroupOf (SU3 n)).normalCore) {u : GL (Fin 3) (F n)} (hu : u ∈ suU n) :
    (x : GL (Fin 3) (F n)) * u * (x : GL (Fin 3) (F n))⁻¹ = u := by
  have hxT : (x : GL (Fin 3) (F n)) ∈ suT n := normalCore_subgroupOf_le_suT n hn hx
  obtain ⟨b, c, hc, rfl⟩ := hu
  set U : ↥(SU3 n) := ⟨suUg n b c, suU_le_SU3 n ⟨b, c, hc, rfl⟩⟩ with hU
  have hmem : U * x * U⁻¹ ∈ ((suB n).subgroupOf (SU3 n)).normalCore :=
    (Subgroup.normalCore_normal ((suB n).subgroupOf (SU3 n))).conj_mem x hx U
  have hconjT : suUg n b c * (x : GL (Fin 3) (F n)) * (suUg n b c)⁻¹ ∈ suT n := by
    have h := normalCore_subgroupOf_le_suT n hn hmem
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hcomm : suUg n b c * (x : GL (Fin 3) (F n)) * (suUg n b c)⁻¹ = (x : GL (Fin 3) (F n)) :=
    suU_conj_suT_mem_suT n ⟨b, c, hc, rfl⟩ hxT hconjT
  have h2 : (x : GL (Fin 3) (F n)) * suUg n b c = suUg n b c * (x : GL (Fin 3) (F n)) := by
    calc (x : GL (Fin 3) (F n)) * suUg n b c
        = (suUg n b c * (x : GL (Fin 3) (F n)) * (suUg n b c)⁻¹) * suUg n b c := by
          rw [hcomm]
      _ = suUg n b c * (x : GL (Fin 3) (F n)) := by group
  calc (x : GL (Fin 3) (F n)) * suUg n b c * (x : GL (Fin 3) (F n))⁻¹
      = (suUg n b c * (x : GL (Fin 3) (F n))) * (x : GL (Fin 3) (F n))⁻¹ := by rw [h2]
    _ = suUg n b c := by group

lemma normalCore_subgroupOf_le_ker (n : ℕ) (hn : 1 ≤ n) {x : ↥(SU3 n)}
    (hx : x ∈ ((suB n).subgroupOf (SU3 n)).normalCore) : x ∈ (psu3Hom n).ker := by
  obtain ⟨a, ha⟩ : ∃ a : (F n)ˣ, (x : GL (Fin 3) (F n)) = suTg n a :=
    normalCore_subgroupOf_le_suT n hn hx
  have hcent : ∀ v ∈ suU n, suTg n a * v * (suTg n a)⁻¹ = v := by
    intro v hv
    rw [← ha]
    exact normalCore_subgroupOf_commute_suU n hn hx hv
  have hscal := suTg_centralizing_suU_is_scalar n hn a hcent
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  show ProjGenLinGroup.mk (x : GL (Fin 3) (F n)) = 1
  rw [ha, hscal, ProjGenLinGroup.mk_scalar]



/-! ## The image of the Borel in `PSU(3,2^n)` -/

noncomputable def psu3B (n : ℕ) : Subgroup (PSU3Model n) :=
  ((suB n).subgroupOf (SU3 n)).map (psu3Hom n)

noncomputable def psu3U (n : ℕ) : Subgroup (PSU3Model n) :=
  ((suU n).subgroupOf (SU3 n)).map (psu3Hom n)

noncomputable def psu3W (n : ℕ) : PSU3Model n := psu3Hom n ⟨suSg n, suSg_mem_SU3 n⟩

lemma psu3U_le_psu3B (n : ℕ) : psu3U n ≤ psu3B n :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono (SU3 n) (by rw [suB]; exact le_sup_left))

/-- The image of the Borel subgroup is strongly embedded in `PSU(3,2^n)`. -/
theorem psu3B_stronglyEmbedded (n : ℕ) (hn : 2 ≤ n) : IsStronglyEmbedded (psu3B n) := by
  have hn1 : 1 ≤ n := by omega
  have hB := suB_stronglyEmbedded n hn1
  have h := isStronglyEmbedded_map_of_surjective (psu3Hom n) (psu3Hom_surjective n)
    ((suB n).subgroupOf (SU3 n)) hB.1 hB.2.1 hB.2.2 (psu3Hom_ker_le_borel n)
    (psu3Hom_ker_le_center n) (odd_card_psu3Hom_ker n hn1)
  exact ⟨h.1, h.2.1, h.2.2⟩

lemma isPGroup_psu3U (n : ℕ) (hn : 1 ≤ n) : IsPGroup 2 ↥(psu3U n) := by
  refine (suUS_isPGroup n hn).of_surjective
    (((psu3Hom n).comp ((suU n).subgroupOf (SU3 n)).subtype).codRestrict (psu3U n)
      (fun x => Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)) ?_
  intro y
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp y.2
  exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩

theorem normalCore_psu3B_eq_bot (n : ℕ) (hn : 2 ≤ n) : (psu3B n).normalCore = ⊥ := by
  have hn1 : 1 ≤ n := by omega
  have hker : (psu3Hom n).ker ≤ (suB n).subgroupOf (SU3 n) := psu3Hom_ker_le_borel n
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, hy⟩ := psu3Hom_surjective n x
  have hCle : ((psu3B n).normalCore).comap (psu3Hom n) ≤ (suB n).subgroupOf (SU3 n) := by
    intro z hz
    have hzB : psu3Hom n z ∈ psu3B n := Subgroup.normalCore_le _ (Subgroup.mem_comap.mp hz)
    obtain ⟨b, hb, hbz⟩ := Subgroup.mem_map.mp hzB
    have h1 : z * b⁻¹ ∈ (psu3Hom n).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hbz, mul_inv_cancel]
    have h3 : z = (z * b⁻¹) * b := by group
    rw [h3]
    exact ((suB n).subgroupOf (SU3 n)).mul_mem (hker h1) hb
  have hyC : y ∈ ((psu3B n).normalCore).comap (psu3Hom n) := by
    rw [Subgroup.mem_comap, hy]; exact hx
  have hycore : y ∈ ((suB n).subgroupOf (SU3 n)).normalCore :=
    Subgroup.normal_le_normalCore.mpr hCle hyC
  have hyker : y ∈ (psu3Hom n).ker := normalCore_subgroupOf_le_ker n hn1 hycore
  have h1 : psu3Hom n y = 1 := hyker
  rw [hy] at h1
  simpa using h1

/-! ## The coset action -/

theorem psu3_cover (n : ℕ) (hn : 1 ≤ n) :
    ∀ g : PSU3Model n, g ∈ psu3B n ∨ ∃ b₁ b₂ : ↥(psu3B n),
      g = (b₁ : PSU3Model n) * psu3W n * (b₂ : PSU3Model n) := by
  intro g
  obtain ⟨A, rfl⟩ := psu3Hom_surjective n g
  rcases suSg_bruhat_cover n hn A.2 with hA | ⟨b₁, hb₁, b₂, hb₂, hA'⟩
  · left
    exact Subgroup.mem_map.mpr ⟨A, hA, rfl⟩
  · right
    refine ⟨⟨psu3Hom n ⟨b₁, suB_le_SU3 n hb₁⟩, Subgroup.mem_map.mpr ⟨_, hb₁, rfl⟩⟩,
      ⟨psu3Hom n ⟨b₂, suB_le_SU3 n hb₂⟩, Subgroup.mem_map.mpr ⟨_, hb₂, rfl⟩⟩, ?_⟩
    have heq : A = (⟨b₁, suB_le_SU3 n hb₁⟩ : ↥(SU3 n)) * ⟨suSg n, suSg_mem_SU3 n⟩ *
        ⟨b₂, suB_le_SU3 n hb₂⟩ := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul] using hA'
    rw [heq, map_mul, map_mul]
    rfl

theorem psu3Model_isMultiplyPretransitive_two (n : ℕ) (hn : 1 ≤ n) :
    MulAction.IsMultiplyPretransitive (PSU3Model n) (PSU3Model n ⧸ psu3B n) 2 :=
  Commons.GroupTheory.GroupAction.coset_multiplyPretransitive_two_of_two_doubleCosets
    (psu3B n) (psu3W n) (psu3_cover n hn)

theorem psu3B_faithfulSMul (n : ℕ) (hn : 2 ≤ n) :
    FaithfulSMul (PSU3Model n) (PSU3Model n ⧸ psu3B n) :=
  (Commons.GroupTheory.GroupAction.faithfulSMul_quotient_iff (psu3B n)).mpr
    (normalCore_psu3B_eq_bot n hn)

/-! ## The commutator of the Borel lies in the image of `U` -/

lemma commutator_suB_subgroupOf_le_suU (n : ℕ) :
    ⁅(suB n).subgroupOf (SU3 n), (suB n).subgroupOf (SU3 n)⁆ ≤ (suU n).subgroupOf (SU3 n) := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [Subgroup.mem_subgroupOf]
  have hcomm : ⁅(x : GL (Fin 3) (F n)), (y : GL (Fin 3) (F n))⁆ ∈ suU n :=
    commutator_suB_le_suU n (Subgroup.commutator_mem_commutator hx hy)
  simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using hcomm

theorem commutator_psu3B_le (n : ℕ) (hn : 1 ≤ n) : ⁅psu3B n, psu3B n⁆ ≤ psu3U n := by
  rw [psu3B, psu3U, Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
  refine Subgroup.mem_map.mpr ⟨⁅a, b⁆, commutator_suB_subgroupOf_le_suU n
    (Subgroup.commutator_mem_commutator ha hb), ?_⟩
  simp only [commutatorElement_def, map_mul, map_inv]

theorem nontrivial_PSU3Model (n : ℕ) (hn : 1 ≤ n) : Nontrivial (PSU3Model n) := by
  refine ⟨⟨psu3W n, 1, fun h => ?_⟩⟩
  have hker : (⟨suSg n, suSg_mem_SU3 n⟩ : ↥(SU3 n)) ∈ (psu3Hom n).ker := by
    rw [MonoidHom.mem_ker]; exact h
  exact suSg_notMem_suB n (psu3Hom_ker_le_borel n hker)

/-! ## Simplicity -/

theorem isSimpleGroup_PSU3Model (n : ℕ) (hn : 2 ≤ n) : IsSimpleGroup (PSU3Model n) := by
  have hn1 : 1 ≤ n := by omega
  haveI : Nontrivial (PSU3Model n) := nontrivial_PSU3Model n hn1
  haveI hfaith : FaithfulSMul (PSU3Model n) (PSU3Model n ⧸ psu3B n) := psu3B_faithfulSMul n hn
  haveI h2 : MulAction.IsMultiplyPretransitive (PSU3Model n) (PSU3Model n ⧸ psu3B n) 2 :=
    psu3Model_isMultiplyPretransitive_two n hn1
  haveI hperf : Group.IsPerfect ↥(PSU3Model n) := isPerfect_PSU3Model n hn
  apply IsSimpleGroup.mk
  intro N hN
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  · refine Or.inr ?_
    haveI : N.Normal := hN
    have htrans :=
      Commons.GroupTheory.GroupAction.isPretransitive_normalSubgroup_of_faithful_twoTransitive
        (G := PSU3Model n) (Ω := PSU3Model n ⧸ psu3B n) N hN hbot
    have hsup : N ⊔ psu3B n = ⊤ := by
      rw [eq_top_iff]
      intro g _
      obtain ⟨n', hn'⟩ := htrans (((g : PSU3Model n)) : PSU3Model n ⧸ psu3B n)
        (((1 : PSU3Model n)) : PSU3Model n ⧸ psu3B n)
      have hsm : ((n' : PSU3Model n) * g) • (((1 : PSU3Model n)) : PSU3Model n ⧸ psu3B n)
          = (n' : PSU3Model n) • (((g : PSU3Model n)) : PSU3Model n ⧸ psu3B n) := by
        rw [mul_smul, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
      have hmem : ((n' : PSU3Model n) * g) ∈ MulAction.stabilizer (PSU3Model n)
          (((1 : PSU3Model n)) : PSU3Model n ⧸ psu3B n) := by
        rw [MulAction.mem_stabilizer_iff, hsm]
        exact hn'
      have h2 : ((n' : PSU3Model n) * g) ∈ psu3B n := by
        rwa [MulAction.stabilizer_quotient] at hmem
      have h3 : g = (n' : PSU3Model n)⁻¹ * ((n' : PSU3Model n) * g) := by group
      rw [h3]
      exact Subgroup.mul_mem_sup (N.inv_mem n'.2) h2
    have hcomm_le : commutator (PSU3Model n) ≤ N ⊔ psu3U n :=
      (Commons.GroupTheory.Commutator.commutator_le_sup_commutator_of_sup_eq_top N (psu3B n)
        hsup).trans (sup_le_sup_left (commutator_psu3B_le n hn1) N)
    have htop : (⊤ : Subgroup (PSU3Model n)) ≤ N ⊔ psu3U n :=
      (le_of_eq hperf.commutator_eq_top.symm).trans hcomm_le
    have hsupU : N ⊔ psu3U n = ⊤ := top_le_iff.mp htop
    have hU2 : IsPGroup 2 ↥(psu3U n) := isPGroup_psu3U n hn1
    have hQ2 : IsPGroup 2 (PSU3Model n ⧸ N) := by
      have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp (psu3U n).subtype) := by
        intro y
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
        have hg : g ∈ (↑(N ⊔ psu3U n) : Set (PSU3Model n)) := by
          rw [hsupU]; trivial
        rw [Subgroup.normal_mul N (psu3U n), Set.mem_mul] at hg
        obtain ⟨n, hn, u, hu, hnu⟩ := hg
        refine ⟨⟨u, hu⟩, ?_⟩
        have hn1' : (QuotientGroup.mk' N) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
        show (QuotientGroup.mk' N) u = (QuotientGroup.mk' N) g
        rw [← hnu, map_mul, hn1', one_mul]
      exact hU2.of_surjective _ hsurj
    haveI : Group.IsPerfect (PSU3Model n ⧸ N) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    haveI : Finite (PSU3Model n ⧸ N) :=
      Finite.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    haveI hpr : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsingle : Subsingleton (PSU3Model n ⧸ N) :=
      Commons.GroupTheory.IsPGroup.subsingleton_of_isPerfect hQ2 inferInstance
    rw [Subgroup.eq_top_iff']
    intro y
    exact (QuotientGroup.eq_one_iff y).mp
      (Subsingleton.elim ((y : PSU3Model n) : PSU3Model n ⧸ N) 1)

end Submission.PSU3
