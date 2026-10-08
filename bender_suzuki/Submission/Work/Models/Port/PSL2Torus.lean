/-
**The rank-one `BN`-pair structure of `PSL(2, 2ⁿ)`.**

For a field `K` of characteristic two the *split torus* of `PSL(2, K)` is the image of the
diagonal matrices `diag(a, a⁻¹)`, and the *Borel* (the stabilizer of a point of the projective
line) is the semi-direct product `U ⋊ T` of the unipotent subgroup `U ≅ (K, +)` and `T ≅ Kˣ`.
The torus acts on `U` by `t(a) · u(c) · t(a)⁻¹ = u(a² · c)`, an action which is
*fixed-point free* on `U ∖ 1` over a field of characteristic two (`a² = 1 ⟹ a = 1`).

This is the `PSL(2, q)` case of the elementary `(B, N)`-pair structure that the three families
of the Bender–Suzuki classification share; the corresponding statements for `Sz(2^(2n+1))`
(`szTS`, `szBorelS_eq_sup`) and `PSU(3, 2ⁿ)` (`suTS`, `suBS_eq_sup`) are in
`Submission/Sz/SuzukiCondition.lean` and `Submission/PSU3/SuzukiCondition.lean`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.exists_sylow_two_elementaryAbelian_projectiveSpecialLinearGroup
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.card_stabilizer_projectiveSpecialLinearGroup
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.card_twoPointStabilizer_projectiveSpecialLinearGroup
import Submission.Work.Models.Port.Commons.LinearAlgebra.Matrix.center_SL2_eq_bot_of_charTwo
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.centralizer_le_of_isStronglyEmbedded
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.centralizer_inf_eq_sup_of_eq_sup_of_le_normalizer_of_central
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.card_sup_of_inf_eq_bot_of_le_normalizer
import Submission.Work.Models.Port.Commons.GroupTheory.MulAut.toMonoidHom_mulAut_conj_apply
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.stronglyEmbedded_stabilizer_projectiveSpecialLinearGroup
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.centralizer_eq_left_of_isStronglyEmbedded

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs
open scoped LinearAlgebra.Projectivization

namespace Submission.PSL2

open Commons.GroupTheory.SL2

/-! ## The split torus of `SL(2, K)` -/

variable {K : Type*}

/-- The diagonal matrix `diag(a, a⁻¹)` as an element of `SL(2, K)`. -/
def diagSL [Field K] (a : Kˣ) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![↑a, 0; 0, ↑(a⁻¹)], by rw [Matrix.det_fin_two]; simp⟩

lemma diagSL_coe [Field K] (a : Kˣ) :
    ((diagSL a : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![↑a, 0; 0, ↑(a⁻¹)] := rfl

@[simp] lemma diagSL_mul [Field K] (a b : Kˣ) : diagSL (a * b) = diagSL a * diagSL b := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, diagSL_coe, diagSL_coe, diagSL_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[simp] lemma diagSL_one [Field K] : (diagSL (1 : Kˣ) : Matrix.SpecialLinearGroup (Fin 2) K) = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [diagSL_coe, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

lemma diagSL_injective [Field K] : Function.Injective (diagSL (K := K)) := by
  intro a b h
  have h00 : (diagSL a : Matrix (Fin 2) (Fin 2) K) 0 0 = (diagSL b : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    rw [h]
  exact Units.ext (by simpa [diagSL_coe] using h00)

lemma diagSL_inv [Field K] (a : Kˣ) : (diagSL a)⁻¹ = diagSL a⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [← diagSL_mul, mul_inv_cancel, diagSL_one])

lemma transvectionSL_coe [Field K] (c : K) :
    ((transvectionSL K c) : Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Commons.GroupTheory.SL2.transvectionSL, Matrix.transvection]

/-- The torus conjugates the unipotent subgroup as `t(a) u(c) t(a)⁻¹ = u(a² c)`. -/
lemma diagSL_conj_transvectionSL [Field K] (a : Kˣ) (c : K) :
    diagSL a * transvectionSL K c * (diagSL a)⁻¹ = transvectionSL K ((a : K)^2 * c) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, diagSL_coe, transvectionSL_coe,
    Matrix.adjugate_fin_two, transvectionSL_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

/-- The diagonal embedding `Kˣ → SL(2, K)`. -/
def diagHom (K : Type*) [Field K] : Kˣ →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun := diagSL
  map_one' := diagSL_one
  map_mul' a b := diagSL_mul a b

@[simp] lemma diagHom_apply [Field K] (a : Kˣ) :
    diagHom K a = diagSL a := rfl

/-! ## The split torus of `PSL(2, K)` -/

/-- The torus `Kˣ → PSL(2, K)`. -/
noncomputable def diagPSLHom (K : Type*) [Field K] :
    Kˣ →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))).comp (diagHom K)

lemma diagPSLHom_apply [Field K] (a : Kˣ) :
    diagPSLHom K a =
      QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) (diagSL a) := rfl

lemma diagPSLHom_injective [Field K] (hchar : CharP K 2) :
    Function.Injective (diagPSLHom K) := by
  have hker : (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))).ker = ⊥ := by
    rw [QuotientGroup.ker_mk', center_specialLinearGroup_two_eq_bot hchar]
  have hmk : Function.Injective
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  exact hmk.comp (diagSL_injective)

/-- The action of the torus on the unipotent subgroup of `PSL(2, K)`. -/
lemma diagPSLHom_conj_unipotentPSLHom [Field K] (a : Kˣ) (c : K) :
    diagPSLHom K a * unipotentPSLHom K (Multiplicative.ofAdd c) * (diagPSLHom K a)⁻¹ =
      unipotentPSLHom K (Multiplicative.ofAdd ((a : K)^2 * c)) := by
  have hprod : diagPSLHom K a * diagPSLHom K a⁻¹ = 1 := by rw [← map_mul]; simp
  have hinv : diagPSLHom K a⁻¹ = (diagPSLHom K a)⁻¹ := (inv_eq_of_mul_eq_one_right hprod).symm
  rw [← hinv]
  change (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))) (diagSL a) *
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)))
        (transvectionSL K c) *
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))) (diagSL a⁻¹) =
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)))
      (transvectionSL K ((a : K)^2 * c))
  rw [← map_mul, ← map_mul, ← diagSL_inv, diagSL_conj_transvectionSL]

/-! ## The projective line and the two points fixed by the torus -/

/-- The point `⟨e₀⟩` of the projective line over `K`. -/
noncomputable def pt0 (K : Type*) [Field K] : Projectivization K (Fin 2 → K) :=
  Projectivization.mk K (Pi.single (0 : Fin 2) (1 : K)) (Pi.single_ne_zero_iff.mpr one_ne_zero)

/-- The point `⟨e₁⟩` of the projective line over `K`. -/
noncomputable def pt1 (K : Type*) [Field K] : Projectivization K (Fin 2 → K) :=
  Projectivization.mk K (Pi.single (1 : Fin 2) (1 : K)) (Pi.single_ne_zero_iff.mpr one_ne_zero)

lemma pt0_ne_pt1 (K : Type*) [Field K] : pt0 K ≠ pt1 K := by
  intro h
  rw [pt0, pt1, Projectivization.mk_eq_mk_iff] at h
  obtain ⟨l, hl⟩ := h
  have h0 := congrFun hl 0
  simp [Pi.smul_apply, Pi.single] at h0

section Geom

variable {K : Type*} [Field K]

/-- The action of a coset representative on the projective line. -/
lemma mk'_smul_apply (A : Matrix.SpecialLinearGroup (Fin 2) K)
    (p : Projectivization K (Fin 2 → K)) :
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) A) • p = A • p :=
  Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk A p

lemma diagSL_smul_pt0 (a : Kˣ) : diagSL a • (pt0 K) = pt0 K := by
  rw [pt0, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  refine ⟨a, ?_⟩
  change (a : K) • Pi.single (0 : Fin 2) (1 : K) =
    Matrix.toLin' (↑(diagSL a)) (Pi.single (0 : Fin 2) (1 : K))
  rw [Matrix.toLin'_apply, diagSL_coe]
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single, smul_eq_mul]

lemma diagSL_smul_pt1 (a : Kˣ) : diagSL a • (pt1 K) = pt1 K := by
  rw [pt1, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  refine ⟨a⁻¹, ?_⟩
  change ((a⁻¹ : Kˣ) : K) • Pi.single (1 : Fin 2) (1 : K) =
    Matrix.toLin' (↑(diagSL a)) (Pi.single (1 : Fin 2) (1 : K))
  rw [Matrix.toLin'_apply, diagSL_coe]
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single, smul_eq_mul]

lemma transvectionSL_smul_pt0 (c : K) : transvectionSL K c • (pt0 K) = pt0 K := by
  rw [pt0, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  refine ⟨1, ?_⟩
  rw [one_smul]
  change Pi.single (0 : Fin 2) (1 : K) =
    Matrix.toLin' (↑(transvectionSL K c) : Matrix (Fin 2) (Fin 2) K) (Pi.single (0 : Fin 2) (1 : K))
  rw [Matrix.toLin'_apply, transvectionSL_coe]
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single]

lemma transvectionSL_smul_pt1_eq_iff (c : K) :
    transvectionSL K c • (pt1 K) = pt1 K ↔ c = 0 := by
  constructor
  · intro h
    rw [pt1, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at h
    obtain ⟨l, hl⟩ := h
    have h0 := congrFun hl 0
    have hT : (transvectionSL K c • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K)) 0 = c := by
      rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, transvectionSL_coe]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single]
    have hl0 : (l • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K)) 0 = 0 := by
      simp [Pi.smul_apply, Pi.single]
    rw [hl0, hT] at h0
    exact h0.symm
  · rintro rfl
    rw [Commons.GroupTheory.SL2.transvectionSL_zero]
    simp

/-- The unipotent subgroup of `PSL(2,K)` fixes `⟨e₀⟩`. -/
lemma unipotent_range_le_stabilizer_pt0 :
    (unipotentPSLHom K).range ≤
      MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) (pt0 K) := by
  intro x hx
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
  rw [MulAction.mem_stabilizer_iff]
  show unipotentPSLHom K y • pt0 K = pt0 K
  rw [show unipotentPSLHom K y =
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)))
        (transvectionSL K (Multiplicative.toAdd y)) from rfl, mk'_smul_apply]
  exact transvectionSL_smul_pt0 (Multiplicative.toAdd y)

/-- The torus fixes `⟨e₀⟩`. -/
lemma diag_range_le_stabilizer_pt0 :
    (diagPSLHom K).range ≤
      MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) (pt0 K) := by
  intro x hx
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
  rw [MulAction.mem_stabilizer_iff]
  show diagPSLHom K a • pt0 K = pt0 K
  rw [show diagPSLHom K a =
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)))
        (diagSL a) from rfl, mk'_smul_apply]
  exact diagSL_smul_pt0 a

/-- The torus fixes `⟨e₁⟩`. -/
lemma diag_range_le_stabilizer_pt1 :
    (diagPSLHom K).range ≤
      MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) (pt1 K) := by
  intro x hx
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
  rw [MulAction.mem_stabilizer_iff]
  show diagPSLHom K a • pt1 K = pt1 K
  rw [show diagPSLHom K a =
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)))
        (diagSL a) from rfl, mk'_smul_apply]
  exact diagSL_smul_pt1 a

/-- The torus acts freely off `⟨e₀⟩`: no non-trivial element of `U` fixes `⟨e₁⟩`. -/
lemma unipotent_range_inf_stabilizer_pt1_eq_bot :
    (unipotentPSLHom K).range ⊓
        MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) (pt1 K) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxU, hx1⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hxU
  rw [MulAction.mem_stabilizer_iff] at hx1
  have h : transvectionSL K (Multiplicative.toAdd y) • (pt1 K) = pt1 K := by
    have h' : unipotentPSLHom K y • pt1 K = pt1 K := hx1
    rw [show unipotentPSLHom K y =
        (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)))
          (transvectionSL K (Multiplicative.toAdd y)) from rfl, mk'_smul_apply] at h'
    exact h'
  have hc : Multiplicative.toAdd y = 0 := (transvectionSL_smul_pt1_eq_iff _).mp h
  rw [← ofAdd_toAdd y, hc, ofAdd_zero, map_one]

end Geom

section Finite

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

lemma card_diagPSLHom_range : Nat.card ↥(diagPSLHom K).range = Nat.card K - 1 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective
      (diagPSLHom_injective (K := K) (inferInstance : CharP K 2))).toEquiv, Nat.card_units]

/-- The torus normalises the unipotent subgroup. -/
lemma diag_range_le_normalizer_unipotent :
    (diagPSLHom K).range ≤
      Subgroup.normalizer (((unipotentPSLHom K).range :
        Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) : Set _) := by
  intro x hx
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : ((unipotentPSLHom K).range).map
        (MulAut.conj (diagPSLHom K a)).toMonoidHom ≤ (unipotentPSLHom K).range := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hu
    refine MonoidHom.mem_range.mpr
      ⟨Multiplicative.ofAdd ((a : K)^2 * Multiplicative.toAdd w), ?_⟩
    rw [Commons.GroupTheory.MulAut.toMonoidHom_mulAut_conj_apply]
    exact (diagPSLHom_conj_unipotentPSLHom a (Multiplicative.toAdd w)).symm.trans
      (by rw [ofAdd_toAdd])
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]

/-- `U` and `T` meet trivially. -/
theorem unipotent_inf_diag_eq_bot :
    (unipotentPSLHom K).range ⊓ (diagPSLHom K).range = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzU, hzT⟩ := Subgroup.mem_inf.mp hz
  have hmem : z ∈ (unipotentPSLHom K).range ⊓
      MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) (pt1 K) :=
    Subgroup.mem_inf.mpr ⟨hzU, diag_range_le_stabilizer_pt1 hzT⟩
  rwa [unipotent_range_inf_stabilizer_pt1_eq_bot (K := K)] at hmem

/-- **The Borel subgroup of `PSL(2, K)` is the semi-direct product `U ⋊ T`** of the unipotent
subgroup and the split torus. -/
theorem unipotent_sup_diag_eq_stabilizer_pt0 :
    (unipotentPSLHom K).range ⊔ (diagPSLHom K).range =
      MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) (pt0 K) := by
  have hle : (unipotentPSLHom K).range ⊔ (diagPSLHom K).range ≤
      MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) (pt0 K) :=
    sup_le unipotent_range_le_stabilizer_pt0 diag_range_le_stabilizer_pt0
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hcardU : Nat.card ↥(unipotentPSLHom K).range = Nat.card K := by
    rw [← Nat.card_congr (MonoidHom.ofInjective
      (unipotentPSLHom_injective (K := K) (inferInstance : CharP K 2))).toEquiv,
      ← Nat.card_congr Multiplicative.ofAdd]
  have hcardM : Nat.card ↥(MulAction.stabilizer
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) (pt0 K)) =
      Nat.card K * (Nat.card K - 1) :=
    card_stabilizer_projectiveSpecialLinearGroup (K := K) (inferInstance : CharP K 2) (by
      have h : 1 < Nat.card K := by
        rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
      omega) (pt0 K)
  rw [Commons.GroupTheory.Subgroup.card_sup_of_inf_eq_bot_of_le_normalizer
      (unipotentPSLHom K).range (diagPSLHom K).range
      diag_range_le_normalizer_unipotent unipotent_inf_diag_eq_bot,
    hcardM, hcardU, card_diagPSLHom_range]

/-- Over a field of characteristic two the torus acts fixed-point-freely on `U`: the only
torus element centralizing a non-trivial `u(c)` is the identity. -/
theorem diagPSLHom_eq_one_of_centralizes_unipotent {a : Kˣ} {c : K} (hc : c ≠ 0)
    (h : diagPSLHom K a * unipotentPSLHom K (Multiplicative.ofAdd c) =
      unipotentPSLHom K (Multiplicative.ofAdd c) * diagPSLHom K a) : a = 1 := by
  have h2 : unipotentPSLHom K (Multiplicative.ofAdd ((a : K)^2 * c)) =
      unipotentPSLHom K (Multiplicative.ofAdd c) := by
    rw [← diagPSLHom_conj_unipotentPSLHom a c, h, mul_assoc, mul_inv_cancel, mul_one]
  have h3 : (a : K)^2 * c = c :=
    Multiplicative.ofAdd.injective
      ((unipotentPSLHom_injective (K := K) (inferInstance : CharP K 2)) h2)
  have h4 : (a : K)^2 = 1 := mul_right_cancel₀ hc (by rw [h3, one_mul])
  exact Units.ext (CharTwo.sq_inj.mp (by rw [h4]; simp))

/-- **The two-point stabilizer of `PSL(2, K)` is the split torus** (`K` of characteristic two):
this is the statement `B ⊓ Bʷ = T` of the rank-one `(B,N)`-pair structure. -/
theorem diag_range_eq_inf_stabilizer :
    (diagPSLHom K).range =
      MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) (pt0 K) ⊓
        MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) (pt1 K) := by
  have hcard : 2 ≤ Nat.card K := by
    have h : 1 < Nat.card K := by
      rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
    omega
  refine Subgroup.eq_of_le_of_card_ge
    (le_inf diag_range_le_stabilizer_pt0 diag_range_le_stabilizer_pt1) ?_
  rw [card_diagPSLHom_range,
    card_twoPointStabilizer_projectiveSpecialLinearGroup (K := K) (inferInstance : CharP K 2)
      hcard (pt0 K) (pt1 K) (pt0_ne_pt1 K)]

/-! ## The Weyl element and the `(B, N)`-pair relation `B ⊓ Bʷ = T` -/

/-- The Weyl element `!![0,1;1,0] ∈ SL(2, K)` of the split `(B, N)`-pair. -/
def weylSL (K : Type*) [Field K] : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; -1, 0], by rw [Matrix.det_fin_two]; simp⟩

/-- The Weyl element of `PSL(2, K)`. -/
noncomputable def weylPSL (K : Type*) [Field K] :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) (weylSL K)

section Weyl

variable {K : Type*} [Field K]

lemma weylSL_smul_pt0 : weylSL K • (pt0 K) = pt1 K := by
  rw [pt0, pt1, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  refine ⟨-1, ?_⟩
  change (-1 : K) • Pi.single (1 : Fin 2) (1 : K) =
    Matrix.toLin' (↑(weylSL K) : Matrix (Fin 2) (Fin 2) K) (Pi.single (0 : Fin 2) (1 : K))
  rw [Matrix.toLin'_apply]
  ext i; fin_cases i <;> simp [weylSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single]

lemma weylPSL_smul_pt0 : weylPSL K • (pt0 K) = pt1 K := by
  rw [weylPSL, mk'_smul_apply]
  exact weylSL_smul_pt0

end Weyl

section WeylFinite

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

/-- **The rank-one `(B,N)`-pair relation `B ⊓ Bʷ = T`** in `PSL(2, K)` for `K` of
characteristic two, where `B` is the point stabilizer and `T` the split torus. -/
theorem inf_map_conj_weyl_eq_diag :
    MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) (pt0 K) ⊓
      (MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) (pt0 K)).map
        (MulAut.conj (weylPSL K)).toMonoidHom = (diagPSLHom K).range := by
  have hmap : (MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) (pt0 K)).map
      (MulAut.conj (weylPSL K)).toMonoidHom =
      MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) (pt1 K) := by
    rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj (weylPSL K) (pt0 K), weylPSL_smul_pt0]
  rw [hmap]
  exact (diag_range_eq_inf_stabilizer).symm

end WeylFinite

section WeylAction

variable {K : Type*} [Field K]

@[simp] lemma weylSL_coe :
    ((weylSL K : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![0, 1; -1, 0] := rfl

/-- **The Weyl element inverts the torus**: `w · t(a) · w⁻¹ = t(a⁻¹)`. -/
lemma weylSL_conj_diagSL (a : Kˣ) : weylSL K * diagSL a * (weylSL K)⁻¹ = diagSL a⁻¹ := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, weylSL_coe, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, diagSL_coe]

/-- **The Weyl element inverts the torus** in `PSL(2, K)`. -/
lemma weylPSL_conj_diagPSLHom (a : Kˣ) :
    weylPSL K * diagPSLHom K a * (weylPSL K)⁻¹ = diagPSLHom K a⁻¹ := by
  have hinv : ((QuotientGroup.mk'
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))) (weylSL K))⁻¹ =
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)))
        ((weylSL K)⁻¹) :=
    inv_eq_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel, map_one])
  rw [weylPSL, diagPSLHom_apply, diagPSLHom_apply, hinv]
  rw [← map_mul, ← map_mul, weylSL_conj_diagSL]

/-- The Weyl element is an involution in characteristic two. -/
lemma weylPSL_mul_self [CharP K 2] : weylPSL K * weylPSL K = 1 := by
  have h : weylSL K * weylSL K = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, weylSL_coe]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]
  rw [weylPSL, ← map_mul, h, map_one]

/-- The Weyl element does not lie in the Borel subgroup (it moves `⟨e₀⟩` to `⟨e₁⟩`). -/
lemma weylPSL_not_mem_stabilizer_pt0 :
    weylPSL K ∉ MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) (pt0 K) := by
  intro h
  rw [MulAction.mem_stabilizer_iff, weylPSL_smul_pt0] at h
  exact pt0_ne_pt1 K h.symm

end WeylAction

/-- **The Weyl element normalises the split torus** `T`, so `T ⊔ ⟨w⟩ ≤ N_G(T)`: this is the
"Weyl group" of the rank-one `(B,N)`-pair. -/
lemma weylPSL_mem_normalizer_diagPSLHom :
    weylPSL K ∈ Subgroup.normalizer (((diagPSLHom K).range :
      Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) : Set _) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : ((diagPSLHom K).range).map (MulAut.conj (weylPSL K)).toMonoidHom ≤
      (diagPSLHom K).range := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
    refine MonoidHom.mem_range.mpr ⟨a⁻¹, ?_⟩
    rw [Commons.GroupTheory.MulAut.toMonoidHom_mulAut_conj_apply, weylPSL_conj_diagPSLHom]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]

/-! ## The centralizer of an involution, via the Frobenius structure of the Borel -/

section Centralizer

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

/-- **The centralizer of the involution `u(c)` of `PSL(2, K)`** (`K` of characteristic two,
`c ≠ 0`) **is the unipotent subgroup `U ≅ (K, +)`**.  This is the "Frobenius" derivation of
the computation in `Submission/PSL2Centralizer.lean`: `B = U ⋊ T` is a Frobenius group with
kernel `U` (the torus acts fixed-point-freely on `U ∖ 1`), so every involution of `U` has
centralizer `U` inside `B`, and strong embedding of `B` promotes this to the whole group. -/
theorem centralizer_unipotentPSLHom_eq_range {c : K} (hc : c ≠ 0) :
    Subgroup.centralizer ({unipotentPSLHom K (Multiplicative.ofAdd c)} :
      Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) = (unipotentPSLHom K).range := by
  have hcard : 2 ≤ Nat.card K := by
    have h : 1 < Nat.card K := by rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
    omega
  obtain ⟨hMtop, hMeven, hModd⟩ :=
    stronglyEmbedded_stabilizer_projectiveSpecialLinearGroup (K := K)
      (inferInstance : CharP K 2) hcard (pt0 K)
  have huU : unipotentPSLHom K (Multiplicative.ofAdd c) ∈ (unipotentPSLHom K).range :=
    MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hu_ne : unipotentPSLHom K (Multiplicative.ofAdd c) ≠ 1 := by
    intro h
    have h' : Multiplicative.ofAdd c = (1 : Multiplicative K) :=
      (unipotentPSLHom_injective (K := K) (inferInstance : CharP K 2)) (by rw [h, map_one])
    exact hc (ofAdd_eq_one.mp h')
  have hu2 : orderOf (unipotentPSLHom K (Multiplicative.ofAdd c)) = 2 := by
    refine (orderOf_eq_prime_iff (p := 2)).mpr ⟨?_, hu_ne⟩
    rw [pow_two, ← map_mul]
    have hy2 : Multiplicative.ofAdd c * Multiplicative.ofAdd c = 1 := by
      rw [← ofAdd_add, CharTwo.add_self_eq_zero, ofAdd_zero]
    rw [hy2, map_one]
  have hcu : ∀ a ∈ (unipotentPSLHom K).range,
      a * unipotentPSLHom K (Multiplicative.ofAdd c) =
        unipotentPSLHom K (Multiplicative.ofAdd c) * a := by
    intro a ha
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp ha
    rw [← map_mul, ← map_mul, mul_comm y (Multiplicative.ofAdd c)]
  have hfpf : ∀ t ∈ (diagPSLHom K).range,
      t ∈ Subgroup.centralizer ({unipotentPSLHom K (Multiplicative.ofAdd c)} :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) → t = 1 := by
    intro t ht hmem
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp ht
    have ha1 : a = 1 := diagPSLHom_eq_one_of_centralizes_unipotent (K := K) hc
      (Subgroup.mem_centralizer_singleton_iff.mp hmem)
    rw [ha1, map_one]
  exact Commons.GroupTheory.StronglyEmbedded.centralizer_eq_left_of_isStronglyEmbedded
    (MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) (pt0 K))
    (unipotentPSLHom K).range (diagPSLHom K).range hMtop hMeven hModd
    (unipotent_sup_diag_eq_stabilizer_pt0 (K := K)).symm
    (unipotent_inf_diag_eq_bot (K := K)) (diag_range_le_normalizer_unipotent (K := K))
    huU hu2 hcu hfpf

end Centralizer

end Finite



end Submission.PSL2
