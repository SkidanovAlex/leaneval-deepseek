import Mathlib
import Submission.Work.DSM5b.HCF.ReesGraded
import Submission.Work.DSM5b.H0Defs
import Submission.Work.DSCOH.resAt_degZero
import Submission.Work.DSCOH.degZero_exists_repr
import Submission.Work.DSM5b.HCF.prod_div_tS_mem_chartRing
import Submission.Work.DSM5b.HCF.locRes_away_mk
import Submission.Work.DSCOH.resAt_divPow_toLoc
import Submission.Work.DSCOH.prodLocIso_divPow_toLoc
import Submission.Work.DSCOH.lmb_subS_eq_xpow
import Submission.Work.DSCOH.divPow_toLoc_mem
import Submission.Work.DSCOH.lmb_support_degree
import Submission.Work.DSM5b.HCF.reesGr_mem_iff
import Submission.Work.DSM5b.HCF.reesPhi_aeval_homogeneous

namespace Work.DSM5b.HCF

universe u
section GeneralArith

variable {A : Type u} [CommRing A] {n : ℕ}
variable {M : Type u} [AddCommGroup M] [Module A M] [Module (Work.DSCOH.Poly A n) M]
  [IsScalarTower A (Work.DSCOH.Poly A n) M]

/-- **Addition of two chart fractions over the common denominator `X_S^{k+k'}`.** -/
theorem divPow_toLoc_add (S : Finset (Fin n)) (k k' : ℕ) (m m' : M) :
    Work.DSCOH.divPow (A := A) (M := M) S k (Work.DSCOH.toLoc (A := A) (M := M) S m) +
      Work.DSCOH.divPow (A := A) (M := M) S k' (Work.DSCOH.toLoc (A := A) (M := M) S m') =
    Work.DSCOH.divPow (A := A) (M := M) S (k + k')
      (Work.DSCOH.toLoc (A := A) (M := M) S
        ((Work.DSCOH.monomial (A := A) S) ^ k' • m + (Work.DSCOH.monomial (A := A) S) ^ k • m')) := by
  rw [Work.DSCOH.divPow_toLoc_mk_general (A := A) (n := n) (M := M),
    Work.DSCOH.divPow_toLoc_mk_general (A := A) (n := n) (M := M),
    Work.DSCOH.divPow_toLoc_mk_general (A := A) (n := n) (M := M),
    LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, one_smul, Submonoid.coe_mul]
  rw [pow_add]

/-- Scalar multiplication of a chart fraction (the scalar is in `A`). -/
theorem divPow_toLoc_smul (S : Finset (Fin n)) (k : ℕ) (a : A) (m : M) :
    a • (Work.DSCOH.divPow (A := A) (M := M) S k (Work.DSCOH.toLoc (A := A) (M := M) S m)) =
      Work.DSCOH.divPow (A := A) (M := M) S k
        (Work.DSCOH.toLoc (A := A) (M := M) S (a • m)) := by
  rw [← LinearMap.map_smul (Work.DSCOH.divPow (A := A) (M := M) S k),
    ← LinearMap.map_smul (Work.DSCOH.toLoc (A := A) (M := M) S)]

/-- `toLoc S m = 0` iff some element of the submonoid `subS S` kills `m`. -/
theorem toLoc_eq_zero_iff (S : Finset (Fin n)) (m : M) :
    Work.DSCOH.toLoc (A := A) (M := M) S m = 0 ↔
      ∃ u : Work.DSCOH.subS (A := A) S, u • m = 0 := by
  have h1 : Work.DSCOH.toLoc (A := A) (M := M) S m =
      LocalizedModule.mk m (1 : Work.DSCOH.subS (A := A) S) := rfl
  have h0 : (0 : Work.DSCOH.locAt (A := A) (M := M) S) =
      LocalizedModule.mk (0 : M) (1 : Work.DSCOH.subS (A := A) S) :=
    (map_zero (Work.DSCOH.toLoc (A := A) (M := M) S)).symm
  rw [h1, h0, LocalizedModule.mk_eq]
  simp

end GeneralArith

section Core

variable {n : ℕ} {R : Type u} [CommRing R]

/-- The lift of `t : Fin n → R` to the index type `ULift.{u} (Fin n)`. -/
noncomputable def tU (t : Fin n → R) : ULift.{u} (Fin n) → R := fun i => t i.down

@[simp] lemma tU_up (t : Fin n → R) (i : Fin n) : tU t (ULift.up i) = t i := rfl

/-- `reesEps R : R[u] → R` is the evaluation `u ↦ 1`, i.e. the sum of the coefficients. -/
noncomputable def reesEps (R : Type u) [CommRing R] : Polynomial R →ₐ[R] R :=
  Polynomial.aeval (1 : R)

lemma reesEps_C (r : R) : reesEps R (Polynomial.C r) = r := by
  simp [reesEps]

lemma reesEps_C_mul_X_pow (r : R) (d : ℕ) :
    reesEps R (Polynomial.C r * Polynomial.X ^ d) = r := by
  simp [reesEps]

lemma reesEps_reesPhi (t : Fin n → R) (f : Work.DSCOH.Poly R n) :
    reesEps R (reesPhi t f) = MvPolynomial.aeval t f := by
  have h : (reesEps R).comp (reesPhi t) = MvPolynomial.aeval t := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [reesEps, reesPhi]
  simpa using DFunLike.congr_fun h f

/-- The chart localisation `R_{t_S}`, `S : Finset (ULift (Fin n))`. -/
abbrev chartLoc (t : Fin n → R) (S : Finset (ULift.{u} (Fin n))) : Type u :=
  Localization.Away (DSMap.Mix2.tS (tU t) S)

/-- `tS (tU t) S = ∏_{i ∈ S.image down} t i`. -/
lemma tS_tU (t : Fin n → R) (S : Finset (ULift.{u} (Fin n))) :
    DSMap.Mix2.tS (tU t) S = ∏ i ∈ S.image ULift.down, t i := by
  show (∏ i ∈ S, tU t i) = ∏ i ∈ S.image ULift.down, t i
  rw [Finset.prod_image (f := t) (s := S) (Set.injOn_of_injective ULift.down_injective)]
  rfl

lemma card_image_down (S : Finset (ULift.{u} (Fin n))) :
    (S.image ULift.down).card = S.card :=
  Finset.card_image_of_injective S ULift.down_injective

lemma image_sdiff_down (S T : Finset (ULift.{u} (Fin n))) :
    (T \ S).image ULift.down = T.image ULift.down \ S.image ULift.down :=
  Finset.image_sdiff T S ULift.down_injective



/-- `aeval t` of the monomial `∏_{i ∈ T} X_i` is `∏_{i ∈ T} t i`. -/
lemma aeval_monomial_t (t : Fin n → R) (T : Finset (Fin n)) :
    MvPolynomial.aeval t (Work.DSCOH.monomial (A := R) T) = ∏ i ∈ T, t i := by
  rw [Work.DSCOH.monomial, MvPolynomial.aeval_prod]
  exact Finset.prod_congr rfl fun i _ => MvPolynomial.aeval_X t i

/-- **The total-degree bookkeeping.**  For `e : Fin n → ℕ` supported on `T = S.image down`,
`(tS (tU t) S)^{∑ e} = (∏_{i ∈ S} (tU t) i^{∑e - e i}) · (∏_{i} t i^{e i})`. -/
lemma tS_pow_eq_prod (t : Fin n → R) (S : Finset (ULift.{u} (Fin n))) (e : Fin n → ℕ)
    (hsupp : ∀ i : Fin n, (⟨i⟩ : ULift.{u} (Fin n)) ∉ S → e i = 0) :
    (DSMap.Mix2.tS (tU t) S) ^ (∑ i, e i) =
      (∏ i ∈ S, (tU t) i ^ ((∑ j, e j) - e i.down)) * (∏ i : Fin n, t i ^ e i) := by
  have hle : ∀ i : Fin n, e i ≤ ∑ j, e j := fun i =>
    Finset.single_le_sum (f := e) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hsplit : ∀ i ∈ S, (tU t) i ^ (∑ j, e j) =
      (tU t) i ^ ((∑ j, e j) - e i.down) * (tU t) i ^ (e i.down) := by
    intro i _
    rw [← pow_add, Nat.sub_add_cancel (hle i.down)]
  have hprod : (∏ i ∈ S, (tU t) i ^ (e i.down)) = ∏ i : Fin n, t i ^ e i := by
    have h1 : (∏ i ∈ S, (tU t) i ^ (e i.down)) = ∏ j ∈ S.image ULift.down, t j ^ e j := by
      rw [Finset.prod_image (f := fun j => t j ^ e j) (s := S)
        (Set.injOn_of_injective ULift.down_injective)]
      rfl
    rw [h1]
    exact Finset.prod_subset (Finset.subset_univ _) (fun j _ hj => by
      have hj' : (⟨j⟩ : ULift.{u} (Fin n)) ∉ S := fun hc => hj (Finset.mem_image.mpr ⟨⟨j⟩, hc, rfl⟩)
      rw [hsupp j hj', pow_zero])
  calc (DSMap.Mix2.tS (tU t) S) ^ (∑ i, e i)
      = ∏ i ∈ S, (tU t) i ^ (∑ j, e j) := by
        rw [DSMap.Mix2.tS]
        exact (Finset.prod_pow _ _ _).symm
    _ = ∏ i ∈ S, ((tU t) i ^ ((∑ j, e j) - e i.down) * (tU t) i ^ (e i.down)) :=
        Finset.prod_congr rfl hsplit
    _ = (∏ i ∈ S, (tU t) i ^ ((∑ j, e j) - e i.down)) *
        (∏ i ∈ S, (tU t) i ^ (e i.down)) := Finset.prod_mul_distrib
    _ = (∏ i ∈ S, (tU t) i ^ ((∑ j, e j) - e i.down)) * (∏ i : Fin n, t i ^ e i) := by
        rw [hprod]

/-- The fraction `c / t_S^k ∈ R_{t_S}`. -/
noncomputable def chartVal (t : Fin n → R) (S : Finset (ULift.{u} (Fin n))) (k : ℕ) (c : R) :
    chartLoc t S :=
  IsLocalization.mk' (chartLoc t S) c
    ⟨(DSMap.Mix2.tS (tU t) S) ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers _) k⟩

lemma chartVal_zero (t : Fin n → R) (S : Finset (ULift.{u} (Fin n))) (k : ℕ) :
    chartVal t S k 0 = 0 := by
  rw [chartVal, IsLocalization.mk'_zero]

lemma chartVal_add (t : Fin n → R) (S : Finset (ULift.{u} (Fin n))) (k : ℕ) (c c' : R) :
    chartVal t S k c + chartVal t S k c' = chartVal t S k (c + c') := by
  rw [chartVal, chartVal, chartVal, ← IsLocalization.mk'_add]
  rw [IsLocalization.mk'_eq_iff_eq']
  simp only [Submonoid.coe_mul]
  congr 1
  ring

lemma chartVal_smul (t : Fin n → R) (S : Finset (ULift.{u} (Fin n))) (k : ℕ) (r c : R) :
    r • chartVal t S k c = chartVal t S k (r * c) := by
  rw [chartVal, chartVal, Algebra.smul_def, IsLocalization.mul_mk'_eq_mk'_of_mul]

lemma chartVal_mul (t : Fin n → R) (S : Finset (ULift.{u} (Fin n))) (k k' : ℕ) (c c' : R) :
    chartVal t S k c * chartVal t S k' c' = chartVal t S (k + k') (c * c') := by
  rw [chartVal, chartVal, chartVal, ← IsLocalization.mk'_mul]
  rw [IsLocalization.mk'_eq_iff_eq']
  simp only [Submonoid.coe_mul]
  congr 1
  rw [pow_add]

lemma chartVal_one (t : Fin n → R) (S : Finset (ULift.{u} (Fin n))) :
    chartVal t S 0 1 = 1 := by
  rw [chartVal, show (⟨(DSMap.Mix2.tS (tU t) S) ^ 0,
      Submonoid.pow_mem _ (Submonoid.mem_powers _) 0⟩ : Submonoid.powers _) = 1 from
    Subtype.ext (pow_zero _), IsLocalization.mk'_one, map_one]

lemma chartVal_sum (t : Fin n → R) (S : Finset (ULift.{u} (Fin n))) (k : ℕ)
    {ι : Type*} (s : Finset ι) (c : ι → R) :
    chartVal t S k (∑ i ∈ s, c i) = ∑ i ∈ s, chartVal t S k (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chartVal_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      exact (chartVal_add t S k _ _).symm


variable (t : Fin n → R)

end Core

end Work.DSM5b.HCF
