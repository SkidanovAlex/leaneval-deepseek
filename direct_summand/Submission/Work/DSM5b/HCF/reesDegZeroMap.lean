import Mathlib
import Submission.Work.DSM5b.HCF.ReesGraded
import Submission.Work.DSM5b.H0Defs
import Submission.Work.DSCOH.resAt_degZero
import Submission.Work.DSCOH.resAt_divPow_toLoc
import Submission.Work.DSCOH.prodLocIso_divPow_toLoc
import Submission.Work.DSCOH.lmb_subS_eq_xpow
import Submission.Work.DSCOH.divPow_toLoc_mem
import Submission.Work.DSCOH.lmb_support_degree
import Submission.Work.DSM5b.HCF.reesGr_mem_iff
import Submission.Work.DSM5b.HCF.reesPhi_aeval_homogeneous
import Submission.Work.DSM5b.HCF.prod_div_tS_mem_chartRing
import Submission.Work.DSM5b.HCF.locRes_away_mk
import Submission.Work.DSM5b.HCF.reesDegZeroAux
namespace Work.DSM5b.HCF

universe u
open DSMap DSMap.Mix DSMap.Mix2

variable {n : ℕ} {R : Type u} [CommRing R]

section Core

variable (t : Fin n → R)

/-- The chosen index of a representative `m/X_S^k` of `x ∈ degZero`. -/
noncomputable def reprK (S : Finset (ULift.{u} (Fin n)))
    (x : ↥(Work.DSCOH.degZero (A := R) (n := n) (M := ↥(reesM t)) (reesGr t)
      (S.image ULift.down))) : ℕ :=
  Classical.choose (Work.DSCOH.degZero_exists_repr (A := R) (n := n) (M := ↥(reesM t))
    (reesGr t) (S.image ULift.down) x.2)

/-- The chosen numerator of a representative `m/X_S^k` of `x ∈ degZero`. -/
noncomputable def reprM (S : Finset (ULift.{u} (Fin n)))
    (x : ↥(Work.DSCOH.degZero (A := R) (n := n) (M := ↥(reesM t)) (reesGr t)
      (S.image ULift.down))) : ↥(reesM t) :=
  Classical.choose (Classical.choose_spec (Work.DSCOH.degZero_exists_repr (A := R) (n := n)
    (M := ↥(reesM t)) (reesGr t) (S.image ULift.down) x.2))

lemma repr_spec (S : Finset (ULift.{u} (Fin n)))
    (x : ↥(Work.DSCOH.degZero (A := R) (n := n) (M := ↥(reesM t)) (reesGr t)
      (S.image ULift.down))) :
    reprM t S x ∈ reesGr t (reprK t S x * (S.image ULift.down).card) ∧
      x.1 = Work.DSCOH.divPow (A := R) (n := n) (M := ↥(reesM t)) (S.image ULift.down)
        (reprK t S x) (Work.DSCOH.toLoc (A := R) (n := n) (M := ↥(reesM t))
          (S.image ULift.down) (reprM t S x)) :=
  Classical.choose_spec (Classical.choose_spec (Work.DSCOH.degZero_exists_repr (A := R) (n := n)
    (M := ↥(reesM t)) (reesGr t) (S.image ULift.down) x.2))

/-- **The value of `x ∈ degZero` in `R_{t_S}`**, computed from the chosen representative
`reprM x / X_{S'}^{reprK x}`: `eps (reprM x) / t_S^{reprK x}`. -/
noncomputable def chiFun (S : Finset (ULift.{u} (Fin n)))
    (x : ↥(Work.DSCOH.degZero (A := R) (n := n) (M := ↥(reesM t)) (reesGr t)
      (S.image ULift.down))) : chartLoc t S :=
  chartVal t S (reprK t S x) (reesEps R (reprM t S x).1)

/-- **The value does not depend on the representative.**  If `m ∈ reesGr t (k · |S'|)` and
`x = m / X_{S'}^k`, then `chiFun x = eps m / t_S^k`. -/
lemma chiFun_apply_mk (S : Finset (ULift.{u} (Fin n)))
    (x : ↥(Work.DSCOH.degZero (A := R) (n := n) (M := ↥(reesM t)) (reesGr t)
      (S.image ULift.down))) {k : ℕ} {m : ↥(reesM t)}
    (hm : m ∈ reesGr t (k * (S.image ULift.down).card))
    (hx : x.1 = Work.DSCOH.divPow (A := R) (n := n) (M := ↥(reesM t)) (S.image ULift.down) k
      (Work.DSCOH.toLoc (A := R) (n := n) (M := ↥(reesM t)) (S.image ULift.down) m)) :
    chiFun t S x = chartVal t S k (reesEps R m.1) := by
  obtain ⟨hKmem, hKx⟩ := repr_spec t S x
  have heq : Work.DSCOH.divPow (A := R) (n := n) (M := ↥(reesM t)) (S.image ULift.down)
        (reprK t S x) (Work.DSCOH.toLoc (A := R) (n := n) (M := ↥(reesM t))
          (S.image ULift.down) (reprM t S x)) =
      Work.DSCOH.divPow (A := R) (n := n) (M := ↥(reesM t)) (S.image ULift.down) k
        (Work.DSCOH.toLoc (A := R) (n := n) (M := ↥(reesM t)) (S.image ULift.down) m) :=
    hKx.symm.trans hx
  rw [Work.DSCOH.divPow_toLoc_mk_general (A := R) (n := n) (M := ↥(reesM t)),
    Work.DSCOH.divPow_toLoc_mk_general (A := R) (n := n) (M := ↥(reesM t))] at heq
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp heq
  obtain ⟨e, hsupp, hue⟩ := Work.DSCOH.lmb_subS_eq_xpow (A := R) (n := n)
    (S.image ULift.down) u
  have hsupp' : ∀ i : Fin n, (⟨i⟩ : ULift.{u} (Fin n)) ∉ S → e i = 0 :=
    fun i hi => hsupp i (fun hc => hi (by
      obtain ⟨a, ha, ha'⟩ := Finset.mem_image.mp hc
      rw [← ULift.down_injective ha'.symm] at ha
      exact ha))
  have hpoly : reesPhi t (Work.DSCOH.xpow (A := R) e) *
      (reesPhi t ((Work.DSCOH.monomial (A := R) (S.image ULift.down)) ^ k) *
        (reprM t S x).1) =
      reesPhi t (Work.DSCOH.xpow (A := R) e) *
      (reesPhi t ((Work.DSCOH.monomial (A := R) (S.image ULift.down)) ^ (reprK t S x)) *
        m.1) := by
    have h := congrArg Subtype.val hu
    simp only [Work.DSM5b.HCF.reesM_smul_coe, Submonoid.smul_def, hue] at h
    simpa using h
  have heps : (∏ i : Fin n, t i ^ e i) *
        (((∏ i ∈ S.image ULift.down, t i) ^ k) * reesEps R (reprM t S x).1) =
      (∏ i : Fin n, t i ^ e i) *
        (((∏ i ∈ S.image ULift.down, t i) ^ (reprK t S x)) * reesEps R m.1) := by
    have h := congrArg (reesEps R) hpoly
    simp only [map_mul] at h
    rw [reesEps_reesPhi, reesEps_reesPhi, reesEps_reesPhi] at h
    simp only [map_pow, aeval_monomial_t, Work.DSCOH.xpow, map_prod, MvPolynomial.aeval_X] at h
    simpa using h
  rw [chiFun, chartVal, chartVal]
  rw [IsLocalization.mk'_eq_iff_eq']
  rw [IsLocalization.eq_iff_exists (Submonoid.powers (DSMap.Mix2.tS (tU t) S)) (chartLoc t S)]
  refine ⟨⟨(DSMap.Mix2.tS (tU t) S) ^ (∑ i, e i),
    Submonoid.pow_mem _ (Submonoid.mem_powers _) _⟩, ?_⟩
  show (DSMap.Mix2.tS (tU t) S) ^ (∑ i, e i) *
      (reesEps R (reprM t S x).1 * (DSMap.Mix2.tS (tU t) S) ^ k) =
    (DSMap.Mix2.tS (tU t) S) ^ (∑ i, e i) *
      (reesEps R m.1 * (DSMap.Mix2.tS (tU t) S) ^ (reprK t S x))
  rw [tS_pow_eq_prod t S e hsupp', tS_tU]
  calc (∏ i ∈ S, tU t i ^ (∑ j, e j - e i.down)) *
        (∏ i : Fin n, t i ^ e i) * (reesEps R (reprM t S x).1 * (∏ i ∈ S.image ULift.down, t i) ^ k)
      = (∏ i ∈ S, tU t i ^ (∑ j, e j - e i.down)) *
        ((∏ i : Fin n, t i ^ e i) *
          ((∏ i ∈ S.image ULift.down, t i) ^ k * reesEps R (reprM t S x).1)) := by ring
    _ = (∏ i ∈ S, tU t i ^ (∑ j, e j - e i.down)) *
        ((∏ i : Fin n, t i ^ e i) *
          ((∏ i ∈ S.image ULift.down, t i) ^ (reprK t S x) * reesEps R m.1)) := by rw [heps]
    _ = (∏ i ∈ S, tU t i ^ (∑ j, e j - e i.down)) *
        (∏ i : Fin n, t i ^ e i) * (reesEps R m.1 * (∏ i ∈ S.image ULift.down, t i) ^ (reprK t S x)) := by ring


lemma isHomog_monomial (T : Finset (Fin n)) :
    (Work.DSCOH.monomial (A := R) T).IsHomogeneous T.card := by
  rw [Work.DSCOH.monomial]
  simpa using MvPolynomial.IsHomogeneous.prod T
    (fun i => (MvPolynomial.X i : Work.DSCOH.Poly R n)) (fun _ => 1)
    (fun i _ => MvPolynomial.isHomogeneous_X R i)

lemma isHomog_monomial_pow (T : Finset (Fin n)) (m : ℕ) :
    ((Work.DSCOH.monomial (A := R) T) ^ m).IsHomogeneous (m * T.card) := by
  induction m with
  | zero => simpa using MvPolynomial.isHomogeneous_one (σ := Fin n) (R := R)
  | succ m ih =>
      rw [pow_succ, Nat.succ_mul]
      exact ih.mul (isHomog_monomial T)

/-- `chartVal S (k + j) (t_S^j * c) = chartVal S k c` (raising the index). -/
lemma chartVal_pad (S : Finset (ULift.{u} (Fin n))) (k j : ℕ) (c : R) :
    chartVal t S (k + j) ((DSMap.Mix2.tS (tU t) S) ^ j * c) = chartVal t S k c := by
  rw [chartVal, chartVal, IsLocalization.mk'_eq_iff_eq']
  simp only [Submonoid.coe_mul, Subtype.coe_mk]
  congr 1
  ring

/-- The index-`0` fraction `c/1` is the image of the scalar `c`. -/
lemma chartVal_zero_index (S : Finset (ULift.{u} (Fin n))) (c : R) :
    chartVal t S 0 c = algebraMap R (chartLoc t S) c := by
  rw [chartVal, show (⟨(DSMap.Mix2.tS (tU t) S) ^ 0,
      Submonoid.pow_mem _ (Submonoid.mem_powers _) 0⟩ : Submonoid.powers _) = 1 from
    Subtype.ext (pow_zero _), IsLocalization.mk'_one]

/-- Multiplication of a chart fraction by a scalar of `R`. -/
lemma chartVal_mul_algebraMap (S : Finset (ULift.{u} (Fin n))) (k : ℕ) (c x : R) :
    chartVal t S k c * algebraMap R (chartLoc t S) x = chartVal t S k (c * x) := by
  rw [← chartVal_zero_index t S x, chartVal_mul, Nat.add_zero]

/-- `reesEps` of the `j`-th power of the monomial `X_T`. -/
lemma reesEps_reesPhi_monomial_pow (T : Finset (Fin n)) (j : ℕ) :
    reesEps R (reesPhi t ((Work.DSCOH.monomial (A := R) T) ^ j)) = (∏ i ∈ T, t i) ^ j := by
  rw [map_pow, map_pow, reesEps_reesPhi, aeval_monomial_t]

/-- **Additivity of `chiFun` on `degZero`.** -/
lemma chiFun_add (S : Finset (ULift.{u} (Fin n)))
    (x y : ↥(Work.DSCOH.degZero (A := R) (n := n) (M := ↥(reesM t)) (reesGr t)
      (S.image ULift.down))) :
    chiFun t S (x + y) = chiFun t S x + chiFun t S y := by
  obtain ⟨kx, mx, hmx, hx⟩ := Work.DSCOH.degZero_exists_repr (A := R) (n := n)
    (M := ↥(reesM t)) (reesGr t) (S.image ULift.down) x.2
  obtain ⟨ky, my, hmy, hy⟩ := Work.DSCOH.degZero_exists_repr (A := R) (n := n)
    (M := ↥(reesM t)) (reesGr t) (S.image ULift.down) y.2
  have hxy : (x + y).1 = Work.DSCOH.divPow (A := R) (n := n) (M := ↥(reesM t))
      (S.image ULift.down) (kx + ky)
      (Work.DSCOH.toLoc (A := R) (n := n) (M := ↥(reesM t)) (S.image ULift.down)
        ((Work.DSCOH.monomial (A := R) (S.image ULift.down)) ^ ky • mx +
          (Work.DSCOH.monomial (A := R) (S.image ULift.down)) ^ kx • my)) := by
    rw [Submodule.coe_add, hx, hy, divPow_toLoc_add]
  have hmem : ((Work.DSCOH.monomial (A := R) (S.image ULift.down)) ^ ky • mx +
      (Work.DSCOH.monomial (A := R) (S.image ULift.down)) ^ kx • my)
      ∈ reesGr t ((kx + ky) * (S.image ULift.down).card) := by
    have hky : ((Work.DSCOH.monomial (A := R) (S.image ULift.down)) ^ ky)
        ∈ Work.DSCOH.homSub R n (ky * (S.image ULift.down).card) := by
      rw [Work.DSCOH.homSub]
      exact (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (isHomog_monomial_pow _ ky)
    have hkx : ((Work.DSCOH.monomial (A := R) (S.image ULift.down)) ^ kx)
        ∈ Work.DSCOH.homSub R n (kx * (S.image ULift.down).card) := by
      rw [Work.DSCOH.homSub]
      exact (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (isHomog_monomial_pow _ kx)
    have h1 := SetLike.GradedSMul.smul_mem hky hmx
    have h2 := SetLike.GradedSMul.smul_mem hkx hmy
    rw [show ky * (S.image ULift.down).card +ᵥ kx * (S.image ULift.down).card
        = (kx + ky) * (S.image ULift.down).card from by
      rw [vadd_eq_add]; ring] at h1
    rw [show kx * (S.image ULift.down).card +ᵥ ky * (S.image ULift.down).card
        = (kx + ky) * (S.image ULift.down).card from by
      rw [vadd_eq_add]; ring] at h2
    exact add_mem h1 h2
  rw [chiFun_apply_mk t S (x + y) hmem hxy, chiFun_apply_mk t S x hmx hx,
    chiFun_apply_mk t S y hmy hy]
  have hnum : reesEps R (((Work.DSCOH.monomial (A := R) (S.image ULift.down)) ^ ky • mx +
      (Work.DSCOH.monomial (A := R) (S.image ULift.down)) ^ kx • my).1)
      = (∏ i ∈ S.image ULift.down, t i) ^ ky * reesEps R mx.1 +
        (∏ i ∈ S.image ULift.down, t i) ^ kx * reesEps R my.1 := by
    rw [Submodule.coe_add, Work.DSM5b.HCF.reesM_smul_coe, Work.DSM5b.HCF.reesM_smul_coe,
      map_add, map_mul, map_mul, reesEps_reesPhi_monomial_pow, reesEps_reesPhi_monomial_pow]
  rw [hnum, ← chartVal_add, ← tS_tU t S, chartVal_pad t S kx ky,
    show kx + ky = ky + kx from Nat.add_comm _ _, chartVal_pad t S ky kx]

/-- **`R`-linearity of `chiFun`.** -/
lemma chiFun_smul (S : Finset (ULift.{u} (Fin n))) (r : R)
    (x : ↥(Work.DSCOH.degZero (A := R) (n := n) (M := ↥(reesM t)) (reesGr t)
      (S.image ULift.down))) :
    chiFun t S (r • x) = r • chiFun t S x := by
  obtain ⟨k, m, hm, hx⟩ := Work.DSCOH.degZero_exists_repr (A := R) (n := n)
    (M := ↥(reesM t)) (reesGr t) (S.image ULift.down) x.2
  have hsmul : (r • x).1 = Work.DSCOH.divPow (A := R) (n := n) (M := ↥(reesM t))
      (S.image ULift.down) k
      (Work.DSCOH.toLoc (A := R) (n := n) (M := ↥(reesM t)) (S.image ULift.down) (r • m)) := by
    rw [Submodule.coe_smul, hx, divPow_toLoc_smul]
  have hmem : r • m ∈ reesGr t (k * (S.image ULift.down).card) := Submodule.smul_mem _ r hm
  rw [chiFun_apply_mk t S (r • x) hmem hsmul, chiFun_apply_mk t S x hm hx,
    Submodule.coe_smul, Algebra.smul_def, Polynomial.algebraMap_eq, map_mul, reesEps_C]
  exact (chartVal_smul t S k r (reesEps R m.1)).symm

/-- The `R`-linear map `degZero (reesGr t) S' → R_{t_S}`, `x = m/X_S^k ↦ eps(m)/t_S^k`. -/
noncomputable def chiR (S : Finset (ULift.{u} (Fin n))) :
    ↥(Work.DSCOH.degZero (A := R) (n := n) (M := ↥(reesM t)) (reesGr t)
        (S.image ULift.down)) →ₗ[R] chartLoc t S where
  toFun := chiFun t S
  map_add' := chiFun_add t S
  map_smul' := chiFun_smul t S

lemma chiR_apply_mk (S : Finset (ULift.{u} (Fin n)))
    (x : ↥(Work.DSCOH.degZero (A := R) (n := n) (M := ↥(reesM t)) (reesGr t)
      (S.image ULift.down))) {k : ℕ} {m : ↥(reesM t)}
    (hm : m ∈ reesGr t (k * (S.image ULift.down).card))
    (hx : x.1 = Work.DSCOH.divPow (A := R) (n := n) (M := ↥(reesM t)) (S.image ULift.down) k
      (Work.DSCOH.toLoc (A := R) (n := n) (M := ↥(reesM t)) (S.image ULift.down) m)) :
    chiR t S x = chartVal t S k (reesEps R m.1) :=
  chiFun_apply_mk t S x hm hx

/-- The `Finsupp`-product of the `t i ^ a i` is the product over `ULift (Fin n)`. -/
lemma finsupp_prod_t (a : Fin n →₀ ℕ) :
    a.prod (fun i k => t i ^ k) = ∏ j : ULift.{u} (Fin n), (tU t) j ^ (a j.down) := by
  rw [Finsupp.prod]
  rw [Finset.prod_subset (Finset.subset_univ a.support) (fun x _ hx => by
    have h0 : a x = 0 := by
      by_contra h
      exact hx ((Finsupp.mem_support_iff (f := a)).mpr h)
    rw [h0, pow_zero])]
  rw [← Equiv.prod_comp Equiv.ulift (fun i : Fin n => t i ^ a i)]
  rfl

/-- The chart fraction `c / t_S^k` for `S = ∅` is the image of the scalar `c`. -/
lemma chartVal_empty_eq (k : ℕ) (c : R) :
    chartVal t (∅ : Finset (ULift.{u} (Fin n))) k c = algebraMap R (chartLoc t ∅) c := by
  rw [chartVal, show (⟨(DSMap.Mix2.tS (tU t) ∅) ^ k,
      Submonoid.pow_mem _ (Submonoid.mem_powers _) k⟩ :
      Submonoid.powers (DSMap.Mix2.tS (tU t) ∅)) = 1 from
    Subtype.ext (by simp [DSMap.Mix2.tS]), IsLocalization.mk'_one]

/-- If `S = ∅` then every chart fraction of index `k` lies in the chart ring. -/
lemma chartVal_mem_of_empty {S : Finset (ULift.{u} (Fin n))} (hS : S = ∅) (k : ℕ) (c : R) :
    chartVal t S k c ∈ DSMap.Mix2.chartRing (tU t) S := by
  subst hS
  rw [chartVal_empty_eq]
  exact Subalgebra.algebraMap_mem _ _

/-- **The value of `x ∈ degZero` lies in the chart ring.** -/
lemma chiR_mem (S : Finset (ULift.{u} (Fin n)))
    (x : ↥(Work.DSCOH.degZero (A := R) (n := n) (M := ↥(reesM t)) (reesGr t)
      (S.image ULift.down))) :
    chiR t S x ∈ DSMap.Mix2.chartRing (tU t) S := by
  obtain ⟨f, hf, hfe⟩ := mem_reesGr.mp (repr_spec t S x).1
  have hval : chiR t S x = chartVal t S (reprK t S x) (MvPolynomial.aeval t f) := by
    show chiFun t S x = _
    rw [chiFun, ← hfe, reesEps_reesPhi]
  rw [hval]
  have hsum : MvPolynomial.aeval t f =
      ∑ a ∈ f.support, f.coeff a * a.prod (fun i k => t i ^ k) := by
    conv_lhs => rw [MvPolynomial.as_sum f]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [MvPolynomial.aeval_monomial]
    simp
  rw [hsum, chartVal_sum]
  refine Subalgebra.sum_mem _ fun a ha => ?_
  have hdeg : ∑ i : Fin n, a i = reprK t S x * (S.image ULift.down).card :=
    Work.DSCOH.lmb_support_degree hf ha
  have hmem_a : chartVal t S (reprK t S x) (∏ j : ULift.{u} (Fin n), (tU t) j ^ (a j.down))
      ∈ DSMap.Mix2.chartRing (tU t) S := by
    by_cases hS : S.Nonempty
    · obtain ⟨i₀, hi₀⟩ := hS
      refine Work.DSM5b.HCF.prod_div_tS_mem_chartRing (tU t) hi₀ (reprK t S x)
        (fun j => a j.down) ?_
      have h1 : (∑ j : ULift.{u} (Fin n), a j.down) = ∑ i : Fin n, a i :=
        Equiv.sum_comp Equiv.ulift a
      rw [h1, hdeg, card_image_down]
    · rw [Finset.not_nonempty_iff_eq_empty] at hS
      subst hS
      have hsum0 : ∑ i : Fin n, a i = 0 := by
        rw [hdeg]; simp
      have ha0 : a = 0 := Finsupp.ext fun i =>
        Finset.sum_eq_zero_iff.mp hsum0 i (Finset.mem_univ i)
      rw [show (∏ j : ULift.{u} (Fin n), (tU t) j ^ (a j.down)) = 1 by
        rw [ha0]; simp]
      exact chartVal_mem_of_empty t rfl (reprK t (∅ : Finset (ULift.{u} (Fin n))) x) 1
  have hfac : chartVal t S (reprK t S x) (f.coeff a * a.prod (fun i k => t i ^ k)) =
      algebraMap R (chartLoc t S) (f.coeff a) *
        chartVal t S (reprK t S x) (a.prod (fun i k => t i ^ k)) := by
    rw [mul_comm (f.coeff a) (a.prod fun i k => t i ^ k),
      ← chartVal_mul_algebraMap, mul_comm]
  rw [hfac, finsupp_prod_t t a]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hmem_a

/-- The fraction `t_S / t_S` is `1`. -/
lemma chartVal_self (S : Finset (ULift.{u} (Fin n))) :
    chartVal t S 1 (DSMap.Mix2.tS (tU t) S) = 1 := by
  rw [chartVal, show (⟨(DSMap.Mix2.tS (tU t) S) ^ 1,
      Submonoid.pow_mem _ (Submonoid.mem_powers _) 1⟩ :
      Submonoid.powers (DSMap.Mix2.tS (tU t) S)) =
      ⟨DSMap.Mix2.tS (tU t) S, Submonoid.mem_powers _⟩ from Subtype.ext (pow_one _),
    IsLocalization.mk'_self]

/-- `c·t_S / t_S = c`. -/
lemma chartVal_one_index_mul_tS (S : Finset (ULift.{u} (Fin n))) (c : R) :
    chartVal t S 1 (c * DSMap.Mix2.tS (tU t) S) = algebraMap R (chartLoc t S) c := by
  rw [show (1 : ℕ) = 0 + 1 from (zero_add 1).symm, ← chartVal_mul, chartVal_zero_index,
    chartVal_self, mul_one]

/-- **The value map, restricted to the chart ring.** -/
noncomputable def chiC (S : Finset (ULift.{u} (Fin n))) :
    ↥(Work.DSCOH.degZero (A := R) (n := n) (M := ↥(reesM t)) (reesGr t)
        (S.image ULift.down)) →ₗ[R] ↥(DSMap.Mix2.chartRing (tU t) S) :=
  LinearMap.codRestrict (DSMap.Mix2.chartRing (tU t) S).toSubmodule (chiR t S) (chiR_mem t S)

@[simp] lemma chiC_coe (S : Finset (ULift.{u} (Fin n)))
    (x : ↥(Work.DSCOH.degZero (A := R) (n := n) (M := ↥(reesM t)) (reesGr t)
      (S.image ULift.down))) :
    ((chiC t S x : ↥(DSMap.Mix2.chartRing (tU t) S)) : chartLoc t S) = chiR t S x := by
  rw [chiC, LinearMap.codRestrict_apply]

/-- The preimage of the scalar `r` under `chiR`. -/
lemma chiR_algebraMap (S : Finset (ULift.{u} (Fin n))) (r : R) :
    ∃ x, chiR t S x = algebraMap R (chartLoc t S) r := by
  have hgen : reesGen t ∈ reesGr t (0 * (S.image ULift.down).card) := by
    rw [zero_mul]
    refine mem_reesGr.mpr ⟨1, ?_, ?_⟩
    · rw [Work.DSCOH.homSub]
      exact (MvPolynomial.mem_homogeneousSubmodule 0 _).mpr
        (MvPolynomial.isHomogeneous_one (σ := Fin n) (R := R))
    · rw [map_one]; rfl
  refine ⟨⟨Work.DSCOH.divPow (A := R) (n := n) (M := ↥(reesM t)) (S.image ULift.down) 0
      (Work.DSCOH.toLoc (A := R) (n := n) (M := ↥(reesM t)) (S.image ULift.down)
        (r • reesGen t)),
      Work.DSCOH.divPow_toLoc_mem (A := R) (n := n) (M := ↥(reesM t)) (reesGr t)
        (S.image ULift.down) 0 (Submodule.smul_mem _ r hgen)⟩, ?_⟩
  rw [chiR_apply_mk t S _ (Submodule.smul_mem _ r hgen) rfl, Submodule.coe_smul,
    Algebra.smul_def, Polynomial.algebraMap_eq, map_mul, reesEps_C, reesGen_coe, map_one,
    mul_one, chartVal_zero_index]

/-- The preimage of a generator `y` of `chartGens (tU t) S`. -/
lemma chiR_chartGens (S : Finset (ULift.{u} (Fin n))) {g : chartLoc t S}
    (hg : g ∈ DSMap.Mix2.chartGens (tU t) S) :
    ∃ x, chiR t S x = g := by
  obtain ⟨i, hi, k, hgk⟩ := hg
  have hmem_i : i.down ∈ S.image ULift.down := Finset.mem_image_of_mem ULift.down hi
  set T : Finset (Fin n) := S.image ULift.down \ {i.down} with hT
  set f : Work.DSCOH.Poly R n := MvPolynomial.X k.down * Work.DSCOH.monomial (A := R) T with hf
  have hcard : T.card = (S.image ULift.down).card - 1 := by
    rw [hT, Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hmem_i]
  have hpos : 0 < (S.image ULift.down).card := Finset.card_pos.mpr ⟨i.down, hmem_i⟩
  have hfmem : f ∈ Work.DSCOH.homSub R n (S.image ULift.down).card := by
    rw [Work.DSCOH.homSub, MvPolynomial.mem_homogeneousSubmodule, hf]
    have h1 : (MvPolynomial.X k.down : Work.DSCOH.Poly R n).IsHomogeneous 1 :=
      MvPolynomial.isHomogeneous_X R k.down
    have h2 := h1.mul (isHomog_monomial T)
    have h3 : 1 + T.card = (S.image ULift.down).card := by rw [hcard]; omega
    rwa [h3] at h2
  have hprod_erase : (∏ j ∈ T, t j) * (tU t i) = DSMap.Mix2.tS (tU t) S := by
    have h := Finset.prod_erase_mul (S.image ULift.down) t hmem_i
    rw [tS_tU]
    rw [hT, Finset.sdiff_singleton_eq_erase]
    exact h
  have hm : (⟨reesPhi t f, mem_reesM.mpr ⟨f, rfl⟩⟩ : ↥(reesM t))
      ∈ reesGr t (1 * (S.image ULift.down).card) :=
    mem_reesGr.mpr ⟨f, by rwa [one_mul], rfl⟩
  refine ⟨⟨Work.DSCOH.divPow (A := R) (n := n) (M := ↥(reesM t)) (S.image ULift.down) 1
      (Work.DSCOH.toLoc (A := R) (n := n) (M := ↥(reesM t)) (S.image ULift.down)
        ⟨reesPhi t f, mem_reesM.mpr ⟨f, rfl⟩⟩),
      Work.DSCOH.divPow_toLoc_mem (A := R) (n := n) (M := ↥(reesM t)) (reesGr t)
        (S.image ULift.down) 1 hm⟩, ?_⟩
  rw [chiR_apply_mk t S _ hm rfl]
  have hfval : reesEps R (reesPhi t f) = t k.down * ∏ j ∈ T, t j := by
    rw [hf, reesEps_reesPhi, map_mul, MvPolynomial.aeval_X, aeval_monomial_t]
  rw [hfval]
  have hu : IsUnit (algebraMap R (chartLoc t S) (tU t i)) :=
    IsLocalization.Away.isUnit_of_dvd (DSMap.Mix2.tS (tU t) S)
      (Finset.dvd_prod_of_mem (tU t) hi)
  refine hu.mul_right_cancel ?_
  have key : chartVal t S 1 (t k.down * ∏ j ∈ T, t j) *
      algebraMap R (chartLoc t S) (tU t i) = algebraMap R (chartLoc t S) (tU t k) := by
    rw [chartVal_mul_algebraMap t S 1 (t k.down * ∏ j ∈ T, t j) (tU t i), mul_assoc,
      hprod_erase, chartVal_one_index_mul_tS]
    rfl
  rw [key]
  exact hgk.symm

/-- **The chart ring is the range of `chiR`.** -/
lemma chartRing_le_range (S : Finset (ULift.{u} (Fin n))) :
    ∀ y ∈ DSMap.Mix2.chartRing (tU t) S, y ∈ Set.range (chiR t S) := by
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem x hx => exact chiR_chartGens t S hx
  | algebraMap r => exact chiR_algebraMap t S r
  | add x y hx hy ihx ihy =>
      obtain ⟨x', hx'⟩ := ihx
      obtain ⟨y', hy'⟩ := ihy
      exact ⟨x' + y', by rw [map_add, hx', hy']⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨x', hx'⟩ := ihx
      obtain ⟨y', hy'⟩ := ihy
      obtain ⟨k, m, hm, hxr⟩ := Work.DSCOH.degZero_exists_repr (A := R) (n := n)
        (M := ↥(reesM t)) (reesGr t) (S.image ULift.down) x'.2
      obtain ⟨l, n', hn', hyr⟩ := Work.DSCOH.degZero_exists_repr (A := R) (n := n)
        (M := ↥(reesM t)) (reesGr t) (S.image ULift.down) y'.2
      obtain ⟨f, hf, hfe⟩ := mem_reesGr.mp hm
      obtain ⟨g, hg, hge⟩ := mem_reesGr.mp hn'
      have hmul_mem : m.1 * n'.1 ∈ reesM t :=
        LinearMap.mem_range.mpr ⟨f * g, by
          simp only [AlgHom.toLinearMap_apply, map_mul, hfe, hge]⟩
      have hm2mem : (⟨m.1 * n'.1, hmul_mem⟩ : ↥(reesM t))
          ∈ reesGr t ((k + l) * (S.image ULift.down).card) := by
        refine mem_reesGr.mpr ⟨f * g, ?_, by rw [map_mul, hfe, hge]⟩
        rw [Work.DSCOH.homSub, MvPolynomial.mem_homogeneousSubmodule] at hf hg ⊢
        have h := hf.mul hg
        rwa [show k * (S.image ULift.down).card + l * (S.image ULift.down).card
            = (k + l) * (S.image ULift.down).card from by ring] at h
      refine ⟨⟨Work.DSCOH.divPow (A := R) (n := n) (M := ↥(reesM t)) (S.image ULift.down)
          (k + l) (Work.DSCOH.toLoc (A := R) (n := n) (M := ↥(reesM t))
            (S.image ULift.down) ⟨m.1 * n'.1, hmul_mem⟩),
          Work.DSCOH.divPow_toLoc_mem (A := R) (n := n) (M := ↥(reesM t)) (reesGr t)
            (S.image ULift.down) (k + l) hm2mem⟩, ?_⟩
      rw [chiR_apply_mk t S _ hm2mem rfl, ← hx', ← hy', chiR_apply_mk t S x' hm hxr,
        chiR_apply_mk t S y' hn' hyr]
      show chartVal t S (k + l) (reesEps R (m.1 * n'.1)) =
        chartVal t S k (reesEps R m.1) * chartVal t S l (reesEps R n'.1)
      rw [map_mul, ← chartVal_mul]

/-- **Surjectivity** of the value map onto the chart ring. -/
lemma chiC_surjective (S : Finset (ULift.{u} (Fin n))) :
    Function.Surjective (chiC t S) := by
  intro y
  obtain ⟨x, hx⟩ := chartRing_le_range t S (y : chartLoc t S) y.2
  exact ⟨x, Subtype.ext (by rw [chiC_coe]; exact hx)⟩

/-- A nonzero element of `reesGr` has nonzero `reesEps`; hence `reesEps = 0` forces it to vanish. -/
lemma eq_zero_of_reesEps_eq_zero {d : ℕ} {m : ↥(reesM t)} (hm : m ∈ reesGr t d)
    (h : reesEps R m.1 = 0) : m = 0 := by
  obtain ⟨c, hc, hcx⟩ := (reesGr_mem_iff t d m).mp hm
  have hc0 : c = 0 := by
    rw [hcx, reesEps_C_mul_X_pow] at h
    exact h
  rw [Subtype.ext_iff, hcx, hc0, map_zero, zero_mul, Submodule.coe_zero]

/-- **Injectivity** of the value map. -/
lemma chiR_eq_zero {S : Finset (ULift.{u} (Fin n))}
    {x : ↥(Work.DSCOH.degZero (A := R) (n := n) (M := ↥(reesM t)) (reesGr t)
      (S.image ULift.down))} (hx : chiR t S x = 0) : x = 0 := by
  obtain ⟨k, m, hm, hx'⟩ := Work.DSCOH.degZero_exists_repr (A := R) (n := n)
    (M := ↥(reesM t)) (reesGr t) (S.image ULift.down) x.2
  have h1 : chartVal t S k (reesEps R m.1) = 0 := by
    rw [← chiR_apply_mk t S x hm hx']; exact hx
  rw [chartVal] at h1
  rw [IsLocalization.mk'_eq_zero_iff] at h1
  obtain ⟨u, hu⟩ := h1
  obtain ⟨N, hN⟩ := u.2
  have hN' : (DSMap.Mix2.tS (tU t) S) ^ N = (u : R) := by
    simpa using hN
  have hu' : (DSMap.Mix2.tS (tU t) S) ^ N * reesEps R m.1 = 0 := by
    rw [hN']; exact hu
  obtain ⟨f, hf, hfe⟩ := mem_reesGr.mp hm
  have hmemN : ((Work.DSCOH.monomial (A := R) (S.image ULift.down)) ^ N) • m
      ∈ reesGr t ((N + k) * (S.image ULift.down).card) := by
    have h1 : ((Work.DSCOH.monomial (A := R) (S.image ULift.down)) ^ N)
        ∈ Work.DSCOH.homSub R n (N * (S.image ULift.down).card) := by
      rw [Work.DSCOH.homSub]
      exact (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (isHomog_monomial_pow _ N)
    have h2 := SetLike.GradedSMul.smul_mem h1 hm
    rw [show N * (S.image ULift.down).card +ᵥ k * (S.image ULift.down).card
        = (N + k) * (S.image ULift.down).card from by
      rw [vadd_eq_add]; ring] at h2
    exact h2
  have heps0 : reesEps R (((Work.DSCOH.monomial (A := R) (S.image ULift.down)) ^ N) • m).1
      = 0 := by
    rw [Work.DSM5b.HCF.reesM_smul_coe, map_mul, reesEps_reesPhi_monomial_pow, ← tS_tU, hu']
  have hkill : ((Work.DSCOH.monomial (A := R) (S.image ULift.down)) ^ N) • m = 0 :=
    eq_zero_of_reesEps_eq_zero t hmemN heps0
  have hz : Work.DSCOH.toLoc (A := R) (n := n) (M := ↥(reesM t)) (S.image ULift.down) m = 0 := by
    rw [toLoc_eq_zero_iff]
    refine ⟨⟨(Work.DSCOH.monomial (A := R) (S.image ULift.down)) ^ N,
      Submonoid.pow_mem _ (Work.DSCOH.monomial_mem _) N⟩, ?_⟩
    rw [Submonoid.smul_def]
    simpa using hkill
  rw [Subtype.ext_iff, hx', hz, map_zero, Submodule.coe_zero]

lemma chiR_injective (S : Finset (ULift.{u} (Fin n))) : Function.Injective (chiR t S) := by
  intro x y hxy
  have h : chiR t S (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have h' := chiR_eq_zero t h
  rw [sub_eq_zero] at h'
  exact h'

lemma chiC_injective (S : Finset (ULift.{u} (Fin n))) : Function.Injective (chiC t S) := by
  intro x y hxy
  apply chiR_injective t S
  have := congrArg (fun z : ↥(DSMap.Mix2.chartRing (tU t) S) => (z : chartLoc t S)) hxy
  simpa using this



end Core

end Work.DSM5b.HCF
