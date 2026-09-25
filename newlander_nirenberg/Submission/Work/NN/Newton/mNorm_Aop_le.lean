import Mathlib
import Submission.Work.NN.Newton.pushforward_setup
import Submission.Work.NN.Newton.pushforward_norms
import Submission.Work.NN.Newton.Minv_holderNorm_one_le
import Submission.Work.NN.Newton.holderNorm_one_fderiv_coeff_le
import Submission.Work.NN.Newton.Bop_eq_identity
import Submission.Work.NN.Newton.EVec_eq
import Submission.Work.NN.Newton.DvCLM_data_le
import Submission.Work.NN.Newton.contDiffOn_Aop
import Submission.Work.NN.Newton.AopAux.mNorm_le_two_vNorm_basis
import Submission.Work.NN.Newton.AopAux.vNorm_clm_apply_le
import Submission.Work.NN.Newton.AopAux.mNorm_DvCLM_le
import Submission.Work.NN.Newton.AopAux.vNorm_Minv_le
import Submission.Work.NN.Newton.AopAux.vNorm_EVec_le

set_option maxHeartbeats 4000000

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Newton

/-! ## Algebra: the `Bop` evaluations on the standard real basis -/

lemma conjC_single {n : ℕ} (j k : Fin n) :
    (conjC n k) (Pi.single j (1:ℂ)) = (if k = j then (1:ℂ) else 0) := by
  rw [conjC_apply]; by_cases h : k = j
  · subst h; simp
  · simp [h]

lemma conjC_single_I {n : ℕ} (j k : Fin n) :
    (conjC n k) (Pi.single j (Complex.I:ℂ)) = (if k = j then -Complex.I else 0) := by
  rw [conjC_apply]; by_cases h : k = j
  · subst h; simp
  · simp [h]

lemma sum_smulRight_single {n : ℕ} (V : Fin n → Core.Cn n) (j : Fin n) :
    (∑ k, (conjC n k).smulRight (V k)) (Pi.single j 1) = V j := by
  rw [ContinuousLinearMap.sum_apply, Finset.sum_eq_single j]
  · rw [ContinuousLinearMap.smulRight_apply, conjC_single j j]; simp
  · intro k _ hk; rw [ContinuousLinearMap.smulRight_apply, conjC_single j k, if_neg hk, zero_smul]
  · intro hj; exact absurd (Finset.mem_univ j) hj

lemma sum_smulRight_single_I {n : ℕ} (V : Fin n → Core.Cn n) (j : Fin n) :
    (∑ k, (conjC n k).smulRight (V k)) (Pi.single j (Complex.I:ℂ)) = -Complex.I • V j := by
  rw [ContinuousLinearMap.sum_apply, Finset.sum_eq_single j]
  · rw [ContinuousLinearMap.smulRight_apply, conjC_single_I j j]; simp
  · intro k _ hk; rw [ContinuousLinearMap.smulRight_apply, conjC_single_I j k, if_neg hk, zero_smul]
  · intro hj; exact absurd (Finset.mem_univ j) hj

lemma Bop_apply_single {n : ℕ} (A : Core.Cn n → Core.Cn n →L[ℝ] Core.Cn n)
    (v : Fin n → Core.Cn n → ℂ) (j : Fin n) (z : Core.Cn n)
    (hAC : ∀ u : Core.Cn n, (Core.JstdCn n + A) z ((Core.JstdCn n + A) z u) = -u) :
    Bop A v z (Pi.single j 1)
      = (-(2 * Complex.I)) • EVec A v j z - DvCLM v z (A z (Pi.single j 1)) := by
  rw [Bop_eq_identity A v z hAC]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  rw [sum_smulRight_single (fun k => (Alin A z) (Pi.single k 1)) j,
    sum_smulRight_single (EVec A v · z) j]
  simp only [smul_smul, Complex.I_sq, one_smul, neg_smul]
  abel

lemma Bop_apply_single_I {n : ℕ} (A : Core.Cn n → Core.Cn n →L[ℝ] Core.Cn n)
    (v : Fin n → Core.Cn n → ℂ) (j : Fin n) (z : Core.Cn n)
    (hAC : ∀ u : Core.Cn n, (Core.JstdCn n + A) z ((Core.JstdCn n + A) z u) = -u) :
    Bop A v z (Pi.single j (Complex.I:ℂ))
      = Alin A z (Pi.single j (Complex.I:ℂ)) + Complex.I • Alin A z (Pi.single j 1)
        + (-(2:ℂ)) • EVec A v j z - DvCLM v z (A z (Pi.single j (Complex.I:ℂ))) := by
  rw [Bop_eq_identity A v z hAC]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  rw [sum_smulRight_single_I (fun k => (Alin A z) (Pi.single k 1)) j,
    sum_smulRight_single_I (EVec A v · z) j]
  simp only [neg_smul, smul_neg, smul_smul, one_smul]
  rw [show (2:ℂ) * Complex.I * Complex.I = -2 by
    rw [mul_assoc, Complex.I_mul_I]; norm_num]
  simp only [neg_smul, neg_neg, one_smul]
  abel

/-! ## An ENNReal arithmetic helper -/

lemma sum_le_ofReal_card {ι : Type*} [Fintype ι] {K : ℝ} (hK : 0 ≤ K)
    {f : ι → ENNReal} (h : ∀ i, f i ≤ ENNReal.ofReal K) :
    ∑ i, f i ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * K) := by
  have h1 : ∑ i, f i ≤ ∑ _i : ι, ENNReal.ofReal K := Finset.sum_le_sum fun i _ => h i
  rw [Finset.sum_const, Finset.card_univ] at h1
  refine h1.trans ?_
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

/-! ## An arithmetic helper -/

lemma two_mul_ofReal_add_self {x : ℝ} (hx : 0 ≤ x) :
    (2 : ENNReal) * (ENNReal.ofReal x + ENNReal.ofReal x) = ENNReal.ofReal (4 * x) := by
  rw [← ENNReal.ofReal_add hx hx, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

/-! ## Bounds for the perturbation `A` itself -/

lemma vNorm_A_basis_le {n : ℕ} {α a R r : ℝ} (ha0 : 0 ≤ a) (hsub : R ≤ r)
    {A : Core.Cn n → Core.Cn n →L[ℝ] Core.Cn n}
    (haA : ∀ w : Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z => A z w j) (Pd n r) ≤ ENNReal.ofReal a)
    (j : Fin n) :
    vNorm 1 α (fun z => A z (Pi.single j 1)) (Pd n R) ≤ ENNReal.ofReal ((n : ℝ) * a) := by
  rw [vNorm]
  have hmem : Pd n R ⊆ Pd n r := Pd_mono hsub
  have h1 : ∀ m : Fin n, Work.CR.Flat.holderNorm 1 α (fun z => A z (Pi.single j 1) m) (Pd n R)
      ≤ ENNReal.ofReal a := fun m =>
    (Work.CR.Flat.holderNorm_mono_set (isOpen_Pd n r) (isOpen_Pd n R) hmem 1 α
      (fun z => A z (Pi.single j 1) m)).trans
      (haA _ (by rw [Pi.norm_single]; norm_num) m)
  calc ∑ m, Work.CR.Flat.holderNorm 1 α (fun z => A z (Pi.single j 1) m) (Pd n R)
      ≤ ∑ _m : Fin n, ENNReal.ofReal a := Finset.sum_le_sum fun m _ => h1 m
    _ = ENNReal.ofReal ((n : ℝ) * a) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]

lemma vNorm_A_basisI_le {n : ℕ} {α a R r : ℝ} (ha0 : 0 ≤ a) (hsub : R ≤ r)
    {A : Core.Cn n → Core.Cn n →L[ℝ] Core.Cn n}
    (haA : ∀ w : Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z => A z w j) (Pd n r) ≤ ENNReal.ofReal a)
    (j : Fin n) :
    vNorm 1 α (fun z => A z (Pi.single j (Complex.I:ℂ))) (Pd n R)
      ≤ ENNReal.ofReal ((n : ℝ) * a) := by
  rw [vNorm]
  have hmem : Pd n R ⊆ Pd n r := Pd_mono hsub
  have h1 : ∀ m : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z => A z (Pi.single j (Complex.I:ℂ)) m) (Pd n R)
      ≤ ENNReal.ofReal a := fun m =>
    (Work.CR.Flat.holderNorm_mono_set (isOpen_Pd n r) (isOpen_Pd n R) hmem 1 α
      (fun z => A z (Pi.single j (Complex.I:ℂ)) m)).trans
      (haA _ (by rw [Pi.norm_single, Complex.norm_I]) m)
  calc ∑ m, Work.CR.Flat.holderNorm 1 α (fun z => A z (Pi.single j (Complex.I:ℂ)) m) (Pd n R)
      ≤ ∑ _m : Fin n, ENNReal.ofReal a := Finset.sum_le_sum fun m _ => h1 m
    _ = ENNReal.ofReal ((n : ℝ) * a) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]

lemma mNorm_A_le {n : ℕ} {α a R r : ℝ} (ha0 : 0 ≤ a) (hsub : R ≤ r)
    (hΩ : UniqueDiffOn ℝ (Pd n R)) {A : Core.Cn n → Core.Cn n →L[ℝ] Core.Cn n}
    (hAcd : ContDiffOn ℝ 1 A (Pd n R))
    (haA : ∀ w : Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z => A z w j) (Pd n r) ≤ ENNReal.ofReal a) :
    mNorm 1 α A (Pd n R) ≤ ENNReal.ofReal (4 * (n : ℝ) ^ 2 * a) := by
  have hna : (0 : ℝ) ≤ (n : ℝ) * a := mul_nonneg (Nat.cast_nonneg _) ha0
  have h1 : (∑ j, vNorm 1 α (fun z => A z (Pi.single j 1)) (Pd n R))
      ≤ ENNReal.ofReal ((n : ℝ) * ((n : ℝ) * a)) := by
    simpa only [Fintype.card_fin] using
      (sum_le_ofReal_card (ι := Fin n) hna (fun j => vNorm_A_basis_le ha0 hsub haA j))
  have h2 : (∑ j, vNorm 1 α (fun z => A z (Pi.single j (Complex.I:ℂ))) (Pd n R))
      ≤ ENNReal.ofReal ((n : ℝ) * ((n : ℝ) * a)) := by
    simpa only [Fintype.card_fin] using
      (sum_le_ofReal_card (ι := Fin n) hna (fun j => vNorm_A_basisI_le ha0 hsub haA j))
  refine (AopAux.mNorm_le_two_vNorm_basis hΩ hAcd h1 h2).trans ?_
  have hK : (0:ℝ) ≤ (n:ℝ) * ((n:ℝ)*a) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ha0)
  have hL : (2 : ENNReal) * (ENNReal.ofReal ((n:ℝ) * ((n:ℝ) * a))
        + ENNReal.ofReal ((n:ℝ) * ((n:ℝ) * a))) = ENNReal.ofReal (4 * ((n:ℝ) * ((n:ℝ) * a))) :=
    two_mul_ofReal_add_self hK
  rw [hL]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

/-! ## Smoothness and norm bounds for the pieces of `Bop` -/

lemma ofReal_mul_le_of_le {p q : ℝ} (hp : 0 ≤ p) {u v : ENNReal}
    (hu : u ≤ ENNReal.ofReal p) (hv : v ≤ ENNReal.ofReal q) :
    u * v ≤ ENNReal.ofReal (p * q) :=
  (mul_le_mul' hu hv).trans (le_of_eq (ENNReal.ofReal_mul hp).symm)

lemma contDiffOn_clm_apply_components {n : ℕ} {k : ℕ} {Ω : Set (Core.Cn n)}
    {T : Core.Cn n → Core.Cn n →L[ℝ] Core.Cn n} {F : Core.Cn n → Core.Cn n}
    (hT : ContDiffOn ℝ k T Ω) (hF : ∀ p, ContDiffOn ℝ k (fun z => F z p) Ω) :
    ∀ p, ContDiffOn ℝ k (fun z => (T z (F z)) p) Ω := by
  have hFvec : ContDiffOn ℝ k F Ω := contDiffOn_pi.2 hF
  have hmain : ContDiffOn ℝ k (fun z => T z (F z)) Ω := hT.clm_apply hFvec
  intro p
  exact (ContinuousLinearMap.proj p : Core.Cn n →L[ℝ] ℂ).contDiff.comp_contDiffOn hmain

/-- `A z (A z e_j)` has `vNorm` at most `32 n^4 a^2`. -/
lemma vNorm_A_compA_le {n : ℕ} {α a R r : ℝ} (ha0 : 0 ≤ a) (hsub : R ≤ r)
    (hΩ : UniqueDiffOn ℝ (Pd n R)) {A : Core.Cn n → Core.Cn n →L[ℝ] Core.Cn n}
    (hAcd : ContDiffOn ℝ 1 A (Pd n R))
    (haA : ∀ w : Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z => A z w j) (Pd n r) ≤ ENNReal.ofReal a)
    (j : Fin n) :
    vNorm 1 α (fun z => A z (A z (Pi.single j 1))) (Pd n R)
      ≤ ENNReal.ofReal (32 * (n:ℝ)^4 * a^2) := by
  have hMA := mNorm_A_le (n:=n) ha0 hsub hΩ hAcd haA
  have hva := vNorm_A_basis_le (n:=n) ha0 hsub haA j
  have hFe : ∀ p, ContDiffOn ℝ 1 (fun z => (A z (Pi.single j 1)) p) (Pd n R) :=
    fun p => contDiffOn_clm_component hAcd (Pi.single j 1) p
  have hTfin : mNorm 1 α A (Pd n R) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hMA
  have hFfin : vNorm 1 α (fun z => A z (Pi.single j 1)) (Pd n R) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hva
  refine (AopAux.vNorm_clm_apply_le hΩ hAcd hFe hTfin hFfin).trans ?_
  have h1 := ofReal_mul_le_of_le (p := 4*(n:ℝ)^2*a) (by positivity) hMA hva
  calc ENNReal.ofReal (8*(n:ℝ)) * (mNorm 1 α A (Pd n R)
        * vNorm 1 α (fun z => A z (Pi.single j 1)) (Pd n R))
      ≤ ENNReal.ofReal (8*(n:ℝ)) * ENNReal.ofReal ((4*(n:ℝ)^2*a) * ((n:ℝ)*a)) :=
        mul_le_mul' le_rfl h1
    _ = ENNReal.ofReal ((8*(n:ℝ)) * ((4*(n:ℝ)^2*a) * ((n:ℝ)*a))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (32*(n:ℝ)^4*a^2) := ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

/-- `A z (A z (i e_j))` has `vNorm` at most `32 n^4 a^2`. -/
lemma vNorm_A_compA_I_le {n : ℕ} {α a R r : ℝ} (ha0 : 0 ≤ a) (hsub : R ≤ r)
    (hΩ : UniqueDiffOn ℝ (Pd n R)) {A : Core.Cn n → Core.Cn n →L[ℝ] Core.Cn n}
    (hAcd : ContDiffOn ℝ 1 A (Pd n R))
    (haA : ∀ w : Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z => A z w j) (Pd n r) ≤ ENNReal.ofReal a)
    (j : Fin n) :
    vNorm 1 α (fun z => A z (A z (Pi.single j (Complex.I:ℂ)))) (Pd n R)
      ≤ ENNReal.ofReal (32 * (n:ℝ)^4 * a^2) := by
  have hMA := mNorm_A_le (n:=n) ha0 hsub hΩ hAcd haA
  have hva := vNorm_A_basisI_le (n:=n) ha0 hsub haA j
  have hFe : ∀ p, ContDiffOn ℝ 1 (fun z => (A z (Pi.single j (Complex.I:ℂ))) p) (Pd n R) :=
    fun p => contDiffOn_clm_component hAcd (Pi.single j (Complex.I:ℂ)) p
  have hTfin : mNorm 1 α A (Pd n R) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hMA
  have hFfin : vNorm 1 α (fun z => A z (Pi.single j (Complex.I:ℂ))) (Pd n R) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hva
  refine (AopAux.vNorm_clm_apply_le hΩ hAcd hFe hTfin hFfin).trans ?_
  have h1 := ofReal_mul_le_of_le (p := 4*(n:ℝ)^2*a) (by positivity) hMA hva
  calc ENNReal.ofReal (8*(n:ℝ)) * (mNorm 1 α A (Pd n R)
        * vNorm 1 α (fun z => A z (Pi.single j (Complex.I:ℂ))) (Pd n R))
      ≤ ENNReal.ofReal (8*(n:ℝ)) * ENNReal.ofReal ((4*(n:ℝ)^2*a) * ((n:ℝ)*a)) :=
        mul_le_mul' le_rfl h1
    _ = ENNReal.ofReal ((8*(n:ℝ)) * ((4*(n:ℝ)^2*a) * ((n:ℝ)*a))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (32*(n:ℝ)^4*a^2) := ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

/-- `Alin A z e_j` has `vNorm` at most `16 n^4 a^2`. -/
lemma vNorm_Alin_le {n : ℕ} {α a R r : ℝ} (ha0 : 0 ≤ a) (hsub : R ≤ r)
    (hΩ : UniqueDiffOn ℝ (Pd n R)) {A : Core.Cn n → Core.Cn n →L[ℝ] Core.Cn n}
    (hAcd : ContDiffOn ℝ 1 A (Pd n R))
    (haA : ∀ w : Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z => A z w j) (Pd n r) ≤ ENNReal.ofReal a)
    (j : Fin n) :
    vNorm 1 α (fun z => Alin A z (Pi.single j 1)) (Pd n R)
      ≤ ENNReal.ofReal (16 * (n:ℝ)^4 * a^2) := by
  have hcc := vNorm_A_compA_le (n:=n) ha0 hsub hΩ hAcd haA j
  have hF : ∀ p, ContDiffOn ℝ 1 (fun z => (A z (A z (Pi.single j 1))) p) (Pd n R) :=
    contDiffOn_clm_apply_components hAcd (fun p => contDiffOn_clm_component hAcd (Pi.single j 1) p)
  have hfun : (fun z => Alin A z (Pi.single j 1))
      = (fun z => (Complex.I/2) • (A z (A z (Pi.single j 1)))) := by
    funext z; simp [Alin, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  rw [hfun, vNorm_smul_const (Complex.I/2) hF hΩ]
  have hkey : ENNReal.ofReal ‖Complex.I/2‖ * ENNReal.ofReal (32*(n:ℝ)^4*a^2)
      = ENNReal.ofReal (16*(n:ℝ)^4*a^2) := by
    rw [← ENNReal.ofReal_mul (norm_nonneg (Complex.I/2)),
      show ‖Complex.I/2‖ = (1/2:ℝ) by norm_num]
    congr 1; ring
  exact (mul_le_mul' le_rfl hcc).trans (le_of_eq hkey)

/-- `Alin A z (i e_j)` has `vNorm` at most `16 n^4 a^2`. -/
lemma vNorm_Alin_I_le {n : ℕ} {α a R r : ℝ} (ha0 : 0 ≤ a) (hsub : R ≤ r)
    (hΩ : UniqueDiffOn ℝ (Pd n R)) {A : Core.Cn n → Core.Cn n →L[ℝ] Core.Cn n}
    (hAcd : ContDiffOn ℝ 1 A (Pd n R))
    (haA : ∀ w : Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z => A z w j) (Pd n r) ≤ ENNReal.ofReal a)
    (j : Fin n) :
    vNorm 1 α (fun z => Alin A z (Pi.single j (Complex.I:ℂ))) (Pd n R)
      ≤ ENNReal.ofReal (16 * (n:ℝ)^4 * a^2) := by
  have hcc := vNorm_A_compA_I_le (n:=n) ha0 hsub hΩ hAcd haA j
  have hF : ∀ p, ContDiffOn ℝ 1 (fun z => (A z (A z (Pi.single j (Complex.I:ℂ)))) p) (Pd n R) :=
    contDiffOn_clm_apply_components hAcd
      (fun p => contDiffOn_clm_component hAcd (Pi.single j (Complex.I:ℂ)) p)
  have hfun : (fun z => Alin A z (Pi.single j (Complex.I:ℂ)))
      = (fun z => (Complex.I/2) • (A z (A z (Pi.single j (Complex.I:ℂ))))) := by
    funext z; simp [Alin, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  rw [hfun, vNorm_smul_const (Complex.I/2) hF hΩ]
  have hkey : ENNReal.ofReal ‖Complex.I/2‖ * ENNReal.ofReal (32*(n:ℝ)^4*a^2)
      = ENNReal.ofReal (16*(n:ℝ)^4*a^2) := by
    rw [← ENNReal.ofReal_mul (norm_nonneg (Complex.I/2)),
      show ‖Complex.I/2‖ = (1/2:ℝ) by norm_num]
    congr 1; ring
  exact (mul_le_mul' le_rfl hcc).trans (le_of_eq hkey)


/-! ## The `Bop` bound -/

lemma contDiffOn_Alin_component {n : ℕ} {Ω : Set (Core.Cn n)}
    {A : Core.Cn n → Core.Cn n →L[ℝ] Core.Cn n} (hAcd : ContDiffOn ℝ 1 A Ω)
    (u : Core.Cn n) (p : Fin n) :
    ContDiffOn ℝ 1 (fun z => Alin A z u p) Ω := by
  have h1 : ContDiffOn ℝ 1 (fun z => (A z (A z u)) p) Ω :=
    contDiffOn_clm_apply_components hAcd (fun q => contDiffOn_clm_component hAcd u q) p
  have h2 := (contDiffOn_const (c := Complex.I/2)).mul h1
  refine h2.congr (fun z _ => ?_)
  simp [Alin, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, Pi.smul_apply,
    smul_eq_mul]

lemma contDiffOn_EVec {n : ℕ} {Ω : Set (Core.Cn n)} (hΩopen : IsOpen Ω)
    {A : Core.Cn n → Core.Cn n →L[ℝ] Core.Cn n} (hA : ∀ m : ℕ, ContDiffOn ℝ m A Ω)
    {v : Fin n → Core.Cn n → ℂ} (hv : ∀ (l : Fin n) (m : ℕ), ContDiffOn ℝ m (v l) Ω) (j m : Fin n) :
    ContDiffOn ℝ 1 (fun z => EVec A v j z m) Ω := by
  have h1 : ContDiffOn ℝ 1 (fun z => (Complex.I/2) * (A z (Pi.single j 1)) m) Ω :=
    (contDiffOn_const (c := Complex.I/2)).mul (contDiffOn_clm_component (hA 1) (Pi.single j 1) m)
  have hfd : ContDiffOn ℝ 1 (fun z => fderiv ℝ (v m) z) Ω :=
    (hv m 2).fderiv_of_isOpen hΩopen (by norm_num)
  have h2 : ContDiffOn ℝ 1 (fun z => Work.CR.Flat.dbarCoord j (v m) z) Ω := by
    have ha : ContDiffOn ℝ 1 (fun z => fderiv ℝ (v m) z (Pi.single j (1:ℂ))) Ω :=
      hfd.clm_apply (contDiffOn_const (c := (Pi.single j (1:ℂ) : Core.Cn n)))
    have hb : ContDiffOn ℝ 1 (fun z => fderiv ℝ (v m) z (Pi.single j (Complex.I:ℂ))) Ω :=
      hfd.clm_apply (contDiffOn_const (c := (Pi.single j (Complex.I:ℂ) : Core.Cn n)))
    have h4 := (contDiffOn_const (c := (1/2:ℂ))).mul
      (ha.add ((contDiffOn_const (c := Complex.I)).mul hb))
    simpa [Work.CR.Flat.dbarCoord] using h4
  have hfun : (fun z => EVec A v j z m)
      = (fun z => (Complex.I/2) * (A z (Pi.single j 1)) m - Work.CR.Flat.dbarCoord j (v m) z) := by
    funext z
    rw [EVec_eq]
    simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact h1.sub h2

lemma contDiffOn_dbarCoord_sub_Lcoef {n : ℕ} {Ω : Set (Core.Cn n)} (hΩopen : IsOpen Ω)
    {A : Core.Cn n → Core.Cn n →L[ℝ] Core.Cn n} (hA : ∀ m : ℕ, ContDiffOn ℝ m A Ω)
    {v : Fin n → Core.Cn n → ℂ} (hv : ∀ (l : Fin n) (m : ℕ), ContDiffOn ℝ m (v l) Ω) (k l : Fin n) :
    ContDiffOn ℝ 1 (fun z => Work.CR.Flat.dbarCoord k (v l) z - Work.NN.Core.Lcoef A (fun y => y l) k z) Ω := by
  have hdbar : ContDiffOn ℝ 1 (fun z => Work.CR.Flat.dbarCoord k (v l) z) Ω := by
    have hfd : ContDiffOn ℝ 1 (fun z => fderiv ℝ (v l) z) Ω :=
      (hv l 2).fderiv_of_isOpen hΩopen (by norm_num)
    have ha : ContDiffOn ℝ 1 (fun z => fderiv ℝ (v l) z (Pi.single k (1:ℂ))) Ω :=
      hfd.clm_apply (contDiffOn_const (c := (Pi.single k (1:ℂ) : Core.Cn n)))
    have hb : ContDiffOn ℝ 1 (fun z => fderiv ℝ (v l) z (Pi.single k (Complex.I:ℂ))) Ω :=
      hfd.clm_apply (contDiffOn_const (c := (Pi.single k (Complex.I:ℂ) : Core.Cn n)))
    have h4 := (contDiffOn_const (c := (1/2:ℂ))).mul
      (ha.add ((contDiffOn_const (c := Complex.I)).mul hb))
    simpa [Work.CR.Flat.dbarCoord] using h4
  have hLc : ContDiffOn ℝ 1 (fun z => Work.NN.Core.Lcoef A (fun y => y l) k z) Ω := by
    have h := (contDiffOn_const (c := Complex.I/2)).mul
      (contDiffOn_clm_component (hA 1) (Pi.single k 1) l)
    refine h.congr (fun z _ => ?_)
    rw [Work.NN.Core.Lcoef, fderiv_coordProj n l z, ContinuousLinearMap.proj_apply]
  exact hdbar.sub hLc

lemma vNorm_DvCLM_compA_le {n : ℕ} {α a b R r : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hsub : R ≤ r)
    (hΩ : UniqueDiffOn ℝ (Pd n R))
    {A : Core.Cn n → Core.Cn n →L[ℝ] Core.Cn n}
    {v : Fin n → Core.Cn n → ℂ}
    (hDvcd : ContDiffOn ℝ 1 (DvCLM v) (Pd n R))
    (hAcd : ContDiffOn ℝ 1 A (Pd n R))
    (hMD : mNorm 1 α (DvCLM v) (Pd n R) ≤ ENNReal.ofReal (32 * (n:ℝ)^2 * b))
    (haA : ∀ w : Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z => A z w j) (Pd n r) ≤ ENNReal.ofReal a)
    (j : Fin n) :
    vNorm 1 α (fun z => DvCLM v z (A z (Pi.single j 1))) (Pd n R)
      ≤ ENNReal.ofReal (256 * (n:ℝ)^4 * a * b) := by
  have hva := vNorm_A_basis_le (n:=n) ha0 hsub haA j
  have hFe : ∀ p, ContDiffOn ℝ 1 (fun z => (A z (Pi.single j 1)) p) (Pd n R) :=
    fun p => contDiffOn_clm_component hAcd (Pi.single j 1) p
  have hTfin : mNorm 1 α (DvCLM v) (Pd n R) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hMD
  have hFfin : vNorm 1 α (fun z => A z (Pi.single j 1)) (Pd n R) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hva
  refine (AopAux.vNorm_clm_apply_le hΩ hDvcd hFe hTfin hFfin).trans ?_
  have h1 := ofReal_mul_le_of_le (p := 32*(n:ℝ)^2*b) (by positivity) hMD hva
  calc ENNReal.ofReal (8*(n:ℝ)) * (mNorm 1 α (DvCLM v) (Pd n R)
        * vNorm 1 α (fun z => A z (Pi.single j 1)) (Pd n R))
      ≤ ENNReal.ofReal (8*(n:ℝ)) * ENNReal.ofReal ((32*(n:ℝ)^2*b) * ((n:ℝ)*a)) :=
        mul_le_mul' le_rfl h1
    _ = ENNReal.ofReal ((8*(n:ℝ)) * ((32*(n:ℝ)^2*b) * ((n:ℝ)*a))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (256*(n:ℝ)^4*a*b) := ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

lemma vNorm_DvCLM_compA_I_le {n : ℕ} {α a b R r : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hsub : R ≤ r)
    (hΩ : UniqueDiffOn ℝ (Pd n R))
    {A : Core.Cn n → Core.Cn n →L[ℝ] Core.Cn n}
    {v : Fin n → Core.Cn n → ℂ}
    (hDvcd : ContDiffOn ℝ 1 (DvCLM v) (Pd n R))
    (hAcd : ContDiffOn ℝ 1 A (Pd n R))
    (hMD : mNorm 1 α (DvCLM v) (Pd n R) ≤ ENNReal.ofReal (32 * (n:ℝ)^2 * b))
    (haA : ∀ w : Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z => A z w j) (Pd n r) ≤ ENNReal.ofReal a)
    (j : Fin n) :
    vNorm 1 α (fun z => DvCLM v z (A z (Pi.single j (Complex.I:ℂ)))) (Pd n R)
      ≤ ENNReal.ofReal (256 * (n:ℝ)^4 * a * b) := by
  have hva := vNorm_A_basisI_le (n:=n) ha0 hsub haA j
  have hFe : ∀ p, ContDiffOn ℝ 1 (fun z => (A z (Pi.single j (Complex.I:ℂ))) p) (Pd n R) :=
    fun p => contDiffOn_clm_component hAcd (Pi.single j (Complex.I:ℂ)) p
  have hTfin : mNorm 1 α (DvCLM v) (Pd n R) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hMD
  have hFfin : vNorm 1 α (fun z => A z (Pi.single j (Complex.I:ℂ))) (Pd n R) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hva
  refine (AopAux.vNorm_clm_apply_le hΩ hDvcd hFe hTfin hFfin).trans ?_
  have h1 := ofReal_mul_le_of_le (p := 32*(n:ℝ)^2*b) (by positivity) hMD hva
  calc ENNReal.ofReal (8*(n:ℝ)) * (mNorm 1 α (DvCLM v) (Pd n R)
        * vNorm 1 α (fun z => A z (Pi.single j (Complex.I:ℂ))) (Pd n R))
      ≤ ENNReal.ofReal (8*(n:ℝ)) * ENNReal.ofReal ((32*(n:ℝ)^2*b) * ((n:ℝ)*a)) :=
        mul_le_mul' le_rfl h1
    _ = ENNReal.ofReal ((8*(n:ℝ)) * ((32*(n:ℝ)^2*b) * ((n:ℝ)*a))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (256*(n:ℝ)^4*a*b) := ENNReal.ofReal_le_ofReal (le_of_eq (by ring))


lemma two_mul_ofReal_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (2 : ENNReal) * (ENNReal.ofReal x + ENNReal.ofReal y) = ENNReal.ofReal (2 * (x + y)) := by
  rw [← ENNReal.ofReal_add hx hy, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]

lemma ofReal_add3 {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    ENNReal.ofReal p + ENNReal.ofReal q + ENNReal.ofReal r
      = ENNReal.ofReal (p + q + r) := by
  rw [← ENNReal.ofReal_add hp hq, ← ENNReal.ofReal_add (add_nonneg hp hq) hr]

lemma ofReal_add4 {p q r s : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    ENNReal.ofReal p + ENNReal.ofReal q + ENNReal.ofReal r + ENNReal.ofReal s
      = ENNReal.ofReal (p + q + r + s) := by
  rw [← ENNReal.ofReal_add hp hq, ← ENNReal.ofReal_add (add_nonneg hp hq) hr,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg hp hq) hr) hs]

lemma vNorm_smul_const_le {n : ℕ} {k : ℕ} {α : ℝ} (c : ℂ) {F : Core.Cn n → Core.Cn n}
    {Ω : Set (Core.Cn n)} (hF : ∀ p, ContDiffOn ℝ (k:ℕ∞) (fun z => F z p) Ω)
    (hΩ : UniqueDiffOn ℝ Ω) :
    vNorm k α (fun z => c • F z) Ω = ENNReal.ofReal ‖c‖ * vNorm k α F Ω :=
  vNorm_smul_const c hF hΩ

/-- `vNorm` of `Bop A v z e_j`. -/
lemma vNorm_Bop_le {n : ℕ} {α a b e R r : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (he0 : 0 ≤ e)
    (hsub : R ≤ r) (hΩ : UniqueDiffOn ℝ (Pd n R)) (hΩopen : IsOpen (Pd n R))
    {A : Core.Cn n → Core.Cn n →L[ℝ] Core.Cn n} {v : Fin n → Core.Cn n → ℂ}
    (hAfull : ∀ m : ℕ, ContDiffOn ℝ m A (Pd n R)) (hvfull : ∀ (l : Fin n) (m : ℕ), ContDiffOn ℝ m (v l) (Pd n R))
    (hAcd : ContDiffOn ℝ 1 A (Pd n R))
    (haA : ∀ w : Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z => A z w j) (Pd n r) ≤ ENNReal.ofReal a)
    (he : ∀ l k : Fin n, Work.CR.Flat.holderNorm 1 α (fun z => Work.CR.Flat.dbarCoord k (v l) z
      - Work.NN.Core.Lcoef A (fun y => y l) k z) (Pd n R) ≤ ENNReal.ofReal e)
    (hDvcd : ContDiffOn ℝ 1 (DvCLM v) (Pd n R))
    (hMD : mNorm 1 α (DvCLM v) (Pd n R) ≤ ENNReal.ofReal (32 * (n:ℝ)^2 * b))
    (hACΩ : ∀ z ∈ Pd n R, ∀ u : Core.Cn n,
      (Core.JstdCn n + A) z ((Core.JstdCn n + A) z u) = -u)
    (j : Fin n) :
    vNorm 1 α (fun z => Bop A v z (Pi.single j 1)) (Pd n R)
      ≤ ENNReal.ofReal (2*(n:ℝ)*e + 256*(n:ℝ)^4*a*b) := by
  have hEvcd : ∀ m, ContDiffOn ℝ 1 (fun z => EVec A v j z m) (Pd n R) :=
    fun m => contDiffOn_EVec hΩopen hAfull hvfull j m
  have hEv := AopAux.vNorm_EVec_le (k := j) hΩ
    (fun l => contDiffOn_dbarCoord_sub_Lcoef hΩopen hAfull hvfull j l) (fun l => he l j)
  have h2e : vNorm 1 α (fun z => (-(2*Complex.I)) • EVec A v j z) (Pd n R)
      ≤ ENNReal.ofReal (2*(n:ℝ)*e) := by
    rw [vNorm_smul_const (-(2*Complex.I)) hEvcd hΩ]
    have hkey : ENNReal.ofReal ‖-(2*Complex.I)‖ * ENNReal.ofReal ((n:ℝ)*e)
        = ENNReal.ofReal (2*(n:ℝ)*e) := by
      rw [← ENNReal.ofReal_mul (norm_nonneg _), show ‖-(2*Complex.I)‖ = (2:ℝ) by norm_num]
      congr 1; ring
    exact (mul_le_mul' le_rfl hEv).trans (le_of_eq hkey)
  have hDvA := vNorm_DvCLM_compA_le (n:=n) ha0 hb0 hsub hΩ hDvcd hAcd hMD haA j
  rw [vNorm_congr (fun z hz => Bop_apply_single A v j z (hACΩ z hz))]
  have hcdF : ∀ m, ContDiffOn ℝ 1 (fun z => ((-(2*Complex.I)) • EVec A v j z) m) (Pd n R) :=
    fun m => (contDiffOn_const (c := -(2*Complex.I))).mul (hEvcd m)
  have hcdG : ∀ m, ContDiffOn ℝ 1 (fun z => DvCLM v z (A z (Pi.single j 1)) m) (Pd n R) :=
    fun m => contDiffOn_clm_apply_components hDvcd
      (fun p => contDiffOn_clm_component hAcd (Pi.single j 1) p) m
  refine (vNorm_sub_le' hcdF hcdG hΩ).trans ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add h2e hDvA

/-- `vNorm` of `Bop A v z (i e_j)`. -/
lemma vNorm_Bop_I_le {n : ℕ} {α a b e R r : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (he0 : 0 ≤ e)
    (hsub : R ≤ r) (hΩ : UniqueDiffOn ℝ (Pd n R)) (hΩopen : IsOpen (Pd n R))
    {A : Core.Cn n → Core.Cn n →L[ℝ] Core.Cn n} {v : Fin n → Core.Cn n → ℂ}
    (hAfull : ∀ m : ℕ, ContDiffOn ℝ m A (Pd n R)) (hvfull : ∀ (l : Fin n) (m : ℕ), ContDiffOn ℝ m (v l) (Pd n R))
    (hAcd : ContDiffOn ℝ 1 A (Pd n R))
    (haA : ∀ w : Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z => A z w j) (Pd n r) ≤ ENNReal.ofReal a)
    (he : ∀ l k : Fin n, Work.CR.Flat.holderNorm 1 α (fun z => Work.CR.Flat.dbarCoord k (v l) z
      - Work.NN.Core.Lcoef A (fun y => y l) k z) (Pd n R) ≤ ENNReal.ofReal e)
    (hDvcd : ContDiffOn ℝ 1 (DvCLM v) (Pd n R))
    (hMD : mNorm 1 α (DvCLM v) (Pd n R) ≤ ENNReal.ofReal (32 * (n:ℝ)^2 * b))
    (hACΩ : ∀ z ∈ Pd n R, ∀ u : Core.Cn n,
      (Core.JstdCn n + A) z ((Core.JstdCn n + A) z u) = -u)
    (j : Fin n) :
    vNorm 1 α (fun z => Bop A v z (Pi.single j (Complex.I:ℂ))) (Pd n R)
      ≤ ENNReal.ofReal (32*(n:ℝ)^4*a^2 + 2*(n:ℝ)*e + 256*(n:ℝ)^4*a*b) := by
  have hEvcd : ∀ m, ContDiffOn ℝ 1 (fun z => EVec A v j z m) (Pd n R) :=
    fun m => contDiffOn_EVec hΩopen hAfull hvfull j m
  have hEv := AopAux.vNorm_EVec_le (k := j) hΩ
    (fun l => contDiffOn_dbarCoord_sub_Lcoef hΩopen hAfull hvfull j l) (fun l => he l j)
  have hX := vNorm_Alin_I_le (n:=n) ha0 hsub hΩ hAcd haA j
  have hcdX : ∀ m, ContDiffOn ℝ 1 (fun z => Alin A z (Pi.single j (Complex.I:ℂ)) m) (Pd n R) :=
    fun m => contDiffOn_Alin_component hAcd (Pi.single j (Complex.I:ℂ)) m
  have hY : vNorm 1 α (fun z => Complex.I • Alin A z (Pi.single j 1)) (Pd n R)
      ≤ ENNReal.ofReal (16*(n:ℝ)^4*a^2) := by
    rw [vNorm_smul_const Complex.I (fun m => contDiffOn_Alin_component hAcd (Pi.single j 1) m) hΩ,
      show ‖Complex.I‖ = (1:ℝ) by norm_num, ENNReal.ofReal_one, one_mul]
    exact vNorm_Alin_le (n:=n) ha0 hsub hΩ hAcd haA j
  have hcdY : ∀ m, ContDiffOn ℝ 1 (fun z => Complex.I • Alin A z (Pi.single j 1) m) (Pd n R) :=
    fun m => (contDiffOn_const (c := Complex.I)).mul (contDiffOn_Alin_component hAcd (Pi.single j 1) m)
  have hZ : vNorm 1 α (fun z => (-(2:ℂ)) • EVec A v j z) (Pd n R)
      ≤ ENNReal.ofReal (2*(n:ℝ)*e) := by
    rw [vNorm_smul_const (-(2:ℂ)) hEvcd hΩ]
    have hkey : ENNReal.ofReal ‖(-(2:ℂ))‖ * ENNReal.ofReal ((n:ℝ)*e) = ENNReal.ofReal (2*(n:ℝ)*e) := by
      rw [← ENNReal.ofReal_mul (norm_nonneg _), show ‖(-(2:ℂ))‖ = (2:ℝ) by norm_num]
      congr 1; ring
    exact (mul_le_mul' le_rfl hEv).trans (le_of_eq hkey)
  have hcdZ : ∀ m, ContDiffOn ℝ 1 (fun z => (-(2:ℂ)) • EVec A v j z m) (Pd n R) :=
    fun m => (contDiffOn_const (c := -(2:ℂ))).mul (hEvcd m)
  have hW := vNorm_DvCLM_compA_I_le (n:=n) ha0 hb0 hsub hΩ hDvcd hAcd hMD haA j
  have hcdW : ∀ m, ContDiffOn ℝ 1 (fun z => DvCLM v z (A z (Pi.single j (Complex.I:ℂ))) m) (Pd n R) :=
    fun m => contDiffOn_clm_apply_components hDvcd
      (fun p => contDiffOn_clm_component hAcd (Pi.single j (Complex.I:ℂ)) p) m
  rw [show vNorm 1 α (fun z => Bop A v z (Pi.single j (Complex.I:ℂ))) (Pd n R)
      = vNorm 1 α (fun z => Alin A z (Pi.single j (Complex.I:ℂ))
          + Complex.I • Alin A z (Pi.single j 1) + (-(2:ℂ)) • EVec A v j z
          - DvCLM v z (A z (Pi.single j (Complex.I:ℂ)))) (Pd n R)
      from vNorm_congr (fun z hz => Bop_apply_single_I A v j z (hACΩ z hz))]
  have hXY : vNorm 1 α (fun z => Alin A z (Pi.single j (Complex.I:ℂ))
        + Complex.I • Alin A z (Pi.single j 1)) (Pd n R)
      ≤ vNorm 1 α (fun z => Alin A z (Pi.single j (Complex.I:ℂ))) (Pd n R)
        + vNorm 1 α (fun z => Complex.I • Alin A z (Pi.single j 1)) (Pd n R) :=
    vNorm_add_le hcdX hcdY hΩ
  have hXYZ : vNorm 1 α (fun z => Alin A z (Pi.single j (Complex.I:ℂ))
        + Complex.I • Alin A z (Pi.single j 1) + (-(2:ℂ)) • EVec A v j z) (Pd n R)
      ≤ (vNorm 1 α (fun z => Alin A z (Pi.single j (Complex.I:ℂ))) (Pd n R)
        + vNorm 1 α (fun z => Complex.I • Alin A z (Pi.single j 1)) (Pd n R))
        + vNorm 1 α (fun z => (-(2:ℂ)) • EVec A v j z) (Pd n R) :=
    (vNorm_add_le (fun m => (hcdX m).add (hcdY m)) hcdZ hΩ).trans (add_le_add hXY le_rfl)
  have hfull : vNorm 1 α (fun z => Alin A z (Pi.single j (Complex.I:ℂ))
        + Complex.I • Alin A z (Pi.single j 1) + (-(2:ℂ)) • EVec A v j z
        - DvCLM v z (A z (Pi.single j (Complex.I:ℂ)))) (Pd n R)
      ≤ ((vNorm 1 α (fun z => Alin A z (Pi.single j (Complex.I:ℂ))) (Pd n R)
        + vNorm 1 α (fun z => Complex.I • Alin A z (Pi.single j 1)) (Pd n R))
        + vNorm 1 α (fun z => (-(2:ℂ)) • EVec A v j z) (Pd n R))
        + vNorm 1 α (fun z => DvCLM v z (A z (Pi.single j (Complex.I:ℂ)))) (Pd n R) :=
    (vNorm_sub_le' (fun m => ((hcdX m).add (hcdY m)).add (hcdZ m)) hcdW hΩ).trans
      (add_le_add hXYZ le_rfl)
  refine hfull.trans ?_
  refine (add_le_add (add_le_add (add_le_add hX hY) hZ) hW).trans (le_of_eq ?_)
  rw [ofReal_add4 (by positivity) (by positivity) (by positivity) (by positivity)]
  congr 1; ring

/-- The `mNorm` bound for `Bop A v`. -/
lemma mNorm_Bop_le {n : ℕ} {α r δ a b e : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hr : 1 ≤ r) (hr4 : r ≤ 4) (hδ : 0 < δ) (hδ8 : δ ≤ 1/8)
    (A : Core.Cn n → Core.Cn n →L[ℝ] Core.Cn n)
    (hA : ∀ m : ℕ, ContDiffOn ℝ m A (Pd n r))
    (hAC : ∀ z ∈ Pd n r, ∀ u : Core.Cn n,
      (Core.JstdCn n + A) z ((Core.JstdCn n + A) z u) = -u)
    {v : Fin n → Core.Cn n → ℂ}
    (hv : ∀ l, ∀ m : ℕ, ContDiffOn ℝ m (v l) (Pd n (r * (1 - δ))))
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (he0 : 0 ≤ e)
    (haA : ∀ w : Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z => A z w j) (Pd n r) ≤ ENNReal.ofReal a)
    (hb : ∀ l, Work.CR.Flat.holderNorm 2 α (v l) (Pd n (r * (1 - δ)))
      ≤ ENNReal.ofReal b)
    (he : ∀ l k : Fin n, Work.CR.Flat.holderNorm 1 α (fun z => Work.CR.Flat.dbarCoord k (v l) z
      - Work.NN.Core.Lcoef A (fun y => y l) k z) (Pd n (r * (1 - δ))) ≤ ENNReal.ofReal e) :
    mNorm 1 α (Bop A v) (Pd n (r * (1 - δ)))
      ≤ ENNReal.ofReal (64*(n:ℝ)^5*a^2 + 8*(n:ℝ)^2*e + 1024*(n:ℝ)^5*a*b) := by
  set R : ℝ := r * (1 - δ) with hRdef
  have hrpos : 0 < r := lt_of_lt_of_le one_pos hr
  have h1mδ : 0 < 1 - δ := by linarith [hδ8]
  have hRpos : 0 < R := by rw [hRdef]; exact mul_pos hrpos h1mδ
  have hsub : R ≤ r := by
    rw [hRdef]
    have h := mul_le_mul_of_nonneg_left (show (1-δ) ≤ 1 by linarith [hδ]) hrpos.le
    linarith
  have hΩopen : IsOpen (Pd n R) := isOpen_Pd n R
  have hΩ : UniqueDiffOn ℝ (Pd n R) := hΩopen.uniqueDiffOn
  have hΩsub : Pd n R ⊆ Pd n r := Pd_mono hsub
  have hAfull : ∀ m : ℕ, ContDiffOn ℝ m A (Pd n R) := fun m => (hA m).mono hΩsub
  have hAcd : ContDiffOn ℝ 1 A (Pd n R) := hAfull 1
  have hvfull : ∀ (l : Fin n) (m : ℕ), ContDiffOn ℝ m (v l) (Pd n R) := fun l m => hv l m
  have hACΩ : ∀ z ∈ Pd n R, ∀ u : Core.Cn n,
      (Core.JstdCn n + A) z ((Core.JstdCn n + A) z u) = -u := fun z hz => hAC z (hΩsub hz)
  obtain ⟨hDvcd, _, _, _, _⟩ := DvCLM_data_le (n:=n) (α:=α) (R:=R) hα0 hRpos hvfull hb0 (fun l => hb l)
  have hMD := AopAux.mNorm_DvCLM_le (n:=n) (α:=α) (r:=r) (δ:=δ) (b:=b)
    hα0 hα1 hr hr4 hδ hδ8 hv hb0 hb
  have hBopcd : ContDiffOn ℝ 1 (Bop A v) (Pd n R) :=
    contDiffOn_Aop_bop hAfull (fun m => contDiffOn_Aop_dvclm hvfull m) 1
  have hK1 : 0 ≤ 2*(n:ℝ)*e + 256*(n:ℝ)^4*a*b := by positivity
  have hK2 : 0 ≤ 32*(n:ℝ)^4*a^2 + 2*(n:ℝ)*e + 256*(n:ℝ)^4*a*b := by positivity
  have h1 : (∑ j, vNorm 1 α (fun z => Bop A v z (Pi.single j 1)) (Pd n R))
      ≤ ENNReal.ofReal ((n:ℝ) * (2*(n:ℝ)*e + 256*(n:ℝ)^4*a*b)) := by
    simpa only [Fintype.card_fin] using sum_le_ofReal_card (ι := Fin n) hK1
      (fun j => vNorm_Bop_le (n:=n) ha0 hb0 he0 hsub hΩ hΩopen hAfull hvfull hAcd haA he hDvcd hMD hACΩ j)
  have h2 : (∑ j, vNorm 1 α (fun z => Bop A v z (Pi.single j (Complex.I:ℂ))) (Pd n R))
      ≤ ENNReal.ofReal ((n:ℝ) * (32*(n:ℝ)^4*a^2 + 2*(n:ℝ)*e + 256*(n:ℝ)^4*a*b)) := by
    simpa only [Fintype.card_fin] using sum_le_ofReal_card (ι := Fin n) hK2
      (fun j => vNorm_Bop_I_le (n:=n) ha0 hb0 he0 hsub hΩ hΩopen hAfull hvfull hAcd haA he hDvcd hMD hACΩ j)
  refine (AopAux.mNorm_le_two_vNorm_basis hΩ hBopcd h1 h2).trans ?_
  have hK1' : 0 ≤ (n:ℝ) * (2*(n:ℝ)*e + 256*(n:ℝ)^4*a*b) := by positivity
  have hK2' : 0 ≤ (n:ℝ) * (32*(n:ℝ)^4*a^2 + 2*(n:ℝ)*e + 256*(n:ℝ)^4*a*b) := by positivity
  rw [two_mul_ofReal_add hK1' hK2']
  refine ENNReal.ofReal_le_ofReal (le_of_eq (by ring))


/-- `vNorm` of `Aop A v · w` (`‖w‖ ≤ 1`), given the `mNorm` bound on `Bop`. -/
lemma vNorm_Aop_le {n : ℕ} {α R : ℝ} {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hΩ : UniqueDiffOn ℝ (Pd n R)) (hΩopen : IsOpen (Pd n R))
    {A : Core.Cn n → Core.Cn n →L[ℝ] Core.Cn n} {v : Fin n → Core.Cn n → ℂ}
    (hBopcd : ContDiffOn ℝ 1 (Bop A v) (Pd n R))
    (hMB : mNorm 1 α (Bop A v) (Pd n R) ≤ ENNReal.ofReal Kb)
    (hMinvcd : ∀ w : Core.Cn n, ‖w‖ ≤ 1 → ∀ p : Fin n,
      ContDiffOn ℝ 1 (fun z => (Minv v z w) p) (Pd n R))
    (hMinvbd : ∀ w : Core.Cn n, ‖w‖ ≤ 1 →
      vNorm 1 α (fun z => Minv v z w) (Pd n R) ≤ ENNReal.ofReal (1024 * (n:ℝ)))
    (w : Core.Cn n) (hw : ‖w‖ ≤ 1) :
    vNorm 1 α (fun z => Aop A v z w) (Pd n R)
      ≤ ENNReal.ofReal (8192 * (n:ℝ)^2 * Kb) := by
  have hF : ∀ p : Fin n, ContDiffOn ℝ 1 (fun z => (Minv v z w) p) (Pd n R) :=
    fun p => hMinvcd _ hw p
  have hFfin : vNorm 1 α (fun z => Minv v z w) (Pd n R) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hMinvbd _ hw)
  have hTfin : mNorm 1 α (Bop A v) (Pd n R) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hMB
  rw [show vNorm 1 α (fun z => Aop A v z w) (Pd n R)
      = vNorm 1 α (fun z => Bop A v z (Minv v z w)) (Pd n R) from
      vNorm_congr (fun z _ => rfl)]
  refine (AopAux.vNorm_clm_apply_le hΩ hBopcd hF hTfin hFfin).trans ?_
  have h1 : mNorm 1 α (Bop A v) (Pd n R) * vNorm 1 α (fun z => Minv v z w) (Pd n R)
      ≤ ENNReal.ofReal (Kb * (1024 * (n:ℝ))) :=
    ofReal_mul_le_of_le hKb0 hMB (hMinvbd _ hw)
  calc ENNReal.ofReal (8*(n:ℝ)) * (mNorm 1 α (Bop A v) (Pd n R)
        * vNorm 1 α (fun z => Minv v z w) (Pd n R))
      ≤ ENNReal.ofReal (8*(n:ℝ)) * ENNReal.ofReal (Kb * (1024 * (n:ℝ))) :=
        mul_le_mul' le_rfl h1
    _ = ENNReal.ofReal ((8*(n:ℝ)) * (Kb * (1024 * (n:ℝ)))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (8192 * (n:ℝ)^2 * Kb) := ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

/-- The final numeric inequality. -/
lemma aop_final_arith {n : ℕ} {a b e : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (he0 : 0 ≤ e) :
    32768 * (n:ℝ)^3 * (64*(n:ℝ)^5*a^2 + 8*(n:ℝ)^2*e + 1024*(n:ℝ)^5*a*b)
      ≤ 2^40 * ((n:ℝ)+1)^16 * (a^2 + e + a * b) := by
  set C : ℝ := 2^40 * ((n:ℝ)+1)^16 with hCdef
  have hn8 : (n:ℝ)^8 ≤ ((n:ℝ)+1)^16 := by
    have h1 : (n:ℝ)^8 ≤ ((n:ℝ)+1)^8 :=
      pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) 8
    have h2 : ((n:ℝ)+1)^8 ≤ ((n:ℝ)+1)^16 :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  have hn5 : (n:ℝ)^5 ≤ ((n:ℝ)+1)^16 := by
    have h1 : (n:ℝ)^5 ≤ ((n:ℝ)+1)^5 :=
      pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) 5
    have h2 : ((n:ℝ)+1)^5 ≤ ((n:ℝ)+1)^16 :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  have hbase8 : (2097152:ℝ) * (n:ℝ)^8 ≤ C := by
    rw [hCdef]
    calc (2097152:ℝ) * (n:ℝ)^8 ≤ 2^40 * (n:ℝ)^8 :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ 2^40 * ((n:ℝ)+1)^16 := mul_le_mul_of_nonneg_left hn8 (by positivity)
  have hbase5 : (262144:ℝ) * (n:ℝ)^5 ≤ C := by
    rw [hCdef]
    calc (262144:ℝ) * (n:ℝ)^5 ≤ 2^40 * (n:ℝ)^5 :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ 2^40 * ((n:ℝ)+1)^16 := mul_le_mul_of_nonneg_left hn5 (by positivity)
  have hbase8' : (33554432:ℝ) * (n:ℝ)^8 ≤ C := by
    rw [hCdef]
    calc (33554432:ℝ) * (n:ℝ)^8 ≤ 2^40 * (n:ℝ)^8 :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ 2^40 * ((n:ℝ)+1)^16 := mul_le_mul_of_nonneg_left hn8 (by positivity)
  have hab : (0:ℝ) ≤ a * b := mul_nonneg ha0 hb0
  have hT1 : 2097152 * (n:ℝ)^8 * a^2 ≤ C * a^2 := mul_le_mul_of_nonneg_right hbase8 (by positivity)
  have hT2 : 262144 * (n:ℝ)^5 * e ≤ C * e := mul_le_mul_of_nonneg_right hbase5 he0
  have hT3 : 33554432 * (n:ℝ)^8 * (a*b) ≤ C * (a*b) := mul_le_mul_of_nonneg_right hbase8' hab
  have hsum := add_le_add (add_le_add hT1 hT2) hT3
  rw [show 32768 * (n:ℝ)^3 * (64*(n:ℝ)^5*a^2 + 8*(n:ℝ)^2*e + 1024*(n:ℝ)^5*a*b)
      = 2097152 * (n:ℝ)^8 * a^2 + 262144 * (n:ℝ)^5 * e + 33554432 * (n:ℝ)^8 * (a*b) by ring]
  refine hsum.trans (le_of_eq ?_)
  rw [hCdef]; ring


theorem mNorm_Aop_le {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {r δ : ℝ} (hr : 1 ≤ r) (hr4 : r ≤ 4) (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8)
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (hA : ∀ m : ℕ, ContDiffOn ℝ m A (Work.NN.Newton.Pd n r))
    (hAC : ∀ z ∈ Work.NN.Newton.Pd n r, ∀ u : Work.NN.Core.Cn n,
      (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z u) = -u)
    {v : Fin n → Work.NN.Core.Cn n → ℂ}
    (hv : ∀ l, ∀ m : ℕ, ContDiffOn ℝ m (v l) (Work.NN.Newton.Pd n (r * (1 - δ))))
    {a b e : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (he0 : 0 ≤ e)
    (haA : ∀ w : Work.NN.Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z => A z w j) (Work.NN.Newton.Pd n r)
        ≤ ENNReal.ofReal a)
    (hb : ∀ l, Work.CR.Flat.holderNorm 2 α (v l) (Work.NN.Newton.Pd n (r * (1 - δ)))
      ≤ ENNReal.ofReal b)
    (he : ∀ l k : Fin n, Work.CR.Flat.holderNorm 1 α
      (fun z => Work.CR.Flat.dbarCoord k (v l) z
        - Work.NN.Core.Lcoef A (fun y => y l) k z)
      (Work.NN.Newton.Pd n (r * (1 - δ))) ≤ ENNReal.ofReal e)
    (hbδ : b ≤ r * δ / 4) (hb1 : b ≤ 1 / 16) :
    Work.NN.Newton.mNorm 1 α (fun z => Work.NN.Newton.Aop A v z)
        (Work.NN.Newton.Pd n (r * (1 - δ)))
      ≤ ENNReal.ofReal ((2 : ℝ) ^ 40 * ((n : ℝ) + 1) ^ 16 * (a ^ 2 + e + a * b)) := by
  set R : ℝ := r * (1 - δ) with hRdef
  have hrpos : 0 < r := lt_of_lt_of_le one_pos hr
  have h1mδ : 0 < 1 - δ := by linarith [hδ8]
  have hRpos : 0 < R := by rw [hRdef]; exact mul_pos hrpos h1mδ
  have hsub : R ≤ r := by
    rw [hRdef]
    have h := mul_le_mul_of_nonneg_left (show (1-δ) ≤ 1 by linarith [hδ]) hrpos.le
    linarith
  have hR4 : R ≤ 4 := by
    rw [hRdef]
    have h := mul_le_mul_of_nonneg_left (show (1-δ) ≤ 1 by linarith [hδ]) hrpos.le
    linarith [hr4]
  have hΩopen : IsOpen (Pd n R) := isOpen_Pd n R
  have hΩ : UniqueDiffOn ℝ (Pd n R) := hΩopen.uniqueDiffOn
  have hΩsub : Pd n R ⊆ Pd n r := Pd_mono hsub
  have hAΩ : ∀ m : ℕ, ContDiffOn ℝ m A (Pd n R) := fun m => (hA m).mono hΩsub
  have hvΩ : ∀ (l : Fin n) (m : ℕ), ContDiffOn ℝ m (v l) (Pd n R) := fun l m => hv l m
  have hb1le8 : b ≤ 1/8 := by linarith [hb1]
  -- the `Bop` bound
  have hMB : mNorm 1 α (Bop A v) (Pd n R)
      ≤ ENNReal.ofReal (64*(n:ℝ)^5*a^2 + 8*(n:ℝ)^2*e + 1024*(n:ℝ)^5*a*b) := by
    rw [hRdef]
    exact mNorm_Bop_le (n:=n) (α:=α) (r:=r) (δ:=δ) (a:=a) (b:=b) (e:=e)
      hα0 hα1 hr hr4 hδ hδ8 A hA hAC hv ha0 ha1 hb0 he0 haA hb he
  have hBopcd : ContDiffOn ℝ 1 (Bop A v) (Pd n R) :=
    contDiffOn_Aop_bop hAΩ (fun m => contDiffOn_Aop_dvclm hvΩ m) 1
  -- the `Minv` data
  have hDvnorm : ∀ z ∈ Pd n R, ‖DvCLM v z‖ ≤ b :=
    fun z hz => (DvCLM_data_le (n:=n) (α:=α) (R:=R) hα0 hRpos hvΩ hb0 (fun l => hb l)).2.1 z hz
  have hunit : ∀ z ∈ Pd n R, IsUnit (1 - DvCLM v z) := by
    intro z hz
    exact IsUnit.one_sub_of_norm_lt_one (by have := hDvnorm z hz; linarith [hb1le8])
  have hAopcd : ContDiffOn ℝ 1 (Aop A v) (Pd n R) := contDiffOn_Aop hAΩ hvΩ hunit 1
  have hMinv := Minv_holderNorm_one_le (n:=n) (α:=α) (R:=R) hα0 hα1 hRpos hR4
    (fun l m => hvΩ l m) hb0 hb1le8 (fun l => hb l)
  have hMinvcd : ∀ w : Core.Cn n, ‖w‖ ≤ 1 → ∀ p : Fin n,
      ContDiffOn ℝ 1 (fun z => (Minv v z w) p) (Pd n R) := fun w hw p => (hMinv w hw p).1
  have hMinvbd : ∀ w : Core.Cn n, ‖w‖ ≤ 1 →
      vNorm 1 α (fun z => Minv v z w) (Pd n R) ≤ ENNReal.ofReal (1024 * (n:ℝ)) := by
    intro w hw
    rw [hRdef]
    exact AopAux.vNorm_Minv_le (n:=n) (α:=α) (r:=r) (δ:=δ) (b:=b) hα0 hα1 hr hr4 hδ hδ8
      hv hb0 hb1 hb w hw
  -- the `Aop` basis bounds
  have hKb0 : 0 ≤ 64*(n:ℝ)^5*a^2 + 8*(n:ℝ)^2*e + 1024*(n:ℝ)^5*a*b := by positivity
  have hvA_e : ∀ j : Fin n, vNorm 1 α (fun z => Aop A v z (Pi.single j 1)) (Pd n R)
      ≤ ENNReal.ofReal (8192 * (n:ℝ)^2
          * (64*(n:ℝ)^5*a^2 + 8*(n:ℝ)^2*e + 1024*(n:ℝ)^5*a*b)) :=
    fun j => vNorm_Aop_le hKb0 hΩ hΩopen hBopcd hMB hMinvcd hMinvbd _
      (by rw [Pi.norm_single]; norm_num)
  have hvA_i : ∀ j : Fin n, vNorm 1 α (fun z => Aop A v z (Pi.single j (Complex.I:ℂ))) (Pd n R)
      ≤ ENNReal.ofReal (8192 * (n:ℝ)^2
          * (64*(n:ℝ)^5*a^2 + 8*(n:ℝ)^2*e + 1024*(n:ℝ)^5*a*b)) :=
    fun j => vNorm_Aop_le hKb0 hΩ hΩopen hBopcd hMB hMinvcd hMinvbd _
      (by rw [Pi.norm_single, Complex.norm_I])
  have hKv : 0 ≤ 8192 * (n:ℝ)^2 * (64*(n:ℝ)^5*a^2 + 8*(n:ℝ)^2*e + 1024*(n:ℝ)^5*a*b) := by
    positivity
  have h1 : (∑ j, vNorm 1 α (fun z => Aop A v z (Pi.single j 1)) (Pd n R))
      ≤ ENNReal.ofReal ((n:ℝ) * (8192 * (n:ℝ)^2
          * (64*(n:ℝ)^5*a^2 + 8*(n:ℝ)^2*e + 1024*(n:ℝ)^5*a*b))) := by
    simpa only [Fintype.card_fin] using sum_le_ofReal_card (ι := Fin n)
      hKv (fun j => hvA_e j)
  have h2 : (∑ j, vNorm 1 α (fun z => Aop A v z (Pi.single j (Complex.I:ℂ))) (Pd n R))
      ≤ ENNReal.ofReal ((n:ℝ) * (8192 * (n:ℝ)^2
          * (64*(n:ℝ)^5*a^2 + 8*(n:ℝ)^2*e + 1024*(n:ℝ)^5*a*b))) := by
    simpa only [Fintype.card_fin] using sum_le_ofReal_card (ι := Fin n)
      hKv (fun j => hvA_i j)
  refine (AopAux.mNorm_le_two_vNorm_basis hΩ hAopcd h1 h2).trans ?_
  have hx : 0 ≤ (n:ℝ) * (8192 * (n:ℝ)^2
      * (64*(n:ℝ)^5*a^2 + 8*(n:ℝ)^2*e + 1024*(n:ℝ)^5*a*b)) :=
    mul_nonneg (Nat.cast_nonneg _) hKv
  rw [two_mul_ofReal_add_self hx]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [show 4 * ((n:ℝ) * (8192 * (n:ℝ)^2
      * (64*(n:ℝ)^5*a^2 + 8*(n:ℝ)^2*e + 1024*(n:ℝ)^5*a*b)))
      = 32768 * (n:ℝ)^3 * (64*(n:ℝ)^5*a^2 + 8*(n:ℝ)^2*e + 1024*(n:ℝ)^5*a*b) by ring]
  exact aop_final_arith (n:=n) ha0 hb0 he0

end Work.NN.Newton
