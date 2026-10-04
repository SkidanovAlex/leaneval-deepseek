import Mathlib
import Submission.Work.Diff.STE.flat.pairing_sharp_core
import Submission.Work.Diff.STE.flat.symInv_garding_bounds
import Submission.Work.Diff.STE.flat.symInv_deriv_Lp_bound
import Submission.Work.Diff.STE.flat.jet_sup_le_uniform_level
import Submission.Work.Diff.STE.commutator_core
import Submission.Work.Diff.STE.commutator_estimate
import Submission.Work.Diff.STE.pdList_mul_sub
import Submission.Work.Diff.STE.flat.level_defs
import Submission.Work.Diff.STE.flat.Sobolev
import Submission.Work.Diff.STE.poincare_cube

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators
open Work.Diff.STE.Flat

noncomputable section

/-! ## Elementary estimates used by the sharp commutator bound -/

/-- Integrability of a continuous real function on the unit cube. -/
lemma csb_integrable_cube {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) :
    Integrable f (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
  Work.Diff.STE.cm_integrableOn_unitCube_of_continuous hf

/-- Cauchy–Schwarz for `L2re`, in `rnorm 2` form. -/
lemma csb_l2re_le_rnorm_two {n : ℕ} {F G : (Fin n → ℝ) → ℂ} (hF : Continuous F)
    (hG : Continuous G) : |Work.Diff.STE.L2re F G| ≤ rnorm 2 F * rnorm 2 G := by
  have h : |Work.Diff.STE.L2re F G|
      ≤ Real.sqrt (∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖F x‖ ^ 2)
        * Real.sqrt (∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖G x‖ ^ 2) := by
    simpa only [Real.rpow_two, pow_two] using L2re_le_sqrt hF hG
  rw [rnorm_two_eq_sqrt, rnorm_two_eq_sqrt]
  exact h

/-- `L²` bound of a product from a sup bound on one factor. -/
lemma csb_rnorm_two_mul_le {n : ℕ} {F G : (Fin n → ℝ) → ℂ} {M : ℝ}
    (hF : Continuous F) (hG : Continuous G) (hFb : ∀ x, ‖F x‖ ≤ M) :
    rnorm 2 (fun x => F x * G x) ≤ M * rnorm 2 G := by
  rw [rnorm_two_eq_sqrt, rnorm_two_eq_sqrt]
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (F 0)) (hFb 0)
  have hint1 : Integrable (fun x : Fin n → ℝ => ‖F x * G x‖ ^ 2)
      (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) := by
    refine Work.Diff.STE.cm_integrableOn_unitCube_of_continuous ?_
    fun_prop
  have hint2 : Integrable (fun x : Fin n → ℝ => M ^ 2 * ‖G x‖ ^ 2)
      (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
    (Work.Diff.STE.cm_integrableOn_unitCube_of_continuous (by fun_prop)).const_mul (M ^ 2)
  have hmono : ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖F x * G x‖ ^ 2
      ≤ M ^ 2 * ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖G x‖ ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono hint1 hint2 (fun x => ?_)
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hFb x) 2) (sq_nonneg _)
  calc Real.sqrt (∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖F x * G x‖ ^ 2)
      ≤ M * Real.sqrt (∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖G x‖ ^ 2) := by
        refine (Real.sqrt_le_sqrt hmono).trans (le_of_eq ?_)
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hM0]

/-- **Three-factor estimate with a sup bound on the first factor.**  If `‖F‖ ≤ M` pointwise then
`|⟨F·G, h⟩| ≤ M ‖G‖₂ ‖h‖₂`. -/
lemma csb_l2re_sup_mul_le {n : ℕ} {F G h : (Fin n → ℝ) → ℂ} {M : ℝ}
    (hFc : Continuous F) (hGc : Continuous G) (hhc : Continuous h) (hFb : ∀ x, ‖F x‖ ≤ M) :
    |Work.Diff.STE.L2re (fun x => F x * G x) h| ≤ M * rnorm 2 G * rnorm 2 h := by
  calc |Work.Diff.STE.L2re (fun x => F x * G x) h|
      ≤ rnorm 2 (fun x => F x * G x) * rnorm 2 h := csb_l2re_le_rnorm_two (hFc.mul hGc) hhc
    _ ≤ (M * rnorm 2 G) * rnorm 2 h :=
        mul_le_mul_of_nonneg_right (csb_rnorm_two_mul_le hFc hGc hFb) (rnorm_nonneg 2 h)
    _ = M * rnorm 2 G * rnorm 2 h := by ring

/-- **Absorption of a square root into a linear term.**  For `ν > 0`, `K ≥ 0`, `E ≥ 0`,
`K √(1+E) ≤ ν E + (ν/2 + K²/(2ν))`. -/
lemma csb_sqrt_one_add_absorb {ν K E : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hE : 0 ≤ E) :
    K * Real.sqrt (1 + E) ≤ ν * E + (ν / 2 + K ^ 2 / (2 * ν)) := by
  rcases eq_or_lt_of_le hK with hK0 | hKpos
  · rw [← hK0]
    simp only [zero_mul]
    positivity
  · have hsq : Real.sqrt (1 + E) ^ 2 = 1 + E := Real.sq_sqrt (by linarith)
    have h1 : 2 * (ν * K * Real.sqrt (1 + E)) ≤ ν ^ 2 * (1 + E) + K ^ 2 := by
      nlinarith [sq_nonneg (ν * Real.sqrt (1 + E) - K), hsq]
    have h2 : ν ^ 2 * (1 + E) + K ^ 2 ≤ 2 * ν ^ 2 * E + ν ^ 2 + K ^ 2 := by
      nlinarith [sq_nonneg ν, hE]
    have h3 : 2 * ν * (K * Real.sqrt (1 + E))
        ≤ 2 * ν * (ν * E + (ν / 2 + K ^ 2 / (2 * ν))) := by
      have hR : 2 * ν * (ν * E + (ν / 2 + K ^ 2 / (2 * ν))) = 2 * ν ^ 2 * E + ν ^ 2 + K ^ 2 := by
        field_simp
        ring
      rw [hR]
      linarith [h1, h2]
    exact le_of_mul_le_mul_left h3 (by positivity)

/-- **The exponent window of the sharp commutator bound.**  For `2 ≤ m ≤ k-1` and the sharp
threshold `n + 4 < 2 k` there is `α = n/r₁` strictly between `0` and `n/2` with
`max 0 (m + n/2 + 1/2 - k) ≤ α ≤ min (n/2) (m - 3/2)`.  These are exactly the two price
conditions for the `L^{r₁}` bound on `∂^m symInvC` (price `≤ k`) and the `L^{r₂}` bound on
`∂^{k-m+2} u` (price `≤ k+1`), where `n/r₂ = n/2 - α`. -/
lemma csb_comm_window {n k m : ℕ} (hn : 1 ≤ n)
    (hk : Fintype.card (Fin n) + 4 < 2 * k) (hm2 : 2 ≤ m) (hmk : m ≤ k - 1) :
    ∃ α : ℝ, max 0 ((m : ℝ) + (n : ℝ) / 2 + 1 / 2 - (k : ℝ)) ≤ α ∧
      α ≤ min ((n : ℝ) / 2) ((m : ℝ) - 3 / 2) ∧ 0 < α ∧ α < (n : ℝ) / 2 := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hkR : (n : ℝ) + 4 < 2 * (k : ℝ) := by
    exact_mod_cast (by simpa using hk : n + 4 < 2 * k)
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hmkR : (m : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (by omega : m + 1 ≤ k)
  set lo : ℝ := max 0 ((m : ℝ) + (n : ℝ) / 2 + 1 / 2 - (k : ℝ)) with hlo
  set hi : ℝ := min ((n : ℝ) / 2) ((m : ℝ) - 3 / 2) with hhi
  have hlo0 : 0 ≤ lo := by rw [hlo]; exact le_max_left _ _
  have hhi_pos : 0 < hi := by
    rw [hhi]
    exact lt_min (by linarith) (by linarith)
  have hlo_lt : lo < (n : ℝ) / 2 := by
    rw [hlo]
    refine max_lt (by linarith) ?_
    linarith
  have hhi_le : hi ≤ (n : ℝ) / 2 := by rw [hhi]; exact min_le_left _ _
  have hle : lo ≤ hi := by
    rw [hlo, hhi]
    refine max_le (le_min (by linarith) (by linarith)) ?_
    exact le_min (by linarith) (by linarith)
  exact ⟨(lo + hi) / 2, by linarith, by linarith, by linarith, by linarith⟩

/-! ## Uniform `L^r` bounds for the two factors of the commutator -/

/-- **Uniform `L^r` bound for the jets of the unknown.**  For a box-supported coefficient family
with level-`L` energy `ENormSqFull L (seriesFunM c)`, every derivative `∂^q (seriesFunM c · i j)`
of order `m ≤ L` whose "price" `m + n/2 - n/r + 1/2` is at most `L` is bounded in `L^r` by a
constant times `√(ENormSqFull L (seriesFunM c))`, uniformly in `N`, `c`, `i`, `j`, `q` and `r`. -/
lemma csb_u_rnorm_le_level {n : ℕ} (hn : 1 ≤ n) (L : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) →
      ∀ (m : ℕ) (r : ℝ), 2 ≤ r →
        (m : ℝ) + (n : ℝ) / 2 - (n : ℝ) / r + 1 / 2 ≤ (L : ℝ) → m ≤ L →
        ∀ (q : List (Fin n)), q.length = m → ∀ (i j : Fin n),
          rnorm r (pdList q (fun y => seriesFunM c y i j))
            ≤ C * Real.sqrt (ENormSqFull L (seriesFunM c)) := by
  obtain ⟨Cun, hCun0, hCun⟩ := rnorm_seriesFun_uniform (ι := Fin n)
  obtain ⟨C2, hC20, hCSQ⟩ := Work.Diff.STE.CSq_le_ENormSq_seriesFun (ι := Fin n) L
  refine ⟨Cun * (2 * Real.pi) ^ L * Real.sqrt C2, by positivity, ?_⟩
  intro N c hc m r hr hprice hmL q hq i j
  have hmom : ∀ M : ℕ, Summable (fun μ : Fin n → ℤ => (wt μ) ^ M * ‖c μ i j‖) :=
    fun M => summable_moment_box c hc i j M
  have hfun : (fun y : Fin n → ℝ => seriesFunM c y i j)
      = Work.Diff.STE.seriesFun (fun μ : Fin n → ℤ => c μ i j) := by
    funext y; rw [seriesFunM_apply]
  have hpd : pdList q (fun y : Fin n → ℝ => seriesFunM c y i j)
      = Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV q (fun μ : Fin n → ℤ => c μ i j)) := by
    rw [hfun]
    exact funext (fun x => Work.Diff.STE.pdList_seriesFun q (fun μ : Fin n → ℤ => c μ i j) hmom x)
  have hj : (Fintype.card (Fin n) : ℝ) * (1 / 2 - 1 / (2 * (r / 2))) + 1 / 2
      ≤ (L : ℝ) - (m : ℝ) := by
    simp only [Fintype.card_fin]
    have hcast : (n : ℝ) * (1 / 2 - 1 / (2 * (r / 2))) = (n : ℝ) / 2 - (n : ℝ) / r := by
      field_simp
    linarith [hprice, hcast]
  have hmass0 : Summable (fun μ : Fin n → ℤ => (wt μ) ^ L * ‖c μ i j‖ ^ 2) :=
    Work.Diff.STE.summable_wt_pow_mul_norm_sq _ hmom L
  have hqm : (q.length : ℝ) = (m : ℝ) := by exact_mod_cast hq
  have hmass := summable_wt_dmulV_le q ((L : ℝ) - (m : ℝ)) L (fun μ : Fin n → ℤ => c μ i j)
    (by linarith) hmass0
  have hsob := hCun (r / 2) (by linarith) ((L : ℝ) - (m : ℝ)) hj
    (Work.Diff.STE.dmulV q (fun μ : Fin n → ℤ => c μ i j)) hmass.1
  rw [show 2 * (r / 2) = r by ring] at hsob
  rw [hpd]
  have hCSQ' : Work.Diff.STE.CSq L (fun μ : Fin n → ℤ => c μ i j)
      ≤ C2 * ENormSqFull L (seriesFunM c) := by
    have h := hCSQ (fun μ : Fin n → ℤ => c μ i j) hmom
    have h1 : Work.Diff.STE.ENormSq L (Work.Diff.STE.seriesFun (fun μ : Fin n → ℤ => c μ i j))
        ≤ ENormSqM L (seriesFunM c) := by
      simpa only [← hfun] using ENormSq_le_ENormSqM (seriesFunM c) i j
    have h2 : Work.Diff.STE.ENormSq 0 (Work.Diff.STE.seriesFun (fun μ : Fin n → ℤ => c μ i j))
        ≤ ENormSqM 0 (seriesFunM c) := by
      simpa only [← hfun] using ENormSq_le_ENormSqM (seriesFunM c) i j
    calc Work.Diff.STE.CSq L (fun μ : Fin n → ℤ => c μ i j)
        ≤ C2 * (Work.Diff.STE.ENormSq L (Work.Diff.STE.seriesFun (fun μ : Fin n → ℤ => c μ i j))
            + Work.Diff.STE.ENormSq 0 (Work.Diff.STE.seriesFun (fun μ : Fin n → ℤ => c μ i j))) := h
      _ ≤ C2 * ENormSqFull L (seriesFunM c) := by
          rw [ENormSqFull]
          exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC20
  have hE0 : 0 ≤ ENormSqFull L (seriesFunM c) := ENormSqFull_nonneg L _
  have h2pi : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  have hmassle : (∑' μ : Fin n → ℤ, (wt μ) ^ ((L : ℝ) - (m : ℝ))
        * ‖Work.Diff.STE.dmulV q (fun μ : Fin n → ℤ => c μ i j) μ‖ ^ 2)
      ≤ (((2 * Real.pi) ^ 2) ^ L) * (C2 * ENormSqFull L (seriesFunM c)) := by
    refine hmass.2.trans ?_
    refine mul_le_mul ?_ hCSQ' (Work.Diff.STE.CSq_nonneg L _) (by positivity)
    exact pow_le_pow_right₀ h2pi (by rw [hq]; exact hmL)
  have htsum0 : 0 ≤ ∑' μ : Fin n → ℤ, (wt μ) ^ ((L : ℝ) - (m : ℝ))
      * ‖Work.Diff.STE.dmulV q (fun μ : Fin n → ℤ => c μ i j) μ‖ ^ 2 :=
    tsum_nonneg fun μ => mul_nonneg (Real.rpow_nonneg (le_of_lt (wt_pos μ)) _) (sq_nonneg _)
  calc rnorm r (Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV q (fun μ : Fin n → ℤ => c μ i j)))
      ≤ Cun * (∑' μ : Fin n → ℤ, (wt μ) ^ ((L : ℝ) - (m : ℝ))
            * ‖Work.Diff.STE.dmulV q (fun μ : Fin n → ℤ => c μ i j) μ‖ ^ 2) ^ (1 / 2 : ℝ) := hsob
    _ ≤ Cun * ((((2 * Real.pi) ^ 2) ^ L) * (C2 * ENormSqFull L (seriesFunM c))) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow htsum0 hmassle (by norm_num)) hCun0
    _ = Cun * (2 * Real.pi) ^ L * Real.sqrt C2 * Real.sqrt (ENormSqFull L (seriesFunM c)) := by
        have hA : (((2 * Real.pi) ^ 2) ^ L) = ((2 * Real.pi) ^ L) ^ 2 := by
          rw [← pow_mul]; ring_nf
        have hB : ((((2 * Real.pi) ^ L) ^ 2 : ℝ)) ^ (1 / 2 : ℝ) = (2 * Real.pi) ^ L := by
          rw [← Real.rpow_natCast ((2 * Real.pi) ^ L) 2, ← Real.rpow_mul (by positivity)]
          norm_num
        rw [hA, Real.mul_rpow (by positivity) (mul_nonneg hC20 hE0), Real.mul_rpow hC20 hE0,
          Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, hB]
        ring

/-- **Uniform `L^r` bound for the jets of the symmetrised inverse metric.**  For a box-supported
coefficient family with level-`L` energy at most `B²` and uniformly `lam`-elliptic real part, every
derivative `∂^q (symInvC c a b)` of order `m ≤ L` whose price `m + n/2 - n/r + 1/2` is at most
`L` is bounded in `L^r` by a constant, uniformly in `N`, `c`, `a`, `b`, `q` and `r`. -/
lemma csb_symInvC_rnorm_le_level {n : ℕ} (hn : 1 ≤ n) (L : ℕ) (hσ : sob n ≤ L)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) →
      ENormSqFull L (seriesFunM c) ≤ B ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          reMat (seriesFunM c x) i j * v i * v j) →
      ∀ (m : ℕ) (r : ℝ), 2 ≤ r →
        (m : ℝ) + (n : ℝ) / 2 - (n : ℝ) / r + 1 / 2 ≤ (L : ℝ) → m ≤ L →
        ∀ (a b : Fin n) (q : List (Fin n)), q.length = m →
          rnorm r (pdList q (fun y => symInvC c a b y)) ≤ C := by
  obtain ⟨Cun, hCun0, hCun⟩ := rnorm_seriesFun_uniform (ι := Fin n)
  obtain ⟨Cinv, hCinv0, hCinv⟩ := CSq_symInvC_le hn L hσ lam hlam B hB
  refine ⟨Cun * (2 * Real.pi) ^ L * Real.sqrt Cinv, by positivity, ?_⟩
  intro N c hc hen hell m r hr hprice hmL a b q hq
  obtain ⟨hsm, hper⟩ := symInvC_contDiff_periodic hσ hB hlam hc hen hell a b
  have hmom2 : ∀ K : ℕ, Summable (fun μ : Fin n → ℤ =>
      (wt μ) ^ K * ‖fourierCoeff (fun y : Fin n → ℝ => symInvC c a b y) μ‖ ^ 2) :=
    fun K => summable_weighted_fourierCoeff_of_contDiff _ hsm hper K
  have hmom1 : ∀ K : ℕ, Summable (fun μ : Fin n → ℤ =>
      (wt μ) ^ K * ‖fourierCoeff (fun y : Fin n → ℝ => symInvC c a b y) μ‖) :=
    fun K => invJet_summable_moment_of_wt_sq _ hmom2 K
  have hser : (fun y : Fin n → ℝ => symInvC c a b y)
      = Work.Diff.STE.seriesFun (fourierCoeff (fun y : Fin n → ℝ => symInvC c a b y)) :=
    funext fun x => (seriesFun_fourierCoeff _ hsm hper x).symm
  have hpd : pdList q (fun y : Fin n → ℝ => symInvC c a b y)
      = Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV q
          (fourierCoeff (fun y : Fin n → ℝ => symInvC c a b y))) := by
    conv_lhs => rw [hser]
    exact funext (fun x => Work.Diff.STE.pdList_seriesFun q _ hmom1 x)
  have hj : (Fintype.card (Fin n) : ℝ) * (1 / 2 - 1 / (2 * (r / 2))) + 1 / 2
      ≤ (L : ℝ) - (m : ℝ) := by
    simp only [Fintype.card_fin]
    have hcast : (n : ℝ) * (1 / 2 - 1 / (2 * (r / 2))) = (n : ℝ) / 2 - (n : ℝ) / r := by
      field_simp
    linarith [hprice, hcast]
  have hqm : (q.length : ℝ) = (m : ℝ) := by exact_mod_cast hq
  have hmass := summable_wt_dmulV_le q ((L : ℝ) - (m : ℝ)) L _
    (by linarith) (hmom2 L)
  have hsob := hCun (r / 2) (by linarith) ((L : ℝ) - (m : ℝ)) hj
    (Work.Diff.STE.dmulV q (fourierCoeff (fun y : Fin n → ℝ => symInvC c a b y))) hmass.1
  rw [show 2 * (r / 2) = r by ring] at hsob
  rw [hpd]
  have hCSQ' : Work.Diff.STE.CSq L (fourierCoeff (fun y : Fin n → ℝ => symInvC c a b y))
      ≤ Cinv := hCinv N c hc hen hell a b
  have h2pi : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  have hmassle : (∑' μ : Fin n → ℤ, (wt μ) ^ ((L : ℝ) - (m : ℝ))
        * ‖Work.Diff.STE.dmulV q
            (fourierCoeff (fun y : Fin n → ℝ => symInvC c a b y)) μ‖ ^ 2)
      ≤ (((2 * Real.pi) ^ 2) ^ L) * Cinv := by
    refine hmass.2.trans ?_
    refine mul_le_mul ?_ hCSQ' (Work.Diff.STE.CSq_nonneg L _) (by positivity)
    exact pow_le_pow_right₀ h2pi (by rw [hq]; exact hmL)
  have htsum0 : 0 ≤ ∑' μ : Fin n → ℤ, (wt μ) ^ ((L : ℝ) - (m : ℝ))
      * ‖Work.Diff.STE.dmulV q
          (fourierCoeff (fun y : Fin n → ℝ => symInvC c a b y)) μ‖ ^ 2 :=
    tsum_nonneg fun μ => mul_nonneg (Real.rpow_nonneg (le_of_lt (wt_pos μ)) _) (sq_nonneg _)
  calc rnorm r (Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV q
        (fourierCoeff (fun y : Fin n → ℝ => symInvC c a b y))))
      ≤ Cun * (∑' μ : Fin n → ℤ, (wt μ) ^ ((L : ℝ) - (m : ℝ))
            * ‖Work.Diff.STE.dmulV q
                (fourierCoeff (fun y : Fin n → ℝ => symInvC c a b y)) μ‖ ^ 2) ^ (1 / 2 : ℝ) := hsob
    _ ≤ Cun * ((((2 * Real.pi) ^ 2) ^ L) * Cinv) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow htsum0 hmassle (by norm_num)) hCun0
    _ = Cun * (2 * Real.pi) ^ L * Real.sqrt Cinv := by
        have hA : (((2 * Real.pi) ^ 2) ^ L) = ((2 * Real.pi) ^ L) ^ 2 := by
          rw [← pow_mul]; ring_nf
        have hB : ((((2 * Real.pi) ^ L) ^ 2 : ℝ)) ^ (1 / 2 : ℝ) = (2 * Real.pi) ^ L := by
          rw [← Real.rpow_natCast ((2 * Real.pi) ^ L) 2, ← Real.rpow_mul (by positivity)]
          norm_num
        rw [hA, Real.mul_rpow (by positivity) hCinv0, Real.sqrt_eq_rpow, hB]
        ring


/-- **The elementary bounds of the weight** `W = (1+B)² (1 + √(1+E))` used to price the
per-term estimates of the sharp commutator bound. -/
lemma csb_W_bounds {B Ef : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ Ef) :
    1 ≤ (1 + B) ^ 2 * (1 + Real.sqrt (1 + Ef)) ∧
    B ≤ (1 + B) ^ 2 * (1 + Real.sqrt (1 + Ef)) ∧
    B ^ 2 ≤ (1 + B) ^ 2 * (1 + Real.sqrt (1 + Ef)) ∧
    B * (1 + Real.sqrt (1 + Ef)) ≤ (1 + B) ^ 2 * (1 + Real.sqrt (1 + Ef)) ∧
    Real.sqrt Ef ≤ 1 + Real.sqrt (1 + Ef) := by
  have hs : (0 : ℝ) ≤ Real.sqrt (1 + Ef) := Real.sqrt_nonneg _
  have h2 : (1 : ℝ) ≤ 1 + Real.sqrt (1 + Ef) := by linarith
  have h1 : (1 : ℝ) ≤ (1 + B) ^ 2 := by nlinarith
  have hB1 : B ≤ (1 + B) ^ 2 := by nlinarith
  have hB2 : B ^ 2 ≤ (1 + B) ^ 2 := by nlinarith
  have h5 : Real.sqrt Ef ≤ 1 + Real.sqrt (1 + Ef) := by
    have h := Real.sqrt_le_sqrt (show Ef ≤ 1 + Ef by linarith)
    linarith
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, h5⟩


/-- `L2re` only sees the product up to commutation. -/
lemma csb_l2re_mul_comm {n : ℕ} {f g h : (Fin n → ℝ) → ℂ} :
    Work.Diff.STE.L2re (fun x => f x * g x) h = Work.Diff.STE.L2re (fun x => g x * f x) h := by
  simp only [Work.Diff.STE.L2re]
  apply congrArg Complex.re
  apply integral_congr_ae
  filter_upwards with x
  ring

/-- **Three-factor estimate with a sup bound on the second factor.** -/
lemma csb_l2re_mul_sup_le {n : ℕ} {F G h : (Fin n → ℝ) → ℂ} {M : ℝ}
    (hFc : Continuous F) (hGc : Continuous G) (hhc : Continuous h) (hGb : ∀ x, ‖G x‖ ≤ M) :
    |Work.Diff.STE.L2re (fun x => F x * G x) h| ≤ M * rnorm 2 F * rnorm 2 h := by
  rw [csb_l2re_mul_comm (f := F) (g := G) (h := h)]
  exact csb_l2re_sup_mul_le hGc hFc hhc hGb

/-- The second derivative as a `pdVec` of order `2`. -/
lemma csb_pdVec_two {n : ℕ} (a b : Fin n) (f : (Fin n → ℝ) → ℂ) :
    pd a (pd b f) = pdVec 2 ![a, b] f := by
  simp [pdVec, pdList]

/-- `pdVec` along the entries of a list is `pdList`. -/
lemma csb_pdVec_get {n : ℕ} (q : List (Fin n)) (f : (Fin n → ℝ) → ℂ) :
    pdVec q.length (fun t : Fin q.length => q.get t) f = pdList q f := by
  simp [pdVec, List.ofFn_get]

/-- The `L²` norm of any iterated derivative is dominated by the matrix energy of the same order. -/
lemma csb_int_pdList_le_ENormSqM {n : ℕ} (u : Torus n) (i j : Fin n) (q : List (Fin n)) :
    ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖pdList q (fun y => u y i j) x‖ ^ 2
      ≤ ENormSqM q.length u := by
  have h := int_pdVec_le_ENormSqM u i j (fun t : Fin q.length => q.get t)
  simpa only [pdVec, List.ofFn_get] using h

/-- The Hölder exponent condition in the form needed by `L2re_mul_mul_le_rnorm`. -/
lemma csb_hsum {r1 r2 : ℝ} (h : 1 / r1 + 1 / r2 = 1 / 2) :
    1 / (r1 / 2) + 1 / (r2 / 2) = 1 := by
  rw [div_div_eq_mul_div, div_div_eq_mul_div]
  have h1 : 1 * 2 / r1 = 2 * (1 / r1) := by ring
  have h2 : 1 * 2 / r2 = 2 * (1 / r2) := by ring
  rw [h1, h2]
  linarith only [h]

/-- **The exponent allocation for the middle range.**  If `α` lies in the window
`[max 0 (m + n/2 + 1/2 - k), min (n/2) (m - 3/2)]`, then the pair
`(r₁, r₂) = (n/α, n/(n/2 - α))` has both exponents `> 2`, conjugate exponents
`1/r₁ + 1/r₂ = 1/2`, and the two prices `m + n/2 - n/r₁ + 1/2` and
`(k - m + 2) + n/2 - n/r₂ + 1/2` are at most `k` and `k+1`. -/
lemma csb_rpow_prices {n k m : ℕ} (hn : 1 ≤ n) (hm2 : 2 ≤ m) {α : ℝ}
    (hα0 : 0 < α) (hαn : α < (n : ℝ) / 2)
    (hlo : max 0 ((m : ℝ) + (n : ℝ) / 2 + 1 / 2 - (k : ℝ)) ≤ α)
    (hhi : α ≤ min ((n : ℝ) / 2) ((m : ℝ) - 3 / 2)) :
    ∃ r1 r2 : ℝ, 2 < r1 ∧ 2 < r2 ∧ 1 / r1 + 1 / r2 = 1 / 2 ∧
      (m : ℝ) + (n : ℝ) / 2 - (n : ℝ) / r1 + 1 / 2 ≤ (k : ℝ) ∧
      ((k : ℝ) - (m : ℝ) + 2) + (n : ℝ) / 2 - (n : ℝ) / r2 + 1 / 2 ≤ (k : ℝ) + 1 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hβ0 : 0 < (n : ℝ) / 2 - α := by linarith
  set r1 : ℝ := (n : ℝ) / α with hr1
  set r2 : ℝ := (n : ℝ) / ((n : ℝ) / 2 - α) with hr2
  have hα0' : α ≠ 0 := ne_of_gt hα0
  have hβ0' : (n : ℝ) / 2 - α ≠ 0 := ne_of_gt hβ0
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hnr1 : (n : ℝ) / r1 = α := by rw [hr1]; field_simp
  have hnr2 : (n : ℝ) / r2 = (n : ℝ) / 2 - α := by rw [hr2]; field_simp
  have hr1gt : 2 < r1 := by
    rw [hr1, lt_div_iff₀ hα0]
    linarith
  have hr2gt : 2 < r2 := by
    rw [hr2, lt_div_iff₀ hβ0]
    linarith
  have hlt1 : (m : ℝ) + (n : ℝ) / 2 + 1 / 2 - (k : ℝ) ≤ α :=
    le_trans (le_max_right 0 ((m : ℝ) + (n : ℝ) / 2 + 1 / 2 - (k : ℝ))) hlo
  have hle2 : α ≤ (m : ℝ) - 3 / 2 :=
    le_trans hhi (min_le_right ((n : ℝ) / 2) ((m : ℝ) - 3 / 2))
  refine ⟨r1, r2, hr1gt, hr2gt, ?_, ?_, ?_⟩
  · have h1 : 1 / r1 = α / (n : ℝ) := by rw [hr1, one_div_div]
    have h2 : 1 / r2 = ((n : ℝ) / 2 - α) / (n : ℝ) := by rw [hr2, one_div_div]
    rw [h1, h2]
    field_simp
    ring
  · rw [hnr1]
    linarith only [hlt1]
  · rw [hnr2]
    linarith only [hle2]

/-- **The bookkeeping of the Leibniz expansion.**  Given the iterated Leibniz rule in difference
form and a uniform bound on each of the Leibniz terms, the `L²` pairing of the commutator with `h`
is bounded by the number `2^{|L|}` of Leibniz terms times that bound. -/
lemma csb_comm_bound_k {n k : ℕ} {F g h : (Fin n → ℝ) → ℂ} (L : List (Fin n))
    (hlen : L.length = k)
    (hleib : (fun y => pdList L (fun z => F z * g z) y - F y * pdList L g y)
        = fun y => (((splits L).filter (fun p => p.1 ≠ [])).map
            (fun p => pdList p.1 F y * pdList p.2 g y)).sum)
    (hcontF : ∀ q : List (Fin n), q.length ≤ L.length → Continuous (pdList q F))
    (hcontg : ∀ q : List (Fin n), q.length ≤ L.length → Continuous (pdList q g))
    (hconth : Continuous h)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hterm : ∀ p ∈ (splits L).filter (fun p => p.1 ≠ []),
        |Work.Diff.STE.L2re (fun y => pdList p.1 F y * pdList p.2 g y) h| ≤ K) :
    |Work.Diff.STE.L2re (fun y => pdList L (fun z => F z * g z) y - F y * pdList L g y) h|
      ≤ (2 : ℝ) ^ k * K := by
  set Sf : List (List (Fin n) × List (Fin n)) := (splits L).filter (fun p => p.1 ≠ []) with hSf
  have hfun : (fun y => (List.map (fun p => pdList p.1 F y * pdList p.2 g y) Sf).sum)
      = (Sf.map (fun p => fun y => pdList p.1 F y * pdList p.2 g y)).sum :=
    Work.Diff.STE.cm_list_sum_apply Sf _
  have hcontSf : ∀ p ∈ Sf, Continuous (fun y => pdList p.1 F y * pdList p.2 g y) := by
    intro p hp
    obtain ⟨hp', _⟩ := List.mem_filter.mp hp
    have hlenp := Work.Diff.STE.cm_splits_mem_length L p hp'
    exact (hcontF p.1 (by omega)).mul (hcontg p.2 (by omega))
  have hlin : Work.Diff.STE.L2re ((Sf.map (fun p => fun y => pdList p.1 F y * pdList p.2 g y)).sum) h
      = (Sf.map (fun p => Work.Diff.STE.L2re (fun y => pdList p.1 F y * pdList p.2 g y) h)).sum :=
    Work.Diff.STE.cm_L2re_list_sum Sf _ h hcontSf hconth
  have hsumle : |(Sf.map (fun p => Work.Diff.STE.L2re
        (fun y => pdList p.1 F y * pdList p.2 g y) h)).sum|
      ≤ (Sf.map (fun _ => K)).sum := by
    refine (Work.Diff.STE.cm_list_abs_sum_le Sf _).trans ?_
    exact List.sum_le_sum (fun p hp => hterm p hp)
  have hconst : (Sf.map (fun _ => K)).sum = (Sf.length : ℝ) * K := by
    induction Sf with
    | nil => simp
    | cons a L ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
        rw [ih]; push_cast; ring
  have hlenSf : (Sf.length : ℝ) ≤ ((splits L).length : ℝ) := by
    have h : Sf.length ≤ (splits L).length := by rw [hSf]; exact List.length_filter_le _ _
    exact_mod_cast h
  calc |Work.Diff.STE.L2re (fun y => pdList L (fun z => F z * g z) y - F y * pdList L g y) h|
      = |Work.Diff.STE.L2re ((Sf.map (fun p => fun y => pdList p.1 F y * pdList p.2 g y)).sum) h| := by
        rw [hleib, hfun]
    _ = |(Sf.map (fun p => Work.Diff.STE.L2re
          (fun y => pdList p.1 F y * pdList p.2 g y) h)).sum| := by rw [hlin]
    _ ≤ (Sf.length : ℝ) * K := by rw [← hconst]; exact hsumle
    _ ≤ ((splits L).length : ℝ) * K := mul_le_mul_of_nonneg_right hlenSf hK0
    _ = (2 : ℝ) ^ k * K := by
        rw [Work.Diff.STE.cm_splits_length_count, hlen]; push_cast; ring

/-- **The final absorption.**  The weight `W = (1+B)² (1 + √(1+Ef))` is absorbed into the
level-`(k+1)` dissipation `ν · EM` using `√(1+Ef) ≤ √(1+B²) √(1+EM)`, which follows from
`Ef ≤ EM + B²`. -/
lemma csb_absorb {Ctot Ef EM B ν : ℝ} (hν : 0 < ν) (hCtot : 0 ≤ Ctot) (hB : 0 ≤ B)
    (hEM0 : 0 ≤ EM) (hEf0 : 0 ≤ Ef) (hEf : Ef ≤ EM + B ^ 2) :
    Ctot * ((1 + B) ^ 2 * (1 + Real.sqrt (1 + Ef)))
      ≤ ν * EM + (Ctot * (1 + B) ^ 2
          + (ν / 2 + (Ctot * (1 + B) ^ 2 * Real.sqrt (1 + B ^ 2)) ^ 2 / (2 * ν))) := by
  have hK0 : 0 ≤ Ctot * (1 + B) ^ 2 * Real.sqrt (1 + B ^ 2) := by positivity
  have hle1 : 1 + Ef ≤ (1 + B ^ 2) * (1 + EM) := by nlinarith
  have hsq : Real.sqrt (1 + Ef) ≤ Real.sqrt (1 + B ^ 2) * Real.sqrt (1 + EM) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hle1
  have hab := csb_sqrt_one_add_absorb hν hK0 hEM0
  have h1 : (1 : ℝ) + Real.sqrt (1 + Ef)
      ≤ 1 + Real.sqrt (1 + B ^ 2) * Real.sqrt (1 + EM) := by linarith
  have h2 : Ctot * (1 + B) ^ 2 * (1 + Real.sqrt (1 + Ef))
      ≤ Ctot * (1 + B) ^ 2 * (1 + Real.sqrt (1 + B ^ 2) * Real.sqrt (1 + EM)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : Ctot * ((1 + B) ^ 2 * (1 + Real.sqrt (1 + Ef)))
      = Ctot * (1 + B) ^ 2 * (1 + Real.sqrt (1 + Ef)) := by ring
  have h4 : Ctot * (1 + B) ^ 2 * (1 + Real.sqrt (1 + B ^ 2) * Real.sqrt (1 + EM))
      = Ctot * (1 + B) ^ 2
        + Ctot * (1 + B) ^ 2 * Real.sqrt (1 + B ^ 2) * Real.sqrt (1 + EM) := by ring
  rw [h3]
  refine h2.trans ?_
  rw [h4]
  linarith only [hab]

set_option maxHeartbeats 800000 in
theorem comm_sharp_bound {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
    (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B)
    (lam' : ℝ) (hlam' : 0 < lam') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
      Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM c) ≤ B ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
      (∀ (x : Fin n → ℝ) (ξ : Fin n → ℝ),
        lam' * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.flat.symInvR c i j x * ξ i * ξ j) →
      (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n,
        |∑ l : Fin k → Fin n,
            Work.Diff.STE.L2re (fun x => Work.Diff.STE.pdVec k l (fun y =>
                Work.Diff.STE.flat.symInvC c a b y
                  * Work.Diff.STE.pd a (Work.Diff.STE.pd b
                      (fun z => Work.Diff.STE.Flat.seriesFunM c z i j)) y) x
                - Work.Diff.STE.flat.symInvC c a b x * Work.Diff.STE.pdVec k l
                    (fun z => Work.Diff.STE.pd a (Work.Diff.STE.pd b
                        (fun w => Work.Diff.STE.Flat.seriesFunM c w i j)) z) x)
              (Work.Diff.STE.pdVec k l (fun x => Work.Diff.STE.Flat.seriesFunM c x i j))|)
        ≤ (lam' / 8) * Work.Diff.STE.Flat.ENormSqM (k + 1) (Work.Diff.STE.Flat.seriesFunM c) + C := by
  have hσ : sob n ≤ k := by
    have h : n + 4 < 2 * k := by simpa using hk
    simp only [sob]; omega
  have h2σ : 2 + sob n ≤ k := by
    have h : n + 4 < 2 * k := by simpa using hk
    simp only [sob]; omega
  have h1σ : 1 + sob n ≤ k := by omega
  obtain ⟨CU, hCU0, hU⟩ := csb_u_rnorm_le_level (n := n) hn (k + 1)
  obtain ⟨CF, hCF0, hF⟩ := csb_symInvC_rnorm_le_level (n := n) hn k hσ lam hlam B hB
  obtain ⟨Cinv, hCinv0, hCinv⟩ := CSq_symInvC_le hn k hσ lam hlam B hB
  obtain ⟨Csup, hCsup0, hCsup⟩ := Work.Diff.STE.norm_seriesFun_le (ι := Fin n) (sob n)
    (by simpa using n_lt_two_sob n)
  obtain ⟨CL2, hCL20, hCL2⟩ := symInvC_pdList_L2_le hn k hk lam hlam B hB
  obtain ⟨CG, hCG0, hCG⟩ := jet_sup_le_uniform_level (n := n) (s := k)
  set CSF : ℝ := Csup * (2 * Real.pi) ^ k * Real.sqrt Cinv with hCSF
  set CSG : ℝ := CG * (1 + B) with hCSG
  have hCSF0 : 0 ≤ CSF := by rw [hCSF]; positivity
  have hCSG0 : 0 ≤ CSG := by rw [hCSG]; positivity
  set Q : ℝ := CU + CF + CSF + CSG + Real.sqrt CL2 + 1 with hQ
  have hQ1 : 1 ≤ Q := by rw [hQ]; linarith [hCU0, hCF0, hCSF0, hCSG0, Real.sqrt_nonneg CL2]
  have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ1
  have hCUQ : CU ≤ Q := by rw [hQ]; linarith [hCF0, hCSF0, hCSG0, Real.sqrt_nonneg CL2]
  have hCFQ : CF ≤ Q := by rw [hQ]; linarith [hCU0, hCSF0, hCSG0, Real.sqrt_nonneg CL2]
  have hCSFQ : CSF ≤ Q := by rw [hQ]; linarith [hCU0, hCF0, hCSG0, Real.sqrt_nonneg CL2]
  have hCSGQ : CSG ≤ Q := by rw [hQ]; linarith [hCU0, hCF0, hCSF0, Real.sqrt_nonneg CL2]
  have hCL2Q : Real.sqrt CL2 ≤ Q := by rw [hQ]; linarith [hCU0, hCF0, hCSF0, hCSG0]
  set Kc : ℝ := Q ^ 3 with hKc
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  have hKc1 : 1 ≤ Kc := by rw [hKc]; exact one_le_pow₀ hQ1
  have hQleKc : Q ≤ Kc := by
    rw [hKc]
    calc Q = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ 3 := pow_le_pow_right₀ hQ1 (by norm_num)
  -- the two-factor products are dominated by `Kc`
  have hCSF_Kc : CSF ≤ Kc := le_trans hCSFQ hQleKc
  have hprod1 : CF * CU ≤ Kc := by
    refine le_trans (mul_le_mul hCFQ hCUQ hCU0 hQ0) ?_
    calc Q * Q = Q ^ 2 := (pow_two Q).symm
      _ ≤ Q ^ 3 := pow_le_pow_right₀ hQ1 (by norm_num)
  have hprod2 : Real.sqrt CL2 * CSG ≤ Kc := by
    refine le_trans (mul_le_mul hCL2Q hCSGQ hCSG0 hQ0) ?_
    calc Q * Q = Q ^ 2 := (pow_two Q).symm
      _ ≤ Q ^ 3 := pow_le_pow_right₀ hQ1 (by norm_num)
  set NC : ℝ := (n : ℝ) ^ 4 * (Fintype.card (Fin k → Fin n) : ℝ) * (2 : ℝ) ^ k with hNC
  have hNC0 : 0 ≤ NC := by rw [hNC]; positivity
  set Ctot : ℝ := NC * Kc with hCtot
  have hCtot0 : 0 ≤ Ctot := by rw [hCtot]; positivity
  set ν : ℝ := lam' / 8 with hν
  have hν0 : 0 < ν := by rw [hν]; positivity
  set Kb : ℝ := Ctot * (1 + B) ^ 2 * Real.sqrt (1 + B ^ 2) with hKb
  have hKb0 : 0 ≤ Kb := by rw [hKb]; positivity
  set Cf : ℝ := Ctot * (1 + B) ^ 2 + (ν / 2 + Kb ^ 2 / (2 * ν)) with hCf
  refine ⟨Cf, ?_, ?_⟩
  · rw [hCf]; positivity
  intro N c hbox hen hell hcoerc
  obtain ⟨_lam0, _hlam0, _Cg, _hCg, hgb⟩ := symInv_garding_bounds hn k hk lam hlam B hB
  obtain ⟨hsmR, hsmC, hperR, hperC, hpdr, hgard⟩ := hgb N c hbox hen hell
  -- smoothness of the entries of the solution
  have hsol : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => seriesFunM c y i j) := by
    intro i j
    have h := Work.Diff.STE.contDiff_seriesFun (c := fun m : Fin n → ℤ => c m i j)
      (fun M => summable_moment_box c hbox i j M)
    simpa only [seriesFunM_apply] using h
  -- the energies and the target weight
  set Efull : ℝ := ENormSqFull (k + 1) (seriesFunM c) with hEfull
  have hEfull0 : 0 ≤ Efull := by rw [hEfull]; exact ENormSqFull_nonneg (k + 1) _
  have hE0le : ENormSqM 0 (seriesFunM c) ≤ B ^ 2 :=
    (le_trans (by rw [ENormSqFull]; exact le_add_of_nonneg_left (ENormSqM_nonneg k _)) hen)
  set W : ℝ := (1 + B) ^ 2 * (1 + Real.sqrt (1 + Efull)) with hW
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := csb_W_bounds (B := B) (Ef := Efull) hB hEfull0
  have hW1 : 1 ≤ W := by rw [hW]; exact hb1
  have hW0 : 0 ≤ W := le_trans zero_le_one hW1
  have hBleW : B ≤ W := by rw [hW]; exact hb2
  have hB2leW : B ^ 2 ≤ W := by rw [hW]; exact hb3
  have hBSleW : B * (1 + Real.sqrt (1 + Efull)) ≤ W := by rw [hW]; exact hb4
  have hsqrtE : Real.sqrt Efull ≤ 1 + Real.sqrt (1 + Efull) := hb5
  -- sup bound on the jets of the symmetrised inverse metric
  have hsupF : ∀ (a b : Fin n) (q : List (Fin n)) (x : Fin n → ℝ),
      q.length + sob n ≤ k → ‖pdList q (fun y => symInvC c a b y) x‖ ≤ CSF := by
    intro a b q x hq
    have hmom2 : ∀ K : ℕ, Summable (fun m : Fin n → ℤ =>
        (wt m) ^ K * ‖fourierCoeff (fun y : Fin n → ℝ => symInvC c a b y) m‖ ^ 2) :=
      fun K => summable_weighted_fourierCoeff_of_contDiff _ (hsmC a b) (hperC a b) K
    have hmom1 : ∀ K : ℕ, Summable (fun m : Fin n → ℤ =>
        (wt m) ^ K * ‖fourierCoeff (fun y : Fin n → ℝ => symInvC c a b y) m‖) :=
      fun K => invJet_summable_moment_of_wt_sq _ hmom2 K
    have hcsq : CSq k (fourierCoeff (fun y : Fin n → ℝ => symInvC c a b y)) ≤ Cinv * (1 + 0) ^ 2 := by
      simpa using hCinv N c hbox hen hell a b
    have h := invJet_sup_pdVec_seriesFun_le (n := n) (s := k) hσ (d := fourierCoeff
        (fun y : Fin n → ℝ => symInvC c a b y)) hmom1 hCsup0 hCsup hCinv0 (by norm_num) hcsq
      q.length hq (fun t : Fin q.length => q.get t) x
    have hser : Work.Diff.STE.seriesFun (fourierCoeff (fun z : Fin n → ℝ => symInvC c a b z))
        = fun y : Fin n → ℝ => symInvC c a b y :=
      funext fun y => seriesFun_fourierCoeff _ (hsmC a b) (hperC a b) y
    rw [hser] at h
    simpa only [hCSF, pdVec, List.ofFn_get, add_zero, mul_one] using h
  -- sup bound on the jets of the solution
  have hsupG : ∀ (m : ℕ) (l : Fin m → Fin n) (i j : Fin n) (x : Fin n → ℝ),
      m + sob n ≤ k → ‖pdVec m l (fun y => seriesFunM c y i j) x‖ ≤ CSG := by
    intro m l i j x hm
    have h := hCG m hm N c hbox l i j x
    have hsqrt : Real.sqrt (ENormSqFull k (seriesFunM c)) ≤ B := by
      rw [← Real.sqrt_sq hB]; exact Real.sqrt_le_sqrt hen
    calc ‖pdVec m l (fun y => seriesFunM c y i j) x‖
        ≤ CG * (1 + Real.sqrt (ENormSqFull k (seriesFunM c))) := h
      _ ≤ CG * (1 + B) := by nlinarith only [hCG0, hsqrt]
      _ = CSG := by rw [hCSG]
  -- `L²` bounds for the three factors of a Leibniz term
  have hL2w : ∀ (i j : Fin n) (l : Fin k → Fin n),
      rnorm 2 (pdVec k l (fun y => seriesFunM c y i j)) ≤ B := by
    intro i j l
    rw [rnorm_two_eq_sqrt]
    refine (Real.sqrt_le_sqrt ?_).trans (le_of_eq (Real.sqrt_sq hB))
    exact (int_pdVec_le_ENormSqM (seriesFunM c) i j l).trans
      ((ENormSqM_le_ENormSqFull k _).trans hen)
  have hL2Gtop : ∀ (i j : Fin n) (q : List (Fin n)), q.length = k + 1 →
      rnorm 2 (pdList q (fun y => seriesFunM c y i j)) ≤ Real.sqrt Efull := by
    intro i j q hq
    have h1 : ENormSqM q.length (seriesFunM c) ≤ Efull := by
      rw [hEfull, hq]; exact ENormSqM_le_ENormSqFull (k + 1) _
    rw [rnorm_two_eq_sqrt]
    exact Real.sqrt_le_sqrt ((csb_int_pdList_le_ENormSqM (seriesFunM c) i j q).trans h1)
  have hL2F : ∀ (a b : Fin n) (q : List (Fin n)), q.length ≤ k →
      rnorm 2 (pdList q (fun y => symInvC c a b y)) ≤ Real.sqrt CL2 := by
    intro a b q hq
    rw [rnorm_two_eq_sqrt]
    exact Real.sqrt_le_sqrt (hCL2 N c hbox hen hell a b q hq)
  -- **the per-term bound**
  have hterm : ∀ (a b i j : Fin n) (l : Fin k → Fin n) (γ' δ' : List (Fin n)),
      γ'.length + δ'.length = k → 1 ≤ γ'.length →
      |Work.Diff.STE.L2re (fun x => pdList γ' (fun y => symInvC c a b y) x
            * pdList δ' (fun y => pd a (pd b (fun z => seriesFunM c z i j)) y) x)
          (pdVec k l (fun y => seriesFunM c y i j))| ≤ Kc * W := by
    intro a b i j l γ' δ' hlen hγ1
    have hGkey : pdList δ' (fun y : Fin n → ℝ => pd a (pd b (fun z => seriesFunM c z i j)) y)
        = pdList (δ' ++ [a, b]) (fun y => seriesFunM c y i j) :=
      Work.Diff.STE.cm_pdList_pair δ' a b _
    have hcontF : Continuous (pdList γ' (fun y => symInvC c a b y)) :=
      (contDiff_pdList_top (hsmC a b) γ').continuous
    have hcontG : Continuous (pdList δ' (fun y : Fin n → ℝ =>
        pd a (pd b (fun z => seriesFunM c z i j)) y)) :=
      (contDiff_pdList_top (contDiff_pd_top (contDiff_pd_top (hsol i j) b) a) δ').continuous
    have hcontw : Continuous (pdVec k l (fun y => seriesFunM c y i j)) :=
      (contDiff_pdList_top (hsol i j) (List.ofFn l)).continuous
    have hmle : γ'.length ≤ k := by omega
    have hw := hL2w i j l
    rcases lt_or_ge γ'.length k with hlt | hge
    · rcases lt_or_ge γ'.length 2 with hlt2 | hge2
      · -- `γ'.length = 1`: sup on the coefficient, `L²` on the two remaining factors
        have hm1 : γ'.length = 1 := by omega
        have hδk : (δ' ++ [a, b]).length = k + 1 := by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega
        have hGtop : rnorm 2 (pdList δ' (fun y : Fin n → ℝ =>
            pd a (pd b (fun z => seriesFunM c z i j)) y)) ≤ Real.sqrt Efull := by
          rw [hGkey]
          exact hL2Gtop i j (δ' ++ [a, b]) hδk
        have hsup : ∀ x, ‖pdList γ' (fun y => symInvC c a b y) x‖ ≤ CSF :=
          fun x => hsupF a b γ' x (by omega)
        have hmain := csb_l2re_sup_mul_le hcontF hcontG hcontw hsup
        have hWsqrtB : Real.sqrt Efull * B ≤ W := by
          have h1 : Real.sqrt Efull * B ≤ (1 + Real.sqrt (1 + Efull)) * B :=
            mul_le_mul_of_nonneg_right hsqrtE hB
          exact le_trans h1 (by rw [mul_comm (1 + Real.sqrt (1 + Efull)) B]; exact hBSleW)
        refine hmain.trans ?_
        calc CSF * rnorm 2 (pdList δ' (fun y : Fin n → ℝ =>
                  pd a (pd b (fun z => seriesFunM c z i j)) y))
                * rnorm 2 (pdVec k l (fun y => seriesFunM c y i j))
            ≤ CSF * Real.sqrt Efull * B := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hGtop hCSF0) hw
                (rnorm_nonneg 2 _) (mul_nonneg hCSF0 (Real.sqrt_nonneg _))
          _ ≤ CSF * W := by
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left hWsqrtB hCSF0
          _ ≤ Kc * W := mul_le_mul_of_nonneg_right hCSF_Kc hW0
      · -- `2 ≤ |γ'| ≤ k - 1`: two-factor Hölder with the sharp exponents
        have hm2 : 2 ≤ γ'.length := hge2
        have hmk : γ'.length ≤ k - 1 := by omega
        obtain ⟨α, hαlo, hαhi, hα0, hαn⟩ := csb_comm_window hn hk hm2 hmk
        obtain ⟨r1, r2, hr1, hr2, hsum, hprice1, hprice2⟩ :=
          csb_rpow_prices hn hm2 hα0 hαn hαlo hαhi
        have hhold := L2re_mul_mul_le_rnorm (p := r1 / 2) (q := r2 / 2)
          (by linarith only [hr1]) (by linarith only [hr2]) (csb_hsum hsum)
          hcontF hcontG hcontw
        rw [show 2 * (r1 / 2) = r1 by ring, show 2 * (r2 / 2) = r2 by ring] at hhold
        have hFb : rnorm r1 (pdList γ' (fun y => symInvC c a b y)) ≤ CF :=
          hF N c hbox hen hell γ'.length r1 (le_of_lt hr1) hprice1 hmle a b γ' rfl
        have hGb : rnorm r2 (pdList δ' (fun y : Fin n → ℝ =>
              pd a (pd b (fun z => seriesFunM c z i j)) y)) ≤ CU * Real.sqrt Efull := by
          rw [hGkey]
          have hδ2 : ((δ' ++ [a, b]).length : ℝ) = (k : ℝ) - (γ'.length : ℝ) + 2 := by
            simp only [List.length_append, List.length_cons, List.length_nil]
            have h : (γ'.length : ℝ) + (δ'.length : ℝ) = (k : ℝ) := by exact_mod_cast hlen
            push_cast
            linarith only [h]
          have hprice : ((δ' ++ [a, b]).length : ℝ) + (n : ℝ) / 2 - (n : ℝ) / r2 + 1 / 2
              ≤ ((k + 1 : ℕ) : ℝ) := by
            push_cast
            rw [hδ2]; linarith only [hprice2]
          have hmle2 : (δ' ++ [a, b]).length ≤ k + 1 := by
            simp only [List.length_append, List.length_cons, List.length_nil]; omega
          exact hU N c hbox (δ' ++ [a, b]).length r2 (le_of_lt hr2) hprice hmle2
            (δ' ++ [a, b]) rfl i j
        have hWsqrtB : Real.sqrt Efull * B ≤ W := by
          have h1 : Real.sqrt Efull * B ≤ (1 + Real.sqrt (1 + Efull)) * B :=
            mul_le_mul_of_nonneg_right hsqrtE hB
          exact le_trans h1 (by rw [mul_comm (1 + Real.sqrt (1 + Efull)) B]; exact hBSleW)
        refine hhold.trans ?_
        refine (mul_le_mul (mul_le_mul hFb hGb (rnorm_nonneg r2 _) hCF0) hw
          (rnorm_nonneg 2 _) (mul_nonneg hCF0 (mul_nonneg hCU0 (Real.sqrt_nonneg _)))).trans ?_
        calc CF * (CU * Real.sqrt Efull) * B = (CF * CU) * (Real.sqrt Efull * B) := by ring
          _ ≤ Kc * W := mul_le_mul hprod1 hWsqrtB (mul_nonneg (Real.sqrt_nonneg _) hB) hKc0
    · -- `γ'.length = k`: `L²` on the coefficient, sup on the second derivative
      have hmk' : γ'.length = k := by omega
      have hδ0 : δ'.length = 0 := by omega
      have hGsup : ∀ x, ‖pdList δ' (fun y : Fin n → ℝ =>
          pd a (pd b (fun z => seriesFunM c z i j)) y) x‖ ≤ CSG := by
        intro x
        have hGv : pdList δ' (fun y : Fin n → ℝ => pd a (pd b (fun z => seriesFunM c z i j)) y)
            = pdVec 2 ![a, b] (fun y => seriesFunM c y i j) := by
          rw [hGkey, List.eq_nil_of_length_eq_zero hδ0, List.nil_append]
          exact (csb_pdVec_two a b (fun y => seriesFunM c y i j)).symm
        rw [hGv]
        exact hsupG 2 ![a, b] i j x h2σ
      have hFL2 : rnorm 2 (pdList γ' (fun y => symInvC c a b y)) ≤ Real.sqrt CL2 :=
        hL2F a b γ' (by omega)
      have hmain := csb_l2re_mul_sup_le hcontF hcontG hcontw hGsup
      refine hmain.trans ?_
      calc CSG * rnorm 2 (pdList γ' (fun y => symInvC c a b y))
              * rnorm 2 (pdVec k l (fun y => seriesFunM c y i j))
          ≤ CSG * Real.sqrt CL2 * B := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hFL2 hCSG0) hw
              (rnorm_nonneg 2 _) (by positivity)
        _ ≤ Kc * W := by
            refine mul_le_mul ?_ hBleW hB hKc0
            rw [mul_comm CSG (Real.sqrt CL2)]; exact hprod2
  -- **the Leibniz bookkeeping for a single direction tuple**
  have hsingle : ∀ (a b i j : Fin n) (l : Fin k → Fin n),
      |Work.Diff.STE.L2re (fun x => Work.Diff.STE.pdVec k l (fun y =>
                symInvC c a b y
                  * pd a (pd b (fun z => seriesFunM c z i j)) y) x
            - symInvC c a b x * Work.Diff.STE.pdVec k l
                (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
          (Work.Diff.STE.pdVec k l (fun x => seriesFunM c x i j))| ≤ (2 : ℝ) ^ k * (Kc * W) := by
    intro a b i j l
    have hFsm : ContDiff ℝ (⊤ : ℕ∞) (fun y => symInvC c a b y) := hsmC a b
    have hGsm : ContDiff ℝ (⊤ : ℕ∞) (fun y => pd a (pd b (fun z => seriesFunM c z i j)) y) :=
      contDiff_pd_top (contDiff_pd_top (hsol i j) b) a
    have hleib := Work.Diff.STE.pdList_mul_sub (List.ofFn l)
      (fun y => symInvC c a b y)
      (fun y => pd a (pd b (fun z => seriesFunM c z i j)) y)
      (fun q _ _ => (contDiff_pdList_top hFsm q).differentiable (by simp))
      (fun q _ _ => (contDiff_pdList_top hGsm q).differentiable (by simp))
    have hterm' : ∀ p ∈ (splits (List.ofFn l)).filter (fun p => p.1 ≠ []),
        |Work.Diff.STE.L2re (fun y => pdList p.1 (fun y => symInvC c a b y) y
            * pdList p.2 (fun y => pd a (pd b (fun z => seriesFunM c z i j)) y) y)
          (pdVec k l (fun y => seriesFunM c y i j))| ≤ Kc * W := by
      intro p hp
      obtain ⟨hp', hneBool⟩ := List.mem_filter.mp hp
      have hlenp := Work.Diff.STE.cm_splits_mem_length (List.ofFn l) p hp'
      have hlen2 : p.1.length + p.2.length = k := by simpa using hlenp
      have h1 : 1 ≤ p.1.length := List.length_pos_of_ne_nil (of_decide_eq_true hneBool)
      exact hterm a b i j l p.1 p.2 hlen2 h1
    have hcontF' : ∀ q : List (Fin n), q.length ≤ (List.ofFn l).length →
        Continuous (pdList q (fun y => symInvC c a b y)) :=
      fun q _ => (contDiff_pdList_top hFsm q).continuous
    have hcontg' : ∀ q : List (Fin n), q.length ≤ (List.ofFn l).length →
        Continuous (pdList q (fun y => pd a (pd b (fun z => seriesFunM c z i j)) y)) :=
      fun q _ => (contDiff_pdList_top hGsm q).continuous
    have hconth' : Continuous (pdVec k l (fun y => seriesFunM c y i j)) :=
      (contDiff_pdList_top (hsol i j) (List.ofFn l)).continuous
    have hres := csb_comm_bound_k (L := List.ofFn l) (k := k) (K := Kc * W)
      (hlen := by simp) (hleib := hleib) (hcontF := hcontF') (hcontg := hcontg')
      (hconth := hconth') (hK0 := mul_nonneg hKc0 hW0) (hterm := hterm')
    simpa only [Work.Diff.STE.pdVec] using hres
  -- **sum over the direction tuples**
  have hdouble : ∀ (a b i j : Fin n),
      |∑ l : Fin k → Fin n,
          Work.Diff.STE.L2re (fun x => Work.Diff.STE.pdVec k l (fun y =>
                symInvC c a b y
                  * pd a (pd b (fun z => seriesFunM c z i j)) y) x
            - symInvC c a b x * Work.Diff.STE.pdVec k l
                (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
          (Work.Diff.STE.pdVec k l (fun x => seriesFunM c x i j))|
        ≤ (Fintype.card (Fin k → Fin n) : ℝ) * ((2 : ℝ) ^ k * (Kc * W)) := by
    intro a b i j
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (fun l _ => hsingle a b i j l)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- **sum over the index quadruples**
  have htot : (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n,
      |∑ l : Fin k → Fin n,
          Work.Diff.STE.L2re (fun x => Work.Diff.STE.pdVec k l (fun y =>
                symInvC c a b y
                  * pd a (pd b (fun z => seriesFunM c z i j)) y) x
            - symInvC c a b x * Work.Diff.STE.pdVec k l
                (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
          (Work.Diff.STE.pdVec k l (fun x => seriesFunM c x i j))|) ≤ Ctot * W := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
        Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) =>
          Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hdouble a b i j))))
    refine h.trans ?_
    have hconst : (∑ _i : Fin n, ∑ _j : Fin n, ∑ _a : Fin n, ∑ _b : Fin n,
        (Fintype.card (Fin k → Fin n) : ℝ) * ((2 : ℝ) ^ k * (Kc * W)))
        = (n : ℝ) ^ 4 * ((Fintype.card (Fin k → Fin n) : ℝ)
            * ((2 : ℝ) ^ k * (Kc * W))) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hconst, hCtot, hNC]
    exact le_of_eq (by ring)
  -- **the absorption of the weight into the level-`(k+1)` dissipation**
  have hEM0 : 0 ≤ ENormSqM (k + 1) (seriesFunM c) := ENormSqM_nonneg (k + 1) _
  have hEf : Efull ≤ ENormSqM (k + 1) (seriesFunM c) + B ^ 2 := by
    rw [hEfull, ENormSqFull]
    linarith only [hE0le]
  have habs : Ctot * W ≤ (lam' / 8) * ENormSqM (k + 1) (seriesFunM c) + Cf :=
    csb_absorb (Ctot := Ctot) (Ef := Efull) (EM := ENormSqM (k + 1) (seriesFunM c))
      (B := B) (ν := lam' / 8) (by positivity) hCtot0 hB hEM0 hEfull0 hEf
  exact htot.trans habs

end

end Work.Diff.STE.flat
