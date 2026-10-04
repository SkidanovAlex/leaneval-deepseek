/-
# The sharp static pairing bound `PairingBoundSharp` (proof)

This file proves `Work.Diff.STE.flat.PairingBoundSharp`, the single analytic input of the flat
`Hᵏ` a priori estimate, at the sharp threshold `Fintype.card (Fin n) + 4 < 2 * k`.
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.level_defs
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.flat.Sobolev
import Submission.Work.Diff.STE.flat.Sobolev.rnorm_seriesFun_rpow_le
import Submission.Work.Diff.STE.flat.sobolev_uniform
import Submission.Work.Diff.STE.flat.CSq_symInvC_le
import Submission.Work.Diff.STE.flat.symInv_deriv_Lp_bound
import Submission.Work.Diff.STE.flat.symInv_garding_bounds
import Submission.Work.Diff.STE.flat.Nfun_CSq_level_bound
import Submission.Work.Diff.STE.flat.pairing_decomp
import Submission.Work.Diff.STE.flat.pairing_gard_le
import Submission.Work.Diff.STE.flat.level_linear
import Submission.Work.Diff.STE.flat.jet_sup_le_uniform_level
import Submission.Work.Diff.STE.flat.pairing_sharp
import Submission.Work.Diff.STE.flat.summable_wt_dmulV_le
import Submission.Work.Diff.STE.pdList_mul_sub
import Submission.Work.Diff.STE.pd_seriesFun
import Submission.Work.Diff.STE.CSq_le_ENormSq_seriesFun
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.integral_normSq_seriesFun
import Submission.Work.Diff.STE.integral_mul_pd_eq_neg
import Submission.Work.Diff.STE.flat.galerkin.inv_entry_le_of_quadForm
import Submission.Work.Diff.STE.bessel_continuous
import Submission.Work.Diff.STE.flat.phi_bound_nosym

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory BigOperators Filter

namespace Work.Diff.STE.flat

noncomputable section

open Work.Diff.STE.Flat

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A continuous function on the unit cube is in every `L^p`. -/
theorem memLp_of_continuous_cube {E : Type*} [NormedAddCommGroup E] {f : (ι → ℝ) → E}
    (hf : Continuous f) (p : ℝ) :
    MemLp f (ENNReal.ofReal p) (volume.restrict (unitCube (ι := ι))) := by
  haveI := Work.Diff.STE.BesselCont.isFiniteMeasure_restrict_unitCube (ι := ι)
  have hK : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem (Work.Diff.STE.BesselCont.measSet_unitCube (ι := ι))]
    with x hx
  exact hC x (fun i _ => ⟨(hx i (Set.mem_univ i)).1.le, (hx i (Set.mem_univ i)).2⟩)



/-- A continuous function on the unit cube is integrable. -/
theorem integrable_of_continuous_cube {E : Type*} [NormedAddCommGroup E]
    {f : (ι → ℝ) → E} (hf : Continuous f) :
    Integrable f (volume.restrict (unitCube (ι := ι))) := by
  haveI := Work.Diff.STE.BesselCont.isFiniteMeasure_restrict_unitCube (ι := ι)
  have hK : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem (Work.Diff.STE.BesselCont.measSet_unitCube (ι := ι))]
    with x hx
  exact hC x (fun i _ => ⟨(hx i (Set.mem_univ i)).1.le, (hx i (Set.mem_univ i)).2⟩)

/-- The `rpow` arithmetic of the Hölder chain: `(a^{1/p})^{1/2} = a^{1/(2p)}`. -/
private lemma rpow_rpow_half (a : ℝ) (ha : 0 ≤ a) (p : ℝ) (hp : p ≠ 0) :
    (a ^ (1 / p)) ^ (1 / 2 : ℝ) = a ^ (1 / (2 * p)) := by
  rw [← Real.rpow_mul ha]
  congr 1
  field_simp

set_option maxHeartbeats 1000000 in
/-- **Hölder on the unit cube** (Cauchy–Schwarz + two-factor Hölder), in the shape used by the
commutator estimate: `|⟨F·G, h⟩| ≤ ‖F‖_{L^{2p}} ‖G‖_{L^{2q}} ‖h‖_{L²}` when `1/p + 1/q = 1`. -/
theorem L2re_mul_mul_le_rnorm (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (hpq : 1 / p + 1 / q = 1)
    {F G h : (ι → ℝ) → ℂ} (hFc : Continuous F) (hGc : Continuous G) (hhc : Continuous h) :
    |L2re (fun x => F x * G x) h|
      ≤ rnorm (2 * p) F * rnorm (2 * q) G * rnorm 2 h := by
  haveI := Work.Diff.STE.BesselCont.isFiniteMeasure_restrict_unitCube (ι := ι)
  -- Step 1: `|L2re (F*G) h| ≤ ∫ ‖F‖‖G‖‖h‖`
  have hstep1 : |L2re (fun x => F x * G x) h|
      ≤ ∫ x in (unitCube (ι := ι)), ‖F x‖ * ‖G x‖ * ‖h x‖ := by
    have h1 : |L2re (fun x => F x * G x) h|
        ≤ ‖∫ x in (unitCube (ι := ι)), (F x * G x) * star (h x)‖ := by
      have h : L2re (fun x => F x * G x) h
          = (∫ x in (unitCube (ι := ι)), (F x * G x) * star (h x)).re := rfl
      rw [h]
      exact Complex.abs_re_le_norm _
    refine h1.trans ?_
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [norm_mul, Complex.star_def, Complex.norm_conj]
  -- Step 2: Cauchy–Schwarz
  have h2p : (0 : ℝ) ≤ 2 := by norm_num
  have h22 : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hF1 : MemLp (fun x : ι → ℝ => ‖F x‖ * ‖G x‖) (ENNReal.ofReal 2)
      (volume.restrict (unitCube (ι := ι))) :=
    memLp_of_continuous_cube (ι := ι) (hFc.norm.mul hGc.norm) 2
  have hh1 : MemLp (fun x : ι → ℝ => ‖h x‖) (ENNReal.ofReal 2)
      (volume.restrict (unitCube (ι := ι))) :=
    memLp_of_continuous_cube (ι := ι) hhc.norm 2
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (unitCube (ι := ι)))
    (f := fun x : ι → ℝ => ‖F x‖ * ‖G x‖) (g := fun x : ι → ℝ => ‖h x‖) h22
    (Eventually.of_forall fun x => by positivity) (Eventually.of_forall fun x => by positivity)
    hF1 hh1
  -- Step 3: two-factor Hölder
  have hpq' : p.HolderConjugate q :=
    Real.holderConjugate_iff.mpr ⟨hp, by simpa [one_div] using hpq⟩
  have hF2 : MemLp (fun x : ι → ℝ => ‖F x‖ ^ (2 : ℝ)) (ENNReal.ofReal p)
      (volume.restrict (unitCube (ι := ι))) :=
    memLp_of_continuous_cube (ι := ι)
      ((Real.continuous_rpow_const h2p).comp hFc.norm) p
  have hG2 : MemLp (fun x : ι → ℝ => ‖G x‖ ^ (2 : ℝ)) (ENNReal.ofReal q)
      (volume.restrict (unitCube (ι := ι))) :=
    memLp_of_continuous_cube (ι := ι)
      ((Real.continuous_rpow_const h2p).comp hGc.norm) q
  have hh2 := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (unitCube (ι := ι)))
    (f := fun x : ι → ℝ => ‖F x‖ ^ (2 : ℝ)) (g := fun x : ι → ℝ => ‖G x‖ ^ (2 : ℝ)) hpq'
    (Eventually.of_forall fun x => by positivity) (Eventually.of_forall fun x => by positivity)
    hF2 hG2
  -- arithmetic
  have hMnn : 0 ≤ ∫ x in (unitCube (ι := ι)), (‖F x‖ * ‖G x‖) ^ (2 : ℝ) :=
    integral_nonneg fun x => by positivity
  have hAnn : 0 ≤ ∫ x in (unitCube (ι := ι)), ‖F x‖ ^ (2 * p) :=
    integral_nonneg fun x => by positivity
  have hBnn : 0 ≤ ∫ x in (unitCube (ι := ι)), ‖G x‖ ^ (2 * q) :=
    integral_nonneg fun x => by positivity
  have hHnn : 0 ≤ ∫ x in (unitCube (ι := ι)), ‖h x‖ ^ (2 : ℝ) :=
    integral_nonneg fun x => by positivity
  have hMform : (∫ x in (unitCube (ι := ι)), (‖F x‖ * ‖G x‖) ^ (2 : ℝ))
      = ∫ x in (unitCube (ι := ι)), ‖F x‖ ^ (2 : ℝ) * ‖G x‖ ^ (2 : ℝ) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only []
    exact Real.mul_rpow (norm_nonneg _) (norm_nonneg _)
  have hAp : (∫ x in (unitCube (ι := ι)), (‖F x‖ ^ (2 : ℝ)) ^ p)
      = ∫ x in (unitCube (ι := ι)), ‖F x‖ ^ (2 * p) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only []
    rw [← Real.rpow_mul (norm_nonneg _)]
  have hBq : (∫ x in (unitCube (ι := ι)), (‖G x‖ ^ (2 : ℝ)) ^ q)
      = ∫ x in (unitCube (ι := ι)), ‖G x‖ ^ (2 * q) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only []
    rw [← Real.rpow_mul (norm_nonneg _)]
  have hMle : (∫ x in (unitCube (ι := ι)), (‖F x‖ * ‖G x‖) ^ (2 : ℝ))
      ≤ (∫ x in (unitCube (ι := ι)), ‖F x‖ ^ (2 * p)) ^ (1 / p)
        * (∫ x in (unitCube (ι := ι)), ‖G x‖ ^ (2 * q)) ^ (1 / q) := by
    rw [← hMform, hAp, hBq] at hh2
    exact hh2
  have hroot : (∫ x in (unitCube (ι := ι)), (‖F x‖ * ‖G x‖) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ (∫ x in (unitCube (ι := ι)), ‖F x‖ ^ (2 * p)) ^ (1 / (2 * p))
        * (∫ x in (unitCube (ι := ι)), ‖G x‖ ^ (2 * q)) ^ (1 / (2 * q)) := by
    have h1 : ((∫ x in (unitCube (ι := ι)), ‖F x‖ ^ (2 * p)) ^ (1 / p)
        * (∫ x in (unitCube (ι := ι)), ‖G x‖ ^ (2 * q)) ^ (1 / q)) ^ (1 / 2 : ℝ)
        = (∫ x in (unitCube (ι := ι)), ‖F x‖ ^ (2 * p)) ^ (1 / (2 * p))
          * (∫ x in (unitCube (ι := ι)), ‖G x‖ ^ (2 * q)) ^ (1 / (2 * q)) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hAnn _) (Real.rpow_nonneg hBnn _),
        rpow_rpow_half _ hAnn p (by positivity), rpow_rpow_half _ hBnn q (by positivity)]
    rw [← h1]
    exact Real.rpow_le_rpow hMnn hMle (by norm_num)
  simp only [rnorm]
  calc |L2re (fun x => F x * G x) h|
      ≤ ∫ x in (unitCube (ι := ι)), (‖F x‖ * ‖G x‖) * ‖h x‖ := hstep1
    _ ≤ (∫ x in (unitCube (ι := ι)), (‖F x‖ * ‖G x‖) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
          * (∫ x in (unitCube (ι := ι)), ‖h x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hcs
    _ ≤ ((∫ x in (unitCube (ι := ι)), ‖F x‖ ^ (2 * p)) ^ (1 / (2 * p))
          * (∫ x in (unitCube (ι := ι)), ‖G x‖ ^ (2 * q)) ^ (1 / (2 * q)))
          * (∫ x in (unitCube (ι := ι)), ‖h x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg hHnn _)


/-! ## The uniform bounds on the symmetrised inverse metric -/

/-- **Uniform sup bound of the symmetrised inverse metric.**  Uniform ellipticity with constant
`lam > 0` alone gives `|(reMat u)⁻¹| ≤ lam⁻¹` entrywise, hence `‖symInvC c a b‖ ≤ lam⁻¹`: no
energy hypothesis is needed. -/
theorem symInvC_sup_le {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) →
      ENormSqFull k (seriesFunM c) ≤ B ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, reMat (seriesFunM c x) i j * v i * v j) →
      ∀ (a b : Fin n) (x : Fin n → ℝ), ‖symInvC c a b x‖ ≤ C := by
  refine ⟨lam⁻¹, by positivity, ?_⟩
  intro N c hc hen hell a b x
  have hG : ∀ p q : Fin n, |((reMat (seriesFunM c x))⁻¹) p q| ≤ lam⁻¹ :=
    fun p q => Work.Diff.STE.flat.galerkin.inv_entry_le_of_quadForm _ hlam (hell x) p q
  simp only [symInvC_apply, symInvR_apply, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  refine (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr ?_
  nlinarith [abs_add_le (((reMat (seriesFunM c x))⁻¹) a b)
    (((reMat (seriesFunM c x))⁻¹) b a), hG a b, hG b a]

/-- **`L²` bound for the derivatives of the symmetrised inverse metric at the full level `k`.**
Unlike `Work.Diff.STE.flat.symInv_deriv_Lp_bound` this needs no loss of one derivative order: it is
the direct Parseval computation from the level-`k` coefficient bound `CSq_symInvC_le`. -/
theorem symInvC_pdList_L2_le {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
    (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) →
      ENormSqFull k (seriesFunM c) ≤ B ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, reMat (seriesFunM c x) i j * v i * v j) →
      ∀ (a b : Fin n) (q : List (Fin n)), q.length ≤ k →
        ∫ x in unitCube, ‖pdList q (fun y => symInvC c a b y) x‖ ^ 2 ≤ C := by
  have hσ : sob n ≤ k := by
    have h := two_sob_le n
    have hk' : n + 4 < 2 * k := by simpa using hk
    omega
  obtain ⟨Ccsq, hCcsq, hCSQ⟩ := CSq_symInvC_le hn k hσ lam hlam B hB
  refine ⟨((2 * Real.pi) ^ 2) ^ k * Ccsq, by positivity, ?_⟩
  intro N c hc hen hell a b q hq
  set f : (Fin n → ℝ) → ℂ := fun y => symInvC c a b y with hfdef
  have hsmper := symInvC_contDiff_periodic hσ hB hlam hc hen hell a b
  have hfsm : ContDiff ℝ (⊤ : ℕ∞) f := hsmper.1
  have hfper : Periodic1 f := hsmper.2
  have hcsq : CSq k (fourierCoeff f) ≤ Ccsq := hCSQ N c hc hen hell a b
  have hfd : ∀ K : ℕ, Summable (fun m : Fin n → ℤ => (wt m) ^ K * ‖fourierCoeff f m‖ ^ 2) :=
    fun K => summable_weighted_fourierCoeff_of_contDiff f hfsm hfper K
  have hfl1 : ∀ K : ℕ, Summable (fun m : Fin n → ℤ => (wt m) ^ K * ‖fourierCoeff f m‖) :=
    fun K => Work.Diff.STE.flat.invJet_summable_moment_of_wt_sq _ hfd K
  have hFser : f = seriesFun (fourierCoeff f) :=
    funext fun x => (seriesFun_fourierCoeff f hfsm hfper x).symm
  have hpd : pdList q f = seriesFun (dmulV q (fourierCoeff f)) := by
    conv_lhs => rw [hFser]
    exact funext fun x => pdList_seriesFun q (fourierCoeff f) hfl1 x
  have hdsum : Summable (fun m : Fin n → ℤ => ‖dmulV q (fourierCoeff f) m‖) := by
    simpa using summable_dmulV q (fourierCoeff f) hfl1 0
  have hpar := integral_normSq_seriesFun (dmulV q (fourierCoeff f)) hdsum
  have hmass := summable_wt_dmulV_le q 0 k (fourierCoeff f) (by simpa using hq) (hfd k)
  rw [hpd, hpar]
  have h1 : (∑' m : Fin n → ℤ, ‖dmulV q (fourierCoeff f) m‖ ^ 2)
      = ∑' m : Fin n → ℤ, (wt m) ^ (0 : ℝ) * ‖dmulV q (fourierCoeff f) m‖ ^ 2 := by
    refine tsum_congr fun m => ?_
    rw [Real.rpow_zero, one_mul]
  rw [h1]
  have h2pi : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  calc ∑' m : Fin n → ℤ, (wt m) ^ (0 : ℝ) * ‖dmulV q (fourierCoeff f) m‖ ^ 2
      ≤ ((2 * Real.pi) ^ 2) ^ q.length * ∑' m : Fin n → ℤ,
          (wt m) ^ k * ‖fourierCoeff f m‖ ^ 2 := hmass.2
    _ = ((2 * Real.pi) ^ 2) ^ q.length * CSq k (fourierCoeff f) := by rw [CSq]
    _ ≤ ((2 * Real.pi) ^ 2) ^ q.length * Ccsq := mul_le_mul_of_nonneg_left hcsq (by positivity)
    _ ≤ ((2 * Real.pi) ^ 2) ^ k * Ccsq :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h2pi hq) hCcsq

/-! ## The sharp `L^{2q}` Sobolev bound for the solution -/

/-- **The sharp Sobolev bound for the derivatives of the solution.**  For a single exponent `q`
(the constant may depend on it) and a single order `m`, the `L^{2q}` norm of `∂^m u` is bounded by
`C (1 + √(ENormSqFull (k+1) u))` as soon as `m + n/2 - n/(2q) < k+1`. -/
theorem pdVec_seriesFunM_rnorm_le {n : ℕ} (m : ℕ) (q : ℝ) (hq : 1 ≤ q) (k : ℕ)
    (hmq : (m : ℝ) + (n : ℝ) / 2 - (n : ℝ) / (2 * q) < (k : ℝ) + 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) →
      ∀ (l : Fin m → Fin n) (i j : Fin n),
        rnorm (2 * q) (pdVec m l (fun y => seriesFunM c y i j))
          ≤ C * (1 + Real.sqrt (ENormSqFull (k + 1) (seriesFunM c))) := by
  classical
  have hj : ((Fintype.card (Fin n) : ℕ) : ℝ) * (1 / 2 - 1 / (2 * q)) < (k : ℝ) + 1 - (m : ℝ) := by
    have h : ((Fintype.card (Fin n) : ℕ) : ℝ) = (n : ℝ) := by simp
    rw [h]
    have h2 : (n : ℝ) * (1 / 2 - 1 / (2 * q)) = (n : ℝ) / 2 - (n : ℝ) / (2 * q) := by ring
    rw [h2]; linarith
  obtain ⟨Csob, hCsob, hSob⟩ :=
    Work.Diff.STE.flat.Sobolev.rnorm_seriesFun_rpow_le (ι := Fin n) q hq
      ((k : ℝ) + 1 - (m : ℝ)) hj
  obtain ⟨Ccsq, hCcsq, hCSQ⟩ := CSq_le_ENormSq_seriesFun (ι := Fin n) (k + 1)
  refine ⟨Csob * (2 * Real.pi) ^ m * Real.sqrt Ccsq + 1, by positivity, ?_⟩
  intro N c hc l i j
  have hmom : ∀ M : ℕ, Summable (fun k' : Fin n → ℤ => (wt k') ^ M * ‖c k' i j‖) :=
    fun M => summable_moment_box c hc i j M
  have hfun : (fun y : Fin n → ℝ => seriesFunM c y i j)
      = seriesFun (fun μ : Fin n → ℤ => c μ i j) := by
    funext y; rw [seriesFunM_apply]
  have hpd : pdVec m l (fun y => seriesFunM c y i j)
      = seriesFun (dmulV (List.ofFn l) (fun μ : Fin n → ℤ => c μ i j)) := by
    rw [hfun]
    exact funext fun x => pdList_seriesFun (List.ofFn l) (fun μ => c μ i j) hmom x
  set γ : (Fin n → ℤ) → ℂ := fun μ => c μ i j with hγdef
  have hγmom : ∀ M : ℕ, Summable (fun μ : Fin n → ℤ => (wt μ) ^ M * ‖γ μ‖) := by
    intro M; rw [hγdef]; exact hmom M
  have hγ2 : Summable (fun μ : Fin n → ℤ => (wt μ) ^ (k + 1) * ‖γ μ‖ ^ 2) :=
    summable_wt_pow_mul_norm_sq γ hγmom (k + 1)
  have hmass := summable_wt_dmulV_le (List.ofFn l) ((k : ℝ) + 1 - (m : ℝ)) (k + 1) γ
    (by simp) hγ2
  have hγfun : seriesFun γ = fun y => seriesFunM c y i j := by
    rw [hγdef]; exact hfun.symm
  rw [hpd]
  have hsob := hSob (dmulV (List.ofFn l) γ) hmass.1
  rw [← Real.sqrt_eq_rpow] at hsob
  have hγmass : Real.sqrt (∑' μ : Fin n → ℤ, (wt μ) ^ ((k : ℝ) + 1 - (m : ℝ))
        * ‖dmulV (List.ofFn l) γ μ‖ ^ 2)
      ≤ Real.sqrt (((2 * Real.pi) ^ 2) ^ m * CSq (k + 1) γ) := by
    refine Real.sqrt_le_sqrt ?_
    have h := hmass.2
    simp only [List.length_ofFn] at h
    exact h
  have hCSQ : CSq (k + 1) γ ≤ Ccsq * ENormSqFull (k + 1) (seriesFunM c) := by
    have hcs := hCSQ γ hγmom
    rw [hγfun] at hcs
    have h1 : ENormSq (k + 1) (fun y => seriesFunM c y i j)
        ≤ ENormSqM (k + 1) (seriesFunM c) := ENormSq_le_ENormSqM (seriesFunM c) i j
    have h2 : ENormSq 0 (fun y => seriesFunM c y i j)
        ≤ ENormSqM 0 (seriesFunM c) := ENormSq_le_ENormSqM (j := 0) (seriesFunM c) i j
    calc CSq (k + 1) γ
        ≤ Ccsq * (ENormSq (k + 1) (fun y => seriesFunM c y i j)
            + ENormSq 0 (fun y => seriesFunM c y i j)) := hcs
      _ ≤ Ccsq * ENormSqFull (k + 1) (seriesFunM c) := by
          rw [ENormSqFull]
          exact mul_le_mul_of_nonneg_left (by linarith) hCcsq
  have hsplit : Real.sqrt (((2 * Real.pi) ^ 2) ^ m
        * (Ccsq * ENormSqFull (k + 1) (seriesFunM c)))
      = (2 * Real.pi) ^ m
        * (Real.sqrt Ccsq * Real.sqrt (ENormSqFull (k + 1) (seriesFunM c))) := by
    have hpp : Real.sqrt (((2 * Real.pi) ^ 2) ^ m) = (2 * Real.pi) ^ m := by
      rw [show ((2 * Real.pi) ^ 2) ^ m = ((2 * Real.pi) ^ m) ^ 2 from by
            rw [← pow_mul, ← pow_mul, mul_comm 2 m],
        Real.sqrt_sq (by positivity)]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hCcsq, hpp]
  have hroot : Real.sqrt (((2 * Real.pi) ^ 2) ^ m * CSq (k + 1) γ)
      ≤ (2 * Real.pi) ^ m
        * (Real.sqrt Ccsq * Real.sqrt (ENormSqFull (k + 1) (seriesFunM c))) := by
    rw [← hsplit]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hCSQ (by positivity))
  refine le_trans hsob ?_
  refine le_trans (mul_le_mul_of_nonneg_left (hγmass.trans hroot) hCsob) ?_
  · have hE : 0 ≤ Real.sqrt (ENormSqFull (k + 1) (seriesFunM c)) := Real.sqrt_nonneg _
    have hAs : 0 ≤ Csob * (2 * Real.pi) ^ m * Real.sqrt Ccsq := by positivity
    have hgoalexp : Csob * ((2 * Real.pi) ^ m
          * (Real.sqrt Ccsq * Real.sqrt (ENormSqFull (k + 1) (seriesFunM c))))
        = (Csob * (2 * Real.pi) ^ m * Real.sqrt Ccsq)
          * Real.sqrt (ENormSqFull (k + 1) (seriesFunM c)) := by ring
    rw [hgoalexp]
    nlinarith [hAs, hE, mul_nonneg hAs hE]


/-! ## The Gårding piece of the sharp pairing -/

/-- **The Gårding dissipation at the sharp level.**  The principal part of the pairing is bounded
by `-(lam'/2) ENormSqM (k+1) u + C`, with `lam' > 0` the ellipticity constant of the symmetrised
inverse metric (`Work.Diff.STE.flat.symInv_garding_bounds`). -/
theorem pairing_gard_sharp {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
    (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B)
    (lam' : ℝ) (hlam' : 0 < lam') :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
        (∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) →
        ENormSqFull k (seriesFunM c) ≤ B ^ 2 →
        (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, reMat (seriesFunM c x) i j * v i * v j) →
        (∀ (x : Fin n → ℝ) (ξ : Fin n → ℝ),
          lam' * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, symInvR c i j x * ξ i * ξ j) →
        (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n,
          L2re (fun x => ∑ a, ∑ b, symInvC c a b x
              * pd a (pd b (pdVec k l (fun y => seriesFunM c y i j))) x)
            (pdVec k l (fun y => seriesFunM c y i j)))
        ≤ -((lam' / 2) * ENormSqM (k + 1) (seriesFunM c)) + C := by
  obtain ⟨_lam'', _hlam'', Cg, hCg, hgb⟩ := symInv_garding_bounds hn k hk lam hlam B hB
  refine ⟨Work.Diff.STE.gardingConst (Fintype.card (Fin n)) lam' Cg * B ^ 2 + 1,
    add_nonneg (mul_nonneg (Work.Diff.STE.gardingConst_nonneg hlam') (sq_nonneg B)) zero_le_one,
    ?_⟩
  intro N c hc hen hell hellρ
  obtain ⟨hsmR, hsmC, hperR, hperC, hpdr, _hell'⟩ := hgb N c hc hen hell
  have hA : ∀ a b : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => symInvR c a b y) := hsmR
  have hAper : ∀ a b : Fin n, Periodic1 (fun y : Fin n → ℝ => symInvR c a b y) := hperR
  have hsym : ∀ a b (y : Fin n → ℝ), symInvR c a b y = symInvR c b a y :=
    fun a b y => symInvR_symm_apply c a b y
  have hpos : ∀ (x : Fin n → ℝ) (ξ : Fin n → ℝ),
      lam' * ∑ i, (ξ i) ^ 2 ≤ ∑ a, ∑ b, symInvR c a b x * ξ a * ξ b :=
    fun x ξ => hellρ x ξ
  have hK₁ : ∀ a b i (x : Fin n → ℝ), |pdR i (symInvR c a b) x| ≤ Cg :=
    fun a b i x => hpdr a b i x
  have hper_entry : ∀ i j : Fin n,
      (∑ l : Fin k → Fin n, L2re
          (fun x => ∑ a, ∑ b, symInvC c a b x
            * pd a (pd b (pdVec k l (fun y => seriesFunM c y i j))) x)
          (pdVec k l (fun y => seriesFunM c y i j)))
        ≤ -((lam' / 2) * ENormSq (k + 1) (fun y => seriesFunM c y i j))
          + Work.Diff.STE.gardingConst (Fintype.card (Fin n)) lam' Cg
            * ENormSq k (fun y => seriesFunM c y i j) := by
    intro i j
    have hu : ContDiff ℝ ((k + 2 : ℕ) : ℕ∞) (fun y : Fin n → ℝ => seriesFunM c y i j) := by
      have h := Work.Diff.STE.contDiff_seriesFun
        (c := fun k' : Fin n → ℤ => c k' i j) (fun M => summable_moment_box c hc i j M)
      exact h.of_le (WithTop.coe_le_coe.mpr le_top)
    have hp : Periodic1 (fun y : Fin n → ℝ => seriesFunM c y i j) := by
      have h := Work.Diff.STE.periodic_seriesFun (fun k' : Fin n → ℤ => c k' i j)
      simpa only [seriesFunM_apply] using h
    have hthis := Work.Diff.STE.flat.garding_vec_const (ι := Fin n) k lam' hlam' Cg
      (fun a b y => symInvR c a b y) hA hAper hsym hpos hK₁
      (fun y => seriesFunM c y i j) (by simpa using hu) hp
    simpa only [symInvC_apply] using hthis
  have hsum : (∑ i : Fin n, ∑ j : Fin n,
        (-((lam' / 2) * ENormSq (k + 1) (fun y => seriesFunM c y i j))
          + Work.Diff.STE.gardingConst (Fintype.card (Fin n)) lam' Cg
            * ENormSq k (fun y => seriesFunM c y i j)))
      = -((lam' / 2) * ENormSqM (k + 1) (seriesFunM c))
        + Work.Diff.STE.gardingConst (Fintype.card (Fin n)) lam' Cg
          * ENormSqM k (seriesFunM c) := by
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, ENormSqM]
  have hEk : ENormSqM k (seriesFunM c) ≤ B ^ 2 := (ENormSqM_le_ENormSqFull k _).trans hen
  have hEkn : 0 ≤ ENormSqM k (seriesFunM c) := ENormSqM_nonneg k _
  have hE1 : 0 ≤ ENormSqM (k + 1) (seriesFunM c) := ENormSqM_nonneg (k + 1) _
  have hgn : 0 ≤ Work.Diff.STE.gardingConst (Fintype.card (Fin n)) lam' Cg :=
    Work.Diff.STE.gardingConst_nonneg hlam'
  calc (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n,
        L2re (fun x => ∑ a, ∑ b, symInvC c a b x
            * pd a (pd b (pdVec k l (fun y => seriesFunM c y i j))) x)
          (pdVec k l (fun y => seriesFunM c y i j)))
      ≤ ∑ i : Fin n, ∑ j : Fin n,
          (-((lam' / 2) * ENormSq (k + 1) (fun y => seriesFunM c y i j))
            + Work.Diff.STE.gardingConst (Fintype.card (Fin n)) lam' Cg
              * ENormSq k (fun y => seriesFunM c y i j)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hper_entry i j
    _ = -((lam' / 2) * ENormSqM (k + 1) (seriesFunM c))
          + Work.Diff.STE.gardingConst (Fintype.card (Fin n)) lam' Cg
            * ENormSqM k (seriesFunM c) := hsum
    _ ≤ -((lam' / 2) * ENormSqM (k + 1) (seriesFunM c))
          + (Work.Diff.STE.gardingConst (Fintype.card (Fin n)) lam' Cg * B ^ 2 + 1) := by
        have h1 : Work.Diff.STE.gardingConst (Fintype.card (Fin n)) lam' Cg
            * ENormSqM k (seriesFunM c) ≤ Work.Diff.STE.gardingConst (Fintype.card (Fin n)) lam' Cg
              * B ^ 2 := mul_le_mul_of_nonneg_left hEk hgn
        linarith [h1, hgn, sq_nonneg B, hE1]


/-! ## The `L²` pairing bound and the lower order pieces -/

/-- Cauchy–Schwarz for `L2re`. -/
theorem L2re_le_sqrt {F G : (ι → ℝ) → ℂ} (hF : Continuous F) (hG : Continuous G) :
    |L2re F G| ≤ Real.sqrt (∫ x in unitCube, ‖F x‖ ^ (2 : ℝ))
      * Real.sqrt (∫ x in unitCube, ‖G x‖ ^ (2 : ℝ)) := by
  haveI := Work.Diff.STE.BesselCont.isFiniteMeasure_restrict_unitCube (ι := ι)
  have hstep1 : |L2re F G| ≤ ∫ x in unitCube, ‖F x‖ * ‖G x‖ := by
    have h1 : |L2re F G| ≤ ‖∫ x in unitCube, F x * star (G x)‖ := by
      have h : L2re F G = (∫ x in unitCube, F x * star (G x)).re := rfl
      rw [h]
      exact Complex.abs_re_le_norm _
    refine h1.trans ?_
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [norm_mul, Complex.star_def, Complex.norm_conj]
  have h22 : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have h1 : MemLp (fun x : ι → ℝ => ‖F x‖) (ENNReal.ofReal 2)
      (volume.restrict (unitCube (ι := ι))) := memLp_of_continuous_cube (ι := ι) hF.norm 2
  have h2 : MemLp (fun x : ι → ℝ => ‖G x‖) (ENNReal.ofReal 2)
      (volume.restrict (unitCube (ι := ι))) := memLp_of_continuous_cube (ι := ι) hG.norm 2
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (unitCube (ι := ι)))
    (f := fun x : ι → ℝ => ‖F x‖) (g := fun x : ι → ℝ => ‖G x‖) h22
    (Eventually.of_forall fun x => by positivity) (Eventually.of_forall fun x => by positivity) h1 h2
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hcs
  exact hstep1.trans hcs

/-- The `rpow`-exponent `2` integral is the usual one. -/
private lemma sqrt_integral_two (F : (ι → ℝ) → ℂ) :
    Real.sqrt (∫ x in unitCube, ‖F x‖ ^ (2 : ℝ))
      = Real.sqrt (∫ x in unitCube, ‖F x‖ ^ 2) := by
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only []
  exact Real.rpow_two (‖F x‖)

/-- **The `Nfun` (lower order) piece of the sharp pairing.** -/
theorem pairing_N_sharp {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (Nfun : (Fin n → ℝ) × (MatC n × (Fin n → MatC n)) → MatC n)
    (hNsm : ContDiffOn ℝ (⊤ : ℕ∞) Nfun (Set.univ ×ˢ
      {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0}))
    (hNper : ∀ w : MatC n × (Fin n → MatC n), Periodic1 (fun x : Fin n → ℝ => Nfun (x, w)))
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) →
      ENormSqFull k (seriesFunM c) ≤ B ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, reMat (seriesFunM c x) i j * v i * v j) →
      (∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x => Nfun (x, jetP c x) i j)) →
      (∀ i j : Fin n, Periodic1 (fun x => Nfun (x, jetP c x) i j)) →
      (∑ i : Fin n, ∑ j : Fin n, |∑ l : Fin k → Fin n,
          L2re (pdVec k l (fun x => Nfun (x, jetP c x) i j))
            (pdVec k l (fun x => seriesFunM c x i j))|)
        ≤ C * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c)) := by
  obtain ⟨Cn, hCn, hNCSQ⟩ := Nfun_CSq_level_bound hn k hk Nfun hNsm hNper lam hlam B hB
  obtain ⟨CEN, hCEN, hEN⟩ := ENormSq_seriesFun_le (ι := Fin n) k
  set nl : ℝ := (Fintype.card (Fin k → Fin n) : ℝ) with hnl
  refine ⟨(n : ℝ) ^ 2 * (nl * (Real.sqrt (CEN * Cn) * B)) + 1,
    add_nonneg (mul_nonneg (by positivity)
      (mul_nonneg (by rw [hnl]; positivity)
        (mul_nonneg (Real.sqrt_nonneg _) hB))) zero_le_one, ?_⟩
  intro N c hc hen hell hNfsm hNper'
  have hnl0 : 0 ≤ nl := by rw [hnl]; positivity
  have hscn : 0 ≤ Real.sqrt (CEN * Cn) := Real.sqrt_nonneg _
  have hEfull1 : 0 ≤ 1 + ENormSqFull (k + 1) (seriesFunM c) := by
    have := ENormSqFull_nonneg (k + 1) (seriesFunM c); linarith
  have hper : ∀ i j : Fin n,
      |∑ l : Fin k → Fin n, L2re (pdVec k l (fun x => Nfun (x, jetP c x) i j))
          (pdVec k l (fun x => seriesFunM c x i j))|
        ≤ nl * (Real.sqrt (CEN * Cn) * B)
          * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c)) := by
    intro i j
    have hNsmij : ContDiff ℝ (⊤ : ℕ∞) (fun x => Nfun (x, jetP c x) i j) := hNfsm i j
    have hNperij : Periodic1 (fun x => Nfun (x, jetP c x) i j) := hNper' i j
    -- smoothness/periodicity of the solution entry
    have hUsm : ContDiff ℝ (⊤ : ℕ∞) (fun x => seriesFunM c x i j) :=
      Work.Diff.STE.contDiff_seriesFun (fun k' => c k' i j)
        (fun M => summable_moment_box c hc i j M)
    have hUper : Periodic1 (fun x => seriesFunM c x i j) := by
      have h := Work.Diff.STE.periodic_seriesFun (fun k' : Fin n → ℤ => c k' i j)
      simpa only [seriesFunM_apply] using h
    -- the `L²` mass bound for the `N` entry
    have hNmom : ∀ M : ℕ, Summable (fun m : Fin n → ℤ =>
        (wt m) ^ M * ‖fourierCoeff (fun x => Nfun (x, jetP c x) i j) m‖) := by
      intro M
      have h2 := summable_weighted_fourierCoeff_of_contDiff
        (fun x => Nfun (x, jetP c x) i j) hNsmij hNperij M
      exact Work.Diff.STE.flat.invJet_summable_moment_of_wt_sq _
        (fun K => summable_weighted_fourierCoeff_of_contDiff
          (fun x => Nfun (x, jetP c x) i j) hNsmij hNperij K) M
    have hNser : (fun x => Nfun (x, jetP c x) i j)
        = seriesFun (fourierCoeff (fun x => Nfun (x, jetP c x) i j)) :=
      funext fun x => (seriesFun_fourierCoeff _ hNsmij hNperij x).symm
    have hENsq : ENormSq k (fun x => Nfun (x, jetP c x) i j)
        ≤ CEN * (Cn * (1 + ENormSqFull (k + 1) (seriesFunM c))) := by
      have h1 := hEN (fourierCoeff (fun x => Nfun (x, jetP c x) i j)) hNmom
      rw [← hNser] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (hNCSQ N c hc hen hell i j) hCEN)
    -- the per-`l` bound
    have hstep : ∀ l : Fin k → Fin n,
        Real.sqrt (∫ x in unitCube,
              ‖pdVec k l (fun x => Nfun (x, jetP c x) i j) x‖ ^ 2)
          * Real.sqrt (∫ x in unitCube,
              ‖pdVec k l (fun x => seriesFunM c x i j) x‖ ^ 2)
        ≤ Real.sqrt (CEN * Cn) * B
          * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c)) := by
      intro l
      have hA1 : (∫ x in unitCube, ‖pdVec k l (fun x => Nfun (x, jetP c x) i j) x‖ ^ 2)
          ≤ ENormSq k (fun x => Nfun (x, jetP c x) i j) :=
        Finset.single_le_sum (f := fun l' : Fin k → Fin n => ∫ x in unitCube,
            ‖pdVec k l' (fun x => Nfun (x, jetP c x) i j) x‖ ^ 2)
          (fun l' _ => integral_nonneg fun x => by positivity) (Finset.mem_univ l)
      have hB1 : (∫ x in unitCube, ‖pdVec k l (fun x => seriesFunM c x i j) x‖ ^ 2)
          ≤ ENormSqFull k (seriesFunM c) :=
        (int_pdVec_le_ENormSqM (seriesFunM c) i j l).trans (ENormSqM_le_ENormSqFull k _)
      have hB2 : Real.sqrt (∫ x in unitCube,
            ‖pdVec k l (fun x => seriesFunM c x i j) x‖ ^ 2) ≤ B := by
        exact (Real.sqrt_le_sqrt (hB1.trans hen)).trans (le_of_eq (Real.sqrt_sq hB))
      have hA2 : Real.sqrt (∫ x in unitCube,
            ‖pdVec k l (fun x => Nfun (x, jetP c x) i j) x‖ ^ 2)
          ≤ Real.sqrt (CEN * Cn) * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c)) := by
        refine (Real.sqrt_le_sqrt (hA1.trans hENsq)).trans ?_
        rw [← mul_assoc, Real.sqrt_mul (mul_nonneg hCEN hCn)]
      calc Real.sqrt (∫ x in unitCube,
              ‖pdVec k l (fun x => Nfun (x, jetP c x) i j) x‖ ^ 2)
            * Real.sqrt (∫ x in unitCube,
              ‖pdVec k l (fun x => seriesFunM c x i j) x‖ ^ 2)
          ≤ (Real.sqrt (CEN * Cn) * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c)))
            * B := mul_le_mul hA2 hB2 (Real.sqrt_nonneg _) (by positivity)
        _ = Real.sqrt (CEN * Cn) * B * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c)) := by
            ring
    have hsum_le : |∑ l : Fin k → Fin n, L2re
          (pdVec k l (fun x => Nfun (x, jetP c x) i j))
          (pdVec k l (fun x => seriesFunM c x i j))|
        ≤ ∑ l : Fin k → Fin n,
          Real.sqrt (∫ x in unitCube,
              ‖pdVec k l (fun x => Nfun (x, jetP c x) i j) x‖ ^ 2)
            * Real.sqrt (∫ x in unitCube,
                ‖pdVec k l (fun x => seriesFunM c x i j) x‖ ^ 2) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      exact (L2re_le_sqrt
        (Work.Diff.STE.flat.contDiff_pdVec_top hNsmij l).continuous
        (Work.Diff.STE.flat.contDiff_pdVec_top hUsm l).continuous).trans
        (le_of_eq (by rw [sqrt_integral_two, sqrt_integral_two]))
    calc |∑ l : Fin k → Fin n, L2re (pdVec k l (fun x => Nfun (x, jetP c x) i j))
          (pdVec k l (fun x => seriesFunM c x i j))|
        ≤ ∑ l : Fin k → Fin n, Real.sqrt (CEN * Cn) * B
            * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c)) :=
          hsum_le.trans (Finset.sum_le_sum fun l _ => hstep l)
      _ = nl * (Real.sqrt (CEN * Cn) * B
            * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c))) := by
          rw [Finset.sum_const, Finset.card_univ, hnl, nsmul_eq_mul]
      _ = nl * (Real.sqrt (CEN * Cn) * B)
            * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c)) := by ring
  calc (∑ i : Fin n, ∑ j : Fin n, |∑ l : Fin k → Fin n,
        L2re (pdVec k l (fun x => Nfun (x, jetP c x) i j))
          (pdVec k l (fun x => seriesFunM c x i j))|)
      ≤ ∑ i : Fin n, ∑ j : Fin n, nl * (Real.sqrt (CEN * Cn) * B)
          * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hper i j
    _ = (n : ℝ) ^ 2 * (nl * (Real.sqrt (CEN * Cn) * B)
          * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ ((n : ℝ) ^ 2 * (nl * (Real.sqrt (CEN * Cn) * B)) + 1)
          * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c)) := by
        have h2 : 0 ≤ (n : ℝ) ^ 2 * (nl * (Real.sqrt (CEN * Cn) * B)) :=
          mul_nonneg (by positivity) (mul_nonneg hnl0 (mul_nonneg hscn hB))
        nlinarith [Real.sqrt_nonneg (1 + ENormSqFull (k + 1) (seriesFunM c)), h2]


/-- `rnorm 2` is the `L²` norm written with a square root. -/
theorem rnorm_two_eq_sqrt {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → ℝ) → ℂ) :
    rnorm 2 g = Real.sqrt (∫ x in unitCube, ‖g x‖ ^ 2) := by
  simp only [rnorm]
  rw [← Real.sqrt_eq_rpow, sqrt_integral_two]

/-- The second derivative is a `pdVec`. -/
private lemma pd_pd_eq_pdVec_two {n : ℕ} (a b : Fin n) (f : (Fin n → ℝ) → ℂ) :
    pd a (pd b f) = pdVec 2 ![a, b] f := by
  simp [pdVec, pdList]

/-- The `L²` norm of a Fourier series is dominated by any weighted coefficient mass. -/
theorem integral_normSq_seriesFun_le_CSq {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ)
    (c : (ι → ℤ) → ℂ) (hc : Summable (fun m => ‖c m‖))
    (hd : Summable (fun m => (wt m) ^ s * ‖c m‖ ^ 2)) :
    ∫ x in unitCube, ‖seriesFun c x‖ ^ 2 ≤ CSq s c := by
  have hle : ∀ m : ι → ℤ, ‖c m‖ ^ 2 ≤ (wt m) ^ s * ‖c m‖ ^ 2 := by
    intro m
    calc ‖c m‖ ^ 2 = 1 * ‖c m‖ ^ 2 := (one_mul _).symm
      _ ≤ (wt m) ^ s * ‖c m‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (one_le_pow₀ (wt_one_le m)) (sq_nonneg _)
  have hs1 : Summable (fun m => ‖c m‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun m => sq_nonneg _) hle hd
  rw [integral_normSq_seriesFun c hc, CSq]
  exact Summable.tsum_le_tsum hle hs1 hd

/-- **The zeroth order piece of the sharp pairing.**

Only the *boundedness of the nonlinearity on the attained jet region* is used: the level-`k`
energy bound `ENormSqFull k u ≤ B²` (with `k ≥ sob n + 2`) bounds the whole `2`-jet
`(u x, ∂u x, ∂²u x)` at every point by the constant `K (1 + B)`, and on that compact elliptic
region `Φ` is bounded by a constant (`Work.Diff.STE.flat.phi_bound_nosym`).  Hence
`∫ ‖Φ (·, jetM u ·)_{ij}‖² ≤ CΦ²` and Cauchy–Schwarz against `∫ ‖u_{ij}‖² ≤ B²` gives the
statement. -/
theorem pairing_zero_sharp {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
    (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (hshape : IsDeTurckNonlin Φ)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) →
      ENormSqFull k (seriesFunM c) ≤ B ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, reMat (seriesFunM c x) i j * v i * v j) →
      (∑ i : Fin n, ∑ j : Fin n,
        |L2re (fun x => Φ (x, jetM (seriesFunM c) x) i j)
          (fun x => seriesFunM c x i j)|)
        ≤ C * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c)) := by
  classical
  have hn4 : n + 4 < 2 * k := by simpa using hk
  obtain ⟨K, hK0, hK⟩ := jet_sup_le_uniform_level (n := n) (s := k)
  set M : ℝ := K * (1 + B) with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  obtain ⟨Cf, hCf0, hCf⟩ := phi_bound_nosym n Φ hshape lam hlam M M M
  refine ⟨(n : ℝ) ^ 2 * Cf * B + 1,
    add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hCf0) hB) zero_le_one, ?_⟩
  intro N c hc hen hell
  have hmom : ∀ (i j : Fin n) (M' : ℕ),
      Summable (fun k' : Fin n → ℤ => (wt k') ^ M' * ‖c k' i j‖) :=
    fun i j M' => summable_moment_box c hc i j M'
  obtain ⟨hΦsm, Nfun, hNsm, hNdec, hNper⟩ := hshape
  obtain ⟨hdec, hfsm, hfper⟩ :=
    Phi_decomp_smooth (c := c) Φ Nfun hNdec hNsm hNper hΦsm hlam hell hmom
  have hjet : ∀ (m : ℕ) (hm : m + sob n ≤ k) (l : Fin m → Fin n) (i j : Fin n)
      (x : Fin n → ℝ),
      ‖pdVec m l (fun y => seriesFunM c y i j) x‖ ≤ M := by
    intro m hm l i j x
    have hb := hK m hm N c hc l i j x
    have hs : Real.sqrt (ENormSqFull k (seriesFunM c)) ≤ B := by
      have h' := Real.sqrt_le_sqrt hen
      rwa [Real.sqrt_sq hB] at h'
    rw [hMdef]
    refine le_trans hb (mul_le_mul_of_nonneg_left (by linarith) hK0)
  have hval : ∀ (x : Fin n → ℝ) (i j : Fin n), ‖seriesFunM c x i j‖ ≤ M := by
    intro x i j
    have h := hjet 0 (by simp only [sob]; omega) (Classical.arbitrary (Fin 0 → Fin n)) i j x
    rwa [show pdVec 0 (Classical.arbitrary (Fin 0 → Fin n))
        (fun y => seriesFunM c y i j) x = seriesFunM c x i j from by simp [pdVec, pdList]] at h
  have hd1 : ∀ (x : Fin n → ℝ) (a i j : Fin n),
      ‖pd a (fun y => seriesFunM c y i j) x‖ ≤ M := by
    intro x a i j
    have h := hjet 1 (by simp only [sob]; omega) (fun _ : Fin 1 => a) i j x
    rwa [show pdVec 1 (fun _ : Fin 1 => a) (fun y => seriesFunM c y i j) x
        = pd a (fun y => seriesFunM c y i j) x from by simp [pdVec, pdList]] at h
  have hd2 : ∀ (x : Fin n → ℝ) (a b i j : Fin n),
      ‖pd a (pd b (fun y => seriesFunM c y i j)) x‖ ≤ M := by
    intro x a b i j
    have h := hjet 2 (by simp only [sob]; omega) ![a, b] i j x
    rwa [show pdVec 2 ![a, b] (fun y => seriesFunM c y i j) x
        = pd a (pd b (fun y => seriesFunM c y i j)) x from by simp [pdVec, pdList]] at h
  have hLpt : ∀ (x : Fin n → ℝ) (a : Fin n),
      ‖(fun i j : Fin n => pd a (fun y => seriesFunM c y i j) x : MatC n)‖ ≤ M := by
    intro x a
    rw [pi_norm_le_iff_of_nonneg hM0]
    intro i
    rw [pi_norm_le_iff_of_nonneg hM0]
    intro j
    exact hd1 x a i j
  have hBpt : ∀ (x : Fin n → ℝ) (a b : Fin n),
      ‖(fun i j : Fin n => pd a (pd b (fun y => seriesFunM c y i j)) x : MatC n)‖ ≤ M := by
    intro x a b
    rw [pi_norm_le_iff_of_nonneg hM0]
    intro i
    rw [pi_norm_le_iff_of_nonneg hM0]
    intro j
    exact hd2 x a b i j
  have hpt : ∀ x ∈ unitCube (ι := Fin n), ‖Φ (x, jetM (seriesFunM c) x)‖ ≤ Cf := by
    intro x hx
    have hxcube : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
      intro i _
      exact ⟨le_of_lt (hx i (Set.mem_univ i)).1, (hx i (Set.mem_univ i)).2⟩
    exact hCf x hxcube (seriesFunM c x)
      (fun a : Fin n => fun i j : Fin n => pd a (fun y => seriesFunM c y i j) x)
      (fun a b : Fin n => fun i j : Fin n =>
        pd a (pd b (fun y => seriesFunM c y i j)) x)
      (hell x) (hval x) (fun a => hLpt x a) (fun a b => hBpt x a b)
  have hpd0 : ∀ (i j : Fin n) (x : Fin n → ℝ),
      pdVec 0 (Classical.arbitrary (Fin 0 → Fin n)) (fun y => seriesFunM c y i j) x
        = seriesFunM c x i j := fun i j x => by simp [pdVec, pdList]
  have hGbound : ∀ (i j : Fin n),
      (∫ x in unitCube (ι := Fin n), ‖seriesFunM c x i j‖ ^ 2) ≤ B ^ 2 := by
    intro i j
    have h1 : (∫ x in unitCube (ι := Fin n),
        ‖pdVec 0 (Classical.arbitrary (Fin 0 → Fin n))
          (fun y => seriesFunM c y i j) x‖ ^ 2) ≤ ENormSqM 0 (seriesFunM c) :=
      int_pdVec_le_ENormSqM (seriesFunM c) i j _
    have h2 : (∫ x in unitCube (ι := Fin n),
        ‖pdVec 0 (Classical.arbitrary (Fin 0 → Fin n))
          (fun y => seriesFunM c y i j) x‖ ^ 2)
        = ∫ x in unitCube (ι := Fin n), ‖seriesFunM c x i j‖ ^ 2 := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only []
      rw [hpd0 i j x]
    rw [← h2]
    exact h1.trans ((ENormSqM_zero_le_ENormSqFull k (seriesFunM c)).trans hen)
  have hFbound : ∀ (i j : Fin n),
      (∫ x in unitCube (ι := Fin n), ‖Φ (x, jetM (seriesFunM c) x) i j‖ ^ 2)
        ≤ Cf ^ 2 := by
    intro i j
    have hle : ∀ᵐ x ∂(volume.restrict (unitCube (ι := Fin n))),
        ‖Φ (x, jetM (seriesFunM c) x) i j‖ ^ 2 ≤ Cf ^ 2 := by
      filter_upwards [ae_restrict_mem
        (Work.Diff.STE.BesselCont.measSet_unitCube (ι := Fin n))] with x hx
      have h1 : ‖Φ (x, jetM (seriesFunM c) x)‖ ≤ Cf := hpt x hx
      have ha := norm_le_pi_norm (Φ (x, jetM (seriesFunM c) x)) i
      have hb := norm_le_pi_norm ((Φ (x, jetM (seriesFunM c) x)) i) j
      have h2 : ‖Φ (x, jetM (seriesFunM c) x) i j‖ ≤ Cf := by linarith
      nlinarith [h2, hCf0, norm_nonneg (Φ (x, jetM (seriesFunM c) x) i j)]
    calc (∫ x in unitCube (ι := Fin n), ‖Φ (x, jetM (seriesFunM c) x) i j‖ ^ 2)
        ≤ ∫ x in unitCube (ι := Fin n), Cf ^ 2 :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
            (integrable_const _) hle
      _ = Cf ^ 2 := by
          rw [MeasureTheory.setIntegral_const, measureReal_def, Work.Diff.STE.volume_unitCube]
          simp
  have hterm : ∀ (i j : Fin n),
      |L2re (fun x => Φ (x, jetM (seriesFunM c) x) i j)
        (fun x => seriesFunM c x i j)| ≤ Cf * B := by
    intro i j
    have h1 := L2re_le_sqrt ((hfsm i j).continuous) ((Work.Diff.STE.contDiff_seriesFun
      (c := fun k' : Fin n → ℤ => c k' i j) (fun M' => hmom i j M')).continuous)
    rw [sqrt_integral_two, sqrt_integral_two] at h1
    refine h1.trans ?_
    have h2 : Real.sqrt (∫ x in unitCube (ι := Fin n),
        ‖Φ (x, jetM (seriesFunM c) x) i j‖ ^ 2) ≤ Cf := by
      refine (Real.sqrt_le_sqrt (hFbound i j)).trans ?_
      rw [Real.sqrt_sq hCf0]
    have h3 : Real.sqrt (∫ x in unitCube (ι := Fin n),
        ‖seriesFunM c x i j‖ ^ 2) ≤ B := by
      refine (Real.sqrt_le_sqrt (hGbound i j)).trans ?_
      rw [Real.sqrt_sq hB]
    exact mul_le_mul h2 h3 (Real.sqrt_nonneg _) hCf0
  have hsum : (∑ i : Fin n, ∑ j : Fin n,
      |L2re (fun x => Φ (x, jetM (seriesFunM c) x) i j)
        (fun x => seriesFunM c x i j)|) ≤ (n : ℝ) ^ 2 * (Cf * B) := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hterm i j))
    refine h.trans ?_
    rw [Finset.sum_const, Finset.sum_const]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_of_eq (by ring)
  have hge1 : 1 ≤ Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c)) := by
    have h1 : (1 : ℝ) ≤ 1 + ENormSqFull (k + 1) (seriesFunM c) := by
      have := ENormSqFull_nonneg (k + 1) (seriesFunM c)
      linarith
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c)) := Real.sqrt_le_sqrt h1
  calc (∑ i : Fin n, ∑ j : Fin n,
        |L2re (fun x => Φ (x, jetM (seriesFunM c) x) i j)
          (fun x => seriesFunM c x i j)|)
      ≤ (n : ℝ) ^ 2 * (Cf * B) := hsum
    _ ≤ ((n : ℝ) ^ 2 * Cf * B + 1) * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c)) := by
        have h2 : 0 ≤ (n : ℝ) ^ 2 * (Cf * B) := by
          refine mul_nonneg (by positivity) (mul_nonneg hCf0 hB)
        have h3 : 0 ≤ Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c)) := Real.sqrt_nonneg _
        nlinarith [h2, h3, hge1]

end

end Work.Diff.STE.flat
