import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.fsRegimeAt
import Submission.Work.BoseFixB1.sbWord_marginal_integrable
import Submission.Work.BoseFixR.PerBoxWordCrude
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

open _root_.BoseGases Submission.BoseGases Work.BoseBox Work.BoseBoxFix Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 0. The sliding cube (defined here, to keep this file on stable modules) -/

/-- The sliding cube in `u`-coordinates: `{|((ℓd)•u)_j| ≤ ½ℓ(1+d)}`. -/
def sCube (ℓ d : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {u | ∀ j : Fin 3, |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d)}

lemma measurableSet_sCube (ℓ d : ℝ) : MeasurableSet (sCube ℓ d) := by
  have hset : sCube ℓ d = ⋂ j : Fin 3, {u : EuclideanSpace ℝ (Fin 3) |
      |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d)} := by
    ext u; simp [sCube]
  rw [hset]
  refine MeasurableSet.iInter fun j => ?_
  exact ((by fun_prop : Continuous (fun u : EuclideanSpace ℝ (Fin 3) =>
    |((ℓ * d) • u).ofLp j|)).measurable measurableSet_Iic)

/-- The complement of the cube is contained in the corpus's `farSet`. -/
lemma sCube_compl_subset_farSet {ℓ d μ : ℝ} : (sCube ℓ d)ᶜ ⊆ farSet ℓ d μ := by
  intro u hu
  simp only [sCube, Set.mem_setOf_eq, Set.mem_compl_iff, not_forall] at hu
  obtain ⟨j, hj⟩ := hu
  exact ⟨j, lt_of_not_ge hj⟩

/-- The sliding cube is the centred cube of side `(1+d)/d`. -/
lemma sCube_eq_acube {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    sCube ℓ d = Submission.BoseGases.acube ((1 + d) / d) := by
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  ext u
  simp only [sCube, Set.mem_ofPred_eq]
  rw [Submission.BoseGases.mem_acube_iff]
  constructor
  · intro h j
    have h1 := h j
    rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hld] at h1
    have h2 : |u.ofLp j| ≤ (((1 / 2) * ℓ * (1 + d))) / (ℓ * d) := by
      rw [le_div_iff₀ hld]
      linarith
    have h3 : (((1 / 2) * ℓ * (1 + d))) / (ℓ * d) = ((1 + d) / d) / 2 := by
      field_simp
    rw [h3] at h2
    have h4 := abs_le.mp h2
    exact Set.mem_Icc.mpr ⟨by linarith [h4.1], h4.2⟩
  · intro h j
    have h1 : |u.ofLp j| ≤ ((1 + d) / d) / 2 := by
      rw [abs_le]
      exact ⟨by linarith [(Set.mem_Icc.mp (h j)).1], (Set.mem_Icc.mp (h j)).2⟩
    rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hld]
    have h3 : ((1 + d) / d) / 2 * (ℓ * d) = (1 / 2) * ℓ * (1 + d) := by
      field_simp
    nlinarith [abs_nonneg (u.ofLp j), h1, h3]

/-- **The volume of the sliding cube**: `|cube| ≤ 8d^{-3}` for `d ≤ 1`. -/
lemma volume_sCube_le {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1) :
    (MeasureTheory.volume (sCube ℓ d)).toReal ≤ 8 * (d ^ 3)⁻¹ := by
  rw [sCube_eq_acube hℓ hd, Submission.BoseGases.acube_volume _ (by positivity),
    ENNReal.toReal_ofReal (by positivity)]
  have hd3 : 0 < d ^ 3 := by positivity
  rw [div_pow, div_le_iff₀ hd3]
  have h2 : (1 + d) ^ 3 ≤ 8 := by
    have h1 : 1 + d ≤ 2 := by linarith
    have h0 : 0 ≤ 1 + d := by linarith
    calc (1 + d) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ h0 h1 3
      _ = 8 := by norm_num
  calc (1 + d) ^ 3 ≤ 8 := h2
    _ = 8 * (d ^ 3)⁻¹ * d ^ 3 := by
        rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hd3), mul_one]

/-- `d ≤ 1` at the parameters (`d = (μa³)^{6/323}`). -/
lemma paramsAt_d_le_one {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) (ht : μ * A ^ 3 ≤ 1) :
    (Work.BoseBox.paramsAt μ A).d ≤ 1 := by
  have ht0 : 0 < μ * A ^ 3 := by positivity
  rw [Work.BoseFixB1.d_eq_fsXp]
  have h := Work.BoseBox.fsXp_le_fsXp (t := μ * A ^ 3) (a := 6) (b := 0) ht0 ht
    (by norm_num)
  simpa [Work.BoseBox.fsXp] using h

/-! ## 1. The word is nonnegative off the cube -/

/-- If the localised cutoff vanishes identically, so does the localised pair kernel. -/
lemma wSmallPair_eq_zero_of_chiB_zero {M : ℕ} {ℓ d : ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hc : ∀ x : EuclideanSpace ℝ (Fin 3), chiSmallB M ℓ d u x = 0)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    wSmallPair M ℓ d u w x y = 0 := by
  simp only [wSmallPair, hc x, hc y, zero_mul, mul_zero]

/-- If the localised cutoff vanishes identically, the localised potential word vanishes. -/
lemma qLHSwordB_eq_zero_of_chiB_zero {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {M : ℕ} {ℓ d μ : ℝ} {n : ℕ} {u : EuclideanSpace ℝ (Fin 3)}
    (hc : ∀ x : EuclideanSpace ℝ (Fin 3), chiSmallB M ℓ d u x = 0)
    (Φ : Submission.BoseGases.X n → ℝ) :
    Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ = 0 := by
  have hw : ∀ x y : EuclideanSpace ℝ (Fin 3), wSmallPair M ℓ d u v x y = 0 :=
    fun x y => wSmallPair_eq_zero_of_chiB_zero hc x y
  have hw1 : ∀ x y : EuclideanSpace ℝ (Fin 3), wSmall1Pair h M ℓ d u x y = 0 :=
    fun x y => wSmallPair_eq_zero_of_chiB_zero hc x y
  rw [Work.SmallBoxSliding.qLHSwordB, Submission.BoseGases.qLHSword]
  have hpt : (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * (-μ * (∑ i : Fin n, w1Fibre ℓ (wSmall1Pair h M ℓ d u) (x i))
        + (1 / 2) * (∑ p ∈ pairSet n, wSmallPair M ℓ d u v (x p.1) (x p.2)))) = fun _ => (0 : ℝ) := by
    funext x
    have hA : (∑ i : Fin n, w1Fibre ℓ (wSmall1Pair h M ℓ d u) (x i)) = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [w1Fibre]
      have : (fun y : EuclideanSpace ℝ (Fin 3) => wSmall1Pair h M ℓ d u (x i) y) = fun _ => (0 : ℝ) :=
        funext (fun y => hw1 (x i) y)
      rw [this, integral_zero]
    have hB : (∑ p ∈ pairSet n, wSmallPair M ℓ d u v (x p.1) (x p.2)) = 0 :=
      Finset.sum_eq_zero (fun p _ => hw (x p.1) (x p.2))
    rw [hA, hB]
    ring
  rw [hpt, integral_zero]

/-- **The word is nonnegative off the sliding cube**: there the localised cutoff vanishes, so the
potential word vanishes, while the kinetic word is always nonnegative. -/
lemma sbWord_nonneg_off_cube {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {ε₀ μ : ℝ} (hadm : Work.BoseBoxFix.Adm v ε₀ μ) {n : ℕ}
    {u : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∈ (sCube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)ᶜ)
    (Φ : Submission.BoseGases.X n → ℝ) :
    0 ≤ Work.BoseFixB1.sbWord h μ u Φ := by
  have hfar : u ∈ farSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ := sCube_compl_subset_farSet hu
  have hc : ∀ x : EuclideanSpace ℝ (Fin 3),
      chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x = 0 :=
    fun x => Work.SmallBoxSliding.farSet_chiSmallB_zero (adm_ell_pos hadm) (adm_d_pos hadm) hfar x
  have hz : Work.BoseFixB1.sbPot h μ u Φ = 0 :=
    qLHSwordB_eq_zero_of_chiB_zero (v := v) (h := h) hc Φ
  rw [Work.BoseFixB1.sbWord, hz, add_zero]
  show 0 ≤ Work.UBBInputs8.tBwordBInd n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
    (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u Φ
  exact Work.UBBInputs9.A.tBwordBInd_nonneg (adm_ell_pos hadm) (adm_eT_bounds hadm).1 u Φ

/-! ## 2. The assembly -/

/-- **The assembly.**  The pointwise per-box bound (for *every* state, `u` and particle number —
`Work.BoseFixB1B.perBoxCrudeLower`'s shape) gives the target. -/
theorem box_collected_of_perBoxCrude {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J)
    {C₁ ε₁ : ℝ} (hC₁ : 0 ≤ C₁) (hε₁ : 0 < ε₁)
    (hpb : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₁ μ →
      ∀ (n : ℕ)
        (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        -(C₁ * (μ ^ 2 * (_root_.BoseGases.a v)
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            + μ * (_root_.BoseGases.a v)))
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)) :
    ∃ C ε₀ : ℝ, 1 ≤ C ∧ 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        -(C * μ ^ 2 * (_root_.BoseGases.a v)
            * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          ≤ ∫ u : EuclideanSpace ℝ (Fin 3),
              Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  obtain ⟨εR, hεR, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  obtain ⟨εF, hεF, hFS⟩ := Work.BoseFixB1.fsRegimeAt (A := _root_.BoseGases.a v) (R := R) hav hR
  refine ⟨max 1 (9 * C₁), min (min ε₁ εR) (min εF 1), le_max_left _ _,
    lt_min (lt_min hε₁ hεR) (lt_min hεF one_pos), ?_⟩
  intro μ hAdm hJK n Φ hnorm hlow
  have hAdm1 : Work.BoseBoxFix.Adm v ε₁ μ :=
    Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hAdmR : Work.BoseBoxFix.Adm v εR μ :=
    Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hAdmF : Work.BoseBoxFix.Adm v εF μ :=
    Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hμ : 0 < μ := adm_mu_pos hAdm
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  have hdil : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := by
    have h2 := adm_dilute hAdm
    have h3 : (min (min ε₁ εR) (min εF 1) : ℝ) ≤ 1 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  obtain ⟨hKl, hKB1, hKB3h, hmu3, hRsb, hd3, hmuA, htM, hμinv, hAδ, hM1⟩ :=
    hFS μ hμ (adm_dilute hAdmF)
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := adm_d_pos hAdm
  have hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  obtain ⟨hRd, hRchi⟩ := hreg μ hμ (adm_dilute hAdmR)
  -- abbreviations
  let ell : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
  let dd : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
  let MM : ℕ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
  let KB : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB
  let nBr : ℝ := Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
  -- the integrability of the χ-mass
  have hchi : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.SmallBoxSliding.chiMass MM ell dd u) :=
    Work.SmallBoxSliding.integrable_chiSmallB_mass hM hℓ hd
  have hIntK : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
        (Φ : Submission.BoseGases.X n → ℝ)) :=
    Work.BoseFixB1.integrable_sbKin_marginal (v := v) (μ := μ) hℓ hd Φ
  have hIntP : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ)) :=
    (Work.BoseFixB1.sbPot_integral_le_potWordU (v := v) (h := h) hv1 hvrad hR hv_supp hav
      hℓ hd hM hRd hRchi Φ).1
  have hIntW : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)) := by
    have heq : (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
        = (fun u : EuclideanSpace ℝ (Fin 3) =>
            Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
              (Φ : Submission.BoseGases.X n → ℝ))
          + (fun u : EuclideanSpace ℝ (Fin 3) =>
              Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ)) := by
      funext u
      rw [Pi.add_apply]
      rfl
    rw [heq]; exact hIntK.add hIntP
  have hcube_fin : MeasureTheory.volume (sCube ell dd) < ⊤ := by
    rw [sCube_eq_acube hℓ hd, Submission.BoseGases.acube_volume _ (by positivity)]
    exact ENNReal.ofReal_lt_top
  have hcube_ne : MeasureTheory.volume (sCube ell dd) ≠ ⊤ := ne_of_lt hcube_fin
  -- the comparison function on the cube
  have hlo_int : MeasureTheory.IntegrableOn (fun u : EuclideanSpace ℝ (Fin 3) =>
      -(C₁ * (μ ^ 2 * (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass MM ell dd u
        + μ * (_root_.BoseGases.a v))) * nBr) (sCube ell dd) := by
    have h2 : MeasureTheory.IntegrableOn (fun u : EuclideanSpace ℝ (Fin 3) =>
        μ ^ 2 * (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass MM ell dd u
          + μ * (_root_.BoseGases.a v)) (sCube ell dd) :=
      ((hchi.integrableOn.const_mul (μ ^ 2 * (_root_.BoseGases.a v))).add
        (MeasureTheory.integrableOn_const hcube_ne))
    exact ((h2.const_mul C₁).neg).mul_const nBr
  have hmono : (∫ u in sCube ell dd,
        -(C₁ * (μ ^ 2 * (_root_.BoseGases.a v)
          * Work.SmallBoxSliding.chiMass MM ell dd u + μ * (_root_.BoseGases.a v))) * nBr)
      ≤ ∫ u in sCube ell dd, Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    exact MeasureTheory.integral_mono_ae hlo_int hIntW.integrableOn
      (Filter.Eventually.of_forall (fun u => hpb μ hAdm1 n Φ u))
  have hcomp : 0 ≤ ∫ u in (sCube ell dd)ᶜ,
        Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    exact MeasureTheory.setIntegral_nonneg (measurableSet_sCube ell dd).compl
      (fun u hu => sbWord_nonneg_off_cube hAdm hu (Φ : Submission.BoseGases.X n → ℝ))
  have hval : (∫ u in sCube ell dd,
        -(C₁ * (μ ^ 2 * (_root_.BoseGases.a v)
          * Work.SmallBoxSliding.chiMass MM ell dd u + μ * (_root_.BoseGases.a v))) * nBr)
      = -(C₁ * nBr) * (μ ^ 2 * (_root_.BoseGases.a v)
            * (∫ u in sCube ell dd, Work.SmallBoxSliding.chiMass MM ell dd u)
          + μ * (_root_.BoseGases.a v) * (MeasureTheory.volume (sCube ell dd)).toReal) := by
    rw [show (fun u : EuclideanSpace ℝ (Fin 3) =>
        -(C₁ * (μ ^ 2 * (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass MM ell dd u
          + μ * (_root_.BoseGases.a v))) * nBr)
        = (fun u : EuclideanSpace ℝ (Fin 3) => (-(C₁ * nBr))
            * (μ ^ 2 * (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass MM ell dd u
              + μ * (_root_.BoseGases.a v))) by funext u; ring]
    rw [MeasureTheory.integral_const_mul]
    rw [show (∫ u in sCube ell dd, (fun u : EuclideanSpace ℝ (Fin 3) =>
          μ ^ 2 * (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass MM ell dd u
            + μ * (_root_.BoseGases.a v)) u)
        = μ ^ 2 * (_root_.BoseGases.a v)
            * (∫ u in sCube ell dd, Work.SmallBoxSliding.chiMass MM ell dd u)
          + μ * (_root_.BoseGases.a v) * (MeasureTheory.volume (sCube ell dd)).toReal from by
      have h1 : MeasureTheory.Integrable
          (fun u : EuclideanSpace ℝ (Fin 3) =>
            μ ^ 2 * (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass MM ell dd u)
          (MeasureTheory.volume.restrict (sCube ell dd)) := hchi.integrableOn.const_mul _
      have h2 : MeasureTheory.Integrable (fun _ : EuclideanSpace ℝ (Fin 3) =>
          μ * (_root_.BoseGases.a v)) (MeasureTheory.volume.restrict (sCube ell dd)) :=
        MeasureTheory.integrableOn_const hcube_ne
      rw [MeasureTheory.integral_add h1 h2, MeasureTheory.integral_const_mul,
        MeasureTheory.setIntegral_const]
      simp only [smul_eq_mul, Measure.real_def]
      ring]
  have hchiI : (∫ u in sCube ell dd, Work.SmallBoxSliding.chiMass MM ell dd u) ≤ ell ^ 3 := by
    have hnn : ∀ᵐ (u : EuclideanSpace ℝ (Fin 3)) ∂MeasureTheory.volume,
        0 ≤ Work.SmallBoxSliding.chiMass MM ell dd u := by
      filter_upwards with u
      exact Work.SmallBoxSliding.chiMass_nonneg MM ell dd u
    calc (∫ u in sCube ell dd, Work.SmallBoxSliding.chiMass MM ell dd u)
        ≤ ∫ u : EuclideanSpace ℝ (Fin 3), Work.SmallBoxSliding.chiMass MM ell dd u :=
          MeasureTheory.setIntegral_le_integral hchi hnn
      _ = ell ^ 3 := Work.SmallBoxSliding.integral_chiMass_eq hM hℓ hd
  have hvolI : (MeasureTheory.volume (sCube ell dd)).toReal ≤ 8 * (dd ^ 3)⁻¹ :=
    volume_sCube_le hℓ hd (paramsAt_d_le_one hav hμ hdil)
  -- the arithmetic
  have hnBr0 : 0 ≤ nBr := Work.BoseFixB1.normB_nonneg _
  have hℓ3 : 0 ≤ ell ^ 3 := by positivity
  have hKB3nn : 0 ≤ KB ^ 3 :=
    pow_nonneg (le_of_lt (Work.BoseFixB1.paramsAt_KB_pos hAdm)) 3
  have hX : μ ^ 2 * (_root_.BoseGases.a v)
        * (∫ u in sCube ell dd, Work.SmallBoxSliding.chiMass MM ell dd u)
      + μ * (_root_.BoseGases.a v) * (MeasureTheory.volume (sCube ell dd)).toReal
      ≤ 9 * (μ ^ 2 * (_root_.BoseGases.a v) * ell ^ 3) := by
    have h0a : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v) := by positivity
    have h0b : 0 ≤ μ * (_root_.BoseGases.a v) := by positivity
    have h1 : μ ^ 2 * (_root_.BoseGases.a v)
          * (∫ u in sCube ell dd, Work.SmallBoxSliding.chiMass MM ell dd u)
        ≤ μ ^ 2 * (_root_.BoseGases.a v) * ell ^ 3 :=
      mul_le_mul_of_nonneg_left hchiI h0a
    have hKBl : KB ^ 3 ≤ μ * ell ^ 3 := by
      show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
        ≤ μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
      rw [Work.BoseFixB1.KB_eq_fsXp,
        Work.BoseBox.fsXp_pow (le_of_lt ht0) (-6) 3,
        Work.BoseFixB1.mu_ell_cube_eq hav hμ]
      refine Work.BoseBox.fsXp_le_fsXp ht0 hdil ?_
      norm_num
    have hd3' : (dd ^ 3)⁻¹ ≤ KB ^ 3 := hd3
    have h3 : μ * (_root_.BoseGases.a v) * (dd ^ 3)⁻¹
        ≤ μ ^ 2 * (_root_.BoseGases.a v) * ell ^ 3 := by
      have h4 : μ * (_root_.BoseGases.a v) * (dd ^ 3)⁻¹
          ≤ μ * (_root_.BoseGases.a v) * KB ^ 3 := mul_le_mul_of_nonneg_left hd3' h0b
      have h5 : μ * (_root_.BoseGases.a v) * KB ^ 3
          ≤ μ * (_root_.BoseGases.a v) * (μ * ell ^ 3) := mul_le_mul_of_nonneg_left hKBl h0b
      have h6 : μ * (_root_.BoseGases.a v) * (μ * ell ^ 3)
          = μ ^ 2 * (_root_.BoseGases.a v) * ell ^ 3 := by ring
      linarith [h4, h5, h6]
    have h2' : μ * (_root_.BoseGases.a v) * (MeasureTheory.volume (sCube ell dd)).toReal
        ≤ μ * (_root_.BoseGases.a v) * (8 * (dd ^ 3)⁻¹) :=
      mul_le_mul_of_nonneg_left hvolI h0b
    have h7 : μ * (_root_.BoseGases.a v) * (8 * (dd ^ 3)⁻¹)
        ≤ 8 * (μ ^ 2 * (_root_.BoseGases.a v) * ell ^ 3) := by linarith [h3]
    linarith [h1, h2', h7]
  have hfin : -(C₁ * nBr) * (9 * (μ ^ 2 * (_root_.BoseGases.a v) * ell ^ 3))
      ≤ -(C₁ * nBr) * (μ ^ 2 * (_root_.BoseGases.a v)
            * (∫ u in sCube ell dd, Work.SmallBoxSliding.chiMass MM ell dd u)
          + μ * (_root_.BoseGases.a v) * (MeasureTheory.volume (sCube ell dd)).toReal) := by
    refine mul_le_mul_of_nonpos_left hX ?_
    nlinarith [mul_nonneg hC₁ hnBr0]
  have hmax : -(max 1 (9 * C₁) * (μ ^ 2 * (_root_.BoseGases.a v) * ell ^ 3)) * nBr
      ≤ -(9 * C₁) * (μ ^ 2 * (_root_.BoseGases.a v) * ell ^ 3) * nBr := by
    have h9 : 9 * C₁ ≤ max 1 (9 * C₁) := le_max_right _ _
    have h0a : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v) := by positivity
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h9 h0a) hℓ3) hnBr0
    nlinarith [h]
  have hsplit := MeasureTheory.integral_add_compl (measurableSet_sCube ell dd) hIntW
  have hid : -(C₁ * nBr) * (9 * (μ ^ 2 * (_root_.BoseGases.a v) * ell ^ 3))
      = -(9 * C₁) * (μ ^ 2 * (_root_.BoseGases.a v) * ell ^ 3) * nBr := by ring
  have hkey : -(max 1 (9 * C₁) * (μ ^ 2 * (_root_.BoseGases.a v) * ell ^ 3)) * nBr
      ≤ ∫ u : EuclideanSpace ℝ (Fin 3),
          Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    have h1 : -(C₁ * nBr) * (9 * (μ ^ 2 * (_root_.BoseGases.a v) * ell ^ 3))
        ≤ ∫ u in sCube ell dd,
            Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) :=
      le_trans hfin (hval ▸ hmono)
    linarith [hsplit, h1, hcomp, hmax, hid]
  have hkey' : -(max 1 (9 * C₁) * μ ^ 2 * (_root_.BoseGases.a v)
        * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3)
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      ≤ ∫ u : EuclideanSpace ℝ (Fin 3),
          Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [show max 1 (9 * C₁) * μ ^ 2 * (_root_.BoseGases.a v)
          * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
        = max 1 (9 * C₁) * (μ ^ 2 * (_root_.BoseGases.a v)
            * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) by ring]
    exact hkey
  exact hkey'

/-! ## 3. The target -/

theorem box_collected_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J) :
    ∃ C ε₀ : ℝ, 1 ≤ C ∧ 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
        0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        -(C * μ ^ 2 * BoseGases.a v * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          ≤ ∫ u : EuclideanSpace ℝ (Fin 3),
              Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  obtain ⟨ε₁, C₁, hε₁, hC₁, hpb⟩ :=
    Work.BoseFixR.PerBoxWordCrude (v := v) h hv hv1 hvrad hR hv_supp hav
  exact box_collected_of_perBoxCrude h hv hv1 hvrad hR hv_supp hav hJ hC₁ hε₁ hpb

end Work.BoseFixR
