import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.arithFlatBox
import Submission.Work.BoseFixB1S.boxPInd_ae_eq_zero_of_ae_eq_zero
import Submission.Work.BoseFixB1S.boxQSum_ge_boxQ0_of_boxQInd_ae_zero
import Submission.Work.BoseFixB1S.mf_boxFlatCount_eq
import Submission.Work.BoseFixB1S.mf_boxMass_pos_of_mem_interiorSet
import Submission.Work.BoseFixB1S.mf_boxQ0_ge_flatCount
import Submission.Work.BoseFixB1S.mf_boxQ0_integrable_inputs
import Submission.Work.BoseFixB1S.perBoxGapBranchB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## 1. The elementary consequences of `mfQ = 0` -/

/-- **`mfQ = 0` gives `Q_{B(u),i}Φ = 0` a.e. for every slot.**  `mfQ` is the sum of the slot
integrals `∫_{abox}(Q_iΦ)²`, each nonnegative; a vanishing sum of nonnegative terms has each
term `0`, and a vanishing integral of a nonnegative *integrable* function vanishes a.e.  (The
integrand is measurable — `Work.SlotWord.measurable_boxQInd` — and bounded on the compact box —
`Work.SlotWord.abs_boxQInd_le_of_bound` with the bound of `Φ`.) -/
theorem mf_boxQInd_ae_eq_zero {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    (hℓ : 0 < sideAt μ (a v)) (hQ : mfQ v μ n Φ u = 0) (hΦc : Continuous Φ) :
    ∀ i : Fin n,
      Work.UBBInputs8.boxQInd (mfV v μ u) (boxA v μ u) i Φ
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n (sideAt μ (a v)))] 0 := by
  have hA : MeasurableSet (boxA v μ u) :=
    Work.SmallBoxSliding.measurableSet_dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u
  have hAc : boxA v μ u ⊆ Submission.BoseGases.acube (sideAt μ (a v)) :=
    Work.SmallBoxSliding.dlBox_subset_acube (sideAt μ (a v)) (paramsAt μ (a v)).d u
  have hsum : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n (sideAt μ (a v)),
      (Work.UBBInputs8.boxQInd (mfV v μ u) (boxA v μ u) i Φ x) ^ 2) = 0 := by
    simpa only [mfQ_def, mfV_def, boxA, Work.UBBInputs8.cnPlusBoxInd] using hQ
  obtain ⟨C, hC0, hCb⟩ := exists_abox_bound hℓ hΦc
  have hfin : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
      (boxA v μ u) < ⊤ := Work.BoseFixB1S.volume_A_lt_top hℓ hAc
  intro i
  have hi : (∫ x in Submission.BoseGases.abox n (sideAt μ (a v)),
      (Work.UBBInputs8.boxQInd (mfV v μ u) (boxA v μ u) i Φ x) ^ 2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => integral_nonneg fun x => sq_nonneg _)).mp
      hsum i (Finset.mem_univ i)
  have hmeas : Measurable (Work.UBBInputs8.boxQInd (mfV v μ u) (boxA v μ u) i Φ) :=
    Work.SlotWord.measurable_boxQInd _ _ hA i hΦc.measurable
  have hbd := fun x (hx : x ∈ Submission.BoseGases.abox n (sideAt μ (a v))) =>
    Work.SlotWord.abs_boxQInd_le_of_bound (volA := mfV v μ u) (C := C)
      (sideAt μ (a v)) hAc hC0 hfin (fun y hy => hCb y hy) i x hx
  have hInt : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        (Work.UBBInputs8.boxQInd (mfV v μ u) (boxA v μ u) i Φ x) ^ 2)
      (Submission.BoseGases.abox n (sideAt μ (a v))) MeasureTheory.volume :=
    Work.BoseFixB1S.integrableOn_sq_of_bound hℓ hmeas hbd
  have hae : (fun x : Submission.BoseGases.X n =>
      (Work.UBBInputs8.boxQInd (mfV v μ u) (boxA v μ u) i Φ x) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n (sideAt μ (a v)))] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hInt).mp hi
  filter_upwards [hae] with x hx
  simpa only [Pi.zero_apply, sq_eq_zero_iff] using hx

/-- **The localised one-body mass is the `boxM1` of the box words.**  Both are the global nested
integral `∫∫w_{1,B(u)}` (`Work.BoseFixB1.boxM1_eq_nested`, the kernel vanishing off the box
— `Work.BoseFixB1.wSmallPair_eq_zero_of_notMem_dlBox`). -/
theorem mfW_eq_mfM1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {u : EuclideanSpace ℝ (Fin 3)} (hM : 1 ≤ (paramsAt μ (a v)).M)
    (hℓ : 0 < sideAt μ (a v)) (hd : 0 < (paramsAt μ (a v)).d) :
    mfW h μ u = mfM1 h μ u := by
  rw [mfM1, Work.BoseFixB1.boxM1_eq_nested]
  · rfl
  · intro x y hxy
    exact Work.BoseFixB1.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u hxy

/-- `mfBracket ≥ μ(a v)`: the error bracket contains the linear term `μ(a v)` and its other
summand is nonnegative. -/
theorem le_mfBracket {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε₀ R μ : ℝ}
    (h : Work.BoseBoxFix.Adm v ε₀ μ) (hav : 0 < a v) (u : EuclideanSpace ℝ (Fin 3)) :
    μ * a v ≤ mfBracket v R μ u := by
  have hμ : 0 ≤ μ := (Work.BoseFixB1.adm_mu_pos h).le
  have hχ : 0 ≤ Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u := Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hKB : 0 ≤ (paramsAt μ (a v)).KB := (Work.BoseFixB1.paramsAt_KB_pos h).le
  have h1 : 0 ≤ R ^ 2 * μ ^ (2 / 3 : ℝ) := by positivity
  have h2 : 0 ≤ (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  have h3 : 0 ≤ μ ^ 2 * (a v) * (R ^ 2 * μ ^ (2 / 3 : ℝ)
      + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
      * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav.le) (add_nonneg h1 h2)) hχ
  have h4 : 0 ≤ μ * (a v) := mul_nonneg hμ hav.le
  rw [mfBracket]
  linarith

/-- `mfI ≥ 0`. -/
theorem mfI_nonneg' {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} : 0 ≤ mfI v μ n Φ := by
  unfold mfI
  exact integral_nonneg fun x => sq_nonneg _

/-! ## 2. The target -/

theorem flatBranchB1_boxConstant {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)),
          Work.BoseFixB1S.mfInt v μ u → Continuous Φ → Work.BoseFixB1S.mfSupp v μ n Φ u →
          Work.BoseFixB1S.mfQ v μ n Φ u = 0 →
          Work.BoseFixB1S.mfLhs h R C μ n Φ u ≤ Work.BoseFixB1S.mfRhs h μ n Φ u := by
  -- the three constants: the FS regime, the mass bound, and the box-mass facts
  obtain ⟨ε_reg, hε_reg, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  obtain ⟨ε_K, K, hε_K, hK0, hKb⟩ :=
    Work.BoseFixB1S.w1MassB_le_const_mul_boxMass (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨ε_b, Kb, hε_b, _hKb0, hb⟩ :=
    Work.BoseFixB1S.boxM1Info (v := v) h hv hv1 hvrad hR hv_supp hav
  refine ⟨min (min 1 ε_reg) (min ε_K ε_b), 5 * K / 2, ?_, ?_, ?_⟩
  · exact lt_min (lt_min one_pos hε_reg) (lt_min hε_K hε_b)
  · linarith
  intro μ hAdm n Φ u hu hΦc hsupp hQ
  have hε1 : min (min 1 ε_reg) (min ε_K ε_b) ≤ 1 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hεreg : min (min 1 ε_reg) (min ε_K ε_b) ≤ ε_reg :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hεK : min (min 1 ε_reg) (min ε_K ε_b) ≤ ε_K :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hεb : min (min 1 ε_reg) (min ε_K ε_b) ≤ ε_b :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have ha : 0 < a v := Work.BoseFixB1.adm_a_pos hAdm
  have hℓ : 0 < sideAt μ (a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ (paramsAt μ (a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hvol : 0 < mfV v μ u := mf_boxMass_pos_of_mem_interiorSet hAdm hε1 hu
  obtain ⟨hR16, hRχ⟩ := hreg μ hμ (le_trans (Work.BoseFixB1.adm_dilute hAdm) hεreg)
  -- the box facts
  obtain ⟨hM1nn, _hM1chi, hM1M2⟩ := hb μ (Work.BoseFixB1.Adm.mono hAdm hεb) u
  have hM1KV : mfW h μ u ≤ K * (a v) * mfV v μ u :=
    hKb μ (Work.BoseFixB1.Adm.mono hAdm hεK) u
  have hA : MeasurableSet (boxA v μ u) :=
    Work.SmallBoxSliding.measurableSet_dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u
  have hAc : boxA v μ u ⊆ Submission.BoseGases.acube (sideAt μ (a v)) :=
    Work.SmallBoxSliding.dlBox_subset_acube (sideAt μ (a v)) (paramsAt μ (a v)).d u
  have hvolA : mfV v μ u = (MeasureTheory.volume (boxA v μ u)).toReal := by
    rw [mfV_def, Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  -- the a.e. vanishing of the box projections
  have hQae := mf_boxQInd_ae_eq_zero (v := v) (μ := μ) (n := n) (Φ := Φ) (u := u) hℓ hQ hΦc
  have hPae : ∀ (i j : Fin n), i ≠ j → Work.UBBInputs8.boxPInd (mfV v μ u) (boxA v μ u) i
      (Work.UBBInputs8.boxQInd (mfV v μ u) (boxA v μ u) j Φ)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n (sideAt μ (a v)))] 0 := by
    intro i j _
    exact boxPInd_ae_eq_zero_of_ae_eq_zero hℓ hvol hA hvolA hAc i
      (Work.SlotWord.measurable_boxQInd _ _ hA j hΦc.measurable) (hQae j)
  -- the two integrability side conditions
  obtain ⟨hw2i, hfib⟩ := mf_boxQ0_integrable_inputs h hv hv1 hvrad hR hv_supp hℓ hd hR16 hRχ
  -- the flat-count collapse
  have hS : mfS v μ n Φ u = (n : ℝ) * mfI v μ n Φ := mf_boxFlatCount_eq hℓ hΦc hsupp hQ
  -- the `boxQ₀` bound, with the count collapsed
  have hbox0 : (1 / 2) * (mfW h μ u / (mfV v μ u) ^ 2)
      * ((((n : ℝ) * mfI v μ n Φ) ^ 2 - ((n : ℝ) * mfI v μ n Φ) * mfI v μ n Φ))
      / mfI v μ n Φ
      - μ * (mfW h μ u / mfV v μ u) * ((n : ℝ) * mfI v μ n Φ) ≤ mfQ0 h μ n Φ u := by
    have h := mf_boxQ0_ge_flatCount (v := v) h (n := n) (Φ := Φ) (μ := μ) (u := u)
      hμ.le hvol hΦc hM1nn hM1M2 hw2i hfib
    rw [hS, ← mfW_eq_mfM1 hM1 hℓ hd] at h
    exact h
  -- the pure-real inequality
  have harith : mfLhs h R (5 * K / 2) μ n Φ u
      ≤ (1 / 2) * (mfW h μ u / (mfV v μ u) ^ 2)
        * ((((n : ℝ) * mfI v μ n Φ) ^ 2 - ((n : ℝ) * mfI v μ n Φ) * mfI v μ n Φ))
        / mfI v μ n Φ
        - μ * (mfW h μ u / mfV v μ u) * ((n : ℝ) * mfI v μ n Φ) :=
    arithFlatBox (n := n) (μ := μ) (volA := mfV v μ u) (W := mfW h μ u)
      (I := mfI v μ n Φ) (K := K) (av := a v) (br := mfBracket v R μ u) (C := 5 * K / 2)
      ha hμ hvol (Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u) mfI_nonneg'
      hK0 (le_refl _) hM1KV (le_mfBracket hAdm ha u)
  -- the potential word
  have hpot : mfQSum h μ n Φ u
      = Submission.BoseGases.qLHSword (N := n) (sideAt μ (a v)) μ
          (Submission.BoseGases.wSmallPair (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u v)
          (Submission.BoseGases.wSmall1Pair h (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u) Φ :=
    (Work.BoseFixB1.bqPotsplit (R0 := R) hv_supp hR hv hvrad hv1 h hM1 hℓ hd hR16 hRχ u
      hvol hΦc).symm
  -- the cross terms
  have hsum0 : mfQ0 h μ n Φ u ≤ mfQSum h μ n Φ u :=
    boxQSum_ge_boxQ0_of_boxQInd_ae_zero hℓ hvol hA hvolA hAc hΦc hQae hPae
      (fun x y => wSmallPair_nonneg_B1S u x y (hv (x - y)))
  -- the kinetic word
  have hkin : 0 ≤ sbKin (v := v) μ (paramsAt μ (a v)).M u Φ := by
    rw [sbKin]
    exact Work.UBBInputs9.A.tBwordBInd_nonneg hℓ (Work.BoseFixB1.adm_eT_bounds hAdm).1 u Φ
  have hRhs : mfQSum h μ n Φ u ≤ mfRhs h μ n Φ u :=
    le_trans (le_of_eq hpot) (le_add_of_nonneg_left hkin)
  linarith [harith, hbox0, hsum0, hRhs]

end

end Work.BoseFixB1S
