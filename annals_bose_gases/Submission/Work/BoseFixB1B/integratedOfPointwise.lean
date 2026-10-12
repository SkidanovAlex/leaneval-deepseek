import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.integrableOn_sbWord_interiorSet_regime
import Submission.Work.BoseFixB1.perBoxF_pieces
import Submission.Work.BoseFixB1.volume_interiorSet_ne_top
import Submission.Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime
import Submission.Work.BoseFixB1.w1MassB_nonneg
import Submission.Work.BoseFixB1B.MeasurabilityGlobal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.BoseFixB1 Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 0. Pointwise ingredients -/

/-- **`Work.BoseFixB1.PerBoxF` rearranged** into the "`u`-wise inequality between the two integrands" shape that
is integrated over `I₋`: moving the (positive) error terms and the background to the right-hand
side.  Pure unfolding plus `linarith`. -/
lemma ipw_le_rearrange {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R c₁ C μ : ℝ} {n : ℕ} {Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))}
    {u : EuclideanSpace ℝ (Fin 3)} (hper : Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u) :
    c₁ * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
          psiWeight 1 μ (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)))
      ≤ sbWord h μ u (Φ : X n → ℝ)
        + (1 / 2) * μ ^ 2 * w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
        + C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
              + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
              * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
              * normB v μ n (Φ : X n → ℝ)
            + μ * (a v) * normB v μ n (Φ : X n → ℝ)) := by
  rw [Work.BoseFixB1.PerBoxF] at hper
  linarith

/-- The smooth small-box count `Σᵢχ_{B(u)}(xᵢ)²` is nonnegative. -/
lemma ipw_nCountB_nonneg {M : ℕ} {ℓ d : ℝ} {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ}
    (x : X n) : 0 ≤ nCountB M ℓ d u x :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The cutoff mass `∫χ_{B(u)}²` is nonnegative. -/
lemma ipw_chiMass_nonneg {M : ℕ} {ℓ d : ℝ} {u : EuclideanSpace ℝ (Fin 3)} :
    0 ≤ chiMass M ℓ d u := by
  rw [Work.SmallBoxSliding.chiMass_def]
  exact integral_nonneg fun x => sq_nonneg _

/-- FS's weight is nonnegative on the physical range (`0 < μ`, `0 ≤ t`). -/
lemma ipw_psiWeight_one_nonneg {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    0 ≤ psiWeight 1 μ t := by
  rw [Work.SmallBoxSliding.psiWeight]
  refine div_nonneg (mul_nonneg zero_le_one (sq_nonneg _)) ?_
  have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (inv_nonneg.mpr hμ.le)
  linarith

/-- The `x`-integral of `Work.BoseFixB1.PerBoxF`'s `F`-term is nonnegative. -/
lemma ipw_inner_nonneg {μ : ℝ} (hμ : 0 < μ) {ℓ d : ℝ}
    {M : ℕ} {n : ℕ} {Φ : X n → ℝ} (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ ∫ x in abox n ℓ, (Φ x) ^ 2 *
        psiWeight 1 μ (nCountB M ℓ d u x / chiMass M ℓ d u) :=
  integral_nonneg fun x =>
    mul_nonneg (sq_nonneg _)
      (ipw_psiWeight_one_nonneg hμ (div_nonneg (ipw_nCountB_nonneg x) (ipw_chiMass_nonneg)))

/-! ## 1. The integrated per-box bound -/

theorem integratedPerBox_of_pointwise {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J)
    (hper : ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          ∀ (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u)
    (hsbInt : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ {n : ℕ}
      (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
      MeasureTheory.IntegrableOn
        (fun u : EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
        (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ))
    (hw1le : ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3),
      Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      ≤ C * (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) :
    ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
            c₁ * Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ)
              ≤ (∫ u in Work.SmallBoxSliding.interiorSet
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                    Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
                + (1 / 2) * μ ^ 2
                    * (∫ u in Work.SmallBoxSliding.interiorSet
                        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                        Work.BoseFixB1.w1MassB h
                          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                    * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                + C * (μ ^ 2 * (_root_.BoseGases.a v)
                          * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                                    * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
                              + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                          * (∫ u in Work.SmallBoxSliding.interiorSet
                              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                              Work.SmallBoxSliding.chiMass
                                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                        + μ * (_root_.BoseGases.a v)
                          * (MeasureTheory.volume (Work.SmallBoxSliding.interiorSet
                              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal)
                    * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
  obtain ⟨ε₀, c₁, C, hε₀, hc₁, hC, hmain⟩ := hper
  obtain ⟨ε₀s, hε₀s, hsbInt⟩ := hsbInt
  obtain ⟨ε₀w, Cw, hε₀w, hCw0, hCw⟩ := hw1le
  refine ⟨min ε₀ (min ε₀s ε₀w), c₁, C, lt_min hε₀ (lt_min hε₀s hε₀w), hc₁, hC, ?_⟩
  intro μ hAdm n Φ hlow
  have hAdm₀ : Work.BoseBoxFix.Adm v ε₀ μ :=
    Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdms : Work.BoseBoxFix.Adm v ε₀s μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hAdmw : Work.BoseBoxFix.Adm v ε₀w μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_right _ _))
  have hμ : 0 < μ := hAdm.1
  -- local abbreviations (definitional, so all the rewrites below are defeq-compatible)
  let ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
  let dd : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
  let MM : ℕ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
  let av : ℝ := _root_.BoseGases.a v
  let KB : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB
  let G : ℝ := (R / (ℓ * dd)) ^ 2 + KB ^ 3 * (μ * av ^ 3) ^ (1 / 2 : ℝ)
  let nB : ℝ := Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
  let I : Set (EuclideanSpace ℝ (Fin 3)) := Work.SmallBoxSliding.interiorSet ℓ dd μ
  let AA : EuclideanSpace ℝ (Fin 3) → ℝ := fun u =>
    ∫ x in abox n ℓ, (Φ x) ^ 2 *
      Work.SmallBoxSliding.psiWeight 1 μ
        (Work.BoseFixB1.nCountB MM ℓ dd u x / Work.SmallBoxSliding.chiMass MM ℓ dd u)
  let ff : EuclideanSpace ℝ (Fin 3) → ℝ := fun u =>
    c₁ * (Work.BoseFixB1.w1MassB h MM ℓ dd u * AA u)
  let gg : EuclideanSpace ℝ (Fin 3) → ℝ := fun u =>
    Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)
      + (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h MM ℓ dd u * nB
      + C * (μ ^ 2 * av * G * Work.SmallBoxSliding.chiMass MM ℓ dd u * nB + μ * av * nB)
  have hℓpos : 0 < ℓ := Work.BoseFixB1.adm_ell_pos hAdm
  have hdpos : 0 < dd := Work.BoseFixB1.adm_d_pos hAdm
  have hImeas : MeasurableSet I := Work.SmallBoxSliding.measurableSet_interiorSet ℓ dd μ
  have hIvol : MeasureTheory.volume I ≠ ⊤ :=
    Work.BoseFixB1.volume_interiorSet_ne_top hℓpos hdpos
  -- (1) the pointwise inequality on `I₋ ⊆ goodSet`
  have hpt : ∀ u ∈ I, ff u ≤ gg u := by
    intro u hu
    have hmem : u ∈ Work.SmallBoxSliding.interiorSet ℓ dd μ := hu
    have hp : Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u := hmain μ hAdm₀ n Φ hlow u hmem
    exact ipw_le_rearrange hp
  -- (2) the right-hand side is integrable on `I₋`
  have hM1 : 1 ≤ MM := by
    simp [MM, Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]
  have hchiOn : IntegrableOn (fun u => Work.SmallBoxSliding.chiMass MM ℓ dd u) I :=
    ((Work.SmallBoxSliding.integrable_chiSmallB_mass hM1 hℓpos hdpos).congr
      (Filter.Eventually.of_forall fun u =>
        (Work.SmallBoxSliding.chiMass_def MM ℓ dd u).symm)).integrableOn
  have hw1Measc : AEStronglyMeasurable
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB1.w1MassB h MM ℓ dd u) volume :=
    Work.BoseFixB1B.aeStronglyMeasurable_w1MassB_global (v := v) h hv hvrad hR hv_supp hℓpos hdpos
  have hw1On : IntegrableOn (fun u => Work.BoseFixB1.w1MassB h MM ℓ dd u) I := by
    refine Integrable.mono' (hchiOn.const_mul (Cw * av)) hw1Measc.restrict ?_
    filter_upwards with u
    have h1 : 0 ≤ Work.BoseFixB1.w1MassB h MM ℓ dd u :=
      Work.BoseFixB1.w1MassB_nonneg (v := v) h hv hvrad hR hv_supp hℓpos hdpos u
    have h3 := hCw μ hAdmw u
    rw [Real.norm_of_nonneg h1]
    simpa only [MM, ℓ, dd, av] using h3
  have hsbOn : IntegrableOn
      (fun u => Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)) I :=
    hsbInt μ hAdms (Φ := Φ)
  have hYint : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 3) => μ * av * nB) I :=
    integrableOn_const hIvol enorm_ne_top
  have hXint : IntegrableOn
      (fun u => μ ^ 2 * av * G * Work.SmallBoxSliding.chiMass MM ℓ dd u * nB) I :=
    ((hchiOn.const_mul (μ ^ 2 * av * G)).const_mul nB).congr
      (Filter.Eventually.of_forall fun u => by ring)
  have h2 : IntegrableOn
      (fun u => (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h MM ℓ dd u * nB) I :=
    ((hw1On.const_mul ((1 / 2) * μ ^ 2)).const_mul nB).congr
      (Filter.Eventually.of_forall fun u => by ring)
  have h3 : IntegrableOn
      (fun u => C * (μ ^ 2 * av * G * Work.SmallBoxSliding.chiMass MM ℓ dd u * nB
        + μ * av * nB)) I :=
    (hXint.add hYint).const_mul C
  have h12 : IntegrableOn
      (fun u => Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)
        + (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h MM ℓ dd u * nB) I := hsbOn.add h2
  have hggOn : IntegrableOn gg I := by
    have hsum : IntegrableOn
        (fun u => (Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)
          + (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h MM ℓ dd u * nB)
          + C * (μ ^ 2 * av * G * Work.SmallBoxSliding.chiMass MM ℓ dd u * nB
            + μ * av * nB)) I := h12.add h3
    simpa only [gg] using hsum
  -- (3) the left-hand side is nonnegative
  have hffnn : 0 ≤ᵐ[MeasureTheory.volume.restrict I] ff := by
    filter_upwards with u
    refine mul_nonneg hc₁.le (mul_nonneg ?_ ?_)
    · exact Work.BoseFixB1.w1MassB_nonneg (v := v) h hv hvrad hR hv_supp hℓpos hdpos u
    · exact ipw_inner_nonneg (ℓ := ℓ) (d := dd) (M := MM) (n := n)
        (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hμ u
  -- (4) integrate the pointwise inequality over `I₋`
  have hptae : ff ≤ᵐ[MeasureTheory.volume.restrict I] gg :=
    (ae_restrict_iff' hImeas).2 (Filter.Eventually.of_forall fun u hu => hpt u hu)
  have hmono : ∫ u in I, ff u ≤ ∫ u in I, gg u :=
    integral_mono_of_nonneg hffnn hggOn hptae
  -- (5) identify the two integrals
  have hff_eq : ∫ u in I, ff u = c₁ * RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ) := by
    show ∫ u in I, c₁ * (Work.BoseFixB1.w1MassB h MM ℓ dd u * AA u) = _
    rw [integral_const_mul]
    rfl
  have hgg_eq : ∫ u in I, gg u =
      (∫ u in Work.SmallBoxSliding.interiorSet
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
              Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
        + (1 / 2) * μ ^ 2
            * (∫ u in Work.SmallBoxSliding.interiorSet
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                Work.BoseFixB1.w1MassB h
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        + C * (μ ^ 2 * (_root_.BoseGases.a v)
                  * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
                      + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                        * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                  * (∫ u in Work.SmallBoxSliding.interiorSet
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                      Work.SmallBoxSliding.chiMass
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                + μ * (_root_.BoseGases.a v)
                  * (MeasureTheory.volume (Work.SmallBoxSliding.interiorSet
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    have step1 : ∫ u in I, gg u
        = (∫ u in I, Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
          + (∫ u in I, (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h MM ℓ dd u * nB)
          + (∫ u in I, C * (μ ^ 2 * av * G * Work.SmallBoxSliding.chiMass MM ℓ dd u * nB
              + μ * av * nB)) := by
      simp only [gg]
      rw [integral_add h12 h3, integral_add hsbOn h2]
    have e1 : ∫ u in I, (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h MM ℓ dd u * nB
        = ((1 / 2) * μ ^ 2 * (∫ u in I, Work.BoseFixB1.w1MassB h MM ℓ dd u)) * nB := by
      rw [integral_mul_const, integral_const_mul]
    have e2 : ∫ u in I, C * (μ ^ 2 * av * G * Work.SmallBoxSliding.chiMass MM ℓ dd u * nB
          + μ * av * nB)
        = C * ((μ ^ 2 * av * G
              * (∫ u in I, Work.SmallBoxSliding.chiMass MM ℓ dd u)) * nB
            + MeasureTheory.Measure.real MeasureTheory.volume I * (μ * av * nB)) := by
      rw [integral_const_mul, integral_add hXint hYint, integral_mul_const,
        integral_const_mul, setIntegral_const, smul_eq_mul]
    calc ∫ u in I, gg u
        = (∫ u in I, Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
          + (∫ u in I, (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h MM ℓ dd u * nB)
          + (∫ u in I, C * (μ ^ 2 * av * G * Work.SmallBoxSliding.chiMass MM ℓ dd u * nB
              + μ * av * nB)) := step1
      _ = (∫ u in I, Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
          + (((1 / 2) * μ ^ 2 * (∫ u in I, Work.BoseFixB1.w1MassB h MM ℓ dd u)) * nB)
          + (C * ((μ ^ 2 * av * G
                * (∫ u in I, Work.SmallBoxSliding.chiMass MM ℓ dd u)) * nB
              + MeasureTheory.Measure.real MeasureTheory.volume I * (μ * av * nB))) := by
          rw [e1, e2]
      _ = (∫ u in Work.SmallBoxSliding.interiorSet
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
              Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
        + (1 / 2) * μ ^ 2
            * (∫ u in Work.SmallBoxSliding.interiorSet
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                Work.BoseFixB1.w1MassB h
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        + C * (μ ^ 2 * (_root_.BoseGases.a v)
                  * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
                      + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                        * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                  * (∫ u in Work.SmallBoxSliding.interiorSet
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                      Work.SmallBoxSliding.chiMass
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                + μ * (_root_.BoseGases.a v)
                  * (MeasureTheory.volume (Work.SmallBoxSliding.interiorSet
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
          dsimp only [MeasureTheory.Measure.real, I, ℓ, dd, MM, av, KB, G, nB]
          ring_nf
  rw [← hff_eq, ← hgg_eq]
  exact hmono

end Work.BoseFixB1B
