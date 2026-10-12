import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.perBoxMF_cases
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The case-split shape -/

/-- **`PerBoxF` with a case hypothesis on `(μ, u)`**: `PerBoxF`'s body *verbatim*, with the extra
hypothesis `P μ u`.  `PerBoxF` itself is the instance `P := fun _ _ => True` (`PerBoxFAll`). -/
def PerBoxFCase (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ)
    (P : ℝ → EuclideanSpace ℝ (Fin 3) → Prop) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        P μ u →
        c₁ * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u *
            (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
              psiWeight 1 μ (nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u x /
                chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)))
          - (1 / 2) * μ ^ 2 * w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
          - C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
              * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u *
              normB v μ n (Φ : X n → ℝ)
            + μ * (a v) * normB v μ n (Φ : X n → ℝ))
        ≤ sbWord h μ u (Φ : X n → ℝ)

/-- The **unconditional** instance: this is the conclusion of `Work.BoseFixB1.perBoxFWeight_holds`
(`perBoxFWeight_holds_of_all` below converts between the two shapes). -/
abbrev PerBoxFAll (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  PerBoxFCase v h R (fun _ _ => True)

/-- The **thin** (degenerate) case of `PerBoxF`. -/
abbrev PerBoxF_thin (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  PerBoxFCase v h R (fun μ u => IsThinBox v h μ u)

/-- The **thick** case: the residual obligation of the a-priori chapter. -/
abbrev PerBoxF_thick (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  PerBoxFCase v h R (fun μ u => ¬ IsThinBox v h μ u)

/-- The **zero-fibre** case of `PerBoxF` (proved, with `c₁ = 1/4`, `C = 0`). -/
abbrev PerBoxF_zeroFibre (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) :
    Prop :=
  PerBoxFCase v h R (fun μ u => IsZeroFibreBox v h μ u)

/-- The **positive-fibre** case of `PerBoxF` — the sharpest available peel. -/
abbrev PerBoxF_posFibre (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) :
    Prop :=
  PerBoxFCase v h R (fun μ u => ¬ IsZeroFibreBox v h μ u)

/-! ## 2. The `∃`-shape of `perBoxFWeight_holds` -/

/-- **`PerBoxFAll` is exactly the conclusion of `perBoxFWeight_holds`** (the two `∃`-bodies
coincide definitionally). -/
theorem perBoxFWeight_holds_of_all {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hA : PerBoxFAll v h R) :
    ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          PerBoxF v h R c₁ C μ n Φ u := by
  obtain ⟨ε₀, c₁, C, hε, hc, hC, H⟩ := hA
  exact ⟨ε₀, c₁, C, hε, hc, hC, fun μ hAdm n Φ u hu => H μ hAdm n Φ u hu trivial⟩

/-! ## 3. The degenerate cases -/

/-- The `F`-weight is nonnegative at density `t ≥ 0`, `μ > 0`. -/
theorem perBoxFCase_psiWeight_nonneg {c μ t : ℝ} (hc : 0 ≤ c) (hμ : 0 < μ) (ht : 0 ≤ t) :
    0 ≤ psiWeight c μ t := by
  rw [Work.SmallBoxSliding.psiWeight]
  refine div_nonneg (mul_nonneg hc (sq_nonneg _)) ?_
  have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ))
  linarith

/-- **The zero-fibre case of `PerBoxF` holds**, with `c₁ = 1/4` and `C = 0`.  On such a box the
one-body mass `W` vanishes (the fibre is an integral of a sum of vanishing slot functions), so the
`F`-term and the `−½μ²W‖Φ‖²` background both vanish and the left side is `0`; the right side is
`sbKin + ∫Φ²·(pair term) ≥ 0`.  Formally this is `perBoxMF_of_fibre_zero` (the *square* form, which
is stronger) transported by the proved `perBoxF_of_perBoxMF_at` (`F(t) ≤ (t−μ)²`). -/
theorem perBoxF_zeroFibre_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    PerBoxF_zeroFibre v h R := by
  refine ⟨1, 1 / 4, 0, one_pos, by norm_num, le_refl 0,
    fun μ hAdm n Φ u hu hfib => ?_⟩
  have hμ : 0 < μ := adm_mu_pos hAdm
  have hM1 : 1 ≤ (paramsAt μ (a v)).M := by
    rw [M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hℓ0 : 0 < sideAt μ (a v) := adm_ell_pos hAdm
  have hpair_nn : ∀ x y : EuclideanSpace ℝ (Fin 3),
      0 ≤ Submission.BoseGases.wSmallPair (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u v x y := fun x y =>
    perBoxMFCase_wSmallPair_nonneg (M := (paramsAt μ (a v)).M) (ℓ := sideAt μ (a v))
      (d := (paramsAt μ (a v)).d) (u := u) (x := x) (y := y) hv
  have hkin : 0 ≤ sbKin (v := v) μ (paramsAt μ (a v)).M u Φ := by
    rw [sbKin]
    exact Work.UBBInputs9.A.tBwordBInd_nonneg hℓ0 (adm_eT_bounds hAdm).1 u (Φ : X n → ℝ)
  have hdeg : ∀ x : EuclideanSpace ℝ (Fin 3),
      (∫ y in Submission.BoseGases.acube (sideAt μ (a v)),
        Submission.BoseGases.wSmall1Pair h (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u x y) = 0 := fun x => hfib x
  -- the square-form inequality with `c₁ = 1/4`, `C = 0`
  have hsq := perBoxMF_of_fibre_zero h hμ u (Φ : X n → ℝ) hM1 hℓ0 hdeg hpair_nn hkin
  have hsq' : (1 / 4) * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
          ((nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
              chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) - μ) ^ 2))
      - (1 / 2) * μ ^ 2 * w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
      - 0 * perBoxErr v μ R n Φ u
      ≤ sbWord h μ u (Φ : X n → ℝ) := by
    simpa using hsq
  exact perBoxF_of_perBoxMF_at h hv hvrad hR hv_supp hAdm Φ hsq'

/-- **The thin case of `PerBoxF` holds** with `c₁ = 1/4`, `C = 0`. -/
theorem perBoxF_thin_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    PerBoxF_thin v h R := by
  obtain ⟨ε₀, c₁, C, hε, hc, hC, H⟩ := perBoxF_zeroFibre_holds (v := v) (h := h)
    (R := R) hv hvrad hR hv_supp
  exact ⟨ε₀, c₁, C, hε, hc, hC, fun μ hAdm n Φ u hu hthin =>
    H μ hAdm n Φ u hu (isZeroFibreBox_of_thin hthin)⟩

/-! ## 4. The case split: `PerBoxF` from its thin and thick cases -/

/-- **`PerBoxF` follows from its thin and thick cases.**  The thresholds are combined by
`min`/`max`; the coefficient by `min`, since `F ≥ 0` and `W ≥ 0` make the left side monotone in
`c₁`. -/
theorem perBoxF_of_thin_thick {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hthin : PerBoxF_thin v h R) (hthick : PerBoxF_thick v h R) : PerBoxFAll v h R := by
  obtain ⟨ε₁, c₁, C₁, hε₁, hc₁, hC₁, H₁⟩ := hthin
  obtain ⟨ε₂, c₂, C₂, hε₂, hc₂, hC₂, H₂⟩ := hthick
  refine ⟨min ε₁ ε₂, min c₁ c₂, max C₁ C₂, lt_min hε₁ hε₂, lt_min hc₁ hc₂,
    le_max_of_le_left hC₁, fun μ hAdm n Φ u hu _hP => ?_⟩
  have h₁ : Work.BoseBoxFix.Adm v ε₁ μ := Adm.mono (ε₀' := min ε₁ ε₂) (ε₀ := ε₁) hAdm
    (min_le_left _ _)
  have h₂ : Work.BoseBoxFix.Adm v ε₂ μ := Adm.mono (ε₀' := min ε₁ ε₂) (ε₀ := ε₂) hAdm
    (min_le_right _ _)
  have hμ : 0 < μ := adm_mu_pos h₁
  have hℓ : 0 < sideAt μ (a v) := adm_ell_pos h₁
  have hd : 0 < (paramsAt μ (a v)).d := adm_d_pos h₁
  -- the `F`-weight is nonnegative, and `W ≥ 0`
  have hΦnn : 0 ≤ ∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
      psiWeight 1 μ (nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u x /
        chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _)
      (perBoxFCase_psiWeight_nonneg (by norm_num) hμ
        (div_nonneg (perBoxMFCase_nCountB_nonneg x) (perBoxMFCase_chiMass_nonneg _ _ _ _)))
  have hW : 0 ≤ w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u :=
    w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  have hstep : min c₁ c₂ * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
          psiWeight 1 μ (nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u x /
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)))
      ≤ c₁ * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
          psiWeight 1 μ (nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u x /
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u))) :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (mul_nonneg hW hΦnn)
  have hstep₂ : min c₁ c₂ * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
          psiWeight 1 μ (nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u x /
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)))
      ≤ c₂ * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
          psiWeight 1 μ (nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u x /
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u))) :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (mul_nonneg hW hΦnn)
  have herr : 0 ≤ μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
        + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
      * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
      * normB v μ n (Φ : X n → ℝ) + μ * (a v) * normB v μ n (Φ : X n → ℝ) := by
    have ha : 0 ≤ a v := le_of_lt (adm_a_pos h₁)
    have hKB : 0 ≤ (paramsAt μ (a v)).KB := le_of_lt (paramsAt_KB_pos h₁)
    have hnb : 0 ≤ normB v μ n (Φ : X n → ℝ) := by
      rw [normB, Work.BoseKinLoc.sqNormB]
      exact integral_nonneg fun x => sq_nonneg _
    have hS : 0 ≤ (R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
        + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) :=
      add_nonneg (sq_nonneg _)
        (mul_nonneg (pow_nonneg hKB 3)
          (Real.rpow_nonneg (mul_nonneg (le_of_lt hμ) (pow_nonneg ha 3)) _))
    have hprod : 0 ≤ μ ^ 2 * (a v)
        * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
        * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        * normB v μ n (Φ : X n → ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha) hS)
        (perBoxMFCase_chiMass_nonneg _ _ _ _)) hnb
    have hlin : 0 ≤ μ * (a v) * normB v μ n (Φ : X n → ℝ) :=
      mul_nonneg (mul_nonneg (le_of_lt hμ) ha) hnb
    linarith [hprod, hlin]
  by_cases hthinμ : IsThinBox v h μ u
  · have key := H₁ μ h₁ n Φ u hu hthinμ
    unfold PerBoxF at key
    have hC : C₁ * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
        * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        * normB v μ n (Φ : X n → ℝ)
      + μ * (a v) * normB v μ n (Φ : X n → ℝ))
        ≤ max C₁ C₂ * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
        * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        * normB v μ n (Φ : X n → ℝ)
      + μ * (a v) * normB v μ n (Φ : X n → ℝ)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) herr
    linarith [key, hstep, hC]
  · have key := H₂ μ h₂ n Φ u hu hthinμ
    unfold PerBoxF at key
    have hC : C₂ * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
        * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        * normB v μ n (Φ : X n → ℝ)
      + μ * (a v) * normB v μ n (Φ : X n → ℝ))
        ≤ max C₁ C₂ * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
        * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        * normB v μ n (Φ : X n → ℝ)
      + μ * (a v) * normB v μ n (Φ : X n → ℝ)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) herr
    linarith [key, hstep₂, hC]

/-- **`PerBoxF` follows from its thick case** — the residual obligation of the a-priori chapter. -/
theorem perBoxF_of_thick {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hthick : PerBoxF_thick v h R) : PerBoxFAll v h R :=
  perBoxF_of_thin_thick hv hvrad hR hv_supp (perBoxF_thin_holds hv hvrad hR hv_supp) hthick

/-- **`perBoxFWeight_holds`'s conclusion from the thick case**: the exact `∃`-shape of the
chapter's crux, with the degenerate boxes discharged. -/
theorem perBoxFWeight_holds_of_thick {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hthick : PerBoxF_thick v h R) :
    ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          PerBoxF v h R c₁ C μ n Φ u :=
  perBoxFWeight_holds_of_all (perBoxF_of_thick hv hvrad hR hv_supp hthick)

end Work.BoseFixB1
