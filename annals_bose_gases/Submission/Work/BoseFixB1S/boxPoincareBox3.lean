import Mathlib
import Submission.Work.BoseFixB1P.BoxScale
import Submission.Work.SmallBoxA0.boxNeumann3_deriv_parseval
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory Filter
open scoped BigOperators

set_option maxHeartbeats 800000

/-- **Sharp mean-free Poincaré inequality on the centred cube `acube a`.**

For `u` of class `C^∞` on `acube a = [-a/2, a/2]³` with vanishing mean,
`(π²/a²) ∫ u² ≤ ∑_k ∫ (∂_k u)²`.  The proof is the Neumann (cosine) box-Parseval
comparison: expand `u` and each `∂_k u` in the product cosine basis of `acube a`
(`Work.SmallBoxA0.acube_parseval_mixed` with the mixed modes, and the
integration-by-parts coefficient identity `Work.SmallBoxA0.acube_mode_deriv_ibp_sine`),
then compare termwise: for a multi-index `k ≠ 0` the Neumann eigenvalue
`λ_k = ∑_m (π k_m/a)²` is `≥ π²/a²`, and the `k = 0` term vanishes by the mean-free
hypothesis. -/
theorem acube_poincare {a : ℝ} (ha : 0 < a) {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hu : ContDiff ℝ (⊤ : ENat) u)
    (hmean : (∫ x in Submission.BoseGases.acube a, u x) = 0) :
    Real.pi ^ 2 / a ^ 2 * (∫ x in Submission.BoseGases.acube a, (u x) ^ 2)
      ≤ ∑ k : Fin 3, ∫ x in Submission.BoseGases.acube a,
          (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
  classical
  have hu1 : ContDiff ℝ 1 u :=
    hu.of_le (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤))
  have hu2 : ContDiff ℝ 2 u :=
    hu.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have huc : Continuous u := hu1.continuous
  have hdf : Continuous (fderiv ℝ u) := hu2.continuous_fderiv (by norm_num)
  have hcont : ∀ m : Fin 3, Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
      fderiv ℝ u x (Submission.BoseGases.kcStdBasis m)) :=
    fun m => hdf.clm_apply continuous_const
  set c : (Fin 3 → ℕ) → ℝ := fun k =>
    ∫ x in Submission.BoseGases.acube a, u x * Submission.BoseGases.boxNeumann3 a k x with hc
  set W : (Fin 3 → ℕ) → ℝ := fun k =>
    ∏ j : Fin 3, Work.SmallBoxA0.mixedWgt a false (k j) with hW
  have hWpos : ∀ k : Fin 3 → ℕ, 0 < W k := fun k => by
    rw [hW]
    exact Finset.prod_pos (fun j _ => Work.SmallBoxA0.mixedWgt_pos ha false (k j))
  -- the mean-free coefficient series (`HasSum`) for `u²`
  have hbase : HasSum (fun k : Fin 3 → ℕ => (c k) ^ 2 / W k)
      (∫ x in Submission.BoseGases.acube a, (u x) ^ 2) := by
    have h := Work.SmallBoxA0.acube_parseval_mixed (s := a) ha
      (fun _ : Fin 3 => false) (F := u) huc
    refine h.congr_fun (fun k => ?_)
    have hnum : (∫ x in Submission.BoseGases.acube a,
          u x * ∏ i : Fin 3, Work.SmallBoxA0.mixedMode a false (k i) (x i)) = c k := by
      rw [hc]
      apply integral_congr_ae
      filter_upwards with x
      simp [Work.SmallBoxA0.mixedMode, Submission.BoseGases.boxNeumann3,
        Submission.BoseGases.boxNeumann]
    have hwt : (∏ i : Fin 3, Work.SmallBoxA0.mixedWgt a false (k i)) = W k := by rw [hW]
    rw [hnum, hwt]
  -- the coefficient identity via integration by parts against the sine modes
  have hcoeff : ∀ (m : Fin 3) (k : Fin 3 → ℕ),
      (∫ x in Submission.BoseGases.acube a, fderiv ℝ u x (Submission.BoseGases.kcStdBasis m) *
          ∏ i : Fin 3, Work.SmallBoxA0.mixedMode a (decide (i = m)) (k i) (x i))
        = -(((k m : ℝ) * Real.pi / a)) * c k := by
    intro m k
    rw [hc]
    rw [integral_congr_ae (Eventually.of_forall (fun x => by
      rw [Work.SmallBoxA0.prod_mixed_split m k]))]
    exact Work.SmallBoxA0.acube_mode_deriv_ibp_sine ha m k hu2
  set d : Fin 3 → (Fin 3 → ℕ) → ℝ := fun m k =>
    ((k m : ℝ) * Real.pi / a) ^ 2 * ((c k) ^ 2 / W k) with hd
  -- the weight of the mixed family with the sine in slot `m` is `W k` when `k m ≠ 0`
  have hWm : ∀ (m : Fin 3) (k : Fin 3 → ℕ), k m ≠ 0 →
      (∏ i : Fin 3, Work.SmallBoxA0.mixedWgt a (decide (i = m)) (k i)) = W k := by
    intro m k hkm
    rw [hW]
    dsimp only
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i = m
    · rw [hi]
      rw [Work.SmallBoxA0.mixedWgt_eq_half (decide (m = m)) hkm,
        Work.SmallBoxA0.mixedWgt_eq_half false hkm]
    · exact Work.SmallBoxA0.mixedWgt_decide_false (ℓ := a) (p := i = m) hi (k i)
  -- per-direction Parseval for the partial derivatives
  have hsum_m : ∀ m : Fin 3, HasSum (d m)
      (∫ x in Submission.BoseGases.acube a,
        (fderiv ℝ u x (Submission.BoseGases.kcStdBasis m)) ^ 2) := by
    intro m
    have hb := Work.SmallBoxA0.acube_parseval_mixed (s := a) ha
      (fun i : Fin 3 => decide (i = m))
      (F := fun x : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ u x (Submission.BoseGases.kcStdBasis m)) (hcont m)
    refine hb.congr_fun (fun k => ?_)
    simp only [hd]
    rw [hcoeff m k]
    by_cases hkm : k m = 0
    · have hA : ((k m : ℝ) * Real.pi / a) = 0 := by rw [hkm]; simp
      rw [hA]
      simp
    · rw [hWm m k hkm]
      ring
  have hsum : HasSum (fun k : Fin 3 → ℕ => ∑ m : Fin 3, d m k)
      (∑ m : Fin 3, ∫ x in Submission.BoseGases.acube a,
        (fderiv ℝ u x (Submission.BoseGases.kcStdBasis m)) ^ 2) := by
    have hall := (hsum_m 0).add ((hsum_m 1).add (hsum_m 2))
    simpa only [Fin.sum_univ_three, add_assoc] using hall
  -- termwise comparison
  have hle : ∀ k : Fin 3 → ℕ,
      Real.pi ^ 2 / a ^ 2 * ((c k) ^ 2 / W k) ≤ ∑ m : Fin 3, d m k := by
    intro k
    by_cases hk : k = 0
    · have hc0 : c k = 0 := by
        rw [hk, hc]
        dsimp only
        have h1 : (fun x : EuclideanSpace ℝ (Fin 3) =>
              u x * Submission.BoseGases.boxNeumann3 a (0 : Fin 3 → ℕ) x) = fun x => u x := by
          funext x
          have hb0 : Submission.BoseGases.boxNeumann3 a (0 : Fin 3 → ℕ) x = 1 := by
            rw [Submission.BoseGases.boxNeumann3]
            apply Finset.prod_eq_one
            intro j _
            simp only [Pi.zero_apply]
            exact Submission.BoseGases.boxNeumann_zero a (x j)
          rw [hb0, mul_one]
        rw [h1, hmean]
      rw [hc0]
      simp [hd, hc0]
    · obtain ⟨m, hm⟩ : ∃ m : Fin 3, k m ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hk (funext hcon)
      have hm1 : (1 : ℝ) ≤ (k m : ℝ) := by
        have h1 : 1 ≤ k m := Nat.one_le_iff_ne_zero.mpr hm
        exact_mod_cast h1
      have hm2 : (1 : ℝ) ≤ (k m : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((k m : ℝ) - 1)]
      have hcW : 0 ≤ (c k) ^ 2 / W k :=
        div_nonneg (sq_nonneg _) (le_of_lt (hWpos k))
      have hsq : (Real.pi / a) ^ 2 ≤ ((k m : ℝ) * Real.pi / a) ^ 2 := by
        have hsplit : ((k m : ℝ) * Real.pi / a) ^ 2 = (k m : ℝ) ^ 2 * (Real.pi / a) ^ 2 := by
          ring
        rw [hsplit]
        calc (Real.pi / a) ^ 2 = 1 * (Real.pi / a) ^ 2 := by ring
          _ ≤ (k m : ℝ) ^ 2 * (Real.pi / a) ^ 2 :=
              mul_le_mul_of_nonneg_right hm2 (sq_nonneg _)
      calc Real.pi ^ 2 / a ^ 2 * ((c k) ^ 2 / W k)
          = (Real.pi / a) ^ 2 * ((c k) ^ 2 / W k) := by ring
        _ ≤ ((k m : ℝ) * Real.pi / a) ^ 2 * ((c k) ^ 2 / W k) :=
              mul_le_mul_of_nonneg_right hsq hcW
        _ = d m k := by rw [hd]
        _ ≤ ∑ m' : Fin 3, d m' k :=
              Finset.single_le_sum (s := Finset.univ) (f := fun m' : Fin 3 => d m' k)
                (fun i _ => by
                  simp only [hd]
                  exact mul_nonneg (sq_nonneg _) hcW)
                (Finset.mem_univ m)
  have hsumL : HasSum (fun k : Fin 3 → ℕ => Real.pi ^ 2 / a ^ 2 * ((c k) ^ 2 / W k))
      (Real.pi ^ 2 / a ^ 2 * (∫ x in Submission.BoseGases.acube a, (u x) ^ 2)) :=
    hbase.mul_left _
  have hcmp := Summable.tsum_le_tsum hle hsumL.summable hsum.summable
  rw [hsumL.tsum_eq, hsum.tsum_eq] at hcmp
  exact hcmp



/-! ## The diagonal rescaling of a box onto a cube -/

/-- The diagonal matrix as a linear map on the coordinate space `Fin 3 → ℝ`. -/
noncomputable def diagLinF (c : Fin 3 → ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  Matrix.toLin' (Matrix.diagonal c)

lemma diagLinF_apply (c : Fin 3 → ℝ) (z : Fin 3 → ℝ) (j : Fin 3) :
    diagLinF c z j = c j * z j := by
  rw [diagLinF, Matrix.diagonal_toLin']
  simp

lemma diagLinF_det (c : Fin 3 → ℝ) : LinearMap.det (diagLinF c) = ∏ j, c j := by
  rw [diagLinF, LinearMap.det_toLin', Matrix.det_diagonal]

/-- `Work.BoseFixB1P.diagScale` is the conjugate of the diagonal matrix by the
measure-preserving identification `cgEuc3 : (Fin 3 → ℝ) ≃ᵐ ℝ³`. -/
lemma diagScale_eq_comp (c : Fin 3 → ℝ) :
    Work.BoseFixB1P.diagScale c
      = ⇑Submission.BoseGases.cgEuc3 ∘ ⇑(diagLinF c) ∘ ⇑Submission.BoseGases.cgEuc3.symm := by
  funext x
  rw [Function.comp_apply, Function.comp_apply, Work.BoseFixB1P.diagScale, diagLinF,
    Matrix.diagonal_toLin']
  congr 1

lemma measurePreserving_cgEuc3 :
    MeasurePreserving (⇑Submission.BoseGases.cgEuc3) (volume : Measure (Fin 3 → ℝ))
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
  have hfun : ⇑Submission.BoseGases.cgEuc3 = WithLp.toLp 2 := by
    funext z
    simp [Submission.BoseGases.cgEuc3, MeasurableEquiv.coe_toLp]
  rw [hfun]
  exact PiLp.volume_preserving_toLp (Fin 3)

lemma measurePreserving_cgEuc3_symm :
    MeasurePreserving (⇑Submission.BoseGases.cgEuc3.symm)
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) (volume : Measure (Fin 3 → ℝ)) :=
  MeasurePreserving.symm Submission.BoseGases.cgEuc3 measurePreserving_cgEuc3

/-- **The diagonal rescaling of Lebesgue measure**: `diagScale c` multiplies Lebesgue
measure by `∏_j c j`. -/
lemma map_diagScale_volume {c : Fin 3 → ℝ} (hc : ∀ j, 0 < c j) :
    Measure.map (Work.BoseFixB1P.diagScale c) (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      = ENNReal.ofReal ((∏ j, c j)⁻¹) • (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
  have hpos : 0 < ∏ j, c j := Finset.prod_pos (fun j _ => hc j)
  have hne : LinearMap.det (diagLinF c) ≠ 0 := by
    rw [diagLinF_det]; exact ne_of_gt hpos
  have hF := Real.map_linearMap_volume_pi_eq_smul_volume_pi (f := diagLinF c) hne
  rw [diagLinF_det, abs_of_pos (inv_pos.mpr hpos)] at hF
  have hmp1 := measurePreserving_cgEuc3
  have hmp2 := measurePreserving_cgEuc3_symm
  have hD : Measurable (⇑(diagLinF c)) :=
    (diagLinF c).continuous_of_finiteDimensional.measurable
  rw [diagScale_eq_comp]
  rw [← Measure.map_map hmp1.measurable (hD.comp hmp2.measurable)]
  rw [← Measure.map_map hD hmp2.measurable]
  rw [hmp2.map_eq, hF, Measure.map_smul, hmp1.map_eq]
  all_goals first | fun_prop | measurability

lemma contDiff_toLp : ContDiff ℝ (⊤ : ENat)
    (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) := by
  rw [show (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3))
      = ⇑(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm from by
        funext z
        rw [PiLp.continuousLinearEquiv_symm_apply]]
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff

lemma contDiff_ofLp : ContDiff ℝ (⊤ : ENat)
    (fun x : EuclideanSpace ℝ (Fin 3) => x.ofLp) := by
  rw [show (fun x : EuclideanSpace ℝ (Fin 3) => x.ofLp)
      = ⇑(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)) from by
        funext z
        rfl]
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff

lemma contDiff_cgEuc3 : ContDiff ℝ (⊤ : ENat) (⇑Submission.BoseGases.cgEuc3) := by
  rw [show ⇑Submission.BoseGases.cgEuc3 = WithLp.toLp 2 from by
    funext z
    simp [Submission.BoseGases.cgEuc3, MeasurableEquiv.coe_toLp]]
  exact contDiff_toLp

lemma contDiff_cgEuc3_symm :
    ContDiff ℝ (⊤ : ENat) (⇑Submission.BoseGases.cgEuc3.symm) := by
  rw [show ⇑Submission.BoseGases.cgEuc3.symm
      = fun x : EuclideanSpace ℝ (Fin 3) => x.ofLp from by
    funext z
    simp [Submission.BoseGases.cgEuc3, MeasurableEquiv.coe_toLp]]
  exact contDiff_ofLp

lemma contDiff_diagScale (c : Fin 3 → ℝ) :
    ContDiff ℝ (⊤ : ENat) (Work.BoseFixB1P.diagScale c) := by
  rw [diagScale_eq_comp]
  exact contDiff_cgEuc3.comp
    (((diagLinF c).toContinuousLinearMap.contDiff).comp contDiff_cgEuc3_symm)

lemma measurable_diagScale (c : Fin 3 → ℝ) : Measurable (Work.BoseFixB1P.diagScale c) :=
  (contDiff_diagScale c).continuous.measurable

/-- The translation vector of `boxScale a p q` (its value at the cube centre `0`). -/
noncomputable def boxShift (a : ℝ) (p q : Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 3) :=
  Submission.BoseGases.cgEuc3 (fun j => p j + (a / 2) * ((q j - p j) / a))

lemma boxScale_eq_diagScale_addT {a : ℝ} (p q : Fin 3 → ℝ) :
    Work.BoseFixB1P.boxScale a p q
      = fun y : EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixB1P.diagScale (fun j => (q j - p j) / a) y + boxShift a p q := by
  funext y
  rw [Work.BoseFixB1P.boxScale_eq_diagScale_add]
  rfl

lemma contDiff_boxScale {a : ℝ} (p q : Fin 3 → ℝ) :
    ContDiff ℝ (⊤ : ENat) (Work.BoseFixB1P.boxScale a p q) := by
  rw [boxScale_eq_diagScale_addT]
  exact (contDiff_diagScale (fun j => (q j - p j) / a)).add contDiff_const

lemma map_boxScale_volume {a : ℝ} (ha : 0 < a) {p q : Fin 3 → ℝ}
    (hpos : ∀ j, 0 < q j - p j) :
    Measure.map (Work.BoseFixB1P.boxScale a p q) (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      = ENNReal.ofReal ((∏ j, (q j - p j) / a)⁻¹) •
          (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
  set t := boxShift a p q with ht
  set d : Fin 3 → ℝ := fun j => (q j - p j) / a with hd
  have hmt : Measurable (fun y : EuclideanSpace ℝ (Fin 3) => y + t) :=
    measurable_id.add_const t
  rw [boxScale_eq_diagScale_addT]
  rw [show (fun y : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB1P.diagScale d y + t)
      = (fun y : EuclideanSpace ℝ (Fin 3) => y + t) ∘ Work.BoseFixB1P.diagScale d from rfl]
  rw [← Measure.map_map hmt (measurable_diagScale d)]
  rw [map_diagScale_volume (fun j => div_pos (hpos j) ha)]
  rw [Measure.map_smul]
  rw [(measurePreserving_add_right (volume : Measure (EuclideanSpace ℝ (Fin 3))) t).map_eq]
  all_goals first | fun_prop | measurability

lemma measurable_boxScale {a : ℝ} (p q : Fin 3 → ℝ) :
    Measurable (Work.BoseFixB1P.boxScale a p q) :=
  (contDiff_boxScale p q).continuous.measurable

/-- **The affine change of variables**: pulling a continuous `G` back from the box `Box3 p q`
to the centred cube `acube a` along the diagonal affine map `boxScale a p q`. -/
theorem boxScale_setIntegral {a : ℝ} (ha : 0 < a) (p q : Fin 3 → ℝ)
    (hpos : ∀ j : Fin 3, 0 < q j - p j) {G : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hG : Continuous G) :
    (∫ y in Submission.BoseGases.acube a, G (Work.BoseFixB1P.boxScale a p q y))
      = (∏ j : Fin 3, (q j - p j) / a)⁻¹ * (∫ x in Work.BoseFixB1P.Box3 p q, G x) := by
  set d : Fin 3 → ℝ := fun j => (q j - p j) / a with hd
  have hdpos : ∀ j, 0 < d j := fun j => div_pos (hpos j) ha
  have hprod : 0 < ∏ j, d j := Finset.prod_pos (fun j _ => hdpos j)
  have hmem : ∀ y : EuclideanSpace ℝ (Fin 3),
      y ∈ Submission.BoseGases.acube a ↔
        Work.BoseFixB1P.boxScale a p q y ∈ Work.BoseFixB1P.Box3 p q := by
    intro y
    simp only [Submission.BoseGases.mem_acube_iff, Work.BoseFixB1P.mem_Box3, Set.mem_Icc]
    constructor
    · intro h j
      have hj := h j
      have hdj : 0 < (q j - p j) / a := hdpos j
      rw [Work.BoseFixB1P.boxScale_apply]
      constructor
      · nlinarith [mul_nonneg (by linarith [hj.1] : (0 : ℝ) ≤ y.ofLp j + a / 2) (le_of_lt hdj),
          hj.1]
      · have h1 : y.ofLp j + a / 2 ≤ a := by linarith [hj.2]
        have h2 : (y.ofLp j + a / 2) * ((q j - p j) / a) ≤ a * ((q j - p j) / a) :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt hdj)
        have h3 : a * ((q j - p j) / a) = q j - p j := by field_simp
        linarith
    · intro h j
      have hj := h j
      have hdj : 0 < (q j - p j) / a := hdpos j
      rw [Work.BoseFixB1P.boxScale_apply] at hj
      constructor
      · have h1 : 0 ≤ (y.ofLp j + a / 2) * ((q j - p j) / a) := by linarith [hj.1]
        have h2 : 0 ≤ y.ofLp j + a / 2 :=
          nonneg_of_mul_nonneg_right (by simpa [mul_comm] using h1) hdj
        linarith
      · have h1 : (y.ofLp j + a / 2) * ((q j - p j) / a) ≤ q j - p j := by linarith [hj.2]
        have h2 : y.ofLp j + a / 2 ≤ a := by
          by_contra hc
          push Not at hc
          have h3 : a * ((q j - p j) / a) < (y.ofLp j + a / 2) * ((q j - p j) / a) :=
            mul_lt_mul_of_pos_right hc hdj
          rw [mul_div_cancel₀ _ (ne_of_gt ha)] at h3
          linarith
        linarith
  have hkey : ∀ F : EuclideanSpace ℝ (Fin 3) → ℝ,
      AEStronglyMeasurable F (Measure.map (Work.BoseFixB1P.boxScale a p q)
        (volume : Measure (EuclideanSpace ℝ (Fin 3)))) →
      (∫ y, F (Work.BoseFixB1P.boxScale a p q y)) = (∏ j, d j)⁻¹ * (∫ x, F x) := by
    intro F hF
    have h1 : (∫ x, F x ∂(Measure.map (Work.BoseFixB1P.boxScale a p q)
          (volume : Measure (EuclideanSpace ℝ (Fin 3)))))
        = ∫ y, F (Work.BoseFixB1P.boxScale a p q y) :=
      integral_map (measurable_boxScale p q).aemeasurable hF
    rw [map_boxScale_volume ha hpos] at h1
    rw [MeasureTheory.integral_smul_measure] at h1
    rw [ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr hprod))] at h1
    exact h1.symm
  have hmeas : AEStronglyMeasurable
      ((Work.BoseFixB1P.Box3 p q).indicator G)
      (Measure.map (Work.BoseFixB1P.boxScale a p q)
        (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :=
    (hG.measurable.aestronglyMeasurable).indicator (Work.BoseFixB1P.measurableSet_Box3 p q)
  have hmain := hkey ((Work.BoseFixB1P.Box3 p q).indicator G) hmeas
  have hL : (∫ y in Submission.BoseGases.acube a, G (Work.BoseFixB1P.boxScale a p q y))
      = ∫ y, (Work.BoseFixB1P.Box3 p q).indicator G (Work.BoseFixB1P.boxScale a p q y) := by
    rw [← integral_indicator (Submission.BoseGases.acube_measurable a)]
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : y ∈ Submission.BoseGases.acube a
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem ((hmem y).mp hy) G]
    · rw [Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (fun h => hy ((hmem y).mpr h)) G]
  have hR : (∫ x in Work.BoseFixB1P.Box3 p q, G x)
      = ∫ x, (Work.BoseFixB1P.Box3 p q).indicator G x := by
    rw [← integral_indicator (Work.BoseFixB1P.measurableSet_Box3 p q)]
  rw [hL, hR, hmain]

/-- **The chain rule for `boxScale`**: the `k`-th directional derivative of `u ∘ boxScale`
is `((q k - p k)/a)` times the corresponding derivative of `u` at the image point. -/
theorem boxScale_fderiv {a : ℝ} (p q : Fin 3 → ℝ)
    {u : EuclideanSpace ℝ (Fin 3) → ℝ} (hu : ContDiff ℝ (⊤ : ENat) u)
    (y : EuclideanSpace ℝ (Fin 3)) (k : Fin 3) :
    fderiv ℝ (fun y => u (Work.BoseFixB1P.boxScale a p q y)) y
        (Submission.BoseGases.kcStdBasis k)
      = ((q k - p k) / a) *
        fderiv ℝ u (Work.BoseFixB1P.boxScale a p q y)
          (Submission.BoseGases.kcStdBasis k) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤))
  have hdiffu : DifferentiableAt ℝ u (Work.BoseFixB1P.boxScale a p q y) :=
    (hu1.differentiable (by norm_num)).differentiableAt
  have hdiffT : DifferentiableAt ℝ (Work.BoseFixB1P.boxScale a p q) y :=
    ((contDiff_boxScale p q).differentiable (by simp)).differentiableAt
  have hdiff : DifferentiableAt ℝ (fun y => u (Work.BoseFixB1P.boxScale a p q y)) y :=
    hdiffu.comp y hdiffT
  rw [← hdiff.lineDeriv_eq_fderiv, ← hdiffu.lineDeriv_eq_fderiv]
  dsimp only [lineDeriv]
  have hT : ∀ t : ℝ,
      Work.BoseFixB1P.boxScale a p q (y + t • Submission.BoseGases.kcStdBasis k)
        = Work.BoseFixB1P.boxScale a p q y
          + (t * ((q k - p k) / a)) • Submission.BoseGases.kcStdBasis k := by
    intro t
    ext j
    simp only [PiLp.add_apply, PiLp.smul_apply, Work.BoseFixB1P.boxScale_apply, smul_eq_mul,
      Submission.BoseGases.kcStdBasis, EuclideanSpace.single_apply]
    by_cases hj : j = k
    · subst hj; ring
    · simp [hj]
  rw [show (fun t : ℝ =>
        u (Work.BoseFixB1P.boxScale a p q (y + t • Submission.BoseGases.kcStdBasis k)))
      = (fun t : ℝ => u (Work.BoseFixB1P.boxScale a p q y
          + (t * ((q k - p k) / a)) • Submission.BoseGases.kcStdBasis k)) from by
        funext t
        rw [hT t]]
  rw [show (fun t : ℝ => u (Work.BoseFixB1P.boxScale a p q y
          + (t * ((q k - p k) / a)) • Submission.BoseGases.kcStdBasis k))
      = (fun t : ℝ => (fun s : ℝ => u (Work.BoseFixB1P.boxScale a p q y
          + s • Submission.BoseGases.kcStdBasis k)) (((q k - p k) / a) * t)) from by
        funext t
        rw [mul_comm]]
  rw [deriv_comp_mul_left ((q k - p k) / a)
    (fun s : ℝ => u (Work.BoseFixB1P.boxScale a p q y
      + s • Submission.BoseGases.kcStdBasis k)) 0]
  simp only [mul_zero]
  rw [show deriv (fun t : ℝ => u (Work.BoseFixB1P.boxScale a p q y
        + t • Submission.BoseGases.kcStdBasis k)) 0
      = fderiv ℝ u (Work.BoseFixB1P.boxScale a p q y)
          (Submission.BoseGases.kcStdBasis k) from hdiffu.lineDeriv_eq_fderiv]
  simp [smul_eq_mul]

/-- **A coordinate hyperplane is Lebesgue-null.** -/
lemma volume_coord_eq (j : Fin 3) (c : ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      {y : EuclideanSpace ℝ (Fin 3) | y j = c} = 0 := by
  classical
  set L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ := EuclideanSpace.projₗ (𝕜 := ℝ) j with hL
  have hLapply : ∀ y : EuclideanSpace ℝ (Fin 3), L y = y j := fun y => by
    rw [hL, PiLp.projₗ_apply]
  have hker : LinearMap.ker L ≠ ⊤ := by
    intro htop
    have hmem : EuclideanSpace.single j (1 : ℝ) ∈ LinearMap.ker L := by
      rw [htop]; trivial
    rw [LinearMap.mem_ker, hLapply] at hmem
    simpa using hmem
  have hzero : (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      ((LinearMap.ker L : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) :
        Set (EuclideanSpace ℝ (Fin 3))) = 0 :=
    Measure.addHaar_submodule (volume : Measure (EuclideanSpace ℝ (Fin 3))) _ hker
  have hpre : {y : EuclideanSpace ℝ (Fin 3) | y j = c}
      = (fun y : EuclideanSpace ℝ (Fin 3) =>
          y + (-(c • EuclideanSpace.single j (1 : ℝ)))) ⁻¹'
          {y : EuclideanSpace ℝ (Fin 3) | y ∈ LinearMap.ker L} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, LinearMap.mem_ker, hLapply, PiLp.add_apply,
      PiLp.neg_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, reduceIte, mul_one]
    constructor
    · intro hx
      rw [hx]; ring
    · intro hx
      linarith [hx]
  rw [hpre, measure_preimage_add_right]
  have hset : {y : EuclideanSpace ℝ (Fin 3) | y ∈ LinearMap.ker L}
      = ((LinearMap.ker L : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) :
          Set (EuclideanSpace ℝ (Fin 3))) := rfl
  rw [hset, hzero]

/-- A box with a non-positive side is Lebesgue-null. -/
lemma volume_Box3_eq_zero_of_nonpos {p q : Fin 3 → ℝ} (j : Fin 3) (h : q j - p j ≤ 0) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) (Work.BoseFixB1P.Box3 p q) = 0 := by
  refine measure_mono_null ?_ (volume_coord_eq j (p j))
  intro x hx
  simp only [Set.mem_setOf_eq]
  have hx' := (Work.BoseFixB1P.mem_Box3.mp hx) j
  simp only [Set.mem_Icc] at hx'
  exact le_antisymm (le_trans hx'.2 (by linarith)) hx'.1

theorem boxPoincareBox3 {a : ℝ} (ha : 0 < a) (p q : Fin 3 → ℝ)
    (hpq : ∀ j : Fin 3, q j - p j ≤ a) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiff ℝ (⊤ : ENat) u)
    (hmean : (∫ x in Work.BoseFixB1P.Box3 p q, u x) = 0) :
    Real.pi ^ 2 / a ^ 2 * (∫ x in Work.BoseFixB1P.Box3 p q, (u x) ^ 2)
      ≤ ∑ k : Fin 3, ∫ x in Work.BoseFixB1P.Box3 p q,
          (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
  by
  classical
  have hu1 : ContDiff ℝ 1 u := hu.of_le (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤))
  have hdf : Continuous (fderiv ℝ u) := hu1.continuous_fderiv (by norm_num)
  have hdirc : ∀ k : Fin 3, Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
      fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) :=
    fun k => hdf.clm_apply continuous_const
  by_cases hdeg : ∃ j : Fin 3, q j - p j ≤ 0
  · obtain ⟨j, hj⟩ := hdeg
    have hnull := volume_Box3_eq_zero_of_nonpos j hj
    have h1 : (∫ x in Work.BoseFixB1P.Box3 p q, (u x) ^ 2) = 0 :=
      MeasureTheory.setIntegral_measure_zero _ hnull
    have h2 : (∑ k : Fin 3, ∫ x in Work.BoseFixB1P.Box3 p q,
        (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      exact MeasureTheory.setIntegral_measure_zero _ hnull
    rw [h1, h2]
    simp
  · push Not at hdeg
    have hdpos : ∀ j : Fin 3, 0 < (q j - p j) / a := fun j => div_pos (hdeg j) ha
    have hdle : ∀ j : Fin 3, (q j - p j) / a ≤ 1 := by
      intro j
      rw [div_le_one ha]
      exact hpq j
    have hprod : 0 < ∏ j : Fin 3, (q j - p j) / a := Finset.prod_pos (fun j _ => hdpos j)
    set v : EuclideanSpace ℝ (Fin 3) → ℝ :=
      fun y => u (Work.BoseFixB1P.boxScale a p q y) with hv
    have hvcd : ContDiff ℝ (⊤ : ENat) v := hu.comp (contDiff_boxScale p q)
    have hvmean : (∫ y in Submission.BoseGases.acube a, v y) = 0 := by
      rw [hv]
      dsimp only
      rw [boxScale_setIntegral ha p q hdeg (hG := hu1.continuous), hmean, mul_zero]
    have hcube := acube_poincare ha hvcd hvmean
    have hL : (∫ y in Submission.BoseGases.acube a, (v y) ^ 2)
        = (∏ j : Fin 3, (q j - p j) / a)⁻¹ *
          (∫ x in Work.BoseFixB1P.Box3 p q, (u x) ^ 2) := by
      rw [hv]
      dsimp only
      exact boxScale_setIntegral ha p q hdeg (G := fun x => (u x) ^ 2)
        (hG := hu1.continuous.pow 2)
    have hR : ∀ k : Fin 3, (∫ y in Submission.BoseGases.acube a,
          (fderiv ℝ v y (Submission.BoseGases.kcStdBasis k)) ^ 2)
        = (∏ j : Fin 3, (q j - p j) / a)⁻¹ * (((q k - p k) / a) ^ 2 *
            (∫ x in Work.BoseFixB1P.Box3 p q,
              (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2)) := by
      intro k
      have h1 : (∫ y in Submission.BoseGases.acube a,
            (fderiv ℝ v y (Submission.BoseGases.kcStdBasis k)) ^ 2)
          = ∫ y in Submission.BoseGases.acube a,
              (fun x : EuclideanSpace ℝ (Fin 3) => ((q k - p k) / a) ^ 2 *
                (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2)
                (Work.BoseFixB1P.boxScale a p q y) := by
        apply setIntegral_congr_fun (Submission.BoseGases.acube_measurable a)
        intro y hy
        rw [hv]
        dsimp only
        rw [boxScale_fderiv p q hu y k]
        ring
      rw [h1]
      rw [boxScale_setIntegral ha p q hdeg
        (G := fun x : EuclideanSpace ℝ (Fin 3) => ((q k - p k) / a) ^ 2 *
          (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2)
        (hG := continuous_const.mul ((hdirc k).pow 2))]
      rw [MeasureTheory.integral_const_mul]
    have hsum_eq : (∑ k : Fin 3, ∫ y in Submission.BoseGases.acube a,
          (fderiv ℝ v y (Submission.BoseGases.kcStdBasis k)) ^ 2)
        = ∑ k : Fin 3, (∏ j : Fin 3, (q j - p j) / a)⁻¹ * (((q k - p k) / a) ^ 2 *
            (∫ x in Work.BoseFixB1P.Box3 p q,
              (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2)) :=
      Finset.sum_congr rfl (fun k _ => hR k)
    rw [hL, hsum_eq] at hcube
    have hfac : (∏ j : Fin 3, (q j - p j) / a)⁻¹ * (Real.pi ^ 2 / a ^ 2 *
          (∫ x in Work.BoseFixB1P.Box3 p q, (u x) ^ 2))
        ≤ (∏ j : Fin 3, (q j - p j) / a)⁻¹ *
          (∑ k : Fin 3, ((q k - p k) / a) ^ 2 *
            (∫ x in Work.BoseFixB1P.Box3 p q,
              (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2)) := by
      have h2 : Real.pi ^ 2 / a ^ 2 * ((∏ j : Fin 3, (q j - p j) / a)⁻¹ *
            (∫ x in Work.BoseFixB1P.Box3 p q, (u x) ^ 2))
          = (∏ j : Fin 3, (q j - p j) / a)⁻¹ * (Real.pi ^ 2 / a ^ 2 *
            (∫ x in Work.BoseFixB1P.Box3 p q, (u x) ^ 2)) := by ring
      have h3 : (∑ k : Fin 3, (∏ j : Fin 3, (q j - p j) / a)⁻¹ *
            (((q k - p k) / a) ^ 2 *
              (∫ x in Work.BoseFixB1P.Box3 p q,
                (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2)))
          = (∏ j : Fin 3, (q j - p j) / a)⁻¹ *
            (∑ k : Fin 3, ((q k - p k) / a) ^ 2 *
              (∫ x in Work.BoseFixB1P.Box3 p q,
                (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2)) := by
        rw [Finset.mul_sum]
      rw [h2, h3] at hcube
      exact hcube
    have hone : Real.pi ^ 2 / a ^ 2 * (∫ x in Work.BoseFixB1P.Box3 p q, (u x) ^ 2)
        ≤ ∑ k : Fin 3, ((q k - p k) / a) ^ 2 *
            (∫ x in Work.BoseFixB1P.Box3 p q,
              (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2) :=
      le_of_mul_le_mul_left hfac (inv_pos.mpr hprod)
    calc Real.pi ^ 2 / a ^ 2 * (∫ x in Work.BoseFixB1P.Box3 p q, (u x) ^ 2)
        ≤ ∑ k : Fin 3, ((q k - p k) / a) ^ 2 *
            (∫ x in Work.BoseFixB1P.Box3 p q,
              (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2) := hone
      _ ≤ ∑ k : Fin 3, ∫ x in Work.BoseFixB1P.Box3 p q,
            (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
          Finset.sum_le_sum (fun k _ => by
            have hJ : 0 ≤ ∫ x in Work.BoseFixB1P.Box3 p q,
                (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
              MeasureTheory.setIntegral_nonneg (Work.BoseFixB1P.measurableSet_Box3 p q)
                (fun x _ => sq_nonneg _)
            calc ((q k - p k) / a) ^ 2 * (∫ x in Work.BoseFixB1P.Box3 p q,
                  (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2)
                ≤ 1 * (∫ x in Work.BoseFixB1P.Box3 p q,
                  (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2) :=
                  mul_le_mul_of_nonneg_right (pow_le_one₀ (le_of_lt (hdpos k)) (hdle k)) hJ
              _ = ∫ x in Work.BoseFixB1P.Box3 p q,
                  (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2 := one_mul _)

end Work.BoseFixB1S
