import Mathlib
import Submission.Work.WilE3.Taylor.CaseII.Defs
import Submission.Work.WilE3.Taylor.CaseII.PertShear
import Submission.Work.WilE3.Taylor.CaseII.contDiffOn_shear_data
import Submission.Work.WilE3.Taylor.CaseII.shear_regular_ae
import Submission.Work.WilE3.Taylor.CaseII.sysDet_pertSys_ne_zero_of_shearInj
import Submission.Work.WilE3.eaEval_analytic

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / CaseII, node **T4 (interior)**: for almost every
  perturbation `v` the square system `pertSys c Φ v i₀` (pivot row `Φ`, other rows the perturbed
  polar minors `pertMinor c Φ v i₀ i`) is *not* identically degenerate along an analytic arc that
  has `Φ ∘ γ > 0` tending to `0`, `∂_{i₀}Φ ≠ 0` and all perturbed minors vanishing.

  The proof is the one designed in `cbc/wilkies_e3_caseII.md` §3 (node T4):

  * on `Ush = {G ∂_{i₀}Φ ≠ 0}` (`G = sqGrad c Φ`) the perturbed minor has the **shear form**
    `pertMinor(v)ᵢ = G ∂_{i₀}Φ · (aᵢ + bᵢ v_{i₀} + vᵢ)` (`PertShear.aSh_add_bSh_mul_add`);
  * `shear_regular_ae` (parametric Sard for the shear system) gives, for a.e. `(v, c)`, that every
    solution `x ∈ Ush` of the shear equations at level `c` has injective shear Jacobian;
  * `sysDet_pertSys_ne_zero_of_shearInj` converts that injectivity into `sysDet ≠ 0` for the actual
    system;
  * the arc `γ` with `Φ ∘ γ > 0`, `Φ (γ 0) = 0` sweeps an interval of levels, so it meets a good
    level in every right-neighbourhood of `0`; hence `sysDet` cannot vanish on a whole
    right-neighbourhood of `0`.
-/

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
open WilkiesDesign.E

namespace Work.WilE3.Taylor.CaseII

variable {k r : ℕ}

/-! ## Auxiliary lemmas -/

/-- `G = sqGrad c Φ` is a sum of squares, hence nonnegative. -/
lemma eaEval_sqGrad_nonneg (c : EAChain k r) (Φ : EAPoly k r) (x : Fin k → ℝ) :
    0 ≤ eaEval c (sqGrad c Φ) x := by
  rw [Work.WilE3.Taylor.eaEval_sqGrad]
  exact Finset.sum_nonneg fun l _ => sq_nonneg _

/-- If `∂_{i₀}Φ` does not vanish at `x`, then neither does `G · ∂_{i₀}Φ` (the sum of squares `G`
contains the square `(∂_{i₀}Φ)²`), i.e. `x ∈ Ush`. -/
lemma denP_ne_zero_of_eaD_ne_zero (c : EAChain k r) (Φ : EAPoly k r) (i₀ : Fin k)
    (x : Fin k → ℝ) (h : eaEval c (eaD c i₀ Φ) x ≠ 0) :
    eaEval c (denP c Φ i₀) x ≠ 0 := by
  rw [eaEval_denP]
  refine mul_ne_zero ?_ h
  intro hG
  have hle : (eaEval c (eaD c i₀ Φ) x) ^ 2 ≤ eaEval c (sqGrad c Φ) x := by
    rw [Work.WilE3.Taylor.eaEval_sqGrad]
    exact Finset.single_le_sum (fun l _ => sq_nonneg (eaEval c (eaD c l Φ) x)) (Finset.mem_univ i₀)
  rw [hG] at hle
  exact h (sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _)))

/-- The shear equations hold at `x ∈ Ush` as soon as the perturbed minors vanish there. -/
lemma shear_constraint_of_pertMinor (c : EAChain k r) (Φ : EAPoly k r) (i₀ : Fin k)
    (v : Fin k → ℝ) (x : Fin k → ℝ) (hx : x ∈ Ush c Φ i₀)
    (hP : ∀ i : Fin k, i ≠ i₀ → eaEval c (pertMinor c Φ v i₀ i) x = 0) :
    ∀ i : Fin k, i ≠ i₀ → aSh c Φ i₀ x i + bSh c Φ i₀ x i * v i₀ + v i = 0 := by
  intro i hi
  have h := aSh_add_bSh_mul_add c Φ i₀ v x hx i hi
  rw [hP i hi] at h
  simpa using h

/-- An event that holds eventually to the right of `0` holds on an explicit interval `(0, ε)`. -/
lemma exists_pos_of_eventually_nhdsGT {P : ℝ → Prop}
    (h : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), P t) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → P t := by
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hε, h'⟩ := h
  exact ⟨ε, hε, fun t ht hlt =>
    h' (by rw [Real.dist_eq, sub_zero, abs_of_pos ht]; exact hlt) (Set.mem_Ioi.mpr ht)⟩

/-! ## The main theorem -/

theorem pertSys_det_ne {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) (Φ : WilkiesDesign.E.EAPoly k r) (i₀ : Fin k) :
    ∀ᵐ v : Fin k → ℝ, ∀ γ : ℝ → Fin k → ℝ, AnalyticAt ℝ γ 0 →
      WilkiesDesign.E.eaEval c Φ (γ 0) = 0 →
      (∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < WilkiesDesign.E.eaEval c Φ (γ t) ∧
        WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i₀ Φ) (γ t) ≠ 0 ∧
        ∀ i : Fin k, i ≠ i₀ → WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.CaseII.pertMinor c Φ v i₀ i) (γ t) = 0) →
      ¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          Work.WilE3.Taylor.CaseII.sysDet c (Work.WilE3.Taylor.CaseII.pertSys c Φ v i₀) (γ t) = 0 := by
  obtain ⟨haSh, hbSh, hφ⟩ := contDiffOn_shear_data c Φ i₀
  have hsh := shear_regular_ae i₀ (Ush c Φ i₀) (isOpen_Ush c Φ i₀) (aSh c Φ i₀) (bSh c Φ i₀)
    (fun x => eaEval c Φ x) haSh hbSh hφ
  rw [Measure.volume_eq_prod (Fin k → ℝ) ℝ] at hsh
  have h1 : ∀ᵐ v : Fin k → ℝ, ∀ᵐ cc : ℝ, ∀ x ∈ Ush c Φ i₀,
      (∀ i : Fin k, i ≠ i₀ → aSh c Φ i₀ x i + bSh c Φ i₀ x i * v i₀ + v i = 0) →
      eaEval c Φ x = cc →
      Function.Injective (LinearMap.pi (fun i : Fin k =>
        if i = i₀ then (fderiv ℝ (fun z : Fin k → ℝ => eaEval c Φ z) x).toLinearMap
        else (fderiv ℝ (fun z : Fin k → ℝ =>
          aSh c Φ i₀ z i + bSh c Φ i₀ z i * v i₀) x).toLinearMap)) :=
    Measure.ae_ae_of_ae_prod hsh
  filter_upwards [h1] with v hv γ hγ hγ0 hgood
  intro hbad
  -- explicit radii for the two eventually-statements and for analyticity
  obtain ⟨δ, hδ, hδgood⟩ := exists_pos_of_eventually_nhdsGT hgood
  obtain ⟨δ₀, hδ₀, hδbad⟩ := exists_pos_of_eventually_nhdsGT hbad
  obtain ⟨ρ, hρ, hρan⟩ := Metric.eventually_nhds_iff.mp (hγ.eventually_analyticAt)
  set t₁ : ℝ := min (min δ δ₀) ρ / 2 with ht₁
  have hminpos : 0 < min (min δ δ₀) ρ := lt_min (lt_min hδ hδ₀) hρ
  have ht₁pos : 0 < t₁ := by rw [ht₁]; positivity
  have ht₁δ : t₁ < δ := by
    have h1 : t₁ < min (min δ δ₀) ρ := by rw [ht₁]; linarith
    exact lt_of_lt_of_le h1 (le_trans (min_le_left (min δ δ₀) ρ) (min_le_left δ δ₀))
  have ht₁δ₀ : t₁ < δ₀ := by
    have h1 : t₁ < min (min δ δ₀) ρ := by rw [ht₁]; linarith
    exact lt_of_lt_of_le h1 (le_trans (min_le_left (min δ δ₀) ρ) (min_le_right δ δ₀))
  have ht₁ρ : t₁ < ρ := by
    have h1 : t₁ < min (min δ δ₀) ρ := by rw [ht₁]; linarith
    exact lt_of_lt_of_le h1 (min_le_right (min δ δ₀) ρ)
  -- the level function `t ↦ Φ (γ t)` is continuous on `[0, t₁]`
  have hΦcont : ContinuousOn (fun t : ℝ => eaEval c Φ (γ t)) (Set.Icc 0 t₁) := by
    refine continuousOn_of_forall_continuousAt fun t ht => ?_
    have hdist : dist t 0 < ρ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      exact lt_of_le_of_lt ht.2 ht₁ρ
    exact ((eaEval_analytic c Φ (γ t)).continuousAt).comp ((hρan hdist).continuousAt)
  have hgoodt₁ := hδgood t₁ ht₁pos ht₁δ
  -- a good level inside the interval of levels swept by the arc
  have hvol : volume (Set.Ioo 0 (eaEval c Φ (γ t₁))) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hgoodt₁.1))
  obtain ⟨cc, hcc, hccgood⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hvol (MeasureTheory.ae_restrict_of_ae hv)
  -- the level is attained by the arc at some `s ∈ (0, t₁)`
  have hzero0 : eaEval c Φ (γ 0) = 0 := hγ0
  have hccIcc : cc ∈ Set.Icc (eaEval c Φ (γ 0)) (eaEval c Φ (γ t₁)) :=
    ⟨by rw [hγ0]; exact hcc.1.le, hcc.2.le⟩
  obtain ⟨s, hs, hsf⟩ := intermediate_value_Icc (le_of_lt ht₁pos) hΦcont hccIcc
  have hsf' : eaEval c Φ (γ s) = cc := hsf
  have hs0 : s ≠ 0 := by
    intro h0
    have h0' : eaEval c Φ (γ s) = 0 := by rw [h0]; exact hγ0
    rw [hsf'] at h0'
    linarith [hcc.1]
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)

  have hsgood := hδgood s hspos (lt_of_le_of_lt hs.2 ht₁δ)
  -- the point `γ s` is on the shear locus, satisfies the shear equations, and the level is good
  have hxUsh : γ s ∈ Ush c Φ i₀ := denP_ne_zero_of_eaD_ne_zero c Φ i₀ (γ s) hsgood.2.1
  have hcons : ∀ i : Fin k, i ≠ i₀ →
      aSh c Φ i₀ (γ s) i + bSh c Φ i₀ (γ s) i * v i₀ + v i = 0 :=
    shear_constraint_of_pertMinor c Φ i₀ v (γ s) hxUsh hsgood.2.2
  have hlev : eaEval c Φ (γ s) = cc := hsf'
  have hinj := hccgood (γ s) hxUsh hcons hlev
  have hdet := sysDet_pertSys_ne_zero_of_shearInj c Φ i₀ v (γ s) hxUsh haSh hbSh hcons hinj
  have hsδ₀ : s < δ₀ := lt_of_le_of_lt hs.2 ht₁δ₀
  exact hdet (hδbad s hspos hsδ₀)

end Work.WilE3.Taylor.CaseII
