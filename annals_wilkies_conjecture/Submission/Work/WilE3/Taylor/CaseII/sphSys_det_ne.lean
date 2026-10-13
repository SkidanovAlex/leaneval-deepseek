import Mathlib
import Submission.Work.WilE3.Taylor.CaseII.Defs
import Submission.Work.WilE3.Taylor.CaseII.sphAux
import Submission.Work.WilE3.Taylor.CaseII.ae_regular_shear
import Submission.Work.WilE3.Taylor.CaseII.ae_of_ae_linearEquiv
import Submission.Work.WilE3.Taylor.CaseII.eaEval_pertMinor3_eq_smul_shfun
import Submission.Work.WilE3.Taylor.CaseII.contDiffOn_master_data
import Submission.Work.WilE3.Taylor.CaseII.sysDet_sphSys_aux
import Submission.Work.WilE3.Taylor.CaseII.pertSys_det_ne
import Submission.Work.WilE3.API.hasFDerivAt_eaEval
import Submission.Work.WilE3.eaEval_analytic
import Submission.Work.WilE3.Taylor.Grad.PolarDefs

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / CaseII, node **T4 (boundary)**: `sphSys_det_ne`.

  For almost every `(v, δ²)` the boundary square system `sphSys c Φ v y δ² i₀ j₀` (row `i₀` is
  `Φ`, row `j₀` the fixed sphere `∑ᵢ (xᵢ-yᵢ)² = δ²`, the other rows the perturbed radial minors
  `pertMinor3`) is *not* identically degenerate along any analytic arc `γ` at a zero of `Φ` with
  `Φ ∘ γ > 0` tending to `0`, along which the sphere and the radial minors vanish and the
  non-degeneracy `μ = ∂_{i₀}Φ (x_{j₀}-y_{j₀}) - ∂_{j₀}Φ (x_{i₀}-y_{i₀}) ≠ 0` holds.

  The proof follows the interior twin `pertSys_det_ne`:

  * on `Uset = {μ ≠ 0}` the radial minor has the **shear form** `pertMinor3 l = G μ · shfun l`
    (`eaEval_pertMinor3_eq_smul_shfun`), where `G = sqGrad c Φ`;
  * `ae_regular_shear` (parametric Sard in free-target form) gives, after transporting along the
    linear reparametrization `TparamLV` (`ae_of_ae_linearEquiv`) and Fubini
    (`Measure.ae_ae_of_ae_prod`), that for a.e. `(v, δ²)` and a.e. level `c` every solution
    `x ∈ Uset` of the shear system at level `c` has injective Jacobian;
  * `sysDet_sphSys_ne_zero` converts that injectivity into `sysDet ≠ 0` for the actual system;
  * the arc sweeps an interval of levels, so it meets a good level in every right-neighbourhood of
    `0`; hence `sysDet` cannot vanish on a whole right-neighbourhood of `0`.
-/

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
open WilkiesDesign.E

namespace Work.WilE3.Taylor.CaseII

variable {k r : ℕ}

/-! ## Elementary facts -/

/-- `eaEval c Q` is continuous. -/
lemma continuous_eaEval_master (c : EAChain k r) (Q : EAPoly k r) :
    Continuous fun x : Fin k → ℝ => eaEval c Q x :=
  continuous_iff_continuousAt.mpr fun x =>
    (Work.WilE3.API.hasFDerivAt_eaEval c Q x).continuousAt

/-- `Uset = {μ ≠ 0}` is open. -/
lemma isOpen_Uset (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ : Fin k) :
    IsOpen (Uset c Φ y i₀ j₀) := by
  rw [Uset]
  refine isOpen_compl_singleton.preimage ?_
  unfold muq Wq Tq
  refine continuous_iff_continuousAt.mpr (fun x => ?_)
  exact (((continuous_eaEval_master c (eaD c i₀ Φ)).continuousAt).mul
      (((continuous_apply j₀).sub continuous_const).continuousAt)).sub
    (((continuous_eaEval_master c (eaD c j₀ Φ)).continuousAt).mul
      (((continuous_apply i₀).sub continuous_const).continuousAt))

/-- Evaluation of the sphere polynomial.  (Made `private` by the area owner: the same name is
declared in `CaseII.badArcAux.lean`, and both modules are needed by `CaseII.GenGrad`.) -/
private lemma eaEval_sphereP (c : EAChain k r) (y : Fin k → ℝ) (δ2 : ℝ) (x : Fin k → ℝ) :
    eaEval c (sphereP y δ2) x = Sq y x - δ2 := by
  simp [sphereP, Sq, Tq, eaEval, map_sum, map_sub, map_pow]

/-- On `Uset` the squared gradient `G = sqGrad c Φ` does not vanish. -/
lemma Gq_ne_zero_of_mem_Uset (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ)
    (i₀ j₀ : Fin k) {x : Fin k → ℝ} (hx : x ∈ Uset c Φ y i₀ j₀) : Gq c Φ x ≠ 0 := by
  intro hG
  have hsum : ∑ l : Fin k, (Wq c Φ l x) ^ 2 = 0 := by
    rw [← hG, Gq, Work.WilE3.Taylor.eaEval_sqGrad]
    simp [Wq]
  have hzero : ∀ i : Fin k, Wq c Φ i x = 0 := by
    intro i
    have hle : (Wq c Φ i x) ^ 2 ≤ ∑ l : Fin k, (Wq c Φ l x) ^ 2 :=
      Finset.single_le_sum (fun l _ => sq_nonneg (Wq c Φ l x)) (Finset.mem_univ i)
    rw [hsum] at hle
    exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))
  exact hx (by simp [muq, hzero i₀, hzero j₀])

/-- Componentwise value of `Amas`. -/
lemma Amas_apply (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ : Fin k)
    (x : Fin k → ℝ) (i : Fin k) :
    Amas c Φ y i₀ j₀ x i
      = if i = i₀ then eaEval c Φ x else if i = j₀ then Sq y x else shA c Φ y i₀ j₀ i x :=
  rfl

/-- Componentwise value of `bmas`. -/
lemma bmas_apply (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ : Fin k)
    (x : Fin k → ℝ) (θ : Fin 2 → ℝ) (i : Fin k) :
    (bmas c Φ y i₀ j₀ x θ) i
      = if i = i₀ ∨ i = j₀ then 0
        else shB1 c Φ y i₀ j₀ i x * θ 0 + shB2 c Φ y i₀ j₀ i x * θ 1 := by
  by_cases h : i = i₀ ∨ i = j₀
  · simp [bmas, h]
  · simp [bmas, h, ContinuousLinearMap.pi_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- Componentwise value of `kappaLV`. -/
lemma kappaLV_apply' {k : ℕ} (i₀ j₀ : Fin k) (hij : i₀ ≠ j₀)
    (p : ((Fin k → ℝ) × ℝ) × ℝ) (i : Fin k) :
    kappaLV k i₀ j₀ hij p i
      = if i = i₀ then p.2 else if i = j₀ then p.1.2 else -(p.1.1 i) := by
  rfl

/-- The first coordinate of `thetaLV`. -/
lemma thetaLV_zero {k : ℕ} (i₀ j₀ : Fin k) (p : ((Fin k → ℝ) × ℝ) × ℝ) :
    thetaLV k i₀ j₀ p 0 = p.1.1 i₀ := by
  change (if (0 : Fin 2) = 0 then p.1.1 i₀ else p.1.1 j₀) = p.1.1 i₀
  rw [if_pos rfl]

/-- The second coordinate of `thetaLV`. -/
lemma thetaLV_one {k : ℕ} (i₀ j₀ : Fin k) (p : ((Fin k → ℝ) × ℝ) × ℝ) :
    thetaLV k i₀ j₀ p 1 = p.1.1 j₀ := by
  have h10 : ¬((1 : Fin 2) = 0) := by decide
  change (if (1 : Fin 2) = 0 then p.1.1 i₀ else p.1.1 j₀) = p.1.1 j₀
  rw [if_neg h10]

/-- The master equation of the shear system at the parameters encoded by `p = ((v, δ²), c)` is
exactly `Φ = c`, `Sq y = δ²` and `shfun l v = 0` for `l ∉ {i₀, j₀}`. -/
lemma master_equiv (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ : Fin k)
    (hij : i₀ ≠ j₀) (p : ((Fin k → ℝ) × ℝ) × ℝ) {x : Fin k → ℝ}
    (hΦ : eaEval c Φ x = p.2) (hS : Sq y x = p.1.2)
    (hl : ∀ l : Fin k, l ≠ i₀ → l ≠ j₀ → shfun c Φ y i₀ j₀ l p.1.1 x = 0) :
    Amas c Φ y i₀ j₀ x + bmas c Φ y i₀ j₀ x (thetaLV k i₀ j₀ p)
      = kappaLV k i₀ j₀ hij p := by
  funext i
  rw [Pi.add_apply, Amas_apply, bmas_apply, kappaLV_apply', thetaLV_zero, thetaLV_one]
  by_cases h₁ : i = i₀
  · rw [if_pos h₁, if_pos (Or.inl h₁), if_pos h₁, add_zero]
    exact hΦ
  · by_cases h₂ : i = j₀
    · rw [if_neg h₁, if_pos h₂, if_pos (Or.inr h₂), if_neg h₁, if_pos h₂, add_zero]
      exact hS
    · rw [if_neg h₁, if_neg h₂, if_neg (fun h => h.elim h₁ h₂), if_neg h₁, if_neg h₂]
      have hli := hl i h₁ h₂
      simp only [shfun, Pi.add_apply] at hli
      linarith

/-- `thetaLV` at the parameters `((v, δ²), c)` is `shearParam v`. -/
lemma thetaLV_eq_shearParam {k : ℕ} (i₀ j₀ : Fin k) (vd : (Fin k → ℝ) × ℝ) (cc : ℝ) :
    thetaLV k i₀ j₀ (vd, cc) = shearParam vd.1 i₀ j₀ := by
  funext t
  by_cases h : t = 0 <;> simp [thetaLV, shearParam, h]

/-! ## The main theorem -/

theorem sphSys_det_ne {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) (Φ : WilkiesDesign.E.EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ : Fin k)
    (hij : i₀ ≠ j₀) :
    ∀ᵐ vd : (Fin k → ℝ) × ℝ, ∀ γ : ℝ → Fin k → ℝ, AnalyticAt ℝ γ 0 →
      WilkiesDesign.E.eaEval c Φ (γ 0) = 0 →
      (∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < WilkiesDesign.E.eaEval c Φ (γ t) ∧
        WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.CaseII.sphereP y vd.2) (γ t) = 0 ∧
        WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i₀ Φ) (γ t) * (γ t j₀ - y j₀)
          - WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c j₀ Φ) (γ t) * (γ t i₀ - y i₀) ≠ 0 ∧
        ∀ l : Fin k, l ≠ i₀ → l ≠ j₀ →
          WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.CaseII.pertMinor3 c Φ vd.1 y i₀ j₀ l) (γ t) = 0) →
      ¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          Work.WilE3.Taylor.CaseII.sysDet c (Work.WilE3.Taylor.CaseII.sphSys c Φ vd.1 y vd.2 i₀ j₀) (γ t) = 0 := by
  haveI hHaarF : Measure.IsAddHaarMeasure (volume : Measure ((Fin k → ℝ) × (Fin 2 → ℝ))) := by
    rw [Measure.volume_eq_prod (Fin k → ℝ) (Fin 2 → ℝ)]
    exact Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin k → ℝ))
      (volume : Measure (Fin 2 → ℝ))
  haveI hHaarProd : Measure.IsAddHaarMeasure (volume : Measure ((Fin k → ℝ) × ℝ)) := by
    rw [Measure.volume_eq_prod (Fin k → ℝ) ℝ]
    exact Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin k → ℝ))
      (volume : Measure ℝ)
  haveI hHaarE : Measure.IsAddHaarMeasure (volume : Measure (((Fin k → ℝ) × ℝ) × ℝ)) := by
    rw [Measure.volume_eq_prod ((Fin k → ℝ) × ℝ) ℝ]
    exact Measure.prod.instIsAddHaarMeasure (volume : Measure ((Fin k → ℝ) × ℝ))
      (volume : Measure ℝ)
  obtain ⟨hA, hb, _⟩ := contDiffOn_master_data c Φ y i₀ j₀
  have hsard := ae_regular_shear (U := Uset c Φ y i₀ j₀) (isOpen_Uset c Φ y i₀ j₀)
    (volume : Measure ((Fin k → ℝ) × (Fin 2 → ℝ)))
    (Amas c Φ y i₀ j₀) (bmas c Φ y i₀ j₀) hA hb
  have htrans := ae_of_ae_linearEquiv (volume : Measure (((Fin k → ℝ) × ℝ) × ℝ))
    (volume : Measure ((Fin k → ℝ) × (Fin 2 → ℝ)))
    (TparamLV k i₀ j₀ hij) hsard
  rw [Measure.volume_eq_prod ((Fin k → ℝ) × ℝ) ℝ] at htrans
  have h1 : ∀ᵐ vd : (Fin k → ℝ) × ℝ, (∀ᵐ cc : ℝ,
      ∀ x ∈ Uset c Φ y i₀ j₀,
      Amas c Φ y i₀ j₀ x + bmas c Φ y i₀ j₀ x (thetaLV k i₀ j₀ (vd, cc))
        = kappaLV k i₀ j₀ hij (vd, cc) →
      Function.Injective (fderiv ℝ (fun z => Amas c Φ y i₀ j₀ z
        + bmas c Φ y i₀ j₀ z (thetaLV k i₀ j₀ (vd, cc))) x)) :=
    Measure.ae_ae_of_ae_prod htrans
  refine h1.mono ?_
  intro vd hvd
  intro γ hγ hγ0 hgood hbad
  obtain ⟨δ, hδ, hδgood⟩ := exists_pos_of_eventually_nhdsGT hgood
  obtain ⟨δ₀, hδ₀, hδbad⟩ := exists_pos_of_eventually_nhdsGT hbad
  obtain ⟨ρ, hρ, hρan⟩ := Metric.eventually_nhds_iff.mp (hγ.eventually_analyticAt)
  set t₁ : ℝ := min (min δ δ₀) ρ / 2 with ht₁
  have hminpos : 0 < min (min δ δ₀) ρ := lt_min (lt_min hδ hδ₀) hρ
  have ht₁pos : 0 < t₁ := by rw [ht₁]; positivity
  have ht₁lt : t₁ < min (min δ δ₀) ρ := by rw [ht₁]; linarith
  have ht₁δ : t₁ < δ := lt_of_lt_of_le ht₁lt (le_trans (min_le_left (min δ δ₀) ρ) (min_le_left δ δ₀))
  have ht₁δ₀ : t₁ < δ₀ := lt_of_lt_of_le ht₁lt (le_trans (min_le_left (min δ δ₀) ρ) (min_le_right δ δ₀))
  have ht₁ρ : t₁ < ρ := lt_of_lt_of_le ht₁lt (min_le_right (min δ δ₀) ρ)
  have hΦcont : ContinuousOn (fun t : ℝ => eaEval c Φ (γ t)) (Set.Icc 0 t₁) := by
    refine continuousOn_of_forall_continuousAt fun t ht => ?_
    have hdist : dist t 0 < ρ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      exact lt_of_le_of_lt ht.2 ht₁ρ
    exact ((eaEval_analytic c Φ (γ t)).continuousAt).comp ((hρan hdist).continuousAt)
  have hgoodt₁ := hδgood t₁ ht₁pos ht₁δ
  have hvol : volume (Set.Ioo 0 (eaEval c Φ (γ t₁))) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hgoodt₁.1))
  obtain ⟨cc, hcc, hccgood⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hvol (MeasureTheory.ae_restrict_of_ae hvd)
  have hccIcc : cc ∈ Set.Icc (eaEval c Φ (γ 0)) (eaEval c Φ (γ t₁)) :=
    ⟨by rw [hγ0]; exact hcc.1.le, hcc.2.le⟩
  obtain ⟨s, hs, hsf⟩ := intermediate_value_Icc (le_of_lt ht₁pos) hΦcont hccIcc
  have hsf' : eaEval c Φ (γ s) = cc := hsf
  have hsne : s ≠ 0 := by
    intro h0
    rw [h0, hγ0] at hsf'
    linarith [hcc.1]
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hsne)
  have hsgood := hδgood s hspos (lt_of_le_of_lt hs.2 ht₁δ)
  -- the point `γ s` lies on `Uset`, satisfies the sphere and shear equations, at a good level
  have hxU : γ s ∈ Uset c Φ y i₀ j₀ := hsgood.2.2.1
  have hS : Sq y (γ s) = vd.2 := by
    have h := hsgood.2.1
    rw [eaEval_sphereP] at h
    linarith
  have hsh : ∀ l : Fin k, l ≠ i₀ → l ≠ j₀ → shfun c Φ y i₀ j₀ l vd.1 (γ s) = 0 := by
    intro l hl₁ hl₂
    have hGμ : Gq c Φ (γ s) * muq c Φ y i₀ j₀ (γ s) ≠ 0 :=
      mul_ne_zero (Gq_ne_zero_of_mem_Uset c Φ y i₀ j₀ hxU) hxU
    have h3 := eaEval_pertMinor3_eq_smul_shfun c Φ y vd.1 i₀ j₀ l hxU
    rw [hsgood.2.2.2 l hl₁ hl₂] at h3
    exact (mul_eq_zero.mp h3.symm).resolve_left hGμ
  have heq : Amas c Φ y i₀ j₀ (γ s) + bmas c Φ y i₀ j₀ (γ s) (thetaLV k i₀ j₀ (vd, cc))
      = kappaLV k i₀ j₀ hij (vd, cc) :=
    master_equiv c Φ y i₀ j₀ hij (vd, cc) hsf' hS hsh
  have hinj := hccgood (γ s) hxU heq
  refine (sysDet_sphSys_ne_zero_aux c Φ y vd.1 vd.2 i₀ j₀ hij hxU hsh ?_)
    (hδbad s hspos (lt_of_le_of_lt hs.2 ht₁δ₀))
  unfold MasterFun
  rw [thetaLV_eq_shearParam i₀ j₀ vd cc] at hinj
  exact hinj

end Work.WilE3.Taylor.CaseII
