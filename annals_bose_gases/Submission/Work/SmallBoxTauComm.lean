import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Q0Value
import Submission.Work.SmallBoxTauModes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-273 — the D1 `τ`-commutator chapter (FS `lm:appbogolubov`)
-/

noncomputable section
open MeasureTheory Metric
open scoped Topology Real BigOperators ENNReal
namespace Submission
open _root_.BoseGases
set_option autoImplicit false
namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. Measures, the peel and the torsion map -/

/-- the box measure on the `N`-body box -/
abbrev boxMeas (N : ℕ) (s : ℝ) : Measure (X N) :=
  (volume : Measure (X N)).restrict (abox N s)

/-- the cube measure -/
abbrev cubeMeas (s : ℝ) : Measure ℝ³ := (volume : Measure ℝ³).restrict (acube s)

lemma isFiniteMeasure_cubeMeas {s : ℝ} (hs : 0 < s) : IsFiniteMeasure (cubeMeas s) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact acube_lt_top s hs.le⟩

lemma isFiniteMeasure_boxMeas {N : ℕ} {s : ℝ} (hs : 0 < s) :
    IsFiniteMeasure (boxMeas N s) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact (abox_lt_top N s hs.le)⟩

/-- Integrability of a continuous function on the box product. -/
lemma integrable_of_continuous_boxProd {N : ℕ} {s : ℝ} (hs : 0 < s) {F : X N × ℝ³ → ℝ}
    (hF : Continuous F) : Integrable F ((boxMeas N s).prod (cubeMeas s)) := by
  have h : Integrable F (((volume : Measure (X N)).prod (volume : Measure ℝ³)).restrict
      (abox N s ×ˢ acube s)) :=
    ContinuousOn.integrableOn_compact ((abox_compact N hs).prod (acube_compact hs))
      hF.continuousOn
  rwa [← Measure.prod_restrict] at h

/-- almost every point of the box product lies in the box. -/
lemma ae_mem_box_prod {N : ℕ} {s : ℝ} (hs : 0 < s) :
    ∀ᵐ p ∂((boxMeas N s).prod (cubeMeas s)), p.1 ∈ abox N s ∧ p.2 ∈ acube s := by
  haveI : IsFiniteMeasure ((volume : Measure (X N)).restrict (abox N s)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (abox_lt_top N s hs.le)⟩
  have h : ∀ᵐ p ∂((boxMeas N s).prod (cubeMeas s)), p ∈ abox N s ×ˢ acube s := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem ((abox_measurable N s).prod (acube_measurable s))
  filter_upwards [h] with p hp using hp

/-- inserting into the box stays in the box -/
lemma update_mem_abox_of_mem {s : ℝ} {n : ℕ} (i : Fin (n + 1)) {x : X (n + 1)}
    (hx : x ∈ abox (n + 1) s) {z : ℝ³} (hz : z ∈ acube s) :
    Function.update x i z ∈ abox (n + 1) s := by
  rw [mem_abox_iff] at hx ⊢
  intro j
  rw [Function.update_apply]
  split_ifs with hj
  · exact hz
  · exact hx j

/-- Peel measure preservation (corpus `abox_peel_mp`, reversed). -/
lemma kcInsN_measurePreserving {s : ℝ} {n : ℕ} (i : Fin (n + 1)) :
    MeasurePreserving (⇑(kcInsN n i)) ((cubeMeas s).prod (boxMeas n s)) (boxMeas (n + 1) s) :=
  MeasurePreserving.symm _ (abox_peel_mp (n := n) s i)

/-- The triple insertion map `(r,(a,b)) ↦ (kcInsN n i (a,r), b)`. -/
noncomputable def boxTripleFun {n : ℕ} (i : Fin (n + 1)) :
    X n × (ℝ³ × ℝ³) → X (n + 1) × ℝ³ :=
  (Prod.map (kcInsN n i) id) ∘ (Prod.map Prod.swap id) ∘ (Equiv.prodAssoc (X n) ℝ³ ℝ³).symm

lemma boxTripleFun_apply {n : ℕ} (i : Fin (n + 1)) (r : X n) (a b : ℝ³) :
    boxTripleFun i (r, (a, b)) = (kcInsN n i (a, r), b) := by
  simp [boxTripleFun, Prod.map_apply, Equiv.prodAssoc]

lemma boxTripleFun_measurePreserving {s : ℝ} (hs : 0 < s) {n : ℕ} (i : Fin (n + 1)) :
    MeasurePreserving (boxTripleFun (n := n) i)
      ((boxMeas n s).prod ((cubeMeas s).prod (cubeMeas s)))
      ((boxMeas (n + 1) s).prod (cubeMeas s)) := by
  haveI : IsFiniteMeasure (cubeMeas s) := isFiniteMeasure_cubeMeas hs
  haveI : IsFiniteMeasure (boxMeas n s) := isFiniteMeasure_boxMeas hs
  have hA : MeasurePreserving (Prod.map (kcInsN n i) id)
      (((cubeMeas s).prod (boxMeas n s)).prod (cubeMeas s))
      ((boxMeas (n + 1) s).prod (cubeMeas s)) :=
    MeasurePreserving.prod (kcInsN_measurePreserving i) (MeasurePreserving.id (cubeMeas s))
  have hB : MeasurePreserving (Prod.map Prod.swap id)
      (((boxMeas n s).prod (cubeMeas s)).prod (cubeMeas s))
      (((cubeMeas s).prod (boxMeas n s)).prod (cubeMeas s)) :=
    MeasurePreserving.prod
      (Measure.measurePreserving_swap (μ := boxMeas n s) (ν := cubeMeas s))
      (MeasurePreserving.id (cubeMeas s))
  have hC : MeasurePreserving (⇑((Equiv.prodAssoc (X n) ℝ³ ℝ³).symm))
      ((boxMeas n s).prod ((cubeMeas s).prod (cubeMeas s)))
      (((boxMeas n s).prod (cubeMeas s)).prod (cubeMeas s)) :=
    MeasurePreserving.symm _
      (measurePreserving_prodAssoc (boxMeas n s) (cubeMeas s) (cubeMeas s))
  have hcomp := hA.comp (hB.comp hC)
  simpa [boxTripleFun] using hcomp

/-- The pair swap `(r,(a,b)) ↦ (r,(b,a))`. -/
noncomputable def pairSwapEquiv (n : ℕ) : X n × (ℝ³ × ℝ³) ≃ᵐ X n × (ℝ³ × ℝ³) :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl (X n)) (MeasurableEquiv.prodComm)

lemma pairSwapEquiv_apply {n : ℕ} (r : X n) (a b : ℝ³) :
    pairSwapEquiv n (r, (a, b)) = (r, (b, a)) := by
  simp [pairSwapEquiv, MeasurableEquiv.prodCongr, MeasurableEquiv.prodComm]

lemma pairSwapEquiv_measurePreserving {s : ℝ} {n : ℕ} :
    MeasurePreserving (⇑(pairSwapEquiv n))
      ((boxMeas n s).prod ((cubeMeas s).prod (cubeMeas s)))
      ((boxMeas n s).prod ((cubeMeas s).prod (cubeMeas s))) := by
  have hA : MeasurePreserving (id : X n → X n) (boxMeas n s) (boxMeas n s) :=
    MeasurePreserving.id _
  have hB : MeasurePreserving Prod.swap ((cubeMeas s).prod (cubeMeas s))
      ((cubeMeas s).prod (cubeMeas s)) := Measure.measurePreserving_swap
  have h := MeasurePreserving.prod hA hB
  simpa [pairSwapEquiv, MeasurableEquiv.prodCongr, MeasurableEquiv.prodComm,
    MeasurableEquiv.refl, Prod.map] using h

/-- **The swap identity.**  The torsion map `(x,z) ↦ (x_{i←z}, x_i)` on
`abox (n+1) s × acube s` preserves the measure. -/
theorem integral_swap_update {s : ℝ} (hs : 0 < s) {n : ℕ} (i : Fin (n + 1))
    (G : X (n + 1) → ℝ³ → ℝ)
    (hG : Continuous fun p : X (n + 1) × ℝ³ => G p.1 p.2) :
    (∫ x in abox (n + 1) s, ∫ z in acube s, G x z)
      = ∫ x in abox (n + 1) s, ∫ z in acube s, G (Function.update x i z) (x i) := by
  have hG' : Continuous fun p : X (n + 1) × ℝ³ =>
      G (Function.update p.1 i p.2) (p.1 i) := by
    have h1 : Continuous fun p : X (n + 1) × ℝ³ => Function.update p.1 i p.2 :=
      continuous_fst.update i continuous_snd
    have h2 : Continuous fun p : X (n + 1) × ℝ³ => p.1 i :=
      (continuous_apply (A := fun _ : Fin (n + 1) => ℝ³) i).comp continuous_fst
    exact hG.comp (h1.prodMk h2)
  have hL : (∫ x in abox (n + 1) s, ∫ z in acube s, G x z)
      = ∫ p : X (n + 1) × ℝ³, G p.1 p.2 ∂((boxMeas (n + 1) s).prod (cubeMeas s)) :=
    (integral_prod _ (integrable_of_continuous_boxProd hs hG)).symm
  have hR : (∫ x in abox (n + 1) s, ∫ z in acube s, G (Function.update x i z) (x i))
      = ∫ p : X (n + 1) × ℝ³, G (Function.update p.1 i p.2) (p.1 i)
          ∂((boxMeas (n + 1) s).prod (cubeMeas s)) :=
    (integral_prod _ (integrable_of_continuous_boxProd hs hG')).symm
  set νt : Measure (X n × (ℝ³ × ℝ³)) :=
    (boxMeas n s).prod ((cubeMeas s).prod (cubeMeas s)) with hνt
  have hpeel := boxTripleFun_measurePreserving hs i
  have hf1 : AEStronglyMeasurable (fun p : X (n + 1) × ℝ³ => G p.1 p.2)
      (Measure.map (boxTripleFun (n := n) i) νt) := by
    rw [hνt]; rw [hpeel.map_eq]; exact hG.aestronglyMeasurable
  have hf2 : AEStronglyMeasurable (fun p : X (n + 1) × ℝ³ =>
        G (Function.update p.1 i p.2) (p.1 i))
      (Measure.map (boxTripleFun (n := n) i) νt) := by
    rw [hνt]; rw [hpeel.map_eq]; exact hG'.aestronglyMeasurable
  have key1 : (∫ p : X (n + 1) × ℝ³, G p.1 p.2
        ∂((boxMeas (n + 1) s).prod (cubeMeas s)))
      = ∫ q, (fun p : X (n + 1) × ℝ³ => G p.1 p.2) (boxTripleFun (n := n) i q) ∂νt := by
    have hm : Measure.map (boxTripleFun (n := n) i) νt
        = (boxMeas (n + 1) s).prod (cubeMeas s) := by
      rw [hνt]; exact hpeel.map_eq
    rw [← hm]
    exact integral_map (φ := boxTripleFun (n := n) i) hpeel.aemeasurable hf1
  have key2 : (∫ p : X (n + 1) × ℝ³, G (Function.update p.1 i p.2) (p.1 i)
        ∂((boxMeas (n + 1) s).prod (cubeMeas s)))
      = ∫ q, (fun p : X (n + 1) × ℝ³ =>
          G (Function.update p.1 i p.2) (p.1 i)) (boxTripleFun (n := n) i q) ∂νt := by
    have hm : Measure.map (boxTripleFun (n := n) i) νt
        = (boxMeas (n + 1) s).prod (cubeMeas s) := by
      rw [hνt]; exact hpeel.map_eq
    rw [← hm]
    exact integral_map (φ := boxTripleFun (n := n) i) hpeel.aemeasurable hf2
  have hpt1 : ∀ q : X n × (ℝ³ × ℝ³),
      (fun p : X (n + 1) × ℝ³ => G (Function.update p.1 i p.2) (p.1 i))
          (boxTripleFun (n := n) i q) = G (kcInsN n i (q.2.2, q.1)) q.2.1 := by
    rintro ⟨r, a, b⟩
    simp only [boxTripleFun_apply, update_kcInsN, kc_insN_apply_same]
  have hpt2 : ∀ q : X n × (ℝ³ × ℝ³),
      (fun p : X (n + 1) × ℝ³ => G p.1 p.2)
          (boxTripleFun (n := n) i q) = G (kcInsN n i (q.2.1, q.1)) q.2.2 := by
    rintro ⟨r, a, b⟩
    simp only [boxTripleFun_apply]
  rw [hL, hR, key2, key1]
  rw [show (∫ q, (fun p : X (n + 1) × ℝ³ => G p.1 p.2)
        (boxTripleFun (n := n) i q) ∂νt)
      = ∫ q, G (kcInsN n i (q.2.1, q.1)) q.2.2 ∂νt from
    integral_congr_ae (Filter.Eventually.of_forall hpt2)]
  rw [show (∫ q, (fun p : X (n + 1) × ℝ³ => G (Function.update p.1 i p.2) (p.1 i))
        (boxTripleFun (n := n) i q) ∂νt)
      = ∫ q, G (kcInsN n i (q.2.2, q.1)) q.2.1 ∂νt from
    integral_congr_ae (Filter.Eventually.of_forall hpt1)]
  rw [← MeasurePreserving.integral_comp' (pairSwapEquiv_measurePreserving (s := s) (n := n))
      (fun q : X n × (ℝ³ × ℝ³) => G (kcInsN n i (q.2.1, q.1)) q.2.2)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun q => ?_))
  obtain ⟨r, a, b⟩ := q
  simp only [pairSwapEquiv_apply]


/-! ## 1. The mode operator `boxOp` -/

/-- The one-body mode operator `a†(f)a(h)` in the corpus's position-slot language. -/
noncomputable def boxOp (s : ℝ) {N : ℕ} (f h : ℝ³ → ℝ) (Ψ : X N → ℝ) (x : X N) : ℝ :=
  ∑ i : Fin N, f (x i) * ∫ z in acube s, h z * Ψ (Function.update x i z)

/-- `boxOp s g 1 = √(s³) • tauDag s g`. -/
lemma boxOp_eq_tauDag {s : ℝ} (hs : 0 < s) {N : ℕ} (g : ℝ³ → ℝ) (Ψ : X N → ℝ)
    (x : X N) :
    boxOp s g (fun _ => (1 : ℝ)) Ψ x = Real.sqrt (s ^ 3) * tauDag s g Ψ x := by
  have hsp : (0 : ℝ) < Real.sqrt (s ^ 3) := Real.sqrt_pos_of_pos (by positivity)
  simp only [boxOp, one_mul, tauDag, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show Real.sqrt (s ^ 3) * ((Real.sqrt (s ^ 3))⁻¹ *
      (g (x i) * ∫ z in acube s, Ψ (Function.update x i z)))
      = (Real.sqrt (s ^ 3) * (Real.sqrt (s ^ 3))⁻¹) *
        (g (x i) * ∫ z in acube s, Ψ (Function.update x i z)) by ring,
    mul_inv_cancel₀ (ne_of_gt hsp), one_mul]

/-- `boxOp s 1 g = √(s³) • tauAnn s g`. -/
lemma boxOp_eq_tauAnn {s : ℝ} (hs : 0 < s) {N : ℕ} (g : ℝ³ → ℝ) (Ψ : X N → ℝ)
    (x : X N) :
    boxOp s (fun _ => (1 : ℝ)) g Ψ x = Real.sqrt (s ^ 3) * tauAnn s g Ψ x := by
  have hsp : (0 : ℝ) < Real.sqrt (s ^ 3) := Real.sqrt_pos_of_pos (by positivity)
  simp only [boxOp, tauAnn, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show Real.sqrt (s ^ 3) * ((Real.sqrt (s ^ 3))⁻¹ *
      ∫ z in acube s, g z * Ψ (Function.update x i z))
      = (Real.sqrt (s ^ 3) * (Real.sqrt (s ^ 3))⁻¹) *
        ∫ z in acube s, g z * Ψ (Function.update x i z) by ring,
    mul_inv_cancel₀ (ne_of_gt hsp), one_mul]

/-- `boxOp s 1 1 Ψ x = |B| Σ_i P_i Ψ x`. -/
lemma boxOp_one_one {s : ℝ} (hs : s ≠ 0) {N : ℕ} (Ψ : X N → ℝ) (x : X N) :
    boxOp s (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x
      = s ^ 3 * ∑ i : Fin N, aP s i Ψ x := by
  simp only [boxOp, one_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => acube_integral_update_eq hs i Ψ x)

/-- `update (update x i z) i (x i) = x`. -/
lemma update_update_self {N : ℕ} (x : X N) (i : Fin N) (z : ℝ³) :
    Function.update (Function.update x i z) i (x i) = x := by
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · rw [Function.update_apply, if_neg hj, Function.update_apply, if_neg hj]

/-! ## 2. Integrability toolbox -/

/-- sup bound for a continuous-kernel inner integral -/
lemma abs_inner_le {s : ℝ} (hs : 0 < s) {n : ℕ}
    {K : X (n + 1) × ℝ³ → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ p ∈ abox (n + 1) s ×ˢ acube s, ‖K p‖ ≤ C) :
    ∀ x ∈ abox (n + 1) s, ‖∫ z in acube s, K (x, z)‖ ≤ C * s ^ 3 := by
  intro x hx
  haveI : IsFiniteMeasure (cubeMeas s) := isFiniteMeasure_cubeMeas hs
  have hmaj : Integrable (fun _ : ℝ³ => C) (cubeMeas s) := integrable_const _
  calc ‖∫ z in acube s, K (x, z)‖
      ≤ ∫ z in acube s, ‖K (x, z)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in acube s, C := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _) hmaj ?_
        filter_upwards [ae_restrict_mem (acube_measurable s)] with z hz
        exact hC (x, z) ⟨hx, hz⟩
    _ = C * s ^ 3 := integral_const_acube s hs C

/-- the inner integral of a continuous kernel is integrable on the box -/
lemma integrable_inner {s : ℝ} (hs : 0 < s) {n : ℕ}
    {K : X (n + 1) × ℝ³ → ℝ} (hK : Continuous K) :
    Integrable (fun x : X (n + 1) => ∫ z in acube s, K (x, z)) (boxMeas (n + 1) s) := by
  haveI : IsFiniteMeasure (cubeMeas s) := isFiniteMeasure_cubeMeas hs
  haveI : IsFiniteMeasure (boxMeas (n + 1) s) := isFiniteMeasure_boxMeas hs
  obtain ⟨C3, hC3⟩ := ((abox_compact (n + 1) hs).prod (acube_compact hs)).exists_bound_of_continuousOn
    (s := abox (n + 1) s ×ˢ acube s) (f := K) hK.continuousOn
  have hbdd : ∀ᵐ p ∂((boxMeas (n + 1) s).prod (cubeMeas s)), ‖K p‖ ≤ max C3 0 := by
    filter_upwards [ae_mem_box_prod hs] with p hp
    exact le_trans (hC3 p hp) (le_max_left _ _)
  exact (Integrable.of_bound hK.aestronglyMeasurable (max C3 0) hbdd).integral_prod_left

/-- sup bound for `A (x i) * ∫_z K (x,z)` -/
lemma abs_inner_mul_le {s : ℝ} (hs : 0 < s) {n : ℕ} (i : Fin (n + 1))
    {A : ℝ³ → ℝ} {K : X (n + 1) × ℝ³ → ℝ} {C2 C3 : ℝ} (hC20 : 0 ≤ C2) (hC30 : 0 ≤ C3)
    (hA : ∀ y ∈ acube s, ‖A y‖ ≤ C2)
    (hK : ∀ p ∈ abox (n + 1) s ×ˢ acube s, ‖K p‖ ≤ C3) :
    ∀ x ∈ abox (n + 1) s, ‖A (x i) * ∫ z in acube s, K (x, z)‖ ≤ C2 * (C3 * s ^ 3) := by
  intro x hx
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hA (x i) (hx i)) (abs_inner_le hs hC30 hK x hx) (abs_nonneg _) hC20

/-- `B x * (A (x i) * ∫_z K (x,z))` is integrable on the box -/
lemma integrable_slot_left {s : ℝ} (hs : 0 < s) {n : ℕ} (i : Fin (n + 1))
    {A : ℝ³ → ℝ} (hA : Continuous A) {K : X (n + 1) × ℝ³ → ℝ} (hK : Continuous K)
    {B : X (n + 1) → ℝ} (hB : Continuous B) :
    Integrable (fun x : X (n + 1) => B x * (A (x i) * ∫ z in acube s, K (x, z)))
      (boxMeas (n + 1) s) := by
  haveI : IsFiniteMeasure (cubeMeas s) := isFiniteMeasure_cubeMeas hs
  haveI : IsFiniteMeasure (boxMeas (n + 1) s) := isFiniteMeasure_boxMeas hs
  obtain ⟨C1, hC1⟩ := (abox_compact (n + 1) hs).exists_bound_of_continuousOn
    (s := abox (n + 1) s) (f := B) hB.continuousOn
  obtain ⟨C2, hC2⟩ := (acube_compact hs).exists_bound_of_continuousOn (f := A) hA.continuousOn
  obtain ⟨C3, hC3⟩ := ((abox_compact (n + 1) hs).prod (acube_compact hs)).exists_bound_of_continuousOn
    (s := abox (n + 1) s ×ˢ acube s) (f := K) hK.continuousOn
  refine Integrable.of_bound (hB.aestronglyMeasurable.mul
    (((hA.comp (continuous_apply (A := fun _ : Fin (n + 1) => ℝ³) i)).aestronglyMeasurable).mul
      (integrable_inner hs hK).aestronglyMeasurable)) (max C1 0 * (max C2 0 * (max C3 0 * s ^ 3))) ?_
  filter_upwards [ae_restrict_mem (abox_measurable (n + 1) s)] with x hx
  have h1 : |B x| ≤ max C1 0 := le_trans (hC1 x hx) (le_max_left _ _)
  have h2 : |A (x i) * ∫ z in acube s, K (x, z)|
      ≤ max C2 0 * (max C3 0 * s ^ 3) :=
    abs_inner_mul_le hs i (le_max_right C2 0) (le_max_right C3 0)
      (fun y hy => le_trans (hC2 y hy) (le_max_left _ _))
      (fun p hp => le_trans (hC3 p hp) (le_max_left _ _)) x hx
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) (le_max_right _ _)

/-- `(A (x i) * ∫_z K (x,z)) * B x` is integrable on the box -/
lemma integrable_slot_right {s : ℝ} (hs : 0 < s) {n : ℕ} (i : Fin (n + 1))
    {A : ℝ³ → ℝ} (hA : Continuous A) {K : X (n + 1) × ℝ³ → ℝ} (hK : Continuous K)
    {B : X (n + 1) → ℝ} (hB : Continuous B) :
    Integrable (fun x : X (n + 1) => (A (x i) * ∫ z in acube s, K (x, z)) * B x)
      (boxMeas (n + 1) s) := by
  haveI : IsFiniteMeasure (cubeMeas s) := isFiniteMeasure_cubeMeas hs
  haveI : IsFiniteMeasure (boxMeas (n + 1) s) := isFiniteMeasure_boxMeas hs
  obtain ⟨C1, hC1⟩ := (abox_compact (n + 1) hs).exists_bound_of_continuousOn
    (s := abox (n + 1) s) (f := B) hB.continuousOn
  obtain ⟨C2, hC2⟩ := (acube_compact hs).exists_bound_of_continuousOn (f := A) hA.continuousOn
  obtain ⟨C3, hC3⟩ := ((abox_compact (n + 1) hs).prod (acube_compact hs)).exists_bound_of_continuousOn
    (s := abox (n + 1) s ×ˢ acube s) (f := K) hK.continuousOn
  refine Integrable.of_bound ((((hA.comp (continuous_apply (A := fun _ : Fin (n + 1) => ℝ³) i)).aestronglyMeasurable).mul
      (integrable_inner hs hK).aestronglyMeasurable).mul hB.aestronglyMeasurable)
    ((max C2 0 * (max C3 0 * s ^ 3)) * max C1 0) ?_
  filter_upwards [ae_restrict_mem (abox_measurable (n + 1) s)] with x hx
  have h1 : |B x| ≤ max C1 0 := le_trans (hC1 x hx) (le_max_left _ _)
  have h2 : |A (x i) * ∫ z in acube s, K (x, z)|
      ≤ max C2 0 * (max C3 0 * s ^ 3) :=
    abs_inner_mul_le hs i (le_max_right C2 0) (le_max_right C3 0)
      (fun y hy => le_trans (hC2 y hy) (le_max_left _ _))
      (fun p hp => le_trans (hC3 p hp) (le_max_left _ _)) x hx
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul h2 h1 (abs_nonneg _) (by positivity)

/-! ## 3. Adjointness of `boxOp` -/

/-- per-slot adjointness identity -/
lemma boxOp_slot_adjoint {s : ℝ} (hs : 0 < s) {n : ℕ} (i : Fin (n + 1)) {f h : ℝ³ → ℝ}
    (hf : Continuous f) (hh : Continuous h) {Φ Ψ : X (n + 1) → ℝ}
    (hΦ : Continuous Φ) (hΨ : Continuous Ψ) :
    (∫ x in abox (n + 1) s,
        Φ x * (f (x i) * ∫ z in acube s, h z * Ψ (Function.update x i z)))
      = ∫ x in abox (n + 1) s,
        h (x i) * (∫ z in acube s, Φ (Function.update x i z) * f z) * Ψ x := by
  have hGc : Continuous fun p : X (n + 1) × ℝ³ =>
      Φ p.1 * f (p.1 i) * (h p.2 * Ψ (Function.update p.1 i p.2)) := by
    refine (((hΦ.comp continuous_fst).mul ?_).mul
      ((hh.comp continuous_snd).mul (hΨ.comp (continuous_fst.update i continuous_snd))))
    exact (hf.comp ((continuous_apply (A := fun _ : Fin (n + 1) => ℝ³) i).comp continuous_fst))
  have step1 : (∫ x in abox (n + 1) s,
        Φ x * (f (x i) * ∫ z in acube s, h z * Ψ (Function.update x i z)))
      = ∫ x in abox (n + 1) s, ∫ z in acube s,
          Φ x * f (x i) * (h z * Ψ (Function.update x i z)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Φ x * (f (x i) * ∫ z in acube s, h z * Ψ (Function.update x i z))
      = ∫ z in acube s, Φ x * f (x i) * (h z * Ψ (Function.update x i z))
    rw [integral_const_mul]
    ring
  rw [step1]
  rw [integral_swap_update hs i
    (fun x z => Φ x * f (x i) * (h z * Ψ (Function.update x i z))) hGc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only []
  rw [show (fun z => Φ (Function.update x i z) * f ((Function.update x i z) i) *
        (h (x i) * Ψ (Function.update (Function.update x i z) i (x i))))
      = fun z => Φ (Function.update x i z) * f z * (h (x i) * Ψ x) by
    funext z
    rw [Function.update_self, update_update_self]]
  rw [integral_mul_const]
  ring

/-- **adjointness**: `boxOp s h f` is the adjoint of `boxOp s f h`. -/
theorem boxOp_adjoint {s : ℝ} (hs : 0 < s) {n : ℕ} {f h : ℝ³ → ℝ}
    (hf : Continuous f) (hh : Continuous h) {Φ Ψ : X (n + 1) → ℝ}
    (hΦ : Continuous Φ) (hΨ : Continuous Ψ) :
    (∫ x in abox (n + 1) s, Φ x * boxOp s f h Ψ x)
      = ∫ x in abox (n + 1) s, boxOp s h f Φ x * Ψ x := by
  have hL : (∫ x in abox (n + 1) s, Φ x * boxOp s f h Ψ x)
      = ∑ i : Fin (n + 1), ∫ x in abox (n + 1) s,
          Φ x * (f (x i) * ∫ z in acube s, h z * Ψ (Function.update x i z)) := by
    rw [show (fun x => Φ x * boxOp s f h Ψ x) = fun x =>
        ∑ i : Fin (n + 1), Φ x *
          (f (x i) * ∫ z in acube s, h z * Ψ (Function.update x i z)) by
      funext x; rw [boxOp, Finset.mul_sum]]
    refine integral_finsetSum _ (fun i _ => ?_)
    exact integrable_slot_left hs i hf
      ((hh.comp continuous_snd).mul (hΨ.comp (continuous_fst.update i continuous_snd))) hΦ
  have hR : (∫ x in abox (n + 1) s, boxOp s h f Φ x * Ψ x)
      = ∑ i : Fin (n + 1), ∫ x in abox (n + 1) s,
          h (x i) * (∫ z in acube s, Φ (Function.update x i z) * f z) * Ψ x := by
    rw [show (fun x => boxOp s h f Φ x * Ψ x) = fun x =>
        ∑ i : Fin (n + 1),
          h (x i) * (∫ z in acube s, Φ (Function.update x i z) * f z) * Ψ x by
      funext x
      rw [boxOp, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have : (∫ z in acube s, f z * Φ (Function.update x i z))
          = ∫ z in acube s, Φ (Function.update x i z) * f z :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
      rw [this]]
    refine integral_finsetSum _ (fun i _ => ?_)
    exact integrable_slot_right hs i hh
      ((hΦ.comp (continuous_fst.update i continuous_snd)).mul (hf.comp continuous_snd)) hΨ
  rw [hL, hR]
  exact Finset.sum_congr rfl (fun i _ => boxOp_slot_adjoint hs i hf hh hΦ hΨ)


/-! ## 4. The composition rule and the double operator -/

/-- `update (update x i z) i w = update x i w`. -/
lemma update_update_same {N : ℕ} (x : X N) (i : Fin N) (z w : ℝ³) :
    Function.update (Function.update x i z) i w = Function.update x i w := by
  ext k
  rw [Function.update_apply]
  by_cases hk : k = i
  · subst hk; simp
  · simp [Function.update_apply, hk]

/-- exchanging the two slots of an off-diagonal double sum -/
lemma sum_erase_swap {N : ℕ} {R : Type*} [AddCommMonoid R] (B : Fin N → Fin N → R) :
    (∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, B i j)
      = ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, B j i := by
  have h1 : ∀ i : Fin N, (∑ j ∈ Finset.univ.erase i, B i j)
      = ∑ j : Fin N, if j = i then 0 else B i j := by
    intro i
    rw [show Finset.univ.erase i = Finset.univ.filter (fun j => j ≠ i) from by
      ext j; simp [Finset.mem_erase]]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : j ≠ i
    · rw [if_pos h, if_neg h]
    · rw [if_neg h, if_pos (not_not.mp h)]
  have h2 : ∀ i : Fin N, (∑ j ∈ Finset.univ.erase i, B j i)
      = ∑ j : Fin N, if j = i then 0 else B j i := by
    intro i
    rw [show Finset.univ.erase i = Finset.univ.filter (fun j => j ≠ i) from by
      ext j; simp [Finset.mem_erase]]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : j ≠ i
    · rw [if_pos h, if_neg h]
    · rw [if_neg h, if_pos (not_not.mp h)]
  simp only [h1, h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [eq_comm]

/-- the two-slot (off-diagonal) part of a composition -/
noncomputable def boxOp2 (s : ℝ) {N : ℕ} (f h f' h' : ℝ³ → ℝ) (Ψ : X N → ℝ) (x : X N) : ℝ :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
    f (x i) * f' (x j) *
      ∫ z in acube s, h z *
        (∫ w in acube s, h' w * Ψ (Function.update (Function.update x i z) j w))

/-- a.e. membership in the cube product -/
lemma ae_mem_cube_prod {s : ℝ} (hs : 0 < s) :
    ∀ᵐ p ∂((cubeMeas s).prod (cubeMeas s)), p.1 ∈ acube s ∧ p.2 ∈ acube s := by
  haveI : IsFiniteMeasure (cubeMeas s) := isFiniteMeasure_cubeMeas hs
  have h : ∀ᵐ p ∂((cubeMeas s).prod (cubeMeas s)), p ∈ acube s ×ˢ acube s := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem ((acube_measurable s).prod (acube_measurable s))
  filter_upwards [h] with p hp using hp

/-- sup bound for a two-variable kernel's cube integral -/
lemma abs_inner_le_cube {s : ℝ} (hs : 0 < s) {K : ℝ³ → ℝ³ → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ z ∈ acube s, ∀ w ∈ acube s, ‖K z w‖ ≤ C) :
    ∀ z ∈ acube s, ‖∫ w in acube s, K z w‖ ≤ C * s ^ 3 := by
  intro z hz
  haveI : IsFiniteMeasure (cubeMeas s) := isFiniteMeasure_cubeMeas hs
  have hmaj : Integrable (fun _ : ℝ³ => C) (cubeMeas s) := integrable_const _
  calc ‖∫ w in acube s, K z w‖ ≤ ∫ w in acube s, ‖K z w‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ w in acube s, C := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => norm_nonneg _) hmaj ?_
        filter_upwards [ae_restrict_mem (acube_measurable s)] with w hw
        exact hC z hz w hw
    _ = C * s ^ 3 := integral_const_acube s hs C

/-- `z ↦ h z * ∫_w h' w Ψ (x_{i←z,j←w})` is integrable on the cube -/
lemma integrable_cube_slot {s : ℝ} (hs : 0 < s) {n : ℕ} (i j : Fin (n + 1))
    {h h' : ℝ³ → ℝ} (hh : Continuous h) (hh' : Continuous h')
    {Ψ : X (n + 1) → ℝ} (hΨ : Continuous Ψ) {x : X (n + 1)} (hx : x ∈ abox (n + 1) s) :
    Integrable (fun z : ℝ³ => h z *
        (∫ w in acube s, h' w * Ψ (Function.update (Function.update x i z) j w)))
      (cubeMeas s) := by
  haveI : IsFiniteMeasure (cubeMeas s) := isFiniteMeasure_cubeMeas hs
  obtain ⟨C1, hC1⟩ := (acube_compact hs).exists_bound_of_continuousOn (f := h) hh.continuousOn
  obtain ⟨C2, hC2⟩ := (acube_compact hs).exists_bound_of_continuousOn (f := h') hh'.continuousOn
  obtain ⟨C3, hC3⟩ := (abox_compact (n + 1) hs).exists_bound_of_continuousOn
    (s := abox (n + 1) s) (f := Ψ) hΨ.continuousOn
  have hupd : Continuous fun p : ℝ³ × ℝ³ =>
      Function.update (Function.update x i p.1) j p.2 := by
    have h1 : Continuous fun p : ℝ³ × ℝ³ => Function.update x i p.1 :=
      (continuous_const (y := x)).update i continuous_fst
    exact h1.update j continuous_snd
  have hK : Continuous fun p : ℝ³ × ℝ³ =>
      h' p.2 * Ψ (Function.update (Function.update x i p.1) j p.2) :=
    (hh'.comp continuous_snd).mul (hΨ.comp hupd)
  have hbdd : ∀ᵐ p ∂((cubeMeas s).prod (cubeMeas s)),
      ‖h' p.2 * Ψ (Function.update (Function.update x i p.1) j p.2)‖ ≤ max C2 0 * max C3 0 := by
    filter_upwards [ae_mem_cube_prod hs] with p hp
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (le_trans (hC2 p.2 hp.2) (le_max_left _ _))
      (le_trans (hC3 _ ?_) (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
    exact update_mem_abox_of_mem j (update_mem_abox_of_mem i hx hp.1) hp.2
  have hinner : Integrable (fun z : ℝ³ =>
      ∫ w in acube s, h' w * Ψ (Function.update (Function.update x i z) j w)) (cubeMeas s) :=
    (Integrable.of_bound hK.aestronglyMeasurable (max C2 0 * max C3 0) hbdd).integral_prod_left
  refine Integrable.of_bound (hh.aestronglyMeasurable.mul hinner.aestronglyMeasurable)
    (max C1 0 * ((max C2 0 * max C3 0) * s ^ 3)) ?_
  filter_upwards [ae_restrict_mem (acube_measurable s)] with z hz
  have h1 : |h z| ≤ max C1 0 := le_trans (hC1 z hz) (le_max_left _ _)
  have h2 : |∫ w in acube s, h' w * Ψ (Function.update (Function.update x i z) j w)|
      ≤ (max C2 0 * max C3 0) * s ^ 3 := by
    rw [← Real.norm_eq_abs]
    refine abs_inner_le_cube (K := fun z w =>
      h' w * Ψ (Function.update (Function.update x i z) j w)) hs
      (mul_nonneg (le_max_right C2 0) (le_max_right C3 0)) (fun z' hz' w hw => ?_) z hz
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (le_trans (hC2 w hw) (le_max_left _ _))
      (le_trans (hC3 _ (update_mem_abox_of_mem j (update_mem_abox_of_mem i hx hz') hw))
        (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) (le_max_right _ _)

/-- **per-slot composition rule** -/
lemma boxOp_slot_comp {s : ℝ} (hs : 0 < s) {n : ℕ} (i : Fin (n + 1))
    {h h' : ℝ³ → ℝ} (hh : Continuous h) (hh' : Continuous h')
    {f' : ℝ³ → ℝ} (hf' : Continuous f') {Ψ : X (n + 1) → ℝ} (hΨ : Continuous Ψ)
    {x : X (n + 1)} (hx : x ∈ abox (n + 1) s) :
    (∫ z in acube s, h z * boxOp s f' h' Ψ (Function.update x i z))
      = (∫ z in acube s, h z * f' z) * (∫ w in acube s, h' w * Ψ (Function.update x i w))
        + ∑ j ∈ Finset.univ.erase i, f' (x j) *
            ∫ z in acube s, h z * (∫ w in acube s, h' w *
              Ψ (Function.update (Function.update x i z) j w)) := by
  haveI : IsFiniteMeasure (cubeMeas s) := isFiniteMeasure_cubeMeas hs
  have hdiag : Integrable (fun z : ℝ³ => h z * f' z) (cubeMeas s) :=
    ContinuousOn.integrableOn_compact (acube_compact hs) (hh.mul hf').continuousOn
  have hsplit : ∀ z : ℝ³, boxOp s f' h' Ψ (Function.update x i z)
        = f' z * (∫ w in acube s, h' w * Ψ (Function.update x i w))
          + ∑ j ∈ Finset.univ.erase i, f' (x j) *
              ∫ w in acube s, h' w * Ψ (Function.update (Function.update x i z) j w) := by
    intro z
    rw [boxOp, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_comm]
    congr 1
    · rw [Function.update_self]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only []
      rw [update_update_same]
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Function.update_apply, if_neg (Finset.mem_erase.mp hj).1]
  set K : ℝ := ∫ w in acube s, h' w * Ψ (Function.update x i w) with hK
  set H : Fin (n + 1) → ℝ³ → ℝ := fun j z =>
    h z * (∫ w in acube s, h' w * Ψ (Function.update (Function.update x i z) j w)) with hH
  have hHint : ∀ j ∈ Finset.univ.erase i, Integrable (H j) (cubeMeas s) :=
    fun j _ => integrable_cube_slot hs i j hh hh' hΨ hx
  have hrewrite : (fun z => h z * boxOp s f' h' Ψ (Function.update x i z)) = fun z =>
      (h z * f' z) * K + ∑ j ∈ Finset.univ.erase i, f' (x j) * H j z := by
    funext z
    rw [hsplit, hK, hH]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl (fun j _ => ?_); ring
  rw [hrewrite, integral_add (hdiag.mul_const K)
    (integrable_finsetSum _ (fun j hj => (hHint j hj).const_mul _))]
  congr 1
  · rw [integral_mul_const]
  · rw [integral_finsetSum _ (fun j hj => (hHint j hj).const_mul _)]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [integral_const_mul]


/-- **the composition rule** -/
lemma boxOp_comp {s : ℝ} (hs : 0 < s) {n : ℕ} {f h f' h' : ℝ³ → ℝ}
    (hf : Continuous f) (hh : Continuous h) (hf' : Continuous f') (hh' : Continuous h')
    {Ψ : X (n + 1) → ℝ} (hΨ : Continuous Ψ) {x : X (n + 1)} (hx : x ∈ abox (n + 1) s) :
    boxOp s f h (boxOp s f' h' Ψ) x
      = (∫ z in acube s, h z * f' z) * boxOp s f h' Ψ x + boxOp2 s f h f' h' Ψ x := by
  have hstep : ∀ i : Fin (n + 1),
      f (x i) * (∫ z in acube s, h z * boxOp s f' h' Ψ (Function.update x i z))
        = (∫ z in acube s, h z * f' z) *
            (f (x i) * ∫ w in acube s, h' w * Ψ (Function.update x i w))
          + ∑ j ∈ Finset.univ.erase i, f (x i) * f' (x j) *
              ∫ z in acube s, h z * (∫ w in acube s, h' w *
                Ψ (Function.update (Function.update x i z) j w)) := by
    intro i
    rw [boxOp_slot_comp hs i hh hh' hf' hΨ hx, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl (fun j _ => ?_); ring
  simp only [boxOp, boxOp2]
  rw [show (∑ i : Fin (n + 1), f (x i) * ∫ z in acube s, h z *
        (∑ j : Fin (n + 1), f' (Function.update x i z j) * ∫ w in acube s, h' w *
          Ψ (Function.update (Function.update x i z) j w)))
      = ∑ i : Fin (n + 1),
          ((∫ z in acube s, h z * f' z) *
              (f (x i) * ∫ w in acube s, h' w * Ψ (Function.update x i w))
            + ∑ j ∈ Finset.univ.erase i, f (x i) * f' (x j) *
                ∫ z in acube s, h z * (∫ w in acube s, h' w *
                  Ψ (Function.update (Function.update x i z) j w))) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (fun z => h z * (∑ j : Fin (n + 1), f' (Function.update x i z j) *
          ∫ w in acube s, h' w * Ψ (Function.update (Function.update x i z) j w)))
        = fun z => h z * boxOp s f' h' Ψ (Function.update x i z) from rfl]
    exact hstep i]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]


/-- the pair integrals of the two orderings agree -/
lemma pair_integral_symm {s : ℝ} (hs : 0 < s) {n : ℕ} {i j : Fin (n + 1)} (hij : i ≠ j)
    {h h' : ℝ³ → ℝ} (hh : Continuous h) (hh' : Continuous h')
    {Ψ : X (n + 1) → ℝ} (hΨ : Continuous Ψ) {x : X (n + 1)} (hx : x ∈ abox (n + 1) s) :
    (∫ z in acube s, h' z * (∫ w in acube s, h w *
        Ψ (Function.update (Function.update x j z) i w)))
      = ∫ z in acube s, h z * (∫ w in acube s, h' w *
          Ψ (Function.update (Function.update x i z) j w)) := by
  haveI : IsFiniteMeasure (cubeMeas s) := isFiniteMeasure_cubeMeas hs
  obtain ⟨C1, hC1⟩ := (acube_compact hs).exists_bound_of_continuousOn (f := h) hh.continuousOn
  obtain ⟨C2, hC2⟩ := (acube_compact hs).exists_bound_of_continuousOn (f := h') hh'.continuousOn
  obtain ⟨C3, hC3⟩ := (abox_compact (n + 1) hs).exists_bound_of_continuousOn
    (s := abox (n + 1) s) (f := Ψ) hΨ.continuousOn
  have hInt : ∀ {K : ℝ³ × ℝ³ → ℝ} (C : ℝ), Continuous K →
      (∀ᵐ p ∂((cubeMeas s).prod (cubeMeas s)), ‖K p‖ ≤ C) →
      Integrable K ((cubeMeas s).prod (cubeMeas s)) :=
    fun C hK hb => Integrable.of_bound hK.aestronglyMeasurable C hb
  have hK1 : Continuous fun p : ℝ³ × ℝ³ => h' p.1 * (h p.2 *
      Ψ (Function.update (Function.update x j p.1) i p.2)) := by
    have hupd : Continuous fun p : ℝ³ × ℝ³ =>
        Function.update (Function.update x j p.1) i p.2 :=
      ((continuous_const (y := x)).update j continuous_fst).update i continuous_snd
    exact (hh'.comp continuous_fst).mul ((hh.comp continuous_snd).mul (hΨ.comp hupd))
  have hb1 : ∀ᵐ p ∂((cubeMeas s).prod (cubeMeas s)),
      ‖h' p.1 * (h p.2 * Ψ (Function.update (Function.update x j p.1) i p.2))‖
        ≤ max C2 0 * (max C1 0 * max C3 0) := by
    filter_upwards [ae_mem_cube_prod hs] with p hp
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul (le_trans (hC2 p.1 hp.1) (le_max_left _ _))
      (mul_le_mul (le_trans (hC1 p.2 hp.2) (le_max_left _ _))
        (le_trans (hC3 _ (update_mem_abox_of_mem i (update_mem_abox_of_mem j hx hp.1) hp.2))
          (le_max_left _ _)) (by positivity) (le_max_right _ _))
      (by positivity) (le_max_right _ _)
  have hK2 : Continuous fun p : ℝ³ × ℝ³ => h p.1 * (h' p.2 *
      Ψ (Function.update (Function.update x i p.1) j p.2)) := by
    have hupd : Continuous fun p : ℝ³ × ℝ³ =>
        Function.update (Function.update x i p.1) j p.2 :=
      ((continuous_const (y := x)).update i continuous_fst).update j continuous_snd
    exact (hh.comp continuous_fst).mul ((hh'.comp continuous_snd).mul (hΨ.comp hupd))
  have hb2 : ∀ᵐ p ∂((cubeMeas s).prod (cubeMeas s)),
      ‖h p.1 * (h' p.2 * Ψ (Function.update (Function.update x i p.1) j p.2))‖
        ≤ max C1 0 * (max C2 0 * max C3 0) := by
    filter_upwards [ae_mem_cube_prod hs] with p hp
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul (le_trans (hC1 p.1 hp.1) (le_max_left _ _))
      (mul_le_mul (le_trans (hC2 p.2 hp.2) (le_max_left _ _))
        (le_trans (hC3 _ (update_mem_abox_of_mem j (update_mem_abox_of_mem i hx hp.1) hp.2))
          (le_max_left _ _)) (by positivity) (le_max_right _ _))
      (by positivity) (le_max_right _ _)
  have h1 : (∫ z in acube s, h' z * (∫ w in acube s, h w *
        Ψ (Function.update (Function.update x j z) i w)))
      = ∫ p : ℝ³ × ℝ³, h' p.1 * (h p.2 *
          Ψ (Function.update (Function.update x j p.1) i p.2))
        ∂((cubeMeas s).prod (cubeMeas s)) := by
    have hinner : ∀ z, h' z * (∫ w in acube s, h w *
          Ψ (Function.update (Function.update x j z) i w))
        = ∫ w in acube s, h' z * (h w * Ψ (Function.update (Function.update x j z) i w)) := by
      intro z; rw [integral_const_mul]
    simp only [hinner]
    exact (integral_prod _ (hInt _ hK1 hb1)).symm
  have h2 : (∫ z in acube s, h z * (∫ w in acube s, h' w *
        Ψ (Function.update (Function.update x i z) j w)))
      = ∫ p : ℝ³ × ℝ³, h p.1 * (h' p.2 *
          Ψ (Function.update (Function.update x i p.1) j p.2))
        ∂((cubeMeas s).prod (cubeMeas s)) := by
    have hinner : ∀ z, h z * (∫ w in acube s, h' w *
          Ψ (Function.update (Function.update x i z) j w))
        = ∫ w in acube s, h z * (h' w * Ψ (Function.update (Function.update x i z) j w)) := by
      intro z; rw [integral_const_mul]
    simp only [hinner]
    exact (integral_prod _ (hInt _ hK2 hb2)).symm
  rw [h1, h2]
  rw [← integral_prod_swap (μ := cubeMeas s) (ν := cubeMeas s)
      (f := fun p : ℝ³ × ℝ³ => h p.1 * (h' p.2 *
        Ψ (Function.update (Function.update x i p.1) j p.2)))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  obtain ⟨z, w⟩ := p
  simp only [Prod.swap_prod_mk]
  rw [show Function.update (Function.update x j z) i w
      = Function.update (Function.update x i w) j z from
    Function.update_comm (Ne.symm hij) z w x]
  ring

/-- **symmetry of the double operator** -/
lemma boxOp2_symm {s : ℝ} (hs : 0 < s) {n : ℕ} {f h f' h' : ℝ³ → ℝ}
    (hh : Continuous h) (hh' : Continuous h') {Ψ : X (n + 1) → ℝ} (hΨ : Continuous Ψ)
    {x : X (n + 1)} (hx : x ∈ abox (n + 1) s) :
    boxOp2 s f h f' h' Ψ x = boxOp2 s f' h' f h Ψ x := by
  simp only [boxOp2]
  rw [sum_erase_swap (fun i j : Fin (n + 1) => f' (x i) * f (x j) *
      ∫ z in acube s, h' z * (∫ w in acube s, h w *
        Ψ (Function.update (Function.update x i z) j w)))]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j hj => ?_))
  rw [pair_integral_symm hs (Ne.symm (Finset.mem_erase.mp hj).1) hh hh' hΨ hx]
  ring

/-- **the commutator identity**: `a†(g)a(χ)a†(χ)a(g) − a†(χ)a(g)a†(g)a(χ)` -/
lemma boxOp_commutator {s : ℝ} (hs : 0 < s) {n : ℕ} {g : ℝ³ → ℝ} (hg : Continuous g)
    {Ψ : X (n + 1) → ℝ} (hΨ : Continuous Ψ) {x : X (n + 1)} (hx : x ∈ abox (n + 1) s) :
    boxOp s (fun _ => (1 : ℝ)) g (boxOp s g (fun _ => (1 : ℝ)) Ψ) x
        - boxOp s g (fun _ => (1 : ℝ)) (boxOp s (fun _ => (1 : ℝ)) g Ψ) x
      = (∫ z in acube s, g z * g z) * boxOp s (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x
        - (s ^ 3) * boxOp s g g Ψ x := by
  have hc1 := boxOp_comp hs (f := fun _ => (1 : ℝ)) (h := g) (f' := g) (h' := fun _ => (1 : ℝ))
    continuous_const hg hg continuous_const hΨ hx
  have hc2 := boxOp_comp hs (f := g) (h := fun _ => (1 : ℝ)) (f' := fun _ => (1 : ℝ)) (h' := g)
    hg continuous_const continuous_const hg hΨ hx
  have hsym := boxOp2_symm (f := fun _ => (1 : ℝ)) (h := g) (f' := g) (h' := fun _ => (1 : ℝ))
    (s := s) hs hg continuous_const hΨ hx
  have hconst : (∫ z in acube s, (fun _ => (1 : ℝ)) z * (fun _ => (1 : ℝ)) z) = s ^ 3 := by
    simp only [mul_one]
    simpa using integral_const_acube s hs 1
  rw [hc1, hc2, hsym, hconst]
  ring


/-- continuity of the `boxOp` parametric integral (locally, on a ball) -/
lemma continuousOn_paramIntegral {s : ℝ} (hs : 0 < s) {N : ℕ} (i : Fin N)
    {h : ℝ³ → ℝ} (hh : Continuous h) {Ψ : X N → ℝ} (hΨ : Continuous Ψ) (x : X N) :
    ContinuousOn (fun y : X N => ∫ z in acube s, h z * Ψ (Function.update y i z))
      (Metric.closedBall x 1) := by
  have hupd : Continuous fun p : X N × ℝ³ => Function.update p.1 i p.2 :=
    continuous_fst.update i continuous_snd
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod (acube_compact hs)).exists_bound_of_continuousOn
    (s := Metric.closedBall x 1 ×ˢ acube s)
    (f := fun p : X N × ℝ³ => Ψ (Function.update p.1 i p.2)) (hΨ.comp hupd).continuousOn
  refine continuousOn_of_dominated (μ := cubeMeas s) (bound := fun z => ‖h z‖ * max C 0) ?_ ?_ ?_ ?_
  · intro y _
    exact (hh.mul (hΨ.comp ((continuous_const (y := y)).update i continuous_id))).aestronglyMeasurable
  · intro y hy
    filter_upwards [ae_restrict_mem (acube_measurable s)] with z hz
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (le_refl _) (le_trans (hC (y, z) ⟨hy, hz⟩) (le_max_left _ _))
      (abs_nonneg _) (abs_nonneg _)
  · exact ContinuousOn.integrableOn_compact (acube_compact hs)
      ((hh.norm.mul continuous_const).continuousOn)
  · filter_upwards with z
    exact (((continuous_const (y := h z) : Continuous fun _ : X N => h z)).mul
      (hΨ.comp (continuous_id.update i (continuous_const (y := z))))).continuousOn

/-- continuity of `boxOp` -/
lemma continuous_boxOp {s : ℝ} (hs : 0 < s) {N : ℕ} {f h : ℝ³ → ℝ} (hf : Continuous f)
    (hh : Continuous h) {Ψ : X N → ℝ} (hΨ : Continuous Ψ) : Continuous (boxOp s f h Ψ) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  refine (continuousOn_finsetSum _ (fun i _ => ?_)).continuousAt
    (closedBall_mem_nhds x one_pos)
  exact ((hf.comp (continuous_apply i)).continuousOn).mul
    (continuousOn_paramIntegral hs i hh hΨ x)


/-! ## 5. Positivity, the `P_i`-bound and the commutator estimate -/

/-- the iterated integral of a continuous kernel is integrable on the box -/
lemma integrable_iterated {s : ℝ} (hs : 0 < s) {n : ℕ} {K : X (n + 1) × ℝ³ → ℝ}
    (hK : Continuous K) :
    Integrable (fun x : X (n + 1) => ∫ z in acube s, K (x, z)) (boxMeas (n + 1) s) := by
  haveI : IsFiniteMeasure (cubeMeas s) := isFiniteMeasure_cubeMeas hs
  haveI : IsFiniteMeasure (boxMeas (n + 1) s) := isFiniteMeasure_boxMeas hs
  obtain ⟨C, hC⟩ := ((abox_compact (n + 1) hs).prod (acube_compact hs)).exists_bound_of_continuousOn
    (s := abox (n + 1) s ×ˢ acube s) (f := K) hK.continuousOn
  have hbdd : ∀ᵐ p ∂((boxMeas (n + 1) s).prod (cubeMeas s)), ‖K p‖ ≤ max C 0 := by
    filter_upwards [ae_mem_box_prod hs] with p hp
    exact le_trans (hC p hp) (le_max_left _ _)
  exact (Integrable.of_bound hK.aestronglyMeasurable (max C 0) hbdd).integral_prod_left

/-- peel of an iterated box integral -/
lemma integral_peel_iterated {s : ℝ} (hs : 0 < s) {n : ℕ} (i : Fin (n + 1))
    {K : X (n + 1) × ℝ³ → ℝ} (hK : Continuous K) :
    (∫ x in abox (n + 1) s, ∫ z in acube s, K (x, z))
      = ∫ r in abox n s, ∫ y in acube s, ∫ z in acube s, K (kcInsN n i (y, r), z) :=
  abox_integral_peel i _ (integrable_iterated hs hK)

/-- **positivity** of `∫ Ψ · boxOp s g g Ψ` -/
lemma boxOp_gg_nonneg {s : ℝ} (hs : 0 < s) {n : ℕ} {g : ℝ³ → ℝ} (hg : Continuous g)
    {Ψ : X (n + 1) → ℝ} (hΨ : Continuous Ψ) :
    0 ≤ ∫ x in abox (n + 1) s, Ψ x * boxOp s g g Ψ x := by
  haveI : IsFiniteMeasure (cubeMeas s) := isFiniteMeasure_cubeMeas hs
  have hcont : ∀ i : Fin (n + 1), Continuous fun p : X (n + 1) × ℝ³ =>
      (Ψ p.1 * g (p.1 i)) * (g p.2 * Ψ (Function.update p.1 i p.2)) := fun i =>
    ((hΨ.comp continuous_fst).mul (hg.comp ((continuous_apply i).comp continuous_fst))).mul
      ((hg.comp continuous_snd).mul (hΨ.comp (continuous_fst.update i continuous_snd)))
  have h1 : (∫ x in abox (n + 1) s, Ψ x * boxOp s g g Ψ x)
      = ∑ i : Fin (n + 1), ∫ x in abox (n + 1) s, ∫ z in acube s,
          (Ψ x * g (x i)) * (g z * Ψ (Function.update x i z)) := by
    rw [show (fun x => Ψ x * boxOp s g g Ψ x) = fun x => ∑ i : Fin (n + 1),
        ∫ z in acube s, (Ψ x * g (x i)) * (g z * Ψ (Function.update x i z)) by
      funext x
      rw [boxOp, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show (∫ z in acube s, (Ψ x * g (x i)) * (g z * Ψ (Function.update x i z)))
          = (Ψ x * g (x i)) * ∫ z in acube s, g z * Ψ (Function.update x i z) from
        integral_const_mul _ _]
      ring]
    exact integral_finsetSum _ (fun i _ => integrable_iterated (n := n) hs (hcont i))
  rw [h1]
  refine Finset.sum_nonneg (fun i _ => ?_)
  rw [integral_peel_iterated hs i (hcont i)]
  refine integral_nonneg (fun r => ?_)
  simp only [kc_insN_apply_same, update_kcInsN]
  have hpt : (fun y : ℝ³ => ∫ z in acube s, (Ψ (kcInsN n i (y, r)) * g y) *
        (g z * Ψ (kcInsN n i (z, r))))
      = fun y => (g y * Ψ (kcInsN n i (y, r))) *
          (∫ z in acube s, g z * Ψ (kcInsN n i (z, r))) := by
    funext y
    rw [show (∫ z in acube s, (Ψ (kcInsN n i (y, r)) * g y) *
          (g z * Ψ (kcInsN n i (z, r))))
        = (Ψ (kcInsN n i (y, r)) * g y) * ∫ z in acube s, g z * Ψ (kcInsN n i (z, r)) from
      integral_const_mul _ _]
    ring
  rw [hpt, integral_mul_const]
  exact mul_self_nonneg _

/-- **the `P_i`-bound**: `∫ Ψ · boxOp s 1 1 Ψ = s³ Σ_i ∫ (P_i Ψ)² ≤ s³ (n+1) ∫Ψ²` -/
lemma boxOp_one_one_integral_le {s : ℝ} (hs : 0 < s) {n : ℕ} {Ψ : X (n + 1) → ℝ}
    (hΨ : Continuous Ψ) :
    (∫ x in abox (n + 1) s, Ψ x * boxOp s (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)
      ≤ s ^ 3 * ((n : ℝ) + 1) * ∫ x in abox (n + 1) s, (Ψ x) ^ 2 := by
  haveI : IsFiniteMeasure (boxMeas (n + 1) s) := isFiniteMeasure_boxMeas hs
  have hne : s ≠ 0 := ne_of_gt hs
  have haP : ∀ i : Fin (n + 1), (∫ x in abox (n + 1) s, Ψ x * aP s i Ψ x)
      = ∫ x in abox (n + 1) s, (aP s i Ψ x) ^ 2 := by
    intro i
    have hsym := aP_sym_box hs i (Φ := aP s i Ψ) (Ψ := Ψ) (aP_continuous hs i hΨ) hΨ
    simp only [pow_two]
    rw [← hsym]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only []
    rw [aP_idem hs i hΨ x]
    ring
  have h1 : (∫ x in abox (n + 1) s, Ψ x * boxOp s (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)
      = s ^ 3 * ∑ i : Fin (n + 1), ∫ x in abox (n + 1) s, Ψ x * aP s i Ψ x := by
    rw [show (fun x => Ψ x * boxOp s (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x) = fun x =>
        ∑ i : Fin (n + 1), s ^ 3 * (Ψ x * aP s i Ψ x) by
      funext x
      rw [boxOp_one_one hne Ψ x, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)]
    have hInt : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))),
        Integrable (fun x : X (n + 1) => s ^ 3 * (Ψ x * aP s i Ψ x)) (boxMeas (n + 1) s) := by
      intro i _
      have hbase : Integrable (fun x : X (n + 1) => Ψ x * aP s i Ψ x) (boxMeas (n + 1) s) :=
        ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs)
          ((hΨ.mul (aP_continuous hs i hΨ)).continuousOn)
      exact (hbase.const_mul (s ^ 3))
    rw [integral_finsetSum _ hInt, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_const_mul]
  rw [h1]
  simp_rw [haP]
  have h2 : ∀ i : Fin (n + 1), (∫ x in abox (n + 1) s, (aP s i Ψ x) ^ 2)
      ≤ ∫ x in abox (n + 1) s, (Ψ x) ^ 2 := fun i => aP_sq_le hs i hΨ
  calc s ^ 3 * ∑ i : Fin (n + 1), ∫ x in abox (n + 1) s, (aP s i Ψ x) ^ 2
      ≤ s ^ 3 * ∑ _i : Fin (n + 1), ∫ x in abox (n + 1) s, (Ψ x) ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => h2 i)) (by positivity)
    _ = s ^ 3 * ((n : ℝ) + 1) * ∫ x in abox (n + 1) s, (Ψ x) ^ 2 := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- two box-mean-free modes commute: `[τ_p, τ_q] = 0` -/
lemma boxOp_commute {s : ℝ} (hs : 0 < s) {n : ℕ} {g g' : ℝ³ → ℝ}
    (hg : Continuous g) (hg' : Continuous g')
    (hgm : (∫ z in acube s, g z) = 0) (hg'm : (∫ z in acube s, g' z) = 0)
    {Ψ : X (n + 1) → ℝ} (hΨ : Continuous Ψ) {x : X (n + 1)} (hx : x ∈ abox (n + 1) s) :
    boxOp s (fun _ => (1 : ℝ)) g (boxOp s (fun _ => (1 : ℝ)) g' Ψ) x
      = boxOp s (fun _ => (1 : ℝ)) g' (boxOp s (fun _ => (1 : ℝ)) g Ψ) x := by
  have h1 := boxOp_comp (f := fun _ => (1 : ℝ)) (h := g) (f' := fun _ => (1 : ℝ)) (h' := g')
    hs continuous_const hg continuous_const hg' hΨ hx
  have h2 := boxOp_comp (f := fun _ => (1 : ℝ)) (h := g') (f' := fun _ => (1 : ℝ)) (h' := g)
    hs continuous_const hg' continuous_const hg hΨ hx
  have h3 := boxOp2_symm (f := fun _ => (1 : ℝ)) (h := g) (f' := fun _ => (1 : ℝ))
    (h' := g') hs hg hg' hΨ hx
  have hc : (∫ z in acube s, g z * (fun _ => (1 : ℝ)) z) = 0 := by simpa using hgm
  have hc' : (∫ z in acube s, g' z * (fun _ => (1 : ℝ)) z) = 0 := by simpa using hg'm
  rw [h1, h2, hc, hc', h3]
  ring

/-! ## 6. The `τ`-commutator bound (FS `lm:appbogolubov`) -/

/-- `tauDag s g Ψ = (√(s³))⁻¹ · boxOp s g 1 Ψ` -/
lemma tauDag_eq {s : ℝ} (hs : 0 < s) {N : ℕ} (g : ℝ³ → ℝ) (Ψ : X N → ℝ) (x : X N) :
    tauDag s g Ψ x = (Real.sqrt (s ^ 3))⁻¹ * boxOp s g (fun _ => (1 : ℝ)) Ψ x := by
  have hsp : (0 : ℝ) < Real.sqrt (s ^ 3) := Real.sqrt_pos_of_pos (by positivity)
  rw [boxOp_eq_tauDag hs g Ψ x]
  field_simp

/-- `tauAnn s g Ψ = (√(s³))⁻¹ · boxOp s 1 g Ψ` -/
lemma tauAnn_eq {s : ℝ} (hs : 0 < s) {N : ℕ} (g : ℝ³ → ℝ) (Ψ : X N → ℝ) (x : X N) :
    tauAnn s g Ψ x = (Real.sqrt (s ^ 3))⁻¹ * boxOp s (fun _ => (1 : ℝ)) g Ψ x := by
  have hsp : (0 : ℝ) < Real.sqrt (s ^ 3) := Real.sqrt_pos_of_pos (by positivity)
  rw [boxOp_eq_tauAnn hs g Ψ x]
  field_simp

/-- **the commutator bound** (FS's `[b_p,b_p†] ≤ n_0 |B|⁻¹ ∫χ_B²`, corpus form):
`∫ (τ†Ψ)² − ∫ (τΨ)² ≤ (∫g²)·(n+1)·∫Ψ²`. -/
theorem tau_commutator_le {s : ℝ} (hs : 0 < s) {n : ℕ} {g : ℝ³ → ℝ} (hg : Continuous g)
    {Ψ : X (n + 1) → ℝ} (hΨ : Continuous Ψ) :
    (∫ x in abox (n + 1) s, (tauDag s g Ψ x) ^ 2)
        - (∫ x in abox (n + 1) s, (tauAnn s g Ψ x) ^ 2)
      ≤ (∫ z in acube s, g z * g z) * ((n : ℝ) + 1)
          * (∫ x in abox (n + 1) s, (Ψ x) ^ 2) := by
  haveI : IsFiniteMeasure (boxMeas (n + 1) s) := isFiniteMeasure_boxMeas hs
  have hs3pos : (0 : ℝ) < s ^ 3 := by positivity
  -- the `tau` ↔ `boxOp` bridge
  have htauD : (∫ x in abox (n + 1) s, (tauDag s g Ψ x) ^ 2)
      = (s ^ 3)⁻¹ * ∫ x in abox (n + 1) s, (boxOp s g (fun _ => (1 : ℝ)) Ψ x) ^ 2 := by
    rw [show (fun x => (tauDag s g Ψ x) ^ 2) = fun x =>
        (s ^ 3)⁻¹ * (boxOp s g (fun _ => (1 : ℝ)) Ψ x) ^ 2 by
      funext x
      rw [tauDag_eq hs g Ψ x, mul_pow, inv_pow, Real.sq_sqrt (le_of_lt hs3pos)]]
    rw [integral_const_mul]
  have htauA : (∫ x in abox (n + 1) s, (tauAnn s g Ψ x) ^ 2)
      = (s ^ 3)⁻¹ * ∫ x in abox (n + 1) s, (boxOp s (fun _ => (1 : ℝ)) g Ψ x) ^ 2 := by
    rw [show (fun x => (tauAnn s g Ψ x) ^ 2) = fun x =>
        (s ^ 3)⁻¹ * (boxOp s (fun _ => (1 : ℝ)) g Ψ x) ^ 2 by
      funext x
      rw [tauAnn_eq hs g Ψ x, mul_pow, inv_pow, Real.sq_sqrt (le_of_lt hs3pos)]]
    rw [integral_const_mul]
  -- adjointness
  have hU : (∫ x in abox (n + 1) s, (boxOp s g (fun _ => (1 : ℝ)) Ψ x) ^ 2)
      = ∫ x in abox (n + 1) s,
          Ψ x * boxOp s (fun _ => (1 : ℝ)) g (boxOp s g (fun _ => (1 : ℝ)) Ψ) x := by
    rw [boxOp_adjoint hs continuous_const hg hΨ (continuous_boxOp hs hg continuous_const hΨ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hV : (∫ x in abox (n + 1) s, (boxOp s (fun _ => (1 : ℝ)) g Ψ x) ^ 2)
      = ∫ x in abox (n + 1) s,
          Ψ x * boxOp s g (fun _ => (1 : ℝ)) (boxOp s (fun _ => (1 : ℝ)) g Ψ) x := by
    rw [boxOp_adjoint hs hg continuous_const hΨ (continuous_boxOp hs continuous_const hg hΨ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  -- integrability of the pieces
  have hIc : Integrable (fun x : X (n + 1) => Ψ x *
      boxOp s (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x) (boxMeas (n + 1) s) :=
    ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs)
      ((hΨ.mul (continuous_boxOp hs continuous_const continuous_const hΨ)).continuousOn)
  have hIg : Integrable (fun x : X (n + 1) => Ψ x * boxOp s g g Ψ x) (boxMeas (n + 1) s) :=
    ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs)
      ((hΨ.mul (continuous_boxOp hs hg hg hΨ)).continuousOn)
  have hI1 : Integrable (fun x : X (n + 1) => Ψ x *
      boxOp s (fun _ => (1 : ℝ)) g (boxOp s g (fun _ => (1 : ℝ)) Ψ) x) (boxMeas (n + 1) s) :=
    ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs)
      ((hΨ.mul (continuous_boxOp hs continuous_const hg
        (continuous_boxOp hs hg continuous_const hΨ))).continuousOn)
  have hI2 : Integrable (fun x : X (n + 1) => Ψ x *
      boxOp s g (fun _ => (1 : ℝ)) (boxOp s (fun _ => (1 : ℝ)) g Ψ) x) (boxMeas (n + 1) s) :=
    ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs)
      ((hΨ.mul (continuous_boxOp hs hg continuous_const
        (continuous_boxOp hs continuous_const hg hΨ))).continuousOn)
  -- the quadratic-form identity
  have key : (∫ x in abox (n + 1) s, (boxOp s g (fun _ => (1 : ℝ)) Ψ x) ^ 2)
        - (∫ x in abox (n + 1) s, (boxOp s (fun _ => (1 : ℝ)) g Ψ x) ^ 2)
      = (∫ z in acube s, g z * g z)
          * (∫ x in abox (n + 1) s, Ψ x * boxOp s (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)
        - s ^ 3 * (∫ x in abox (n + 1) s, Ψ x * boxOp s g g Ψ x) := by
    rw [hU, hV, ← integral_sub hI1 hI2]
    rw [show (∫ x in abox (n + 1) s, (Ψ x *
            boxOp s (fun _ => (1 : ℝ)) g (boxOp s g (fun _ => (1 : ℝ)) Ψ) x
          - Ψ x * boxOp s g (fun _ => (1 : ℝ)) (boxOp s (fun _ => (1 : ℝ)) g Ψ) x))
        = ∫ x in abox (n + 1) s, ((∫ z in acube s, g z * g z)
              * (Ψ x * boxOp s (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)
            - s ^ 3 * (Ψ x * boxOp s g g Ψ x)) from
      integral_congr_ae (by
        filter_upwards [ae_restrict_mem (abox_measurable (n + 1) s)] with x hx
        rw [← mul_sub, boxOp_commutator hs hg hΨ hx]
        ring)]
    rw [integral_sub (hIc.const_mul _) (hIg.const_mul _), integral_const_mul, integral_const_mul]
  -- the final chain
  rw [htauD, htauA, ← mul_sub, key]
  have hcgnn : 0 ≤ ∫ z in acube s, g z * g z := integral_nonneg fun z => mul_self_nonneg _
  have hBnn : 0 ≤ ∫ x in abox (n + 1) s, Ψ x * boxOp s g g Ψ x := boxOp_gg_nonneg hs hg hΨ
  have hA := boxOp_one_one_integral_le hs hΨ
  calc (s ^ 3)⁻¹ * ((∫ z in acube s, g z * g z)
          * (∫ x in abox (n + 1) s,
              Ψ x * boxOp s (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)
        - s ^ 3 * (∫ x in abox (n + 1) s, Ψ x * boxOp s g g Ψ x))
      ≤ (s ^ 3)⁻¹ * ((∫ z in acube s, g z * g z)
          * (∫ x in abox (n + 1) s,
              Ψ x * boxOp s (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact sub_le_self _ (mul_nonneg (by positivity) hBnn)
    _ ≤ (s ^ 3)⁻¹ * ((∫ z in acube s, g z * g z)
          * (s ^ 3 * ((n : ℝ) + 1) * ∫ x in abox (n + 1) s, (Ψ x) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hA hcgnn
    _ = (∫ z in acube s, g z * g z) * ((n : ℝ) + 1)
          * (∫ x in abox (n + 1) s, (Ψ x) ^ 2) := by
        field_simp


/-! ## 7. Two-mode Bogoliubov at the quadratic-form level (FS `thm:bogolubov-complete`) -/

/-- the three coefficient identities packaged for the analytic step -/
lemma bogoliubov_coeff {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) :
    ((A + Real.sqrt (A ^ 2 - B ^ 2)) / 2) * (1 + (B / (A + Real.sqrt (A ^ 2 - B ^ 2))) ^ 2) = A
    ∧ 2 * (((A + Real.sqrt (A ^ 2 - B ^ 2)) / 2) * (B / (A + Real.sqrt (A ^ 2 - B ^ 2)))) = B
    ∧ ((A + Real.sqrt (A ^ 2 - B ^ 2)) / 2) * (B / (A + Real.sqrt (A ^ 2 - B ^ 2))) ^ 2
        = (A - Real.sqrt (A ^ 2 - B ^ 2)) / 2 := by
  have hs2 : Real.sqrt (A ^ 2 - B ^ 2) ^ 2 = A ^ 2 - B ^ 2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg B, abs_le.mp hB])
  have hden : A + Real.sqrt (A ^ 2 - B ^ 2) ≠ 0 := by
    have : 0 ≤ Real.sqrt (A ^ 2 - B ^ 2) := Real.sqrt_nonneg _
    nlinarith
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> nlinarith [sq_nonneg B]

/-- the c-number Bogoliubov core: with `D = (A+s)/2`, `α = B/(A+s)`,
`s = √(A²−B²)`, one has
`A(P+Q) + B(R+R') = D(P+Q+2α(R+R')+α²(S+T)) − Dα²((T−P)+(S−Q))`. -/
lemma bogoliubov_core {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) (P Q R R' S T : ℝ) :
    A * (P + Q) + B * (R + R')
      = ((A + Real.sqrt (A ^ 2 - B ^ 2)) / 2)
            * (P + Q + 2 * (B / (A + Real.sqrt (A ^ 2 - B ^ 2))) * (R + R')
                + (B / (A + Real.sqrt (A ^ 2 - B ^ 2))) ^ 2 * (S + T))
        - ((A + Real.sqrt (A ^ 2 - B ^ 2)) / 2) * (B / (A + Real.sqrt (A ^ 2 - B ^ 2))) ^ 2
            * ((T - P) + (S - Q)) := by
  have h1 := (bogoliubov_coeff hA hB).1
  have h2 := (bogoliubov_coeff hA hB).2.1
  rw [show ((A + Real.sqrt (A ^ 2 - B ^ 2)) / 2)
        * (P + Q + 2 * (B / (A + Real.sqrt (A ^ 2 - B ^ 2))) * (R + R')
            + (B / (A + Real.sqrt (A ^ 2 - B ^ 2))) ^ 2 * (S + T))
      - ((A + Real.sqrt (A ^ 2 - B ^ 2)) / 2) * (B / (A + Real.sqrt (A ^ 2 - B ^ 2))) ^ 2
          * ((T - P) + (S - Q))
      = ((A + Real.sqrt (A ^ 2 - B ^ 2)) / 2)
            * (1 + (B / (A + Real.sqrt (A ^ 2 - B ^ 2))) ^ 2) * (P + Q)
          + (2 * (((A + Real.sqrt (A ^ 2 - B ^ 2)) / 2)
              * (B / (A + Real.sqrt (A ^ 2 - B ^ 2))))) * (R + R') from by ring]
  rw [h1, h2]


/-- expanding `∫ (f₁ + α f₂)²` -/
lemma sq_expand {s : ℝ} (hs : 0 < s) {n : ℕ} {f₁ f₂ : X (n + 1) → ℝ}
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) (α : ℝ) :
    (∫ x in abox (n + 1) s, (f₁ x + α * f₂ x) ^ 2)
      = (∫ x in abox (n + 1) s, (f₁ x) ^ 2)
        + 2 * α * (∫ x in abox (n + 1) s, f₁ x * f₂ x)
        + α ^ 2 * (∫ x in abox (n + 1) s, (f₂ x) ^ 2) := by
  haveI : IsFiniteMeasure (boxMeas (n + 1) s) := isFiniteMeasure_boxMeas hs
  have hI1 : Integrable (fun x : X (n + 1) => (f₁ x) ^ 2) (boxMeas (n + 1) s) :=
    ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs) (hf₁.pow 2).continuousOn
  have hI2 : Integrable (fun x : X (n + 1) => 2 * α * (f₁ x * f₂ x)) (boxMeas (n + 1) s) :=
    (ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs)
      (hf₁.mul hf₂).continuousOn).const_mul _
  have hI3 : Integrable (fun x : X (n + 1) => α ^ 2 * (f₂ x) ^ 2) (boxMeas (n + 1) s) :=
    (ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs) (hf₂.pow 2).continuousOn).const_mul _
  rw [show (fun x => (f₁ x + α * f₂ x) ^ 2) = fun x =>
      (f₁ x) ^ 2 + 2 * α * (f₁ x * f₂ x) + α ^ 2 * (f₂ x) ^ 2 by
    funext x; ring]
  rw [show (∫ x in abox (n + 1) s,
        ((f₁ x) ^ 2 + 2 * α * (f₁ x * f₂ x) + α ^ 2 * (f₂ x) ^ 2))
      = (∫ x in abox (n + 1) s, ((f₁ x) ^ 2 + 2 * α * (f₁ x * f₂ x)))
        + (∫ x in abox (n + 1) s, α ^ 2 * (f₂ x) ^ 2) from
    integral_add (hI1.add hI2) hI3]
  rw [show (∫ x in abox (n + 1) s, ((f₁ x) ^ 2 + 2 * α * (f₁ x * f₂ x)))
      = (∫ x in abox (n + 1) s, (f₁ x) ^ 2)
        + (∫ x in abox (n + 1) s, 2 * α * (f₁ x * f₂ x)) from
    integral_add hI1 hI2]
  rw [integral_const_mul, integral_const_mul]

/-- **two-mode Bogoliubov inequality** (FS `thm:bogolubov-complete` at the level of
the corpus's `τ`-operators): for `A > 0`, `|B| ≤ A`,
`A(‖τ_gΨ‖²+‖τ_{g'}Ψ‖²) + B(⟨τ_g†Ψ,τ_{g'}†Ψ⟩ + ⟨τ_g†Ψ,τ_{g'}Ψ⟩)
   ≥ −((A−√(A²−B²))/2)·([τ_g,τ_g†]+[τ_{g'},τ_{g'}†])(Ψ)`. -/
theorem tau_two_mode_ineq {s : ℝ} (hs : 0 < s) {n : ℕ} {g g' : ℝ³ → ℝ}
    (hg : Continuous g) (hg' : Continuous g') {Ψ : X (n + 1) → ℝ} (hΨ : Continuous Ψ)
    {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) :
    - ((A - Real.sqrt (A ^ 2 - B ^ 2)) / 2)
        * ((∫ x in abox (n + 1) s, (tauDag s g Ψ x) ^ 2)
            - (∫ x in abox (n + 1) s, (tauAnn s g Ψ x) ^ 2)
          + ((∫ x in abox (n + 1) s, (tauDag s g' Ψ x) ^ 2)
              - (∫ x in abox (n + 1) s, (tauAnn s g' Ψ x) ^ 2)))
      ≤ A * ((∫ x in abox (n + 1) s, (tauAnn s g Ψ x) ^ 2)
              + (∫ x in abox (n + 1) s, (tauAnn s g' Ψ x) ^ 2))
        + B * ((∫ x in abox (n + 1) s, tauAnn s g Ψ x * tauDag s g' Ψ x)
              + (∫ x in abox (n + 1) s, tauDag s g Ψ x * tauAnn s g' Ψ x)) := by
  set α : ℝ := B / (A + Real.sqrt (A ^ 2 - B ^ 2)) with hα
  set D : ℝ := (A + Real.sqrt (A ^ 2 - B ^ 2)) / 2 with hD
  set P : ℝ := ∫ x in abox (n + 1) s, (tauAnn s g Ψ x) ^ 2 with hP
  set Q : ℝ := ∫ x in abox (n + 1) s, (tauAnn s g' Ψ x) ^ 2 with hQ
  set R : ℝ := ∫ x in abox (n + 1) s, tauAnn s g Ψ x * tauDag s g' Ψ x with hR
  set R' : ℝ := ∫ x in abox (n + 1) s, tauDag s g Ψ x * tauAnn s g' Ψ x with hR'
  set T : ℝ := ∫ x in abox (n + 1) s, (tauDag s g Ψ x) ^ 2 with hT
  set S : ℝ := ∫ x in abox (n + 1) s, (tauDag s g' Ψ x) ^ 2 with hS
  have hcg : Continuous (tauAnn s g Ψ) := by
    have h : tauAnn s g Ψ = fun x => (Real.sqrt (s ^ 3))⁻¹ *
        boxOp s (fun _ => (1 : ℝ)) g Ψ x := by funext x; rw [tauAnn_eq hs g Ψ x]
    rw [h]; exact (continuous_boxOp hs continuous_const hg hΨ).const_mul _
  have hcg' : Continuous (tauAnn s g' Ψ) := by
    have h : tauAnn s g' Ψ = fun x => (Real.sqrt (s ^ 3))⁻¹ *
        boxOp s (fun _ => (1 : ℝ)) g' Ψ x := by funext x; rw [tauAnn_eq hs g' Ψ x]
    rw [h]; exact (continuous_boxOp hs continuous_const hg' hΨ).const_mul _
  have hdg : Continuous (tauDag s g Ψ) := by
    have h : tauDag s g Ψ = fun x => (Real.sqrt (s ^ 3))⁻¹ *
        boxOp s g (fun _ => (1 : ℝ)) Ψ x := by funext x; rw [tauDag_eq hs g Ψ x]
    rw [h]; exact (continuous_boxOp hs hg continuous_const hΨ).const_mul _
  have hdg' : Continuous (tauDag s g' Ψ) := by
    have h : tauDag s g' Ψ = fun x => (Real.sqrt (s ^ 3))⁻¹ *
        boxOp s g' (fun _ => (1 : ℝ)) Ψ x := by funext x; rw [tauDag_eq hs g' Ψ x]
    rw [h]; exact (continuous_boxOp hs hg' continuous_const hΨ).const_mul _
  have hsq1 : (∫ x in abox (n + 1) s, (tauAnn s g Ψ x + α * tauDag s g' Ψ x) ^ 2)
      = P + 2 * α * R + α ^ 2 * S := by
    rw [hP, hR, hS]
    rw [sq_expand hs hcg hdg' α]
  have hsq2 : (∫ x in abox (n + 1) s, (tauAnn s g' Ψ x + α * tauDag s g Ψ x) ^ 2)
      = Q + 2 * α * R' + α ^ 2 * T := by
    rw [hQ, hR', hT]
    rw [sq_expand hs hcg' hdg α]
    rw [show (∫ x in abox (n + 1) s, tauAnn s g' Ψ x * tauDag s g Ψ x)
        = ∫ x in abox (n + 1) s, tauDag s g Ψ x * tauAnn s g' Ψ x from
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)]
  have hnn : 0 ≤ D * (P + Q + 2 * α * (R + R') + α ^ 2 * (S + T)) := by
    have h : 0 ≤ D * ((∫ x in abox (n + 1) s, (tauAnn s g Ψ x + α * tauDag s g' Ψ x) ^ 2)
        + (∫ x in abox (n + 1) s, (tauAnn s g' Ψ x + α * tauDag s g Ψ x) ^ 2)) :=
      mul_nonneg (by rw [hD]; positivity)
        (add_nonneg (integral_nonneg fun x => sq_nonneg _)
          (integral_nonneg fun x => sq_nonneg _))
    rw [hsq1, hsq2] at h
    convert h using 2
    ring
  have hc3' : D * α ^ 2 = (A - Real.sqrt (A ^ 2 - B ^ 2)) / 2 := by
    rw [hD, hα]; exact (bogoliubov_coeff hA hB).2.2
  have hcore' : A * (P + Q) + B * (R + R')
      = D * (P + Q + 2 * α * (R + R') + α ^ 2 * (S + T))
        - D * α ^ 2 * ((T - P) + (S - Q)) := by
    rw [hD, hα]
    exact bogoliubov_core hA hB P Q R R' S T
  rw [hc3'] at hcore'
  linarith [hnn, hcore']


/-- **the two-mode Bogoliubov bound with the commutator input** (FS's chain):
`A(‖τ_gΨ‖²+‖τ_{g'}Ψ‖²) + B(⟨τ_g†Ψ,τ_{g'}†Ψ⟩+⟨τ_g†Ψ,τ_{g'}Ψ⟩)
   ≥ −(A−√(A²−B²))/2·((c_g+c_{g'})·N·‖Ψ‖²)`. -/
theorem tau_two_mode_bound {s : ℝ} (hs : 0 < s) {n : ℕ} {g g' : ℝ³ → ℝ}
    (hg : Continuous g) (hg' : Continuous g') {Ψ : X (n + 1) → ℝ} (hΨ : Continuous Ψ)
    {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) :
    - ((A - Real.sqrt (A ^ 2 - B ^ 2)) / 2)
        * ((∫ z in acube s, g z * g z) * ((n : ℝ) + 1) * (∫ x in abox (n + 1) s, (Ψ x) ^ 2)
          + (∫ z in acube s, g' z * g' z) * ((n : ℝ) + 1)
              * (∫ x in abox (n + 1) s, (Ψ x) ^ 2))
      ≤ A * ((∫ x in abox (n + 1) s, (tauAnn s g Ψ x) ^ 2)
              + (∫ x in abox (n + 1) s, (tauAnn s g' Ψ x) ^ 2))
        + B * ((∫ x in abox (n + 1) s, tauAnn s g Ψ x * tauDag s g' Ψ x)
              + (∫ x in abox (n + 1) s, tauDag s g Ψ x * tauAnn s g' Ψ x)) := by
  have h := tau_two_mode_ineq hs hg hg' hΨ hA hB
  have hc1 := tau_commutator_le (n := n) hs hg hΨ
  have hc2 := tau_commutator_le (n := n) hs hg' hΨ
  have hsp : 0 ≤ (A - Real.sqrt (A ^ 2 - B ^ 2)) / 2 := by
    have h1 : Real.sqrt (A ^ 2 - B ^ 2) ≤ A := by
      rw [Real.sqrt_le_left (le_of_lt hA)]
      nlinarith [abs_le.mp hB]
    linarith
  have hsum : ((∫ x in abox (n + 1) s, (tauDag s g Ψ x) ^ 2)
        - (∫ x in abox (n + 1) s, (tauAnn s g Ψ x) ^ 2))
      + ((∫ x in abox (n + 1) s, (tauDag s g' Ψ x) ^ 2)
        - (∫ x in abox (n + 1) s, (tauAnn s g' Ψ x) ^ 2))
      ≤ (∫ z in acube s, g z * g z) * ((n : ℝ) + 1)
          * (∫ x in abox (n + 1) s, (Ψ x) ^ 2)
        + (∫ z in acube s, g' z * g' z) * ((n : ℝ) + 1)
          * (∫ x in abox (n + 1) s, (Ψ x) ^ 2) := add_le_add hc1 hc2
  have h1 : - ((A - Real.sqrt (A ^ 2 - B ^ 2)) / 2)
        * ((∫ z in acube s, g z * g z) * ((n : ℝ) + 1)
            * (∫ x in abox (n + 1) s, (Ψ x) ^ 2)
          + (∫ z in acube s, g' z * g' z) * ((n : ℝ) + 1)
            * (∫ x in abox (n + 1) s, (Ψ x) ^ 2))
      ≤ - ((A - Real.sqrt (A ^ 2 - B ^ 2)) / 2)
        * (((∫ x in abox (n + 1) s, (tauDag s g Ψ x) ^ 2)
            - (∫ x in abox (n + 1) s, (tauAnn s g Ψ x) ^ 2))
          + ((∫ x in abox (n + 1) s, (tauDag s g' Ψ x) ^ 2)
            - (∫ x in abox (n + 1) s, (tauAnn s g' Ψ x) ^ 2))) := by
    have hm := mul_le_mul_of_nonneg_left hsum hsp
    linarith [hm]
  linarith [h1, h]

end BoseGases
end Submission
