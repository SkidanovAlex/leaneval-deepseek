import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseSym.Bridge.exists_testSub_quot_le
import Submission.Work.BoseSym.Bridge.hsub_liminf_energy
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym.Bridge — the convergence of the truncated box energy

This module proves

`Tendsto (fun M : ℕ => boxEnergyTrunc N L v M) atTop (nhds (boxE N L v))`

for `0 < L`, `0 ≤ v` and `Vpot N v` integrable on the box.

The two halves are:

* `boxEnergyTrunc N L v M ≤ boxE N L v` for every `M ≥ 0`: at every state the truncated
  Rayleigh quotient is the full one with the potential replaced by its truncation, which
  is pointwise smaller; the *dictionary* `boxE_quot_eq_gradForm` identifies the full
  quotient with the gradient form of `𝓗`;
* `boxE N L v ≤ lim_m boxEnergyTrunc N L v m`: if the truncated infima stayed a fixed
  distance `ε` below `boxE`, one could take near-minimisers of the truncated problems,
  extract a limit point in the energy space with energy below `boxE - ε`
  (`hsub_liminf_energy`: compactness of the embedding of `Hsub` into `L²` plus Fatou for
  the truncated potentials), and realise it by a smooth test function of the same energy
  (`exists_testSub_quot_le`), contradicting the definition of `boxE` as an infimum over
  the box states.
-/

namespace Work.BoseSym.Bridge

open MeasureTheory Filter
open BoseGases
open Submission.BoseGases
open scoped Topology Real ContDiff ENNReal

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Integrability on the box -/

lemma intIntegrand_eq_Vpot {N : ℕ} {L : ℝ} {v : E3 → ℝ} (Ψ : CInfty0Box N L) :
    intIntegrand N L v Ψ = fun x => ((Ψ : Conf N → ℝ) x) ^ 2 * Vpot N v x := by
  funext x
  rfl

/-- `Vpot · Ψ²` is integrable on the box when `Vpot` is and `Ψ` is a box state. -/
lemma integrableOn_Vpot_mul_sq_box {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ}
    (hV : IntOnBox N L (Vpot N v)) (Ψ : CInfty0Box N L) :
    IntegrableOn (fun x => Vpot N v x * ((Ψ : Conf N → ℝ) x) ^ 2) (box N L) volume := by
  obtain ⟨C, hC⟩ := (hasCompactSupport_Ψ hL Ψ).exists_bound_of_continuous
    (psi_contDiff Ψ).continuous
  have hbnd : ∀ᵐ x ∂(volume.restrict (box N L)), ‖((Ψ : Conf N → ℝ) x) ^ 2‖ ≤ C ^ 2 := by
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC x) 2
  have haesm : AEStronglyMeasurable (fun x : Conf N => ((Ψ : Conf N → ℝ) x) ^ 2)
      (volume.restrict (box N L)) :=
    ((psi_contDiff Ψ).continuous.pow 2).aestronglyMeasurable
  have h := Integrable.bdd_mul (c := C ^ 2) (μ := volume.restrict (box N L)) hV haesm hbnd
  refine h.congr (Eventually.of_forall fun x => ?_)
  ring

lemma integrableOn_intIntegrand_of_IntOnBox {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ}
    (hV : IntOnBox N L (Vpot N v)) (Ψ : CInfty0Box N L) :
    IntegrableOn (intIntegrand N L v Ψ) (box N L) volume := by
  refine (integrableOn_Vpot_mul_sq_box hL hV Ψ).congr ?_
  filter_upwards with x
  rw [intIntegrand_eq_Vpot]
  ring

/-! ## The dictionary -/

/-- The kinetic energy is the box integral of the squared pointwise gradient. -/
lemma kineticEnergy_eq_gradSum {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) :
    kineticEnergy N L Ψ
      = ∑ i : Fin N, ∑ k : Fin 3,
          ∫ x in box N L, (fderiv ℝ (Ψ : Conf N → ℝ) x (kcDir N i k)) ^ 2 := by
  rw [← kinNeu_emb_eq (L := L) hL Ψ, kinNeu_emb_expand (L := L) hL Ψ]

/-- The interaction energy as a box integral of `Vpot`. -/
lemma interactionEnergy_eq_Vpot {N : ℕ} {L : ℝ} {v : E3 → ℝ} (Ψ : CInfty0Box N L) :
    interactionEnergy N L v Ψ
      = ∫ x in box N L, Vpot N v x * ((Ψ : Conf N → ℝ) x) ^ 2 := by
  unfold interactionEnergy Vpot
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact mul_comm _ _

/-- A double sum of box integrals of squared directional derivatives is the box integral
of the double sum. -/
lemma gradSum_eq_integral {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) :
    (∑ i : Fin N, ∑ k : Fin 3,
        ∫ x in box N L, (fderiv ℝ (Ψ : Conf N → ℝ) x (kcDir N i k)) ^ 2)
      = ∫ x in box N L, ∑ i : Fin N, ∑ k : Fin 3,
          (fderiv ℝ (Ψ : Conf N → ℝ) x (kcDir N i k)) ^ 2 := by
  have hinner : ∀ i : Fin N,
      (∑ k : Fin 3, ∫ x in box N L, (fderiv ℝ (Ψ : Conf N → ℝ) x (kcDir N i k)) ^ 2)
        = ∫ x in box N L, ∑ k : Fin 3,
            (fderiv ℝ (Ψ : Conf N → ℝ) x (kcDir N i k)) ^ 2 := by
    intro i
    exact (integral_finsetSum (s := (Finset.univ : Finset (Fin 3)))
      (μ := volume.restrict (box N L))
      (f := fun (k : Fin 3) (x : Conf N) =>
        (fderiv ℝ (Ψ : Conf N → ℝ) x (kcDir N i k)) ^ 2)
      (fun k _ => integrableOn_fderivSq hL Ψ (kcDir N i k))).symm
  calc (∑ i : Fin N, ∑ k : Fin 3,
        ∫ x in box N L, (fderiv ℝ (Ψ : Conf N → ℝ) x (kcDir N i k)) ^ 2)
      = ∑ i : Fin N, ∫ x in box N L, ∑ k : Fin 3,
          (fderiv ℝ (Ψ : Conf N → ℝ) x (kcDir N i k)) ^ 2 :=
        Finset.sum_congr rfl fun i _ => hinner i
    _ = ∫ x in box N L, ∑ i : Fin N, ∑ k : Fin 3,
          (fderiv ℝ (Ψ : Conf N → ℝ) x (kcDir N i k)) ^ 2 :=
        (integral_finsetSum (s := (Finset.univ : Finset (Fin N)))
          (μ := volume.restrict (box N L))
          (f := fun (i : Fin N) (x : Conf N) => ∑ k : Fin 3,
            (fderiv ℝ (Ψ : Conf N → ℝ) x (kcDir N i k)) ^ 2)
          (fun i _ => integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
            (f := fun (k : Fin 3) (x : Conf N) =>
              (fderiv ℝ (Ψ : Conf N → ℝ) x (kcDir N i k)) ^ 2)
            (fun k _ => integrableOn_fderivSq hL Ψ (kcDir N i k)))).symm

/-- **The dictionary.** The Rayleigh quotient of `𝓗` at a box state is the box integral
of the squared gradient plus the box integral of `Vpot Ψ²`, divided by `∫_box Ψ²`. -/
theorem boxE_quot_eq_gradForm {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ}
    (hV : IntOnBox N L (Vpot N v)) (Ψ : CInfty0Box N L) :
    (∫ x in box N L, (Ψ : Conf N → ℝ) x * 𝓗 N v (Ψ : Conf N → ℝ) x)
        / (√ (∫ x in box N L, (Ψ : Conf N → ℝ) x * (Ψ : Conf N → ℝ) x)) ^ 2
      = ((∫ x in box N L, ∑ i : Fin N, ∑ k : Fin 3,
            (fderiv ℝ (Ψ : Conf N → ℝ) x (kcDir N i k)) ^ 2)
          + ∫ x in box N L, Vpot N v x * ((Ψ : Conf N → ℝ) x) ^ 2)
        / (∫ x in box N L, ((Ψ : Conf N → ℝ) x) ^ 2) := by
  have hdec := energy_decomposition N L v Ψ hL (integrableOn_intIntegrand_of_IntOnBox hL hV Ψ)
  have hkin := kineticEnergy_eq_gradSum hL Ψ
  have hint := interactionEnergy_eq_Vpot (v := v) Ψ
  have hswap := gradSum_eq_integral hL Ψ
  have hden : (√ (∫ x in box N L, (Ψ : Conf N → ℝ) x * (Ψ : Conf N → ℝ) x)) ^ 2
      = ∫ x in box N L, ((Ψ : Conf N → ℝ) x) ^ 2 := by
    rw [Real.sq_sqrt (integral_nonneg fun x => mul_self_nonneg _)]
    exact integral_congr_ae (Eventually.of_forall fun x => (sq _).symm)
  rw [hdec, hkin, hint, hswap, hden]

/-! ## The energy space and the box trial states -/

lemma l2Sq_smul_amb {N : ℕ} (c : ℝ) (p : Amb N) : l2Sq (c • p) = c ^ 2 * l2Sq p := by
  simp only [l2Sq, Prod.smul_fst, norm_smul, Real.norm_eq_abs]
  rw [mul_pow, sq_abs]

lemma gSq_smul_amb {N : ℕ} (c : ℝ) (p : Amb N) : gSq (c • p) = c ^ 2 * gSq p := by
  simp only [gSq, Prod.smul_snd, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow, sq_abs]

lemma graphPoint_mem_Hsub_self {N : ℕ} {L : ℝ} (F : testSub N L) :
    graphPoint N L F ∈ Hsub N L :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨F, rfl⟩)

/-- The bridge between the energy space and the box trial states. -/
lemma quot_graphPoint_eq {N : ℕ} {L : ℝ} {W : Conf N → ℝ} (F : testSub N L) :
    (gSq (graphPoint N L F) + potSq W (graphPoint N L F)) / l2Sq (graphPoint N L F)
      = ((∫ x in box N L, ∑ i : Fin N, ∑ k : Fin 3,
            (fderiv ℝ (F : Conf N → ℝ) x (kcDir N i k)) ^ 2)
          + ∫ x in box N L, W x * ((F : Conf N → ℝ) x) ^ 2)
        / (∫ x in box N L, ((F : Conf N → ℝ) x) ^ 2) := by
  rw [gSq_graphPoint_box, potSq_graphPoint_box, l2Sq_graphPoint_box]
  rfl

/-- A nonzero test function is a box trial state. -/
noncomputable def testToBox {N : ℕ} {L : ℝ} (F : testSub N L) (hF : (F : Conf N → ℝ) ≠ 0) :
    CInfty0Box N L where
  toFun := (F : Conf N → ℝ)
  contDiff := F.2.1.contDiffOn
  support := F.2.2.trans (le_of_eq (interior_box_eq_openBox N L).symm)
  nezero := hF

@[simp] lemma testToBox_coe {N : ℕ} {L : ℝ} (F : testSub N L) (hF : (F : Conf N → ℝ) ≠ 0) :
    (testToBox F hF : Conf N → ℝ) = (F : Conf N → ℝ) := rfl

/-! ## `boxE` as an infimum of quotients -/

lemma boxE_quot_nonneg {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ} (hv : 0 ≤ v)
    (hV : IntOnBox N L (Vpot N v)) (Ψ : CInfty0Box N L) :
    0 ≤ (∫ x in box N L, (Ψ : Conf N → ℝ) x * 𝓗 N v (Ψ : Conf N → ℝ) x)
        / (√ (∫ x in box N L, (Ψ : Conf N → ℝ) x * (Ψ : Conf N → ℝ) x)) ^ 2 := by
  rw [boxE_quot_eq_gradForm hL hV Ψ]
  refine div_nonneg (add_nonneg ?_ ?_) (integral_nonneg fun x => sq_nonneg _)
  · exact integral_nonneg fun x => Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun k _ => sq_nonneg _
  · exact integral_nonneg fun x => mul_nonneg (Vpot_nonneg hv x) (sq_nonneg _)

lemma boxE_quot_bddBelow {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ} (hv : 0 ≤ v)
    (hV : IntOnBox N L (Vpot N v)) :
    BddBelow (Set.range fun Ψ : CInfty0Box N L =>
      (∫ x in box N L, (Ψ : Conf N → ℝ) x * 𝓗 N v (Ψ : Conf N → ℝ) x)
        / (√ (∫ x in box N L, (Ψ : Conf N → ℝ) x * (Ψ : Conf N → ℝ) x)) ^ 2) :=
  ⟨0, by rintro _ ⟨Ξ, rfl⟩; exact boxE_quot_nonneg hL hv hV Ξ⟩

/-- `boxE` is at most the quotient of any box state, in gradient form. -/
lemma boxE_le_quot_of_gradForm {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ} (hv : 0 ≤ v)
    (hV : IntOnBox N L (Vpot N v)) (Ψ : CInfty0Box N L) :
    boxE N L v
      ≤ ((∫ x in box N L, ∑ i : Fin N, ∑ k : Fin 3,
            (fderiv ℝ (Ψ : Conf N → ℝ) x (kcDir N i k)) ^ 2)
          + ∫ x in box N L, Vpot N v x * ((Ψ : Conf N → ℝ) x) ^ 2)
        / (∫ x in box N L, ((Ψ : Conf N → ℝ) x) ^ 2) := by
  have h1 : boxE N L v
      ≤ (∫ x in box N L, (Ψ : Conf N → ℝ) x * 𝓗 N v (Ψ : Conf N → ℝ) x)
        / (√ (∫ x in box N L, (Ψ : Conf N → ℝ) x * (Ψ : Conf N → ℝ) x)) ^ 2 :=
    ciInf_le (boxE_quot_bddBelow hL hv hV) Ψ
  rwa [boxE_quot_eq_gradForm hL hV Ψ] at h1

/-- `boxE` is at most the Dirichlet quotient of the graph point of any nonzero test
function. -/
theorem boxE_le_quot_testSub {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ} (hv : 0 ≤ v)
    (hV : IntOnBox N L (Vpot N v)) (F : testSub N L) (hF : (F : Conf N → ℝ) ≠ 0) :
    boxE N L v
      ≤ (gSq (graphPoint N L F) + potSq (Vpot N v) (graphPoint N L F))
          / l2Sq (graphPoint N L F) := by
  have h1 := boxE_le_quot_of_gradForm hL hv hV (testToBox F hF)
  simp only [testToBox_coe] at h1
  rw [← quot_graphPoint_eq F] at h1
  simpa using h1

/-! ## The truncated box energy is at most the box energy -/

/-- `boxEnergyTrunc` is the infimum of the truncated quotients in gradient form. -/
lemma boxEnergyTrunc_eq_iInf_gradForm {N : ℕ} {L : ℝ} {v : E3 → ℝ} {M : ℝ} :
    boxEnergyTrunc N L v M
      = ⨅ Ψ : CInfty0Box N L,
          ((∫ x in box N L, ∑ i : Fin N, ∑ k : Fin 3,
              (fderiv ℝ (Ψ : Conf N → ℝ) x (kcDir N i k)) ^ 2)
            + ∫ x in box N L, Vtrunc N v M x * ((Ψ : Conf N → ℝ) x) ^ 2)
          / (∫ x in box N L, ((Ψ : Conf N → ℝ) x) ^ 2) := rfl

lemma truncQuot_bddBelow {N : ℕ} {L : ℝ} {v : E3 → ℝ} (hv : 0 ≤ v) {M : ℝ} (hM : 0 ≤ M) :
    BddBelow (Set.range fun Ψ : CInfty0Box N L =>
      ((∫ x in box N L, ∑ i : Fin N, ∑ k : Fin 3,
          (fderiv ℝ (Ψ : Conf N → ℝ) x (kcDir N i k)) ^ 2)
        + ∫ x in box N L, Vtrunc N v M x * ((Ψ : Conf N → ℝ) x) ^ 2)
      / (∫ x in box N L, ((Ψ : Conf N → ℝ) x) ^ 2)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨Ξ, rfl⟩
  refine div_nonneg (add_nonneg ?_ ?_) (integral_nonneg fun x => sq_nonneg _)
  · exact integral_nonneg fun x => Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun k _ => sq_nonneg _
  · exact integral_nonneg fun x => mul_nonneg (Vtrunc_nonneg hv hM x) (sq_nonneg _)

/-- The truncated box energy is at most the box energy, for `M ≥ 0`. -/
theorem boxEnergyTrunc_le_boxE {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ} (hv : 0 ≤ v)
    (hV : IntOnBox N L (Vpot N v)) {M : ℝ} (hM : 0 ≤ M) :
    boxEnergyTrunc N L v M ≤ boxE N L v := by
  rw [boxEnergyTrunc_eq_iInf_gradForm]
  refine ciInf_mono (truncQuot_bddBelow hv hM) fun Ψ => ?_
  rw [boxE_quot_eq_gradForm hL hV Ψ]
  refine div_le_div_of_nonneg_right ?_ (integral_nonneg fun x => sq_nonneg _)
  refine add_le_add le_rfl ?_
  have h := integral_mono_of_nonneg (μ := volume.restrict (box N L))
    (f := fun x : Conf N => Vtrunc N v M x * ((Ψ : Conf N → ℝ) x) ^ 2)
    (g := fun x : Conf N => Vpot N v x * ((Ψ : Conf N → ℝ) x) ^ 2)
    (Eventually.of_forall fun x => mul_nonneg (Vtrunc_nonneg hv hM x) (sq_nonneg _))
    (integrableOn_Vpot_mul_sq_box hL hV Ψ)
    (Eventually.of_forall fun x =>
      mul_le_mul_of_nonneg_right (Vtrunc_le_Vpot N v M x) (sq_nonneg _))
  simpa using h

/-! ## The box quadratic form -/

/-- The box quadratic form: the kinetic energy plus the potential energy computed by the
box integral of `W (p.1)²`. -/
noncomputable def bForm (N : ℕ) (L : ℝ) (W : Conf N → ℝ) (p : Amb N) : ℝ :=
  gSq p + ∫ x in box N L, W x * ((p.1 : Conf N → ℝ) x) ^ 2

lemma bForm_smul {N : ℕ} {L : ℝ} (W : Conf N → ℝ) (c : ℝ) (p : Amb N) :
    bForm N L W (c • p) = c ^ 2 * bForm N L W p := by
  have hcoe : (((c • p : Amb N).1 : Conf N → ℝ)) =ᵐ[volume.restrict (box N L)]
      fun x => c * ((p.1 : Conf N → ℝ) x) :=
    (MeasureTheory.Lp.coeFn_smul c p.1).filter_mono MeasureTheory.ae_restrict_le
  have hcongr : (∫ x in box N L, W x * (((c • p : Amb N).1 : Conf N → ℝ) x) ^ 2)
      = ∫ x in box N L, c ^ 2 * (W x * (((p.1 : Conf N → ℝ)) x) ^ 2) := by
    refine integral_congr_ae ?_
    filter_upwards [hcoe] with x hx
    rw [hx]
    ring
  rw [bForm, bForm, gSq_smul_amb, hcongr, integral_const_mul]
  ring

lemma bForm_nonneg {N : ℕ} {L : ℝ} {W : Conf N → ℝ} (hW : 0 ≤ W) (p : Amb N) :
    0 ≤ bForm N L W p := by
  refine add_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _) ?_
  exact integral_nonneg fun x => mul_nonneg (hW x) (sq_nonneg _)

lemma bForm_graphPoint {N : ℕ} {L : ℝ} {W : Conf N → ℝ} (F : testSub N L) :
    bForm N L W (graphPoint N L F)
      = (∫ x in box N L, ∑ i : Fin N, ∑ k : Fin 3,
            (fderiv ℝ (F : Conf N → ℝ) x (kcDir N i k)) ^ 2)
          + ∫ x in box N L, W x * ((F : Conf N → ℝ) x) ^ 2 := by
  rw [bForm, gSq_graphPoint_box]
  simp only [intBox, eDir, graphPoint]
  set hmem : MemLp (F : Conf N → ℝ) 2 (volC N) :=
    memLp_of_contDiff_hasCompactSupport F.2.1 (hasCompactSupport_of_testFun F.2)
  have hae : (fun x => W x * ((MemLp.toLp (F : Conf N → ℝ) hmem : L2 N) x) ^ 2)
      =ᵐ[volume.restrict (box N L)] (fun x => W x * ((F : Conf N → ℝ) x) ^ 2) := by
    filter_upwards [(MemLp.coeFn_toLp hmem).filter_mono
      MeasureTheory.ae_restrict_le] with x hx
    rw [hx]
  rw [integral_congr_ae hae]

/-! ## Measurability and integrability of the truncated potentials on the box -/

lemma aestronglyMeasurable_Vpot_box {N : ℕ} {L : ℝ} {v : E3 → ℝ}
    (hV : IntOnBox N L (Vpot N v)) :
    AEStronglyMeasurable (Vpot N v) (volume.restrict (box N L)) :=
  hV.aestronglyMeasurable

lemma aestronglyMeasurable_Vtrunc_box {N : ℕ} {L : ℝ} {v : E3 → ℝ}
    (hV : IntOnBox N L (Vpot N v)) (M : ℝ) :
    AEStronglyMeasurable (Vtrunc N v M) (volume.restrict (box N L)) := by
  refine ((aestronglyMeasurable_Vpot_box hV).aemeasurable.min
    aemeasurable_const).aestronglyMeasurable

/-- The squared first component of an element of the energy space is integrable on the
box. -/
lemma integrableOn_sq_fst {N : ℕ} {L : ℝ} (p : Hsub N L) :
    IntegrableOn (fun x : Conf N => (((p : Amb N).1 : Conf N → ℝ) x) ^ 2) (box N L) volume :=
  (MemLp.integrable_sq (Lp.memLp ((p : Amb N).1))).integrableOn

lemma integrableOn_Vtrunc_mul_sq_box {N : ℕ} {L : ℝ} {v : E3 → ℝ} (hv : 0 ≤ v) (hL : 0 < L)
    (hV : IntOnBox N L (Vpot N v)) {M : ℝ} (hM : 0 ≤ M) (Ψ : CInfty0Box N L) :
    IntegrableOn (fun x : Conf N =>
        Vtrunc N v M x * ((Ψ : Conf N → ℝ) x) ^ 2) (box N L) volume := by
  have hcs : HasCompactSupport (fun x : Conf N => ((Ψ : Conf N → ℝ) x) ^ 2) :=
    (hasCompactSupport_Ψ hL Ψ).comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hsqint : Integrable (fun x : Conf N => ((Ψ : Conf N → ℝ) x) ^ 2)
      (volume.restrict (box N L)) :=
    (Continuous.integrable_of_hasCompactSupport ((psi_contDiff Ψ).continuous.pow 2)
      hcs).integrableOn
  have hbnd : ∀ᵐ x ∂(volume.restrict (box N L)), ‖Vtrunc N v M x‖ ≤ M := by
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Vtrunc_nonneg hv hM x)]
    exact Vtrunc_le N v M x
  exact Integrable.bdd_mul (c := M) (μ := volume.restrict (box N L)) hsqint
    (aestronglyMeasurable_Vtrunc_box hV M) hbnd

lemma integrableOn_Vtrunc_mul_sq_hsub {N : ℕ} {L : ℝ} {v : E3 → ℝ} (hv : 0 ≤ v)
    (hV : IntOnBox N L (Vpot N v)) {M : ℝ} (hM : 0 ≤ M) (p : Hsub N L) :
    IntegrableOn (fun x : Conf N =>
        Vtrunc N v M x * (((p : Amb N).1 : Conf N → ℝ) x) ^ 2) (box N L) volume := by
  refine Integrable.bdd_mul (c := M) (μ := volume.restrict (box N L)) (integrableOn_sq_fst p)
    (aestronglyMeasurable_Vtrunc_box hV M) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (Vtrunc_nonneg hv hM x)]
  exact Vtrunc_le N v M x

/-! ## The main theorem -/

set_option maxHeartbeats 32000000 in
theorem tendsto_boxEnergyTrunc {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ} (hv : 0 ≤ v)
    (hV : IntOnBox N L (Vpot N v)) :
    Filter.Tendsto (fun M : ℕ => boxEnergyTrunc N L v M) Filter.atTop
      (nhds (boxE N L v)) := by
  -- monotonicity in the truncation level
  have hmono : Monotone fun M : ℕ => boxEnergyTrunc N L v M := by
    intro m n hmn
    show boxEnergyTrunc N L v (m : ℝ) ≤ boxEnergyTrunc N L v (n : ℝ)
    rw [boxEnergyTrunc_eq_iInf_gradForm, boxEnergyTrunc_eq_iInf_gradForm]
    refine ciInf_mono (truncQuot_bddBelow hv (Nat.cast_nonneg m)) fun Ψ => ?_
    refine div_le_div_of_nonneg_right (add_le_add le_rfl ?_)
      (integral_nonneg fun x => sq_nonneg _)
    exact integral_mono_of_nonneg
      (Eventually.of_forall fun x =>
        mul_nonneg (Vtrunc_nonneg hv (Nat.cast_nonneg m) x) (sq_nonneg _))
      (integrableOn_Vtrunc_mul_sq_box hv hL hV (Nat.cast_nonneg n) Ψ)
      (Eventually.of_forall fun x =>
        mul_le_mul_of_nonneg_right (Vtrunc_mono N v (by exact_mod_cast hmn) x) (sq_nonneg _))
  -- the easy bound and the value of the supremum
  have hle : ∀ M : ℕ, boxEnergyTrunc N L v M ≤ boxE N L v := fun M =>
    boxEnergyTrunc_le_boxE hL hv hV (Nat.cast_nonneg M)
  have hbdd : BddAbove (Set.range fun M : ℕ => boxEnergyTrunc N L v M) :=
    ⟨boxE N L v, by rintro _ ⟨M, rfl⟩; exact hle M⟩
  have hsup : ⨆ M : ℕ, boxEnergyTrunc N L v M = boxE N L v := by
    refine le_antisymm (ciSup_le hle) ?_
    by_contra hcon
    push Not at hcon
    obtain ⟨ε, hε0, hε⟩ : ∃ ε : ℝ, 0 < ε ∧
        (⨆ M : ℕ, boxEnergyTrunc N L v M) + 2 * ε ≤ boxE N L v :=
      ⟨(boxE N L v - ⨆ M : ℕ, boxEnergyTrunc N L v M) / 4,
        by linarith [hcon], by linarith [hcon]⟩
    -- near-minimisers of the truncated problems, normalised inside the energy space
    have hsel : ∀ n : ℕ, ∃ p : Hsub N L, l2Sq (p : Amb N) = 1 ∧
        bForm N L (Vtrunc N v (n : ℝ)) (p : Amb N) < boxE N L v - ε := by
      intro n
      haveI : Nonempty (CInfty0Box N L) := nonempty_CInfty0Box N hL
      have h2 : (⨅ Ψ : CInfty0Box N L,
          ((∫ x in box N L, ∑ i : Fin N, ∑ k : Fin 3,
              (fderiv ℝ (Ψ : Conf N → ℝ) x (kcDir N i k)) ^ 2)
            + ∫ x in box N L, Vtrunc N v (n : ℝ) x * ((Ψ : Conf N → ℝ) x) ^ 2)
          / (∫ x in box N L, ((Ψ : Conf N → ℝ) x) ^ 2)) < boxE N L v - ε := by
        rw [← boxEnergyTrunc_eq_iInf_gradForm]
        have h1 : boxEnergyTrunc N L v (n : ℝ) ≤ ⨆ M : ℕ, boxEnergyTrunc N L v M :=
          le_ciSup hbdd n
        linarith
      obtain ⟨Ψ, hΨ⟩ := exists_lt_of_ciInf_lt h2
      have hF : (boxToTest N L Ψ : Conf N → ℝ) ≠ 0 := fun h0 =>
        Ψ.nezero (by rw [← boxToTest_coe]; exact h0)
      have hpos : 0 < l2Sq (graphPoint N L (boxToTest N L Ψ)) :=
        pos_l2Sq_graphPoint (boxToTest N L Ψ) hF
      refine ⟨(Real.sqrt (l2Sq (graphPoint N L (boxToTest N L Ψ))))⁻¹
        • (⟨graphPoint N L (boxToTest N L Ψ), graphPoint_mem_Hsub_self _⟩ : Hsub N L),
        ?_, ?_⟩
      · change l2Sq ((Real.sqrt (l2Sq (graphPoint N L (boxToTest N L Ψ))))⁻¹
            • (graphPoint N L (boxToTest N L Ψ))) = 1
        rw [l2Sq_smul_amb, inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
      · have hD : (∫ x in box N L, ((Ψ : Conf N → ℝ) x) ^ 2)
            = l2Sq (graphPoint N L (boxToTest N L Ψ)) := by
          rw [l2Sq_graphPoint_box]
          simp only [intBox, boxToTest_coe]
        have hQ : bForm N L (Vtrunc N v (n : ℝ)) (graphPoint N L (boxToTest N L Ψ))
            = (∫ x in box N L, ∑ i : Fin N, ∑ k : Fin 3,
                  (fderiv ℝ (Ψ : Conf N → ℝ) x (kcDir N i k)) ^ 2)
              + ∫ x in box N L, Vtrunc N v (n : ℝ) x * ((Ψ : Conf N → ℝ) x) ^ 2 := by
          rw [bForm_graphPoint]
          simp only [boxToTest_coe]
        change bForm N L (Vtrunc N v (n : ℝ))
            ((Real.sqrt (l2Sq (graphPoint N L (boxToTest N L Ψ))))⁻¹
              • (graphPoint N L (boxToTest N L Ψ))) < boxE N L v - ε
        have hc2 : (Real.sqrt (l2Sq (graphPoint N L (boxToTest N L Ψ))))⁻¹ ^ 2
            = (∫ x in box N L, ((Ψ : Conf N → ℝ) x) ^ 2)⁻¹ := by
          rw [inv_pow, Real.sq_sqrt hpos.le, hD]
        rw [bForm_smul, hQ, hc2, mul_comm, ← div_eq_mul_inv]
        exact hΨ
    choose p hp1 hp2 using hsel
    -- the hypotheses of the liminf lemma
    have hC : ∀ n : ℕ, gSq ((p n : Amb N)) ≤ boxE N L v - ε := by
      intro n
      have h1 := hp2 n
      have h2 : 0 ≤ ∫ x in box N L,
          Vtrunc N v (n : ℝ) x * (((p n : Amb N).1 : Conf N → ℝ) x) ^ 2 :=
        integral_nonneg fun x => mul_nonneg (Vtrunc_nonneg hv (Nat.cast_nonneg n) x) (sq_nonneg _)
      simp only [bForm] at h1
      linarith
    have hW0 : ∀ n : ℕ, 0 ≤ Vtrunc N v (n : ℝ) := fun n x =>
      Vtrunc_nonneg hv (Nat.cast_nonneg n) x
    have hWlim0 : 0 ≤ Vpot N v := fun x => Vpot_nonneg hv x
    have hWm : ∀ n : ℕ, AEStronglyMeasurable (Vtrunc N v (n : ℝ))
        (volume.restrict (box N L)) := fun n => aestronglyMeasurable_Vtrunc_box hV _
    have hWmono : ∀ n : ℕ, ∀ x, Vtrunc N v (n : ℝ) x ≤ Vtrunc N v ((n + 1 : ℕ) : ℝ) x :=
      fun n x => Vtrunc_mono N v (by push_cast; linarith) x
    have hWtend : ∀ x, Filter.Tendsto (fun n : ℕ => Vtrunc N v (n : ℝ) x) Filter.atTop
        (nhds (Vpot N v x)) := by
      intro x
      have hev : (fun n : ℕ => Vtrunc N v (n : ℝ) x) =ᶠ[Filter.atTop]
          (fun _ => Vpot N v x) := by
        refine Filter.eventually_atTop.2 ⟨Nat.ceil (Vpot N v x), fun n hn => ?_⟩
        refine min_eq_left ?_
        calc Vpot N v x ≤ (Nat.ceil (Vpot N v x) : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by exact_mod_cast hn
      exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds
    have hCi : ∀ n : ℕ, IntegrableOn (fun x : Conf N =>
        Vtrunc N v (n : ℝ) x * (((p n : Amb N).1 : Conf N → ℝ) x) ^ 2) (box N L) volume :=
      fun n => integrableOn_Vtrunc_mul_sq_hsub hv hV (Nat.cast_nonneg n) (p n)
    have hCb : ∀ n : ℕ, ∫ x in box N L,
        Vtrunc N v (n : ℝ) x * (((p n : Amb N).1 : Conf N → ℝ) x) ^ 2 ≤ boxE N L v - ε := by
      intro n
      have h1 := hp2 n
      have h2 : 0 ≤ gSq ((p n : Amb N)) := Finset.sum_nonneg fun j _ => sq_nonneg _
      simp only [bForm] at h1
      linarith
    obtain ⟨φ, hφ, q, hq1, hqint, hqbound⟩ :=
      hsub_liminf_energy (C := boxE N L v - ε) (C' := boxE N L v - ε) (p := p)
        (W := fun n : ℕ => Vtrunc N v (n : ℝ)) (Wlim := Vpot N v)
        hp1 hC hW0 hWlim0 hWm (aestronglyMeasurable_Vpot_box hV) hWmono hWtend hCi hCb
    -- the limit point has energy below `boxE - ε`
    have hlimb : ∀ n : ℕ, gSq ((p n : Amb N))
        + ∫ x in box N L, Vtrunc N v (n : ℝ) x
            * (((p n : Amb N).1 : Conf N → ℝ) x) ^ 2 ≤ boxE N L v - ε :=
      fun n => le_of_lt (by simpa only [bForm] using hp2 n)
    have hlim : ∀ᶠ n : ℕ in Filter.atTop,
        gSq ((p (φ n) : Amb N))
          + ∫ x in box N L, Vtrunc N v ((φ n : ℕ) : ℝ) x
              * (((p (φ n) : Amb N).1 : Conf N → ℝ) x) ^ 2 ≤ boxE N L v - ε :=
      Eventually.of_forall fun n => hlimb (φ n)
    have hu0 : ∀ n : ℕ, 0 ≤ gSq ((p (φ n) : Amb N))
        + ∫ x in box N L, Vtrunc N v ((φ n : ℕ) : ℝ) x
            * (((p (φ n) : Amb N).1 : Conf N → ℝ) x) ^ 2 := by
      intro n
      refine add_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _) ?_
      exact integral_nonneg fun x => mul_nonneg
        (Vtrunc_nonneg hv (Nat.cast_nonneg (φ n)) x) (sq_nonneg _)
    have hbd : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
        (fun n : ℕ => gSq ((p (φ n) : Amb N))
          + ∫ x in box N L, Vtrunc N v ((φ n : ℕ) : ℝ) x
              * (((p (φ n) : Amb N).1 : Conf N → ℝ) x) ^ 2) :=
      ⟨0, Filter.eventually_map.mpr (Eventually.of_forall hu0)⟩
    have hqE : gSq (q : Amb N) + ∫ x in box N L,
        Vpot N v x * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2 ≤ boxE N L v - ε :=
      le_trans hqbound
        (Filter.liminf_le_of_frequently_le (Filter.Eventually.frequently hlim) hbd)
    -- realise that energy by a smooth test function
    have hVb : 0 < (volume (box N L)).toReal := volume_box_pos (N := N) hL
    obtain ⟨F, hFne, hFbound⟩ :=
      exists_testSub_quot_le (L := L) hL (V := Vpot N v) (fun x => Vpot_nonneg hv x) hV
        q hq1 hqint (show (0 : ℝ) < ε / (2 * (volume (box N L)).toReal) from
          div_pos hε0 (by linarith))
    -- the constant `ε / (2 |box|)` sits inside the box integral; its integral is `ε / 2`
    have hvol_lt : volume (box N L) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      rw [htop] at hVb
      simp at hVb
    have hconst_int : IntegrableOn
        (fun _ : Conf N => ε / (2 * (volume (box N L)).toReal)) (box N L) volume := by
      rw [IntegrableOn]
      refine integrable_const_iff.mpr (Or.inr ?_)
      rw [isFiniteMeasure_iff, Measure.restrict_apply_univ]
      exact hvol_lt
    have hconst : (∫ x in box N L, ε / (2 * (volume (box N L)).toReal)) = ε / 2 := by
      rw [setIntegral_const, measureReal_def, smul_eq_mul,
        mul_comm (volume (box N L)).toReal, div_mul_eq_mul_div,
        mul_div_mul_right ε 2 (ne_of_gt hVb)]
    have hsplit : (∫ x in box N L, (Vpot N v x * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2
          + ε / (2 * (volume (box N L)).toReal)))
        = (∫ x in box N L, Vpot N v x * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2) + ε / 2 := by
      rw [integral_add hqint hconst_int, hconst]
    -- contradiction with the definition of `boxE`
    have hF0 : (F : Conf N → ℝ) ≠ 0 := by
      intro h0
      apply hFne
      rw [l2Sq_graphPoint_box]
      simp only [intBox]
      simp [h0]
    have h := boxE_le_quot_testSub hL hv hV F hF0
    have hcontra : boxE N L v ≤ (gSq (q : Amb N)
        + ∫ x in box N L, Vpot N v x * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2) + ε / 2 := by
      refine le_trans h (le_trans hFbound ?_)
      rw [hsplit]
      exact le_of_eq (by ring)
    have h3 : boxE N L v ≤ boxE N L v - ε / 2 := by
      linarith only [hqE, hcontra]
    linarith only [h3, hε0]
  -- conclude from monotone convergence
  have htend := tendsto_atTop_ciSup hmono hbdd
  rwa [hsup] at htend

end

end Work.BoseSym.Bridge
