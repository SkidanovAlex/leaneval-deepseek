import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.UBBInputs2.aemeasurable_comp_sub_coord
import Submission.Work.UBBInputs2.aemeasurable_comp_sub_index
import Submission.Work.UBBInputs2.exists_integral_u_wSmall1Pair_fibre_bound
import Submission.Work.UBBInputs2.exists_integral_u_wSmallPair_bound
import Submission.Work.UBBInputs2.integrable_pairSum_v
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of the joint `(u,x)`-integrand of the localised potential word

`Work.UBBInputs2.integrable_qLHSBIntegrand` is the bookkeeping input consumed by
`Work.UBBInputs2.LocPotential` (field `hint` of `BoxSumBoundKernel` /
`boxSumBoundCanon_of_kernel`): the joint integrand
`(u,x) ↦ qLHSBIntegrand h M L d (dens N L) Φ u x` is `Integrable` for the product measure
`volume.prod volume` on `ℝ³ × X N`, for a compactly supported continuous `Φ`.

The proof follows Mathlib's fibre criterion `MeasureTheory.integrable_prod_iff'`:
a.e.-measurability of the integrand (delegated pieces
`aemeasurable_comp_sub_index` / `aemeasurable_comp_sub_coord` handle the only non-trivial
point, the composition of the merely a.e.-measurable `v` and `g₀` with `x ↦ x i - y`),
fibre integrability in `u` (from the existing sliding-variable integrability lemmas), and an
integrable dominating function for the fibre norm integral, obtained from the uniform-in-`a`
kernel bounds (`exists_integral_u_wSmall1Pair_fibre_bound`, `exists_integral_u_wSmallPair_bound`)
together with `integrable_pairSum_v`.
-/

noncomputable section
open MeasureTheory Metric
open scoped Real BigOperators ENNReal Topology

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace Work.UBBInputs2

open Submission.BoseGases

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

theorem integrable_qLHSBIntegrand {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {d M : ℕ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    (hR0 : 0 < R0) (hv1 : MeasureTheory.MemLp v 1) (hM : 1 ≤ M) (hd : (0 : ℝ) < (d : ℝ))
    (hdR : ∀ L : ℝ, 1 ≤ L → R0 ≤ (L * (d : ℝ)) / 16)
    (hdRχ : ∀ L : ℝ, 1 ≤ L → R0 ≤ L * chiR0)
    {L : ℝ} (hL : 1 ≤ L) {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) (hΦs : HasCompactSupport Φ) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
        Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ) (Work.UBB.dens N L) Φ p.1 p.2) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hR' : R0 ≤ (L * (d : ℝ)) / 16 := hdR L hL
  have hRχ : R0 ≤ L * chiR0 := hdRχ L hL
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    exists_integral_u_wSmall1Pair_fibre_bound hv_supp hR0 h hM hLpos hd hR' hRχ
  obtain ⟨C₂, hC₂0, hC₂⟩ :=
    exists_integral_u_wSmallPair_bound hv_supp hR0 hM hLpos hd hR' hRχ
  have hval : ∀ (u : ℝ³) (x : X N),
      Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ) (Work.UBB.dens N L) Φ u x
        = Φ x ^ 2 * ((-(Work.UBB.dens N L)) *
              (∑ i : Fin N, ∫ y in acube L, wSmall1Pair h M L (d : ℝ) u (x i) y)
            + (1 / 2) * (∑ q ∈ pairSet N,
                wSmallPair M L (d : ℝ) u v (x q.1) (x q.2))) := by
    intro u x
    simp only [Work.SmallBoxSliding.qLHSBIntegrand]
    try ring
  have hvd : AEMeasurable v (volume : Measure ℝ³) := hv1.aestronglyMeasurable.aemeasurable
  have hg0 : AEMeasurable (g0 v h) (volume : Measure ℝ³) :=
    (g0_integrable hR0 hv_supp h).aemeasurable
  have hpair : ∀ q : Fin N × Fin N, AEMeasurable
      (fun p : ℝ³ × X N => wSmallPair M L (d : ℝ) p.1 v (p.2 q.1) (p.2 q.2))
      ((volume : Measure ℝ³).prod (volume : Measure (X N))) := by
    intro q
    have hA : AEMeasurable (fun p : ℝ³ × X N => chiSmallB M L (d : ℝ) p.1 (p.2 q.1))
        ((volume : Measure ℝ³).prod (volume : Measure (X N))) :=
      (Work.SmallBoxSliding.chiSmallB_continuous_joint M L (d : ℝ) q.1).aemeasurable
    have hC : AEMeasurable (fun p : ℝ³ × X N => chiSmallB M L (d : ℝ) p.1 (p.2 q.2))
        ((volume : Measure ℝ³).prod (volume : Measure (X N))) :=
      (Work.SmallBoxSliding.chiSmallB_continuous_joint M L (d : ℝ) q.2).aemeasurable
    have hnum : AEMeasurable (fun p : ℝ³ × X N => v (p.2 q.1 - p.2 q.2))
        ((volume : Measure ℝ³).prod (volume : Measure (X N))) :=
      (aemeasurable_comp_sub_index hvd q.1 q.2).aemeasurable
    have hden : AEMeasurable
        (fun p : ℝ³ × X N => convScaleSmall M (L * (d : ℝ)) (p.2 q.1 - p.2 q.2))
        ((volume : Measure ℝ³).prod (volume : Measure (X N))) := by
      apply Continuous.aemeasurable
      unfold convScaleSmall
      exact (conv3Small_continuous hM).comp
        ((((continuous_apply q.1).comp continuous_snd).sub
          ((continuous_apply q.2).comp continuous_snd)).const_smul ((L * (d : ℝ))⁻¹))
    have hW0 : AEMeasurable
        (fun p : ℝ³ × X N => wSmallScaled M (L * (d : ℝ)) v (p.2 q.1 - p.2 q.2))
        ((volume : Measure ℝ³).prod (volume : Measure (X N))) := by
      refine (hnum.div hden).congr (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Pi.div_apply, wSmallScaled]
    have hcv : AEMeasurable (fun p : ℝ³ × X N => convScale L (p.2 q.1 - p.2 q.2))
        ((volume : Measure ℝ³).prod (volume : Measure (X N))) :=
      ((convScale_continuous L).comp
        (((continuous_apply q.1).comp continuous_snd).sub
          ((continuous_apply q.2).comp continuous_snd))).aemeasurable
    have hW : AEMeasurable
        (fun p : ℝ³ × X N => wSmallScaled M (L * (d : ℝ)) v (p.2 q.1 - p.2 q.2)
          / convScale L (p.2 q.1 - p.2 q.2))
        ((volume : Measure ℝ³).prod (volume : Measure (X N))) := hW0.div hcv
    refine ((hA.mul hW).mul hC).congr (Filter.Eventually.of_forall (fun p => ?_))
    simp only [Pi.mul_apply, Pi.div_apply, wSmallPair]
  have hone : ∀ i : Fin N, AEStronglyMeasurable
      (fun p : ℝ³ × X N => ∫ y in acube L, wSmall1Pair h M L (d : ℝ) p.1 (p.2 i) y)
      ((volume : Measure ℝ³).prod (volume : Measure (X N))) := by
    intro i
    have hchiA : AEMeasurable
        (fun q : (ℝ³ × X N) × ℝ³ => chiSmallB M L (d : ℝ) q.1.1 (q.1.2 i))
        (((volume : Measure ℝ³).prod (volume : Measure (X N))).prod
          ((volume : Measure ℝ³).restrict (acube L))) :=
      ((Work.SmallBoxSliding.chiSmallB_continuous_joint M L (d : ℝ) i).comp
        continuous_fst).aemeasurable
    have hchiC_cont : Continuous
        (fun q : (ℝ³ × X N) × ℝ³ => chiSmallB M L (d : ℝ) q.1.1 q.2) := by
      unfold chiSmallB
      refine Continuous.mul ?_ ?_
      · exact (chiScale_continuous L).comp continuous_snd
      · exact (chiSmall_continuous hM).comp
          (((continuous_snd.const_smul ((L * (d : ℝ))⁻¹)).sub
            (continuous_fst.comp continuous_fst)))
    have hchiC : AEMeasurable
        (fun q : (ℝ³ × X N) × ℝ³ => chiSmallB M L (d : ℝ) q.1.1 q.2)
        (((volume : Measure ℝ³).prod (volume : Measure (X N))).prod
          ((volume : Measure ℝ³).restrict (acube L))) := hchiC_cont.aemeasurable
    have hnum : AEMeasurable (fun q : (ℝ³ × X N) × ℝ³ => g0 v h (q.1.2 i - q.2))
        (((volume : Measure ℝ³).prod (volume : Measure (X N))).prod
          ((volume : Measure ℝ³).restrict (acube L))) :=
      (aemeasurable_comp_sub_coord hg0 i L).aemeasurable
    have hden : AEMeasurable
        (fun q : (ℝ³ × X N) × ℝ³ => convScaleSmall M (L * (d : ℝ)) (q.1.2 i - q.2))
        (((volume : Measure ℝ³).prod (volume : Measure (X N))).prod
          ((volume : Measure ℝ³).restrict (acube L))) := by
      apply Continuous.aemeasurable
      unfold convScaleSmall
      exact (conv3Small_continuous hM).comp
        ((((continuous_apply i).comp (continuous_snd.comp continuous_fst)).sub
          continuous_snd).const_smul ((L * (d : ℝ))⁻¹))
    have hW0 : AEMeasurable
        (fun q : (ℝ³ × X N) × ℝ³ => wSmallScaled M (L * (d : ℝ)) (g0 v h) (q.1.2 i - q.2))
        (((volume : Measure ℝ³).prod (volume : Measure (X N))).prod
          ((volume : Measure ℝ³).restrict (acube L))) := by
      refine (hnum.div hden).congr (Filter.Eventually.of_forall (fun q => ?_))
      simp only [Pi.div_apply, wSmallScaled]
    have hcv : AEMeasurable
        (fun q : (ℝ³ × X N) × ℝ³ => convScale L (q.1.2 i - q.2))
        (((volume : Measure ℝ³).prod (volume : Measure (X N))).prod
          ((volume : Measure ℝ³).restrict (acube L))) :=
      ((convScale_continuous L).comp
        (((continuous_apply i).comp (continuous_snd.comp continuous_fst)).sub
          continuous_snd)).aemeasurable
    have hW : AEMeasurable
        (fun q : (ℝ³ × X N) × ℝ³ => wSmallScaled M (L * (d : ℝ)) (g0 v h) (q.1.2 i - q.2)
          / convScale L (q.1.2 i - q.2))
        (((volume : Measure ℝ³).prod (volume : Measure (X N))).prod
          ((volume : Measure ℝ³).restrict (acube L))) := hW0.div hcv
    have hjoint : AEStronglyMeasurable
        (fun q : (ℝ³ × X N) × ℝ³ => wSmall1Pair h M L (d : ℝ) q.1.1 (q.1.2 i) q.2)
        (((volume : Measure ℝ³).prod (volume : Measure (X N))).prod
          ((volume : Measure ℝ³).restrict (acube L))) := by
      refine ((hchiA.mul hW).mul hchiC).aestronglyMeasurable.congr
        (Filter.Eventually.of_forall (fun q => ?_))
      simp only [Pi.mul_apply, Pi.div_apply, wSmall1Pair, wSmallPair]
    exact AEStronglyMeasurable.integral_prod_right' hjoint
  have hSmeas : AEMeasurable
      (fun p : ℝ³ × X N => ∑ i : Fin N,
        ∫ y in acube L, wSmall1Pair h M L (d : ℝ) p.1 (p.2 i) y)
      ((volume : Measure ℝ³).prod (volume : Measure (X N))) := by
    refine (Finset.aemeasurable_sum (Finset.univ)
      (fun (i : Fin N) (_ : i ∈ Finset.univ) => (hone i).aemeasurable)).congr
      (Filter.Eventually.of_forall (fun p => ?_))
    simp only [Finset.sum_apply]
  have hTmeas : AEMeasurable
      (fun p : ℝ³ × X N => ∑ q ∈ pairSet N,
        wSmallPair M L (d : ℝ) p.1 v (p.2 q.1) (p.2 q.2))
      ((volume : Measure ℝ³).prod (volume : Measure (X N))) := by
    refine (Finset.aemeasurable_sum (pairSet N)
      (fun (q : Fin N × Fin N) (_ : q ∈ pairSet N) => hpair q)).congr
      (Filter.Eventually.of_forall (fun p => ?_))
    simp only [Finset.sum_apply]
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ³ × X N => Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ)
        (Work.UBB.dens N L) Φ p.1 p.2)
      ((volume : Measure ℝ³).prod (volume : Measure (X N))) := by
    have hΦ2 : AEMeasurable (fun p : ℝ³ × X N => Φ p.2 ^ 2)
        ((volume : Measure ℝ³).prod (volume : Measure (X N))) :=
      (hΦc.aemeasurable.comp_snd).pow_const 2
    have hinner : AEMeasurable
        (fun p : ℝ³ × X N => (-(Work.UBB.dens N L)) *
              (∑ i : Fin N, ∫ y in acube L, wSmall1Pair h M L (d : ℝ) p.1 (p.2 i) y)
            + (1 / 2) * (∑ q ∈ pairSet N,
                wSmallPair M L (d : ℝ) p.1 v (p.2 q.1) (p.2 q.2)))
        ((volume : Measure ℝ³).prod (volume : Measure (X N))) :=
      (AEMeasurable.const_mul hSmeas (-(Work.UBB.dens N L))).add
        (AEMeasurable.const_mul hTmeas (1 / 2))
    have hfun : (fun p : ℝ³ × X N => Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ)
          (Work.UBB.dens N L) Φ p.1 p.2)
        = fun p : ℝ³ × X N => Φ p.2 ^ 2 * ((-(Work.UBB.dens N L)) *
              (∑ i : Fin N, ∫ y in acube L, wSmall1Pair h M L (d : ℝ) p.1 (p.2 i) y)
            + (1 / 2) * (∑ q ∈ pairSet N,
                wSmallPair M L (d : ℝ) p.1 v (p.2 q.1) (p.2 q.2))) := by
      funext p
      exact hval p.1 p.2
    rw [hfun]
    exact (hΦ2.mul hinner).aestronglyMeasurable
  have hfib : ∀ x : X N, Integrable
      (fun u : ℝ³ => Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ)
        (Work.UBB.dens N L) Φ u x) (volume : Measure ℝ³) := by
    intro x
    have hSint : Integrable
        (fun u : ℝ³ => ∑ i : Fin N, ∫ y in acube L, wSmall1Pair h M L (d : ℝ) u (x i) y)
        (volume : Measure ℝ³) :=
      integrable_finsetSum _ (fun i _ =>
        (Work.SmallBoxSliding.integrable_wSmall1Pair_prod hv_supp hR0 h hM hLpos hd hR' hRχ (x i)).integral_prod_left)
    have hTint : Integrable
        (fun u : ℝ³ => ∑ q ∈ pairSet N, wSmallPair M L (d : ℝ) u v (x q.1) (x q.2))
        (volume : Measure ℝ³) :=
      integrable_finsetSum _ (fun q _ => Work.SmallBoxSliding.integrable_wSmallPair_u hM hLpos hd v (x q.1) (x q.2))
    have h3 : Integrable
        (fun u : ℝ³ => (-(Work.UBB.dens N L)) *
              (∑ i : Fin N, ∫ y in acube L, wSmall1Pair h M L (d : ℝ) u (x i) y)
            + (1 / 2) * (∑ q ∈ pairSet N, wSmallPair M L (d : ℝ) u v (x q.1) (x q.2)))
        (volume : Measure ℝ³) :=
      (hSint.const_mul (-(Work.UBB.dens N L))).add (hTint.const_mul (1 / 2))
    refine (h3.const_mul (Φ x ^ 2)).congr (Filter.Eventually.of_forall (fun u => ?_))
    exact (hval u x).symm
  set K : X N → ℝ := fun x => Φ x ^ 2 * (|Work.UBB.dens N L| * (N : ℝ) * C₁
      + (1 / 2) * C₂ * ∑ q ∈ pairSet N, ‖v (x q.1 - x q.2)‖) with hK
  have hKint : Integrable K (volume : Measure (X N)) := by
    have hΦ2 : Integrable (fun x : X N => Φ x ^ 2) (volume : Measure (X N)) := by
      refine integrable_of_continuous_hasCompactSupport ?_ ?_
      · fun_prop
      · simpa only [Function.comp_def] using
          (hΦs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
    have h1 : Integrable (fun x : X N => Φ x ^ 2 * (|Work.UBB.dens N L| * (N : ℝ) * C₁))
        (volume : Measure (X N)) := hΦ2.mul_const _
    have h2 : Integrable (fun x : X N => (1 / 2) * C₂ *
        (Φ x ^ 2 * ∑ q ∈ pairSet N, ‖v (x q.1 - x q.2)‖)) (volume : Measure (X N)) :=
      (integrable_pairSum_v hv1 hΦc hΦs).const_mul ((1 / 2) * C₂)
    have hcongr : ((fun x : X N => Φ x ^ 2 * (|Work.UBB.dens N L| * (N : ℝ) * C₁))
          + fun x : X N => (1 / 2) * C₂ * (Φ x ^ 2 * ∑ q ∈ pairSet N, ‖v (x q.1 - x q.2)‖))
        =ᵐ[volume] K := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Pi.add_apply, hK]
      ring
    exact Integrable.congr (h1.add h2) hcongr
  have hbound : ∀ x : X N, ∫ u : ℝ³, ‖Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ)
        (Work.UBB.dens N L) Φ u x‖ ≤ K x := by
    intro x
    let S : ℝ³ → ℝ := fun u =>
      ∑ i : Fin N, ∫ y in acube L, wSmall1Pair h M L (d : ℝ) u (x i) y
    let T : ℝ³ → ℝ := fun u =>
      ∑ q ∈ pairSet N, wSmallPair M L (d : ℝ) u v (x q.1) (x q.2)
    let Z : ℝ³ → ℝ := fun u => (-(Work.UBB.dens N L)) * S u + (1 / 2) * T u
    have hSint : ∀ i : Fin N, Integrable
        (fun u : ℝ³ => ∫ y in acube L, wSmall1Pair h M L (d : ℝ) u (x i) y)
        (volume : Measure ℝ³) := fun i =>
      (Work.SmallBoxSliding.integrable_wSmall1Pair_prod hv_supp hR0 h hM hLpos hd hR' hRχ (x i)).integral_prod_left
    have hTint : ∀ q ∈ pairSet N, Integrable
        (fun u : ℝ³ => wSmallPair M L (d : ℝ) u v (x q.1) (x q.2))
        (volume : Measure ℝ³) := fun q _ =>
      Work.SmallBoxSliding.integrable_wSmallPair_u hM hLpos hd v (x q.1) (x q.2)
    have hS : Integrable S (volume : Measure ℝ³) := by
      simpa only [S] using (integrable_finsetSum (Finset.univ)
        (fun (i : Fin N) (_ : i ∈ Finset.univ) => hSint i))
    have hT : Integrable T (volume : Measure ℝ³) := by
      simpa only [T] using (integrable_finsetSum (pairSet N)
        (fun (q : Fin N × Fin N) (hq : q ∈ pairSet N) => hTint q hq))
    have hSnorm : Integrable (fun u : ℝ³ => ‖S u‖) (volume : Measure ℝ³) := hS.norm
    have hTnorm : Integrable (fun u : ℝ³ => ‖T u‖) (volume : Measure ℝ³) := hT.norm
    have hZ : Integrable Z (volume : Measure ℝ³) := by
      refine Integrable.congr
        ((hS.const_mul (-(Work.UBB.dens N L))).add (hT.const_mul (1 / 2))) ?_
      refine Filter.Eventually.of_forall (fun u => ?_)
      simp only [Pi.add_apply, Z]
    have hZnorm : Integrable (fun u : ℝ³ => ‖Z u‖) (volume : Measure ℝ³) := hZ.norm
    have hstep1 : ∫ u : ℝ³, ‖Z u‖ ≤
        ∫ u : ℝ³, (|Work.UBB.dens N L| * ‖S u‖ + (1 / 2) * ‖T u‖) := by
      refine integral_mono hZnorm ((hSnorm.const_mul _).add (hTnorm.const_mul _)) (fun u => ?_)
      calc ‖Z u‖ = ‖(-(Work.UBB.dens N L)) * S u + (1 / 2) * T u‖ := rfl
        _ ≤ ‖(-(Work.UBB.dens N L)) * S u‖ + ‖(1 / 2) * T u‖ := norm_add_le _ _
        _ = |Work.UBB.dens N L| * ‖S u‖ + (1 / 2) * ‖T u‖ := by
            have e1 : ‖(-(Work.UBB.dens N L)) * S u‖ = |Work.UBB.dens N L| * ‖S u‖ := by
              rw [norm_mul, Real.norm_eq_abs, abs_neg]
            have e2 : ‖(1 / 2 : ℝ) * T u‖ = (1 / 2) * ‖T u‖ := by
              rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
            rw [e1, e2]
    have hstep2 : ∫ u : ℝ³, (|Work.UBB.dens N L| * ‖S u‖ + (1 / 2) * ‖T u‖)
        = |Work.UBB.dens N L| * (∫ u : ℝ³, ‖S u‖) + (1 / 2) * (∫ u : ℝ³, ‖T u‖) := by
      rw [integral_add (hSnorm.const_mul _) (hTnorm.const_mul _),
        integral_const_mul, integral_const_mul]
      try ring
    have hSbd : ∫ u : ℝ³, ‖S u‖ ≤ (N : ℝ) * C₁ := by
      have h1 : ∫ u : ℝ³, ‖S u‖ ≤
          ∫ u : ℝ³, ∑ i : Fin N, ‖∫ y in acube L,
            wSmall1Pair h M L (d : ℝ) u (x i) y‖ := by
        refine integral_mono hSnorm
          (integrable_finsetSum (Finset.univ)
            (fun (i : Fin N) (_ : i ∈ Finset.univ) => (hSint i).norm)) (fun u => ?_)
        calc ‖S u‖ = ‖∑ i : Fin N, ∫ y in acube L,
                wSmall1Pair h M L (d : ℝ) u (x i) y‖ := rfl
          _ ≤ ∑ i : Fin N, ‖∫ y in acube L, wSmall1Pair h M L (d : ℝ) u (x i) y‖ :=
              norm_sum_le _ _
      have h2 : ∫ u : ℝ³, ∑ i : Fin N, ‖∫ y in acube L,
            wSmall1Pair h M L (d : ℝ) u (x i) y‖
          = ∑ i : Fin N, ∫ u : ℝ³, ‖∫ y in acube L,
            wSmall1Pair h M L (d : ℝ) u (x i) y‖ :=
        integral_finsetSum (Finset.univ)
          (fun (i : Fin N) (_ : i ∈ Finset.univ) => (hSint i).norm)
      have h3 : ∑ i : Fin N, ∫ u : ℝ³, ‖∫ y in acube L,
            wSmall1Pair h M L (d : ℝ) u (x i) y‖ ≤ ∑ _i : Fin N, C₁ :=
        Finset.sum_le_sum (fun i _ => hC₁ (x i))
      have h4 : ∑ _i : Fin N, C₁ = (N : ℝ) * C₁ := by simp
      calc ∫ u : ℝ³, ‖S u‖ ≤ ∑ i : Fin N, ∫ u : ℝ³, ‖∫ y in acube L,
            wSmall1Pair h M L (d : ℝ) u (x i) y‖ := le_trans h1 h2.le
        _ ≤ ∑ _i : Fin N, C₁ := h3
        _ = (N : ℝ) * C₁ := h4
    have hTbd : ∫ u : ℝ³, ‖T u‖ ≤ C₂ * ∑ q ∈ pairSet N, ‖v (x q.1 - x q.2)‖ := by
      have h1 : ∫ u : ℝ³, ‖T u‖ ≤
          ∫ u : ℝ³, ∑ q ∈ pairSet N, ‖wSmallPair M L (d : ℝ) u v (x q.1) (x q.2)‖ := by
        refine integral_mono hTnorm
          (integrable_finsetSum (pairSet N)
            (fun (q : Fin N × Fin N) (hq : q ∈ pairSet N) => (hTint q hq).norm))
          (fun u => ?_)
        calc ‖T u‖ = ‖∑ q ∈ pairSet N, wSmallPair M L (d : ℝ) u v (x q.1) (x q.2)‖ := rfl
          _ ≤ ∑ q ∈ pairSet N, ‖wSmallPair M L (d : ℝ) u v (x q.1) (x q.2)‖ := norm_sum_le _ _
      have h2 : ∫ u : ℝ³, ∑ q ∈ pairSet N, ‖wSmallPair M L (d : ℝ) u v (x q.1) (x q.2)‖
          = ∑ q ∈ pairSet N, ∫ u : ℝ³, ‖wSmallPair M L (d : ℝ) u v (x q.1) (x q.2)‖ :=
        integral_finsetSum (pairSet N)
          (fun (q : Fin N × Fin N) (hq : q ∈ pairSet N) => (hTint q hq).norm)
      have h3 : ∑ q ∈ pairSet N, ∫ u : ℝ³, ‖wSmallPair M L (d : ℝ) u v (x q.1) (x q.2)‖
          ≤ ∑ q ∈ pairSet N, C₂ * ‖v (x q.1 - x q.2)‖ :=
        Finset.sum_le_sum (fun q _ => hC₂ (x q.1) (x q.2))
      have h4 : ∑ q ∈ pairSet N, C₂ * ‖v (x q.1 - x q.2)‖
          = C₂ * ∑ q ∈ pairSet N, ‖v (x q.1 - x q.2)‖ :=
        (Finset.mul_sum (pairSet N) (fun q : Fin N × Fin N => ‖v (x q.1 - x q.2)‖) C₂).symm
      calc ∫ u : ℝ³, ‖T u‖
            ≤ ∑ q ∈ pairSet N, ∫ u : ℝ³, ‖wSmallPair M L (d : ℝ) u v (x q.1) (x q.2)‖ :=
              le_trans h1 h2.le
        _ ≤ ∑ q ∈ pairSet N, C₂ * ‖v (x q.1 - x q.2)‖ := h3
        _ = C₂ * ∑ q ∈ pairSet N, ‖v (x q.1 - x q.2)‖ := h4
    have hfinal : ∫ u : ℝ³, ‖Z u‖ ≤ |Work.UBB.dens N L| * ((N : ℝ) * C₁)
        + (1 / 2) * (C₂ * ∑ q ∈ pairSet N, ‖v (x q.1 - x q.2)‖) := by
      calc ∫ u : ℝ³, ‖Z u‖
          ≤ |Work.UBB.dens N L| * (∫ u : ℝ³, ‖S u‖) + (1 / 2) * (∫ u : ℝ³, ‖T u‖) :=
            le_trans hstep1 hstep2.le
        _ ≤ |Work.UBB.dens N L| * ((N : ℝ) * C₁)
              + (1 / 2) * (C₂ * ∑ q ∈ pairSet N, ‖v (x q.1 - x q.2)‖) :=
            add_le_add (mul_le_mul_of_nonneg_left hSbd (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hTbd (by norm_num))
    have hpt : ∀ u : ℝ³, ‖Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ)
          (Work.UBB.dens N L) Φ u x‖ = Φ x ^ 2 * ‖Z u‖ := by
      intro u
      rw [hval u x]
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Φ x))]
      rfl
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, hK]
    refine le_trans (mul_le_mul_of_nonneg_left hfinal (sq_nonneg (Φ x))) (le_of_eq ?_)
    ring
  have hFint : Integrable
      (fun x : X N => ∫ u : ℝ³, ‖Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ)
        (Work.UBB.dens N L) Φ u x‖) (volume : Measure (X N)) := by
    refine Integrable.mono' hKint ?_ ?_
    · have hN : AEStronglyMeasurable
          (fun z : X N × ℝ³ => ‖Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ)
            (Work.UBB.dens N L) Φ z.2 z.1‖)
          ((volume : Measure (X N)).prod (volume : Measure ℝ³)) := hmeas.prod_swap.norm
      exact AEStronglyMeasurable.integral_prod_right' (μ := (volume : Measure (X N)))
        (ν := (volume : Measure ℝ³)) hN
    · filter_upwards with x
      rw [Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))]
      exact hbound x
  have hmain : Integrable
      (fun p : ℝ³ × X N => Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ)
        (Work.UBB.dens N L) Φ p.1 p.2)
      ((volume : Measure ℝ³).prod (volume : Measure (X N))) :=
    (integrable_prod_iff' (μ := (volume : Measure ℝ³)) (ν := (volume : Measure (X N)))
      hmeas).mpr ⟨ae_of_all _ hfib, hFint⟩
  exact hmain

end Work.UBBInputs2
