import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs8.A

open MeasureTheory Metric
open scoped Real BigOperators ENNReal Topology
open Submission.BoseGases
open Work.SmallBoxSliding

/-! Round 8, strand A (the potential side of the a-priori clause list).

At the **repointed** localisation kernels the corpus telescoping identity
`Work.SmallBoxSliding.qLHSwordB_integral_u` lands on the **corpus global word**

    ∫_u qLHSwordB h M L d μ u Φ du = qLHSword L μ (wPairC L v) (wPairC L (g₀ v h)) Φ ,

an *identity* (no comparison).  It requires the *joint* integrand `qLHSBIntegrand` to be
`Integrable` on the full space `ℝ³ × X N`, which is refuted at the constant state
(`Work.UBBInputs7.Finding.not_integrable_qLHSBIntegrand_const`).  The proof only ever *uses* the
box-restricted integrability, so this module states the same identity at the *weaker*
(box-restricted) hypothesis, which `A.integrable_qLHSBIntegrand_box` supplies for every
continuous `Φ` — the repair that closes the `hpot` field of the a-priori list with no word
comparison at all. -/
theorem qLHSwordB_integral_u_box {N : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {L d μ : ℝ} (hL : 0 < L) (hd : 0 < d)
    (hR : R0 ≤ (L * d) / 16) (hRχ : R0 ≤ L * chiR0)
    {Φ : Submission.BoseGases.X N → ℝ}
    (hint : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
      Work.SmallBoxSliding.qLHSBIntegrand h M L d μ Φ p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N L)))) :
    (∫ u : EuclideanSpace ℝ (Fin 3), Work.SmallBoxSliding.qLHSwordB (N := N) h M L d μ u Φ)
      = qLHSword (N := N) L μ (wPairC L v) (wPairC L (g0 v h)) Φ := by
  have hInt_prod : Integrable (Function.uncurry (fun (u : EuclideanSpace ℝ (Fin 3))
        (x : X N) =>
      Work.SmallBoxSliding.qLHSBIntegrand h M L d μ Φ u x))
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((volume : Measure (X N)).restrict (abox N L))) := hint
  have hLHS : (∫ u : EuclideanSpace ℝ (Fin 3),
        Work.SmallBoxSliding.qLHSwordB (N := N) h M L d μ u Φ)
      = ∫ u : EuclideanSpace ℝ (Fin 3), ∫ x in abox N L,
          Work.SmallBoxSliding.qLHSBIntegrand h M L d μ Φ u x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u =>
      Work.SmallBoxSliding.qLHSwordB_eq_integral h M L d μ u Φ)
  have hswap : (∫ u : EuclideanSpace ℝ (Fin 3), ∫ x in abox N L,
          Work.SmallBoxSliding.qLHSBIntegrand h M L d μ Φ u x)
      = ∫ x in abox N L, ∫ u : EuclideanSpace ℝ (Fin 3),
          Work.SmallBoxSliding.qLHSBIntegrand h M L d μ Φ u x := by
    have hh := integral_integral_swap (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      (ν := (volume : Measure (X N)).restrict (abox N L))
      (f := fun (u : EuclideanSpace ℝ (Fin 3)) (x : X N) =>
        Work.SmallBoxSliding.qLHSBIntegrand h M L d μ Φ u x) hInt_prod
    simpa [Function.uncurry] using hh
  have hpoint : ∀ x : X N,
      (∫ u : EuclideanSpace ℝ (Fin 3),
          Work.SmallBoxSliding.qLHSBIntegrand h M L d μ Φ u x)
        = Φ x ^ 2 * (- μ * (∑ i : Fin N, w1Fibre L (wPairC L (g0 v h)) (x i))
            + (1 / 2) * (∑ q ∈ pairSet N, wPairC L v (x q.1) (x q.2))) := by
    intro x
    have hSint : ∀ i : Fin N, Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        ∫ y in acube L, wSmall1Pair h M L d u (x i) y) := by
      intro i
      have hjoint := Work.SmallBoxSliding.integrable_wSmall1Pair_prod
        hv_supp hR0 h hM hL hd hR hRχ (x i)
      simpa using hjoint.integral_prod_left
    have hTint : ∀ q ∈ pairSet N, Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        wSmallPair M L d u v (x q.1) (x q.2)) :=
      fun q _ => Work.SmallBoxSliding.integrable_wSmallPair_u hM hL hd v (x q.1) (x q.2)
    have hSval : (∫ u : EuclideanSpace ℝ (Fin 3),
          ∑ i : Fin N, ∫ y in acube L,
            wSmall1Pair h M L d u (x i) y)
        = ∑ i : Fin N, w1Fibre L (wPairC L (g0 v h)) (x i) := by
      rw [integral_finsetSum Finset.univ (fun i _ => hSint i)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [wSmall1Pair_uint_swap hv_supp hR0 h hM hL hd hR (x i)
        (Work.SmallBoxSliding.integrable_wSmall1Pair_prod hv_supp hR0 h hM hL hd hR hRχ (x i))]
      rfl
    have hTval : (∫ u : EuclideanSpace ℝ (Fin 3),
          ∑ q ∈ pairSet N, wSmallPair M L d u v (x q.1) (x q.2))
        = ∑ q ∈ pairSet N, wPairC L v (x q.1) (x q.2) := by
      rw [integral_finsetSum (pairSet N) (fun q hq => hTint q hq)]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [wSmallPair_v_uint_eq hv_supp hM hL hd hR (x q.1) (x q.2)]
      rfl
    have hB : (∫ u : EuclideanSpace ℝ (Fin 3),
          (- μ * (∑ i : Fin N, ∫ y in acube L,
              wSmall1Pair h M L d u (x i) y)
            + (1 / 2) * (∑ q ∈ pairSet N,
                wSmallPair M L d u v (x q.1) (x q.2))))
        = - μ * (∑ i : Fin N, w1Fibre L (wPairC L (g0 v h)) (x i))
          + (1 / 2) * (∑ q ∈ pairSet N, wPairC L v (x q.1) (x q.2)) := by
      have h1 : (∫ u : EuclideanSpace ℝ (Fin 3),
            (- μ * (∑ i : Fin N, ∫ y in acube L,
                wSmall1Pair h M L d u (x i) y)
              + (1 / 2) * (∑ q ∈ pairSet N,
                  wSmallPair M L d u v (x q.1) (x q.2))))
          = (∫ u : EuclideanSpace ℝ (Fin 3),
                - μ * (∑ i : Fin N, ∫ y in acube L,
                    wSmall1Pair h M L d u (x i) y))
            + (∫ u : EuclideanSpace ℝ (Fin 3),
                (1 / 2) * (∑ q ∈ pairSet N,
                    wSmallPair M L d u v (x q.1) (x q.2))) :=
        integral_add
          (f := fun u : EuclideanSpace ℝ (Fin 3) => - μ * (∑ i : Fin N,
              ∫ y in acube L, wSmall1Pair h M L d u (x i) y))
          (g := fun u : EuclideanSpace ℝ (Fin 3) => (1 / 2) * (∑ q ∈ pairSet N,
              wSmallPair M L d u v (x q.1) (x q.2)))
          ((integrable_finsetSum (s := Finset.univ) (fun i _ => hSint i)).const_mul (-μ))
          ((integrable_finsetSum (s := pairSet N) (fun q hq => hTint q hq)).const_mul (1 / 2))
      have h2 : (∫ u : EuclideanSpace ℝ (Fin 3),
            - μ * (∑ i : Fin N, ∫ y in acube L,
                wSmall1Pair h M L d u (x i) y))
          = - μ * (∫ u : EuclideanSpace ℝ (Fin 3),
              ∑ i : Fin N, ∫ y in acube L,
                wSmall1Pair h M L d u (x i) y) :=
        integral_const_mul (-μ) _
      have h3 : (∫ u : EuclideanSpace ℝ (Fin 3),
            (1 / 2) * (∑ q ∈ pairSet N,
                wSmallPair M L d u v (x q.1) (x q.2)))
          = (1 / 2) * (∫ u : EuclideanSpace ℝ (Fin 3),
              ∑ q ∈ pairSet N,
                wSmallPair M L d u v (x q.1) (x q.2)) :=
        integral_const_mul (1 / 2) _
      rw [h1, h2, h3, hSval, hTval]
    unfold Work.SmallBoxSliding.qLHSBIntegrand
    have h4 : (∫ u : EuclideanSpace ℝ (Fin 3),
          Φ x ^ 2 * (- μ * (∑ i : Fin N, ∫ y in acube L,
              wSmall1Pair h M L d u (x i) y)
            + (1 / 2) * (∑ q ∈ pairSet N,
                wSmallPair M L d u v (x q.1) (x q.2))))
        = Φ x ^ 2 * (∫ u : EuclideanSpace ℝ (Fin 3),
            (- μ * (∑ i : Fin N, ∫ y in acube L,
                wSmall1Pair h M L d u (x i) y)
              + (1 / 2) * (∑ q ∈ pairSet N,
                  wSmallPair M L d u v (x q.1) (x q.2)))) :=
      integral_const_mul (Φ x ^ 2) _
    rw [h4, hB]
  calc (∫ u : EuclideanSpace ℝ (Fin 3),
        Work.SmallBoxSliding.qLHSwordB (N := N) h M L d μ u Φ)
      = ∫ u : EuclideanSpace ℝ (Fin 3), ∫ x in abox N L,
          Work.SmallBoxSliding.qLHSBIntegrand h M L d μ Φ u x := hLHS
    _ = ∫ x in abox N L, ∫ u : EuclideanSpace ℝ (Fin 3),
          Work.SmallBoxSliding.qLHSBIntegrand h M L d μ Φ u x := hswap
    _ = ∫ x in abox N L, Φ x ^ 2 * (- μ * (∑ i : Fin N, w1Fibre L (wPairC L (g0 v h)) (x i))
          + (1 / 2) * (∑ q ∈ pairSet N, wPairC L v (x q.1) (x q.2))) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
    _ = qLHSword (N := N) L μ (wPairC L v) (wPairC L (g0 v h)) Φ := rfl

end Work.UBBInputs8.A
