import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.SmallBoxSliding.Telescope
import Submission.Work.SmallBoxSliding.integrable_wSmall1Pair_prod
import Submission.Work.SmallBoxSliding.integrable_wSmallPair_u
import Submission.Work.SmallBoxSliding.wSmall1Pair_uint_swap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `u`-partition of the localised potential word `qLHSwordB`

FS `final_v2.tex` `eq:appsliding`, potential half: integrating the localised
potential word `qLHSwordB h M ℓ d μ · Φ` over the sliding centre `u`
reproduces the **corpus global word** at the corpus bump `χ` *and* the FS
ℓ-scale renormalisation:

  `qLHSword (N) ℓ (dens N ℓ) (wPairC ℓ v) (wPairC ℓ (g₀ v h)) Φ`,

where `wPairC ℓ f x y = χ(x/ℓ)·(f(x−y)/(χ⋆χ)((x−y)/ℓ))·χ(y/ℓ)`.

At the **repointed** localisation kernels (`BoseGases.chiSmallB`, whose
`ℓ`-scale factor is the corpus bump `chiScale ℓ`, and `BoseGases.wSmallPair`,
which carries *both* the `(ℓd)`-scale and the `ℓ`-scale renormalisation) the
telescoping is an **identity**: the `u`-integral of `wSmallPair` cancels both
`(χ_M⋆χ_M)(·/(ℓd))` and `(χ⋆χ)(·/ℓ)`
(`BoseGases.chiSmallB_w_pair_uint_cancel`,
`BoseGases.chiSmallB_w1_pair_uint_cancel`), leaving exactly `wPairC`.

This is the second half of `Telescope`'s word identity
`∫_u sboxEBWord … u du = kinWordChi + qLHSword (wPairC ℓ v) (wPairC ℓ (g₀ v h))`.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators ENNReal Topology

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

theorem qLHSwordB_integral_u {N : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ (ℓ * d) / 16) (hRχ : R0 ≤ ℓ * chiR0) {Φ : Submission.BoseGases.X N → ℝ}
    (hint : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
      Work.SmallBoxSliding.qLHSBIntegrand h M ℓ d μ Φ p.1 p.2))
    (hintRef : MeasureTheory.IntegrableOn
      (Work.SmallBoxSliding.qLHSChiIntegrand h M ℓ d μ Φ) (Submission.BoseGases.abox N ℓ)) :
    (∫ u : EuclideanSpace ℝ (Fin 3), Work.SmallBoxSliding.qLHSwordB (N := N) h M ℓ d μ u Φ)
      = qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
  -- `hintRef` (integrability of the reference integrand over the analysis box) is
  -- part of the interface of the request; the identity itself only needs `hint`.
  have _hintRef := hintRef
  have hLHS : (∫ u : ℝ³, qLHSwordB (N := N) h M ℓ d μ u Φ)
      = ∫ u : ℝ³, ∫ x in abox N ℓ, qLHSBIntegrand h M ℓ d μ Φ u x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u => qLHSwordB_eq_integral h M ℓ d μ u Φ)
  have hInt_prod : Integrable (Function.uncurry (fun (u : ℝ³) (x : X N) =>
      qLHSBIntegrand h M ℓ d μ Φ u x))
      ((volume : Measure ℝ³).prod ((volume : Measure (X N)).restrict (abox N ℓ))) := by
    refine hint.mono_measure ?_
    have hpr := Measure.prod_restrict (μ := (volume : Measure ℝ³))
      (ν := (volume : Measure (X N))) (Set.univ : Set ℝ³) (abox N ℓ)
    rw [Measure.restrict_univ] at hpr
    rw [hpr]
    exact Measure.restrict_le_self
  have hswap : (∫ u : ℝ³, ∫ x in abox N ℓ, qLHSBIntegrand h M ℓ d μ Φ u x)
      = ∫ x in abox N ℓ, ∫ u : ℝ³, qLHSBIntegrand h M ℓ d μ Φ u x := by
    have hh := integral_integral_swap (μ := (volume : Measure ℝ³))
      (ν := (volume : Measure (X N)).restrict (abox N ℓ))
      (f := fun (u : ℝ³) (x : X N) => qLHSBIntegrand h M ℓ d μ Φ u x) hInt_prod
    simpa [Function.uncurry] using hh
  have hpoint : ∀ x : X N, (∫ u : ℝ³, qLHSBIntegrand h M ℓ d μ Φ u x)
      = Φ x ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
          + (1 / 2) * (∑ q ∈ pairSet N, wPairC ℓ v (x q.1) (x q.2))) := by
    intro x
    have hSint : ∀ i : Fin N, Integrable (fun u : ℝ³ =>
        ∫ y in acube ℓ, wSmall1Pair h M ℓ d u (x i) y) := by
      intro i
      have hjoint := integrable_wSmall1Pair_prod hv_supp hR0 h hM hℓ hd hR hRχ (x i)
      simpa using hjoint.integral_prod_left
    have hTint : ∀ q ∈ pairSet N, Integrable (fun u : ℝ³ =>
        wSmallPair M ℓ d u v (x q.1) (x q.2)) :=
      fun q _ => integrable_wSmallPair_u hM hℓ hd v (x q.1) (x q.2)
    have hSval : (∫ u : ℝ³, ∑ i : Fin N, ∫ y in acube ℓ, wSmall1Pair h M ℓ d u (x i) y)
        = ∑ i : Fin N, w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i) := by
      rw [integral_finsetSum Finset.univ (fun i _ => hSint i)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [wSmall1Pair_uint_swap hv_supp hR0 h hM hℓ hd hR (x i)
        (integrable_wSmall1Pair_prod hv_supp hR0 h hM hℓ hd hR hRχ (x i))]
      rfl
    have hTval : (∫ u : ℝ³, ∑ q ∈ pairSet N, wSmallPair M ℓ d u v (x q.1) (x q.2))
        = ∑ q ∈ pairSet N, wPairC ℓ v (x q.1) (x q.2) := by
      rw [integral_finsetSum (pairSet N) (fun q hq => hTint q hq)]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [wSmallPair_v_uint_eq hv_supp hM hℓ hd hR (x q.1) (x q.2)]
      rfl
    have hB : (∫ u : ℝ³, (- μ * (∑ i : Fin N, ∫ y in acube ℓ, wSmall1Pair h M ℓ d u (x i) y)
          + (1 / 2) * (∑ q ∈ pairSet N, wSmallPair M ℓ d u v (x q.1) (x q.2))))
        = - μ * (∑ i : Fin N, w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
          + (1 / 2) * (∑ q ∈ pairSet N, wPairC ℓ v (x q.1) (x q.2)) := by
      have h1 : (∫ u : ℝ³, (- μ * (∑ i : Fin N, ∫ y in acube ℓ,
              wSmall1Pair h M ℓ d u (x i) y)
            + (1 / 2) * (∑ q ∈ pairSet N, wSmallPair M ℓ d u v (x q.1) (x q.2))))
          = (∫ u : ℝ³, - μ * (∑ i : Fin N, ∫ y in acube ℓ,
                wSmall1Pair h M ℓ d u (x i) y))
            + (∫ u : ℝ³, (1 / 2) * (∑ q ∈ pairSet N,
                wSmallPair M ℓ d u v (x q.1) (x q.2))) :=
        integral_add
          (f := fun u : ℝ³ => - μ * (∑ i : Fin N, ∫ y in acube ℓ,
            wSmall1Pair h M ℓ d u (x i) y))
          (g := fun u : ℝ³ => (1 / 2) * (∑ q ∈ pairSet N,
            wSmallPair M ℓ d u v (x q.1) (x q.2)))
          ((integrable_finsetSum (s := Finset.univ) (fun i _ => hSint i)).const_mul (-μ))
          ((integrable_finsetSum (s := pairSet N) (fun q hq => hTint q hq)).const_mul (1 / 2))
      have h2 : (∫ u : ℝ³, - μ * (∑ i : Fin N, ∫ y in acube ℓ,
            wSmall1Pair h M ℓ d u (x i) y))
          = - μ * (∫ u : ℝ³, ∑ i : Fin N, ∫ y in acube ℓ,
              wSmall1Pair h M ℓ d u (x i) y) :=
        integral_const_mul (-μ) _
      have h3 : (∫ u : ℝ³, (1 / 2) * (∑ q ∈ pairSet N,
            wSmallPair M ℓ d u v (x q.1) (x q.2)))
          = (1 / 2) * (∫ u : ℝ³, ∑ q ∈ pairSet N,
              wSmallPair M ℓ d u v (x q.1) (x q.2)) :=
        integral_const_mul (1 / 2) _
      rw [h1, h2, h3, hSval, hTval]
    unfold qLHSBIntegrand
    have h4 : (∫ u : ℝ³, Φ x ^ 2 * (- μ * (∑ i : Fin N, ∫ y in acube ℓ,
            wSmall1Pair h M ℓ d u (x i) y)
          + (1 / 2) * (∑ q ∈ pairSet N, wSmallPair M ℓ d u v (x q.1) (x q.2))))
        = Φ x ^ 2 * (∫ u : ℝ³, (- μ * (∑ i : Fin N, ∫ y in acube ℓ,
            wSmall1Pair h M ℓ d u (x i) y)
          + (1 / 2) * (∑ q ∈ pairSet N, wSmallPair M ℓ d u v (x q.1) (x q.2)))) :=
      integral_const_mul (Φ x ^ 2) _
    rw [h4, hB]
  calc (∫ u : ℝ³, qLHSwordB (N := N) h M ℓ d μ u Φ)
      = ∫ u : ℝ³, ∫ x in abox N ℓ, qLHSBIntegrand h M ℓ d μ Φ u x := hLHS
    _ = ∫ x in abox N ℓ, ∫ u : ℝ³, qLHSBIntegrand h M ℓ d μ Φ u x := hswap
    _ = ∫ x in abox N ℓ, Φ x ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
          + (1 / 2) * (∑ q ∈ pairSet N, wPairC ℓ v (x q.1) (x q.2))) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
    _ = qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := rfl

end Work.SmallBoxSliding
