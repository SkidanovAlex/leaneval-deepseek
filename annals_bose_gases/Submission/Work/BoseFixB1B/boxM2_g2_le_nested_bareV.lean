import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.integrableOn_wSmallPair_cube_fixed
import Submission.Work.BoseFixB1B.integral_prod_eq_iterated_of_ae_fibre_integrable
import Submission.Work.BoseFixB1S.boxM1Info
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.boxM2_g2_le_nested_bareV`

The **bare-`v` pair-mass domination** for the sliding-box localised kernels of FS
`eq:HBU`: in the dilute regime (`R ≤ ℓ·d/16` and `R ≤ ℓ·chiR0`),

    boxM2 |B(u)| B(u) w_{B(u)}[g₂]  ≤  ∬ w_{B(u)}[v] ,

where `B(u) = dlBox ℓ d u`, `w_{B(u)}[f] = wSmallPair M ℓ d u f` and
`g₂ := v(1−ω₀)(1+ω₀)` with `ω₀ = Classical.choose h` the chosen scattering solution.

This is step (3) of the bare-`v` mass excess
(`Work.BoseFixB1B.bareVPairMassExcess`, `PerBoxRoute.md`): the pair block of `boxQSum`
(which carries the *bare* kernel `w_{B(u)}[v]`) pays the `w₁`-credit.

## The proof

* `g₂ v h z = v z · (1 − ω₀ z)·(1 + ω₀ z) ≤ v z · 1 = v z` **for every** `z`, since
  `(1−ω₀)(1+ω₀) = 1 − ω₀² ≤ 1` and `v ≥ 0` pointwise — no a.e. input and no diluteness.
  Hence `wSmallPair_mono_of_le` (`Work.BoseFixB1`) gives
  `w_{B(u)}[g₂](x,y) ≤ w_{B(u)}[v](x,y)` for all `(x,y)`.

* Both kernels are integrable on the big box: the general pointwise domination
  `Work.BoseFixB1.abs_wSmallPair_le` together with the product integrability of
  `|f(x−y)|` over `acube ℓ × acube ℓ`
  (`Work.BoseFixB1.integrableOn_wSmallPair_cube_fixed`, applied with the `L¹`
  numerators `g₂` and `v`), so `integral_mono` compares the box integrals.

* `boxM2` *is* the product-measure integral over `B(u) × B(u)`, which is Fubini-split
  by `MeasureTheory.setIntegral_prod` into the iterated integral; both integrals may
  then be extended from `B(u)` to all of `ℝ³`, because `w_{B(u)}[v]` vanishes as soon
  as one argument leaves `B(u)` (`chiSmallB` is supported there).
-/

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

theorem boxM2_g2_le_nested_bareV {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
      ≤ ∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wSmallPair M ℓ d u v x y := by
  classical
  -- ### 1. the pointwise numerator comparison `g₂ ≤ v`
  have hg2le : ∀ z : E3, Submission.BoseGases.g2 v h z ≤ v z := by
    intro z
    have hw : (1 - Classical.choose h z) * (1 + Classical.choose h z) ≤ 1 := by
      nlinarith [sq_nonneg (Classical.choose h z)]
    calc Submission.BoseGases.g2 v h z
        = v z * ((1 - Classical.choose h z) * (1 + Classical.choose h z)) := by
          simp only [Submission.BoseGases.g2]
          ring
      _ ≤ v z * 1 := mul_le_mul_of_nonneg_left hw (hv z)
      _ = v z := mul_one _
  -- ### 2. the pointwise kernel comparison
  have hpt : ∀ p : E3 × E3,
      Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2
        ≤ Submission.BoseGases.wSmallPair M ℓ d u v p.1 p.2 :=
    fun p => Work.BoseFixB1.wSmallPair_mono_of_le p.1 p.2 (hg2le (p.1 - p.2))
  -- ### 3. integrability of both kernels on the big box `acube ℓ × acube ℓ`
  have hIntF : MeasureTheory.IntegrableOn
      (fun p : E3 × E3 =>
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) :=
    Work.BoseFixB1.integrableOn_wSmallPair_cube_fixed (f := Submission.BoseGases.g2 v h)
      (Submission.BoseGases.g2_integrable hR hv hvrad hv_supp h) (R0 := R)
      (fun z hz => Submission.BoseGases.g2_zero_of_norm_ge hv_supp hz h)
      hM hℓ hd hR16 hRχ u
  have hIntG : MeasureTheory.IntegrableOn
      (fun p : E3 × E3 => Submission.BoseGases.wSmallPair M ℓ d u v p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) :=
    Work.BoseFixB1.integrableOn_wSmallPair_cube_fixed (f := v)
      (MeasureTheory.memLp_one_iff_integrable.mp hv1) (R0 := R)
      (fun z hz => Submission.BoseGases.v_eq_zero_of_norm_ge hv_supp hz)
      hM hℓ hd hR16 hRχ u
  have hsub : Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u
      ⊆ Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ :=
    Set.prod_mono (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
      (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
  -- ### 4. the box integral comparison
  have hstep :
      (∫ p in Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u,
          Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2)
        ≤ ∫ p in Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u,
            Submission.BoseGases.wSmallPair M ℓ d u v p.1 p.2 :=
    MeasureTheory.integral_mono (hIntF.mono_set hsub) (hIntG.mono_set hsub) hpt
  -- ### 5. Fubini on the box, and the extension to all of `ℝ³`
  have hfub :
      (∫ p in Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u,
          Submission.BoseGases.wSmallPair M ℓ d u v p.1 p.2)
        = ∫ x in Submission.BoseGases.dlBox ℓ d u,
            ∫ y in Submission.BoseGases.dlBox ℓ d u,
              Submission.BoseGases.wSmallPair M ℓ d u v x y :=
    MeasureTheory.setIntegral_prod
      (fun p : E3 × E3 => Submission.BoseGases.wSmallPair M ℓ d u v p.1 p.2)
      (hIntG.mono_set hsub)
  have hinner : ∀ x : E3,
      (∫ y in Submission.BoseGases.dlBox ℓ d u, Submission.BoseGases.wSmallPair M ℓ d u v x y)
        = ∫ y : E3, Submission.BoseGases.wSmallPair M ℓ d u v x y :=
    fun x => MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun y : E3 => Submission.BoseGases.wSmallPair M ℓ d u v x y)
      (s := Submission.BoseGases.dlBox ℓ d u)
      (fun y hy => Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u (Or.inr hy))
  have houter :
      (∫ x in Submission.BoseGases.dlBox ℓ d u,
          ∫ y : E3, Submission.BoseGases.wSmallPair M ℓ d u v x y)
        = ∫ x : E3, ∫ y : E3, Submission.BoseGases.wSmallPair M ℓ d u v x y := by
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun x : E3 => ∫ y : E3, Submission.BoseGases.wSmallPair M ℓ d u v x y)
      (s := Submission.BoseGases.dlBox ℓ d u) (fun x hx => ?_)
    have hz : (fun y : E3 => Submission.BoseGases.wSmallPair M ℓ d u v x y)
        = fun _ => (0 : ℝ) :=
      funext (fun y => Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u (Or.inl hx))
    rw [hz, MeasureTheory.integral_zero]
  -- ### 6. the chain
  calc Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
      = ∫ p in Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u,
          Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2 := rfl
    _ ≤ ∫ p in Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u,
          Submission.BoseGases.wSmallPair M ℓ d u v p.1 p.2 := hstep
    _ = ∫ x in Submission.BoseGases.dlBox ℓ d u,
          ∫ y in Submission.BoseGases.dlBox ℓ d u,
            Submission.BoseGases.wSmallPair M ℓ d u v x y := hfub
    _ = ∫ x in Submission.BoseGases.dlBox ℓ d u,
          ∫ y : E3, Submission.BoseGases.wSmallPair M ℓ d u v x y :=
        MeasureTheory.setIntegral_congr_fun (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
          (fun x _ => hinner x)
    _ = ∫ x : E3, ∫ y : E3, Submission.BoseGases.wSmallPair M ℓ d u v x y := houter

end Work.BoseFixB1B
