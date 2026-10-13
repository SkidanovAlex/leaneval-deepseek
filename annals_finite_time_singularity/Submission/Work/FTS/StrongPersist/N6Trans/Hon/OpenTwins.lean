/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Hon/OpenTwins`: open-quadrant twins of the `SmoothQuad`-typed continuity/integrability API

The frozen transport engine (`Work.FTS.TransportS.HardDefs`, `T3BadAux.*`, `T3SlotAux.*`)
states the continuity and product-integrability lemmas of the `T3` slot engine under the
hypothesis `Work.FTS.LocData.SmoothQuad g` (`C^∞` on `z > -1`, `0 < θ < π/2`).  Every one of
them uses that hypothesis *only* on the open quadrant `Qd = (0,∞) × (0,π/2)`, so each has an
honest twin with `Work.FTS.EllipticEst.SmoothOpen g` (`C^∞` on `Qd`) in its place.

This module collects those twins: the joint continuity of `mixed`, `Thard`, `Xz`, `Yz`, `gK`,
`gK'` and of the `H1`-slice integrand, together with the product-integrability of
`HkIntegrand α k g`, of `(Xz α g k)²` and of `gK α f g k`.

All declarations are `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.T3BadAux.slot_prod_le
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Joint continuity on the open quadrant -/

/-- The uncurried mixed derivative of an open-smooth function is continuous on the open
quadrant.  (Open twin of `continuousOn_mixed_Qd`.) -/
theorem continuousOn_mixed_Qd_open {g : ℝ → ℝ → ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i g p.1 p.2) Work.FTS.LocData.Qd :=
  (hsg.mixed j i).continuousOn

/-- The uncurried hard slot `Thard g k` is continuous on the open quadrant. -/
theorem continuousOn_Thard_Qd_open {g : ℝ → ℝ → ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.H2.Thard g k p.1 p.2) Work.FTS.LocData.Qd := by
  refine (continuousOn_mixed_Qd_open hsg (4 - k.val) k.val).congr fun p _ => ?_
  simp only [Work.FTS.H2.Thard_eq_mixed]

/-- The uncurried weighted slot `Xz α g k` is continuous on the open quadrant. -/
theorem continuousOn_Xz_Qd_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.Xz α g k p.1 p.2)
      Work.FTS.LocData.Qd := by
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    refine ((continuousOn_mixed_Qd_open hsg 4 0).mul
      Work.FTS.TransportS.continuousOn_wdivsin_Qd).congr fun p _ => ?_
    simp only [Work.FTS.TransportS.Xz_apply_zero, Work.Spaces.mixed_zero_right, Pi.mul_apply]
  · refine ((continuousOn_mixed_Qd_open hsg (4 - k.val) k.val).mul
      (Work.FTS.TransportS.continuousOn_Wt_Qd α)).congr fun p _ => ?_
    simp only [Work.FTS.TransportS.Xz_apply_ne hk, Pi.mul_apply]

/-- The uncurried weighted slot `Yz α g k` is continuous on the open quadrant. -/
theorem continuousOn_Yz_Qd_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.Yz α g k p.1 p.2)
      Work.FTS.LocData.Qd := by
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    refine ((continuousOn_mixed_Qd_open hsg 5 0).mul
      Work.FTS.TransportS.continuousOn_wdivsin_Qd).congr fun p _ => ?_
    simp only [Work.FTS.TransportS.Yz_apply_zero, Work.Spaces.mixed_zero_right, Pi.mul_apply]
  · refine ((continuousOn_mixed_Qd_open hsg (5 - k.val) k.val).mul
      (Work.FTS.TransportS.continuousOn_Wt_Qd α)).congr fun p _ => ?_
    simp only [Work.FTS.TransportS.Yz_apply_ne hk, Pi.mul_apply]

/-- The uncurried `k`-th hard summand `gK α f g k` is continuous on the open quadrant. -/
theorem continuousOn_gK_Qd_open {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.gK α f g k p.1 p.2)
      Work.FTS.LocData.Qd := by
  have hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) Work.FTS.LocData.Qd :=
    (hsf.continuousOn).mono fun p hp => hp
  refine (hf.mul ((continuousOn_Xz_Qd_open (α := α) hsg k).mul
    (continuousOn_Yz_Qd_open (α := α) hsg k))).congr fun p hp => ?_
  have hp' := Set.mem_prod.mp hp
  rw [Work.FTS.TransportS.gK_eq_mul α f g k p.1 p.2 ⟨le_of_lt hp'.2.1, le_of_lt hp'.2.2⟩]
  simp only [Pi.mul_apply]

/-- The uncurried integration-by-parts integrand `gK' α f g k` is continuous on the open
quadrant. -/
theorem continuousOn_gK'_Qd_open {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.gK' α f g k p.1 p.2)
      Work.FTS.LocData.Qd := by
  have hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) Work.FTS.LocData.Qd :=
    (hsf.continuousOn).mono fun p hp => hp
  have hpf : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz f p.1 p.2) Work.FTS.LocData.Qd :=
    (hsf.pz.continuousOn).mono fun p hp => hp
  have hratio : ContinuousOn (fun p : ℝ × ℝ => (p.1 - 3) / (1 + p.1)) Work.FTS.LocData.Qd :=
    ContinuousOn.div (continuousOn_fst.sub continuousOn_const)
      (continuousOn_const.add continuousOn_fst) (fun p hp => by
        have h1 : (0 : ℝ) < p.1 := (Set.mem_prod.mp hp).1
        linarith)
  refine ((((hpf.mul continuousOn_fst).mul Work.FTS.TransportS.continuousOn_w_sq_Qd).add
    (hf.mul (Work.FTS.TransportS.continuousOn_w_sq_Qd.mul hratio))).mul
      ((continuousOn_Thard_Qd_open hsg k).pow 2)).congr fun p _ => ?_
  simp only [Work.FTS.TransportS.gK', Pi.mul_apply, Pi.add_apply, Pi.pow_apply]

/-- The rewritten `H1`-slice integrand of the radial integration by parts is continuous on the
open quadrant.  (Open twin of `T3BadAux.continuousOn_slotH1_Qd`.) -/
theorem continuousOn_slotH1_Qd_open {f g : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2 * Work.Spaces.mixed (5 - k.val) k.val g p.1 p.2
      * (Work.Spaces.w p.1) ^ 2 * Work.FTS.H2.Thard g k p.1 p.2) Work.FTS.LocData.Qd :=
  ((((hsf.continuousOn).mono fun p hp => hp).mul
      (continuousOn_mixed_Qd_open hsg (5 - k.val) k.val)).mul
    (Work.FTS.TransportS.continuousOn_w_sq_Qd.mul
      (continuousOn_Thard_Qd_open hsg k))).congr fun p _ => by
    simp only [Pi.mul_apply]
    rw [show Function.uncurry f p = f p.1 p.2 from rfl]
    ring

/-! ## Product-integrability -/

/-- The uncurried `HkIntegrand α k g` is a.e. strongly measurable for the product of the
restricted Lebesgue measures, for `g` smooth on the open quadrant. -/
theorem aesm_HkIntegrand_prod_open {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k g p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (hg.continuousOn_HkIntegrand α k)

/-- The `ℋ^k`-integrand of `g` is product-integrable, and its product integral is
`HkSq α k g`, for `g` smooth on the open quadrant.  (Open twin of
`integrable_HkIntegrand_prod`.) -/
theorem integrable_HkIntegrand_prod_open {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α k g) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k g p.1 p.2)
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))
      ∧ (∫ p, Work.Spaces.HkIntegrand α k g p.1 p.2
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
        = Work.Spaces.HkSq α k g := by
  have h := Work.Spaces.integrable_prod_of_iterated
    (μ := volume.restrict Work.Spaces.Iz) (ν := volume.restrict Work.Spaces.Iθ)
    (G := fun z θ => Work.Spaces.HkIntegrand α k g z θ)
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
    (aesm_HkIntegrand_prod_open (k := k) hg)
    ((MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iz from
      measurableSet_Ici)).mpr (Filter.Eventually.of_forall fun z hz => hmem.1 z hz))
    hmem.2
  exact ⟨h.1, by rw [h.2]; rfl⟩

/-- A single order-`4` weighted factor is a summand of `HkIntegrand α 4 g`, hence
product-integrable, for `g` smooth on the open quadrant. -/
theorem integrable_Xz_sq_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (hmg4 : Work.Spaces.HkMem α 4 g) (k : Fin 5) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.FTS.TransportS.Xz α g k p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  refine MeasureTheory.Integrable.mono' (integrable_HkIntegrand_prod_open hsg hmg4).1
    (Work.Spaces.aesm_of_continuousOn_Qd _ ((continuousOn_Xz_Qd_open hsg k).pow 2)) ?_
  filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
    (Work.FTS.TransportS.Xz α g k p.1 p.2) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g p.1 p.2)
    fun z θ hz hθ hθ' => Work.FTS.TransportS.Xz_sq_le_HkIntegrand4 α g k z θ] with p hp
  simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hp

/-- The `k`-th hard summand `gK α f g k` is product-integrable, for `g` smooth on the open
quadrant and `g ∈ ℋ⁵`.  (Open twin of `integrable_gK`.) -/
theorem integrable_gK_open {α Mf : ℝ} {f g : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmg5 : Work.Spaces.HkMem α 5 g) (hMf : 0 ≤ Mf)
    (hf : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf) (k : Fin 5) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.gK α f g k p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  refine MeasureTheory.Integrable.mono'
    ((integrable_HkIntegrand_prod_open hsg hmg5).1.const_mul Mf)
    (Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_gK_Qd_open hsf hsg k)) ?_
  filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
    |Work.FTS.TransportS.gK α f g k p.1 p.2| ≤ Mf * Work.Spaces.HkIntegrand α 5 g p.1 p.2)
    fun z θ hz hθ hθ' => Work.FTS.TransportS.abs_gK_le hMf hf k hz ⟨hθ, hθ'⟩] with p hp
  simpa only [Real.norm_eq_abs, mul_comm] using hp

end Work.FTS.StrongPersist.N6Trans.Hon
