/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Hon/slot_prod_le_open`: the per-slot product bound in the honest (open) setting

The frozen module `Work.FTS.TransportS.T3BadAux.slot_prod_le` proves

`|∫∫ gK α f g k| ≤ 2 Mf ∫∫ (Xz α g k)²`

under the *frozen* hypotheses: `SmoothQuad g` (`C^∞` on the half-strip
`Ioi (-1) ×ˢ Ioo 0 (π/2)`) and the *pointwise* boundary decay
`z (Thard g k z θ · w z)² → 0` for every interior `θ`.

This file removes both restrictions.  Every use of `SmoothQuad g` in that proof goes through
one of the open-quadrant continuity/integrability lemmas collected in
`Submission/Work/FTS/StrongPersist/N6Trans/Hon/OpenTwins.lean` (`continuousOn_slotH1_Qd_open`,
`continuousOn_gK'_Qd_open`, `integrable_HkIntegrand_prod_open`, `integrable_Xz_sq_open`,
`integrable_gK_open`), and the pointwise boundary condition is only ever used *slice by slice*
in the a.e. Fubini step, so the a.e. form suffices.

The one non-trivial piece is `slot_slice_le_ae_open`: the radial slice bound for a.e. angle,
whose proof is the `open`-typed adaptation of `T3BadAux.slot_slice_le_ae`.  The final theorem
`slot_prod_le_open` is then the Fubini assembly.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.OpenTwins
import Submission.Work.FTS.TransportS.T3BadAux.slot_prod_le
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

set_option maxHeartbeats 1600000

/-! ## The a.e. radial slice bound (open twin of `T3BadAux.slot_slice_le_ae`) -/

/-- **The radial slice bound for a.e. angle, honest hypotheses.**  All the slice hypotheses of
`slot_slice_le` hold for a.e. `θ ∈ Iθ`: the two smoothness conditions come from
`SmoothOpen f`/`SmoothOpen g`, the boundary conditions are the hypothesis `htr`, and the three
integrability conditions follow from the product-integrability of `HkIntegrand α 4 g`,
`HkIntegrand α 5 g` and `(Xz α g k)²` together with the pointwise dominations `slot_H1_le`,
`slot_gKprime_le`. -/
theorem slot_slice_le_ae_open {α Mf : ℝ} {f g : ℝ → ℝ → ℝ} (k : Fin 5) (hMf : 0 ≤ Mf)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (hm4 : Work.Spaces.HkMem α 4 g) (hm5 : Work.Spaces.HkMem α 5 g)
    (hfb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ Mf)
    (hDfb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Dz f z θ| ≤ Mf)
    (htr : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0)) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |∫ z, Work.FTS.TransportS.gK α f g k z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)|
        ≤ 2 * Mf * ∫ z, (Work.FTS.TransportS.Xz α g k z θ) ^ 2
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  -- a.e. integrability of the radial slices of the `ℋ⁴`/`ℋ⁵` integrands
  have h4 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 4 g z θ)
        (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.TransportS.ae_integrableOn_slice
      (H := fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      (integrable_HkIntegrand_prod_open hsg hm4).1
    filter_upwards [h] with θ hθ
    exact (Work.FTS.TransportS.T3BadAux.integrableOn_Ioi_iff_Iz).mpr hθ
  have h5 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 5 g z θ)
        (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.TransportS.ae_integrableOn_slice
      (H := fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 5 g p.1 p.2)
      (integrable_HkIntegrand_prod_open hsg hm5).1
    filter_upwards [h] with θ hθ
    exact (Work.FTS.TransportS.T3BadAux.integrableOn_Ioi_iff_Iz).mpr hθ
  have hX2 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => (Work.FTS.TransportS.Xz α g k z θ) ^ 2)
        (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.TransportS.ae_integrableOn_slice
      (H := fun p : ℝ × ℝ => (Work.FTS.TransportS.Xz α g k p.1 p.2) ^ 2)
      (integrable_Xz_sq_open hsg hm4 k)
    filter_upwards [h] with θ hθ
    exact (Work.FTS.TransportS.T3BadAux.integrableOn_Ioi_iff_Iz).mpr hθ
  filter_upwards [Work.FTS.TransportS.ae_mem_Ioo_Iθ, h4, h5, hX2, htr] with
    θ hθ hI4 hI5 hIX2 htrθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hmem : ∀ z : ℝ, z ∈ Set.Ioi (0 : ℝ) → z ∈ Work.Spaces.Iz :=
    fun z hz => by simp only [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hz
  have hfbI : ∀ z : ℝ, z ∈ Set.Ioi (0 : ℝ) → |f z θ| ≤ Mf :=
    fun z hz => hfb z (hmem z hz) θ hθI
  have hDfbI : ∀ z : ℝ, z ∈ Set.Ioi (0 : ℝ) → |Work.Spaces.Dz f z θ| ≤ Mf :=
    fun z hz => hDfb z (hmem z hz) θ hθI
  -- the two smoothness conditions
  have hφcd : ContDiffOn ℝ 1 (fun z => f z θ) (Set.Ioi (0 : ℝ)) :=
    (hsf.curry_z hθ).of_le (by simp [Work.Stability.smoothOrder])
  have hucd : ContDiffOn ℝ 1 (fun z => Work.FTS.H2.Thard g k z θ) (Set.Ioi (0 : ℝ)) := by
    rw [Work.FTS.H2.Thard_eq_mixed g k]
    exact ((hsg.mixed (4 - k.val) k.val).curry_z hθ).of_le
      (by simp [Work.Stability.smoothOrder])
  -- the first integrability condition: rewrite `z ∂_z(Thard g k)` as `mixed (5-k) k g`
  have hint1 : MeasureTheory.IntegrableOn (fun z => f z θ * z * (Work.Spaces.w z) ^ 2
      * Work.FTS.H2.Thard g k z θ * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ)
      (Set.Ioi (0 : ℝ)) := by
    have hEq : (fun z => f z θ * z * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.Thard g k z θ
        * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ)
        = fun z => f z θ * Work.Spaces.mixed (5 - k.val) k.val g z θ
          * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.Thard g k z θ := by
      funext z
      have h : z * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ
          = Work.Spaces.mixed (5 - k.val) k.val g z θ := by
        rw [← Work.FTS.TransportS.Dz_Thard_apply g k z θ]
        rfl
      calc f z θ * z * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.Thard g k z θ
            * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ
          = f z θ * (z * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ)
            * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.Thard g k z θ := by ring
        _ = f z θ * Work.Spaces.mixed (5 - k.val) k.val g z θ
            * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.Thard g k z θ := by rw [h]
    rw [hEq]
    refine MeasureTheory.Integrable.mono'
      (((hI4.add hI5).div_const (Work.FTS.H2.sghard α k θ)).const_mul (Mf / 2))
      (Work.FTS.TransportS.T3BadAux.aesm_zslice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => f p.1 p.2 * Work.Spaces.mixed (5 - k.val) k.val g p.1 p.2
          * (Work.Spaces.w p.1) ^ 2 * Work.FTS.H2.Thard g k p.1 p.2)
        (continuousOn_slotH1_Qd_open hsf hsg k) hθ) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    rw [Real.norm_eq_abs]
    exact Work.FTS.TransportS.T3BadAux.slot_H1_le (α := α) (Mf := Mf) hMf k hθ (hfbI z hz)
  -- the second integrability condition
  have hint2 : MeasureTheory.IntegrableOn
      (fun z => Work.FTS.TransportS.gK' α f g k z θ) (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.Integrable.mono'
      ((hI4.div_const (Work.FTS.H2.sghard α k θ)).const_mul (4 * Mf))
      (Work.FTS.TransportS.T3BadAux.aesm_zslice_of_continuousOn_Qd _
        (continuousOn_gK'_Qd_open hsf hsg k) hθ) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    rw [Real.norm_eq_abs]
    exact Work.FTS.TransportS.T3BadAux.slot_gKprime_le (α := α) (Mf := Mf) hMf k hz hθ
      (hfbI z hz) (hDfbI z hz)
  have hkey : |∫ z in Set.Ioi (0 : ℝ), Work.FTS.TransportS.gK α f g k z θ|
      ≤ 2 * Mf * ∫ z in Set.Ioi (0 : ℝ), (Work.FTS.TransportS.Xz α g k z θ) ^ 2 :=
    Work.FTS.TransportS.T3BadAux.slot_slice_le (α := α) (Mf := Mf) (f := f) (g := g) k hMf
      hθ hφcd hucd (fun z hz => hfb z hz θ hθI) (fun z hz => hDfb z hz θ hθI)
      htrθ.1 htrθ.2 hint1 hint2 hIX2
  rw [Work.FTS.TransportS.T3BadAux.restrict_Iz_eq_Ioi]
  exact hkey

/-! ## The product-measure bound -/

theorem slot_prod_le_open {α Mf : ℝ} {f g : ℝ → ℝ → ℝ} (k : Fin 5) (hMf : 0 ≤ Mf)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (hm4 : Work.Spaces.HkMem α 4 g) (hm5 : Work.Spaces.HkMem α 5 g)
    (hfb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ Mf)
    (hDfb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Dz f z θ| ≤ Mf)
    (htr : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0)) :
    |∫ p, Work.FTS.TransportS.gK α f g k p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
      ≤ 2 * Mf * ∫ p, (Work.FTS.TransportS.Xz α g k p.1 p.2) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hfb' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |f z θ| ≤ Mf :=
    fun z θ hz hθ hθ' => hfb z (le_of_lt hz) θ ⟨le_of_lt hθ, le_of_lt hθ'⟩
  have hΦ : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.FTS.TransportS.gK α f g k p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    integrable_gK_open hsf hsg hm5 hMf hfb' k
  have hΨ : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.FTS.TransportS.Xz α g k p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    integrable_Xz_sq_open hsg hm4 k
  have hΦc : MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => Work.FTS.TransportS.gK α f g k z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hΦ
  have hΨc : MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => (Work.FTS.TransportS.Xz α g k z θ) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hΨ
  have hslice := slot_slice_le_ae_open (α := α) (Mf := Mf) (f := f) (g := g) k hMf
    hsf hsg hm4 hm5 hfb hDfb htr
  have hmΦ : MeasureTheory.Integrable
      (fun θ => ∫ z, Work.FTS.TransportS.gK α f g k z θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hΦ.integral_prod_right
  have hmΨ : MeasureTheory.Integrable
      (fun θ => ∫ z, (Work.FTS.TransportS.Xz α g k z θ) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hΨ.integral_prod_right
  have hL : (∫ p, Work.FTS.TransportS.gK α f g k p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ θ, ∫ z, Work.FTS.TransportS.gK α f g k z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.integral_integral hΦc).symm.trans
      (MeasureTheory.integral_integral_swap hΦc)
  have hR : (∫ p, (Work.FTS.TransportS.Xz α g k p.1 p.2) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ θ, ∫ z, (Work.FTS.TransportS.Xz α g k z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.integral_integral hΨc).symm.trans
      (MeasureTheory.integral_integral_swap hΨc)
  rw [hL, ← Real.norm_eq_abs]
  calc ‖∫ θ, ∫ z, Work.FTS.TransportS.gK α f g k z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)‖
      ≤ ∫ θ, ‖∫ z, Work.FTS.TransportS.gK α f g k z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)‖
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ θ, 2 * Mf * (∫ z, (Work.FTS.TransportS.Xz α g k z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        MeasureTheory.integral_mono_ae hmΦ.norm (hmΨ.const_mul (2 * Mf)) hslice
    _ = 2 * Mf * ∫ θ, (∫ z, (Work.FTS.TransportS.Xz α g k z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        MeasureTheory.integral_const_mul (2 * Mf) _
    _ = 2 * Mf * ∫ p, (Work.FTS.TransportS.Xz α g k p.1 p.2) ^ 2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        rw [hR]

end Work.FTS.StrongPersist.N6Trans.Hon
