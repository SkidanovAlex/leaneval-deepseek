import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.TT.SliceDatum
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.H2W.ESV.HkMem_zero_slices
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Assembly
import Submission.Work.FTS.EllipticEst.H2W.Fstar_DzIter_le_Psi
import Submission.Work.FTS.EllipticEst.H2W.Fstar_DzIter_two_F
import Submission.Work.FTS.EllipticEst.H2W.level0SlicesBridge
import Submission.Work.FTS.EllipticEst.H2W.ESV.easySlotsAssembly
import Submission.Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open
import Submission.Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm
import Submission.Work.FTS.EllipticEst.HkSq_congr_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W/easySlotsAe` — the reduction of `easySlots` to the level-`0` estimate in the `AeData` class

The target `Work.FTS.EllipticEst.H2W.easySlots` is

```
α⁴ (|D_θ A · Wt|²_{L²} + |D_θ² A · Wt|²_{L²}) ≤ C |F|²_{ℋ²},     A = z²∂_z²Ψ,
```

for every datum of the weak class `TT.EllWeakPos α 2 F Ψ` and `0 < α ≤ 1/4`.

## What this file proves

* `AeData_DzIter` — the `j`-th radial derivative (`j ≤ 2`) of a datum of the weak class
  `EllWeakPos α 2` *is* a datum of the almost-everywhere class `Ae.AeData` of the level-`0`
  estimate: the equation is `TT.bslOp_DzIter_eq`, the Dirichlet data `TT.DzIter_zero_at_*`, the
  smoothness `SmoothOpen.DzIter`, the three `HkMem`-certificates `HkMem_zero_slices`, the
  `Ψ`-moments `Fstar_DzIter_le_Psi` (pointwise), and the `F`-moments
  `remov.Fstar_DzIter_one_F_ge_two` (`j = 1`, pointwise) resp. `Fstar_DzIter_two_F_ae`
  (`j = 2`, almost everywhere — the *pointwise* statement at `j = 2` is not derivable from the
  class, see `H2W/Fstar_DzIter_two_F.lean`).

* `easySlots_slot_bounds` — given the level-`0` estimate in the class `Ae.AeData`
  (`hL0`, the conclusion of `Ae.Assembly.level0Ae_of`), the two quantities of the reduction
  `α⁴·HkSq α 0 A` and `α⁴·HkSq α 0 (∂_θ²A)` are bounded by `HkSq α 2 F`.

* `easySlots_of_level0Ae` — the target, from `hL0` and the (proved, `easySlotsAssembly`) slicewise
  assembly `esl_lhs_bound`.

## Why not the route through the `A`-datum

The earlier reduction in `H2W/easySlotsAssembly` consumed the level-`0` estimate for the
*`A`-datum* `u = A = z²∂_z²Ψ` with the source `G = z²∂_z²F`, i.e.

  `α⁴ HkSq α 0 A + HkSq α 0 (∂_θ²A) ≤ C HkSq α 0 (z²∂_z²F)`.                      (L0A)

That statement is *not* a consequence of the weak class: its right-hand side misses the angular
slots of the source.  In the exactly solvable family `Ψ = ψ(z)φ(θ)`, `Lzero φ = μ φ`, with source
`F = χ(z)φ(θ)` (so `ψ` solves `μψ − α²ψ'' − α(5+α)ψ' = χ`), both sides factor, and (L0A) becomes

  `(α⁴ + B_θ/A_θ) · ∫(z²ψ'')²w² ≤ C · ∫(z²χ'')²w²`,   `B_θ = ∫φ''²σ`, `A_θ = ∫φ²σ`,

in which the angular factor `B_θ/A_θ` on the left has no counterpart on the right; the `θ`-slots
of `F` that would supply it live in `HkSq α 2 F`, not in `HkSq α 0 (z²∂_z²F)`.  The reduction
below therefore uses the *radially shifted* data `(D_z^j F, D_z^j Ψ)`, whose sources do carry
them.
-/

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary integrand facts -/

/-- The level-`0` `HkIntegrand` is the square of the single weighted slot. -/
theorem hkIntegrand_zero_eq_Wg (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.pzIter_zero, Finset.range_one,
    Finset.sum_singleton]
  norm_num

/-- **Subadditivity of `HkSq α 0`** in the junk-tolerant form: for honest `a`, `b`,
`HkSq α 0 (a - b) ≤ 2 HkSq α 0 a + 2 HkSq α 0 b`.  The pointwise input is the algebraic
`(x - y)² ≤ 2x² + 2y²` applied to `x = a·Wg`, `y = b·Wg`; the honesty of `a` and `b` makes the
majorant an honest integral, so no case distinction is needed. -/
theorem HkSq_zero_sub_le (α : ℝ) (a b : ℝ → ℝ → ℝ)
    (ha : Work.Spaces.HkMem α 0 a) (hb : Work.Spaces.HkMem α 0 b) :
    Work.Spaces.HkSq α 0 (fun z θ => a z θ - b z θ)
      ≤ 2 * Work.Spaces.HkSq α 0 a + 2 * Work.Spaces.HkSq α 0 b := by
  have hpt : ∀ z θ, Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ - b z θ) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α 0 a z θ + 2 * Work.Spaces.HkIntegrand α 0 b z θ := by
    intro z θ
    rw [hkIntegrand_zero_eq_Wg, hkIntegrand_zero_eq_Wg, hkIntegrand_zero_eq_Wg]
    have h : ((a z θ - b z θ) * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        = ((a z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)))
            - (b z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)))) ^ 2 := by
      ring
    rw [h]
    nlinarith [sq_nonneg ((a z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)))
      + (b z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))))]
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ - b z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (2 * Work.Spaces.HkIntegrand α 0 a z θ
            + 2 * Work.Spaces.HkIntegrand α 0 b z θ) := by
    intro z hz
    refine MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict Work.Spaces.Iθ)
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
      (((ha.1 z hz).const_mul 2).add ((hb.1 z hz).const_mul 2))
      (Eventually.of_forall fun θ => hpt z θ)
  have hmajz : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, (2 * Work.Spaces.HkIntegrand α 0 a z θ
        + 2 * Work.Spaces.HkIntegrand α 0 b z θ)) Work.Spaces.Iz := by
    have h : MeasureTheory.IntegrableOn (fun z =>
        2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 a z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 b z θ))
        Work.Spaces.Iz := (ha.2.const_mul 2).add (hb.2.const_mul 2)
    refine h.congr_fun (fun z hz => ?_) measurableSet_Ici
    exact ((MeasureTheory.integral_add ((ha.1 z hz).const_mul 2)
      ((hb.1 z hz).const_mul 2)).trans
        (by rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul])).symm
  have hval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (2 * Work.Spaces.HkIntegrand α 0 a z θ + 2 * Work.Spaces.HkIntegrand α 0 b z θ))
      = 2 * Work.Spaces.HkSq α 0 a + 2 * Work.Spaces.HkSq α 0 b := by
    rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
    rw [show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (2 * Work.Spaces.HkIntegrand α 0 a z θ + 2 * Work.Spaces.HkIntegrand α 0 b z θ))
        = ∫ z in Work.Spaces.Iz,
            (2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 a z θ)
              + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 b z θ)) from
      setIntegral_congr_fun measurableSet_Ici (fun z hz => by
        rw [MeasureTheory.integral_add ((ha.1 z hz).const_mul 2) ((hb.1 z hz).const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul])]
    rw [MeasureTheory.integral_add (ha.2.const_mul 2) (hb.2.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  refine (MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict Work.Spaces.Iz)
    (Eventually.of_forall fun z => setIntegral_nonneg measurableSet_Icc
      (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ))
    hmajz (ae_restrict_of_forall_mem measurableSet_Ici hslice)).trans (le_of_eq hval)

/-- **The Clairaut identity for the twisted datum.**  On the open quadrant, the iterated angular
second derivative of `A = z²∂_z²Ψ` is the twisted datum of the angular second derivative,
`∂_θ²(z²∂_z²Ψ) = z²∂_z²(∂_θ²Ψ)`. -/
theorem pthIter_two_zsq_eq_rad2 (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = Work.FTS.EllipticEst.H2W.Ae.rad2 (Work.Spaces.pthIter 2 Ψ) z θ := by
  -- `∂_θ² (z² · g) = z² · ∂_θ² g` at a point
  have hmul : ∀ (g : ℝ → ℝ → ℝ),
      Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * g z θ) z θ
        = z ^ 2 * Work.Spaces.pthIter 2 g z θ := by
    intro g
    have h1 : (fun z θ => z ^ 2 * g z θ) = (fun z θ => z * (z * g z θ)) := by
      funext z θ; ring
    rw [h1, pthIter_const_mul_fst 2 (fun z θ => z * g z θ),
      pthIter_const_mul_fst 2 g]
    ring
  rw [hmul (Work.Spaces.pzIter 2 Ψ)]
  -- `pzIter 2 (pthIter 2 Ψ) = pthIter 2 (pzIter 2 Ψ)` on the quadrant
  have hV : (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := ⟨hz, hθ⟩
  have hcc : Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.pzIter 2 Ψ) z θ := by
    have h1 : Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
        = Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ :=
      pz_pthIter_two_eqOn hΨ hV
    have h2 : Work.Spaces.pz (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ)) z θ
        = Work.Spaces.pthIter 2 (Work.Spaces.pzIter 2 Ψ) z θ :=
      pz_pthIter_two_eqOn hΨ.pz hV
    have h3 : Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ)) z θ
        = Work.Spaces.pz (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ)) z θ :=
      Work.Spaces.pz_congr_of_isOpen (isOpen_Ioi.prod isOpen_Ioo)
        (fun p hp => pz_pthIter_two_eqOn hΨ hp) hV
    show Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ)) z θ = _
    rw [h3, h2]
  rw [← hcc]
  rfl

/-! ## The almost-everywhere class for the radially shifted data -/

/-- **The `j`-th radial derivative of a weak-class datum is an `AeData`** (for `j ≤ 2`). -/
theorem AeData_DzIter (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (j : ℕ) (hj : j ≤ 2) :
    Work.FTS.EllipticEst.H2W.Ae.AeData α (Work.Spaces.DzIter j Ψ) (Work.Spaces.DzIter j F) := by
  have hsmΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have h3 := HkMem_zero_slices α F Ψ h j hj
  refine ⟨hα, hα4, ?_, ?_, ?_, ?_, h3.1, h3.2.1, h3.2.2, ?_, ?_⟩
  · intro z hz θ hθ0 hθ1
    exact Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ j h.smooth h.eq z hz θ hθ0 hθ1
  · intro z
    exact Work.FTS.EllipticEst.TT.DzIter_zero_at_zero Ψ j h.zero z
  · intro z
    exact Work.FTS.EllipticEst.TT.DzIter_zero_at_pi_half Ψ j h.pi_half z
  · intro n
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall
      (Work.Spaces.DzIter j Ψ)).mp (hsmΨ.DzIter j) n
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact Fstar_DzIter_le_Psi α F Ψ h j (by omega) z (Set.mem_Ioi.mp hz)
  · interval_cases j
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      exact h.orthF z (Set.mem_Ioi.mp hz)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      exact Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two (α := α) (k := 2)
        (le_refl 2) h z (Set.mem_Ioi.mp hz)
    · exact Fstar_DzIter_two_F_ae α F Ψ h

/-! ## The two slots from the level-`0` estimate -/

/-- **The two quantities of the reduction are bounded by `HkSq α 2 F`, given the level-`0`
estimate in the `AeData` class.**

The first is the first conjunct of `hL0` applied to the base datum; the second uses the two
*shifted* data: `HkSq α 0 (∂_θ²(z²∂_z²Ψ)) = HkSq α 0 (z²∂_z²(∂_θ²Ψ))` (Clairaut), and
`z²∂_z² = D_z² - D_z` turns this into `HkSq α 0 (D_z²(∂_θ²Ψ))` and `HkSq α 0 (D_z(∂_θ²Ψ))`, which
are `HkSq α 0 (∂_θ²(D_z^j Ψ))` for `j = 1, 2` — the second conjunct of `hL0` on the shifted
data. -/
theorem easySlots_slot_bounds
    (hL0 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u) ≤ C * Work.Spaces.HkSq α 0 G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
        α ^ 4 * (Work.Spaces.HkSq α 0 (eslA Ψ)
            + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ)))
          ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := hL0
  have hC₀nn : 0 ≤ C₀ := le_of_lt hC₀pos
  refine ⟨max 1 (5 * C₀), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro α F Ψ hα hα4 h
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hFnn : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have hFsq : Work.Spaces.HkSq α 0 F ≤ Work.Spaces.HkSq α 2 F :=
    HkSq_zero_DzIter_le_HkSq α F h.memF 0 (by norm_num)
  -- ## the first slot
  have hB : α ^ 4 * Work.Spaces.HkSq α 0 (eslA Ψ) ≤ C₀ * Work.Spaces.HkSq α 2 F := by
    have hbase := hC₀ α Ψ F (AeData_DzIter α F Ψ hα hα4 h 0 (by norm_num))
    have hnn : 0 ≤ Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ) :=
      Work.Spaces.HkSq_nonneg α 0 _
    have h1 : α ^ 4 * Work.Spaces.HkSq α 0 (eslA Ψ) ≤ C₀ * Work.Spaces.HkSq α 0 F := by
      change α ^ 4 * Work.Spaces.HkSq α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ≤ C₀ * Work.Spaces.HkSq α 0 F
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_left hFsq hC₀nn)
  -- ## the second slot
  have hA : α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ))
      ≤ 4 * C₀ * Work.Spaces.HkSq α 2 F := by
    -- Clairaut
    have hcl : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ))
        = Work.Spaces.HkSq α 0
            (Work.FTS.EllipticEst.H2W.Ae.rad2 (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ0 hθ1 =>
        pthIter_two_zsq_eq_rad2 Ψ hΨso hz ⟨hθ0, hθ1⟩)
    -- the split `z²∂_z² = D_z² - D_z`
    have hdec : Work.Spaces.HkSq α 0
          (Work.FTS.EllipticEst.H2W.Ae.rad2 (Work.Spaces.pthIter 2 Ψ))
        = Work.Spaces.HkSq α 0 (fun z θ => Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
            - Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ0 hθ1 =>
        Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open (Work.Spaces.pthIter 2 Ψ)
          (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2) hz ⟨hθ0, hθ1⟩)
    -- honesty of the two shifted source-side slots
    have hmem2 : Work.Spaces.HkMem α 0
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) :=
      (HkMem_zero_slices α F Ψ h 2 (by norm_num)).2.1
    have hmem1 : Work.Spaces.HkMem α 0
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :=
      (HkMem_zero_slices α F Ψ h 1 (by norm_num)).2.1
    -- the `HkMem` of `D_z^j (∂_θ²Ψ)`, transferred through the Clairaut identity
    have hmemD2 : Work.Spaces.HkMem α 0
        (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.H2W.AeDataAofAux.HkMem_zero_congr
        ((Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2).DzIter 2).continuousOn
        (fun z θ hz hθ0 hθ1 =>
          (Work.FTS.EllipticEst.H2W.pthIter_two_DzIter_comm Ψ 2 hΨso (⟨hz, hθ0, hθ1⟩ : (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))).symm)
        ((HkMem_zero_slices α F Ψ h 2 (by norm_num)).2.2)
    have hmemD1 : Work.Spaces.HkMem α 0
        (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.H2W.AeDataAofAux.HkMem_zero_congr
        ((Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2).DzIter 1).continuousOn
        (fun z θ hz hθ0 hθ1 =>
          (Work.FTS.EllipticEst.H2W.pthIter_two_DzIter_comm Ψ 1 hΨso (⟨hz, hθ0, hθ1⟩ : (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))).symm)
        ((HkMem_zero_slices α F Ψ h 1 (by norm_num)).2.2)
    have hsub := HkSq_zero_sub_le α (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ))
      (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) hmemD2 hmemD1
    -- the Clairaut transfers back
    have e2 : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ))
        = Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ)) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ0 hθ1 =>
        (Work.FTS.EllipticEst.H2W.pthIter_two_DzIter_comm Ψ 2 hΨso (⟨hz, hθ0, hθ1⟩ : (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))).symm)
    have e1 : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ))
        = Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ0 hθ1 =>
        (Work.FTS.EllipticEst.H2W.pthIter_two_DzIter_comm Ψ 1 hΨso (⟨hz, hθ0, hθ1⟩ : (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))).symm)
    -- the shifted level-`0` estimates
    have hj2 := hC₀ α (Work.Spaces.DzIter 2 Ψ) (Work.Spaces.DzIter 2 F)
      (AeData_DzIter α F Ψ hα hα4 h 2 (by norm_num))
    have hj1 := hC₀ α (Work.Spaces.DzIter 1 Ψ) (Work.Spaces.DzIter 1 F)
      (AeData_DzIter α F Ψ hα hα4 h 1 (by norm_num))
    have hj2' : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
        ≤ C₀ * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 F) := by
      have : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) :=
        mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α 0 _)
      linarith
    have hj1' : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ C₀ * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 F) := by
      have : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :=
        mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α 0 _)
      linarith
    have hD2 : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 F) ≤ Work.Spaces.HkSq α 2 F :=
      HkSq_zero_DzIter_le_HkSq α F h.memF 2 (by norm_num)
    have hD1 : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 F) ≤ Work.Spaces.HkSq α 2 F :=
      HkSq_zero_DzIter_le_HkSq α F h.memF 1 (by norm_num)
    have hkey : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ))
        ≤ 4 * C₀ * Work.Spaces.HkSq α 2 F := by
      rw [hcl, hdec]
      calc Work.Spaces.HkSq α 0 (fun z θ => Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
              - Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ)
          ≤ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ))
            + 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) := hsub
        _ = 2 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
            + 2 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) := by
            rw [e2, e1]
        _ ≤ 2 * (C₀ * Work.Spaces.HkSq α 2 F) + 2 * (C₀ * Work.Spaces.HkSq α 2 F) := by
            have h2' := mul_le_mul_of_nonneg_left hD2 hC₀nn
            have h1' := mul_le_mul_of_nonneg_left hD1 hC₀nn
            linarith
        _ = 4 * C₀ * Work.Spaces.HkSq α 2 F := by ring
    have hα4le : α ^ 4 ≤ 1 := pow_le_one₀ (le_of_lt hα) (by linarith)
    calc α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ))
        ≤ 1 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ)) :=
          mul_le_mul_of_nonneg_right hα4le (Work.Spaces.HkSq_nonneg α 0 _)
      _ ≤ 4 * C₀ * Work.Spaces.HkSq α 2 F := by simpa using hkey
  -- ## the conclusion
  have hsum : α ^ 4 * (Work.Spaces.HkSq α 0 (eslA Ψ)
      + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ)))
      ≤ C₀ * Work.Spaces.HkSq α 2 F + 4 * C₀ * Work.Spaces.HkSq α 2 F := by
    have hdist : α ^ 4 * (Work.Spaces.HkSq α 0 (eslA Ψ)
        + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ)))
        = α ^ 4 * Work.Spaces.HkSq α 0 (eslA Ψ)
          + α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ)) := by ring
    rw [hdist]
    linarith [hB, hA]
  have hfinal : C₀ * Work.Spaces.HkSq α 2 F + 4 * C₀ * Work.Spaces.HkSq α 2 F
      ≤ max 1 (5 * C₀) * Work.Spaces.HkSq α 2 F := by
    have hle : 5 * C₀ ≤ max 1 (5 * C₀) := le_max_right _ _
    nlinarith [hFnn, hC₀nn]
  linarith [hsum, hfinal]

/-! ## The target -/

/-- **`easySlots` from the level-`0` estimate in the `AeData` class.** -/
theorem easySlots_of_level0Ae
    (hL0 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u) ≤ C * Work.Spaces.HkSq α 0 G) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
          α ^ 4 * (Work.Spaces.L2Sq (fun z θ =>
              Work.Spaces.mixed 0 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
                * Work.Spaces.Wt α z θ)
            + Work.Spaces.L2Sq (fun z θ =>
              Work.Spaces.mixed 0 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
                * Work.Spaces.Wt α z θ))
          ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨Cs, hCspos, hsb⟩ := easySlots_slot_bounds hL0
  obtain ⟨Cag, hCagpos, hag₀⟩ := Work.FTS.EllipticEst.H2W.angularAgmon
  obtain ⟨Cp, hCppos, hpiv⟩ := Work.FTS.EllipticEst.H2W.pivotBound
  have hC1nn : (0 : ℝ) ≤ 20000 * Cp + 10000 * Real.pi + 1 := by positivity
  obtain ⟨Cl, hClpos, hlh⟩ := esl_lhs_bound Cag (20000 * Cp + 10000 * Real.pi + 1)
    (le_of_lt hCagpos) hC1nn hag₀
    (Work.FTS.EllipticEst.H2W.deriv_sq_mul_sEta_le Cp hCppos hpiv)
    (fun α u hα hα4 hu => Work.FTS.EllipticEst.H2W.eslDth2Bound α hα hα4 u hu)
    (fun α F Ψ hh => Work.FTS.EllipticEst.H2W.eslHkMemPthTwoZsq α hh)
  refine ⟨Cl * Cs, by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  have h1 := hlh α F Ψ hα hα4 h
  have h2 := hsb α F Ψ hα hα4 h
  have hα4nn : (0 : ℝ) ≤ α ^ 4 := by positivity
  have hXnn : 0 ≤ Work.Spaces.HkSq α 0 (eslA Ψ)
      + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ)) :=
    add_nonneg (Work.Spaces.HkSq_nonneg α 0 _) (Work.Spaces.HkSq_nonneg α 0 _)
  have hClnn : 0 ≤ Cl := le_of_lt hClpos
  change α ^ 4 * (Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.mixed 0 1 (eslA Ψ) z θ * Work.Spaces.Wt α z θ)
      + Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.mixed 0 2 (eslA Ψ) z θ * Work.Spaces.Wt α z θ))
    ≤ Cl * Cs * Work.Spaces.HkSq α 2 F
  calc α ^ 4 * (Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.mixed 0 1 (eslA Ψ) z θ * Work.Spaces.Wt α z θ)
        + Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.mixed 0 2 (eslA Ψ) z θ * Work.Spaces.Wt α z θ))
      ≤ α ^ 4 * (Cl * (Work.Spaces.HkSq α 0 (eslA Ψ)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ)))) :=
        mul_le_mul_of_nonneg_left h1 hα4nn
    _ = Cl * (α ^ 4 * (Work.Spaces.HkSq α 0 (eslA Ψ)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ)))) := by ring
    _ ≤ Cl * (Cs * Work.Spaces.HkSq α 2 F) := mul_le_mul_of_nonneg_left h2 hClnn
    _ = Cl * Cs * Work.Spaces.HkSq α 2 F := by ring

/-! ## The reduction to `Ae.Step1` and `Ae.Step2` alone

`Step3` of `Ae.Assembly` is *not* needed: the two quantities of the reduction are bounded by
`HkSq α 2 F` using the first-order radial estimate (`Step1`, applied to the base datum and to its
first radial derivative) together with the angular estimate (`Step2`) applied to the base and the
once/twice radially shifted data. -/

/-- `grad` is `D_z`, so `grad (D_z^j u) = D_z^{j+1} u` definitionally. -/
theorem Ae_grad_DzIter (u : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.FTS.EllipticEst.H2W.Ae.grad (Work.Spaces.DzIter j u) = Work.Spaces.DzIter (j + 1) u :=
  rfl

/-- **The two quantities of the reduction are bounded by `HkSq α 2 F` from `Step1` and `Step2`
alone.** -/
theorem easySlots_slot_bounds_steps (h1 : Work.FTS.EllipticEst.H2W.Ae.Step1)
    (h2 : Work.FTS.EllipticEst.H2W.Ae.Step2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
        α ^ 4 * (Work.Spaces.HkSq α 0 (eslA Ψ)
            + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ)))
          ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C₁, hC₁pos, hS1⟩ := h1
  obtain ⟨C₂, hC₂pos, hS2⟩ := h2
  have hC₁nn : 0 ≤ C₁ := le_of_lt hC₁pos
  refine ⟨max 1 (4 * C₁ ^ 2 + 4 * (C₂ * (1 + C₁)) ^ 2),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro α F Ψ hα hα4 h
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hFnn : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have hα2le : α ^ 2 ≤ 1 := pow_le_one₀ (le_of_lt hα) (by linarith)
  -- (P) the squared radial `Step1` bound for the datum `(D_z^j F, D_z^j Ψ)`, `j ≤ 1`
  have hP : ∀ j : ℕ, j ≤ 1 →
      α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter (j + 1) Ψ)
        ≤ C₁ ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j F) := by
    intro j hj
    obtain ⟨-, -, -, hbd⟩ := hS1 α (Work.Spaces.DzIter j Ψ) (Work.Spaces.DzIter j F)
      (AeData_DzIter α F Ψ hα hα4 h j (by omega))
    have hsq : (α * Work.FTS.EllipticEst.H2W.Ae.nrm α
          (Work.FTS.EllipticEst.H2W.Ae.grad (Work.Spaces.DzIter j Ψ))) ^ 2
        ≤ (C₁ * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.Spaces.DzIter j F)) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (le_of_lt hα) (Real.sqrt_nonneg _)) hbd 2
    have e : (Work.FTS.EllipticEst.H2W.Ae.nrm α
          (Work.FTS.EllipticEst.H2W.Ae.grad (Work.Spaces.DzIter j Ψ))) ^ 2
        = Work.Spaces.HkSq α 0 (Work.Spaces.DzIter (j + 1) Ψ) := by
      rw [Work.FTS.EllipticEst.H2W.Ae.nrm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 0 _)]
      rfl
    have e' : (Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.Spaces.DzIter j F)) ^ 2
        = Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j F) := by
      rw [Work.FTS.EllipticEst.H2W.Ae.nrm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 0 _)]
    rw [mul_pow, mul_pow, e, e'] at hsq
    exact hsq
  -- ## the first slot
  have hB : α ^ 4 * Work.Spaces.HkSq α 0 (eslA Ψ) ≤ 4 * C₁ ^ 2 * Work.Spaces.HkSq α 2 F := by
    have hmem2 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 Ψ) :=
      (hS1 α (Work.Spaces.DzIter 1 Ψ) (Work.Spaces.DzIter 1 F)
        (AeData_DzIter α F Ψ hα hα4 h 1 (by norm_num))).2.1
    have hmem1 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 Ψ) :=
      (hS1 α Ψ F (AeData_DzIter α F Ψ hα hα4 h 0 (by norm_num))).2.1
    have hsub := HkSq_zero_sub_le α (Work.Spaces.DzIter 2 Ψ) (Work.Spaces.DzIter 1 Ψ) hmem2 hmem1
    have hcl : Work.Spaces.HkSq α 0 (eslA Ψ)
        = Work.Spaces.HkSq α 0 (fun z θ => Work.Spaces.DzIter 2 Ψ z θ
            - Work.Spaces.DzIter 1 Ψ z θ) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ0 hθ1 =>
        Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open Ψ hΨso hz ⟨hθ0, hθ1⟩)
    have h2' : α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 Ψ)
        ≤ C₁ ^ 2 * Work.Spaces.HkSq α 2 F :=
      (hP 1 (by norm_num)).trans (mul_le_mul_of_nonneg_left
        (HkSq_zero_DzIter_le_HkSq α F h.memF 1 (by norm_num)) (sq_nonneg C₁))
    have h1' : α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 Ψ)
        ≤ C₁ ^ 2 * Work.Spaces.HkSq α 2 F :=
      (hP 0 (by norm_num)).trans (mul_le_mul_of_nonneg_left
        (HkSq_zero_DzIter_le_HkSq α F h.memF 0 (by norm_num)) (sq_nonneg C₁))
    have hk : 0 ≤ C₁ ^ 2 * Work.Spaces.HkSq α 2 F := mul_nonneg (sq_nonneg C₁) hFnn
    have hα2C : α ^ 2 * (C₁ ^ 2 * Work.Spaces.HkSq α 2 F)
        ≤ C₁ ^ 2 * Work.Spaces.HkSq α 2 F := by nlinarith [hα2le, hk]
    calc α ^ 4 * Work.Spaces.HkSq α 0 (eslA Ψ)
        = α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => Work.Spaces.DzIter 2 Ψ z θ
            - Work.Spaces.DzIter 1 Ψ z θ) := by rw [hcl]
      _ ≤ α ^ 4 * (2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 Ψ)
            + 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 Ψ)) :=
          mul_le_mul_of_nonneg_left hsub (by positivity)
      _ = 2 * (α ^ 2 * (α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 Ψ)))
            + 2 * (α ^ 2 * (α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 Ψ))) := by ring
      _ ≤ 2 * (α ^ 2 * (C₁ ^ 2 * Work.Spaces.HkSq α 2 F))
            + 2 * (α ^ 2 * (C₁ ^ 2 * Work.Spaces.HkSq α 2 F)) := by
          have hh2 : α ^ 2 * (α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 Ψ))
              ≤ α ^ 2 * (C₁ ^ 2 * Work.Spaces.HkSq α 2 F) :=
            mul_le_mul_of_nonneg_left h2' (sq_nonneg α)
          have hh1 : α ^ 2 * (α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 Ψ))
              ≤ α ^ 2 * (C₁ ^ 2 * Work.Spaces.HkSq α 2 F) :=
            mul_le_mul_of_nonneg_left h1' (sq_nonneg α)
          linarith
      _ ≤ 4 * C₁ ^ 2 * Work.Spaces.HkSq α 2 F := by linarith [hα2C, hk]
  -- ## the second slot
  have hA : α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ))
      ≤ 4 * (C₂ * (1 + C₁)) ^ 2 * Work.Spaces.HkSq α 2 F := by
    have hmemD2 : Work.Spaces.HkMem α 0
        (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.H2W.AeDataAofAux.HkMem_zero_congr
        (((Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2).DzIter 2).continuousOn)
        (fun z θ hz hθ0 hθ1 =>
          (Work.FTS.EllipticEst.H2W.pthIter_two_DzIter_comm Ψ 2 hΨso
            (⟨hz, hθ0, hθ1⟩ : (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))).symm)
        ((HkMem_zero_slices α F Ψ h 2 (by norm_num)).2.2)
    have hmemD1 : Work.Spaces.HkMem α 0
        (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.H2W.AeDataAofAux.HkMem_zero_congr
        (((Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2).DzIter 1).continuousOn)
        (fun z θ hz hθ0 hθ1 =>
          (Work.FTS.EllipticEst.H2W.pthIter_two_DzIter_comm Ψ 1 hΨso
            (⟨hz, hθ0, hθ1⟩ : (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))).symm)
        ((HkMem_zero_slices α F Ψ h 1 (by norm_num)).2.2)
    have hsub2 := HkSq_zero_sub_le α (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ))
      (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) hmemD2 hmemD1
    have hcl2 : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ))
        = Work.Spaces.HkSq α 0
            (Work.FTS.EllipticEst.H2W.Ae.rad2 (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ0 hθ1 =>
        pthIter_two_zsq_eq_rad2 Ψ hΨso hz ⟨hθ0, hθ1⟩)
    have hdec : Work.Spaces.HkSq α 0
          (Work.FTS.EllipticEst.H2W.Ae.rad2 (Work.Spaces.pthIter 2 Ψ))
        = Work.Spaces.HkSq α 0 (fun z θ => Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
            - Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ0 hθ1 =>
        Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open (Work.Spaces.pthIter 2 Ψ)
          (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2) hz ⟨hθ0, hθ1⟩)
    have e2 : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ))
        = Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ)) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ0 hθ1 =>
        (Work.FTS.EllipticEst.H2W.pthIter_two_DzIter_comm Ψ 2 hΨso
          (⟨hz, hθ0, hθ1⟩ : (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))).symm)
    have e1 : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ))
        = Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ0 hθ1 =>
        (Work.FTS.EllipticEst.H2W.pthIter_two_DzIter_comm Ψ 1 hΨso
          (⟨hz, hθ0, hθ1⟩ : (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))).symm)
    have hE : ∀ j : ℕ, j ≤ 2 →
        Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
          ≤ (C₂ * (1 + C₁)) ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j F) := by
      intro j hj
      have hAe := AeData_DzIter α F Ψ hα hα4 h j hj
      have hs := hS2 α (Work.Spaces.DzIter j Ψ) (Work.Spaces.DzIter j F) hAe
      have hp := (hS1 α (Work.Spaces.DzIter j Ψ) (Work.Spaces.DzIter j F) hAe).2.2.2
      have hG : Work.FTS.EllipticEst.H2W.Ae.nrm α
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
          ≤ C₂ * (1 + C₁) * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.Spaces.DzIter j F) := by
        have hnn : 0 ≤ Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.Spaces.DzIter j F) :=
          Real.sqrt_nonneg _
        show Work.FTS.EllipticEst.H2W.Ae.nrm α
            (Work.FTS.EllipticEst.H2W.Ae.ang2 (Work.Spaces.DzIter j Ψ)) ≤ _
        nlinarith [hs, hp, hnn, mul_nonneg (le_of_lt hC₂pos) hnn]
      have hsq : (Work.FTS.EllipticEst.H2W.Ae.nrm α
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))) ^ 2
          ≤ (C₂ * (1 + C₁) * Work.FTS.EllipticEst.H2W.Ae.nrm α
              (Work.Spaces.DzIter j F)) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hG 2
      have e : (Work.FTS.EllipticEst.H2W.Ae.nrm α
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))) ^ 2
          = Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ)) := by
        rw [Work.FTS.EllipticEst.H2W.Ae.nrm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 0 _)]
      have e' : (Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.Spaces.DzIter j F)) ^ 2
          = Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j F) := by
        rw [Work.FTS.EllipticEst.H2W.Ae.nrm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 0 _)]
      rw [mul_pow, e, e'] at hsq
      exact hsq
    have hE2 : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
        ≤ (C₂ * (1 + C₁)) ^ 2 * Work.Spaces.HkSq α 2 F :=
      (hE 2 (by norm_num)).trans (mul_le_mul_of_nonneg_left
        (HkSq_zero_DzIter_le_HkSq α F h.memF 2 (by norm_num)) (sq_nonneg _))
    have hE1 : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ (C₂ * (1 + C₁)) ^ 2 * Work.Spaces.HkSq α 2 F :=
      (hE 1 (by norm_num)).trans (mul_le_mul_of_nonneg_left
        (HkSq_zero_DzIter_le_HkSq α F h.memF 1 (by norm_num)) (sq_nonneg _))
    have hk2 : 0 ≤ (C₂ * (1 + C₁)) ^ 2 * Work.Spaces.HkSq α 2 F :=
      mul_nonneg (sq_nonneg _) hFnn
    calc α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ))
        = α ^ 4 * Work.Spaces.HkSq α 0
            (Work.FTS.EllipticEst.H2W.Ae.rad2 (Work.Spaces.pthIter 2 Ψ)) := by rw [hcl2]
      _ = α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ =>
            Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
              - Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) := by rw [hdec]
      _ ≤ α ^ 4 * (2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ))
            + 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ))) :=
          mul_le_mul_of_nonneg_left hsub2 (by positivity)
      _ = α ^ 4 * (2 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
            + 2 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))) := by
          rw [e2, e1]
      _ ≤ α ^ 4 * (2 * ((C₂ * (1 + C₁)) ^ 2 * Work.Spaces.HkSq α 2 F)
            + 2 * ((C₂ * (1 + C₁)) ^ 2 * Work.Spaces.HkSq α 2 F)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [hE2, hE1]
      _ ≤ 4 * (C₂ * (1 + C₁)) ^ 2 * Work.Spaces.HkSq α 2 F := by
          have h4 : α ^ 4 * (2 * ((C₂ * (1 + C₁)) ^ 2 * Work.Spaces.HkSq α 2 F)
                + 2 * ((C₂ * (1 + C₁)) ^ 2 * Work.Spaces.HkSq α 2 F))
              = 4 * (α ^ 4 * ((C₂ * (1 + C₁)) ^ 2 * Work.Spaces.HkSq α 2 F)) := by ring
          rw [h4]
          have hα4le : α ^ 4 ≤ 1 := pow_le_one₀ (le_of_lt hα) (by linarith)
          nlinarith [hα4le, hk2]
  -- ## the conclusion
  have hdist : α ^ 4 * (Work.Spaces.HkSq α 0 (eslA Ψ)
      + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ)))
      = α ^ 4 * Work.Spaces.HkSq α 0 (eslA Ψ)
        + α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ)) := by ring
  have hle : 4 * C₁ ^ 2 + 4 * (C₂ * (1 + C₁)) ^ 2
      ≤ max 1 (4 * C₁ ^ 2 + 4 * (C₂ * (1 + C₁)) ^ 2) := le_max_right _ _
  rw [hdist]
  have h4C : 4 * C₁ ^ 2 * Work.Spaces.HkSq α 2 F
        + 4 * (C₂ * (1 + C₁)) ^ 2 * Work.Spaces.HkSq α 2 F
      ≤ max 1 (4 * C₁ ^ 2 + 4 * (C₂ * (1 + C₁)) ^ 2) * Work.Spaces.HkSq α 2 F := by
    have h5 : 0 ≤ 4 * C₁ ^ 2 + 4 * (C₂ * (1 + C₁)) ^ 2 := by positivity
    nlinarith [hle, hFnn, h5]
  linarith [hB, hA, h4C]

/-- **`easySlots` from the first two steps of the level-`0` estimate alone.** -/
theorem easySlots_of_steps (h1 : Work.FTS.EllipticEst.H2W.Ae.Step1)
    (h2 : Work.FTS.EllipticEst.H2W.Ae.Step2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
          α ^ 4 * (Work.Spaces.L2Sq (fun z θ =>
              Work.Spaces.mixed 0 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
                * Work.Spaces.Wt α z θ)
            + Work.Spaces.L2Sq (fun z θ =>
              Work.Spaces.mixed 0 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
                * Work.Spaces.Wt α z θ))
          ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨Cs, hCspos, hsb⟩ := easySlots_slot_bounds_steps h1 h2
  obtain ⟨Cag, hCagpos, hag₀⟩ := Work.FTS.EllipticEst.H2W.angularAgmon
  obtain ⟨Cp, hCppos, hpiv⟩ := Work.FTS.EllipticEst.H2W.pivotBound
  have hC1nn : (0 : ℝ) ≤ 20000 * Cp + 10000 * Real.pi + 1 := by positivity
  obtain ⟨Cl, hClpos, hlh⟩ := esl_lhs_bound Cag (20000 * Cp + 10000 * Real.pi + 1)
    (le_of_lt hCagpos) hC1nn hag₀
    (Work.FTS.EllipticEst.H2W.deriv_sq_mul_sEta_le Cp hCppos hpiv)
    (fun α u hα hα4 hu => Work.FTS.EllipticEst.H2W.eslDth2Bound α hα hα4 u hu)
    (fun α F Ψ hh => Work.FTS.EllipticEst.H2W.eslHkMemPthTwoZsq α hh)
  refine ⟨Cl * Cs, by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  have h1' := hlh α F Ψ hα hα4 h
  have h2' := hsb α F Ψ hα hα4 h
  have hα4nn : (0 : ℝ) ≤ α ^ 4 := by positivity
  have hClnn : 0 ≤ Cl := le_of_lt hClpos
  change α ^ 4 * (Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.mixed 0 1 (eslA Ψ) z θ * Work.Spaces.Wt α z θ)
      + Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.mixed 0 2 (eslA Ψ) z θ * Work.Spaces.Wt α z θ))
    ≤ Cl * Cs * Work.Spaces.HkSq α 2 F
  calc α ^ 4 * (Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.mixed 0 1 (eslA Ψ) z θ * Work.Spaces.Wt α z θ)
        + Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.mixed 0 2 (eslA Ψ) z θ * Work.Spaces.Wt α z θ))
      ≤ α ^ 4 * (Cl * (Work.Spaces.HkSq α 0 (eslA Ψ)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ)))) :=
        mul_le_mul_of_nonneg_left h1' hα4nn
    _ = Cl * (α ^ 4 * (Work.Spaces.HkSq α 0 (eslA Ψ)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ)))) := by ring
    _ ≤ Cl * (Cs * Work.Spaces.HkSq α 2 F) := mul_le_mul_of_nonneg_left h2' hClnn
    _ = Cl * Cs * Work.Spaces.HkSq α 2 F := by ring

end

end Work.FTS.EllipticEst.H2W
