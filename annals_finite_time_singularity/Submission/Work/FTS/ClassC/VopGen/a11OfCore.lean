import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.VopGen.Gate
import Submission.Work.FTS.EllipticEst.Prop.levelTopSlotsTwoBnds
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
-- ===== merged: Submission.Work.FTS.ClassC.VopGen.CoreSplit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.ClassC.VopGen.CoreSplit` — the two halves of the level-`2` core inequality

`CoreASlot11Hyp` (the tree's `Cores.Aux.coreASlot11`, the `(1,1)`-slot/T2 wall) is the single gate
of the level-parametric `V`-slot (`VopGen/Gate.lean`, `VopGen/a11OfCore.lean`).  The documented
route of `Cores/ASlot11Aux/coreASlot11.lean` splits it into two *independent* halves:

* `SliceAgmonStmt` — the **a.e.-slicewise angular Agmon inequality** for the slice
  `f := z ↦ D_z(z²∂_z²Ψ)(z,·)`: for a.e. `z > 0`,

    `∫_θ (f')² μ ≤ -∫_θ f · f'' · μ`,   `μ = sin(2θ)^{2-γ}`,

  which is `Prop.sliceAgmonMu` (`Prop/mixedSlotInterpEta.lean`, PROVED) applied slicewise, its six
  hypotheses being supplied by the weak class `EllWeakPos α 2 F Ψ`: smoothness of `Aof Ψ`
  (`Prop.smoothOpen_zsq_mul`), the two endpoint bounds `|f θ| ≤ M·sin(2θ)`, `|f'| ≤ M`
  (`Cores/InterpGammaCore/InterpJumpAux/{value_abs_le_mul_left,value_abs_le_mul_right,
  exists_deriv_abs_bound}`, PROVED), the vanishing of the endpoint *values* of `f`
  (`Prop.aof_tendsto_zero`, PROVED), and the `σ_η`-honesty of `f'' = ∂_θ²(D_z(z²∂_z²Ψ))`
  (`VopGen.hkMem_pth2_Dz_AofGen`, PROVED; equivalently
  `Prop.HkMem_zero_pthIter2_Ab` after Clairaut).

* `TruncStmt` — everything after the slice inequality: the logarithmic cut-off
  `Work.Blocks.logCutoff_open` (smooth, supported in `(0,∞)`, increasing to `1`, with
  `‖D_zχ_k‖_∞ ≤ K/log(k+2)`), the per-`θ`-slice radial integration by parts
  (`Prop.radialIbpWild`, PROVED — its flux vanishes because the cut-off is compactly supported in
  `(0,∞)`), Cauchy–Schwarz in `z` and then in `θ` (giving `√(qr) + 3√(pr)` with
  `p = ∫∫X²ρμ`, `q = ∫∫(D_zX)²ρμ`, `r = ∫∫Y²ρμ`, `X = D_z(z²∂_z²Ψ)`, `Y = ∂_θ²(z²∂_z²Ψ)`), the
  passage `k → ∞` (Fatou on the left, the uniform bound on the right), and AM–GM (`K = 2`
  suffices).

The glue is definitional: `coreASlot11_of_pieces hA hB = hB hA`.
-/
noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.VopGen

set_option autoImplicit false

/-- **The a.e.-slicewise angular Agmon inequality** for `f = D_z(z²∂_z²Ψ)` (the "slice half" of
the level-`2` core inequality). -/
def SliceAgmonStmt : Prop :=
  ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ -(∫ θ in Work.Spaces.Iθ,
            Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ
              * (Work.Spaces.pthIter 2 (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ))) z θ
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))

/-- **The "truncation half" of the level-`2` core inequality**: from the a.e.-slicewise Agmon
inequality, the core inequality (`= Cores.Aux.coreASlot11`). -/
def TruncStmt : Prop :=
  SliceAgmonStmt → CoreASlot11Hyp

/-- **The level-`2` core inequality from its two halves.** -/
theorem coreASlot11_of_pieces (hA : SliceAgmonStmt) (hB : TruncStmt) : CoreASlot11Hyp := hB hA

end Work.FTS.ClassC.VopGen
end
end
-- ===== merged: Submission.Work.FTS.ClassC.VopGen.a11OfCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.ClassC.VopGen.a11OfCore` — the `(1,1)`-slot in the `Tk`-form from the core inequality

`CoreASlot11Hyp` (the tree's `Cores.Aux.coreASlot11`) bounds the light-weighted `(1,1)`-slot of
`A = z²∂_z²Ψ` by the three light-weighted *pure* slots of `A`.  The level-`2` assembly
(`Cores.TopSlotsTwoClean_of`) needs the same slot in the `Tk`-form `A11Hyp`
(`= Cores.ASlot11Bound`).  This file bridges the two:

* `Tk α 1 (D_z A)` is the double integral of `(D_θ(D_zA)·Wt)²`, and
  `(sin(2θ)·∂_θ(D_zA)·Wt)² = (∂_θ(D_zA))²·w²·sin(2θ)^{2-γ}` on `Iθ`: so `Tk α 1 (D_z A)` *is*
  the left-hand side of `CoreASlot11Hyp`;
* each of the three right-hand side slots of `CoreASlot11Hyp` is compared with its
  `s^{-η}`-weighted (hence *heavier*) counterpart, which is controlled by `|F|²_{ℋ²}` through the
  proved level-`0` slot bounds `Prop.HkSq_zero_Ab_DzIter_le` (`∂_z`-slots of `A`) and
  `Prop.HkSq_zero_pthIter2_Ab_le` (`∂_θ²`-slot of `A`, via `∂_θ²A = D_z²(∂_θ²Ψ) − D_z(∂_θ²Ψ)`).
-/
noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.VopGen

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.Spaces (HkSq HkMem HkIntegrand HkIntegrand_nonneg w Iz Iθ)

/-- `sin(2θ)` is nonnegative on `Iθ`. -/
private theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- The nonnegativity of the light-weighted slot integrand. -/
private theorem slot_nonneg (f : ℝ → ℝ) (z : ℝ) (α : ℝ) :
    0 ≤ ∫ θ in Iθ,
      (f θ) ^ 2 * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
  MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (sin_two_nonneg_Iθ ⟨hθ.1, hθ.2⟩) _)

/-- **The level-`1` weight identity** `(sin(2θ)·Wt)² = w²·sin(2θ)^{2-γ}` on `Iθ`. -/
private theorem sin_mul_Wt_sq_prv (α z θ : ℝ) (hα4 : α ≤ 1 / 4) (hθ : θ ∈ Iθ) :
    (Real.sin (2 * θ) * Work.Spaces.Wt α z θ) ^ 2
      = (w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ (2 : ℕ)
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_mul_natCast hs (-(Work.Spaces.gam α / 2)) 2]
    congr 1
    push_cast
    ring
  have htwo : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
    have hne : ((2 : ℕ) : ℝ) + (-(Work.Spaces.gam α)) ≠ 0 := by
      rw [Work.Spaces.gam]
      intro hc
      linarith
    rw [← Real.rpow_natCast (Real.sin (2 * θ)) 2,
      ← Real.rpow_add' (x := Real.sin (2 * θ)) hs (y := ((2 : ℕ) : ℝ))
        (z := -(Work.Spaces.gam α)) hne]
    congr 1 <;> push_cast <;> ring
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow, h1]
  calc (Real.sin (2 * θ)) ^ 2 * ((w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = (w z) ^ 2
          * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
    _ = (w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by rw [htwo]

/-- The light angular weight is dominated by the heavy one: `sin(2θ)^{2-γ} ≤ sin(2θ)^{-η}`. -/
private theorem rpow_two_sub_gam_le_sEta {α θ : ℝ} (hα4 : α ≤ 1 / 4) (hθ : θ ∈ Iθ) :
    (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h]
    rw [Real.zero_rpow (show 2 - Work.Spaces.gam α ≠ 0 by
          rw [Work.Spaces.gam]; intro hc; linarith),
      Real.zero_rpow (show -(Work.Spaces.eta) ≠ 0 by
          rw [Work.Spaces.eta]; intro hc; linarith)]
  have hle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hexp : 0 ≤ Work.Spaces.eta + (2 - Work.Spaces.gam α) := by
    rw [Work.Spaces.eta, Work.Spaces.gam]; linarith
  have hkey : (Real.sin (2 * θ)) ^ (Work.Spaces.eta + (2 - Work.Spaces.gam α)) ≤ 1 :=
    Real.rpow_le_one hs hle1 hexp
  have hsplit : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta + (2 - Work.Spaces.gam α))
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [← Real.rpow_add h]
    congr 1
    ring
  rw [hsplit]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hs _) hkey

/-- **The light-weighted integral is dominated by the `ℋ⁰`-square.** -/
private theorem light_le_HkSq (α : ℝ) (hα4 : α ≤ 1 / 4) (g : ℝ → ℝ → ℝ) (hmem : HkMem α 0 g) :
    (∫ z in Iz, ∫ θ in Iθ,
        (g z θ) ^ 2 * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      ≤ HkSq α 0 g := by
  rw [Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => slot_nonneg (g z) z α) hmem.2 ?_
  filter_upwards [Work.FTS.EllipticEst.Prop.ae_restrict_Iz_pos] with z hz
  have hzI : z ∈ Iz := Set.mem_Ici.mpr hz.le
  refine MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (Real.rpow_nonneg (sin_two_nonneg_Iθ ⟨hθ.1, hθ.2⟩) _))) (hmem.1 z hzI) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
  rw [Work.FTS.EllipticEst.Prop.HkIntegrand_zero_apply]
  have hsin : (0 : ℝ) ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ ⟨hθ.1, hθ.2⟩
  have hsq : (g z θ * (w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (g z θ) ^ 2 * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [show g z θ * (w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        = (g z θ * w z) / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) from by ring]
    rw [Work.FTS.EllipticEst.Prop.div_rpow_half_sq_Iθ ⟨hθ.1, hθ.2⟩]
    ring
  rw [hsq]
  exact mul_le_mul_of_nonneg_left (rpow_two_sub_gam_le_sEta hα4 ⟨hθ.1, hθ.2⟩)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The `ℋ⁰`-honesty of the `j`-th radial slot of `A = z²∂_z²Ψ`, `j ≤ 2`. -/
private theorem hkMem_zero_DzIter_Aof {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (j : ℕ) (hj : j ≤ 2) :
    HkMem α 0 (Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.Prop.smoothOpen_zsq_mul (hΨ.pzIter 2)
  exact Work.FTS.EllipticEst.Prop.HkMem_zero_of_pointwise (c := 1) zero_le_one (hA.DzIter j) h.memA
    (fun z θ hz hθ hlt => by
      rw [Work.FTS.EllipticEst.Prop.HkIntegrand_zero_apply]
      simpa using Work.Spaces.sq_le_HkIntegrand_z α 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ j hj)

/-- **The `(1,1)`-slot in the `Tk`-form**, from the core inequality. -/
theorem a11OfCore (h : CoreASlot11Hyp) : A11Hyp := by
  obtain ⟨K, hKpos, hK⟩ := h
  obtain ⟨C0, hC0pos, h0⟩ := Work.FTS.EllipticEst.EllGap.ellWeak0Clean
  obtain ⟨CZ, hCZpos, hZ⟩ := Work.FTS.EllipticEst.Prop.HkSq_zero_Ab_DzIter_le ⟨C0, hC0pos, h0⟩
  obtain ⟨CY, hCYpos, hY⟩ := Work.FTS.EllipticEst.Prop.HkSq_zero_DzIter_Bb_le ⟨C0, hC0pos, h0⟩
  refine ⟨K * (2 * CZ + 4 * CY) + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 hwk
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
  have hNF : 0 ≤ HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have h4 : α ^ 4 ≤ 1 := pow_le_one₀ hα.le (by linarith)
  -- ## the `Tk`-form of the left-hand side
  have hTkId : Work.FTS.EllipticEst.remov.Step.Tk α 1
        (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      = ∫ z in Iz, ∫ θ in Iθ,
          (Work.Spaces.pth (Work.Spaces.DzIter 1
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ) ^ 2 * (w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
    rw [Work.FTS.EllipticEst.remov.Step.Tk]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine MeasureTheory.integral_congr_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_)
    beta_reduce
    rw [show Work.Spaces.mixed 0 1 (Work.Spaces.DzIter 1
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ from rfl]
    rw [show (Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter 1
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.pth (Work.Spaces.DzIter 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ) ^ 2
          * (Real.sin (2 * θ) * Work.Spaces.Wt α z θ) ^ 2 from by ring]
    rw [sin_mul_Wt_sq_prv α z θ hα4 hθ]
    ring
  -- ## the three slot bounds (light weights dominated by heavy ones)
  have ht1 : α ^ 4 * (∫ z in Iz, ∫ θ in Iθ,
      (Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2 * (w z) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) ≤ CZ * HkSq α 2 F := by
    have hcomp := light_le_HkSq α hα4
      (Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      (hkMem_zero_DzIter_Aof hwk 2 (by norm_num))
    have hcong : HkSq α 0 (Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        = HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ hlt =>
        Work.FTS.ClassC.NormPiecesAux.zsqPz2_DzIter_eqOn Ψ hΨ 2 z θ hz hθ hlt)
    have hb := hZ α F Ψ hα hα4 hwk 2 (by norm_num)
    calc α ^ 4 * (∫ z in Iz, ∫ θ in Iθ,
          (Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
            * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ α ^ 4 * HkSq α 0
            (Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
          mul_le_mul_of_nonneg_left hcomp (by positivity)
      _ = α ^ 4 * HkSq α 0
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) := by rw [hcong]
      _ ≤ CZ * HkSq α 2 F := hb
  have ht2 : α ^ 4 * (∫ z in Iz, ∫ θ in Iθ,
      (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2 * (w z) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) ≤ CZ * HkSq α 2 F := by
    have hcomp := light_le_HkSq α hα4
      (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      (hkMem_zero_DzIter_Aof hwk 1 (by norm_num))
    have hcong : HkSq α 0 (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        = HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ hlt =>
        Work.FTS.ClassC.NormPiecesAux.zsqPz2_DzIter_eqOn Ψ hΨ 1 z θ hz hθ hlt)
    have hb := hZ α F Ψ hα hα4 hwk 1 (by norm_num)
    calc α ^ 4 * (∫ z in Iz, ∫ θ in Iθ,
          (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
            * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ α ^ 4 * HkSq α 0
            (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
          mul_le_mul_of_nonneg_left hcomp (by positivity)
      _ = α ^ 4 * HkSq α 0
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) := by rw [hcong]
      _ ≤ CZ * HkSq α 2 F := hb
  have ht3 : α ^ 4 * (∫ z in Iz, ∫ θ in Iθ,
      (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
        * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) ≤ 4 * CY * HkSq α 2 F := by
    have hcomp := light_le_HkSq α hα4
      (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      (Work.FTS.EllipticEst.Prop.HkMem_zero_pthIter2_Ab hwk)
    have hb := Work.FTS.EllipticEst.Prop.HkSq_zero_pthIter2_Ab_le hwk
    have hY1 := hY α F Ψ hα hα4 hwk 1 (by norm_num)
    have hY2 := hY α F Ψ hα hα4 hwk 2 (by norm_num)
    have hCY2 : 0 ≤ HkSq α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) :=
      Work.Spaces.HkSq_nonneg α 0 _
    have hCY1 : 0 ≤ HkSq α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) :=
      Work.Spaces.HkSq_nonneg α 0 _
    calc α ^ 4 * (∫ z in Iz, ∫ θ in Iθ,
          (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
            * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ α ^ 4 * HkSq α 0
            (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
          mul_le_mul_of_nonneg_left hcomp (by positivity)
      _ ≤ α ^ 4 * (2 * (HkSq α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ))
            + HkSq α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ 2 * (HkSq α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ))
            + HkSq α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ))) := by
          nlinarith [hCY1, hCY2, h4]
      _ ≤ 2 * (CY * HkSq α 2 F + CY * HkSq α 2 F) := by linarith [hY2, hY1]
      _ = 4 * CY * HkSq α 2 F := by ring
  -- ## the core inequality and the assembly
  have hcore := hK α F Ψ hα hα4 hwk
  have hLHSnn : 0 ≤ ∫ z in Iz, ∫ θ in Iθ,
      (Work.Spaces.pth (Work.Spaces.DzIter 1
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ) ^ 2 * (w z) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
    integral_nonneg fun z => slot_nonneg _ z α
  calc α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
        (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      = α ^ 4 * (∫ z in Iz, ∫ θ in Iθ,
          (Work.Spaces.pth (Work.Spaces.DzIter 1
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ) ^ 2 * (w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by rw [hTkId]
    _ ≤ α ^ 4 * (K * ((∫ z in Iz, ∫ θ in Iθ,
            (Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
              * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + (∫ z in Iz, ∫ θ in Iθ,
            (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
              * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + (∫ z in Iz, ∫ θ in Iθ,
            (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
              * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
    _ ≤ (K * (2 * CZ + 4 * CY) + 1) * HkSq α 2 F := by
        have hshape : ∀ a b c : ℝ, α ^ 4 * (K * (a + b + c))
            = K * (α ^ 4 * a + α ^ 4 * b + α ^ 4 * c) := by
          intro a b c; ring
        rw [hshape]
        nlinarith [ht1, ht2, ht3, hNF, hKpos.le, hCZpos.le, hCYpos.le]

end Work.FTS.ClassC.VopGen
end
end
