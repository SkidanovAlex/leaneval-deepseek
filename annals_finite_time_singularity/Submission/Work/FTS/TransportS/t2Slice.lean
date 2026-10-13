/-
Copyright: work module for the Elgindi finite-time singularity project.

# `t2Slice`: the `θ`-slice integrability of the easy part of the `D_z`-transport pairing

`Work.FTS.TransportS.T2Slice` is the third of the five inputs of the frozen statement `T2S`
(see `Submission/Work/FTS/TransportS/T2S.lean`): for `f` in the open-quadrant class
(`SmoothOpen f`, `HkMem α 4 f`, `CoefThMem 1 f`) and `g` in the `RegQ α 4`-class with the
order-`5` honesty `HkMem α 5 g`, every angular slice `θ ↦ Heasy α f g z θ` (`z ∈ Iz`) is
integrable on `Iθ`.

## Route

`Heasy = H4PairInt α (f·D_z g) g − Hhard` decomposes, on the open interval, into the block
products `EasyZ f g i · GblkZ g i` and `EasyM α f g j i · GblkM α g j i`
(`Work.FTS.H2.HeasyBlocksId`).  The `Gblk`-blocks are the summands of the `ℋ⁴`-integrand of
`g` (`Work.FTS.H2.HkIntegrand_eq_blocks`), whence the pointwise AM–GM bound
`|Heasy| ≤ (EasyU + HkIntegrand α 4 g)/2` (`T2SliceAux.heasy_abs_le`).

* `EasyU` is integrable: each `(EasyZ f g i)²` (`i ≤ 4`) is
  (`T2SliceAux.easyZ_sq_int'`) and each `(EasyM α f g j i)²` (`1 ≤ i`, `i+j ≤ 4`) is
  (`T2SliceAux.easyM_sq_int`); both rest on the pointwise data of the frozen hypotheses: the
  `f`-data are bounded pure `D_z^b f`, `b ≤ 3` (`T2SliceAux.sliceBoundF`) and `ℋ⁴`-slots; the
  `g`-data are bounded mixed derivatives of order `≤ 4` (`T2SliceAux.sliceBoundG'`, from
  `HkMem α 5 g` — exactly the extra order-`5` honesty that repairs the counterexample of
  `NOTES_T2SliceEasyQuad_FALSE.md`) and `ℋ⁵`-slots.
* `HkIntegrand α 4 g` is integrable because `HkIntegrand α 4 g ≤ HkIntegrand α 5 g`
  (`Work.Spaces.HkIntegrand_mono`) and `HkMem α 5 g` gives the slice integrability of the
  latter.
* The a.e. strong measurability of the slice of `Heasy` is the continuity of `Heasy` on the
  open quadrant (`continuousOn_H4PairInt_open`, `continuousOn_Hhard_Qd`) restricted to the
  slice.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.T2S
import Submission.Work.FTS.TransportS.t2Aesm
import Submission.Work.FTS.TransportS.T2SliceAux.t2Mine
import Submission.Work.FTS.TransportS.T2SliceAux.sliceBoundF
import Submission.Work.FTS.TransportS.T2SliceAux.easyM_sq_int

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## `SmoothQuad` implies `SmoothOpen` (`Work.FTS.TransportS.smoothOpen_of_smoothQuad`) -/

/-! ## A.e. strong measurability of the slice of `Heasy` -/

theorem aesm_heasy (α : ℝ) {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.LocData.SmoothQuad g) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable (fun θ => Work.FTS.H2.Heasy α f g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hgO : Work.FTS.EllipticEst.SmoothOpen g := smoothOpen_of_smoothQuad hg
  have hu : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * Work.Spaces.Dz g z θ) :=
    smoothOpen_mul_Dz hf hgO
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.H2.Heasy α f g p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.H2.H4PairInt α
        (fun z θ => f z θ * Work.Spaces.Dz g z θ) g p.1 p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (continuousOn_H4PairInt_open α hu hgO).mono fun p hp => hp
    have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.H2.Hhard α f g p.1 p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (continuousOn_Hhard_Qd hf hg).mono fun p hp => hp
    have hsub : (fun p : ℝ × ℝ => Work.FTS.H2.Heasy α f g p.1 p.2)
        = fun p : ℝ × ℝ => Work.FTS.H2.H4PairInt α
            (fun z θ => f z θ * Work.Spaces.Dz g z θ) g p.1 p.2
          - Work.FTS.H2.Hhard α f g p.1 p.2 := rfl
    rw [hsub]
    exact h1.sub h2
  exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz

/-! ## Integrability of the `ℋ⁴`-integrand of `g` on the slice -/

theorem hk4_slice_int {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 5 g) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
      Work.Spaces.Iθ := by
  refine MeasureTheory.Integrable.mono' (hmem.1 z hz.le)
    (Work.Spaces.aesm_slice_of_continuousOn_Qd _
      ((Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 g hg).mono
        (fun p hp => hp)) hz) ?_
  filter_upwards with θ
  have h4 := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have h5 := Work.Spaces.HkIntegrand_nonneg α 5 g z θ
  simpa only [Real.norm_eq_abs, abs_of_nonneg h4, abs_of_nonneg h5]
    using Work.Spaces.HkIntegrand_mono α 4 g z θ

/-! ## Integrability of the easy energy `EasyU` on the slice -/

theorem easyU_slice_int {α : ℝ} {f g : ℝ → ℝ → ℝ} {z : ℝ}
    (hZ : ∀ i : ℕ, i ≤ 4 → MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.H2.EasyZ f g i z θ) ^ 2) Work.Spaces.Iθ)
    (hM : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 4 → MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.H2.EasyM α f g j i z θ) ^ 2) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.H2.EasyU α f g z θ) Work.Spaces.Iθ := by
  show MeasureTheory.IntegrableOn (fun θ =>
    (∑ i ∈ Finset.range 5, (Work.FTS.H2.EasyZ f g i z θ) ^ 2)
      + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then (Work.FTS.H2.EasyM α f g j i z θ) ^ 2 else 0))
    Work.Spaces.Iθ
  refine MeasureTheory.Integrable.add ?_ ?_
  · refine MeasureTheory.integrable_finsetSum _ fun i hi => ?_
    exact hZ i (by have := Finset.mem_range.mp hi; omega)
  · refine MeasureTheory.integrable_finsetSum _ fun i hi => ?_
    refine MeasureTheory.integrable_finsetSum _ fun j hj => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · rw [show (fun θ => (if 1 ≤ i ∧ i + j ≤ 4 then (Work.FTS.H2.EasyM α f g j i z θ) ^ 2
          else 0)) = fun θ => (Work.FTS.H2.EasyM α f g j i z θ) ^ 2 from
        funext fun θ => if_pos hc]
      exact hM j i hc.1 hc.2
    · rw [show (fun θ => (if 1 ≤ i ∧ i + j ≤ 4 then (Work.FTS.H2.EasyM α f g j i z θ) ^ 2
          else 0)) = fun _ => (0 : ℝ) from
        funext fun θ => if_neg hc]
      exact integrableOn_zero

/-! ## The main theorem -/

theorem t2Slice : Work.FTS.TransportS.T2Slice := by
  intro α f g hα hα1 hsf hsg z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hzpos
  · -- the slice at `z = 0` vanishes identically
    subst h0
    have hzero : (fun θ => Work.FTS.H2.Heasy α f g 0 θ) = fun _ => (0 : ℝ) := by
      funext θ
      simp only [Work.FTS.H2.Heasy, Work.FTS.H2.H4PairInt, Work.FTS.H2.Hhard,
        Work.FTS.H2.Whz, Work.FTS.H2.Wm, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
      simp
    rw [hzero]
    exact integrableOn_zero
  · -- the case `z > 0`
    have hf : Work.FTS.EllipticEst.SmoothOpen f := hsf.1
    have hgQ : Work.FTS.LocData.SmoothQuad g := hsg.1.1
    have hgO : Work.FTS.EllipticEst.SmoothOpen g := smoothOpen_of_smoothQuad hgQ
    have hmemf : Work.Spaces.HkMem α 4 f := hsf.2.1
    have hmemg : Work.Spaces.HkMem α 5 g := hsg.2.1
    -- the pointwise data
    obtain ⟨Kf, hKf0, hFb⟩ :=
      Work.FTS.TransportS.T2SliceAux.sliceBoundF α f hα hα1 hf hmemf z hzpos
    obtain ⟨Kg, hKg0, hGb⟩ :=
      Work.FTS.TransportS.T2SliceAux.sliceBoundG' α g hα hα1 hgO hmemg z hzpos
    -- the `ℋ⁴`/`ℋ⁵` slots on the slice
    have hFs : ∀ b : ℕ, b ≤ 4 → MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ := fun b hb =>
      Work.FTS.TransportS.T2SliceAux.pureSlotOn hf hmemf b hb hzpos
    have hGs : ∀ j : ℕ, j ≤ 5 → MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.DzIter j g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ := fun j hj =>
      Work.FTS.TransportS.T2SliceAux.pureSlotOn hgO hmemg j hj hzpos
    have hFsm : ∀ a b : ℕ, 1 ≤ a → a + b ≤ 4 → MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.mixed b a f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := fun a b ha hab =>
      Work.FTS.TransportS.T2SliceAux.mixedSlotOn hf hmemf a b ha hab hzpos
    have hGsm : ∀ a b : ℕ, 1 ≤ a → a + b ≤ 5 → MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.mixed b a g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := fun a b ha hab =>
      Work.FTS.TransportS.T2SliceAux.mixedSlotOn hgO hmemg a b ha hab hzpos
    -- the easy blocks
    have hZ : ∀ i : ℕ, i ≤ 4 → MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.H2.EasyZ f g i z θ) ^ 2) Work.Spaces.Iθ := fun i hi =>
      Work.FTS.TransportS.T2SliceAux.easyZ_sq_int' α f g Kf Kg hKf0 hKg0 hf hgO hzpos
        hFb (fun j hj θ hθ => hGb 0 j (by omega) θ hθ) hFs hGs i hi
    have hM : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 4 → MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.H2.EasyM α f g j i z θ) ^ 2) Work.Spaces.Iθ := fun j i hi hij =>
      Work.FTS.TransportS.T2SliceAux.easyM_sq_int α f g Kf Kg hα hKf0 hKg0 hf hgO hzpos
        hFb hGb hFsm hGsm j i hi hij
    -- the domination
    have hEasyU : MeasureTheory.IntegrableOn (fun θ => Work.FTS.H2.EasyU α f g z θ)
        Work.Spaces.Iθ := easyU_slice_int hZ hM
    have hHk : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
        Work.Spaces.Iθ := hk4_slice_int hgQ hmemg hzpos
    have hdom : MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.H2.EasyU α f g z θ + Work.Spaces.HkIntegrand α 4 g z θ) / 2)
        Work.Spaces.Iθ := (hEasyU.add hHk).div_const 2
    refine MeasureTheory.Integrable.mono' hdom (aesm_heasy α hf hgQ hzpos) ?_
    filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with θ hθ
    rw [Real.norm_eq_abs]
    exact Work.FTS.TransportS.T2SliceAux.heasy_abs_le hθ

end Work.FTS.TransportS
