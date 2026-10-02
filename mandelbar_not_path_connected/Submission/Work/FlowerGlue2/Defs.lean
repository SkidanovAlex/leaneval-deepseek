/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue2 team
-/
import Mathlib
import Submission.Work.PARIMPL.Basic
import Submission.Work.FlowerGlue.RefCoord
import Submission.Work.FatouCoord.Main
import Submission.Work.FatouCoordFix.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue2.Defs` — the chart vocabulary of the mandelbar implosion comparison

This is the vocabulary file of the area `Submission/Work/FlowerGlue2/`, the area that exports the
*flower bundles* which the `LavaursPhase` proof of `PARIMPL2` consumes
(`Submission/Work/NOTES_LEAD_mandelbar_implosion.md` §2–§4).  The three objects here are the
ones on which every statement of the area is phrased:

* `w0 P z = -P.s c₀ / (z - d.z₁)` — the chart of the parameter normal form `P : ParNormal d`
  at the parabolic parameter `c₀`, i.e. `w0 = -1/ζ_{c₀}` with `ζ_{c₀}` the chart coordinate of
  `Work.PARIMPL.ParNormal`;
* `approxCoordRep κ w = w - κ * log (-w)` — the repelling analogue of
  `Work.FatouCoord.approxCoord` (principal logarithm of `-w`, fine on `Re w < 0`);
* `WinG P R H` / `WoutG P R H` — the *geometric* windows of the transit, i.e. compact
  real-level sets of the `c₀`-chart (as opposed to the global level sets of
  `approxUin`, which have spurious components — the defect F1 of the lead's note).

The structure `RefData d` is the *reference attracting Fatou coordinate with its asymptotic*:
the bundling requested as item (FG-a) of the design note.  Its instantiation is the theorem
`Work.FlowerGlue2.exists_refData` (`RefAsymp.lean`).

## Contents

* `Work.FlowerGlue2.w0`, `kappa0`, `approxCoordRep`, `WinG`, `WoutG`;
* `Work.FlowerGlue2.RefData` (the reference coordinate, its germ data and its asymptotic);
* the elementary API of `w0`, `WinG`, `WoutG`.
-/

open scoped Topology
open Filter Set Metric

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.FlowerGlue2

open Work.PARIMPL (ParNormal Ft gtc)

open Classical

noncomputable section

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-! ## 1. The chart coordinate and the repelling model coordinate -/

/-- The `c₀`-chart coordinate of the parameter normal form `P`:  `w0 z = -P.s c₀ / (z - d.z₁)`.
Since `P.m c₀ = d.z₁`, this is `-1/ζ_{c₀}` in the notation of the design note. -/
def w0 (P : ParNormal d) (z : ℂ) : ℂ := -P.s c₀ / (z - d.z₁)

@[simp] theorem w0_apply (P : ParNormal d) (z : ℂ) : w0 P z = -P.s c₀ / (z - d.z₁) := rfl

/-- The correction constant `κ₀ = P.κ c₀` of the approximate Écalle coordinate at `c₀`; on the
implosion side `κ₀ = 1 - h₁` because the germ constant `τ = P.h c₀ 0` equals `1` there. -/
def kappa0 (P : ParNormal d) : ℂ := P.κ c₀

/-- The repelling model coordinate `w - κ log (-w)`: the principal logarithm of `-w`, which is
holomorphic and single-valued on the left half-plane `Re w < 0` — the sector on which the
outgoing window lives. -/
def approxCoordRep (κ w : ℂ) : ℂ := w - κ * Complex.log (-w)

@[simp] theorem approxCoordRep_apply (κ w : ℂ) :
    approxCoordRep κ w = w - κ * Complex.log (-w) := rfl

/-- The **incoming geometric window**: a compact real-level set of the `c₀`-chart, sitting at
depth `R` and of imaginary width `H`.  Unlike the global level set of `approxUin` it has no
spurious components (the defect F1 of `NOTES_LEAD_mandelbar_implosion.md` §1). -/
def WinG (P : ParNormal d) (R H : ℝ) : Set ℂ :=
  {z | z ≠ d.z₁ ∧ (w0 P z).re ∈ Icc R (R + 2) ∧ |(w0 P z).im| ≤ H}

/-- The **outgoing geometric window**: the mirror image of `WinG` in the chart. -/
def WoutG (P : ParNormal d) (R H : ℝ) : Set ℂ :=
  {z | z ≠ d.z₁ ∧ (w0 P z).re ∈ Icc (-R - 2) (-R) ∧ |(w0 P z).im| ≤ H}

@[simp] theorem mem_WinG {P : ParNormal d} {R H : ℝ} {z : ℂ} :
    z ∈ WinG P R H ↔ z ≠ d.z₁ ∧ (w0 P z).re ∈ Icc R (R + 2) ∧ |(w0 P z).im| ≤ H := Iff.rfl

@[simp] theorem mem_WoutG {P : ParNormal d} {R H : ℝ} {z : ℂ} :
    z ∈ WoutG P R H ↔ z ≠ d.z₁ ∧ (w0 P z).re ∈ Icc (-R - 2) (-R) ∧ |(w0 P z).im| ≤ H :=
  Iff.rfl

/-! ## 2. Elementary API of the chart coordinate -/

theorem w0_ne_zero {P : ParNormal d} {z : ℂ} (hz : z ≠ d.z₁) : w0 P z ≠ 0 := by
  simp only [w0_apply]
  exact div_ne_zero (neg_ne_zero.mpr (P.s_ne c₀ (mem_ball_self P.hρ₀))) (sub_ne_zero.mpr hz)

theorem sub_z₁_ne_zero {P : ParNormal d} {z : ℂ} (hz : z ≠ d.z₁) : z - d.z₁ ≠ 0 :=
  sub_ne_zero.mpr hz

/-- The chart coordinate is injective off the parabolic point. -/
theorem w0_injOn (P : ParNormal d) : Set.InjOn (w0 P) {z : ℂ | z ≠ d.z₁} := by
  intro z hz z' hz' h
  have hs : P.s c₀ ≠ 0 := P.s_ne c₀ (mem_ball_self P.hρ₀)
  simp only [w0_apply] at h
  have h5 : (-P.s c₀) * (z - d.z₁)⁻¹ = (-P.s c₀) * (z' - d.z₁)⁻¹ := by
    simpa only [div_eq_mul_inv] using h
  exact sub_left_inj.mp (inv_inj.mp (mul_left_cancel₀ (neg_ne_zero.mpr hs) h5))

/-- The chart coordinate is nonzero off the parabolic point. -/
theorem w0_ne_zero' {P : ParNormal d} {z : ℂ} (hz : z ≠ d.z₁) : w0 P z ≠ 0 :=
  w0_ne_zero hz

theorem mem_WinG_of_chart {P : ParNormal d} {R H : ℝ} {z : ℂ} (hz : z ≠ d.z₁)
    (hr : (w0 P z).re ∈ Icc R (R + 2)) (him : |(w0 P z).im| ≤ H) : z ∈ WinG P R H :=
  ⟨hz, hr, him⟩

theorem mem_WoutG_of_chart {P : ParNormal d} {R H : ℝ} {z : ℂ} (hz : z ≠ d.z₁)
    (hr : (w0 P z).re ∈ Icc (-R - 2) (-R)) (him : |(w0 P z).im| ≤ H) : z ∈ WoutG P R H :=
  ⟨hz, hr, him⟩

theorem WinG_subset_ne (P : ParNormal d) (R H : ℝ) : WinG P R H ⊆ {z : ℂ | z ≠ d.z₁} :=
  fun _ h => h.1

theorem WoutG_subset_ne (P : ParNormal d) (R H : ℝ) : WoutG P R H ⊆ {z : ℂ | z ≠ d.z₁} :=
  fun _ h => h.1

theorem WinG_mono_im {P : ParNormal d} {R H H' : ℝ} (h : H ≤ H') : WinG P R H ⊆ WinG P R H' :=
  fun _ hz => ⟨hz.1, hz.2.1, le_trans hz.2.2 h⟩

theorem WoutG_mono_im {P : ParNormal d} {R H H' : ℝ} (h : H ≤ H') : WoutG P R H ⊆ WoutG P R H' :=
  fun _ hz => ⟨hz.1, hz.2.1, le_trans hz.2.2 h⟩

/-- The chart is recovered from its value: the inverse chart relation. -/
theorem chart_recovery {P : ParNormal d} {z : ℂ} (hz : z ≠ d.z₁) :
    z = d.z₁ - P.s c₀ / w0 P z := by
  have hs : P.s c₀ ≠ 0 := P.s_ne c₀ (mem_ball_self P.hρ₀)
  have hw : w0 P z ≠ 0 := w0_ne_zero hz
  rw [w0_apply]
  field_simp
  ring

/-! ## 1b. The far-left repelling petals (`Drep`, `Dst`)

`Drep P R` is the left half-plane of the `c₀`-chart, and `Dst P R` its *Stolz* sector
(`|Im w0| < -Re w0 + 1`).  These are the domains on which the reference repelling coordinate of
`Work.FlowerGlue2.rep_unique_backward` is inverted; the Stolz form is the one for which no sign
hypothesis on `P.h1 c₀` is needed (`NOTES_LEAD_mandelbar_gaps3.md` §1.0). -/

/-- The **reference repelling half-plane petal** in the `c₀`-chart. -/
def Drep (P : ParNormal d) (R : ℝ) : Set ℂ := {z | z ≠ d.z₁ ∧ (w0 P z).re < -R}

/-- The **Stolz petal**: the sector of the chart on which `Re w0 < -R` with `|Im w0|` at most
`-Re w0 + 1` (strict, so that the set is open). -/
def Dst (P : ParNormal d) (R : ℝ) : Set ℂ :=
  {z | z ≠ d.z₁ ∧ (w0 P z).re < -R ∧ |(w0 P z).im| < -(w0 P z).re + 1}

@[simp] theorem mem_Drep {P : ParNormal d} {R : ℝ} {z : ℂ} :
    z ∈ Drep P R ↔ z ≠ d.z₁ ∧ (w0 P z).re < -R := Iff.rfl

@[simp] theorem mem_Dst {P : ParNormal d} {R : ℝ} {z : ℂ} :
    z ∈ Dst P R ↔ z ≠ d.z₁ ∧ (w0 P z).re < -R ∧ |(w0 P z).im| < -(w0 P z).re + 1 := Iff.rfl

theorem Dst_subset_Drep (P : ParNormal d) (R : ℝ) : Dst P R ⊆ Drep P R :=
  fun _ h => ⟨h.1, h.2.1⟩

theorem Drep_subset_of_le {P : ParNormal d} {R R' : ℝ} (h : R' ≤ R) : Drep P R ⊆ Drep P R' :=
  fun _ hz => ⟨hz.1, lt_of_lt_of_le hz.2 (neg_le_neg h)⟩

theorem Dst_subset_of_le {P : ParNormal d} {R R' : ℝ} (h : R' ≤ R) : Dst P R ⊆ Dst P R' :=
  fun _ hz => ⟨hz.1, lt_of_lt_of_le hz.2.1 (neg_le_neg h), hz.2.2⟩

/-- The chart coordinate is continuous off the parabolic point. -/
theorem continuousAt_w0 (P : ParNormal d) {z : ℂ} (hz : z ≠ d.z₁) :
    ContinuousAt (w0 P) z := by
  have hfun : w0 P = fun z : ℂ => -P.s c₀ / (z - d.z₁) := by
    funext z; rw [w0_apply]
  rw [hfun]
  exact continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hz)

theorem isOpen_Drep (P : ParNormal d) (R : ℝ) : IsOpen (Drep P R) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨hzne, hre⟩ := hz
  have h1 : {z' : ℂ | (w0 P z').re < -R} ∈ 𝓝 z :=
    (continuousAt_w0 P hzne).preimage_mem_nhds
      (IsOpen.mem_nhds
        (isOpen_lt Complex.continuous_re continuous_const : IsOpen {w : ℂ | w.re < -R}) hre)
  have h2 : {z : ℂ | z ≠ d.z₁} ∈ 𝓝 z := isOpen_ne.mem_nhds hzne
  exact Filter.inter_mem h2 h1

theorem isOpen_Dst (P : ParNormal d) (R : ℝ) : IsOpen (Dst P R) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨hzne, hre, him⟩ := hz
  have hcw : ContinuousAt (w0 P) z := continuousAt_w0 P hzne
  have h1 : {z' : ℂ | (w0 P z').re < -R} ∈ 𝓝 z :=
    hcw.preimage_mem_nhds
      (IsOpen.mem_nhds
        (isOpen_lt Complex.continuous_re continuous_const : IsOpen {w : ℂ | w.re < -R}) hre)
  have h2 : {z' : ℂ | |(w0 P z').im| + (w0 P z').re < 1} ∈ 𝓝 z := by
    have hcont : ContinuousAt (fun z' : ℂ => |(w0 P z').im| + (w0 P z').re) z :=
      ((continuous_abs.continuousAt.comp (Complex.continuous_im.continuousAt.comp hcw))).add
        (Complex.continuous_re.continuousAt.comp hcw)
    have hlt : |(w0 P z).im| + (w0 P z).re < 1 := by linarith
    exact hcont.preimage_mem_nhds
      (IsOpen.mem_nhds (isOpen_lt continuous_id continuous_const : IsOpen {y : ℝ | y < 1}) hlt)
  have h3 : {z : ℂ | z ≠ d.z₁} ∈ 𝓝 z := isOpen_ne.mem_nhds hzne
  have h23 : {z' : ℂ | |(w0 P z').im| < -(w0 P z').re + 1} ∈ 𝓝 z := by
    have heq : {z' : ℂ | |(w0 P z').im| < -(w0 P z').re + 1}
        = {z' : ℂ | |(w0 P z').im| + (w0 P z').re < 1} := by
      ext z'
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq,
        show -(w0 P z').re + 1 = 1 - (w0 P z').re by ring]
      constructor <;> intro h <;> linarith
    rw [heq]; exact h2
  exact Filter.inter_mem h3 (Filter.inter_mem h1 h23)

/-- Every point of a window is at distance at most `‖P.s c₀‖ / R` from the parabolic point. -/
theorem norm_sub_le_of_mem_WoutG {P : ParNormal d} {R H : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ WoutG P R H) : ‖z - d.z₁‖ ≤ ‖P.s c₀‖ / R := by
  have hz₁ : z ≠ d.z₁ := hz.1
  have hw : w0 P z ≠ 0 := w0_ne_zero hz₁
  have hre : (w0 P z).re ≤ -R := hz.2.1.2
  have hmono : R ≤ ‖w0 P z‖ := by
    have h1 : |(w0 P z).re| ≤ ‖w0 P z‖ := Complex.abs_re_le_norm _
    rw [abs_of_nonpos (by linarith : (w0 P z).re ≤ 0)] at h1
    linarith
  have hz_eq : z - d.z₁ = -P.s c₀ / w0 P z := by
    linear_combination chart_recovery (P := P) hz₁
  rw [hz_eq, norm_div, norm_neg]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hR hmono

/-- The two geometric windows are separated as soon as `R > 0`. -/
theorem disjoint_WinG_WoutG (P : ParNormal d) {R H H' : ℝ} (hR : 0 < R) :
    Disjoint (WinG P R H) (WoutG P R H') := by
  rw [Set.disjoint_left]
  intro z hz hz'
  have h1 : R ≤ (w0 P z).re := hz.2.1.1
  have h2 : (w0 P z).re ≤ -R := hz'.2.1.2
  linarith

/-! ## 3. The reference attracting coordinate with its asymptotic (FG-a) -/

/-- **The reference attracting Fatou coordinate of a root-parabolic parameter, with its
asymptotic and the germ data that produces it.**

This is the bundling requested in `NOTES_LEAD_mandelbar_implosion.md` §3.2 item (FG-a): the
construction `Work.FlowerGlue.exists_refCoord` together with the estimate
`Work.FlowerGlue.fatouCoord_approx_bound`.  The extra fields `lam`, `ap`, `f`, `h`, `r`, `A`,
`A'`, `hb`, `conj` record *which* affine chart of the germ at `d.z₁` the coordinate was built
in; they are what makes the chart-consistency statement
`Work.FlowerGlue2.exists_refCoord_P` (the L0.6 of the design note) provable, by comparing this
chart with the chart `z = P.m c₀ + P.s c₀·ζ` of `ParNormal` at `c₀`.

The coordinate lives on the half-plane petal `Rf.P`, which (by `mem_P`) contains every point of
the half-plane `Re (w0-chart) > N`; and on that half-plane

  `‖Rf.φ z - approxCoord (1 - ap) (chart-coordinate of z)‖ ≤ K / Re (chart-coordinate of z)`.

The width `N` and the constant `K` are the explicit constants of the construction. -/
structure RefData {c : ℂ} (d : Work.EL.RootParabolic c) where
  /-- the reference coordinate (a half-plane petal with its Abel coordinate, saturating) -/
  toRef : Work.FlowerGlue.RefCoord d
  /-- the scale `λ_f` of the germ chart `u ↦ d.z₁ + λ_f·u` -/
  lam : ℂ
  /-- the linear coefficient `a_f` of the germ of the normal form in that chart -/
  ap : ℂ
  /-- the normalised germ -/
  f : ℂ → ℂ
  /-- the germ's `h` -/
  h : ℂ → ℂ
  /-- the germ radius -/
  r : ℝ
  /-- the germ constants -/
  A : ℝ
  A' : ℝ
  lam_ne : lam ≠ 0
  hb : Work.FatouCoord.ParabolicBounds f h ap r A A'
  /-- the germ chart conjugates `F c` to `f` on the chart ball -/
  conj : ∀ u ∈ ball (0 : ℂ) r, Work.EL.F c (d.z₁ + lam * u) = d.z₁ + lam * f u
  /-- the depth threshold of the asymptotic -/
  N : ℝ
  /-- the constant of the asymptotic -/
  K : ℝ
  N_pos : 0 < N
  K_nonneg : 0 ≤ K
  /-- the petal contains the whole half-plane `Re (chart) > N` -/
  mem_P : ∀ z : ℂ, z ≠ d.z₁ → N < (-lam / (z - d.z₁)).re → z ∈ toRef.P
  /-- the asymptotic `φ = approxCoord + O(1/Re chart)` -/
  asymp : ∀ z : ℂ, z ≠ d.z₁ → N < (-lam / (z - d.z₁)).re →
    ‖toRef.φ z - Work.FatouCoord.approxCoord (1 - ap) (-lam / (z - d.z₁))‖
      ≤ K / (-lam / (z - d.z₁)).re

/-! ## 4. The comparison datum of the attracting side (N1)

The flower bundle (N1 of `NOTES_LEAD_mandelbar_implosion.md` §3.3) is kept free of the flower
*type* so that it is cheap to elaborate and so that `box_deep` can be stated against it without
dragging the whole `ParabolicFlowerFix` record: the petal `Pa` and its coordinate `φa` are
*parameters*, so an `AttrCompare P fl.Pa fl.φa` is genuinely tied to the flower `fl`, while the
record only stores the dynamics facts of the petal, the reference coordinate and the asymptotic
comparison. -/

/-- **The attracting comparison datum** (N1).  For the petal `Pa` and its coordinate `φa`:
`φa = approxCoord κ₀ (w0 ·) + sa + O(1/Re w0)` on the whole half-plane `Re w0 > N`, together
with the petal data of the flower and the `ℤ`-saturating reference coordinate to which `φa` is
compared. -/
structure AttrCompare {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    (Pa : Set ℂ) (φa : ℂ → ℂ) where
  isOpen_Pa : IsOpen Pa
  mapsTo_Pa : MapsTo (Work.PARIMPL.Ft c₀) Pa Pa
  tendsto_Pa : ∀ z ∈ Pa,
    Tendsto (fun n : ℕ => (Work.PARIMPL.Ft c₀)^[n] z) atTop (nhds d.z₁)
  enters_Pa : ∀ z : ℂ,
    Tendsto (fun n : ℕ => (Work.PARIMPL.Ft c₀)^[n] z) atTop (nhds d.z₁) →
    (∀ n : ℕ, (Work.PARIMPL.Ft c₀)^[n] z ≠ d.z₁) → ∃ n : ℕ, (Work.PARIMPL.Ft c₀)^[n] z ∈ Pa
  φa_inj : Set.InjOn φa Pa
  φa_shift : ∀ z ∈ Pa, φa (Work.PARIMPL.Ft c₀ z) = φa z + 1
  /-- the reference coordinate -/
  Rf : Work.FlowerGlue.RefCoord d
  /-- the phase constant: `φa = reference coordinate + sa + O(1/Re w0)` -/
  sa : ℂ
  /-- the depth threshold -/
  N : ℝ
  /-- the constant of the asymptotic -/
  K : ℝ
  N_pos : 0 < N
  K_nonneg : 0 ≤ K
  /-- the reference petal contains the whole half-plane `Re w0 > N` -/
  mem_P : ∀ z : ℂ, z ≠ d.z₁ → N < (w0 P z).re → z ∈ Rf.P
  /-- the asymptotic comparison, on the petal (where `φa` is constrained) -/
  asymp : ∀ z ∈ Pa, z ≠ d.z₁ → N < (w0 P z).re →
    ‖φa z - (Work.FatouCoord.approxCoord (P.κ c₀) (w0 P z) + sa)‖ ≤ K / (w0 P z).re

end

end Work.FlowerGlue2
