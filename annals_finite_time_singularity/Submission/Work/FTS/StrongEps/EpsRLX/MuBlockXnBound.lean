/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsRLX/MuBlockXnBound` — the `ℋ⁴`-Lipschitz bound of the modulation block

The block

  `muBlock α Φs E W = fun z θ => -μ̄(W)·AK α z θ + N_* μ(W) (lamfun μ(W)) W z θ`

telescopes along a difference `d = W₁ - W₂` into

  `muBlock W₁ - muBlock W₂
     = -Δμ̄·AK α + μ₁·(D_z d - d) + Δμ·(D_z W₂ - W₂)`

on the open quadrant (`MuBlockBase.muBlock_sub_eq`).  This module turns that identity into the
`ℋ⁴`-bound

  `|muBlock W₁ - muBlock W₂|_{ℋ⁴} ≤ C·(1 + |W₁|_{ℋ⁵} + |W₂|_{ℋ⁵})²·|d|_{ℋ⁵}`

under the hypotheses that `W₁`, `W₂` are of class `C`, that the two modulation constants are
small (`|μ| ≤ 1/2`, which makes the `N_*`-collapse available) and that the differences
`Δμ̄`, `Δμ` are Lipschitz in the `ℋ⁵`-size of the difference with constant `Km`, with
`|AK α|_{ℋ⁴} ≤ KAK`.  The three summands are estimated separately
(`Xn_const_mul`, the `ℋ⁵`-upgrade `Xn_Dz_le_Xn5` for the `D_z`-slots, and the subadditivity
`HkNorm_add_le_open`), and the arithmetic is collected at the end.

The statement is *not* restricted to `α ≤ 1`; the only place where the range of `α` enters is the
`ℋ⁴`-honesty of the fixed profile `AK α`, which is supplied for every `α > 0` by
`EpsRLX.HkMemAKGeneral`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsRLX.MuBlockBase
import Submission.Work.FTS.StrongEps.EpsRLX.HkMemAKGeneral
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.GalFields.Norm.Basic
import Submission.Work.FTS.GalFields.Tail.SlotAdjoints
import Submission.Work.FTS.StrongEps.EComparison.Reduction
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.CoercivityFix.Assembly.RegQAux
import Submission.Work.FTS.StrongPersist.H6Rows.AK6Row
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.NonlinRows.NRow5

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary tools for `Xn` -/

/-- `Xn` only sees the values on the open quadrant. -/
private theorem Xn_congr_open (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    Work.FTS.Nonlin.Xn α f = Work.FTS.Nonlin.Xn α g := by
  rw [show Work.FTS.Nonlin.Xn α f = Work.Spaces.HkNorm α 4 f from rfl,
    show Work.FTS.Nonlin.Xn α g = Work.Spaces.HkNorm α 4 g from rfl,
    Work.Spaces.HkNorm, Work.Spaces.HkNorm,
    Work.FTS.EllipticEst.HkSq_congr_open α 4 h]

/-- `Xn` is homogeneous for the multiplication by a scalar. -/
private theorem Xn_const_mul (α : ℝ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.FTS.Nonlin.Xn α (fun z θ => c * f z θ) = |c| * Work.FTS.Nonlin.Xn α f := by
  have h1 : (fun z θ : ℝ => c * f z θ) = c • f := by
    funext z θ; simp [Pi.smul_apply, smul_eq_mul]
  rw [h1]
  exact Work.FTS.EllipticEst.HkNorm_smul c α 4 f

/-- `Xn` is invariant under negation. -/
private theorem Xn_neg (α : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.FTS.Nonlin.Xn α (fun z θ => - f z θ) = Work.FTS.Nonlin.Xn α f := by
  show Work.Spaces.HkNorm α 4 (fun z θ : ℝ => - f z θ) = Work.Spaces.HkNorm α 4 f
  have h2 : (fun z θ : ℝ => - f z θ) = (-1 : ℝ) • f := by
    funext z θ; simp [Pi.smul_apply]
  rw [h2, Work.FTS.EllipticEst.HkNorm_smul]
  norm_num

/-- **Subadditivity of `Xn` on the open-quadrant class**, in the difference form. -/
private theorem Xn_sub_le (α : ℝ) (hα : 0 < α) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α 4 f) (hmg : Work.Spaces.HkMem α 4 g) :
    Work.FTS.Nonlin.Xn α (fun z θ => f z θ - g z θ)
      ≤ 2 * (Work.FTS.Nonlin.Xn α f + Work.FTS.Nonlin.Xn α g) := by
  have hgs : Work.FTS.EllipticEst.SmoothOpen (fun z θ => - g z θ) :=
    Work.FTS.GalFields.Tail.SmoothOpen.neg hg
  have hgm : Work.Spaces.HkMem α 4 (fun z θ => - g z θ) :=
    Work.FTS.NonlinRows.HkMem_neg' α 4 hmg
  have h1 := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hf hgs hmf hgm
  have hneg : Work.Spaces.HkNorm α 4 (fun z θ : ℝ => - g z θ) = Work.Spaces.HkNorm α 4 g :=
    Xn_neg α g
  rw [hneg] at h1
  rw [Xn_congr_open α (f := fun z θ => f z θ - g z θ) (g := fun z θ => f z θ + - g z θ)
    (fun z θ _ _ _ => by ring)]
  simpa only [Work.FTS.Nonlin.Xn] using h1

/-! ## The bound -/

theorem MuBlockXnBound {α Km KAK : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hKm : 0 ≤ Km) :
    ∃ C : ℝ, 0 < C ∧ ∀ {W₁ W₂ : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      |Work.FTS.StrongEps.EpsRLX.muOf α Φs E W₁| ≤ 1 / 2 →
      |Work.FTS.StrongEps.EpsRLX.muOf α Φs E W₂| ≤ 1 / 2 →
      |Work.FTS.StrongEps.EpsRLX.mubarOf α Φs E W₁
          - Work.FTS.StrongEps.EpsRLX.mubarOf α Φs E W₂|
        ≤ Km * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) →
      |Work.FTS.StrongEps.EpsRLX.muOf α Φs E W₁
          - Work.FTS.StrongEps.EpsRLX.muOf α Φs E W₂|
        ≤ Km * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) →
      Work.FTS.Nonlin.Xn α (Work.Construction.AK α) ≤ KAK →
      Work.FTS.Nonlin.Xn α (fun z θ =>
        Work.FTS.StrongEps.EpsRLX.muBlock α Φs E W₁ z θ
          - Work.FTS.StrongEps.EpsRLX.muBlock α Φs E W₂ z θ)
        ≤ C * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) ^ 2
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
  refine ⟨2 * |Km| * (|KAK| + 8) + 20, by positivity, ?_⟩
  intro W₁ W₂ hW₁ hW₂ hμ₁ hμ₂ hbdμb hbdμ hAKb
  -- ## the abbreviations
  set μ₁ : ℝ := muOf α Φs E W₁ with hμ₁def
  set μ₂ : ℝ := muOf α Φs E W₂ with hμ₂def
  set mb₁ : ℝ := mubarOf α Φs E W₁ with hmb₁def
  set mb₂ : ℝ := mubarOf α Φs E W₂ with hmb₂def
  set d : Fn := fun z θ => W₁ z θ - W₂ z θ with hddef
  set Y : ℝ := Work.FTS.GalFields.Xn5 α W₁ with hYdef
  set Y' : ℝ := Work.FTS.GalFields.Xn5 α W₂ with hY'def
  set Z : ℝ := Work.FTS.GalFields.Xn5 α d with hZdef
  set P : ℝ := 1 + Y + Y' with hPdef
  set S : ℝ := P * Z with hSdef
  set T : ℝ := P ^ 2 * Z with hTdef
  set Cc : ℝ := 2 * |Km| * (|KAK| + 8) + 20 with hCdef
  -- ## the four converted hypotheses
  have hμ₁b : |μ₁| ≤ 1 / 2 := hμ₁
  have hμ₂b : |μ₂| ≤ 1 / 2 := hμ₂
  have hmbdb : |mb₁ - mb₂| ≤ Km * P * Z := hbdμb
  have hmudb : |μ₁ - μ₂| ≤ Km * P * Z := hbdμ
  have hAKb' : Work.FTS.Nonlin.Xn α (Work.Construction.AK α) ≤ |KAK| :=
    le_trans hAKb (le_abs_self KAK)
  have hμ₁ne : μ₁ ≠ -1 := by
    intro hcon; rw [hcon] at hμ₁b; norm_num at hμ₁b
  have hμ₂ne : μ₂ ≠ -1 := by
    intro hcon; rw [hcon] at hμ₂b; norm_num at hμ₂b
  -- ## the smoothness / honesty data
  have hsm₁ : Work.FTS.EllipticEst.SmoothOpen W₁ := hW₁.reg
  have hsm₂ : Work.FTS.EllipticEst.SmoothOpen W₂ := hW₂.reg
  have hdC : Work.FTS.ClassC.ClassC α d := by
    rw [hddef]
    exact Work.FTS.StrongEps.EComparison.classC_sub hW₁ hW₂
  have hdsm : Work.FTS.EllipticEst.SmoothOpen d := hdC.reg
  have h5₁ : Work.Spaces.HkMem α 5 W₁ :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm₁ 5 (by norm_num) hW₁.mem
  have h5₂ : Work.Spaces.HkMem α 5 W₂ :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm₂ 5 (by norm_num) hW₂.mem
  have h5d : Work.Spaces.HkMem α 5 d :=
    Work.FTS.OpenPkg.HkMem_mono_open hdsm 5 (by norm_num) hdC.mem
  have h4d : Work.Spaces.HkMem α 4 d :=
    Work.FTS.OpenPkg.HkMem_mono_open hdsm 4 (by norm_num) hdC.mem
  have h4₂ : Work.Spaces.HkMem α 4 W₂ :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm₂ 4 (by norm_num) hW₂.mem
  have hDzd4 : Work.Spaces.HkMem α 4 (Work.Spaces.Dz d) :=
    Work.FTS.IPGen.HkMem_Dz_le hdsm h5d
  have hDz₂4 : Work.Spaces.HkMem α 4 (Work.Spaces.Dz W₂) :=
    Work.FTS.IPGen.HkMem_Dz_le hsm₂ h5₂
  -- the `ℋ⁴`-honesty of the fixed profile `AK α` (valid for every `α > 0`)
  have hAKmem : Work.Spaces.HkMem α 4 (Work.Construction.AK α) :=
    Work.FTS.StrongEps.EpsRLX.HkMemAKGeneral α hα
  have hAKsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.AK α) :=
    Work.FTS.StrongPersist.AK_smoothO α
  -- ## the five pieces
  set m1 : Fn := fun z θ => -(mb₁ - mb₂) * Work.Construction.AK α z θ with hm1def
  set m2 : Fn := fun z θ => μ₁ * (Work.Spaces.Dz d z θ - d z θ) with hm2def
  set m3 : Fn := fun z θ => (μ₁ - μ₂) * (Work.Spaces.Dz W₂ z θ - W₂ z θ) with hm3def
  set m23 : Fn := fun z θ => m2 z θ + m3 z θ with hm23def
  set nice : Fn := fun z θ => m1 z θ + m23 z θ with hnicedef
  -- ## smoothness of the pieces
  have hsm1 : Work.FTS.EllipticEst.SmoothOpen m1 := by
    rw [hm1def]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (-(mb₁ - mb₂)) hAKsm
  have hsm2 : Work.FTS.EllipticEst.SmoothOpen m2 := by
    rw [hm2def]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul μ₁
      (Work.FTS.NonlinRows.smoothOpen_sub hdsm.Dz hdsm)
  have hsm3 : Work.FTS.EllipticEst.SmoothOpen m3 := by
    rw [hm3def]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (μ₁ - μ₂)
      (Work.FTS.NonlinRows.smoothOpen_sub hsm₂.Dz hsm₂)
  have hsm23 : Work.FTS.EllipticEst.SmoothOpen m23 := by
    rw [hm23def]
    exact Work.FTS.NonlinRows.smoothOpen_add hsm2 hsm3
  have hsmNice : Work.FTS.EllipticEst.SmoothOpen nice := by
    rw [hnicedef]
    exact Work.FTS.NonlinRows.smoothOpen_add hsm1 hsm23
  -- ## honesty of the pieces
  have hmemSubd : Work.Spaces.HkMem α 4 (fun z θ => Work.Spaces.Dz d z θ - d z θ) := by
    have h := Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 hdsm.Dz
      (Work.FTS.GalFields.Tail.SmoothOpen.neg hdsm) hDzd4
      (Work.FTS.NonlinRows.HkMem_neg' α 4 h4d)
    exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 h
      (fun z _ θ _ => by ring)
  have hmemSub2 : Work.Spaces.HkMem α 4 (fun z θ => Work.Spaces.Dz W₂ z θ - W₂ z θ) := by
    have h := Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 hsm₂.Dz
      (Work.FTS.GalFields.Tail.SmoothOpen.neg hsm₂) hDz₂4
      (Work.FTS.NonlinRows.HkMem_neg' α 4 h4₂)
    exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 h
      (fun z _ θ _ => by ring)
  have hm1mem : Work.Spaces.HkMem α 4 m1 := by
    rw [hm1def]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-(mb₁ - mb₂)) hAKmem
  have hm2mem : Work.Spaces.HkMem α 4 m2 := by
    rw [hm2def]
    exact Work.FTS.LocData.HkMem_const_mul α 4 μ₁ hmemSubd
  have hm3mem : Work.Spaces.HkMem α 4 m3 := by
    rw [hm3def]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (μ₁ - μ₂) hmemSub2
  have hm23mem : Work.Spaces.HkMem α 4 m23 := by
    rw [hm23def]
    exact Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 hsm2 hsm3 hm2mem hm3mem
  have hmNicemem : Work.Spaces.HkMem α 4 nice := by
    rw [hnicedef]
    exact Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 hsm1 hsm23 hm1mem hm23mem
  -- ## the sizes
  have hY0 : 0 ≤ Y := by rw [hYdef]; exact Work.Spaces.HkNorm_nonneg α 5 W₁
  have hY'0 : 0 ≤ Y' := by rw [hY'def]; exact Work.Spaces.HkNorm_nonneg α 5 W₂
  have hZ0 : 0 ≤ Z := by rw [hZdef]; exact Work.Spaces.HkNorm_nonneg α 5 d
  have hP1 : 1 ≤ P := by rw [hPdef]; linarith
  have hS0 : 0 ≤ S := by
    rw [hSdef]; exact mul_nonneg (by rw [hPdef]; linarith) hZ0
  have hT0 : 0 ≤ T := by
    rw [hTdef]; exact mul_nonneg (sq_nonneg _) hZ0
  have hY'P : Y' ≤ P := by rw [hPdef]; linarith
  have hST : S ≤ T := by
    rw [hSdef, hTdef]
    exact mul_le_mul_of_nonneg_right (by nlinarith [hP1]) hZ0
  have hZT : Z ≤ T := by
    rw [hTdef]; nlinarith [hP1, hZ0]
  have hSY' : S * Y' ≤ T := by
    rw [hSdef, hTdef]; nlinarith [hP1, hZ0, hY'P]
  have hbdSZ : Km * P * Z = |Km| * S := by
    rw [hSdef, abs_of_nonneg hKm]; ring
  have hmbdb' : |mb₁ - mb₂| ≤ |Km| * S := by rw [← hbdSZ]; exact hmbdb
  have hmudb' : |μ₁ - μ₂| ≤ |Km| * S := by rw [← hbdSZ]; exact hmudb
  -- ## the three `Xn`-bounds
  have hX1 : Work.FTS.Nonlin.Xn α m1 ≤ |Km| * S * |KAK| := by
    rw [hm1def, Xn_const_mul, abs_neg]
    exact mul_le_mul hmbdb' hAKb'
      (Work.Spaces.HkNorm_nonneg α 4 (Work.Construction.AK α))
      (mul_nonneg (abs_nonneg Km) hS0)
  have hsubDb : Work.FTS.Nonlin.Xn α (fun z θ => Work.Spaces.Dz d z θ - d z θ) ≤ 4 * Z := by
    have h1 := Xn_sub_le α hα hdsm.Dz hdsm hDzd4 h4d
    have h2 : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz d) ≤ Z := by
      rw [hZdef]; exact Work.FTS.GalFields.Xn_Dz_le_Xn5 hα hdsm h5d
    have h3 : Work.FTS.Nonlin.Xn α d ≤ Z := by
      rw [hZdef]
      exact Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 5) (k' := 4) (by norm_num) h5d
    linarith
  have hsub2b : Work.FTS.Nonlin.Xn α (fun z θ => Work.Spaces.Dz W₂ z θ - W₂ z θ) ≤ 4 * Y' := by
    have h1 := Xn_sub_le α hα hsm₂.Dz hsm₂ hDz₂4 h4₂
    have h2 : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz W₂) ≤ Y' := by
      rw [hY'def]; exact Work.FTS.GalFields.Xn_Dz_le_Xn5 hα hsm₂ h5₂
    have h3 : Work.FTS.Nonlin.Xn α W₂ ≤ Y' := by
      rw [hY'def]
      exact Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 5) (k' := 4) (by norm_num) h5₂
    linarith
  have hX2 : Work.FTS.Nonlin.Xn α m2 ≤ 2 * Z := by
    rw [hm2def, Xn_const_mul]
    calc |μ₁| * Work.FTS.Nonlin.Xn α (fun z θ => Work.Spaces.Dz d z θ - d z θ)
        ≤ (1 / 2) * (4 * Z) :=
          mul_le_mul hμ₁b hsubDb
            (Work.Spaces.HkNorm_nonneg α 4 (fun z θ => Work.Spaces.Dz d z θ - d z θ))
            (by norm_num)
      _ = 2 * Z := by ring
  have hX3 : Work.FTS.Nonlin.Xn α m3 ≤ |Km| * S * (4 * Y') := by
    rw [hm3def, Xn_const_mul]
    exact mul_le_mul hmudb' hsub2b
      (Work.Spaces.HkNorm_nonneg α 4 (fun z θ => Work.Spaces.Dz W₂ z θ - W₂ z θ))
      (mul_nonneg (abs_nonneg Km) hS0)
  -- ## the assembly
  have hXn23 : Work.FTS.Nonlin.Xn α m23 ≤ 2 * (Work.FTS.Nonlin.Xn α m2 + Work.FTS.Nonlin.Xn α m3) := by
    rw [hm23def]
    exact Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hsm2 hsm3 hm2mem hm3mem
  have hXnNice : Work.FTS.Nonlin.Xn α nice ≤ 2 * (Work.FTS.Nonlin.Xn α m1 + Work.FTS.Nonlin.Xn α m23) := by
    rw [hnicedef]
    exact Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hsm1 hsm23 hm1mem hm23mem
  have hstep1 : 2 * (Work.FTS.Nonlin.Xn α m1 + Work.FTS.Nonlin.Xn α m23)
      ≤ 2 * (|Km| * S * |KAK| + 2 * (2 * Z + |Km| * S * (4 * Y'))) := by
    have h2 : Work.FTS.Nonlin.Xn α m23 ≤ 2 * (2 * Z + |Km| * S * (4 * Y')) := by
      linarith [hXn23, hX2, hX3]
    linarith [hX1, h2]
  have hstep2 : 2 * (|Km| * S * |KAK| + 2 * (2 * Z + |Km| * S * (4 * Y'))) ≤ Cc * T := by
    have e0 : 2 * (|Km| * S * |KAK| + 2 * (2 * Z + |Km| * S * (4 * Y')))
        = 2 * (|Km| * (S * |KAK|)) + 8 * Z + 16 * (|Km| * (S * Y')) := by ring
    have e1 : 2 * (|Km| * (S * |KAK|)) ≤ 2 * (|Km| * (T * |KAK|)) := by
      have h := mul_le_mul_of_nonneg_right hST (abs_nonneg KAK)
      have h2 := mul_le_mul_of_nonneg_left h (abs_nonneg Km)
      linarith
    have e2 : 8 * Z ≤ 8 * T := by linarith [hZT]
    have e3 : 16 * (|Km| * (S * Y')) ≤ 16 * (|Km| * T) := by
      have h := mul_le_mul_of_nonneg_left hSY' (abs_nonneg Km)
      linarith
    have e4 : Cc * T = 2 * (|Km| * (T * |KAK|)) + 8 * T + 16 * (|Km| * T) + 12 * T := by
      rw [hCdef]; ring
    rw [e0, e4]
    linarith [e1, e2, e3, hT0]
  have hgoal : Cc * P ^ 2 * Z = Cc * T := by rw [hTdef]; ring
  rw [hgoal]
  refine le_trans ?_ (le_trans hXnNice (le_trans hstep1 hstep2))
  refine le_of_eq (Xn_congr_open α (fun z θ hz hθ0 hθ1 => ?_))
  rw [muBlock_sub_eq hsm₁ hsm₂ (by rw [← hμ₁def]; exact hμ₁ne) (by rw [← hμ₂def]; exact hμ₂ne)
    z θ hz hθ0 hθ1]
  simp only [hnicedef, hm23def, hm1def, hm2def, hm3def, hddef]
  ring

end Work.FTS.StrongEps.EpsRLX
