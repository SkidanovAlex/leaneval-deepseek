import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.H5.DataW
import Submission.Work.FTS.StrongEps.H5.Data
import Submission.Work.FTS.StrongEps.H5.LevelShift
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0
import Submission.Work.FTS.StrongEps.H5.Atoms.L5AtomsW
import Submission.Work.FTS.StrongEps.H5.Atoms.L5L12W
import Submission.Work.FTS.StrongEps.H5.Atoms.L5C2mL12W
import Submission.Work.FTS.StrongEps.H5.Atoms.W5DthFstar
import Submission.Work.FTS.StrongEps.H5.Atoms.W5DzFstar
import Submission.Work.FTS.StrongEps.H5.Atoms.W5C2mL12Fstar
import Submission.Work.FTS.StrongEps.H5.Atoms.HkMem5N0fix

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5

open MeasureTheory Set Filter
open scoped Real Topology
open Work.Spaces
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The level-`5` additivity of `HkMem`/`HkNorm` -/

/-- **Binary additivity of the level-`5` membership and norm** (the level-`5` analogue of
`ClassCRHS.add2`). -/
theorem add2_5 {α : ℝ} (hα : 0 < α) {u v : ℝ → ℝ → ℝ} {Bu Bv : ℝ}
    (husm : Work.FTS.EllipticEst.SmoothOpen u) (hvsm : Work.FTS.EllipticEst.SmoothOpen v)
    (hu : Work.Spaces.HkMem α 5 u) (hv : Work.Spaces.HkMem α 5 v)
    (bu : Work.Spaces.HkNorm α 5 u ≤ Bu) (bv : Work.Spaces.HkNorm α 5 v ≤ Bv)
    (hBu : 0 ≤ Bu) (hBv : 0 ≤ Bv) :
    Work.Spaces.HkMem α 5 (fun z θ => u z θ + v z θ) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => u z θ + v z θ) ≤ 2 * (Bu + Bv) := by
  have hmem : Work.Spaces.HkMem α 5 (fun z θ => u z θ + v z θ) :=
    Work.FTS.EllipticEst.RPFresh.HkMem_add_open α 5 husm hvsm hu hv
  refine ⟨hmem, ?_⟩
  have hb := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 5 hα husm hvsm hu hv
  have h1 := Work.Spaces.HkNorm_nonneg α 5 u
  have h2 := Work.Spaces.HkNorm_nonneg α 5 v
  linarith

/-! ## The assembly from the atomic data

The atomic sources are the lemmas `L5W_atoms_w`, `L5_L12w`, `L5_c2mL12w`, `W5_DthFstar`,
`W5_DzFstar`, `W5_c2m_L12Fstar`, `HkMem5_N0fix` (modules `H5/Atoms*.lean`). -/

/-- **The level-`5` `N₀`-block from the atomic data.** -/
theorem HkMemXnN05_of_atoms
    (hWat : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
      ∃ a : ℝ, 0 < a ∧ ∀ {w : Fn}, Work.FTS.ClassC.ClassC α w →
        Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 → Work.Spaces.HkNorm α 6 w ≤ B →
        L5 α w a ∧ L5 α (Work.Spaces.Dz w) a ∧ L5 α (Work.Spaces.Dth w) a)
    (hL12 : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
      ∃ a : ℝ, 0 < a ∧ ∀ {w : Fn}, Work.FTS.ClassC.ClassC α w →
        Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 → Work.Spaces.HkNorm α 6 w ≤ B →
        L5 α (fun z θ => Work.Construction.L12 w z) a)
    (hc2mL12 : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
      ∃ a : ℝ, 0 < a ∧ ∀ {w : Fn}, Work.FTS.ClassC.ClassC α w →
        Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 → Work.Spaces.HkNorm α 6 w ≤ B →
        L5 α (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) a)
    (hDthF : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∃ a : ℝ, 0 < a ∧
        W5 α (Work.Spaces.Dth (Work.Construction.Fstar α)) a)
    (hDzF : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∃ a : ℝ, 0 < a ∧
        W5 α (Work.Spaces.Dz (Work.Construction.Fstar α)) a)
    (hc2mL12F : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∃ a : ℝ, 0 < a ∧
        W5 α (fun z θ => Work.Construction.c2m θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z) a)
    (hN0fix : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∃ a : ℝ, 0 < a ∧
        Work.Spaces.HkMem α 5 (Work.FTS.Nonlin.N0fix α) ∧
        Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N0fix α) ≤ a) :
    ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
      ∃ K : ℝ, 0 < K ∧ ∀ {w : Fn},
        Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
        Work.Spaces.HkNorm α 6 w ≤ B →
        Work.Spaces.HkMem α 5 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) ∧
        Work.Spaces.HkNorm α 5 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) ≤ K := by
  intro α hαI C₀ B
  have hα : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  -- ## the universal constants
  obtain ⟨Cp, hCp, hprod⟩ := Work.FTS.OpenPkg.prod_field
  obtain ⟨Cw, hCw, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  -- ## the atomic data
  obtain ⟨aw, haw, hwdata⟩ := hWat hαI (C₀ := C₀) (B := B)
  obtain ⟨aL, haL, hLdata⟩ := hL12 hαI (C₀ := C₀) (B := B)
  obtain ⟨aN, haN, hNdata⟩ := hc2mL12 hαI (C₀ := C₀) (B := B)
  obtain ⟨aDF, haDF, hDFdata⟩ := hDthF hαI
  obtain ⟨aDz, haDz, hDzdata⟩ := hDzF hαI
  obtain ⟨aF2, haF2, hF2data⟩ := hc2mL12F hαI
  obtain ⟨a0, ha0, h0mem, h0bd⟩ := hN0fix hαI
  have hrpow : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  -- ## the level-`5` bounds of the seven pieces
  set b0 : ℝ := a0 with hb0
  set b1 : ℝ := |1 / α| * (3 * (Cp * α ^ (-(1 / 2 : ℝ)) * aL * aw)) with hb1
  set b2 : ℝ := |3 / (2 * α)| * (3 * (Cw * α ^ (-(1 / 2 : ℝ)) * aDF * aL)) with hb2
  set b3 : ℝ := |3 / (2 * α)| * (3 * (Cp * α ^ (-(1 / 2 : ℝ)) * aw * aL)) with hb3
  set b4 : ℝ := |(-1 : ℝ)| * (3 * (Cw * α ^ (-(1 / 2 : ℝ)) * aDz * aN)) with hb4
  set b5 : ℝ := |(-1 : ℝ)| * (3 * (Cp * α ^ (-(1 / 2 : ℝ)) * aN * aw)) with hb5
  set b6 : ℝ := |(-1 : ℝ)| * (3 * (Cw * α ^ (-(1 / 2 : ℝ)) * aF2 * aw)) with hb6
  have hb0nn : 0 ≤ b0 := by rw [hb0]; exact ha0.le
  have hb1nn : 0 ≤ b1 := by
    rw [hb1]
    exact mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (mul_nonneg hCp.le hrpow) haL.le) haw.le))
  have hb2nn : 0 ≤ b2 := by
    rw [hb2]
    exact mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (mul_nonneg hCw.le hrpow) haDF.le) haL.le))
  have hb3nn : 0 ≤ b3 := by
    rw [hb3]
    exact mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (mul_nonneg hCp.le hrpow) haw.le) haL.le))
  have hb4nn : 0 ≤ b4 := by
    rw [hb4]
    exact mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (mul_nonneg hCw.le hrpow) haDz.le) haN.le))
  have hb5nn : 0 ≤ b5 := by
    rw [hb5]
    exact mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (mul_nonneg hCp.le hrpow) haN.le) haw.le))
  have hb6nn : 0 ≤ b6 := by
    rw [hb6]
    exact mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (mul_nonneg hCw.le hrpow) haF2.le) haw.le))
  -- ## the cumulative bounds
  set c6 : ℝ := 2 * (b5 + b6) with hc6
  set c5 : ℝ := 2 * (b4 + c6) with hc5
  set c4 : ℝ := 2 * (b3 + c5) with hc4
  set c3 : ℝ := 2 * (b2 + c4) with hc3
  set c2 : ℝ := 2 * (b1 + c3) with hc2
  set c1 : ℝ := 2 * (b0 + c2) with hc1
  have hc6nn : 0 ≤ c6 := by rw [hc6]; linarith
  have hc5nn : 0 ≤ c5 := by rw [hc5]; linarith
  have hc4nn : 0 ≤ c4 := by rw [hc4]; linarith
  have hc3nn : 0 ≤ c3 := by rw [hc3]; linarith
  have hc2nn : 0 ≤ c2 := by rw [hc2]; linarith
  have hc1nn : 0 ≤ c1 := by rw [hc1]; linarith
  refine ⟨c1 + 1, by linarith, ?_⟩
  -- ## the data
  intro w hw hXnw hX6
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hw.reg
  have hL12sm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_aux hα hw
  have hc2msm : Work.FTS.EllipticEst.SmoothOpen
      (fun _ (θ : ℝ) => Work.Construction.c2m θ) :=
    Work.FTS.GalFields.RHS.smoothOpen_c2m_ang
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have hL12Fsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_L12_Fstar α
  have hnegsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) :=
    Work.FTS.NonlinRows.smoothOpen_mul hc2msm hL12sm
  -- ## the atomic facts
  have hatoms := hwdata hw hXnw hX6
  have hL5w : L5 α w aw := hatoms.1
  have hL5Dzw : L5 α (Work.Spaces.Dz w) aw := hatoms.2.1
  have hL5Dthw : L5 α (Work.Spaces.Dth w) aw := hatoms.2.2
  have hL5L12 : L5 α (fun z θ => Work.Construction.L12 w z) aL := hLdata hw hXnw hX6
  have hL5N : L5 α (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) aN :=
    hNdata hw hXnw hX6
  have hDF5 : W5 α (Work.Spaces.Dth (Work.Construction.Fstar α)) aDF := hDFdata
  have hDz5 : W5 α (Work.Spaces.Dz (Work.Construction.Fstar α)) aDz := hDzdata
  have hF25 : W5 α (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z) aF2 := hF2data
  -- ## the six product rows
  have row1 := L5_mul (α := α) (Cprod := Cp) (C := fun z θ => Work.Construction.L12 w z)
    (G := w) (c := 1 / α) (a := aL) (b := aw) hα hα1 hCp (hprod α hα hα1)
    haL.le haw.le hL5L12 hL5w
  have row2 := W5_mul (α := α) (Cw := Cw) (F := Work.Spaces.Dth (Work.Construction.Fstar α))
    (G := fun z θ => Work.Construction.L12 w z) (c := 3 / (2 * α)) (a := aDF) (b := aL)
    hα hα1 hCw (hwprod α hα hα1) haDF.le haL.le hDF5 hL5L12
  have row3 := L5_mul (α := α) (Cprod := Cp) (C := Work.Spaces.Dth w)
    (G := fun z θ => Work.Construction.L12 w z) (c := 3 / (2 * α)) (a := aw) (b := aL)
    hα hα1 hCp (hprod α hα hα1) haw.le haL.le hL5Dthw hL5L12
  have row4 := W5_mul (α := α) (Cw := Cw) (F := Work.Spaces.Dz (Work.Construction.Fstar α))
    (G := fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) (c := -1)
    (a := aDz) (b := aN) hα hα1 hCw (hwprod α hα hα1) haDz.le haN.le hDz5 hL5N
  have row5 := L5_mul (α := α) (Cprod := Cp) (C := fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 w z) (G := Work.Spaces.Dz w) (c := -1) (a := aN) (b := aw)
    hα hα1 hCp (hprod α hα hα1) haN.le haw.le hL5N hL5Dzw
  have row6 := W5_mul (α := α) (Cw := Cw) (F := fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z) (G := Work.Spaces.Dz w)
    (c := -1) (a := aF2) (b := aw) hα hα1 hCw (hwprod α hα hα1) haF2.le haw.le hF25 hL5Dzw
  -- ## the equalities with the named pieces
  have h1eq : Work.FTS.Nonlin.N03g α w = fun z θ => (1 / α)
      * ((fun z θ => Work.Construction.L12 w z) z θ * w z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N03g, Work.Construction.N03]
    ring
  have h2eq : Work.FTS.Nonlin.N04aF α w = fun z θ => (3 / (2 * α))
      * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          * (fun z θ => Work.Construction.L12 w z) z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04aF, Work.Construction.N04a, Work.Construction.s2,
      Work.Spaces.Dth, Work.Spaces.pth]
    ring
  have h3eq : Work.FTS.Nonlin.N04bF α w = fun z θ => (3 / (2 * α))
      * (Work.Spaces.Dth w z θ * (fun z θ => Work.Construction.L12 w z) z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04bF, Work.Construction.N04b, Work.Construction.s2,
      Work.Spaces.Dth, Work.Spaces.pth]
    ring
  have h4eq : Work.FTS.Nonlin.N05aF α w = fun z θ => -1
      * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ
          * (Work.Construction.c2m θ * Work.Construction.L12 w z)) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05aF, Work.Construction.N05a]
    ring
  have h5eq : Work.FTS.Nonlin.N05bF α w = fun z θ => -1
      * ((Work.Construction.c2m θ * Work.Construction.L12 w z) * Work.Spaces.Dz w z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05bF, Work.Construction.N05b]
    ring
  have h6eq : Work.FTS.Nonlin.N06F α w = fun z θ => -1
      * ((Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z)
          * Work.Spaces.Dz w z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N06F, Work.Construction.N06]
    ring
  -- ## the seven pieces: membership, smoothness, norm bound
  have h0m : Work.Spaces.HkMem α 5 (Work.FTS.Nonlin.N0fix α) := h0mem
  have h1m : Work.Spaces.HkMem α 5 (Work.FTS.Nonlin.N03g α w) := by
    rw [h1eq]; exact row1.1
  have h2m : Work.Spaces.HkMem α 5 (Work.FTS.Nonlin.N04aF α w) := by
    rw [h2eq]; exact row2.1
  have h3m : Work.Spaces.HkMem α 5 (Work.FTS.Nonlin.N04bF α w) := by
    rw [h3eq]; exact row3.1
  have h4m : Work.Spaces.HkMem α 5 (Work.FTS.Nonlin.N05aF α w) := by
    rw [h4eq]; exact row4.1
  have h5m : Work.Spaces.HkMem α 5 (Work.FTS.Nonlin.N05bF α w) := by
    rw [h5eq]; exact row5.1
  have h6m : Work.Spaces.HkMem α 5 (Work.FTS.Nonlin.N06F α w) := by
    rw [h6eq]; exact row6.1
  have h0bd' : Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N0fix α) ≤ b0 := by
    rw [hb0]; exact h0bd
  have h1bd : Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N03g α w) ≤ b1 := by
    rw [h1eq, hb1]; exact row1.2
  have h2bd : Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N04aF α w) ≤ b2 := by
    rw [h2eq, hb2]; exact row2.2
  have h3bd : Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N04bF α w) ≤ b3 := by
    rw [h3eq, hb3]; exact row3.2
  have h4bd : Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N05aF α w) ≤ b4 := by
    rw [h4eq, hb4]; exact row4.2
  have h5bd : Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N05bF α w) ≤ b5 := by
    rw [h5eq, hb5]; exact row5.2
  have h6bd : Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N06F α w) ≤ b6 := by
    rw [h6eq, hb6]; exact row6.2
  have h0sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N0fix α) :=
    Work.FTS.StrongPersist.L3Rhs.smoothOpen_N0fix α hα hα1
  have h1sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N03g α w) := by
    rw [h1eq]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (1 / α)
      (Work.FTS.NonlinRows.smoothOpen_mul hL12sm hsmw)
  have h2sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N04aF α w) := by
    rw [h2eq]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α))
      (Work.FTS.NonlinRows.smoothOpen_mul hFsm.Dth hL12sm)
  have h3sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N04bF α w) := by
    rw [h3eq]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α))
      (Work.FTS.NonlinRows.smoothOpen_mul hsmw.Dth hL12sm)
  have h4sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N05aF α w) := by
    rw [h4eq]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (-1)
      (Work.FTS.NonlinRows.smoothOpen_mul hFsm.Dz hnegsm)
  have h5sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N05bF α w) := by
    rw [h5eq]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (-1)
      (Work.FTS.NonlinRows.smoothOpen_mul hnegsm hsmw.Dz)
  have h6sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N06F α w) := by
    rw [h6eq]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (-1)
      (Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.NonlinRows.smoothOpen_mul hc2msm hL12Fsm) hsmw.Dz)
  -- ## the nested assembly
  have ht6 := add2_5 (α := α) hα (u := Work.FTS.Nonlin.N05bF α w)
    (v := Work.FTS.Nonlin.N06F α w) h5sm h6sm h5m h6m h5bd h6bd hb5nn hb6nn
  have ht6' : Work.Spaces.HkNorm α 5
      (fun z θ => Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ) ≤ c6 := by
    rw [hc6]; exact ht6.2
  have hsm6' : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ) :=
    Work.FTS.NonlinRows.smoothOpen_add h5sm h6sm
  have ht5 := add2_5 (α := α) hα (u := Work.FTS.Nonlin.N05aF α w)
    (v := fun z θ => Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)
    h4sm hsm6' h4m ht6.1 h4bd ht6' hb4nn hc6nn
  have ht5' : Work.Spaces.HkNorm α 5
      (fun z θ => Work.FTS.Nonlin.N05aF α w z θ
        + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)) ≤ c5 := by
    rw [hc5]; exact ht5.2
  have hsm5' : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Nonlin.N05aF α w z θ
        + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)) :=
    Work.FTS.NonlinRows.smoothOpen_add h4sm hsm6'
  have ht4 := add2_5 (α := α) hα (u := Work.FTS.Nonlin.N04bF α w)
    (v := fun z θ => Work.FTS.Nonlin.N05aF α w z θ
      + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))
    h3sm hsm5' h3m ht5.1 h3bd ht5' hb3nn hc5nn
  have ht4' : Work.Spaces.HkNorm α 5
      (fun z θ => Work.FTS.Nonlin.N04bF α w z θ
        + (Work.FTS.Nonlin.N05aF α w z θ
          + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))) ≤ c4 := by
    rw [hc4]; exact ht4.2
  have hsm4' : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Nonlin.N04bF α w z θ
        + (Work.FTS.Nonlin.N05aF α w z θ
          + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))) :=
    Work.FTS.NonlinRows.smoothOpen_add h3sm hsm5'
  have ht3 := add2_5 (α := α) hα (u := Work.FTS.Nonlin.N04aF α w)
    (v := fun z θ => Work.FTS.Nonlin.N04bF α w z θ
      + (Work.FTS.Nonlin.N05aF α w z θ
        + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))
    h2sm hsm4' h2m ht4.1 h2bd ht4' hb2nn hc4nn
  have ht3' : Work.Spaces.HkNorm α 5
      (fun z θ => Work.FTS.Nonlin.N04aF α w z θ
        + (Work.FTS.Nonlin.N04bF α w z θ
          + (Work.FTS.Nonlin.N05aF α w z θ
            + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))) ≤ c3 := by
    rw [hc3]; exact ht3.2
  have hsm3' : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Nonlin.N04aF α w z θ
        + (Work.FTS.Nonlin.N04bF α w z θ
          + (Work.FTS.Nonlin.N05aF α w z θ
            + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))) :=
    Work.FTS.NonlinRows.smoothOpen_add h2sm hsm4'
  have ht2 := add2_5 (α := α) hα (u := Work.FTS.Nonlin.N03g α w)
    (v := fun z θ => Work.FTS.Nonlin.N04aF α w z θ
      + (Work.FTS.Nonlin.N04bF α w z θ
        + (Work.FTS.Nonlin.N05aF α w z θ
          + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))))
    h1sm hsm3' h1m ht3.1 h1bd ht3' hb1nn hc3nn
  have ht2' : Work.Spaces.HkNorm α 5
      (fun z θ => Work.FTS.Nonlin.N03g α w z θ
        + (Work.FTS.Nonlin.N04aF α w z θ
          + (Work.FTS.Nonlin.N04bF α w z θ
            + (Work.FTS.Nonlin.N05aF α w z θ
              + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))))) ≤ c2 := by
    rw [hc2]; exact ht2.2
  have hsm2' : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Nonlin.N03g α w z θ
        + (Work.FTS.Nonlin.N04aF α w z θ
          + (Work.FTS.Nonlin.N04bF α w z θ
            + (Work.FTS.Nonlin.N05aF α w z θ
              + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))))) :=
    Work.FTS.NonlinRows.smoothOpen_add h1sm hsm3'
  have ht1 := add2_5 (α := α) hα (u := Work.FTS.Nonlin.N0fix α)
    (v := fun z θ => Work.FTS.Nonlin.N03g α w z θ
      + (Work.FTS.Nonlin.N04aF α w z θ
        + (Work.FTS.Nonlin.N04bF α w z θ
          + (Work.FTS.Nonlin.N05aF α w z θ
            + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))))
    h0sm hsm2' h0m ht2.1 h0bd' ht2' hb0nn hc2nn
  have hSum_le : Work.Spaces.HkNorm α 5
      (fun z θ => Work.FTS.Nonlin.N0fix α z θ
        + (Work.FTS.Nonlin.N03g α w z θ
          + (Work.FTS.Nonlin.N04aF α w z θ
            + (Work.FTS.Nonlin.N04bF α w z θ
              + (Work.FTS.Nonlin.N05aF α w z θ
                + (Work.FTS.Nonlin.N05bF α w z θ
                  + Work.FTS.Nonlin.N06F α w z θ)))))) ≤ c1 := by
    rw [hc1]; exact ht1.2
  -- ## the transfer to `N₀`
  have hsplit := fun z θ (h : (z, θ) ∈ Work.Construction.Qd) =>
    Work.FTS.StrongEps.ClassCRHS.N0_split_open_aux hα hsmw z θ h
  have hmem : Work.Spaces.HkMem α 5
      (Work.Construction.N0 α (Work.Construction.Ftot α w) w) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 5 ht1.1
      (fun z hz θ hθ => (hsplit z θ ⟨hz, hθ.1, hθ.2⟩).symm)
  have hksq : Work.Spaces.HkSq α 5 (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
      = Work.Spaces.HkSq α 5
        (fun z θ => Work.FTS.Nonlin.N0fix α z θ
          + (Work.FTS.Nonlin.N03g α w z θ
            + (Work.FTS.Nonlin.N04aF α w z θ
              + (Work.FTS.Nonlin.N04bF α w z θ
                + (Work.FTS.Nonlin.N05aF α w z θ
                  + (Work.FTS.Nonlin.N05bF α w z θ
                    + Work.FTS.Nonlin.N06F α w z θ)))))) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 5
      (fun z θ hz hθ0 hθ1 => hsplit z θ ⟨hz, hθ0, hθ1⟩)
  have hXn : Work.Spaces.HkNorm α 5
      (Work.Construction.N0 α (Work.Construction.Ftot α w) w) ≤ c1 := by
    have h : Work.Spaces.HkNorm α 5
        (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
        = Work.Spaces.HkNorm α 5
          (fun z θ => Work.FTS.Nonlin.N0fix α z θ
            + (Work.FTS.Nonlin.N03g α w z θ
              + (Work.FTS.Nonlin.N04aF α w z θ
                + (Work.FTS.Nonlin.N04bF α w z θ
                  + (Work.FTS.Nonlin.N05aF α w z θ
                    + (Work.FTS.Nonlin.N05bF α w z θ
                      + Work.FTS.Nonlin.N06F α w z θ)))))) := by
      simp only [Work.Spaces.HkNorm, hksq]
    rw [h]
    exact hSum_le
  exact ⟨hmem, le_trans hXn (by linarith)⟩

/-- **The `N₀`-block at level 5** (the level-`5` analogue of `HkMemXnN0`,
`Submission/Work/FTS/StrongEps/ClassCRHS/HkMemXnN0.lean`).

Same route as `HkMemXnN5`: the level shift `H5.HkSq_succ_le` plus the Leibniz identities
`H5.Dz_mul_eqOn_Q0` / `H5.Dth_mul_eqOn_Q0` plus the level-four product rules
(`OpenPkg.prod_field`, `OpenPkg.wprod_field_winf`, `OpenPkg.angmul_field`), applied to the seven
monomials of `N0 α (F_*+w) w` (see `Work.Construction.N0`: the terms
`(3/(2α))s2·L12(F_*)·pth(F_*)`, `-c2m·L12(F_*)·Dz(F_*)`, `(1/α)·L12 g·g`,
`(3/(2α))s2·L12 g·pth F`, `-c2m·L12 g·Dz F`, `-c2m·L12(F_*)·Dz g`, where `F = F_* + w`).
There is no star and no elliptic data here: the atoms are `w`, `Dth w`, `Dz w`, the radial
functions `L12 w z`, `FK w`, and the fixed profiles `F_*`, `DthF_*`, `DzF_*`, `s2`, `c2m`, `hKer`,
`L12(F_*)`, together with the `(z/(1+z))`-weighted versions where the level-4 proof uses them.
`K` may depend on `α, C₀, B` but not on `w`.  The level-4 proof is
`HkMemXnN0` + `ClassCRHS/HkMemXnN0Rows.lean` + `HkMemXnN0Aux.lean`. -/
theorem HkMemXnN05 : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
    ∃ K : ℝ, 0 < K ∧ ∀ {w : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ B →
      Work.Spaces.HkMem α 5 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) ∧
      Work.Spaces.HkNorm α 5 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) ≤ K :=
  HkMemXnN05_of_atoms Atoms.L5AtomsW Atoms.L5L12W (Atoms.L5C2mL12W Atoms.L5L12W)
    Atoms.W5DthFstar Atoms.W5DzFstar Atoms.W5C2mL12Fstar Atoms.HkMem5N0fix

end Work.FTS.StrongEps.H5
