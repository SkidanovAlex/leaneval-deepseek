import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.H5.AngRad5.Engine5
import Submission.Work.FTS.StrongEps.H5.RadMem5
import Submission.Work.FTS.StrongEps.ClassCRHS.StarAtomsFK
import Submission.Work.FTS.StrongEps.H5.AngSlotBounds2
import Submission.Work.FTS.StrongEps.H5.RadProfiles
import Submission.Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt
import Submission.Work.FTS.StrongEps.ClassCRHS.StarAtomsScaled
import Submission.Work.FTS.StrongEps.H5.Atoms.DzIter_SR0_le5
import Submission.Work.FTS.StrongEps.H5.Atoms.DzIter_SR2_le5
import Submission.Work.FTS.StrongEps.H5.Atoms.DzIter_hKerSq_le5

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.Atoms

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.FTS.StrongEps.ClassCRHS

/-! ## Auxiliary facts

The five level-`5` atoms of this file are separable products `a(θ)·r(z)` of an angular
factor `a ∈ {SA0 α, SA1 α, 4α·SA0 α, 4α·SA1 α}` (with `SA0 = αΓ/c`, `SA1 = αD_θΓ/c`) and a
radial factor `r ∈ {SR0, SR2, hKer²}`.  The two derivatives of the engine used below are:

* the `D_θ`-iterates of a constant multiple of a `θ`-only function, and
* the two identifications of the `FK`-products with such separated products
  (`FK(F_*)·D_θF_* = (4α·SA1)(θ)·hKer²` and `FK(F_*)·F_* = (4α·SA0)(θ)·hKer²`). -/

/-- `D_θ`-iterates of a constant multiple of a `θ`-only function. -/
private lemma DthIter_rad_const_mul (c : ℝ) (i : ℕ) (g : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun _ (θ' : ℝ) => c * g θ') z θ
      = c * Work.Spaces.DthIter i (fun _ (θ' : ℝ) => g θ') z θ := by
  rw [Work.FTS.LocData.DthIter_rad_eq i (fun θ' => c * g θ') z θ,
    Work.Spaces.dthU_iter_const_mul i c g]
  show c * Work.Spaces.dthU^[i] g θ
    = c * Work.Spaces.DthIter i (fun _ (θ' : ℝ) => g θ') z θ
  rw [Work.FTS.LocData.DthIter_rad_eq i g z θ]

/-- A crude product comparison used to combine the five `ℋ⁵`-bounds into one constant. -/
private lemma shift_le {a S S4 c c' : ℝ} (ha : 0 ≤ a) (hS : 0 ≤ S) (hS4 : 0 ≤ S4)
    (hc : 0 ≤ c) (hcc : c ≤ c') : a * S * c ≤ a * (S + S4) * c' := by
  have hS' : 0 ≤ S + S4 := by linarith
  have h1 : S * c ≤ (S + S4) * c' := mul_le_mul (le_add_of_nonneg_right hS4) hcc hc hS'
  calc a * S * c = a * (S * c) := by ring
    _ ≤ a * ((S + S4) * c') := mul_le_mul_of_nonneg_left h1 ha
    _ = a * (S + S4) * c' := by ring

/-- `FK(F_*)·D_θF_* = (4α·SA1)(θ)·(hKer z)²`. -/
private lemma sep_FK_Dth {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
      = fun z θ => (4 * α * SA1 α θ) * (Work.Spaces.hKer z) ^ 2 := by
  funext z θ
  have hFK : Work.Construction.FK (Work.Construction.Fstar α) z = α * Work.FM.Fstar z := by
    rw [Work.FTS.Nonlin.FK_Fstar hα hα1, Work.FM.Fstar]
  have hpth : Work.Spaces.pth (Work.Construction.Fstar α) z θ
      = (α * Work.FM.Fstar z / Work.Spaces.c α)
        * deriv (fun t => Work.Spaces.Gam α t) θ := by
    rw [Work.Spaces.pth]
    rw [show (fun θ' : ℝ => Work.Construction.Fstar α z θ')
        = fun θ' : ℝ => (α * Work.FM.Fstar z / Work.Spaces.c α)
            * Work.Spaces.Gam α θ' from by
      funext θ'
      rw [Work.Construction.Fstar]
      ring]
    rw [Work.Spaces.deriv_const_mul']
  rw [Work.Spaces.Dth, hFK, hpth]
  simp only [Work.Spaces.dthU_apply, Work.Spaces.hKer_apply, SA1, Work.FM.Fstar]
  ring_nf

/-- `FK(F_*)·F_* = (4α·SA0)(θ)·(hKer z)²`. -/
private lemma sep_FK_Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ)
      = fun z θ => (4 * α * SA0 α θ) * (Work.Spaces.hKer z) ^ 2 := by
  funext z θ
  have hFK : Work.Construction.FK (Work.Construction.Fstar α) z = α * Work.FM.Fstar z := by
    rw [Work.FTS.Nonlin.FK_Fstar hα hα1, Work.FM.Fstar]
  rw [hFK]
  simp only [SA0, Work.Construction.Fstar, Work.Spaces.hKer_apply, Work.FM.Fstar]
  ring_nf

theorem FixedAtoms5 (hE : Work.FTS.StrongEps.H5.AngRad5.AngRadEngine5) :
    ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∃ C : ℝ, 0 < C ∧
      Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ≤ C ∧
      Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ C ∧
      Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ≤ C ∧
      Work.FTS.VocabO.HQo α 5 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ C ∧
      Work.FTS.VocabO.HQo α 5 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ) ≤ C := by
  obtain ⟨Ceng, hCengpos, hEng⟩ := hE
  intro α hαI
  obtain ⟨hα, hα1⟩ := Set.mem_Ioc.mp hαI
  -- ## the angular slot data of `SA0 = αΓ/c` and `SA1 = α D_θΓ/c`
  obtain ⟨B0, B1, hB0pos, hB1pos, hSA0bd, hSA0sl, hSA1bd, hSA1sl, -, -⟩ :=
    Work.FTS.StrongEps.H5.AngSlotBounds2 α hα hα1
  -- ## the angular mass of the sharp majorant `SGmj α = Γ(α + sin 2θ)`
  obtain ⟨M, hMpos, hMmass⟩ := Work.FTS.StrongEps.ClassCRHS.SGmj_mass
  obtain ⟨hMint, hMbd⟩ := hMmass α hα hα1
  have hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ SGmj α θ := fun θ hθ => SGmj_nonneg hα hθ
  -- ## the radial level-`5` data of `SR0`, `SR2` and `hKer²`
  obtain ⟨Cp0, hCp0pos, hCp0⟩ := Work.FTS.StrongEps.H5.Atoms.DzIter_SR0_le5
  obtain ⟨Cp2, hCp2pos, hCp2⟩ := Work.FTS.StrongEps.H5.Atoms.DzIter_SR2_le5
  obtain ⟨Cphk, hCphkpos, hCphk⟩ := Work.FTS.StrongEps.H5.Atoms.DzIter_hKerSq_le5
  have hSR0sm : ∀ n : ℕ, ContDiffOn ℝ n SR0 (Set.Ioi 0) := contDiffOn_SR0
  have hSR2sm : ∀ n : ℕ, ContDiffOn ℝ n SR2 (Set.Ioi 0) := contDiffOn_SR2
  have hhksm : ∀ n : ℕ, ContDiffOn ℝ n (fun z => (Work.Spaces.hKer z) ^ 2) (Set.Ioi 0) :=
    fun n => (Work.FTS.Nonlinear.Open.row23_contDiffOn_hKer n).pow 2
  obtain ⟨Cr0, hCr0pos, hCr0⟩ :=
    Work.FTS.StrongEps.H5.RadMem5 (r := SR0) hCp0pos hSR0sm hCp0
  obtain ⟨Cr2, hCr2pos, hCr2⟩ :=
    Work.FTS.StrongEps.H5.RadMem5 (r := SR2) hCp2pos hSR2sm hCp2
  obtain ⟨Crhk, hCrhkpos, hCrhk⟩ := Work.FTS.StrongEps.H5.RadMem5
    (r := fun z => (Work.Spaces.hKer z) ^ 2) hCphkpos hhksm hCphk
  have hSR0open : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => SR0 z) :=
    Work.FTS.Nonlinear.Open.row23_smoothOpen_radial hSR0sm
  have hSR2open : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => SR2 z) :=
    Work.FTS.Nonlinear.Open.row23_smoothOpen_radial hSR2sm
  have hHksm_open : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => (Work.Spaces.hKer z) ^ 2) :=
    Work.FTS.Nonlinear.Open.row23_smoothOpen_radial hhksm
  -- ## the `4α`-scaled angular factors of the two `FK`-products
  have h4αnn : (0 : ℝ) ≤ 4 * α := by positivity
  have hsm40 : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => 4 * α * SA0 α θ) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (4 * α) (smoothOpen_SA0 α)
  have hsm41 : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => 4 * α * SA1 α θ) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (4 * α) (smoothOpen_SA1 α)
  have hF0bd : ∀ θ ∈ Work.Spaces.Iθ, |4 * α * SA0 α θ| ≤ 4 * B0 := by
    intro θ hθ
    rw [abs_mul, abs_of_nonneg h4αnn]
    calc 4 * α * |SA0 α θ| ≤ 4 * α * B0 :=
          mul_le_mul_of_nonneg_left (hSA0bd θ hθ) h4αnn
      _ = 4 * (α * B0) := by ring
      _ ≤ 4 * B0 := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 4)
          exact mul_le_of_le_one_left hB0pos.le hα1
  have hF0sl : ∀ i : ℕ, 1 ≤ i → i ≤ 5 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => 4 * α * SA0 α θ') 0 θ|
        ≤ (4 * B1) * SGmj α θ := by
    intro i hi1 hi5 θ hθ
    rw [DthIter_rad_const_mul (4 * α) i (fun θ' => SA0 α θ') 0 θ, abs_mul,
      abs_of_nonneg h4αnn]
    calc 4 * α * |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => SA0 α θ') 0 θ|
        ≤ 4 * α * (B1 * SGmj α θ) :=
          mul_le_mul_of_nonneg_left (hSA0sl i hi1 hi5 θ hθ) h4αnn
      _ = 4 * (α * (B1 * SGmj α θ)) := by ring
      _ ≤ 4 * (B1 * SGmj α θ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 4)
          exact mul_le_of_le_one_left (mul_nonneg hB1pos.le (hGnn θ hθ)) hα1
      _ = (4 * B1) * SGmj α θ := by ring
  have hF1bd : ∀ θ ∈ Work.Spaces.Iθ, |4 * α * SA1 α θ| ≤ 4 * B0 := by
    intro θ hθ
    rw [abs_mul, abs_of_nonneg h4αnn]
    calc 4 * α * |SA1 α θ| ≤ 4 * α * B0 :=
          mul_le_mul_of_nonneg_left (hSA1bd θ hθ) h4αnn
      _ = 4 * (α * B0) := by ring
      _ ≤ 4 * B0 := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 4)
          exact mul_le_of_le_one_left hB0pos.le hα1
  have hF1sl : ∀ i : ℕ, 1 ≤ i → i ≤ 5 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => 4 * α * SA1 α θ') 0 θ|
        ≤ (4 * B1) * SGmj α θ := by
    intro i hi1 hi5 θ hθ
    rw [DthIter_rad_const_mul (4 * α) i (fun θ' => SA1 α θ') 0 θ, abs_mul,
      abs_of_nonneg h4αnn]
    calc 4 * α * |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => SA1 α θ') 0 θ|
        ≤ 4 * α * (B1 * SGmj α θ) :=
          mul_le_mul_of_nonneg_left (hSA1sl i hi1 hi5 θ hθ) h4αnn
      _ = 4 * (α * (B1 * SGmj α θ)) := by ring
      _ ≤ 4 * (B1 * SGmj α θ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 4)
          exact mul_le_of_le_one_left (mul_nonneg hB1pos.le (hGnn θ hθ)) hα1
      _ = (4 * B1) * SGmj α θ := by ring
  -- ## the five applications of the angular `×` radial engine
  have hK0 := hEng hα hα1 (a := SA0 α) (r := SR0) (G := SGmj α)
    (B0 := B0) (B1 := B1) (M := M) (Crad := Cr0 * Cp0)
    (smoothOpen_SA0 α) hSR0open hGnn hMint hB0pos.le hB1pos.le hMpos.le
    (mul_pos hCr0pos hCp0pos).le hSA0bd hSA0sl hMbd (hCr0 α hαI).1 (hCr0 α hαI).2
  have hK1 := hEng hα hα1 (a := SA1 α) (r := SR0) (G := SGmj α)
    (B0 := B0) (B1 := B1) (M := M) (Crad := Cr0 * Cp0)
    (smoothOpen_SA1 α) hSR0open hGnn hMint hB0pos.le hB1pos.le hMpos.le
    (mul_pos hCr0pos hCp0pos).le hSA1bd hSA1sl hMbd (hCr0 α hαI).1 (hCr0 α hαI).2
  have hK2 := hEng hα hα1 (a := SA0 α) (r := SR2) (G := SGmj α)
    (B0 := B0) (B1 := B1) (M := M) (Crad := Cr2 * Cp2)
    (smoothOpen_SA0 α) hSR2open hGnn hMint hB0pos.le hB1pos.le hMpos.le
    (mul_pos hCr2pos hCp2pos).le hSA0bd hSA0sl hMbd (hCr2 α hαI).1 (hCr2 α hαI).2
  have hK3 := hEng hα hα1 (a := fun θ => 4 * α * SA1 α θ)
    (r := fun z => (Work.Spaces.hKer z) ^ 2) (G := SGmj α)
    (B0 := 4 * B0) (B1 := 4 * B1) (M := M) (Crad := Crhk * Cphk)
    hsm41 hHksm_open hGnn hMint (by positivity) (by positivity) hMpos.le
    (mul_pos hCrhkpos hCphkpos).le hF1bd hF1sl hMbd (hCrhk α hαI).1 (hCrhk α hαI).2
  have hK4 := hEng hα hα1 (a := fun θ => 4 * α * SA0 α θ)
    (r := fun z => (Work.Spaces.hKer z) ^ 2) (G := SGmj α)
    (B0 := 4 * B0) (B1 := 4 * B1) (M := M) (Crad := Crhk * Cphk)
    hsm40 hHksm_open hGnn hMint (by positivity) (by positivity) hMpos.le
    (mul_pos hCrhkpos hCphkpos).le hF0bd hF0sl hMbd (hCrhk α hαI).1 (hCrhk α hαI).2
  -- ## the packaged constant
  set S : ℝ := Real.sqrt (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M) with hSdef
  set S4 : ℝ := Real.sqrt ((4 * B0) ^ 2 * 10 ^ 4 + 5 * (4 * B1) ^ 2 * M) with hS4def
  set K : ℝ := Ceng * (S + S4) * (Cr0 * Cp0 + Cr2 * Cp2 + Crhk * Cphk) + 1 with hKdef
  have hSnn : 0 ≤ S := by rw [hSdef]; exact Real.sqrt_nonneg _
  have hS4nn : 0 ≤ S4 := by rw [hS4def]; exact Real.sqrt_nonneg _
  have hKpos : 0 < K := by
    have h1 : 0 ≤ Cr0 * Cp0 := (mul_pos hCr0pos hCp0pos).le
    have h2 : 0 ≤ Cr2 * Cp2 := (mul_pos hCr2pos hCp2pos).le
    have h3 : 0 ≤ Crhk * Cphk := (mul_pos hCrhkpos hCphkpos).le
    have hprod : 0 ≤ Ceng * (S + S4) * (Cr0 * Cp0 + Cr2 * Cp2 + Crhk * Cphk) :=
      mul_nonneg (mul_nonneg hCengpos.le (by linarith)) (by linarith)
    rw [hKdef]
    linarith
  have e0 : Ceng * S * (Cr0 * Cp0) ≤ K := by
    have h := shift_le (a := Ceng) (S := S) (S4 := S4) (c := Cr0 * Cp0)
      (c' := Cr0 * Cp0 + Cr2 * Cp2 + Crhk * Cphk) hCengpos.le hSnn hS4nn
      (mul_pos hCr0pos hCp0pos).le (by linarith [(mul_pos hCr2pos hCp2pos).le,
        (mul_pos hCrhkpos hCphkpos).le])
    rw [hKdef]
    linarith
  have e2 : Ceng * S * (Cr2 * Cp2) ≤ K := by
    have h := shift_le (a := Ceng) (S := S) (S4 := S4) (c := Cr2 * Cp2)
      (c' := Cr0 * Cp0 + Cr2 * Cp2 + Crhk * Cphk) hCengpos.le hSnn hS4nn
      (mul_pos hCr2pos hCp2pos).le (by linarith [(mul_pos hCr0pos hCp0pos).le,
        (mul_pos hCrhkpos hCphkpos).le])
    rw [hKdef]
    linarith
  have e3 : Ceng * S4 * (Crhk * Cphk) ≤ K := by
    have h := shift_le (a := Ceng) (S := S4) (S4 := S) (c := Crhk * Cphk)
      (c' := Cr0 * Cp0 + Cr2 * Cp2 + Crhk * Cphk) hCengpos.le hS4nn hSnn
      (mul_pos hCrhkpos hCphkpos).le (by linarith [(mul_pos hCr0pos hCp0pos).le,
        (mul_pos hCr2pos hCp2pos).le])
    have hswap : S4 + S = S + S4 := by ring
    rw [hswap] at h
    rw [hKdef]
    linarith
  -- ## the five norm bounds with the single constant `K`
  have hK0b : Work.Spaces.HkNorm α 5 (fun z θ => SA0 α θ * SR0 z) ≤ Ceng * S * (Cr0 * Cp0) := by
    rw [hSdef]; exact hK0.2
  have hK1b : Work.Spaces.HkNorm α 5 (fun z θ => SA1 α θ * SR0 z) ≤ Ceng * S * (Cr0 * Cp0) := by
    rw [hSdef]; exact hK1.2
  have hK2b : Work.Spaces.HkNorm α 5 (fun z θ => SA0 α θ * SR2 z) ≤ Ceng * S * (Cr2 * Cp2) := by
    rw [hSdef]; exact hK2.2
  have hK3b : Work.Spaces.HkNorm α 5
      (fun z θ => (4 * α * SA1 α θ) * (Work.Spaces.hKer z) ^ 2)
        ≤ Ceng * S4 * (Crhk * Cphk) := by
    rw [hS4def]; exact hK3.2
  have hK4b : Work.Spaces.HkNorm α 5
      (fun z θ => (4 * α * SA0 α θ) * (Work.Spaces.hKer z) ^ 2)
        ≤ Ceng * S4 * (Crhk * Cphk) := by
    rw [hS4def]; exact hK4.2
  -- ## the transfers to the literal atoms
  have hq0 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      SA0 α θ * SR0 z = z / (1 + z) * Work.Construction.Fstar α z θ :=
    fun z θ hz _ _ => agree0 hα hα1 hz
  have hq1 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      SA1 α θ * SR0 z
        = z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ :=
    fun z θ hz _ _ => agree1 hα hα1 hz
  have hq2 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      SA0 α θ * SR2 z
        = z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ :=
    fun z θ hz _ _ => agree2 hα hα1 hz
  have hs0 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => SA0 α θ * SR0 z) :=
    Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad (smoothOpen_SA0 α) hSR0open
  have hs1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => SA1 α θ * SR0 z) :=
    Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad (smoothOpen_SA1 α) hSR0open
  have hs2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => SA0 α θ * SR2 z) :=
    Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad (smoothOpen_SA0 α) hSR2open
  have hs3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (4 * α * SA1 α θ) * (Work.Spaces.hKer z) ^ 2) :=
    Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad hsm41 hHksm_open
  have hs4 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (4 * α * SA0 α θ) * (Work.Spaces.hKer z) ^ 2) :=
    Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad hsm40 hHksm_open
  -- ## atom 0: `z/(1+z)·F_* = SA0(θ)·SR0(z)`
  have hQ0 : Work.FTS.VocabO.HQo α 5
      (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) :=
    ⟨hs0.congr hq0, Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 5 hK0.1
      (fun z hz θ hθ => hq0 z θ hz hθ.1 hθ.2)⟩
  have hb0 : Work.Spaces.HkNorm α 5
      (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ≤ K := by
    show Real.sqrt (Work.Spaces.HkSq α 5
      (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ)) ≤ K
    rw [← Work.FTS.EllipticEst.HkSq_congr_open α 5 hq0]
    exact le_trans hK0b e0
  -- ## atom 1: `z/(1+z)·D_θF_* = SA1(θ)·SR0(z)`
  have hQ1 : Work.FTS.VocabO.HQo α 5
      (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) :=
    ⟨hs1.congr hq1, Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 5 hK1.1
      (fun z hz θ hθ => hq1 z θ hz hθ.1 hθ.2)⟩
  have hb1 : Work.Spaces.HkNorm α 5
      (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ K := by
    show Real.sqrt (Work.Spaces.HkSq α 5
      (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)) ≤ K
    rw [← Work.FTS.EllipticEst.HkSq_congr_open α 5 hq1]
    exact le_trans hK1b e0
  -- ## atom 2: `z/(1+z)·D_zF_* = SA0(θ)·SR2(z)`
  have hQ2 : Work.FTS.VocabO.HQo α 5
      (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) :=
    ⟨hs2.congr hq2, Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 5 hK2.1
      (fun z hz θ hθ => hq2 z θ hz hθ.1 hθ.2)⟩
  have hb2 : Work.Spaces.HkNorm α 5
      (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ≤ K := by
    show Real.sqrt (Work.Spaces.HkSq α 5
      (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)) ≤ K
    rw [← Work.FTS.EllipticEst.HkSq_congr_open α 5 hq2]
    exact le_trans hK2b e2
  -- ## atom 3: `FK(F_*)·D_θF_*`
  have hQ3 : Work.FTS.VocabO.HQo α 5
      (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) := by
    rw [sep_FK_Dth hα hα1]
    exact ⟨hs3, hK3.1⟩
  have hb3 : Work.Spaces.HkNorm α 5
      (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ K := by
    rw [sep_FK_Dth hα hα1]
    exact le_trans hK3b e3
  -- ## atom 4: `FK(F_*)·F_*`
  have hQ4 : Work.FTS.VocabO.HQo α 5
      (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ) := by
    rw [sep_FK_Fstar hα hα1]
    exact ⟨hs4, hK4.1⟩
  have hb4 : Work.Spaces.HkNorm α 5
      (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ) ≤ K := by
    rw [sep_FK_Fstar hα hα1]
    exact le_trans hK4b e3
  exact ⟨K, hKpos, hQ0, hb0, hQ1, hb1, hQ2, hb2, hQ3, hb3, hQ4, hb4⟩

end Work.FTS.StrongEps.H5.Atoms
