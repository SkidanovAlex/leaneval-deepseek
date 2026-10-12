import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.oneBodyKineticHalfAux
import Submission.Work.BoseFixB1B.sbKinCube_marginal_integrable
import Submission.Work.BoseFixB1C.symACubeTailProved
import Submission.Work.BoseFixB1S.corrInputCube
import Submission.Work.BoseFixB1S.cruxUnprojCube
import Submission.Work.BoseFixB1S.symACubeFsParams
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1C.kineticHalfCube_le_mainWord` — the decision-(B) `hmain`, `sorry`-free

**Why this file exists**: it is a *verbatim* re-run of
`Work.BoseFixB1B.kineticHalfCube_le_mainWord` (`Submission/Work/BoseFixB1B/kineticHalfCube_le_mainWord.lean`,
459 lines) with its single `sorry`-carrying input `Work.BoseFixB1B.symACube_tail_scalar` replaced by
the **PROVED**, axiom-clean `Work.BoseFixB1C.symACube_tail_scalar`
(`Submission/Work/BoseFixB1C/symACubeTailProved.lean`).  Everything else is unchanged: the triangle
of inputs `Work.BoseFixB1S.corrInputCube`, `Work.BoseFixB1S.symACubeFsParams`,
`Work.BoseFixB1S.cruxUnprojCube`, `Core.spectral_chain`, `Core.oneBody_assembly` and the whole
bookkeeping are the originals.  Consequently this declaration is axiom-clean, and the chain
`kineticHalfCube_le_mainWord → oneBodyKineticHalfCube_of_mainWord → kineticHalfCube_of_oneBody →
slidingBCube_of_oneBody` yields `Work.BoseFixB1C.SlidingBCube_holds` with no `sorryAx`
(`Submission/Work/BoseFixB1C/slidingBCubeHolds.lean`).

The original statement follows (unchanged).

The **cube-windowed one-body kinetic half against the frozen (ball-windowed) main word**: the
`N = 1` spectral half of FS `eq:BSsliding2` at the single cube cutoff `chiSmallB`, stated against
`Work.BoseKinLoc.mainWord` (whose window is the *ball* bump `chiScale ℓ` at the ℓ-scale) plus the
anchored gap payment `(bValue/(2ℓ²))·cnPlus ℓ φ`.

This is the `hmain` input of `Work.BoseFixB1B.oneBodyKineticHalfCube_of_mainWord` (which turns it
into `OneBodyKineticHalfCube`, hence `KineticHalfCube`, hence `SlidingBCube`).

## The proof (the cube re-run of `Work.BoseFixB1S.kineticCruxParsed_of_inputs`)

Write `ℓ = sideAt μ (a v)`, `d`, `s`, `eT`, `M`, `cc = sbCut μ (a v)`, `η = slotFun1 φ`,
`hf = η − ⍝_{acube ℓ}η`, `g = χ_ℓ·hf`, `Q₂ = ∫_{acube ℓ}hf²`, `w q = ‖kinFT g q‖²`.  Then

* `∫_u cubeSpectral v μ φ u = (2π)⁻³ ∫_u bsW (fsKinCoeff cc) (χ_{B(u)}(η − ⍝_{B(u)}η))`
  (`tBwordKinInd_cube_eq_bsW`, pointwise in `u`);
* the intersection-mean correction `Work.BoseFixB1S.corrInputCube` (at `chiSmallB`) costs
  `(bValue/(4ℓ²))·Q₂`;
* `χ_{B(u)}·hf = cubeWin M (ℓd) u · g`, so the shifted family form is
  `bsFamilyFormUnprojCube M (ℓd) (fsKinCoeff cc) g` (`chiSmallB_eq_chiScale_mul_cubeWin`,
  `twoPi_inv_bsW_cubeWin_eq_bsOneBodyUnprojCube`);
* `Work.BoseFixB1S.cruxUnprojCube` bounds that family form by the *cube* symbol integral
  `(2π)⁻³∫_q symACube M (ℓd) (fsKinCoeff cc) q·w q`;
* `Work.BoseFixB1S.symACubeFsParams` is the pointwise two-cut comparison at FS's parameters,
  whose two mixture rows are *literally* the rows of `mainWord`, and whose constant term is
  `(ℓd)⁻²·symACube M 1 (fsKinCoeff (2s)⁻¹) 0`; integrated against `w` and combined with
  Plancherel, the mixture rows give `mainWord ℓ d s eT 0 η` (`mainWord_unproj_eq`), and the
  constant row costs `(bValue/(4ℓ²))·Q₂` — this is exactly the delegated scalar
  `Work.BoseFixB1C.symACube_tail_scalar` (`β·chiSupAbs² ≤ (bValue/4)·d²`, whose proof is the
  polynomial decay `β ≲ (2s)^{86}` of the cosine bump's symbol, the cube twin of
  `Work.BoseFixB1.Core.symA_zero_decay_pow`) together with `∫g² ≤ chiSupAbs²·Q₂`;
* `cnPlus ℓ φ = Q₂` (`Work.BoseFixB1.cnPlus_one_eq`), and `2·(bValue/(4ℓ²)) = bValue/(2ℓ²)`.

The bookkeeping is the frozen one of `Work.BoseFixB1.KH.kineticHalf_le_mainWord`
(`Work.BoseFixB1S.kineticCruxParsed_of_inputs`) with `chiB ↦ chiSmallB`, `symA ↦ symACube M`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal ContDiff

namespace Work.BoseFixB1C

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X1" => Submission.BoseGases.X 1

open _root_.BoseGases Submission.BoseGases

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## The target -/

theorem kineticHalfCube_le_mainWord {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ φ : Submission.BoseGases.X 1 → ℝ, ContDiff ℝ (⊤ : ENat) φ →
        (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1B.cubeSpectral v μ φ u)
          ≤ Work.BoseKinLoc.mainWord (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT 0
                (Work.BSKinetic.slotFun1 φ)
            + (Work.BoseBox.bValue / (2 * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 2))
                * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) φ := by
  -- the three inputs: cube mean-mismatch, cube two-cut symbol comparison, cube tail
  obtain ⟨ε₁, hε₁, hC⟩ := Work.BoseFixB1S.corrInputCube (v := v) h
  obtain ⟨ε₂, hε₂, hMix⟩ := Work.BoseFixB1S.symACubeFsParams (v := v)
  obtain ⟨ε₃, hε₃, hT⟩ := Work.BoseFixB1C.symACube_tail_scalar (v := v)
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃), ?_⟩
  intro μ hAdm φ hφ
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdm₂ : Work.BoseBoxFix.Adm v ε₂ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hAdm₃ : Work.BoseBoxFix.Adm v ε₃ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_right _ _))
  have hℓpos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hdpos : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
    Work.BoseFixB1.adm_d_pos hAdm
  have hspos : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s :=
    Work.BoseFixB1.adm_s_pos hAdm
  obtain ⟨heT0, heT1⟩ := Work.BoseFixB1.adm_eT_bounds hAdm
  -- abbreviations
  set ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hℓdef
  set dd : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hddef
  set ss : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s with hsdef
  set ee : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT with heedef
  set cc : ℝ := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) with hccdef
  set MM : ℕ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M with hMMdef
  set η : E3 → ℝ := Work.BSKinetic.slotFun1 φ with hηdef
  set hf : E3 → ℝ :=
    fun z : E3 => η z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, η z' with hfdef
  set g : E3 → ℝ := fun z : E3 => Submission.BoseGases.chiScale ℓ z * hf z with hgdef
  set w : E3 → ℝ := fun q : E3 => ‖Submission.BoseGases.kinFT (fun z : E3 => (g z : ℂ)) q‖ ^ 2
    with hwdef
  set Q₂ : ℝ := ∫ z in Submission.BoseGases.acube ℓ, (hf z) ^ 2 with hQdef
  have hℓ : 0 < ℓ := by rw [hℓdef]; exact hℓpos
  have hd : 0 < dd := by rw [hddef]; exact hdpos
  have hs : 0 < ss := by rw [hsdef]; exact hspos
  have hee0 : 0 ≤ ee := by rw [heedef]; exact heT0
  have hee1 : ee ≤ 1 := by rw [heedef]; exact heT1
  have hcc0 : 0 ≤ cc := by
    rw [hccdef, Work.BoseFixB1.sbCut]
    exact inv_nonneg.mpr (by positivity)
  have hM1 : 1 ≤ MM := by
    rw [hMMdef]
    show 1 ≤ Work.BoseBox.mValue
    norm_num [Work.BoseBox.mValue]
  have hηsm : ContDiff ℝ (⊤ : ENat) η := by
    rw [hηdef]
    exact hφ.comp (by fun_prop)
  have hφη : (fun x : X1 => η (x 0)) = φ := by
    funext x
    have hx : (fun _ : Fin 1 => x 0) = x := by funext j; fin_cases j; rfl
    rw [hηdef, Work.BSKinetic.slotFun1, hx]
  have hhfsm : ContDiff ℝ (⊤ : ENat) hf := by
    rw [hfdef]
    exact hηsm.sub contDiff_const
  have hgsm : ContDiff ℝ (⊤ : ENat) g := by
    rw [hgdef]
    exact (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).mul hhfsm
  have hgcs : HasCompactSupport g := by
    rw [hgdef]
    exact (Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)).mul_right
  have hwnn : ∀ q : E3, 0 ≤ w q := by intro q; rw [hwdef]; positivity
  -- ## (0) the left side, pointwise: the cube-windowed `bsW` integral
  have hLHS : (∫ u : E3, Work.BoseFixB1B.cubeSpectral v μ φ u)
      = ∫ u : E3, ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW
          (Submission.BoseGases.fsKinCoeff cc)
          (fun z : E3 => Submission.BoseGases.chiSmallB MM ℓ dd u z *
            (η z - (1 / Work.SmallBoxSliding.boxMass ℓ dd u) *
              ∫ z' in Submission.BoseGases.dlBox ℓ dd u, η z')) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have h0 := Work.BoseFixB1S.tBwordKinInd_cube_eq_bsW (M := MM) (c := cc) hM1 hℓ hd u φ
    simpa only [Work.BoseFixB1B.cubeSpectral, Work.BoseFixB1.bSide, Work.BoseFixB1.bD,
      Work.BoseFixB1.bM, Work.BoseFixB1.bA, Work.BoseFixB1.bV, ← hℓdef, ← hddef, ← hMMdef,
      ← hccdef, ← hφη] using h0
  -- ## (1) the intersection-mean correction
  have step1 : ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ u : E3, Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff cc)
          (fun z : E3 => Submission.BoseGases.chiSmallB MM ℓ dd u z *
            (η z - (1 / Work.SmallBoxSliding.boxMass ℓ dd u) *
              ∫ z' in Submission.BoseGases.dlBox ℓ dd u, η z')))
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ u : E3, Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff cc)
            (fun z : E3 => Submission.BoseGases.chiSmallB MM ℓ dd u z * hf z))
        + (Work.BoseBox.bValue / (4 * ℓ ^ 2)) * Q₂ := by
    have h0 := hC μ hAdm₁ η hηsm
    simpa only [← hℓdef, ← hddef, ← hMMdef, ← hccdef, hfdef, hQdef, one_div] using h0
  -- ## (2) the middle term is the shifted cube family form of `g`
  have step2 : ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ u : E3, Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff cc)
          (fun z : E3 => Submission.BoseGases.chiSmallB MM ℓ dd u z * hf z))
      = Work.BoseFixB1S.bsFamilyFormUnprojCube MM (ℓ * dd) (Submission.BoseGases.fsKinCoeff cc)
          g := by
    rw [Work.BoseFixB1S.bsFamilyFormUnprojCube, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff cc)
        (fun z : E3 => Submission.BoseGases.chiSmallB MM ℓ dd u z * hf z)
      = Work.BoseFixB1S.bsOneBodyUnprojCube MM (ℓ * dd) (Submission.BoseGases.fsKinCoeff cc)
          u g
    have hfun : (fun z : E3 => Submission.BoseGases.chiSmallB MM ℓ dd u z * hf z)
        = fun z : E3 => Work.BoseFixB1S.cubeWin MM (ℓ * dd) u z * g z := by
      funext z
      rw [Work.BoseFixB1S.chiSmallB_eq_chiScale_mul_cubeWin]
      simp only [hgdef]
      ring
    rw [hfun]
    exact Work.BoseFixB1S.twoPi_inv_bsW_cubeWin_eq_bsOneBodyUnprojCube MM (ℓ * dd)
      (Submission.BoseGases.fsKinCoeff cc) u g
  -- ## (3) the cube unprojection inequality
  have step3 : Work.BoseFixB1S.bsFamilyFormUnprojCube MM (ℓ * dd)
        (Submission.BoseGases.fsKinCoeff cc) g
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ q : E3, Work.BoseFixB1S.symACube MM (ℓ * dd) (Submission.BoseGases.fsKinCoeff cc)
            q * w q :=
    Work.BoseFixB1S.cruxUnprojCube MM hM1 (mul_pos hℓ hd) hcc0 hgsm hgcs
  -- ## (4) the pointwise two-cut comparison
  have hmix_nn : ∀ q : E3, 0 ≤ ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹)
      ‖q‖ + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖) := by
    intro q
    have h1 : 0 ≤ Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖ :=
      Submission.BoseGases.fsKinCoeff_nonneg _ _
    have h2 : 0 ≤ Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖ :=
      Submission.BoseGases.fsKinCoeff_nonneg _ _
    nlinarith [hee0, hee1, h1, h2]
  have htail_nn : 0 ≤ ((ℓ * dd) ^ 2)⁻¹ * Work.BoseFixB1S.symACube MM 1
      (Submission.BoseGases.fsKinCoeff ((2 * ss)⁻¹)) 0 := by
    refine mul_nonneg (by positivity) ?_
    rw [Work.BoseFixB1S.symACube]
    exact mul_nonneg (by positivity) (MeasureTheory.integral_nonneg fun p =>
      mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg _ _) (sq_nonneg _))
  have hsym_pt : ∀ q : E3,
      Work.BoseFixB1S.symACube MM (ℓ * dd) (Submission.BoseGases.fsKinCoeff cc) q * w q
        ≤ (((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
              + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖)
            + ((ℓ * dd) ^ 2)⁻¹ * Work.BoseFixB1S.symACube MM 1
                (Submission.BoseGases.fsKinCoeff ((2 * ss)⁻¹)) 0) * w q := by
    intro q
    refine mul_le_mul_of_nonneg_right ?_ (hwnn q)
    have hm := hMix μ hAdm₂ q
    simpa only [← hℓdef, ← hddef, ← hsdef, ← heedef, ← hccdef, ← hMMdef] using hm
  -- integrability of the dominating integrand
  have hbig_int : MeasureTheory.Integrable (fun q : E3 =>
      (((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
          + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖)
        + ((ℓ * dd) ^ 2)⁻¹ * Work.BoseFixB1S.symACube MM 1
            (Submission.BoseGases.fsKinCoeff ((2 * ss)⁻¹)) 0) * w q) := by
    have h0 := Work.BoseFixB1.Core.integrable_mixConst_mul_kinFT_sq
      (c₁ := (2 * (ss * ℓ))⁻¹) (c₂ := (2 * (dd * ss * ℓ))⁻¹) (ε := ee)
      (p := ((ℓ * dd) ^ 2)⁻¹ * Work.BoseFixB1S.symACube MM 1
        (Submission.BoseGases.fsKinCoeff ((2 * ss)⁻¹)) 0)
      hgsm hgcs
    simpa only [hwdef, Work.BSKinetic.Decomp.bsPsi, ← hgdef] using h0
  have hsym_int : ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ q : E3, Work.BoseFixB1S.symACube MM (ℓ * dd) (Submission.BoseGases.fsKinCoeff cc)
          q * w q)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ q : E3, (((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
              + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖)
            + ((ℓ * dd) ^ 2)⁻¹ * Work.BoseFixB1S.symACube MM 1
                (Submission.BoseGases.fsKinCoeff ((2 * ss)⁻¹)) 0) * w q) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    by_cases hint : MeasureTheory.Integrable (fun q : E3 =>
        Work.BoseFixB1S.symACube MM (ℓ * dd) (Submission.BoseGases.fsKinCoeff cc) q * w q)
    · exact MeasureTheory.integral_mono_ae hint hbig_int (Filter.Eventually.of_forall hsym_pt)
    · rw [MeasureTheory.integral_undef hint]
      refine MeasureTheory.integral_nonneg fun q => ?_
      exact mul_nonneg (add_nonneg (hmix_nn q) htail_nn) (hwnn q)
  -- ## (5) splitting the integral and Plancherel
  have hmixw_int : MeasureTheory.Integrable (fun q : E3 =>
      ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
        + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖) * w q) := by
    have h0 := Work.BoseFixB1.Core.integrable_mixConst_mul_kinFT_sq
      (c₁ := (2 * (ss * ℓ))⁻¹) (c₂ := (2 * (dd * ss * ℓ))⁻¹) (ε := ee) (p := 0) hgsm hgcs
    have h0' : MeasureTheory.Integrable (fun q : E3 =>
        ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
          + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖ + 0) * w q) := by
      simpa only [hwdef, Work.BSKinetic.Decomp.bsPsi, ← hgdef] using h0
    refine h0'.congr (Filter.Eventually.of_forall fun q => ?_)
    ring
  have hw_int : MeasureTheory.Integrable w := by
    have h0 := Work.BSKinetic.integrable_kinFT_sq g hgsm hgcs
    simpa only [hwdef, Work.BSKinetic.Decomp.bsPsi, ← hgdef] using h0
  have hsplit' : ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ q : E3, (((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
            + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖)
          + ((ℓ * dd) ^ 2)⁻¹ * Work.BoseFixB1S.symACube MM 1
              (Submission.BoseGases.fsKinCoeff ((2 * ss)⁻¹)) 0) * w q)
      = ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ q : E3, ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
              + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖) * w q)
        + (((ℓ * dd) ^ 2)⁻¹ * Work.BoseFixB1S.symACube MM 1
              (Submission.BoseGases.fsKinCoeff ((2 * ss)⁻¹)) 0)
            * (((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, w q)) := by
    have hfun : (fun q : E3 => (((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹)
            ‖q‖ + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖)
          + ((ℓ * dd) ^ 2)⁻¹ * Work.BoseFixB1S.symACube MM 1
              (Submission.BoseGases.fsKinCoeff ((2 * ss)⁻¹)) 0) * w q)
        = fun q : E3 => ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
            + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖) * w q
          + (((ℓ * dd) ^ 2)⁻¹ * Work.BoseFixB1S.symACube MM 1
              (Submission.BoseGases.fsKinCoeff ((2 * ss)⁻¹)) 0) * w q := by
      funext q; ring
    rw [hfun, MeasureTheory.integral_add hmixw_int (hw_int.const_mul _),
      MeasureTheory.integral_const_mul]
    ring
  have hpl : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, w q) = ∫ z : E3, (g z) ^ 2 := by
    rw [hwdef]
    exact Work.BSKinetic.plancherel_pconv g hgsm hgcs
  -- ## (6) the tail payment
  have hIndInt : MeasureTheory.Integrable (fun z : E3 =>
      (Submission.BoseGases.acube ℓ).indicator (fun z : E3 => (hf z) ^ 2) z) := by
    have hcompact : IsCompact (Submission.BoseGases.acube ℓ) :=
      Work.UBBInputs8.A.isCompact_acube ℓ
    exact (MeasureTheory.integrable_indicator_iff hcompact.measurableSet).mpr <|
      ((hhfsm.continuous.pow 2).continuousOn).integrableOn_compact (μ := MeasureTheory.volume)
        hcompact
  have hg2_le : ∀ z : E3, (g z) ^ 2 ≤ (Submission.BoseGases.chiSupAbs) ^ 2 *
      (Submission.BoseGases.acube ℓ).indicator (fun z : E3 => (hf z) ^ 2) z := by
    intro z
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hz, hgdef]
      have hb : |Submission.BoseGases.chiScale ℓ z| ≤ Submission.BoseGases.chiSupAbs :=
        Submission.BoseGases.chiScale_abs_le_sup ℓ z
      have hb2 : (Submission.BoseGases.chiScale ℓ z) ^ 2
          ≤ (Submission.BoseGases.chiSupAbs) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      nlinarith [hb2, sq_nonneg (hf z)]
    · rw [Set.indicator_of_notMem hz]
      have h0 : Submission.BoseGases.chiScale ℓ z = 0 := by
        by_contra hc
        exact hz (Submission.BoseGases.chiScale_mem_acube hℓ hc)
      have hgz : g z = 0 := by
        show Submission.BoseGases.chiScale ℓ z * hf z = 0
        rw [h0, zero_mul]
      rw [hgz]
      norm_num
  have hgL2 : (∫ z : E3, (g z) ^ 2) ≤ (Submission.BoseGases.chiSupAbs) ^ 2 * Q₂ := by
    have hcompact : IsCompact (Submission.BoseGases.acube ℓ) :=
      Work.UBBInputs8.A.isCompact_acube ℓ
    have h1 : (∫ z : E3, (g z) ^ 2)
        ≤ ∫ z : E3, (Submission.BoseGases.chiSupAbs) ^ 2 *
            (Submission.BoseGases.acube ℓ).indicator (fun z : E3 => (hf z) ^ 2) z := by
      by_cases hint : MeasureTheory.Integrable (fun z : E3 => (g z) ^ 2)
      · exact MeasureTheory.integral_mono_ae hint (hIndInt.const_mul _)
          (Filter.Eventually.of_forall hg2_le)
      · rw [MeasureTheory.integral_undef hint]
        exact MeasureTheory.integral_nonneg fun z =>
          mul_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun _ _ => sq_nonneg _) z)
    have h2 : (∫ z : E3, (Submission.BoseGases.chiSupAbs) ^ 2 *
        (Submission.BoseGases.acube ℓ).indicator (fun z : E3 => (hf z) ^ 2) z)
        = (Submission.BoseGases.chiSupAbs) ^ 2 * Q₂ := by
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_indicator hcompact.measurableSet, hQdef]
    linarith [h1, h2.le]
  have hQ₂nn : 0 ≤ Q₂ := by
    rw [hQdef]
    exact MeasureTheory.integral_nonneg fun z => sq_nonneg _
  have htail : (((ℓ * dd) ^ 2)⁻¹ * Work.BoseFixB1S.symACube MM 1
        (Submission.BoseGases.fsKinCoeff ((2 * ss)⁻¹)) 0) * (∫ z : E3, (g z) ^ 2)
      ≤ (Work.BoseBox.bValue / (4 * ℓ ^ 2)) * Q₂ := by
    have hTa : Work.BoseFixB1S.symACube MM 1
        (Submission.BoseGases.fsKinCoeff ((2 * ss)⁻¹)) 0
        * (Submission.BoseGases.chiSupAbs) ^ 2 ≤ (Work.BoseBox.bValue / 4) * dd ^ 2 := by
      have h0 := hT μ hAdm₃
      simpa only [← hMMdef, ← hsdef, ← hddef] using h0
    have hβnn : 0 ≤ Work.BoseFixB1S.symACube MM 1
        (Submission.BoseGases.fsKinCoeff ((2 * ss)⁻¹)) 0 := by
      rw [Work.BoseFixB1S.symACube]
      exact mul_nonneg (by positivity) (MeasureTheory.integral_nonneg fun p =>
        mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg _ _) (sq_nonneg _))
    calc (((ℓ * dd) ^ 2)⁻¹ * Work.BoseFixB1S.symACube MM 1
          (Submission.BoseGases.fsKinCoeff ((2 * ss)⁻¹)) 0) * (∫ z : E3, (g z) ^ 2)
        ≤ (((ℓ * dd) ^ 2)⁻¹ * Work.BoseFixB1S.symACube MM 1
            (Submission.BoseGases.fsKinCoeff ((2 * ss)⁻¹)) 0)
            * ((Submission.BoseGases.chiSupAbs) ^ 2 * Q₂) :=
          mul_le_mul_of_nonneg_left hgL2 (mul_nonneg (by positivity) hβnn)
      _ = (((ℓ ^ 2 * dd ^ 2)⁻¹ * (Work.BoseFixB1S.symACube MM 1
            (Submission.BoseGases.fsKinCoeff ((2 * ss)⁻¹)) 0
            * (Submission.BoseGases.chiSupAbs) ^ 2)) * Q₂) := by
          rw [show ((ℓ * dd) ^ 2)⁻¹ = (ℓ ^ 2 * dd ^ 2)⁻¹ by ring]
          ring
      _ ≤ ((ℓ ^ 2 * dd ^ 2)⁻¹ * ((Work.BoseBox.bValue / 4) * dd ^ 2)) * Q₂ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hTa (by positivity)) hQ₂nn
      _ = (Work.BoseBox.bValue / (4 * ℓ ^ 2)) * Q₂ := by
          have hne : ℓ ≠ 0 := ne_of_gt hℓ
          have hne2 : dd ≠ 0 := ne_of_gt hd
          field_simp
  -- ## (7) `mainWord` and `cnPlus` identifications
  have hw_eq : ∀ q : E3, w q
      = ‖Submission.BoseGases.kinFT (fun z : E3 =>
          ((Submission.BoseGases.chiScale ℓ z * hf z : ℝ) : ℂ)) q‖ ^ 2 := by
    intro q
    have hfun : (fun z : E3 => (g z : ℂ))
        = fun z : E3 => ((Submission.BoseGases.chiScale ℓ z * hf z : ℝ) : ℂ) := by
      funext z
      rw [hgdef]
    rw [hwdef, hfun]
  have hmain_id : Work.BoseKinLoc.mainWord ℓ dd ss ee 0 η
      = ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ q : E3, ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
              + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖) * w q) := by
    rw [Work.BoseFixB1.Core.mainWord_unproj_eq ℓ dd ss ee hℓ hηsm]
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    have hbsQ : Work.BSKinetic.bsQ ℓ 0 η = hf := by
      rw [Work.BoseFixB1.bsQ_zero_eq, hfdef]
    simp only [hbsQ, hw_eq]
  have hcn : Submission.BoseGases.cnPlus ℓ φ = Q₂ := by
    rw [Work.BoseFixB1.cnPlus_one_eq hℓ φ hφ, ← hηdef, hQdef]
  -- ## assembly
  have hstep1' : (∫ u : E3, ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW
        (Submission.BoseGases.fsKinCoeff cc)
        (fun z : E3 => Submission.BoseGases.chiSmallB MM ℓ dd u z *
          (η z - (1 / Work.SmallBoxSliding.boxMass ℓ dd u) *
            ∫ z' in Submission.BoseGases.dlBox ℓ dd u, η z')))
      = ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ u : E3, Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff cc)
          (fun z : E3 => Submission.BoseGases.chiSmallB MM ℓ dd u z *
            (η z - (1 / Work.SmallBoxSliding.boxMass ℓ dd u) *
              ∫ z' in Submission.BoseGases.dlBox ℓ dd u, η z'))) := by
    rw [MeasureTheory.integral_const_mul]
  calc (∫ u : E3, Work.BoseFixB1B.cubeSpectral v μ φ u)
      = ∫ u : E3, ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW
          (Submission.BoseGases.fsKinCoeff cc)
          (fun z : E3 => Submission.BoseGases.chiSmallB MM ℓ dd u z *
            (η z - (1 / Work.SmallBoxSliding.boxMass ℓ dd u) *
              ∫ z' in Submission.BoseGases.dlBox ℓ dd u, η z')) := hLHS
    _ = ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ u : E3, Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff cc)
          (fun z : E3 => Submission.BoseGases.chiSmallB MM ℓ dd u z *
            (η z - (1 / Work.SmallBoxSliding.boxMass ℓ dd u) *
              ∫ z' in Submission.BoseGases.dlBox ℓ dd u, η z'))) := hstep1'
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ u : E3, Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff cc)
            (fun z : E3 => Submission.BoseGases.chiSmallB MM ℓ dd u z * hf z))
        + (Work.BoseBox.bValue / (4 * ℓ ^ 2)) * Q₂ := step1
    _ = Work.BoseFixB1S.bsFamilyFormUnprojCube MM (ℓ * dd)
          (Submission.BoseGases.fsKinCoeff cc) g
        + (Work.BoseBox.bValue / (4 * ℓ ^ 2)) * Q₂ := by rw [step2]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ q : E3, Work.BoseFixB1S.symACube MM (ℓ * dd)
            (Submission.BoseGases.fsKinCoeff cc) q * w q)
        + (Work.BoseBox.bValue / (4 * ℓ ^ 2)) * Q₂ := by linarith [step3]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ q : E3, (((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
              + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖)
            + ((ℓ * dd) ^ 2)⁻¹ * Work.BoseFixB1S.symACube MM 1
                (Submission.BoseGases.fsKinCoeff ((2 * ss)⁻¹)) 0) * w q)
        + (Work.BoseBox.bValue / (4 * ℓ ^ 2)) * Q₂ := by linarith [hsym_int]
    _ = ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ q : E3, ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
              + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖) * w q)
        + (((ℓ * dd) ^ 2)⁻¹ * Work.BoseFixB1S.symACube MM 1
              (Submission.BoseGases.fsKinCoeff ((2 * ss)⁻¹)) 0)
            * (((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, w q))
        + (Work.BoseBox.bValue / (4 * ℓ ^ 2)) * Q₂ := by rw [hsplit']
    _ = ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ q : E3, ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
              + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖) * w q)
        + (((ℓ * dd) ^ 2)⁻¹ * Work.BoseFixB1S.symACube MM 1
              (Submission.BoseGases.fsKinCoeff ((2 * ss)⁻¹)) 0) * (∫ z : E3, (g z) ^ 2)
        + (Work.BoseBox.bValue / (4 * ℓ ^ 2)) * Q₂ := by rw [hpl]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ q : E3, ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
              + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖) * w q)
        + (Work.BoseBox.bValue / (4 * ℓ ^ 2)) * Q₂
        + (Work.BoseBox.bValue / (4 * ℓ ^ 2)) * Q₂ := by linarith [htail]
    _ = Work.BoseKinLoc.mainWord ℓ dd ss ee 0 η + (Work.BoseBox.bValue / (2 * ℓ ^ 2)) * Q₂ := by
        rw [← hmain_id]; ring
    _ = Work.BoseKinLoc.mainWord (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT 0
          (Work.BSKinetic.slotFun1 φ)
        + (Work.BoseBox.bValue / (2 * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 2))
          * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) φ := by
        rw [← hℓdef, ← hddef, ← hsdef, ← heedef, ← hηdef, ← hcn]

end Work.BoseFixB1C
