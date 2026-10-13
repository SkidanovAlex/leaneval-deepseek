import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.VocabO
import Submission.Work.Construction.Defs
import Submission.Work.FTS.StrongEps.ClassCRHS.StarAux
import Submission.Work.FTS.Nonlinear.Open.AngRadHkMem
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Open.Row23
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row23
import Submission.Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.LocData.angMaj_mem
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le
import Submission.Work.Spaces.GammaW_Prelim
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FM.Core
import Submission.Work.FTS.StrongEps.ClassCRHS.RadHkMemXn
import Submission.Work.FTS.StrongEps.ClassCRHS.DzBoundR0
import Submission.Work.FTS.StrongEps.ClassCRHS.DzBoundR2
import Submission.Work.FTS.StrongEps.ClassCRHS.AngSlotBounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The smoothness and the pointwise decompositions of the three scaled atoms

The three `F_*`-atoms are

`F0 = z/(1+z)·F_*`,  `F1 = z/(1+z)·D_θF_*`,  `F2 = z/(1+z)·D_zF_*`,

and each of them is, on the open quadrant, the product of an angular profile and one of
the two radial profiles `SR0 = 2z²/(1+z)³` (for `F0`, `F1`) and `SR2 = 2z²(1-z)/(1+z)⁴`
(for `F2`) — with angular profiles `SA0 = αΓ/c` (for `F0`, `F2`) resp. `SA1 = αD_θΓ/c`
(for `F1`).  The identities are proved below (`agree0`, `agree1`, `agree2`); the only
genuinely analytic input is `deriv (2z/(1+z)²) z = 2(1-z)/(1+z)³`, which is
`Work.FM.deriv_Fstar`.

The point of this file is then: the four facts

* `Work.FTS.EllipticEst.SmoothOpen` of each product,
* `Work.Spaces.HkMem α 4` of each product (via the angular `×` radial engine
  `Work.FTS.Nonlinear.Open.AngRadHkMem`),
* `Work.FTS.Nonlin.Xn α` of each product bounded by an `α`-uniform constant (via
  `Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen`),
* the transfer of all of these to the literal atoms `F0, F1, F2`

follow from the `α`-uniform angular slot bounds `AngSlotBounds` (sibling file), the
`α`-uniform radial `D_z`-iterate bounds `DzBoundR0`/`DzBoundR2` (sibling files), the
radial `ℋ⁴`-package `RadHkMemXn` (sibling file) and the `α`-uniform angular mass bound
`gamWeightInt`. -/

/-! ### Smoothness -/

lemma contDiffOn_SR0 (n : ℕ) : ContDiffOn ℝ n SR0 (Set.Ioi 0) := by
  have h : ContDiffOn ℝ n (fun z : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) (Set.Ioi 0) := by
    have hnum : ContDiffOn ℝ n (fun z : ℝ => 2 * z ^ 2) (Set.Ioi 0) := by fun_prop
    have hden : ContDiffOn ℝ n (fun z : ℝ => (1 + z) ^ 3) (Set.Ioi 0) := by fun_prop
    exact hnum.div hden (fun z hz => pow_ne_zero 3
      (ne_of_gt (by linarith [Set.mem_Ioi.mp hz] : (0 : ℝ) < 1 + z)))
  exact h

lemma contDiffOn_SR2 (n : ℕ) : ContDiffOn ℝ n SR2 (Set.Ioi 0) := by
  have h : ContDiffOn ℝ n (fun z : ℝ => 2 * z ^ 2 * (1 - z) / (1 + z) ^ 4) (Set.Ioi 0) := by
    have hnum : ContDiffOn ℝ n (fun z : ℝ => 2 * z ^ 2 * (1 - z)) (Set.Ioi 0) := by fun_prop
    have hden : ContDiffOn ℝ n (fun z : ℝ => (1 + z) ^ 4) (Set.Ioi 0) := by fun_prop
    exact hnum.div hden (fun z hz => pow_ne_zero 4
      (ne_of_gt (by linarith [Set.mem_Ioi.mp hz] : (0 : ℝ) < 1 + z)))
  exact h

lemma smoothOpen_SA0 (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => SA0 α θ) := by
  have h0 := Work.FTS.Nonlinear.Open.row23_smoothOpen_Gam α
  have h1 := Work.FTS.NonlinRows.smoothOpen_const_mul (α / Work.Spaces.c α) h0
  exact h1.congr (fun _ θ _ _ _ => by simp only [SA0]; ring)

lemma smoothOpen_SA1 (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => SA1 α θ) := by
  have h0 := Work.FTS.Nonlinear.Open.row23_smoothOpen_dthU_Gam α
  have h1 := Work.FTS.NonlinRows.smoothOpen_const_mul (α / Work.Spaces.c α) h0
  exact h1.congr (fun _ θ _ _ _ => by simp only [SA1]; ring)

lemma smoothOpen_SRrad0 : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => SR0 z) :=
  Work.FTS.Nonlinear.Open.row23_smoothOpen_radial contDiffOn_SR0

lemma smoothOpen_SRrad2 : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => SR2 z) :=
  Work.FTS.Nonlinear.Open.row23_smoothOpen_radial contDiffOn_SR2

/-! ### The three decompositions on the open quadrant -/

lemma agree0 {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z) :
    SA0 α θ * SR0 z = z / (1 + z) * Work.Construction.Fstar α z θ := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : (1 : ℝ) + z ≠ 0 := by linarith
  simp only [SA0, SR0, Work.Construction.Fstar, Work.FM.Fstar]
  field_simp

lemma agree1 {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z) :
    SA1 α θ * SR0 z = z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : (1 : ℝ) + z ≠ 0 := by linarith
  rw [Work.Spaces.Dth, Work.Spaces.pth]
  have hfun : (fun θ' : ℝ => Work.Construction.Fstar α z θ')
      = fun θ' : ℝ => (α * Work.FM.Fstar z / Work.Spaces.c α)
          * Work.Spaces.Gam α θ' := by
    funext θ'; rw [Work.Construction.Fstar]; ring
  rw [hfun, Work.Spaces.deriv_const_mul']
  simp only [SA1, SR0, Work.Spaces.dthU_apply, Work.FM.Fstar]
  field_simp

lemma agree2 {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z) :
    SA0 α θ * SR2 z = z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : (1 : ℝ) + z ≠ 0 := by linarith
  rw [Work.Spaces.Dz, Work.Spaces.pz]
  have hfun : (fun z' : ℝ => Work.Construction.Fstar α z' θ)
      = fun z' : ℝ => (α * Work.Spaces.Gam α θ / Work.Spaces.c α)
          * Work.FM.Fstar z' := by
    funext z'; rw [Work.Construction.Fstar]; ring
  rw [hfun, Work.Spaces.deriv_const_mul', Work.FM.deriv_Fstar z (by linarith)]
  simp only [SA0, SR2]
  field_simp

/-! ### The angular majorant -/

lemma SGmj_nonneg {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ SGmj α θ := by
  have h1 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have h2 : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  simp only [SGmj]
  positivity

/-- The mass bound of the angular majorant `Γ(α + sin 2θ)` against the weight
`sin(2θ)^{-γ}`, uniform in `α ∈ (0,1]` (`Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt`). -/
lemma SGmj_mass : ∃ M : ℝ, 0 < M ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => SGmj α θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ ∧
    ∫ θ in Work.Spaces.Iθ, SGmj α θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ ≤ M := by
  obtain ⟨M, hMpos, hM⟩ := Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt
  refine ⟨M, hMpos, fun α hα hα1 => ?_⟩
  obtain ⟨hint, hbd⟩ := hM α hα hα1
  have heq : (fun θ : ℝ => SGmj α θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
      = fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ := by
    funext θ
    simp only [SGmj]
    ring
  rw [heq]
  exact ⟨hint, hbd⟩

/-! ### The angular `×` radial engine, packaged -/

/-- The angular `×` radial engine of `Work.FTS.Nonlinear.Open.AngRadHkMem` together with the
norm bound `Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen`. -/
lemma atom_hk {α : ℝ} (hα : 0 < α) {a r G : ℝ → ℝ} {B0 B1 M Crad : ℝ}
    (ha : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ))
    (hr : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => r z))
    (hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G θ)
    (hGint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ)
    (hB0n : 0 ≤ B0) (hB1n : 0 ≤ B1) (hMn : 0 ≤ M)
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0)
    (ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B1 * G θ)
    (hmass : ∫ θ in Work.Spaces.Iθ,
      G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ ≤ M)
    (hrmem : Work.Spaces.HkMem α 4 (fun z (_ : ℝ) => r z))
    (hXnR : Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => r z) ≤ Crad) :
    Work.Spaces.HkMem α 4 (fun z θ => a θ * r z) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => a θ * r z)
        ≤ Real.sqrt (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M) * Crad := by
  have hHk : Work.Spaces.HkMem α 4 (fun z θ => a θ * r z) :=
    Work.FTS.Nonlinear.Open.AngRadHkMem (α := α) (a := a) (r := r) (G := G)
      (B0 := B0) (B1 := B1) ha hr hGnn hGint ha0 ha1 hrmem
  refine ⟨hHk, ?_⟩
  refine (Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen α hα a r G (B0 := B0) (B1 := B1)
    (M1 := M) hB0n hB1n hMn hGnn ha0 ha1 hGint hmass hrmem).trans ?_
  exact mul_le_mul_of_nonneg_left hXnR (Real.sqrt_nonneg _)

/-! ## The three scaled atoms -/

/-- **The three scaled `F_*`-atoms are `ℋ⁴`-honest with `ℋ⁴`-norm bounded uniformly in `α`.**

`F_* = F_*(α) = α (Γ(θ)/c(α)) 2z/(1+z)²` is the fundamental profile; `Dth = D_θ = sin(2θ)∂_θ`
and `Dz = z ∂_z`.  Note that the *unscaled* `F_*` is **not** in `ℋ⁴` (the weight `w` has a `1/z²`
at `z = 0` while `F_* ≍ z`); the assertion is about the scaled data `(z/(1+z))·F_*`, which is a
`𝒲^{4,∞}`-type function of the shape `const·(Γ or D_θΓ)(θ)·z²/(1+z)³`.

Route: `F_* = a θ * r z` is a separable angular `×` radial product (with `a = αΓ/c`,
`r z = 2z/(1+z)²`); write the scaled data in the same separable form, e.g.
`z/(1+z)·F_* = a θ * (z·r z/(1+z))`, `z/(1+z)·D_θF_* = a₁ θ * (z r z/(1+z))` with
`a₁ = α D_θΓ/c`, `z/(1+z)·D_zF_* = a₂ θ * (z r₂ z/(1+z))` with `r₂ = D_z r`, and apply the
angular `×` radial engine `Work.FTS.Nonlinear.Open.AngRadHkMem` (route/pattern of
`Submission/Work/FTS/Nonlinear/Open/Row23.lean`, which does exactly this for the profile
`dthU (Γ)/c` against `hKer²`), plus `Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen` for the
norm bound, and `FstarPkg.dthIter_one_Gam_le` / `FstarPkg.dthU_pow_Gam_sharp` for the angular
slot bounds on `D_θ^iΓ` (the good majorant for the `AngRadHkMem` hypothesis is `G = Γ` — note
`∫_Iθ Γ² sin(2θ)^{-γ} < ∞`; `FstarPkg.GamSinRpowMulLeOne` is available).
The two radial profiles `z·r/(1+z)` and `z·r₂/(1+z)` are smooth on `(0,∞)` with bounded
`D_z`-iterates up to order 4 and decay `O(1/z)` at `∞`, so the pure radial slots are directly
integrable.  `Work.Spaces.c_bounds` gives `1/10 ≤ c(α) ≤ 10`; the constant `C` must however be
*uniform* over `α ∈ (0,1]` (both reviewers checked that the norms are `O(√α)` as `α → 0⁺`, so
this is achievable). -/
theorem StarAtomsScaled : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    Work.FTS.VocabO.HQo α 4 (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ∧
    Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ≤ C ∧
    Work.FTS.VocabO.HQo α 4
      (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
    Work.FTS.Nonlin.Xn α
      (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ C ∧
    Work.FTS.VocabO.HQo α 4
      (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ∧
    Work.FTS.Nonlin.Xn α
      (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ≤ C := by
  -- ### the four facts furnished by the sibling files of this directory
  obtain ⟨B0, B1, hB0pos, hB1pos, hang⟩ := AngSlotBounds
  obtain ⟨M, hMpos, hMmass⟩ := SGmj_mass
  obtain ⟨Cr0, hCr0pos, hCr0bd⟩ := DzBoundR0
  obtain ⟨Cr2, hCr2pos, hCr2bd⟩ := DzBoundR2
  obtain ⟨Crd0, hCrd0pos, hCrd0⟩ :=
    RadHkMemXn (r := SR0) (C := Cr0) hCr0pos contDiffOn_SR0 hCr0bd
  obtain ⟨Crd2, hCrd2pos, hCrd2⟩ :=
    RadHkMemXn (r := SR2) (C := Cr2) hCr2pos contDiffOn_SR2 hCr2bd
  have hB0nn : 0 ≤ B0 := le_of_lt hB0pos
  have hB1nn : 0 ≤ B1 := le_of_lt hB1pos
  have hMnn : 0 ≤ M := le_of_lt hMpos
  have hCrd0nn : 0 ≤ Crd0 := le_of_lt hCrd0pos
  set S : ℝ := Real.sqrt (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M) with hSdef
  have hSnn : 0 ≤ S := Real.sqrt_nonneg _
  refine ⟨S * max Crd0 Crd2 + 1, ?_, fun α hαI => ?_⟩
  · have h1 : 0 ≤ S * max Crd0 Crd2 :=
      mul_nonneg hSnn (le_trans hCrd0nn (le_max_left _ _))
    linarith
  · obtain ⟨hα, hα1⟩ := Set.mem_Ioc.mp hαI
    obtain ⟨hA0bd, hA0sl, hA1bd, hA1sl⟩ := hang α hαI
    obtain ⟨hMint, hMbd⟩ := hMmass α hα hα1
    have hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ SGmj α θ := fun θ hθ => SGmj_nonneg hα hθ
    -- ### the three engineered products
    have hK0 := atom_hk (α := α) hα (a := SA0 α) (r := SR0) (G := SGmj α)
      (B0 := B0) (B1 := B1) (M := M) (Crad := Crd0) (smoothOpen_SA0 α) smoothOpen_SRrad0
      hGnn hMint hB0nn hB1nn hMnn hA0bd hA0sl hMbd (hCrd0 α hαI).1 (hCrd0 α hαI).2
    have hK1 := atom_hk (α := α) hα (a := SA1 α) (r := SR0) (G := SGmj α)
      (B0 := B0) (B1 := B1) (M := M) (Crad := Crd0) (smoothOpen_SA1 α) smoothOpen_SRrad0
      hGnn hMint hB0nn hB1nn hMnn hA1bd hA1sl hMbd (hCrd0 α hαI).1 (hCrd0 α hαI).2
    have hK2 := atom_hk (α := α) hα (a := SA0 α) (r := SR2) (G := SGmj α)
      (B0 := B0) (B1 := B1) (M := M) (Crad := Crd2) (smoothOpen_SA0 α) smoothOpen_SRrad2
      hGnn hMint hB0nn hB1nn hMnn hA0bd hA0sl hMbd (hCrd2 α hαI).1 (hCrd2 α hαI).2
    -- ### the transfers to the literal atoms
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
      Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad (smoothOpen_SA0 α) smoothOpen_SRrad0
    have hs1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => SA1 α θ * SR0 z) :=
      Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad (smoothOpen_SA1 α) smoothOpen_SRrad0
    have hs2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => SA0 α θ * SR2 z) :=
      Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad (smoothOpen_SA0 α) smoothOpen_SRrad2
    have hsq0 := Work.FTS.EllipticEst.HkSq_congr_open α 4 hq0
    have hsq1 := Work.FTS.EllipticEst.HkSq_congr_open α 4 hq1
    have hsq2 := Work.FTS.EllipticEst.HkSq_congr_open α 4 hq2
    refine ⟨⟨hs0.congr hq0,
        Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hK0.1
          (fun z hz θ hθ => hq0 z θ hz hθ.1 hθ.2)⟩,
      ?_, ⟨hs1.congr hq1,
        Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hK1.1
          (fun z hz θ hθ => hq1 z θ hz hθ.1 hθ.2)⟩,
      ?_, ⟨hs2.congr hq2,
        Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hK2.1
          (fun z hz θ hθ => hq2 z θ hz hθ.1 hθ.2)⟩,
      ?_⟩
    · show Real.sqrt (Work.Spaces.HkSq α 4
        (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ))
          ≤ S * max Crd0 Crd2 + 1
      rw [← hsq0]
      exact hK0.2.trans (le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hSnn)
        (by linarith))
    · show Real.sqrt (Work.Spaces.HkSq α 4
        (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ))
          ≤ S * max Crd0 Crd2 + 1
      rw [← hsq1]
      exact hK1.2.trans (le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hSnn)
        (by linarith))
    · show Real.sqrt (Work.Spaces.HkSq α 4
        (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ))
          ≤ S * max Crd0 Crd2 + 1
      rw [← hsq2]
      exact hK2.2.trans (le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hSnn)
        (by linarith))

end Work.FTS.StrongEps.ClassCRHS
