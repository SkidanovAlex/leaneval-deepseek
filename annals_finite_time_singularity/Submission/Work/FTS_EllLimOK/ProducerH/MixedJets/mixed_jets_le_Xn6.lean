import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.pkgCos_le4
import Submission.Work.FTS_EllLimOK.ProducerH.slotBd_phiTil
import Submission.Work.FTS_EllLimOK.ThetaJets.Theta_jets_le
import Submission.Work.FTS_RegExport.RXT.Sys.slice_contDiffOn_four
import Submission.Work.FTS_StreamBdry.Inputs.ftau_Dz_cont
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.MixedJets

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Smoothness of the singular part `Θ`

`Θ α g = (1/(4α)) sin 2θ · L₁₂ g` is a separable product of a `θ`-only and a `z`-only smooth
factor; this is the (private) `Theta_smoothOpen` of `PkgJets/pkg_pointwise_jets`, needed here for
the pointwise splitting of `D_z^jD_θ^i (Φ̃ + Θ)`. -/

private theorem Theta_smoothOpen {α Ce : ℝ} (hα : 0 < α) {g Φg : ℝ → ℝ → ℝ}
    (hGo : Work.FTS.VocabO.EllPkgGo α Ce g Φg) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Theta α g) := by
  have hEq : Work.Construction.Theta α g
      = (fun z θ => (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 g z) := by
    funext z θ
    simp only [Work.Construction.Theta, Work.Construction.s2]
  rw [hEq]
  exact Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul
    (Work.FTS.NonlinRows.smoothOpen_const_mul (1 / (4 * α))
      Work.FTS.GalFields.RHS.smoothOpen_sin_two)
    (Work.FTS.GalFields.RHS.Sharp.smoothOpen_L12_gal hα hGo)

/-- **The pointwise mixed-jet bound of `E g` relative to the `ℋ⁶`-norm of the source.**

For every `α ≤ 1/4`, every linear `E` carrying the level-`8` existence class together with the
two packages on the class `C`, there is a constant `K` (depending on `α`, `Ce` only) with

  `|D_z^j D_θ^i (E g)(z,θ)| ≤ K·|g|_{ℋ⁶}`   (`j + i ≤ 4`, `(z,θ) ∈ Qd`, `g ∈ ClassC α`).

This is the pointwise half of the far-field field `PkgDecay` of the repaired package: no decay in
`z` is claimed, only a bound *proportional* to `Xn₆ α g` (uniform in `g`, which is what a
`LimSeq4`-argument needs).

The proof splits `E g = Φ̃ + Θ` (`Φ̃ = PhiTil α g (E g)`,
`Θ α g = (1/(4α)) sin 2θ·L₁₂ g`):

* the jets of `Θ` are `≤ C_Θ(α)·Xn₆ α g` (`ThetaJets.Theta_jets_le`, from the radial
  `z`-jet bound `L₁₂jets_classC` and the angular factor `|D_θ^i sin 2·| ≤ 384`);
* the jets of `Φ̃` are `≤ C_V·K_V` where `K_V = C_S·|Ce|·Xn₆ α g` bounds the jets of the
  coefficient slot `Vop Φ̃` (`SlotSup.slot_jets_sup_le` applied to the `ℋ⁶`-slot `V` of
  `EllPkgK`), and the transfer `Vop`-jets ⟹ `Φ̃`-jets is
  `VopTransfer.mixed_le_of_Vop_jets`, whose pinning hypothesis is the field `PkgCos`
  (`ProducerH.pkgCos_of_ellClassOk`). -/
theorem mixed_jets_le_Xn6 {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
        Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧
        Work.FTS.ClassC.EllPkgK α 6 Ce g (E g)) :
    ∃ K : ℝ, 0 < K ∧ ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        |Work.Spaces.mixed j i (E g) z θ| ≤ K * Work.FTS.StrongGlobal.Xn6 α g := by
  have hα1 : α ≤ 1 := by linarith
  -- the three universal constants
  obtain ⟨CS, hCS0, hCS⟩ := Work.FTS_EllLimOK.SlotSup.slot_jets_sup_le α hα hα1
  obtain ⟨CV, hCV0, hCV⟩ := Work.FTS_EllLimOK.VopTransfer.mixed_le_of_Vop_jets
  obtain ⟨Cth, hCth0, hCth⟩ := Work.FTS_EllLimOK.ThetaJets.Theta_jets_le α hα
  -- the pinning field `PkgCos`
  have hcos : Work.FTS_EllLimOK.PkgCos α E :=
    pkgCos_le4 α hα hα4 E (fun g hg => (hE g hg).1)
  have hPkg : Work.FTS_EllLimOK.HasPkg α Ce E :=
    fun g hg => ⟨(hE g hg).2.1, (hE g hg).2.2⟩
  have hpin := Work.FTS_EllLimOK.Pinning.hpin_of_pkgCos hα hα1 hPkg hcos
  refine ⟨CV * (CS * |Ce|) + Cth + 1, by positivity, ?_⟩
  intro g hg j i hji z θ hzθ
  have hz : 0 < z := hzθ.1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hzθ.2
  have hXnn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Work.Spaces.HkNorm_nonneg α 6 g
  have hGo : Work.FTS.VocabO.EllPkgGo α Ce g (E g) := (hE g hg).2.1
  have hK : Work.FTS.ClassC.EllPkgK α 6 Ce g (E g) := (hE g hg).2.2
  -- smoothness of the two summands
  have hΦsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.PhiTil α g (E g)) :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα hGo
  have hΘsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Theta α g) :=
    Theta_smoothOpen hα hGo
  -- ## the jets of the coefficient slot `Vop Φ̃`
  have hVjets : ∀ (l m : ℕ), l + m ≤ 4 → ∀ (z' θ' : ℝ), 0 < z' →
      θ' ∈ Set.Ioo (0 : ℝ) (π / 2) →
      |Work.Spaces.mixed l m (Work.Construction.Vop (Work.Construction.PhiTil α g (E g))) z' θ'|
        ≤ CS * (|Ce| * Work.FTS.StrongGlobal.Xn6 α g) := by
    intro l m hlm z' θ' hz' hθ'
    refine le_trans (hCS _ hK.V.1.1 hK.V.1.2 l m (by omega) z' θ' hz' hθ'.1 hθ'.2) ?_
    refine mul_le_mul_of_nonneg_left ?_ hCS0.le
    calc Work.Spaces.HkNorm α 6 (Work.Construction.Vop (Work.Construction.PhiTil α g (E g)))
        ≤ Ce * Work.Spaces.HkNorm α 6 g := hK.V.2
      _ ≤ |Ce| * Work.FTS.StrongGlobal.Xn6 α g :=
          mul_le_mul_of_nonneg_right (le_abs_self Ce) hXnn
  -- ## the jets of `Φ̃`
  have hΦjets : |Work.Spaces.mixed j i (Work.Construction.PhiTil α g (E g)) z θ|
      ≤ CV * (CS * (|Ce| * Work.FTS.StrongGlobal.Xn6 α g)) :=
    hCV (CS * (|Ce| * Work.FTS.StrongGlobal.Xn6 α g))
      (mul_nonneg hCS0.le (mul_nonneg (abs_nonneg Ce) hXnn))
      _ hΦsm (hpin g hg) hVjets j i hji z θ hz hθ
  -- ## the jets of `Θ`
  have hΘjets : |Work.Spaces.mixed j i (Work.Construction.Theta α g) z θ|
      ≤ Cth * Work.FTS.StrongGlobal.Xn6 α g :=
    hCth g hg j i hji z θ hz hθ
  -- ## the decomposition `E g = Φ̃ + Θ`
  have hdec : E g = fun z θ => Work.Construction.PhiTil α g (E g) z θ
      + Work.Construction.Theta α g z θ := by
    funext z' θ'
    simp only [Work.Construction.PhiTil]
    ring
  rw [hdec, Work.FTS.EllipticEst.SmoothOpen.mixed_add hΦsm hΘsm j i z θ hz hθ.1 hθ.2]
  refine le_trans (abs_add_le _ _) ?_
  have hsum : CV * (CS * (|Ce| * Work.FTS.StrongGlobal.Xn6 α g))
        + Cth * Work.FTS.StrongGlobal.Xn6 α g
      ≤ (CV * (CS * |Ce|) + Cth + 1) * Work.FTS.StrongGlobal.Xn6 α g := by
    nlinarith [hXnn]
  linarith [hΦjets, hΘjets, hsum]

end Work.FTS_EllLimOK.ProducerH.MixedJets
