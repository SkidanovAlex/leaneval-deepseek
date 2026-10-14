import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.GalFields.RHS.SharpAux.HonTerms.Base
import Submission.Work.FTS.RegExportIface.Producers
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.Trace
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.classCSinRate
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgMid
import Submission.Work.R1G.DecayInZ_gA

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The rate of `D_z^j Φ̃`** (`j ≤ 2`), by the two-sided Gronwall estimate `vopRated` applied to
the `θ`-slice of `D_z^j Φ̃`, whose `Vop`-jets are the `V`-slot jets of `PhiTil` and whose traces
vanish at both angular endpoints. -/
theorem phiTilDz_rate {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Fn →ₗ[ℝ] Fn}
    (hE : ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
        Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧
        Work.FTS.ClassC.EllPkgK α 6 Ce g (E g))
    {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab : a₀ ≤ b₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g → ∀ j : ℕ, j ≤ 2 →
      ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Ioo 0 (π / 2),
        |Work.Spaces.DzIter j (Work.Construction.PhiTil α g (E g)) z θ|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g * min θ (π / 2 - θ) := by
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨Cv, hCvpos, hCv⟩ := vopPhiTil_jets_le_Xn6 hα hα4 hE
  refine ⟨4 * Cv, by positivity, ?_⟩
  intro g hg j hj z hz θ hθ
  have hz0 : 0 < z := lt_of_lt_of_le ha₀ hz.1
  have hX0 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Work.Spaces.HkNorm_nonneg α 6 g
  have hGo : Work.FTS.VocabO.EllPkgGo α Ce g (E g) := (hE g hg).2.1
  have hO7 : Work.FTS.EllExist.EllClassOk 7 α g (E g) :=
    Work.FTS.EllSol.ellClassOk_eight_seven (hE g hg).1
  have hΦsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.PhiTil α g (E g)) :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα hGo
  -- the two traces, through the identification `Φ̃ = EllResid α g (E g)`
  obtain ⟨htr1, htr2⟩ := Work.FTS.ClassC.VopAux.vopTracesPointwise_classC j (by omega) α g (E g)
    hα hα4 hg hO7 z hz0
  have htr1' : Filter.Tendsto (fun θ' : ℝ => Work.Spaces.DzIter j
      (Work.Construction.PhiTil α g (E g)) z θ') (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [phiTil_eq α g (E g)] using htr1
  have htr2' : Filter.Tendsto (fun θ' : ℝ => Work.Spaces.DzIter j
      (Work.Construction.PhiTil α g (E g)) z θ')
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := by
    simpa only [phiTil_eq α g (E g)] using htr2
  have hcoslim : Filter.Tendsto (fun θ' : ℝ => Real.cos θ' * Work.Spaces.DzIter j
      (Work.Construction.PhiTil α g (E g)) z θ')
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := by
    have h := (Real.continuous_cos.continuousWithinAt.tendsto.mul htr2')
    simpa using h
  have hK : 0 ≤ 2 * Cv * Work.FTS.StrongGlobal.Xn6 α g := by positivity
  have hbound : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pth (Work.Spaces.DzIter j (Work.Construction.PhiTil α g (E g))) z θ'
        - Real.tan θ' * Work.Spaces.DzIter j (Work.Construction.PhiTil α g (E g)) z θ'|
        ≤ 2 * Cv * Work.FTS.StrongGlobal.Xn6 α g := by
    intro θ' hθ'
    have hQ : (z, θ') ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz0, hθ'.1, hθ'.2⟩
    have hcomm : Work.Spaces.pth (Work.Spaces.DzIter j (Work.Construction.PhiTil α g (E g)))
        z θ' = Work.Spaces.DzIter j (Work.Spaces.pth (Work.Construction.PhiTil α g (E g)))
          z θ' :=
      Work.Blocks.pth_DzIter_eqOn_Q0 hΦsm j hQ
    rw [hcomm]
    have hid := dzIter_add_const_mul_aux
      (A := Work.Spaces.pth (Work.Construction.PhiTil α g (E g)))
      (F := Work.Construction.PhiTil α g (E g)) hΦsm.pth hΦsm
      (fun θ'' => -(Real.tan θ'')) j z hz0 θ' hθ'
    have hvop : Work.Spaces.mixed j 0
        (Work.Construction.Vop (Work.Construction.PhiTil α g (E g))) z θ'
        = Work.Spaces.DzIter j (Work.Spaces.pth (Work.Construction.PhiTil α g (E g))) z θ'
          - Real.tan θ' * Work.Spaces.DzIter j (Work.Construction.PhiTil α g (E g)) z θ' := by
      have heq : Work.Construction.Vop (Work.Construction.PhiTil α g (E g))
          = fun z θ => Work.Spaces.pth (Work.Construction.PhiTil α g (E g)) z θ
              + (-(Real.tan θ)) * Work.Construction.PhiTil α g (E g) z θ := by
        funext z θ
        simp only [Work.Construction.Vop]
        ring
      rw [heq, Work.Spaces.mixed_zero_right, hid]
      ring
    rw [← hvop]
    refine le_trans (hCv g hg j (by omega) z θ' hz0 ⟨hθ'.1, hθ'.2⟩) ?_
    nlinarith [hX0, hCvpos]
  obtain ⟨hb1, hb2⟩ := vopRated
    (f := fun θ' => Work.Spaces.DzIter j (Work.Construction.PhiTil α g (E g)) z θ')
    (f' := fun θ' => Work.Spaces.pth (Work.Spaces.DzIter j
      (Work.Construction.PhiTil α g (E g))) z θ')
    (K := 2 * Cv * Work.FTS.StrongGlobal.Xn6 α g) hK
    (fun θ' hθ' => ((hΦsm.DzIter j).curry_θ hz0).contDiffAt
        (isOpen_Ioo.mem_nhds hθ') |>.differentiableAt
        Work.FTS.LocData.smoothOrder_ne_zero |>.hasDerivAt)
    hbound htr1' hcoslim
  have hmin : |Work.Spaces.DzIter j (Work.Construction.PhiTil α g (E g)) z θ|
      ≤ 2 * (2 * Cv * Work.FTS.StrongGlobal.Xn6 α g) * min θ (π / 2 - θ) :=
    vop_two_sided_le_min hK hb1 hb2 θ hθ
  calc |Work.Spaces.DzIter j (Work.Construction.PhiTil α g (E g)) z θ|
      ≤ 2 * (2 * Cv * Work.FTS.StrongGlobal.Xn6 α g) * min θ (π / 2 - θ) := hmin
    _ = (4 * Cv) * Work.FTS.StrongGlobal.Xn6 α g * min θ (π / 2 - θ) := by ring

/-- **The rate of `D_z^j (E g)`** (`j ≤ 2`): `Ψ = Φ̃ + Θ` with `Θ` explicit of rate `sin 2θ`. -/
theorem psiDz_rate {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Fn →ₗ[ℝ] Fn}
    (hE : ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
        Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧
        Work.FTS.ClassC.EllPkgK α 6 Ce g (E g))
    {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab : a₀ ≤ b₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g → ∀ j : ℕ, j ≤ 2 →
      ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Ioo 0 (π / 2),
        |Work.Spaces.DzIter j (E g) z θ|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g * min θ (π / 2 - θ) := by
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨C1, hC1pos, hC1⟩ := phiTilDz_rate hα hα4 hE ha₀ hab
  obtain ⟨C2, hC2pos, hC2⟩ := thetaDz_le_min hα hα1
  refine ⟨C1 + C2, by positivity, ?_⟩
  intro g hg j hj z hz θ hθ
  have hz0 : 0 < z := lt_of_lt_of_le ha₀ hz.1
  have hΦsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.PhiTil α g (E g)) :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα (hE g hg).2.1
  have hΨsm : Work.FTS.EllipticEst.SmoothOpen (E g) := (hE g hg).1.2.1
  have hΘsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Theta α g) := by
    have hsub : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (E g) z θ + (-1) * Work.Construction.PhiTil α g (E g) z θ) :=
      Work.FTS.EllipticEst.smoothOpen_add hΨsm
        (Work.FTS.EllipticEst.SmoothOpen.const_mul' (-1) hΦsm)
    refine hsub.congr ?_
    intro z θ _ _ _
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    ring
  have hadd : Work.Spaces.DzIter j (E g) z θ
      = Work.Spaces.DzIter j (Work.Construction.PhiTil α g (E g)) z θ
        + Work.Spaces.DzIter j (Work.Construction.Theta α g) z θ := by
    have heq : (E g) = fun z θ => Work.Construction.PhiTil α g (E g) z θ
        + Work.Construction.Theta α g z θ := Eg_eq_phiTil_add α g (E g)
    conv_lhs => rw [heq]
    exact dzIter_add_eqOn hΦsm hΘsm j z hz0 θ ⟨hθ.1, hθ.2⟩
  rw [hadd]
  refine le_trans (abs_add_le _ _) ?_
  have h1 := hC1 g hg j hj z hz θ hθ
  have h2 := hC2 g hg j (by omega) z θ hz0 ⟨hθ.1, hθ.2⟩
  have hX0 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Work.Spaces.HkNorm_nonneg α 6 g
  have hm0 : 0 ≤ min θ (π / 2 - θ) := le_of_lt (lt_min hθ.1 (by linarith [hθ.2]))
  calc |Work.Spaces.DzIter j (Work.Construction.PhiTil α g (E g)) z θ|
        + |Work.Spaces.DzIter j (Work.Construction.Theta α g) z θ|
      ≤ C1 * Work.FTS.StrongGlobal.Xn6 α g * min θ (π / 2 - θ)
        + C2 * Work.FTS.StrongGlobal.Xn6 α g * min θ (π / 2 - θ) := add_le_add h1 h2
    _ = (C1 + C2) * Work.FTS.StrongGlobal.Xn6 α g * min θ (π / 2 - θ) := by ring


end Work.FTS_EllLimOK.ProducerH.BoxAux
