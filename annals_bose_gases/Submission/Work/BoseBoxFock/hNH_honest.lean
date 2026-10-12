import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseBoxFock.KafzDict
import Submission.Work.BoseBoxFock.vac_row
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

set_option autoImplicit false

open scoped BigOperators

/-- The `NH`-row of the honest family, transported under `split`.

`NH = (1/32) • ∑_{k ∈ s} w k · (a_{φ k}† a_{φ k})` with `a_{φ k} = annOf m (φ k)` a
superposition of *excited* lattice modes (`φ k 0 = 0`), so that `split` carries each
summand to the lift of the complex spectator number operator
`a_{φ k}^{C †} a_{φ k}^{C}`, `a^{C}_{φ k} = annOfE (φ k)`. -/
lemma split_NH_sum {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (s : Finset Mode) (w : Mode → ℝ) (φ : Mode → Fin m → ℝ)
    (h0 : ∀ k, φ k 0 = 0) (x : Work.BoseB4.RealFock m) :
    Work.BoseB4.split (((1 / 32 : ℝ) • ∑ k ∈ s, w k •
        ((Work.BoseB4.creOf m (φ k)).comp (Work.BoseB4.annOf m (φ k)))) x)
      = Work.BoseB4.lift ((1 / 32 : ℂ) • ∑ k ∈ s, (((w k : ℝ)) : ℂ) •
          ((Work.BoseBoxFock.creOfE (φ k)).comp (Work.BoseBoxFock.annOfE (φ k))))
            (Work.BoseB4.split x) := by
  have hsum : Work.BoseB4.split ((∑ k ∈ s, w k •
        ((Work.BoseB4.creOf m (φ k)).comp (Work.BoseB4.annOf m (φ k)))) x)
      = (Work.BoseB4.lift (∑ k ∈ s, ((w k : ℝ) : ℂ) •
          ((Work.BoseBoxFock.creOfE (φ k)).comp (Work.BoseBoxFock.annOfE (φ k)))))
            (Work.BoseB4.split x) := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      Work.BoseB4.lift_sum, Work.BoseB4.lift_smul, LinearMap.comp_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Work.BoseBoxFock.split_creOf_annOf (φ k) (φ k) (h0 k) (h0 k) x]
    exact Complex.coe_smul (w k) (Work.BoseB4.lift ((Work.BoseBoxFock.creOfE (φ k)).comp
      (Work.BoseBoxFock.annOfE (φ k))) (Work.BoseB4.split x))
  rw [LinearMap.smul_apply, map_smul, hsum, Work.BoseB4.lift_smul, LinearMap.smul_apply]
  rw [show (1 / 32 : ℂ) = ((1 / 32 : ℝ) : ℂ) by norm_num]
  exact (Complex.coe_smul (1 / 32 : ℝ)
    ((Work.BoseB4.lift (∑ k ∈ s, ((w k : ℝ) : ℂ) •
      ((Work.BoseBoxFock.creOfE (φ k)).comp (Work.BoseBoxFock.annOfE (φ k)))))
        (Work.BoseB4.split x))).symm

theorem hNH_honest {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut}
    {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ} (μ : ℝ) :
    ∀ y : Work.BoseB4.RealFock (HM μ).m,
      Work.BoseB4.split ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NH y)
        = Work.BoseB4.lift ((1 / 32 : ℂ) • ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
            (((Work.BoseBoxFock.etaH fu (((Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl
                * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
                * Real.sqrt (μ * BoseGases.a v))
              (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k)) : ℝ) : ℂ) •
              ((Work.BoseBoxFock.creOfE ((HM μ).f k)).comp (Work.BoseBoxFock.annOfE ((HM μ).f k))))
          (Work.BoseB4.split y) := by
  intro y
  dsimp only [Work.BoseBoxFock.HonestBoxFam]
  rw [Work.BoseBoxFock.tildeDataHon_NH]
  exact split_NH_sum _ _ _ (fun k => (HM μ).hf0 k) y

end Work.BoseBoxFock
