import ChallengeDeps
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Submission.Work.BoseBogFS.ChatChiFun
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-!
# `Work.BoseBogFS.honest_E_W1_zero`

The `Ŵ₁(0)` row of the honest environment: the kernel `E.W1` of
`HonestBoxFam v h fc fu HM μ` evaluated at the zero mode is the *mass*
`∫ W₁` of the honest kernel.

Unfolding `HonestBoxFam`/`KzEnvHon` the environment's `W1` is

  `W1 k = ζ_Λ(k) · Ŵ₁(k)`  with `ζ_Λ(k) = uvCut fu (uvRad ℓ N) k`,
  `Ŵ₁(k) = chat (W1fun v h ℓ) k`,  `ℓ = sideAt μ (a v)`,

and the zero mode is `kmom 0 = 0` (`kmom = kmomLab ℓ N` and `kmomLab ℓ N 0 = 0`).
So the claim is `ζ_Λ(0)·Ŵ₁(0) = ∫ W₁`, which is `1 · ∫ W₁`: the cut-off is `1` at `k = 0`
(`LowCut.one`) and `chat W 0 = ∫ W` at zero momentum (`integral_complex_ofReal`).

Note that the identity `chat W 0 = ∫ W` holds *unconditionally* — both sides are the
junk value `0` when `W` is not integrable — so no integrability hypothesis on
`W1fun v h ℓ` is needed (which is essential here: `ℓ = sideAt μ (a v)` is positive only
at `μa > 0`, whereas the statement quantifies over all real `μ`).
-/

/-- `chat W 0 = ∫ W`: the `p`-convention Fourier transform at zero momentum is the plain
integral.  Stated without an integrability hypothesis (`MeasureTheory.integral` and
`Submission.BoseGases.kinFT` are both `0` on non-integrable functions, so the identity
is an identity of total functions: `integral_complex_ofReal` is unconditional). -/
lemma chat_zero_eq_integral_uncond (W : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BoseFixR.chat W 0 = ∫ y : EuclideanSpace ℝ (Fin 3), W y := by
  simp only [Work.BoseFixR.chat, Submission.BoseGases.kinFT, inner_zero_left,
    Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul]
  rw [integral_complex_ofReal]
  exact Complex.ofReal_re _

/-- The label `0` of the momentum cube `Lab N` carries momentum `0`. -/
lemma kmomLab_zero_honest (ℓ : ℝ) (N : ℕ) : Work.BoseBoxFock.kmomLab ℓ N 0 = 0 := by
  have hlab : Work.BoseBoxFock.labVec N 0 = 0 := by
    funext i
    show ZMod.valMinAbs ((0 : Work.BoseBoxFock.Lab N) i) = (0 : ℤ)
    rw [show (0 : Work.BoseBoxFock.Lab N) i = (0 : ZMod (2 * N + 1)) from rfl]
    exact (ZMod.valMinAbs_eq_zero (0 : ZMod (2 * N + 1))).mpr rfl
  simp only [Work.BoseBoxFock.kmomLab, hlab]
  have hv : Work.BoseB4.vec (0 : Fin 3 → ℤ) = 0 := by
    ext i
    simp [Work.BoseB4.vec]
  rw [hv, smul_zero]

theorem honest_E_W1_zero {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    (μ : ℝ) :
    (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0
      = ∫ x, Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) x := by
  dsimp only [Work.BoseBoxFock.HonestBoxFam, Work.BoseBoxFock.KzEnvHon]
  change Work.BoseBoxFock.uvCut fu
        (Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (HM μ).N)
        (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N 0) *
      Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N 0)
    = ∫ (x : EuclideanSpace ℝ (Fin 3)),
        Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) x
  rw [kmomLab_zero_honest]
  simp only [Work.BoseBoxFock.uvCut, norm_zero, zero_div,
    Work.BoseBoxFix.LowCut.one fu 0 (by norm_num : (0 : ℝ) ≤ 1), one_mul]
  exact chat_zero_eq_integral_uncond _

end Work.BoseBogFS
