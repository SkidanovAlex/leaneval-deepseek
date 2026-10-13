import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.PhiStar.CoreAux.F0_mul
import Submission.Work.FTS.PhiStar.CoreAux.F0_add
import Submission.Work.FTS.PhiStar.CoreAux.F0_congr
import Submission.Work.FTS.PhiStar.CoreAux.Fb_basic
import Submission.Work.FTS.PhiStar.CoreAux.EVDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.CoreAux

theorem Fb_mul_theta_free {n : ℕ} {K A : ℝ} {f c : ℝ → ℝ → ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsc : Work.FTS.EllipticEst.SmoothOpen c)
    (hf : Work.FTS.PhiStar.Fb n K f) (hc : Work.FTS.PhiStar.F0 n A c)
    (hcd : Work.FTS.PhiStar.F0 n A (Work.Spaces.pth c)) :
    Work.FTS.PhiStar.Fb n ((2 : ℝ) ^ (n + 1) * K * A) (fun z θ => f z θ * c z θ) := by
  have hle : (2 : ℝ) ^ n * K * A ≤ (2 : ℝ) ^ (n + 1) * K * A := by
    have hx : (0 : ℝ) ≤ (2 : ℝ) ^ n * K * A :=
      mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) n) hK) hA
    have hpow : (2 : ℝ) ^ (n + 1) * K * A = ((2 : ℝ) ^ n * K * A) * 2 := by
      rw [pow_succ]; ring
    rw [hpow]; linarith
  refine ⟨?_, ?_⟩
  · exact (F0_mul hK hA hsf hsc hf.f0 hc).mono le_rfl hle
  · have h2a : F0 n ((2 : ℝ) ^ n * K * A) (fun z θ => Work.Spaces.pth f z θ * c z θ) :=
      F0_mul hK hA hsf.pth hsc hf.fd hc
    have h2b : F0 n ((2 : ℝ) ^ n * K * A) (fun z θ => f z θ * Work.Spaces.pth c z θ) :=
      F0_mul hK hA hsf hsc.pth hf.f0 hcd
    have hsum : F0 n ((2 : ℝ) ^ n * K * A + (2 : ℝ) ^ n * K * A)
        (fun z θ => Work.Spaces.pth f z θ * c z θ + f z θ * Work.Spaces.pth c z θ) :=
      F0_add (Fbq_smoothOpen_mul hsf.pth hsc) (Fbq_smoothOpen_mul hsf hsc.pth) h2a h2b
    have hconst : (2 : ℝ) ^ n * K * A + (2 : ℝ) ^ n * K * A
        = (2 : ℝ) ^ (n + 1) * K * A := by
      rw [pow_succ]; ring
    exact F0_congr (Fbq_pth_mul hsf hsc) (hsum.mono le_rfl (le_of_eq hconst))

end Work.FTS.PhiStar.CoreAux
