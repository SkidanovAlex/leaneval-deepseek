/-
# `EpsE4Thr/slotW_LGammaT_O` — the `W`-slot coercivity of `𝓛_Γ^T` in the **open** class

The frozen `Work.FTS.CoercivityFix.Coer1T.slotW_LGammaT` proves

  `(1/5)·Ef f - 1000·EDthW f ≤ wip (w²) (LGammaT α f) f`

for `f ∈ Work.FTS.Nonlin.CoerAdm α` (the *interior* class, `LocData.SmoothQuad`, analytic on the
half-strip `z > -1`).  The route's projected mollified slice only satisfies the **open** class
`CoerAdmO α` (there `SmoothQuad` is replaced by `SmoothOpen`, `C^∞` on the open quadrant), together
with the open integrability bundle `IntPkgO α f`.  This file proves the same slot estimate on that
reachable class.

The proof is the frozen one, split at exactly the same place, and the two substantive halves are
consumed from their own modules (independently proved):

* `OpenCoer.LGammaCoercive.LGamma_coercive_O` — the paper's proposition `L2Coercivity`,
  `(1/4)·Ef f ≤ wip (w²) (LGamma α f) f`;
* `OpenCoer.ProjPair.proj_pair_conj_O` — the sharp projector pairing bound
  `|wip (w²) (Proj α (Transport f)) f| ≤ (1/20)·Ef f + 1000·EDthW f`, with the integrability
  certificate of that pairing.

The assembly is the frozen one: `LGammaT α f = LGamma α f - Proj α (Transport f)`
(definitionally), both pairings are (`IntegrableOn`) honest — the second from the first conjunct of
`proj_pair_conj_O`, the first from `OpenCoer.intLG_O` — so `Coer1.wip_sub_left` splits the `wip`
and the two inequalities add up to the constant `1/5 = 1/4 - 1/20` in front of `Ef f`.

Supporting open-class facts live in `Submission/Work/FTS/StrongEps/EpsE4Thr/OpenCoer/SlotWCommon.lean`
(`intLG_O`, `intK_O`, `intG_O`, `intT1_w2_O`, `intDth2_O`, `aesm_dth_mul_w_O`, `C0_sq_le_EDthW_O`).
A second, independent transcription of the *same two* coercivity statements — written in parallel
inside this area — is kept as `OpenCoer/SlotWPort.lean` (`OpenCoer.Pvt.LGamma_coercive_pvt`,
`OpenCoer.Pvt.proj_pair_conj_pvt`); the target below uses the delegated modules, so the two
transcriptions mutually corroborate each other.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgO
import Submission.Work.FTS.CoercivityFix.Coer1T.slotW_LGammaT
import Submission.Work.FTS.StrongEps.EpsE4Thr.wip_transport_le_O
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenCoer.SlotWCommon
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenCoer.LGammaCoercive.LGamma_coercive_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenCoer.ProjPair.proj_pair_conj_O

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

theorem slotW_LGammaT_O {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14)
    {f : Work.FTS.Galerkin.Fn} (hf : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f)
    (hHH : Work.Coercivity.HardyHyp f) (hG : Work.Coercivity.GammaL2Bnd α) :
    (1 / 5) * Work.Coercivity.Ef f - 1000 * Work.Coercivity.EDthW f
      ≤ Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.Coercivity.LGammaT α f) f := by
  have hα1' : α ≤ 1 := by linarith [hα1]
  have hf2 : RegQo α 2 f := regQo_mono (by norm_num) hf.1
  have hs : Work.FTS.EllipticEst.SmoothOpen f := hf.1.1
  -- the two halves of the slot estimate
  have hA : (1 / 4) * Work.Coercivity.Ef f
      ≤ Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.Coercivity.LGamma α f) f :=
    OpenCoer.LGammaCoercive.LGamma_coercive_O hα hα1' hf2 hIP hHH hG
  have hB := OpenCoer.ProjPair.proj_pair_conj_O hα hα1' hf2 hIP hG
  have hBle : Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
      (Work.Coercivity.Proj α (Work.Coercivity.Transport f)) f
      ≤ (1 / 20) * Work.Coercivity.Ef f + 1000 * Work.Coercivity.EDthW f :=
    le_trans (le_abs_self _) hB.2
  -- the integrability of the two pairings, for `wip_sub_left`
  have hsub := Work.FTS.CoercivityFix.Coer1.wip_sub_left
    (ρ := fun z _ => Work.Spaces.w z ^ 2) (A := Work.Coercivity.LGamma α f)
    (B := Work.Coercivity.Proj α (Work.Coercivity.Transport f)) (C := f)
    (OpenCoer.intLG_O α hα hα1' hIP hs hHH) hB.1
  have hLGT : Work.Coercivity.LGammaT α f
      = (fun z θ => Work.Coercivity.LGamma α f z θ
          - Work.Coercivity.Proj α (Work.Coercivity.Transport f) z θ) := rfl
  rw [hLGT, hsub]
  linarith [hA, hBle]

end Work.FTS.StrongEps.EpsE4Thr
