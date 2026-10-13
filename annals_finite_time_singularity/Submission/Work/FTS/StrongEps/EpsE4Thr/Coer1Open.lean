/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/Coer1Open.lean` — the level-one coercivity of `𝓛_Γ^T` on
the **open** class, assembled from the four slot estimates

`CoercivityFix/Coer1T/coer1_LGammaT.lean` proves the paper's Corollary
`FirstDerivativeCoercivity` at level one,

  `HkSq α 1 f ≤ H1IP α (𝓛_Γ^T f) f`   (`α ≤ 10⁻¹⁴`, `f ∈ CoerAdm α`),

by assembling four *slot estimates* (`slotDz`, `slotEta`, `slotW`, `slotGam`) with the arithmetic
ledger (`ledger`) and the two transfer-defect comparisons (`EDthW_le_EDth_Q`, `EL12z_le_Q`).

This file performs the assembly on the open class `CoerAdmO`:

* the ledger is `LedgerO.ledger_O` (proved; the only class-dependent input is
  `StrongPersist.HkSq_one_eq_SO`);
* the two defect comparisons are `EDthW_EL12z_open` (proved);
* the four slot estimates are taken as **hypotheses** — so this lemma is the *assembly point* of
  the open-class level-one coercivity, independent of the order in which the individual slot
  ports (`slotDz_LGammaT_O`, `slotEta_LGammaT_O`, `slotW_LGammaT_O`, `slotGam_LGammaT_O`) land.
  Their statements are exactly the four hypotheses of `LedgerO.ledger_O`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.EpsE4Thr.LedgerO
import Submission.Work.FTS.StrongEps.EpsE4Thr.EDthW_EL12z_open
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.hardyHyp_of_coerAdmO
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkg_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.slotEta_LGammaT_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.slotW_LGammaT_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.slotGam_LGammaT_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.slotDz_LGammaT_O
import Submission.Work.FTS.CoercivityFix.Coer1T.gammaL2Bnd_fts
import Submission.Work.FTS.CoercivityFix.Coer1T.gammaPointwiseBnd_fts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The level-one coercivity of `𝓛_Γ^T` on the open coercivity class**, from the four slot
estimates.  The class hypothesis is `CoerAdmO α f` (there is no `SmoothQuad` anywhere), and the
four `hP`/`hQ`/`hR`/`hS` are the slot bounds in the shape of `LedgerO.ledger_O`'s hypotheses
(they are the conclusions of the open ports of `slotDz_LGammaT`, `slotEta_LGammaT`,
`slotW_LGammaT`, `slotGam_LGammaT`). -/
theorem coer1_LGammaT_O_of_slots {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14)
    {f : Fn} (hf : CoerAdmO α f) (hHH : Work.Coercivity.HardyHyp f)
    (hP : (1 / 5) * Work.Coercivity.EDz f - 100 * Work.Coercivity.EfEta f
        - 100 * Work.Coercivity.EDth α f - 10 ^ 12 * Work.Coercivity.Ef f
      ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f))
    (hQ : (1 / 5) * Work.Coercivity.EfEta f
        - 100000 * (Work.Coercivity.EL12z f + Work.Coercivity.EDthW f + Work.Coercivity.Ef f)
      ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Coercivity.LGammaT α f) f)
    (hR : (1 / 5) * Work.Coercivity.Ef f - 1000 * Work.Coercivity.EDthW f
      ≤ Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.Coercivity.LGammaT α f) f)
    (hS : (17 / 40 - 1 / 100) * Work.Coercivity.EDth α f
        - (1 / 10 ^ 6) * Work.Coercivity.Ef f
      ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f)) :
    Work.Spaces.HkSq α 1 f ≤ Work.Coercivity.H1IP α (Work.Coercivity.LGammaT α f) f := by
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hf.1.1
  have hm1 : Work.Spaces.HkMem α 1 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hso 1 (by norm_num) hf.1.2.1
  have hm2 : Work.Spaces.HkMem α 2 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hso 2 (by norm_num) hf.1.2.1
  obtain ⟨hED, hEL⟩ := EDthW_EL12z_open (α := α) hα hso hm2 hHH
  exact ledger_O α hα hα1 hso hm1 hED hEL hP hQ hR hS

/-- **The level-one coercivity of `𝓛_Γ^T` on the open class, with only the `D_z`-slot estimate
outstanding.**  The `η`-, `W`- and `γ`-slots are supplied by the proved open ports
(`slotEta_LGammaT_O`, `slotW_LGammaT_O`, `slotGam_LGammaT_O`), the Hardy bundle by
`hardyHyp_of_coerAdmO`, and the two `γ`-packages by `gammaL2Bnd_fts`/`gammaPointwiseBnd_fts`. -/
theorem coer1_LGammaT_O_of_dzslot {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14)
    {f : Fn} (hf : CoerAdmO α f) (hIP : IntPkgO α f)
    (hP : (1 / 5) * Work.Coercivity.EDz f - 100 * Work.Coercivity.EfEta f
        - 100 * Work.Coercivity.EDth α f - 10 ^ 12 * Work.Coercivity.Ef f
      ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f)) :
    Work.Spaces.HkSq α 1 f ≤ Work.Coercivity.H1IP α (Work.Coercivity.LGammaT α f) f := by
  have hHH : Work.Coercivity.HardyHyp f := hardyHyp_of_coerAdmO hα hα1 hf
  exact coer1_LGammaT_O_of_slots hα hα1 hf hHH hP
    (slotEta_LGammaT_O hα hα1 hf hIP hHH (Work.FTS.CoercivityFix.Coer1T.gammaL2Bnd_fts α hα hα1))
    (slotW_LGammaT_O hα hα1 hf hIP hHH (Work.FTS.CoercivityFix.Coer1T.gammaL2Bnd_fts α hα hα1))
    (slotGam_LGammaT_O hα hα1 hf hIP hHH
      (Work.FTS.CoercivityFix.Coer1T.gammaPointwiseBnd_fts α hα))


/-- **The level-one coercivity of `𝓛_Γ^T` on the open coercivity class** — the paper's Corollary
`FirstDerivativeCoercivity` on `CoerAdmO`, with no `SmoothQuad` anywhere.  All four slot estimates
are the proved open ports, the Hardy bundle comes from `hardyHyp_of_coerAdmO`, and the two
`γ`-packages from `gammaL2Bnd_fts`/`gammaPointwiseBnd_fts`. -/
theorem coer1_LGammaT_O {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14)
    {f : Fn} (hf : CoerAdmO α f) (hIP : IntPkgO α f) :
    Work.Spaces.HkSq α 1 f ≤ Work.Coercivity.H1IP α (Work.Coercivity.LGammaT α f) f := by
  have hHH : Work.Coercivity.HardyHyp f := hardyHyp_of_coerAdmO hα hα1 hf
  exact coer1_LGammaT_O_of_slots hα hα1 hf hHH
    (slotDz_LGammaT_O hα hα1 hf hIP hHH)
    (slotEta_LGammaT_O hα hα1 hf hIP hHH (Work.FTS.CoercivityFix.Coer1T.gammaL2Bnd_fts α hα hα1))
    (slotW_LGammaT_O hα hα1 hf hIP hHH (Work.FTS.CoercivityFix.Coer1T.gammaL2Bnd_fts α hα hα1))
    (slotGam_LGammaT_O hα hα1 hf hIP hHH
      (Work.FTS.CoercivityFix.Coer1T.gammaPointwiseBnd_fts α hα))


end Work.FTS.StrongEps.EpsE4Thr
