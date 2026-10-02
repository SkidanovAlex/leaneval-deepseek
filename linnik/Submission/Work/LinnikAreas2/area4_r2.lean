/-
# `Submission.Work.LinnikAreas2.area4_r2` — Area 4 of the round-2 Linnik contract

`Work.LinnikContract2.Area4 = Area1 → D1 ∧ D2` (`Submission/Work/LinnikContract2/Areas.lean`),
where

* `(D1)` is HB Lemma 11.1, assembled in `Submission/Work/LinnikAreas2/D1Final.lean`
  (`Work.LinnikAreas2.d1_of_pieces`) from its two analytic inputs:
  * `psiBound_of_graham (hpsi : GrahamPsiSieve) (hgen : PsiWeightedGen)` — HB (11.14) at the
    contract's parameters.  `PsiWeightedGen` is `psi_weighted_eval_gen` (proved);
    `GrahamPsiSieve`, HB (11.13) `ψ` case, is `graham_psi_sieve_assembled` below, obtained from the
    *proved* two-sided `Lz` cross estimate `Work.ZeroDensity.Jutila.lzCross_est`
    (`ZeroDensity/Jutila/MsqSharpCrossLower.lean`) through
    `LinnikAreas2.PsiSieve2.graham_psi_sieve_of_lz`;
  * `thetaBound_of_sharp (hgraham : GrahamTheta) (hsharp : ThetaSharp)` — the sharp (subtracted)
    form of HB (11.17).  `GrahamTheta` is the `θ`-sieve `graham_theta_sieve` (proved), `ThetaSharp`
    is `theta_diag_sharp2`;
* `(D2)` is HB Table 13 via Lemma 12.1 (`d2_of_area1_aux`, on `Kbound_gen` and the 101 row
  certificates `T13Cert.rowCert_*`).

## Import-cone hygiene

Three name collisions in the shared, multi-branch `LinnikAreas/Density4` library make the `(D1)`
assembly and the `θ`-sieve impossible to import into one environment; they are resolved *without*
changing any mathematical statement (see the module docs of `PsiDefs2`, `PsiSieve`, `BzCrossEasy`
and the two renames `PhiSh`/`kappaBz`):

* the module `Density4.sum_log_div_le` and the lemma of the same name declared in
  `Density4/sum_abs_selLam_le.lean` (used by the `ZeroDensity/Jutila` branch) collide, and
  `Density4/psi_defs.lean` imported the module; the `ψ`-vocabulary is carried by
  `LinnikAreas2/PsiDefs2.lean` (+ `MidBoundsHarmonic2`, `SmallPieceLe2`) instead;
* the currently non-building `Jutila.BzCross` chain `ModelB → czRI_bound → czHarmDecay` entered the
  `ψ`-sieve only through `Jutila.BzCrossAux`'s easy case, now carried by
  `LinnikAreas2/BzCrossEasy.lean`; and the assembled sieve uses `lzCross_est`, which routes around
  the `BzCross` inputs altogether;
* `Density4.Phi` (declared both in `ShiftedDefs.lean` and, with a different type, in
  `SsmSetup.lean`) and `Density4.kappaR` (declared both in `BzBilinDefs.lean` and, with a
  different body, in `KappaDefs.lean`) are duplicate declaration names; the
  `ShiftedDefs`/`BzBilinDefs` ones are renamed `PhiSh`/`kappaBz` in place, with all their users
  updated.
-/
import Mathlib
import Submission.Work.LinnikAreas2.D1Final
import Submission.Work.LinnikAreas2.Kbound_gen
import Submission.Work.LinnikAreas2.D2Main
import Submission.Work.LinnikAreas2.graham_theta_sieve
import Submission.Work.LinnikAreas2.PsiSieve
import Submission.Work.LinnikAreas2.ThetaSharpAssembly
import Submission.Work.LinnikAreas2.psi_weighted_eval_gen
import Submission.Work.ZeroDensity.Jutila.MsqSharpCrossLower

namespace Work.LinnikAreas2

/-- **Graham's `ψ`-sieve, HB (11.13)**, from the proved two-sided `Lz` cross estimate
`Work.ZeroDensity.Jutila.lzCross_est`. -/
theorem graham_psi_sieve_assembled : GrahamPsiSieve :=
  fun ε hε => PsiSieve2.graham_psi_sieve_of_lz Work.ZeroDensity.Jutila.lzCross_est ε hε

/-- **Area 4 of the round-2 Linnik contract.**  `(D1)` is HB Lemma 11.1 (assembled in
`Submission.Work.LinnikAreas2.D1Final`); `(D2)` is HB Lemma 12.1 + Table 13 with the *wide*
(height-50) hypothesis (`d2_of_area1_aux`). -/
theorem area4_r2 : Work.LinnikContract2.Area4 :=
  fun h1 => ⟨d1_of_pieces h1
      (psiBound_of_graham graham_psi_sieve_assembled psi_weighted_eval_gen)
      (thetaBound_of_sharp graham_theta_sieve thetaSharp_proved),
    d2_of_area1_aux h1 (Kbound_gen h1)⟩

end Work.LinnikAreas2
