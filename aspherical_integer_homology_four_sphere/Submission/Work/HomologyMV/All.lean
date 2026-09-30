import Submission.Work.HomologyMV.Basic
import Submission.Work.HomologyMV.Model
import Submission.Work.HomologyMV.LinAlg
import Submission.Work.HomologyMV.Data
import Submission.Work.HomologyMV.Concrete
import Submission.Work.HomologyMV.Certs
import Submission.Work.HomologyMV.Interface
import Submission.Work.HomologyMV.ext_single
import Submission.Work.HomologyMV.ext_on_basis
import Submission.Work.HomologyMV.isoKer_of_surjective
import Submission.Work.HomologyMV.isoCoker_of_zero
import Submission.Work.HomologyMV.kerIso_of_commSquare
import Submission.Work.HomologyMV.rangeTop_of_commSquare
import Submission.Work.HomologyMV.ker_toLin_iso_int_of_normalForm
import Submission.Work.HomologyMV.coker_toLin_iso_int_of_normalForm
import Submission.Work.HomologyMV.kerModel_succ_iso_Sol
import Submission.Work.HomologyMV.wConcrete_surj
import Submission.Work.HomologyMV.wConcrete_ker
import Submission.Work.HomologyMV.Step
import Submission.Work.HomologyMV.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `HomologyMV/`: aggregate import

Import this module to get the whole `HomologyMV` chapter.

Main entry points:

* `Work.HomologyMV.MVLES` — the Mayer–Vietoris long exact sequence interface (and its
  constructors `MVLES.mkOfSlots`, `MVLES.mkOfNonneg`);
* **`Work.HomologyMV.intHomology_of_concrete`** — *the theorem to instantiate*: from the
  Mayer–Vietoris LES of `M̂ = A ∪ B`, the identifications of its first two slots with the free
  models, the commuting square with the matrices of `rtdata`, and `H_0(M̂) ≅ ℤ`, it gives
  `intHomology k X ≅ (if k = 0 ∨ k = 4 then ℤ else 0)` in the shape of the target statement;
* `Work.HomologyMV.intHomology_of_concrete'` — the same with `H_0(X) ≅ ℤ` as the degree-`0`
  input;
* `Work.HomologyMV.mv_homology`, `Work.HomologyMV.intHomology_mv` — the same with an arbitrary
  family of model maps `w`;
* `Work.HomologyMV.intHomology_iso_of_quasiIso` — the recipe that produces the identifications
  `eM`, `eN` from a quasi-isomorphism (`HS2`/`HS3`/`G0`) composed with a certificate
  (`CERT`'s `SDR.sound`);
* `Work.HomologyMV.SurjCert`, `Work.HomologyMV.KernelCert`, and their concrete instances
  `Work.HomologyMV.wConcrete_surj`, `Work.HomologyMV.wConcrete_ker`;
* `Work.HomologyMV.ker_phi3_iso_int`, `Work.HomologyMV.coker_phi0_iso_int` — the two end
  certificates (`H₄ ≅ ℤ`, and `H₀ ≅ coker φ₀ ≅ ℤ`).

See `Submission/Work/HomologyMV/NOTES.md` for the interface, the conventions and the remaining
work.
-/

namespace Work.HomologyMV

end Work.HomologyMV
