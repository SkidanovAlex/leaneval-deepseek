/-
# `H5/L5of` — the level-`5` data bundle from the level-`5` `ℋ⁵`-data

The `L5` bundle (`H5.Data`) collects, for the level-`5` treatment of a product `f·g`, the
level-four data of `f` *and of its first derivatives* `D_z f`, `D_θ f`.  For an atom that already
carries level-`5` `ℋ⁵`-data this bundle is free: the derivative memberships come from
`HkMem_dz_le`/`HkMem_Dθ_le` (or `IPGen.HkMem_Dz_le`/`HkMem_Dth_le`) and the derivative bounds
from the level shift `HkSq_Dz_le_Q0Sm` / `HkSq_Dth_le` together with
`HkSq_mono`/`HkNorm_mono_of_mem`:

  `|D_z f|_{ℋ⁴} ≤ |f|_{ℋ⁵}`,  `|D_θ f|_{ℋ⁴} ≤ |f|_{ℋ⁵}`.

So an atom with `HQo α 5 A` and `HkNorm α 5 A ≤ a` automatically carries `L5 α A a`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.StrongEps.H5.Data
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_Dth_le
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.StrongPersist.IP6_lo_coeffs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

open Work.Spaces
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The level-`5` bundle of an atom, from its level-`5` `ℋ⁵`-data.** -/
theorem L5_of_HQo5 {α : ℝ} (hα : 0 < α) {A : Fn} {a : ℝ}
    (h : Work.FTS.VocabO.HQo α 5 A) (hb : Work.Spaces.HkNorm α 5 A ≤ a) :
    L5 α A a := by
  have hmem4 : Work.Spaces.HkMem α 4 A :=
    Work.FTS.OpenPkg.HkMem_mono_open h.1 4 (by norm_num) h.2
  have hbd4 : Work.FTS.Nonlin.Xn α A ≤ a :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 5) (k' := 4)
      (by norm_num) h.2) hb
  have hDz5 : Work.Spaces.HkNorm α 4 (Work.Spaces.Dz A) ≤ Work.Spaces.HkNorm α 5 A :=
    Real.sqrt_le_sqrt (Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α 4
      (Work.FTS.StrongPersist.q0Sm_of_smoothOpen h.1 5) h.2)
  have hDth5 : Work.Spaces.HkNorm α 4 (Work.Spaces.Dth A) ≤ Work.Spaces.HkNorm α 5 A :=
    Real.sqrt_le_sqrt (Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα 4 h.2)
  exact ⟨⟨h.1, hmem4⟩, hbd4,
    ⟨h.1.Dz, Work.FTS.IPGen.HkMem_Dz_le h.1 h.2⟩, le_trans hDz5 hb,
    ⟨h.1.Dth, Work.FTS.IPGen.HkMem_Dth_le (by linarith) h.1 h.2⟩, le_trans hDth5 hb⟩

end Work.FTS.StrongEps.H5
