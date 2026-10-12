import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Real.Basic
import Submission.Work.BoseBoxFock.AllDefs
import Submission.Work.BoseC3QAll.Final
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.AllStatement` — the frozen statement `Control3QFSAll`

Design item D2 (`Submission/Work/BOSE_ALL_DESIGN.md` §5): the C3Q chapter
(`Submission/Work/BoseB7AK/C3Q`, where FS `thm:Control3Q` is proved at the
corrected gate) is ported to the `All` vocabulary by `_port.py` into this
directory, and this module converts the ported headline into the **frozen**
statement `Work.BoseBoxFock.Control3QFSAll` of
`Submission/Work/BoseBoxFock/AllDefs.lean`.

## Contents

* `q3KernelFSAll_of_frozen` — the **gate bridge**: the frozen gate
  `Work.BoseBoxFock.Q3KernelFSAll` yields the ported gate
  `Work.BoseC3QAll.Q3KernelFSAll` of this directory.  The two differ in exactly
  one place: the ported gate carries the row `kmom_neg`
  (`F.kmom (-i) = -F.kmom i`), which the §10 chain of `Defs.lean` uses
  (`noWrap_used_pairs` and the seven evaluations `kerA … kerE`), and which the
  frozen gate does not list — it is available from the Fock data itself
  (`FockData.kmom_neg`), so the bridge costs nothing.  The remaining 31 fields,
  including the windowed `q2exLowerR` row against `Q2exAll`, are literally the
  same fields, so the bridge is a `structure` literal.
* `control3QFSAll` — **the deliverable**: `Work.BoseBoxFock.Control3QFSAll K₀ b₀ hb₀`
  for every `K₀` and `b₀ > 0`, i.e. FS `thm:Control3Q` at the `All` gate: there
  are `C`, `t₀ > 0` (depending only on `K₀, b₀`) such that for every Fock system
  `F`, θ-mode datum `T`, parameter point `E` with `E.t ≤ t₀`, `b₀ ≤ E.b` and the
  windowed `All` gate, and every state `Φ` in the `n₊`-window,
  `⟨Φ, controlWordHiAll T E Φ⟩ ≥ -(C · controlErrA E)·‖Φ‖²`.

  It is `Work.BoseC3QAll.control3QFS` (`Final.lean`) at `u = v = 0`, composed
  with the gate bridge: the two words agree (`Work.BoseBoxFock.controlWordHiAll`
  is definitionally the ported `Work.BoseC3QAll.controlWordHi`) and
  `Work.BoseB7A.controlErrA` is definitionally the ported `controlErrA`, so the
  composition is `exact`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

open Work.BoseB7

universe u v

/-- **The gate bridge**: the frozen `All` gate gives the ported one.  The only
difference between the two structures is the row `kmom_neg`, which is a field of
`FockData` (`F.kmom_neg`). -/
theorem q3KernelFSAll_of_frozen {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {K₀ : ℝ} {F : Work.BoseB7.FockData Mode}
    {T : Work.BoseB7A.TildeData F} {E : Work.BoseB7.Q3Env Mode}
    (h : Work.BoseBoxFock.Q3KernelFSAll K₀ F T E) : Q3KernelFSAll K₀ F T E where
  W1_le := h.W1_le
  W1_even := h.W1_even
  A_even := h.A_even
  B_even := h.B_even
  B_eq := h.B_eq
  AB := h.AB
  A_ge := h.A_ge
  fL_nonneg := h.fL_nonneg
  fL_le_one := h.fL_le_one
  fL_even := h.fL_even
  fL_supp2 := h.fL_supp2
  kmom_subW := h.kmom_subW
  kmom_subL := h.kmom_subL
  kmom_neg := F.kmom_neg
  hasKernelW := h.hasKernelW
  hasKernel_noWrap := h.hasKernel_noWrap
  hatChiSq_le := h.hatChiSq_le
  hatChi_le := h.hatChi_le
  hatChi_even := h.hatChi_even
  hatChiSq_even := h.hatChiSq_even
  hatChi_small := h.hatChi_small
  ccrX_small := h.ccrX_small
  hatChiSq_form := h.hatChiSq_form
  count_PL := h.count_PL
  sum_hatChiSq := h.sum_hatChiSq
  tail_hatChiSq := h.tail_hatChiSq
  sum_W1sq := h.sum_W1sq
  alpha_lip := h.alpha_lip
  W1omega0_nonneg := h.W1omega0_nonneg
  W1omega0_le := h.W1omega0_le
  intOne := h.intOne
  q2exLowerR := h.q2exLowerR

/-- **FS `thm:Control3Q` at the `All` gate** (the deliverable of design item D2):
`Work.BoseBoxFock.Control3QFSAll K₀ b₀ hb₀`. -/
theorem control3QFSAll (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) : Work.BoseBoxFock.Control3QFSAll K₀ b₀ hb₀ := by
  obtain ⟨C, t₀, hC, ht₀, H⟩ := control3QFS.{0, 0} K₀ b₀ hb₀
  refine ⟨C, t₀, hC, ht₀, ?_⟩
  intro Mode _ _ _ F T E hv ht hb hK Φ hΦ
  exact H (Mode := Mode) F T E hv ht hb (q3KernelFSAll_of_frozen hK) Φ hΦ

end Work.BoseC3QAll

/-! ## The design's name for the deliverable

`Submission/Work/BOSE_ALL_STATEMENTS.lean.txt` §"item 5 glue" states the
deliverable *inside* `namespace Work.BoseBoxFock` as

    theorem control3QFSAll (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) : Control3QFSAll K₀ b₀ hb₀

(the file `AllDefs.lean` itself lands only the *vocabulary*, not this glue, and
is frozen).  This file declares that name from here — it is the item D2 name, so
no other area declares it — so that the D3/D4 consumers can use
`Work.BoseBoxFock.control3QFSAll` exactly as the design writes it, in addition
to the area-local `Work.BoseC3QAll.control3QFSAll` above. -/
namespace Work.BoseBoxFock

/-- Design item D2, under the design's own name (see the note above). -/
theorem control3QFSAll (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) : Control3QFSAll K₀ b₀ hb₀ :=
  Work.BoseC3QAll.control3QFSAll K₀ b₀ hb₀

/-- The gate bridge under the design's namespace (the port of
`Work.BoseB7AK.C3Q.Q3KernelFS_bridge`): the frozen gate gives the ported one. -/
theorem q3KernelFSAll_of_frozen {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {K₀ : ℝ} {F : Work.BoseB7.FockData Mode}
    {T : Work.BoseB7A.TildeData F} {E : Work.BoseB7.Q3Env Mode}
    (h : Q3KernelFSAll K₀ F T E) : Work.BoseC3QAll.Q3KernelFSAll K₀ F T E :=
  Work.BoseC3QAll.q3KernelFSAll_of_frozen h

end Work.BoseBoxFock
