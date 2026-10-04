import Mathlib
import Submission.Work.Diff.Alg.Pinch.Chat_shift_base
import Submission.Work.Diff.Alg.Pinch.RoomAux.RFAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The shifted strictness property of the Brendle–Schoen family

Vocabulary shared by the assembly of `Work.Diff.Alg.Pinch.Chat_room_global` and its helper
lemmas.  `ShiftStrict n s ĉ X` says that for the point `X ∈ Ĉ(s)` with `scalAlg X = 1`, the
"shifted reaction direction" `Q (X - ĉ • Iso n)` is *strictly* positive on

* every direction `v` on which the Ricci-pinching form of the cone's preimage
  `chatLinv n s X` is tight, and
* every direction `(x,y,z,w)` on which the complex-sectional-curvature form `Q2P.EFun` of the
  preimage vanishes (i.e. at the boundary of the `PIC2` cone).

These are exactly the hypotheses of the two general one-step lemmas
`Work.Diff.Alg.Pinch.ChatT_one_step_pic` and `Work.Diff.Alg.Pinch.RicPinch_one_step_of_strict`
applied to the preimage point `chatLinv n s X` and the direction
`chatLinv n s (Q (X - ĉ • Iso n))`.

## How the property is supposed to be used (and proved)

`ShiftStrict n s ĉ X` is *exactly* the pair of pointwise strictness hypotheses of the two
general one-step lemmas applied to `S := chatLinv n s X` (an element of `Dpic (chatPP n s)`)
and the direction `W := chatLinv n s (Q (X - ĉ • Iso n))`:

* `Work.Diff.Alg.Pinch.RicPinch_one_step_of_strict` (with `p = chatPP n s`), whose hypothesis is
  the first conjunct (the Ricci tight directions), and
* `Work.Diff.Alg.Pinch.ChatT_one_step_pic` (with `hP : InPIC2 S`), whose hypothesis is the second
  conjunct (the degenerate directions of the quartic form `Q2P.EFun`).

The `ĉ = 0` case is *proved* in the workspace: `Work.Diff.Alg.Pinch.EFun_X_strict_at_degenerate`
(branch `0 < b ≤ 1/2`, parameters `ccA n b`, `ccP n b`) and
`..._a` (branch `1/2 < a`, parameters `a`, `1/2`, `1 - 4/((n-2)+8a)`) for the `PIC2` half, and
`Work.Diff.Alg.Pinch.ricForm_X_strict_at_tight` / `..._a` for the Ricci half.  Note
`Chat n s = Ccone (chatAA n s) (chatBB s) (chatPP n s)` and
`chatAA n s = if s ≤ 1/2 then chatA n s else s`, `chatBB s = if s ≤ 1/2 then s else 1/2`,
`chatPP n s = if s ≤ 1/2 then chatP n s else 1 - 4/((n-2)+8s)`.

⚠ Import hygiene: the branch `b ≤ 1/2` Ric-form strictness lives in
`Work.Diff.Alg.Pinch.RicFormAux`, which *clashes* with `RicFormDefs` (both declare
`qform_ric0`, `ricForm`, ...).  A clash-free copy of that file, wrapped in the namespace
`Work.Diff.Alg.Pinch.RFAux`, is provided as `Submission.Work.Diff.Alg.Pinch.RoomAux.RFAux`
(importable *together* with the second-branch files); the first-branch Ric statement is
`RFAux.ric_X_strict_aux`.

Typical route for a *bounded* range of `s` (compactness): the set of `(s, X, (x,y,z,w))` with
`s` in the range, `X ∈ Chat n s`, `scalAlg X = 1` and `Q2P.EFun (chatLinv n s X) (x,y,z,w) = 0`
is compact (the slices are closed and bounded, see `chat_norm_le_scalAlg` /
`chat_norm_le_scalAlg_uniform`, and the family of cones is closed in `(s, X)`); the quantity
`Q2P.EFun (chatLinv n s (Q (X - ĉ • Iso n))) (x,y,z,w)` is continuous in `(s, X, ·, ĉ)` and
strictly positive at `ĉ = 0`; a contradiction-sequence argument with `ĉ → 0+` then gives a
positive uniform `ĉ₀`.  The same works for the Ricci half with
`∑ᵢⱼ ric S i j vᵢ vⱼ - (p/n) scal S ∑ᵢ vᵢ²` evaluated at `S = chatLinv n s X` and at
`S = chatLinv n s (Q (X - ĉ • Iso n))` on `{v : ∑ vᵢ² = 1}`.
-/

namespace Work.Diff.Alg.Pinch

/-- The shifted strictness property at `(s, ĉ, X)`. -/
def ShiftStrict (n : ℕ) (s ĉ : ℝ) (X : Submission.Diff.Alg.Curv4 n) : Prop :=
  (∀ v : Fin n → ℝ, v ≠ 0 →
      (chatPP n s * Submission.Diff.Alg.scalAlg (chatLinv n s X) / (n : ℝ))
          * (∑ i, v i * v i)
        = ∑ i, ∑ j, (ric (chatLinv n s X) i j * v i * v j) →
      (chatPP n s * Submission.Diff.Alg.scalAlg
            (chatLinv n s (Submission.Diff.Alg.Q (X - ĉ • Submission.Diff.Alg.Iso n))) / (n : ℝ))
          * (∑ i, v i * v i)
        < ∑ i, ∑ j, (ric (chatLinv n s (Submission.Diff.Alg.Q (X - ĉ • Submission.Diff.Alg.Iso n)))
              i j * v i * v j))
  ∧ (∀ x y z w : Fin n → ℝ,
      Work.Diff.Alg.Q2P.EFun (chatLinv n s X) x y z w = 0 →
      Work.Diff.Alg.Q2P.EFun (Submission.Diff.Alg.Iso n) x y z w ≠ 0 →
      0 < Work.Diff.Alg.Q2P.EFun
            (chatLinv n s (Submission.Diff.Alg.Q (X - ĉ • Submission.Diff.Alg.Iso n)))
            x y z w)

end Work.Diff.Alg.Pinch
