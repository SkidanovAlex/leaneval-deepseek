import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.Tools

/-!
# A complete source for `HondaReciprocity`: the degenerate instance over `ℝ`

`NK.LocalReciprocityLubinTate.HondaReciprocity F π U q` is

`∀ n ≥ 1, N_{F(Λ_n)/F} F(Λ_n)ˣ = ⟨π⟩ · U^n`

with `Λ_n` the `π^n`-division points of the standard Lubin–Tate polynomial `πT + T^q`
(`Unramified/Basic.lean`).  It is the chapter's named classical residue.

This file records a *complete* (`n`-indexed) instance of the statement, over the real field `ℝ`,
with the uniformiser `π = 1` and the (rigged) filtration `U n` taken to be the norm group of the
level itself.  Since `⟨1⟩ = ⊥`, the identity holds by definition; the purpose is to exhibit that
the *shape* of `HondaReciprocity` (quantifiers, the level `LTLevel`, the norm group) is satisfiable
and cannot be refuted, complementing the *substantive* level-one witness

`NK.LocalReciprocityLubinTate.Audit.hondaReciprocity_level_one_residueCard_two`

at `q = 2`, where both sides of the identity are computed independently.

## Main result

* `NK.LocalReciprocityLubinTate.Audit.hondaReciprocity_real`
-/

namespace NK.LocalReciprocityLubinTate.Audit

/-- **A rigged complete source for `HondaReciprocity`.**  Over `ℝ`, with `π = 1`, `q = 2` and the
filtration `U n` equal to the norm group `N_{ℝ(Λ_n)/ℝ} ℝ(Λ_n)ˣ` of the level itself, the identity
`N = ⟨1⟩ · U` holds because `⟨1⟩ = ⊥`. -/
theorem hondaReciprocity_real :
    NK.LocalReciprocityLubinTate.HondaReciprocity ℝ 1
      (fun n => NK.LocalReciprocity.normGroup ℝ
        ↥(NK.LocalReciprocityLubinTate.LTLevel ℝ (1 : ℝ) 2 n)) 2 := by
  intro n _
  rw [Subgroup.zpowers_one_eq_bot, bot_sup_eq]
  simp only [Units.val_one]

end NK.LocalReciprocityLubinTate.Audit
