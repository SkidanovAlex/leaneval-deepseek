import Mathlib
import Submission.Work.Properness.Defs
import Submission.Work.Properness.isProper_iff_map_HK_eq_A
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

-- The library is built with `autoImplicit = false`; the target statement (written by the
-- requester) uses the auto-bound identifier `Universe` together with auto-bound universe levels,
-- so we enable `autoImplicit` locally in order to elaborate it *exactly* as stated.  (This is what
-- the sibling file `isProper_iff_map_HK_eq_A.lean` does as well.)
set_option autoImplicit true
set_option linter.unusedVariables false

namespace Work.Properness

/-- **Properness from generators lying in `H_K`.**

If a family of subgroups `T i ≤ H_K` of the "decomposition groups" is such that the images
`ψ(T i)` generate the whole kernel `A = ker π`, then the lift `ψ` is proper (surjective).

Indeed `T i ≤ H_K` gives `(T i).map ψ.1 ≤ S.HK.map ψ.1` for each `i`, hence
`A = ⨆ i, (T i).map ψ.1 ≤ S.HK.map ψ.1`; combined with the unconditional inclusion
`S.HK.map ψ.1 ≤ A` (`Setup.map_HK_le_A`) this yields `S.HK.map ψ.1 = A`, and
`Setup.isProper_iff_map_HK_eq_A` converts the latter into surjectivity of `ψ`. -/
theorem isProper_of_iSup_map_eq {u v w : Universe} {S : Work.Properness.Setup.{u, v, w}} {ι : Type*} (ψ : S.Lift) (T : ι → Subgroup S.H) (hT : ∀ i, T i ≤ S.HK) (hgen : (⨆ i, (T i).map ψ.1) = S.A) : S.IsProper ψ := by
  rw [isProper_iff_map_HK_eq_A_aux ψ]
  apply le_antisymm (S.map_HK_le_A ψ)
  rw [← hgen]
  exact iSup_le (fun i => Subgroup.map_mono (hT i))

end Work.Properness
