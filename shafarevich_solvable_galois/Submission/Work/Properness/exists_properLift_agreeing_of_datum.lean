/-
Copyright (c) 2025. All rights reserved.

# A proper solution of an embedding problem agreeing with prescribed local data

This file sharpens `Work.Properness.exists_properLift_of_datum`: not only does a Grunwald–Wang
datum produce *some* proper solution, the solution produced from the datum can be chosen so that it
takes on the prescribed values `φ i` on the subgroups `T i ≤ H_K`.

We recall the setting: `S` is the abstract embedding problem with abelian kernel
(`Work.Properness.Setup`), `ψ₀ : S.Lift` is a plain solution, `T i ≤ S.HK` are subgroups of
`H_K = ker ρ` and `φ i : T i →* S.A` prescribes the local behaviour.  The hypothesis
`S.GrunwaldWangDatum ψ₀ T hT φ` is the conclusion of the Grunwald–Wang step: it provides a
`1`-cocycle `x ∈ Z¹(H, A)` with `x(t) = φ i t · (ψ₀ t)⁻¹` for `t ∈ T i`.

The lift `ψ = x · ψ₀` (`Work.Properness.exists_lift_of_mulFun`) then satisfies
`ψ t = φ i t` for all `t ∈ T i` (`Work.Properness.liftOfDatum_apply_eq`), so that
`(T i).map ψ = (φ i).range` (`Work.Properness.map_T_liftOfDatum`).  If moreover the local images
generate the whole kernel, `⨆ i, (φ i).range = ⊤`, then `ψ(H_K) = A`
(`Work.Properness.isProper_of_iSup_map_eq`), i.e. `ψ` is a **proper** solution.

## Main declaration

* `Work.Properness.exists_properLift_agreeing_of_datum` — the requested theorem.
-/
import Mathlib
import Submission.Work.Properness.Defs
import Submission.Work.Properness.exists_properLift_of_datum
import Submission.Work.Properness.exists_lift_mulFun
import Submission.Work.Properness.isProper_of_iSup_map_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

-- The requested statement binds `{u v w : Universe}`.  `Universe` is not a Lean 4 keyword, so it
-- is an implicitly bound variable and the statement only elaborates with `autoImplicit` enabled;
-- this is exactly what the sibling files `Submission/Work/Properness/exists_properLift_of_datum.lean`
-- and `Submission/Work/Properness/isProper_of_iSup_map_eq.lean` do.  The statement itself is kept
-- verbatim.
set_option autoImplicit true
set_option linter.unusedVariables false

namespace Work.Properness

/-- **A proper solution agreeing with prescribed local data.**

Let `ψ₀` be a lift, `T i ≤ H_K` subgroups and `φ i : T i →* A` homomorphisms whose images generate
the whole kernel, `⨆ i, (φ i).range = ⊤`.  If the Grunwald–Wang datum `S.GrunwaldWangDatum ψ₀ T hT φ`
is available — that is, some global `1`-cocycle `x ∈ Z¹(H, A)` realizes the differences
`φ i - ψ₀|_{T i}` — then there is a lift `ψ` of the embedding problem which is **proper**
(`ψ` is surjective) and which agrees with the prescribed data:

`ψ t = φ i t` for every `i` and every `t ∈ T i`.

The lift is the explicit `ψ = x · ψ₀`: it is a lift by
`Work.Properness.exists_lift_of_mulFun`, it agrees with `φ i` on `T i` by
`Work.Properness.liftOfDatum_apply_eq`, and it is surjective because
`A = (⊤ : Subgroup A).map A.subtype = (⨆ i, (φ i).range).map A.subtype
   = ⨆ i, (T i).map ψ ≤ H_K.map ψ ≤ A`. -/
theorem exists_properLift_agreeing_of_datum {u v w : Universe} {S : Work.Properness.Setup.{u, v, w}} {ι : Type*} [Fintype ι] (ψ₀ : S.Lift) (T : ι → Subgroup S.H) (hT : ∀ i, T i ≤ S.HK) (φ : ∀ i, T i →* S.A) (hdat : S.GrunwaldWangDatum ψ₀ T hT φ) (hgen : (⨆ i, (φ i).range) = ⊤) : ∃ ψ : S.Lift, S.IsProper ψ ∧ ∀ (i : ι) (t : T i), (ψ : S.H → S.E) (t : S.H) = (φ i t : S.E) := by
  obtain ⟨x, hx⟩ := hdat
  obtain ⟨ψ, hψ⟩ := Work.Properness.exists_lift_of_mulFun ψ₀ x
  refine ⟨ψ, ?_, ?_⟩
  · rw [Work.Properness.isProper_iff_map_HK_eq_A_aux ψ]
    refine le_antisymm (S.map_HK_le_A ψ) ?_
    have hA : S.A = (⊤ : Subgroup S.A).map (S.A).subtype := by
      rw [← MonoidHom.range_eq_map]
      exact (Subgroup.range_subtype (S.A)).symm
    calc S.A = (⊤ : Subgroup S.A).map (S.A).subtype := hA
      _ = ((⨆ i, (φ i).range)).map (S.A).subtype := by rw [hgen]
      _ = ⨆ i, ((φ i).range).map (S.A).subtype :=
          Subgroup.map_iSup (S.A).subtype (fun i => (φ i).range)
      _ = ⨆ i, (T i).map ψ.1 :=
          iSup_congr (fun i => (Work.Properness.map_T_liftOfDatum hT hx hψ i).symm)
      _ ≤ S.HK.map ψ.1 := iSup_le (fun i => Subgroup.map_mono (hT i))
  · intro i t
    exact Work.Properness.liftOfDatum_apply_eq hT hx hψ i t

end Work.Properness
