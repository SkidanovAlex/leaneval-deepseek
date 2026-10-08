/-
# BMAX — GW design 18, §C: the "mixed case" of Bender 1970, 1.7(iii) is impossible

This file implements, inside area BMAX, the two leaves and the mixed-case argument of
`Submission/Work/NOTES_LEAD_gw_design18.md` §C (the lead's sketch is
`Submission/Work/_design_gw/Core18MixedAbsurd.lean`; the declarations below are this area's
own copies so that BMAX's deliverable does not depend on a file it does not own).

Mathematically: in `Bender17iiiCond`'s mixed case, `F*(A)` is not a `p`-group while `F*(B)`
*is* a `q`-group.  But the witness of `A ⇝ B` gives `E(A) ≤ B`, and 1.7(i) gives
`F*(B) ≤ A`; so `F*(B)` is an `E(A)`-invariant solvable subgroup of `A` normalizing `E(A)`,
whence `E(A)` centralizes it
(`Work.BMAX.layerIn_le_centralizer_of_solvable`, Bender 1970 p. 165: "any `E`-invariant
solvable subgroup of `X` is centralized by `E`"), and
`E(A) ≤ C_B(F*(B)) ≤ F*(B)` (`centralizer_fstarIn_inf_le'`, i.e. `T.fstar` for the D-group
`B`) — a `q`-group.  Hence `E(A) = ⊥`, and the "layer case" of Bender's local analysis
(`Work.GW2.LayerDedekindProp`) is **not** needed at all: the mixed case is empty.

* `le_normalizer_fstarIn` — `K ≤ N_G(F*(K))` (design leaf C-a);
* `layerIn_eq_bot_of_le_pGroup` — a layer inside a `q`-group is trivial (design leaf C-b);
* `layerIn_eq_bot_of_mixed` — the mixed case forces `E(A) = ⊥`.
-/
import Mathlib
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.Basic
import Submission.Work.BMAX.centralizer_pResidualIn_witness_le
import Submission.Work.BMAX.layerIn_le_centralizer_of_solvable
import Submission.Work.BMAX.GWPiEq

namespace Work.BMAX

open Subgroup

/-- **Design leaf C-a.**  `F*(K) = F(K)·E(K)` is normal in `K`, hence `K` normalizes it. -/
theorem le_normalizer_fstarIn {G : Type} [Group G] (K : Subgroup G) :
    K ≤ Subgroup.normalizer ((Work.GW2.fstarIn K : Subgroup G) : Set G) := by
  have hFn : (Work.GW2.fitting K).Normal := by
    rw [Work.GW2.fitting]; exact Subgroup.normalCore_normal _
  have hLn : (Work.GW2.layer K).Normal :=
    Subgroup.sSup_normal _ (fun _ hH => hH.1)
  have hfsn : (Work.GW2.fstar K).Normal := by
    rw [Work.GW2.fstar]; exact inferInstance
  rw [Work.GW2.fstarIn]
  exact le_normalizer_map_subtype_of_normal hfsn

/-- **Design leaf C-b.**  A subgroup of a `q`-group contains no non-trivial quasisimple
subgroup, so `E(A) = 1` whenever `E(A) ≤ K` with `K` a `q`-group.  (Same argument as
`Work.BMAX.layerIn_eq_bot_of_isPGroup_fstarIn`: a quasisimple `E` is perfect, hence not
nilpotent, hence not a subgroup of a finite `q`-group.) -/
theorem layerIn_eq_bot_of_le_pGroup {G : Type} [Group G] [Finite G] (A K : Subgroup G)
    (q : ℕ) [Fact q.Prime] (h : Work.GW2.layerIn A ≤ K) (hK : IsPGroup q K) :
    Work.GW2.layerIn A = ⊥ := by
  have hlay : Work.GW2.layer A = ⊥ := by
    rw [Work.GW2.layer]
    refine eq_bot_iff.mpr (sSup_le ?_)
    rintro E ⟨hEn, hEq⟩
    have hEle : E.map A.subtype ≤ K :=
      le_trans (Subgroup.map_mono (le_sSup
        (show E ∈ {F : Subgroup ↥A | F.Normal ∧ Work.GW2.IsQuasisimple F} from ⟨hEn, hEq⟩))) h
    refine le_bot_iff.mpr ?_
    by_contra hne
    haveI : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).mpr hne
    haveI : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hEq.1
    have hPE : IsPGroup q ↥E :=
      IsPGroup.of_equiv (IsPGroup.to_le hK hEle)
        (Subgroup.equivMapOfInjective E A.subtype A.subtype_injective).symm
    exact (Group.IsPerfect.not_isNilpotent ↥E) (IsPGroup.isNilpotent hPE)
  rw [Work.GW2.layerIn, hlay, Subgroup.map_bot]

/-- **The mixed case is empty.**  If `F*(B)` is a `q`-group, `E(A) ≤ B` and `F*(B) ≤ A`,
then `E(A) = ⊥`.  (No Dedekind-type hypothesis on `F(A)` is needed.) -/
theorem layerIn_eq_bot_of_mixed {G : Type} [Group G] [Finite G] (T : Work.GW2.LocalToolkit)
    (A B : Subgroup G) (hBsyl : Work.GW2.DihOrCycSylow B) (hDB : Work.GW2.IsDGroup B)
    (q : ℕ) (hq : q.Prime) (hPqB : IsPGroup q (Work.GW2.fstarIn B))
    (hEA : Work.GW2.layerIn A ≤ B) (hFB : Work.GW2.fstarIn B ≤ A) :
    Work.GW2.layerIn A = ⊥ := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hsolv : Group.IsSolvable ↥(Work.GW2.fstarIn B) := by
    haveI : Group.IsNilpotent ↥(Work.GW2.fstarIn B) := hPqB.isNilpotent
    infer_instance
  have hLn : Work.GW2.fstarIn B ≤
      Subgroup.normalizer ((Work.GW2.layerIn A : Subgroup G) : Set G) :=
    hFB.trans (le_normalizer_layerIn A)
  have hEn : Work.GW2.layerIn A ≤
      Subgroup.normalizer ((Work.GW2.fstarIn B : Subgroup G) : Set G) :=
    hEA.trans (le_normalizer_fstarIn B)
  have hcent : Work.GW2.layerIn A ≤
      Subgroup.centralizer ((Work.GW2.fstarIn B : Subgroup G) : Set G) :=
    layerIn_le_centralizer_of_solvable hsolv hLn hEn
  have hle : Work.GW2.layerIn A ≤ Work.GW2.fstarIn B :=
    (le_inf hcent hEA).trans (centralizer_fstarIn_inf_le' T B hBsyl hDB)
  exact layerIn_eq_bot_of_le_pGroup A (Work.GW2.fstarIn B) q hle hPqB

end Work.BMAX
