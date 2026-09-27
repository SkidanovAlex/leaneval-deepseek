import Mathlib
import Submission.Work.Cohomology.MVApply

open CategoryTheory Simplicial Opposite
open Submission.Cohomology

namespace Work.Cohomology

/-- **The connecting map of the Mayer–Vietoris sequence is surjective when the two pieces are
acyclic one degree higher.**  For subcomplexes `A, B` with `A ⊔ B = ⊤`, if `H A ℚ (k+1)` and
`H B ℚ (k+1)` are subsingletons then `mvConnecting S A B hAB k : H (A ∩ B) ℚ k → H S ℚ (k+1)` is
surjective.

Proof plan.  Let `y : H S ℚ (k+1)`, written `y = H.mk ε hε`.  Put `a := pullbackCo ℚ A.ι ε` and
`b := pullbackCo ℚ B.ι ε`: these are cocycles of `A` and `B` in degree `k+1`, hence coboundaries
`a = coboundary A ℚ k a'`, `b = coboundary B ℚ k b'` by
`Submission.Cohomology.mem_boundaries_of_subsingleton` (using the two subsingleton hypotheses).
Let `c := mvBeta S A B k (a', b')`.  Then `c` is a cocycle of `A ∩ B` in degree `k`, since
`coboundary (A ∩ B) ℚ k c = mvBeta S A B (k+1) (mvD S A B k (a',b'))` (by `mvBeta_coboundary`)
`= mvBeta S A B (k+1) (mvAlpha S A B (k+1) ε)` (by the definitions of `a` and `b` and `mvD_fst`/
`mvD_snd`) `= 0` (`mvBeta_comp_mvAlpha`).  Finally `mvConnecting_mk` reduces the goal to
`mvDeltaRep S A B hAB k c` being cohomologous to `ε` on `S`: indeed
`mvLift S A B k c - (a',b') ∈ LinearMap.ker (mvBeta S A B k) = (mvAlpha S A B k).range`
(using `mvBeta_mvLift` and `mvBeta_ker_eq_range`, available here as `mvExact`), say it is
`mvAlpha S A B k w`; then `mvD S A B k (mvLift S A B k c) = mvD S A B k (a',b') + mvAlpha S A B (k+1)
(coboundary S ℚ k w) = mvAlpha S A B (k+1) (ε + coboundary S ℚ k w)` by `mvD_mvD` and
`mvAlpha_coboundary`, and applying `mvProj` to both sides (using `mvProj_mvAlpha` and
`mvAlpha_mvProj`) gives `mvDeltaRep S A B hAB k c = ε + coboundary S ℚ k w`, i.e. equal classes. -/
theorem mvConnecting_surjective (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (k : ℕ)
    (hA : Subsingleton (Submission.Cohomology.H A ℚ (k+1)))
    (hB : Subsingleton (Submission.Cohomology.H B ℚ (k+1))) :
    Function.Surjective (Submission.Cohomology.mvConnecting S A B hAB k) := by
  intro y
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (boundariesInCycles S ℚ (k+1)) y
  -- The restrictions of `z` to `A` and `B` are coboundaries, by acyclicity.
  obtain ⟨a', ha'⟩ := (mem_boundaries_succ (pullbackCo ℚ A.ι z.1)).mp
    (mem_boundaries_of_subsingleton A hA (pullbackCo_mem_cycles A.ι z.2))
  obtain ⟨b', hb'⟩ := (mem_boundaries_succ (pullbackCo ℚ B.ι z.1)).mp
    (mem_boundaries_of_subsingleton B hB (pullbackCo_mem_cycles B.ι z.2))
  -- `mvD (a',b')` is the pair of restrictions of `z`.
  have hDab : mvD S A B k (a', b') = mvAlpha S A B (k+1) z.1 := by
    apply Prod.ext
    · simp only [mvD_fst, mvAlpha_fst]; exact ha'
    · simp only [mvD_snd, mvAlpha_snd]; exact hb'
  -- The gluing `c` of `a'` and `b'` is a cocycle of `A ∩ B`.
  set c : Cochain (A ⊓ B : S.Subcomplex) ℚ k := mvBeta S A B k (a', b') with hc_def
  have hc : c ∈ cycles (A ⊓ B : S.Subcomplex) ℚ k := by
    rw [mem_cycles_iff, hc_def, ← mvBeta_coboundary, hDab]
    have := congrArg (fun f => f z.1) (mvBeta_comp_mvAlpha S A B (k + 1))
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using this
  -- `mvLift c` and `(a',b')` differ by an element of the range of `mvAlpha`.
  have hker : mvLift S A B k c - (a', b') ∈ LinearMap.ker (mvBeta S A B k) := by
    rw [LinearMap.mem_ker, map_sub, mvBeta_mvLift, hc_def, sub_self]
  rw [mvExact S A B hAB k] at hker
  obtain ⟨w, hw⟩ := hker
  have hsplit : mvLift S A B k c = mvAlpha S A B k w + (a', b') := by
    rw [hw]; abel
  -- The differential of the lift, pushed to `S`.
  have key : mvD S A B k (mvLift S A B k c)
      = mvAlpha S A B (k+1) (z.1 + coboundary S ℚ k w) := by
    rw [hsplit, map_add, ← mvAlpha_coboundary, hDab, ← map_add]
    congr 1
    ring
  have key2 : mvDeltaRep S A B hAB k c = z.1 + coboundary S ℚ k w := by
    show mvProj S A B hAB (k+1) (mvD S A B k (mvLift S A B k c)) = _
    rw [key, mvProj_mvAlpha]
  -- Conclusion: `mvDeltaRep c` and `z.1` differ by a coboundary.
  refine ⟨H.mk c hc, ?_⟩
  rw [mvConnecting_mk]
  change H.mk (mvDeltaRep S A B hAB k c) _ = H.mk z.1 z.2
  rw [H.mk_eq_mk_iff]
  have hdiff : mvDeltaRep S A B hAB k c - z.1 = coboundary S ℚ k w := by
    rw [key2]; abel
  rw [hdiff]
  exact LinearMap.mem_range_self _ _

end Work.Cohomology
