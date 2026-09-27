import Mathlib
import Submission.Work.Cohomology.MVH
import Submission.Work.Cohomology.MVApply

open CategoryTheory Simplicial Opposite
open Submission.Cohomology

set_option backward.isDefEq.respectTransparency.types false

namespace Work.Cohomology

/-- The class of a cocycle vanishes in cohomology if and only if the cocycle is a coboundary. -/
private lemma H_mk_eq_zero {S : SSet.{0}} {R : Type} [CommRing R] {n : ℕ}
    (u : Cochain S R n) (hu : u ∈ cycles S R n) :
    H.mk u hu = 0 ↔ u ∈ boundaries S R n := by
  rw [show (0 : H S R n) = H.mk 0 (Submodule.zero_mem _) from rfl, H.mk_eq_mk_iff, sub_zero]

/-- **Exactness of the Mayer–Vietoris sequence at `H^{j+1}(S)`**: the kernel of the restriction map
`mvAlphaH S A B (j+1)` is the range of the connecting map `mvConnecting S A B hAB j`.

`range ⊆ ker` is immediate from the defining identity `mvAlpha_mvDeltaRep`: the two restrictions of
`mvDeltaRep c` are the two components of `mvD (mvLift c)`, hence coboundaries.

For `ker ⊆ range`, let `x = H.mk u hu` with `mvAlphaH (j+1) x = 0`.  Then the restrictions of `u` to
`A` and to `B` are coboundaries, say `pullbackCo A.ι u = coboundary a'` and
`pullbackCo B.ι u = coboundary b'` (here `j+1 ≥ 1` is used).  Put `c := mvBeta S A B j (a',b')`; it
is a cocycle of `A ∩ B` because `coboundary c = mvBeta (mvD (a',b')) = mvBeta (mvAlpha u) = 0`.
Since `mvBeta (mvLift c) = c = mvBeta (a',b')`, we have `mvLift c - (a',b') = mvAlpha w` for some
`w` by exactness, and then `mvDeltaRep c = mvProj (mvD (mvLift c)) = u + coboundary w`, so
`mvConnecting (H.mk c hc) = H.mk (mvDeltaRep c) = H.mk u hu = x`. -/
theorem mvAlphaH_ker_eq_range (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (j : ℕ) :
    LinearMap.ker (Submission.Cohomology.mvAlphaH S A B (j+1))
      = (Submission.Cohomology.mvConnecting S A B hAB j).range := by
  apply le_antisymm
  · -- `ker ≤ range`: the snake-lemma (connecting map) construction.
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [LinearMap.mem_range]
    obtain ⟨u, hu, hxu⟩ : ∃ u : Cochain S ℚ (j+1),
        ∃ hu : u ∈ cycles S ℚ (j+1), H.mk u hu = x :=
      ⟨(Quot.out x).1, (Quot.out x).2, Quot.out_eq x⟩
    -- the two restrictions of `u` are coboundaries
    have hAb : pullbackCo ℚ A.ι u ∈ boundaries A ℚ (j+1) := by
      have h := congrArg Prod.fst hx
      simp only [mvAlphaH_apply] at h
      rw [← hxu, H.map_mk] at h
      have h3 := (H.mk_eq_mk_iff (pullbackCo ℚ A.ι u) 0
        (pullbackCo_mem_cycles A.ι hu) (Submodule.zero_mem _)).mp h
      rwa [sub_zero] at h3
    have hBb : pullbackCo ℚ B.ι u ∈ boundaries B ℚ (j+1) := by
      have h := congrArg Prod.snd hx
      simp only [mvAlphaH_apply] at h
      rw [← hxu, H.map_mk] at h
      have h3 := (H.mk_eq_mk_iff (pullbackCo ℚ B.ι u) 0
        (pullbackCo_mem_cycles B.ι hu) (Submodule.zero_mem _)).mp h
      rwa [sub_zero] at h3
    obtain ⟨a', ha'⟩ := (mem_boundaries_succ (pullbackCo ℚ A.ι u)).mp hAb
    obtain ⟨b', hb'⟩ := (mem_boundaries_succ (pullbackCo ℚ B.ι u)).mp hBb
    -- `mvD (a',b')` is the pair of restrictions of `u`
    have hDab : mvD S A B j (a', b') = mvAlpha S A B (j+1) u := by
      apply Prod.ext
      · simp only [mvD_fst, mvAlpha_fst]; exact ha'
      · simp only [mvD_snd, mvAlpha_snd]; exact hb'
    -- the gluing is a cocycle of `A ∩ B`
    set c : Cochain (A ⊓ B : S.Subcomplex) ℚ j := mvBeta S A B j (a', b') with hc_def
    have hc : c ∈ cycles (A ⊓ B : S.Subcomplex) ℚ j := by
      rw [mem_cycles_iff, hc_def, ← mvBeta_coboundary, hDab]
      have := congrArg (fun f => f u) (mvBeta_comp_mvAlpha S A B (j + 1))
      simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using this
    -- `mvLift c` and `(a',b')` differ by an element of the range of `mvAlpha`
    have hker : mvLift S A B j c - (a', b') ∈ LinearMap.ker (mvBeta S A B j) := by
      rw [LinearMap.mem_ker, map_sub, mvBeta_mvLift, hc_def, sub_self]
    rw [mvExact S A B hAB j] at hker
    obtain ⟨w, hw⟩ := hker
    have hsplit : mvLift S A B j c = mvAlpha S A B j w + (a', b') := by
      rw [hw]; abel
    -- the differential of the lift, pushed to `S`
    have key : mvD S A B j (mvLift S A B j c)
        = mvAlpha S A B (j+1) (u + coboundary S ℚ j w) := by
      rw [hsplit, map_add, ← mvAlpha_coboundary, hDab, ← map_add]
      congr 1
      ring
    have key2 : mvDeltaRep S A B hAB j c = u + coboundary S ℚ j w := by
      show mvProj S A B hAB (j+1) (mvD S A B j (mvLift S A B j c)) = _
      rw [key, mvProj_mvAlpha]
    refine ⟨H.mk c hc, ?_⟩
    rw [mvConnecting_mk, ← hxu]
    rw [H.mk_eq_mk_iff]
    have hdiff : mvDeltaRep S A B hAB j c - u = coboundary S ℚ j w := by
      rw [key2]; abel
    rw [hdiff]
    exact (mem_boundaries_succ (coboundary S ℚ j w)).mpr ⟨w, rfl⟩
  · -- `range ≤ ker`: the two restrictions of the connecting map vanish.
    rintro y hy
    rw [LinearMap.mem_range] at hy
    obtain ⟨z, rfl⟩ := hy
    rw [LinearMap.mem_ker]
    obtain ⟨c, hc, hzc⟩ : ∃ c : Cochain (A ⊓ B : S.Subcomplex) ℚ j,
        ∃ hc : c ∈ cycles (A ⊓ B : S.Subcomplex) ℚ j, H.mk c hc = z :=
      ⟨(Quot.out z).1, (Quot.out z).2, Quot.out_eq z⟩
    rw [← hzc, mvConnecting_mk]
    rw [mvAlphaH_apply]
    apply Prod.ext
    · rw [H.map_mk]
      apply (H_mk_eq_zero _ _).mpr
      rw [mem_boundaries_succ]
      refine ⟨(mvLift S A B j c).1, ?_⟩
      have h := congrArg Prod.fst (mvAlpha_mvDeltaRep S A B hAB j
        (fun i => mvExact S A B hAB i) hc)
      simp only [mvAlpha_fst, mvD_fst] at h
      exact h.symm
    · rw [H.map_mk]
      apply (H_mk_eq_zero _ _).mpr
      rw [mem_boundaries_succ]
      refine ⟨(mvLift S A B j c).2, ?_⟩
      have h := congrArg Prod.snd (mvAlpha_mvDeltaRep S A B hAB j
        (fun i => mvExact S A B hAB i) hc)
      simp only [mvAlpha_snd, mvD_snd] at h
      exact h.symm

end Work.Cohomology
