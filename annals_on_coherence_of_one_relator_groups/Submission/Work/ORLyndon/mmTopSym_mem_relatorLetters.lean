import Mathlib
import Submission.Work.ORLyndon.mmHi_mem_relatorLetters
import Submission.Work.ORLyndon.lyndonIndependence_eps_zero_mm
import Submission.Work.OROneRel.magnus_step_root
import Submission.Work.ORReductions.FreeGroupGens.freeGens_mem_range_map_iff

set_option autoImplicit false

universe u

namespace Work.ORLyndon

theorem mmTopSym_mem_relatorLetters {α : Type u} [DecidableEq α] (t : α) (u : FreeGroup α) (l : ℕ)
    (hu : Work.OROneRel.IsCyclicallyReducedRelator u) (he : Work.OROneRel.eps t u = 0)
    (hl : 1 ≤ l) (x : α) (hxt : x ≠ t) (hx : x ∈ Work.OROneRel.relatorLetters u) :
    Work.ORLyndon.mmTopSym t u l x hxt ∈
      Work.OROneRel.relatorLetters (Work.OROneRel.rootW t u l hu he hl) := by
  classical
  -- the top decorated letter `(x, mmHi t u x)` of `u` occurs in the Magnus rewriting `mmWL t u`
  obtain ⟨b, hb⟩ := Work.OROneRel.exists_mmHi t u
    (Work.ORLyndon.mmDecs_nonempty_of_mem_relatorLetters t u ⟨x, hxt⟩ hx)
  have hq0 : ((⟨((⟨x, hxt⟩ : {a : α // a ≠ t}), Work.OROneRel.mmHi t u ⟨x, hxt⟩),
        Work.OROneRel.mmHi_mem_decSet t u ⟨x, hxt⟩⟩ : Work.OROneRel.mmBeta t u), b)
      ∈ Work.OROneRel.mmWL t u := by
    rw [show Work.OROneRel.mmWL t u =
        (Work.OROneRel.mmList t u).map (fun p => (Work.OROneRel.mmBetaOf t u p.1, p.2)) from by
      rw [Work.OROneRel.mmWL]]
    refine List.mem_map.mpr ⟨((⟨x, hxt⟩, Work.OROneRel.mmHi t u ⟨x, hxt⟩), b), hb, ?_⟩
    refine Prod.ext ?_ rfl
    exact Subtype.ext (Work.OROneRel.mmBetaOf_val t u (Work.OROneRel.mmHi_mem_decSet t u ⟨x, hxt⟩))
  -- the transport of the decorated alphabet along `u ↦ u ^ l` is injective
  have hf : Function.Injective (Work.OROneRel.mmTransFun t u l hu he hl) := by
    intro a b hab
    refine Subtype.ext ?_
    have h := congrArg (fun e : Work.OROneRel.mmBeta t (u ^ l) =>
      (e : Work.OROneRel.MMAlpha t)) hab
    simpa [Work.OROneRel.mmTransFun] using h
  -- `rootW` is the image of the Magnus rewriting word under that transport
  have hroot : Work.OROneRel.rootW t u l hu he hl =
      FreeGroup.mk ((Work.OROneRel.mmWL t u).map
        (fun q => (Work.OROneRel.mmTransFun t u l hu he hl q.1, q.2))) := by
    rw [Work.OROneRel.rootW, Work.OROneRel.mmW, FreeGroup.map.mk]
  have hred : FreeGroup.IsReduced ((Work.OROneRel.mmWL t u).map
      (fun q => (Work.OROneRel.mmTransFun t u l hu he hl q.1, q.2))) :=
    Work.ORReductions.FreeGroupGens.isReduced_mapWord hf (Work.OROneRel.mmWL_isReduced t u hu he)
  have htw : (Work.OROneRel.rootW t u l hu he hl).toWord =
      (Work.OROneRel.mmWL t u).map
        (fun q => (Work.OROneRel.mmTransFun t u l hu he hl q.1, q.2)) := by
    rw [hroot, FreeGroup.toWord_mk, hred.reduce_eq]
  rw [Work.OROneRel.relatorLetters, Set.mem_ofPred_eq]
  refine ⟨b, ?_⟩
  rw [htw]
  refine List.mem_map.mpr ⟨_, hq0, ?_⟩
  refine Prod.ext ?_ rfl
  refine Subtype.ext ?_
  rw [Work.OROneRel.mmTransFun_val]
  show ((⟨x, hxt⟩, Work.OROneRel.mmHi t u ⟨x, hxt⟩) : Work.OROneRel.MMAlpha t) =
      ((⟨x, hxt⟩, Work.OROneRel.mmHi t (u ^ l) ⟨x, hxt⟩) : Work.OROneRel.MMAlpha t)
  rw [Work.OROneRel.mmHi_pow t u hu he l hl]

end Work.ORLyndon
