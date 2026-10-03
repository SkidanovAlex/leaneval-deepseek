import Mathlib
import Submission.Work.ORLyndon.mmHi_mem_relatorLetters
import Submission.Work.ORLyndon.lyndonIndependence_eps_zero_mm_bot
import Submission.Work.OROneRel.magnus_step_root
import Submission.Work.OROneRel.relatorLetters_pow_subset

namespace Work.ORLyndon

universe u

theorem mmBotSym_mem_relatorLetters {α : Type u} [DecidableEq α] (t : α) (u : FreeGroup α) (l : ℕ)
    (hu : Work.OROneRel.IsCyclicallyReducedRelator u) (he : Work.OROneRel.eps t u = 0)
    (hl : 1 ≤ l) (x : α) (hxt : x ≠ t) (hx : x ∈ Work.OROneRel.relatorLetters u) :
    Work.ORLyndon.mmBotSym t u l x hxt ∈
      Work.OROneRel.relatorLetters (Work.OROneRel.rootW t u l hu he hl) := by
  classical
  -- `u ^ l` is again a cyclically reduced word of exponent sum zero in `t`.
  have he' : Work.OROneRel.eps t (u ^ l) = 0 := by
    rw [← zpow_natCast u l, Work.OROneRel.epsc_zpow, he, mul_zero]
  have hcyc' : Work.OROneRel.IsCyclicallyReducedRelator (u ^ l) :=
    Work.OROneRel.isCyclicallyReducedRelator_pow hu l
  have hred : FreeGroup.IsReduced (Work.OROneRel.mmWL t (u ^ l)) :=
    Work.OROneRel.mmWL_isReduced t (u ^ l) hcyc' he'
  -- An occurrence of `x` in the Magnus rewriting of `u ^ l`.
  have hne : (Work.OROneRel.mmDecs t (u ^ l) ⟨x, hxt⟩).Nonempty := by
    rw [Work.OROneRel.mmDecs_pow t u hu he l hl ⟨x, hxt⟩]
    exact mmDecs_nonempty_of_mem_relatorLetters t u ⟨x, hxt⟩ hx
  obtain ⟨b, hb⟩ := Work.OROneRel.exists_mmLo t (u ^ l) hne
  -- The bottom symbol of `x` occurs in the Magnus rewriting of `u ^ l`.
  have hmemWL : ((mmBotSym t u l x hxt : Work.OROneRel.mmBeta t (u ^ l)), b) ∈
      Work.OROneRel.mmWL t (u ^ l) := by
    rw [show Work.OROneRel.mmWL t (u ^ l) = (Work.OROneRel.mmList t (u ^ l)).map
        (fun p => (Work.OROneRel.mmBetaOf t (u ^ l) p.1, p.2)) from by rw [Work.OROneRel.mmWL]]
    refine List.mem_map.mpr ⟨_, hb, ?_⟩
    refine Prod.ext ?_ rfl
    refine Subtype.ext ?_
    rw [Work.OROneRel.mmBetaOf_val t (u ^ l)
      (Work.OROneRel.mmLo_mem_decSet t (u ^ l) ⟨x, hxt⟩)]
    exact (mmBotSym_val t u l x hxt).symm
  have hmem : mmBotSym t u l x hxt ∈
      Work.OROneRel.relatorLetters (Work.OROneRel.mmW t (u ^ l)) :=
    (Work.OROneRel.mem_relatorLetters_mmW hred (mmBotSym t u l x hxt)).mpr ⟨b, hmemWL⟩
  -- Transport along `rootW ^ l = mmW t (u ^ l)`.
  have hsub := Work.OROneRel.relatorLetters_pow_subset
    (Work.OROneRel.rootW t u l hu he hl) l
  rw [Work.OROneRel.rootW_pow t u l hu he hl] at hsub
  exact hsub hmem

end Work.ORLyndon
