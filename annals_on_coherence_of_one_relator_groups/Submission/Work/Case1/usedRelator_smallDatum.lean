import Mathlib
import Submission.Work.Case1.SmallDatum
import Submission.Work.Case1.SmallPresentation

universe u v

namespace Work.Case1

open Work.ORLocInd.Howie

/-- `relInvOf` is a left inverse of `rel`: the position of the relator `rel P D r` is `r`. -/
theorem relInvOf_rel {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    {P : Presentation V} {v : V} {n : ℕ} (D : Datum P v n) (r : Fin (SmallPres.Nr P D))
    (h : SmallPres.rel P D r ∈ SmallPres.rels P D) :
    SmallPres.relInvOf P D (SmallPres.rel P D r) h = r := by
  have hsub : (⟨SmallPres.rel P D r, h⟩ : {i : P.ι // i ∈ SmallPres.rels P D}) =
      SmallPres.rIso P D r := Subtype.ext rfl
  show (SmallPres.rIso P D).symm ⟨SmallPres.rel P D r, h⟩ = r
  rw [hsub]
  exact OrderIso.symm_apply_apply _ _

theorem usedRelator_smallDatum {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    {W : Type u} (S : Work.Case1.Skel V W) (P : Work.ORLocInd.Howie.Presentation V) {v : V} {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n) (hrel : ∀ i : P.ι, Work.ORLocInd.Howie.UsedRelator D i) :
    ∀ i : (Work.Case1.SmallPres.smallPresentation S P D hrel).ι,
      Work.ORLocInd.Howie.UsedRelator (Work.Case1.SmallDatum.smallDatum S P D hrel) i := by
  intro i
  obtain ⟨r⟩ := i
  obtain ⟨j, t, ht, hti⟩ := SmallPres.mem_rels.mp (SmallPres.rIso P D r).2
  refine ⟨j, SmallDatum.smallTerm S P D hrel t ht, ?_, ?_⟩
  · show SmallDatum.smallTerm S P D hrel t ht ∈ SmallDatum.smallTerms S P D hrel j
    exact List.mem_map.mpr ⟨⟨t, ht⟩, List.mem_attach _ _, rfl⟩
  · refine congrArg ULift.up ?_
    have hsub : (⟨t.i, SmallPres.term_i_mem_rels ht⟩ : {i : P.ι // i ∈ SmallPres.rels P D}) =
        SmallPres.rIso P D r := Subtype.ext hti
    show SmallPres.relInvOf P D t.i (SmallPres.term_i_mem_rels ht) = r
    show (SmallPres.rIso P D).symm ⟨t.i, SmallPres.term_i_mem_rels ht⟩ = r
    rw [hsub]
    exact OrderIso.symm_apply_apply _ _

end Work.Case1
