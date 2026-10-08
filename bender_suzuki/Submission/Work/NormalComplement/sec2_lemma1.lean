import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.sec2_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- **Peterfalvi I Ch. III §2 Lemma 1** (p.176), dispatch wrapper: immediately from
`Work.NormalComplement.sec2_one` (already proved, `sorry`-free), whose hypotheses are the nine
fields of `Setup3`.  See `Submission/Work/NormalComplement/_design/Sec3.lean`. -/
theorem sec2_lemma1 (hFT : Submission.Blueprint.FeitThompsonProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} (h : Work.NormalComplement.Design.Setup3 G H t W) :
    Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t ⊆
        (Work.NormalComplement.Design.Ecomm H t W : Set G) ∧
      (∀ e ∈ Work.NormalComplement.Design.Egrp H t W,
        t * e * t⁻¹ ∈ Work.NormalComplement.Design.Egrp H t W) ∧
      ∀ x ∈ Work.NormalComplement.Design.Egrp H t W ⊓ Submission.Blueprint.centD H t,
        x ∉ Work.NormalComplement.Design.Ecomm H t W →
        ∀ k ∈ Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t,
          x * k * x⁻¹ = k → k = 1 :=
  sec2_one hFT h.sit h.se h.invol h.notMem h.le h.normal h.sup h.Ene h.d1

end Work.NormalComplement
