import Mathlib
import Submission.Work.Models.Port.BenderSetup
import Submission.Work.Models.Basic
import Submission.Work.Models.Abstract.inf_conj_w

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Models.Abstract

/-- For a Bender pair and `t ∉ B`, the Bruhat decomposition exhibits `t = b w c` with
`b, c ∈ B`, and the two-point stabiliser `D = B ⊓ B^t` is the conjugate `b T b⁻¹` of the torus.
Indeed `B^t = B^{b w c} = B^{b · w · c} = B^b · (B^w)^b = B · (B^w)^b` (as `c ∈ B`
normalises `B`), so `D = B ⊓ (B^w)^b = (B ⊓ B^w)^b = T^b` (as `b ∈ B` normalises `B`), using
`B ⊓ B^w = T`.  Proof: Bruhat gives `t = b·w·c`; `c ∈ B` gives `conj t B = conj b (conj w B)`;
`conj b` distributes over the intersection and fixes `B` because `b ∈ B`; and
`B ⊓ conj w B = T`. -/
theorem twoPoint_eq {G : Type*} [Group G] [Finite G] (P : Submission.BenderPair G) {t : G}
    (ht : t ∉ P.B) :
    ∃ b ∈ P.B, ∃ c ∈ P.B, t = b * P.w * c ∧
      Submission.Blueprint.twoPoint P.B t = Submission.Blueprint.conj b P.T := by
  -- Bruhat decomposition: `t ∉ B` puts `t` in the big cell `B w B`.
  obtain ⟨b, c, hbc⟩ : ∃ b c : ↥P.B, t = (b : G) * P.w * (c : G) := by
    rcases P.bruhat t with h | h
    · exact absurd h ht
    · exact h
  refine ⟨(b : G), b.2, (c : G), c.2, hbc, ?_⟩
  -- Elements of `B` normalise `B`, so conjugating by them fixes `B`.
  have hconjb : Submission.Blueprint.conj (b : G) P.B = P.B :=
    Work.Models.conj_self_of_mem_normalizer (Subgroup.le_normalizer b.2)
  have hconjc : Submission.Blueprint.conj (c : G) P.B = P.B :=
    Work.Models.conj_self_of_mem_normalizer (Subgroup.le_normalizer c.2)
  -- `conj t B = conj b (conj w B)`.
  have hconjt : Submission.Blueprint.conj t P.B
      = Submission.Blueprint.conj (b : G) (Submission.Blueprint.conj P.w P.B) := by
    rw [hbc, Work.Models.conj_mul, Work.Models.conj_mul, hconjc]
  -- `conj b` distributes over the intersection.
  have hconjinf : Submission.Blueprint.conj (b : G)
        (P.B ⊓ Submission.Blueprint.conj P.w P.B)
      = Submission.Blueprint.conj (b : G) P.B
        ⊓ Submission.Blueprint.conj (b : G) (Submission.Blueprint.conj P.w P.B) :=
    Subgroup.map_inf P.B (Submission.Blueprint.conj P.w P.B)
      (MulAut.conj (b : G)).toMonoidHom (MulAut.conj (b : G)).injective
  rw [Work.Models.twoPoint_def, hconjt, ← Work.Models.Abstract.inf_conj_w P, hconjinf, hconjb]

end Work.Models.Abstract
