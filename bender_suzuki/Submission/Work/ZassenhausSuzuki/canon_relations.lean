import Mathlib
import Submission.Work.ZassenhausSuzuki.CoreV3
import Submission.Work.ZassenhausSuzuki.canon_aux
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.RankOneUniqueness.canon_exists
import Submission.Work.RankOneUniqueness.canon_unique
import Submission.Work.RankOneUniqueness.f_exists
import Submission.Work.RankOneUniqueness.f_unique
import Submission.Work.ZassenhausPSL2.ZData.t_conj_eq_inv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

theorem canon_relations {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (C : Work.ZassenhausPSL2.Canon H Q t) :
    (∀ x : Q, (x : G) ≠ 1 → C.f (C.f x) = x) ∧
    (∀ x : Q, (x : G) ≠ 1 → (C.g x)⁻¹ = C.f x⁻¹) ∧
    (∀ x : Q, (x : G) ≠ 1 → C.h x⁻¹ = C.h x) ∧
    (∀ x : Q, (x : G) ≠ 1 →
      ((C.f (C.g x) : Q) : G)
        = ((C.h x : ↥(Submission.Blueprint.twoPoint H t)) : G)⁻¹ * ((C.f x : Q) : G)⁻¹
          * ((C.h x : ↥(Submission.Blueprint.twoPoint H t)) : G)) ∧
    (∀ (d : ↥(Submission.Blueprint.twoPoint H t)) (x : Q), (x : G) ≠ 1 →
      ∀ (hd : (d : G) * (x : G) * (d : G)⁻¹ ∈ Q)
        (hd' : (d : G)⁻¹ * ((C.f x : Q) : G) * (d : G) ∈ Q),
      C.f ⟨(d : G) * (x : G) * (d : G)⁻¹, hd⟩
        = ⟨(d : G)⁻¹ * ((C.f x : Q) : G) * (d : G), hd'⟩) ∧
    (∀ (d : ↥(Submission.Blueprint.twoPoint H t)) (x : Q), (x : G) ≠ 1 →
      ∀ (hd : (d : G) * (x : G) * (d : G)⁻¹ ∈ Q),
      ((C.h ⟨(d : G) * (x : G) * (d : G)⁻¹, hd⟩ : ↥(Submission.Blueprint.twoPoint H t)) : G)
        = (d : G)⁻¹ * (d : G)⁻¹ * ((C.h x : ↥(Submission.Blueprint.twoPoint H t)) : G)) ∧
    (∀ x₁ x₂ : Q, (x₁ : G) ≠ 1 → (x₂ : G) ≠ 1 → (x₁ * x₂ : G) ≠ 1 →
      ((C.f (x₁ * x₂) : Q) : G)
        = ((C.h x₂ : ↥(Submission.Blueprint.twoPoint H t)) : G)
            * ((C.f (C.f x₁ * C.g x₂) : Q) : G)
            * ((C.h x₂ : ↥(Submission.Blueprint.twoPoint H t)) : G)⁻¹
            * ((C.f x₂ : Q) : G)) := by
  exact ⟨canon_H2 hsplit C, canon_H1 hsplit C, canon_H3 hsplit hzass h2 C,
    canon_H4 hsplit hzass h2 C, canon_H5 hsplit hzass h2 C,
    canon_H6 hsplit hzass h2 C, canon_H7 hsplit hzass h2 C⟩

end Work.ZassenhausSuzuki
