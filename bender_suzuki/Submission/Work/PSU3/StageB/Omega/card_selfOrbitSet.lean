import Mathlib
import Submission.Work.PSU3.StageB.Omega.count_self_eq
import Submission.Work.PSU3.StageB.Omega.exists_coset_zeta

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.Omega

lemma card_selfOrbitSet {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) :
    Nat.card {x : ↥Q // (x : G) ∈ fr.Q0 ∧
        Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split (ω * x))) ∈
          Work.PSU3.StageB.orbE fr (Multiplicative.toAdd (fr.bar ω))}
      = orderOf fr.ζ - 1 := by
  classical
  -- the cardinality facts of the frame (in particular `|KW : Ksub| = orderOf ζ`)
  obtain ⟨_hn, hQ0, _hKW, _hKsub, hdiv⟩ := omega_card_facts hS fr
  -- the counted set, in "orbit-of-`bar ω`" form, is the set counted by `count_self_eq`
  have hcard : Nat.card {x : ↥Q // (x : G) ∈ fr.Q0 ∧
      Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split (ω * x))) ∈
        Work.PSU3.StageB.orbE fr (Multiplicative.toAdd (fr.bar ω))}
      = Nat.card {x : ↥Q // (x : G) ∈ fr.Q0 ∧ ∃ d : fr.KW, ∃ y : ↥Q, (y : G) ∈ fr.Q0 ∧
          Work.PSU3.StageB.fcan hS.split (ω * x) =
            Work.PSU3.StageB.qconj hS.split
              (⟨(d : G), fr.KW_le d.2⟩ : ↥(Submission.Blueprint.twoPoint H t)) (ω * y)} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      (mem_cntSet_iff_orbE (ω := ω) (ω' := ω) hS fr x).symm)
  rw [hcard]
  exact count_self_eq hS fr hQ0 hdiv hω

end Work.PSU3.StageB.Omega
