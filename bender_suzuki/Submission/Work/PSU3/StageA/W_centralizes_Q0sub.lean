import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- `W = C_V(K)` centralises `Q₀ = ⟨Inv H⟩`.

Both `Q₀` and `W` live inside the two-point stabiliser geometry of a strongly embedded
subgroup `H` with involution `t ∉ H`.  The only non-elementary input is Peterfalvi I
Ch. II §4 Prop. 4 (the `P4` clause of `ChIIFourProp`), which identifies
`C_V(K) = C_D(Inv H)`:  since `Kset H t = J(D,t)` we have
`W H t = V ∩ C(K) = D ∩ C(Inv H)`, so every `w ∈ W` centralises every involution of `H`,
hence every generator of `Q₀`, hence all of `Q0sub H = ⟨Q₀⟩`. -/
theorem W_centralizes_Q0sub {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp) :
    ∀ w ∈ Work.ThmF.W H t, ∀ z ∈ Work.ThmF.Q0sub H, w * z = z * w := by
  intro w hw z hz
  have hstrong : IsStronglyEmbedded H := hS.split.stronglyEmbedded
  have hinvol : orderOf t = 2 := hS.split.invol
  have hnotmem : t ∉ H := hS.split.not_mem
  -- Peterfalvi I Ch. II §4 Prop. 4:  `C_V(K) = C_D(Inv H)`.
  obtain ⟨-, -, -, -, hP4, -⟩ :=
    hC4 G hS.situation H hstrong t hinvol hnotmem
  -- `W H t = V ∩ C(K)`, with `K = Kset H t = invertedBy D t`, so `hP4` gives
  -- `w ∈ D ∩ C(Inv H)`.
  have hw' : w ∈ twoPoint H t ⊓ Subgroup.centralizer (involutions (H : Set G)) := by
    rw [← hP4]
    exact hw
  have hwcent : w ∈ Subgroup.centralizer (involutions (H : Set G)) :=
    (Subgroup.mem_inf.mp hw').2
  -- `w` centralises every element of the generating set `Q0 H = Inv H ∪ {1}`.
  have hgen : ∀ a ∈ Work.ThmF.Q0 H, a * w = w * a := by
    intro a ha
    rcases Work.ThmF.mem_Q0_iff.mp ha with ⟨haH, haord⟩ | ha1
    · exact (Subgroup.mem_centralizer_iff.mp hwcent) a ⟨haH, haord⟩
    · rw [ha1]; simp
  -- hence `w` centralises the subgroup they generate.
  have hclosure : Work.ThmF.Q0sub H ≤ Subgroup.centralizer ({w} : Set G) := by
    rw [Work.ThmF.Q0sub, Subgroup.closure_le]
    intro a ha
    show a ∈ Subgroup.centralizer ({w} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    exact (hgen a ha).symm
  have hz' : z ∈ Subgroup.centralizer ({w} : Set G) := hclosure hz
  exact (Subgroup.mem_centralizer_iff.mp hz') w (Set.mem_singleton w)

end Work.PSU3.StageA
