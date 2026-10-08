import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.Canon
import Submission.Work.RankOneUniqueness.canon_unique

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.RankOne

open Submission.Blueprint
open Work.RankOneUniqueness

/-- A group isomorphism carrying `H` to `H'` and `t` to `t'` maps the two-point stabiliser
`twoPoint H t = H ⊓ H^t` into `twoPoint H' t'`. -/
private lemma map_mem_twoPoint {G G' : Type} [Group G] [Group G']
    {H : Subgroup G} {H' : Subgroup G'} {t : G} {t' : G'}
    (φ : G ≃* G') (hH : ∀ x : G, x ∈ H ↔ φ x ∈ H') (ht : φ t = t') {d : G}
    (hd : d ∈ Submission.Blueprint.twoPoint H t) :
    φ d ∈ Submission.Blueprint.twoPoint H' t' := by
  refine mem_twoPoint_iff.mpr ⟨(hH d).mp (mem_twoPoint_iff.mp hd).1, ?_⟩
  obtain ⟨e, he, hee⟩ := (mem_conj_iff H t d).mp (mem_twoPoint_iff.mp hd).2
  exact (mem_conj_iff H' t' (φ d)).mpr
    ⟨φ e, (hH e).mp he, by rw [← hee, map_mul, map_mul, map_inv, ht]⟩

theorem canon_transport {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    {H Q : Subgroup G} {t : G}
    {H' Q' : Subgroup G'} {t' : G'}
    (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (h' : Submission.Blueprint.IsSplitRankOne H' Q' t')
    (φ : G ≃* G') (hQ : ∀ x : G, x ∈ Q ↔ φ x ∈ Q') (hH : ∀ x : G, x ∈ H ↔ φ x ∈ H')
    (ht : φ t = t') {x : ↥Q} (hx1 : (x : G) ≠ 1) :
    (Work.PSU3.StageB.gcan h' ⟨φ x, (hQ x).mp x.2⟩ : G') =
        φ (Work.PSU3.StageB.gcan h x : G) ∧
      ((Work.PSU3.StageB.hcan h'
          ⟨φ x, (hQ x).mp x.2⟩ :
            ↥(Submission.Blueprint.twoPoint H' t')) : G') =
        φ (Work.PSU3.StageB.hcan h x : G) ∧
      (Work.PSU3.StageB.fcan h' ⟨φ x, (hQ x).mp x.2⟩ : G') =
        φ (Work.PSU3.StageB.fcan h x : G) := by
  have hx1' : ((⟨φ x, (hQ x).mp x.2⟩ : ↥Q') : G') ≠ 1 := by
    show φ (x : G) ≠ 1
    intro hcon
    exact hx1 (φ.injective (by simpa using hcon))
  have hg' : φ (Work.PSU3.StageB.gcan h x : G) ∈ Q' :=
    (hQ _).mp (Work.PSU3.StageB.gcan h x).2
  have hf' : φ (Work.PSU3.StageB.fcan h x : G) ∈ Q' :=
    (hQ _).mp (Work.PSU3.StageB.fcan h x).2
  have hd' : φ (Work.PSU3.StageB.hcan h x : G) ∈ Submission.Blueprint.twoPoint H' t' :=
    map_mem_twoPoint φ hH ht (Work.PSU3.StageB.hcan h x).2
  have heq : t' * ((⟨φ x, (hQ x).mp x.2⟩ : ↥Q') : G') * t' =
      ((⟨φ (Work.PSU3.StageB.gcan h x : G), hg'⟩ : ↥Q') : G') *
        ((⟨φ (Work.PSU3.StageB.hcan h x : G), hd'⟩ :
            ↥(Submission.Blueprint.twoPoint H' t')) : G') *
          t' * ((⟨φ (Work.PSU3.StageB.fcan h x : G), hf'⟩ : ↥Q') : G') := by
    have hspec := congrArg φ (Work.PSU3.StageB.canon_spec h hx1)
    simp only [map_mul, ht] at hspec
    simpa using hspec
  obtain ⟨h1, h2, h3⟩ := Work.PSU3.StageB.canon_unique'' h' hx1'
    (x := ⟨φ x, (hQ x).mp x.2⟩)
    (g := ⟨φ (Work.PSU3.StageB.gcan h x : G), hg'⟩)
    (d := ⟨φ (Work.PSU3.StageB.hcan h x : G), hd'⟩)
    (y := ⟨φ (Work.PSU3.StageB.fcan h x : G), hf'⟩) heq
  exact ⟨h1.symm, h2.symm, h3.symm⟩

end Work.PSU3.RankOne
