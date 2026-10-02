import Mathlib
import Submission.Work.ThomBordism.localGenDefs
import Submission.Work.ThomBordism.compactZero_free
import Submission.Work.ThomBordism.isCoordBall_restrict_iso_free

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The local class of a relative class is locally constant (compact support)

For a compact set `A` in a charted manifold and a class `β ∈ H_n(M, M∖A)`, the vanishing of the
localisation of `β` at a point of `A` is a *local* property: if it holds at one point of a
preconnected `A`, then it holds everywhere on `A`.

The proof lifts `β` to a class on a finite union of coordinate balls covering `A`
(`existsLift_free`), and uses the fact that the restriction out of a coordinate ball is an
isomorphism (`isCoordBall_restrict_iso_free`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism

noncomputable section

variable {n : ℕ}

theorem relHmap_eq_zero_of_eq_zero_at (hn : 1 ≤ n) {M : TopCat} [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {A : Set M} (hAc : IsCompact A)
    (hpre : IsPreconnected A)
    (β : RelH M n A) {x : M} (hx : x ∈ A)
    (hβ : RelHmap M n (Set.singleton_subset_iff.mpr hx) β = 0) :
    ∀ (y : M) (hy : y ∈ A), RelHmap M n (Set.singleton_subset_iff.mpr hy) β = 0 := by
  classical
  obtain ⟨t, hL, hxt, hxA, hcov, γ, hγ⟩ := existsLift_free n hn M hAc β
  -- the class of `γ` on each ball
  set δ : (p : Set M × M) → RelH M n p.1 :=
    fun p => if hp : p ∈ t then
      RelHmap M n (Set.subset_biUnion_of_mem
        (u := fun q : Set M × M => q.1) (s := (t : Set (Set M × M))) hp) γ
      else 0 with hδ
  -- ### Step 1: the equivalence at each ball
  have key : ∀ (p : Set M × M) (hp : p ∈ t) (y : M) (hy : y ∈ p.1 ∩ A),
      RelHmap M n (Set.singleton_subset_iff.mpr hy.2) β = 0 ↔ δ p = 0 := by
    intro p hp y hy
    have hy1 : y ∈ p.1 := hy.1
    have hyA : y ∈ A := hy.2
    have hinj : Function.Injective
        (RelHmap M n (Set.singleton_subset_iff.mpr hy1)) := by
      have := isCoordBall_restrict_iso_free (n := n) hn (M := M) (hL p hp) hy1
      exact (ModuleCat.mono_iff_injective _).mp inferInstance
    have h1 : δ p = RelHmap M n (Set.subset_biUnion_of_mem
        (u := fun q : Set M × M => q.1) (s := (t : Set (Set M × M))) hp) γ := by
      rw [hδ]; exact dif_pos hp
    have h2 : RelHmap M n (Set.singleton_subset_iff.mpr hy1) (δ p)
        = RelHmap M n (Set.singleton_subset_iff.mpr hyA) β := by
      have hfac := RelHmap_comp' M n (Set.singleton_subset_iff.mpr hy1)
        (Set.subset_biUnion_of_mem (u := fun q : Set M × M => q.1) (s := (t : Set (Set M × M))) hp)
        (Set.singleton_subset_iff.mpr (hcov hyA))
      have e1 : RelHmap M n (Set.singleton_subset_iff.mpr hy1) (δ p)
          = RelHmap M n (Set.singleton_subset_iff.mpr (hcov hyA)) γ := by
        rw [h1]
        exact LinearMap.congr_fun hfac γ
      have hfac2 := RelHmap_comp' M n (Set.singleton_subset_iff.mpr hyA) hcov
        (Set.singleton_subset_iff.mpr (hcov hyA))
      have e2 : RelHmap M n (Set.singleton_subset_iff.mpr hyA) β
          = RelHmap M n (Set.singleton_subset_iff.mpr (hcov hyA)) γ := by
        rw [← hγ]
        exact LinearMap.congr_fun hfac2 γ
      rw [e1, e2]
    constructor
    · intro h
      have hz : RelHmap M n (Set.singleton_subset_iff.mpr hy1) (δ p) = 0 := by
        rw [h2, h]
      exact hinj (by rw [hz, map_zero])
    · intro h
      rw [← h2, h, map_zero]
  -- ### Step 2: the clopen argument
  set Z : Set M := ⋃ p ∈ t, (if δ p = 0 then p.1 ∩ A else ∅) with hZdef
  have hZclosed : IsClosed Z := by
    rw [hZdef]
    exact isClosed_biUnion_finset (fun p hp => by
      by_cases h : δ p = 0
      · rw [if_pos h]
        exact ((hL p hp).isCompact).isClosed.inter hAc.isClosed
      · rw [if_neg h]
        exact isClosed_empty)
  have hcompl : A \ Z = ⋃ p ∈ t, (if δ p = 0 then ∅ else p.1 ∩ A) := by
    ext y
    constructor
    · intro hy
      have hyA : y ∈ A := hy.1
      have hyZ : y ∉ Z := hy.2
      obtain ⟨p, hp, hyp⟩ := Set.mem_iUnion₂.mp (hcov hyA)
      refine Set.mem_iUnion₂.mpr ⟨p, hp, ?_⟩
      have hδp : ¬ δ p = 0 := by
        intro h0
        exact hyZ (by
          rw [hZdef]
          exact Set.mem_iUnion₂.mpr ⟨p, hp, by rw [if_pos h0]; exact ⟨hyp, hyA⟩⟩)
      rw [if_neg hδp]
      exact ⟨hyp, hyA⟩
    · intro hy
      obtain ⟨p, hp, hyp⟩ := Set.mem_iUnion₂.mp hy
      by_cases h : δ p = 0
      · rw [if_pos h] at hyp
        exact hyp.elim
      · rw [if_neg h] at hyp
        refine ⟨hyp.2, ?_⟩
        intro hyZ
        obtain ⟨q, hq, hyq⟩ := Set.mem_iUnion₂.mp hyZ
        by_cases hq0 : δ q = 0
        · rw [if_pos hq0] at hyq
          have hzero : RelHmap M n (Set.singleton_subset_iff.mpr hyq.2) β = 0 :=
            (key q hq y hyq).mpr hq0
          have hδp : δ p = 0 := (key p hp y hyp).mp hzero
          exact h hδp
        · rw [if_neg hq0] at hyq
          exact hyq.elim
  have hZcompl_closed : IsClosed (A \ Z) := by
    rw [hcompl]
    exact isClosed_biUnion_finset (fun p hp => by
      by_cases h : δ p = 0
      · rw [if_pos h]
        exact isClosed_empty
      · rw [if_neg h]
        exact ((hL p hp).isCompact).isClosed.inter hAc.isClosed)
  -- the preconnected argument
  have hsub : A ⊆ Z ∪ (A \ Z) := by intro y hy; by_cases h : y ∈ Z <;> simp [hy, h]
  have hdisj : A ∩ (Z ∩ (A \ Z)) = ∅ := by
    ext y
    constructor
    · rintro ⟨hyA, hyZ, hyAZ⟩
      exact hyAZ.2 hyZ
    · intro hy
      exact absurd hy (Set.notMem_empty y)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hpre Z (A \ Z)
    hZclosed hZcompl_closed hsub hdisj) with hAZ | hAZ
  · -- `A ⊆ Z`: conclude
    intro y hyA
    obtain ⟨p, hp, hyp⟩ := Set.mem_iUnion₂.mp (hAZ hyA)
    by_cases h : δ p = 0
    · rw [if_pos h] at hyp
      exact (key p hp y hyp).mpr h
    · rw [if_neg h] at hyp
      exact hyp.elim
  · -- `A ⊆ A ∖ Z`: contradict the hypothesis at `x`
    exfalso
    obtain ⟨p, hp, hyp⟩ := Set.mem_iUnion₂.mp (hcov hx)
    have hnp : ¬ δ p = 0 := by
      intro h0
      exact (hAZ hx).2 (by
        rw [hZdef]
        exact Set.mem_iUnion₂.mpr ⟨p, hp, by rw [if_pos h0]; exact ⟨hyp, hx⟩⟩)
    exact hnp ((key p hp x ⟨hyp, hx⟩).mp hβ)

end

end Work.ThomBordism
