import Mathlib
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.Cohomology
import Submission.Work.Cohomology.Cup

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

open Submission.Cohomology

/-!
# Well-definedness of the evaluation of the cup product against a cycle

The cup product of cochains is *not* a cochain map on the nose, but the Leibniz rule
`δ(u ⌣ v) = δu ⌣ v ± u ⌣ δv` shows that it is well defined on cohomology: if `u` and `u'`
(resp. `v` and `v'`) are cohomologous cocycles, then `u ⌣ v - u' ⌣ v'` is a sum of two
coboundaries, and a coboundary pairs to zero with every cycle.

The main consequence, proved here, is that for a cycle `ω` in degree `p + q` the number
`seval (u ⌣ v) ω` depends only on the cohomology classes of the cocycles `u`, `v`:

`seval (cupOf rfl u v) ω = seval (cupOf rfl u' v') ω`.

This is the input that makes the Kronecker pairing of a cup product against a cycle descend to
cohomology (used for the Künneth/cross product computation).

Because `Nat.add` is not definitionally associative, all statements are phrased with the ambient
degree `n` as a variable and an explicit equation `h : p + q = n`; in the degree decomposition of
a boundary the ambient degree is then *substituted* (rather than rewritten), which keeps the
dependent occurrences (`ω`, `hω`) in the goal correct.
-/

/-! ## Linearity of the evaluation pairing in the cochain variable -/

lemma seval_add_cochain (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ)
    (u₁ u₂ : Cochain S R n) (c : SChain S R n) :
    seval S R n (u₁ + u₂) c = seval S R n u₁ c + seval S R n u₂ c := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
      simp only [map_add, ih, seval_single, Pi.add_apply]
      ring

lemma seval_sub_cochain (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ)
    (u₁ u₂ : Cochain S R n) (c : SChain S R n) :
    seval S R n (u₁ - u₂) c = seval S R n u₁ c - seval S R n u₂ c := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
      simp only [map_add, ih, seval_single, Pi.sub_apply]
      ring

/-! ## The pairing of a coboundary with a cycle vanishes -/

/-- The evaluation pairing of the zero cochain vanishes. -/
lemma seval_zero (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ) (c : SChain S R n) :
    seval S R n (0 : Cochain S R n) c = 0 := by
  rw [seval_apply]
  simp

lemma seval_eq_zero_of_mem_boundaries {S : SSet.{0}} {R : Type} [CommRing R] {n : ℕ}
    {u : Cochain S R n} (hu : u ∈ boundaries S R n) {c : SChain S R n}
    (hc : c ∈ chainCycles S R n) : seval S R n u c = 0 := by
  match n with
  | 0 =>
      rw [boundaries, Submodule.mem_bot] at hu
      rw [hu, seval_zero]
  | m + 1 =>
      rw [boundaries, LinearMap.mem_range] at hu
      obtain ⟨v, rfl⟩ := hu
      exact seval_coboundary_eq_zero v c hc

/-! ## Vanishing of `seval` of a cup product with a coboundary in either slot -/

lemma seval_cupOf_mem_boundaries_left {S : SSet.{0}} {R : Type} [CommRing R] {n p q : ℕ}
    (h : p + q = n) {A : Cochain S R p} (hA : A ∈ boundaries S R p)
    {b : Cochain S R q} (hb : b ∈ cycles S R q)
    (ω : SChain S R n) (hω : ω ∈ chainCycles S R n) :
    seval S R n (cupOf S R h A b) ω = 0 := by
  cases p with
  | zero =>
      have hA0 : A = 0 := by simpa only [boundaries, Submodule.mem_bot] using hA
      subst hA0
      rw [cupOf_zero_left, seval_zero]
  | succ m =>
      have hn : n = m + q + 1 := by omega
      subst hn
      obtain ⟨a, rfl⟩ := (mem_boundaries_succ (R := R) (n := m) A).mp hA
      exact seval_eq_zero_of_mem_boundaries
        (cupOf_coboundary_left_mem_boundaries (R := R) (n := m + q) (p := m) (q := q) rfl a hb)
        hω

lemma seval_cupOf_mem_boundaries_right {S : SSet.{0}} {R : Type} [CommRing R] {n p q : ℕ}
    (h : p + q = n) {A : Cochain S R p} (hA : A ∈ cycles S R p)
    {B : Cochain S R q} (hB : B ∈ boundaries S R q)
    (ω : SChain S R n) (hω : ω ∈ chainCycles S R n) :
    seval S R n (cupOf S R h A B) ω = 0 := by
  cases q with
  | zero =>
      have hB0 : B = 0 := by simpa only [boundaries, Submodule.mem_bot] using hB
      subst hB0
      rw [cupOf_zero_right, seval_zero]
  | succ m =>
      have hn : n = p + (m + 1) := by omega
      subst hn
      obtain ⟨b, rfl⟩ := (mem_boundaries_succ (R := R) (n := m) B).mp hB
      exact seval_eq_zero_of_mem_boundaries
        (cupOf_coboundary_right_mem_boundaries (R := R) (m := p + (m + 1)) (p := p) (q := m)
          rfl hA b)
        hω

/-! ## The main computation -/

/-- The evaluation of the cup product of two cocycles against a cycle depends only on the
cohomology classes of the cocycles. -/
theorem seval_cupOf_eq_of_cohomologous {S : SSet.{0}} {R : Type} [CommRing R] {n p q : ℕ}
    (h : p + q = n) (u u' : Cochain S R p) (v v' : Cochain S R q)
    (hu : u ∈ cycles S R p) (hv : v ∈ cycles S R q)
    (hu' : u' ∈ cycles S R p) (hv' : v' ∈ cycles S R q)
    (h1 : u - u' ∈ boundaries S R p) (h2 : v - v' ∈ boundaries S R q)
    (ω : SChain S R n) (hω : ω ∈ chainCycles S R n) :
    seval S R n (cupOf S R h u v) ω = seval S R n (cupOf S R h u' v') ω := by
  have hleft : seval S R n (cupOf S R h (u - u') v) ω = 0 :=
    seval_cupOf_mem_boundaries_left h h1 hv ω hω
  have hright : seval S R n (cupOf S R h u' (v - v')) ω = 0 :=
    seval_cupOf_mem_boundaries_right h hu' h2 ω hω
  have hdec : cupOf S R h u v - cupOf S R h u' v'
      = cupOf S R h (u - u') v + cupOf S R h u' (v - v') := by
    have e1 : u = u' + (u - u') := by abel
    have e2 : v = v' + (v - v') := by abel
    rw [e1, e2, cupOf_add_left, cupOf_add_right]
    abel_nf
  have hsub : seval S R n (cupOf S R h u v) ω - seval S R n (cupOf S R h u' v') ω = 0 := by
    rw [← seval_sub_cochain, hdec, seval_add_cochain, hleft, hright]
    simp
  exact sub_eq_zero.mp hsub

/-! ## Pullback of cochains is compatible with the group structure -/

lemma pullbackCo_sub {S T : SSet.{0}} (R : Type) [CommRing R] (f : S ⟶ T) {n : ℕ}
    (u u' : Cochain T R n) : pullbackCo R f (u - u') = pullbackCo R f u - pullbackCo R f u' := by
  ext σ
  rfl

end Work.Cohomology

namespace Work.Cohomology

theorem seval_cup_eq_of_cohomologous {X Y : SSet.{0}} {p q : ℕ}
    (ω : Submission.Cohomology.SChain (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ (p + q))
    (hω : ω ∈ Submission.Cohomology.chainCycles
      (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ (p + q))
    (u u' : Submission.Cohomology.Cochain X ℚ p) (v v' : Submission.Cohomology.Cochain Y ℚ q)
    (hu : u ∈ Submission.Cohomology.cycles X ℚ p)
    (hv : v ∈ Submission.Cohomology.cycles Y ℚ q)
    (hu' : u' ∈ Submission.Cohomology.cycles X ℚ p)
    (hv' : v' ∈ Submission.Cohomology.cycles Y ℚ q)
    (h1 : u - u' ∈ Submission.Cohomology.boundaries X ℚ p)
    (h2 : v - v' ∈ Submission.Cohomology.boundaries Y ℚ q) :
    Submission.Cohomology.seval (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ (p + q)
      (Submission.Cohomology.cupOf (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ rfl
        (Submission.Cohomology.pullbackCo ℚ (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) u)
        (Submission.Cohomology.pullbackCo ℚ (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) v)) ω
    = Submission.Cohomology.seval (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ (p + q)
      (Submission.Cohomology.cupOf (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ rfl
        (Submission.Cohomology.pullbackCo ℚ (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) u')
        (Submission.Cohomology.pullbackCo ℚ (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) v')) ω := by
  have h1' : Submission.Cohomology.pullbackCo ℚ
        (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) u
      - Submission.Cohomology.pullbackCo ℚ
        (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) u'
      ∈ Submission.Cohomology.boundaries
        (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ p := by
    rw [← pullbackCo_sub]
    exact Submission.Cohomology.pullbackCo_mem_boundaries
      (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) h1
  have h2' : Submission.Cohomology.pullbackCo ℚ
        (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) v
      - Submission.Cohomology.pullbackCo ℚ
        (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) v'
      ∈ Submission.Cohomology.boundaries
        (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ q := by
    rw [← pullbackCo_sub]
    exact Submission.Cohomology.pullbackCo_mem_boundaries
      (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) h2
  exact seval_cupOf_eq_of_cohomologous (R := ℚ) rfl
    (Submission.Cohomology.pullbackCo ℚ
      (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) u)
    (Submission.Cohomology.pullbackCo ℚ
      (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) u')
    (Submission.Cohomology.pullbackCo ℚ
      (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) v)
    (Submission.Cohomology.pullbackCo ℚ
      (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) v')
    (Submission.Cohomology.pullbackCo_mem_cycles
      (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) hu)
    (Submission.Cohomology.pullbackCo_mem_cycles
      (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) hv)
    (Submission.Cohomology.pullbackCo_mem_cycles
      (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) hu')
    (Submission.Cohomology.pullbackCo_mem_cycles
      (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) hv')
    h1' h2' ω hω

end Work.Cohomology
