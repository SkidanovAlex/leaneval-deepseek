import Mathlib
import Submission.Work.Cohomology.Basic
import Submission.Work.Cohomology.Cup
import Submission.Work.Cohomology.coboundary_comp
import Submission.Work.Cohomology.cupOf_coboundary
import Submission.Work.Cohomology.Cohomology
import Submission.Work.Cohomology.H_cupOf_mk
import Submission.Work.Cohomology.CupOne
import Submission.Work.Cohomology.cupOne_relation

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

open Submission.Cohomology

/-!
# Graded commutativity of the cup product on simplicial cohomology

For cochains `u : C^P(S;R)` and `v : C^Q(S;R)` the cup-1 product of
`Submission.Work.Cohomology.CupOne` satisfies the *cup-1 relation* (proved in
`Submission.Work.Cohomology.cupOne_relation`)

`δ(u ⌣₁ v) + (δu) ⌣₁ v + (-1)^P u ⌣₁ (δv) = (-1)^{PQ} (v ⌣ u) - (u ⌣ v)`,

whose two middle terms vanish when `u` and `v` are cocycles.  Hence for cocycles the cochain
`(-1)^{PQ}(v ⌣ u) - (u ⌣ v)` is a coboundary, which is precisely the statement that the cup
product on cohomology is graded commutative.  The present file derives
`H.cup n n y x = (-1)^{n·n} • H.cup n n x y` from the relation.
-/

/-- `cupOf` does not depend on the proof of the degree equation. -/
lemma cupOf_congr_proof {S : SSet.{0}} {R : Type} [CommRing R] {p q m : ℕ}
    (h h' : p + q = m) (u : Cochain S R p) (v : Cochain S R q) :
    cupOf S R h u v = cupOf S R h' u v := by
  congr 1

/-- Scalar multiplication of a cohomology class, computed on a representative. -/
lemma H_mk_zsmul {S : SSet.{0}} {R : Type} [CommRing R] {n : ℕ} (m : ℤ)
    (u : Cochain S R n) (hu : u ∈ cycles S R n) :
    m • H.mk u hu
      = H.mk (m • u) (by
          rw [← Int.cast_smul_eq_zsmul (R := R) m u]
          exact Submodule.smul_mem _ (m : R) hu) := by
  rw [H.mk, H.mk, ← Submodule.Quotient.mk_smul]
  congr 1

theorem H_cup_comm {S : SSet.{0}} {R : Type} [CommRing R] (n : ℕ)
    (x y : Submission.Cohomology.H S R n) :
    Submission.Cohomology.H.cup n n y x
      = (-1 : ℤ) ^ (n * n) • Submission.Cohomology.H.cup n n x y := by
  rcases n with _ | k
  · -- degree `0`: both cup products are the same cochain
    rw [H.cup, H.cup, H.cupOf, H.cupOf]
    simp only [Nat.mul_zero, pow_zero, one_smul]
    rw [H.mk_eq_mk_iff]
    have hsw : cupOf S R (rfl : 0 + 0 = 0 + 0) (Quot.out y).1 (Quot.out x).1
        = cupOf S R (rfl : 0 + 0 = 0 + 0) (Quot.out x).1 (Quot.out y).1 := by
      ext σ
      rw [cupOf_apply, cupOf_apply]
      have hf : frontOf S (rfl : 0 + 0 = 0 + 0) σ = σ := by
        rw [frontOf, show (SimplexCategory.subinterval 0 0 (by omega : 0 + 0 ≤ 0) : ⦋0⦌ ⟶ ⦋0⦌)
          = 𝟙 ⦋0⦌ from by ext i; fin_cases i; rfl, op_id, S.map_id]
        rfl
      have hb : backOf S (rfl : 0 + 0 = 0 + 0) σ = σ := hf
      rw [hf, hb, mul_comm]
    rw [hsw, sub_self]
    exact Submodule.zero_mem _
  · -- degree `k + 1`: use the cup-1 relation, whose correction terms vanish on cocycles
    have hx : coboundary S R (k + 1) (Quot.out x).1 = 0 :=
      (mem_cycles_iff _).mp (Quot.out x).2
    have hy : coboundary S R (k + 1) (Quot.out y).1 = 0 :=
      (mem_cycles_iff _).mp (Quot.out y).2
    have hh : (k + 1) + (k + 1) = Nat.add (k + 1) k + 1 := rfl
    have h1 := cupOne_relation (P := k + 1) (Q := k + 1) (n := Nat.add (k + 1) k)
      hh (by omega) (by omega) (Quot.out x).1 (Quot.out y).1
    rw [hx, hy] at h1
    simp only [cupOneOf_zero_left, cupOneOf_zero_right, add_zero, zsmul_zero] at h1
    rw [H.cup, H.cup, H.cupOf, H.cupOf, H_mk_zsmul, H.mk_eq_mk_iff]
    refine ⟨(-1 : ℤ) ^ ((k + 1) * (k + 1)) •
      cupOneOf S R hh (Quot.out x).1 (Quot.out y).1, ?_⟩
    rw [map_zsmul, h1, smul_sub, negOnePow_smul_smul]

end Work.Cohomology
