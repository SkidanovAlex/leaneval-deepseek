import Mathlib
import Submission.Work.WilkiesH.Strat.Defs
import Submission.Work.WilkiesH.Strat.omega_closure_defs
import Submission.Work.WilkiesH.Strat.omega_closure_pure
import Submission.Work.WilkiesH.Strat.omega_closure_joint_mem
import Submission.Work.WilkiesH.Strat.omega_closure_coordImage
import Submission.Work.WilG0.API

/-!
# The closure of an `Ω`-set is an `Ω`-set, with polynomial complexity

For a sharply o-minimal structure `S` (BNZ, *Wilkie's conjecture for Pfaffian structures*,
§2.1) we show that the topological closure of a set `W ∈ S.Ω F D n` belongs to `S.Ω a (q D) n`
for a format `a` and a polynomial `q` depending only on `(F, n)` (and *not* on `D` or `W`).

The proof writes

`closure W = (⋃_{t > 0} {x | the open box of radius t around x misses W})ᶜ`

and realises the inner union as the projection of a single `Ω`-set: the joint set
`jointSet W ⊆ ℝ^(n + (n+1))` (`Strat/omega_closure_defs.lean`) records a witness `y ∈ W`, the
point `x` and the radius `t`, subject to the strict polynomial inequalities
`(x i - y i)² < t²` (`Omega.omega_poly_lt`) and `0 < t`.  Projecting out the witness costs a
single `coordImage` (`WilG5.coordImage_mem`), and the remaining operations are the
complement, one binary intersection, one projection and one complement, each of which the
`SOMin` axioms control.  The two set-theoretic identities
`closureSet W = (interiorComp W)ᶜ` and `projLast (Kᶜ ∩ {t > 0}) = interiorComp W` are the
files `Strat/omega_closure_pure.lean` and the local lemma below.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Strat

open WilkiesDesign WilkiesConjecture

/-! ## `{z : 0 < z j}` is an `Ω`-set -/

theorem posSet_mem_four (S : WilkiesDesign.SOMin) (N : ℕ) (j : Fin N) :
    posSet N j ∈ S.Ω (N + 3) 4 N := by
  have hdeg : (-(MvPolynomial.X j) : MvPolynomial (Fin N) ℝ).totalDegree ≤ 1 := by
    rw [MvPolynomial.totalDegree_neg]
    exact Work.WilG5.td_X_le j
  have h := Work.WilkiesH.Omega.omega_poly_lt S N (-(MvPolynomial.X j) : MvPolynomial (Fin N) ℝ)
  have heq : {x : Fin N → ℝ | (-(MvPolynomial.X j) : MvPolynomial (Fin N) ℝ).eval x < 0}
      = posSet N j := by
    ext z
    simp [posSet]
  rw [heq] at h
  exact Work.WilG5.mem_mono h (N + 3) 4 le_rfl (by omega)

/-! ## The projection identity -/

/-- The complement of the closure of `W` is the projection of "the box of radius `t` around
`x` misses `W`" along the radius, for `W` presented by its joint set. -/
theorem projLast_compl_coordImage_jointSet {n : ℕ} (W : Set (Fin n → ℝ)) :
    WilkiesDesign.projLast ((Work.WilG5.coordImage (Fin.natAdd n) (jointSet W))ᶜ ∩
      posSet (n + 1) (Fin.last n)) = interiorComp W := by
  rw [omega_closure_coordImage W]
  ext x
  constructor
  · rintro ⟨t, ht⟩
    rw [Set.mem_inter_iff] at ht
    obtain ⟨htK, htpos⟩ := ht
    simp only [posSet, Set.mem_setOf_eq] at htpos
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at htK
    refine ⟨t, by simpa using htpos, ?_⟩
    rintro ⟨y, hyW, hyb⟩
    apply htK
    exact ⟨by simpa using htpos, y, hyW, fun i => by
      rw [snoc_castAdd_one, snoc_last']
      exact hyb i⟩
  · rintro ⟨t, htpos, hnot⟩
    refine ⟨t, ?_⟩
    rw [Set.mem_inter_iff]
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
      rintro ⟨hpos, y, hyW, hyb⟩
      exact hnot ⟨y, hyW, fun i => by
        have h := hyb i
        simp only [snoc_castAdd_one, snoc_last'] at h
        exact h⟩
    · simp only [posSet, Set.mem_setOf_eq]
      simpa using htpos

/-! ## The target -/

theorem omega_closure_v2 {S : WilkiesDesign.SOMin} (hcd : S.SharpCD) :
    ∀ F n : ℕ, ∃ (a : ℕ) (q : Polynomial ℕ),
      ∀ (D : ℕ) (W : Set (Fin n → ℝ)), W ∈ S.Ω F D n →
        ∃ C : Set (Fin n → ℝ), C ∈ S.Ω a (q.eval D) n ∧
          ∀ x : Fin n → ℝ, (x ∈ C ↔ ∀ ε > 0, ∃ y : Fin n → ℝ,
            y ∈ W ∧ ∀ i, |y i - x i| < ε) := by
  intro F n
  refine ⟨F + 600 * (n + 1), Polynomial.X + Polynomial.C (600 * (n + 1)), ?_⟩
  intro D W hW
  refine ⟨(WilkiesDesign.projLast ((Work.WilG5.coordImage (Fin.natAdd n) (jointSet W))ᶜ ∩
      posSet (n + 1) (Fin.last n)))ᶜ, ?_, ?_⟩
  · have hq : (Polynomial.X + Polynomial.C (600 * (n + 1))).eval D = D + 600 * (n + 1) := by
      simp [Polynomial.eval_add, Polynomial.eval_X]
    rw [hq]
    have hJ := omega_closure_joint_mem (S := S) hW
    have hJ' : jointSet W ∈ S.Ω (F + 200 * (n + 1)) (D + 200 * (n + 1)) (n + (n + 1)) :=
      Work.WilG5.mem_mono hJ _ _ (by omega) (by omega)
    have hK := Work.WilG5.coordImage_mem (S := S) (ι := Fin.natAdd n) hJ'
    have hKc := S.compl hK
    have hKc' : (Work.WilG5.coordImage (Fin.natAdd n) (jointSet W))ᶜ ∈
        S.Ω (F + 400 * (n + 1)) (D + 400 * (n + 1)) (n + 1) :=
      Work.WilG5.mem_mono hKc _ _ (by omega) (by omega)
    have hP' : posSet (n + 1) (Fin.last n) ∈ S.Ω (F + 400 * (n + 1)) 4 (n + 1) :=
      Work.WilG5.mem_mono (posSet_mem_four S (n + 1) (Fin.last n)) _ _ (by omega) (by omega)
    have hB := Work.WilG0.Omega_inter2 hKc' hP'
    have hE := S.proj hB
    have hC := S.compl hE
    exact Work.WilG5.mem_mono hC _ _ (by omega) (by omega)
  · intro x
    change x ∈ (WilkiesDesign.projLast ((Work.WilG5.coordImage (Fin.natAdd n) (jointSet W))ᶜ ∩
      posSet (n + 1) (Fin.last n)))ᶜ ↔ x ∈ closureSet W
    rw [projLast_compl_coordImage_jointSet W, omega_closure_pure W]

end Work.WilkiesH.Strat
