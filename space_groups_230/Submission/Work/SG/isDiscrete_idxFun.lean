import Mathlib
import Submission.Work.SG.realize_defs
import Submission.Work.SG.finite_int_of_mulVec_bound
import Submission.Work.SG.absCoord_le_of_dist_le

/-!
# Discreteness of the index-parametrised realisation group

For a real matrix `M` with `M.det ≠ 0`, a finite set `P` of integer matrices whose conjugates
`oConj M A = M A M⁻¹` are orthogonal, and any `τ : IMat → Fin 3 → ℝ`, the family
`(A, n) ↦ gOf M A _ (τ A + intVec n)` is *properly discontinuous*: for every `x` and every
`ε > 0` only finitely many of its members move `x` by at most `ε`.

The junk value of `idxFun` off `P` does not matter: every `(A, n)` with `A ∉ P` yields the
identity motion.

The mathematical content is the elementary estimate

`|(M *ᵥ n) j| ≤ ε + |(M A M⁻¹ *ᵥ x + M *ᵥ τ A − x) j|`,

for `n ∈ ℤ³` such that `gOf M A _ (τ A + n)` moves `x` by at most `ε`.  Since `M` is invertible
this confines `n` to a fixed coordinate box, and a coordinate box in `ℤ³` is finite.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem
open Matrix

/-- Coordinates of the motion `x ↦ M A M⁻¹ x + M w`. -/
lemma gOf_ofLp (M : RMat) (A : IMat)
    (hO : Matrix.transpose (oConj M A) * (oConj M A) = 1) (w : Fin 3 → ℝ) (x : E 3) :
    (gOf M A hO w x).ofLp = oConj M A *ᵥ x.ofLp + M *ᵥ w := by
  rw [gOf_apply]; simp

/-- For a fixed linear part and offset only finitely many `n ∈ ℤ³` give a motion moving `x` by
at most `ε`. -/
lemma finite_int_of_dist_le (M : RMat) (hM : M.det ≠ 0) (A : IMat)
    (hO : Matrix.transpose (oConj M A) * (oConj M A) = 1) (w : Fin 3 → ℝ) (x : E 3)
    (ε : ℝ) (hε : 0 ≤ ε) :
    {n : Fin 3 → ℤ | dist (gOf M A hO (w + intVec n) x) x ≤ ε}.Finite := by
  refine Set.Finite.subset (finite_int_of_mulVec_bound M hM
    (fun j => ε + |(oConj M A *ᵥ x.ofLp + M *ᵥ w - x.ofLp) j|) (fun j => ?_)) ?_
  · have h1 := abs_nonneg ((oConj M A *ᵥ x.ofLp + M *ᵥ w - x.ofLp) j)
    linarith
  · intro n hn j
    exact absCoord_le_of_dist_le M A hO w x ε n hn j

theorem isDiscrete_idxFun (M : Work.SG.RMat) (hM : M.det ≠ 0)
    (P : Set Work.SG.IMat) (hP : P.Finite) (τ : Work.SG.IMat → Fin 3 → ℝ)
    (horth : ∀ A ∈ P, Matrix.transpose (Work.SG.oConj M A) * (Work.SG.oConj M A) = 1) :
    ∀ x : LeanEval.Geometry.SpaceGroupsProblem.E 3, ∀ ε > (0 : ℝ),
      {g : LeanEval.Geometry.SpaceGroupsProblem.EuclideanIsom 3 |
        (∃ i : Work.SG.IMat × (Fin 3 → ℤ), Work.SG.idxFun M P τ horth i = g) ∧
          dist (g x) x ≤ ε}.Finite := by
  intro x ε hε
  set t : P → Set (EuclideanIsom 3) := fun A =>
    (fun n : Fin 3 → ℤ => gOf M A.1 (horth A.1 A.2) (τ A.1 + intVec n)) ''
      {n : Fin 3 → ℤ | dist (gOf M A.1 (horth A.1 A.2) (τ A.1 + intVec n) x) x ≤ ε}
    with ht
  have hfin : ∀ A : P, (t A).Finite := fun A =>
    Set.Finite.image (fun n : Fin 3 → ℤ => gOf M A.1 (horth A.1 A.2) (τ A.1 + intVec n))
      (finite_int_of_dist_le M hM A.1 (horth A.1 A.2) (τ A.1) x ε (le_of_lt hε))
  have hUniv : (⋃ A : P, t A).Finite := by
    have : Finite P := hP.to_subtype
    have h := Set.Finite.biUnion (s := (Set.univ : Set P)) Set.finite_univ (fun A _ => hfin A)
    simpa using h
  refine Set.Finite.subset ((Set.finite_singleton 1).union hUniv) ?_
  rintro g ⟨⟨⟨A, n⟩, hidx⟩, hdist⟩
  rw [Set.mem_union]
  by_cases hA : A ∈ P
  · right
    rw [Set.mem_iUnion]
    refine ⟨⟨A, hA⟩, ?_⟩
    have hg : gOf M A (horth A hA) (τ A + intVec n) = g := by
      rw [← hidx]
      ext y
      rw [idxFun_apply M P τ horth hA n y, gOf_apply]
    rw [Set.mem_image]
    refine ⟨n, ?_, hg⟩
    rw [← hg] at hdist
    exact hdist
  · left
    rw [Set.mem_singleton_iff]
    rw [idxFun_of_notMem M P τ horth hA n] at hidx
    exact hidx.symm

end Work.SG
