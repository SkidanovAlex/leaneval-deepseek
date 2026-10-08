import Mathlib
import Submission.Work.Hering.GL32.AppIXP0

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `GL(3,2)` is transitive on the pairs of points of `PG(2,2)`

The group `GL32 = GL(3,2)` acts on the set `Pt` of the seven nonzero vectors of `F₂³` (the points of
`PG(2,2)`) and hence on the set `Pair` of twenty-one unordered pairs of distinct points.  This file
proves that the action on `Pair` is transitive:
`pair_smul_transitive : ∀ q : Pair, ∃ g : GL32, g • p₀ = q`, where `p₀ = {e₀, e₁}`.

The mathematical content is the classical fact that `GL(3,2)` is `2`-transitive on `Pt`: given two
distinct points, i.e. two distinct nonzero vectors `a`, `b` of `F₂³`, they are linearly independent
over `F₂`, and can be completed to a basis.  Concretely we exhibit `c` with `det3 a b c = 1` (a
finite verification over `F₂`) and use the invertible matrix with columns `a`, `b`, `c` as an element
of `GL32` mapping `e₀ ↦ a`, `e₁ ↦ b`.

This is the input used in Step 1 of Appendix IX (the Frobenius step), where it produces the
`GL(3,2)`-equivariant surjection `k[Ω] ↠ M` onto a simple module `M`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Hering.GL32

/-- Two distinct points of `PG(2,2)` span a line, hence admit a vector completing them to a basis:
equivalently, some `c` has `det3 a b c = 1`.  This is a finite verification over `F₂`. -/
lemma exists_det3_eq_one (a b : Pt) (h : a ≠ b) : ∃ c : F2v, det3 a.1 b.1 c = 1 := by
  revert a b
  decide

/-- Any ordered pair of distinct points of `PG(2,2)` is the image of `(e₀, e₁)` under some element
of `GL(3,2)`: the linear equivalence given by the invertible matrix with columns `a`, `b`, `c`,
where `c` completes `a`, `b` to a basis (`det3 a b c = 1`). -/
lemma exists_gl32_maps (a b : Pt) (h : a ≠ b) :
    ∃ g : GL32, g e₀ = a.1 ∧ g e₁ = b.1 := by
  obtain ⟨c, hc⟩ := exists_det3_eq_one a b h
  -- the matrix whose columns are `a`, `b`, `c`
  let M : Matrix (Fin 3) (Fin 3) (ZMod 2) := (Matrix.of ![a.1, b.1, c]).transpose
  have hdet : M.det = 1 := hc
  let g : GL32 := Matrix.toLinearEquiv (Pi.basisFun (ZMod 2) (Fin 3)) M
    (by rw [hdet]; exact isUnit_one)
  refine ⟨g, ?_, ?_⟩
  · -- `g e₀` is the first column of `M`, i.e. `a`
    change Matrix.toLin (Pi.basisFun (ZMod 2) (Fin 3)) (Pi.basisFun (ZMod 2) (Fin 3)) M e₀ = a.1
    rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
    rw [show e₀ = Pi.single (0 : Fin 3) (1 : ZMod 2) from by decide]
    rw [Matrix.mulVec_single_one]
    funext i
    fin_cases i <;> simp [M]
  · -- `g e₁` is the second column of `M`, i.e. `b`
    change Matrix.toLin (Pi.basisFun (ZMod 2) (Fin 3)) (Pi.basisFun (ZMod 2) (Fin 3)) M e₁ = b.1
    rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
    rw [show e₁ = Pi.single (1 : Fin 3) (1 : ZMod 2) from by decide]
    rw [Matrix.mulVec_single_one]
    funext i
    fin_cases i <;> simp [M]

/-- **`GL(3,2)` is transitive on the pairs of points of `PG(2,2)`**: every pair is the image of the
standard pair `p₀ = {e₀, e₁}`. -/
theorem pair_smul_transitive (q : Pair) : ∃ g : GL32, g • p₀ = q := by
  obtain ⟨s, hs⟩ := q
  -- work with the underlying `Sym2 Pt`, so that the goal does not depend on the proof `hs`
  have key : ∀ s : Sym2 Pt, ¬ s.IsDiag → ∃ g : GL32, ((g • p₀ : Pair) : Sym2 Pt) = s := by
    intro s
    induction s using Sym2.ind with
    | h a b =>
      intro hd
      have hab : a ≠ b := fun h => hd (by rw [Sym2.mk_isDiag_iff]; exact h)
      obtain ⟨g, hg0, hg1⟩ := exists_gl32_maps a b hab
      refine ⟨g, ?_⟩
      have hpt0 : ptPerm g p₀pt = a := Subtype.ext (by rw [ptPerm_coe, p₀pt_val, hg0])
      have hpt1 : ptPerm g p₁pt = b := Subtype.ext (by rw [ptPerm_coe, p₁pt_val, hg1])
      show Sym2.map (ptPerm g) p₀.1 = Sym2.mk a b
      rw [p₀_val, Sym2.map_mk, hpt0, hpt1]
  obtain ⟨g, hg⟩ := key s hs
  exact ⟨g, Subtype.ext hg⟩

end Work.Hering.GL32
