import Mathlib
import Submission.Work.MotC2.Translation
import Submission.Work.MotC2.transAlgEquiv_injective

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.Nodes

open Work.MotC2

/-- `transAlgEquiv` converts the `ℕ`-multiple `n • Q` in the group of points into the `n`-th power
of the corresponding automorphism: it is the multiplicative monoid homomorphism out of the
(additive) point group. -/
private lemma transAlgEquiv_nsmul {L : Type*} [Field L] [DecidableEq L]
    (E : WeierstrassCurve L) [E.IsElliptic] (Q : E.toAffine.Point) (n : ℕ) :
    transAlgEquiv E (n • Q) = (transAlgEquiv E Q) ^ n := by
  induction n with
  | zero => rw [zero_nsmul, transAlgEquiv_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, transAlgEquiv_add, ih, pow_succ]

/-- **Universe-polymorphic form of `Work.MotC2.transAlgEquiv_injective`.**

The map `Q ↦ τ_Q` from the points of `E` to the `L`-algebra automorphisms of the function field
`L(E)` is injective.  The public copy `Work.MotC2.transAlgEquiv_injective` is stated for
`L : Type` only, whereas `Work.MotC2.transAlgEquiv` itself is universe-polymorphic; the target
below lives in an arbitrary universe `L : Type*`, so we reproduce the same argument here. -/
private theorem transAlgEquiv_injective' {L : Type*} [Field L] [DecidableEq L]
    (E : WeierstrassCurve L) [E.IsElliptic] : Function.Injective (transAlgEquiv E) := by
  -- `transAlgEquiv` is multiplicative, so `τ_X = τ_Y` forces `τ_{X - Y} = 1`.
  have hC : ∀ X Y : E.toAffine.Point, transAlgEquiv E X = transAlgEquiv E Y →
      transAlgEquiv E (X - Y) = 1 := by
    intro X Y hXY
    rw [sub_eq_add_neg, transAlgEquiv_add, hXY, ← transAlgEquiv_add E Y (-Y),
      add_neg_cancel, transAlgEquiv_zero]
  intro X Y hXY
  -- If `X - Y = 0` there is nothing to prove.
  rcases hP : (X - Y) with _ | ⟨a, b, hns⟩
  · exact sub_eq_zero.mp (hP.trans WeierstrassCurve.Affine.Point.zero_def.symm)
  · -- Otherwise `X - Y` is a nonsingular affine point `(a, b)` and `τ_{X-Y} = 1`.
    have hτ : transAlgEquiv E (WeierstrassCurve.Affine.Point.some a b hns) = 1 := by
      rw [← hP]
      exact hC X Y hXY
    -- The translation by `(a, b)` sends the local ring at `(a, b)` to the local ring at `O`
    -- (`TransPlace`); since `τ = 1`, it fixes it, so the two local rings coincide.
    have hmap : affPlaceAt E a b = infPlace E := by
      have h1 := (TransPlace L E a b hns).1
      rw [hτ] at h1
      rw [show ((1 : Func E ≃ₐ[L] Func E) : Func E →ₐ[L] Func E) = AlgHom.id L (Func E)
        from rfl, Subalgebra.map_id] at h1
      exact h1
    -- But `x = genX E` is regular at `(a, b)` and has a pole at `O`: contradiction.
    exact absurd (hmap ▸ algebraMap_mem_affPlaceAt E a b (coordX E)) (genX_notMem_infPlace E)

theorem five_nsmul_eq_zero_of_transAlgEquiv_pow_eq_one {L : Type*} [Field L]
    [DecidableEq L] (E : WeierstrassCurve L) [E.IsElliptic] (Q : E.toAffine.Point)
    (h : (Work.MotC2.transAlgEquiv E Q) ^ 5 = 1) : (5 : ℕ) • Q = 0 := by
  have h5 : transAlgEquiv E ((5 : ℕ) • Q) = (transAlgEquiv E Q) ^ 5 :=
    transAlgEquiv_nsmul E Q 5
  rw [h] at h5
  have h0 : transAlgEquiv E ((5 : ℕ) • Q) = transAlgEquiv E (0 : E.toAffine.Point) := by
    rw [h5, transAlgEquiv_zero]
  exact transAlgEquiv_injective' E h0

end Work.MotV5.Nodes
