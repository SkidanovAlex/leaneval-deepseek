import Mathlib
import Submission.Work.SymQuot.NormPoint.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


universe u

namespace Work.SymQuot.NormPoint

/-- The coordinate functional `w ↦ (v.repr w) i` vanishes on the span of the basis vectors
`v k` with `k > j`, whenever `i ≤ j`. -/
theorem normVal_eq_evalT_aux_coord {F : Type u} [Field F] {Q : Type u} [CommRing Q]
    [Algebra F Q] {n : ℕ} (v : Module.Basis (Fin n) F Q) :
    ∀ (j : Fin n) (w : Q) (i : Fin n),
      w ∈ Submodule.span F (v '' {k : Fin n | j < k}) → i ≤ j → (v.repr w) i = 0 := by
  intro j w i hw hij
  refine Submodule.span_induction (p := fun w _ => (v.repr w) i = 0) ?_ ?_ ?_ ?_ hw
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [v.repr_self,
      Finsupp.single_eq_of_ne (show i ≠ k from ne_of_lt (lt_of_le_of_lt hij hk))]
  · simp
  · intro x y hx hy hx' hy'
    simp only [map_add, Finsupp.add_apply, hx', hy', add_zero]
  · intro a x hx hx'
    simp only [map_smul, Finsupp.smul_apply, hx', smul_zero]

theorem normVal_eq_evalT {F : Type u} [Field F] {Q : Type u} [CommRing Q] [Algebra F Q] {n : ℕ}
    (v : Module.Basis (Fin n) F Q) (ψ : Fin n → (Q →ₐ[F] F))
    (hψ : ∀ j (b : Q), b * v j - ψ j b • v j ∈ Submodule.span F (v '' {k | j < k}))
    (t : Tens F Q n) : normVal v t = evalT ψ t := by
  have hB : ∀ (j : Fin n) (w : Q) (i : Fin n),
      w ∈ Submodule.span F (v '' {k : Fin n | j < k}) → i ≤ j → (v.repr w) i = 0 :=
    normVal_eq_evalT_aux_coord v
  have hcoord : ∀ (j : Fin n) (b : Q) (i : Fin n),
      i ≤ j → (v.repr (b * v j)) i = if j = i then ψ j b else 0 := by
    intro j b i hij
    have hsplit : b * v j = (b * v j - ψ j b • v j) + ψ j b • v j :=
      (sub_add_cancel _ _).symm
    rw [hsplit, map_add, Finsupp.add_apply, map_smul, Finsupp.smul_apply, v.repr_self,
      Finsupp.single_apply]
    rw [hB j (b * v j - ψ j b • v j) i (hψ j b) hij]
    split_ifs with h
    · simp
    · simp
  have hkey : ∀ f : Fin n → Q, v.det (f * ⇑v) = ∏ j, ψ j (f j) := by
    intro f
    have htri : (v.toMatrix (f * ⇑v)).IsLowerTriangular := by
      intro i j hij
      have hij' : i < j := hij
      show (v.repr (f j * v j)) i = 0
      rw [hcoord j (f j) i (le_of_lt hij'),
        ite_eq_right (show ¬ (j = i) from Ne.symm (ne_of_lt hij'))]
    calc v.det (f * ⇑v) = (v.toMatrix (f * ⇑v)).det := v.det_apply (f * ⇑v)
      _ = ∏ j, (v.toMatrix (f * ⇑v)) j j := Matrix.det_of_isLowerTriangular _ htri
      _ = ∏ j, ψ j (f j) := by
          apply Finset.prod_congr rfl
          intro j _
          show (v.repr (f j * v j)) j = ψ j (f j)
          rw [hcoord j (f j) j le_rfl, ite_eq_left rfl]
  have key : ∀ f : Fin n → Q,
      normVal v (PiTensorProduct.tprod F f) = evalT ψ (PiTensorProduct.tprod F f) := by
    intro f
    rw [normVal, detT, PiTensorProduct.tprod_mul_tprod, PiTensorProduct.lift.tprod, evalT_tprod]
    exact hkey f
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      rw [show normVal v (r • PiTensorProduct.tprod F f) =
              r * normVal v (PiTensorProduct.tprod F f) by
            simp only [normVal, smul_mul_assoc, map_smul, smul_eq_mul],
          show evalT ψ (r • PiTensorProduct.tprod F f) =
              r * evalT ψ (PiTensorProduct.tprod F f) by
            simp only [map_smul, smul_eq_mul],
          key f]
  | add x y hx hy =>
      rw [show normVal v (x + y) = normVal v x + normVal v y by
            simp only [normVal, add_mul, map_add],
          show evalT ψ (x + y) = evalT ψ x + evalT ψ y by rw [map_add],
          hx, hy]

end Work.SymQuot.NormPoint
