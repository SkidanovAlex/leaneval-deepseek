import Mathlib
import Submission.Work.SymQuot.NormPoint.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open TensorProduct
open scoped TensorProduct

universe u

namespace Work.SymQuot.NormPoint

/-- `detT v` evaluated on a pure tensor is the determinant form `v.det`. -/
theorem detT_tprod {F : Type u} [Field F] {Q : Type u} [CommRing Q] [Algebra F Q] {n : ℕ}
    (v : Module.Basis (Fin n) F Q) (f : Fin n → Q) :
    detT v (PiTensorProduct.tprod F f) = v.det f := by
  rw [detT, PiTensorProduct.lift.tprod]
  exact congr_fun (AlternatingMap.coe_multilinearMap v.det) f

/-- **NP0.** If `w` is fixed by the transposition swapping the `i`-th and `j`-th tensor factors
(`i ≠ j`), then `detT v w = 0`, in every characteristic.

The naive argument `detT (τ w) = -detT w` only gives `2 • detT w = 0` and fails in
characteristic `2`.  Instead we expand `w` in the product basis `Basis.piTensorProduct`
indexed by functions `p : Fin n → Fin n`: the coordinates satisfy `c (p ∘ τ) = c p`, and the
involution `p ↦ p ∘ τ` pairs each `p` with `p ∘ τ`, on which
`det (v ∘ p) + det (v ∘ (p ∘ τ)) = det (v ∘ p) - det (v ∘ p) = 0`; the fixed points of the
involution have `p i = p j` and hence `det (v ∘ p) = 0`. -/
theorem detT_eq_zero_of_swap_fixed {F : Type u} [Field F] {Q : Type u} [CommRing Q]
    [Algebra F Q] {n : ℕ} (v : Module.Basis (Fin n) F Q) {i j : Fin n} (hij : i ≠ j)
    {w : Tens F Q n} (hw : permAlg (Q := Q) (Equiv.swap i j) w = w) : detT v w = 0 := by
  classical
  let b : Module.Basis (Fin n → Fin n) F (Tens F Q n) :=
    Basis.piTensorProduct (fun _ : Fin n => v)
  have hb_apply : ∀ p : Fin n → Fin n, b p = PiTensorProduct.tprod F (fun k => v (p k)) := by
    intro p
    dsimp only [b]
    rw [Basis.piTensorProduct_apply]
  have hb_perm : ∀ p : Fin n → Fin n,
      permAlg (Q := Q) (Equiv.swap i j) (b p) = b (p ∘ Equiv.swap i j) := by
    intro p
    rw [hb_apply p, hb_apply (p ∘ Equiv.swap i j), permAlg_tprod, Equiv.symm_swap]
    rfl
  have hb_det : ∀ p : Fin n → Fin n, detT v (b p) = v.det (v ∘ p) := by
    intro p
    rw [hb_apply p, detT_tprod]
    rfl
  have hb_perm_repr : ∀ (x : Tens F Q n) (p : Fin n → Fin n),
      b.repr (permAlg (Q := Q) (Equiv.swap i j) x) p = b.repr x (p ∘ Equiv.swap i j) := by
    intro x p
    have hmap : (b.coord p).comp (permAlg (Q := Q) (Equiv.swap i j)).toLinearMap =
        b.coord (p ∘ Equiv.swap i j) := by
      apply b.ext
      intro q
      simp only [LinearMap.comp_apply, Module.Basis.coord_apply, AlgEquiv.toLinearMap_apply]
      rw [hb_perm q, Module.Basis.repr_self, Module.Basis.repr_self]
      rw [Finsupp.single_apply, Finsupp.single_apply]
      by_cases h : q ∘ Equiv.swap i j = p
      · rw [ite_eq_left h]
        have hq : q = p ∘ Equiv.swap i j := by
          rw [← h]; funext k; simp [Function.comp]
        rw [ite_eq_left hq]
      · rw [ite_eq_right h]
        have hq : ¬ (q = p ∘ Equiv.swap i j) :=
          fun hh => h (by rw [hh]; funext k; simp [Function.comp])
        rw [ite_eq_right hq]
    have h := DFunLike.congr_fun hmap x
    simpa only [LinearMap.comp_apply, Module.Basis.coord_apply, AlgEquiv.toLinearMap_apply] using h
  have hc_symm : ∀ p : Fin n → Fin n, b.repr w (p ∘ Equiv.swap i j) = b.repr w p := by
    intro p
    rw [← hb_perm_repr w p, hw]
  have hsum : detT v w = ∑ p, b.repr w p • v.det (v ∘ p) := by
    conv_lhs => rw [← Module.Basis.sum_repr b w]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [map_smul, hb_det p]
  rw [hsum]
  refine Finset.sum_involution (s := Finset.univ)
    (f := fun p : Fin n → Fin n => b.repr w p • v.det (v ∘ p))
    (fun p _ => p ∘ Equiv.swap i j) ?_ ?_ ?_ ?_
  · intro p _
    have hc := hc_symm p
    have hdet : v.det (v ∘ (p ∘ Equiv.swap i j)) = - v.det (v ∘ p) := by
      have h := AlternatingMap.map_swap v.det (v ∘ p) hij
      simpa only [Function.comp_assoc] using h
    rw [hc, hdet, smul_neg]
    abel
  · intro p _ hfp hcon
    apply hfp
    have hpi : p i = p j := by
      have h := congr_fun hcon i
      simpa [Function.comp] using h.symm
    have hvij : (v ∘ p) i = (v ∘ p) j := by simp only [Function.comp_apply]; rw [hpi]
    have hdet : v.det (v ∘ p) = 0 := AlternatingMap.map_eq_zero_of_eq v.det (v ∘ p) hvij hij
    rw [hdet, smul_zero]
  · intro p _; exact Finset.mem_univ _
  · intro p _; funext k; simp [Function.comp]

end Work.SymQuot.NormPoint
