import Mathlib
import Submission.Work.Charts.ChartCg
import Submission.Work.Charts.eval_bnDelta_perm
import Submission.Work.SymQuot.ProdOpen

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

universe u

namespace Work.Charts

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

noncomputable section

/-- A congruence for `Scheme.Hom.appLE` in the *morphism*: if two morphisms `f = g` agree, the
induced maps on sections agree, whatever proofs of the inclusions are used.  (This is the same
statement as `Work.SymQuot.appLE_congr_hom`, kept here so that this file is self-contained.) -/
lemma appLE_congr_mor {X Y : Scheme} {f g : X ⟶ Y} (h : f = g) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V e' := by
  subst h
  congr 1

/-- **`S_n`-invariance of the Brill–Noether determinant, as sections.**

Pulling the section `bnDelta C U n s ∈ Γ(C^n, U^n)` back along the automorphism
`permIso C σ` of `C^n` (which permutes the factors) gives `bnDelta` again: the matrix of the
values of the sections is obtained by permuting the *columns* of `bnMatrix`, and the square of
the determinant kills the sign of the permutation (`(sign σ)² = 1`).

This is the section-level form of `eval_bnDelta_perm`. -/
lemma appLE_bnDelta_perm {K : Type u} [Field K] {C : CurveBasics.Curve K} {n : ℕ}
    [Work.SpecLin.DivBase C] [Work.SpecLin.SymGeom C n] (U : C.left.Opens)
    (s : Fin n → C.left.presheaf.obj (Opposite.op U)) (σ : Equiv.Perm (Fin n))
    (e : cgOpen C U n ≤ (Work.SymQuot.permIso C.toOver σ).hom.left ⁻¹ᵁ cgOpen C U n) :
    ((Work.SymQuot.permIso C.toOver σ).hom.left.appLE (cgOpen C U n) (cgOpen C U n) e).hom
      (bnDelta C U n s) = bnDelta C U n s := by
  -- The entries of the pulled-back matrix: the `(j,m)`-entry pulls back to the
  -- `(j, σ.symm m)`-entry, because `permIso σ ≫ proj_m = proj_{σ.symm m}`.
  have hEntry : ∀ j m : Fin n,
      ((Work.SymQuot.permIso C.toOver σ).hom.left.appLE (cgOpen C U n) (cgOpen C U n) e).hom
        (pullSection C U n m (s j)) = pullSection C U n (σ.symm m) (s j) := by
    intro j m
    simp only [pullSection]
    rw [← CommRingCat.comp_apply]
    rw [Scheme.Hom.appLE_comp_appLE]
    exact congrArg (fun φ => φ (s j))
      (appLE_congr_mor (U := U) (V := cgOpen C U n)
        (Work.SymQuot.comp_hom_proj C.toOver n σ m) _ _)
  have hM : ((Work.SymQuot.permIso C.toOver σ).hom.left.appLE (cgOpen C U n) (cgOpen C U n) e).hom.mapMatrix
      (bnMatrix C U n s) = (bnMatrix C U n s).submatrix id σ.symm := by
    ext j m
    simp only [RingHom.mapMatrix_apply, Matrix.submatrix_apply, Matrix.map_apply, bnMatrix]
    exact hEntry j m
  have hsign : ((↑↑(Equiv.Perm.sign σ.symm) : Γ((Cprod C n).left, cgOpen C U n))) ^ 2 = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ.symm) with h | h <;> simp [h]
  calc ((Work.SymQuot.permIso C.toOver σ).hom.left.appLE (cgOpen C U n) (cgOpen C U n) e).hom
        (bnDelta C U n s)
      = (((Work.SymQuot.permIso C.toOver σ).hom.left.appLE (cgOpen C U n) (cgOpen C U n) e).hom
          ((bnMatrix C U n s).det)) ^ 2 := by
        simp only [bnDelta, map_pow]
    _ = ((((Work.SymQuot.permIso C.toOver σ).hom.left.appLE (cgOpen C U n) (cgOpen C U n) e).hom.mapMatrix
          (bnMatrix C U n s)).det) ^ 2 := by
        rw [RingHom.map_det]
    _ = (((bnMatrix C U n s).submatrix id σ.symm).det) ^ 2 := by rw [hM]
    _ = ((↑↑(Equiv.Perm.sign σ.symm) : Γ((Cprod C n).left, cgOpen C U n)) * (bnMatrix C U n s).det) ^ 2 := by
        rw [Matrix.det_permute']
    _ = ((↑↑(Equiv.Perm.sign σ.symm) : Γ((Cprod C n).left, cgOpen C U n)) ^ 2) * ((bnMatrix C U n s).det) ^ 2 := by
        rw [mul_pow]
    _ = (bnMatrix C U n s).det ^ 2 := by rw [hsign, one_mul]
    _ = bnDelta C U n s := by simp only [bnDelta]

/-- **The Brill–Noether open is invariant under permutations of the factors.**

`bnOpen C U n s = D(δ) ⊆ C^n` is the non-vanishing locus of `δ = det (s_j(x_m))²`.  Since the
square of the determinant is invariant under permuting the columns (`appLE_bnDelta_perm`),
preimage along the automorphism `permIso C σ` of `C^n` agrees with `bnOpen`; hence membership of a
point is equivalent to membership of its permuted image. -/
theorem mem_bnOpen_perm {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [Work.SpecLin.DivBase C] [Work.SpecLin.SymGeom C n] (U : C.left.Opens)
    (s : Fin n → (C.left.presheaf.obj (Opposite.op U))) (σ : Equiv.Perm (Fin n))
    {x : (Work.Charts.Cprod C n).left} :
    x ∈ Work.Charts.bnOpen C U n s ↔
      (Work.SymQuot.permIso C.toOver σ).hom.left x ∈ Work.Charts.bnOpen C U n s := by
  -- The product open `U^n` is `S_n`-invariant.
  have hV : (Work.SymQuot.permIso C.toOver σ).hom.left ⁻¹ᵁ cgOpen C U n = cgOpen C U n :=
    Work.SymQuot.piOpen_invariant C.toOver U n σ
  have hd := appLE_bnDelta_perm U s σ hV.ge
  -- `bnOpen` is the basic open of `bnDelta`; `basicOpen_appLE` computes its preimage.
  have hkey : (Work.SymQuot.permIso C.toOver σ).hom.left ⁻¹ᵁ bnOpen C U n s = bnOpen C U n s := by
    have h := Scheme.basicOpen_appLE (Work.SymQuot.permIso C.toOver σ).hom.left
      (cgOpen C U n) (cgOpen C U n) hV.ge (bnDelta C U n s)
    rw [hd] at h
    have h2 : (Work.SymQuot.permIso C.toOver σ).hom.left ⁻¹ᵁ bnOpen C U n s ≤ cgOpen C U n := by
      rw [← hV]
      exact Scheme.Hom.preimage_mono _ (bnOpen_le s)
    have h3 : cgOpen C U n ⊓ (Work.SymQuot.permIso C.toOver σ).hom.left ⁻¹ᵁ bnOpen C U n s
        = (Work.SymQuot.permIso C.toOver σ).hom.left ⁻¹ᵁ bnOpen C U n s := inf_eq_right.mpr h2
    exact h3.symm.trans h.symm
  have h1 : x ∈ bnOpen C U n s ↔
      x ∈ (Work.SymQuot.permIso C.toOver σ).hom.left ⁻¹ᵁ bnOpen C U n s := by rw [hkey]
  rw [h1]
  exact Scheme.Hom.mem_preimage _

end

end Work.Charts
