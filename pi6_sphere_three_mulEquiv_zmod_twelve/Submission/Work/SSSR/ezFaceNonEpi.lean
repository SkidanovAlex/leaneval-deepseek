import Mathlib
import Submission.Work.SSSR.serreE1Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/- If a simplex `y : Y _⦋d⦌` is non-degenerate and `v : ⦋n⦌ ⟶ ⦋d⦌` is not an epimorphism
(i.e. not a surjection on vertices), then the simplex `Y.map v.op y` obtained by pulling back
`y` along `v` has non-degenerate dimension strictly less than `d`.

The proof uses the epi–mono factorisation `v = factorThruImage v ≫ image.ι v`. Since `v` is not
epi, the monomorphism `image.ι v` is not epi either, so `(image v).len < d`. On the other hand
`Y.map v.op y` generates the same subcomplex as `Y.map (image.ι v).op y`, so their
non-degenerate representatives agree, and the latter has dimension at most `(image v).len`. -/
open CategoryTheory CategoryTheory.Limits Simplicial Opposite in
theorem ezFaceNonEpi {Y : SSet.{0}} {d n : ℕ} (y : Y _⦋d⦌)
    (hy : y ∈ Y.nonDegenerate d) (v : ⦋n⦌ ⟶ ⦋d⦌) (hv : ¬ Epi v) :
    (SSet.S.mk (Y.map v.op y)).toN.dim < d := by
  let x : Y.S := SSet.S.mk (Y.map v.op y)
  let z : Y.S := SSet.S.mk (Y.map (image.ι v).op y)
  have hfac : Y.map (factorThruImage v).op z.simplex = x.simplex := by
    show Y.map (factorThruImage v).op (Y.map (image.ι v).op y) = Y.map v.op y
    rw [← Functor.map_comp_apply, ← op_comp, image.fac]
  have hsub : x.subcomplex = z.subcomplex :=
    SSet.S.subcomplex_eq_of_epi x z (factorThruImage v) hfac
  have htoN : x.toN = z.toN :=
    (SSet.S.toN_eq_iff).mpr (by rw [SSet.S.subcomplex_toN]; exact hsub.symm)
  have hzle : z.toN.dim ≤ (image v).len := SSet.S.dim_toN_le z
  have hne : ¬ Epi (image.ι v) := by
    intro hι
    haveI := hι
    exact hv (by rw [← image.fac v]; infer_instance)
  have hlt : (image v).len < d := by
    have h1 : (image v).len ≤ d := SimplexCategory.le_of_mono (image.ι v)
    rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · exfalso
      haveI : IsIso (image.ι v) :=
        (SimplexCategory.isIso_iff_of_mono (image.ι v)).mpr (by rw [h, SimplexCategory.len_mk])
      exact hne (inferInstance : Epi (image.ι v))
  have key : x.toN.dim ≤ (image v).len := by rw [htoN]; exact hzle
  exact lt_of_le_of_lt key hlt

end Work.SSSR
