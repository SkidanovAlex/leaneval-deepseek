import Mathlib
import Submission.Work.DSEQ0.eulerCharDefs
import Submission.Work.DSEQ0.CurryAffineCover
import Submission.Work.DSEQ0.CurrySpecResolution
import Submission.Work.DSEQ0.isZero_homology_extend_of_pos
import Submission.Work.DSEQ0.isZero_homology_iff_coboundary
import Submission.Work.DSEQ0.curryTransfer
import Submission.Work.DSEQ0.isZero_homology_cech_of_cechZ

universe u

namespace Work.DSEQ0

open CategoryTheory AlgebraicGeometry Limits Opposite

/-- **The positive-degree homology of the curried Čech complex vanishes.**

`Work.DSEQ0.curryComplexZ A X f W U` is the `ℤ`-indexed Čech complex of the curried presheaf
`V ↦ Γ(X, W ⊓ V)` along the family `U`; the hypothesis `hinf` says that the finite intersections
`W ⊓ ⋂ₐ U(y a)` are affine, and `hle` that the `W ⊓ U i` cover the affine open `W`.  Under these
hypotheses the complex resolves `Γ(X, W)`, hence is acyclic in positive degrees.

The proof compares the curried complex on `X` with the Čech complex of the pulled-back family
`hW.fromSpec ⁻¹ᵁ (W ⊓ U i)` on `Spec Γ(X, W)` (`curryTransfer`): the two are related by a
termwise bijection commuting with the differentials, which is then corrected by a translation so
that it also preserves `0`.  For the pulled-back complex the Čech resolution theorem
`Work.DSF1.Cech.cechAffineCover_quasiIso` applies (`isZero_homology_currySpecComplex`), and the
vanishing is transported along the comparison using the coboundary criterion
`isZero_homology_iff_coboundary` and the extension to `ℤ`-degrees
`isZero_homology_extend_of_pos`. -/
theorem curryComplexZ_homology_isZero (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) {W : X.Opens} (hW : AlgebraicGeometry.IsAffineOpen W)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hinf : ∀ (n : ℕ) (y : Fin (n + 1) → ι),
      AlgebraicGeometry.IsAffineOpen (W ⊓ ⨅ a, U (y a))) (hle : W ≤ ⨆ i, U i) :
    ∀ i : ℤ, 0 < i → CategoryTheory.Limits.IsZero
      ((Work.DSEQ0.curryComplexZ A X f W U).homology i) := by
  intro i hi
  -- the curried complex `C` and the pulled-back complex `D` of `Spec Γ(X, W)`
  set C := (CategoryTheory.cechComplexFunctor U).obj (curryPresheaf A X f W) with hCdef
  set D := DSMap.cech (X.presheaf.obj (Opposite.op W))
    (AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.obj (Opposite.op W))))
    (CategoryTheory.CategoryStruct.id _) (curryPullback hW U) with hDdef
  -- the `ℤ`-indexed pulled-back complex is acyclic in positive degrees
  have hZ : ∀ j : ℤ, 0 < j → CategoryTheory.Limits.IsZero
      ((DSMap.cechZ (X.presheaf.obj (Opposite.op W))
        (AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.obj (Opposite.op W))))
        (CategoryTheory.CategoryStruct.id _) (curryPullback hW U)).homology j) :=
    isZero_homology_currySpecComplex (X := X) (W := W) hW U hinf hle
  -- hence the same for its `ℕ`-part
  have hD : ∀ n : ℕ, 0 < n → CategoryTheory.Limits.IsZero (D.homology n) :=
    isZero_homology_cech_of_cechZ (X.presheaf.obj (Opposite.op W)) (curryPullback hW U) hZ
  -- the termwise bijection of the two complexes
  obtain ⟨φ₀, hφ₀⟩ := curryTransfer A X f hW U
  -- correct it so that it also preserves `0`
  let w : ∀ n : ℕ, ↥(D.X n) := fun n => φ₀ n 0
  have hw : ∀ n : ℕ, (D.d n (n + 1)).hom (w n) = w (n + 1) := by
    intro n
    have h := hφ₀ n (0 : ↥(C.X n))
    rw [map_zero] at h
    exact h.symm
  let φ : ∀ n : ℕ, ↥(C.X n) ≃ ↥(D.X n) := fun n => (φ₀ n).trans (Equiv.subRight (w n))
  have hφ : ∀ (n : ℕ) (x : ↥(C.X n)),
      φ (n + 1) ((C.d n (n + 1)).hom x) = (D.d n (n + 1)).hom (φ n x) := by
    intro n x
    show (Equiv.subRight (w (n + 1))) (φ₀ (n + 1) ((C.d n (n + 1)).hom x)) =
      (D.d n (n + 1)).hom ((Equiv.subRight (w n)) (φ₀ n x))
    rw [Equiv.subRight_apply, Equiv.subRight_apply, hφ₀ n x, map_sub, hw n]
  have hφzero : ∀ n : ℕ, φ n 0 = 0 := by
    intro n
    show (Equiv.subRight (w n)) (φ₀ n 0) = 0
    rw [Equiv.subRight_apply]
    simp [w]
  -- the coboundary criterion for the pulled-back complex
  have hDtriv : ∀ n : ℕ, 0 < n → ∀ s : ↥(D.X n), (D.d n (n + 1)).hom s = 0 →
      ∃ t : ↥(D.X (n - 1)), (D.d (n - 1) n).hom t = s := fun n hn =>
    (isZero_homology_iff_coboundary (X.presheaf.obj (Opposite.op W)) D n hn).mp (hD n hn)
  -- transport it to the curried complex
  have hCtriv : ∀ n : ℕ, 0 < n → ∀ s : ↥(C.X n), (C.d n (n + 1)).hom s = 0 →
      ∃ t : ↥(C.X (n - 1)), (C.d (n - 1) n).hom t = s := by
    intro n hn s hs
    have hstep : (D.d n (n + 1)).hom (φ n s) = 0 := by
      rw [← hφ n s, hs, hφzero]
    obtain ⟨z, hz⟩ := hDtriv n hn (φ n s) hstep
    refine ⟨(φ (n - 1)).symm z, ?_⟩
    have h2 := hφ (n - 1) ((φ (n - 1)).symm z)
    rw [Nat.sub_add_cancel hn, Equiv.apply_symm_apply] at h2
    apply (φ n).injective
    rw [h2, hz]
  -- the curried complex is acyclic in positive degrees
  have hCzero : ∀ n : ℕ, 0 < n → CategoryTheory.Limits.IsZero (C.homology n) := fun n hn =>
    (isZero_homology_iff_coboundary A C n hn).mpr (hCtriv n hn)
  -- pass to the `ℤ`-indexed extension
  have hfin := isZero_homology_extend_of_pos A C hCzero i hi
  rw [curryComplexZ, ← hCdef]
  exact hfin

end Work.DSEQ0
