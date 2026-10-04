import Mathlib
import Submission.Geodesic
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.Man.Sect
import Submission.Work.Diff.EXT.splice_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the sharp jet bound of the chart matrix in the coordinate frame

This module collects the small pieces of vocabulary used by `chartMatJet_sharp`:

* `flatAffine c`: the affine map `z ↦ (finBasis.equivFun)⁻¹ (c + z)` of the model space
  `E ≃ (Fin n → ℝ)`; the flat coordinate map `Work.Diff.STE.flatToE x₀` of the chart at `x₀` is
  `flatAffine ((finBasis.equivFun) ((extChartAt I x₀) x₀))`;
* `Bmat D i a p`: the **frame-change coefficients** of the coordinate-frame vector `∂_a` of the
  chart at `x₀ i` in the `g₀`-orthonormal frame `D.e i p`, at the point of flat coordinate `z`;
* the congruence lemmas for the iterated partial derivatives `pdRList`.
-/

noncomputable section

namespace Work.Diff.STE.Lead

set_option linter.unusedSectionVars false

open Filter

/-! ## 1. The affine flat coordinate map -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The affine lift of a point `c` of the flat coordinate space `Fin (finrank ℝ E) → ℝ` to the
model space `E`, along the canonical basis `finBasis`: `z ↦ (finBasis.equivFun)⁻¹ (c + z)`. -/
def flatAffine (c : Fin (Module.finrank ℝ E) → ℝ) :
    (Fin (Module.finrank ℝ E) → ℝ) → E :=
  fun z => (Module.finBasis ℝ E).equivFun.symm (c + z)

@[simp] lemma flatAffine_apply (c : Fin (Module.finrank ℝ E) → ℝ)
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    flatAffine (E := E) c z = (Module.finBasis ℝ E).equivFun.symm (c + z) := rfl

/-- The inverse of the coordinate equivalence on a canonical basis vector is the basis vector. -/
lemma equivFun_symm_single (p : Fin (Module.finrank ℝ E)) :
    (Module.finBasis ℝ E).equivFun.symm (Pi.single p (1 : ℝ)) = Work.Diff.EXT.bB (E := E) p := by
  rw [Module.Basis.equivFun_symm_apply]
  simp

/-- Translation by a basis vector: `(finBasis.equivFun)⁻¹ (c + e_p) = (finBasis.equivFun)⁻¹ c + bB p`
(with `e_p` the `p`-th canonical basis vector of the flat space). -/
lemma flatAffine_add_single (c : Fin (Module.finrank ℝ E) → ℝ)
    (p : Fin (Module.finrank ℝ E)) :
    (Module.finBasis ℝ E).equivFun.symm (c + Pi.single p (1 : ℝ))
      = flatAffine (E := E) c 0 + Work.Diff.EXT.bB (E := E) p := by
  simp only [flatAffine_apply, map_add, add_zero, equivFun_symm_single]

section Manifold

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The flat coordinate map of the chart at `x₀` is the affine map `flatAffine` of its centre. -/
lemma flatToE_eq_flatAffine (x₀ : M) :
    Work.Diff.STE.flatToE (I := I) x₀
      = flatAffine (E := E) ((Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀)) := rfl

/-! ## 2. The frame-change matrix -/

/-- The **frame-change coefficient** `B_{pa}(z)`: the `g₀`-pairing of the coordinate-frame vector
`∂_a = frameVector (x₀ i) · (bB a)` of the chart at `x₀ i` with the `p`-th vector of the
`g₀`-orthonormal frame `D.e i`, at the point of flat coordinate `z`.  This is the coefficient that
expands the coordinate frame in the orthonormal frame. -/
def Bmat (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (a p : Fin (Module.finrank ℝ E)) : (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun z => g₀.inner (D.pt i z)
    (Submission.Geodesic.frameVector (I := I) (D.x₀ i) (D.pt i z) (Work.Diff.EXT.bB (E := E) a))
    (D.e i p (D.pt i z))

@[simp] lemma Bmat_apply (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (a p : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ) :
    Bmat (I := I) (M := M) D i a p z = g₀.inner (D.pt i z)
      (Submission.Geodesic.frameVector (I := I) (D.x₀ i) (D.pt i z) (Work.Diff.EXT.bB (E := E) a))
      (D.e i p (D.pt i z)) := rfl

end Manifold

/-! ## 3. Congruence of the iterated partial derivatives -/

section Congr

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If two functions agree near `z`, then so do all their iterated partial derivatives (as
functions). -/
lemma pdRList_eventuallyEq' {f g : (ι → ℝ) → ℝ} {z : ι → ℝ} (h : f =ᶠ[nhds z] g) :
    ∀ l : List ι, Work.Diff.STE.pdRList l f =ᶠ[nhds z] Work.Diff.STE.pdRList l g := by
  intro l
  induction l with
  | nil => exact h
  | cons i l ih =>
    have hfd : fderiv ℝ (Work.Diff.STE.pdRList l f) =ᶠ[nhds z]
        fderiv ℝ (Work.Diff.STE.pdRList l g) := ih.fderiv
    filter_upwards [hfd] with y hy
    exact congrArg (fun (L : (ι → ℝ) →L[ℝ] ℝ) => L (Pi.single i 1)) hy

/-- Congruence of the iterated partial derivatives at a point. -/
lemma pdRList_congr' {f g : (ι → ℝ) → ℝ} {z : ι → ℝ} (h : f =ᶠ[nhds z] g) (l : List ι) :
    Work.Diff.STE.pdRList l f z = Work.Diff.STE.pdRList l g z :=
  (pdRList_eventuallyEq' h l).eq_of_nhds

end Congr

end Work.Diff.STE.Lead
