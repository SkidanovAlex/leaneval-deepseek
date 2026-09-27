import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.E4Aux.facets_cover_frontier

namespace Work.Engulf.E4Aux

open Set Finset

/-- An affine map sends an affine combination with weights summing to one to the corresponding
affine combination of the images.  (Both the source and the target are modules, hence affine
spaces over themselves, so a finite sum of scalar multiples is exactly an `affineCombination`;
`Finset.map_affineCombination` computes the image of the latter.) -/
lemma map_sum_smul_eq_sum_smul {N n : ℕ} {ι : Type*} (A : PL.E N →ᵃ[ℝ] PL.E n)
    (s : Finset ι) (w : ι → ℝ) (p : ι → PL.E N) (hw : ∑ i ∈ s, w i = 1) :
    A (∑ i ∈ s, w i • p i) = ∑ i ∈ s, w i • A (p i) := by
  rw [← Finset.affineCombination_eq_linear_combination s p w hw,
      Finset.map_affineCombination s p w hw A]
  exact Finset.affineCombination_eq_linear_combination s (fun i => A (p i)) w hw

/-- **Non-degeneracy of the prepared map on a shelled simplex.**  If the images of the vertices of
a finite vertex set `s` under an affine map `A` are affinely independent, then `A` is injective on
the simplex `simp s`.  (Barycentric coordinates of a point of `simp s` with respect to the
affinely independent family `s` are unique, so the images of two points with the same `A`-image are
equal.)  This is what turns the general position of the vertex images of a shelled simplex into the
non-degeneracy hypothesis of `JoinPrismForm` (`G2`) and the injectivity step of the bad-set lemma
`E4b`. -/
theorem injOn_of_affineIndependent_image {N n : ℕ} {s : Finset (PL.E N)}
    {A : PL.E N →ᵃ[ℝ] PL.E n}
    (h : AffineIndependent ℝ (fun v : ↥s => A v)) : Set.InjOn A (PL.simp s) := by
  intro x hx y hy hxy
  -- barycentric coordinates of `x` and `y` with respect to the vertex set `s`
  obtain ⟨a, _ha0, ha1, hax⟩ := exists_weights_of_mem_convexHull hx
  obtain ⟨b, _hb0, hb1, hby⟩ := exists_weights_of_mem_convexHull hy
  -- the affine map turns them into affine combinations of the vertex images
  have hAx : A x = ∑ v ∈ s, a v • A v := by
    rw [← hax]
    exact map_sum_smul_eq_sum_smul A s a (fun v => v) ha1
  have hAy : A y = ∑ v ∈ s, b v • A v := by
    rw [← hby]
    exact map_sum_smul_eq_sum_smul A s b (fun v => v) hb1
  -- affinely independent vertex images have unique barycentric coordinates
  have hab : ∀ v ∈ s, a v = b v :=
    Work.PL.Generic.eq_of_sum_smul_eq_of_affineIndependent
      (y := fun v : PL.E N => A v) h ha1 hb1 (by rw [← hAx, ← hAy]; exact hxy)
  calc x = ∑ v ∈ s, a v • v := hax.symm
    _ = ∑ v ∈ s, b v • v := Finset.sum_congr rfl (fun v hv => by rw [hab v hv])
    _ = y := hby

end Work.Engulf.E4Aux
