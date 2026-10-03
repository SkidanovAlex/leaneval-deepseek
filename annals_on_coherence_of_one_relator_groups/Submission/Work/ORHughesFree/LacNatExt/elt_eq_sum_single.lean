import Mathlib
import Submission.Work.ORHughesFree.LacNatExt.PolyTDefs

namespace Work.ORHughesFree.NaturalExtension

theorem lacelt_eq_sum_single {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (f : SkewL R) (d : ℕ) (hneg : ∀ k : ℤ, k < 0 → coeffElt f k = 0)
    (hup : ∀ k : ℤ, (d : ℤ) < k → coeffElt f k = 0) :
    f = ∑ k : Fin (d + 1),
      SkewMonoidAlgebra.single (Multiplicative.ofAdd (k : ℤ)) (coeffElt f (k : ℤ)) := by
  classical
  -- The index map `k ↦ ofAdd k` from `{0, …, d}` into `Multiplicative ℤ` is injective.
  let e : Fin (d + 1) → Multiplicative ℤ := fun k => Multiplicative.ofAdd (k : ℤ)
  have hinj : Function.Injective e := by
    intro a b hab
    have h : ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) := Multiplicative.ofAdd.injective hab
    exact Fin.ext (by omega)
  -- The hypotheses bound the support of `f` inside the image of `e`.
  have hsupp : f.support ⊆ (Finset.univ : Finset (Fin (d + 1))).image e := by
    intro g hg
    have hgne : f.coeff g ≠ 0 := SkewMonoidAlgebra.mem_support_iff.mp hg
    have hcoe : f.coeff g = coeffElt f (Multiplicative.toAdd g) := by simp [coeffElt]
    have hge : 0 ≤ Multiplicative.toAdd g := by
      by_contra h
      exact hgne (by rw [hcoe]; exact hneg _ (lt_of_not_ge h))
    have hle : Multiplicative.toAdd g ≤ (d : ℤ) := by
      by_contra h
      exact hgne (by rw [hcoe]; exact hup _ (lt_of_not_ge h))
    refine Finset.mem_image.mpr ⟨⟨(Multiplicative.toAdd g).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp only [e]
    rw [Int.toNat_of_nonneg hge]
    simp
  -- Write `f` as the sum of its `single` terms over its support, then enlarge the index set
  -- to the image of `e` (the added terms vanish) and reindex.
  conv_lhs => rw [← SkewMonoidAlgebra.sum_coeff_single f]
  rw [Finsupp.sum, show f.coeff.support = f.support from rfl]
  rw [Finset.sum_subset hsupp (fun x _ hx1 => by
        have hxf : f.coeff x = 0 := by
          by_contra h; exact hx1 (SkewMonoidAlgebra.mem_support_iff.mpr h)
        rw [hxf, SkewMonoidAlgebra.single_zero])]
  rw [Finset.sum_image (fun a _ b _ h => hinj h)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  dsimp only [e, coeffElt]

end Work.ORHughesFree.NaturalExtension
