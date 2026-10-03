import Mathlib
import Submission.Work.ORTorsion.Defs
import Submission.Work.ORTorsion.Support.degCoeff_support_subset
import Submission.Work.ORTorsion.Support.exists_mapToG_eq

namespace Work.ORTorsion.Support

open scoped TensorProduct
open Work.ORTorsion
open Work.ORTorsion.LaurentBase

/-- If the images in `G ⧸ ⟨⟨u⟩⟩` of the support of `x : K[H]` are pairwise distinct, then so
are the images of the support of the degree-`b` coefficient `degCoeff Lb b x ∈ K[N]`.

The elements of the support of `degCoeff Lb b x` are the `h * s ^ (-b)` with `h` a term of `x`
of degree `b` (`Support.degCoeff_support_subset`), and `h ↦ h * s ^ (-b)` is injective; since
multiplication by a fixed group element descends to the quotient `G ⧸ ⟨⟨u⟩⟩`, distinctness of the
images of the `h` is inherited by the images of the `h * s ^ (-b)`. -/
theorem injOn_degCoeff {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Algebra K U] (L : TorsionData K G U) {H : Subgroup G} {φ : H →* Multiplicative ℤ}
    (Lb : LaurentBase K U G L.gen L.D H φ) (x : MonoidAlgebra K H) (b : ℤ)
    (hπ : Set.InjOn (QuotientGroup.mk (s := Subgroup.normalClosure {L.u}))
      (mapToG H x).coeff.support) :
    Set.InjOn (QuotientGroup.mk (s := Subgroup.normalClosure {L.u}))
      (mapToG Lb.N (LaurentBase.degCoeff Lb b x)).coeff.support := by
  classical
  intro g1 hg1 g2 hg2 hmk
  have hinjN : Function.Injective (⇑Lb.N.subtype) := fun a b h => Subtype.ext h
  have hinjH : Function.Injective (⇑H.subtype) := fun a b h => Subtype.ext h
  -- Every element of the support of `mapToG Lb.N (degCoeff Lb b x)` lies in `Lb.N` and is a
  -- term of `degCoeff Lb b x`.
  obtain ⟨n1, hn1supp, hn1eq⟩ : ∃ n1 : ↥Lb.N,
      n1 ∈ (LaurentBase.degCoeff Lb b x).coeff.support ∧ (n1 : G) = g1 := by
    rw [coeff_mapToG, Finsupp.mapDomain_support_of_injective hinjN] at hg1
    exact Finset.mem_image.mp hg1
  obtain ⟨n2, hn2supp, hn2eq⟩ : ∃ n2 : ↥Lb.N,
      n2 ∈ (LaurentBase.degCoeff Lb b x).coeff.support ∧ (n2 : G) = g2 := by
    rw [coeff_mapToG, Finsupp.mapDomain_support_of_injective hinjN] at hg2
    exact Finset.mem_image.mp hg2
  -- Each such term comes from a term `h'` of `x` of degree `b`, with `(h' : G) = g * s ^ b`.
  obtain ⟨h1', h1'supp, h1e⟩ := degCoeff_support_subset L Lb b x n1 hn1supp
  obtain ⟨h2', h2'supp, h2e⟩ := degCoeff_support_subset L Lb b x n2 hn2supp
  have h1e' : (h1' : G) = g1 * (Lb.s : G) ^ b := by rw [h1e, hn1eq]
  have h2e' : (h2' : G) = g2 * (Lb.s : G) ^ b := by rw [h2e, hn2eq]
  -- The `h'` lie in the support of `mapToG H x`.
  have hHmem1 : (h1' : G) ∈ (mapToG H x).coeff.support := by
    rw [coeff_mapToG, Finsupp.mapDomain_support_of_injective hinjH]
    exact Finset.mem_image.mpr ⟨h1', h1'supp, rfl⟩
  have hHmem2 : (h2' : G) ∈ (mapToG H x).coeff.support := by
    rw [coeff_mapToG, Finsupp.mapDomain_support_of_injective hinjH]
    exact Finset.mem_image.mpr ⟨h2', h2'supp, rfl⟩
  -- Their images in the quotient agree, because multiplication by `s ^ b` is invertible there.
  have hmk' : QuotientGroup.mk (s := Subgroup.normalClosure {L.u}) (h1' : G)
      = QuotientGroup.mk (s := Subgroup.normalClosure {L.u}) (h2' : G) := by
    rw [h1e', h2e', QuotientGroup.mk_mul, QuotientGroup.mk_mul, hmk]
  have hh : (h1' : G) = (h2' : G) := hπ hHmem1 hHmem2 hmk'
  -- Hence `g1 * s ^ b = g2 * s ^ b`, and cancelling `s ^ b` gives `g1 = g2`.
  have key : g1 * (Lb.s : G) ^ b = g2 * (Lb.s : G) ^ b := by rw [← h1e', ← h2e']; exact hh
  exact mul_right_cancel key

end Work.ORTorsion.Support
