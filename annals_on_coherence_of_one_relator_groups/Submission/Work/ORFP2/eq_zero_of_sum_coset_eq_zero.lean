import Mathlib
import Submission.Work.ORFP2.CosetProj

/-!
# Independence of the coset representatives: `k[G]` is free over `k[H]` on the cosets

For a subgroup `H ≤ G` of a group `G` and a commutative ring `k`, the left `k[H]`-module
`k[G]` is free with basis `{single (out q) 1 | q : G ⧸ H}` indexed by the left cosets of `H`
(equivalently, `k[G] = ⨁_q k[H] · out q`).  This file proves the corresponding linear
independence statement:

if `s` is a finite set of pairwise distinct cosets and `b : G ⧸ H → k[H]` is such that
`∑_{q ∈ s} single (out q) 1 * transferHom (b q) = 0` in `k[G]`, then `b q = 0` for all `q ∈ s`.

The proof extracts, for each `q`, the `q`-component of the sum: the `k[H]`-linear projection
`comp k H q  x = projH (single (out q)⁻¹ * x)` (see `CosetProj`) is `id` on the diagonal term
`single (out q) 1 * transferHom a` and vanishes on all the others, because distinct cosets have
representatives differing by an element outside `H`.
-/

namespace Work.ORFP2

namespace CosetInd

open MonoidAlgebra

variable (k : Type*) [CommRing k] {G : Type*} [Group G]

/-- The coefficient of `transferHom a` at an element of `H`. -/
lemma transferHom_coeff_mem (H : Subgroup G) (a : MonoidAlgebra k H) (g : G) (hg : g ∈ H) :
    (transferHom k H a).coeff g = a.coeff ⟨g, hg⟩ := by
  rw [transferHom, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.coeff_mapDomain]
  have := Finsupp.mapDomain_apply_of_injective (f := fun x : H => (x : G)) (Subtype.val_injective) a.coeff ⟨g, hg⟩
  simpa using this

/-- The coefficient of `transferHom a` vanishes off `H`. -/
lemma transferHom_coeff_not_mem (H : Subgroup G) (a : MonoidAlgebra k H) (g : G) (hg : g ∉ H) :
    (transferHom k H a).coeff g = 0 := by
  rw [transferHom, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.coeff_mapDomain]
  exact Finsupp.mapDomain_of_notMem_range a.coeff g (by
    rintro ⟨y, hy⟩
    exact hg (hy ▸ y.2))

/-- `projH` is the identity on `k[H]` embedded in `k[G]`. -/
lemma projH_transferHom_eq (H : Subgroup G) (a : MonoidAlgebra k H) :
    projH k H (transferHom k H a) = a := by
  ext ⟨g, hg⟩
  rw [projH_coeff k H _ g hg, transferHom_coeff_mem k H a g hg]

/-- `comp k H q` is additive. -/
lemma comp_add (H : Subgroup G) (q : G ⧸ H) (x y : MonoidAlgebra k G) :
    comp k H q (x + y) = comp k H q x + comp k H q y := by
  rw [comp, comp, comp, mul_add, projH_add]

/-- `comp k H q` sends `0` to `0`. -/
lemma comp_zero (H : Subgroup G) (q : G ⧸ H) : comp k H q (0 : MonoidAlgebra k G) = 0 := by
  rw [comp, mul_zero, projH_zero]

/-- The component map on a fixed coset, as an additive homomorphism. -/
noncomputable def compAddHom (H : Subgroup G) (q : G ⧸ H) :
    MonoidAlgebra k G →+ MonoidAlgebra k H where
  toFun := comp k H q
  map_zero' := comp_zero k H q
  map_add' := comp_add k H q

/-- `comp k H q` commutes with finite sums. -/
lemma comp_sum {α : Type*} (H : Subgroup G) (q : G ⧸ H) (s : Finset α)
    (f : α → MonoidAlgebra k G) :
    comp k H q (s.sum f) = s.sum (fun x => comp k H q (f x)) :=
  map_sum (compAddHom k H q) f s

/-- On the diagonal the `q`-component of `single (out q) 1 * transferHom a` is `a`. -/
lemma comp_self (H : Subgroup G) (q : G ⧸ H) (a : MonoidAlgebra k H) :
    comp k H q (single (Quotient.out q) (1 : k) * transferHom k H a) = a := by
  have h1 : single (Quotient.out q)⁻¹ (1 : k) * (single (Quotient.out q) 1 * transferHom k H a)
      = transferHom k H a := by
    rw [← mul_assoc, single_mul_single, inv_mul_cancel, mul_one, ← MonoidAlgebra.one_def, one_mul]
  rw [comp, h1, projH_transferHom_eq]

/-- Off the diagonal — `q' ≠ q` — the `q'`-component of `single (out q) 1 * transferHom a`
vanishes: the two coset representatives differ by an element outside `H`. -/
lemma comp_of_ne (H : Subgroup G) (q q' : G ⧸ H) (hne : q' ≠ q) (a : MonoidAlgebra k H) :
    comp k H q' (single (Quotient.out q) (1 : k) * transferHom k H a) = 0 := by
  rw [comp, projH_eq_zero_iff]
  intro g hg
  rw [coeff_single_mul_apply]
  simp only [one_mul, inv_inv]
  rw [coeff_single_mul_apply]
  simp only [one_mul]
  have hnot : (Quotient.out q)⁻¹ * (Quotient.out q' * g) ∉ H := by
    intro hmem
    have h2 : (Quotient.out q)⁻¹ * (Quotient.out q' * g) * g⁻¹ ∈ H :=
      H.mul_mem hmem (H.inv_mem hg)
    have hmem2 : (Quotient.out q)⁻¹ * Quotient.out q' ∈ H := by
      simpa [mul_assoc] using h2
    have hmk : QuotientGroup.mk (Quotient.out q) = QuotientGroup.mk (Quotient.out q') :=
      QuotientGroup.eq.mpr hmem2
    exact hne (((Quotient.out_eq q).symm.trans (hmk.trans (Quotient.out_eq q'))).symm)
  exact transferHom_coeff_not_mem k H a _ hnot

/-- Extracting the `q`-component of a finite coset sum: only the `q`-term survives. -/
lemma sum_comp_coset (H : Subgroup G) (s : Finset (G ⧸ H)) (b : G ⧸ H → MonoidAlgebra k H)
    (q : G ⧸ H) (hq : q ∈ s) :
    comp k H q (s.sum fun y => single (Quotient.out y) (1 : k) * transferHom k H (b y)) = b q := by
  classical
  rw [comp_sum k H q s (fun y => single (Quotient.out y) (1 : k) * transferHom k H (b y))]
  rw [Finset.sum_eq_single q (fun y _ hne => comp_of_ne k H y q hne.symm (b y))
    (fun hqs => absurd hq hqs)]
  exact comp_self k H q (b q)

end CosetInd

open CosetInd

/-- **Independence of the coset representatives.**  If a finitely supported family
`b : G ⧸ H → k[H]`, restricted to a finite set `s` of distinct left cosets, satisfies
`∑_{q ∈ s} single (out q) 1 * transferHom k H (b q) = 0` in the group algebra `k[G]`, then
`b q = 0` for every `q ∈ s`.  Equivalently, the elements `single (out q) 1` are linearly
independent over `k[H]`. -/
theorem eq_zero_of_sum_coset_eq_zero (k : Type*) [CommRing k] {G : Type*} [Group G]
    (H : Subgroup G) (s : Finset (G ⧸ H)) (b : G ⧸ H → MonoidAlgebra k H)
    (h : ∑ q ∈ s, MonoidAlgebra.single (Quotient.out q) (1 : k) * transferHom k H (b q) = 0) :
    ∀ q ∈ s, b q = 0 := by
  intro q hq
  have key := sum_comp_coset k H s b q hq
  rw [h, comp_zero] at key
  exact key.symm

end Work.ORFP2
