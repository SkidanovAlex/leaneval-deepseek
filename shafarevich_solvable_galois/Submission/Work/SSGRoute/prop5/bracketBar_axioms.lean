import Mathlib
import Submission.Work.SSGRoute.prop5.coreLieBar
import Submission.Work.SSGRoute.prop5.gradedCast
import Submission.Work.SSGRoute.prop5.bracketBar_add_swap
import Submission.Work.SSGRoute.prop5.bracketBar_deriv_of_lof
import Submission.Work.SSGRoute.prop5.deriv_congruence
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The axioms of the graded Lie ring `Λbar`

`Λbar = ⨁ k, Λ k` is the direct sum of the graded pieces `Λ k = γ_k/γ_{k+1}` of the lower central
series of `G`, and `bracketBar` is the bilinear extension of the graded commutator
`bracketL p q : Λ p →+ Λ q →+ Λ (p+q+1)`.

This file proves that `bracketBar` makes `Λbar` into a graded Lie ring:

* `bracketBar x x = 0` for every `x`;
* `bracketBar x (bracketBar y z) = bracketBar (bracketBar x y) z + bracketBar y (bracketBar x z)`
  (the derivation identity for `ad x`).

The mathematics is the classical one for the associated graded of the lower central series.  The
only structural subtlety is that the graded pieces are indexed by *expressions* in `ℕ` which are
equal but not syntactically identical (`(p+q+1)+r+1` against `p+(q+r+1)+1`, …), so comparing the
brackets `bracketL p q` and `bracketL q p` — the two live in `Λ (p+q+1)` and `Λ (q+p+1)` — needs the
explicit transport `graded.GLamCast` and its companions `graded.lofL_cast`/`graded.GLamCast_mk'`
from `gradedCast`.  On homogeneous elements the two axioms are then exactly

* `bracketL_antisymm` (antisymmetry of the graded commutator, proved in `gradedCast` from the exact
  group identity `⁅a,b⁆ * ⁅b,a⁆ = 1`);
* `bracketL_deriv`, the derivation identity modulo `γ_{p+q+r+3}`, which is the Leibniz rule for the
  associated graded Lie ring (`deriv_congruence`, proved from the graded Jacobi identity);
* `bracketL_self`, the vanishing of `bracketL p p a a` (here antisymmetry alone only gives
  `⁅a,a⁆ = -⁅a,a⁆`, so one must use that `⁅a,a⁆ = 1` in the group);

and the extension to all of `Λbar` is the multilinear bookkeeping of
`bracketBar_add_swap` and `bracketBar_deriv_of_lof`.
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5
namespace graded

variable {G : Type*} [Group G]

/-- A class in a graded piece is the class of its underlying group element. -/
theorem commClass_mk' (p q : ℕ) (a : ↑(Gam (G := G) p)) (b : ↑(Gam (G := G) q)) :
    commClass p q a b =
      QuotientGroup.mk' ((Gam (G := G) (p + q + 1 + 1)).subgroupOf (Gam (G := G) (p + q + 1)))
        ⟨⁅(a : G), (b : G)⁆, commutator_mem_Gam (p := p) (q := q) a.property b.property⟩ := rfl

/-- An additivity statement for the inclusions `lofL`. -/
theorem lofL_add (m : ℕ) (x y : LamAdd (G := G) m) :
    lofL (G := G) m (x + y) = lofL (G := G) m x + lofL (G := G) m y :=
  map_add (DirectSum.lof ℤ ℕ (LamAdd (G := G)) m) x y

/-- The inclusion `lofL`, transported along an equality of degrees. -/
theorem lofL_cast {m n : ℕ} (h : m = n) (v : LamAdd (G := G) n) :
    lofL (G := G) m (GLamCast (G := G) h.symm v) = lofL (G := G) n v := by
  cases h
  rfl

/-- The class of a product of group elements is the sum of the classes, granted the corresponding
congruence modulo the next term of the lower central series. -/
theorem mk'_add_eq {N : ℕ} {u v w : G}
    {hu : u ∈ Gam (G := G) N} {hv : v ∈ Gam (G := G) N} {hw : w ∈ Gam (G := G) N}
    (h : u * (v * w)⁻¹ ∈ Gam (G := G) (N + 1)) :
    Additive.ofMul (QuotientGroup.mk' ((Gam (G := G) (N + 1)).subgroupOf (Gam (G := G) N)) ⟨u, hu⟩) =
      Additive.ofMul (QuotientGroup.mk' ((Gam (G := G) (N + 1)).subgroupOf (Gam (G := G) N)) ⟨v, hv⟩) +
      Additive.ofMul (QuotientGroup.mk' ((Gam (G := G) (N + 1)).subgroupOf (Gam (G := G) N)) ⟨w, hw⟩) := by
  rw [← ofMul_mul]
  congr 1
  rw [← map_mul]
  simp only [QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv]
  simpa only [div_eq_mul_inv] using h

/-- **The derivation identity on homogeneous elements of `Λbar`.**  This is the Leibniz rule
`[x,[y,z]] = [[x,y],z] + [y,[x,z]]` for the classes of the nested commutators, the three terms
living in `Λ (p+q+1+r+1)`, `Λ ((p+q+1)+r+1)` and `Λ (q+(p+r+1)+1)` and being compared in
`Λ (p+(q+r+1)+1)` through `GLamCast`. -/
theorem bracketL_deriv {p q r : ℕ}
    (h2 : (p + q + 1) + r + 1 = p + (q + r + 1) + 1)
    (h3 : q + (p + r + 1) + 1 = p + (q + r + 1) + 1)
    (a : LamAdd (G := G) p) (b : LamAdd (G := G) q) (c : LamAdd (G := G) r) :
    bracketL (G := G) p (q + r + 1) a (bracketL (G := G) q r b c) =
      GLamCast (G := G) h2 (bracketL (G := G) (p + q + 1) r (bracketL (G := G) p q a b) c) +
      GLamCast (G := G) h3 (bracketL (G := G) q (p + r + 1) b (bracketL (G := G) p r a c)) := by
  obtain ⟨a', ha'⟩ := QuotientGroup.mk'_surjective
    ((Gam (G := G) (p + 1)).subgroupOf (Gam (G := G) p)) (Additive.toMul a)
  obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective
    ((Gam (G := G) (q + 1)).subgroupOf (Gam (G := G) q)) (Additive.toMul b)
  obtain ⟨c', hc'⟩ := QuotientGroup.mk'_surjective
    ((Gam (G := G) (r + 1)).subgroupOf (Gam (G := G) r)) (Additive.toMul c)
  have ha : a = Additive.ofMul (QuotientGroup.mk' _ a') := by rw [ha']; rfl
  have hb : b = Additive.ofMul (QuotientGroup.mk' _ b') := by rw [hb']; rfl
  have hc : c = Additive.ofMul (QuotientGroup.mk' _ c') := by rw [hc']; rfl
  rw [ha, hb, hc]
  rw [bracketL_apply_mk, commClass_mk']
  rw [bracketL_apply_mk, commClass_mk']
  rw [bracketL_apply_mk, commClass_mk']
  rw [bracketL_apply_mk, commClass_mk']
  rw [GLamCast_mk']
  rw [bracketL_apply_mk, commClass_mk']
  rw [bracketL_apply_mk, commClass_mk']
  rw [GLamCast_mk']
  refine mk'_add_eq (N := p + (q + r + 1) + 1) ?_
  have hderiv := deriv_congruence (G := G) p q r a'.property b'.property c'.property
  rw [show p + q + r + 3 = p + (q + r + 1) + 1 + 1 from by omega] at hderiv
  exact hderiv

/-- The graded bracket of a homogeneous element with itself vanishes:  here antisymmetry only
gives `2 • ⁅a,a⁆ = 0`, so one uses that `⁅a,a⁆ = 1` in the group. -/
theorem bracketL_self {p : ℕ} (a : LamAdd (G := G) p) :
    bracketL (G := G) p p a a = 0 := by
  obtain ⟨a', ha'⟩ := QuotientGroup.mk'_surjective
    ((Gam (G := G) (p + 1)).subgroupOf (Gam (G := G) p)) (Additive.toMul a)
  have ha : a = Additive.ofMul (QuotientGroup.mk' _ a') := by rw [ha']; rfl
  rw [ha, bracketL_apply_mk, commClass_mk']
  have hsub : (⟨⁅(a' : G), (a' : G)⁆,
      commutator_mem_Gam (p := p) (q := p) a'.property a'.property⟩ :
        ↑(Gam (G := G) (p + p + 1))) = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_one]
    rw [commutatorElement_def]
    group
  rw [hsub]
  simp

/-- **The derivation identity for homogeneous elements of `Λbar`.** -/
theorem bracketBar_deriv_lofL (p q r : ℕ) (a : LamAdd (G := G) p) (b : LamAdd (G := G) q)
    (c : LamAdd (G := G) r) :
    bracketBar (G := G) (lofL (G := G) p a)
        (bracketBar (G := G) (lofL (G := G) q b) (lofL (G := G) r c)) =
      bracketBar (G := G) (bracketBar (G := G) (lofL (G := G) p a) (lofL (G := G) q b))
          (lofL (G := G) r c) +
        bracketBar (G := G) (lofL (G := G) q b)
          (bracketBar (G := G) (lofL (G := G) p a) (lofL (G := G) r c)) := by
  rw [bracketBar_lofL]
  rw [bracketBar_lofL]
  rw [bracketBar_lofL]
  rw [bracketBar_lofL]
  rw [bracketBar_lofL]
  rw [bracketBar_lofL]
  rw [← lofL_cast (G := G) (show p + (q + r + 1) + 1 = (p + q + 1) + r + 1 from by omega)
        (bracketL (G := G) (p + q + 1) r (bracketL (G := G) p q a b) c)]
  rw [← lofL_cast (G := G) (show p + (q + r + 1) + 1 = q + (p + r + 1) + 1 from by omega)
        (bracketL (G := G) q (p + r + 1) b (bracketL (G := G) p r a c))]
  rw [← lofL_add]
  exact congrArg (lofL (G := G) (p + (q + r + 1) + 1))
    (bracketL_deriv (G := G) (show (p + q + 1) + r + 1 = p + (q + r + 1) + 1 from by omega)
      (show q + (p + r + 1) + 1 = p + (q + r + 1) + 1 from by omega) a b c)

/-- **The alternating property of `bracketBar`.**  It follows from the bilinear antisymmetry
`bracketBar_add_swap` together with the vanishing of the bracket of a generator with itself. -/
theorem bracketBar_self (x : Lbar G) : bracketBar (G := G) x x = 0 := by
  have hgen : ∀ (p : ℕ) (a : LamAdd (G := G) p),
      bracketBar (G := G) (lofL (G := G) p a) (lofL (G := G) p a) = 0 := by
    intro p a
    rw [bracketBar_lofL, bracketL_self]
    simp
  have hadd : ∀ u v : Lbar G, bracketBar (G := G) (u + v) (u + v) =
      bracketBar (G := G) u u + bracketBar (G := G) v v := by
    intro u v
    have hswap := bracketBar_add_swap (G := G) u v
    have expand : bracketBar (G := G) (u + v) (u + v) =
        bracketBar (G := G) u u + (bracketBar (G := G) u v + bracketBar (G := G) v u) +
          bracketBar (G := G) v v := by
      simp only [map_add, AddMonoidHom.add_apply]
      abel
    rw [expand, hswap]
    abel
  refine DFinsupp.induction (p := fun y => bracketBar (G := G) y y = 0) x ?_ ?_
  · simp
  · intro i b f hf hb ih
    rw [show (DFinsupp.single i b : Lbar (G := G)) = lofL (G := G) i b from rfl]
    rw [hadd, hgen, ih]
    simp

end graded
end Work.SSGRoute.prop5

namespace Work.SSGRoute.prop5

/-- **The axioms of the graded Lie ring `Λbar`**:  the graded bracket `bracketBar` on
`Λbar = ⨁ k, γ_k/γ_{k+1}` is alternating, and `ad x` is a derivation for every `x`. -/
theorem bracketBar_axioms (G : Type*) [Group G] :
    (∀ x : Work.SSGRoute.prop5.graded.Lbar G,
      Work.SSGRoute.prop5.graded.bracketBar (G := G) x x = 0) ∧
    (∀ x y z : Work.SSGRoute.prop5.graded.Lbar G,
      Work.SSGRoute.prop5.graded.bracketBar (G := G) x
        (Work.SSGRoute.prop5.graded.bracketBar (G := G) y z) =
      Work.SSGRoute.prop5.graded.bracketBar (G := G)
        (Work.SSGRoute.prop5.graded.bracketBar (G := G) x y) z +
      Work.SSGRoute.prop5.graded.bracketBar (G := G) y
        (Work.SSGRoute.prop5.graded.bracketBar (G := G) x z)) := by
  refine ⟨fun x => graded.bracketBar_self (G := G) x, fun x y z => ?_⟩
  exact Work.SSGRoute.prop5.bracketBar_deriv_of_lof (G := G)
    (fun p q r a b c => graded.bracketBar_deriv_lofL (G := G) p q r a b c) x y z

end Work.SSGRoute.prop5
