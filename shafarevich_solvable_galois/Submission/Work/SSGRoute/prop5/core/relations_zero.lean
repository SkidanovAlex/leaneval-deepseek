import Mathlib
import Submission.Work.SSGRoute.prop5.core.Defs
import Submission.Work.SSGRoute.prop5.coreGraded
import Submission.Work.SSGRoute.prop5.bracketBar_axioms
import Submission.Work.SSGRoute.prop5.witt.Vocab
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Relations between the tree monomials in `γ_k/γ_{k+1}`

Let `F = FreeGroup X` and let `Λ q = γ_q/γ_{q+1}` be the associated graded of the lower central
series (Mathlib indexing), so that `cls X q : γ_q → Λ q` is the class map and
`treeCl X c ∈ Λ (size c - 1)` is the class of the commutator monomial of a binary tree `c`.

The statement proved here is that the *relations holding between the Lie monomials
`monLie X c` of trees of a fixed size `k` are also relations between the corresponding classes
`cls (monGrp c)`*:  the kernel of `c ↦ monLie X c` (on the free `ℤ`-module on the trees of size
`k`) is contained in the kernel of `c ↦ cls (monGrp X c)`.

## Route

`Λbar = ⨁ q, Λ q` is the associated graded Lie ring of `F`;  `bracketBar` is its graded bracket
and `bracketBar_axioms` provides the alternating property and the Leibniz rule, so that `Λbar`
carries a `LieRing` structure (the bilinearity of `bracketBar` being built into
`bracketBar : Λbar →+ Λbar →+ Λbar`).  The free Lie ring `L = FreeLieAlgebra ℤ X` is free, so
the assignment `x ↦ [of x] ∈ Λ 0` extends to a Lie homomorphism

`psi : L →ₗ⁅ℤ⁆ Λbar`,

and the induction on trees shows

`psi (monLie X c) = lofL (size c - 1) (treeCl X c)`,

i.e. `psi` computes the class in the graded piece of the commutator monomial of `c`.  A relation
`Σ aᵢ monLie X cᵢ = 0` of trees of size `k` is therefore carried by `psi` into the relation
`Σ aᵢ lofL (k-1) (cls (monGrp cᵢ)) = 0`, and the injectivity of `lofL (k-1) : Λ (k-1) → Λbar`
gives `Σ aᵢ cls (monGrp cᵢ) = 0`.
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5.graded

/-! ## The graded Lie ring structure on `Λbar`

`bracketBar : Λbar →+ Λbar →+ Λbar` is bilinear by construction, so the only axioms of a Lie ring
that have to be verified are the Leibniz rule (`bracketBar_axioms`) and `⁅x,x⁆ = 0`
(`bracketBar_self`); the `ℤ`-linearity in the second variable gives the `LieAlgebra ℤ` structure.
-/

noncomputable instance instRzBracketLbar (G : Type*) [Group G] : Bracket (Lbar G) (Lbar G) :=
  ⟨fun x y => bracketBar x y⟩

noncomputable instance instRzLieRingLbar (G : Type*) [Group G] : LieRing (Lbar G) where
  add_lie := fun x y z => by
    show bracketBar (x + y) z = bracketBar x z + bracketBar y z
    rw [map_add]
    rfl
  lie_add := fun x y z => by
    show bracketBar x (y + z) = bracketBar x y + bracketBar x z
    rw [map_add]
  lie_self := fun x => bracketBar_self x
  leibniz_lie := fun x y z => (bracketBar_axioms G).2 x y z

noncomputable instance instRzLieAlgebraLbar (G : Type*) [Group G] : LieAlgebra ℤ (Lbar G) where
  lie_smul := fun t x y => by
    show bracketBar x (t • y) = t • bracketBar x y
    exact map_zsmul (bracketBar x) t y

end Work.SSGRoute.prop5.graded

namespace Work.SSGRoute.prop5.core

/-! ## The Lie homomorphism `L → Λbar` -/

/-- The Lie homomorphism from the free Lie ring `L = FreeLieAlgebra ℤ X` to the associated graded
`Λbar = ⨁ q, γ_q/γ_{q+1}` of the free group, sending a generator `x` to the class of `x` in
`Λ 0 = F/F'`.  Since `L` is the free Lie ring, this assignment extends uniquely. -/
noncomputable def rzPsi (X : Type) : FreeLieAlgebra ℤ X →ₗ⁅ℤ⁆ graded.Lbar (FreeGroup X) :=
  FreeLieAlgebra.lift ℤ (fun x => graded.lofL (G := FreeGroup X) 0
    (cls X 0 ⟨FreeGroup.of x, by simp [Gam, graded.Gam]⟩))

theorem rzPsi_of (X : Type) (x : X) :
    rzPsi X (FreeLieAlgebra.of ℤ x) = graded.lofL (G := FreeGroup X) 0
      (cls X 0 ⟨FreeGroup.of x, by simp [Gam, graded.Gam]⟩) :=
  FreeLieAlgebra.lift_of_apply _ x

/-! ## Elementary computations with the class map -/

/-- The class map, written with `QuotientGroup.mk'` (the form in which the graded bracket computes
on classes of commutators). -/
theorem rz_cls_eq_mk' (X : Type) (q : ℕ) (x : Gam X q) :
    cls X q x = Additive.ofMul (QuotientGroup.mk'
      ((Gam X (q+1)).subgroupOf (Gam X q)) x) := rfl

/-- The class of the commutator of `x ∈ γ_p` and `y ∈ γ_q` is the graded bracket of the classes. -/
theorem rz_cls_commutator (X : Type) {p q : ℕ} (x : Gam X p) (y : Gam X q) :
    cls X (p + q + 1)
        ⟨⁅(x : FreeGroup X), (y : FreeGroup X)⁆, graded.commutator_mem_Gam x.property y.property⟩ =
      graded.bracketL p q (cls X p x) (cls X q y) := by
  rw [rz_cls_eq_mk', rz_cls_eq_mk', rz_cls_eq_mk', graded.bracketL_apply_mk]
  rfl

/-- The inclusion of a graded piece into `Λbar`, transported along an equality of degrees. -/
theorem rz_lofL_cast {X : Type} {m n : ℕ} (h : m = n) (x : graded.LamAdd (G := FreeGroup X) m) :
    graded.lofL (G := FreeGroup X) m x =
      graded.lofL (G := FreeGroup X) n (graded.GLamCast (G := FreeGroup X) h x) := by
  conv_lhs => rw [← graded.GLamCast_symm_apply (G := FreeGroup X) h x]
  exact graded.lofL_cast (G := FreeGroup X) h (graded.GLamCast (G := FreeGroup X) h x)

/-- The inclusions `Λ n → Λbar` are injective. -/
theorem rz_lofL_injective (G : Type*) [Group G] (n : ℕ) :
    Function.Injective (graded.lofL (G := G) n) := by
  intro x y hxy
  have h' := congrArg (DirectSum.component ℤ ℕ (fun k => Additive (graded.GLam (G := G) k)) n) hxy
  simpa using h'

/-- The compatibility of the class of a commutator monomial with the bracket of the classes of the
two subtrees, up to the transport of the degree `(size a - 1) + (size b - 1) + 1` onto
`size (mul a b) - 1`. -/
theorem rz_GLamCast_bracket_treeCl (X : Type) (a b : Magma X)
    (h : (Magma.size a - 1) + (Magma.size b - 1) + 1 = Magma.size (Magma.mul a b) - 1) :
    graded.GLamCast (G := FreeGroup X) h
        (graded.bracketL (Magma.size a - 1) (Magma.size b - 1) (treeCl X a) (treeCl X b)) =
      treeCl X (Magma.mul a b) := by
  simp only [treeCl]
  rw [← rz_cls_commutator (x := ⟨monGrp X a, monGrp_mem_Gam a⟩)
        (y := ⟨monGrp X b, monGrp_mem_Gam b⟩)]
  rw [rz_cls_eq_mk', graded.GLamCast_mk', rz_cls_eq_mk']
  congr 1

/-! ## `psi` computes the class of the commutator monomial -/

/-- The main computation: the Lie homomorphism `psi` sends the Lie monomial of a binary tree to the
class, in the graded piece `Λ (size c - 1)`, of the corresponding commutator monomial in the free
group. -/
theorem rz_psi_monLie (X : Type) (c : Magma X) :
    rzPsi X (monLie X c) = graded.lofL (G := FreeGroup X) (Magma.size c - 1) (treeCl X c) := by
  induction c with
  | gen x =>
    rw [monLie_gen, rzPsi_of]
    congr 1
  | mul a b iha ihb =>
    have hidx : (Magma.size a - 1) + (Magma.size b - 1) + 1 = Magma.size (Magma.mul a b) - 1 := by
      rw [Magma.size_mul]; have ha := Magma.size_pos a; have hb := Magma.size_pos b; omega
    rw [monLie_mul, LieHom.map_lie, iha, ihb]
    change graded.bracketBar (graded.lofL (G := FreeGroup X) (Magma.size a - 1) (treeCl X a))
        (graded.lofL (G := FreeGroup X) (Magma.size b - 1) (treeCl X b)) =
      graded.lofL (G := FreeGroup X) (Magma.size (Magma.mul a b) - 1) (treeCl X (Magma.mul a b))
    rw [graded.bracketBar_lofL]
    rw [rz_lofL_cast (X := X) hidx]
    congr 1
    exact rz_GLamCast_bracket_treeCl X a b hidx

/-- The computation of `rz_psi_monLie` with the size of the tree prescribed to be `k`, in the form
in which it is applied to a family of trees of common size. -/
theorem rz_psi_monLie_of_size (X : Type) (k : ℕ) (c : Magma X) (hc : Magma.size c = k) :
    rzPsi X (monLie X c) = graded.lofL (G := FreeGroup X) (k - 1)
      (cls X (k - 1) ⟨monGrp X c, by simpa [hc] using monGrp_mem_Gam c⟩) := by
  rw [rz_psi_monLie]
  have h : Magma.size c - 1 = k - 1 := by rw [hc]
  rw [rz_lofL_cast (X := X) h]
  congr 1
  simp only [treeCl]
  rw [rz_cls_eq_mk', graded.GLamCast_mk', rz_cls_eq_mk']

/-! ## The target statement -/

theorem relations_zero (X : Type) (k : ℕ) (hk : 1 ≤ k) (r : ℕ)
    (c : Fin r → Work.SSGRoute.prop5.Magma X) (a : Fin r → ℤ)
    (hc : ∀ i, Work.SSGRoute.prop5.Magma.size (c i) = k)
    (h : ∑ i, a i • Work.SSGRoute.prop5.monLie X (c i) = 0) :
    ∑ i, a i • Work.SSGRoute.prop5.core.cls X (k - 1)
      ⟨Work.SSGRoute.prop5.core.monGrp X (c i),
        by simpa [hc i] using Work.SSGRoute.prop5.core.monGrp_mem_Gam (c i)⟩ = 0 := by
  -- push the relation through the Lie homomorphism `psi`
  have hmap : ∑ i, a i • rzPsi X (monLie X (c i)) = 0 := by
    have h1 : rzPsi X (∑ i, a i • monLie X (c i)) = 0 := by rw [h]; simp
    simpa using h1
  -- replace each `psi (monLie (c i))` by the class of the commutator monomial
  have h2 : ∑ i, a i • graded.lofL (G := FreeGroup X) (k - 1)
      (cls X (k - 1)
        ⟨monGrp X (c i), by simpa [hc i] using monGrp_mem_Gam (c i)⟩) = 0 := by
    rw [← hmap]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [rz_psi_monLie_of_size X k (c i) (hc i)]
  -- move the inclusion of the graded piece out of the sum
  have h3 : (graded.lofL (G := FreeGroup X) (k - 1))
      (∑ i, a i • cls X (k - 1)
        ⟨monGrp X (c i), by simpa [hc i] using monGrp_mem_Gam (c i)⟩) = 0 := by
    simpa only [map_sum, map_zsmul] using h2
  -- the inclusion is injective
  refine rz_lofL_injective (FreeGroup X) (k - 1) ?_
  simpa using h3

end Work.SSGRoute.prop5.core
