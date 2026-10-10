import Mathlib.Algebra.DirectSum.Module
import Mathlib.GroupTheory.Commutator.Basic
import Submission.Work.SSGRoute.prop5.coreLieBar
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transport between graded pieces, and antisymmetry of the graded bracket

The `k`-th piece `Λ k = γ_k/γ_{k+1}` of the associated graded of the lower central series is a
quotient of `Gam k`, and `Gam` is only well defined *up to* the numeral `k`:  the expressions
`(p+q+1)+r+1` and `p+(q+r+1)+1` are equal natural numbers but not syntactically equal, so the
corresponding `Λ`'s have to be compared through an explicit transport.  This file provides

* `GLamCast h` for `h : m = n`, the transport `Λ m ≃+ Λ n`;
* `GLamCast_mk'`, its computation on quotient classes (it does not change the underlying group
  element);
* `lof_cast`, its compatibility with the inclusions `lof` into the direct sum `Λbar`;
* `bracketL_antisymm`, the antisymmetry of the graded bracket — the one structural fact about the
  graded commutator that genuinely needs a transport, because `bracketL p q` lands in `Λ (p+q+1)`
  while `bracketL q p` lands in `Λ (q+p+1)`.
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5
namespace graded

variable {G : Type*} [Group G]

/-- The additive group underlying the `k`-th graded piece of the lower central series. -/
abbrev LamAdd (k : ℕ) : Type _ := Additive (GLam (G := G) k)

/-- Transport of graded pieces along an equality of degrees. -/
noncomputable def GLamCast {m n : ℕ} (h : m = n) : LamAdd (G := G) m ≃+ LamAdd (G := G) n :=
  h ▸ (AddEquiv.refl (LamAdd (G := G) m))

@[simp] theorem GLamCast_rfl (m : ℕ) (x : LamAdd (G := G) m) :
    GLamCast (G := G) rfl x = x := rfl

@[simp] theorem GLamCast_trans {k m n : ℕ} (h₁ : k = m) (h₂ : m = n)
    (x : LamAdd (G := G) k) :
    GLamCast (G := G) h₂ (GLamCast (G := G) h₁ x) = GLamCast (G := G) (h₁.trans h₂) x := by
  subst h₂
  rfl

@[simp] theorem GLamCast_symm_apply {m n : ℕ} (h : m = n) (x : LamAdd (G := G) m) :
    GLamCast (G := G) h.symm (GLamCast (G := G) h x) = x := by
  subst h
  rfl

@[simp] theorem GLamCast_symm_apply' {m n : ℕ} (h : m = n) (x : LamAdd (G := G) n) :
    GLamCast (G := G) h (GLamCast (G := G) h.symm x) = x := by
  subst h
  rfl

/-- `GLamCast` does not change the underlying group element of a quotient class. -/
theorem GLamCast_mk' {m n : ℕ} (h : m = n) (x : ↑(Gam (G := G) m)) :
    GLamCast (G := G) h
        (Additive.ofMul
          (QuotientGroup.mk' ((Gam (G := G) (m + 1)).subgroupOf (Gam (G := G) m)) x)) =
      Additive.ofMul (QuotientGroup.mk' ((Gam (G := G) (n + 1)).subgroupOf (Gam (G := G) n))
        ⟨(x : G), (congrArg (Gam (G := G)) h) ▸ x.property⟩) := by
  cases h
  rfl

/-- The inclusions of the graded pieces into the direct sum, transported along an equality of
degrees. -/
theorem lof_cast {m n : ℕ} (h : m = n) (v : LamAdd (G := G) n) :
    DirectSum.lof ℤ ℕ (LamAdd (G := G)) m (GLamCast (G := G) h.symm v) =
      DirectSum.lof ℤ ℕ (LamAdd (G := G)) n v := by
  cases h
  rfl


/-- The inclusion of the `p`-th graded piece into the direct sum `Λbar`. -/
abbrev lofL (p : ℕ) (a : LamAdd (G := G) p) : Lbar (G := G) :=
  DirectSum.lof ℤ ℕ (LamAdd (G := G)) p a

@[simp] theorem lofL_coe (p : ℕ) (a : LamAdd (G := G) p) :
    lofL (G := G) p a = DirectSum.lof ℤ ℕ (LamAdd (G := G)) p a := rfl

/-- The bracket of two homogeneous elements of `Λbar`. -/
theorem bracketBar_lofL (p q : ℕ) (a : LamAdd (G := G) p) (b : LamAdd (G := G) q) :
    bracketBar (G := G) (lofL (G := G) p a) (lofL (G := G) q b) =
      lofL (G := G) (p + q + 1) (bracketL (G := G) p q a b) :=
  bracketBar_lof (G := G) p q a b

/-- **Antisymmetry of the graded bracket.**  For `a ∈ Λ p` and `b ∈ Λ q` the bracket of `a` and `b`
is minus the bracket of `b` and `a`, the two being compared through the transport from `Λ (q+p+1)`
to `Λ (p+q+1)`. -/
theorem bracketL_antisymm {p q : ℕ} (h : p + q + 1 = q + p + 1)
    (a : LamAdd (G := G) p) (b : LamAdd (G := G) q) :
    bracketL (G := G) p q a b = - GLamCast (G := G) h.symm (bracketL (G := G) q p b a) := by
  obtain ⟨a', ha'⟩ := QuotientGroup.mk'_surjective
    ((Gam (G := G) (p + 1)).subgroupOf (Gam (G := G) p)) (Additive.toMul a)
  obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective
    ((Gam (G := G) (q + 1)).subgroupOf (Gam (G := G) q)) (Additive.toMul b)
  have ha : a = Additive.ofMul (QuotientGroup.mk' _ a') := by rw [ha']; rfl
  have hb : b = Additive.ofMul (QuotientGroup.mk' _ b') := by rw [hb']; rfl
  rw [ha, hb, bracketL_apply_mk, bracketL_apply_mk]
  show Additive.ofMul (commClass p q a' b') =
    - GLamCast (G := G) h.symm (Additive.ofMul (commClass q p b' a'))
  rw [show commClass q p b' a'
      = QuotientGroup.mk' ((Gam (G := G) (q + p + 1 + 1)).subgroupOf (Gam (G := G) (q + p + 1)))
          ⟨⁅(b' : G), (a' : G)⁆, commutator_mem_Gam (p := q) (q := p) b'.property a'.property⟩
      from rfl]
  rw [GLamCast_mk']
  rw [show commClass p q a' b'
      = QuotientGroup.mk' ((Gam (G := G) (p + q + 1 + 1)).subgroupOf (Gam (G := G) (p + q + 1)))
          ⟨⁅(a' : G), (b' : G)⁆, commutator_mem_Gam (p := p) (q := q) a'.property b'.property⟩
      from rfl]
  rw [← ofMul_inv]
  congr 1
  rw [← map_inv]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_inv]
  rw [commutatorElement_inv]

end graded
end Work.SSGRoute.prop5
