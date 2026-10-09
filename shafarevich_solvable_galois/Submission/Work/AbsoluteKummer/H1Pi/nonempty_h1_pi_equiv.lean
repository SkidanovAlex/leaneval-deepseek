/-
# `H¹` commutes with finite products of coefficient modules

For a topological group `G` and a finite family `(M i)` of additive commutative groups with a
`G`-action, first continuous cohomology commutes with the product of the coefficients:

  `H¹(G, ∏ᵢ Mᵢ) ≃+ ∏ᵢ H¹(G, Mᵢ)`.

The proof splits into three independent pieces.

* Locally constant functions into a product are exactly the tuples of locally constant functions
  (`Fintype ι` is used through the finiteness of the intersection of the open sets).
* Consequently the *currying* map `(G → ∏ᵢ Mᵢ) → (∏ᵢ (G → Mᵢ))` restricts to an isomorphism of
  subgroups `Z¹(G, ∏ᵢ Mᵢ) ≃+ ∏ᵢ Z¹(G, Mᵢ)`, and carries the `1`-coboundaries onto the tuples of
  `1`-coboundaries.
* A quotient of a product by a product of subgroups is the product of the quotients.
-/
import Mathlib
import Submission.Work.AbsoluteKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.H1Pi

open scoped Classical

noncomputable section

/-! ## Quotients of products -/

section PiQuotient

variable {ι : Type*} {A : ι → Type*} [∀ i, AddCommGroup (A i)]

/-- The quotient of a product by a product of additive subgroups is the product of the quotients. -/
theorem nonempty_pi_quotient_equiv (S : ∀ i, AddSubgroup (A i)) :
    Nonempty ((∀ i, A i) ⧸ (AddSubgroup.pi Set.univ S) ≃+ (∀ i, A i ⧸ S i)) := by
  let f : (∀ i, A i) →+ (∀ i, A i ⧸ S i) :=
    { toFun := fun x i => QuotientAddGroup.mk' (S i) (x i)
      map_zero' := by funext i; rfl
      map_add' := by intro x y; funext i; rfl }
  have hker : f.ker = AddSubgroup.pi Set.univ S := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_pi]
    simp only [Set.mem_univ, true_implies]
    constructor
    · intro h i
      have h2 : QuotientAddGroup.mk' (S i) (x i) = 0 := congrFun h i
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at h2
      exact h2
    · intro h
      funext i
      change QuotientAddGroup.mk' (S i) (x i) = 0
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      exact h i
  have hsurj : Function.Surjective f := by
    intro y
    choose x hx using fun i => QuotientAddGroup.mk'_surjective (S i) (y i)
    exact ⟨fun i => x i, by funext i; exact hx i⟩
  exact ⟨(QuotientAddGroup.quotientAddEquivOfEq hker).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj)⟩

end PiQuotient

/-! ## The currying isomorphism on `1`-cocycles -/

variable {G : Type*} [TopologicalSpace G] [Group G]
variable {ι : Type*} [Fintype ι]
variable {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, DistribMulAction G (M i)]

/-- Coordinate extraction `Z¹(G, ∏ᵢ Mᵢ) → ∏ᵢ Z¹(G, Mᵢ)`. -/
def z1PiHom : Z1 G (∀ i, M i) →+ (∀ i, Z1 G (M i)) where
  toFun f := fun i => ⟨fun g => (f : G → ∀ i, M i) g i, by
    rw [mem_Z1_iff]
    have hf : Work.GroupCohomology.IsCrossedHom G (∀ i, M i) (f : G → ∀ i, M i) ∧
        IsLocallyConstant (f : G → ∀ i, M i) := f.2
    constructor
    · intro g h
      have h2 := congrFun (hf.1 g h) i
      simpa using h2
    · intro x
      obtain ⟨U, hU, hxU, hc⟩ := hf.2 x
      exact ⟨U, hU, hxU, fun y hy => congrFun (hc y hy) i⟩⟩
  map_zero' := by ext i g; rfl
  map_add' := by intro f f'; ext i g; rfl

/-- Assembly `∏ᵢ Z¹(G, Mᵢ) → Z¹(G, ∏ᵢ Mᵢ)`.  Local constancy uses that `ι` is finite. -/
def z1PiInv : (∀ i, Z1 G (M i)) →+ Z1 G (∀ i, M i) where
  toFun F := ⟨fun g i => (F i : G → M i) g, by
    rw [mem_Z1_iff]
    constructor
    · intro g h; funext i; exact (F i).2.1 g h
    · intro x
      choose U hU hxU hc using fun i => ((F i).2.2) x
      exact ⟨⋂ i, U i, isOpen_iInter_of_finite hU, Set.mem_iInter.mpr hxU,
        fun y hy => funext fun i => hc i y (Set.mem_iInter.mp hy i)⟩⟩
  map_zero' := by ext i g; rfl
  map_add' := by intro F F'; ext i g; rfl

/-- **`Z¹` commutes with finite products of coefficients.** -/
def z1PiEquiv : Z1 G (∀ i, M i) ≃+ (∀ i, Z1 G (M i)) where
  toFun := z1PiHom
  invFun := z1PiInv
  map_add' := z1PiHom.map_add
  left_inv := fun f => by apply Subtype.ext; funext g i; rfl
  right_inv := fun F => by funext i; apply Subtype.ext; funext g; rfl

@[simp] theorem z1PiEquiv_coe_apply (f : Z1 G (∀ i, M i)) (i : ι) (g : G) :
    ((z1PiEquiv f i : Z1 G (M i)) : G → M i) g = (f : G → ∀ i, M i) g i := rfl


/-! ## The main statement -/

theorem nonempty_h1_pi_equiv {G : Type*} [TopologicalSpace G] [Group G] {ι : Type*} [Fintype ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, DistribMulAction G (M i)] : Nonempty (Work.AbsoluteKummer.H1 G (∀ i, M i) ≃+ (∀ i, Work.AbsoluteKummer.H1 G (M i))) := by
  -- `z1PiEquiv` carries the `1`-coboundaries of the product onto the tuples of `1`-coboundaries.
  have hiff : ∀ f : Z1 G (∀ i, M i),
      f ∈ (B1 G (∀ i, M i)).comap (Z1 G (∀ i, M i)).subtype ↔
        z1PiEquiv f ∈ AddSubgroup.pi Set.univ
          (fun i => (B1 G (M i)).comap (Z1 G (M i)).subtype) := by
    intro f
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_pi, Set.mem_univ, true_implies, mem_B1_iff]
    constructor
    · rintro ⟨a, ha⟩ i
      refine ⟨a i, ?_⟩
      funext g
      have h2 := congrFun (congrFun ha g) i
      simpa [GroupCohomology.d0_apply, z1PiEquiv_coe_apply, AddSubgroup.coe_subtype,
        Pi.sub_apply, Pi.smul_apply] using h2
    · rintro h
      choose a ha using h
      refine ⟨fun i => a i, ?_⟩
      funext g i
      have h2 := congrFun (ha i) g
      simpa [GroupCohomology.d0_apply, z1PiEquiv_coe_apply, AddSubgroup.coe_subtype,
        Pi.sub_apply, Pi.smul_apply] using h2
  have hmap : AddSubgroup.map (z1PiEquiv (M := M)).toAddMonoidHom
      ((B1 G (∀ i, M i)).comap (Z1 G (∀ i, M i)).subtype) =
      AddSubgroup.pi Set.univ (fun i => (B1 G (M i)).comap (Z1 G (M i)).subtype) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hiff x).mp hx
    · intro hy
      refine ⟨z1PiEquiv.symm y, (hiff (z1PiEquiv.symm y)).mpr ?_, by simp⟩
      simpa using hy
  have e1 : Work.AbsoluteKummer.H1 G (∀ i, M i) ≃+
      ((∀ i, Z1 G (M i)) ⧸ AddSubgroup.pi Set.univ
        (fun i => (B1 G (M i)).comap (Z1 G (M i)).subtype)) :=
    QuotientAddGroup.congr _ _ (z1PiEquiv (M := M)) hmap
  obtain ⟨e2⟩ := nonempty_pi_quotient_equiv
    (fun i => (B1 G (M i)).comap (Z1 G (M i)).subtype)
  exact ⟨e1.trans e2⟩

end

end Work.AbsoluteKummer.H1Pi
