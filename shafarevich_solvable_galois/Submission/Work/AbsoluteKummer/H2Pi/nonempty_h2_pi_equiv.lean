/-
# `H²` commutes with finite products of coefficient modules

For a topological group `G` and a finite family `(M i)` of additive commutative groups with a
`G`-action, second continuous cohomology commutes with the product of the coefficients:

  `H²(G, ∏ᵢ Mᵢ) ≃+ ∏ᵢ H²(G, Mᵢ)`.

The proof is the exact analogue of `Submission/Work/AbsoluteKummer/H1Pi/nonempty_h1_pi_equiv.lean`
one degree up:

* locally constant functions into a product are exactly the tuples of locally constant functions
  (`Fintype ι` is used through the finiteness of the intersection of the open sets);
* consequently the coordinate extraction `Z²(G, ∏ᵢ Mᵢ) → ∏ᵢ Z²(G, Mᵢ)` is an isomorphism of
  additive groups (both the inhomogeneous `2`-cocycle identity and local constancy are *pointwise*
  conditions, so they hold componentwise), and it carries the `2`-coboundaries of the product onto
  the tuples of `2`-coboundaries (again pointwise: `d¹` is defined componentwise);
* a quotient of a product by a product of subgroups is the product of the quotients
  (`Work.AbsoluteKummer.H1Pi.nonempty_pi_quotient_equiv`).

This is the input of the reduction of the trivial-action base case of `α²`
(`Work.SSGRoute.PT.alphaTwo_trivAction_of_trivMod`) to the module `ℤ/p`.
-/
import Mathlib
import Submission.Work.AbsoluteKummer.Defs
import Submission.Work.AbsoluteKummer.H1Pi.nonempty_h1_pi_equiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.H2Pi

open scoped Classical

noncomputable section

variable {G : Type*} [TopologicalSpace G] [Group G]
variable {ι : Type*} [Fintype ι]
variable {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, DistribMulAction G (M i)]

/-- The inhomogeneous differential `d¹` is computed coordinatewise on a product of coefficients. -/
theorem d1_pi_apply {A : ι → Type*} [∀ i, AddCommGroup (A i)]
    [∀ i, DistribMulAction G (A i)] (a : G → (∀ i, A i)) (g h : G) (i : ι) :
    (Work.GroupCohomology.d1 G (∀ i, A i) a (g, h)) i =
      Work.GroupCohomology.d1 G (A i) (fun g => a g i) (g, h) := by
  simp only [Work.GroupCohomology.d1_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]

/-! ## The currying isomorphism on `2`-cocycles -/

/-- Coordinate extraction `Z²(G, ∏ᵢ Mᵢ) → ∏ᵢ Z²(G, Mᵢ)`. -/
def z2PiHom : Z2 G (∀ i, M i) →+ (∀ i, Z2 G (M i)) where
  toFun f := fun i => ⟨fun p => (f : G × G → ∀ i, M i) p i, by
    rw [mem_Z2_iff]
    have hf := (mem_Z2_iff (M := ∀ i, M i) (c := (f : G × G → ∀ i, M i))).mp f.2
    constructor
    · intro g h k
      have h2 := congrFun (hf.1 g h k) i
      simpa using h2
    · intro x
      obtain ⟨U, hU, hxU, hc⟩ := hf.2 x
      exact ⟨U, hU, hxU, fun y hy => congrFun (hc y hy) i⟩⟩
  map_zero' := by ext i p; rfl
  map_add' := by intro f f'; ext i p; rfl

/-- Assembly `∏ᵢ Z²(G, Mᵢ) → Z²(G, ∏ᵢ Mᵢ)`.  Local constancy uses that `ι` is finite. -/
def z2PiInv : (∀ i, Z2 G (M i)) →+ Z2 G (∀ i, M i) where
  toFun F := ⟨fun p i => (F i : G × G → M i) p, by
    rw [mem_Z2_iff]
    constructor
    · intro g h k
      funext i
      exact ((mem_Z2_iff (M := M i) (c := (F i : G × G → M i))).mp (F i).2).1 g h k
    · intro x
      choose U hU hxU hc using fun i =>
        ((mem_Z2_iff (M := M i) (c := (F i : G × G → M i))).mp (F i).2).2 x
      exact ⟨⋂ i, U i, isOpen_iInter_of_finite hU, Set.mem_iInter.mpr hxU,
        fun y hy => funext fun i => hc i y (Set.mem_iInter.mp hy i)⟩⟩
  map_zero' := by ext i g h; rfl
  map_add' := by intro F F'; ext i g h; rfl

/-- **`Z²` commutes with finite products of coefficients.** -/
def z2PiEquiv : Z2 G (∀ i, M i) ≃+ (∀ i, Z2 G (M i)) where
  toFun := z2PiHom
  invFun := z2PiInv
  map_add' := z2PiHom.map_add
  left_inv := fun f => by apply Subtype.ext; funext p i; rfl
  right_inv := fun F => by funext i; apply Subtype.ext; funext p; rfl

@[simp] theorem z2PiEquiv_coe_apply (f : Z2 G (∀ i, M i)) (i : ι) (p : G × G) :
    ((z2PiEquiv f i : Z2 G (M i)) : G × G → M i) p = (f : G × G → ∀ i, M i) p i := rfl

/-! ## The main statement -/

theorem nonempty_h2_pi_equiv {G : Type*} [TopologicalSpace G] [Group G] {ι : Type*} [Fintype ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, DistribMulAction G (M i)] :
    Nonempty (Work.AbsoluteKummer.H2 G (∀ i, M i) ≃+
      (∀ i, Work.AbsoluteKummer.H2 G (M i))) := by
  -- `z2PiEquiv` carries the `2`-coboundaries of the product onto the tuples of `2`-coboundaries.
  have hiff : ∀ c : Z2 G (∀ i, M i),
      c ∈ (B2 G (∀ i, M i)).comap (Z2 G (∀ i, M i)).subtype ↔
        z2PiEquiv c ∈ AddSubgroup.pi Set.univ
          (fun i => (B2 G (M i)).comap (Z2 G (M i)).subtype) := by
    intro c
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_pi, Set.mem_univ, true_implies, mem_B2_iff]
    constructor
    · rintro ⟨a, ha, hac⟩ i
      refine ⟨fun g => a g i, ?_, ?_⟩
      · rw [mem_C1c_iff]
        have ha' : IsLocallyConstant a := (mem_C1c_iff a).mp ha
        intro x
        obtain ⟨U, hU, hxU, hc⟩ := ha' x
        exact ⟨U, hU, hxU, fun y hy => congrFun (hc y hy) i⟩
      · funext p
        obtain ⟨g, h⟩ := p
        have h2 := congrFun (congrFun hac (g, h)) i
        rw [d1_pi_apply] at h2
        simpa using h2
    · rintro h
      choose a ha hac using h
      refine ⟨fun g i => a i g, ?_, ?_⟩
      · rw [mem_C1c_iff]
        intro x
        choose U hU hxU hc using fun i => (mem_C1c_iff (a i)).mp (ha i) x
        exact ⟨⋂ i, U i, isOpen_iInter_of_finite hU, Set.mem_iInter.mpr hxU,
          fun y hy => funext fun i => hc i y (Set.mem_iInter.mp hy i)⟩
      · funext p i
        obtain ⟨g, h⟩ := p
        have h2 := congrFun (hac i) (g, h)
        rw [d1_pi_apply]
        simpa using h2
  have hmap : AddSubgroup.map (z2PiEquiv (M := M)).toAddMonoidHom
      ((B2 G (∀ i, M i)).comap (Z2 G (∀ i, M i)).subtype) =
      AddSubgroup.pi Set.univ (fun i => (B2 G (M i)).comap (Z2 G (M i)).subtype) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hiff x).mp hx
    · intro hy
      refine ⟨z2PiEquiv.symm y, (hiff (z2PiEquiv.symm y)).mpr ?_, by simp⟩
      simpa using hy
  have e1 : Work.AbsoluteKummer.H2 G (∀ i, M i) ≃+
      ((∀ i, Z2 G (M i)) ⧸ AddSubgroup.pi Set.univ
        (fun i => (B2 G (M i)).comap (Z2 G (M i)).subtype)) :=
    QuotientAddGroup.congr _ _ (z2PiEquiv (M := M)) hmap
  obtain ⟨e2⟩ := H1Pi.nonempty_pi_quotient_equiv
    (fun i => (B2 G (M i)).comap (Z2 G (M i)).subtype)
  exact ⟨e1.trans e2⟩

end

end Work.AbsoluteKummer.H2Pi
