import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Module.Submodule.Range
import Submission.Work.SSGRoute.prop5.core.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The commutator monomials of weight `k` span `γ_{k-1}/γ_k`

`gen_span`: if `y ∈ γ_{k-1}` (Mathlib indexing, `Gam X (k-1)`) then the class of `y` in the
graded piece `Λ_{k-1} = γ_{k-1}/γ_k` of the lower central series lies in the `ℤ`-span of the
classes `treeClOf X k c` of the commutator monomials `monGrp X c` attached to the binary trees `c`
with `k` leaves.

## Route

For `n : ℕ` let `clsInRange X n ≤ FreeGroup X` be the set of `v ∈ γ_n` whose class in
`Λ_n = γ_n/γ_{n+1}` lies in the range of `treeToLam X (n+1)`.  This is a subgroup, because the
class map is additive; we prove `Gam X n ≤ clsInRange X n` by induction on `n`.

* `n = 0`: `γ_0 = ⊤`, and the range of `treeToLam X 1` is the span of the classes of the trees
  with one leaf, i.e. of the free generators;  by `lam0_span_gen` these span all of `Λ_0 = F/F'`.
* `n+1`: `γ_{n+1} = ⁅γ_n, ⊤⁆`, so by `Subgroup.commutator_le` it suffices to treat the commutator
  `⁅u, f⁆` of `u ∈ γ_n` with an arbitrary `f ∈ F`.  Its class is the graded bracket of the class
  of `u` with the class of `f` (`cls_commutator_of`), the first factor lies in the range of
  `treeToLam X (n+1)` by the induction hypothesis, and the second factor lies in the span of the
  generator classes (`lam0_span_gen`).  The bilinearity of the graded bracket
  (`tree_bracket_mem`) then puts the result in the range of `treeToLam X (n+2)`.
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5.core

variable {X : Type*}

/-! ## Elementary additivity of the class map -/

/-- The class of a product is the sum of the classes. -/
theorem gs_cls_mul (n : ℕ) (a b : Gam X n) : cls X n (a * b) = cls X n a + cls X n b := rfl

/-- The class of `1` is `0`. -/
theorem gs_cls_one (n : ℕ) : cls X n (1 : Gam X n) = 0 := by
  rw [cls_apply]
  exact map_zero (cl X n)

/-- The class of an inverse is the negative of the class. -/
theorem gs_cls_inv (n : ℕ) (a : Gam X n) : cls X n a⁻¹ = -cls X n a := by
  show Additive.ofMul ((clMul X n) a⁻¹) = -Additive.ofMul ((clMul X n) a)
  exact map_neg (cl X n) (Additive.ofMul a)

/-- The class in `Λ_n` of an element of `γ_n`, with the membership proof as an explicit
argument. -/
def clsRaw (X : Type*) (n : ℕ) (g : FreeGroup X) (hg : g ∈ Gam X n) : Lam X n :=
  cls X n ⟨g, hg⟩

@[simp] theorem clsRaw_apply (n : ℕ) (g : FreeGroup X) (hg : g ∈ Gam X n) :
    clsRaw X n g hg = cls X n ⟨g, hg⟩ := rfl

/-- `clsRaw` does not depend on the chosen membership proof. -/
theorem clsRaw_congr {n : ℕ} {g : FreeGroup X} (h₁ h₂ : g ∈ Gam X n) :
    clsRaw X n g h₁ = clsRaw X n g h₂ :=
  congrArg (cls X n) (Subtype.ext rfl)

/-- The classes of the free generators in `Λ_0 = F/F'`. -/
def genClass (X : Type*) (x : X) : Lam X 0 :=
  cls X 0 ⟨FreeGroup.of x, (trivial : FreeGroup.of x ∈ Gam X 0)⟩

/-- **The class of a commutator is the graded bracket of the classes** (`bracketL` computes the
graded bracket on classes of commutators, cf. `graded.bracketL_apply_mk`). -/
theorem cls_commutator_of (n : ℕ) (u : FreeGroup X) (hu : u ∈ Gam X n)
    (f : FreeGroup X) (hf : f ∈ Gam X 0) (h : ⁅u, f⁆ ∈ Gam X (n + 1)) :
    cls X (n + 1) ⟨⁅u, f⁆, h⟩ =
      graded.bracketL (G := FreeGroup X) n 0 (clsRaw X n u hu) (clsRaw X 0 f hf) := by
  rw [clsRaw_apply, clsRaw_apply]
  rw [show cls X (n + 1) ⟨⁅u, f⁆, h⟩ =
        Additive.ofMul (QuotientGroup.mk' ((Gam X (n + 1 + 1)).subgroupOf (Gam X (n + 1)))
          ⟨⁅u, f⁆, h⟩) from rfl,
      show cls X n ⟨u, hu⟩ =
        Additive.ofMul (QuotientGroup.mk' ((Gam X (n + 1)).subgroupOf (Gam X n))
          ⟨u, hu⟩) from rfl,
      show cls X 0 ⟨f, hf⟩ =
        Additive.ofMul (QuotientGroup.mk' ((Gam X (0 + 1)).subgroupOf (Gam X 0))
          ⟨f, hf⟩) from rfl,
      graded.bracketL_apply_mk]
  rfl

/-- The graded bracket of the class of `u ∈ γ_n` with the class of an element of `γ_0` is the
class of the commutator, with the membership proof displayed as it occurs in `treeClOf`. -/
theorem bracketL_clsRaw_comm (n : ℕ) (u : FreeGroup X) (hu : u ∈ Gam X n)
    (v : FreeGroup X) (hv : v ∈ Gam X 0) :
    graded.bracketL (G := FreeGroup X) n 0 (clsRaw X n u hu) (clsRaw X 0 v hv) =
      clsRaw X (n + 1) ⁅u, v⁆ (graded.commutator_mem_Gam (p := n) (q := 0) hu hv) :=
  (cls_commutator_of n u hu v hv (graded.commutator_mem_Gam (p := n) (q := 0) hu hv)).symm

/-! ## `Λ_0` is spanned by the classes of the free generators -/

theorem lam0_span_gen (X : Type) (w : Lam X 0) :
    w ∈ Submodule.span ℤ (Set.range (genClass X)) := by
  have key : ∀ (g : FreeGroup X) (hg : g ∈ Gam X 0),
      clsRaw X 0 g hg ∈ Submodule.span ℤ (Set.range (genClass X)) := by
    intro g
    refine FreeGroup.induction_on g ?_ ?_ ?_ ?_
    · intro hg
      have h : clsRaw X 0 1 hg = cls X 0 (1 : Gam X 0) :=
        Eq.trans (clsRaw_congr hg (trivial : (1 : FreeGroup X) ∈ Gam X 0))
          (congrArg (cls X 0) (Subtype.ext rfl))
      rw [h, gs_cls_one]
      exact Submodule.zero_mem _
    · intro x hg
      have h : clsRaw X 0 (FreeGroup.of x) hg = genClass X x :=
        Eq.trans (clsRaw_congr hg (trivial : FreeGroup.of x ∈ Gam X 0))
          (congrArg (cls X 0) (Subtype.ext rfl))
      rw [h]
      exact Submodule.subset_span ⟨x, rfl⟩
    · intro x ih hg
      have h : clsRaw X 0 (FreeGroup.of x)⁻¹ hg =
          -(clsRaw X 0 (FreeGroup.of x) (trivial : FreeGroup.of x ∈ Gam X 0)) :=
        Eq.trans (clsRaw_congr hg (trivial : (FreeGroup.of x)⁻¹ ∈ Gam X 0))
          (Eq.trans (congrArg (cls X 0) (Subtype.ext rfl))
            (gs_cls_inv 0 ⟨FreeGroup.of x, (trivial : FreeGroup.of x ∈ Gam X 0)⟩))
      rw [h]
      exact Submodule.neg_mem _ (ih (trivial : FreeGroup.of x ∈ Gam X 0))
    · intro x y ihx ihy hg
      have h : clsRaw X 0 (x * y) hg =
          clsRaw X 0 x (trivial : x ∈ Gam X 0) +
            clsRaw X 0 y (trivial : y ∈ Gam X 0) :=
        Eq.trans (clsRaw_congr hg (trivial : (x * y) ∈ Gam X 0))
          (Eq.trans (congrArg (cls X 0) (Subtype.ext rfl))
            (gs_cls_mul 0 ⟨x, (trivial : x ∈ Gam X 0)⟩ ⟨y, (trivial : y ∈ Gam X 0)⟩))
      rw [h]
      exact Submodule.add_mem _ (ihx (trivial : x ∈ Gam X 0)) (ihy (trivial : y ∈ Gam X 0))
  obtain ⟨f, rfl⟩ : ∃ f : Gam X 0, cls X 0 f = w := by
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective ((Gam X (0 + 1)).subgroupOf (Gam X 0))
      (Additive.toMul w)
    refine ⟨a, ?_⟩
    rw [show cls X 0 a = Additive.ofMul (QuotientGroup.mk'
          ((Gam X (0 + 1)).subgroupOf (Gam X 0)) a) from rfl, ha]
    rfl
  exact key f.1 f.2

/-! ## The bilinearity of the graded bracket on the span of the trees -/

theorem tree_bracket_mem (X : Type) (n : ℕ) (φ : TreeIdx X (n + 1) →₀ ℤ) (w : Lam X 0)
    (hw : w ∈ Submodule.span ℤ (Set.range (genClass X))) :
    graded.bracketL (G := FreeGroup X) n 0 (treeToLam X (n + 1) φ) w ∈
      LinearMap.range (treeToLam X (n + 2)) := by
  -- a single tree against a generator class
  have key1 : ∀ (c : TreeIdx X (n + 1)) (x : X),
      graded.bracketL (G := FreeGroup X) n 0 (treeClOf X (n + 1) c) (genClass X x) ∈
        LinearMap.range (treeToLam X (n + 2)) := by
    intro c x
    have hsize : Magma.size (Magma.mul c.1 (Magma.gen x)) = n + 2 := by
      rw [Magma.size_mul, Magma.size_gen, c.2]
    refine ⟨Finsupp.single ⟨Magma.mul c.1 (Magma.gen x), hsize⟩ 1, ?_⟩
    rw [treeToLam_single]
    have hu : monGrp X c.1 ∈ Gam X n := by
      have h : Magma.size c.1 - 1 = n := by omega
      simpa only [h] using monGrp_mem_Gam c.1
    have hf : FreeGroup.of x ∈ Gam X 0 := trivial
    have hc : ⁅monGrp X c.1, FreeGroup.of x⁆ ∈ Gam X (n + 0 + 1) :=
      graded.commutator_mem_Gam (p := n) (q := 0) hu hf
    have hA : treeClOf X (n + 1) c = clsRaw X n (monGrp X c.1) hu :=
      congrArg (cls X n) (Subtype.ext rfl)
    have hB : genClass X x = clsRaw X 0 (FreeGroup.of x) hf :=
      congrArg (cls X 0) (Subtype.ext rfl)
    have hC : treeClOf X (n + 2) ⟨Magma.mul c.1 (Magma.gen x), hsize⟩ =
        clsRaw X (n + 1) (monGrp X (Magma.mul c.1 (Magma.gen x))) hc :=
      congrArg (cls X (n + 1)) (Subtype.ext rfl)
    rw [hC, hA, hB, bracketL_clsRaw_comm n (monGrp X c.1) hu (FreeGroup.of x) hf]
    rfl
  -- a single tree against an element of the span
  have key2 : ∀ (c : TreeIdx X (n + 1)) (w : Lam X 0),
      w ∈ Submodule.span ℤ (Set.range (genClass X)) →
        graded.bracketL (G := FreeGroup X) n 0 (treeClOf X (n + 1) c) w ∈
          LinearMap.range (treeToLam X (n + 2)) := by
    intro c w hw
    refine Submodule.span_induction
      (p := fun w (_ : w ∈ Submodule.span ℤ (Set.range (genClass X))) =>
        graded.bracketL (G := FreeGroup X) n 0 (treeClOf X (n + 1) c) w ∈
          LinearMap.range (treeToLam X (n + 2))) ?_ ?_ ?_ ?_ hw
    · intro w hw
      obtain ⟨y, rfl⟩ := hw
      exact key1 c y
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro x y hx hy ihx ihy
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
    · intro a x hx ih
      rw [map_zsmul]
      exact Submodule.smul_mem _ a ih
  -- an arbitrary element of the free module on the trees
  refine Finsupp.induction_linear φ ?_ ?_ ?_
  · rw [map_zero, map_zero]
    exact Submodule.zero_mem _
  · intro f g hf hg
    rw [map_add, map_add]
    exact Submodule.add_mem _ hf hg
  · intro c a
    have hφ : (Finsupp.single c a : TreeIdx X (n + 1) →₀ ℤ) = a • Finsupp.single c 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hφ, map_smul, treeToLam_single, map_zsmul]
    exact Submodule.smul_mem _ a (key2 c w hw)

/-! ## The subgroup of `γ_n` whose classes lie in the range of `treeToLam` -/

/-- The elements of `γ_n` whose class in `Λ_n` lies in the range of the map sending a tree of
size `n+1` to the class of its commutator monomial. -/
def clsInRange (X : Type*) (n : ℕ) : Subgroup (FreeGroup X) where
  carrier := {v | ∃ hv : v ∈ Gam X n, cls X n ⟨v, hv⟩ ∈ LinearMap.range (treeToLam X (n + 1))}
  mul_mem' := by
    rintro a b ⟨ha, hca⟩ ⟨hb, hcb⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have h : (⟨a * b, mul_mem ha hb⟩ : Gam X n) = (⟨a, ha⟩ : Gam X n) * ⟨b, hb⟩ :=
      Subtype.ext rfl
    rw [h, gs_cls_mul]
    exact Submodule.add_mem _ hca hcb
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    show cls X n (1 : Gam X n) ∈ LinearMap.range (treeToLam X (n + 1))
    rw [gs_cls_one]
    exact Submodule.zero_mem _
  inv_mem' := by
    rintro a ⟨ha, hca⟩
    refine ⟨inv_mem ha, ?_⟩
    have h : (⟨a⁻¹, inv_mem ha⟩ : Gam X n) = (⟨a, ha⟩ : Gam X n)⁻¹ := Subtype.ext rfl
    rw [h, gs_cls_inv]
    exact Submodule.neg_mem _ hca

/-- Membership in `clsInRange X n` is independent of the membership proof of the element. -/
theorem clsInRange_spec {n : ℕ} {v : FreeGroup X} (hv : v ∈ clsInRange X n)
    (h : v ∈ Gam X n) :
    cls X n ⟨v, h⟩ ∈ LinearMap.range (treeToLam X (n + 1)) := by
  obtain ⟨h₀, hc⟩ := hv
  have he : (⟨v, h⟩ : Gam X n) = ⟨v, h₀⟩ := Subtype.ext rfl
  rwa [he]

/-! ## The induction along the lower central series -/

theorem gam_le_clsInRange (X : Type) (n : ℕ) : Gam X n ≤ clsInRange X n := by
  induction n with
  | zero =>
      intro v hv
      refine ⟨hv, ?_⟩
      show cls X 0 ⟨v, hv⟩ ∈ LinearMap.range (treeToLam X 1)
      have hle : Submodule.span ℤ (Set.range (genClass X)) ≤
          LinearMap.range (treeToLam X 1) := by
        rw [Submodule.span_le]
        rintro w ⟨x, rfl⟩
        exact ⟨Finsupp.single ⟨Magma.gen x, rfl⟩ 1, by
          rw [treeToLam_single]
          exact congrArg (cls X 0) (Subtype.ext rfl)⟩
      exact hle (lam0_span_gen X _)
  | succ n ih =>
      show ⁅Gam X n, ⊤⁆ ≤ clsInRange X (n + 1)
      refine Subgroup.commutator_le.mpr ?_
      intro u hu f hf
      have hf₀ : f ∈ Gam X 0 := hf
      obtain ⟨φ, hφ⟩ := clsInRange_spec (X := X) (ih hu) hu
      refine ⟨graded.commutator_mem_Gam (p := n) (q := 0) hu hf₀, ?_⟩
      rw [cls_commutator_of (X := X) n u hu f hf₀
            (graded.commutator_mem_Gam (p := n) (q := 0) hu hf₀)]
      simp only [clsRaw_apply]
      rw [← hφ]
      exact tree_bracket_mem X n φ (cls X 0 ⟨f, hf₀⟩) (lam0_span_gen X _)

/-! ## The target -/

theorem gen_span (X : Type) (k : ℕ) (hk : 1 ≤ k) (y : FreeGroup X)
    (hy : y ∈ Work.SSGRoute.prop5.core.Gam X (k - 1)) :
    Work.SSGRoute.prop5.core.cls X (k - 1) ⟨y, hy⟩ ∈
      LinearMap.range (Work.SSGRoute.prop5.core.treeToLam X k) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, (Nat.sub_add_cancel hk).symm⟩
  exact clsInRange_spec (X := X) (gam_le_clsInRange X n hy) hy

end Work.SSGRoute.prop5.core
