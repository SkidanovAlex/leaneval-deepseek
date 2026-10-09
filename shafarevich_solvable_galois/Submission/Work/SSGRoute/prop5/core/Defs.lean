import Mathlib
import Submission.Work.SSGRoute.prop5.magnus_mem_one_add
import Submission.Work.SSGRoute.prop5.magnusGroupPart
import Submission.Work.SSGRoute.prop5.coreGraded
import Submission.Work.SSGRoute.prop5.witt.Basic
import Submission.Work.SSGRoute.prop5.witt.Vocab
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vocabulary for the Magnus core theorem

The core statement proved in this subdirectory is the "hard half" of the Magnus embedding theorem:
if `y ∈ γ_{n+1}` (Mathlib: `y ∈ lowerCentralSeries n`) and the Magnus image of `y` is congruent to
`1` modulo the degree `n+2` part of the truncated free associative algebra, then `y ∈ γ_{n+2}`.

The proof runs through the associated graded of the lower central series

`Λ_q = γ_q/γ_{q+1}`  (Mathlib indexing: `γ_q = (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries q`)

and the two monomial evaluations attached to a binary tree `c`:

* `monGrp X c`, the commutator monomial in the free group, of weight `Magma.size c`;
* `monBrk X c`, the bracketed monomial in `FreeAssoc X = ℤ[FreeMonoid X]`.

This file collects the vocabulary: the graded pieces, the class map, and the linear maps from the
free `ℤ`-module on the trees of a fixed size (resp. on the *Hall* trees of a fixed size) to the
graded piece, together with the corresponding map into the truncated associative algebra.
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5
namespace core

variable {X : Type*}

/-- The commutator monomial in the free group attached to a binary tree: generators go to the
corresponding free generator and a product of trees to the group commutator. -/
def monGrp (X : Type*) : Magma X → FreeGroup X
  | .gen x => FreeGroup.of x
  | .mul a b => ⁅monGrp X a, monGrp X b⁆

@[simp] theorem monGrp_gen (X : Type*) (x : X) : monGrp X (.gen x) = FreeGroup.of x := rfl

@[simp] theorem monGrp_mul (X : Type*) (a b : Magma X) :
    monGrp X (.mul a b) = ⁅monGrp X a, monGrp X b⁆ := rfl

/-- The `q`-th term of the lower central series of a free group (Mathlib indexing: `Gam 0 = ⊤`,
`Gam 1 = [F,F]`, ...), i.e. the paper's `γ_{q+1}`. -/
abbrev Gam (X : Type*) (q : ℕ) : Subgroup (FreeGroup X) :=
  graded.Gam (G := FreeGroup X) q

/-- The commutator monomial of a binary tree lies in the corresponding term of the lower central
series. -/
theorem monGrp_mem_Gam (c : Magma X) : monGrp X c ∈ Gam X (Magma.size c - 1) := by
  induction c with
  | gen x => simp [Magma.size_gen]
  | mul a b iha ihb =>
      rw [monGrp_mul, Magma.size_mul]
      have h := commutator_lowerCentralSeries_le (FreeGroup X) (Magma.size a - 1) (Magma.size b - 1)
        (Subgroup.commutator_mem_commutator iha ihb)
      have hidx : Magma.size a - 1 + (Magma.size b - 1) + 1 = Magma.size a + Magma.size b - 1 := by
        have ha := Magma.size_pos a
        have hb := Magma.size_pos b
        omega
      rwa [hidx] at h

/-- The `q`-th graded piece `γ_q/γ_{q+1}` of the lower central series of a free group, written
additively so that it is a `ℤ`-module. -/
abbrev Lam (X : Type*) (q : ℕ) : Type _ := Additive (graded.GLam (G := FreeGroup X) q)

instance instGamNormal (X : Type*) (q : ℕ) : (Gam X q).Normal :=
  graded.Gam_normal (G := FreeGroup X) q

instance instLamNormal (X : Type*) (q : ℕ) :
    ((Gam X (q + 1)).subgroupOf (Gam X q)).Normal :=
  (instGamNormal X (q + 1)).subgroupOf (Gam X q)

/-- The class map `γ_q → γ_q/γ_{q+1}`, multiplicatively. -/
def clMul (X : Type*) (q : ℕ) : Gam X q →* graded.GLam (G := FreeGroup X) q where
  toFun x := QuotientGroup.mk x
  map_one' := rfl
  map_mul' := fun a b => rfl

/-- The class map `γ_q → γ_q/γ_{q+1}`, additively. -/
def cl (X : Type*) (q : ℕ) : Additive (Gam X q) →+ Lam X q :=
  (clMul X q).toAdditive

/-- The class in `Λ_q` of a member of `γ_q`. -/
def cls (X : Type*) (q : ℕ) (x : Gam X q) : Lam X q := cl X q (Additive.ofMul x)

@[simp] theorem cls_apply (X : Type*) (q : ℕ) (x : Gam X q) :
    cls X q x = Additive.ofMul (clMul X q x) := rfl

theorem cls_eq_zero_iff {q : ℕ} {x : Gam X q} :
    cls X q x = 0 ↔ (x : FreeGroup X) ∈ Gam X (q + 1) := by
  change (clMul X q x : graded.GLam (G := FreeGroup X) q) = 1 ↔ _
  rw [clMul]
  exact QuotientGroup.eq_one_iff x

/-- The class of the commutator monomial of a tree of size `k`, in `Λ_{k-1}`. -/
def treeCl (X : Type*) (c : Magma X) : Lam X (Magma.size c - 1) :=
  cls X (Magma.size c - 1) ⟨monGrp X c, monGrp_mem_Gam c⟩

/-- The trees of size `k`. -/
abbrev TreeIdx (X : Type*) (k : ℕ) := {c : Magma X // Magma.size c = k}

/-- The Hall trees of size `k`. -/
abbrev HallIdx (X : Type*) [LinearOrder X] (k : ℕ) := {h : Magma X // IsHall h ∧ Magma.size h = k}

/-- The class of the commutator monomial of a tree of size `k`, as a function of the tree. -/
def treeClOf (X : Type*) (k : ℕ) (c : TreeIdx X k) : Lam X (k - 1) :=
  cls X (k - 1) ⟨monGrp X c.1, by simpa [c.2] using monGrp_mem_Gam c.1⟩

/-- The class of the commutator monomial of a Hall tree of size `k`. -/
def hallClOf (X : Type*) [LinearOrder X] (k : ℕ) (h : HallIdx X k) : Lam X (k - 1) :=
  cls X (k - 1) ⟨monGrp X h.1, by simpa [h.2.2] using monGrp_mem_Gam h.1⟩

/-- The `ℤ`-linear map sending a tree of size `k` to the class of its commutator monomial. -/
def treeToLam (X : Type*) (k : ℕ) : (TreeIdx X k →₀ ℤ) →ₗ[ℤ] Lam X (k - 1) :=
  Finsupp.linearCombination ℤ (treeClOf X k)

/-- The `ℤ`-linear map sending a Hall tree of size `k` to the class of its commutator monomial. -/
def hallToLam (X : Type*) [LinearOrder X] (k : ℕ) :
    (HallIdx X k →₀ ℤ) →ₗ[ℤ] Lam X (k - 1) :=
  Finsupp.linearCombination ℤ (hallClOf X k)

/-- The `ℤ`-linear map sending a Hall tree of size `k` to the image of its bracketed monomial in
the truncated associative algebra `FreeAssoc X ⧸ fil X (k+1)`. -/
def hallToA (X : Type*) [LinearOrder X] (k : ℕ) :
    (HallIdx X k →₀ ℤ) →ₗ[ℤ] (FreeAssoc X ⧸ fil X (k + 1)) :=
  Finsupp.linearCombination ℤ
    (fun h : HallIdx X k => Ideal.Quotient.mk (fil X (k + 1)) (monBrk X h.1))

@[simp] theorem treeToLam_single (k : ℕ) (c : TreeIdx X k) :
    treeToLam X k (Finsupp.single c 1) = treeClOf X k c := by
  rw [treeToLam, Finsupp.linearCombination_single, one_smul]

@[simp] theorem hallToLam_single [LinearOrder X] (k : ℕ) (h : HallIdx X k) :
    hallToLam X k (Finsupp.single h 1) = hallClOf X k h := by
  rw [hallToLam, Finsupp.linearCombination_single, one_smul]

@[simp] theorem hallToA_single [LinearOrder X] (k : ℕ) (h : HallIdx X k) :
    hallToA X k (Finsupp.single h 1) =
      Ideal.Quotient.mk (fil X (k + 1)) (monBrk X h.1) := by
  rw [hallToA, Finsupp.linearCombination_single, one_smul]

end core
end Work.SSGRoute.prop5
