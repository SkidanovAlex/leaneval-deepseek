import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Lie.Free
import Mathlib.FieldTheory.Normal.Defs
import Submission.Work.SSGRoute.prop5.core.relations_zero
import Submission.Work.SSGRoute.prop5.magLead_mem_nestedImage
import Submission.Work.SSGRoute.prop5.witt.Swap
import Submission.Work.SSGRoute.prop5.witt.hall_spanning
import Submission.Work.SSGRoute.prop5.witt.leading_term_coeff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open scoped commutatorElement
open Work.SSGRoute.prop5
universe u

-- >>> witt/Assembly.lean
/-
# Assembly of Witt's theorem from the Hall-set pieces

Given the four Hall-set inputs
* `hall_foliage_lt_right` : the foliages of Hall trees are smaller than their right subtrees,
* `hall_spanning` : the Hall bracketings span the free Lie algebra,
* `leading_term_coeff` : the foliage of a Hall tree is the leading word of its bracket
  evaluation, with coefficient `1`,
* `foliage_injective` : the foliage determines a Hall tree,
we prove that the canonical Lie homomorphism from the free Lie ring on `X` (over `ℤ`) to the
free associative ring is injective.
-/

set_option maxHeartbeats 4000000

namespace Work.SSGRoute.UpWitt

open scoped commutatorElement

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable {X : Type u} [LinearOrder X]

/-- The canonical Lie homomorphism from the free Lie ring on `X` to the free associative ring,
the latter regarded as a Lie ring through the commutator. -/
noncomputable def fL (X : Type u) : FreeLieAlgebra ℤ X →ₗ⁅ℤ⁆ FreeAlgebra ℤ X :=
  FreeLieAlgebra.lift ℤ (fun x => (FreeAlgebra.ι ℤ x : FreeAlgebra ℤ X))

theorem fL_monLie (w : Magma X) : fL X (monLie X w) = monBrkA X w := by
  induction w with
  | gen x => exact FreeLieAlgebra.lift_of_apply (fun x => (FreeAlgebra.ι ℤ x : FreeAlgebra ℤ X)) x
  | mul a b iha ihb =>
      rw [monLie_mul, LieHom.map_lie, monBrkA_mul, iha, ihb, LieRing.of_associative_ring_bracket]

/-- The `ℤ`-span of the Lie evaluations of the Hall trees. -/
noncomputable def Sp (X : Type u) [LinearOrder X] : Submodule ℤ (FreeLieAlgebra ℤ X) :=
  Submodule.span ℤ (Set.range (fun h : {h : Magma X // IsHall h} => monLie X h.1))

theorem Sp_lie_mem (hspan : ∀ w : Magma X, monLie X w ∈ Sp X) {x y : FreeLieAlgebra ℤ X}
    (hx : x ∈ Sp X) (hy : y ∈ Sp X) : ⁅x, y⁆ ∈ Sp X := by
  refine Submodule.span_induction (p := fun z _ => ∀ y ∈ Sp X, ⁅z, y⁆ ∈ Sp X) ?_ ?_ ?_ ?_ hx y hy
  · intro z hz y hy
    rcases hz with ⟨h, rfl⟩
    refine Submodule.span_induction (p := fun z _ => ⁅monLie X h.1, z⁆ ∈ Sp X) ?_ ?_ ?_ ?_ hy
    · intro z hz
      rcases hz with ⟨g, rfl⟩
      have h1 : monLie X (Magma.mul h.1 g.1) ∈ Sp X := hspan _
      rwa [monLie_mul] at h1
    · simp
    · intro a b _ _ ha hb; rw [lie_add]; exact Submodule.add_mem _ ha hb
    · intro c a _ ha; rw [lie_smul]; exact Submodule.smul_mem _ c ha
  · intro y hy; simp
  · intro a b _ _ ha hb y hy; rw [add_lie]; exact Submodule.add_mem _ (ha y hy) (hb y hy)
  · intro c a _ ha y hy; rw [smul_lie]; exact Submodule.smul_mem _ c (ha y hy)

theorem Sp_eq_top (hspan : ∀ w : Magma X, monLie X w ∈ Sp X) : Sp X = ⊤ := by
  let S' : LieSubalgebra ℤ (FreeLieAlgebra ℤ X) :=
    LieSubalgebra.mk (Sp X) (fun hx hy => Sp_lie_mem hspan hx hy)
  have hmem : ∀ x : X, FreeLieAlgebra.of ℤ x ∈ S' := by
    intro x
    exact hspan (Magma.gen x)
  let Ψ : FreeLieAlgebra ℤ X →ₗ⁅ℤ⁆ S' :=
    FreeLieAlgebra.lift ℤ (fun x => ⟨FreeLieAlgebra.of ℤ x, hmem x⟩)
  have hcomp : S'.incl.comp Ψ = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro x
    show S'.incl (Ψ (FreeLieAlgebra.of ℤ x)) = FreeLieAlgebra.of ℤ x
    have h1 : Ψ (FreeLieAlgebra.of ℤ x) = ⟨FreeLieAlgebra.of ℤ x, hmem x⟩ :=
      FreeLieAlgebra.lift_of_apply (fun y => (⟨FreeLieAlgebra.of ℤ y, hmem y⟩ : S')) x
    rw [h1]
    rfl
  have htop : ∀ z : FreeLieAlgebra ℤ X, z ∈ S'.toSubmodule := by
    intro z
    have hz : S'.incl (Ψ z) = z := by
      have h2 := congr_arg (fun (φ : FreeLieAlgebra ℤ X →ₗ⁅ℤ⁆ FreeLieAlgebra ℤ X) => φ z) hcomp
      simpa using h2
    rw [← hz]
    exact (Ψ z).2
  ext z
  simp only [Submodule.mem_top, iff_true]
  exact htop z

end

section Coeff

variable {X : Type u} [LinearOrder X]

/-- The coefficient of a word in `monBrkA X w` agrees with the corresponding coefficient of
`monBrk X w`. -/
theorem coeffF_zero (u : List X) : coeffF (0 : MonoidAlgebra ℤ (FreeMonoid X)) u = 0 := by
  simp [coeffF]

theorem coeffF_equivA (w : Magma X) (u : List X) :
    coeffF (monBrk X w) u
      = coeffF (FreeAlgebra.equivMonoidAlgebraFreeMonoid (monBrkA X w)) u :=
  (congrArg (fun a => coeffF a u) (equivMonoidAlgebra_monBrkA w)).symm

theorem coeffF_smul (c : ℤ) (a : MonoidAlgebra ℤ (FreeMonoid X)) (u : List X) :
    coeffF (c • a) u = c * coeffF a u := by
  simp only [coeffF]
  rw [MonoidAlgebra.coeff_smul_apply, smul_eq_mul]

theorem coeffF_sum {ι : Type*} (s : Finset ι) (f : ι → MonoidAlgebra ℤ (FreeMonoid X))
    (u : List X) :
    coeffF (∑ i ∈ s, f i) u = ∑ i ∈ s, coeffF (f i) u := by
  classical
  induction s using Finset.induction with
  | empty => simp [coeffF]
  | insert a s ha ih => simp [Finset.sum_insert ha, coeffF_add, ih]

end Coeff

section Main

variable {X : Type u} [LinearOrder X]

/-- The `monLie` images of distinct Hall trees are distinct in the free Lie algebra, as a
consequence of the leading-term description of the bracket evaluation. -/
theorem monLie_inj_of_coeff
    (hlead : ∀ c : Magma X, IsHall c →
      coeffF (monBrk X c) (Magma.foliage c) = 1 ∧
        ∀ w : List X, w < Magma.foliage c → coeffF (monBrk X c) w = 0)
    (hinj : ∀ a b : Magma X, IsHall a → IsHall b → Magma.foliage a = Magma.foliage b → a = b)
    {a b : Magma X} (ha : IsHall a) (hb : IsHall b) (h : monLie X a = monLie X b) : a = b := by
  by_cases hfab : Magma.foliage a = Magma.foliage b
  · exact hinj a b ha hb hfab
  · exfalso
    have hbrk : monBrkA X a = monBrkA X b := by
      have := congrArg (fL X) h
      rwa [fL_monLie, fL_monLie] at this
    rcases lt_or_gt_of_ne hfab with hlt | hgt
    · have hcoeff : coeffF (monBrk X a) (Magma.foliage a) = coeffF (monBrk X b) (Magma.foliage a) := by
        rw [coeffF_equivA a, coeffF_equivA b, hbrk]
      rw [(hlead a ha).1, (hlead b hb).2 _ hlt] at hcoeff
      exact one_ne_zero hcoeff
    · have hcoeff : coeffF (monBrk X a) (Magma.foliage b) = coeffF (monBrk X b) (Magma.foliage b) := by
        rw [coeffF_equivA a, coeffF_equivA b, hbrk]
      rw [(hlead b hb).1, (hlead a ha).2 _ hgt] at hcoeff
      exact one_ne_zero hcoeff.symm

/-- **Independence of the bracket evaluations of the Hall trees.** -/
theorem independence
    (hlead : ∀ c : Magma X, IsHall c →
      coeffF (monBrk X c) (Magma.foliage c) = 1 ∧
        ∀ w : List X, w < Magma.foliage c → coeffF (monBrk X c) w = 0)
    (hinj : ∀ a b : Magma X, IsHall a → IsHall b → Magma.foliage a = Magma.foliage b → a = b)
    (s : Finset {h : Magma X // IsHall h}) (α : {h : Magma X // IsHall h} → ℤ)
    (hzero : (∑ h ∈ s, α h • monBrkA X h.1) = 0) :
    ∀ h ∈ s, α h = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨h₁, h₁s, h₁ne⟩ := hcon
  set s' := s.filter (fun h => α h ≠ 0) with hs'
  have hs'ne : s'.Nonempty := ⟨h₁, by simp [hs', h₁s, h₁ne]⟩
  obtain ⟨h₀, h₀s', h₀min⟩ := Finset.exists_min_image s' (fun h => Magma.foliage h.1) hs'ne
  rw [hs', Finset.mem_filter] at h₀s'
  obtain ⟨h₀s, h₀ne⟩ := h₀s'
  -- transport the relation to the monoid algebra
  have hzero' : (∑ h ∈ s, α h • monBrk X h.1) = 0 := by
    have h2 := congrArg (FreeAlgebra.equivMonoidAlgebraFreeMonoid) hzero
    simpa [map_sum, equivMonoidAlgebra_monBrkA] using h2
  -- the coefficient of the minimal foliage
  have hkey : coeffF (∑ h ∈ s, α h • monBrk X h.1) (Magma.foliage h₀.1) = α h₀ := by
    rw [coeffF_sum, Finset.sum_eq_single h₀]
    · rw [coeffF_smul, (hlead h₀.1 h₀.2).1, mul_one]
    · intro h hs hne
      rw [coeffF_smul]
      by_cases hα : α h = 0
      · rw [hα, zero_mul]
      · have hh : h ∈ s' := by simp [hs', hs, hα]
        have hle := h₀min h hh
        rcases lt_or_eq_of_le hle with hlt | heq
        · rw [(hlead h.1 h.2).2 _ hlt, mul_zero]
        · exact absurd (Subtype.ext (hinj h₀.1 h.1 h₀.2 h.2 heq)).symm hne
    · intro h₀not; exact absurd h₀s h₀not
  rw [hzero', coeffF_zero] at hkey
  exact h₀ne hkey.symm

/-- Independence, in the finitely-supported-index form. -/
theorem independence_finsupp
    (hlead : ∀ c : Magma X, IsHall c →
      coeffF (monBrk X c) (Magma.foliage c) = 1 ∧
        ∀ w : List X, w < Magma.foliage c → coeffF (monBrk X c) w = 0)
    (hinj : ∀ a b : Magma X, IsHall a → IsHall b → Magma.foliage a = Magma.foliage b → a = b)
    (c : {h : Magma X // IsHall h} →₀ ℤ)
    (h : c.sum (fun h r => r • monBrkA X h.1) = 0) : c = 0 := by
  classical
  rw [Finsupp.ext_iff]
  intro h₀
  have hsum : (∑ h ∈ c.support, c h • monBrkA X h.1) = 0 := by
    rw [← Finsupp.sum_of_support_subset c (Finset.Subset.refl _)
      (fun h r => r • monBrkA X h.1) (by simp)]
    exact h
  have := independence hlead hinj c.support (fun h => c h) hsum
  by_cases hh : h₀ ∈ c.support
  · simpa using this h₀ hh
  · simpa [Finsupp.mem_support_iff] using hh

/-- **The main theorem, in the ordered case.** -/
theorem fL_injective
    (hspan : ∀ w : Magma X, monLie X w ∈ Sp X)
    (hlead : ∀ c : Magma X, IsHall c →
      coeffF (monBrk X c) (Magma.foliage c) = 1 ∧
        ∀ w : List X, w < Magma.foliage c → coeffF (monBrk X c) w = 0)
    (hinj : ∀ a b : Magma X, IsHall a → IsHall b → Magma.foliage a = Magma.foliage b → a = b)
    {z w : FreeLieAlgebra ℤ X} (hzw : fL X z = fL X w) : z = w := by
  classical
  have htop : Sp X = ⊤ := Sp_eq_top hspan
  have hmem : z - w ∈ Sp X := by rw [htop]; exact Submodule.mem_top
  rw [Sp, Submodule.mem_span_set] at hmem
  obtain ⟨c, hcsub, hcsum⟩ := hmem
  have hex : ∀ x ∈ c.support, ∃ h : {h : Magma X // IsHall h}, monLie X h.1 = x :=
    fun x hx => by rcases hcsub hx with ⟨h, hh⟩; exact ⟨h, hh⟩
  set f : {h : Magma X // IsHall h} → FreeLieAlgebra ℤ X := fun h => monLie X h.1 with hf
  have hinjOn : Set.InjOn f (f ⁻¹' ↑c.support) := by
    intro a _ b _ hab
    exact Subtype.ext (monLie_inj_of_coeff hlead hinj a.2 b.2 hab)
  have hbij : Set.BijOn f (f ⁻¹' ↑c.support) ↑c.support := by
    refine ⟨fun h hh => hh, hinjOn, ?_⟩
    intro x hx
    rcases hex x hx with ⟨h, hh⟩
    have hmem : f h ∈ c.support := by
      rw [hf]
      show monLie X h.1 ∈ c.support
      rw [hh]
      exact hx
    exact ⟨h, hmem, by rw [hf]; exact hh⟩
  set c' : {h : Magma X // IsHall h} →₀ ℤ := Finsupp.comapDomain f c hbij.2.1 with hc'def
  have hsumL : c'.sum (fun h r => r • f h) = c.sum (fun x r => r • x) := by
    show (Finsupp.comapDomain f c hbij.2.1).sum (fun h r => r • f h) = c.sum (fun x r => r • x)
    exact Finsupp.sum_comapDomain f c (fun x r => r • x) hbij
  have hsumB : c'.sum (fun h r => r • monBrkA X h.1) = 0 := by
    have h1 : c'.sum (fun h r => r • monBrkA X h.1)
        = c'.sum (fun h r => r • fL X (f h)) := by
      refine Finsupp.sum_congr (fun h _ => ?_)
      rw [hf, fL_monLie]
    have h2 : c'.sum (fun h r => r • fL X (f h)) = fL X (c'.sum (fun h r => r • f h)) := by
      rw [Finsupp.sum_of_support_subset c' (Finset.Subset.refl _) (fun h r => r • fL X (f h))
        (by simp)]
      rw [Finsupp.sum_of_support_subset c' (Finset.Subset.refl _) (fun h r => r • f h) (by simp)]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun h _ => ?_)
      rw [map_smul]
    rw [h1, h2, hsumL, hcsum, map_sub, hzw, sub_self]
  have hc' : c' = 0 := independence_finsupp hlead hinj c' hsumB
  have : z - w = 0 := by
    rw [← hcsum, ← hsumL, hc']
    simp
  exact sub_eq_zero.mp this

end Main

end Work.SSGRoute.UpWitt

-- >>> Defs.lean

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

namespace Work.SSGRoute.UpCore

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

end Work.SSGRoute.UpCore

-- >>> magLeadLemmas.lean

/-!
# The Magnus leading term at the sharp truncation

This file collects the facts about the Magnus leading term `magLead N z = magnus X N z - 1`
needed for the proof of the Magnus core theorem, at the truncation level `N = k + 1` adapted to
elements of `γ_k` (Mathlib: `Gam X (k-1)`):

* `monBrk_coeff_length`, `monBrk_mem_fil`: homogeneity of the bracketed monomial `monBrk`;
* `magLead_monGrp_sub_mem`: the leading term of a commutator monomial is the bracketed monomial;
* `magLead_mul_mem`, `magLead_zpow`, `magLead_prod`: additivity of the leading term on `γ_k`;
* `magLead_eq_zero_of_mem`: reduction of the truncation level.

The proofs of the last four are adapted from `prop5/magnusGroupPart.lean` (where the same facts are
proved with the less sharp hypothesis `N ≤ 2*k`).
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.UpCore

variable {X : Type*}

/-! ## Homogeneity of the bracketed monomial -/

/-- `monBrk X c` is a combination of words of length exactly `Magma.size c`. -/
theorem monBrk_coeff_length (c : Magma X) (v : FreeMonoid X) (h : (monBrk X c).coeff v ≠ 0) :
    v.length = Magma.size c := by
  classical
  have hmain : ∀ (c : Magma X) (v : FreeMonoid X), v ∈ (monBrk X c).coeff.support →
      v.length = Magma.size c := by
    intro c
    induction c with
    | gen x =>
        intro v hv
        rw [monBrk_gen, MonoidAlgebra.coeff_single] at hv
        have hv' : v = FreeMonoid.of x := by
          by_contra hne
          rw [Finsupp.mem_support_iff] at hv
          exact hv (Finsupp.single_eq_of_ne hne)
        rw [hv']
        simp
    | mul a b iha ihb =>
        intro v hv
        rw [monBrk_mul, MonoidAlgebra.coeff_sub] at hv
        rcases Finset.mem_union.mp (Finsupp.support_sub hv) with hv | hv
        · rcases Finset.mem_mul.mp
            (MonoidAlgebra.support_coeff_mul_subset (monBrk X a) (monBrk X b) hv) with
            ⟨u, hu, u', hu', rfl⟩
          rw [FreeMonoid.length_mul, iha u hu, ihb u' hu', Magma.size_mul]
        · rcases Finset.mem_mul.mp
            (MonoidAlgebra.support_coeff_mul_subset (monBrk X b) (monBrk X a) hv) with
            ⟨u, hu, u', hu', rfl⟩
          rw [FreeMonoid.length_mul, ihb u hu, iha u' hu', Magma.size_mul, Nat.add_comm]
  exact hmain c v (by rwa [Finsupp.mem_support_iff])

/-- `monBrk X c` lies in the `size c`-th filtration ideal. -/
theorem monBrk_mem_fil (c : Magma X) : monBrk X c ∈ fil X (Magma.size c) := by
  rw [fil_eq_filI]
  change monBrk X c ∈ filz X (Magma.size c)
  rw [mem_filz_iff]
  intro w hw
  exact le_of_eq (monBrk_coeff_length c w hw).symm

/-- The image of `monBrk X c` in `FreeAssoc X ⧸ fil X N` lies in `filq X N (size c)`. -/
theorem monBrk_mk_mem_filq (N : ℕ) (c : Magma X) :
    Ideal.Quotient.mk (fil X N) (monBrk X c) ∈ filq X N (Magma.size c) :=
  Ideal.mem_map_of_mem (Ideal.Quotient.mk (fil X N)) (monBrk_mem_fil c)

@[simp] theorem monBrk_gen_eq_wordEl (x : X) : monBrk X (Magma.gen x) = wordEl [x] := by
  rw [monBrk_gen, wordEl]
  congr 1

/-- Membership in a filtration piece transported across an equality of the exponents. -/
theorem mem_filq_of_eq {N a b : ℕ} (h : a = b) {x : FreeAssoc X ⧸ fil X N}
    (hx : x ∈ filq X N a) : x ∈ filq X N b := h ▸ hx

/-! ## The leading term of a commutator monomial -/

/-- **The Magnus leading term of a commutator monomial is the bracketed monomial.** -/
theorem magLead_monGrp_sub_mem (N : ℕ) (c : Magma X) (hN : Magma.size c + 1 ≤ N) :
    magLead N (monGrp X c) - Ideal.Quotient.mk (fil X N) (monBrk X c) ∈
      filq X N (Magma.size c + 1) := by
  induction c with
  | gen x =>
      have h1 : magLead N (monGrp X (Magma.gen x)) =
          Ideal.Quotient.mk (fil X N) (monBrk X (Magma.gen x)) := by
        rw [monGrp_gen, magLead_of, monBrk_gen_eq_wordEl]
      rw [h1, sub_self]
      exact Submodule.zero_mem _
  | mul a b iha ihb =>
      have hpa : 1 ≤ Magma.size a := Magma.size_pos a
      have hpb : 1 ≤ Magma.size b := Magma.size_pos b
      have hsum : Magma.size a + Magma.size b + 1 ≤ N := by
        rw [Magma.size_mul] at hN; omega
      have hia : Magma.size a + 1 ≤ N := by omega
      have hib : Magma.size b + 1 ≤ N := by omega
      have hIa := iha hia
      have hIb := ihb hib
      have hcomm := magLead_commutator N (Magma.size a) (Magma.size b) hpa hpb hsum
        (Work.SSGRoute.UpCore.monGrp_mem_Gam (X := X) a) (Work.SSGRoute.UpCore.monGrp_mem_Gam (X := X) b)
      have hAa : magLead N (monGrp X a) ∈ filq X N (Magma.size a) :=
        magLead_mem_filq N (Magma.size a) hpa (by omega) (Work.SSGRoute.UpCore.monGrp_mem_Gam (X := X) a)
      have hBb : magLead N (monGrp X b) ∈ filq X N (Magma.size b) :=
        magLead_mem_filq N (Magma.size b) hpb (by omega) (Work.SSGRoute.UpCore.monGrp_mem_Gam (X := X) b)
      have hMa : Ideal.Quotient.mk (fil X N) (monBrk X a) ∈ filq X N (Magma.size a) :=
        monBrk_mk_mem_filq N a
      have hMb : Ideal.Quotient.mk (fil X N) (monBrk X b) ∈ filq X N (Magma.size b) :=
        monBrk_mk_mem_filq N b
      -- the difference of the two brackets lies in the next piece
      have hdiff : magLead N ⁅monGrp X a, monGrp X b⁆
          - (Ideal.Quotient.mk (fil X N) (monBrk X a) * Ideal.Quotient.mk (fil X N) (monBrk X b)
             - Ideal.Quotient.mk (fil X N) (monBrk X b) * Ideal.Quotient.mk (fil X N) (monBrk X a))
          ∈ filq X N (Magma.size a + Magma.size b + 1) := by
        have hAB : magLead N (monGrp X a) * magLead N (monGrp X b)
            - Ideal.Quotient.mk (fil X N) (monBrk X a)
              * Ideal.Quotient.mk (fil X N) (monBrk X b) ∈ filq X N (Magma.size a + Magma.size b + 1) := by
          have he : magLead N (monGrp X a) * magLead N (monGrp X b)
              - Ideal.Quotient.mk (fil X N) (monBrk X a)
                * Ideal.Quotient.mk (fil X N) (monBrk X b)
              = (magLead N (monGrp X a) - Ideal.Quotient.mk (fil X N) (monBrk X a))
                  * magLead N (monGrp X b)
                + Ideal.Quotient.mk (fil X N) (monBrk X a)
                  * (magLead N (monGrp X b) - Ideal.Quotient.mk (fil X N) (monBrk X b)) := by
            noncomm_ring
          rw [he]
          refine Submodule.add_mem _ ?_ ?_
          · have := mul_mem_filq X N (Magma.size a + 1) (Magma.size b) hIa hBb
            exact mem_filq_of_eq (by omega) this
          · have := mul_mem_filq X N (Magma.size a) (Magma.size b + 1) hMa hIb
            exact mem_filq_of_eq (by omega) this
        have hBA : magLead N (monGrp X b) * magLead N (monGrp X a)
            - Ideal.Quotient.mk (fil X N) (monBrk X b)
              * Ideal.Quotient.mk (fil X N) (monBrk X a) ∈ filq X N (Magma.size a + Magma.size b + 1) := by
          have he : magLead N (monGrp X b) * magLead N (monGrp X a)
              - Ideal.Quotient.mk (fil X N) (monBrk X b)
                * Ideal.Quotient.mk (fil X N) (monBrk X a)
              = (magLead N (monGrp X b) - Ideal.Quotient.mk (fil X N) (monBrk X b))
                  * magLead N (monGrp X a)
                + Ideal.Quotient.mk (fil X N) (monBrk X b)
                  * (magLead N (monGrp X a) - Ideal.Quotient.mk (fil X N) (monBrk X a)) := by
            noncomm_ring
          rw [he]
          refine Submodule.add_mem _ ?_ ?_
          · have := mul_mem_filq X N (Magma.size b + 1) (Magma.size a) hIb hAa
            exact mem_filq_of_eq (by omega) this
          · have := mul_mem_filq X N (Magma.size b) (Magma.size a + 1) hMb hIa
            exact mem_filq_of_eq (by omega) this
        have hsub : (magLead N (monGrp X a) * magLead N (monGrp X b)
              - magLead N (monGrp X b) * magLead N (monGrp X a))
            - (Ideal.Quotient.mk (fil X N) (monBrk X a)
                * Ideal.Quotient.mk (fil X N) (monBrk X b)
              - Ideal.Quotient.mk (fil X N) (monBrk X b)
                * Ideal.Quotient.mk (fil X N) (monBrk X a))
            ∈ filq X N (Magma.size a + Magma.size b + 1) := by
          have he : (magLead N (monGrp X a) * magLead N (monGrp X b)
              - magLead N (monGrp X b) * magLead N (monGrp X a))
            - (Ideal.Quotient.mk (fil X N) (monBrk X a)
                * Ideal.Quotient.mk (fil X N) (monBrk X b)
              - Ideal.Quotient.mk (fil X N) (monBrk X b)
                * Ideal.Quotient.mk (fil X N) (monBrk X a))
            = (magLead N (monGrp X a) * magLead N (monGrp X b)
                - Ideal.Quotient.mk (fil X N) (monBrk X a)
                  * Ideal.Quotient.mk (fil X N) (monBrk X b))
              - (magLead N (monGrp X b) * magLead N (monGrp X a)
                - Ideal.Quotient.mk (fil X N) (monBrk X b)
                  * Ideal.Quotient.mk (fil X N) (monBrk X a)) := by
            noncomm_ring
          rw [he]
          exact Submodule.sub_mem _ hAB hBA
        have hsum := Submodule.add_mem _ hcomm hsub
        have he : (magLead N ⁅monGrp X a, monGrp X b⁆
              - (magLead N (monGrp X a) * magLead N (monGrp X b)
                 - magLead N (monGrp X b) * magLead N (monGrp X a)))
            + ((magLead N (monGrp X a) * magLead N (monGrp X b)
                 - magLead N (monGrp X b) * magLead N (monGrp X a))
              - (Ideal.Quotient.mk (fil X N) (monBrk X a)
                  * Ideal.Quotient.mk (fil X N) (monBrk X b)
                - Ideal.Quotient.mk (fil X N) (monBrk X b)
                  * Ideal.Quotient.mk (fil X N) (monBrk X a)))
            = magLead N ⁅monGrp X a, monGrp X b⁆
              - (Ideal.Quotient.mk (fil X N) (monBrk X a)
                  * Ideal.Quotient.mk (fil X N) (monBrk X b)
                - Ideal.Quotient.mk (fil X N) (monBrk X b)
                  * Ideal.Quotient.mk (fil X N) (monBrk X a)) := by
          noncomm_ring
        rw [he] at hsum
        exact hsum
      -- conclude
      rw [monGrp_mul]
      simpa only [Magma.size_mul, monBrk_mul, map_sub, map_mul] using hdiff

/-! ## Additivity at the sharp truncation -/

theorem magLead_mul_mem (k : ℕ) (hk : 1 ≤ k) {y z : FreeGroup X}
    (hy : y ∈ Gam X (k - 1)) (hz : z ∈ Gam X (k - 1)) :
    magLead (k + 1) (y * z) = magLead (k + 1) y + magLead (k + 1) z :=
  magLead_mul (k + 1) k hk (by omega) (by omega) hy hz

theorem magLead_inv_mem (k : ℕ) (hk : 1 ≤ k) {y : FreeGroup X} (hy : y ∈ Gam X (k - 1)) :
    magLead (k + 1) y⁻¹ = -magLead (k + 1) y :=
  magLead_inv (k + 1) k hk (by omega) (by omega) hy

theorem magLead_pow_mem (k : ℕ) (hk : 1 ≤ k) (p : ℕ) {y : FreeGroup X}
    (hy : y ∈ Gam X (k - 1)) :
    magLead (k + 1) (y ^ p) = (p : ℤ) • magLead (k + 1) y := by
  rw [magLead_pow (k + 1) k p hk (by omega) (by omega) hy, zsmul_eq_mul]

/-- **The Magnus leading term converts integer powers into scalar multiples.** -/
theorem magLead_zpow (k : ℕ) (hk : 1 ≤ k) (m : ℤ) {y : FreeGroup X}
    (hy : y ∈ Gam X (k - 1)) :
    magLead (k + 1) (y ^ m) = m • magLead (k + 1) y := by
  rcases Int.eq_nat_or_neg m with ⟨n, h | h⟩
  · rw [h, zpow_natCast, magLead_pow_mem k hk n hy]
  · rw [h, show y ^ (-(n : ℤ)) = (y ^ n)⁻¹ by rw [zpow_neg, zpow_natCast]]
    rw [magLead_inv_mem k hk (Subgroup.pow_mem _ hy n), magLead_pow_mem k hk n hy, neg_smul]

/-! ## Reduction of the truncation level -/

/-- If the Magnus leading term modulo `fil N` lies in the degree `n+2` part, then it vanishes
modulo `fil (n+2)`. -/
theorem magLead_eq_zero_of_mem (N n : ℕ) (hn : n + 2 ≤ N) (y : FreeGroup X)
    (h : magLead N y ∈ filq X N (n + 2)) : magLead (n + 2) y = 0 := by
  have hle : fil X N ≤ fil X (n + 2) := fil_antitone X hn
  let π : FreeAssoc X ⧸ fil X N →+* FreeAssoc X ⧸ fil X (n + 2) := Ideal.Quotient.factor hle
  have hπmk : ∀ a : FreeAssoc X,
      π (Ideal.Quotient.mk (fil X N) a) = Ideal.Quotient.mk (fil X (n + 2)) a :=
    fun a => Ideal.Quotient.factor_mk hle a
  have hnat : (Units.map π.toMonoidHom).comp (magnus X N) = magnus X (n + 2) := by
    refine FreeGroup.ext_hom _ _ (fun x => ?_)
    apply Units.ext
    simp only [MonoidHom.comp_apply, Units.coe_map]
    rw [magnus_of X N x, magnus_of X (n + 2) x]
    change π (1 + Ideal.Quotient.mk (fil X N) (MonoidAlgebra.single (FreeMonoid.of x) 1)) =
      1 + Ideal.Quotient.mk (fil X (n + 2)) (MonoidAlgebra.single (FreeMonoid.of x) 1)
    rw [map_add, map_one, hπmk]
  have hval : π (↑((magnus X N) y)) = ↑((magnus X (n + 2)) y) := by
    have h2 := congrArg (fun u : (FreeAssoc X ⧸ fil X (n + 2))ˣ =>
      (u : FreeAssoc X ⧸ fil X (n + 2))) (DFunLike.congr_fun hnat y)
    rw [MonoidHom.comp_apply, Units.coe_map] at h2
    exact h2
  have h1 : π (magLead N y) = magLead (n + 2) y := by
    show π (↑((magnus X N) y) - 1) = _
    rw [map_sub, map_one, hval]
    rfl
  obtain ⟨a, ha, haeq⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (fil X N))
    Ideal.Quotient.mk_surjective).1 h
  rw [← h1, ← haeq, hπmk]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

end Work.SSGRoute.UpCore

-- >>> relations_zero.lean

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

-- (graded instances provided by the original Work.SSGRoute.UpCore.relations_zero)

namespace Work.SSGRoute.UpCore

/-! ## The Lie homomorphism `L → Λbar` -/

/-- The Lie homomorphism from the free Lie ring `L = FreeLieAlgebra ℤ X` to the associated graded
`Λbar = ⨁ q, γ_q/γ_{q+1}` of the free group, sending a generator `x` to the class of `x` in
`Λ 0 = F/F'`.  Since `L` is the free Lie ring, this assignment extends uniquely. -/
noncomputable def rzPsi (X : Type u) : FreeLieAlgebra ℤ X →ₗ⁅ℤ⁆ graded.Lbar (FreeGroup X) :=
  FreeLieAlgebra.lift ℤ (fun x => graded.lofL (G := FreeGroup X) 0
    (cls X 0 ⟨FreeGroup.of x, by simp [Gam, graded.Gam]⟩))

theorem rzPsi_of (X : Type u) (x : X) :
    rzPsi X (FreeLieAlgebra.of ℤ x) = graded.lofL (G := FreeGroup X) 0
      (cls X 0 ⟨FreeGroup.of x, by simp [Gam, graded.Gam]⟩) :=
  FreeLieAlgebra.lift_of_apply _ x

/-! ## Elementary computations with the class map -/

/-- The class map, written with `QuotientGroup.mk'` (the form in which the graded bracket computes
on classes of commutators). -/
theorem rz_cls_eq_mk' (X : Type u) (q : ℕ) (x : Gam X q) :
    cls X q x = Additive.ofMul (QuotientGroup.mk'
      ((Gam X (q+1)).subgroupOf (Gam X q)) x) := rfl

/-- The class of the commutator of `x ∈ γ_p` and `y ∈ γ_q` is the graded bracket of the classes. -/
theorem rz_cls_commutator (X : Type u) {p q : ℕ} (x : Gam X p) (y : Gam X q) :
    cls X (p + q + 1)
        ⟨⁅(x : FreeGroup X), (y : FreeGroup X)⁆, graded.commutator_mem_Gam x.property y.property⟩ =
      graded.bracketL p q (cls X p x) (cls X q y) := by
  rw [rz_cls_eq_mk', rz_cls_eq_mk', rz_cls_eq_mk', graded.bracketL_apply_mk]
  rfl

/-- The inclusion of a graded piece into `Λbar`, transported along an equality of degrees. -/
theorem rz_lofL_cast {X : Type u} {m n : ℕ} (h : m = n) (x : graded.LamAdd (G := FreeGroup X) m) :
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
theorem rz_GLamCast_bracket_treeCl (X : Type u) (a b : Magma X)
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
theorem rz_psi_monLie (X : Type u) (c : Magma X) :
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
theorem rz_psi_monLie_of_size (X : Type u) (k : ℕ) (c : Magma X) (hc : Magma.size c = k) :
    rzPsi X (monLie X c) = graded.lofL (G := FreeGroup X) (k - 1)
      (cls X (k - 1) ⟨monGrp X c, by simpa [hc] using monGrp_mem_Gam c⟩) := by
  rw [rz_psi_monLie]
  have h : Magma.size c - 1 = k - 1 := by rw [hc]
  rw [rz_lofL_cast (X := X) h]
  congr 1
  simp only [treeCl]
  rw [rz_cls_eq_mk', graded.GLamCast_mk', rz_cls_eq_mk']

/-! ## The target statement -/

theorem relations_zero (X : Type u) (k : ℕ) (hk : 1 ≤ k) (r : ℕ)
    (c : Fin r → Work.SSGRoute.prop5.Magma X) (a : Fin r → ℤ)
    (hc : ∀ i, Work.SSGRoute.prop5.Magma.size (c i) = k)
    (h : ∑ i, a i • Work.SSGRoute.prop5.monLie X (c i) = 0) :
    ∑ i, a i • Work.SSGRoute.UpCore.cls X (k - 1)
      ⟨Work.SSGRoute.UpCore.monGrp X (c i),
        by simpa [hc i] using Work.SSGRoute.UpCore.monGrp_mem_Gam (c i)⟩ = 0 := by
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

end Work.SSGRoute.UpCore

-- >>> coreDefs.lean

/-!
# The Magnus leading term and the graded pieces of the lower central series

This file (namespace `Work.SSGRoute.UpLctf`) collects, in one place, the two ingredients needed
to prove the "core" statement of the Magnus embedding theorem:

* the commutator monomial `monGrp c` attached to a free-magma tree `c`, its Magnus leading term
  `mlt N z = (magnus X N z) - 1` in the truncated free associative algebra, and the basic
  congruences for `mlt` (homogeneity, additivity on `γ_k`, behaviour on commutators);
* the graded piece `Lam X q = γ_q/γ_{q+1}` of the lower central series, its class map `cls`, and
  the linear map `treeToLam X k` from the well-indexed trees of size `k` to `Λ_{k-1}`.

The definitions duplicate the ones in `prop5/core/Defs.lean` and `prop5/magnusGroupPart.lean`; they
are repeated here because those modules import `prop5/magnusLieDefs.lean`, which clashes with the
`IsLyndon` of `prop5/witt/Defs.lean` used by the Hall-set development of Witt's theorem.
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.UpLctf

open Work.SSGRoute.prop5

variable {X : Type*}

/-! ## The commutator monomial in the free group -/

/-- The commutator monomial in the free group attached to a binary tree. -/
def monGrp (X : Type*) : Magma X → FreeGroup X
  | .gen x => FreeGroup.of x
  | .mul a b => ⁅monGrp X a, monGrp X b⁆

@[simp] theorem monGrp_gen (X : Type*) (x : X) : monGrp X (.gen x) = FreeGroup.of x := rfl

@[simp] theorem monGrp_mul (X : Type*) (a b : Magma X) :
    monGrp X (.mul a b) = ⁅monGrp X a, monGrp X b⁆ := rfl

/-- The `q`-th term of the lower central series of a free group (Mathlib indexing). -/
abbrev Gam (X : Type*) (q : ℕ) : Subgroup (FreeGroup X) := graded.Gam (G := FreeGroup X) q

/-- The commutator monomial of a tree of size `m` lies in the `(m-1)`-th term of the lower central
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

/-! ## The Magnus leading term -/

/-- The Magnus leading term of `z` at truncation `N`: the Magnus image modulo `fil X N`, shifted
by `1`. -/
def mlt (N : ℕ) (z : FreeGroup X) : FreeAssoc X ⧸ fil X N :=
  ((magnus X N z : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1

@[simp] theorem mlt_one (N : ℕ) : mlt (X := X) N 1 = 0 := by
  simp [mlt]

/-- The leading term of a generator. -/
theorem mlt_of (N : ℕ) (x : X) :
    mlt N (FreeGroup.of x) =
      Ideal.Quotient.mk (fil X N) (MonoidAlgebra.single (FreeMonoid.of x) (1 : ℤ)) := by
  rw [mlt, magnus_of]
  noncomm_ring

/-- The `N`-th filtration piece of the truncated algebra is zero. -/
theorem filq_self_eq_bot (X : Type*) (N : ℕ) : filq X N N = ⊥ := by
  rw [filq, Ideal.map_eq_bot_iff_le_ker]
  intro a ha
  rw [RingHom.mem_ker]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

theorem mem_filq_self_eq_zero {N : ℕ} {x : FreeAssoc X ⧸ fil X N} (h : x ∈ filq X N N) :
    x = 0 := by
  rw [filq_self_eq_bot X N] at h
  exact h

/-- The "easy half" of the Magnus embedding: the leading term of an element of `γ_k` (Mathlib
indexing: `lowerCentralSeries (k-1)`) lies in the degree-`k` filtration piece. -/
theorem mlt_mem_filq (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) {z : FreeGroup X}
    (hz : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) :
    mlt N z ∈ filq X N k := by
  have h := magnus_mem_one_add X N (k - 1) (by omega) z hz
  rwa [Nat.sub_add_cancel hk] at h

/-- The leading term vanishes on `γ_{k+1}`. -/
theorem mlt_eq_zero_of_mem_succ (k : ℕ) {z : FreeGroup X}
    (hz : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries k) :
    mlt (k + 1) z = 0 := by
  have h1 : mlt (k + 1) z ∈ filq X (k + 1) (k + 1) :=
    mlt_mem_filq (k + 1) (k + 1) (by omega) le_rfl (by simpa using hz)
  exact mem_filq_self_eq_zero h1

/-- **Additivity of the leading term on `γ_k`** (when `N ≤ 2k`). -/
theorem mlt_mul (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (hN2 : N ≤ 2 * k) {g h : FreeGroup X}
    (hg : g ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1))
    (hh : h ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) :
    mlt N (g * h) = mlt N g + mlt N h := by
  have hsq : mlt N g * mlt N h = 0 := by
    refine mem_filq_self_eq_zero ?_
    refine (filq_antitone X N (by omega : N ≤ k + k)) ?_
    exact mul_mem_filq X N k k (mlt_mem_filq N k hk hkN hg) (mlt_mem_filq N k hk hkN hh)
  have key : mlt N (g * h) = mlt N g + mlt N h + mlt N g * mlt N h := by
    unfold mlt
    rw [map_mul, Units.val_mul]
    noncomm_ring
  rw [key, hsq, add_zero]

/-- The leading term of an inverse. -/
theorem mlt_inv (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (hN2 : N ≤ 2 * k) {w : FreeGroup X}
    (hw : w ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) :
    mlt N w⁻¹ = -mlt N w := by
  have h1 : mlt N (w * w⁻¹) = 0 := by rw [mul_inv_cancel]; exact mlt_one N
  have h2 := mlt_mul N k hk hkN hN2 hw (Subgroup.inv_mem _ hw)
  rw [h1] at h2
  have h3 : mlt N w⁻¹ + mlt N w = 0 := by
    rw [add_comm (mlt N w⁻¹) (mlt N w)]; exact h2.symm
  exact eq_neg_of_add_eq_zero_left h3

/-! ## The commutator identity -/

/-- The pure unit-group identity behind the bracket lemma. -/
theorem commutator_sub_one {R : Type*} [Ring R] (A B : Rˣ) :
    ((⁅A, B⁆ : Rˣ) : R) - 1
      = ((((A : R) - 1) * ((B : R) - 1) - ((B : R) - 1) * ((A : R) - 1))
          * (((A⁻¹ : Rˣ) : R) * ((B⁻¹ : Rˣ) : R))) := by
  have key : (A : R) * (B : R) - (B : R) * (A : R)
      = ((A : R) - 1) * ((B : R) - 1) - ((B : R) - 1) * ((A : R) - 1) := by noncomm_ring
  rw [← key, commutatorElement_def, sub_mul]
  simp only [Units.val_mul]
  have h3 : ((B : R) * (A : R)) * (((A⁻¹ : Rˣ) : R) * ((B⁻¹ : Rˣ) : R)) = 1 := by
    have hgrp : (B * A * (A⁻¹ * B⁻¹) : Rˣ) = 1 := by group
    rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, hgrp, Units.val_one]
  rw [h3]
  simp only [mul_assoc]

/-- The filtration pieces of the truncated algebra are two-sided. -/
instance instIsTwoSidedFilq (X : Type*) (N k : ℕ) : (filq X N k).IsTwoSided where
  mul_mem_of_left := by
    intro a b ha
    obtain ⟨a', ha', rfl⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (fil X N))
      (Ideal.Quotient.mk_surjective)).1 ha
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul]
    exact Ideal.mem_map_of_mem _ (Ideal.IsTwoSided.mul_mem_of_left b' ha')

/-- The inverse of a Magnus image is congruent to `1` modulo the first filtration piece. -/
theorem magnus_inv_sub_one_mem (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) {z : FreeGroup X}
    (hz : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) :
    (((magnus X N z)⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1 ∈
      filq X N 1 := by
  have hz' : mlt N z ∈ filq X N k := mlt_mem_filq N k hk hkN hz
  have h1 : (((magnus X N z)⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N)
      * ((magnus X N z : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h : (((magnus X N z)⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1
      = - ((((magnus X N z)⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N)
          * (((magnus X N z : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1)) := by
    rw [mul_sub, mul_one, h1, neg_sub]
  rw [h]
  refine neg_mem ?_
  rw [show ((magnus X N z : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1
      = mlt N z from rfl]
  exact Ideal.mul_mem_left _ _ ((filq_antitone X N hk) hz')

/-- **The bracket lemma**: for `u ∈ γ_p` and `v ∈ γ_q` the leading term of `⁅u,v⁆` agrees modulo
`filq X N (p+q+1)` with the ring commutator of the leading terms. -/
theorem mlt_commutator (N p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p + q + 1 ≤ N)
    {u v : FreeGroup X}
    (hu : u ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (p - 1))
    (hv : v ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (q - 1)) :
    mlt N ⁅u,v⁆ - (mlt N u * mlt N v - mlt N v * mlt N u) ∈ filq X N (p + q + 1) := by
  have hpu : p ≤ N := by omega
  have hqv : q ≤ N := by omega
  have hmemu : mlt N u ∈ filq X N p := mlt_mem_filq N p hp hpu hu
  have hmemv : mlt N v ∈ filq X N q := mlt_mem_filq N q hq hqv hv
  have hinvu : (((magnus X N u)⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1
      ∈ filq X N 1 := magnus_inv_sub_one_mem N p hp hpu hu
  have hinvv : (((magnus X N v)⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1
      ∈ filq X N 1 := magnus_inv_sub_one_mem N q hq hqv hv
  set A : (FreeAssoc X ⧸ fil X N)ˣ := magnus X N u with hA
  set B : (FreeAssoc X ⧸ fil X N)ˣ := magnus X N v with hB
  have hAu : ((A : FreeAssoc X ⧸ fil X N)) - 1 = mlt N u := rfl
  have hBv : ((B : FreeAssoc X ⧸ fil X N)) - 1 = mlt N v := rfl
  have hmap : magnus X N ⁅u,v⁆ = ⁅A, B⁆ := by
    rw [hA, hB, map_commutatorElement]
  have hlt : mlt N ⁅u,v⁆
      = ((((A : FreeAssoc X ⧸ fil X N)) - 1) * (((B : FreeAssoc X ⧸ fil X N)) - 1)
          - (((B : FreeAssoc X ⧸ fil X N)) - 1) * (((A : FreeAssoc X ⧸ fil X N)) - 1))
        * ((((A⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))
            * (((B⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))) := by
    rw [mlt, hmap, commutator_sub_one]
  have hY : ((((A⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))
        * (((B⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))) - 1
      ∈ filq X N 1 := by
    have h2 : ((((A⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))
          * (((B⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))) - 1
        = ((((A⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N)) - 1)
            * (((B⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))
          + ((((B⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N)) - 1) := by
      noncomm_ring
    rw [h2]
    exact Submodule.add_mem _
      (Ideal.mul_mem_right _ _ (by rw [hA]; exact hinvu))
      (by rw [hB]; exact hinvv)
  have hX : (((A : FreeAssoc X ⧸ fil X N)) - 1) * (((B : FreeAssoc X ⧸ fil X N)) - 1)
      - (((B : FreeAssoc X ⧸ fil X N)) - 1) * (((A : FreeAssoc X ⧸ fil X N)) - 1)
      ∈ filq X N (p + q) := by
    rw [hAu, hBv]
    refine Submodule.sub_mem _ (mul_mem_filq X N p q hmemu hmemv) ?_
    exact (Nat.add_comm p q) ▸ mul_mem_filq X N q p hmemv hmemu
  have hkey : mlt N ⁅u,v⁆ - (mlt N u * mlt N v - mlt N v * mlt N u)
      = ((((A : FreeAssoc X ⧸ fil X N)) - 1) * (((B : FreeAssoc X ⧸ fil X N)) - 1)
          - (((B : FreeAssoc X ⧸ fil X N)) - 1) * (((A : FreeAssoc X ⧸ fil X N)) - 1))
        * (((((A⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))
            * (((B⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))) - 1) := by
    rw [hlt, hAu, hBv]
    noncomm_ring
  rw [hkey]
  exact mul_mem_filq X N (p + q) 1 hX hY

/-! ## The graded pieces and the class maps -/

/-- The `q`-th graded piece `γ_q/γ_{q+1}`, written additively. -/
abbrev Lam (X : Type*) (q : ℕ) : Type _ := Additive (graded.GLam (G := FreeGroup X) q)

/-- The class map `γ_q → γ_q/γ_{q+1}`. -/
def clMul (X : Type*) (q : ℕ) : Gam X q →* graded.GLam (G := FreeGroup X) q where
  toFun x := QuotientGroup.mk x
  map_one' := rfl
  map_mul' := fun a b => rfl

/-- The class map, additively. -/
def cl (X : Type*) (q : ℕ) : Additive (Gam X q) →+ Lam X q := (clMul X q).toAdditive

/-- The class in `Λ_q` of a member of `γ_q`. -/
def cls (X : Type*) (q : ℕ) (x : Gam X q) : Lam X q := cl X q (Additive.ofMul x)

@[simp] theorem cls_apply (X : Type*) (q : ℕ) (x : Gam X q) :
    cls X q x = Additive.ofMul (clMul X q x) := rfl

/-- The class of `1` is zero. -/
@[simp] theorem cls_one (q : ℕ) : cls X q (1 : Gam X q) = 0 := rfl

/-- The class of a product is the sum of the classes. -/
theorem cls_mul (q : ℕ) (x y : Gam X q) : cls X q (x * y) = cls X q x + cls X q y := rfl

/-- The class of an inverse is the negative of the class. -/
theorem cls_inv (q : ℕ) (x : Gam X q) : cls X q x⁻¹ = -cls X q x := by
  have h : cls X q x⁻¹ + cls X q x = 0 := by
    rw [add_comm, ← cls_mul, mul_inv_cancel, show cls X q 1 = 0 from rfl]
  exact eq_neg_of_add_eq_zero_left h

/-- The class is zero exactly on `γ_{q+1}`. -/
theorem cls_eq_zero_iff {q : ℕ} {x : Gam X q} :
    cls X q x = 0 ↔ (x : FreeGroup X) ∈ Gam X (q + 1) := by
  change (clMul X q x : graded.GLam (G := FreeGroup X) q) = 1 ↔ _
  rw [clMul]
  exact QuotientGroup.eq_one_iff x

/-- The trees of size `k`. -/
abbrev TreeIdx (X : Type*) (k : ℕ) := {c : Magma X // Magma.size c = k}

/-- The class in `Λ_{k-1}` of the commutator monomial of a tree of size `k`. -/
def treeClOf (X : Type*) (k : ℕ) (c : TreeIdx X k) : Lam X (k - 1) :=
  cls X (k - 1) ⟨monGrp X c.1, by simpa [c.2] using monGrp_mem_Gam c.1⟩

/-- The linear map sending a tree of size `k` to the class of its commutator monomial. -/
def treeToLam (X : Type*) (k : ℕ) : (TreeIdx X k →₀ ℤ) →ₗ[ℤ] Lam X (k - 1) :=
  Finsupp.linearCombination ℤ (treeClOf X k)

@[simp] theorem treeToLam_single (k : ℕ) (c : TreeIdx X k) :
    treeToLam X k (Finsupp.single c 1) = treeClOf X k c := by
  rw [treeToLam, Finsupp.linearCombination_single, one_smul]

@[simp] theorem treeToLam_gen (x : X) :
    treeClOf X 1 ⟨Magma.gen x, rfl⟩ = cls X 0 ⟨FreeGroup.of x, Subgroup.mem_top _⟩ := rfl

end Work.SSGRoute.UpLctf

-- >>> lamSpan.lean

/-!
# The lower central factors of a free group are spanned by commutator monomials

For a binary tree `c : Magma X` of size `m` the commutator monomial `monGrp X c` is an element of
the lower central series term `Gam X (m - 1)` of the free group.  This file proves that the classes
of the trees of size `n+1` span `Λ_n = γ_n/γ_{n+1}`:

`cls X n y ∈ range (treeToLam X (n+1))`  for every `y ∈ γ_n`.

The proof is a direct induction using `Gam X (m+1) = ⁅Gam X m, ⊤⁆`, the graded bilinearity of the
commutator modulo the next term, and the fact that bracketing a weight-`m` monomial with a
generator produces a weight-`(m+1)` monomial.  (Ported from `Submission/Work/lctf/`.)
-/

noncomputable section

open scoped commutatorElement

set_option linter.style.haveILetI false

namespace Work.SSGRoute.UpLctf

open Work.SSGRoute.prop5

variable {X : Type*}

/-- The set of commutator monomials of weight `m`. -/
def monGrpSet (X : Type*) (m : ℕ) : Set (FreeGroup X) :=
  {x | ∃ c : Magma X, Magma.size c = m ∧ x = monGrp X c}

theorem mem_monGrpSet {m : ℕ} {x : FreeGroup X} :
    x ∈ monGrpSet X m ↔ ∃ c : Magma X, Magma.size c = m ∧ x = monGrp X c := Iff.rfl

/-- The commutator of a supremum: if `A`, `B`, `C` are normal then
`⁅A ⊔ B, C⁆ ≤ ⁅A,C⁆ ⊔ ⁅B,C⁆`. -/
theorem commutator_sup_le_of_normal {G : Type*} [Group G] (A B C : Subgroup G)
    [A.Normal] [B.Normal] [C.Normal] : ⁅A ⊔ B, C⁆ ≤ ⁅A, C⁆ ⊔ ⁅B, C⁆ := by
  refine Subgroup.commutator_le.mpr ?_
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := A) (t := B)).mp hx
  rw [commutatorElement_mul_left_eq_conj_mul]
  have h1 : a * ⁅b, y⁆ * a⁻¹ ∈ ⁅B, C⁆ :=
    Subgroup.Normal.conj_mem (Subgroup.commutator_normal B C) ⁅b, y⁆
      (Subgroup.commutator_mem_commutator hb hy) a
  have h2 : ⁅a, y⁆ ∈ ⁅A, C⁆ := Subgroup.commutator_mem_commutator ha hy
  have h1' : a * ⁅b, y⁆ * a⁻¹ ∈ ⁅A, C⁆ ⊔ ⁅B, C⁆ := Subgroup.mem_sup_right h1
  have h2' : ⁅a, y⁆ ∈ ⁅A, C⁆ ⊔ ⁅B, C⁆ := Subgroup.mem_sup_left h2
  exact Subgroup.mul_mem _ h1' h2'

/-- If a weight-`m` monomial bracketed with every generator lies in `K`, then it bracketed with
every element of the free group lies in `K` (`K` normal). -/
theorem bracket_monGrp_of_gen {c : Magma X} {K : Subgroup (FreeGroup X)} [K.Normal]
    (hgen : ∀ x : X, ⁅monGrp X c, FreeGroup.of x⁆ ∈ K) :
    ∀ q : FreeGroup X, ⁅monGrp X c, q⁆ ∈ K := by
  intro q
  refine FreeGroup.induction_on q ?_ ?_ ?_ ?_
  · simp
  · intro x; exact hgen x
  · intro x hx
    rw [commutatorElement_inv_right, ← commutatorElement_inv (monGrp X c) (FreeGroup.of x)]
    simpa using Subgroup.Normal.conj_mem (inferInstance : K.Normal)
      (⁅monGrp X c, FreeGroup.of x⁆⁻¹) (K.inv_mem hx) (FreeGroup.of x)⁻¹
  · intro a b ha hb
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hc : a * ⁅monGrp X c, b⁆ * a⁻¹ ∈ K :=
      Subgroup.Normal.conj_mem (inferInstance : K.Normal) ⁅monGrp X c, b⁆ hb a
    rw [show ⁅monGrp X c, a⁆ * a * ⁅monGrp X c, b⁆ * a⁻¹
          = ⁅monGrp X c, a⁆ * (a * ⁅monGrp X c, b⁆ * a⁻¹) from by group]
    exact K.mul_mem ha hc

/-- **The crux.**  Bracketing the normal closure of the weight-`(m+1)` monomials with the whole
free group only produces elements of the normal closure of the weight-`(m+2)` monomials, modulo
`Gam X (m+2)`. -/
theorem crux (X : Type u) (m : ℕ) :
    ⁅Subgroup.normalClosure (monGrpSet X (m + 1)), (⊤ : Subgroup (FreeGroup X))⁆ ≤
      Subgroup.normalClosure (monGrpSet X (m + 2)) ⊔ Gam X (m + 2) := by
  set K : Subgroup (FreeGroup X) :=
    Subgroup.normalClosure (monGrpSet X (m + 2)) ⊔ Gam X (m + 2) with hK
  haveI hKnorm : K.Normal := by rw [hK]; infer_instance
  let T : Subgroup (FreeGroup X) :=
    { carrier := {u | ∀ q : FreeGroup X, ⁅u, q⁆ ∈ K}
      one_mem' := by intro q; simp
      mul_mem' := by
        intro u v hu hv q
        change ⁅u * v, q⁆ ∈ K
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hc : u * ⁅v, q⁆ * u⁻¹ ∈ K :=
          Subgroup.Normal.conj_mem hKnorm ⁅v, q⁆ (hv q) u
        exact K.mul_mem hc (hu q)
      inv_mem' := by
        intro u hu q
        change ⁅u⁻¹, q⁆ ∈ K
        rw [commutatorElement_inv_left, ← commutatorElement_inv u q]
        simpa using Subgroup.Normal.conj_mem hKnorm (⁅u, q⁆⁻¹) (K.inv_mem (hu q)) u⁻¹ }
  haveI hTnorm : T.Normal :=
    ⟨fun n hn g => by
      change ∀ q : FreeGroup X, ⁅g * n * g⁻¹, q⁆ ∈ K
      intro q
      have h := Subgroup.Normal.conj_mem hKnorm (⁅n, g⁻¹ * q * g⁆) (hn (g⁻¹ * q * g)) g
      rw [conjugate_commutatorElement n (g⁻¹ * q * g) g] at h
      simpa [show g * (g⁻¹ * q * g) * g⁻¹ = q from by group] using h⟩
  have hUT : Subgroup.normalClosure (monGrpSet X (m + 1)) ≤ T :=
    Subgroup.normalClosure_le_normal (fun s hs => by
      obtain ⟨c, hc, rfl⟩ := hs
      intro q
      refine bracket_monGrp_of_gen (c := c) (fun x => ?_) q
      have hmul : ⁅monGrp X c, FreeGroup.of x⁆ = monGrp X (Magma.mul c (Magma.gen x)) := by
        rw [monGrp_mul, monGrp_gen]
      rw [hmul]
      refine Subgroup.mem_sup_left (Subgroup.subset_normalClosure ?_)
      exact ⟨Magma.mul c (Magma.gen x), by rw [Magma.size_mul, hc, Magma.size_gen], rfl⟩)
  refine Subgroup.commutator_le.mpr ?_
  intro u hu q _
  exact hUT hu q

/-- **The main group-theoretic statement.**  The `m`-th term of the lower central series of a free
group is generated by the commutator monomials of weight `m+1`, modulo the next term. -/
theorem lcs_le_normalClosure_sup (X : Type u) : ∀ m : ℕ,
    Gam X m ≤ Subgroup.normalClosure (monGrpSet X (m + 1)) ⊔ Gam X (m + 1) := by
  intro m
  induction m with
  | zero =>
      have h0 : Gam X 0 = ⊤ := graded.Gam_zero
      rw [h0]
      rw [← FreeGroup.closure_range_of X]
      rw [Subgroup.closure_le]
      rintro x ⟨y, rfl⟩
      exact Subgroup.mem_sup_left
        (Subgroup.subset_normalClosure ⟨Magma.gen y, Magma.size_gen y, by simp [monGrp_gen]⟩)
  | succ m ih =>
      have hs : Gam X (m + 1) = ⁅Gam X m, ⊤⁆ := graded.Gam_succ m
      rw [hs]
      refine le_trans (Subgroup.commutator_mono ih le_rfl) ?_
      refine le_trans (commutator_sup_le_of_normal _ _ _) ?_
      exact sup_le (crux X m) le_sup_right

/-- Auxiliary: the class of `v * x * v⁻¹` equals the class of `x` for `x ∈ Gam X n`. -/
theorem cls_conj (X : Type u) (n : ℕ) (x : Gam X n) (v : FreeGroup X)
    (hmem : v * (x : FreeGroup X) * v⁻¹ ∈ Gam X n) :
    cls X n ⟨v * (x : FreeGroup X) * v⁻¹, hmem⟩ = cls X n x := by
  have hc : v * (x : FreeGroup X) * v⁻¹ * (x : FreeGroup X)⁻¹ ∈ Gam X (n + 1) :=
    graded.conj_diff_mem n x.2 v
  have hc' : v * (x : FreeGroup X) * v⁻¹ * (x : FreeGroup X)⁻¹ ∈ Gam X n :=
    graded.Gam_antitone (Nat.le_succ n) hc
  have hweq : (⟨v * (x : FreeGroup X) * v⁻¹, hmem⟩ : Gam X n) =
      (⟨v * (x : FreeGroup X) * v⁻¹ * (x : FreeGroup X)⁻¹, hc'⟩ : Gam X n) * x := by
    ext
    simp only [Subgroup.coe_mul]
    group
  rw [hweq]
  have hadd : cls X n ((⟨v * (x : FreeGroup X) * v⁻¹ * (x : FreeGroup X)⁻¹, hc'⟩ : Gam X n) * x)
      = cls X n ⟨v * (x : FreeGroup X) * v⁻¹ * (x : FreeGroup X)⁻¹, hc'⟩ + cls X n x := by
    rw [cls_apply, cls_apply, cls_apply, map_mul]
    rfl
  rw [hadd]
  have hz : cls X n (⟨v * (x : FreeGroup X) * v⁻¹ * (x : FreeGroup X)⁻¹, hc'⟩ : Gam X n) = 0 := by
    rw [cls_eq_zero_iff]
    exact hc
  rw [hz, zero_add]

theorem cls_mem_range_treeToLam (X : Type u) (n : ℕ) (y : Work.SSGRoute.UpLctf.Gam X n) :
    Work.SSGRoute.UpLctf.cls X n y ∈
      LinearMap.range (Work.SSGRoute.UpLctf.treeToLam X (n + 1)) := by
  set M : Submodule ℤ (Lam X n) := LinearMap.range (treeToLam X (n + 1)) with hM
  let Msub : Subgroup (Gam X n) :=
    { carrier := {x | cls X n x ∈ M}
      one_mem' := by
        show cls X n (1 : Gam X n) ∈ M
        rw [cls_one (X := X) n]
        exact M.zero_mem
      mul_mem' := by
        intro x z hx hz
        show cls X n (x * z) ∈ M
        rw [cls_mul n x z]
        exact M.add_mem hx hz
      inv_mem' := by
        intro x hx
        show cls X n x⁻¹ ∈ M
        rw [cls_inv n x]
        exact M.neg_mem hx }
  let P : Subgroup (FreeGroup X) := Subgroup.map (Gam X n).subtype Msub
  haveI hPnorm : P.Normal :=
    ⟨fun g hg v => by
      change v * g * v⁻¹ ∈ P
      rw [Subgroup.mem_map] at hg ⊢
      obtain ⟨x, hxM, hxg⟩ := hg
      have hwmem : v * (x : FreeGroup X) * v⁻¹ ∈ Gam X n :=
        Subgroup.Normal.conj_mem (inferInstance : (Gam X n).Normal) (x : FreeGroup X) x.2 v
      refine ⟨⟨v * (x : FreeGroup X) * v⁻¹, hwmem⟩, ?_, ?_⟩
      · change cls X n ⟨v * (x : FreeGroup X) * v⁻¹, hwmem⟩ ∈ M
        rw [cls_conj X n x v hwmem]
        exact hxM
      · show v * (x : FreeGroup X) * v⁻¹ = v * g * v⁻¹
        rw [show (x : FreeGroup X) = g from hxg]⟩
  have hUP : Subgroup.normalClosure (monGrpSet X (n + 1)) ≤ P :=
    Subgroup.normalClosure_le_normal (fun s hs => by
      obtain ⟨c, hc, rfl⟩ := hs
      have hg : monGrp X c ∈ Gam X n := by
        have h := monGrp_mem_Gam (X := X) c
        rw [hc] at h
        exact h
      refine Subgroup.mem_map.mpr ⟨⟨monGrp X c, hg⟩, ?_, rfl⟩
      change cls X n ⟨monGrp X c, hg⟩ ∈ M
      have h2 : treeClOf X (n + 1) ⟨c, hc⟩ = cls X n ⟨monGrp X c, hg⟩ := rfl
      rw [← h2]
      exact LinearMap.mem_range.mpr
        ⟨Finsupp.single ⟨c, hc⟩ 1, treeToLam_single (X := X) (n + 1) ⟨c, hc⟩⟩)
  have hyU : (y : FreeGroup X) ∈
      Subgroup.normalClosure (monGrpSet X (n + 1)) ⊔ Gam X (n + 1) :=
    lcs_le_normalClosure_sup X n y.2
  obtain ⟨u, hu, b, hb, hubeq⟩ :=
    (Subgroup.mem_sup_of_normal_left
      (s := Subgroup.normalClosure (monGrpSet X (n + 1))) (t := Gam X (n + 1))).mp hyU
  obtain ⟨xu, hxuM, hxueq⟩ := Subgroup.mem_map.mp (hUP hu)
  have hu' : u ∈ Gam X n := hxueq ▸ xu.2
  have hb' : b ∈ Gam X n := graded.Gam_antitone (Nat.le_succ n) hb
  have hy_eq : y = (⟨u, hu'⟩ : Gam X n) * ⟨b, hb'⟩ := by
    ext
    simpa [Subgroup.coe_mul] using hubeq.symm
  have hcls : cls X n y = cls X n ⟨u, hu'⟩ := by
    rw [hy_eq, cls_mul n]
    have hz : cls X n ⟨b, hb'⟩ = 0 := by
      rw [cls_eq_zero_iff]
      exact hb
    rw [hz, add_zero]
  rw [hcls]
  have hux : cls X n ⟨u, hu'⟩ = cls X n xu := by
    congr 1
    exact Subtype.ext hxueq.symm
  rw [hux]
  exact hxuM


end Work.SSGRoute.UpLctf

-- >>> gen_span.lean

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

namespace Work.SSGRoute.UpCore

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

theorem lam0_span_gen (X : Type u) (w : Lam X 0) :
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

theorem tree_bracket_mem (X : Type u) (n : ℕ) (φ : TreeIdx X (n + 1) →₀ ℤ) (w : Lam X 0)
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

theorem gam_le_clsInRange (X : Type u) (n : ℕ) : Gam X n ≤ clsInRange X n := by
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

theorem gen_span (X : Type u) (k : ℕ) (hk : 1 ≤ k) (y : FreeGroup X)
    (hy : y ∈ Work.SSGRoute.UpCore.Gam X (k - 1)) :
    Work.SSGRoute.UpCore.cls X (k - 1) ⟨y, hy⟩ ∈
      LinearMap.range (Work.SSGRoute.UpCore.treeToLam X k) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, (Nat.sub_add_cancel hk).symm⟩
  exact clsInRange_spec (X := X) (gam_le_clsInRange X n hy) hy

end Work.SSGRoute.UpCore

-- >>> Assembly.lean

/-!
# Assembly of the Magnus core theorem

This file proves the "instance" form of the hard half of the Magnus embedding theorem:
if `y ∈ γ_{n+1}` and the Magnus image of `y` is congruent to `1` modulo the degree `n+2` part of
the truncated free associative algebra, then `y ∈ γ_{n+2}`.
-/

noncomputable section

open scoped commutatorElement

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Work.SSGRoute.UpCore

variable {X : Type*}

/-- `Gam X q` is the same subgroup as `(⊤ : Subgroup (FreeGroup X)).lowerCentralSeries q`. -/
theorem mem_Gam_iff {q : ℕ} {z : FreeGroup X} :
    z ∈ Gam X q ↔ z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries q := by
  rw [Gam, graded.Gam]

theorem monGrp_mem_Gam' (c : Magma X) :
    monGrp X c ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (Magma.size c - 1) :=
  mem_Gam_iff.mp (monGrp_mem_Gam c)

/-! ## Witt's theorem in the form needed here -/

theorem hswap_hall {X : Type u} [LinearOrder X] {a b : Magma X} (h : IsHall (Magma.mul a b)) :
    Magma.foliage a ++ Magma.foliage b < Magma.foliage b ++ Magma.foliage a :=
  swap_hall_of_crux (fun _ _ hh => witt.hall_foliage_lt_right hh) h

theorem hspan_hall {X : Type u} [LinearOrder X] (v : Magma X) : monLie X v ∈ Work.SSGRoute.UpWitt.Sp X :=
  witt.hall_spanning (monLie X) (fun _ _ => rfl) v

theorem hlead_hall {X : Type u} [LinearOrder X] (c : Magma X) (hc : IsHall c) :
    coeffF (monBrk X c) (Magma.foliage c) = 1 ∧
      ∀ w : List X, w < Magma.foliage c → coeffF (monBrk X c) w = 0 :=
  witt.leading_term_coeff hc (fun a b hab => hswap_hall hab)

theorem fL_injective_ordered {X : Type u} [LinearOrder X] : Function.Injective (Work.SSGRoute.UpWitt.fL X) := by
  intro a b hab
  exact Work.SSGRoute.UpWitt.fL_injective (X := X) hspan_hall hlead_hall
    (fun a b ha hb h => witt.hall_foliage_injective_aux ha hb h) hab

/-- Witt's theorem: the canonical map from the free Lie ring to the free associative ring is
injective. -/
theorem fL_injective_all (X : Type u) : Function.Injective (Work.SSGRoute.UpWitt.fL X) := by
  classical
  obtain ⟨instLO, -⟩ := exists_wellFoundedLT X
  letI := instLO
  exact fL_injective_ordered

/-- The canonical `ℤ`-linear map from the free Lie ring on `X` into `FreeAssoc X`. -/
noncomputable def Psi (X : Type u) : FreeLieAlgebra ℤ X →ₗ[ℤ] FreeAssoc X :=
  (FreeAlgebra.equivMonoidAlgebraFreeMonoid : FreeAlgebra ℤ X ≃ₐ[ℤ] FreeAssoc X).toLinearEquiv.toLinearMap.comp
    (Work.SSGRoute.UpWitt.fL X).toLinearMap

/-- `fL` sends the bracket evaluation of a tree to the commutator evaluation.  (The version in
`witt/Assembly.lean` is stated under a `LinearOrder X` hypothesis; this one is order free.) -/
theorem fL_monLie' (X : Type u) (c : Magma X) : Work.SSGRoute.UpWitt.fL X (monLie X c) = monBrkA X c := by
  induction c with
  | gen x => exact FreeLieAlgebra.lift_of_apply _ x
  | mul a b iha ihb =>
      rw [monLie_mul, monBrkA_mul, LieHom.map_lie, iha, ihb, LieRing.of_associative_ring_bracket]

theorem Psi_monLie (X : Type u) (c : Magma X) : Psi X (monLie X c) = monBrk X c := by
  show (FreeAlgebra.equivMonoidAlgebraFreeMonoid : FreeAlgebra ℤ X ≃ₐ[ℤ] FreeAssoc X)
    ((Work.SSGRoute.UpWitt.fL X) (monLie X c)) = monBrk X c
  rw [fL_monLie', equivMonoidAlgebra_monBrkA]

theorem Psi_injective (X : Type u) : Function.Injective (Psi X) := by
  intro a b hab
  have h : (Work.SSGRoute.UpWitt.fL X) a = (Work.SSGRoute.UpWitt.fL X) b := by
    have h2 := congrArg (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm) hab
    change (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm)
        ((FreeAlgebra.equivMonoidAlgebraFreeMonoid) ((Work.SSGRoute.UpWitt.fL X) a)) =
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm)
        ((FreeAlgebra.equivMonoidAlgebraFreeMonoid) ((Work.SSGRoute.UpWitt.fL X) b)) at h2
    simpa using h2
  exact fL_injective_all X h

/-- Linearity of a linear combination of a family under an additive map. -/
theorem linearCombination_map {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] (f : M →+ N)
    (g : ι → M) (μ : ι →₀ ℤ) :
    f (Finsupp.linearCombination ℤ g μ)
      = Finsupp.linearCombination ℤ (fun i => f (g i)) μ := by
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum,
    map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_zsmul])

theorem linearCombination_map_linear {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (f : M →ₗ[ℤ] N) (g : ι → M) (μ : ι →₀ ℤ) :
    f (Finsupp.linearCombination ℤ g μ)
      = Finsupp.linearCombination ℤ (fun i => f (g i)) μ :=
  linearCombination_map f.toAddMonoidHom g μ

theorem linearCombination_congr_left {ι M : Type*} [AddCommGroup M] {g g' : ι → M}
    (h : g = g') (μ : ι →₀ ℤ) :
    Finsupp.linearCombination ℤ g μ = Finsupp.linearCombination ℤ g' μ := by rw [h]

/-! ## The Magnus leading term as a map on the graded piece -/

/-- The Magnus leading term, as a monoid homomorphism `γ_k/γ_{k+1} →* (1 + filq (k+1) k)`. -/
noncomputable def MbarMul (X : Type*) (k : ℕ) (hk : 1 ≤ k) :
    graded.GLam (G := FreeGroup X) (k - 1) →* Multiplicative (↥(filq X (k + 1) k)) :=
  QuotientGroup.lift ((Gam X (k - 1 + 1)).subgroupOf (Gam X (k - 1)))
    (MonoidHom.mk' (fun u : Gam X (k - 1) =>
      Multiplicative.ofAdd (⟨magLead (k + 1) (u : FreeGroup X),
        magLead_mem_filq (X := X) (k + 1) k hk (by omega) (mem_Gam_iff.mp u.2)⟩ :
          ↥(filq X (k + 1) k)))
      (by
        intro a b
        apply Multiplicative.ext
        apply Subtype.ext
        exact magLead_mul_mem (X := X) k hk a.2 b.2))
    (by
      intro u hu
      apply Multiplicative.ext
      apply Subtype.ext
      have hu1 : (u : FreeGroup X) ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries
          (k - 1 + 1) := mem_Gam_iff.mp ((Subgroup.mem_subgroupOf).1 hu)
      have hu2 : (u : FreeGroup X) ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries k := by
        rwa [Nat.sub_add_cancel hk] at hu1
      exact magLead_eq_zero_of_mem_succ (X := X) k hu2)

/-- The Magnus leading term, as an additive map on the graded piece `Λ_{k-1} = γ_k/γ_{k+1}`. -/
noncomputable def Mbar (X : Type*) (k : ℕ) (hk : 1 ≤ k) :
    Lam X (k - 1) →+ ↥(filq X (k + 1) k) where
  toFun z := Multiplicative.toAdd (MbarMul X k hk (Additive.toMul z))
  map_zero' := by
    show Multiplicative.toAdd (MbarMul X k hk 1) = 0
    rw [map_one]
    rfl
  map_add' a b := by
    show Multiplicative.toAdd (MbarMul X k hk (Additive.toMul (a + b))) =
      Multiplicative.toAdd (MbarMul X k hk (Additive.toMul a)) +
        Multiplicative.toAdd (MbarMul X k hk (Additive.toMul b))
    rw [show Additive.toMul (a + b) = Additive.toMul a * Additive.toMul b from rfl, map_mul]
    rfl

theorem Mbar_cls (X : Type*) (k : ℕ) (hk : 1 ≤ k) (u : Gam X (k - 1)) :
    Mbar X k hk (cls X (k - 1) u) =
      ⟨magLead (k + 1) (u : FreeGroup X),
        magLead_mem_filq (X := X) (k + 1) k hk (by omega) (mem_Gam_iff.mp u.2)⟩ := rfl

/-- The Magnus leading term, pushed into the truncated free associative algebra. -/
noncomputable def MbarQ (X : Type*) (k : ℕ) (hk : 1 ≤ k) :
    Lam X (k - 1) →+ (FreeAssoc X ⧸ fil X (k + 1)) :=
  ((Submodule.subtype (filq X (k + 1) k)).toAddMonoidHom).comp (Mbar X k hk)

theorem MbarQ_cls (X : Type*) (k : ℕ) (hk : 1 ≤ k) (u : Gam X (k - 1)) :
    MbarQ X k hk (cls X (k - 1) u) = magLead (k + 1) (u : FreeGroup X) := by
  show (Submodule.subtype (filq X (k + 1) k)) (Mbar X k hk (cls X (k - 1) u)) = _
  rw [Mbar_cls X k hk u]
  rfl

/-! ## The degree-`k` part of the truncated algebra -/

/-- `monBrk X c` lies in the degree-`size c` part of `FreeAssoc X`. -/
theorem monBrk_mem_wordSpan (c : Magma X) : monBrk X c ∈ wordSpan (X := X) (Magma.size c) := by
  rw [mem_wordSpan_iff]
  intro w hw
  by_contra hc
  exact hw (monBrk_coeff_length c w hc)

/-- `monBrk X c` lies in the degree-`k` part whenever `size c = k`. -/
theorem monBrk_mem_wordSpan_of_size (c : Magma X) {k : ℕ} (hk : Magma.size c = k) :
    monBrk X c ∈ wordSpan (X := X) k := by
  rw [mem_wordSpan_iff]
  intro w hw
  by_contra hc
  exact hw (hk ▸ monBrk_coeff_length c w hc)

/-- A `ℤ`-linear combination of bracketed monomials of trees of size `k` lies in the degree-`k`
part of `FreeAssoc X`. -/
theorem lincomb_monBrk_mem_wordSpan (k : ℕ) (μ : TreeIdx X k →₀ ℤ) :
    Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monBrk X c.1) μ ∈ wordSpan (X := X) k := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ (fun c _ => Submodule.smul_mem _ _ (monBrk_mem_wordSpan_of_size c.1 c.2))

/-- An element of the degree-`k` part of `FreeAssoc X` which lies in `fil X (k+1)` is zero. -/
theorem eq_zero_of_mem_wordSpan_of_mem_fil {k : ℕ} {a : FreeAssoc X}
    (h1 : a ∈ wordSpan (X := X) k) (h2 : a ∈ fil X (k + 1)) : a = 0 :=
  calc a = degPart (X := X) k a := (degPart_eq_self_of_mem_wordSpan h1).symm
    _ = 0 := degPart_eq_zero_of_mem_fil h2 (by omega)

/-- The bracketed monomial of a tree of size `k` is the Magnus leading term of the corresponding
commutator monomial. -/
theorem magLead_monGrp_eq (k : ℕ) (c : TreeIdx X k) :
    magLead (k + 1) (monGrp X c.1) =
      Ideal.Quotient.mk (fil X (k + 1)) (monBrk X c.1) := by
  have h1 := magLead_monGrp_sub_mem (X := X) (k + 1) c.1 (by rw [c.2])
  rw [show Magma.size c.1 + 1 = k + 1 from by rw [c.2]] at h1
  have h2 : filq X (k + 1) (k + 1) = ⊥ := filq_self_eq_bot' (X := X) (k + 1)
  rw [h2, Submodule.mem_bot] at h1
  exact sub_eq_zero.mp h1

/-! ## The assembly -/

theorem magnusCore_aux (X : Type u) (k : ℕ) (hk : 1 ≤ k) (y : FreeGroup X)
    (hy : y ∈ Gam X (k - 1)) (hzero : magLead (k + 1) y = 0) :
    y ∈ Gam X k := by
  classical
  obtain ⟨μ, hμ⟩ := gen_span X k hk y hy
  -- the values of the two sums
  set gv : TreeIdx X k → ↥(filq X (k + 1) k) := fun c =>
    ⟨magLead (k + 1) (monGrp X c.1),
      magLead_mem_filq (X := X) (k + 1) k hk (by omega)
        (by simpa [c.2] using monGrp_mem_Gam' (X := X) c.1)⟩ with hgv
  set qv : TreeIdx X k → FreeAssoc X ⧸ fil X (k + 1) :=
    fun c => magLead (k + 1) (monGrp X c.1) with hqv
  have hqv' : ∀ c, (gv c : FreeAssoc X ⧸ fil X (k + 1)) = qv c := fun c => rfl
  -- the Magnus leading term of `y` is the image in `FreeAssoc X ⧸ fil X (k+1)` of the Lie element
  have hlead : magLead (k + 1) y
      = Ideal.Quotient.mk (fil X (k + 1))
        (Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monBrk X c.1) μ) := by
    have hM : MbarQ X k hk (cls X (k - 1) ⟨y, hy⟩) = MbarQ X k hk (treeToLam X k μ) := by
      rw [hμ]
    rw [MbarQ_cls X k hk ⟨y, hy⟩] at hM
    have hR : MbarQ X k hk (treeToLam X k μ)
        = Finsupp.linearCombination ℤ (fun c : TreeIdx X k => magLead (k + 1) (monGrp X c.1)) μ := by
      rw [show treeToLam X k μ = Finsupp.linearCombination ℤ (treeClOf X k) μ from rfl,
        linearCombination_map (MbarQ X k hk) (treeClOf X k) μ]
      exact linearCombination_congr_left (funext (fun c => by
        rw [treeClOf, MbarQ_cls X k hk])) μ
    rw [hR] at hM
    rw [hM]
    rw [show Ideal.Quotient.mk (fil X (k + 1))
        (Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monBrk X c.1) μ)
        = Finsupp.linearCombination ℤ (fun c : TreeIdx X k =>
            Ideal.Quotient.mk (fil X (k + 1)) (monBrk X c.1)) μ from
      linearCombination_map ((Ideal.Quotient.mk (fil X (k + 1))).toAddMonoidHom)
        (fun c : TreeIdx X k => monBrk X c.1) μ]
    exact linearCombination_congr_left (funext (fun c =>
      magLead_monGrp_eq (X := X) k c)) μ
  have hmk : Ideal.Quotient.mk (fil X (k + 1))
      (Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monBrk X c.1) μ) = 0 := by
    rw [← hlead]; exact hzero
  have hsum0 : Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monBrk X c.1) μ = 0 :=
    eq_zero_of_mem_wordSpan_of_mem_fil (lincomb_monBrk_mem_wordSpan k μ)
      (Ideal.Quotient.eq_zero_iff_mem.mp hmk)
  -- hence the Lie element is killed by the (injective) canonical map into `FreeAssoc X`
  have hz : Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monLie X c.1) μ = 0 := by
    apply Psi_injective X
    rw [map_zero]
    change (Psi X).toAddMonoidHom
      (Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monLie X c.1) μ) = 0
    rw [linearCombination_map (Psi X).toAddMonoidHom (fun c : TreeIdx X k => monLie X c.1) μ]
    rw [linearCombination_congr_left (funext (fun c => by
      show (Psi X).toAddMonoidHom (monLie X c.1) = monBrk X c.1
      exact Psi_monLie X c.1)) μ, hsum0]
  -- the class of `y` vanishes
  have hcls0 : Finsupp.linearCombination ℤ (fun c : TreeIdx X k => cls X (k - 1)
      ⟨monGrp X c.1, by simpa [c.2] using monGrp_mem_Gam (X := X) c.1⟩) μ = 0 := by
    have hz' : rzPsi X (Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monLie X c.1) μ)
        = 0 := by rw [hz]; simp
    have hcomp : rzPsi X (Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monLie X c.1) μ)
        = graded.lofL (G := FreeGroup X) (k - 1)
          (Finsupp.linearCombination ℤ (fun c : TreeIdx X k => cls X (k - 1)
            ⟨monGrp X c.1, by simpa [c.2] using monGrp_mem_Gam (X := X) c.1⟩) μ) := by
      rw [show (rzPsi X) (Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monLie X c.1) μ)
          = (rzPsi X).toLinearMap
            (Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monLie X c.1) μ) from rfl]
      rw [linearCombination_map_linear (rzPsi X).toLinearMap
        (fun c : TreeIdx X k => monLie X c.1) μ]
      rw [linearCombination_congr_left (funext (fun c => by
        show (rzPsi X).toLinearMap (monLie X c.1) = graded.lofL (G := FreeGroup X) (k - 1)
          (cls X (k - 1) ⟨monGrp X c.1, by simpa [c.2] using monGrp_mem_Gam (X := X) c.1⟩)
        exact rz_psi_monLie_of_size X k (c.1) (c.2))) μ]
      exact (linearCombination_map
        ((DirectSum.lof ℤ ℕ (fun i => graded.LamAdd (G := FreeGroup X) i) (k - 1)).toAddMonoidHom)
        (fun c : TreeIdx X k => cls X (k - 1)
          ⟨monGrp X c.1, by simpa [c.2] using monGrp_mem_Gam (X := X) c.1⟩) μ).symm
    rw [hcomp] at hz'
    exact rz_lofL_injective (FreeGroup X) (k - 1) (by simpa using hz')
  -- conclude
  have hfinal : cls X (k - 1) ⟨y, hy⟩ = 0 := by
    have h2 : treeToLam X k μ = Finsupp.linearCombination ℤ (fun c : TreeIdx X k => cls X (k - 1)
        ⟨monGrp X c.1, by simpa [c.2] using monGrp_mem_Gam (X := X) c.1⟩) μ := by
      rw [show treeToLam X k μ = Finsupp.linearCombination ℤ (treeClOf X k) μ from rfl]
      exact linearCombination_congr_left (funext (fun c => by rw [treeClOf])) μ
    rw [← hμ, h2, hcls0]
  have hmemk := (cls_eq_zero_iff (X := X) (q := k - 1) (x := ⟨y, hy⟩)).1 hfinal
  simpa [Nat.sub_add_cancel hk] using hmemk

end Work.SSGRoute.UpCore

end
