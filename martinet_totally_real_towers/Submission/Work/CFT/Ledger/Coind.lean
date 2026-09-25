/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CFT.Ledger
-/
import Mathlib
import Submission.Work.CFT.MainTheorem.Defs
import Submission.Work.CFT.IdeleClassGroup.tateCohomology_zero_iso

/-!
# The coset picture of a coinduced representation

For an injective homomorphism `φ : G →* H` of finite groups and a `ℤ`-linear representation
`A` of `G`, this file collects the "concrete" description of the coinduced representation
`Rep.coind φ A` (an `H`-representation on the `G`-equivariant functions `H → A`) used to prove
Shapiro's lemma in the low degrees `0` and `-1` of Tate cohomology.

The main device is a choice of representatives of the left cosets of `φ.range` in `H`:

* `CosetIdx φ` — the type of left cosets of `φ.range` in `H`;
* `cosetRep φ` — a section `H ⧸ φ.range → H` of the quotient map with `cosetRep (φ.range) = 1`;
* `decomp φ hφ` — the bijection `G × CosetIdx φ ≃ H`, `(g, q) ↦ φ g * cosetRep q`.

With these, `coind φ A` is analysed through

* `coindEval` — the underlying function of an element of `coind φ A`;
* `gCoord` — the `G`-coordinate of an element of `H`;
* `evalSum` — the `ℤ`-linear map `coind φ A → A`, `f ↦ ∑_q f (cosetRep q)`;
* `iota` — the `ℤ`-linear maps `A → coind φ A` supported on a single coset.

The final definitions `augIdeal`, `Hm1Sub` and `Hm1Quotient` present `Ĥ⁻¹(G, A)` as
`ker N_A / I_G A`.
-/

open scoped Classical
open CategoryTheory

namespace Work.CFT.Ledger

noncomputable section

section Coset

variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H]

/-- The left cosets of `φ.range` in `H`: the orbits of the action of the subgroup `φ.range` on
`H` by left multiplication. -/
abbrev CosetIdx (φ : G →* H) := MulAction.orbitRel.Quotient φ.range H

instance instFintypeCosetIdx (φ : G →* H) : Fintype (CosetIdx φ) :=
  Quotient.fintype (MulAction.orbitRel φ.range H)

variable (φ : G →* H)

/-- A choice of representative of each left coset of `φ.range` in `H`, normalised so that the
coset of `1` is represented by `1`. -/
noncomputable def cosetRep : CosetIdx φ → H :=
  fun q => if q = Quotient.mk'' (1 : H) then 1 else Quotient.out q

lemma mk_cosetRep (q : CosetIdx φ) : Quotient.mk'' (cosetRep φ q) = q := by
  unfold cosetRep; split_ifs with h
  · rw [h]
  · exact Quotient.out_eq' q

lemma cosetRep_one : cosetRep φ (Quotient.mk'' (1 : H)) = 1 := by
  unfold cosetRep; simp

/-- The coset of `φ g * x` is the coset of `x`. -/
lemma mk_mul_cosetRep (g : G) (q : CosetIdx φ) :
    Quotient.mk'' (φ g * cosetRep φ q) = q := by
  conv_rhs => rw [← mk_cosetRep φ q]
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨⟨φ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩, rfl⟩

lemma mk_mul_left (g : G) (x : H) :
    Quotient.mk'' (φ g * x) = (Quotient.mk'' x : CosetIdx φ) := by
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨⟨φ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩, rfl⟩

/-- The map `(g, q) ↦ φ g * cosetRep q` from `G × (H ⧸ φ.range)` to `H`. -/
noncomputable def decompFun : G × CosetIdx φ → H := fun p => φ p.1 * cosetRep φ p.2

lemma decompFun_injective (hφ : Function.Injective φ) : Function.Injective (decompFun φ) := by
  rintro ⟨g₁, q₁⟩ ⟨g₂, q₂⟩ heq
  simp only [decompFun] at heq
  have h1 : cosetRep φ q₁ = φ (g₁⁻¹ * g₂) * cosetRep φ q₂ := by
    have h2 : cosetRep φ q₁ = (φ g₁)⁻¹ * (φ g₁ * cosetRep φ q₁) := by group
    rw [h2, heq, map_mul, map_inv]
    group
  have hmem : cosetRep φ q₁ ∈ MulAction.orbit φ.range (cosetRep φ q₂) := by
    rw [MulAction.mem_orbit_iff]
    exact ⟨⟨φ (g₁⁻¹ * g₂), MonoidHom.mem_range.mpr ⟨g₁⁻¹ * g₂, rfl⟩⟩, by
      show φ (g₁⁻¹ * g₂) * cosetRep φ q₂ = cosetRep φ q₁
      rw [h1]⟩
  have hq : q₁ = q₂ := by
    rw [← mk_cosetRep φ q₁, ← mk_cosetRep φ q₂, Quotient.eq'', MulAction.orbitRel_apply]
    exact hmem
  subst hq
  exact Prod.ext (hφ (mul_right_cancel heq)) rfl

lemma decompFun_surjective : Function.Surjective (decompFun φ) := by
  intro x
  have hmem : x ∈ MulAction.orbit φ.range (cosetRep φ (Quotient.mk'' x)) := by
    rw [← MulAction.orbitRel_apply, ← Quotient.eq'', mk_cosetRep φ (Quotient.mk'' x)]
  rw [MulAction.mem_orbit_iff] at hmem
  obtain ⟨⟨s, hsS⟩, hs⟩ := hmem
  obtain ⟨g, hg⟩ := hsS
  refine ⟨(g, Quotient.mk'' x), ?_⟩
  have hs' : s * cosetRep φ (Quotient.mk'' x) = x := hs
  show φ g * cosetRep φ (Quotient.mk'' x) = x
  rw [hg, hs']

/-- The bijection `G × (H ⧸ φ.range) ≃ H`, `(g, q) ↦ φ g * cosetRep q`. -/
noncomputable def decomp (hφ : Function.Injective φ) : G × CosetIdx φ ≃ H :=
  Equiv.ofBijective (decompFun φ) ⟨decompFun_injective φ hφ, decompFun_surjective φ⟩

lemma decomp_apply (hφ : Function.Injective φ) (p : G × CosetIdx φ) :
    decomp φ hφ p = φ p.1 * cosetRep φ p.2 := rfl

lemma decomp_symm_apply (hφ : Function.Injective φ) (x : H) :
    φ ((decomp φ hφ).symm x).1 * cosetRep φ ((decomp φ hφ).symm x).2 = x := by
  conv_rhs => rw [← Equiv.apply_symm_apply (decomp φ hφ) x]
  rfl

lemma decomp_symm_mul (hφ : Function.Injective φ) (g : G) (q : CosetIdx φ) :
    (decomp φ hφ).symm (φ g * cosetRep φ q) = (g, q) := by
  rw [Equiv.symm_apply_eq]
  rfl

/-- The coset component of the inverse of `decomp` is the coset of the point. -/
lemma decomp_symm_snd (hφ : Function.Injective φ) (x : H) :
    ((decomp φ hφ).symm x).2 = Quotient.mk'' x := by
  have h := decomp_symm_apply φ hφ x
  have h2 := mk_mul_cosetRep φ ((decomp φ hφ).symm x).1 ((decomp φ hφ).symm x).2
  rw [h] at h2
  exact h2.symm

/-- Sums over `H` decompose as sums over the cosets. -/
lemma sum_decomp {M : Type*} [AddCommMonoid M] (hφ : Function.Injective φ) (F : H → M) :
    ∑ h : H, F h = ∑ q : CosetIdx φ, ∑ g : G, F (φ g * cosetRep φ q) := by
  have h1 : ∑ h : H, F h = ∑ p : G × CosetIdx φ, F (φ p.1 * cosetRep φ p.2) :=
    Fintype.sum_equiv (decomp φ hφ).symm F (fun p => F (φ p.1 * cosetRep φ p.2)) (fun h => by
      rw [decomp_symm_apply])
  rw [h1, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- Right multiplication permutes the left cosets of `φ.range`. -/
noncomputable def cosetSmul (h : H) : CosetIdx φ → CosetIdx φ :=
  fun q => Quotient.liftOn' q (fun x : H => Quotient.mk'' (x * h)) (fun a b hab => by
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab
    obtain ⟨s, hs⟩ := hab
    obtain ⟨g, hg⟩ := s.2
    have hs' : φ g * b = a := by rw [hg]; exact hs
    rw [← hs', show (φ g * b) * h = φ g * (b * h) from mul_assoc _ _ _, mk_mul_left])

lemma cosetSmul_mk (h x : H) :
    cosetSmul φ h (Quotient.mk'' x) = Quotient.mk'' (x * h) := rfl

lemma cosetSmul_inv (h : H) : Function.LeftInverse (cosetSmul φ h⁻¹) (cosetSmul φ h) := by
  intro q
  conv_lhs => rw [← mk_cosetRep φ q]
  rw [cosetSmul_mk, cosetSmul_mk, mul_assoc, mul_inv_cancel, mul_one, mk_cosetRep]

lemma cosetSmul_bijective (h : H) : Function.Bijective (cosetSmul φ h) :=
  ⟨(cosetSmul_inv φ h).injective, by
    simpa only [inv_inv] using (cosetSmul_inv φ h⁻¹).surjective⟩

lemma cosetSmul_apply_cosetRep (h : H) (q : CosetIdx φ) :
    cosetSmul φ h q = Quotient.mk'' (cosetRep φ q * h) := by
  conv_lhs => rw [← mk_cosetRep φ q]
  rw [cosetSmul_mk]

end Coset

section Aug


variable {G : Type} [Group G]

/-- The augmentation subgroup `I_G A = ⟨ρ g a - a⟩` of a `ℤ`-linear representation `A` of `G`. -/
def augIdeal (A : Rep ℤ G) : AddSubgroup A.V :=
  letI : Module ℤ A.V := A.hV2
  AddSubgroup.closure (Set.range fun (gv : G × A.V) => A.ρ gv.1 gv.2 - gv.2)

lemma smul_sub_self_mem_augIdeal (A : Rep ℤ G) (g : G) (x : A.V) :
    A.ρ g x - x ∈ augIdeal A := by
  letI : Module ℤ A.V := A.hV2
  exact AddSubgroup.subset_closure ⟨(g, x), rfl⟩

variable [Fintype G]

end Aug

section AugClosure


variable {G : Type} [Group G]

end AugClosure

section Aug2


variable {G : Type} [Group G] [Fintype G]

/-- The augmentation subgroup `I_G A`, viewed as a subgroup of the kernel of the norm map. -/
def Hm1Sub (A : Rep ℤ G) : AddSubgroup ↥((Work.CFT.IdeleClassGroup.normMap A).ker) where
  carrier := {x | x.1 ∈ augIdeal A}
  zero_mem' := (augIdeal A).zero_mem
  add_mem' := fun hx hy => (augIdeal A).add_mem hx hy
  neg_mem' := fun hx => (augIdeal A).neg_mem hx

lemma mem_Hm1Sub {A : Rep ℤ G} {x : ↥((Work.CFT.IdeleClassGroup.normMap A).ker)} :
    x ∈ Hm1Sub A ↔ x.1 ∈ augIdeal A := Iff.rfl

/-- `Ĥ⁻¹(G, A)`, presented as `ker N_A ⧸ I_G A`. -/
abbrev Hm1Quotient (A : Rep ℤ G) : Type _ :=
  ↥((Work.CFT.IdeleClassGroup.normMap A).ker) ⧸ Hm1Sub A

end Aug2

section Coind

variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H]
variable (φ : G →* H) (A : Rep ℤ G)

/-- The coset of the identity element. -/
abbrev oneCoset : CosetIdx φ := Quotient.mk'' (1 : H)

lemma cosetRep_oneCoset : cosetRep φ (oneCoset φ) = 1 := cosetRep_one φ

end Coind

section CoindA


variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H]
variable (φ : G →* H) (A : Rep ℤ G)

lemma mk_oneCoset_eq_iff (x : H) : Quotient.mk'' x = oneCoset φ ↔ x ∈ φ.range := by
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨s, hs⟩
    have hs1 : (s : H) * 1 = x := hs
    have hs' : (s : H) = x := by simpa using hs1
    exact hs' ▸ s.2
  · rintro ⟨g, hg⟩
    exact ⟨⟨φ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩, by
      show φ g * 1 = x
      rw [mul_one, ← hg]⟩

lemma mul_mem_range_iff (g : G) (x : H) : x * φ g ∈ φ.range ↔ x ∈ φ.range := by
  constructor
  · rintro ⟨g', hg'⟩
    exact ⟨g' * g⁻¹, by rw [map_mul, map_inv, hg']; group⟩
  · rintro ⟨g', hg'⟩
    exact ⟨g' * g, by rw [map_mul, hg']⟩

lemma mk_mul_cosetRep_eq_iff (x : H) (q : CosetIdx φ) :
    Quotient.mk'' (x * cosetRep φ q) = q ↔ x ∈ φ.range := by
  constructor
  · intro h
    have h2 : Quotient.mk'' (x * cosetRep φ q) =
        (Quotient.mk'' (cosetRep φ q) : CosetIdx φ) := by
      rw [h, mk_cosetRep]
    rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h2
    obtain ⟨s, hs⟩ := h2
    have hs1 : (s : H) * cosetRep φ q = x * cosetRep φ q := hs
    have hxs : (s : H) = x := mul_right_cancel hs1
    exact hxs ▸ s.2
  · intro hx
    conv_rhs => rw [← mk_cosetRep φ q]
    rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    obtain ⟨g, hg⟩ := hx
    exact ⟨⟨φ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩, by
      show φ g * cosetRep φ q = x * cosetRep φ q
      rw [hg]⟩

/-- The `G`-coordinate of an element of `H`: the unique `g` with `φ g * cosetRep (mk x) = x`. -/
noncomputable def gCoord (hφ : Function.Injective φ) (x : H) : G :=
  ((decomp φ hφ).symm x).1

lemma phi_gCoord_mul_cosetRep (hφ : Function.Injective φ) (x : H) :
    φ (gCoord φ hφ x) * cosetRep φ (Quotient.mk'' x) = x := by
  rw [← decomp_symm_snd φ hφ x]
  exact decomp_symm_apply φ hφ x

lemma gCoord_mul_cosetRep (hφ : Function.Injective φ) (g : G) (q : CosetIdx φ) :
    gCoord φ hφ (φ g * cosetRep φ q) = g := by
  apply hφ
  have h := phi_gCoord_mul_cosetRep φ hφ (φ g * cosetRep φ q)
  rw [mk_mul_cosetRep] at h
  exact mul_right_cancel h

lemma phi_gCoord_of_mem_range (hφ : Function.Injective φ) {x : H} (hx : x ∈ φ.range) :
    φ (gCoord φ hφ x) = x := by
  have h := phi_gCoord_mul_cosetRep φ hφ x
  rw [(mk_oneCoset_eq_iff φ x).mpr hx, cosetRep_oneCoset, mul_one] at h
  exact h

lemma gCoord_eq_of_phi_eq (hφ : Function.Injective φ) {x : H} {g : G} (hx : φ g = x) :
    gCoord φ hφ x = g :=
  hφ (by rw [phi_gCoord_of_mem_range φ hφ ⟨g, hx⟩, hx])

lemma gCoord_mul_left (hφ : Function.Injective φ) (g : G) (x : H) :
    gCoord φ hφ (φ g * x) = g * gCoord φ hφ x := by
  have h1 := phi_gCoord_mul_cosetRep φ hφ (φ g * x)
  have h2 := phi_gCoord_mul_cosetRep φ hφ x
  rw [mk_mul_left] at h1
  have h3 : φ g * x = φ g * (φ (gCoord φ hφ x) * cosetRep φ (Quotient.mk'' x)) := by rw [h2]
  have h4 : φ (gCoord φ hφ (φ g * x)) * cosetRep φ (Quotient.mk'' x)
      = (φ g * φ (gCoord φ hφ x)) * cosetRep φ (Quotient.mk'' x) := by
    rw [h1, h3, mul_assoc]
  refine hφ ?_
  rw [map_mul]
  exact mul_right_cancel h4

/-- The underlying function `H → A` of an element of the coinduced representation. -/
noncomputable def coindEval (f : (Rep.coind φ A).V) : H → A.V := fun h => (f : H → A.V) h

@[simp] lemma coindEval_zero : coindEval φ A 0 = 0 := rfl

@[simp] lemma coindEval_add (f g : (Rep.coind φ A).V) :
    coindEval φ A (f + g) = coindEval φ A f + coindEval φ A g := rfl

/-- The `H`-action on the coinduced representation, on underlying functions. -/
lemma coindEval_smul (h x : H) (f : (Rep.coind φ A).V) :
    coindEval φ A ((Rep.coind φ A).ρ h f) x = coindEval φ A f (x * h) := by
  rw [Rep.of_ρ, Representation.coind_apply]
  rfl

/-- The defining equivariance of an element of the coinduced representation. -/
lemma coindEval_equivariant (f : (Rep.coind φ A).V) (g : G) (x : H) :
    coindEval φ A f (φ g * x) = A.ρ g (coindEval φ A f x) := by
  letI : Module ℤ A.V := A.hV2
  exact (Representation.mem_coindV φ A.ρ _).mp f.2 g x

lemma coindEval_sum {ι : Type*} (s : Finset ι) (v : ι → (Rep.coind φ A).V) :
    coindEval φ A (∑ i ∈ s, v i) = ∑ i ∈ s, coindEval φ A (v i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coindEval_add, ih]

/-- The sum of an element of the coinduced representation over a set of coset representatives. -/
noncomputable def evalSum : (Rep.coind φ A).V →+ A.V where
  toFun f := ∑ q : CosetIdx φ, coindEval φ A f (cosetRep φ q)
  map_zero' := by simp
  map_add' f g := by
    have h : ∀ q : CosetIdx φ, coindEval φ A (f + g) (cosetRep φ q)
        = coindEval φ A f (cosetRep φ q) + coindEval φ A g (cosetRep φ q) :=
      fun q => congrFun (coindEval_add φ A f g) _
    simp only [h, Finset.sum_add_distrib]

@[simp] lemma evalSum_coindEval (f : (Rep.coind φ A).V) :
    evalSum φ A f = ∑ q : CosetIdx φ, coindEval φ A f (cosetRep φ q) := rfl

lemma evalSum_comp_add (f g : (Rep.coind φ A).V) :
    evalSum φ A (f + g) = evalSum φ A f + evalSum φ A g := map_add _ f g

/-- The function supported on the coset `q`, with value `a` at the representative. -/
noncomputable def iotaFun (hφ : Function.Injective φ) (q : CosetIdx φ) (a : A.V) : H → A.V :=
  fun x => if Quotient.mk'' x = q then A.ρ (gCoord φ hφ x) a else 0

lemma iotaFun_apply (hφ : Function.Injective φ) (q : CosetIdx φ) (a : A.V) (x : H) :
    iotaFun φ A hφ q a x
      = if Quotient.mk'' x = q then A.ρ (gCoord φ hφ x) a else 0 := rfl

lemma iotaFun_equivariant (hφ : Function.Injective φ) (q : CosetIdx φ) (a : A.V) :
    ∀ (g : G) (x : H), iotaFun φ A hφ q a (φ g * x) = A.ρ g (iotaFun φ A hφ q a x) := by
  intro g₀ x
  have h1 : Quotient.mk'' (φ g₀ * x) = Quotient.mk'' x := mk_mul_left φ g₀ x
  have h2 : gCoord φ hφ (φ g₀ * x) = g₀ * gCoord φ hφ x := gCoord_mul_left φ hφ g₀ x
  rw [iotaFun_apply, iotaFun_apply, h1, h2]
  split_ifs with h
  · rw [map_mul]; rfl
  · simp

/-- The element of `coind φ A` supported on the coset `q`, with value `a` at the representative. -/
noncomputable def iota (hφ : Function.Injective φ) (q : CosetIdx φ) :
    A.V →+ (Rep.coind φ A).V where
  toFun a := by
    letI : Module ℤ A.V := A.hV2
    exact ⟨iotaFun φ A hφ q a,
      (Representation.mem_coindV φ A.ρ _).mpr (iotaFun_equivariant φ A hφ q a)⟩
  map_zero' := by
    apply Subtype.ext; funext x
    change iotaFun φ A hφ q 0 x = (0 : H → A.V) x
    rw [iotaFun_apply]
    split_ifs <;> simp
  map_add' a b := by
    apply Subtype.ext; funext x
    change iotaFun φ A hφ q (a + b) x = iotaFun φ A hφ q a x + iotaFun φ A hφ q b x
    rw [iotaFun_apply, iotaFun_apply, iotaFun_apply]
    split_ifs <;> simp [map_add]

lemma coindEval_iota (hφ : Function.Injective φ) (q : CosetIdx φ) (a : A.V) :
    coindEval φ A (iota φ A hφ q a) = iotaFun φ A hφ q a := rfl

lemma iotaFun_apply_mul (hφ : Function.Injective φ) (q q' : CosetIdx φ) (a : A.V) (g : G) :
    iotaFun φ A hφ q a (φ g * cosetRep φ q') =
      if q' = q then A.ρ g a else 0 := by
  rw [iotaFun_apply, mk_mul_cosetRep, gCoord_mul_cosetRep]

lemma iota_apply_mul (hφ : Function.Injective φ) (q q' : CosetIdx φ) (a : A.V) (g : G) :
    coindEval φ A (iota φ A hφ q a) (φ g * cosetRep φ q') =
      if q' = q then A.ρ g a else 0 := by
  rw [coindEval_iota, iotaFun_apply_mul]

lemma evalSum_iota (hφ : Function.Injective φ) (q : CosetIdx φ) (a : A.V) :
    evalSum φ A (iota φ A hφ q a) = a := by
  have h : ∀ q' : CosetIdx φ, coindEval φ A (iota φ A hφ q a) (cosetRep φ q')
      = if q' = q then a else 0 := by
    intro q'
    have h2 := iota_apply_mul φ A hφ q q' a 1
    simpa using h2
  rw [evalSum_coindEval]
  simp only [h]
  have := Finset.sum_ite_eq' (Finset.univ : Finset (CosetIdx φ)) q (fun _ => a)
  simpa using this

lemma coindEval_iota_oneCoset (hφ : Function.Injective φ) (a : A.V) :
    coindEval φ A (iota φ A hφ (oneCoset φ) a) 1 = a := by
  have h := iota_apply_mul φ A hφ (oneCoset φ) (oneCoset φ) a 1
  rw [cosetRep_oneCoset, mul_one] at h
  simpa using h

/-- Every element of `coind φ A` is the sum of its projections to the cosets. -/
lemma sum_iota (hφ : Function.Injective φ) (f : (Rep.coind φ A).V) :
    ∑ q : CosetIdx φ, iota φ A hφ q (coindEval φ A f (cosetRep φ q)) = f := by
  apply Subtype.ext
  funext x
  rw [← decomp_symm_apply φ hφ x]
  change coindEval φ A (∑ q : CosetIdx φ, iota φ A hφ q (coindEval φ A f (cosetRep φ q)))
      (φ ((decomp φ hφ).symm x).1 * cosetRep φ ((decomp φ hφ).symm x).2) = coindEval φ A f _
  rw [coindEval_sum, Finset.sum_apply]
  have h3 : ∀ q : CosetIdx φ,
      coindEval φ A (iota φ A hφ q (coindEval φ A f (cosetRep φ q)))
          (φ ((decomp φ hφ).symm x).1 * cosetRep φ ((decomp φ hφ).symm x).2)
        = if ((decomp φ hφ).symm x).2 = q
            then A.ρ ((decomp φ hφ).symm x).1 (coindEval φ A f (cosetRep φ q)) else 0 := by
    intro q
    change iotaFun φ A hφ q (coindEval φ A f (cosetRep φ q))
      (φ ((decomp φ hφ).symm x).1 * cosetRep φ ((decomp φ hφ).symm x).2) = _
    rw [iotaFun_apply_mul]
  simp only [h3]
  rw [Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_univ _)]
  exact (coindEval_equivariant φ A f ((decomp φ hφ).symm x).1
    (cosetRep φ ((decomp φ hφ).symm x).2)).symm

/-- The action of `φ g` on the element supported on the trivial coset. -/
lemma smul_iota_oneCoset (hφ : Function.Injective φ) (g : G) (a : A.V) :
    (Rep.coind φ A).ρ (φ g) (iota φ A hφ (oneCoset φ) a)
      = iota φ A hφ (oneCoset φ) (A.ρ g a) := by
  apply Subtype.ext
  funext x
  change coindEval φ A ((Rep.coind φ A).ρ (φ g) (iota φ A hφ (oneCoset φ) a)) x
      = coindEval φ A (iota φ A hφ (oneCoset φ) (A.ρ g a)) x
  rw [coindEval_smul, coindEval_iota, coindEval_iota, iotaFun_apply, iotaFun_apply]
  letI : Module ℤ A.V := A.hV2
  by_cases hx : x ∈ φ.range
  · have hx' : x * φ g ∈ φ.range := (mul_mem_range_iff φ g x).mpr hx
    have hmk : Quotient.mk'' x = oneCoset φ := (mk_oneCoset_eq_iff φ x).mpr hx
    have hmk' : Quotient.mk'' (x * φ g) = oneCoset φ :=
      (mk_oneCoset_eq_iff φ (x * φ g)).mpr hx'
    rw [hmk, hmk', if_pos rfl, if_pos rfl]
    have hgc : gCoord φ hφ (x * φ g) = gCoord φ hφ x * g :=
      gCoord_eq_of_phi_eq φ hφ (by rw [map_mul, phi_gCoord_of_mem_range φ hφ hx])
    rw [hgc, map_mul, Module.End.mul_apply]
  · have hx' : x * φ g ∉ φ.range := fun h => hx ((mul_mem_range_iff φ g x).mp h)
    have hmk : ¬ Quotient.mk'' x = oneCoset φ := fun h => hx ((mk_oneCoset_eq_iff φ x).mp h)
    have hmk' : ¬ Quotient.mk'' (x * φ g) = oneCoset φ :=
      fun h => hx' ((mk_oneCoset_eq_iff φ (x * φ g)).mp h)
    rw [if_neg hmk', if_neg hmk]

/-- The action of `cosetRep q` on the element supported on the coset `q`. -/
lemma smul_iota (hφ : Function.Injective φ) (q : CosetIdx φ) (a : A.V) :
    (Rep.coind φ A).ρ (cosetRep φ q) (iota φ A hφ q a)
      = iota φ A hφ (oneCoset φ) a := by
  apply Subtype.ext
  funext x
  change coindEval φ A ((Rep.coind φ A).ρ (cosetRep φ q) (iota φ A hφ q a)) x
      = coindEval φ A (iota φ A hφ (oneCoset φ) a) x
  rw [coindEval_smul, coindEval_iota, coindEval_iota, iotaFun_apply, iotaFun_apply]
  by_cases hx : x ∈ φ.range
  · have hx' : Quotient.mk'' (x * cosetRep φ q) = q := by
      rw [← phi_gCoord_of_mem_range φ hφ hx, mk_mul_cosetRep]
    have hmk : Quotient.mk'' x = oneCoset φ := (mk_oneCoset_eq_iff φ x).mpr hx
    rw [hx', hmk, if_pos rfl, if_pos rfl]
    have hgc : gCoord φ hφ (x * cosetRep φ q) = gCoord φ hφ x := by
      conv_lhs => rw [← phi_gCoord_of_mem_range φ hφ hx]
      exact gCoord_mul_cosetRep φ hφ (gCoord φ hφ x) q
    rw [hgc]
  · have hxq : ¬ Quotient.mk'' (x * cosetRep φ q) = q :=
      fun h => hx ((mk_mul_cosetRep_eq_iff φ x q).mp h)
    have hmk : ¬ Quotient.mk'' x = oneCoset φ := fun h => hx ((mk_oneCoset_eq_iff φ x).mp h)
    rw [if_neg hxq, if_neg hmk]

/-- Differences of `iota`'s lie in the augmentation subgroup. -/
lemma iota_sub_mem_augIdeal (hφ : Function.Injective φ) (q : CosetIdx φ) (a : A.V) :
    iota φ A hφ q a - iota φ A hφ (oneCoset φ) a ∈ augIdeal (Rep.coind φ A) := by
  have h : iota φ A hφ q a - iota φ A hφ (oneCoset φ) a
      = -((Rep.coind φ A).ρ (cosetRep φ q) (iota φ A hφ q a) - iota φ A hφ q a) := by
    rw [smul_iota φ A hφ q a]; abel
  rw [h]
  exact AddSubgroup.neg_mem _ (smul_sub_self_mem_augIdeal (Rep.coind φ A) _ _)

/-- `iota` at the trivial coset maps the augmentation subgroup into the augmentation subgroup. -/
lemma iota_augIdeal_le (hφ : Function.Injective φ) {a : A.V} (ha : a ∈ augIdeal A) :
    iota φ A hφ (oneCoset φ) a ∈ augIdeal (Rep.coind φ A) := by
  have hgen : ∀ (g : G) (b : A.V),
      iota φ A hφ (oneCoset φ) (A.ρ g b - b) ∈ augIdeal (Rep.coind φ A) := by
    intro g b
    rw [map_sub, ← smul_iota_oneCoset φ A hφ g b]
    exact smul_sub_self_mem_augIdeal (Rep.coind φ A) _ _
  rw [augIdeal] at ha hgen ⊢
  induction ha using AddSubgroup.closure_induction with
  | mem y hy => obtain ⟨⟨g, b⟩, rfl⟩ := hy; exact hgen g b
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add x y hx hy ihx ihy => rw [map_add]; exact AddSubgroup.add_mem _ ihx ihy
  | neg x hx ih => rw [map_neg]; exact AddSubgroup.neg_mem _ ih

end CoindA

section Inv


variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H]
variable (φ : G →* H) (A : Rep ℤ G)

lemma coindEval_eq_one_of_invariant (f : (Rep.coind φ A).V)
    (hf : ∀ h : H, (Rep.coind φ A).ρ h f = f) (x : H) :
    coindEval φ A f x = coindEval φ A f 1 := by
  rw [← one_mul x, ← coindEval_smul φ A x 1 f, hf x]

lemma coindEval_mem_invariants (f : ↥(Work.CFT.IdeleClassGroup.invariants (Rep.coind φ A))) :
    coindEval φ A f.1 1 ∈ Work.CFT.IdeleClassGroup.invariants A := by
  have hf : ∀ h : H, (Rep.coind φ A).ρ h f.1 = f.1 :=
    (Work.CFT.IdeleClassGroup.mem_invariants _ f.1).mp f.2
  rw [Work.CFT.IdeleClassGroup.mem_invariants]
  intro g
  rw [← coindEval_equivariant φ A f.1 g 1, mul_one, ← one_mul (φ g),
    ← coindEval_smul φ A (φ g) 1 f.1, hf (φ g)]

/-- The constant function with value an invariant `a ∈ A^G`, in `coind φ A`. -/
noncomputable def constCoind (a : ↥(Work.CFT.IdeleClassGroup.invariants A)) :
    (Rep.coind φ A).V := by
  letI : Module ℤ A.V := A.hV2
  exact ⟨fun _ => a.1, (Representation.mem_coindV φ A.ρ _).mpr (fun g x => by
    show a.1 = A.ρ g a.1
    exact ((Work.CFT.IdeleClassGroup.mem_invariants A a.1).mp a.2 g).symm)⟩

lemma coindEval_constCoind (a : ↥(Work.CFT.IdeleClassGroup.invariants A)) (x : H) :
    coindEval φ A (constCoind φ A a) x = a.1 := rfl

lemma smul_constCoind (h : H) (a : ↥(Work.CFT.IdeleClassGroup.invariants A)) :
    (Rep.coind φ A).ρ h (constCoind φ A a) = constCoind φ A a := by
  apply Subtype.ext; funext x
  change coindEval φ A ((Rep.coind φ A).ρ h (constCoind φ A a)) x = a.1
  rw [coindEval_smul]
  rfl

lemma constCoind_mem_invariants (a : ↥(Work.CFT.IdeleClassGroup.invariants A)) :
    constCoind φ A a ∈ Work.CFT.IdeleClassGroup.invariants (Rep.coind φ A) :=
  (Work.CFT.IdeleClassGroup.mem_invariants _ _).mpr (smul_constCoind φ A · a)

/-- The norm map of the coinduced representation, evaluated at `1`. -/
lemma normMap_coindEval_one (hφ : Function.Injective φ) (g : (Rep.coind φ A).V) :
    coindEval φ A (Work.CFT.IdeleClassGroup.normMap (Rep.coind φ A) g) 1
      = Work.CFT.IdeleClassGroup.normMap A (evalSum φ A g) := by
  have h1 : Work.CFT.IdeleClassGroup.normMap (Rep.coind φ A) g
      = ∑ h : H, (Rep.coind φ A).ρ h g := rfl
  rw [h1, coindEval_sum, Finset.sum_apply]
  have h2 : ∀ h : H, coindEval φ A ((Rep.coind φ A).ρ h g) 1 = coindEval φ A g h := by
    intro h; rw [coindEval_smul, one_mul]
  simp only [h2]
  rw [sum_decomp φ hφ (fun h => coindEval φ A g h)]
  have h3 : ∀ q : CosetIdx φ,
      (∑ g' : G, coindEval φ A g (φ g' * cosetRep φ q))
        = Work.CFT.IdeleClassGroup.normMap A (coindEval φ A g (cosetRep φ q)) := by
    intro q
    rw [Work.CFT.IdeleClassGroup.normMap_apply]
    exact Finset.sum_congr rfl
      (fun g' _ => coindEval_equivariant φ A g g' (cosetRep φ q))
  simp only [h3]
  rw [← map_sum]
  rfl

end Inv

end

end Work.CFT.Ledger
