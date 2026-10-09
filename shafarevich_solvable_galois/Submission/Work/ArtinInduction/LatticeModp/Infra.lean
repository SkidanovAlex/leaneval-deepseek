/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Mod `p` reduction of `ℤ`-lattices with a `G`-action

Infrastructure for `Work.ArtinInduction.lattice_modp_commensurable`.

For a `ℤ`-module `M` carrying a `DistribMulAction G` and a `G`-stable `ℤ`-submodule `A ⊆ M`, the
quotient `A/pA` is naturally a finite `𝔽_p[G]`-module.  This file builds the relevant typeclass
instances (`Module (ZMod p)`, `DistribMulAction G`, `SMulCommClass G (ZMod p)`, `Finite`) and the
basic naturality lemmas.

The instances are plain `def`s (`quotSMul`, `quotDMA`, `quotZMod`, `quotSCC`) rather than global
`instance`s, so that they can be installed locally with `letI` and do not clash with ambient
instances of a consumer file.
-/
import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise

set_option linter.style.haveILetI false
set_option linter.defProp false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.ArtinInduction.LatticeModp

variable {G : Type} [Group G]

/-! ## The action of `G` on quotient additive groups -/

/-- `x ↦ g • x` as an additive homomorphism. -/
def gEnd {X : Type} [AddCommGroup X] [DistribMulAction G X] (g : G) : X →+ X :=
  DistribMulAction.toAddMonoidEnd G X g

lemma quotMap'_wellDefined {X : Type} [AddCommGroup X] [DistribMulAction G X]
    (S : AddSubgroup X) (hS : ∀ (g : G) (x : X), x ∈ S → g • x ∈ S) (g : G) :
    ∀ a b : X, QuotientAddGroup.leftRel S a b → QuotientAddGroup.leftRel S (g • a) (g • b) := by
  intro a b hab
  rw [QuotientAddGroup.leftRel_apply] at hab ⊢
  have h := hS g (-a + b) hab
  rwa [smul_add, smul_neg] at h

/-- The action of `G` on `X ⧸ S`, for `S` an additive subgroup stable under `G`. -/
noncomputable def qSMulA {X : Type} [AddCommGroup X] [DistribMulAction G X] (S : AddSubgroup X)
    (hS : ∀ (g : G) (x : X), x ∈ S → g • x ∈ S) : SMul G (X ⧸ S) :=
  ⟨fun g => Quotient.map' (fun x => g • x) (quotMap'_wellDefined S hS g)⟩

/-- The `G`-action on `X ⧸ S`, for `S` an additive subgroup stable under `G`. -/
noncomputable def qDMAA {X : Type} [AddCommGroup X] [DistribMulAction G X] (S : AddSubgroup X)
    (hS : ∀ (g : G) (x : X), x ∈ S → g • x ∈ S) : DistribMulAction G (X ⧸ S) :=
  letI := qSMulA S hS
  Function.Surjective.distribMulAction (f := QuotientAddGroup.mk' S)
    (QuotientAddGroup.mk'_surjective S)
    (fun g x => Quotient.map'_mk'' (fun y => g • y) (quotMap'_wellDefined S hS g) x)

lemma qDMAA_mk {X : Type} [AddCommGroup X] [DistribMulAction G X] (S : AddSubgroup X)
    (hS : ∀ (g : G) (x : X), x ∈ S → g • x ∈ S) (g : G) (x : X) :
    @SMul.smul G (X ⧸ S) (qDMAA S hS).toSMul g (QuotientAddGroup.mk x)
      = QuotientAddGroup.mk (g • x) :=
  Quotient.map'_mk'' (fun y => g • y) (quotMap'_wellDefined S hS g) x

/-- The action of `G` on `X ⧸ S`, for `S : Submodule ℤ X` stable under `G`. -/
noncomputable def quotSMul {X : Type} [AddCommGroup X] [DistribMulAction G X] (S : Submodule ℤ X)
    (hS : ∀ (g : G) (x : X), x ∈ S → g • x ∈ S) : SMul G (X ⧸ S) :=
  qSMulA S.toAddSubgroup hS

/-- The `G`-action on `X ⧸ S`, for `S : Submodule ℤ X` stable under `G`. -/
noncomputable def quotDMA {X : Type} [AddCommGroup X] [DistribMulAction G X] (S : Submodule ℤ X)
    (hS : ∀ (g : G) (x : X), x ∈ S → g • x ∈ S) : DistribMulAction G (X ⧸ S) :=
  qDMAA S.toAddSubgroup hS

lemma quotDMA_mk {X : Type} [AddCommGroup X] [DistribMulAction G X] (S : Submodule ℤ X)
    (hS : ∀ (g : G) (x : X), x ∈ S → g • x ∈ S) (g : G) (x : X) :
    @SMul.smul G (X ⧸ S) (quotDMA S hS).toSMul g (QuotientAddGroup.mk x)
      = QuotientAddGroup.mk (g • x) :=
  qDMAA_mk S.toAddSubgroup hS g x

/-! ## The `ZMod p`-module structure on a quotient -/

/-- The `ZMod p`-module structure on `X ⧸ S` when `S` contains the `p`-multiples. -/
noncomputable def quotZMod (p : ℕ) {X : Type} [AddCommGroup X] (S : Submodule ℤ X)
    (hSp : ∀ x : X, (p : ℕ) • x ∈ S) : Module (ZMod p) (X ⧸ S) :=
  QuotientAddGroup.zmodModule (n := p) (H := S.toAddSubgroup) hSp

/-- In any `ZMod p`-module the scalar action is the `ℕ`-scalar action. -/
lemma zmod_smul_eq_nsmul (p : ℕ) [NeZero p] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (c : ZMod p) (v : V) : c • v = c.val • v := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  exact Nat.cast_smul_eq_nsmul (ZMod p) c.val v

/-- Naturality of the `ZMod p`-action on a quotient. -/
lemma quotZMod_mk (p : ℕ) [NeZero p] {X : Type} [AddCommGroup X] (S : Submodule ℤ X)
    (hSp : ∀ x : X, (p : ℕ) • x ∈ S) (c : ZMod p) (m : X) :
    @SMul.smul (ZMod p) (X ⧸ S) (quotZMod p S hSp).toSMul c (Submodule.Quotient.mk m)
      = Submodule.Quotient.mk (c.val • m) := by
  have h1 : @SMul.smul (ZMod p) (X ⧸ S) (quotZMod p S hSp).toSMul c (Submodule.Quotient.mk m)
      = c.val • (Submodule.Quotient.mk m : X ⧸ S) :=
    @zmod_smul_eq_nsmul p ‹NeZero p› (X ⧸ S) _ (quotZMod p S hSp) c (Submodule.Quotient.mk m)
  rw [h1]
  exact QuotientAddGroup.mk_nsmul S.toAddSubgroup m c.val

/-- The `ℤ`-action and the `G`-action on a quotient commute. -/
noncomputable def quotSCC (p : ℕ) [NeZero p] {X : Type} [AddCommGroup X] [DistribMulAction G X] (S : Submodule ℤ X)
    (hS : ∀ (g : G) (x : X), x ∈ S → g • x ∈ S)
    (hSp : ∀ x : X, (p : ℕ) • x ∈ S) :
    @SMulCommClass G (ZMod p) (X ⧸ S) (quotDMA S hS).toSMul (quotZMod p S hSp).toSMul := by
  letI := quotDMA S hS
  letI := quotZMod p S hSp
  refine ⟨fun g c x => ?_⟩
  rw [zmod_smul_eq_nsmul p c, zmod_smul_eq_nsmul p c]
  exact (DistribMulAction.toAddMonoidEnd G (X ⧸ S) g).map_nsmul c.val x

/-! ## The `p`-multiples submodule -/

/-- The submodule `Ideal.span {p} • ⊤` of `p`-multiples of `X`. -/
abbrev pSmulSub (p : ℕ) (X : Type) [AddCommGroup X] : Submodule ℤ X :=
  (Ideal.span {(p : ℤ)}) • (⊤ : Submodule ℤ X)

lemma mem_pSmulSub_iff {p : ℕ} {X : Type} [AddCommGroup X] {x : X} :
    x ∈ pSmulSub p X ↔ ∃ y : X, (p : ℤ) • y = x := by
  unfold pSmulSub
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨fun ⟨b, _, hb⟩ => ⟨b, hb⟩, fun ⟨b, hb⟩ => ⟨b, Submodule.mem_top, hb⟩⟩

lemma pSmul_mem_pSmulSub {p : ℕ} {X : Type} [AddCommGroup X] (y : X) :
    (p : ℤ) • y ∈ pSmulSub p X :=
  mem_pSmulSub_iff.mpr ⟨y, rfl⟩

lemma nsmul_mem_pSmulSub {p : ℕ} {X : Type} [AddCommGroup X] (y : X) :
    (p : ℕ) • y ∈ pSmulSub p X := by
  rw [mem_pSmulSub_iff]
  exact ⟨y, Nat.cast_smul_eq_nsmul ℤ p y⟩

lemma pSmulSub_smul_mem {p : ℕ} {X : Type} [AddCommGroup X] [DistribMulAction G X]
    {m : X} (hm : m ∈ pSmulSub p X) (g : G) : g • m ∈ pSmulSub p X := by
  rw [mem_pSmulSub_iff] at hm ⊢
  obtain ⟨y, rfl⟩ := hm
  exact ⟨g • y, by rw [smul_comm]⟩

/-! ## The action of `G` on a `G`-stable submodule -/

/-- The action of `G` on a `G`-stable `ℤ`-submodule, through the ambient action. -/
noncomputable def subSMul {X : Type} [AddCommGroup X] [DistribMulAction G X] (A : Submodule ℤ X)
    (hA : ∀ (g : G) (x : X), x ∈ A → g • x ∈ A) : SMul G ↥A :=
  ⟨fun g x => ⟨g • x.1, hA g x.1 x.2⟩⟩

/-- The `G`-action on a `G`-stable `ℤ`-submodule, through the ambient action. -/
noncomputable def subDMA {X : Type} [AddCommGroup X] [DistribMulAction G X] (A : Submodule ℤ X)
    (hA : ∀ (g : G) (x : X), x ∈ A → g • x ∈ A) : DistribMulAction G ↥A where
  smul g x := ⟨g • x.1, hA g x.1 x.2⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g x y := Subtype.ext (smul_add g x.1 y.1)

/-! ## Finiteness of `X ⧸ pX` for finitely generated `X` -/

/-- If two integers have congruent images in `ZMod p`, then the difference between the
`ZMod.val` representative of the first and the second is divisible by `p`. -/
lemma dvd_val_sub_of_intCast_eq (p : ℕ) [NeZero p] (a b : ℤ)
    (h : (a : ZMod p) = (b : ZMod p)) : (p : ℤ) ∣ ((a : ZMod p).val : ℤ) - b := by
  have h1 : ((((a : ZMod p).val : ℕ)) : ZMod p) = (b : ZMod p) := by
    rw [ZMod.natCast_zmod_val]; exact h
  have h1' : (((((a : ZMod p).val : ℕ) : ℤ)) : ZMod p) = ((b : ℤ) : ZMod p) := by
    rw [Int.cast_natCast]; exact h1
  have h2 : ((((a : ZMod p).val : ℕ) : ℤ)) ≡ b [ZMOD (p : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff _ _ p).mp h1'
  exact (Int.modEq_iff_dvd.mp h2.symm)

/-- For `p ≠ 0`, the quotient of a finitely generated `ℤ`-module by its `p`-multiples is
finite. -/
theorem finite_quot_pSmulSub_of_moduleFinite {X : Type} [AddCommGroup X] (p : ℕ) (hp : p ≠ 0)
    [Module.Finite ℤ X] : Finite (X ⧸ pSmulSub p X) := by
  haveI : NeZero p := ⟨hp⟩
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ X
  refine Finite.of_surjective (fun w : Fin n → ZMod p =>
    Submodule.Quotient.mk (p := pSmulSub p X) (f (fun i => ((w i).val : ℤ)))) ?_
  rintro y
  obtain ⟨x, rfl⟩ := (Submodule.Quotient.mk_surjective (p := pSmulSub p X)) y
  obtain ⟨v, rfl⟩ := hf x
  refine ⟨fun i => (v i : ZMod p), ?_⟩
  rw [Submodule.Quotient.eq]
  have hk : ∀ i, ∃ k : ℤ, (((v i : ZMod p)).val : ℤ) = v i + p * k := by
    intro i
    obtain ⟨k, hk⟩ := dvd_val_sub_of_intCast_eq p (v i) (v i) rfl
    exact ⟨k, by linarith⟩
  choose k hk using hk
  have hpt : (fun i : Fin n => (((v i : ZMod p)).val : ℤ)) = v + (fun i => p * k i) := by
    funext i; rw [Pi.add_apply, hk i]
  have hsmul : (fun i : Fin n => p * k i) = p • k := by
    funext i; exact (nsmul_eq_mul p (k i)).symm
  have hmem : f (fun i => p * k i) ∈ pSmulSub p X := by
    rw [hsmul, map_nsmul]
    exact nsmul_mem_pSmulSub (p := p) (X := X) (f k)
  rw [hpt, map_add]
  simpa using hmem

/-! ## Additive invariants and the mod `p` reduction -/

/-- Additive invariants of finite `𝔽_p[G]`-modules. -/
abbrev Inv (p : ℕ) (G : Type) [Group G] :=
  (N : Type) → [AddCommGroup N] → [Module (ZMod p) N] → [DistribMulAction G N] →
    [SMulCommClass G (ZMod p) N] → [Finite N] → ℚ

/-- Additivity of an invariant along `G`-equivariant short exact sequences. -/
abbrev IsAddInv {p : ℕ} {G : Type} [Group G] (ρ : Inv p G) : Prop :=
  ∀ (N₁ N₂ N₃ : Type)
    [AddCommGroup N₁] [Module (ZMod p) N₁] [DistribMulAction G N₁]
    [SMulCommClass G (ZMod p) N₁] [Finite N₁]
    [AddCommGroup N₂] [Module (ZMod p) N₂] [DistribMulAction G N₂]
    [SMulCommClass G (ZMod p) N₂] [Finite N₂]
    [AddCommGroup N₃] [Module (ZMod p) N₃] [DistribMulAction G N₃]
    [SMulCommClass G (ZMod p) N₃] [Finite N₃]
    (i : N₁ →ₗ[ZMod p] N₂) (j : N₂ →ₗ[ZMod p] N₃)
    (hi : Function.Injective i) (hj : Function.Surjective j)
    (hker : LinearMap.ker j = LinearMap.range i)
    (hieq : ∀ (g : G) (m : N₁), i (g • m) = g • i m)
    (hjeq : ∀ (g : G) (n : N₂), j (g • n) = g • j n),
    ρ N₂ = ρ N₁ + ρ N₃

/-- The value of an additive invariant on a quotient `X ⧸ S` (with `S` containing the
`p`-multiples and stable under `G`), using the canonical instances. -/
noncomputable def quotRho {p : ℕ} [NeZero p] {G : Type} [Group G] (ρ : Inv p G) (X : Type)
    [AddCommGroup X] [DistribMulAction G X] (S : Submodule ℤ X)
    (hS : ∀ (g : G) (x : X), x ∈ S → g • x ∈ S) (hSp : ∀ x : X, (p : ℕ) • x ∈ S)
    (hfin : Finite (X ⧸ S)) : ℚ := by
  letI := quotZMod p S hSp
  letI := quotDMA S hS
  letI := quotSCC p S hS hSp
  letI := hfin
  exact ρ (X ⧸ S)

/-! ## Elementary consequences of additivity -/

/-- An additive invariant vanishes on a subsingleton module. -/
lemma rho_subsingleton {p : ℕ} {G : Type} [Group G] (ρ : Inv p G) (hadd : IsAddInv ρ)
    {X : Type} [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction G X]
    [SMulCommClass G (ZMod p) X] [Finite X] [Subsingleton X] : ρ X = 0 := by
  have hker : LinearMap.ker (0 : X →ₗ[ZMod p] X) = LinearMap.range (0 : X →ₗ[ZMod p] X) :=
    Subsingleton.elim _ _
  have h := hadd X X X (0 : X →ₗ[ZMod p] X) (0 : X →ₗ[ZMod p] X)
    (fun x y _ => Subsingleton.elim x y) (fun y => ⟨0, Subsingleton.elim _ _⟩) hker
    (fun g m => by simp) (fun g n => by simp)
  rw [h]; linarith


/-- The value of an invariant is independent of which (automatically equal) instances are used. -/
lemma rho_inst_eq {p : ℕ} {G : Type} [Group G] {X : Type} [AddCommGroup X] (ρ : Inv p G)
    (i₁ i₂ : Module (ZMod p) X) (j₁ j₂ : DistribMulAction G X)
    (k₁ : @SMulCommClass G (ZMod p) X j₁.toSMul i₁.toSMul)
    (k₂ : @SMulCommClass G (ZMod p) X j₂.toSMul i₂.toSMul)
    (f₁ f₂ : Finite X) (hi : i₁ = i₂) (hj : j₁ = j₂) :
    @ρ X _ i₁ j₁ k₁ f₁ = @ρ X _ i₂ j₂ k₂ f₂ := by
  cases hi
  cases hj
  rw [Subsingleton.elim k₁ k₂, Subsingleton.elim f₁ f₂]

/-- The canonical `ZMod p`-module structure on `A/pA`. -/
noncomputable def redZMod (p : ℕ) {X : Type} [AddCommGroup X] (A : Submodule ℤ X) :
    Module (ZMod p) (↥A ⧸ pSmulSub p ↥A) :=
  quotZMod p (pSmulSub p ↥A) (fun x => nsmul_mem_pSmulSub x)

/-- The canonical `G`-action on `A/pA`. -/
noncomputable def redDMA (p : ℕ) {G : Type} [Group G] {X : Type} [AddCommGroup X]
    [DistribMulAction G X] (A : Submodule ℤ X) (hA : ∀ (g : G) (x : X), x ∈ A → g • x ∈ A) :
    DistribMulAction G (↥A ⧸ pSmulSub p ↥A) :=
  letI := subDMA (G := G) A hA
  quotDMA (pSmulSub p ↥A) (fun g m hm => pSmulSub_smul_mem hm g)

/-- Naturality of the canonical `G`-action on `A/pA`. -/
lemma redDMA_mk (p : ℕ) {G : Type} [Group G] {X : Type} [AddCommGroup X] [DistribMulAction G X]
    (A : Submodule ℤ X) (hA : ∀ (g : G) (x : X), x ∈ A → g • x ∈ A) (g : G) (x : ↥A) :
    @SMul.smul G (↥A ⧸ pSmulSub p ↥A) (redDMA p A hA).toSMul g (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk ⟨g • (x : X), hA g x.1 x.2⟩ := by
  letI := subDMA (G := G) A hA
  rw [show @SMul.smul G (↥A ⧸ pSmulSub p ↥A) (redDMA p A hA).toSMul g (Submodule.Quotient.mk x)
      = @SMul.smul G (↥A ⧸ pSmulSub p ↥A)
          (quotDMA (pSmulSub p ↥A) (fun g m hm => pSmulSub_smul_mem hm g)).toSMul g
          (Submodule.Quotient.mk x) from rfl]
  exact quotDMA_mk (pSmulSub p ↥A) (fun g m hm => pSmulSub_smul_mem hm g) g x

/-- Compatibility of the canonical `G`-action and the canonical `ZMod p`-structure on `A/pA`. -/
noncomputable def redSCC (p : ℕ) [NeZero p] {G : Type} [Group G] {X : Type} [AddCommGroup X]
    [DistribMulAction G X] (A : Submodule ℤ X)
    (hA : ∀ (g : G) (x : X), x ∈ A → g • x ∈ A) :
    @SMulCommClass G (ZMod p) (↥A ⧸ pSmulSub p ↥A) (redDMA p A hA).toSMul
      (redZMod p A).toSMul :=
  letI := subDMA (G := G) A hA
  quotSCC (G := G) p (pSmulSub p ↥A) (fun g m hm => pSmulSub_smul_mem hm g)
    (fun x => nsmul_mem_pSmulSub x)

/-- Finiteness of `A/pA`. -/
noncomputable def redFin (p : ℕ) (hp : p ≠ 0) {X : Type} [AddCommGroup X] (A : Submodule ℤ X)
    (hfg : Module.Finite ℤ ↥A) : Finite (↥A ⧸ pSmulSub p ↥A) :=
  finite_quot_pSmulSub_of_moduleFinite p hp (X := ↥A)

/-- The value of an additive invariant on the mod `p` reduction `A/pA`. -/
noncomputable def redRho {p : ℕ} [NeZero p] {G : Type} [Group G] (ρ : Inv p G) (X : Type)
    [AddCommGroup X] [DistribMulAction G X] (A : Submodule ℤ X)
    (hA : ∀ (g : G) (x : X), x ∈ A → g • x ∈ A) (hfg : Module.Finite ℤ ↥A) : ℚ :=
  @ρ (↥A ⧸ pSmulSub p ↥A) _ (redZMod p A) (redDMA p A hA) (redSCC p A hA)
    (redFin p (NeZero.ne p) A hfg)

/-- Unfolding lemma for `redRho`. -/
lemma redRho_def {p : ℕ} [NeZero p] {G : Type} [Group G] (ρ : Inv p G) (X : Type)
    [AddCommGroup X] [DistribMulAction G X] (A : Submodule ℤ X)
    (hA : ∀ (g : G) (x : X), x ∈ A → g • x ∈ A) (hfg : Module.Finite ℤ ↥A) :
    redRho (G := G) ρ X A hA hfg
      = @ρ (↥A ⧸ pSmulSub p ↥A) _ (redZMod p A) (redDMA p A hA) (redSCC p A hA)
          (redFin p (NeZero.ne p) A hfg) := rfl

/-- The value of an *arbitrary* additive invariant on `A/pA` (with any instances inducing the
natural `G`-action, see `hd`) equals `redRho`. -/
lemma rho_eq_redRho {p : ℕ} [NeZero p] {G : Type} [Group G] (ρ : Inv p G) {M : Type}
    [AddCommGroup M] [DistribMulAction G M] (A : Submodule ℤ M)
    (hA : ∀ (g : G) (m : M), m ∈ A → g • m ∈ A) (hfg : Module.Finite ℤ ↥A)
    (m : Module (ZMod p) (↥A ⧸ pSmulSub p ↥A)) (d : DistribMulAction G (↥A ⧸ pSmulSub p ↥A))
    (k : @SMulCommClass G (ZMod p) (↥A ⧸ pSmulSub p ↥A) d.toSMul m.toSMul)
    (f : Finite (↥A ⧸ pSmulSub p ↥A))
    (hd : ∀ (g : G) (x : ↥A),
      @SMul.smul G (↥A ⧸ pSmulSub p ↥A) d.toSMul g (Submodule.Quotient.mk x)
        = Submodule.Quotient.mk ⟨g • (x : M), hA g x.1 x.2⟩) :
    @ρ (↥A ⧸ pSmulSub p ↥A) _ m d k f = redRho (G := G) ρ M A hA hfg := by
  have hj : redDMA p A hA = d := by
    apply DistribMulAction.ext
    funext g y
    induction y using Submodule.Quotient.induction_on with
    | H x => rw [redDMA_mk p A hA g x, hd g x]
  rw [redRho_def (G := G) ρ M A hA hfg]
  exact (rho_inst_eq (G := G) ρ (redZMod p A) m (redDMA p A hA) d (redSCC p A hA) k
    (redFin p (NeZero.ne p) A hfg) f (Subsingleton.elim _ _) hj).symm

end Work.ArtinInduction.LatticeModp
