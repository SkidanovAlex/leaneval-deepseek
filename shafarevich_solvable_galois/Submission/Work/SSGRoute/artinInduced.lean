import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The induced module `Ind_H^G N` of a group

For a group `G`, a subgroup `H ≤ G` and an `𝔽_p[H]`-module `N`, the induced module is

  `Ind_H^G N = { f : G → N // ∀ g h, f (g * h) = h⁻¹ • f g }`,

a `𝔽_p[G]`-module for the action `(g • f) (x) = f (g⁻¹ * x)`.  It is the `𝔽_p[G]`-module
`𝔽_p[G] ⊗_{𝔽_p[H]} N`, and it is the vehicle of Shapiro's lemma and of Artin/Brauer induction.

This file builds the definition and its module structure only (nothing here is `sorry`); it is the
vocabulary in which the characteristic-`p` Artin induction statement (Milne, *Arithmetic Duality
Theorems*, I.2.10) is expressed.
-/

namespace Work.SSGRoute.ArtinInduced

/-- The carrier of the induced module `Ind_H^G N` as a `𝔽_p`-submodule of the functions `G → N`:
the functions satisfying the `H`-equivariance condition `f (g * h) = h⁻¹ • f g`. -/
def indCarrier (p : ℕ) (G : Type*) [Group G] (H : Subgroup G) (N : Type*) [AddCommGroup N]
    [Module (ZMod p) N] [DistribMulAction H N] [SMulCommClass H (ZMod p) N] :
    Submodule (ZMod p) (G → N) where
  carrier := {f | ∀ (g : G) (h : H), f (g * h) = h⁻¹ • f g}
  zero_mem' := by intro g h; simp
  add_mem' := by
    intro f g' hf hg g h
    simp only [Pi.add_apply, hf g h, hg g h, smul_add]
  smul_mem' := by
    intro c f hf g h
    simp only [Pi.smul_apply, hf g h]
    rw [smul_comm (h⁻¹ : H) c (f g)]

/-- **The induced module** `Ind_H^G N` of an `𝔽_p[H]`-module `N` to `G`, as a type.  Its `𝔽_p`- and
`𝔽_p[G]`-module structures are the instances below. -/
abbrev ind (p : ℕ) (G : Type*) [Group G] (H : Subgroup G) (N : Type*) [AddCommGroup N]
    [Module (ZMod p) N] [DistribMulAction H N] [SMulCommClass H (ZMod p) N] : Type _ :=
  ↥(indCarrier p G H N)

instance indAddCommGroup (p : ℕ) (G : Type*) [Group G] (H : Subgroup G) (N : Type*)
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction H N] [SMulCommClass H (ZMod p) N] :
    AddCommGroup (ind p G H N) :=
  inferInstanceAs (AddCommGroup ↥(indCarrier p G H N))

instance indModuleZMod (p : ℕ) (G : Type*) [Group G] (H : Subgroup G) (N : Type*)
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction H N] [SMulCommClass H (ZMod p) N] :
    Module (ZMod p) (ind p G H N) :=
  inferInstanceAs (Module (ZMod p) ↥(indCarrier p G H N))

theorem ind_mem (p : ℕ) (G : Type*) [Group G] (H : Subgroup G) (N : Type*) [AddCommGroup N]
    [Module (ZMod p) N] [DistribMulAction H N] [SMulCommClass H (ZMod p) N]
    (f : ind p G H N) (g : G) (h : H) : f.1 (g * h) = h⁻¹ • f.1 g := f.2 g h

/-- The left action of `G` on the induced module: `(g • f) x = f (g⁻¹ * x)`. -/
instance indSMul (p : ℕ) (G : Type*) [Group G] (H : Subgroup G) (N : Type*)
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction H N] [SMulCommClass H (ZMod p) N] :
    SMul G (ind p G H N) where
  smul g f :=
    ⟨fun x => f.1 (g⁻¹ * x), by
      intro x h
      show f.1 (g⁻¹ * (x * h)) = h⁻¹ • f.1 (g⁻¹ * x)
      rw [← mul_assoc, ind_mem p G H N f (g⁻¹ * x) h]⟩

@[simp] theorem ind_smul_apply (p : ℕ) (G : Type*) [Group G] (H : Subgroup G) (N : Type*)
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction H N] [SMulCommClass H (ZMod p) N]
    (g x : G) (f : ind p G H N) : (g • f).1 x = f.1 (g⁻¹ * x) := rfl

instance indDistribMulAction (p : ℕ) (G : Type*) [Group G] (H : Subgroup G) (N : Type*)
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction H N] [SMulCommClass H (ZMod p) N] :
    DistribMulAction G (ind p G H N) where
  one_smul f := by
    apply Subtype.ext
    funext x
    simp only [ind_smul_apply, inv_one, one_mul]
  mul_smul g g' f := by
    apply Subtype.ext
    funext x
    simp only [ind_smul_apply, mul_inv_rev, mul_assoc]
  smul_zero g := by
    apply Subtype.ext
    funext x
    simp only [ind_smul_apply]
    rfl
  smul_add g f f' := by
    apply Subtype.ext
    funext x
    simp only [ind_smul_apply]
    rfl

instance indSMulCommClass (p : ℕ) (G : Type*) [Group G] (H : Subgroup G) (N : Type*)
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction H N] [SMulCommClass H (ZMod p) N] :
    SMulCommClass G (ZMod p) (ind p G H N) where
  smul_comm g c f := by
    apply Subtype.ext
    funext x
    rfl

/-- The induced module of a finite group with finite coefficients is finite. -/
instance indFinite (p : ℕ) (G : Type*) [Group G] (H : Subgroup G) (N : Type*)
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction H N] [SMulCommClass H (ZMod p) N]
    [Finite G] [Finite N] : Finite (ind p G H N) :=
  Finite.of_injective (fun f : ind p G H N => (f.1 : G → N)) (fun _ _ h => Subtype.ext h)

end Work.SSGRoute.ArtinInduced
