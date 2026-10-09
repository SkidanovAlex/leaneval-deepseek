/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Setup for the Shapiro ("induction of 2-cocycles") construction

Given a finite group `G`, a subgroup `H ≤ G` and an `𝔽_p[G]`-module `M`, we want to turn a
2-cocycle `c` on `H` with values in `M` into a 2-cocycle `C` on `G` with values in the induced
module `M ⊗ 𝔽_p[X]` for a suitable `G`-set `X`, in such a way that evaluating `C` at the pair
`(h,h')` and extracting the coefficient at a base point returns `c (h,h')`.

The construction is carried out for an abstract *framed* `G`-set: a `G`-set `X` with a point `x₀`
fixed by `H` and a map `s : X → G` such that `s x` is "compatible" with `x` in the sense that
`(s x)⁻¹ * g * s (g⁻¹ • x) ∈ H` for all `g, x` and `s x₀ = 1`.  (For `X = G ⧸ H` and `s` a
section of the coset projection these are exactly the properties one checks at hand.)

This file contains:

* the coset space `G ⧸ H` with a set-theoretic section `sec` sending the base point to `1` and
  the associated `H`-coordinates `A g x = (sec x)⁻¹ * g * sec (g⁻¹ • x)`; these provide the
  framed `G`-set used to instantiate the construction;
* for an abstract framed `G`-set, the `H`-coordinates `AX`, the permutation module
  `PermModX p X = 𝔽_p[X]` with its `𝔽_p[G]`-module structure, the identification
  `permEquivX : M ⊗ 𝔽_p[X] ≃ (X → M)` and the function `funCX`.
-/

import Mathlib
import Submission.Work.Shrinking.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false

namespace Work.SSGRoute
namespace Shapiro

open scoped TensorProduct

universe u v w

/-! ## The coset space `G ⧸ H`, a section, and `H`-coordinates -/

/-- The base point of the coset space `G ⧸ H`, i.e. the coset `H` itself. -/
def basePoint (p : ℕ) (G : Type u) [Group G] (H : Subgroup G) : G ⧸ H := ((1 : G) : G ⧸ H)

@[simp] lemma basePoint_eq (p : ℕ) (G : Type u) [Group G] (H : Subgroup G) :
    basePoint p G H = ((1 : G) : G ⧸ H) := rfl

/-- A set-theoretic section of the projection `G → G ⧸ H`, sending the base point to `1`. -/
noncomputable def sec (p : ℕ) (G : Type u) [Group G] (H : Subgroup G) (x : G ⧸ H) : G := by
  classical
  exact if x = basePoint p G H then 1 else Quotient.out x

variable (p : ℕ) (G : Type u) [Group G] (H : Subgroup G)

lemma mk_sec (x : G ⧸ H) : ((sec p G H x : G) : G ⧸ H) = x := by
  rw [sec]
  split_ifs with hx
  · rw [hx, basePoint_eq]
  · exact QuotientGroup.out_eq' x

lemma sec_basePoint : sec p G H (basePoint p G H) = 1 := by
  rw [sec, if_pos rfl]

lemma basePoint_smul_eq (h : H) : ((h : G) • basePoint p G H : G ⧸ H) = basePoint p G H := by
  rw [basePoint_eq, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  exact (QuotientGroup.eq (s := H)).mpr (by simpa using inv_mem h.property)

/-- The `H`-coordinate of `g` at the coset `x`: `A p G H g x = (sec x)⁻¹ * g * sec (g⁻¹ • x)`. -/
noncomputable def A (p : ℕ) (G : Type u) [Group G] (H : Subgroup G) (g : G) (x : G ⧸ H) : H :=
  ⟨(sec p G H x)⁻¹ * g * sec p G H (g⁻¹ • x), by
    have h1 : ((g * sec p G H (g⁻¹ • x) : G) : G ⧸ H) = x := by
      rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, mk_sec p G H (g⁻¹ • x), smul_inv_smul]
    have h2 : ((sec p G H x)⁻¹ * (g * sec p G H (g⁻¹ • x))) ∈ H :=
      (QuotientGroup.eq (s := H)).mp (by rw [mk_sec p G H x, h1])
    simpa [mul_assoc] using h2⟩

@[simp] lemma coe_A (g : G) (x : G ⧸ H) :
    (A p G H g x : G) = (sec p G H x)⁻¹ * g * sec p G H (g⁻¹ • x) := rfl

/-- The defining relation between the section and the `H`-coordinates. -/
lemma sec_mul_A (g : G) (x : G ⧸ H) :
    g * sec p G H (g⁻¹ • x) = sec p G H x * (A p G H g x : G) := by
  rw [coe_A p G H g x]
  group

/-- The `H`-coordinate on the coset space is multiplicative. -/
lemma A_mul (g g' : G) (x : G ⧸ H) :
    A p G H (g * g') x = A p G H g x * A p G H g' (g⁻¹ • x) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul H, coe_A p G H (g * g') x, coe_A p G H g x, coe_A p G H g' (g⁻¹ • x)]
  rw [show (g * g')⁻¹ • x = g'⁻¹ • (g⁻¹ • x) from by rw [mul_inv_rev, mul_smul]]
  group

/-- At the base point the `H`-coordinate of `h : H` is `h` itself. -/
lemma A_basePoint (h : H) : A p G H (h : G) (basePoint p G H) = h := by
  apply Subtype.ext
  have hfix : (((h : G))⁻¹ • basePoint p G H : G ⧸ H) = basePoint p G H := by
    simpa using basePoint_smul_eq p G H (h⁻¹)
  rw [coe_A p G H (h : G) (basePoint p G H), hfix, sec_basePoint]
  group

/-! ## Framed `G`-sets: `H`-coordinates -/

section Framed

variable (X : Type w) [MulAction G X]

/-- The `H`-coordinate of `g` at the point `x` of a framed `G`-set:
`AX G H X s hsec g x = (s x)⁻¹ * g * s (g⁻¹ • x)`. -/
noncomputable def AX (s : X → G)
    (hsec : ∀ (g : G) (x : X), (s x)⁻¹ * g * s (g⁻¹ • x) ∈ H) (g : G) (x : X) : H :=
  ⟨(s x)⁻¹ * g * s (g⁻¹ • x), hsec g x⟩

@[simp] lemma coe_AX (s : X → G)
    (hsec : ∀ (g : G) (x : X), (s x)⁻¹ * g * s (g⁻¹ • x) ∈ H) (g : G) (x : X) :
    (AX G H X s hsec g x : G) = (s x)⁻¹ * g * s (g⁻¹ • x) := rfl

/-- The defining relation between `s` and the `H`-coordinates. -/
lemma s_mul_AX (s : X → G)
    (hsec : ∀ (g : G) (x : X), (s x)⁻¹ * g * s (g⁻¹ • x) ∈ H) (g : G) (x : X) :
    g * s (g⁻¹ • x) = s x * (AX G H X s hsec g x : G) := by
  rw [coe_AX G H X s hsec g x]
  group

/-- The `H`-coordinates of a framed `G`-set are multiplicative. -/
lemma AX_mul (s : X → G)
    (hsec : ∀ (g : G) (x : X), (s x)⁻¹ * g * s (g⁻¹ • x) ∈ H) (g g' : G) (x : X) :
    AX G H X s hsec (g * g') x = AX G H X s hsec g x * AX G H X s hsec g' (g⁻¹ • x) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul H, coe_AX G H X s hsec (g * g') x, coe_AX G H X s hsec g x,
    coe_AX G H X s hsec g' (g⁻¹ • x)]
  rw [show (g * g')⁻¹ • x = g'⁻¹ • (g⁻¹ • x) from by rw [mul_inv_rev, mul_smul]]
  group

/-- At a point fixed by `H` the `H`-coordinate of `h : H` is `h` itself. -/
lemma AX_base (s : X → G)
    (hsec : ∀ (g : G) (x : X), (s x)⁻¹ * g * s (g⁻¹ • x) ∈ H) (x₀ : X) (hbase : s x₀ = 1)
    (hfix : ∀ h : H, (h : G) • x₀ = x₀) (h : H) : AX G H X s hsec (h : G) x₀ = h := by
  apply Subtype.ext
  have hfix' : (((h : G))⁻¹ • x₀ : X) = x₀ := by
    simpa using hfix (h⁻¹)
  rw [coe_AX G H X s hsec (h : G) x₀, hfix', hbase]
  group

end Framed

/-! ## The permutation module `𝔽_p[X]` of a `G`-set -/

section PermMod

variable (X : Type w) [MulAction G X]

/-- The permutation module `𝔽_p[X]` of a `G`-set `X`, as the module of functions `X → 𝔽_p`. -/
abbrev PermModX : Type w := X → ZMod p

instance instSMulPermModX : SMul G (PermModX p X) :=
  ⟨fun g f x => f (g⁻¹ • x)⟩

@[simp] lemma smul_PermModX_apply (g : G) (f : PermModX p X) (x : X) :
    (g • f) x = f (g⁻¹ • x) := rfl

instance instMulActionPermModX : MulAction G (PermModX p X) where
  one_smul f := by ext x; simp [smul_PermModX_apply]
  mul_smul g g' f := by
    ext x
    simp only [smul_PermModX_apply]
    rw [mul_inv_rev, mul_smul]

instance instDistribMulActionPermModX : DistribMulAction G (PermModX p X) where
  toMulAction := instMulActionPermModX p G X
  smul_zero g := by ext x; simp [smul_PermModX_apply]
  smul_add g f f' := by ext x; simp [smul_PermModX_apply, Pi.add_apply]

instance instSMulCommClassPermModX : SMulCommClass G (ZMod p) (PermModX p X) where
  smul_comm g c f := by ext x; simp [smul_PermModX_apply, Pi.smul_apply]

/-- The permutation module of a finite `G`-set is finite dimensional over `𝔽_p`. -/
theorem moduleFinite_permModX [Fintype X] : Module.Finite (ZMod p) (PermModX p X) :=
  Module.Finite.pi

end PermMod

/-! ## The identification `M ⊗ 𝔽_p[X] ≃ (X → M)` and the induced cocycle -/

section Cocycle

variable (X : Type w) [MulAction G X]
variable (s : X → G)
variable (hsec : ∀ (g : G) (x : X), (s x)⁻¹ * g * s (g⁻¹ • x) ∈ H)
variable (x₀ : X) (hbase : s x₀ = 1) (hfix : ∀ h : H, (h : G) • x₀ = x₀)
variable (M : Type v) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
  [SMulCommClass G (ZMod p) M]

/-- The canonical `𝔽_p`-linear identification `M ⊗ 𝔽_p[X] ≃ (X → M)`, `m ⊗ f ↦ (x ↦ f x • m)`. -/
noncomputable def permEquivX [Fintype X] [DecidableEq X] :
    M ⊗[ZMod p] PermModX p X ≃ₗ[ZMod p] (X → M) :=
  TensorProduct.piScalarRight (ZMod p) (ZMod p) M X

@[simp] lemma permEquivX_tmul [Fintype X] [DecidableEq X] (m : M) (f : PermModX p X) :
    permEquivX p X M (m ⊗ₜ[ZMod p] f) = fun x => f x • m := by
  rw [permEquivX, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]

/-- The function `X → M` attached to a 2-cochain `c` on `H` and a pair `(g,g')` of elements of `G`;
its value at the base point is used to define the induced cocycle. -/
noncomputable def funCX (c : H × H → M) (g g' : G) : X → M :=
  fun x => (s x : G) • c (AX G H X s hsec g x, AX G H X s hsec g' (g⁻¹ • x))

@[simp] lemma funCX_apply (c : H × H → M) (g g' : G) (x : X) :
    funCX G H X s hsec M c g g' x
      = (s x : G) • c (AX G H X s hsec g x, AX G H X s hsec g' (g⁻¹ • x)) := rfl

end Cocycle

end Shapiro
end Work.SSGRoute
