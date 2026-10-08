import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ZassenhausSuzuki`: Higman's group `A(K,θ)` and the Suzuki configuration

This module fixes the vocabulary of the area, following Baumeister–Grüninger,
*Finite Zassenhaus Moufang sets with root groups of even order*, §5 (arXiv:1011.5836),
and M. Suzuki, *On a class of doubly transitive groups*, Ann. of Math. **75** (1962).

Sources for the definitions (`REFS/zassenhaus_groups.md` §3.4):

* **Example 5.2 (BG).** For a field `K` of characteristic two and a non-zero endomorphism
  `θ` of `K` (here always a ring automorphism) put `A(K,θ) := K × K` with
  `(a,b) * (c,d) = (a + c, b + d + a·(θ c))`.  For `K = GF(2ⁿ)` this is written `A(n,θ)`;
  if `θ ≠ 1` it is non-abelian with centre `{(0,b)}`, and if `o(θ)` is odd it is a
  *Suzuki 2-group* (Higman's list).
* **Definition 5.5 (BG).** For a Tits endomorphism `θ` (`θ² =` Frobenius) put
  `N(a,b) = a^{2+θ} + a b + b^θ` and let `τ` be the map `(a,b) ↦ (b/N(a,b), a/N(a,b))`.
  The little projective group of the resulting Suzuki Moufang set is `Sz(2ⁿ)`;
  in the matrix model (`LeanEval.GroupTheory.Defs.SzModel`) the Weyl involution `t`
  satisfies `t x t = m · t · τ(x)` for `x ∈ A(K,θ)^#` and a suitable `m ∈ Borel`.
* **Lemma 5.4 (BG) = Suzuki 1962, Lemma 6.** A cyclic Hua subgroup of `Aut(A(n,θ))` of order
  `2ⁿ - 1` acting transitively on the involutions is `Aut(A(n,θ))`-conjugate to `Λ`.

The purpose of `IsSuzukiConfiguration` below is to record in one structure *exactly* the
data that area `RankOneUniqueness` needs to identify `G` with the model `SzModel n`:
the Borel `H = Q ⋊ D` is isomorphic to the concrete Borel `SzBorel K θ = A(K,θ) ⋊ Kˣ`,
with `Q` and `D` matching `A(K,θ)` and `Kˣ`, and with the Weyl involution `t` acting on
`Q^#` by the Suzuki formula `τ`.

## Main definitions

* `SzA K θ` — Higman's group `A(K,θ)`.
* `SzBorel K θ` — the Borel `A(K,θ) ⋊ Kˣ` of the Suzuki group (action `h_λ`).
* `IsTitsTheta θ` — `θ²` is the Frobenius (squaring) of `K`.
* `IsSuzukiConfiguration G H Q t K θ` — the Suzuki rank-one configuration on `G`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

/-- **Higman's group `A(K,θ)`** (BG Example 5.2), multiplicatively: the set `K × K` with
`(a,b) * (c,d) = (a+c, b+d+a·θ(c))`.  The group law is written additively in the sources;
here it is multiplicative so that `SzA K θ` is an honest `Group`. -/
@[ext]
structure SzA (K : Type*) [Field K] (θ : K ≃+* K) where
  /-- first coordinate -/
  a : K
  /-- second coordinate -/
  b : K

namespace SzA

variable {K : Type*} [Field K] (θ : K ≃+* K)

instance instMul : Mul (SzA K θ) :=
  ⟨fun x y => ⟨x.a + y.a, x.b + y.b + x.a * θ y.a⟩⟩

instance instOne : One (SzA K θ) := ⟨⟨0, 0⟩⟩

instance instInv : Inv (SzA K θ) := ⟨fun x => ⟨-x.a, -x.b + x.a * θ x.a⟩⟩

@[simp] theorem mul_a (x y : SzA K θ) : (x * y).a = x.a + y.a := rfl
@[simp] theorem mul_b (x y : SzA K θ) : (x * y).b = x.b + y.b + x.a * θ y.a := rfl
@[simp] theorem one_a : (1 : SzA K θ).a = 0 := rfl
@[simp] theorem one_b : (1 : SzA K θ).b = 0 := rfl
@[simp] theorem inv_a (x : SzA K θ) : x⁻¹.a = -x.a := rfl
@[simp] theorem inv_b (x : SzA K θ) : x⁻¹.b = -x.b + x.a * θ x.a := rfl

theorem mul_assoc' (x y z : SzA K θ) : x * y * z = x * (y * z) := by
  ext <;> simp only [mul_a, mul_b, map_add, map_mul]
  · ring
  · ring

theorem one_mul' (x : SzA K θ) : 1 * x = x := by
  ext <;> simp

theorem mul_one' (x : SzA K θ) : x * 1 = x := by
  ext <;> simp

theorem inv_mul_cancel' (x : SzA K θ) : x⁻¹ * x = 1 := by
  ext <;> simp only [mul_a, mul_b, one_a, one_b, inv_a, inv_b, map_neg]
  · ring
  · ring

instance instFinite [Finite K] : Finite (SzA K θ) :=
  Finite.of_injective (fun x : SzA K θ => (x.a, x.b))
    (by intro x y h; ext <;> simp_all)

instance instGroup : Group (SzA K θ) where
  mul := (· * ·)
  one := 1
  inv := Inv.inv
  mul_assoc := mul_assoc' θ
  one_mul := one_mul' θ
  mul_one := mul_one' θ
  inv_mul_cancel := inv_mul_cancel' θ

/-- `N(a,b) = a^{2+θ} + a b + b^θ` (BG Definition 5.5). -/
def N (x : SzA K θ) : K := x.a * x.a * θ x.a + x.a * x.b + θ x.b

@[simp] theorem N_mk (a b : K) : N θ (⟨a, b⟩ : SzA K θ) = a * a * θ a + a * b + θ b := rfl

/-- The Suzuki involution `τ` in coordinates (BG Definition 5.5):
`(a,b) ↦ (b/N(a,b), a/N(a,b))`.  The map is total; on `x ≠ 1` the denominator is non-zero
under the Tits hypothesis, see `N_ne_zero`. -/
def sigma (x : SzA K θ) : SzA K θ := ⟨x.b / N θ x, x.a / N θ x⟩

@[simp] theorem sigma_a (x : SzA K θ) : (sigma θ x).a = x.b / N θ x := rfl
@[simp] theorem sigma_b (x : SzA K θ) : (sigma θ x).b = x.a / N θ x := rfl

/-- The Suzuki torus automorphism `h_λ : (a,b) ↦ (λ a, λ^{1+θ} b)` (BG Example 5.2), as a
plain function. -/
def hLam (lam : K) (x : SzA K θ) : SzA K θ := ⟨lam * x.a, lam * θ lam * x.b⟩

@[simp] theorem hLam_a (lam : K) (x : SzA K θ) : (hLam θ lam x).a = lam * x.a := rfl
@[simp] theorem hLam_b (lam : K) (x : SzA K θ) : (hLam θ lam x).b = lam * θ lam * x.b := rfl

theorem hLam_one (x : SzA K θ) : hLam θ 1 x = x := by
  ext <;> simp

theorem hLam_mul (lam mu : K) (x : SzA K θ) :
    hLam θ (lam * mu) x = hLam θ lam (hLam θ mu x) := by
  ext <;> simp only [hLam_a, hLam_b, map_mul] <;> ring

/-- `h_λ` is a group automorphism of `A(K,θ)` (BG Example 5.2). -/
def hLamAut (lam : Kˣ) : MulAut (SzA K θ) where
  toFun := hLam θ (lam : K)
  invFun := hLam θ ((lam⁻¹ : Kˣ) : K)
  left_inv x := by
    show hLam θ ((lam⁻¹ : Kˣ) : K) (hLam θ (lam : K) x) = x
    rw [← hLam_mul θ ((lam⁻¹ : Kˣ) : K) (lam : K) x]
    have h : ((lam⁻¹ : Kˣ) : K) * (lam : K) = 1 := by simp
    rw [h, hLam_one]
  right_inv x := by
    show hLam θ (lam : K) (hLam θ ((lam⁻¹ : Kˣ) : K) x) = x
    rw [← hLam_mul θ (lam : K) ((lam⁻¹ : Kˣ) : K) x]
    have h : (lam : K) * ((lam⁻¹ : Kˣ) : K) = 1 := by simp
    rw [h, hLam_one]
  map_mul' x y := by
    ext <;> simp only [hLam_a, hLam_b, mul_a, mul_b, map_add, map_mul] <;> ring

@[simp] theorem hLamAut_apply (lam : Kˣ) (x : SzA K θ) :
    hLamAut θ lam x = hLam θ (lam : K) x := rfl

/-- The injective homomorphism `Kˣ →* Aut(A(K,θ))`, `λ ↦ h_λ` (BG Example 5.2);
its image is the group denoted `Λ`. -/
def hLamHom : Kˣ →* MulAut (SzA K θ) where
  toFun := hLamAut θ
  map_one' := by
    apply MulEquiv.ext
    intro x
    exact hLam_one θ x
  map_mul' lam mu := by
    apply MulEquiv.ext
    intro x
    rw [MulAut.mul_apply, hLamAut_apply, hLamAut_apply, hLamAut_apply, Units.val_mul]
    exact hLam_mul θ (lam : K) (mu : K) x

@[simp] theorem hLamHom_apply (lam : Kˣ) (x : SzA K θ) :
    hLamHom θ lam x = hLam θ (lam : K) x := rfl

end SzA

/-- The Borel subgroup `SzBorel K θ = A(K,θ) ⋊ Kˣ` of the Suzuki group, where `Kˣ` acts
through the automorphisms `h_λ` of BG Example 5.2. -/
abbrev SzBorel (K : Type*) [Field K] (θ : K ≃+* K) := SzA K θ ⋊[SzA.hLamHom θ] Kˣ

namespace SzBorel

variable {K : Type*} [Field K] (θ : K ≃+* K)

/-- The root subgroup `A(K,θ)` inside the Borel. -/
def root : Subgroup (SzBorel K θ) where
  carrier := {x | x.right = 1}
  one_mem' := rfl
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [SemidirectProduct.mul_right, hx, hy, mul_one]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [SemidirectProduct.inv_right, hx, inv_one]

/-- The torus `Kˣ` inside the Borel. -/
def torus : Subgroup (SzBorel K θ) where
  carrier := {x | x.left = 1}
  one_mem' := rfl
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [SemidirectProduct.mul_left, hx, hy, map_one, one_mul]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [SemidirectProduct.inv_left, hx, inv_one, map_one]

theorem mem_root {x : SzBorel K θ} : x ∈ root θ ↔ x.right = 1 := Iff.rfl
theorem mem_torus {x : SzBorel K θ} : x ∈ torus θ ↔ x.left = 1 := Iff.rfl

/-- The image of the Suzuki map `τ` inside the Borel: `(a,b) ↦ τ(a,b)` on the root
subgroup, extended by the identity on the second coordinate. -/
def sigmaElt (x : SzBorel K θ) : SzBorel K θ :=
  SemidirectProduct.inl (SzA.sigma θ x.left)

end SzBorel

/-- `θ` is a **Tits endomorphism** of `K` (BG Definition 5.5): `θ ≠ 1` and `θ²` is the
Frobenius endomorphism `x ↦ x²` of `K`.  For `K = GF(2ⁿ)` this forces `n` odd. -/
def IsTitsTheta {K : Type*} [Semiring K] (θ : K ≃+* K) : Prop :=
  θ ≠ 1 ∧ ∀ x : K, θ (θ x) = x ^ 2

end Work.ZassenhausSuzuki
