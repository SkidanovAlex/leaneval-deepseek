import Submission.Work.Higman.Family

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix VIII of Peterfalvi I: automorphism groups of the Suzuki 2-groups `A`, `B`, `C`

Peterfalvi I, App. VIII (pp. 221–229) computes `Aut(A(n,φ))`, `Aut(B(n,1))` and the stabiliser of
`P₁` in `Aut(C(n,ε))`, showing that each maps onto a group of *semilinear* maps
`x ↦ λ·σ(x)` with elementary abelian `2`-group kernel, hence is solvable. These are the inputs
used in Ch. IV §4 to exclude the non-abelian case of the hard core of Hering's theorem.

The groups `A(n,φ)`, `B(n,1,ε)`, `C(n,ε)` are the explicit two-step groups of Higman's table
(`Work.Higman.Family`).
-/

set_option autoImplicit false

namespace Work.Hering

/-- **App. VIII Prop. 1** (p. 224): if `φ` is an automorphism of `GF(2ⁿ)` with `φ⁴ ≠ 1`, then
`Aut(A(n,φ))` is solvable. (Any `φ` of odd order `≠ 1` satisfies `φ⁴ ≠ 1`.) -/
def AppVIIIProp1 : Prop :=
  ∀ (n : ℕ) (φ : GaloisField 2 n ≃+* GaloisField 2 n),
    φ ^ 4 ≠ 1 → Group.IsSolvable (MulAut (Work.Higman.AType (GaloisField 2 n) φ))

/-- **App. VIII Prop. 3** (p. 226): `Aut(B(n,1,ε))` is solvable (for `ε` satisfying the
irreducibility condition `a² + εab + b² = 0 ⇒ a = b = 0`). -/
def AppVIIIProp3 : Prop :=
  ∀ (n : ℕ) (ε : GaloisField 2 n),
    (∀ a b : GaloisField 2 n, a * a + ε * (a * b) + b * b = 0 → a = 0 ∧ b = 0) →
    Group.IsSolvable
      (MulAut (Work.Higman.BType (GaloisField 2 n) (RingEquiv.refl (GaloisField 2 n)) ε))

/-- The setwise stabiliser of a subgroup `P` of `G` in the automorphism group `Aut(G)`. -/
def stabilizerMulAut {G : Type*} [Group G] (P : Subgroup G) : Subgroup (MulAut G) where
  carrier := {φ | ∀ x : G, φ x ∈ P ↔ x ∈ P}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro φ ψ hφ hψ x
    show (φ * ψ) x ∈ P ↔ x ∈ P
    rw [show (φ * ψ) x = φ (ψ x) from rfl, hφ, hψ]
  inv_mem' := by
    intro φ hφ x
    have h := hφ (φ⁻¹ x)
    simpa using h.symm

/-- The subgroup `P₁ = π^{-1}(0 × K)` of `C(n,ε)`, in the two-step model: the elements whose
`A`-coordinate `x.fst : K × K` has first component `0` (App. VIII, p. 227). -/
def CTypeP1 {F : Type*} [Field F] [CharP F 2] [Finite F] (θ : F ≃+* F) (ε : F) :
    Subgroup (Work.Higman.CType F θ ε) where
  carrier := {x | x.fst.1 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    show (x * y).fst.1 = 0
    rw [Work.Higman.TwoStep.fst_mul]
    show x.fst.1 + y.fst.1 = 0
    rw [hx, hy, zero_add]
  inv_mem' := by
    intro x hx
    show x⁻¹.fst.1 = 0
    rw [Work.Higman.TwoStep.fst_inv]
    exact hx

/-- **App. VIII Prop. 4** (p. 227): with `n = 2s+1`, `θ : x ↦ x^{2^s}` the `s`-th power of the
Frobenius of `GF(2ⁿ)`, `ε` satisfying the source's anisotropy condition
`x·θ(x) + ε·x^{1/2}·θ(y²) + y² = 0 ⇒ x = y = 0`, and `P₁ ≤ C(n,ε)` the subgroup of elements whose
`A`-coordinate has first component `0`, the stabiliser of `P₁` in `Aut(C(n,ε))` is solvable. -/
def AppVIIIProp4 : Prop :=
  ∀ (s : ℕ) (ε : GaloisField 2 (2 * s + 1)), 1 ≤ s →
    (∀ x y : GaloisField 2 (2 * s + 1),
      x * (((frobeniusEquiv (GaloisField 2 (2 * s + 1)) 2) ^ s) x) +
        ε * (Work.Higman.sqrtF (GaloisField 2 (2 * s + 1)) x *
          (((frobeniusEquiv (GaloisField 2 (2 * s + 1)) 2) ^ s) (y * y))) + y * y = 0 →
      x = 0 ∧ y = 0) →
    Group.IsSolvable (stabilizerMulAut (CTypeP1
      ((frobeniusEquiv (GaloisField 2 (2 * s + 1)) 2) ^ s) ε))

end Work.Hering
