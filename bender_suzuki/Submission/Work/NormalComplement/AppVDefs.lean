/-
# The abstract core of Peterfalvi Appendix V (d) (p.211)

Appendix V (d) says: let `U` act faithfully on an elementary abelian group `Q` of order `d ^ n`
(`d` prime), let `T ⊴ U` be cyclic and irreducible on `Q`, and let `1 ≠ P ≤ U` with
`|C_Q(P₁)| = d` for every `1 ≠ P₁ ≤ P`.  Then `|P| = p` is prime, `|Q| = d ^ p`, and
`C_U(s) = P` for `1 ≠ s ∈ C_Q(P)`.

The proof (Schur's lemma + Galois theory of finite fields) is carried out in the linear-algebra
core `AppVCoreProp` below, which is stated for a finite field `k` and a finite `k`-vector space `V`:
`Q` becomes `V`, the cyclic irreducible `T` becomes an irreducible linear automorphism `t`,
`U` becomes a subgroup of `V ≃ₗ[k] V` normalising `⟨t⟩`, fixed subgroups `C_Q(P₁)` become fixed
subspaces `{v | ∀ u ∈ P₁, u v = v}`, and `d = |k|`.

The statement `AppVProp` of `Sections.lean` is then obtained from `AppVCoreProp` by the glue
lemma `Work.NormalComplement.appV_of_core`.
-/
import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- **The abstract linear-algebra core of App. V (d).**  `k` is a finite field, `V` a finite
`k`-vector space, `t` an irreducible linear automorphism of `V` (no non-trivial `t`-invariant
subspace, i.e. `V` is simple as a `k[t]`-module), `U ≤ GL_k(V)` normalises `⟨t⟩`, and `1 ≠ P ≤ U`
satisfies `|C_V(P₁)| = |k|` for every `1 ≠ P₁ ≤ P`.  Then `|P| = p` is prime, `|V| = |k| ^ p`, and
`C_U(v) = P` for every `0 ≠ v ∈ C_V(P)`.

The proof: `F := k[t]` is a field of order `|k| ^ n` (`n = dim_k V`, Schur), `V` is 1-dimensional
over `F`, each `u ∈ U` acts `σ_u`-semilinearly, and the fixed space of `P₁` is the fixed field of
`σ(P₁) ≤ Gal(F/k)`; hence `|C_V(P₁)| = |k|` forces `|σ(P₁)| = n`. -/
def AppVCoreProp : Prop :=
  ∀ (k V : Type) [Field k] [Finite k] [AddCommGroup V] [Module k V] [Finite V]
    (t : V ≃ₗ[k] V)
    (_ : ∀ W : Submodule k V, (∀ x ∈ W, t x ∈ W) → W = ⊥ ∨ W = ⊤)
    (U : Subgroup (V ≃ₗ[k] V)) (_ : t ∈ U) (_ : ∀ u ∈ U, u * t * u⁻¹ ∈ Subgroup.zpowers t)
    (P : Subgroup (V ≃ₗ[k] V)) (_ : P ≤ U) (_ : P ≠ ⊥)
    (_ : ∀ P₁ : Subgroup (V ≃ₗ[k] V), P₁ ≤ P → P₁ ≠ ⊥ →
        Nat.card {v : V // ∀ u ∈ P₁, u v = v} = Nat.card k),
    (Nat.card P).Prime ∧ Nat.card V = (Nat.card k) ^ Nat.card P ∧
      ∀ v : V, (∀ u ∈ P, u v = v) → v ≠ 0 → ∀ u ∈ U, u v = v → u ∈ P

end Work.NormalComplement
