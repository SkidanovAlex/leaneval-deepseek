import Mathlib
import Submission.Work.CFT.Kummer.Defs

/-!
# Shafarevich's relation-rank estimate: the Kummer-theoretic input

This file isolates the arithmetic input of **Shafarevich's relation-rank estimate** for the Galois
group of the maximal pro-`p` extension of a number field, in the Kummer form used by
D. Hajir, C. Maire, R. Ramakrishna, *Cutting towers of number fields*, arXiv:1901.04354,
§"Some set up", referring to H. Koch, *Galois theory of p-extensions*, Chapter 11:

> `V_S = {x ∈ Kˣ | x ∈ K_v^{×p} for v ∈ S, and v(x) ≡ 0 mod p for all v}`, `𝓒_S` the character
> group of `V_S/K^{×p}`, and the exact sequence `0 → Ш²_S → H²(G_S) → ⊕_{v∈S} H²(G_{K_v})`,
> where each local term is `ℤ/pℤ` or `0` according as `μ_p ⊆ K_v`; when `μ_p ⊆ K` global
> reciprocity puts the image in the hyperplane of vectors whose invariants sum to zero.  From
> Chapter 11 of Koch:
> `d_p G_S = (Σ_{v ∈ S_p} [K_v:ℚ_v]) − δ_{K,p} + (Σ_{v∈S} δ_{K_v,p}) − (r₁+r₂) + 1 + d_p 𝓒_S`,
> and there is a natural injection `Ш²_S ↪ 𝓒_S`, an isomorphism if `S` contains all primes above
> `p`.

The two facts **(a)** (the injection) and **(b)** (the rank formula) are the only arithmetic input
of the estimate proved in `Work.CFT.Kummer.Estimate`; they are recorded here as fields of two
structures, one for `S = ∅` (`UnramifiedShafarevich`) and one for a tame `S`
(`ShafarevichTame`), and are *not* proved in this development (see `README.md`).

In the general rank formula the notation `S_p` is the set of places of `S` **above** `p`; for
`S = ∅` and for tame `S` (no place of `S` above `p`) the corresponding sum of local degrees
vanishes.  The general "wild" case needs `[K_v : ℚ_p]`, which is not available in Mathlib; the
`S = ∅` case and the tame case, which are the ones used by the tower construction, are what is
formalised here.

## Main definitions

* `Work.CFT.Kummer.IsTame K p S` — `S` contains no place above `p`.
* `Work.CFT.Kummer.UnramifiedShafarevich K p G` — facts (a), (b) at `S = ∅` for
  `G = Gal(K_∅(p)/K)`.
* `Work.CFT.Kummer.ShafarevichTame K p S G` — facts (a), (b) for tame `S`, together with the local
  data `H²(G_{K_v}, 𝔽_p)` and Hilbert reciprocity.
* `Work.CFT.Kummer.KochTransfer p G` — Koch's transfer / pro-`p` presentation theorem, the input
  for passing to finite quotients of `G`.
-/

open scoped nonZeroDivisors
open NumberField

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Work.CFT.Kummer

/-- `H¹(G, 𝔽_p)` with trivial coefficients (`Work.Tower.Shafarevich.H1Fp`, re-exported). -/
abbrev H1Fp (p : ℕ) (G : Type) [Group G] : ModuleCat (ZMod p) :=
  Work.Tower.Shafarevich.H1Fp p G

/-- `H²(G, 𝔽_p)` with trivial coefficients (`Work.Tower.Shafarevich.H2Fp`, re-exported). -/
abbrev H2Fp (p : ℕ) (G : Type) [Group G] : ModuleCat (ZMod p) :=
  Work.Tower.Shafarevich.H2Fp p G

/-- A finite set `S` of finite places of `K` is **tame** at the prime `p` if no place of `S` lies
above `p`; in the notation of Hajir–Maire–Ramakrishna, `S_p = ∅`. -/
def IsTame (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) : Prop :=
  ∀ v ∈ S, ¬ IsAboveP K p v

/-- **The Shafarevich–Kummer input at `S = ∅`**, for the Galois group
`G = Gal(K_∅(p)/K)` of the maximal pro-`p` extension of `K` unramified everywhere:

* `sha` is the **natural injection** `Ш²_∅ = H²(G, 𝔽_p) ↪ 𝓒_∅` of Koch's Chapter 11 (for `S = ∅`
  there are no local conditions, so `Ш²_∅ = H²(G,𝔽_p)`);
* `rank_formula` is the **H¹ rank formula** at `S = ∅`,
  `dim 𝓒_∅ = dim H¹(G,𝔽_p) + (r₁ + r₂ - 1) + δ_{K,p}`, which is Koch's formula
  `d_p G_∅ = (Σ_{v ∈ S_p}[K_v:ℚ_v]) - δ_{K,p} + (Σ_{v∈S}δ_{K_v,p}) - (r₁+r₂) + 1 + d_p 𝓒_∅`
  with `S = ∅` (so that both sums vanish), using `r₁ + r₂ - 1 = NumberField.Units.rank K`.

These two facts are the entire arithmetic input of `Work.CFT.Kummer.finrank_H2Fp_le_H1Fp_add`. -/
class UnramifiedShafarevich (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (G : Type) [Group G] where
  /-- `H²(G, 𝔽_p)` is finite-dimensional. -/
  [finite_H2 : Module.Finite (ZMod p) (H2Fp p G)]
  /-- The Kummer character group `𝓒_∅` is finite-dimensional. -/
  [finite_dual : Module.Finite (ZMod p) (kummerDual K p ∅)]
  /-- **(a)** the Shafarevich map `Ш²_∅ = H²(G,𝔽_p) → 𝓒_∅`. -/
  sha : H2Fp p G →ₗ[ZMod p] kummerDual K p ∅
  /-- **(a)** the Shafarevich map is injective. -/
  sha_injective : Function.Injective sha
  /-- **(b)** the H¹ rank formula at `S = ∅`. -/
  rank_formula : Module.finrank (ZMod p) (kummerDual K p ∅) =
    Module.finrank (ZMod p) (H1Fp p G) + NumberField.Units.rank K + deltaK K p

/-- **The Shafarevich–Kummer input for a tame set `S`** of finite places, for the Galois group
`G = Gal(K_S(p)/K)` of the maximal pro-`p` extension of `K` unramified outside `S`.  Besides facts
(a) and (b) it carries the local data:

* `H2loc v` is the local group `H²(G_{K_v}, 𝔽_p)`, an `𝔽_p`-vector space of dimension
  `δ_{K_v,p} = deltaLocal K p v` (by the local Euler–Poincaré/duality computation for `p`-adic
  fields it is `𝔽_p` if `μ_p ⊆ K_v` and `0` otherwise);
* `loc` is the localisation map `H²(G_S,𝔽_p) → ∏_{v∈S} H²(G_{K_v},𝔽_p)` and `inv v` the local
  invariant `H²(G_{K_v},𝔽_p) → 𝔽_p`, injective when `μ_p ⊆ K_v`;
* `reciprocity` is **Hilbert reciprocity**: when `μ_p ⊆ K`, the image of `loc` lies in the
  hyperplane of vectors whose local invariants sum to zero;
* `sha` is the injection `Ш²_S = ker loc ↪ 𝓒_S` of Koch's Chapter 11;
* `rank_formula` is the H¹ rank formula for tame `S` (`S_p = ∅`), namely
  `dim 𝓒_S + Σ_{v∈S}δ_{K_v,p} = dim H¹(G_S,𝔽_p) + δ_{K,p} + (r₁+r₂-1)`. -/
class ShafarevichTame (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) (G : Type) [Group G] where
  /-- `S` contains no place above `p`. -/
  tame : IsTame K p S
  /-- `H²(G, 𝔽_p)` is finite-dimensional. -/
  [finite_H2 : Module.Finite (ZMod p) (H2Fp p G)]
  /-- The Kummer character group `𝓒_S` is finite-dimensional. -/
  [finite_dual : Module.Finite (ZMod p) (kummerDual K p S)]
  /-- The local groups `H²(G_{K_v}, 𝔽_p)`, indexed by the places `v ∈ S`. -/
  H2loc : {v // v ∈ S} → ModuleCat (ZMod p)
  /-- The local groups are finite-dimensional. -/
  [h2locFinite : ∀ v, Module.Finite (ZMod p) (H2loc v : Type)]
  /-- The local groups have the expected dimensions: `dim H²(G_{K_v},𝔽_p) = δ_{K_v,p}`, i.e. the
  local group is `𝔽_p` if `μ_p ⊆ K_v` and `0` otherwise. -/
  finrank_H2loc : ∀ v, Module.finrank (ZMod p) (H2loc v : Type) = deltaLocal K p v.1
  /-- The product of the local groups is finite-dimensional. -/
  [locFinite : Module.Finite (ZMod p) ((v : {v // v ∈ S}) → (H2loc v : Type))]
  /-- The localisation map `H²(G_S,𝔽_p) → ∏_{v∈S} H²(G_{K_v},𝔽_p)`. -/
  loc : H2Fp p G →ₗ[ZMod p] ((v : {v // v ∈ S}) → (H2loc v : Type))
  /-- The local invariant maps. -/
  inv : (v : {v // v ∈ S}) → (H2loc v : Type) →ₗ[ZMod p] ZMod p
  /-- The local invariant is injective when `μ_p ⊆ K_v`. -/
  inv_injective : ∀ v, deltaLocal K p v.1 = 1 → Function.Injective (inv v)
  /-- **Hilbert reciprocity**: when `μ_p ⊆ K`, the image of the localisation map lies in the
  hyperplane of vectors whose local invariants sum to zero. -/
  reciprocity : deltaK K p = 1 → ∀ x : H2Fp p G,
    (∑ v : {v // v ∈ S}, inv v (loc x v)) = 0
  /-- **(a)** the Shafarevich map `Ш²_S = ker loc → 𝓒_S`. -/
  sha : ↥(LinearMap.ker loc) →ₗ[ZMod p] kummerDual K p S
  /-- **(a)** the Shafarevich map is injective. -/
  sha_injective : Function.Injective sha
  /-- **(b)** the H¹ rank formula for tame `S`. -/
  rank_formula : Module.finrank (ZMod p) (kummerDual K p S) +
      (∑ v ∈ S, deltaLocal K p v) =
    Module.finrank (ZMod p) (H1Fp p G) + deltaK K p + NumberField.Units.rank K

/-- **The primitive Kummer/Poitou–Tate input at `S = ∅`**, factoring out the Kummer-theoretic
content: (a) the Shafarevich injection `Ш²_∅ = H²(G,𝔽_p) ↪ 𝓒_∅`, together with (b′) the fact that
the generator rank of the maximal everywhere-unramified pro-`p` group `G` is the `p`-rank of the
class group, `dim H¹(G,𝔽_p) = dim Cl_K[p]`.

By the Kummer computation `Work.CFT.Kummer.finrank_kummerDual_empty`
(`dim 𝓒_∅ = dim Cl_K[p] + (r₁+r₂-1) + δ_{K,p}`, proved in this area) this is *equivalent* to
`UnramifiedShafarevich`; see `Work.CFT.Kummer.unramifiedShafarevich_iff_classGroup` in `ClassRank`.
The point of the separate formulation is that (b′) is precisely the arithmetic statement whose
proof needs unramified global class field theory (Artin reciprocity for the Hilbert class field),
with all of the Kummer theory moved into theorems of this area. -/
class UnramifiedShafarevichClassGroup (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (G : Type) [Group G] where
  /-- `H²(G, 𝔽_p)` is finite-dimensional. -/
  [finite_H2 : Module.Finite (ZMod p) (H2Fp p G)]
  /-- The Kummer character group `𝓒_∅` is finite-dimensional. -/
  [finite_dual : Module.Finite (ZMod p) (kummerDual K p ∅)]
  /-- **(a)** the Shafarevich map `Ш²_∅ = H²(G,𝔽_p) → 𝓒_∅`. -/
  sha : H2Fp p G →ₗ[ZMod p] kummerDual K p ∅
  /-- **(a)** the Shafarevich map is injective. -/
  sha_injective : Function.Injective sha
  /-- **(b′)** the generator rank is the `p`-rank of the class group. -/
  h1_eq_classGroupRank : Module.finrank (ZMod p) (H1Fp p G) =
    Module.finrank (ZMod p) (classGroupTorsion K p)

/-- **Koch's transfer / pro-`p` presentation theorem**: if `N` is the normal closure of `k`
elements of `G`, then the quotient `G ⧸ N` has pro-`p` relation rank at most
`dim H²(G, 𝔽_p) + k`.  Equivalently, adjoining `k` relators to a (minimal) pro-`p` presentation of
`G` presents `G ⧸ N`, and `dim_{𝔽_p} H²(P, 𝔽_p)` is the minimal number of relators in a minimal
pro-`p` presentation of a pro-`p` group `P` (Koch, *Galois theory of p-extensions*,
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Prop. 3.9.5).  This is the group-theoretic
input that transfers Shafarevich's estimate from `G` to its finite quotients; it is stated here as a
hypothesis about the abstract group `G` standing for the pro-`p` group. -/
def KochTransfer (p : ℕ) (G : Type) [Group G] : Prop :=
  ∀ (N : Subgroup G) [N.Normal] (k : ℕ) (g : Fin k → G)
      (_hN : N = Subgroup.normalClosure (Set.range g)),
    Module.finrank (ZMod p) (H2Fp p (G ⧸ N)) ≤ Module.finrank (ZMod p) (H2Fp p G) + k

set_option warn.classDefReducibility false in
attribute [instance] UnramifiedShafarevich.finite_H2 UnramifiedShafarevich.finite_dual
  ShafarevichTame.finite_H2 ShafarevichTame.finite_dual ShafarevichTame.h2locFinite
  ShafarevichTame.locFinite UnramifiedShafarevichClassGroup.finite_H2
  UnramifiedShafarevichClassGroup.finite_dual

end Work.CFT.Kummer
