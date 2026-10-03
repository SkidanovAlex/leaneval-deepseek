/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# `StarRegularEnvelope`: the analytic core `N(G)`/`U(G)`

For a countable group `G` we denote by `N(G)` the group von Neumann algebra (the commutant
of the right regular representation on `ℓ²(G)`) and by `U(G)` the algebra of operators
affiliated to `N(G)`, i.e. the Ore localisation of `N(G)` at its set of non-zero-divisors
(Berberian).  `U(G)` is a positive definite `*`-regular ring containing `ℂ[G]`, equipped
with a faithful Sylvester rank function `rk_G` (the extended dimension function), and the
subgroup inclusions `U(H) ⊆ U(G)`, `H ≤ G` are *Linnell independent*.

This file fixes the *interface* through which the rest of the project uses these objects.
It is a faithful transcription of the properties used in
Jaikin-Zapirain–López-Álvarez, arXiv:1810.12135, §3.1–3.5 (the group case) and in
Jaikin-Zapirain–Linton, arXiv:2303.05976, §2.3, §5 and App. (Linnell independence).

## Main definitions

* `Work.ORVonNeumann.EnvelopeInclusion` — the data of `U(H) ⊆ U(G)`, `H ≤ G`;
* `Work.ORVonNeumann.LinnellIndependent` — the Linnell independence property
  (`U(H) ⊗_{ℂ[H]} ℂ[G] → U(G)` injective, in the equivalent coset form);
* `Work.ORVonNeumann.StarRegularEnvelope` — the envelope.

## Field-by-field correspondence with the literature

| field of `StarRegularEnvelope` | meaning | source |
|---|---|---|
| `U`, `ringU`, `starU`, `algebraU` | the algebra `U(G)` of operators affiliated to `N(G)`, an involution and a `ℂ`-algebra structure | JZLA20 §3.2 |
| `ι`, `ι_injective`, `ι_star`, `ι_algebraMap` | the `*`-embedding `ℂ[G] ↪ U(G)`, `(∑ r_g g)⋆ = ∑ conj(r_g) g⁻¹` | JZLA20 §3.2 |
| `starRegular` | `U(G)` is `*`-regular (equivalently, by `isStarRegularRing_iff_hasRelativeInverse`, every element has a relative inverse) | JZLA20 §3.1 |
| `posDef` | `Matₙ(U(G))` is `*`-regular for all `n` ("positive definite") | JZLA20 §3.1 |
| `rk`, `rk_faithful` | the extended rank function `rk_G`, normalised (`rk 1 = 1` is an axiom) and faithful | JZLA20 §3.2 |
| `sub H` | `U(H) ⊆ U(G)`, `H ≤ G`, as a `*`-ring embedding | JZLA20 §3.2 |
| `sub H .linnell` | Linnell independence of `U(H)` in `U(G)` | JL (arXiv:2303.05976), proof of Theorem `vanishing`; Gräter's theorem in JL §2.3 |

## The concrete construction, and what of it is proved

`ℓ²(G) = MeasureTheory.Lp ℂ 2 (Measure.count : Measure G)` is a genuine Hilbert space, `ρ` is
the right regular representation as a monoid homomorphism `G →* B(ℓ²(G))` given by composition
with `· * g`, and `N(G) := StarSubalgebra.centralizer ℂ (Set.range ρ)` is its commutant in
`B(ℓ²(G))`, with `τ (T) := ⟪δ₁, T δ₁⟫`.

**Proved for every countable `G`** (see `Submission.Work.ORVonNeumann.Rep` and
`Submission.Work.Rep`): `{δ_g}` is an orthonormal Hilbert basis of `ℓ²(G)` with
`x = ∑' g, ⟪δ_g, x⟫ • δ_g`; `τ` is a faithful, positive, `*`-preserving **tracial** linear
functional (`Work.ORVonNeumann.Rep.tau_tracial`, `...tau_star_mul_self_eq_zero_iff`); `N(G)`
has the **Baer** property (`Work.ORVonNeumann.Rep.exists_rightAnnihilatorProjection`) and is
**directly finite** (`Work.ORVonNeumann.Rep.directly_finite`); the left regular
representation is a unitary injective homomorphism `G →* N(G)`
(`Work.ORVonNeumann.Rep.leftRegularHom`); and `τ` on projections is a dimension function with
values in `[0,1]` (`Work.ORVonNeumann.Rep.tau_projection*`).  They assemble into
`Work.ORVonNeumann.Rep.countableGroupVonNeumann : GroupVonNeumannAlgebra G`, whose only
hypothesis is the Ore condition at non-zero-divisors.

**Proved for every countable `G`** additionally: the Ore condition at non-zero-divisors
(`Work.Rep.oreSet_nonZeroDivisors`), so that `U(G) = N(G)[(N(G) ∖ {0})⁻¹]` exists
unconditionally; the involution making it a `*`-ring
(`Work.ORVonNeumann.Ore.star_oreLocalization`, `...VonNeumannAlgebra.UStar`); and the
inclusion `ℂ[G] ↪ U(G)` as a `*`-subalgebra (`...VonNeumannAlgebra.U`, `...UStar`).

**Proved for every countable `G` as well** (so the corresponding fields below are theorems,
not assumptions): the `*`-regularity of `U(G)` — `starRegular`
(`Work.ORVonNeumann.VonNeumannAlgebra.starRegularAffiliated`; the abstract form
`...isStarRegularRing_affiliated` holds for every `GroupVonNeumannAlgebra`, being Berberian's
theorem for a finite Baer `*`-ring).

**Proved for every countable `G` as well**: positive definiteness (`posDef`,
`Work.ORVonNeumann.VonNeumannAlgebra.posDefAffiliated`) and the faithful rank function on
`U(G)` (`rk`, `rk_faithful`, `Work.ORVonNeumann.VonNeumannAlgebra.rankAffiliated`; the rank
function on `N(G)` itself is `Work.ORVonNeumann.Rep.rank_vonNeumann`).

**The subgroup data** `sub : ∀ H : Subgroup G, EnvelopeInclusion G U ι H`, i.e. the inclusion
`U(H) ↪ U(G)` and Linnell independence, is proved for every `H ≤ G`
(`Work.ORVonNeumann.envelopeInclusionGeneral`) for the concrete model: it is the diagonal
embedding `N(H) → N(G)` along the right-coset decomposition `ℓ²(G) = ⊕_q ℓ²(H q)`
(`Work.ORVonNeumann.Rep.exists_diagHom`, `Rep.cosetDiagOp`), extended to `U(H) →+* U(G)` by
the Ore universal property
(`Work.ORVonNeumann.VonNeumannAlgebra.exists_envelopeInclusion_of_diagHom`).  Hence **every
field of the envelope is a theorem**: `Work.ORVonNeumann.countableStarRegularEnvelope :
StarRegularEnvelope G` is defined in `Submission.Work.ORVonNeumann.CountableEnvelope` for
every countable `G` carrying the counting-measure structure, and
`Work.ORVonNeumann.countableStarRegularEnvelopeOfCountable : Nonempty (StarRegularEnvelope G)`
for a bare `[Group G] [Countable G]`.

## Main results

* `Work.ORVonNeumann.StarRegularEnvelope.rank_injective` — the rank function pulls back to
  `ℂ[G]` and is faithful there;
* `Work.ORVonNeumann.StarRegularEnvelope.rank_single_one` — `rk_G(g) = 1`;
* `Work.ORVonNeumann.Envelope.linnell_powers` — the `t`-powers are `U(N)`-independent
  (JZLA20, Proposition 3.11).
-/
import Mathlib
import Submission.Work.ORVonNeumann.Basic
import Submission.Work.ORVonNeumann.SylvesterRank
import Submission.Work.ORVonNeumann.GroupAlgebraStar

set_option autoImplicit false

universe u

namespace Work.ORVonNeumann

variable {G : Type u}

/-- The Linnell independence property for a map `V ⊗_{ℂ[H]} ℂ[G] → U`, in the equivalent
coset form: if `q 0, …, q n` lie in pairwise distinct right cosets of `H` and all `d i` are
nonzero, then `∑ i, φ (d i) * q i ≠ 0`.

For the multiplicative map `U(H) ⊗_{ℂ[H]} ℂ[G] → U(G)` of Jaikin-Zapirain–Linton
(arXiv:2303.05976, proof of Theorem `vanishing`) this is exactly injectivity, by linearity
and the fact that the `ℂ[H]`-balanced relations are generated by `d · c ⊗ x = d ⊗ c · x`. -/
def LinnellIndependent [Group G] (H : Subgroup G) (V : Type u) [Ring V] (U : Type u)
    [Ring U] (φ : V →+* U) (ι : MonoidAlgebra ℂ G →+* U) : Prop :=
  ∀ (n : ℕ) (q : Fin (n + 1) → G) (d : Fin (n + 1) → V),
    (∀ i, d i ≠ 0) → (∀ i j, q i * (q j)⁻¹ ∈ H → i = j) →
      (∑ i, φ (d i) * ι (MonoidAlgebra.single (q i) 1)) ≠ 0

/-- The data of the inclusion `U(H) ⊆ U(G)` for a subgroup `H ≤ G`, together with the
Linnell independence of `U(H)` in `U(G)`.

`V` is `U(H)`, `ιH` is the structure map `ℂ[H] → U(H)`, `φ : U(H) → U(G)` is the inclusion
and `ι` is the structure map `ℂ[G] → U(G)`. -/
structure EnvelopeInclusion (G : Type u) [Group G] (U : Type u) [Ring U] [StarRing U]
    [Algebra ℂ U] (ι : MonoidAlgebra ℂ G →+* U) (H : Subgroup G) where
  /-- the ring `U(H)` -/
  V : Type u
  [ringV : Ring V]
  [starV : StarRing V]
  [algebraV : Algebra ℂ V]
  /-- the structure map `ℂ[H] → U(H)` -/
  ιH : MonoidAlgebra ℂ H →+* V
  ιH_injective : Function.Injective ιH
  ιH_star : ∀ x : MonoidAlgebra ℂ H, ιH (star x) = star (ιH x)
  ιH_algebraMap : ∀ c : ℂ, ιH (algebraMap ℂ (MonoidAlgebra ℂ H) c) = algebraMap ℂ V c
  starRegularV : IsStarRegularRing V
  posDefV : IsPositiveDefinite V
  rkV : SylvesterRankFunction V
  rkV_faithful : rkV.Faithful
  /-- the inclusion `U(H) → U(G)` -/
  φ : V →+* U
  φ_injective : Function.Injective φ
  φ_star : ∀ v : V, φ (star v) = star (φ v)
  φ_ι : ∀ (h : H) (c : ℂ),
    φ (ιH (MonoidAlgebra.single h c)) = ι (MonoidAlgebra.single (h : G) c)
  linnell : LinnellIndependent H V U φ ι

attribute [instance] EnvelopeInclusion.ringV EnvelopeInclusion.starV EnvelopeInclusion.algebraV

/-- **The analytic core of the one-relator coherence project.**

`U` is `U(G)`, the algebra of operators affiliated to the group von Neumann algebra
`N(G)`; `ι` is the inclusion `ℂ[G] ↪ U(G)`; `rk` is the extended rank function `rk_G`,
faithful and normalised (`rk 1 = 1`); `sub` records the subgroups `U(H) ⊆ U(G)` and the
Linnell independence of `U(H)` in `U(G)`.

Every field is a property used in the literature:
* `starRegular` is JZLA20 §3.1 (`U(G)` is `*`-regular);
* `posDef` is JZLA20 §3.1 (`Matₙ(U(G))` is `*`-regular for all `n`);
* `rk`/`rk_faithful` are JZLA20 §3.2;
* `sub.linnell` is JL, proof of Theorem `vanishing` (Linnell independence). -/
structure StarRegularEnvelope (G : Type u) [Group G] where
  /-- the algebra `U(G)` of affiliated operators -/
  U : Type u
  [ringU : Ring U]
  [starU : StarRing U]
  [algebraU : Algebra ℂ U]
  /-- the inclusion `ℂ[G] → U(G)` -/
  ι : MonoidAlgebra ℂ G →+* U
  ι_injective : Function.Injective ι
  ι_star : ∀ x : MonoidAlgebra ℂ G, ι (star x) = star (ι x)
  ι_algebraMap : ∀ c : ℂ, ι (algebraMap ℂ (MonoidAlgebra ℂ G) c) = algebraMap ℂ U c
  starRegular : IsStarRegularRing U
  posDef : IsPositiveDefinite U
  /-- the extended rank function `rk_G` -/
  rk : SylvesterRankFunction U
  rk_faithful : rk.Faithful
  /-- the subgroups `U(H) ⊆ U(G)` with Linnell independence -/
  sub : ∀ H : Subgroup G, EnvelopeInclusion G U ι H

attribute [instance] StarRegularEnvelope.ringU StarRegularEnvelope.starU StarRegularEnvelope.algebraU

namespace StarRegularEnvelope

variable [Group G] (E : StarRegularEnvelope G)

/-- The rank function of `U(G)` pulled back to `ℂ[G]` along `ι`. -/
noncomputable def rankCG : SylvesterRankFunction (MonoidAlgebra ℂ G) := E.rk.map E.ι

@[simp]
theorem rankCG_apply {n m : ℕ} (A : Matrix (Fin n) (Fin m) (MonoidAlgebra ℂ G)) :
    E.rankCG.rank A = E.rk.rank (A.map E.ι) := rfl

/-- The pull-back of `rk_G` to `ℂ[G]` is faithful. -/
theorem rankCG_faithful : E.rankCG.Faithful := by
  intro x hx
  have h : E.rk.rank (!![E.ι x] : Matrix (Fin 1) (Fin 1) E.U) = 0 := by
    have : (!![x] : Matrix (Fin 1) (Fin 1) (MonoidAlgebra ℂ G)).map E.ι = !![E.ι x] := by
      ext i j; simp [Matrix.map_apply]
    rw [rankCG_apply, this] at hx
    exact hx
  exact E.ι_injective (by rw [map_zero]; exact E.rk_faithful (E.ι x) h)

/-- `ℂ[G]` embeds into `U(G)` and `rk_G` is faithful on it. -/
theorem rank_injective {x : MonoidAlgebra ℂ G}
    (h : E.rk.rank (!![E.ι x] : Matrix (Fin 1) (Fin 1) E.U) = 0) : x = 0 :=
  E.ι_injective (by rw [map_zero]; exact E.rk_faithful (E.ι x) h)

/-- The image of a group element in `U(G)` is a unit, because `g` is invertible in `ℂ[G]`. -/
theorem isUnit_single (g : G) : IsUnit (E.ι (MonoidAlgebra.single g 1)) := by
  refine ⟨⟨E.ι (MonoidAlgebra.single g 1), E.ι (MonoidAlgebra.single g⁻¹ 1), ?_, ?_⟩, rfl⟩
  · rw [← map_mul, MonoidAlgebra.single_mul_single, mul_inv_cancel]
    rw [mul_one, show MonoidAlgebra.single (1 : G) (1 : ℂ) = 1 from MonoidAlgebra.one_def,
      map_one]
  · rw [← map_mul, MonoidAlgebra.single_mul_single, inv_mul_cancel]
    rw [mul_one, show MonoidAlgebra.single (1 : G) (1 : ℂ) = 1 from MonoidAlgebra.one_def,
      map_one]

/-- The image of the identity group element is `1`. -/
@[simp]
theorem iota_one : E.ι (MonoidAlgebra.single (1 : G) 1) = 1 := by
  rw [← MonoidAlgebra.one_def, map_one]

/-- `ι` is injective on the group basis. -/
theorem iota_single_ne_zero (g : G) : E.ι (MonoidAlgebra.single g 1) ≠ 0 := fun h =>
  (MonoidAlgebra.single_ne_zero (M := G) (R := ℂ) (m := g)).mpr one_ne_zero
    (E.ι_injective (by rw [h, map_zero]))

end StarRegularEnvelope

end Work.ORVonNeumann
