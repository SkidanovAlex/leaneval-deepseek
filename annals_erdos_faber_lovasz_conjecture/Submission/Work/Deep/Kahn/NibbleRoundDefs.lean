import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.Defs
import Submission.Work.Deep.Kahn.RoundDefs

/-!
# The one-round interface of the (colour-degree) nibble proof of Kahn's theorem

This module fixes the *shape* of the one-round step that the iteration of the semi-random
method consumes, in the form in which it is proved in the literature:
Kang--Kelly--Kühn--Methuku--Osthus, *A special case of Vu's conjecture* (arXiv:2109.11438),
Lemma `lemma:nibble` and Proposition `prop:calculations`.

## The state of the iteration

A *state* is a pair `(𝓗, L)` where `𝓗 ⊆ 𝓗_orig` is the hypergraph of still uncoloured edges
and `L` is a list assignment for it, together with the two numerical invariants

* `Λ` — the **common size of all lists** (`|L e| = Λ` for every edge `e`; the lists are
  truncated to a common size so that this is an invariant), and
* `D` — a bound on the **colour degrees** `#{e ∋ x | γ ∈ L e} ≤ D`.

The iteration maintains `(1 + ε) D ≤ Λ`, improves the *ratio* `Λ / D` by a factor
`1 + Θ(p)` per round, and stops as soon as `Λ ≥ 8 C D`, where the finishing step
(`Work.Deep.Kahn.finishing_step`, Reed's list-colouring-constants lemma) applies.

## The one-round step

In one round every edge is independently *activated* with probability `p = 1/K` and given a
uniform random colour from its list.  An activated edge is *kept* if no activated edge
meeting it receives the same colour; the kept edges are coloured and removed, and the colours
of all *activated* edges meeting an uncoloured edge are removed from its list (the "wasteful"
procedure of Reed--Sudakov).

The two quantities analysed are, with `s := (1 - p/Λ) ^ (C D)` (the list retention) and
`u := (1 - p/Λ) ^ (D (C-1))` (the colour-degree retention through the *other* vertices):

* `newLambda Λ C D K = Λ * s` — the number of colours left in the list of an edge;
* `newDeg Λ C D K = D * ((1-p) u + p (1-s))` — an upper bound on the colour degree after the
  round (the two terms are the "unactivated survivor" and the "activated but blocked"
  contributions).

The colour-degree retention `u` has the exponent `D (C-1)` and not `C D`: for an uncoloured
edge `e ∋ x` and a colour `γ ∈ L e`, the `D-1` other `γ`-edges through `x` are already
accounted for by the conditioning, so only the `(C-1) D` `γ`-neighbours of `e` through its
*other* vertices can block `e` at `γ`.  Using the exponent `C D` here would make the
colour-degree bound *false* (the true count is larger, by a factor of order `1 + 1/C`, on the
(eventually certain) event that no `γ`-edge through `x` is activated).

`RoundStepStatement` below asserts the existence of a round outcome meeting both estimates,
up to an additive error `η Λ` resp. `η D`, for every instance in the regime
`(1+ε) D ≤ Λ ≤ 10 C D`, `D ≫ (C + K + 1/η)^9`, `log D ≤ K ≤ (log D)^2`, `16 C ≤ (1+ε) K`,
`η K ≤ 1`.  Its proof (the deep probabilistic input of the chapter) is
`Work.Deep.Kahn.nibbleStep`; it proceeds by

1. the **embedding** `EmbeddingStatement`: the instance is embedded into a *regularised* one
   with every edge of size exactly `C`, every list of size exactly `Λ` and every colour degree
   exactly `D` (`prop:embedding`), in such a way that a round outcome of the embedded instance
   restricts to one of the original instance;
2. the **regularised analysis** `RegularisedNibbleStatement`: in the regularised instance the
   retention probability of a colour is exactly `s` (each colour of an uncoloured edge is
   blocked by `C (D-1)` activated edges), the deviations are obtained from a two-level
   Chernoff argument (`Work.Deep.Kahn.chernoff_uniform_prod`), and the Lovász local lemma
   combines the bad events (one per edge and one per pair `(x,γ)`) into a single outcome.

The additive error is `η Λ` on the lists and `η D` on the colour degrees, with `η` a
parameter of the step (one takes `η ≈ 1/K ≈ 1/log D`).

## Why the *embedded* (regularised) form is necessary

The sharp retention factor `s = (1-p/Λ)^{C(D-1)}` uses that the `C (D-1)` colours blocking a
colour `γ` of an edge `e` come from *all* `C` vertices of `e`, and this needs every vertex `y`
of `e` to have colour degree exactly `D` at `γ`.  For an arbitrary instance the honest
retention is `(1-p/Λ)^{|e| (D_y(γ) - 1)}` with the *actual* degrees `D_y(γ) ≤ D`, and the
ratio `Λ/D` then improves only while `Λ/D > C - 1`; the embedding is what allows the iteration
to start from the ratio `1 + ε`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

/-- The **list retention** factor `(1 - p/Λ) ^ (C D)` of a colour of an uncoloured edge in
one round, where `p = 1/K`: a colour `γ` survives in the list of `e` (i.e. no *kept* edge
through one of the `C` vertices of `e` uses `γ`) with probability `(1 - p/Λ)^(CD)` — the
number of `γ`-neighbours of `e` that can use `γ` is `CD`. -/
def retention (Λ C D K : ℕ) : ℝ := (1 - (1 / (K : ℝ)) / (Λ : ℝ)) ^ (C * D)

/-- The **unactivated colour-degree retention** factor `(1 - p/Λ) ^ (D (C-1))`.

For the colour degree of an uncoloured edge `e ∋ x` at a colour `γ ∈ L e` one must exclude
the possibility that some *kept* edge through a vertex of `e` uses `γ`.  Conditioning on the
colour (and activation) data of the `D-1` other `γ`-edges through `x` (as one may, since they
are "already accounted for" — this is the `D(C-1)` of Kang--Kühn--Methuku--Osthus, Lemma
`lemma:nibble`), only the `(C-1) D` `γ`-neighbours of `e` through its *other* vertices can
still block `e` at `γ`; hence the factor `(1 - p/Λ)^(D (C-1))`, which is larger than
`retention`. -/
def retentionU (Λ C D K : ℕ) : ℝ := (1 - (1 / (K : ℝ)) / (Λ : ℝ)) ^ (D * (C - 1))

/-- The number of colours left in the list of an edge after one round. -/
def newLambda (Λ C D K : ℕ) : ℝ := (Λ : ℝ) * retention Λ C D K

/-- An upper bound on the colour degree after one round: the unactivated survivors
(`retentionU`, the leading term) and the activated-but-blocked edges. -/
def newDeg (Λ C D K : ℕ) : ℝ :=
  (D : ℝ) * ((1 - 1 / (K : ℝ)) * retentionU Λ C D K +
    (1 / (K : ℝ)) * (1 - retention Λ C D K))

/-- **The one-round nibble step** (the interface consumed by the iteration).

For every rank bound `C ≥ 2`, slack `ε > 0` and error parameter `η > 0` there is `Dmin > 0`
such that: for every linear hypergraph `𝓗` with edges of size at most `C`, list assignment
`L` all of whose lists have a common size `Λ`, colour degrees at most `D`, in the regime

* `(1 + ε) D ≤ Λ ≤ 10 C D`,  `D ≥ Dmin`,
* `log D ≤ K ≤ (log D)^2`, `16 C ≤ (1 + ε) K`, `η K ≤ 1`, `C + K + η⁻¹ ≤ D^{1/9}`,

and with the additional requirement that the threshold `Dmin` is *polynomial* in
`C + η⁻¹ + ε⁻¹` (so that `η log Dmin` can be made small by choosing `η` small: the iteration
needs the per-round ratio gain `≈ ε/((1+ε) K)` to dominate the additive error `≈ 2 η`, and
`K ≈ log D ≥ log Dmin`).

there are a subhypergraph `𝓗₀ ⊆ 𝓗`, a proper colouring `φ` of `𝓗₀` from the lists, and list
assignment `L'` for the uncoloured hypergraph `𝓗 ∖ 𝓗₀` such that

* (soundness) `L' e ⊆ L e` and no colour used by a kept edge meeting `e` lies in `L' e`;
* (lists) `|L' e| ≥ newLambda Λ C D K - η Λ`;
* (colour degrees) `#{e ∋ x | γ ∈ L' e} ≤ newDeg Λ C D K + η D`.

The soundness clause says that `L' e` avoids every colour *used* by a kept edge meeting `e`
(so `L' e ⊆ L e \ used(e)` where `used(e)` is the set of colours used at `e`), which is what
the next round needs; the colour-degree clause is the estimate of the number of uncoloured
`γ`-edges through `x` that still carry `γ`, i.e. of those edges at which `γ` was *not* used. -/
def RoundStepStatement : Prop :=
  ∀ (C : ℕ), 2 ≤ C → ∀ (ε η : ℝ), 0 < ε → 0 < η → ∃ Dmin : ℝ, 0 < Dmin ∧
    Dmin ≤ ((C : ℝ) + η⁻¹ + ε⁻¹ + 1) ^ (1000 : ℕ) + 10 ^ (1000 : ℕ) ∧
    ∀ (n c : ℕ) (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
      (L : 𝓗 → Finset (Fin c)) (D Λ K : ℕ),
      1 ≤ D → 1 ≤ Λ → 2 ≤ K → η * (K : ℝ) ≤ 1 →
      (16 : ℝ) * (C : ℝ) ≤ (1 + ε) * (K : ℝ) →
      𝓗.IsLinear →
      (∀ e : 𝓗, edgeSize (e : Set (Fin n)) ≤ C) →
      (∀ e : 𝓗, (L e).card = Λ) →
      (∀ x : Fin n, ∀ γ : Fin c,
        Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} ≤ D) →
      (1 + ε) * (D : ℝ) ≤ (Λ : ℝ) → (Λ : ℝ) ≤ 10 * (C : ℝ) * (D : ℝ) →
      Dmin ≤ (D : ℝ) →
      Real.log (D : ℝ) ≤ (K : ℝ) → (K : ℝ) ≤ (Real.log (D : ℝ)) ^ 2 →
      ((C : ℝ) + (K : ℝ) + η⁻¹) ≤ (D : ℝ) ^ ((1 : ℝ) / 9) →
      ∃ (𝓗₀ : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) (hsub : 𝓗₀ ⊆ 𝓗)
        (φ : 𝓗₀.Coloring (Fin c))
        (L' : ((𝓗 \ 𝓗₀ : Set (Set (Fin n))) : Type) → Finset (Fin c)),
        (∀ e : 𝓗₀, φ.labels e ∈ L ⟨(e : Set (Fin n)), hsub e.2⟩) ∧
        (∀ e : ((𝓗 \ 𝓗₀ : Set (Set (Fin n))) : Type),
            L' e ⊆ L ⟨(e : Set (Fin n)), e.2.1⟩) ∧
        (∀ e : ((𝓗 \ 𝓗₀ : Set (Set (Fin n))) : Type),
            newLambda Λ C D K - η * (Λ : ℝ) ≤ ((L' e).card : ℝ)) ∧
        (∀ e : ((𝓗 \ 𝓗₀ : Set (Set (Fin n))) : Type), ∀ f : 𝓗₀,
            (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty → φ.labels f ∉ L' e)) ∧
        (∀ x : Fin n, ∀ γ : Fin c,
            ((Nat.card {e : ((𝓗 \ 𝓗₀ : Set (Set (Fin n))) : Type) //
                x ∈ (e : Set (Fin n)) ∧ γ ∈ L' e} : ℕ) : ℝ) ≤ newDeg Λ C D K + η * (D : ℝ))

/-- **The regularised one-round nibble step** (the deep probabilistic input, without the
embedding).

Same conclusion as `RoundStepStatement`, but for a *regularised* instance: every edge has
exactly `C` vertices, every list has exactly `Λ` colours, and every colour degree that occurs
at all is exactly `D` (i.e. `#{e ∋ x | γ ∈ L e} = D` whenever `γ` belongs to the list of some
edge through `x`).  In that situation the retention factor of a colour of an edge is exactly
`(1 - p/Λ) ^ (C (D-1))`. -/
def RegularisedNibbleStatement : Prop :=
  ∀ (C : ℕ), 2 ≤ C → ∀ (ε η : ℝ), 0 < ε → 0 < η → ∃ Dmin : ℝ, 0 < Dmin ∧
    Dmin ≤ ((C : ℝ) + η⁻¹ + ε⁻¹ + 1) ^ (1000 : ℕ) + 10 ^ (1000 : ℕ) ∧
    ∀ (n c : ℕ) (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
      (L : 𝓗 → Finset (Fin c)) (D Λ K : ℕ),
      1 ≤ D → 1 ≤ Λ → 2 ≤ K → η * (K : ℝ) ≤ 1 →
      (16 : ℝ) * (C : ℝ) ≤ (1 + ε) * (K : ℝ) →
      𝓗.IsLinear →
      (∀ e : 𝓗, edgeSize (e : Set (Fin n)) = C) →
      (∀ e : 𝓗, (L e).card = Λ) →
      (∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
        Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D) →
      (1 + ε) * (D : ℝ) ≤ (Λ : ℝ) → (Λ : ℝ) ≤ 10 * (C : ℝ) * (D : ℝ) →
      Dmin ≤ (D : ℝ) →
      Real.log (D : ℝ) ≤ (K : ℝ) → (K : ℝ) ≤ (Real.log (D : ℝ)) ^ 2 →
      ((C : ℝ) + (K : ℝ) + η⁻¹) ≤ (D : ℝ) ^ ((1 : ℝ) / 9) →
      ∃ (𝓗₀ : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) (hsub : 𝓗₀ ⊆ 𝓗)
        (φ : 𝓗₀.Coloring (Fin c))
        (L' : ((𝓗 \ 𝓗₀ : Set (Set (Fin n))) : Type) → Finset (Fin c)),
        (∀ e : 𝓗₀, φ.labels e ∈ L ⟨(e : Set (Fin n)), hsub e.2⟩) ∧
        (∀ e : ((𝓗 \ 𝓗₀ : Set (Set (Fin n))) : Type),
            L' e ⊆ L ⟨(e : Set (Fin n)), e.2.1⟩) ∧
        (∀ e : ((𝓗 \ 𝓗₀ : Set (Set (Fin n))) : Type),
            newLambda Λ C D K - η * (Λ : ℝ) ≤ ((L' e).card : ℝ)) ∧
        (∀ e : ((𝓗 \ 𝓗₀ : Set (Set (Fin n))) : Type), ∀ f : 𝓗₀,
            (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty → φ.labels f ∉ L' e)) ∧
        (∀ x : Fin n, ∀ γ : Fin c,
            ((Nat.card {e : ((𝓗 \ 𝓗₀ : Set (Set (Fin n))) : Type) //
                x ∈ (e : Set (Fin n)) ∧ γ ∈ L' e} : ℕ) : ℝ) ≤ newDeg Λ C D K + η * (D : ℝ))

/-- **The embedding (regularisation) input** (`prop:embedding`).

Every linear hypergraph `𝓗` whose edges have size at most `C`, whose lists have a common size
`Λ` and whose colour degrees are at most `D` embeds into a linear hypergraph `𝓗'` in which

* every edge has exactly `C` vertices,
* every list has exactly `Λ` colours,
* every colour degree that occurs is exactly `D`,

and moreover the embedding preserves lists (`L' (ι e) = (L e).image ρ`) and vertex-edge
incidence (`x ∈ e → emb x ∈ ι e`), reflects intersections, and does not decrease colour
degrees.  Consequently a colouring (or a round outcome) of `𝓗'` restricts along `(ι, ρ)` to
one of `𝓗`. -/
def EmbeddingStatement : Prop :=
  ∀ (n c : ℕ) (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) (L : 𝓗 → Finset (Fin c))
    (C D Λ : ℕ),
    2 ≤ C → 1 ≤ D → 1 ≤ Λ → 𝓗.IsLinear →
    (∀ e : 𝓗, edgeSize (e : Set (Fin n)) ≤ C) →
    (∀ e : 𝓗, (L e).card = Λ) →
    (∀ x : Fin n, ∀ γ : Fin c,
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} ≤ D) →
    ∃ (n' c' : ℕ) (𝓗' : ErdosFaberLovaszConjecture.Hypergraph (Fin n'))
      (L' : 𝓗' → Finset (Fin c')) (emb : Fin n → Fin n') (ι : 𝓗 → 𝓗') (ρ : Fin c → Fin c'),
      Function.Injective emb ∧ Function.Injective ι ∧ Function.Injective ρ ∧
      𝓗'.IsLinear ∧
      (∀ e : 𝓗', edgeSize (e : Set (Fin n')) = C) ∧
      (∀ e : 𝓗', (L' e).card = Λ) ∧
      (∀ e : 𝓗, L' (ι e) = (L e).image ρ) ∧
      (∀ (x : Fin n) (e : 𝓗), x ∈ (e : Set (Fin n)) → emb x ∈ (ι e : Set (Fin n'))) ∧
      (∀ e f : 𝓗, e ≠ f →
        (((e : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty →
          ((ι e : Set (Fin n')) ∩ (ι f : Set (Fin n'))).Nonempty)) ∧
      (∀ x' : Fin n', ∀ γ' : Fin c',
        (∃ e' : 𝓗', x' ∈ (e' : Set (Fin n')) ∧ γ' ∈ L' e') →
        Nat.card {e' : 𝓗' // x' ∈ (e' : Set (Fin n')) ∧ γ' ∈ L' e'} = D) ∧
      (∀ x : Fin n, ∀ γ : Fin c,
        Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} ≤
          Nat.card {e' : 𝓗' // emb x ∈ (e' : Set (Fin n')) ∧ ρ γ ∈ L' e'})

end

end Work.Deep.Kahn
