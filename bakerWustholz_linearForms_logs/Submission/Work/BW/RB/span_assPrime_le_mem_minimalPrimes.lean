import Mathlib
import Submission.Work.BW.RB.A4
import Submission.Work.BW.RB.unmixed_of_height_eq_card

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

/-! Guidance from the project lead (the requester):

LEAD 09-29 20:00: Srel_spanned_le route (design agent, DESIGN.md below). The hunmixed route through srel_cut_unmixed is ABANDONED: its hypothesis fails along the generic chain (embedded primes over non-I-containing minimal primes). New route: at each chain step cut ONLY the height-(r+1) minimal primes, which is locally a complete intersection, so there are no embedded primes there (via the proved unmixed_of_height_eq_card at a maximal ideal chosen by the Jacobson property). The five lemmas under BW/RB/ are dispatched top-level: span_assPrime_le_mem_minimalPrimes (1), primLen_sup_span_le_sum_loc (2), chain_height_of_avoid (3), srel_chain_step (4; uses 1,2), srel_le_of_generic_chain (5; uses 3,4). Lemma 2 also needs locLenAt_sup_inf_le (in flight under H36-L1661). Import sibling stubs as needed. Srel_spanned_le then follows in a few lines from exists_generic_chain + lemma 5 (Srel_bot for the ⊥ span).

# `Work.BW.Srel_spanned_le`: design (2026-09-29)

## Ruling

`Srel_spanned_le` **as stated is TRUE**. The route is a variant of (a): the generic chain plus a
cut that is *graded by height*.

The planned hypothesis `hunmixed` of `RB.srel_cut_unmixed` at the chain ideals `J_r` **cannot be
discharged in general**. That hypothesis asks, at every admissible maximal ideal, that every
associated prime of `R/J_r` be minimal. It is false along the chain, so do not wait on that route.

What makes it false is a minimal prime of `J_r` that contains `I` and has height `< r`. There is no
Cohen–Macaulay control at such a prime, and embedded primes of `J_r` can sit on top of it.

Example (local picture at the admissible point `((1:1),(1:1))`, with `N = 1`):
- `l₀ = X₀₁ - X₀₀` and `l₁ = X₁₁ - X₁₀`.
- `I` is spanned by the degree-`D` part of `l₀·(l₀,l₁)²`, with `D = (3,2)`.
- For generic `g₁, g₂ ∈ I_D`, locally `J₂ = l₀·(q₁,q₂)`, where `(q₁,q₂)` is `(l₀,l₁)`-primary.
- So `(l₀,l₁) ∈ Ass(J₂)` is embedded over the minimal prime `(l₀)`, and `J₂ ≠ I` (`dim I_D > 2`).

Mathlib has **no** Cohen–Macaulay or unmixedness theory. The only unmixedness available is the
project's own `RB.unmixed_of_height_eq_card` (via `unmixed_regSeq`). It covers ideals of height =
number of generators in `ℂ[σ]_𝔪`, with `𝔪` maximal. That is enough, because unmixedness is only
needed *locally*, at primes where it does hold.

## Key observation

Cut only the primes of height `r+1`. Let `q` be a minimal prime of `J_{r+1} = J_r + (g)` of height
`r+1`, and let `p ≤ q` be a minimal prime of `J_r`.

- If `g ∈ p`, then `J_{r+1} ≤ p ≤ q`, so `p = q`. That contradicts `ht p ≤ r` (Krull).
- So `g ∉ p`. Since `g ∈ I`, this gives `I ≰ p`, and genericity gives `ht p = r`.

So below `q`, `J_r` is `r` elements generating an ideal all of whose minimal primes have height `r`.
Such an ideal is a complete intersection, hence unmixed there (Macaulay). The existing
`unmixed_of_height_eq_card` applies after moving to a maximal ideal `𝔪 ⊇ q` that avoids the
lower-height minimal primes. Hilbert's Nullstellensatz provides that `𝔪`: `MR N` is a Jacobson ring.

Components of `I` of height `h` are then collected at step `h`, when they first appear as minimal
primes of `J_h` of height `h` containing `I`. Components of `J_r` that contain `I` are **never cut
again**, so their bad local structure never matters.

## The argument (telescoping)

Setup:
- `W = span_ℂ s ≤ homPiece N D` and `I = span s ≠ ⊥`.
- `exists_generic_chain` gives `g 0, …, g (k-1) ∈ W` with `span = I`.
- Each `g j` avoids the minimal primes of `J_j = (g i : i < j)` that do not contain `I`.

For `s ≤ k` put:
- `A s = ∑_{p ∈ Min J_s, adm, I ≰ p} ℓ_p(J_s)·H(p)`
- `B s = ∑_{q ∈ Min J_s, adm, ht q = s, I ≤ q} ℓ_q(J_s)·H(q)`

1. **Heights** (`chain_height_of_avoid`). Every `p ∈ Min J_s` with `I ≰ p` has `ht p = s`, by
   induction plus Krull.
2. **Step** (`srel_chain_step`, for `s < k`). The admissible height-`(s+1)` minimal primes of
   `J_{s+1}` weigh at most `A s`. They are exactly the index sets of `A(s+1)` and `B(s+1)` (by 1),
   so `A(s+1) + B(s+1) ≤ A s`. Proof:
   - (a) The key observation above.
   - (b) Local unmixedness at `q` (`span_assPrime_le_mem_minimalPrimes`).
   - (c) The local multiplicity inequality (`primLen_sup_span_le_sum_loc`):
     `ℓ_q(J+(g)) ≤ ∑_{p ≤ q} ℓ_p(J)·ℓ_q(p+(g))`.
   - (d) Swap the sums. For each `p`, `∑_{q ≥ p} ℓ_q(p+(g)) H(q) ≤ Srel(p+(g)) ≤ Srel p = H(p)`,
     by `finset_sum_le_srel`, `srel_cut_prime` and `srel_self_of_isPrime`, all already proved.
3. **Base.** `A 0 = rayDeg ⊥`, since `Min ⊥ = {⊥}` and `I ≰ ⊥`, using `OnGPrime_bot` and
   `primLen_bot`.
4. **Telescoping.** `A k + ∑_{s=1}^k B s ≤ A 0`.
5. **Collection.** `Srel I ≤ ∑_{s=1}^k B s`. Take an admissible `q ∈ Min I` of height `h`, with
   `1 ≤ h ≤ k`.
   - `q ∈ Min J_h`: `q` contains some `p ∈ Min J_h`. If `I ≤ p`, then `p = q` by minimality over
     `I`. Otherwise `ht p = h = ht q`, so `p = q`.
   - `ℓ_q(I) ≤ ℓ_q(J_h)`, by `primLen_mono` and `primLen_ne_top`.

If `span s = ⊥`, `Srel_bot` closes the goal directly.

## Lemmas (namespace `Work.BW.RB`; each checked to elaborate against `RB.A4` on the box)

| file | role | depends on |
|---|---|---|
| `span_assPrime_le_mem_minimalPrimes.stmt` | local CI unmixedness at a prime `q` (Jacobson → maximal `𝔪` → `unmixed_of_height_eq_card` → transport back) | `unmixed_of_height_eq_card`, Mathlib `isJacobsonRing_iff_prime_eq`, `IsLocalization.minimalPrimes_comap`, `IsLocalization.height_map_of_disjoint` |
| `primLen_sup_span_le_sum_loc.stmt` | `primLen_sup_span_le_sum` with `hunmixed` localized to `q` (same documented proof; the old node follows from it) | `locLenAt_sup_inf_le` (still sorry, delegated), `locLenAt_primary_cut_le`, Lasker |
| `chain_height_of_avoid.stmt` | heights `= s` along an avoiding chain | Krull `Ideal.height_le_card_of_mem_minimalPrimes_span_finset`, `Ideal.height_add_one_le_of_lt_of_isPrime` |
| `srel_chain_step.stmt` | `A(s+1)+B(s+1) ≤ A s` in height-graded form | the two above + `srel_cut_prime`, `finset_sum_le_srel`, `mem_minimalPrimes_sup_span_of_le` |
| `srel_le_of_generic_chain.stmt` | telescoping + collection | all of the above, `primLen_mono`, `primLen_ne_top`, `Srel_bot` pieces |

Then `Srel_spanned_le` needs these steps:
1. `by_cases h : Ideal.span s = ⊥`; in that case `rw [h]; exact (Srel_bot D).le`.
2. Otherwise `exists_generic_chain D (Submodule.span ℂ s) (Submodule.span_le.2 hs) (Ideal.span s) _`.
   The side goal is `Ideal.span s = Ideal.span ↑(Submodule.span ℂ s)`, proved by `le_antisymm` with
   `Ideal.span_mono Submodule.subset_span` and `Ideal.span_le` plus
   `Submodule.span_le.2 Ideal.subset_span` in `restrictScalars`.
3. Rewrite `↑((univ.filter (·.1 < j.1)).image g) = g '' {i | i.1 < j.1}` with `Finset.coe_image`,
   `Finset.coe_filter` and `simp`.
4. Apply `srel_le_of_generic_chain`.

Parallelism: nodes 1, 2 and 3 are independent. Node 4 needs 1 and 2, and node 5 needs 3 and 4.
`RB.srel_cut_unmixed` becomes unnecessary for `Srel_spanned_le`; cancel it unless something else
consumes it. Its sorry `primLen_sup_span_le_sum` is subsumed by node 2.

## Risks

- **Node 1, transport.** Moving associated and minimal primes between `R` and `R_𝔪`, and getting
  the height of `J R_𝔪` equal to `r` when `J.height < r` globally. The public
  `height_map_localization_eq_of_mem_minimalPrimes` needs `ht r₀ = ht J`, which fails here. Use the
  private helpers' arguments directly: `≤` via a minimal prime `r₀ ≤ 𝔪` of height `r`, and `≥` via
  `IsLocalization.height_under`. This is bookkeeping, not mathematics.
- **Node 2** inherits the one real remaining algebra sorry, `locLenAt_sup_inf_le`. The mathematics
  is sound (dimension-1 associativity formula, with equality in fact). Its proof must run the
  primary-decomposition induction with `ℕ∞` lengths; finiteness of each partial intersection's cut
  at `q` follows from `primLen_ne_top`, because `q` is minimal over each `Q_i' + (P)`.
- **Node 4** is finsum-swapping bookkeeping over finite index sets. Use `finsum_cond_eq_sum` with
  `Ideal.finite_minimalPrimes_of_isNoetherianRing`, as `srel_cut_unmixed` already does.
- There is no dependence on Cohen–Macaulay theory beyond the existing `unmixed_regSeq` at maximal
  ideals.
-/

namespace Work.BW.RB

open Work.BW

private lemma rb_span_toFinset_eq {A : Type*} [Semiring A] [DecidableEq A] (l : List A) :
    Ideal.span ((l.toFinset : Finset A) : Set A) = Ideal.span {x | x ∈ l} := by
  congr 1
  ext x
  simp

/-- The colon of a quotient module, in ring terms. -/
private lemma rb_quot_colon_singleton_mk {R : Type*} [CommRing R] (J : Ideal R) (z : R) :
    (⊥ : Submodule R (R ⧸ J)).colon {Submodule.Quotient.mk z}
      = (J : Submodule R R).colon {z} := by
  ext rr
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
  rw [← Submodule.Quotient.mk_smul (p := (J : Submodule R R)) rr z,
      Submodule.Quotient.mk_eq_zero]

/-- Localization commutes with the colon by a single element, for a prime disjoint from the
localizing submonoid. -/
private lemma rb_map_colon_eq_colon_map {N : ℕ} (J : Ideal (MR N)) (q : Ideal (MR N))
    (hq : q.IsPrime) (p : Ideal (MR N)) (hp : p.IsPrime) (hpq : p ≤ q) (z : MR N)
    (hz : p = (J : Submodule (MR N) (MR N)).colon {z}) :
    p.map (algebraMap (MR N) (Localization.AtPrime q))
      = (J.map (algebraMap (MR N) (Localization.AtPrime q))).colon
          {algebraMap (MR N) (Localization.AtPrime q) z} := by
  classical
  haveI := hq
  set A := Localization.AtPrime q with hA
  set g' := algebraMap (MR N) A with hg'
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul]
    exact Ideal.mem_map_of_mem _ (by rw [hz, Submodule.mem_colon_singleton] at hx; exact hx)
  · intro rr hrr
    obtain ⟨a, s, hs⟩ := IsLocalization.exists_mk'_eq q.primeCompl rr
    rw [← hs] at hrr ⊢
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hrr
    have hkey : IsLocalization.mk' A a s * g' z = IsLocalization.mk' A (a * z) s := by
      rw [hg', ← IsLocalization.mk'_one (M := q.primeCompl) (S := A) (x := z),
        ← IsLocalization.mk'_mul]
      congr 1
      exact Subtype.ext (mul_one s.1)
    rw [hkey] at hrr
    obtain ⟨t, ht, htaz⟩ :=
      (IsLocalization.mk'_mem_map_algebraMap_iff q.primeCompl A J (a * z) s).mp hrr
    have hta : t * a ∈ p := by
      rw [hz, Submodule.mem_colon_singleton]
      show (t * a) • z ∈ J
      rw [smul_eq_mul, mul_assoc]
      exact htaz
    have ht_notp : t ∉ p := fun h => ht (hpq h)
    have ha : a ∈ p := (hp.mem_or_mem hta).resolve_left ht_notp
    exact (IsLocalization.mk'_mem_map_algebraMap_iff q.primeCompl A p a s).mpr
      ⟨1, q.primeCompl.one_mem, by simpa using ha⟩

/-- Local unmixedness at a single maximal ideal: if every minimal prime of `J` contained in `𝔪`
has height `≥ r` and `J` is generated by `r` elements, then every associated prime of `R ⧸ J`
contained in `𝔪` is minimal over `J`. -/
private lemma rb_step {N r : ℕ} (g : Fin r → MR N) (q : Ideal (MR N))
    (𝔪 : Ideal (MR N)) [h𝔪max : 𝔪.IsMaximal] (h𝔪q : q ≤ 𝔪)
    (hgood : ∀ P ∈ (Ideal.span (Set.range g)).minimalPrimes, P ≤ 𝔪 → (r : ℕ∞) ≤ P.height) :
    ∀ p ∈ associatedPrimes (MR N) (MR N ⧸ Ideal.span (Set.range g)), p ≤ q →
      p ∈ (Ideal.span (Set.range g)).minimalPrimes := by
  classical
  intro p hp_ass hpq
  have hprime_𝔪 : 𝔪.IsPrime := h𝔪max.isPrime
  set J : Ideal (MR N) := Ideal.span (Set.range g) with hJ
  have h' : (⊥ : Submodule (MR N) (MR N ⧸ J)).IsAssociatedPrime p := hp_ass
  rw [Submodule.isAssociatedPrime_iff] at h'
  obtain ⟨hp_prime, x, hx⟩ := h'
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (p := (J : Submodule (MR N) (MR N))) x
  rw [rb_quot_colon_singleton_mk] at hx
  have hJp : J ≤ p := by
    intro y hy
    rw [hx, Submodule.mem_colon_singleton]
    exact J.mul_mem_right z hy
  have hpq𝔪 : p ≤ 𝔪 := hpq.trans h𝔪q
  have hdisj : Disjoint (𝔪.primeCompl : Set (MR N)) (p : Set (MR N)) := by
    rw [Set.disjoint_left]
    intro y hy hyp
    exact hy (hpq𝔪 hyp)
  have hprimeA : (p.map (algebraMap (MR N) (Localization.AtPrime 𝔪))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint 𝔪.primeCompl (Localization.AtPrime 𝔪) p hp_prime hdisj
  set l : List (Localization.AtPrime 𝔪) :=
    (List.ofFn g).map (algebraMap (MR N) (Localization.AtPrime 𝔪)) with hl
  have hspan : Ideal.span {x : Localization.AtPrime 𝔪 | x ∈ l}
      = J.map (algebraMap (MR N) (Localization.AtPrime 𝔪)) := by
    have hset : {x : Localization.AtPrime 𝔪 | x ∈ l} =
        algebraMap (MR N) (Localization.AtPrime 𝔪) '' (Set.range g) := by
      rw [hl]
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_range, List.mem_map, List.mem_ofFn]
    rw [hset, ← Ideal.map_span, ← hJ]
  have hmem : ∀ x ∈ l, x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪) := by
    intro x hx
    rw [hl] at hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔪 (Localization.AtPrime 𝔪)]
    have hgj : g j ∈ J := by rw [hJ]; exact Ideal.subset_span (Set.mem_range_self j)
    exact Ideal.mem_map_of_mem _ (hJp.trans hpq𝔪 hgj)
  have hne_top : J.map (algebraMap (MR N) (Localization.AtPrime 𝔪)) ≠ ⊤ :=
    ne_top_of_le_ne_top hprimeA.ne_top (Ideal.map_mono hJp)
  have hupper : (J.map (algebraMap (MR N) (Localization.AtPrime 𝔪))).height ≤ (r : ℕ∞) := by
    have h1 : Ideal.span ((l.toFinset : Finset (Localization.AtPrime 𝔪)) :
        Set (Localization.AtPrime 𝔪)) = J.map (algebraMap (MR N) (Localization.AtPrime 𝔪)) := by
      rw [rb_span_toFinset_eq, hspan]
    rw [← h1]
    calc (Ideal.span ((l.toFinset : Finset (Localization.AtPrime 𝔪)) :
            Set (Localization.AtPrime 𝔪))).height
        ≤ ((l.toFinset.card : ℕ) : ℕ∞) :=
          Ideal.height_span_le_card_of_span_ne_top (by rw [h1]; exact hne_top)
      _ ≤ (l.length : ℕ∞) := by exact_mod_cast List.toFinset_card_le l
      _ = (r : ℕ∞) := by rw [hl, List.length_map, List.length_ofFn]
  have hlower : (r : ℕ∞) ≤ (J.map (algebraMap (MR N) (Localization.AtPrime 𝔪))).height := by
    rw [Ideal.height_eq_inf_minimalPrimes]
    refine le_iInf fun P => le_iInf fun hP => ?_
    have hPprime : P.IsPrime := hP.isPrime
    have hPmin : Ideal.under (MR N) P ∈ J.minimalPrimes := by
      have hmap := IsLocalization.minimalPrimes_map 𝔪.primeCompl (Localization.AtPrime 𝔪) J
      rw [hmap] at hP
      exact hP
    have hPle𝔪 : Ideal.under (MR N) P ≤ 𝔪 := by
      have h1 : P ≤ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪) :=
        IsLocalRing.le_maximalIdeal hPprime.ne_top
      calc Ideal.under (MR N) P ≤
            (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)).under (MR N) :=
            Ideal.comap_mono h1
        _ = 𝔪 := IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime 𝔪) 𝔪
    have h2 := hgood (Ideal.under (MR N) P) hPmin hPle𝔪
    rwa [IsLocalization.height_under 𝔪.primeCompl P] at h2
  have hhtA : (J.map (algebraMap (MR N) (Localization.AtPrime 𝔪))).height = (r : ℕ∞) :=
    le_antisymm hupper hlower
  have hht_eq : (Ideal.span {x : Localization.AtPrime 𝔪 | x ∈ l}).height = (l.length : ℕ∞) := by
    rw [hspan, hhtA, hl, List.length_map, List.length_ofFn]
  have hAss : p.map (algebraMap (MR N) (Localization.AtPrime 𝔪)) ∈
      associatedPrimes (Localization.AtPrime 𝔪)
        (Localization.AtPrime 𝔪 ⧸ Ideal.span {x : Localization.AtPrime 𝔪 | x ∈ l}) := by
    have hcolon : p.map (algebraMap (MR N) (Localization.AtPrime 𝔪))
        = (J.map (algebraMap (MR N) (Localization.AtPrime 𝔪))).colon
            {algebraMap (MR N) (Localization.AtPrime 𝔪) z} :=
      rb_map_colon_eq_colon_map J 𝔪 hprime_𝔪 p hp_prime hpq𝔪 z hx
    change (⊥ : Submodule (Localization.AtPrime 𝔪)
      (Localization.AtPrime 𝔪 ⧸ Ideal.span {x : Localization.AtPrime 𝔪 | x ∈ l})).IsAssociatedPrime
      (p.map (algebraMap (MR N) (Localization.AtPrime 𝔪)))
    rw [Submodule.isAssociatedPrime_iff]
    refine ⟨hprimeA, ⟨Submodule.Quotient.mk (algebraMap (MR N) (Localization.AtPrime 𝔪) z), ?_⟩⟩
    rw [rb_quot_colon_singleton_mk, hspan]
    exact hcolon
  have hminA : p.map (algebraMap (MR N) (Localization.AtPrime 𝔪))
      ∈ (J.map (algebraMap (MR N) (Localization.AtPrime 𝔪))).minimalPrimes := by
    have h2 := unmixed_of_height_eq_card 𝔪 l hmem hht_eq
    have h3 := h2 (p.map (algebraMap (MR N) (Localization.AtPrime 𝔪))) hAss
    rwa [hspan] at h3
  have hunder : Ideal.under (MR N) (p.map (algebraMap (MR N) (Localization.AtPrime 𝔪)))
      ∈ J.minimalPrimes := by
    have hmap := IsLocalization.minimalPrimes_map 𝔪.primeCompl (Localization.AtPrime 𝔪) J
    rw [hmap] at hminA
    exact hminA
  rw [IsLocalization.under_map_of_isPrime_disjoint 𝔪.primeCompl (Localization.AtPrime 𝔪) hp_prime hdisj]
    at hunder
  exact hunder

/-- Local unmixedness of an ideal generated by `r` elements (Macaulay).  Let `J = (g 0, …, g (r-1))`
and let `q` be a prime such that every minimal prime of `J` contained in `q` has height exactly
`r`.  Then every associated prime of `R/J` contained in `q` is a minimal prime of `J`.

No global hypothesis on `J`: minimal primes of `J` of height `< r` are allowed, as long as they
are not contained in `q`.

Route.  Let `p ∈ Ass(R/J)` with `p ≤ q`; then `J ≤ p`.
1. The bad set `B = {p' ∈ Min J | p'.height ≠ r}` is finite, and no `p' ∈ B` lies in `q` (by
   `hht`).  Pick `f p' ∈ p' \ q` and put `f = ∏_{p' ∈ B} f p'`; then `f ∉ q` because `q` is
   prime.
2. Jacobson: `MR N` is a Jacobson ring (`inferInstance`; `isJacobsonRing_iff_prime_eq` gives
   `q = q.jacobson = sInf {𝔪 | q ≤ 𝔪 ∧ 𝔪.IsMaximal}`).  So there is a maximal `𝔪 ≥ q` with
   `f ∉ 𝔪`.  Then no `p' ∈ B` lies in `𝔪`, so every minimal prime of `J` inside `𝔪` has height
   `r`.
3. Work in `A = Localization.AtPrime 𝔪` with `l = (List.ofFn g).map (algebraMap _ A)`, so that
   `Ideal.span {x | x ∈ l} = J.map (algebraMap _ A)`.  `hmem`: `g j ∈ J ≤ p ≤ q ≤ 𝔪`.
   `hht`: `≤ r` by Krull (`r` generators); `≥ r` because every prime of `A` over `J A` is
   `P' A` with `J ≤ P' ≤ 𝔪`, and `P'` contains a minimal prime of `J` inside `𝔪`, of height `r`.
   Heights are preserved by `IsLocalization.height_map_of_disjoint` / `IsLocalization.height_under`;
   compare the private helpers in `RB/height_map_localization_eq_of_mem_minimalPrimes.lean`.
   Then `unmixed_of_height_eq_card 𝔪 l hmem hht` gives that every associated prime of
   `A ⧸ J A` is minimal over `J A`.
4. Transport.  Write `p = J.colon {x}` with `x ∉ J` (definition of associated prime).  Then
   `p A = (J A).colon {x/1}`: for `⊇`, if `(a/s)·x ∈ J A` then `t a x ∈ J` for some `t ∉ 𝔪`, so
   `t a ∈ p` and hence `a ∈ p`, because `t ∉ p`.  Also `x/1 ∉ J A`: otherwise `t x ∈ J` with
   `t ∉ 𝔪`, so `t ∈ p ≤ 𝔪`.  Hence `p A ∈ Ass(A ⧸ J A)` and so `p A ∈ Min(J A)`.  Contracting,
   `p = (p A).comap` is minimal over `J`, because minimal primes correspond under localization
   for primes inside `𝔪`.  Alternatively use Mathlib's
   `Module.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule` together with
   `IsLocalization.minimalPrimes_comap`-type facts. -/
theorem span_assPrime_le_mem_minimalPrimes {N r : ℕ} (g : Fin r → MR N) (q : Ideal (MR N))
    (hq : q.IsPrime)
    (hht : ∀ p ∈ (Ideal.span (Set.range g)).minimalPrimes, p ≤ q → p.height = (r : ℕ∞)) :
    ∀ p ∈ associatedPrimes (MR N) (MR N ⧸ Ideal.span (Set.range g)), p ≤ q →
      p ∈ (Ideal.span (Set.range g)).minimalPrimes := by
  classical
  set J : Ideal (MR N) := Ideal.span (Set.range g) with hJ
  have hminJ : J.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N) J
  set B : Finset (Ideal (MR N)) :=
    (hminJ.toFinset).filter (fun P => P.height < (r : ℕ∞)) with hBdef
  have hB : ∀ P, P ∈ B ↔ P ∈ J.minimalPrimes ∧ P.height < (r : ℕ∞) := by
    intro P
    rw [hBdef, Finset.mem_filter, Set.Finite.mem_toFinset hminJ]
  have hex : ∀ P ∈ B, ∃ y, y ∈ P ∧ y ∉ q := by
    intro P hP
    obtain ⟨hPmin, hPlt⟩ := (hB P).mp hP
    by_contra hcon
    push Not at hcon
    have hPq : P ≤ q := hcon
    have hh := hht P hPmin hPq
    rw [hh] at hPlt
    exact absurd hPlt (lt_irrefl _)
  set f : Ideal (MR N) → MR N :=
    fun P => if h : P ∈ B then (hex P h).choose else 0 with hfdef
  have hf_mem : ∀ P ∈ B, f P ∈ P := by
    intro P hP
    have h1 : f P = (hex P hP).choose := by rw [hfdef]; exact dite_eq_left hP
    rw [h1]; exact (hex P hP).choose_spec.1
  have hf_notq : ∀ P ∈ B, f P ∉ q := by
    intro P hP
    have h1 : f P = (hex P hP).choose := by rw [hfdef]; exact dite_eq_left hP
    rw [h1]; exact (hex P hP).choose_spec.2
  set F : MR N := ∏ P ∈ B, f P with hFdef
  have hF_notq : F ∉ q := by
    haveI := hq
    rw [hFdef, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨P, hPB, hPq⟩
    exact hf_notq P hPB hPq
  have hqjac : q.jacobson = q :=
    isJacobsonRing_iff_prime_eq.mp (inferInstance : IsJacobsonRing (MR N)) q hq
  have hmem_inf : ¬ (F ∈ sInf {I : Ideal (MR N) | q ≤ I ∧ I.IsMaximal}) := by
    change F ∉ q.jacobson
    rw [hqjac]
    exact hF_notq
  rw [Ideal.mem_sInf] at hmem_inf
  push Not at hmem_inf
  obtain ⟨𝔪, h𝔪mem, hF𝔪⟩ := hmem_inf
  simp only [Set.mem_ofPred_eq] at h𝔪mem
  obtain ⟨h𝔪q, h𝔪max⟩ := h𝔪mem
  haveI : 𝔪.IsMaximal := h𝔪max
  have hgood : ∀ P ∈ J.minimalPrimes, P ≤ 𝔪 → (r : ℕ∞) ≤ P.height := by
    intro P hPmin hP𝔪
    by_contra hcon
    rw [not_le] at hcon
    have hPB : P ∈ B := (hB P).mpr ⟨hPmin, hcon⟩
    have hFm : F ∈ 𝔪 := by
      rw [hFdef]
      exact Ideal.prod_mem 𝔪 hPB (hP𝔪 (hf_mem P hPB))
    exact hF𝔪 hFm
  intro p hp_ass hpq
  exact rb_step g q 𝔪 h𝔪q hgood p hp_ass hpq

end Work.BW.RB
