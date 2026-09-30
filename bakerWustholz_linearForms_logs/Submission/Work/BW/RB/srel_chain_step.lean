import Mathlib
import Submission.Work.BW.RB.A4
import Submission.Work.BW.RB.srel_cut_unmixed
import Submission.Work.BW.RB.span_assPrime_le_mem_minimalPrimes
import Submission.Work.BW.RB.primLen_sup_span_le_sum_loc
import Submission.Work.BW.RB.multiHom_span_of_homPiece
import Submission.Work.BW.RB.multiHom_minimalPrimes

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

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


set_option linter.style.haveILetI false

/-- The key observation of the height-graded cut: if `q` is a minimal prime of
`J + (G)` of height `r+1` and `p` is a minimal prime of `J = span (range g)` contained in `q`, then
`G ∉ p`, hence `I ≰ p` (since `G ∈ I`), and `p` has height exactly `r`.

Indeed, if `G ∈ p` then `J + (G) ≤ p ≤ q`, so `p = q` by the minimality of `q` over `J + (G)`; but
`p.height ≤ r` by Krull (the `r` generators `g j`) while `q.height = r+1`. -/
lemma chain_step_local {N r : ℕ} (I : Ideal (MR N)) (g : Fin r → MR N) (G : MR N)
    (hGI : G ∈ I)
    (hht : ∀ p ∈ (Ideal.span (Set.range g)).minimalPrimes, ¬ I ≤ p → p.height = (r : ℕ∞))
    {q : Ideal (MR N)} (hqK : q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes)
    (hqht : q.height = (r : ℕ∞) + 1) :
    ∀ p ∈ (Ideal.span (Set.range g)).minimalPrimes, p ≤ q →
      G ∉ p ∧ ¬ I ≤ p ∧ p.height = (r : ℕ∞) := by
  intro p hpJ hpq
  have hGp : G ∉ p := by
    intro hGmem
    have hKp : Ideal.span (Set.range g) ⊔ Ideal.span {G} ≤ p :=
      sup_le hpJ.1.2 (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hGmem))
    have hqp : q ≤ p := hqK.2 (y := p) ⟨hpJ.1.1, hKp⟩ hpq
    have hpq_eq : p = q := le_antisymm hpq hqp
    have hle : p.height ≤ (r : ℕ∞) := by
      have hspan : Ideal.span (↑(Finset.univ.image g) : Set (MR N)) = Ideal.span (Set.range g) := by
        congr 1
        ext x
        simp [Set.mem_range]
      have hp' : p ∈ (Ideal.span (↑(Finset.univ.image g) : Set (MR N))).minimalPrimes := by
        rw [hspan]; exact hpJ
      have hcard : (Finset.univ.image g).card ≤ r := by
        calc (Finset.univ.image g).card ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_image_le
          _ = r := by simp
      have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hp'
      calc p.height ≤ ((Finset.univ.image g).card : ℕ∞) := h1
        _ ≤ (r : ℕ∞) := by exact_mod_cast hcard
    rw [hpq_eq, hqht] at hle
    have h2 : ((r + 1 : ℕ) : ℕ∞) ≤ (r : ℕ∞) := by
      simpa [Nat.cast_add, Nat.cast_one] using hle
    exact absurd (ENat.coe_le_coe.mp h2) (Nat.not_succ_le_self r)
  have hnI : ¬ I ≤ p := fun hIp => hGp (hIp hGI)
  exact ⟨hGp, hnI, hht p hpJ hnI⟩

/-- One step of the generic chain (Philippon 3.3, height-graded).  Let `J = (g 0, …, g (r-1))` with
all `g j` of multidegree `D`, and let `G ∈ I` also have multidegree `D`.  Suppose every minimal
prime of `J` not containing `I` has height `r` and avoids `G`.  Then the admissible minimal primes
of `J + (G)` *of height `r+1`* weigh at most the admissible minimal primes of `J` not containing
`I`:

  `∑_{q ∈ Min(J+(G)), adm, ht q = r+1} ℓ_q(J+(G)) H(q) ≤ ∑_{p ∈ Min J, adm, I ≰ p} ℓ_p(J) H(p)`.

Route.  Fix `q` on the left.
(a) Every `p ∈ Min J` with `p ≤ q` satisfies `G ∉ p`, `I ≰ p` and `p.height = r`.  Indeed, if
    `G ∈ p` then `J + (G) ≤ p ≤ q`, so `p = q` by the minimality of `q`.  But `p.height ≤ r` by
    Krull (`Ideal.height_le_card_of_mem_minimalPrimes_span_finset`), while `q.height = r+1`.
    Hence `G ∉ p`, so `I ≰ p` since `G ∈ I`, and `p.height = r` by `hht`.
(b) By (a) and `span_assPrime_le_mem_minimalPrimes`, every associated prime of `R/J` below `q`
    is minimal.  So `primLen_sup_span_le_sum_loc` gives
    `ℓ_q(J+(G)) ≤ ∑_{p ∈ Min J, p ≤ q} ℓ_p(J) ℓ_q(p+(G))`.
(c) Multiply by `rayDeg q ≥ 0` (`rayDeg_nonneg`), sum over `q`, and swap the two finite sums.
    Every `p` that occurs has `I ≰ p` by (a), and is admissible by `OnGPrime_anti`.  Also
    `q ∈ Min(p + (G))` by `mem_minimalPrimes_sup_span_of_le` (`RB/srel_cut_unmixed.lean`).  So
    for fixed `p`, `finset_sum_le_srel` bounds the inner sum
    `∑_{q ≥ p} ℓ_q(p+(G)) H(q)` by `Srel (p ⊔ span {G})`.  That is `≤ Srel p = rayDeg p` by
    `srel_cut_prime` (with `MultiHom p` from `multiHom_minimalPrimes` and `multiHom_span`) and
    `srel_self_of_isPrime`.  Summing `ℓ_p(J)·rayDeg p` over these `p` gives the right-hand side.

This replaces `srel_cut_unmixed`, whose global `hunmixed` hypothesis is false along the chain.
Only primes of height `r+1` are cut, and below those `J` has no minimal prime containing `I`. -/
theorem srel_chain_step {N r : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (I : Ideal (MR N)) (g : Fin r → MR N) (hg : ∀ j, g j ∈ homPiece N D)
    (G : MR N) (hG : G ∈ homPiece N D) (hGI : G ∈ I)
    (hht : ∀ p ∈ (Ideal.span (Set.range g)).minimalPrimes, ¬ I ≤ p → p.height = (r : ℕ∞))
    (hav : ∀ p ∈ (Ideal.span (Set.range g)).minimalPrimes, ¬ I ≤ p → G ∉ p) :
    (∑ᶠ (q : Ideal (MR N)) (_ : q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes ∧
        OnGPrime N q ∧ q.height = (r : ℕ∞) + 1),
        ((primLen (Ideal.span (Set.range g) ⊔ Ideal.span {G}) q).toNat : ℚ) * rayDeg N D q) ≤
      ∑ᶠ (p : Ideal (MR N)) (_ : p ∈ (Ideal.span (Set.range g)).minimalPrimes ∧
        OnGPrime N p ∧ ¬ I ≤ p),
        ((primLen (Ideal.span (Set.range g)) p).toNat : ℚ) * rayDeg N D p := by
  classical
  obtain ⟨SK, hSK⟩ : ∃ S : Finset (Ideal (MR N)),
      ∀ q, q ∈ S ↔ q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes :=
    ⟨(Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N)
        (Ideal.span (Set.range g) ⊔ Ideal.span {G})).toFinset,
      fun q => Set.Finite.mem_toFinset
        (Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N)
          (Ideal.span (Set.range g) ⊔ Ideal.span {G}))⟩
  obtain ⟨SP, hSP⟩ : ∃ S : Finset (Ideal (MR N)),
      ∀ p, p ∈ S ↔ p ∈ (Ideal.span (Set.range g)).minimalPrimes :=
    ⟨(Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N)
        (Ideal.span (Set.range g))).toFinset,
      fun q => Set.Finite.mem_toFinset
        (Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N) (Ideal.span (Set.range g)))⟩
  have hL : (∑ᶠ (q : Ideal (MR N)) (_ : q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes ∧
        OnGPrime N q ∧ q.height = (r : ℕ∞) + 1),
        ((primLen (Ideal.span (Set.range g) ⊔ Ideal.span {G}) q).toNat : ℚ) * rayDeg N D q)
      = ∑ q ∈ SK, (if (q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes ∧
          OnGPrime N q ∧ q.height = (r : ℕ∞) + 1)
          then ((primLen (Ideal.span (Set.range g) ⊔ Ideal.span {G}) q).toNat : ℚ) * rayDeg N D q
          else 0) :=
    finsum_cond_eq_sum _ SK (fun a ha => (hSK a).mpr ha.1) _
  have hR : (∑ᶠ (p : Ideal (MR N)) (_ : p ∈ (Ideal.span (Set.range g)).minimalPrimes ∧
        OnGPrime N p ∧ ¬ I ≤ p),
        ((primLen (Ideal.span (Set.range g)) p).toNat : ℚ) * rayDeg N D p)
      = ∑ p ∈ SP, (if (p ∈ (Ideal.span (Set.range g)).minimalPrimes ∧
          OnGPrime N p ∧ ¬ I ≤ p)
          then ((primLen (Ideal.span (Set.range g)) p).toNat : ℚ) * rayDeg N D p
          else 0) :=
    finsum_cond_eq_sum _ SP (fun a ha => (hSP a).mpr ha.1) _
  rw [hL, hR]
  have hmulti : MultiHom N (Ideal.span (Set.range g)) :=
    multiHom_span_of_homPiece (Set.range g) (by rintro x ⟨j, rfl⟩; exact ⟨D, hg j⟩)
  have hlocal : ∀ q ∈ SK,
      (if q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes ∧ OnGPrime N q ∧
          q.height = (r : ℕ∞) + 1
        then ((primLen (Ideal.span (Set.range g) ⊔ Ideal.span {G}) q).toNat : ℚ) * rayDeg N D q
        else 0) ≤
      (if q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes ∧ OnGPrime N q ∧
          q.height = (r : ℕ∞) + 1
        then (∑ p ∈ SP, (if p ≤ q then ((primLen (Ideal.span (Set.range g)) p).toNat : ℚ) *
            ((primLen (p ⊔ Ideal.span {G}) q).toNat : ℚ) else 0)) * rayDeg N D q
        else 0) := by
    intro q hqSK
    by_cases hc : (q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes ∧
        OnGPrime N q ∧ q.height = (r : ℕ∞) + 1)
    · rw [if_pos hc, if_pos hc]
      refine mul_le_mul_of_nonneg_right ?_ (rayDeg_nonneg D q)
      have hloc : ∀ p ∈ associatedPrimes (MR N)
            (MR N ⧸ Ideal.span (Set.range g)), p ≤ q →
            p ∈ (Ideal.span (Set.range g)).minimalPrimes :=
        span_assPrime_le_mem_minimalPrimes g q hc.1.1.1
          (fun p hpJ hpq => (chain_step_local I g G hGI hht hc.1 hc.2.2 p hpJ hpq).2.2)
      have hb := primLen_sup_span_le_sum_loc (Ideal.span (Set.range g)) G q hc.1 hloc
      have hconv : (∑ᶠ (p : Ideal (MR N))
            (_ : p ∈ (Ideal.span (Set.range g)).minimalPrimes ∧ p ≤ q),
            ((primLen (Ideal.span (Set.range g)) p).toNat : ℚ) *
              ((primLen (p ⊔ Ideal.span {G}) q).toNat : ℚ))
          = ∑ p ∈ SP, (if p ≤ q then ((primLen (Ideal.span (Set.range g)) p).toNat : ℚ) *
              ((primLen (p ⊔ Ideal.span {G}) q).toNat : ℚ) else 0) := by
        rw [finsum_cond_eq_sum
          (fun p => p ∈ (Ideal.span (Set.range g)).minimalPrimes ∧ p ≤ q) SP
          (fun a ha => (hSP a).mpr ha.1)]
        refine Finset.sum_congr rfl (fun p hp => ?_)
        by_cases hpq : p ≤ q
        · rw [if_pos ⟨(hSP p).mp hp, hpq⟩, if_pos hpq]
        · rw [if_neg (fun h => hpq h.2), if_neg hpq]
      rw [hconv] at hb
      exact hb
    · rw [if_neg hc, if_neg hc]
  refine le_trans (Finset.sum_le_sum hlocal) ?_
  have eq12 : (∑ q ∈ SK, (if q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes ∧
        OnGPrime N q ∧ q.height = (r : ℕ∞) + 1
        then (∑ p ∈ SP, (if p ≤ q then ((primLen (Ideal.span (Set.range g)) p).toNat : ℚ) *
            ((primLen (p ⊔ Ideal.span {G}) q).toNat : ℚ) else 0)) * rayDeg N D q
        else 0))
      = (∑ p ∈ SP, ((primLen (Ideal.span (Set.range g)) p).toNat : ℚ) *
          (∑ q ∈ SK, (if (q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes ∧
              OnGPrime N q ∧ q.height = (r : ℕ∞) + 1) ∧ p ≤ q
            then ((primLen (p ⊔ Ideal.span {G}) q).toNat : ℚ) * rayDeg N D q else 0))) := by
    calc (∑ q ∈ SK, (if q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes ∧
          OnGPrime N q ∧ q.height = (r : ℕ∞) + 1
          then (∑ p ∈ SP, (if p ≤ q then ((primLen (Ideal.span (Set.range g)) p).toNat : ℚ) *
              ((primLen (p ⊔ Ideal.span {G}) q).toNat : ℚ) else 0)) * rayDeg N D q
          else 0))
        = (∑ q ∈ SK, (if q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes ∧
            OnGPrime N q ∧ q.height = (r : ℕ∞) + 1
            then (∑ p ∈ SP, (if p ≤ q then ((primLen (Ideal.span (Set.range g)) p).toNat : ℚ) *
                ((primLen (p ⊔ Ideal.span {G}) q).toNat : ℚ) else 0) * rayDeg N D q)
            else 0)) := by
          refine Finset.sum_congr rfl (fun q hq => ?_)
          rw [Finset.sum_mul]
      _ = (∑ q ∈ SK, ∑ p ∈ SP, (if q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes ∧
            OnGPrime N q ∧ q.height = (r : ℕ∞) + 1
            then (if p ≤ q then ((primLen (Ideal.span (Set.range g)) p).toNat : ℚ) *
                ((primLen (p ⊔ Ideal.span {G}) q).toNat : ℚ) else 0) * rayDeg N D q
            else 0)) := by
          refine Finset.sum_congr rfl (fun q hq => ?_)
          by_cases hq' : (q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes ∧
              OnGPrime N q ∧ q.height = (r : ℕ∞) + 1) <;> simp [hq']
      _ = (∑ p ∈ SP, ∑ q ∈ SK, (if q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes ∧
            OnGPrime N q ∧ q.height = (r : ℕ∞) + 1
            then (if p ≤ q then ((primLen (Ideal.span (Set.range g)) p).toNat : ℚ) *
                ((primLen (p ⊔ Ideal.span {G}) q).toNat : ℚ) else 0) * rayDeg N D q
            else 0)) := Finset.sum_comm
      _ = (∑ p ∈ SP, ((primLen (Ideal.span (Set.range g)) p).toNat : ℚ) *
          (∑ q ∈ SK, (if (q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes ∧
              OnGPrime N q ∧ q.height = (r : ℕ∞) + 1) ∧ p ≤ q
            then ((primLen (p ⊔ Ideal.span {G}) q).toNat : ℚ) * rayDeg N D q else 0))) := by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun q hq => ?_)
          by_cases hq' : (q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes ∧
              OnGPrime N q ∧ q.height = (r : ℕ∞) + 1)
          · by_cases hpq : p ≤ q
            · rw [if_pos hq', if_pos hpq, if_pos ⟨hq', hpq⟩]; ring
            · rw [if_pos hq', if_neg hpq, if_neg (fun h => hpq h.2)]; ring
          · rw [if_neg hq', if_neg (fun h => hq' h.1)]; ring
  have ineq23 : (∑ p ∈ SP, ((primLen (Ideal.span (Set.range g)) p).toNat : ℚ) *
        (∑ q ∈ SK, (if (q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes ∧
            OnGPrime N q ∧ q.height = (r : ℕ∞) + 1) ∧ p ≤ q
          then ((primLen (p ⊔ Ideal.span {G}) q).toNat : ℚ) * rayDeg N D q else 0)))
      ≤ (∑ p ∈ SP, (if p ∈ (Ideal.span (Set.range g)).minimalPrimes ∧ OnGPrime N p ∧ ¬ I ≤ p
          then ((primLen (Ideal.span (Set.range g)) p).toNat : ℚ) * rayDeg N D p else 0)) := by
    refine Finset.sum_le_sum (fun p hpSP => ?_)
    have hpJ : p ∈ (Ideal.span (Set.range g)).minimalPrimes := (hSP p).mp hpSP
    by_cases hcp : p ∈ (Ideal.span (Set.range g)).minimalPrimes ∧ OnGPrime N p ∧ ¬ I ≤ p
    · rw [if_pos hcp]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← Finset.sum_filter]
      have hsub : ∀ q ∈ SK.filter (fun q => (q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes ∧
            OnGPrime N q ∧ q.height = (r : ℕ∞) + 1) ∧ p ≤ q),
          q ∈ (p ⊔ Ideal.span {G}).minimalPrimes ∧ OnGPrime N q := by
        intro q hq
        rw [Finset.mem_filter] at hq
        obtain ⟨hqSK, hcQ, hpq⟩ := hq
        exact ⟨mem_minimalPrimes_sup_span_of_le (Ideal.span (Set.range g)) G p hpJ q
            ((hSK q).mp hqSK) hpq, hcQ.2.1⟩
      exact le_trans (finset_sum_le_srel D (p ⊔ Ideal.span {G}) _ hsub)
        (srel_sup_span_le_rayDeg D hD (Ideal.span (Set.range g)) hmulti G hG p hpJ)
    · rw [if_neg hcp]
      have hzero : (∑ q ∈ SK, (if (q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes ∧
            OnGPrime N q ∧ q.height = (r : ℕ∞) + 1) ∧ p ≤ q
          then ((primLen (p ⊔ Ideal.span {G}) q).toNat : ℚ) * rayDeg N D q else 0)) = 0 := by
        refine Finset.sum_eq_zero (fun q hqSK => ?_)
        have hfalse : ¬((q ∈ (Ideal.span (Set.range g) ⊔ Ideal.span {G}).minimalPrimes ∧
            OnGPrime N q ∧ q.height = (r : ℕ∞) + 1) ∧ p ≤ q) := by
          rintro ⟨hcQ, hpq⟩
          have hloc := chain_step_local I g G hGI hht hcQ.1 hcQ.2.2 p hpJ hpq
          exact hcp ⟨hpJ, OnGPrime_anti hpq hcQ.2.1, hloc.2.1⟩
        rw [if_neg hfalse]
      rw [hzero, mul_zero]
  exact le_trans (le_of_eq eq12) ineq23

end Work.BW.RB
