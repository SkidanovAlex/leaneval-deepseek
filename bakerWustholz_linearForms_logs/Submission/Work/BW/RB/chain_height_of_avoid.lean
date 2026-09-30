import Mathlib
import Submission.Work.BW.RB.A4

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

set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

/-- Heights along an avoiding chain.  If each `g j` avoids every minimal prime of
`J_j = (g i : i < j)` that does not contain `I`, then for every `s ≤ k` every minimal prime of
`J_s` not containing `I` has height exactly `s`.

Route: induction on `s`, as in `chainProp_exists` (`RB/exists_chain_height_eq.lean`).
* `s = 0`: `J_0 = ⊥`, whose only minimal prime is `⊥`, of height `0`.
* Step `s → s+1` (`s < k`): `J_{s+1} = J_s ⊔ span {g ⟨s, _⟩}`, because
  `g '' {i | i.1 < s+1} = g '' {i | i.1 < s} ∪ {g ⟨s,_⟩}`.  Let `p ∈ Min J_{s+1}` with `I ≰ p`.
  - `≥`: `p` contains some `p' ∈ Min J_s` (`Ideal.exists_minimalPrimes_le`), and `I ≰ p'`
    because `p' ≤ p`.  So `p'.height = s` and `g ⟨s,_⟩ ∉ p'` by `hav`, whence `p' < p` and
    `p.height ≥ s + 1` (`Ideal.height_add_one_le_of_lt_of_isPrime`, with `p'.height` finite by
    `height_ne_top`).
  - `≤`: Krull, `Ideal.height_le_card_of_mem_minimalPrimes_span_finset` applied to the finset
    `(univ.filter (·.1 < s+1)).image g`, of card `≤ s+1`. -/
theorem chain_height_of_avoid {N k : ℕ} (I : Ideal (MR N)) (g : Fin k → MR N)
    (hav : ∀ j : Fin k, ∀ p ∈ (Ideal.span (g '' {i : Fin k | i.1 < j.1})).minimalPrimes,
      ¬ I ≤ p → g j ∉ p) :
    ∀ s : ℕ, s ≤ k → ∀ p ∈ (Ideal.span (g '' {i : Fin k | i.1 < s})).minimalPrimes,
      ¬ I ≤ p → p.height = (s : ℕ∞) := by
  intro s
  induction s with
  | zero =>
    intro _ p hp hnI
    have hbot : (Ideal.span (g '' {i : Fin k | i.1 < 0}) : Ideal (MR N)) = ⊥ := by
      rw [show {i : Fin k | i.1 < 0} = (∅ : Set (Fin k)) from by
        ext i; simp, Set.image_empty, Ideal.span_empty]
    rw [hbot] at hp
    have hpbot : p = ⊥ := by
      have h : p ∈ minimalPrimes (MR N) := hp
      rwa [IsDomain.minimalPrimes_eq_singleton_bot] at h
    rw [hpbot, Ideal.height_bot]
    simp
  | succ n ih =>
    intro hs p hp hnI
    have hnk : n < k := by omega
    have hs' : n ≤ k := by omega
    have ih' := ih hs'
    have hset : {i : Fin k | i.1 < n + 1} = {i : Fin k | i.1 < n} ∪ {⟨n, hnk⟩} := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · intro hi
        rcases Nat.lt_or_ge i.1 n with h | h
        · exact Or.inl h
        · refine Or.inr (Fin.ext ?_)
          show i.1 = n
          omega
      · rintro (h | rfl)
        · omega
        · simp
    have hstep : (Ideal.span (g '' {i : Fin k | i.1 < n + 1}) : Ideal (MR N))
        = Ideal.span (g '' {i : Fin k | i.1 < n}) ⊔ Ideal.span {g ⟨n, hnk⟩} := by
      rw [hset, Set.image_union, Set.image_singleton, Ideal.span_union]
    have hpJ : p ∈ (Ideal.span (g '' {i : Fin k | i.1 < n}) ⊔
        Ideal.span {g ⟨n, hnk⟩}).minimalPrimes := by
      rw [← hstep]; exact hp
    haveI : p.IsPrime := hpJ.isPrime
    have hJle : (Ideal.span (g '' {i : Fin k | i.1 < n}) : Ideal (MR N)) ≤ p :=
      le_trans le_sup_left hpJ.le
    obtain ⟨p', hp'mem, hp'le⟩ := Ideal.exists_minimalPrimes_le hJle
    have hp'nI : ¬ I ≤ p' := fun h => hnI (h.trans hp'le)
    have hp'ht : p'.height = (n : ℕ∞) := ih' p' hp'mem hp'nI
    have hgnp' : g ⟨n, hnk⟩ ∉ p' := hav ⟨n, hnk⟩ p' hp'mem hp'nI
    have hgp : g ⟨n, hnk⟩ ∈ p :=
      hpJ.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hlt : p' < p := lt_of_le_of_ne hp'le (fun he => hgnp' (he ▸ hgp))
    haveI : p'.IsPrime := hp'mem.isPrime
    have hlow : ((n + 1 : ℕ) : ℕ∞) ≤ p.height := by
      have h := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      rw [hp'ht] at h
      simpa using h
    have hup : p.height ≤ ((n + 1 : ℕ) : ℕ∞) := by
      have hw : (↑((Finset.univ.filter (fun i : Fin k => i.1 < n + 1)).image g) : Set (MR N))
          = g '' {i : Fin k | i.1 < n + 1} := by
        ext y
        simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_image, Set.mem_ofPred_eq]
      have hspan : (Ideal.span (↑((Finset.univ.filter (fun i : Fin k => i.1 < n + 1)).image g) :
            Set (MR N))) = Ideal.span (g '' {i : Fin k | i.1 < n + 1}) := by
        rw [hw]
      have hpmem : p ∈ (Ideal.span (↑((Finset.univ.filter (fun i : Fin k => i.1 < n + 1)).image g) :
          Set (MR N))).minimalPrimes := by
        rw [hspan]; exact hp
      have hfil : (Finset.univ.filter (fun i : Fin k => i.1 < n + 1)).card ≤ n + 1 := by
        have h1 : ((Finset.univ.filter (fun i : Fin k => i.1 < n + 1)).image (fun i => i.1)).card
            = (Finset.univ.filter (fun i : Fin k => i.1 < n + 1)).card :=
          Finset.card_image_of_injective _ Fin.val_injective
        rw [← h1]
        refine (Finset.card_le_card ?_).trans (le_of_eq (Finset.card_range (n + 1)))
        intro m hm
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hm
        obtain ⟨i, hi, rfl⟩ := hm
        exact Finset.mem_range.mpr hi
      have hcard : ((Finset.univ.filter (fun i : Fin k => i.1 < n + 1)).image g).card ≤ n + 1 :=
        (Finset.card_image_le (s := Finset.univ.filter (fun i : Fin k => i.1 < n + 1))
          (f := g)).trans hfil
      exact (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hpmem).trans
        (Nat.cast_le.mpr hcard)
    exact le_antisymm hup hlow

end Work.BW.RB
