import Mathlib
import Submission.Work.BW.RB.A4
import Submission.Work.BW.RB.chain_height_of_avoid
import Submission.Work.BW.RB.srel_chain_step
import Submission.Work.BW.primLen_mono
import Submission.Work.BW.primLen_ne_top

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

noncomputable section

/-- The ideal generated by the first `s` elements of a chain `g : Fin k → MR N`. -/
abbrev chainId {N k : ℕ} (g : Fin k → MR N) (s : ℕ) : Ideal (MR N) :=
  Ideal.span (g '' {i : Fin k | i.1 < s})

lemma chainId_zero {N k : ℕ} (g : Fin k → MR N) : chainId g 0 = (⊥ : Ideal (MR N)) := by
  simp [chainId]

lemma chainId_succ {N k : ℕ} (g : Fin k → MR N) {s : ℕ} (hs : s < k) :
    chainId g (s + 1) = chainId g s ⊔ Ideal.span {g ⟨s, hs⟩} := by
  have hset : {i : Fin k | i.1 < s + 1} = {i : Fin k | i.1 < s} ∪ {⟨s, hs⟩} := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact Or.inl h
      · exact Or.inr (Fin.ext h)
    · rintro (h | h)
      · omega
      · rw [h]; exact Nat.lt_succ_self s
  show Ideal.span (g '' {i : Fin k | i.1 < s + 1}) =
    Ideal.span (g '' {i : Fin k | i.1 < s}) ⊔ Ideal.span {g ⟨s, hs⟩}
  rw [hset, Set.image_union, Set.image_singleton, Ideal.span_union]


/-- `finsum` over a proposition. -/
private lemma rb_finsum_over_prop {M : Type*} [AddCommMonoid M] {P : Prop} [Decidable P] (g : M) :
    (∑ᶠ (_ : P), g) = if P then g else 0 := by
  classical
  by_cases h : P
  · rw [if_pos h]
    exact finsum_eq_single (fun _ : P => g) h fun x hx => absurd (Subsingleton.elim x h) hx
  · rw [if_neg h]
    haveI : IsEmpty P := ⟨fun hp => h hp⟩
    exact finsum_of_isEmpty _

/-- A `finsum` over a decidable predicate equals the corresponding `Finset` sum. -/
private lemma rb_finsum_cond_eq_sum {α M : Type*} [AddCommMonoid M] (P : α → Prop)
    [DecidablePred P] (S : Finset α) (hS : ∀ a, P a → a ∈ S) (g : α → M) :
    (∑ᶠ (a : α) (_ : P a), g a) = ∑ a ∈ S, (if P a then g a else 0) := by
  classical
  have hsub : Function.support (fun a : α => ∑ᶠ (_ : P a), g a) ⊆ ↑S := by
    intro a ha
    by_contra hna
    have hPa : ¬ P a := fun hpa => hna (hS a hpa)
    simp only [Function.mem_support] at ha
    exact ha (by rw [rb_finsum_over_prop, if_neg hPa])
  rw [finsum_eq_sum_of_support_subset _ hsub]
  exact Finset.sum_congr rfl fun a _ => rb_finsum_over_prop (g a)

/-- Telescoping the generic chain.  Let `I ≠ ⊥` be spanned by `g 0, …, g (k-1)`, all of
multidegree `D`, and suppose each `g j` avoids the minimal primes of `J_j = (g i : i < j)` that
do not contain `I`.  This is the output of `exists_generic_chain`, after rewriting
`↑((univ.filter (·.1 < j.1)).image g) = g '' {i | i.1 < j.1}`.  Then
`Srel N D I ≤ rayDeg N D ⊥`.

Route.  Write `J_s = span (g '' {i | i.1 < s})` for `s ≤ k`, so `J_0 = ⊥` and `J_k = I`, and
* `A s = ∑_{p ∈ Min J_s, adm, I ≰ p} ℓ_p(J_s) H(p)`,
* `B s = ∑_{q ∈ Min J_s, adm, ht q = s, I ≤ q} ℓ_q(J_s) H(q)`.
1. `A 0 = rayDeg ⊥`: `Min ⊥ = {⊥}`, `I ≰ ⊥` since `I ≠ ⊥`, and `OnGPrime_bot`, `primLen_bot`.
2. Step, for `s < k`: `A (s+1) + B (s+1) ≤ A s`.  By `chain_height_of_avoid`, every
   `p ∈ Min J_{s+1}` with `I ≰ p` has height `s+1`.  So the index set
   `{q ∈ Min J_{s+1}, adm, ht = s+1}` is the disjoint union of the index sets of `A (s+1)` and
   `B (s+1)`, and `srel_chain_step` bounds its sum by `A s`.  Apply that with the prefix
   `g' : Fin s → MR N`, `g' i = g (Fin.castLE _ i)`, and `G = g ⟨s, _⟩`; `hht` comes from
   `chain_height_of_avoid`, `hav` from the hypothesis, and `G ∈ I` from `hgI`.
3. Summing, `A k + ∑_{s=1}^{k} B s ≤ A 0`, and `A k ≥ 0`.
4. `Srel N D I ≤ ∑_{s=1}^{k} B s`.  Let `q ∈ Min I` be admissible and put `h = q.height`.  It is
   finite (`height_ne_top`), `h ≥ 1` since `q ≠ ⊥` (because `I ≤ q` and `I ≠ ⊥`; in a domain the
   height-0 prime is `⊥`), and `h ≤ k` by Krull.  Then `q ∈ Min J_h`: `q` contains some
   `p ∈ Min J_h`.  If `I ≤ p`, then `p = q` by the minimality of `q` over `I`.  Otherwise
   `p.height = h` by `chain_height_of_avoid`, and `p ≤ q` with equal finite heights forces
   `p = q`.  Finally `ℓ_q(I) ≤ ℓ_q(J_h)` by `primLen_mono` (`J_h ≤ I`), with both finite
   (`primLen_ne_top`), so `toNat` is monotone.  Distinct `q` land in distinct `(h, q)` slots of
   the `B`-sums, and all terms are `≥ 0`. -/
theorem srel_le_of_generic_chain {N k : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (I : Ideal (MR N)) (hI : I ≠ ⊥) (g : Fin k → MR N) (hg : ∀ j, g j ∈ homPiece N D)
    (hgI : Ideal.span (Set.range g) = I)
    (hav : ∀ j : Fin k, ∀ p ∈ (Ideal.span (g '' {i : Fin k | i.1 < j.1})).minimalPrimes,
      ¬ I ≤ p → g j ∉ p) :
    Srel N D I ≤ rayDeg N D ⊥ := by
  classical
  have hJ0 : chainId g 0 = (⊥ : Ideal (MR N)) := chainId_zero g
  -- a finset of minimal primes for every member of the chain
  have hexSJ : ∀ s : ℕ, ∃ S : Finset (Ideal (MR N)),
      ∀ q, q ∈ S ↔ q ∈ (chainId g s).minimalPrimes := by
    intro s
    exact ⟨(Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N) (chainId g s)).toFinset,
      fun q => Set.Finite.mem_toFinset _⟩
  let SJ : ℕ → Finset (Ideal (MR N)) := fun s => Classical.choose (hexSJ s)
  have hSJ : ∀ (s : ℕ) (q : Ideal (MR N)), q ∈ SJ s ↔ q ∈ (chainId g s).minimalPrimes :=
    fun s => Classical.choose_spec (hexSJ s)
  -- the two height-graded sums
  let A : ℕ → ℚ := fun s => ∑ q ∈ SJ s,
    (if OnGPrime N q ∧ ¬ I ≤ q then
      ((primLen (chainId g s) q).toNat : ℚ) * rayDeg N D q else 0)
  let B : ℕ → ℚ := fun s => ∑ q ∈ SJ s,
    (if OnGPrime N q ∧ q.height = (s : ℕ∞) ∧ I ≤ q then
      ((primLen (chainId g s) q).toNat : ℚ) * rayDeg N D q else 0)
  -- (1) the base case
  have hA0 : A 0 = rayDeg N D ⊥ := by
    show (∑ q ∈ SJ 0, (if OnGPrime N q ∧ ¬ I ≤ q then
      ((primLen (chainId g 0) q).toNat : ℚ) * rayDeg N D q else 0)) = rayDeg N D ⊥
    have hSJ0 : SJ 0 = {⊥} := by
      ext q
      rw [hSJ 0 q, hJ0, minimalPrimes_bot]
      simp
    rw [hSJ0, Finset.sum_singleton,
      if_pos ⟨OnGPrime_bot, fun h => hI (le_bot_iff.mp h)⟩, hJ0, primLen_bot N]
    ring
  have hA_nonneg : ∀ s, 0 ≤ A s := by
    intro s
    refine Finset.sum_nonneg fun q _ => ?_
    split
    · exact mul_nonneg (by positivity) (rayDeg_nonneg D q)
    · exact le_refl 0
  -- (2) the one-step inequality
  have hstep : ∀ s, s < k → A (s + 1) + B (s + 1) ≤ A s := by
    intro s hs
    have hsk : s ≤ k := le_of_lt hs
    let g' : Fin s → MR N := fun i => g (Fin.castLE hsk i)
    let G : MR N := g ⟨s, hs⟩
    have hrange : Set.range g' = g '' {i : Fin k | i.1 < s} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨Fin.castLE hsk i, i.2, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i.1, hi⟩, congrArg g (Fin.ext rfl)⟩
    have hJmap : chainId g s = Ideal.span (Set.range g') := by rw [hrange]
    have hJsucc : chainId g (s + 1) = Ideal.span (Set.range g') ⊔ Ideal.span {G} := by
      rw [chainId_succ g hs, ← hJmap]
    have hht : ∀ p ∈ (Ideal.span (Set.range g')).minimalPrimes, ¬ I ≤ p →
        p.height = (s : ℕ∞) := by
      intro p hp hnp
      rw [hrange] at hp
      exact chain_height_of_avoid I g hav s hsk p hp hnp
    have hav' : ∀ p ∈ (Ideal.span (Set.range g')).minimalPrimes, ¬ I ≤ p → G ∉ p := by
      intro p hp hnp
      rw [hrange] at hp
      exact hav ⟨s, hs⟩ p hp hnp
    have hGmem : G ∈ homPiece N D := hg ⟨s, hs⟩
    have hGI : G ∈ I := by
      rw [← hgI]
      exact Ideal.subset_span ⟨⟨s, hs⟩, rfl⟩
    have step := srel_chain_step (N := N) (r := s) D hD I g'
      (fun j => hg (Fin.castLE hsk j)) G hGmem hGI hht hav'
    rw [← hJsucc, ← hJmap] at step
    have hcast : ((s + 1 : ℕ) : ℕ∞) = (s : ℕ∞) + 1 := by push_cast; ring
    -- `A s` in `finsum` form
    have hAeq : A s = ∑ᶠ (p : Ideal (MR N))
        (_ : p ∈ (chainId g s).minimalPrimes ∧ OnGPrime N p ∧ ¬ I ≤ p),
        ((primLen (chainId g s) p).toNat : ℚ) * rayDeg N D p := by
      show (∑ q ∈ SJ s, (if OnGPrime N q ∧ ¬ I ≤ q then
        ((primLen (chainId g s) q).toNat : ℚ) * rayDeg N D q else 0)) = _
      rw [rb_finsum_cond_eq_sum (fun q : Ideal (MR N) =>
        q ∈ (chainId g s).minimalPrimes ∧ OnGPrime N q ∧ ¬ I ≤ q) (SJ s)
        (fun a ha => (hSJ s a).mpr ha.1)]
      refine Finset.sum_congr rfl fun q hq => ?_
      by_cases h1 : OnGPrime N q ∧ ¬ I ≤ q
      · rw [if_pos h1, if_pos ⟨(hSJ s q).mp hq, h1⟩]
      · rw [if_neg h1, if_neg (fun h => h1 h.2)]
    -- the height-`s+1` admissible primes in `finset` form
    have hCeq : (∑ q ∈ SJ (s + 1), (if OnGPrime N q ∧
          q.height = ((s + 1 : ℕ) : ℕ∞) then
        ((primLen (chainId g (s + 1)) q).toNat : ℚ) * rayDeg N D q else 0))
        = ∑ᶠ (q : Ideal (MR N)) (_ : q ∈ (chainId g (s + 1)).minimalPrimes ∧
            OnGPrime N q ∧ q.height = (s : ℕ∞) + 1),
          ((primLen (chainId g (s + 1)) q).toNat : ℚ) * rayDeg N D q := by
      rw [rb_finsum_cond_eq_sum (fun q : Ideal (MR N) =>
        q ∈ (chainId g (s + 1)).minimalPrimes ∧ OnGPrime N q ∧
          q.height = (s : ℕ∞) + 1) (SJ (s + 1))
        (fun a ha => (hSJ (s + 1) a).mpr ha.1)]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [hcast]
      by_cases h1 : OnGPrime N q ∧ q.height = (s : ℕ∞) + 1
      · rw [if_pos h1, if_pos ⟨(hSJ (s + 1) q).mp hq, h1⟩]
      · rw [if_neg h1, if_neg (fun h => h1 h.2)]
    have hAB : A (s + 1) + B (s + 1) = (∑ q ∈ SJ (s + 1),
        (if OnGPrime N q ∧ q.height = ((s + 1 : ℕ) : ℕ∞) then
          ((primLen (chainId g (s + 1)) q).toNat : ℚ) * rayDeg N D q else 0)) := by
      show (∑ q ∈ SJ (s + 1), (if OnGPrime N q ∧ ¬ I ≤ q then
            ((primLen (chainId g (s + 1)) q).toNat : ℚ) * rayDeg N D q else 0))
          + (∑ q ∈ SJ (s + 1), (if OnGPrime N q ∧
              q.height = ((s + 1 : ℕ) : ℕ∞) ∧ I ≤ q then
            ((primLen (chainId g (s + 1)) q).toNat : ℚ) * rayDeg N D q else 0)) = _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q hq => ?_
      by_cases hadm : OnGPrime N q
      · by_cases hIq : I ≤ q
        · by_cases hht : q.height = ((s + 1 : ℕ) : ℕ∞)
          · rw [if_neg (show ¬ (OnGPrime N q ∧ ¬ I ≤ q) from fun h => h.2 hIq),
                if_pos (show OnGPrime N q ∧ q.height = ((s + 1 : ℕ) : ℕ∞) ∧ I ≤ q from
                  ⟨hadm, hht, hIq⟩),
                if_pos (show OnGPrime N q ∧ q.height = ((s + 1 : ℕ) : ℕ∞) from ⟨hadm, hht⟩)]
            ring
          · rw [if_neg (show ¬ (OnGPrime N q ∧ ¬ I ≤ q) from fun h => h.2 hIq),
                if_neg (show ¬ (OnGPrime N q ∧ q.height = ((s + 1 : ℕ) : ℕ∞) ∧ I ≤ q) from
                  fun h => hht h.2.1),
                if_neg (show ¬ (OnGPrime N q ∧ q.height = ((s + 1 : ℕ) : ℕ∞)) from
                  fun h => hht h.2)]
            ring
        · have hqmem : q ∈ (chainId g (s + 1)).minimalPrimes := (hSJ (s + 1) q).mp hq
          have hht : q.height = ((s + 1 : ℕ) : ℕ∞) :=
            chain_height_of_avoid I g hav (s + 1) (Nat.succ_le_of_lt hs) q hqmem hIq
          rw [if_pos (show OnGPrime N q ∧ ¬ I ≤ q from ⟨hadm, hIq⟩),
                if_neg (show ¬ (OnGPrime N q ∧ q.height = ((s + 1 : ℕ) : ℕ∞) ∧ I ≤ q) from
                  fun h => hIq h.2.2),
                if_pos (show OnGPrime N q ∧ q.height = ((s + 1 : ℕ) : ℕ∞) from ⟨hadm, hht⟩)]
          ring
      · rw [if_neg (show ¬ (OnGPrime N q ∧ ¬ I ≤ q) from fun h => hadm h.1),
            if_neg (show ¬ (OnGPrime N q ∧ q.height = ((s + 1 : ℕ) : ℕ∞) ∧ I ≤ q) from
              fun h => hadm h.1),
            if_neg (show ¬ (OnGPrime N q ∧ q.height = ((s + 1 : ℕ) : ℕ∞)) from fun h => hadm h.1)]
        ring
    calc A (s + 1) + B (s + 1)
        = (∑ q ∈ SJ (s + 1), (if OnGPrime N q ∧
            q.height = ((s + 1 : ℕ) : ℕ∞) then
          ((primLen (chainId g (s + 1)) q).toNat : ℚ) * rayDeg N D q else 0)) := hAB
      _ = ∑ᶠ (q : Ideal (MR N)) (_ : q ∈ (chainId g (s + 1)).minimalPrimes ∧
            OnGPrime N q ∧ q.height = (s : ℕ∞) + 1),
          ((primLen (chainId g (s + 1)) q).toNat : ℚ) * rayDeg N D q := hCeq
      _ ≤ ∑ᶠ (p : Ideal (MR N))
          (_ : p ∈ (chainId g s).minimalPrimes ∧ OnGPrime N p ∧ ¬ I ≤ p),
          ((primLen (chainId g s) p).toNat : ℚ) * rayDeg N D p := step
      _ = A s := hAeq.symm
  -- (3) telescoping
  have htel : ∀ s : ℕ, s ≤ k → A s + ∑ t ∈ Finset.Icc 1 s, B t ≤ A 0 := by
    intro s
    induction s with
    | zero => intro _; simp
    | succ n ih =>
      intro hs
      have hn : n ≤ k := Nat.le_of_succ_le hs
      have hnk : n < k := Nat.lt_of_succ_le hs
      rw [Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega) B]
      have h1 := ih hn
      have h2 := hstep n hnk
      linarith
  -- (4) collecting the components of `I`
  have hcoll : Srel N D I ≤ ∑ t ∈ Finset.Icc 1 k, B t := by
    obtain ⟨SI, hSI⟩ : ∃ S : Finset (Ideal (MR N)), ∀ q, q ∈ S ↔ q ∈ I.minimalPrimes :=
      ⟨(Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N) I).toFinset,
        fun q => Set.Finite.mem_toFinset _⟩
    have hSrel : Srel N D I = ∑ q ∈ SI, (if OnGPrime N q then
        ((primLen I q).toNat : ℚ) * rayDeg N D q else 0) := by
      rw [Srel, rb_finsum_cond_eq_sum (fun q : Ideal (MR N) =>
        q ∈ I.minimalPrimes ∧ OnGPrime N q) SI (fun a ha => (hSI a).mpr ha.1)
        (fun q => ((primLen I q).toNat : ℚ) * rayDeg N D q)]
      refine Finset.sum_congr rfl fun q hq => ?_
      by_cases h2 : OnGPrime N q
      · rw [if_pos ⟨(hSI q).mp hq, h2⟩, if_pos h2]
      · rw [if_neg (fun h => h2 h.2), if_neg h2]
    rw [hSrel]
    have hqle : ∀ q ∈ SI, I ≤ q := fun q hq => ((hSI q).mp hq).le
    have hqne : ∀ q ∈ SI, q ≠ ⊥ := by
      intro q hq h
      exact hI (le_bot_iff.mp (h ▸ hqle q hq))
    have hqrull : ∀ q ∈ SI, q.height ≤ (k : ℕ∞) := by
      intro q hq
      have hspan : Ideal.span (↑(Finset.univ.image g) : Set (MR N)) = I := by
        rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hgI]
      have hmem : q ∈ (Ideal.span (↑(Finset.univ.image g) : Set (MR N))).minimalPrimes := by
        rw [hspan]; exact (hSI q).mp hq
      have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmem
      have h2 : (Finset.univ.image g).card ≤ k := by
        simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := g)
      calc q.height ≤ ((Finset.univ.image g).card : ℕ∞) := h1
        _ ≤ (k : ℕ∞) := by exact_mod_cast h2
    have hqnetop : ∀ q ∈ SI, q.height ≠ ⊤ := fun q hq =>
      ne_of_lt (lt_of_le_of_lt (hqrull q hq) (ENat.natCast_lt_top k))
    have hqf : ∀ q ∈ SI, q.height = ((q.height.toNat : ℕ) : ℕ∞) :=
      fun q hq => (ENat.natCast_toNat (hqnetop q hq)).symm
    have hqk : ∀ q ∈ SI, q.height.toNat ≤ k := by
      intro q hq
      have h := ENat.toNat_le_toNat (hqrull q hq) (ENat.natCast_ne_top k)
      simpa [ENat.toNat_natCast] using h
    have hq1 : ∀ q ∈ SI, 1 ≤ q.height.toNat := by
      intro q hq
      refine Nat.one_le_iff_ne_zero.mpr fun h0 => ?_
      have hpos : q.height ≠ 0 := fun hzero =>
        hqne q hq (Ideal.height_eq_zero_iff_eq_bot.mp hzero)
      refine hpos ?_
      calc q.height = ((q.height.toNat : ℕ) : ℕ∞) := hqf q hq
        _ = ((0 : ℕ) : ℕ∞) := by rw [h0]
        _ = 0 := ENat.natCast_zero
    have hqJ : ∀ q ∈ SI, chainId g q.height.toNat ≤ I := by
      intro q _
      rw [← hgI]
      exact Ideal.span_mono (Set.image_subset_range g _)
    have hqht : ∀ q ∈ SI, q ∈ (chainId g q.height.toNat).minimalPrimes := by
      intro q hq
      haveI : q.IsPrime := ((hSI q).mp hq).isPrime
      obtain ⟨p, hpmin, hpq⟩ := Ideal.exists_minimalPrimes_le
        (I := chainId g q.height.toNat) (J := q) ((hqJ q hq).trans (hqle q hq))
      by_cases hIp : I ≤ p
      · have hqlep : q ≤ p := ((hSI q).mp hq).2 ⟨hpmin.isPrime, hIp⟩ hpq
        exact (le_antisymm hpq hqlep) ▸ hpmin
      · have hpht : p.height = ((q.height.toNat : ℕ) : ℕ∞) :=
          chain_height_of_avoid I g hav q.height.toNat (hqk q hq) p hpmin hIp
        haveI : p.FiniteHeight := (Ideal.finiteHeight_iff p).mpr
          (Or.inr (by rw [hpht]; exact ENat.natCast_ne_top _))
        haveI : p.IsPrime := hpmin.isPrime
        have hpq' : p = q := Ideal.eq_of_le_of_height_le (I := p) hpq
          (le_of_eq (by rw [hpht]; exact hqf q hq))
        exact hpq' ▸ hpmin
    let FF : (Σ t : ℕ, Ideal (MR N)) → ℚ := fun x =>
      if OnGPrime N x.2 ∧ x.2.height = (x.1 : ℕ∞) ∧ I ≤ x.2 then
        ((primLen (chainId g x.1) x.2).toNat : ℚ) * rayDeg N D x.2 else 0
    let PP : Finset (Σ t : ℕ, Ideal (MR N)) := (Finset.Icc 1 k).sigma SJ
    have hPPsum : ∑ x ∈ PP, FF x = ∑ t ∈ Finset.Icc 1 k, B t := by
      show ∑ x ∈ (Finset.Icc 1 k).sigma SJ, FF x = ∑ t ∈ Finset.Icc 1 k, B t
      rw [Finset.sum_sigma]
    let Q' : Finset (Σ t : ℕ, Ideal (MR N)) :=
      SI.image (fun q => (⟨q.height.toNat, q⟩ : Σ _ : ℕ, Ideal (MR N)))
    have hQ'def : Q' = SI.image (fun q => (⟨q.height.toNat, q⟩ : Σ _ : ℕ, Ideal (MR N))) := rfl
    have hinj : Set.InjOn (fun q : Ideal (MR N) =>
        (⟨q.height.toNat, q⟩ : Σ _ : ℕ, Ideal (MR N))) ↑SI := by
      intro q _ q' _ heq
      exact congrArg (fun x : (Σ _ : ℕ, Ideal (MR N)) => x.2) heq
    have hsub : Q' ⊆ PP := by
      intro x hx
      rw [hQ'def] at hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      rw [show PP = (Finset.Icc 1 k).sigma SJ from rfl, Finset.mem_sigma]
      exact ⟨Finset.mem_Icc.mpr ⟨hq1 q hq, hqk q hq⟩, (hSJ q.height.toNat q).mpr (hqht q hq)⟩
    have hpt : ∀ q ∈ SI, (if OnGPrime N q then
          ((primLen I q).toNat : ℚ) * rayDeg N D q else 0) ≤ FF ⟨q.height.toNat, q⟩ := by
      intro q hq
      by_cases hadm : OnGPrime N q
      · rw [if_pos hadm]
        change ((primLen I q).toNat : ℚ) * rayDeg N D q ≤
          (if OnGPrime N q ∧ q.height = ((q.height.toNat : ℕ) : ℕ∞) ∧ I ≤ q then
            ((primLen (chainId g q.height.toNat) q).toNat : ℚ) * rayDeg N D q else 0)
        rw [if_pos ⟨hadm, hqf q hq, hqle q hq⟩]
        refine mul_le_mul_of_nonneg_right ?_ (rayDeg_nonneg D q)
        exact_mod_cast ENat.toNat_le_toNat (primLen_mono (hqJ q hq) q)
          (primLen_ne_top (chainId g q.height.toNat) q (hqht q hq))
      · rw [if_neg hadm]
        change (0 : ℚ) ≤ (if OnGPrime N q ∧
            q.height = ((q.height.toNat : ℕ) : ℕ∞) ∧ I ≤ q then
            ((primLen (chainId g q.height.toNat) q).toNat : ℚ) * rayDeg N D q else 0)
        split
        · exact mul_nonneg (by positivity) (rayDeg_nonneg D q)
        · exact le_refl 0
    calc ∑ q ∈ SI, (if OnGPrime N q then ((primLen I q).toNat : ℚ) * rayDeg N D q else 0)
        ≤ ∑ q ∈ SI, FF ⟨q.height.toNat, q⟩ := Finset.sum_le_sum hpt
      _ = ∑ x ∈ Q', FF x := by
          rw [hQ'def]
          exact (Finset.sum_image hinj).symm
      _ ≤ ∑ x ∈ PP, FF x := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => by
          dsimp only [FF]
          split
          · exact mul_nonneg (by positivity) (rayDeg_nonneg D x.2)
          · exact le_refl 0)
      _ = ∑ t ∈ Finset.Icc 1 k, B t := hPPsum
  -- assembly
  have htelk : A k + ∑ t ∈ Finset.Icc 1 k, B t ≤ A 0 := htel k le_rfl
  have hAkn : 0 ≤ A k := hA_nonneg k
  have hle : ∑ t ∈ Finset.Icc 1 k, B t ≤ A 0 := by linarith
  calc Srel N D I ≤ ∑ t ∈ Finset.Icc 1 k, B t := hcoll
    _ ≤ A 0 := hle
    _ = rayDeg N D ⊥ := hA0

end

end Work.BW.RB

