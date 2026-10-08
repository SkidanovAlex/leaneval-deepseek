/-
# BMAX — elementary reductions for "`F(A)` is Dedekind" (Bender 17i, `hnot` form)

This file collects the *elementary* ingredients of the reduction of

  `Bender17i_fitting_dedekind_hnot` :
    `G` finite simple, `A` coatomic, `F*(A)` not a `p`-group for any prime `p`
      ⟹  every subgroup of `F(A)` is normalised by `F(A)` (i.e. `F(A)` is Dedekind),

to its two genuine cases.

## Contents

* `Work.BMAX.DedekindIn K` : the conclusion shape "every subgroup of `K` is normalised by `K`".
* `pCoreIn_le_fittingIn` : `O_p(A) ≤ F(A)`.
* `le_normalizer_pCoreIn` : `A` normalises `O_p(A)`.
* `normalizer_pCoreIn_eq` : for `hA` coatomic, `hG` simple and `O_p(A) ≠ 1`, the normalizer
  `N_G(O_p(A))` is exactly `A`.
* `pCoreIn_eq_bot_iff_mem_primesOf` : `O_q(A) = 1 ↔ q ∉ π(F(A))`
  (a restatement of the proved `Work.BMAX.pCoreIn_eq_bot_iff_not_mem_primesOf`).
* `not_isPGroup_fittingIn_of_two_pCoreIn` : two distinct primes `p ≠ q` with `O_p(A) ≠ 1 ≠ O_q(A)`
  force `F(A)` to be a `p`-group for no prime.
* `fittingIn_isPGroup_of_unique_pCore` : if `O_q(A) = 1` for all primes `q ≠ p`, then `F(A)` is a
  `p`-group.

These are used by `Work.BMAX.Bender17i_fitting_dedekind_hnot` and are made available (via
`depends_on`) to the two case lemmas of that theorem.
-/
import Mathlib
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.Basic
import Submission.Work.BMAX.centralizer_pResidualIn_witness_le
import Submission.Work.BMAX.pCoreIn_eq_bot_iff_not_mem_primesOf

set_option linter.style.haveILetI false

namespace Work.BMAX

open Subgroup

/-- **`K` is Dedekind inside the ambient group `G`**: `K` normalises every subgroup of `K`.

For `K = F(A)` this is exactly the conclusion of `Bender17i_fitting_dedekind_hnot`. -/
def DedekindIn {G : Type*} [Group G] (K : Subgroup G) : Prop :=
  ∀ X : Subgroup G, X ≤ K → K ≤ Subgroup.normalizer (X : Set G)

/-- `⊥` is Dedekind. -/
theorem dedekindIn_bot {G : Type*} [Group G] : DedekindIn (⊥ : Subgroup G) :=
  fun _ _ => bot_le

/-- A Dedekind subgroup restricts: if `K` is Dedekind and `L ≤ K`, then `L` is Dedekind. -/
theorem DedekindIn.mono {G : Type*} [Group G] {K L : Subgroup G} (h : DedekindIn K) (hLK : L ≤ K) :
    DedekindIn L :=
  fun X hX => hLK.trans (h X (hX.trans hLK))

/-- **`K` is Dedekind as soon as it normalises all its cyclic subgroups.**

Indeed if `K ≤ N_G(⟨x⟩)` for every `x ∈ K`, then for `g ∈ K` and `x ∈ X ≤ K` we get
`g * x * g⁻¹ ∈ ⟨x⟩ ≤ X`.  Hence a proof of Dedekindness may restrict attention to cyclic
subgroups. -/
theorem dedekindIn_of_forall_zpowers {G : Type*} [Group G] {K : Subgroup G}
    (h : ∀ x : G, x ∈ K →
      K ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G)) :
    DedekindIn K := by
  intro X hX
  rw [Subgroup.le_normalizer_iff]
  intro g hg x hx
  have hxK : x ∈ K := hX hx
  have hgN : g ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := h x hxK hg
  have hmem : g * x * g⁻¹ ∈ Subgroup.zpowers x :=
    (Subgroup.mem_normalizer_iff.mp hgN x).mp (Subgroup.mem_zpowers x)
  exact (Subgroup.zpowers_le.mpr hx) hmem

/-- `O_p(A) ≤ F(A)`. -/
theorem pCoreIn_le_fittingIn {G : Type*} [Group G] [Finite G] (A : Subgroup G) {p : ℕ}
    (hp : p.Prime) : Work.GW2.pCoreIn p A ≤ Work.GW2.fittingIn A := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Work.GW2.pCoreIn, Work.GW2.fittingIn]
  refine Subgroup.map_mono ?_
  -- `O_p(↥A) ≤ F(↥A)`: a normal `p`-subgroup is normal and nilpotent.
  rw [Work.GW2.pCore, Work.GW2.fitting]
  exact Subgroup.normalCore_mono
    (sSup_le fun N hN => le_sSup ⟨hN.1, hN.2.isNilpotent⟩)

/-- `A` normalises `O_p(A)`. -/
theorem le_normalizer_pCoreIn {G : Type*} [Group G] (A : Subgroup G) (p : ℕ) :
    A ≤ Subgroup.normalizer ((Work.GW2.pCoreIn p A : Subgroup G) : Set G) := by
  rw [Work.GW2.pCoreIn]
  exact le_normalizer_map_subtype_of_normal (Work.GW2.pCore_normal p ↥A)

/-- For a coatomic `A` of a finite simple group and `O_p(A) ≠ 1`, the normalizer of `O_p(A)` is
exactly `A`: `O_p(A)` is normal in `A` and not normal in `G`. -/
theorem normalizer_pCoreIn_eq {G : Type*} [Group G] [Finite G] (hG : IsSimpleGroup G)
    {A : Subgroup G} (hA : IsCoatom A) {p : ℕ} (hne : Work.GW2.pCoreIn p A ≠ ⊥) :
    Subgroup.normalizer ((Work.GW2.pCoreIn p A : Subgroup G) : Set G) = A := by
  have hle := le_normalizer_pCoreIn A p
  rcases lt_or_eq_of_le hle with hlt | heq
  · -- the normalizer is above the coatom `A`, hence everything; `O_p(A)` would be normal in `G`
    have htop : Subgroup.normalizer ((Work.GW2.pCoreIn p A : Subgroup G) : Set G) = ⊤ :=
      hA.lt_iff.mp hlt
    have hnormal : (Work.GW2.pCoreIn p A).Normal :=
      Subgroup.normalizer_eq_top_iff.mp htop
    haveI := hnormal
    have hZle : Work.GW2.pCoreIn p A ≤ A :=
      Subgroup.map_subtype_le (Work.GW2.pCore p ↥A)
    rcases hG.eq_bot_or_eq_top_of_normal (Work.GW2.pCoreIn p A) with h | h
    · exact absurd h hne
    · exact absurd (h ▸ hZle) (fun htop' => hA.1 (top_le_iff.mp htop'))
  · exact heq.symm

/-- `O_q(A) = ⊥ ↔ q ∉ π(F(A))` (restatement of the proved leaf, kept here so that the two case
lemmas of `Bender17i_fitting_dedekind_hnot` can cite it without importing the `CORE3` leaf). -/
theorem pCoreIn_eq_bot_iff_mem_primesOf {G : Type} [Group G] [Finite G] (A : Subgroup G)
    {q : ℕ} (hq : q.Prime) :
    Work.GW2.pCoreIn q A = ⊥ ↔ q ∉ Work.GW2.primesOf (Work.GW2.fittingIn A) :=
  Work.BMAX.pCoreIn_eq_bot_iff_not_mem_primesOf A q hq

/-- **`O_p(A) ≠ 1` for two distinct primes makes `F(A)` a `p`-group for no prime.**

`p` and `q` both divide `|F(A)|`, so `|F(A)|` is a power of no single prime. -/
theorem not_isPGroup_fittingIn_of_two_pCoreIn {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpA : Work.GW2.pCoreIn p A ≠ ⊥) (hqA : Work.GW2.pCoreIn q A ≠ ⊥) :
    ∀ r : ℕ, r.Prime → ¬ IsPGroup r ↥(Work.GW2.fittingIn A) := by
  have hpmem : p ∈ Work.GW2.primesOf (Work.GW2.fittingIn A) := by
    by_contra hb
    exact hpA ((pCoreIn_eq_bot_iff_mem_primesOf A hp).mpr hb)
  have hqmem : q ∈ Work.GW2.primesOf (Work.GW2.fittingIn A) := by
    by_contra hb
    exact hqA ((pCoreIn_eq_bot_iff_mem_primesOf A hq).mpr hb)
  have hpdvd : p ∣ Nat.card ↥(Work.GW2.fittingIn A) := (Nat.mem_primeFactors.mp hpmem).2.1
  have hqdvd : q ∣ Nat.card ↥(Work.GW2.fittingIn A) := (Nat.mem_primeFactors.mp hqmem).2.1
  intro r hr hrg
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hrg
  have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow (hn ▸ hpdvd))
  have hqr : q = r := (Nat.prime_dvd_prime_iff_eq hq hr).mp (hq.dvd_of_dvd_pow (hn ▸ hqdvd))
  exact hpq (hpr.trans hqr.symm)

/-- **If `O_q(A) = 1` for every prime `q ≠ p`, then `F(A)` is a `p`-group.** -/
theorem fittingIn_isPGroup_of_unique_pCore {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {p : ℕ} (hp : p.Prime) (h : ∀ q : ℕ, q.Prime → q ≠ p → Work.GW2.pCoreIn q A = ⊥) :
    IsPGroup p ↥(Work.GW2.fittingIn A) := by
  rw [isPGroup_iff_primeFactors_card_subset hp.ne_zero]
  intro q hq
  have hqprime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
  have hqmem : q ∈ Work.GW2.primesOf (Work.GW2.fittingIn A) := hq
  have hqne : Work.GW2.pCoreIn q A ≠ ⊥ := fun hbot =>
    ((pCoreIn_eq_bot_iff_mem_primesOf A hqprime).mp hbot) hqmem
  by_cases hqp : q = p
  · rw [hqp, hp.primeFactors]; exact Finset.mem_singleton_self p
  · exact absurd (h q hqprime hqp) hqne

end Work.BMAX
