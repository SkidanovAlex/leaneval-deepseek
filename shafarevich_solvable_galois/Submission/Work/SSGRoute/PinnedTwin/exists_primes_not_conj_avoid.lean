import Mathlib
import Submission.Work.SSGRoute.PinnedTwin.Shim
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Primes of a number field avoiding a finite set and an involution

`Work.SSGRoute.PinnedTwin.exists_primes_not_conj_avoid`: for a finite Galois extension `k ⊆ K` of
number fields, an involution `ρ ∈ Gal(K/k)` (`ρ ^ 2 = 1`), a natural number `N` and a finite set
`Bad` of finite places of `K`, there is a finite set `s` of `N` finite places of `K` such that

* no element of `s` is in `Bad`;
* no element of `s` divides `2`;
* `s` contains no prime together with its `ρ`-translate, unless that translate is the prime itself
  (i.e. `ρ q = q` for `q`, `ρ q ∈ s`).

The proof splits into three independent ingredients:

* `infinite_heightOneSpectrum_ringOfIntegers` — `𝓞 K` has infinitely many nonzero prime ideals
  (for each rational prime `p`, a maximal ideal of `𝓞 K` lies over `(p) ⊆ ℤ`, and distinct
  rational primes give distinct ideals because a prime ideal containing two coprime integers
  contains `1`);
* `finite_setOf_two_mem_asIdeal` — only finitely many primes contain `2`, since they all divide
  the nonzero ideal `(2)` (`Ideal.finite_factors`);
* `exists_finset_card_subset_of_invol` — a purely combinatorial selection lemma: inside an infinite
  set, a self-inverse map `f` admits a subset of any prescribed finite cardinality with no two
  distinct elements exchanged by `f`.

Removing `Bad` and the primes dividing `2` from the infinite set of all primes keeps it infinite,
and the selection lemma applied to `placeSmul ρ` (an involution by `placeSmul_mul`, `placeSmul_one`)
produces `s`.
-/

namespace Work.SSGRoute.PinnedTwin

open IsDedekindDomain

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-- **There are infinitely many nonzero prime ideals in the ring of integers of a number field.**

For every rational prime `p` there is a maximal ideal `Q` of `𝓞 K` with `Q.LiesOver (p)`, hence
`p ∈ Q`; two distinct rational primes `p, p'` give distinct ideals, since a prime ideal containing
both would contain a `ℤ`-linear combination `1 = ap + bp'`. -/
lemma infinite_heightOneSpectrum_ringOfIntegers (K : Type) [Field K] [NumberField K] :
    Infinite (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) := by
  haveI hInt : Algebra.IsIntegral ℤ (NumberField.RingOfIntegers K) := inferInstance
  haveI hFa : FaithfulSMul ℤ (NumberField.RingOfIntegers K) := inferInstance
  have hinf : Infinite {p : ℕ // p.Prime} := Nat.infinite_setOfPred_prime.to_subtype
  -- the ideal `(p) ⊆ ℤ` is nonzero
  have hspan_ne : ∀ p : {p : ℕ // p.Prime},
      Ideal.span {(p.1 : ℤ)} ≠ (⊥ : Ideal ℤ) := by
    intro p h
    have hm : (p.1 : ℤ) ∈ (⊥ : Ideal ℤ) := by
      rw [← h]; exact Ideal.mem_span_singleton_self _
    rw [Submodule.mem_bot] at hm
    exact p.2.ne_zero (Int.natCast_eq_zero.mp hm)
  -- a maximal ideal of `𝓞 K` over each `(p)`
  have hchoice : ∀ p : {p : ℕ // p.Prime},
      ∃ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        (algebraMap ℤ (NumberField.RingOfIntegers K) (p.1 : ℤ)) ∈ q.asIdeal := by
    intro p
    haveI : (Ideal.span {(p.1 : ℤ)}).IsMaximal := by
      refine Ideal.IsPrime.isMaximal ?_ (hspan_ne p)
      rw [Ideal.span_singleton_prime (by have := p.2.two_le; omega)]
      exact Nat.prime_iff_prime_int.mp p.2
    obtain ⟨Q, hQmax, hQlies⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (R := ℤ) (S := NumberField.RingOfIntegers K) (Ideal.span {(p.1 : ℤ)})
    haveI := hQlies
    have hover : Ideal.span {(p.1 : ℤ)} = Ideal.under ℤ Q := Ideal.LiesOver.over
    have hunder : (p.1 : ℤ) ∈ Ideal.under ℤ Q := by
      rw [← hover]; exact Ideal.mem_span_singleton_self _
    have hmem : (algebraMap ℤ (NumberField.RingOfIntegers K) (p.1 : ℤ)) ∈ Q :=
      (Ideal.mem_under ℤ Q).mp hunder
    exact ⟨⟨Q, hQmax.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot (hspan_ne p) Q⟩, hmem⟩
  let f : {p : ℕ // p.Prime} → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    fun p => Classical.choose (hchoice p)
  have hf : ∀ p, (algebraMap ℤ (NumberField.RingOfIntegers K) (p.1 : ℤ)) ∈ (f p).asIdeal :=
    fun p => Classical.choose_spec (hchoice p)
  refine Infinite.of_injective f ?_
  intro p p' hpp
  by_contra hne
  have hcop : Nat.Coprime p.1 p'.1 :=
    (Nat.coprime_primes p.2 p'.2).mpr (fun he => hne (Subtype.ext he))
  obtain ⟨a, b, hab⟩ := (hcop.isCoprime.map (algebraMap ℤ (NumberField.RingOfIntegers K)))
  have h1 : (1 : NumberField.RingOfIntegers K) ∈ (f p).asIdeal := by
    rw [← hab]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
    · exact hf p
    · exact hpp ▸ hf p'
  have htop : (f p).asIdeal = ⊤ := Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one
  exact (f p).isPrime.ne_top htop

/-- **Only finitely many nonzero prime ideals of `𝓞 K` contain `2`.**

All of them divide the nonzero ideal `(2)`, and only finitely many prime ideals divide a given
nonzero ideal. -/
lemma finite_setOf_two_mem_asIdeal (K : Type) [Field K] [NumberField K] :
    {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
      (2 : NumberField.RingOfIntegers K) ∈ q.asIdeal}.Finite := by
  have h2 : (2 : NumberField.RingOfIntegers K) ≠ 0 := two_ne_zero
  refine (Ideal.finite_factors (I := Ideal.span {(2 : NumberField.RingOfIntegers K)}) ?_).subset ?_
  · simpa [Ideal.span_singleton_eq_bot] using h2
  · intro q hq
    simp only [Set.mem_ofPred_eq] at hq ⊢
    exact Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_iff_mem _ |>.mpr hq)

/-- **Combinatorial selection lemma.**  For a self-inverse map `f` of a type `α` and an infinite set
`X ⊆ α`, every `N` admits an `N`-element subset `s ⊆ X` that is *`f`-free* in the sense that
`f x ∈ s ⟹ f x = x` for every `x ∈ s`.  (Equivalently: `s` contains no two distinct elements
exchanged by `f`.)

The proof is the greedy construction: pick `x ∈ X`, delete the pair `{x, f x}` from `X`, recurse,
and add `x` back; deleting two points of an infinite set leaves it infinite. -/
lemma exists_finset_card_subset_of_invol {α : Type*} (f : α → α) (hf : ∀ x, f (f x) = x)
    (X : Set α) (hX : X.Infinite) (N : ℕ) :
    ∃ s : Finset α, s.card = N ∧ (↑s : Set α) ⊆ X ∧ ∀ x ∈ s, f x ∈ s → f x = x := by
  classical
  suffices H : ∀ M : ℕ, ∀ X : Set α, X.Infinite →
      ∃ s : Finset α, s.card = M ∧ (↑s : Set α) ⊆ X ∧ ∀ x ∈ s, f x ∈ s → f x = x from
    H N X hX
  intro M
  induction M with
  | zero => intro X _; exact ⟨∅, rfl, by simp, by simp⟩
  | succ n ih =>
    intro X hX
    obtain ⟨x, hx⟩ := hX.nonempty
    have hpair : ({x, f x} : Set α).Finite := Set.Finite.insert x (Set.finite_singleton (f x))
    have hX' : (X \ ({x, f x} : Set α)).Infinite := hX.sdiff hpair
    obtain ⟨s, hcard, hsub, hprop⟩ := ih _ hX'
    have hxmem : x ∈ ({x, f x} : Set α) := Set.mem_insert x {f x}
    have hxnot : x ∉ s := fun h => (hsub (by simpa using h)).2 hxmem
    refine ⟨insert x s, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hxnot, hcard]
    · intro y hy
      rw [Finset.mem_coe, Finset.mem_insert] at hy
      rcases hy with hyx | hy
      · rw [hyx]; exact hx
      · exact (hsub (by simpa using hy)).1
    · intro y hy hfy
      have hfxmem : f x ∈ ({x, f x} : Set α) := Set.mem_insert_of_mem x rfl
      rw [Finset.mem_insert] at hy hfy
      rcases hy with hyx | hy
      · subst hyx
        rcases hfy with hfyx | hfy
        · exact hfyx
        · exact absurd hfxmem (hsub (by simpa using hfy)).2
      · rcases hfy with hfyx | hfy
        · have hyx' : y = f x := by rw [← hf y, hfyx]
          have hmem : y ∈ ({x, f x} : Set α) := by
            rw [hyx']; exact Set.mem_insert_of_mem x rfl
          exact absurd hmem (hsub (by simpa using hy)).2
        · exact hprop y hy (by simpa using hfy)

/-- **The target lemma.**  For a finite Galois extension `k ⊆ K` of number fields, an involution
`ρ ∈ Gal(K/k)`, a natural number `N` and a finite set `Bad` of finite places of `K`, there are `N`
finite places of `K`, none in `Bad`, none dividing `2`, and no two of which are exchanged by `ρ`
unless they are equal. -/
theorem exists_primes_not_conj_avoid {k K : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1) (N : ℕ)
    (Bad : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    ∃ s : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), s.card = N ∧
      (∀ q ∈ s, q ∉ Bad) ∧ (∀ q ∈ s, (2 : NumberField.RingOfIntegers K) ∉ q.asIdeal) ∧
      (∀ q ∈ s,
        Commons.NumberTheory.NumberField.Completion.placeSmul ρ q ∈ s →
          Commons.NumberTheory.NumberField.Completion.placeSmul ρ q = q) := by
  classical
  haveI := infinite_heightOneSpectrum_ringOfIntegers K
  -- the `ρ`-translate map is an involution
  have hρρ : ρ * ρ = 1 := by rw [← pow_two, hρ2]
  have hinvol : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      Commons.NumberTheory.NumberField.Completion.placeSmul ρ
        (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q) = q := by
    intro q
    rw [← Commons.NumberTheory.NumberField.Completion.placeSmul_mul, hρρ,
      Commons.NumberTheory.NumberField.Completion.placeSmul_one]
  -- the admissible places form an infinite set
  have hZfin : ((↑Bad : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) ∪
        {q | (2 : NumberField.RingOfIntegers K) ∈ q.asIdeal}).Finite :=
    Bad.finite_toSet.union (finite_setOf_two_mem_asIdeal K)
  have hXinf : {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
      q ∉ Bad ∧ (2 : NumberField.RingOfIntegers K) ∉ q.asIdeal}.Infinite := by
    have h := (Set.infinite_univ (α := IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))).sdiff hZfin
    have heq : {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
        q ∉ Bad ∧ (2 : NumberField.RingOfIntegers K) ∉ q.asIdeal}
        = Set.univ \ ((↑Bad : Set (IsDedekindDomain.HeightOneSpectrum
            (NumberField.RingOfIntegers K))) ∪
          {q | (2 : NumberField.RingOfIntegers K) ∈ q.asIdeal}) := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_univ, true_and, Set.mem_union,
        Finset.mem_coe, not_or]
    rw [heq]
    exact h
  obtain ⟨s, hcard, hsub, hprop⟩ :=
    exists_finset_card_subset_of_invol
      (Commons.NumberTheory.NumberField.Completion.placeSmul ρ) hinvol _ hXinf N
  refine ⟨s, hcard, ?_, ?_, ?_⟩
  · intro q hq
    exact (hsub (by simpa using hq)).1
  · intro q hq
    exact (hsub (by simpa using hq)).2
  · intro q hq hmem
    exact hprop q hq hmem

end Work.SSGRoute.PinnedTwin
