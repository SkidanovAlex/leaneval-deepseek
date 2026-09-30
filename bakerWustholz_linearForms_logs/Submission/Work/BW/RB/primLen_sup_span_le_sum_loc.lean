import Mathlib
import Submission.Work.BW.RB.A4
import Submission.Work.BW.primLen_ne_top
import Submission.Work.BW.primLen_mono
import Submission.Work.BW.primLen_bot
import Submission.Work.BW.BWGradedBase
import Submission.Work.BW.colon_localize_length_add
import Submission.Work.BW.rayDeg_additive
import Submission.Work.BW.RB.locLenAt_sup_inf_le_loc
import Submission.Work.BW.RB.cut_step_le_loc
import Submission.Work.BW.primary_cut_step_chain
import Submission.Work.BW.cut_minimalPrimes
import Submission.Work.BW.isPrimary_of_saturated_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.BW.RB

open Work.BW

section General

variable {R : Type*} [CommRing R]

/-- `locLenAt` is antitone in the ideal: a larger ideal gives a smaller quotient. -/
lemma locLenAt_anti (q : Ideal R) (hq : q.IsPrime) {I J : Ideal R} (h : I ≤ J) :
    locLenAt q hq J ≤ locLenAt q hq I := by
  letI := hq
  have key : ∀ L : Ideal R, locLenAt q hq L = Module.length (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ L.map (algebraMap R (Localization.AtPrime q))) := fun L => rfl
  rw [key J, key I]
  exact Module.length_le_of_surjective (Submodule.factor (Ideal.map_mono h))
    (Submodule.factor_surjective _)

/-- The colon of an ideal by `⊤` is itself. -/
lemma colon_univ_eq (Q : Ideal R) : (Q : Submodule R R).colon Set.univ = Q := by
  ext x
  rw [Submodule.mem_colon]
  constructor
  · intro h; simpa using h 1 (Set.mem_univ 1)
  · intro h y _; simpa using Q.mul_mem_right y h

/-- **Finset subadditivity of the principal cut.**  Iterating `locLenAt_sup_inf_le_loc` across a
finite intersection. -/
lemma finset_inf_sup_le_sum [IsNoetherianRing R] (q : Ideal R) (hq : q.IsPrime) (P : R) :
    ∀ (t : Finset (Ideal R)),
      (∀ I : Finset (Ideal R), I ⊆ t → locLenAt q hq (I.inf id ⊔ Ideal.span {P}) ≠ ⊤) →
      locLenAt q hq (t.inf id ⊔ Ideal.span {P}) ≤
        ∑ Q ∈ t, locLenAt q hq (Q ⊔ Ideal.span {P}) := by
  intro t
  induction t using Finset.induction with
  | empty =>
      intro _
      rw [Finset.sum_empty]
      have htop : (∅ : Finset (Ideal R)).inf id ⊔ Ideal.span {P} = ⊤ := by simp
      rw [htop]
      rw [locLenAt_eq_zero_of_not_le q hq ⊤ (fun h => hq.ne_top (top_le_iff.mp h))]
  | insert a s ha ih =>
      intro hfin
      have hfin_s : ∀ I : Finset (Ideal R), I ⊆ s → locLenAt q hq (I.inf id ⊔ Ideal.span {P}) ≠ ⊤ :=
        fun I hI => hfin I (hI.trans (Finset.subset_insert a s))
      have hfin_pair : locLenAt q hq ((a ⊓ s.inf id) ⊔ Ideal.span {P}) ≠ ⊤ := by
        simpa using hfin ({a} ∪ s) (by simp)
      have hstep := locLenAt_sup_inf_le_loc a (s.inf id) P q hq hfin_pair
      have hih := ih hfin_s
      calc locLenAt q hq ((insert a s).inf id ⊔ Ideal.span {P})
          = locLenAt q hq ((a ⊓ s.inf id) ⊔ Ideal.span {P}) := by
            rw [Finset.inf_insert]
            rfl
        _ ≤ locLenAt q hq (a ⊔ Ideal.span {P}) + locLenAt q hq (s.inf id ⊔ Ideal.span {P}) := hstep
        _ ≤ locLenAt q hq (a ⊔ Ideal.span {P}) + ∑ Q ∈ s, locLenAt q hq (Q ⊔ Ideal.span {P}) :=
            add_le_add le_rfl hih
        _ = ∑ Q ∈ insert a s, locLenAt q hq (Q ⊔ Ideal.span {P}) := by
            rw [Finset.sum_insert ha]

end General

/-- **Multiplicity domination for one primary component**: for `Q` a `p`-primary ideal of a
Noetherian ring `R`, `P ∉ p` and `q` a minimal prime of `Q + (P)`, the local length of `R/(Q+(P))`
at `q` is at most the multiplicity `ℓ_p(Q)` times the local length of `R/(p+(P))` at `q`.
Derived from `cut_step_le_loc` by telescoping along `primary_cut_step_chain`. -/
theorem locLenAt_primary_cut_le_loc {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p Q : Ideal R) (hp : p.IsPrime)
    (hQ : Q.IsPrimary) (hrad : Q.radical = p) (P : R) (hPp : P ∉ p) (q : Ideal R)
    (hq : q ∈ (Q ⊔ Ideal.span {P}).minimalPrimes) :
    locLenAt q hq.isPrime (Q ⊔ Ideal.span {P}) ≤
      locLenAt p hp Q * locLenAt q hq.isPrime (p ⊔ Ideal.span {P}) := by
  haveI : p.IsPrime := hp
  have hq' : q.IsPrime := hq.isPrime
  haveI : q.IsPrime := hq'
  have hQq : Q ≤ q := le_sup_left.trans hq.1.2
  have hpq : p ≤ q := by
    rw [← hrad]
    exact (hq'.isRadical).radical_le_iff.mpr hQq
  have hmin : ∀ r : R, r ∉ p → r ∈ q → q ∈ (p ⊔ Ideal.span {r}).minimalPrimes :=
    fun r hrp hrq => cut_minimalPrimes p Q hp hQ hrad P hPp q hq r hrp hrq
  obtain ⟨k, I, hI0, hIk, hmono, hk, hpJ, hrank, hsat⟩ := primary_cut_step_chain p Q hp hQ hrad
  have hmono' : ∀ i j : Fin (k + 1), i ≤ j → I i ≤ I j := by
    intro i j hij
    rcases lt_or_eq_of_le hij with h | h
    · exact (hmono i j h).le
    · rw [h]
  have hQ_le : ∀ j : Fin (k + 1), Q ≤ I j := by
    intro j; rw [← hI0]; exact hmono' 0 j (Fin.zero_le j)
  have hle_p : ∀ j : Fin (k + 1), j ≠ Fin.last k → I j ≤ p := by
    intro j hj
    by_contra hnp
    obtain ⟨x, hxj, hxp⟩ := Set.not_subset.mp hnp
    have hunit : IsUnit (algebraMap R (Localization.AtPrime p) x) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p x).mpr hxp
    have htop : (I j).map (algebraMap R (Localization.AtPrime p)) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hxj) hunit
    have hjeq : I j = ⊤ := by rw [← hsat j, htop, Ideal.comap_top]
    have hlt : j < Fin.last k := lt_of_le_of_ne (Fin.le_last j) hj
    have hlt' := hmono j (Fin.last k) hlt
    rw [hIk, hjeq] at hlt'
    exact absurd hlt' (lt_irrefl _)
  have hprim : ∀ j : Fin (k + 1), j ≠ Fin.last k → (I j).IsPrimary ∧ (I j).radical = p :=
    fun j hj => isPrimary_of_saturated_le p Q (I j) hp hQ hrad (hQ_le j) (hle_p j hj) (hsat j)
  have hJfun : ∀ i : Fin k,
      (I i.succ).IsPrimary ∧ (I i.succ).radical = p ∨ I i.succ = ⊤ := by
    intro i
    by_cases h : i.succ = Fin.last k
    · right; rw [h]; exact hIk
    · left; exact hprim i.succ h
  have hX0 : locLenAt q hq' (⊤ : Ideal R) = 0 := by
    refine locLenAt_eq_zero_of_not_le q hq' ⊤ ?_
    intro h
    exact hq'.ne_top (top_le_iff.mp h)
  have key : ∀ i : Fin (k + 1),
      locLenAt q hq' (Q ⊔ Ideal.span {P}) ≤
        locLenAt q hq' (I i ⊔ Ideal.span {P}) +
          (i : ℕ) * locLenAt q hq' (p ⊔ Ideal.span {P}) := by
    intro i
    induction i using Fin.induction with
    | zero => simp [hI0]
    | succ j ih =>
      have hlt : j.castSucc < j.succ := by simp [Fin.lt_def]
      have hstep := cut_step_le_loc p q hp hq' hpq P hPp (I j.castSucc) (I j.succ)
        (hmono _ _ hlt).le (hsat j.castSucc) (hsat j.succ) (hpJ j) (hJfun j) hmin (hrank j)
      refine le_trans ih (le_trans (add_le_add hstep le_rfl) ?_)
      rw [Fin.val_succ]
      generalize locLenAt q hq' (I j.succ ⊔ Ideal.span {P}) = A
      generalize locLenAt q hq' (p ⊔ Ideal.span {P}) = X
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc, Fin.val_castSucc,
        add_comm X (((j : ℕ) : ℕ∞) * X)]
  have hlast := key (Fin.last k)
  have hsuptop : (⊤ : Ideal R) ⊔ Ideal.span {P} = ⊤ := sup_eq_left.mpr le_top
  rw [hIk, hsuptop, hX0, zero_add, Fin.val_last, hk] at hlast
  exact hlast


/-- Minimal primes are monotone for the *reverse* order on ideals: if `J ≤ I ≤ q` and `q` is
minimal over `J`, then `q` is minimal over `I`. -/
lemma minimalPrimes_of_le' {R : Type*} [CommRing R] {J I : Ideal R} (hJI : J ≤ I)
    {q : Ideal R} (hq : q ∈ J.minimalPrimes) (hIq : I ≤ q) : q ∈ I.minimalPrimes :=
  ⟨⟨hq.1.1, hIq⟩, fun r hr hrq => hq.2 ⟨hr.1, hJI.trans hr.2⟩ hrq⟩

/-- For a minimal prime `p` of `J` and a minimal prime `q` of `J ⊔ (P)` above `p`, the prime `q`
is minimal over `p ⊔ (P)`. -/
lemma mem_minimalPrimes_sup_span_of_le' {R : Type*} [CommRing R] (J : Ideal R) (P : R)
    (p : Ideal R) (hp : p ∈ J.minimalPrimes) (q : Ideal R)
    (hqK : q ∈ (J ⊔ Ideal.span {P}).minimalPrimes) (hpq : p ≤ q) :
    q ∈ (p ⊔ Ideal.span {P}).minimalPrimes := by
  classical
  refine minimalPrimes_of_le' (J := J ⊔ Ideal.span {P}) (I := p ⊔ Ideal.span {P}) ?_ hqK ?_
  · exact sup_le_sup hp.1.2 le_rfl
  · refine sup_le hpq ?_
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hqK.1.2 (Ideal.mem_sup_right
      (Ideal.mem_span_singleton_self P))))

/-- The associated primes of a submodule agree with those of the quotient module. -/
lemma associatedPrimes_quot_eq' {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) : N.associatedPrimes = associatedPrimes R (M ⧸ N) := by
  have hzero : ∀ y : M, N.mkQ y = 0 ↔ y ∈ N := fun y => by
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  have key : ∀ x : M, N.colon {x} = (⊥ : Submodule R (M ⧸ N)).colon {N.mkQ x} := by
    intro x
    ext r
    rw [Submodule.mem_colon, Submodule.mem_colon]
    constructor
    · intro h s hs
      rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact (hzero (r • x)).mpr (h x (Set.mem_singleton x))
    · intro h s hs
      rw [Set.mem_singleton_iff] at hs
      rw [hs]
      refine (hzero (r • x)).mp ?_
      have hx := h (N.mkQ x) (Set.mem_singleton (N.mkQ x))
      rwa [Submodule.mem_bot, ← map_smul] at hx
  ext I
  rw [Submodule.AssociatePrimes.mem_iff, AssociatedPrimes.mem_iff, Submodule.isAssociatedPrime_def]
  change (I.IsPrime ∧ ∃ x : M, I = (N.colon {x}).radical) ↔
    (⊥ : Submodule R (M ⧸ N)).IsAssociatedPrime I
  rw [Submodule.isAssociatedPrime_def]
  constructor
  · rintro ⟨hp, x, hx⟩
    exact ⟨hp, ⟨N.mkQ x, by rw [← key]; exact hx⟩⟩
  · rintro ⟨hp, x, hx⟩
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective N x
    exact ⟨hp, y, by rw [key]; exact hx⟩

/-- `(a * b).toNat` for finite `a`, `b`. -/
lemma enat_mul_eq_natCast {a b : ℕ∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a * b = ((a.toNat * b.toNat : ℕ) : ℕ∞) := by
  conv_lhs => rw [← ENat.natCast_toNat ha, ← ENat.natCast_toNat hb]
  rw [← ENat.natCast_mul]

/-- `a * b ≠ ⊤` for finite `a`, `b`. -/
lemma enat_mul_ne_top {a b : ℕ∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a * b ≠ ⊤ := by
  rw [enat_mul_eq_natCast ha hb]
  exact ENat.natCast_ne_top _

/-- Multiplication on the right is monotone in the left factor, for finite values. -/
lemma enat_mul_le_mul_right {a a' w : ℕ∞} (h : a ≤ a')
    (ha : a ≠ ⊤) (ha' : a' ≠ ⊤) (hw : w ≠ ⊤) : a * w ≤ a' * w := by
  rw [enat_mul_eq_natCast ha hw, enat_mul_eq_natCast ha' hw]
  exact_mod_cast Nat.mul_le_mul_right _ (ENat.toNat_le_toNat h ha')

/-- The multiplicity inequality for one minimal prime of a cut, with a *local* unmixedness
hypothesis.  Let `q` be a minimal prime of `K = J + (P)` and suppose every associated prime of
`R/J` contained in `q` is a minimal prime of `J`.  Then

  `ℓ_q(K) ≤ ∑_{p ∈ Min J, p ≤ q} ℓ_p(J) · ℓ_q(p + (P))`.

This is `Work.BW.RB.primLen_sup_span_le_sum` (in `RB/srel_cut_unmixed.lean`) with its hypothesis
`hunmixed` (all admissible maximal ideals) replaced by the hypothesis at `q` only, and with no
admissibility of `q`. -/
theorem primLen_sup_span_le_sum_loc {N : ℕ} (J : Ideal (MR N)) (P : MR N)
    (q : Ideal (MR N)) (hq : q ∈ (J ⊔ Ideal.span {P}).minimalPrimes)
    (hloc : ∀ p ∈ associatedPrimes (MR N) (MR N ⧸ J), p ≤ q → p ∈ J.minimalPrimes) :
    ((primLen (J ⊔ Ideal.span {P}) q).toNat : ℚ) ≤
      ∑ᶠ (p : Ideal (MR N)) (_ : p ∈ J.minimalPrimes ∧ p ≤ q),
        (((primLen J p).toNat : ℚ) * ((primLen (p ⊔ Ideal.span {P}) q).toNat : ℚ)) := by
  classical
  have hqp : q.IsPrime := hq.1.1
  have hKq : J ⊔ Ideal.span {P} ≤ q := hq.1.2
  have hspanP : Ideal.span {P} ≤ q := le_trans le_sup_right hKq
  have hPq : P ∈ q := hspanP (Ideal.subset_span (Set.mem_singleton P))
  have hKfin : primLen (J ⊔ Ideal.span {P}) q ≠ ⊤ := primLen_ne_top _ _ hq
  have hKfinL : locLenAt q hqp (J ⊔ Ideal.span {P}) ≠ ⊤ := by
    rwa [primLen_eq_locLenAt] at hKfin
  -- a finite index set for the minimal primes of `J`
  obtain ⟨TJ, hTJ⟩ : ∃ S : Finset (Ideal (MR N)), ∀ p, p ∈ S ↔ p ∈ J.minimalPrimes :=
    ⟨(Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N) J).toFinset,
      fun p => Set.Finite.mem_toFinset (Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N) J)⟩
  -- a minimal primary decomposition of `J`
  obtain ⟨t, ht⟩ : ∃ s : Finset (Ideal (MR N)),
      (J : Submodule (MR N) (MR N)).IsMinimalPrimaryDecomposition s :=
    Submodule.IsLasker.exists_isMinimalPrimaryDecomposition
      (Submodule.isLasker (MR N) (MR N)) (J : Submodule (MR N) (MR N))
  have hJt : ∀ Q ∈ t, J ≤ Q := fun Q hQ => by
    rw [← ht.inf_eq]; exact Finset.inf_le hQ
  -- the associated-prime membership of the radical of a component
  have hradAss_of : ∀ Q ∈ t, Q.radical ∈ associatedPrimes (MR N) (MR N ⧸ J) := by
    intro Q hQ
    have h := ht.mem_associatedPrimes hQ
    rw [colon_univ_eq] at h
    rwa [← associatedPrimes_quot_eq' (J : Submodule (MR N) (MR N))]
  -- Step 1: subadditivity across the intersection
  have hfin_t : ∀ I : Finset (Ideal (MR N)), I ⊆ t →
      locLenAt q hqp (I.inf id ⊔ Ideal.span {P}) ≠ ⊤ := by
    intro I hI
    have h1 : (t.inf id : Ideal (MR N)) ≤ (I.inf id : Ideal (MR N)) :=
      Finset.le_inf (fun a ha => Finset.inf_le (hI ha))
    have hJI : J ≤ I.inf id ⊔ Ideal.span {P} := by
      rw [← ht.inf_eq]
      exact le_trans h1 le_sup_left
    exact ne_top_of_le_ne_top hKfinL (locLenAt_anti q hqp (sup_le hJI le_sup_right))
  have hstep1 : locLenAt q hqp (J ⊔ Ideal.span {P}) ≤
      ∑ Q ∈ t, locLenAt q hqp (Q ⊔ Ideal.span {P}) := by
    have h := finset_inf_sup_le_sum q hqp P t hfin_t
    rwa [ht.inf_eq] at h
  -- Step 2: per-component bound
  have hstep2 : ∀ Q ∈ t, locLenAt q hqp (Q ⊔ Ideal.span {P}) ≤
      (if Q.radical ≤ q then
        primLen J Q.radical * primLen (Q.radical ⊔ Ideal.span {P}) q else 0) := by
    intro Q hQ
    by_cases hradq : Q.radical ≤ q
    · rw [if_pos hradq]
      have hQprim : Q.IsPrimary := ht.primary hQ
      have hradprim : Q.radical.IsPrime := by
        have h := hQprim.isPrime_radical_colon
        rwa [colon_univ_eq] at h
      have hpMin : Q.radical ∈ J.minimalPrimes := hloc _ (hradAss_of Q hQ) hradq
      by_cases hPp : P ∈ Q.radical
      · have hJrad : J ⊔ Ideal.span {P} ≤ Q.radical :=
          sup_le (le_trans (hJt Q hQ) Ideal.le_radical)
            (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hPp))
        have hradq_eq : Q.radical = q := le_antisymm hradq (hq.2 ⟨hradprim, hJrad⟩ hradq)
        have hrad_eq : (Q.radical ⊔ Ideal.span {P}) = q := by
          rw [hradq_eq,
            sup_eq_left.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hPq))]
        have hgoal : primLen J Q.radical * primLen (Q.radical ⊔ Ideal.span {P}) q
            = locLenAt q hqp J := by
          rw [hrad_eq, hradq_eq, primLen_eq_locLenAt J q hqp, primLen_eq_locLenAt q q hqp,
            locLenAt_self q hqp, mul_one]
        rw [hgoal]
        exact locLenAt_anti q hqp (le_trans (hJt Q hQ) le_sup_left)
      · -- `q` is minimal over `Q ⊔ (P)`
        have hqminQ : q ∈ (Q ⊔ Ideal.span {P}).minimalPrimes :=
          ⟨⟨hqp, sup_le (le_trans Ideal.le_radical hradq) hspanP⟩,
            fun r hr hleq => hq.2 ⟨hr.1, sup_le (le_trans (hJt Q hQ) (le_trans le_sup_left hr.2))
              (le_trans le_sup_right hr.2)⟩ hleq⟩
        have hqminR : q ∈ (Q.radical ⊔ Ideal.span {P}).minimalPrimes :=
          ⟨⟨hqp, sup_le hradq hspanP⟩,
            fun r hr hleq =>
              hqminQ.2 ⟨hr.1, sup_le (le_trans Ideal.le_radical (le_trans le_sup_left hr.2))
                (le_trans le_sup_right hr.2)⟩ hleq⟩
        have hb := locLenAt_primary_cut_le_loc (Q.radical) Q hradprim hQprim rfl P hPp q hqminQ
        refine le_trans hb ?_
        have hQmin : Q.radical ∈ Q.minimalPrimes :=
          ⟨⟨hradprim, Ideal.le_radical⟩,
            fun r hr _ => hr.1.radical_le_iff.mpr hr.2⟩
        have h2 : locLenAt (Q.radical) hradprim Q ≠ ⊤ := by
          rw [← primLen_eq_locLenAt Q Q.radical hradprim]
          exact primLen_ne_top Q Q.radical hQmin
        have h3 : primLen J Q.radical ≠ ⊤ := primLen_ne_top J Q.radical hpMin
        have h1 : locLenAt (Q.radical) hradprim Q ≤ primLen J Q.radical := by
          rw [← primLen_eq_locLenAt Q Q.radical hradprim]
          exact primLen_mono (hJt Q hQ) Q.radical
        have h4 : primLen (Q.radical ⊔ Ideal.span {P}) q ≠ ⊤ := primLen_ne_top _ q hqminR
        rw [← primLen_eq_locLenAt (Q.radical ⊔ Ideal.span {P}) q hqminQ.isPrime]
        exact enat_mul_le_mul_right h1 h2 h3 h4
    · rw [if_neg hradq]
      refine le_of_eq ?_
      refine locLenAt_eq_zero_of_not_le q hqp (Q ⊔ Ideal.span {P}) ?_
      intro hle
      exact hradq (hqp.radical_le_iff.mpr (le_trans le_sup_left hle))
  -- Step 3: reindex the sum over the components onto the minimal primes
  have hstep3 : ∑ Q ∈ t, (if Q.radical ≤ q then
        primLen J Q.radical * primLen (Q.radical ⊔ Ideal.span {P}) q else 0) ≤
      ∑ p ∈ TJ, (if p ∈ J.minimalPrimes ∧ p ≤ q then
        primLen J p * primLen (p ⊔ Ideal.span {P}) q else 0) := by
    have hinj : ∀ Q ∈ t, ∀ Q' ∈ t, Q.radical = Q'.radical → Q = Q' := by
      intro Q hQ Q' hQ' h
      by_contra hne
      have hd : Q.radical ≠ Q'.radical := by
        have h := ht.distinct hQ hQ' hne
        simpa only [Function.onFun, colon_univ_eq] using h
      exact hd h
    have hsum1 : ∑ Q ∈ t, (if Q.radical ≤ q then
          primLen J Q.radical * primLen (Q.radical ⊔ Ideal.span {P}) q else 0)
        = ∑ Q ∈ t.filter (fun Q => Q.radical ≤ q),
            (primLen J Q.radical * primLen (Q.radical ⊔ Ideal.span {P}) q) :=
      (Finset.sum_filter (s := t) (fun Q : Ideal (MR N) => Q.radical ≤ q)
        (fun Q : Ideal (MR N) =>
          primLen J Q.radical * primLen (Q.radical ⊔ Ideal.span {P}) q)).symm
    have hsum2 : ∑ Q ∈ t.filter (fun Q => Q.radical ≤ q),
            (primLen J Q.radical * primLen (Q.radical ⊔ Ideal.span {P}) q)
        = ∑ p ∈ (t.filter (fun Q => Q.radical ≤ q)).image (fun Q => Q.radical),
            (primLen J p * primLen (p ⊔ Ideal.span {P}) q) :=
      (Finset.sum_image (s := t.filter (fun Q : Ideal (MR N) => Q.radical ≤ q))
        (f := fun p => primLen J p * primLen (p ⊔ Ideal.span {P}) q)
        (g := fun Q : Ideal (MR N) => Q.radical)
        (fun x hx y hy hxy =>
          hinj x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy)).symm
    rw [hsum1, hsum2]
    have hif : ∀ p ∈ (t.filter (fun Q => Q.radical ≤ q)).image (fun Q => Q.radical),
        (primLen J p * primLen (p ⊔ Ideal.span {P}) q)
          = (if p ∈ J.minimalPrimes ∧ p ≤ q then
              primLen J p * primLen (p ⊔ Ideal.span {P}) q else 0) := by
      intro p hp
      obtain ⟨Q, hQ, hQeq⟩ := Finset.mem_image.mp hp
      have hQq : Q.radical ≤ q := (Finset.mem_filter.mp hQ).2
      have hQmem : Q ∈ t := (Finset.mem_filter.mp hQ).1
      rw [← hQeq, if_pos ⟨hloc _ (hradAss_of Q hQmem) hQq, hQq⟩]
    rw [Finset.sum_congr rfl hif]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      obtain ⟨Q, hQ, hQeq⟩ := Finset.mem_image.mp hp
      have hQq : Q.radical ≤ q := (Finset.mem_filter.mp hQ).2
      have hQmem : Q ∈ t := (Finset.mem_filter.mp hQ).1
      rw [← hQeq]
      exact (hTJ _).mpr (hloc _ (hradAss_of Q hQmem) hQq)
    · intro p hpT hpnot
      by_cases hc : p ∈ J.minimalPrimes ∧ p ≤ q
      · rw [if_pos hc]; exact zero_le
      · rw [if_neg hc]
  have hnat : locLenAt q hqp (J ⊔ Ideal.span {P}) ≤
      ∑ p ∈ TJ, (if p ∈ J.minimalPrimes ∧ p ≤ q then
        primLen J p * primLen (p ⊔ Ideal.span {P}) q else 0) :=
    le_trans hstep1 (le_trans (Finset.sum_le_sum hstep2) hstep3)
  -- Step 4: pass to `toNat` and to `ℚ`
  have hfin_terms : ∀ p ∈ TJ, (if p ∈ J.minimalPrimes ∧ p ≤ q then
        primLen J p * primLen (p ⊔ Ideal.span {P}) q else 0) ≠ ⊤ := by
    intro p _
    by_cases hc : p ∈ J.minimalPrimes ∧ p ≤ q
    · rw [if_pos hc]
      exact enat_mul_ne_top (primLen_ne_top J p hc.1)
        (primLen_ne_top _ q (mem_minimalPrimes_sup_span_of_le' J P p hc.1 q hq hc.2))
    · rw [if_neg hc]; exact ENat.natCast_ne_top 0
  have hSum_ne : (∑ p ∈ TJ, (if p ∈ J.minimalPrimes ∧ p ≤ q then
        primLen J p * primLen (p ⊔ Ideal.span {P}) q else 0)) ≠ ⊤ :=
    ENat.sum_ne_top.mpr hfin_terms
  have htoNat : (locLenAt q hqp (J ⊔ Ideal.span {P})).toNat ≤
      (∑ p ∈ TJ, (if p ∈ J.minimalPrimes ∧ p ≤ q then
        primLen J p * primLen (p ⊔ Ideal.span {P}) q else 0)).toNat :=
    ENat.toNat_le_toNat hnat hSum_ne
  rw [primLen_eq_locLenAt (J ⊔ Ideal.span {P}) q hqp]
  rw [finsum_cond_eq_sum (fun p : Ideal (MR N) => p ∈ J.minimalPrimes ∧ p ≤ q) TJ
    (fun a ha => (hTJ a).mpr ha.1)]
  have hcast : (∑ p ∈ TJ, (if p ∈ J.minimalPrimes ∧ p ≤ q then
        (((primLen J p).toNat : ℚ) * ((primLen (p ⊔ Ideal.span {P}) q).toNat : ℚ)) else 0))
      = ((∑ p ∈ TJ, (if p ∈ J.minimalPrimes ∧ p ≤ q then
        primLen J p * primLen (p ⊔ Ideal.span {P}) q else 0)).toNat : ℚ) := by
    rw [ENat.toNat_sum hfin_terms, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    by_cases hc : p ∈ J.minimalPrimes ∧ p ≤ q
    · rw [if_pos hc, if_pos hc, ENat.toNat_mul, Nat.cast_mul]
    · rw [if_neg hc, if_neg hc]; norm_num
  rw [hcast]
  exact_mod_cast htoNat

end Work.BW.RB
