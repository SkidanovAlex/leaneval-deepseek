import Mathlib
import Submission.Work.BW.unmixed_regSeq
import Submission.Work.BW.mvpoly_local_regSeq
import Submission.Work.BW.RB.associatedPrimes_quotient_ofList_eq_minimalPrimes
import Submission.Work.BW.RB.exists_mem_notMem_minimalPrimes
import Submission.Work.BW.RB.ge_height_ofList_append_singleton


namespace Work.BW.RB

/-- If `(ofList f).height = f.length` then every minimal prime over `ofList f` has height
`f.length`.  (Included here since it is needed for the induction below.) -/
private theorem height_eq_length_of_mem_minimalPrimes_ofList {R : Type*} [CommRing R]
    [IsNoetherianRing R] [DecidableEq R]
    (f : List R) {Q : Ideal R} (hQ : Q ∈ (Ideal.ofList f).minimalPrimes)
    (hht : (Ideal.ofList f).height = (f.length : ℕ∞)) :
    Q.height = (f.length : ℕ∞) := by
  have hspan : Ideal.span ((f.toFinset : Finset R) : Set R) = Ideal.ofList f := by
    rw [List.coe_toFinset]
  have hQ' : Q ∈ (Ideal.span ((f.toFinset : Finset R) : Set R)).minimalPrimes := by
    rw [hspan]; exact hQ
  refine le_antisymm ?_ ?_
  · exact (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hQ').trans
      (Nat.cast_le.mpr (List.toFinset_card_le f))
  · rw [← hht, Ideal.height_eq_inf_minimalPrimes]
    exact iInf₂_le Q hQ

/-- One induction step: given a regular sequence `f` of length `k` inside `p` whose ideal has
height `k`, and `k < ht p`, extend it by a suitable `x ∈ p`. -/
private theorem step {σ : Type*} [Fintype σ]
    (𝔪 : Ideal (MvPolynomial σ ℂ)) [𝔪.IsMaximal]
    (p : Ideal (Localization.AtPrime 𝔪)) [Ideal.IsPrime p]
    (f : List (Localization.AtPrime 𝔪)) (k : ℕ)
    (hlen : f.length = k)
    (hle : Ideal.ofList f ≤ p)
    (hht : (Ideal.ofList f).height = (k : ℕ∞))
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime 𝔪) f)
    (hk : k < p.height) :
    ∃ x ∈ p,
      (Ideal.ofList (f ++ [x])).height = (k : ℕ∞) + 1 ∧
      RingTheory.Sequence.IsRegular (Localization.AtPrime 𝔪) (f ++ [x]) := by
  classical
  haveI : IsNoetherianRing (Localization.AtPrime 𝔪) := inferInstance
  haveI : Nontrivial (Localization.AtPrime 𝔪) := inferInstance
  have hpne : p ≠ ⊤ := (inferInstance : Ideal.IsPrime p).ne_top
  have hpmax : p ≤ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪) :=
    IsLocalRing.le_maximalIdeal hpne
  have hmemf : ∀ y ∈ f, y ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪) :=
    fun y hy => hpmax (hle (Ideal.subset_span hy))
  -- heights of the minimal primes
  have hminht : ∀ Q ∈ (Ideal.ofList f).minimalPrimes, Q.height = (k : ℕ∞) := fun Q hQ => by
    have := height_eq_length_of_mem_minimalPrimes_ofList f (Q := Q) hQ (by rw [hlen]; exact hht)
    rwa [hlen] at this
  -- prime avoidance
  have hex : ∃ x ∈ p, ∀ Q ∈ (Ideal.ofList f).minimalPrimes, x ∉ Q :=
    exists_mem_notMem_minimalPrimes (I := Ideal.ofList f) (p := p)
      (fun Q hQ => by rw [hminht Q hQ]; exact hk)
  obtain ⟨x, hxp, hxavoid⟩ := hex
  -- lower bound on the height
  have hge : (k : ℕ∞) + 1 ≤ (Ideal.ofList (f ++ [x])).height :=
    ge_height_ofList_append_singleton (k := k) hminht hxavoid
  -- upper bound on the height
  have hset : ((f.toFinset ∪ {x} : Finset (Localization.AtPrime 𝔪)) :
      Set (Localization.AtPrime 𝔪)) = {y | y ∈ f ++ [x]} := by
    ext y
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_singleton, List.mem_toFinset,
      Set.mem_ofPred_eq, List.mem_append, List.mem_singleton]
  have hspan_eq : Ideal.span ((f.toFinset ∪ {x} : Finset (Localization.AtPrime 𝔪)) :
      Set (Localization.AtPrime 𝔪)) = Ideal.ofList (f ++ [x]) := by
    rw [hset]
  have hle_p : Ideal.ofList (f ++ [x]) ≤ p := by
    rw [Ideal.ofList_append, Ideal.ofList_singleton]
    refine sup_le hle ?_
    rw [Ideal.span_le]
    rintro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]; exact hxp
  have hne : Ideal.ofList (f ++ [x]) ≠ ⊤ := ne_top_of_le_ne_top hpne hle_p
  have hle_succ : (Ideal.ofList (f ++ [x])).height ≤ (k : ℕ∞) + 1 := by
    have hne' : Ideal.span ((f.toFinset ∪ {x} : Finset (Localization.AtPrime 𝔪)) :
        Set (Localization.AtPrime 𝔪)) ≠ ⊤ := by
      rw [hspan_eq]; exact hne
    have hc := Ideal.height_span_le_card_of_span_ne_top (R := Localization.AtPrime 𝔪)
      (s := f.toFinset ∪ {x}) hne'
    have hcard : (f.toFinset ∪ {x} : Finset (Localization.AtPrime 𝔪)).card ≤ k + 1 := by
      have h1 : (f.toFinset ∪ {x} : Finset (Localization.AtPrime 𝔪)).card
          ≤ f.toFinset.card + ({x} : Finset (Localization.AtPrime 𝔪)).card :=
        Finset.card_union_le _ _
      rw [Finset.card_singleton] at h1
      have h2 : f.toFinset.card ≤ k := by rw [← hlen]; exact List.toFinset_card_le f
      omega
    calc (Ideal.ofList (f ++ [x])).height
        = (Ideal.span ((f.toFinset ∪ {x} : Finset (Localization.AtPrime 𝔪)) :
            Set (Localization.AtPrime 𝔪))).height := by rw [hspan_eq]
      _ ≤ ((f.toFinset ∪ {x} : Finset (Localization.AtPrime 𝔪)).card : ℕ∞) := hc
      _ ≤ ((k + 1 : ℕ) : ℕ∞) := by exact_mod_cast hcard
      _ = (k : ℕ∞) + 1 := by rw [Nat.cast_add, Nat.cast_one]
  -- regularity
  have hmem' : ∀ y ∈ f ++ [x], y ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪) := by
    intro y hy
    rw [List.mem_append] at hy
    rcases hy with hy | hy
    · exact hmemf y hy
    · rw [List.mem_singleton] at hy
      rw [hy]; exact hpmax hxp
  have hreg' : RingTheory.Sequence.IsRegular (Localization.AtPrime 𝔪) (f ++ [x]) := by
    rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem']
    rw [RingTheory.Sequence.isWeaklyRegular_append_iff]
    refine ⟨hreg.1, ?_⟩
    rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    have hkey : (Ideal.ofList f • ⊤ : Submodule (Localization.AtPrime 𝔪)
        (Localization.AtPrime 𝔪)) = ((Ideal.ofList f : Ideal (Localization.AtPrime 𝔪)) :
        Submodule (Localization.AtPrime 𝔪) (Localization.AtPrime 𝔪)) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    rw [hkey]
    have hass : ∀ q ∈ associatedPrimes (Localization.AtPrime 𝔪)
          (Localization.AtPrime 𝔪 ⧸ Ideal.ofList f), x ∉ q := by
      intro q hq
      have hqmin : q ∈ (Ideal.ofList f).minimalPrimes :=
        associatedPrimes_quotient_ofList_eq_minimalPrimes 𝔪 f hmemf hreg ▸ hq
      exact hxavoid q hqmin
    rw [isSMulRegular_iff_right_eq_zero_of_smul]
    intro y hy
    by_contra hy0
    have hmemU : x ∈ (⋃ q ∈ associatedPrimes (Localization.AtPrime 𝔪)
          (Localization.AtPrime 𝔪 ⧸ Ideal.ofList f), (q : Set (Localization.AtPrime 𝔪))) := by
      rw [biUnion_associatedPrimes_eq_zero_divisors]
      exact ⟨y, hy0, hy⟩
    obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hmemU
    exact hass q hq hxq
  exact ⟨x, hxp, le_antisymm hle_succ hge, hreg'⟩

/-- In `R = ℂ[σ]_𝔪` (σ finite, 𝔪 maximal), every prime `p` contains a regular sequence of
length `ht p`, and the ideal it generates again has height `ht p`. -/
theorem exists_isRegular_ofList_le_prime {σ : Type*} [Fintype σ]
    (𝔪 : Ideal (MvPolynomial σ ℂ)) [𝔪.IsMaximal]
    (p : Ideal (Localization.AtPrime 𝔪)) [p.IsPrime] {h : ℕ} (hp : p.height = h) :
    ∃ f : List (Localization.AtPrime 𝔪), f.length = h ∧
      Ideal.ofList f ≤ p ∧ (Ideal.ofList f).height = h ∧
      RingTheory.Sequence.IsRegular (Localization.AtPrime 𝔪) f := by
  classical
  haveI : Nontrivial (Localization.AtPrime 𝔪) := inferInstance
  have key : ∀ k : ℕ, k ≤ h → ∃ f : List (Localization.AtPrime 𝔪), f.length = k ∧
      Ideal.ofList f ≤ p ∧ (Ideal.ofList f).height = (k : ℕ∞) ∧
      RingTheory.Sequence.IsRegular (Localization.AtPrime 𝔪) f := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨[], rfl, by rw [Ideal.ofList_nil]; exact bot_le, by simp, by
        exact RingTheory.Sequence.IsRegular.nil _ _⟩
    | succ k ih =>
      intro hk
      obtain ⟨f, hlen, hle, hht, hreg⟩ := ih (Nat.le_of_succ_le hk)
      have hklt : (k : ℕ∞) < p.height := by
        rw [hp]
        exact_mod_cast (Nat.lt_of_succ_le hk : k < h)
      obtain ⟨x, hxp, hht', hreg'⟩ := step 𝔪 p f k hlen hle hht hreg hklt
      refine ⟨f ++ [x], by simp [hlen], ?_, ?_, hreg'⟩
      · rw [Ideal.ofList_append, Ideal.ofList_singleton]
        refine sup_le hle ?_
        rw [Ideal.span_le]
        rintro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]; exact hxp
      · rw [hht', Nat.cast_add, Nat.cast_one]
  exact key h le_rfl

end Work.BW.RB
