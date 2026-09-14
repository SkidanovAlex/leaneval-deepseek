import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.RingTheory.Ideal.finite_subtype_minimalPrimes

namespace Commons.Algebra.MvPolynomial

open _root_.MvPolynomial

set_option autoImplicit false
set_option linter.style.haveILetI false

/-- The vanishing ideal of a set is the infimum over its points of the vanishing ideals of the
corresponding singletons. -/
lemma vanishingIdeal_eq_iInf_singleton {F : Type*} [Field F] {σ : Type*} (V : Set (σ → F)) :
    MvPolynomial.vanishingIdeal F V
      = ⨅ x ∈ V, MvPolynomial.vanishingIdeal F ({x} : Set (σ → F)) := by
  ext p
  simp [MvPolynomial.mem_vanishingIdeal_iff]

/-- Distinct points have distinct vanishing ideals: `x ↦ vanishingIdeal F {x}` is injective. -/
lemma vanishingIdeal_singleton_injective {F : Type*} [Field F] {σ : Type*} :
    Function.Injective (fun x : σ → F => MvPolynomial.vanishingIdeal F ({x} : Set (σ → F))) := by
  intro x y hxy
  by_contra hne
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hxy' : MvPolynomial.vanishingIdeal F ({x} : Set (σ → F))
      = MvPolynomial.vanishingIdeal F ({y} : Set (σ → F)) := hxy
  have hmem : MvPolynomial.X i - MvPolynomial.C (x i)
      ∈ MvPolynomial.vanishingIdeal F ({x} : Set (σ → F)) := by
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp
  have hnot : MvPolynomial.X i - MvPolynomial.C (x i)
      ∉ MvPolynomial.vanishingIdeal F ({y} : Set (σ → F)) := by
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp only [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, sub_eq_zero]
    exact fun h' => hi h'.symm
  exact hnot (hxy' ▸ hmem)

/-- Over an algebraically closed field with finitely many variables, if the zero locus of `I` is
finite then the vanishing ideal of any of its points is a minimal prime over `I`. -/
lemma mem_minimalPrimes_vanishingIdeal_singleton {F : Type*} [Field F] [IsAlgClosed F]
    {σ : Type*} [Fintype σ] {I : Ideal (MvPolynomial σ F)} {x : σ → F}
    (hx : x ∈ MvPolynomial.zeroLocus F I)
    (hfin : (MvPolynomial.zeroLocus F I).Finite) :
    MvPolynomial.vanishingIdeal F ({x} : Set (σ → F)) ∈ I.minimalPrimes := by
  rw [Ideal.minimalPrimes]
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · exact le_trans (MvPolynomial.le_vanishingIdeal_zeroLocus I)
      (MvPolynomial.vanishingIdeal_anti_mono (Set.singleton_subset_iff.2 hx))
  · intro y hy hym
    have hrad : I.radical ≤ y := (hy.1.radical_le_iff).2 hy.2
    have hyZ : MvPolynomial.vanishingIdeal F (MvPolynomial.zeroLocus F I) ≤ y := by
      rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]; exact hrad
    have hkey : hfin.toFinset.inf
        (fun z => MvPolynomial.vanishingIdeal F ({z} : Set (σ → F)))
        = MvPolynomial.vanishingIdeal F (MvPolynomial.zeroLocus F I) := by
      apply le_antisymm
      · rw [vanishingIdeal_eq_iInf_singleton]
        refine le_iInf fun z => le_iInf fun hz => ?_
        exact Finset.inf_le ((hfin.mem_toFinset).2 hz)
      · rw [vanishingIdeal_eq_iInf_singleton]
        refine Finset.le_inf fun z hz => ?_
        exact le_trans (iInf_le _ z) (iInf_le _ ((hfin.mem_toFinset).1 hz))
    have hle : hfin.toFinset.inf
        (fun z => MvPolynomial.vanishingIdeal F ({z} : Set (σ → F))) ≤ y :=
      hkey.le.trans hyZ
    obtain ⟨z, hzmem, hzy⟩ := (Ideal.IsPrime.inf_le' hy.1).1 hle
    have hyneq : y ≠ ⊤ := hy.1.ne_top
    have hz_eq : MvPolynomial.vanishingIdeal F ({z} : Set (σ → F)) = y :=
      Ideal.IsMaximal.eq_of_le (inferInstance) hyneq hzy
    have hzx : MvPolynomial.vanishingIdeal F ({z} : Set (σ → F))
        ≤ MvPolynomial.vanishingIdeal F ({x} : Set (σ → F)) := by
      rw [hz_eq]; exact hym
    have heq : MvPolynomial.vanishingIdeal F ({z} : Set (σ → F))
        = MvPolynomial.vanishingIdeal F ({x} : Set (σ → F)) :=
      Ideal.IsMaximal.eq_of_le (inferInstance)
        (inferInstance : (MvPolynomial.vanishingIdeal F ({x} : Set (σ → F))).IsMaximal).ne_top hzx
    rw [← hz_eq]
    exact heq.ge

/-- Over an algebraically closed field, the number of points of the zero locus of an ideal `I` of
a polynomial ring is at most the number of minimal primes of `I`.  (When the zero locus is finite
these two numbers are in fact equal, since the minimal primes are then the maximal ideals cutting
out the points; when it is infinite both sides are `0` and the bound is trivial because `Nat.card`
of an infinite type is `0`.) -/
theorem ncard_zeroLocus_le_card_minimalPrimes {F : Type*} [Field F] [IsAlgClosed F]
    {σ : Type*} [Fintype σ] (I : Ideal (MvPolynomial σ F)) :
    (MvPolynomial.zeroLocus F I).ncard
      ≤ Nat.card {p : Ideal (MvPolynomial σ F) // p ∈ I.minimalPrimes} := by
  have hT := Commons.RingTheory.Ideal.finite_subtype_minimalPrimes I
  haveI := hT
  by_cases hfin : (MvPolynomial.zeroLocus F I).Finite
  · let f : ↥(MvPolynomial.zeroLocus F I) →
        {p : Ideal (MvPolynomial σ F) // p ∈ I.minimalPrimes} :=
      fun x => ⟨MvPolynomial.vanishingIdeal F ({x.1} : Set (σ → F)),
        mem_minimalPrimes_vanishingIdeal_singleton x.2 hfin⟩
    have hinj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply vanishingIdeal_singleton_injective
      exact Subtype.ext_iff.mp hxy
    have hle := Nat.card_le_card_of_injective f hinj
    rwa [Nat.card_coe_set_eq] at hle
  · rw [Set.Infinite.ncard (show (MvPolynomial.zeroLocus F I).Infinite from hfin)]
    exact Nat.zero_le _

end Commons.Algebra.MvPolynomial