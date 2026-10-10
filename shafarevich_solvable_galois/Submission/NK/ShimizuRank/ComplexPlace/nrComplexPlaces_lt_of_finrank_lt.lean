import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ShimizuRank.ComplexPlace

open scoped Classical
open NumberField NumberField.InfinitePlace

/-- An infinite place `w` of `L` lies over `v` iff its restriction to `K` is `v`. This is
`NumberField.InfinitePlace.LiesOver` unwrapped to the `comap` form used below. -/
lemma liesOver_iff_comap {K L : Type*} [Field K] [Field L] [Algebra K L] (w : InfinitePlace L)
    (v : InfinitePlace K) : w.LiesOver v ↔ w.comap (algebraMap K L) = v := by
  constructor
  · intro h
    let _ := h
    exact LiesOver.comap_eq w v
  · intro h
    exact ⟨congrArg Subtype.val h⟩

/-- Above a *complex* place of `K`, the number of places of `L` is exactly the degree `[L : K]`:
there is no ramification and no inert pair, since the completion is `ℂ`. -/
lemma fiber_card {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) (hv : v.IsComplex) :
    (Finset.univ.filter (fun w : InfinitePlace L => w.comap (algebraMap K L) = v)).card
      = Module.finrank K L := by
  rw [← Fintype.card_subtype (fun w : InfinitePlace L => w.comap (algebraMap K L) = v)]
  -- a complex place is never ramified below
  have hram : (ramifiedPlacesOver L v).ncard = 0 := by
    have hempty : ramifiedPlacesOver L v = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro w ⟨hw, hram⟩
      rw [isRamified_iff] at hram
      rw [(liesOver_iff_comap w v).mp hw] at hram
      exact (not_isReal_iff_isComplex.mpr hv) hram.2
    rw [hempty, Set.ncard_empty]
  have hfin : (unramifiedPlacesOver L v).ncard = Module.finrank K L := by
    have := unramifedPlacesOver_ncard_add_eq_finrank L v
    rw [hram, mul_zero, add_zero] at this
    exact this
  have hbridge : (unramifiedPlacesOver L v).ncard = Fintype.card ↥(unramifiedPlacesOver L v) := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  rw [← hfin, hbridge]
  -- for complex `v` every place above it is unramified
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun w => by
    rw [unramifiedPlacesOver, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨(liesOver_iff_comap w v).mpr h, isUnramified_iff.mpr (Or.inr (h ▸ hv))⟩
    · rintro ⟨hl, -⟩
      exact (liesOver_iff_comap w v).mp hl))

/-- **Counting complex places above a number-field extension.**  Every complex place of `K`
has exactly `[L : K]` places of `L` above it, and all of them are complex; hence `L` has at least
`[L : K]` times as many complex places as `K`.  (The count above a complex place is
`unramifedPlacesOver_ncard_add_eq_finrank` together with the vanishing of the ramified places
over a complex place.) -/
lemma nrComplexPlaces_mul_finrank_le (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] :
    nrComplexPlaces K * Module.finrank K L ≤ nrComplexPlaces L := by
  classical
  -- Every complex place of `K` has exactly `[L : K]` complex places of `L` above it, and the
  -- fibres over distinct places are disjoint; this already accounts for
  -- `nrComplexPlaces K * [L : K]` complex places of `L`.
  let f : {v : InfinitePlace K // IsComplex v} → Finset (InfinitePlace L) :=
    fun v => Finset.univ.filter (fun w => w.comap (algebraMap K L) = v.1)
  have hf : ∀ v, (f v).card = Module.finrank K L := fun v => fiber_card v.1 v.2
  have hdisj : ((Finset.univ : Finset {v : InfinitePlace K // IsComplex v}) :
      Set _).PairwiseDisjoint f := by
    intro v _ v' _ hne
    change Disjoint (f v) (f v')
    rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [f, Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
    exact hne (Subtype.ext (hw.symm.trans hw'))
  have hcard : ((Finset.univ : Finset {v : InfinitePlace K // IsComplex v}).biUnion f).card
      = ∑ v : {v : InfinitePlace K // IsComplex v}, (f v).card := by
    rw [Finset.card_biUnion hdisj]
  have hmem : (Finset.univ : Finset {v : InfinitePlace K // IsComplex v}).biUnion f ⊆
      Finset.univ.filter (fun w : InfinitePlace L => IsComplex w) := by
    intro w hw
    rw [Finset.mem_biUnion] at hw
    obtain ⟨v, -, hwv⟩ := hw
    simp only [f, Finset.mem_filter, Finset.mem_univ, true_and] at hwv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact IsComplex.of_comap (algebraMap K L) (hwv ▸ v.2)
  have hle : ((Finset.univ : Finset {v : InfinitePlace K // IsComplex v}).biUnion f).card
      ≤ nrComplexPlaces L := by
    refine le_trans (Finset.card_le_card hmem) ?_
    rw [← Fintype.card_subtype (fun w : InfinitePlace L => IsComplex w)]
  have hsum : (∑ v : {v : InfinitePlace K // IsComplex v}, (f v).card)
      = nrComplexPlaces K * Module.finrank K L := by
    rw [Finset.sum_congr rfl (fun v _ => hf v), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    rfl
  calc nrComplexPlaces K * Module.finrank K L
      = ∑ v : {v : InfinitePlace K // IsComplex v}, (f v).card := hsum.symm
    _ = ((Finset.univ : Finset {v : InfinitePlace K // IsComplex v}).biUnion f).card :=
        hcard.symm
    _ ≤ nrComplexPlaces L := hle

/-
**Shimizu's Lemma 4f.2, arithmetic half**: a nontrivial finite extension of number fields with a
complex prime has strictly more complex primes.

Intended proof (Mathlib only).  Let `∂ : InfinitePlace L → InfinitePlace K` be
`comap · (algebraMap K L)`, and group the places of `L` by their restriction:
`nrComplexPlaces L = ∑_{v : InfinitePlace K} #{w : InfinitePlace L | w.comap (algebraMap K L) = v ∧ IsComplex w}`.
For a complex `v`, every `w` above `v` is complex (`InfinitePlace.IsComplex.of_comap`) and
unramified (`InfinitePlace.isUnramified_iff`: unramified iff `IsReal w ∨ IsComplex (comap w)`), so the
`v`-fiber has cardinality `Module.finrank K L`; that fiber count is
`NumberField.InfinitePlace.unramifedPlacesOver_ncard_add_eq_finrank L v`
(`(unramifiedPlacesOver L v).ncard + 2 * (ramifiedPlacesOver L v).ncard = Module.finrank K L`)
together with `ramifiedPlacesOver L v = ∅` for complex `v`
(`InfinitePlace.isRamified_iff`: ramified means complex over a *real* place).
Hence `nrComplexPlaces L ≥ nrComplexPlaces K * Module.finrank K L`.
If `nrComplexPlaces K ≠ 0` then `1 < Module.finrank K L` makes this `> nrComplexPlaces K`.
If `nrComplexPlaces K = 0`, take a complex place `w` of `L`; its restriction `v` is not complex
(otherwise `nrComplexPlaces K ≥ 1`), so `w` is a complex place over the real place `v` and
`nrComplexPlaces L ≥ 1 > 0`.

Please declare the result in namespace `NK.ShimizuRank`, in the module
`Submission.NK.ShimizuRank.ComplexPlace.nrComplexPlaces_lt_of_finrank_lt`.
-/
theorem nrComplexPlaces_lt_of_finrank_lt {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (h : 1 < Module.finrank K L)
    (hv : ∃ v : NumberField.InfinitePlace L, NumberField.InfinitePlace.IsComplex v) :
    NumberField.InfinitePlace.nrComplexPlaces K < NumberField.InfinitePlace.nrComplexPlaces L := by
  classical
  have key := nrComplexPlaces_mul_finrank_le K L
  rcases Nat.eq_zero_or_pos (nrComplexPlaces K) with h0 | hpos
  · -- `K` has no complex place: the complex place of `L` given by the hypothesis is already one.
    obtain ⟨v, hv⟩ := hv
    have hL : 0 < nrComplexPlaces L := by
      have : 0 < Fintype.card {w : InfinitePlace L // IsComplex w} :=
        Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩
      simpa using this
    omega
  · have hlt : nrComplexPlaces K < nrComplexPlaces K * Module.finrank K L :=
      lt_mul_of_one_lt_right hpos h
    omega

end NK.ShimizuRank.ComplexPlace
