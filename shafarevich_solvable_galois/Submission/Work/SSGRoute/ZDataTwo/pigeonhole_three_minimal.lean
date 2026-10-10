import Mathlib.Data.Finset.Max
import Submission.Work.SSGRoute.ZDataTwo.pigeonhole_three
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The minimal three-term repetition of the Schmidt–Wingberg `p = 2` shoe-box argument

`Work.SSGRoute.ZDataTwo.pigeonhole_three_minimal`: for any function `a : ℕ → ι` into a finite type
`ι` there are indices `i < j < N` with `a i = a j = a N`, chosen so that `N` is the *minimal*
index at which such a triple occurs (the third occurrence of some value), and so that `i`, `j`
are the *last two* occurrences of that value strictly below `N`.  Concretely the choice satisfies

* (minimality) for every `N' < N` there is no `i' < j' < N'` with `a i' = a j' = a N'`;
* (consecutiveness) no `t` with `i < t < j` or `j < t < N` has `a t = a i = a j`.

This is the form of the shoe-box principle used in the `p = 2` case of the construction of the
class `z` in §4 of Schmidt–Wingberg, "Šafarevič's theorem on solvable groups as Galois groups"
(arXiv:math/9809211, pp. 16–17): there one chooses `N` minimal with
`Ψ_N(z_i) = Ψ_N(z_j) = Ψ_N(z_N)` for `i < j < N`, and then uses that `z_i, z_j` are the two last
indices below `N` with that value.

## Proof

Existence of a triple `i < j < N` of equal values is the already available `pigeonhole_three`.
Let `N` be the least index admitting such a triple (`Nat.find`), so minimality is immediate.  For
the value `v = a N`, the positions strictly below `N` at which `a` takes the value `v` form a
finite set with at least two elements; taking its maximum `j` and then the maximum `i` of the
elements strictly below `j` (the two last occurrences of `v` below `N`) gives the required indices
with both "no occurrence in between" conditions by maximality.
-/

namespace Work.SSGRoute.ZDataTwo

/-- **Two consecutive occurrences.**  If `a` takes the value `v` at two positions `i₀ < j₀`, both
strictly below `N`, then it takes the value `v` at two "consecutive" positions `i < j < N`: no
position strictly between `i` and `j`, and none strictly between `j` and `N`, carries the value
`v`.  (These are the two *last* occurrences of `v` below `N`.) -/
theorem two_consecutive_occurrences {ι : Type} (a : ℕ → ι) (i₀ j₀ N : ℕ) (v : ι)
    (h1 : i₀ < j₀) (h2 : j₀ < N) (h3 : a i₀ = v) (h4 : a j₀ = v) :
    ∃ i j : ℕ, i < j ∧ j < N ∧ a i = v ∧ a j = v ∧
      (∀ t : ℕ, j < t → t < N → a t ≠ v) ∧
      (∀ t : ℕ, i < t → t < j → a t ≠ v) := by
  classical
  -- the set of positions strictly below `N` carrying the value `v`
  let T : Finset ℕ := (Finset.range N).filter (fun t => a t = v)
  have hj₀ : j₀ ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h2, h4⟩
  have hTne : T.Nonempty := ⟨j₀, hj₀⟩
  -- `j` is the last occurrence of `v` below `N`
  have hjmem : T.max' hTne ∈ T := Finset.max'_mem T hTne
  have hjN : T.max' hTne < N := Finset.mem_range.mp (Finset.mem_filter.mp hjmem).1
  have haj : a (T.max' hTne) = v := (Finset.mem_filter.mp hjmem).2
  have hi₀T : i₀ ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_trans h1 h2), h3⟩
  have hi₀lt : i₀ < T.max' hTne := lt_of_lt_of_le h1 (Finset.le_max' T j₀ hj₀)
  -- `i` is the last occurrence of `v` strictly before `j`
  let T' : Finset ℕ := T.filter (fun t => t < T.max' hTne)
  have hi₀T' : i₀ ∈ T' := Finset.mem_filter.mpr ⟨hi₀T, hi₀lt⟩
  have hT'ne : T'.Nonempty := ⟨i₀, hi₀T'⟩
  have himem : T'.max' hT'ne ∈ T' := Finset.max'_mem T' hT'ne
  have hiT : T'.max' hT'ne ∈ T := (Finset.mem_filter.mp himem).1
  have hij : T'.max' hT'ne < T.max' hTne := (Finset.mem_filter.mp himem).2
  have hai : a (T'.max' hT'ne) = v := (Finset.mem_filter.mp hiT).2
  refine ⟨T'.max' hT'ne, T.max' hTne, hij, hjN, hai, haj, ?_, ?_⟩
  · -- nothing strictly between `j` and `N` carries `v`
    intro t hjt htN hcontra
    have htT : t ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htN, hcontra⟩
    have hle : t ≤ T.max' hTne := Finset.le_max' T t htT
    omega
  · -- nothing strictly between `i` and `j` carries `v`
    intro t hit htj hcontra
    have htT : t ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_trans htj hjN), hcontra⟩
    have htT' : t ∈ T' := Finset.mem_filter.mpr ⟨htT, htj⟩
    have hle : t ≤ T'.max' hT'ne := Finset.le_max' T' t htT'
    omega

/-- **Minimal three-term repetition.**  For any `a : ℕ → ι` with `ι` finite there are `i < j < N`
with `a i = a j = a N`, where `N` is the least index admitting such a triple and `i < j` are the
two last occurrences of the value `a N` strictly below `N`. -/
theorem pigeonhole_three_minimal {ι : Type} [Fintype ι] (a : ℕ → ι) :
    ∃ i j N : ℕ, i < j ∧ j < N ∧ a i = a j ∧ a j = a N ∧
      (∀ N' : ℕ, N' < N →
        ¬ ∃ i' j' : ℕ, i' < j' ∧ j' < N' ∧ a i' = a j' ∧ a j' = a N') ∧
      (∀ t : ℕ, j < t → t < N → a t ≠ a j) ∧
      (∀ t : ℕ, i < t → t < j → a t ≠ a i) := by
  classical
  -- some index admits a triple of equal values
  obtain ⟨i₀, j₀, N₀, hi₀j₀, hj₀N₀, hEq1, hEq2⟩ := pigeonhole_three a
  let P : ℕ → Prop := fun N => ∃ i j : ℕ, i < j ∧ j < N ∧ a i = a j ∧ a j = a N
  have hP : ∃ N, P N := ⟨N₀, i₀, j₀, hi₀j₀, hj₀N₀, hEq1, hEq2⟩
  -- `N` is the least such index
  have hPN : P (Nat.find hP) := Nat.find_spec hP
  obtain ⟨i', j', hi'j', hj'N, hEq1', hEq2'⟩ := hPN
  -- the two last occurrences of `a (Nat.find hP)` strictly below `Nat.find hP`
  obtain ⟨i, j, hij, hjN, hai, haj, hafter, hbefore⟩ :=
    two_consecutive_occurrences a i' j' (Nat.find hP) (a j') hi'j' hj'N hEq1' rfl
  refine ⟨i, j, Nat.find hP, hij, hjN, hai.trans haj.symm, haj.trans hEq2', ?_, ?_, ?_⟩
  · -- minimality of `Nat.find hP`
    intro N' hN' hcon
    obtain ⟨i'', j'', hi''j'', hj''N', hq1, hq2⟩ := hcon
    exact absurd (Nat.find_min' hP ⟨i'', j'', hi''j'', hj''N', hq1, hq2⟩) (not_le.mpr hN')
  · -- no occurrence of `a j` between `j` and `N`
    intro t hjt htN hcontra
    exact hafter t hjt htN (hcontra.trans haj)
  · -- no occurrence of `a i` between `i` and `j`
    intro t hit htj hcontra
    exact hbefore t hit htj (hcontra.trans hai)

end Work.SSGRoute.ZDataTwo
