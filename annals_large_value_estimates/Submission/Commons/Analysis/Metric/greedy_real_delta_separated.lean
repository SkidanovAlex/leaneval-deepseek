import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Commons.Analysis.Metric

set_option autoImplicit false

/-- At most `b - a + 1` points of an interval `[a, b]` (`a ≤ b`) can be pairwise at
distance at least `1`.  Equivalently, a finite set of reals that is `1`-separated and
contained in `[a, b]` has at most `b - a + 1` elements.

Proof by induction on the cardinality, always removing the smallest element:
if `m` is the least and `m'` the second least element then every remaining point lies
in `[m', b]`, and `m' ≥ a + 1`. -/
lemma card_le_of_one_separated_Icc : ∀ (n : ℕ) (A : Finset ℝ), A.card = n →
    (∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ |x - y|) →
    ∀ a b : ℝ, a ≤ b → (∀ x ∈ A, a ≤ x) → (∀ x ∈ A, x ≤ b) →
    (A.card : ℝ) ≤ b - a + 1 := by
  intro n
  induction n with
  | zero =>
      intro A hcard hsep a b hab ha hb
      rw [hcard]; simp
      linarith
  | succ n ih =>
      intro A hcard hsep a b hab ha hb
      have hne : A.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
      set m := A.min' hne with hmdef
      have hmA : m ∈ A := A.min'_mem hne
      set A' := A.erase m with hA'def
      have h1 : A'.card + 1 = A.card := by
        rw [hA'def]; exact Finset.card_erase_add_one hmA
      by_cases hne' : A'.Nonempty
      · -- at least two elements
        set m' := A'.min' hne' with hm'def
        have hm'mem : m' ∈ A' := A'.min'_mem hne'
        have hm'A : m' ∈ A := Finset.mem_of_mem_erase hm'mem
        have hne_m : m' ≠ m := (Finset.mem_erase.mp hm'mem).1
        have hmle : m ≤ m' := A.min'_le m' hm'A
        have hlt : m < m' := lt_of_le_of_ne hmle (Ne.symm hne_m)
        have hdist : 1 ≤ |m' - m| := hsep m' hm'A m hmA hne_m
        have hge1 : 1 ≤ m' - m := by
          rw [abs_of_pos (sub_pos.mpr hlt)] at hdist
          exact hdist
        have hcard' : A'.card = n := by omega
        have hsep' : ∀ x ∈ A', ∀ y ∈ A', x ≠ y → 1 ≤ |x - y| := by
          intro x hx y hy hxy
          exact hsep x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy
        have ha' : ∀ x ∈ A', m' ≤ x := fun x hx => A'.min'_le x hx
        have hb' : ∀ x ∈ A', x ≤ b := fun x hx => hb x (Finset.mem_of_mem_erase hx)
        have hab' : m' ≤ b := hb' m' hm'mem
        have hind := ih A' hcard' hsep' m' b hab' ha' hb'
        have hcardeq : (A.card : ℝ) = (A'.card : ℝ) + 1 := by
          rw [← h1]; push_cast; ring
        rw [hcardeq]
        have : a + 1 ≤ m' := by linarith [ha m hmA]
        linarith
      · -- single element
        have hempty : A' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne'
        have hcard1 : (A.card : ℝ) = 1 := by
          rw [hempty, Finset.card_empty] at h1
          rw [← h1]; norm_num
        rw [hcard1]
        linarith [ha m hmA, hb m hmA]

/-- Greedy/maximal `δ`-separated subset of a finite set of reals: from a finite set `S` of
pairwise `1`-separated reals and any `δ ≥ 1` there is a `δ`-separated `J ⊆ S` with
`|S| ≤ (2δ+1)|J|`.

Proof: take a `δ`-separated `J ⊆ S` of maximal cardinality.  Then the intervals
`[j - δ, j + δ]` around the points of `J` cover `S`, and each of them contains at most
`2δ + 1` points of `S` (which is `1`-separated). -/
theorem greedy_real_delta_separated (S : Finset ℝ) (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |i - j|)
    (δ : ℝ) (hδ : 1 ≤ δ) :
    ∃ J : Finset ℝ, J ⊆ S ∧ (∀ i ∈ J, ∀ j ∈ J, i ≠ j → δ ≤ |i - j|) ∧
      (S.card : ℝ) ≤ (J.card : ℝ) * (2 * δ + 1) := by
  classical
  let P : Finset ℝ → Prop := fun J => J ⊆ S ∧ ∀ i ∈ J, ∀ j ∈ J, i ≠ j → δ ≤ |i - j|
  have hex : P ∅ := ⟨Finset.empty_subset _, by simp⟩
  rcases Finset.exists_max_image (S.powerset.filter P) (fun J => J.card)
      ⟨∅, by simp [P, hex]⟩ with ⟨J₀, hJ₀, hJ₀max⟩
  have hJ₀sub : J₀ ⊆ S := (Finset.mem_filter.mp hJ₀).2.1
  have hJ₀P : ∀ i ∈ J₀, ∀ j ∈ J₀, i ≠ j → δ ≤ |i - j| := (Finset.mem_filter.mp hJ₀).2.2
  have hδpos : 0 < δ := lt_of_lt_of_le zero_lt_one hδ
  -- covering: every point of `S` is within distance `< δ` of a point of `J₀`
  have hcov : ∀ i ∈ S, ∃ j ∈ J₀, |i - j| < δ := by
    intro i hiS
    by_cases hiJ : i ∈ J₀
    · exact ⟨i, hiJ, by simpa using hδpos⟩
    · by_contra hno
      have hfar : ∀ j ∈ J₀, δ ≤ |i - j| := by
        intro j hj
        by_contra hlt
        exact hno ⟨j, hj, lt_of_not_ge hlt⟩
      have hPins : P (insert i J₀) := by
        refine ⟨Finset.insert_subset hiS hJ₀sub, ?_⟩
        intro x hx y hy hxy
        rw [Finset.mem_insert] at hx hy
        rcases hx with rfl | hxJ
        · rcases hy with rfl | hyJ
          · exact absurd rfl hxy
          · exact hfar y hyJ
        · rcases hy with rfl | hyJ
          · rw [abs_sub_comm]; exact hfar x hxJ
          · exact hJ₀P x hxJ y hyJ hxy
      have hmem : insert i J₀ ∈ S.powerset.filter P := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_powerset.mpr (Finset.insert_subset hiS hJ₀sub), hPins⟩
      have hle : (insert i J₀).card ≤ J₀.card := hJ₀max _ hmem
      have hgt : (insert i J₀).card = J₀.card + 1 := Finset.card_insert_of_notMem hiJ
      omega
  -- assign to each point of `S` a `J₀`-representative within distance `< δ`
  let g : ℝ → ℝ := fun i => if hi : i ∈ S then Classical.choose (hcov i hi) else 0
  have hgJ : ∀ i, i ∈ S → g i ∈ J₀ := by
    intro i hi
    simp only [g, dif_pos hi]
    exact (Classical.choose_spec (hcov i hi)).1
  have hgd : ∀ i, i ∈ S → |i - g i| < δ := by
    intro i hi
    simp only [g, dif_pos hi]
    exact (Classical.choose_spec (hcov i hi)).2
  -- partition `S` into the fibres of `g`
  let Fib : ℝ → Finset ℝ := fun j => S.filter (fun i => g i = j)
  have hcard_sum : S.card = ∑ j ∈ J₀, (Fib j).card := by
    have hmap : Set.MapsTo g (S : Set ℝ) (J₀ : Set ℝ) := fun x hx => hgJ x hx
    have hf := Finset.card_eq_sum_card_fiberwise (s := S) (t := J₀) (f := g) hmap
    simpa [Fib] using hf
  -- each fibre has at most `2δ+1` points
  have hfib_le : ∀ j ∈ J₀, ((Fib j).card : ℝ) ≤ 2 * δ + 1 := by
    intro j hj
    have hsub : Fib j ⊆ S := by intro x hx; exact (Finset.mem_filter.mp hx).1
    have hsepF : ∀ x ∈ Fib j, ∀ y ∈ Fib j, x ≠ y → 1 ≤ |x - y| := by
      intro x hx y hy hxy
      exact hsep x (hsub hx) y (hsub hy) hxy
    have hA : ∀ x ∈ Fib j, j - δ ≤ x := by
      intro x hx
      have hgx : g x = j := (Finset.mem_filter.mp hx).2
      have hlt : |x - j| < δ := by rw [← hgx]; exact hgd x (hsub hx)
      have := (abs_lt.mp hlt).1
      linarith
    have hB : ∀ x ∈ Fib j, x ≤ j + δ := by
      intro x hx
      have hgx : g x = j := (Finset.mem_filter.mp hx).2
      have hlt : |x - j| < δ := by rw [← hgx]; exact hgd x (hsub hx)
      have := (abs_lt.mp hlt).2
      linarith
    have hab : j - δ ≤ j + δ := by linarith
    have hcnt := card_le_of_one_separated_Icc (Fib j).card (Fib j) rfl hsepF
      (j - δ) (j + δ) hab hA hB
    linarith
  have hsum_le : ∑ j ∈ J₀, ((Fib j).card : ℝ) ≤ (J₀.card : ℝ) * (2 * δ + 1) := by
    have h := Finset.sum_le_card_nsmul J₀ (fun j => ((Fib j).card : ℝ)) (2 * δ + 1) hfib_le
    rw [nsmul_eq_mul] at h
    exact h
  have hcard_sum_real : (S.card : ℝ) = ∑ j ∈ J₀, ((Fib j).card : ℝ) := by
    rw [hcard_sum, Nat.cast_sum]
  refine ⟨J₀, hJ₀sub, hJ₀P, ?_⟩
  calc (S.card : ℝ) = ∑ j ∈ J₀, ((Fib j).card : ℝ) := hcard_sum_real
    _ ≤ (J₀.card : ℝ) * (2 * δ + 1) := hsum_le

end Commons.Analysis.Metric