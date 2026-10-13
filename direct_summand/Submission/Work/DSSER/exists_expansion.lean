import Mathlib
import Submission.Work.DSSER.Basic
import Submission.Work.DSSER.Words
import Submission.Work.DSSER.IdealPow

universe u

namespace Work.DSSER

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-! ## Decomposition of `𝔪^N` into degree-`N` monomials

The bridge between the abstract description `𝔪^N = span {z^w : |w| = N}` and a concrete
coefficient function on the words of degree `N`. -/

/-- Every element of `𝔪^N` is a combination of the degree-`N` monomials `z^w`, indexed by the
words `w ∈ wordBlk d N` (i.e. `∑ i, w i = N`). -/
theorem exists_coeff {d : ℕ} (z : Fin d → R)
    (hm : Ideal.span (Set.range z) = maximalIdeal R) (N : ℕ) {rho : R}
    (h : rho ∈ maximalIdeal R ^ N) :
    ∃ c : (Fin d → ℕ) → R, rho = ∑ w ∈ (wordBlk d N).toFinset, c w * zMono z w := by
  classical
  have hspan : maximalIdeal R ^ N =
      Submodule.span R (zMono z '' (↑(wordBlk d N).toFinset : Set (Fin d → ℕ))) := by
    rw [maximalIdeal_pow_eq_span R z hm N]
    congr 1
    ext a
    constructor
    · intro ha
      rw [Set.mem_ofPred_eq] at ha
      obtain ⟨w, hw, rfl⟩ := ha
      exact Set.mem_image_of_mem _ (List.mem_toFinset.mpr (mem_wordBlk.mpr hw))
    · intro ha
      rw [Set.mem_image] at ha
      obtain ⟨w, hw, rfl⟩ := ha
      rw [Set.mem_ofPred_eq]
      exact ⟨w, mem_wordBlk.mp (List.mem_toFinset.mp hw), rfl⟩
  rw [hspan] at h
  obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' R).mp h
  exact ⟨c, by rw [← hc]; simp [smul_eq_mul]⟩

/-- Choice of the coefficient function of `rho ∈ 𝔪^N`; junk value on words of other degrees and
when `rho ∉ 𝔪^N`. -/
noncomputable def digDec {d : ℕ} (z : Fin d → R)
    (hm : Ideal.span (Set.range z) = maximalIdeal R) (N : ℕ) (rho : R)
    (w : Fin d → ℕ) : R := by
  classical
  exact if h : rho ∈ maximalIdeal R ^ N then Classical.choose (exists_coeff z hm N h) w else 0

theorem digDec_spec {d : ℕ} (z : Fin d → R)
    (hm : Ideal.span (Set.range z) = maximalIdeal R) (N : ℕ) (rho : R)
    (h : rho ∈ maximalIdeal R ^ N) :
    rho = ∑ w ∈ (wordBlk d N).toFinset, digDec z hm N rho w * zMono z w := by
  classical
  have key : ∀ w, digDec z hm N rho w = Classical.choose (exists_coeff z hm N h) w := by
    intro w
    rw [digDec]
    rw [dite_eq_left h]
  rw [Finset.sum_congr rfl (fun w _ => by rw [key w])]
  exact Classical.choose_spec (exists_coeff z hm N h)

/-! ## Splitting a coefficient as a `p`-th power plus an element of `𝔪` -/

/-- Given `R = R^p + 𝔪`, the `p`-th root of the part of `c` lying in `R^p`. -/
noncomputable def splitMu (p : ℕ)
    (hperf : ∀ x : R, ∃ μ : R, x - μ ^ p ∈ maximalIdeal R) (c : R) : R :=
  Classical.choose (hperf c)

theorem splitMu_spec (p : ℕ)
    (hperf : ∀ x : R, ∃ μ : R, x - μ ^ p ∈ maximalIdeal R) (c : R) :
    c - splitMu p hperf c ^ p ∈ maximalIdeal R :=
  Classical.choose_spec (hperf c)

/-! ## The one-step remainder -/

/-- One step of the digit expansion: the `𝔪`-part of the `N`-th coefficient goes into the next
remainder. -/
noncomputable def digNext {d : ℕ} (p : ℕ) (z : Fin d → R)
    (hm : Ideal.span (Set.range z) = maximalIdeal R)
    (hperf : ∀ x : R, ∃ μ : R, x - μ ^ p ∈ maximalIdeal R) (N : ℕ) (rho : R) : R :=
  ∑ w ∈ (wordBlk d N).toFinset,
    (digDec z hm N rho w - splitMu p hperf (digDec z hm N rho w) ^ p) * zMono z w

/-- The next remainder lies in `𝔪^(N+1)` (unconditionally on `rho`). -/
theorem digNext_mem {d : ℕ} (p : ℕ) (z : Fin d → R)
    (hm : Ideal.span (Set.range z) = maximalIdeal R)
    (hperf : ∀ x : R, ∃ μ : R, x - μ ^ p ∈ maximalIdeal R) (N : ℕ) (rho : R) :
    digNext p z hm hperf N rho ∈ maximalIdeal R ^ (N + 1) := by
  classical
  rw [digNext]
  refine Ideal.sum_mem _ fun w hw => ?_
  have hwdeg : ∑ i, w i = N := mem_wordBlk.mp (List.mem_toFinset.mp hw)
  have hc : digDec z hm N rho w - splitMu p hperf (digDec z hm N rho w) ^ p ∈ maximalIdeal R :=
    splitMu_spec p hperf _
  have hz : zMono z w ∈ maximalIdeal R ^ N := by
    rw [← hwdeg]; exact zMono_mem_pow hm w
  have hmem := Ideal.mul_mem_mul hc hz
  rwa [Ideal.IsTwoSided.pow_succ]

/-! ## The recursion -/

/-- The sequence of remainders: `r 0 = x` and `r (N+1) = digNext N (r N)`. -/
noncomputable def digSeq {d : ℕ} (p : ℕ) (z : Fin d → R)
    (hm : Ideal.span (Set.range z) = maximalIdeal R)
    (hperf : ∀ x : R, ∃ μ : R, x - μ ^ p ∈ maximalIdeal R) (x : R) : ℕ → R
  | 0 => x
  | N + 1 => digNext p z hm hperf N (digSeq p z hm hperf x N)

theorem digSeq_zero {d : ℕ} (p : ℕ) (z : Fin d → R)
    (hm : Ideal.span (Set.range z) = maximalIdeal R)
    (hperf : ∀ x : R, ∃ μ : R, x - μ ^ p ∈ maximalIdeal R) (x : R) :
    digSeq p z hm hperf x 0 = x := rfl

theorem digSeq_succ {d : ℕ} (p : ℕ) (z : Fin d → R)
    (hm : Ideal.span (Set.range z) = maximalIdeal R)
    (hperf : ∀ x : R, ∃ μ : R, x - μ ^ p ∈ maximalIdeal R) (x : R) (N : ℕ) :
    digSeq p z hm hperf x (N + 1) = digNext p z hm hperf N (digSeq p z hm hperf x N) := rfl

/-- The remainders are `𝔪`-adically small. -/
theorem digSeq_mem {d : ℕ} (p : ℕ) (z : Fin d → R)
    (hm : Ideal.span (Set.range z) = maximalIdeal R)
    (hperf : ∀ x : R, ∃ μ : R, x - μ ^ p ∈ maximalIdeal R) (x : R) :
    ∀ N, digSeq p z hm hperf x N ∈ maximalIdeal R ^ N := by
  intro N
  induction N with
  | zero =>
    rw [digSeq_zero, Submodule.pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ N ih =>
    rw [digSeq_succ]
    exact digNext_mem p z hm hperf N (digSeq p z hm hperf x N)

/-! ## The coefficients `μ` -/

/-- The coefficient attached to the word `w`: the `p`-th root of the `R^p`-part of the `|w|`-th
coefficient of the remainder `r |w|`. -/
noncomputable def digMu {d : ℕ} (p : ℕ) (z : Fin d → R)
    (hm : Ideal.span (Set.range z) = maximalIdeal R)
    (hperf : ∀ x : R, ∃ μ : R, x - μ ^ p ∈ maximalIdeal R) (x : R)
    (w : Fin d → ℕ) : R :=
  splitMu p hperf (digDec z hm (∑ i, w i) (digSeq p z hm hperf x (∑ i, w i)) w)

/-! ## The telescoping identity -/

theorem digSeq_expansion {d : ℕ} (p : ℕ) (z : Fin d → R)
    (hm : Ideal.span (Set.range z) = maximalIdeal R)
    (hperf : ∀ x : R, ∃ μ : R, x - μ ^ p ∈ maximalIdeal R) (x : R) :
    ∀ N, x = ((wordList d N).map
        (fun w => digMu p z hm hperf x w ^ p * zMono z w)).sum + digSeq p z hm hperf x N := by
  intro N
  induction N with
  | zero =>
    rw [wordList_zero, List.map_nil, List.sum_nil, zero_add, digSeq_zero]
  | succ N ih =>
    have hrN : digSeq p z hm hperf x N ∈ maximalIdeal R ^ N := digSeq_mem p z hm hperf x N
    have hdec := digDec_spec z hm N (digSeq p z hm hperf x N) hrN
    have hsplit : digSeq p z hm hperf x N =
        ((wordBlk d N).map
            (fun w => digMu p z hm hperf x w ^ p * zMono z w)).sum
          + digSeq p z hm hperf x (N + 1) := by
      rw [digSeq_succ, digNext]
      conv_lhs => rw [hdec]
      rw [← List.sum_toFinset _ (wordBlk_nodup d N)]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w hw => ?_
      have hmuw : digMu p z hm hperf x w
          = splitMu p hperf (digDec z hm N (digSeq p z hm hperf x N) w) := by
        rw [digMu, mem_wordBlk.mp (List.mem_toFinset.mp hw)]
      rw [hmuw]
      ring
    conv_lhs => rw [ih]
    rw [wordList_succ, List.map_append, List.sum_append]
    rw [hsplit]
    ring

/-- **The digit expansion in `R`.**  If `𝔪 = (z_i)` and `R = R^p + 𝔪`, then every `x : R` can be
written as an `𝔪`-adically convergent sum `∑_w μ_w^p z^w` indexed by the words `w : Fin d → ℕ`, with
partial sums over `wordList d N` (the words of degree `< N`) and remainders `r N ∈ 𝔪^N`:

`x = ((wordList d N).map (fun w => μ w ^ p * zMono z w)).sum + r N`.

Route: recursion on `N`.  At each step write `r ∈ 𝔪^N` as a combination of the degree-`N` monomials
using `Work.DSSER.maximalIdeal_pow_eq_span` (`𝔪^N = span {z^w : |w| = N}`), the bridge between the
`Finset` sum over the words of degree `N` and the list sum over `wordBlk d N`
(`Basic.mem_wordBlk`, `List.sum_toFinset`, `wordBlk_nodup`), then split each coefficient
`c w = μ w ^ p + m w` with `m w ∈ 𝔪` using `hperf`, and put the `m w` part into the next remainder
(`𝔪^N · 𝔪 = 𝔪^(N+1)`).  Telescoping with `Work.DSSER.wordList_succ`
(`wordList d (N+1) = wordList d N ++ wordBlk d N`) and `List.sum_append` gives the statement.
`hp : 0 < p` is present because the expansion is used in a context where `p` is prime (it is not
otherwise needed). -/
theorem exists_expansion (R : Type u) [CommRing R] [IsLocalRing R] (p : ℕ) (hp : 0 < p) {d : ℕ}
    (z : Fin d → R) (hm : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal R)
    (hperf : ∀ x : R, ∃ μ : R, x - μ ^ p ∈ IsLocalRing.maximalIdeal R) (x : R) :
    ∃ (μ : (Fin d → ℕ) → R) (r : ℕ → R), (∀ N, r N ∈ IsLocalRing.maximalIdeal R ^ N) ∧
      ∀ N, x = ((Work.DSSER.wordList d N).map (fun w => μ w ^ p * Work.DSSER.zMono z w)).sum + r N := by
  exact ⟨digMu p z hm hperf x, digSeq p z hm hperf x, digSeq_mem p z hm hperf x,
    digSeq_expansion p z hm hperf x⟩

end Work.DSSER
