import Mathlib
import Submission.Work.FIArea1.conjunct2_defs

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The fiber bound for the prime substitution of *FI* (5.22)

The proof is elementary.  Write `|z| = gnorm z` for the square of the complex absolute value of a
Gaussian integer.  Given `W ≠ 0`, a real `q > 1` and a finset `s` of Gaussian primes `π` with
`|π| > q` and `π ∣ W`, we must show

`♯s ≤ 4 · (1 + log|W| / log q)`.

The argument is an induction on `|W|`:

* if `s` is empty there is nothing to prove;
* otherwise pick `π₀ ∈ s` and write `W = π₀ · W'`.  Every `π ∈ s` is either associated to `π₀`
  (there are at most `4` such, the four units of `ℤ[i]` being `±1`, `±i`), or satisfies `π ∣ W'`
  (because `π` is prime and `π ∤ π₀`).  So
  `♯s ≤ 4 + ♯{π ∈ s : π ∤ π₀}`, and the second term is controlled by the induction hypothesis
  applied to `W'`, since `|W| = |π₀| · |W'| ≥ 2|W'|`;
* `log|W'| = log|W| − log|π₀| < log|W| − log q` turns the induction hypothesis for `W'`
  into the claim for `W`.

The helper lemmas below are the two arithmetic inputs: the units of `ℤ[i]` are `±1, ±i`
(`mem_dvdCardU4_of_isUnit`), and hence a fixed Gaussian integer has at most four associates
(`card_filter_associated_le_four`). -/

/-- The four units `±1, ±i` of `ℤ[i]`, as an explicit finset. -/
def dvdCardU4 : Finset GaussianInt :=
  {1, -1, (⟨0, 1⟩ : GaussianInt), (⟨0, -1⟩ : GaussianInt)}

lemma dvdCardU4_card : dvdCardU4.card = 4 := by
  rw [dvdCardU4]; decide

lemma mem_dvdCardU4_iff (u : GaussianInt) :
    u ∈ dvdCardU4 ↔ u = 1 ∨ u = -1 ∨ u = (⟨0, 1⟩ : GaussianInt)
      ∨ u = (⟨0, -1⟩ : GaussianInt) := by
  rw [dvdCardU4]; simp

/-- `gnorm` vanishes only at `0`. -/
lemma dvdCard_gnorm_eq_zero_iff (z : GaussianInt) : Work.FIPlan.gnorm z = 0 ↔ z = 0 := by
  rw [Work.FIPlan.gnorm, Int.natAbs_eq_zero, GaussianInt.norm_eq_zero]

/-- **Every unit of `ℤ[i]` is `±1` or `±i`.**  Indeed `IsUnit u` forces `gnorm u = 1`
(`Zsqrtd.norm_eq_one_iff`), i.e. `u.re ^ 2 + u.im ^ 2 = 1`, which in `ℤ` has exactly the four
solutions `(±1, 0)` and `(0, ±1)`. -/
lemma mem_dvdCardU4_of_isUnit (u : GaussianInt) (h : IsUnit u) : u ∈ dvdCardU4 := by
  have hg : Work.FIPlan.gnorm u = 1 := Zsqrtd.norm_eq_one_iff.mpr h
  have h2 : u.re ^ 2 + u.im ^ 2 = 1 := by
    have hg2 := Work.FIArea1.gnorm_int u
    rw [hg] at hg2
    norm_num at hg2
    exact hg2.symm
  have hre_le : u.re ^ 2 ≤ 1 := by nlinarith [sq_nonneg u.im, h2]
  have him_le : u.im ^ 2 ≤ 1 := by nlinarith [sq_nonneg u.re, h2]
  have hre : u.re ^ 2 = 0 ∨ u.re ^ 2 = 1 := by omega
  have him : u.im ^ 2 = 0 ∨ u.im ^ 2 = 1 := by omega
  rcases hre with hre | hre <;> rcases him with him | him
  · omega
  · have hre0 : u.re = 0 := sq_eq_zero_iff.mp hre
    rcases sq_eq_one_iff.mp him with h | h
    · refine (mem_dvdCardU4_iff u).mpr (Or.inr (Or.inr (Or.inl ?_)))
      exact Zsqrtd.ext (by simpa using hre0) (by simpa using h)
    · refine (mem_dvdCardU4_iff u).mpr (Or.inr (Or.inr (Or.inr ?_)))
      exact Zsqrtd.ext (by simpa using hre0) (by simpa using h)
  · have him0 : u.im = 0 := sq_eq_zero_iff.mp him
    rcases sq_eq_one_iff.mp hre with h | h
    · refine (mem_dvdCardU4_iff u).mpr (Or.inl ?_)
      exact Zsqrtd.ext (by simpa using h) (by simpa using him0)
    · refine (mem_dvdCardU4_iff u).mpr (Or.inr (Or.inl ?_))
      exact Zsqrtd.ext (by simpa using h) (by simpa using him0)
  · omega

/-- **At most four elements of a finset are associates of a fixed `π₀`.**  The associates of `π₀`
are the `π₀ · u` with `u` a unit, and the units are the four elements of `dvdCardU4`. -/
lemma card_filter_associated_le_four (π0 : GaussianInt) (s : Finset GaussianInt) :
    (s.filter (fun π => Associated π π0)).card ≤ 4 := by
  have hsub : s.filter (fun π => Associated π π0) ⊆ dvdCardU4.image (fun u => π0 * u) := by
    intro π hπ
    rw [Finset.mem_filter] at hπ
    obtain ⟨-, hassoc⟩ := hπ
    obtain ⟨v, hv⟩ := hassoc
    refine Finset.mem_image.mpr ⟨↑(v⁻¹), mem_dvdCardU4_of_isUnit _ (v⁻¹).isUnit, ?_⟩
    have hv1 : (↑v : GaussianInt) * ↑(v⁻¹) = 1 := Units.mul_inv v
    rw [← hv, mul_assoc, hv1, mul_one]
  calc (s.filter (fun π => Associated π π0)).card
      ≤ (dvdCardU4.image (fun u => π0 * u)).card := Finset.card_le_card hsub
    _ ≤ dvdCardU4.card := Finset.card_image_le
    _ = 4 := dvdCardU4_card

/-- **The fiber bound for the prime substitution of *FI* (5.22).**

A Gaussian integer `W ≠ 0` has at most `≪ 1 + log|W|²/log q` Gaussian prime divisors of norm
`> q`: if `π₁, …, π_k` are pairwise non-associate primes dividing `W` then `π₁⋯π_k ∣ W`, hence
`q^k < ∏ |πᵢ|² ≤ |W|²`.  Counting associates it suffices to bound `♯s ≤ 4k`.  This is the factor
`(log MN)^{2}` of the paper's bound `D̃(M,N) ≪ τ²D(MP₁, NP₁^{-1})(log MN)²`, the number of primes
`π` of norm in `(P₁,2P₁]` that can arise for one substituted triple. -/
theorem gauss_prime_dvd_card_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : GaussianInt) (q : ℝ) (s : Finset GaussianInt),
      W ≠ 0 → 1 < q →
      (∀ π ∈ s, Prime π ∧ q < (Work.FIPlan.gnorm π : ℝ) ∧ π ∣ W) →
      ((s.card : ℝ)) ≤ C * (1 + Real.log ((Work.FIPlan.gnorm W : ℝ) + 2) / Real.log q) := by
  refine ⟨4, by norm_num, ?_⟩
  intro W q s hW hq hs
  have hq1 : (0 : ℝ) < q := lt_trans zero_lt_one hq
  have hlogq : 0 < Real.log q := Real.log_pos hq
  -- a nonzero Gaussian integer has `gnorm ≥ 1`
  have hnorm1 : ∀ {z : GaussianInt}, z ≠ 0 → 1 ≤ Work.FIPlan.gnorm z := by
    intro z hz
    exact Nat.one_le_iff_ne_zero.mpr (fun h => hz ((dvdCard_gnorm_eq_zero_iff z).mp h))
  -- the induction on `|W|`
  have key : ∀ n : ℕ, ∀ (W : GaussianInt), Work.FIPlan.gnorm W ≤ n → W ≠ 0 →
      ∀ s : Finset GaussianInt,
        (∀ π ∈ s, Prime π ∧ q < (Work.FIPlan.gnorm π : ℝ) ∧ π ∣ W) →
        (s.card : ℝ) ≤ 4 + 4 * (Real.log (Work.FIPlan.gnorm W : ℝ) / Real.log q) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W hn hW s hs
      by_cases hne : s = ∅
      · -- empty `s`
        subst hne
        simp only [Finset.card_empty, Nat.cast_zero]
        have h1 : (1 : ℝ) ≤ (Work.FIPlan.gnorm W : ℝ) := by exact_mod_cast hnorm1 hW
        have : 0 ≤ Real.log (Work.FIPlan.gnorm W : ℝ) / Real.log q :=
          div_nonneg (Real.log_nonneg h1) (le_of_lt hlogq)
        linarith
      · -- pick `π₀ ∈ s` and divide `W` by it
        obtain ⟨π0, hπ0s⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        obtain ⟨hprime0, hqπ0, hπ0dvd⟩ := hs π0 hπ0s
        obtain ⟨W', hW'eq⟩ := hπ0dvd
        have hW'ne : W' ≠ 0 := by
          intro h0
          exact hW (by rw [hW'eq, h0, mul_zero])
        have hgn : Work.FIPlan.gnorm W = Work.FIPlan.gnorm π0 * Work.FIPlan.gnorm W' := by
          rw [hW'eq, Work.FIArea1.gnorm_mul]
        have hπ0ne0 : Work.FIPlan.gnorm π0 ≠ 0 :=
          fun h => hprime0.ne_zero ((dvdCard_gnorm_eq_zero_iff π0).mp h)
        have hW'ne0 : Work.FIPlan.gnorm W' ≠ 0 :=
          fun h => hW'ne ((dvdCard_gnorm_eq_zero_iff W').mp h)
        have hπ0ge2 : 2 ≤ Work.FIPlan.gnorm π0 := by
          have h1 : Work.FIPlan.gnorm π0 ≠ 1 :=
            fun h => hprime0.not_isUnit (Zsqrtd.norm_eq_one_iff.mp h)
          omega
        -- `W'` is strictly smaller, so the induction hypothesis applies to it
        have hlt : Work.FIPlan.gnorm W' < n := by
          have h1 : 1 ≤ Work.FIPlan.gnorm W' := hnorm1 hW'ne
          have h2 : 2 * Work.FIPlan.gnorm W' ≤ Work.FIPlan.gnorm W := by
            rw [hgn]; exact Nat.mul_le_mul_right _ hπ0ge2
          omega
        -- split `s` into the associates of `π₀` and the rest
        have hsub : (s.filter (fun π => Associated π π0)).card ≤ 4 :=
          card_filter_associated_le_four π0 s
        have hIH : ((s.filter (fun π => ¬ Associated π π0)).card : ℝ) ≤
            4 + 4 * (Real.log (Work.FIPlan.gnorm W' : ℝ) / Real.log q) := by
          refine ih (Work.FIPlan.gnorm W') hlt W' le_rfl hW'ne _ ?_
          intro π hπ
          rw [Finset.mem_filter] at hπ
          obtain ⟨hπs, hnotassoc⟩ := hπ
          obtain ⟨hpπ, hqπ, hπdvd⟩ := hs π hπs
          refine ⟨hpπ, hqπ, ?_⟩
          rw [hW'eq] at hπdvd
          rcases hpπ.dvd_or_dvd hπdvd with h | h
          · exact absurd (Prime.associated_of_dvd hpπ hprime0 h) hnotassoc
          · exact h
        have hcard : (s.card : ℝ) =
            ((s.filter (fun π => Associated π π0)).card : ℝ) +
            ((s.filter (fun π => ¬ Associated π π0)).card : ℝ) := by
          have h := Finset.card_filter_add_card_filter_not (s := s)
            (p := fun π => Associated π π0)
          rw [← h]; push_cast; ring
        have h1sub : ((s.filter (fun π => Associated π π0)).card : ℝ) ≤ 4 := by
          exact_mod_cast hsub
        -- the logarithmic gain from dividing by `π₀`
        have hlogmul : Real.log (Work.FIPlan.gnorm W : ℝ) =
            Real.log (Work.FIPlan.gnorm π0 : ℝ) + Real.log (Work.FIPlan.gnorm W' : ℝ) := by
          rw [hgn, Nat.cast_mul,
            Real.log_mul (Nat.cast_ne_zero.mpr hπ0ne0) (Nat.cast_ne_zero.mpr hW'ne0)]
        have hloglt : Real.log (Work.FIPlan.gnorm W' : ℝ) <
            Real.log (Work.FIPlan.gnorm W : ℝ) - Real.log q := by
          have hπ0q : Real.log q < Real.log (Work.FIPlan.gnorm π0 : ℝ) :=
            Real.log_lt_log hq1 hqπ0
          linarith [hlogmul]
        have hdivlt : Real.log (Work.FIPlan.gnorm W' : ℝ) / Real.log q <
            Real.log (Work.FIPlan.gnorm W : ℝ) / Real.log q - 1 := by
          have hA : Real.log (Work.FIPlan.gnorm W' : ℝ) / Real.log q <
              (Real.log (Work.FIPlan.gnorm W : ℝ) - Real.log q) / Real.log q :=
            div_lt_div_of_pos_right hloglt hlogq
          have hB : (Real.log (Work.FIPlan.gnorm W : ℝ) - Real.log q) / Real.log q =
              Real.log (Work.FIPlan.gnorm W : ℝ) / Real.log q - 1 := by
            field_simp
          linarith [hA, hB]
        linarith [hcard, h1sub, hIH, hdivlt]
  have hkey := key (Work.FIPlan.gnorm W) W le_rfl hW s hs
  have hlogmono : Real.log (Work.FIPlan.gnorm W : ℝ) ≤
      Real.log ((Work.FIPlan.gnorm W : ℝ) + 2) := by
    apply Real.log_le_log
    · have h1 : (1 : ℝ) ≤ (Work.FIPlan.gnorm W : ℝ) := by exact_mod_cast hnorm1 hW
      linarith
    · linarith
  have hdiv : Real.log (Work.FIPlan.gnorm W : ℝ) / Real.log q ≤
      Real.log ((Work.FIPlan.gnorm W : ℝ) + 2) / Real.log q :=
    div_le_div_of_nonneg_right hlogmono (le_of_lt hlogq)
  calc (s.card : ℝ) ≤ 4 + 4 * (Real.log (Work.FIPlan.gnorm W : ℝ) / Real.log q) := hkey
    _ ≤ 4 * (1 + Real.log ((Work.FIPlan.gnorm W : ℝ) + 2) / Real.log q) := by linarith

end

end Work.FIArea1
