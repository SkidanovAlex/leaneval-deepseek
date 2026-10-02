/-
# `Work.Deep.Conc.BruhnJoos.bruhn_joos_talagrand`

**The Bruhn–Joos concentration inequality with exceptional outcomes.**

For a random variable `X` on the uniform product space `∀ i, π i` which

* is bounded, `|X ω| ≤ M`, and
* satisfies `(s, c)`-certificates off an exceptional set `Ω*` of probability at most `M⁻²`,
  i.e. from every `ω ∉ Ω*` and level `u > 0` one can find `≤ s` coordinates such that any
  `ω' ∉ Ω*` agreeing with `ω` there up to fewer than `u/c` disagreements has `X ω' < X ω + u`,

one has, for `t > 50 c √s`,

  `P(|X - E X| ≥ t) ≤ 4 exp(-t²/(16 c² s)) + 4 P(Ω*)`.

The proof has three ingredients, all of which are developed here or in sibling modules:

* the certified two-set form of Talagrand's convex-distance inequality
  (`BruhnJoos.talagrand_certified`, proved in the parallel `Deep/Reed` subproject) turns the
  certificate hypothesis into the level-set estimate
  `P(X ≥ a+h, Ω*ᶜ) · P(X ≤ a, Ω*ᶜ) ≤ exp(-h²/(4c²s))`  (`two_set_level`);
* a median `m` of `X` (`exists_median`) together with this estimate bounds the two tails of
  `|X - m|` above by `4 exp(-u²/(4c²s)) + P(Ω*)` (`upper_tail`, `lower_tail`);
* integrating the tails over a grid (`expect_le_grid`, `sum_exp_neg_sq_le`) shows
  `|E X - m| ≤ 16 c √s`, and the remaining numerical comparison of the two exponentials is
  `exp_tail_comparison`.

The truncation at the level sets, the grid sum and the exceptional set `Ω*` are what allow the
bound to cope with statistics whose coordinate effects are rare but large (e.g. an edge that
creates a monochromatic double star), where bounded differences fails.
-/
import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Conc.Basic
import Submission.Work.Deep.Conc.Pi
import Submission.Work.Deep.Conc.BruhnJoos.talagrand_two_set
import Submission.Work.Deep.Conc.BruhnJoos.talagrand_certified
import Submission.Work.Deep.Conc.BruhnJoos.expect_le_grid
import Submission.Work.Deep.Conc.BruhnJoos.exists_median
import Submission.Work.Deep.Conc.BruhnJoos.sum_exp_neg_sq_le
import Submission.Work.Deep.Conc.BruhnJoos.exp_tail_comparison

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Finset

namespace Work.Deep.Conc.BruhnJoos

open Work.Deep.Conc

section Basic

variable {Ω : Type*} [Fintype Ω]

/-- Complementing an event: `P(S) ≤ P(S \ T) + P(T)`. -/
lemma prob_le_prob_sdiff_add (S T : Set Ω) : prob S ≤ prob (S \ T) + prob T := by
  have hsub : S ⊆ (S \ T) ∪ T := by
    intro x hx
    by_cases h : x ∈ T
    · exact Or.inr h
    · exact Or.inl ⟨hx, h⟩
  exact le_trans (prob_mono hsub) (prob_union_le _ _)

/-- `P(S) - P(T) ≤ P(S \ T)`. -/
lemma prob_sdiff_ge (S T : Set Ω) : prob S - prob T ≤ prob (S \ T) := by
  linarith [prob_le_prob_sdiff_add S T]

end Basic

section TwoSet

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {π : ι → Type*} [∀ i, Fintype (π i)] [∀ i, DecidableEq (π i)]

/-- **Level-set form of the certified Talagrand inequality.**  Under the certificate
hypothesis off `Ω*`, any upper level set `{X ≥ a+h}` and lower level set `{X ≤ a}`, restricted
to the non-exceptional outcomes, satisfy `P(A) P(B) ≤ exp(-h²/(4c²s))`. -/
theorem two_set_level (hne : ∀ i, Nonempty (π i)) (X : (∀ i, π i) → ℝ)
    (c : ℝ) (hc : 1 ≤ c) (s : ℕ) (hs : 1 ≤ s) (Ωstar : Set (∀ i, π i))
    (hcert : ∀ u : ℝ, 0 < u → ∀ ω, ω ∉ Ωstar → ∃ I : Finset ι, I.card ≤ s ∧
      ∀ ω', ω' ∉ Ωstar → ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) < u / c →
        X ω' < X ω + u) :
    ∀ a h : ℝ, 0 < h →
      prob ({ω | a + h ≤ X ω} ∩ Ωstarᶜ) * prob ({ω | X ω ≤ a} ∩ Ωstarᶜ)
        ≤ Real.exp (- h ^ 2 / (4 * c ^ 2 * (s : ℝ))) := by
  intro a h hh
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hcert' : ∀ ω ∈ ({ω | X ω ≤ a} ∩ Ωstarᶜ),
      ∃ I : Finset ι, I.card ≤ s ∧
        ∀ ω' ∈ ({ω | a + h ≤ X ω} ∩ Ωstarᶜ),
          h / c ≤ ∑ i ∈ I, (if ω i ≠ ω' i then (1 : ℝ) else 0) := by
    intro ω hω
    have hωX : X ω ≤ a := by simpa using hω.1
    have hωΩ : ω ∉ Ωstar := hω.2
    have hu : 0 < a + h - X ω := by linarith
    obtain ⟨I, hIcard, hI⟩ := hcert (a + h - X ω) hu ω hωΩ
    refine ⟨I, hIcard, fun ω' hω' => ?_⟩
    have hω'X : a + h ≤ X ω' := by simpa using hω'.1
    have hω'Ω : ω' ∉ Ωstar := hω'.2
    have hle : (a + h - X ω) / c ≤ ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) := by
      by_contra hlt
      rw [not_le] at hlt
      have := hI ω' hω'Ω hlt
      linarith
    have hcard : ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ)
        = ∑ i ∈ I, (if ω i ≠ ω' i then (1 : ℝ) else 0) := by
      rw [Finset.card_filter, Nat.cast_sum]
      exact Finset.sum_congr rfl fun i _ => by by_cases h : ω i ≠ ω' i <;> simp [h]
    calc h / c ≤ (a + h - X ω) / c := div_le_div_of_nonneg_right (by linarith) hcpos.le
      _ ≤ ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) := hle
      _ = ∑ i ∈ I, (if ω i ≠ ω' i then (1 : ℝ) else 0) := hcard
  have key := talagrand_certified hne ({ω | a + h ≤ X ω} ∩ Ωstarᶜ) ({ω | X ω ≤ a} ∩ Ωstarᶜ)
      (h / c) (div_nonneg hh.le hcpos.le) s hs hcert'
  have hexp : - (h / c) ^ 2 / (4 * (s : ℝ)) = - h ^ 2 / (4 * c ^ 2 * (s : ℝ)) := by
    field_simp
  rwa [hexp] at key

/-- **Upper tail off the exceptional set.** -/
theorem upper_tail (hne : ∀ i, Nonempty (π i)) (X : (∀ i, π i) → ℝ)
    (c : ℝ) (hc : 1 ≤ c) (s : ℕ) (hs : 1 ≤ s) (Ωstar : Set (∀ i, π i))
    (hcert : ∀ u : ℝ, 0 < u → ∀ ω, ω ∉ Ωstar → ∃ I : Finset ι, I.card ≤ s ∧
      ∀ ω', ω' ∉ Ωstar → ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) < u / c →
        X ω' < X ω + u)
    (m : ℝ) (hm : (1 / 2 : ℝ) ≤ prob {ω | X ω ≤ m})
    (hp : prob Ωstar ≤ 1 / 4) :
    ∀ u : ℝ, 0 ≤ u → prob {ω | m + u ≤ X ω}
      ≤ 4 * Real.exp (- u ^ 2 / (4 * c ^ 2 * (s : ℝ))) + prob Ωstar := by
  intro u hu
  haveI : Nonempty (∀ i, π i) := ⟨fun i => Classical.choice (hne i)⟩
  rcases eq_or_lt_of_le hu with h0 | hpos
  · subst h0
    have h1 : prob {ω : ∀ i, π i | m + 0 ≤ X ω} ≤ 1 := prob_le_one _ Fintype.card_pos
    have h2 : 4 * Real.exp (- (0 : ℝ) ^ 2 / (4 * c ^ 2 * (s : ℝ))) + prob Ωstar
        = 4 + prob Ωstar := by simp
    rw [h2]
    linarith [prob_nonneg Ωstar]
  · have hB : (1 / 4 : ℝ) ≤ prob ({ω | X ω ≤ m} ∩ Ωstarᶜ) := by
      have h := prob_sdiff_ge (S := {ω | X ω ≤ m}) (T := Ωstar)
      rw [Set.diff_eq] at h
      linarith
    have hts := two_set_level hne X c hc s hs Ωstar hcert m u hpos
    have hA : prob ({ω | m + u ≤ X ω} ∩ Ωstarᶜ)
        ≤ 4 * Real.exp (- u ^ 2 / (4 * c ^ 2 * (s : ℝ))) := by
      have hA0 : 0 ≤ prob ({ω | m + u ≤ X ω} ∩ Ωstarᶜ) := prob_nonneg _
      have h1 : prob ({ω | m + u ≤ X ω} ∩ Ωstarᶜ) * (1 / 4)
          ≤ Real.exp (- u ^ 2 / (4 * c ^ 2 * (s : ℝ))) :=
        le_trans (mul_le_mul_of_nonneg_left hB hA0) hts
      have h4 : (0 : ℝ) < 1 / 4 := by norm_num
      calc prob ({ω | m + u ≤ X ω} ∩ Ωstarᶜ)
          = prob ({ω | m + u ≤ X ω} ∩ Ωstarᶜ) * (1 / 4) / (1 / 4) := by ring
        _ ≤ Real.exp (- u ^ 2 / (4 * c ^ 2 * (s : ℝ))) / (1 / 4) :=
            div_le_div_of_nonneg_right h1 h4.le
        _ = 4 * Real.exp (- u ^ 2 / (4 * c ^ 2 * (s : ℝ))) := by ring
    have hP : prob {ω | m + u ≤ X ω}
        ≤ prob ({ω | m + u ≤ X ω} ∩ Ωstarᶜ) + prob Ωstar := by
      have h := prob_le_prob_sdiff_add {ω | m + u ≤ X ω} Ωstar
      rwa [Set.diff_eq] at h
    linarith

/-- **Lower tail off the exceptional set.** -/
theorem lower_tail (hne : ∀ i, Nonempty (π i)) (X : (∀ i, π i) → ℝ)
    (c : ℝ) (hc : 1 ≤ c) (s : ℕ) (hs : 1 ≤ s) (Ωstar : Set (∀ i, π i))
    (hcert : ∀ u : ℝ, 0 < u → ∀ ω, ω ∉ Ωstar → ∃ I : Finset ι, I.card ≤ s ∧
      ∀ ω', ω' ∉ Ωstar → ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) < u / c →
        X ω' < X ω + u)
    (m : ℝ) (hm : (1 / 2 : ℝ) ≤ prob {ω | m ≤ X ω})
    (hp : prob Ωstar ≤ 1 / 4) :
    ∀ u : ℝ, 0 ≤ u → prob {ω | X ω ≤ m - u}
      ≤ 4 * Real.exp (- u ^ 2 / (4 * c ^ 2 * (s : ℝ))) + prob Ωstar := by
  intro u hu
  haveI : Nonempty (∀ i, π i) := ⟨fun i => Classical.choice (hne i)⟩
  rcases eq_or_lt_of_le hu with h0 | hpos
  · subst h0
    have h1 : prob {ω : ∀ i, π i | X ω ≤ m - 0} ≤ 1 := prob_le_one _ Fintype.card_pos
    have h2 : 4 * Real.exp (- (0 : ℝ) ^ 2 / (4 * c ^ 2 * (s : ℝ))) + prob Ωstar
        = 4 + prob Ωstar := by simp
    rw [h2]
    linarith [prob_nonneg Ωstar]
  · have hB : (1 / 4 : ℝ) ≤ prob ({ω | m ≤ X ω} ∩ Ωstarᶜ) := by
      have h := prob_sdiff_ge (S := {ω | m ≤ X ω}) (T := Ωstar)
      rw [Set.diff_eq] at h
      linarith
    have hts := two_set_level hne X c hc s hs Ωstar hcert (m - u) u hpos
    have hsub : ({ω | (m - u) + u ≤ X ω} : Set (∀ i, π i)) = {ω | m ≤ X ω} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor <;> intro h <;> linarith
    rw [hsub] at hts
    have hA : prob ({ω | X ω ≤ m - u} ∩ Ωstarᶜ)
        ≤ 4 * Real.exp (- u ^ 2 / (4 * c ^ 2 * (s : ℝ))) := by
      have hA0 : 0 ≤ prob ({ω | X ω ≤ m - u} ∩ Ωstarᶜ) := prob_nonneg _
      have hcomm : prob ({ω | m ≤ X ω} ∩ Ωstarᶜ) * prob ({ω | X ω ≤ m - u} ∩ Ωstarᶜ)
          = prob ({ω | X ω ≤ m - u} ∩ Ωstarᶜ) * prob ({ω | m ≤ X ω} ∩ Ωstarᶜ) := by ring
      rw [hcomm] at hts
      have h1 : prob ({ω | X ω ≤ m - u} ∩ Ωstarᶜ) * (1 / 4)
          ≤ Real.exp (- u ^ 2 / (4 * c ^ 2 * (s : ℝ))) :=
        le_trans (mul_le_mul_of_nonneg_left hB hA0) hts
      have h4 : (0 : ℝ) < 1 / 4 := by norm_num
      calc prob ({ω | X ω ≤ m - u} ∩ Ωstarᶜ)
          = prob ({ω | X ω ≤ m - u} ∩ Ωstarᶜ) * (1 / 4) / (1 / 4) := by ring
        _ ≤ Real.exp (- u ^ 2 / (4 * c ^ 2 * (s : ℝ))) / (1 / 4) :=
            div_le_div_of_nonneg_right h1 h4.le
        _ = 4 * Real.exp (- u ^ 2 / (4 * c ^ 2 * (s : ℝ))) := by ring
    have hP : prob {ω | X ω ≤ m - u}
        ≤ prob ({ω | X ω ≤ m - u} ∩ Ωstarᶜ) + prob Ωstar := by
      have h := prob_le_prob_sdiff_add {ω | X ω ≤ m - u} Ωstar
      rwa [Set.diff_eq] at h
    linarith

/-- **Grid bound on the one-sided excess.**  If every level set `{X ≥ m + u}` of the
nonnegative function `Y = (X - m)⁺` away from `Ω*` has probability at most
`4 exp(-u²/(4c²s)) + P(Ω*)` (and `0 ≤ Y ≤ 2M`, `P(Ω*) ≤ M⁻²`), then `E Y ≤ 16 c √s`. -/
theorem grid_expect_le (hne : ∀ i, Nonempty (π i)) (X : (∀ i, π i) → ℝ)
    (m : ℝ) (M c : ℝ) (s : ℕ) (hM : 1 ≤ M) (hmM : |m| ≤ M)
    (hXabs : ∀ ω, |X ω| ≤ M) (hc : 1 ≤ c) (hs : 1 ≤ s) (Ωstar : Set (∀ i, π i))
    (hexc : prob Ωstar ≤ 1 / M ^ 2)
    (hupper : ∀ u : ℝ, 0 ≤ u → prob {ω | m + u ≤ X ω}
      ≤ 4 * Real.exp (- u ^ 2 / (4 * c ^ 2 * (s : ℝ))) + prob Ωstar) :
    expect (fun ω => max (X ω - m) 0) ≤ 16 * c * Real.sqrt (s : ℝ) := by
  haveI : Nonempty (∀ i, π i) := ⟨fun i => Classical.choice (hne i)⟩
  set K : ℝ := 4 * c ^ 2 * (s : ℝ) with hK
  set δ : ℝ := 2 * c * Real.sqrt (s : ℝ) with hδ
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hKpos : 0 < K := by rw [hK]; positivity
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδsq : δ ^ 2 = K := by
    rw [hδ, hK, mul_pow, mul_pow, Real.sq_sqrt hsR.le]
    ring
  have hcs : 1 ≤ c * Real.sqrt (s : ℝ) := by
    have h1 : 1 ≤ Real.sqrt (s : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hs)
    nlinarith
  set n : ℕ := Nat.floor (2 * M / δ) + 1 with hn
  have hL : (0 : ℝ) < 2 * M := by linarith
  have hn' : 2 * M < (n : ℝ) * δ := by
    rw [hn, Nat.cast_add, Nat.cast_one]
    have h := Nat.lt_floor_add_one (2 * M / δ)
    have h2 := mul_lt_mul_of_pos_right h hδpos
    rwa [div_mul_cancel₀ _ (ne_of_gt hδpos)] at h2
  have hY0 : ∀ ω, 0 ≤ max (X ω - m) 0 := fun ω => le_max_right _ _
  have hYL : ∀ ω, max (X ω - m) 0 ≤ 2 * M := by
    intro ω
    have h1 : X ω ≤ M := (abs_le.mp (hXabs ω)).2
    have h2 : -M ≤ m := (abs_le.mp hmM).1
    have h3 : X ω - m ≤ 2 * M := by linarith
    exact max_le h3 (by linarith)
  have hgrid := expect_le_grid (fun ω => max (X ω - m) 0) hδpos hL hY0 hYL hn'
  -- each grid term is bounded by the exponential tail bound
  have harg : ∀ k : ℕ, - (((k : ℝ) * δ) ^ 2) / K = - ((k : ℝ) ^ 2) := by
    intro k
    rw [mul_pow, hδsq]
    field_simp
  have hterm : ∀ k ∈ Finset.range n,
      prob {ω | (k : ℝ) * δ ≤ max (X ω - m) 0}
        ≤ 4 * Real.exp (- ((k : ℝ) ^ 2)) + prob Ωstar := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      have h1 : prob {ω : ∀ i, π i | ((0 : ℕ) : ℝ) * δ ≤ max (X ω - m) 0} ≤ 1 :=
        prob_le_one _ Fintype.card_pos
      have h2 : Real.exp (- (((0 : ℕ) : ℝ) ^ 2)) = 1 := by norm_num
      rw [h2]
      linarith [prob_nonneg Ωstar]
    · have hkpos' : 0 < (k : ℝ) * δ := by
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
        nlinarith
      have hset : {ω | (k : ℝ) * δ ≤ max (X ω - m) 0} = {ω | m + (k : ℝ) * δ ≤ X ω} := by
        ext ω
        simp only [Set.mem_setOf_eq]
        constructor
        · intro h
          have h0 : (0 : ℝ) ≤ X ω - m := by
            by_contra hc0
            rw [not_le] at hc0
            have : max (X ω - m) 0 = 0 := max_eq_right hc0.le
            linarith
          rw [max_eq_left h0] at h
          linarith
        · intro h
          have h0 : (0 : ℝ) ≤ X ω - m := by linarith
          rw [max_eq_left h0]
          linarith
      have h := hupper ((k : ℝ) * δ) hkpos'.le
      rw [harg k] at h
      rw [hset]
      exact h
  have hsum_bound : (∑ k ∈ Finset.range n, prob {ω | (k : ℝ) * δ ≤ max (X ω - m) 0})
      ≤ ∑ k ∈ Finset.range n, (4 * Real.exp (- ((k : ℝ) ^ 2)) + prob Ωstar) :=
    Finset.sum_le_sum hterm
  have hsumid : (∑ k ∈ Finset.range n,
        (4 * Real.exp (- ((k : ℝ) ^ 2)) + prob Ωstar))
      = 4 * (∑ k ∈ Finset.range n, Real.exp (- ((k : ℝ) ^ 2)))
        + (n : ℝ) * prob Ωstar := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hnp : δ * (n : ℝ) * prob Ωstar ≤ 4 * c * Real.sqrt (s : ℝ) := by
    have hnδ : (n : ℝ) * δ ≤ 2 * M + δ := by
      have hf : (((Nat.floor (2 * M / δ)) : ℕ) : ℝ) ≤ 2 * M / δ :=
        Nat.floor_le (by positivity)
      have hcast : (n : ℝ) = (((Nat.floor (2 * M / δ)) : ℕ) : ℝ) + 1 := by
        rw [hn, Nat.cast_add, Nat.cast_one]
      rw [hcast, add_mul, one_mul]
      have h2 : (((Nat.floor (2 * M / δ)) : ℕ) : ℝ) * δ ≤ (2 * M / δ) * δ :=
        mul_le_mul_of_nonneg_right hf hδpos.le
      rw [div_mul_cancel₀ _ (ne_of_gt hδpos)] at h2
      linarith
    have h1 : δ * (n : ℝ) * prob Ωstar ≤ (2 * M + δ) * prob Ωstar := by
      have h3 : δ * (n : ℝ) = (n : ℝ) * δ := by ring
      rw [h3]
      exact mul_le_mul_of_nonneg_right hnδ (prob_nonneg Ωstar)
    refine le_trans h1 ?_
    refine le_trans (mul_le_mul_of_nonneg_left hexc (by linarith : (0 : ℝ) ≤ 2 * M + δ)) ?_
    have h3 : (2 * M + δ) * (1 / M ^ 2) ≤ 2 + δ := by
      rw [mul_one_div, div_le_iff₀ (by positivity : (0 : ℝ) < M ^ 2)]
      have hfac : (2 + δ) * M ^ 2 - (2 * M + δ) = (M - 1) * (2 * M + δ * (M + 1)) := by ring
      have hnn : 0 ≤ (M - 1) * (2 * M + δ * (M + 1)) :=
        mul_nonneg (by linarith) (by nlinarith [hδpos.le, hM])
      linarith
    have h4 : 2 + δ ≤ 4 * c * Real.sqrt (s : ℝ) := by
      rw [hδ]
      linarith
    linarith
  calc expect (fun ω => max (X ω - m) 0)
      ≤ δ * ∑ k ∈ Finset.range n, prob {ω | (k : ℝ) * δ ≤ max (X ω - m) 0} := hgrid
    _ ≤ δ * ∑ k ∈ Finset.range n, (4 * Real.exp (- ((k : ℝ) ^ 2)) + prob Ωstar) :=
        mul_le_mul_of_nonneg_left hsum_bound hδpos.le
    _ = 4 * δ * (∑ k ∈ Finset.range n, Real.exp (- ((k : ℝ) ^ 2)))
          + δ * (n : ℝ) * prob Ωstar := by
        rw [hsumid]; ring
    _ ≤ 4 * δ * (3 / 2) + δ * (n : ℝ) * prob Ωstar := by
        have hS := sum_exp_neg_sq_le n
        have h4δ : (0 : ℝ) ≤ 4 * δ := by positivity
        have := mul_le_mul_of_nonneg_left hS h4δ
        linarith
    _ ≤ 16 * c * Real.sqrt (s : ℝ) := by
        have h1 : 4 * δ * (3 / 2) = 12 * c * Real.sqrt (s : ℝ) := by rw [hδ]; ring
        linarith

/-- **Median versus mean.**  For a certified bounded random variable off `Ω*`, the mean is
within `16 c √s` of any median. -/
theorem median_to_mean (hne : ∀ i, Nonempty (π i)) (X : (∀ i, π i) → ℝ)
    (M : ℝ) (hM : 1 ≤ M) (hsup : ∀ ω, |X ω| ≤ M)
    (c : ℝ) (hc : 1 ≤ c) (s : ℕ) (hs : 1 ≤ s) (Ωstar : Set (∀ i, π i))
    (hexc : prob Ωstar ≤ 1 / M ^ 2)
    (hcert : ∀ u : ℝ, 0 < u → ∀ ω, ω ∉ Ωstar → ∃ I : Finset ι, I.card ≤ s ∧
      ∀ ω', ω' ∉ Ωstar → ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) < u / c →
        X ω' < X ω + u)
    (hp : prob Ωstar ≤ 1 / 4)
    (m : ℝ) (hmrange : m ∈ Set.range X)
    (hmt : (1 / 2 : ℝ) ≤ prob {ω | X ω ≤ m})
    (hmb : (1 / 2 : ℝ) ≤ prob {ω | m ≤ X ω}) :
    |expect X - m| ≤ 16 * c * Real.sqrt (s : ℝ) := by
  haveI : Nonempty (∀ i, π i) := ⟨fun i => Classical.choice (hne i)⟩
  have hmM : |m| ≤ M := by
    obtain ⟨ω, hω⟩ := hmrange
    rw [← hω]
    exact hsup ω
  have hupper := upper_tail hne X c hc s hs Ωstar hcert m hmt hp
  have hlower := lower_tail hne X c hc s hs Ωstar hcert m hmb hp
  have hE1 := grid_expect_le hne X m M c s hM hmM hsup hc hs Ωstar hexc hupper
  have hE2 : expect (fun ω => max (m - X ω) 0) ≤ 16 * c * Real.sqrt (s : ℝ) := by
    have hneg : expect (fun ω => max ((-X) ω - (-m)) 0) ≤ 16 * c * Real.sqrt (s : ℝ) := by
      refine grid_expect_le hne (fun ω => -X ω) (-m) M c s hM ?_ ?_ hc hs Ωstar hexc ?_
      · simpa using hmM
      · intro ω; simpa using hsup ω
      · intro u hu
        have hset : {ω : ∀ i, π i | -m + u ≤ -X ω} = {ω | X ω ≤ m - u} := by
          ext ω
          simp only [Set.mem_setOf_eq]
          constructor <;> intro h <;> linarith
        rw [hset]
        exact hlower u hu
    have hfun : (fun ω => max (m - X ω) 0) = fun ω => max ((-X) ω - -m) 0 := by
      funext ω
      have hω' : m - X ω = (-X) ω - -m := by simp only [Pi.neg_apply]; ring
      rw [hω']
    rw [hfun]
    exact hneg
  have h1 : expect X - m ≤ 16 * c * Real.sqrt (s : ℝ) := by
    have hsub : expect (fun ω => X ω - m) = expect X - m := by
      have h : (fun ω => X ω - m) = X - (fun _ => m) := rfl
      rw [h, expect_sub, expect_const]
    have hmono : expect (fun ω => X ω - m) ≤ expect (fun ω => max (X ω - m) 0) :=
      expect_mono' (fun ω => le_max_left _ _)
    rw [hsub] at hmono
    linarith
  have h2 : m - expect X ≤ 16 * c * Real.sqrt (s : ℝ) := by
    have hsub : expect (fun ω => m - X ω) = m - expect X := by
      have h : (fun ω => m - X ω) = (fun _ => m) - X := rfl
      rw [h, expect_sub, expect_const]
    have hmono : expect (fun ω => m - X ω) ≤ expect (fun ω => max (m - X ω) 0) :=
      expect_mono' (fun ω => le_max_left _ _)
    rw [hsub] at hmono
    linarith
  exact abs_le.mpr ⟨by linarith, h1⟩

end TwoSet

theorem bruhn_joos_talagrand {ι : Type*} [Fintype ι] [DecidableEq ι]
    {π : ι → Type*} [∀ i, Fintype (π i)] [∀ i, DecidableEq (π i)]
    (hne : ∀ i, Nonempty (π i))
    (X : (∀ i, π i) → ℝ) (M : ℝ) (hM : 1 ≤ M) (hsup : ∀ ω, |X ω| ≤ M)
    (c : ℝ) (hc : 1 ≤ c) (s : ℕ) (hs : 1 ≤ s)
    (Ωstar : Set (∀ i, π i)) (hexc : Work.Deep.Conc.prob Ωstar ≤ 1 / M ^ 2)
    (hcert : ∀ u : ℝ, 0 < u → ∀ ω, ω ∉ Ωstar →
      ∃ I : Finset ι, I.card ≤ s ∧
        ∀ ω', ω' ∉ Ωstar →
          ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) < u / c → X ω' < X ω + u) :
    ∀ t : ℝ, 50 * c * Real.sqrt (s : ℝ) < t →
      Work.Deep.Conc.prob {ω | t ≤ |X ω - Work.Deep.Conc.expect X|}
        ≤ 4 * Real.exp (- t ^ 2 / (16 * c ^ 2 * (s : ℝ))) + 4 * Work.Deep.Conc.prob Ωstar := by
  classical
  intro t ht
  haveI : Nonempty (∀ i, π i) := ⟨fun i => Classical.choice (hne i)⟩
  have hcs : 1 ≤ c * Real.sqrt (s : ℝ) := by
    have h1 : 1 ≤ Real.sqrt (s : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hs)
    nlinarith
  have hexp_pos : 0 < Real.exp (- t ^ 2 / (16 * c ^ 2 * (s : ℝ))) := Real.exp_pos _
  by_cases hp : Work.Deep.Conc.prob Ωstar ≤ 1 / 4
  · obtain ⟨m, hmrange, hmt, hmb⟩ := exists_median X
    have hΔ := median_to_mean hne X M hM hsup c hc s hs Ωstar hexc hcert hp m hmrange hmt hmb
    have hu : 0 < t - 16 * c * Real.sqrt (s : ℝ) := by nlinarith
    have hsub : {ω | t ≤ |X ω - Work.Deep.Conc.expect X|} ⊆
        {ω | m + (t - 16 * c * Real.sqrt (s : ℝ)) ≤ X ω} ∪
        {ω | X ω ≤ m - (t - 16 * c * Real.sqrt (s : ℝ))} := by
      intro ω hω
      have h1 : t ≤ |X ω - m| + 16 * c * Real.sqrt (s : ℝ) := by
        calc t ≤ |X ω - Work.Deep.Conc.expect X| := hω
          _ ≤ |X ω - m| + |m - Work.Deep.Conc.expect X| := abs_sub_le _ _ _
          _ ≤ |X ω - m| + 16 * c * Real.sqrt (s : ℝ) := by
              rw [abs_sub_comm] at hΔ
              linarith
      have h2 : t - 16 * c * Real.sqrt (s : ℝ) ≤ |X ω - m| := by linarith
      rcases abs_cases (X ω - m) with ⟨h, -⟩ | ⟨h, -⟩
      · left
        simp only [Set.mem_ofPred_eq]
        linarith
      · right
        simp only [Set.mem_ofPred_eq]
        linarith
    have hU := upper_tail hne X c hc s hs Ωstar hcert m hmt hp
      (t - 16 * c * Real.sqrt (s : ℝ)) hu.le
    have hL := lower_tail hne X c hc s hs Ωstar hcert m hmb hp
      (t - 16 * c * Real.sqrt (s : ℝ)) hu.le
    have hcmp := exp_tail_comparison hc hs ht
    calc Work.Deep.Conc.prob {ω | t ≤ |X ω - Work.Deep.Conc.expect X|}
        ≤ Work.Deep.Conc.prob
            ({ω | m + (t - 16 * c * Real.sqrt (s : ℝ)) ≤ X ω} ∪
             {ω | X ω ≤ m - (t - 16 * c * Real.sqrt (s : ℝ))}) := prob_mono hsub
      _ ≤ Work.Deep.Conc.prob {ω | m + (t - 16 * c * Real.sqrt (s : ℝ)) ≤ X ω}
            + Work.Deep.Conc.prob {ω | X ω ≤ m - (t - 16 * c * Real.sqrt (s : ℝ))} :=
          prob_union_le _ _
      _ ≤ (4 * Real.exp (- (t - 16 * c * Real.sqrt (s : ℝ)) ^ 2 / (4 * c ^ 2 * (s : ℝ)))
              + Work.Deep.Conc.prob Ωstar)
            + (4 * Real.exp (- (t - 16 * c * Real.sqrt (s : ℝ)) ^ 2 / (4 * c ^ 2 * (s : ℝ)))
              + Work.Deep.Conc.prob Ωstar) := add_le_add hU hL
      _ = 8 * Real.exp (- (t - 16 * c * Real.sqrt (s : ℝ)) ^ 2 / (4 * c ^ 2 * (s : ℝ)))
            + 2 * Work.Deep.Conc.prob Ωstar := by ring
      _ ≤ 4 * Real.exp (- t ^ 2 / (16 * c ^ 2 * (s : ℝ))) + 4 * Work.Deep.Conc.prob Ωstar := by
          have hpnn : (0 : ℝ) ≤ Work.Deep.Conc.prob Ωstar := prob_nonneg Ωstar
          linarith [hcmp]
  · rw [not_le] at hp
    have h1 : Work.Deep.Conc.prob {ω | t ≤ |X ω - Work.Deep.Conc.expect X|} ≤ 1 :=
      prob_le_one _ Fintype.card_pos
    have h2 : (1 : ℝ) ≤ 4 * Real.exp (- t ^ 2 / (16 * c ^ 2 * (s : ℝ)))
        + 4 * Work.Deep.Conc.prob Ωstar := by
      have h3 : (1 : ℝ) ≤ 4 * Work.Deep.Conc.prob Ωstar := by linarith
      linarith
    linarith

end Work.Deep.Conc.BruhnJoos
