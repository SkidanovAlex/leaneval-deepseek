import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Commons.Probability.Chernoff.chernoff_two_sided_finite_weighted

open Finset
open scoped BigOperators

namespace Work.Deep.Prob.Colouring

/-!
# Two-sided Chernoff for a uniform random `K`-colouring, in count form

For a finite set `ι`, weights `X : ι → ℝ` with `0 ≤ X r ≤ C`, a colour `i : Fin K` and a
tolerance `τ ≥ 0`, the number of colourings `c : ι → Fin K` for which the total weight of the
elements coloured `i` deviates from its mean `(∑ r, X r)/K` by at least `τ` is at most
`K ^ (card ι) * 2 * exp (-(τ²) / (2 C ((∑ r, X r)/K + τ/3)))`.

The combinatorial input is that for a fixed colour `i` the map
`c ↦ (r ↦ decide (c r = i))` sends the uniform counting measure on `ι → Fin K` to the
product Bernoulli measure of parameter `1/K`: the fibre of a Boolean pattern `s` has
`∏ r, (if s r then 1 else K - 1)` elements, which equals
`K ^ (card ι) * ∏ r, (if s r then 1/K else 1 - 1/K)`.  This reduces the count to the
weighted Bernoulli Chernoff bound `chernoff_two_sided_finite_weighted`.
-/

/-- In a `K`-colouring, the "type" of an element: `true` if it receives the colour `i`. -/
private lemma factor_eq_one {K : ℕ} (i c : Fin K) {s : Bool} (h : decide (c = i) = s) :
    (if s then (if c = i then (1:ℝ) else 0) else (if c = i then 0 else 1)) = 1 := by
  cases s
  · have hci : c ≠ i := decide_eq_false_iff_not.mp h
    simp [hci]
  · have hci : c = i := by rw [decide_eq_true_iff] at h; exact h
    simp [hci]

/-- Complementary case of `factor_eq_one`. -/
private lemma factor_eq_zero {K : ℕ} (i c : Fin K) {s : Bool} (h : decide (c = i) ≠ s) :
    (if s then (if c = i then (1:ℝ) else 0) else (if c = i then 0 else 1)) = 0 := by
  cases s
  · have hci : c = i := by
      by_contra hne
      exact h (decide_eq_false_iff_not.mpr hne)
    simp [hci]
  · have hci : c ≠ i := by
      intro hcon
      exact h (by simp [hcon])
    simp [hci]

/-- **Independence over the coordinates of a `K`-colouring.**  The sum over all colourings
of the product over coordinates of the "pattern indicator" factors into a product. -/
lemma sum_pattern_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ} (i : Fin K) (s : ι → Bool) :
    (∑ c : ι → Fin K, ∏ r, (if s r then (if c r = i then (1:ℝ) else 0)
        else (if c r = i then 0 else 1)))
      = ∏ r, (if s r then 1 else (K:ℝ) - 1) := by
  have h1 : (∑ c : ι → Fin K, ∏ r, (if s r then (if c r = i then (1:ℝ) else 0)
        else (if c r = i then 0 else 1)))
      = ∏ r : ι, (∑ a : Fin K, (if s r then (if a = i then (1:ℝ) else 0)
        else (if a = i then 0 else 1))) := by
    have h := Finset.sum_prod_piFinset (s := (Finset.univ : Finset (Fin K)))
      (g := fun r a => (if s r then (if a = i then (1:ℝ) else 0)
        else (if a = i then 0 else 1)))
    rw [Fintype.piFinset_univ] at h
    simpa using h
  rw [h1]
  apply Finset.prod_congr rfl
  intro r _
  by_cases hs : s r
  · simp only [hs, if_true]
    rw [Finset.sum_ite_eq']; simp
  · simp only [hs, if_false, Bool.false_eq_true]
    have h1 : (∑ a : Fin K, (1:ℝ)) = (K:ℝ) := by simp
    have h2 : (∑ a : Fin K, (if a = i then (1:ℝ) else 0)) = 1 := by
      rw [Finset.sum_ite_eq']; simp
    have hsplit : (∑ a : Fin K, (if a = i then (0:ℝ) else 1))
        = (∑ a : Fin K, (1:ℝ)) - (∑ a : Fin K, (if a = i then (1:ℝ) else 0)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : a = i <;> simp [h]
    rw [hsplit, h1, h2]

/-- **The size of the fibre of a Boolean pattern.**  The number of `K`-colourings for which
the elements of type `true` are exactly those in `s` is `∏ r, (if s r then 1 else K - 1)`. -/
lemma card_fibre_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ} (i : Fin K) (s : ι → Bool) :
    ((Finset.univ.filter (fun c : ι → Fin K => ∀ r, decide (c r = i) = s r)).card : ℝ)
      = ∏ r, (if s r then (1:ℝ) else (K:ℝ) - 1) := by
  have hcard : ((Finset.univ.filter (fun c : ι → Fin K => ∀ r, decide (c r = i) = s r)).card : ℝ)
      = ∑ c ∈ (Finset.univ.filter (fun c : ι → Fin K => ∀ r, decide (c r = i) = s r)), (1:ℝ) := by
    rw [Finset.card_eq_sum_ones]
    simp
  calc ((Finset.univ.filter (fun c : ι → Fin K => ∀ r, decide (c r = i) = s r)).card : ℝ)
      = ∑ c ∈ (Finset.univ.filter (fun c : ι → Fin K => ∀ r, decide (c r = i) = s r)), (1:ℝ) := hcard
    _ = ∑ c : ι → Fin K, (if (∀ r, decide (c r = i) = s r) then (1:ℝ) else 0) := by
        rw [Finset.sum_filter]
    _ = ∑ c : ι → Fin K, ∏ r, (if s r then (if c r = i then (1:ℝ) else 0)
          else (if c r = i then 0 else 1)) := by
        apply Finset.sum_congr rfl
        intro c _
        by_cases hP : ∀ r, decide (c r = i) = s r
        · rw [if_pos hP]
          exact (Finset.prod_eq_one (fun r _ => factor_eq_one i (c r) (hP r))).symm
        · rw [if_neg hP]
          push Not at hP
          obtain ⟨r, hr⟩ := hP
          exact (Finset.prod_eq_zero (s := (Finset.univ : Finset ι))
            (f := fun r => (if s r then (if c r = i then (1:ℝ) else 0) else (if c r = i then 0 else 1)))
            (Finset.mem_univ r) (factor_eq_zero i (c r) hr)).symm
    _ = ∏ r, (if s r then (1:ℝ) else (K:ℝ) - 1) := sum_pattern_prod i s

/-- The fibre size in terms of the Bernoulli weight: multiplying the weight of a pattern by
`K ^ (card ι)` gives the number of colourings with that pattern. -/
lemma prod_fibre_eq_pow_mul {ι : Type*} [Fintype ι] {K : ℕ} (hK : 1 ≤ K) (s : ι → Bool) :
    ∏ r, (if s r then (1:ℝ) else (K:ℝ) - 1)
      = (K:ℝ) ^ (Fintype.card ι) * ∏ r, (if s r then (1:ℝ)/(K:ℝ) else 1 - 1/(K:ℝ)) := by
  have hKR : (K:ℝ) ≠ 0 := by positivity
  have hpow : (K:ℝ) ^ (Fintype.card ι) = ∏ _r : ι, (K:ℝ) := by
    rw [Finset.prod_const, Finset.card_univ]
  rw [hpow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro r _
  by_cases hs : s r
  · simp only [hs, if_true]
    field_simp
  · simp only [hs, if_false, Bool.false_eq_true]
    field_simp

/-- Passing between the propositional and boolean description of "is coloured `i`". -/
private lemma sum_decide {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ} (i : Fin K)
    (X : ι → ℝ) (c : ι → Fin K) :
    (∑ r : ι, (if decide (c r = i) then X r else 0)) = ∑ r : ι, (if c r = i then X r else 0) := by
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : c r = i <;> simp [h]

/-- **Two-sided Chernoff bound for a uniformly random `K`-colouring (count form).**

Colour each element of a finite set `ι` independently and uniformly with one of `K ≥ 2`
colours.  Let `X : ι → ℝ` be weights with `0 ≤ X r ≤ C`, fix a colour `i` and `τ ≥ 0`.
Then the number of colourings for which the total weight of the elements of colour `i`
deviates from its mean `(∑ r, X r) / K` by at least `τ` is at most
`K ^ (card ι) * 2 * exp (-(τ ^ 2) / (2 * C * ((∑ r, X r) / K + τ / 3)))`.

The count is expressed as a `Finset.card` over the colouring space `ι → Fin K`.  The proof
imports `Submission.Commons.Probability.Chernoff.chernoff_two_sided_finite_weighted`
(the weighted Bernoulli two-sided Chernoff bound, in the workspace): for a fixed colour `i`
the map `c ↦ (r ↦ (c r = i))` pushes the uniform measure on `ι → Fin K` forward to the
product Bernoulli measure with parameter `1 / K` (the fibre over a Boolean pattern `s` has
cardinality `∏ r, if s r then 1 else K - 1`), and
`∏ r, (if s r then 1 else K - 1) = K ^ card ι * ∏ r, (if s r then 1 / K else 1 - 1 / K)`. -/
theorem card_weighted_dev_le {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ} (hK : 2 ≤ K)
    (X : ι → ℝ) (hX0 : ∀ r, 0 ≤ X r) {C : ℝ} (hC0 : 0 ≤ C) (hXC : ∀ r, X r ≤ C)
    (i : Fin K) {τ : ℝ} (hτ : 0 ≤ τ) :
    ((Finset.univ.filter (fun c : ι → Fin K =>
        τ ≤ |(∑ r : ι, if c r = i then X r else 0) - (∑ r : ι, X r) / (K : ℝ)|)).card : ℝ)
      ≤ (K : ℝ) ^ (Fintype.card ι) *
          (2 * Real.exp (-(τ ^ 2) / (2 * C * ((∑ r : ι, X r) / (K : ℝ) + τ / 3)))) := by
  classical
  have hK1 : 1 ≤ K := le_trans (by norm_num) hK
  have hKRpos : (0:ℝ) < (K:ℝ) := by
    have : (2:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
    linarith
  set μ : ℝ := (∑ r : ι, X r) / (K:ℝ) with hμ
  let W : (ι → Bool) → ℝ := fun s => ∏ r, (if s r then (1:ℝ)/(K:ℝ) else 1 - 1/(K:ℝ))
  let T : Finset (ι → Bool) := Finset.univ.filter (fun s => τ ≤ |(∑ r : ι, if s r then X r else 0) - μ|)
  let fibre : (ι → Bool) → Finset (ι → Fin K) :=
    fun s => Finset.univ.filter (fun c => ∀ r, decide (c r = i) = s r)
  -- Replace the propositional target event by its `decide`-form.
  have hS_eq : (Finset.univ.filter (fun c : ι → Fin K =>
        τ ≤ |(∑ r : ι, if c r = i then X r else 0) - μ|))
      = Finset.univ.filter (fun c : ι → Fin K =>
        τ ≤ |(∑ r : ι, if decide (c r = i) then X r else 0) - μ|) := by
    apply Finset.filter_congr
    intro c _
    rw [sum_decide i X c]
  rw [hS_eq]
  -- The bad colourings are covered by the fibres of the bad patterns.
  have h1 : ((Finset.univ.filter (fun c : ι → Fin K =>
        τ ≤ |(∑ r : ι, if decide (c r = i) then X r else 0) - μ|)).card : ℝ)
      ≤ ∑ s ∈ T, ((fibre s).card : ℝ) := by
    have hsub : (Finset.univ.filter (fun c : ι → Fin K =>
          τ ≤ |(∑ r : ι, if decide (c r = i) then X r else 0) - μ|))
        ⊆ T.biUnion fibre := by
      intro c hc
      rw [Finset.mem_biUnion]
      refine ⟨fun r => decide (c r = i), ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hc).2⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, fun r => rfl⟩
    calc ((Finset.univ.filter (fun c : ι → Fin K =>
          τ ≤ |(∑ r : ι, if decide (c r = i) then X r else 0) - μ|)).card : ℝ)
        ≤ ((T.biUnion fibre).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((∑ s ∈ T, (fibre s).card : ℕ) : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ = ∑ s ∈ T, ((fibre s).card : ℝ) := by simp only [Nat.cast_sum]
  -- Evaluate the size of each fibre.
  have h2 : (∑ s ∈ T, ((fibre s).card : ℝ))
      = ∑ s ∈ T, ∏ r, (if s r then (1:ℝ) else (K:ℝ) - 1) := by
    apply Finset.sum_congr rfl
    intro s _
    exact card_fibre_eq i s
  -- Convert to the Bernoulli weights, scaled by `K ^ card ι`.
  have h3 : (∑ s ∈ T, ∏ r, (if s r then (1:ℝ) else (K:ℝ) - 1))
      = (K:ℝ)^(Fintype.card ι) * ∑ s ∈ T, W s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    exact prod_fibre_eq_pow_mul hK1 s
  have h4 : (∑ s ∈ T, W s)
      = ∑ s : ι → Bool, W s * (if τ ≤ |(∑ r : ι, if s r then X r else 0) - μ| then (1:ℝ) else 0) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : τ ≤ |(∑ r : ι, if s r then X r else 0) - μ| <;> simp [h]
  have hp0 : ∀ r : ι, (0:ℝ) ≤ (1:ℝ)/(K:ℝ) := fun _ => by positivity
  have hp1 : ∀ r : ι, (1:ℝ)/(K:ℝ) ≤ 1 := by
    intro _
    rw [div_le_one hKRpos]
    exact_mod_cast hK1
  have hsum1 : (∑ r : ι, (1:ℝ)/(K:ℝ) * X r) = μ := by
    rw [← Finset.mul_sum, hμ]
    field_simp
  have hcher := Commons.Probability.Chernoff.chernoff_two_sided_finite_weighted
    (p := fun _ : ι => (1:ℝ)/(K:ℝ)) hp0 hp1 (X := X) hX0 (C := C) hC0 hXC (t := τ) hτ
  have hcher' : (∑ s : ι → Bool, W s *
        (if τ ≤ |(∑ r : ι, if s r then X r else 0) - μ| then (1:ℝ) else 0))
      ≤ 2 * Real.exp (-(τ^2) / (2 * C * (μ + τ/3))) := by
    simpa only [hsum1] using hcher
  calc ((Finset.univ.filter (fun c : ι → Fin K =>
          τ ≤ |(∑ r : ι, if decide (c r = i) then X r else 0) - μ|)).card : ℝ)
      ≤ ∑ s ∈ T, ((fibre s).card : ℝ) := h1
    _ = ∑ s ∈ T, ∏ r, (if s r then (1:ℝ) else (K:ℝ) - 1) := h2
    _ = (K:ℝ)^(Fintype.card ι) * ∑ s ∈ T, W s := h3
    _ = (K:ℝ)^(Fintype.card ι) * ∑ s : ι → Bool, W s *
          (if τ ≤ |(∑ r : ι, if s r then X r else 0) - μ| then (1:ℝ) else 0) := by rw [h4]
    _ ≤ (K:ℝ)^(Fintype.card ι) * (2 * Real.exp (-(τ^2)/(2*C*(μ + τ/3)))) :=
        mul_le_mul_of_nonneg_left hcher' (by positivity)
    _ = (K:ℝ)^(Fintype.card ι) *
          (2 * Real.exp (-(τ^2)/(2*C*((∑ r : ι, X r)/(K:ℝ) + τ/3)))) := by rw [hμ]

end Work.Deep.Prob.Colouring
