/-
# `Work.Deep.Conc.BruhnJoos.talagrand_certified`

The **certified two-set form** of Talagrand's convex distance inequality: if for every `ω ∈ B`
there is a set `I` of at most `s` coordinates on which `ω` differs from *every* element of `A`
in at least `r` coordinates, then

  `P(A) · P(B) ≤ exp(-r²/(4s))`.

This is the form in which Talagrand's inequality is applied to collision-type statistics: the
certificate sets `I` produced by `Work.Deep.Conc.Tail.collide_certificates` (there `I` is the
whole coordinate set, `s = |V|`, `r = u/θ`) feed directly into it.  It is a corollary of the
two-set convex-distance inequality `Work.Deep.Conc.BruhnJoos.talagrand_two_set`, by taking the
witness vector `α = 1_I/√|I|`.
-/
import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Conc.Basic
import Submission.Work.Deep.Conc.Pi
import Submission.Work.Deep.Conc.BruhnJoos.talagrand_two_set

set_option autoImplicit false
open scoped BigOperators
open Finset

namespace Work.Deep.Conc.BruhnJoos

open Work.Deep.Conc

/-- The witness vector `1_I/√|I|` is a unit vector when `I` is nonempty. -/
private lemma unit_witness {ι : Type*} [Fintype ι] [DecidableEq ι] {I : Finset ι}
    (hI : I.Nonempty) :
    (∑ i : ι, (if i ∈ I then 1 / Real.sqrt (I.card : ℝ) else 0) ^ 2) = 1 := by
  have hIcardpos : 0 < (I.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hI
  have hpt : ∀ i : ι, (if i ∈ I then 1 / Real.sqrt (I.card : ℝ) else 0) ^ 2
      = if i ∈ I then (1 / Real.sqrt (I.card : ℝ)) ^ 2 else 0 := by
    intro i
    by_cases hi : i ∈ I <;> simp [hi]
  rw [Finset.sum_congr rfl (fun i _ => hpt i),
    show (∑ i : ι, if i ∈ I then (1 / Real.sqrt (I.card : ℝ)) ^ 2 else 0)
      = ∑ _i ∈ I, (1 / Real.sqrt (I.card : ℝ)) ^ 2 by
      rw [← Finset.sum_filter]; simp,
    Finset.sum_const, nsmul_eq_mul]
  rw [div_pow, one_pow, Real.sq_sqrt hIcardpos.le]
  field_simp

/-- The weighted sum of the witness vector `1_I/√|I|` against an indicator vector. -/
private lemma witness_mul_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (I : Finset ι)
    (c : ι → ℝ) :
    (∑ i ∈ I, c i) / Real.sqrt (I.card : ℝ)
      = ∑ i : ι, (if i ∈ I then 1 / Real.sqrt (I.card : ℝ) else 0) * c i := by
  rw [Finset.sum_div]
  rw [show (∑ i ∈ I, c i / Real.sqrt (I.card : ℝ))
      = ∑ i : ι, if i ∈ I then c i / Real.sqrt (I.card : ℝ) else 0 by
    rw [← Finset.sum_filter]; simp]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ I <;> simp [hi, div_eq_mul_inv, mul_comm, mul_left_comm]

/-- **Certified two-set Talagrand inequality** (with `A` nonempty; the empty case is trivial). -/
private theorem talagrand_certified_aux {ι : Type*} [Fintype ι] [DecidableEq ι] {π : ι → Type*}
    [∀ i, Fintype (π i)] [∀ i, DecidableEq (π i)] (hne : ∀ i, Nonempty (π i))
    (A B : Set (∀ i, π i)) (hAne : A.Nonempty) (r : ℝ) (hr : 0 ≤ r) (s : ℕ) (hs : 1 ≤ s)
    (h : ∀ ω ∈ B, ∃ I : Finset ι, I.card ≤ s ∧
        ∀ ω' ∈ A, r ≤ ∑ i ∈ I, (if ω i ≠ ω' i then (1 : ℝ) else 0)) :
    Work.Deep.Conc.prob A * Work.Deep.Conc.prob B ≤ Real.exp (- r ^ 2 / (4 * (s : ℝ))) := by
  classical
  haveI : Nonempty (∀ i, π i) := ⟨fun i => Classical.choice (hne i)⟩
  have hspos : 0 < (s : ℝ) := by exact_mod_cast hs
  have hsqrtpos : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr hspos
  have hprob1 : Work.Deep.Conc.prob A * Work.Deep.Conc.prob B ≤ 1 :=
    mul_le_one₀ (Work.Deep.Conc.prob_le_one A (Fintype.card_pos))
      (Work.Deep.Conc.prob_nonneg B) (Work.Deep.Conc.prob_le_one B (Fintype.card_pos))
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · rw [← hr0]
    simpa using hprob1
  · have hwit : ∀ ω ∈ B, ∃ α : ι → ℝ, (∑ i, α i ^ 2) = 1 ∧ (∀ i, 0 ≤ α i) ∧
        ∀ ω' ∈ A, r / Real.sqrt (s : ℝ) ≤ ∑ i, α i * (if ω i ≠ ω' i then (1 : ℝ) else 0) := by
      intro ω hω
      obtain ⟨I, hIcard, hI⟩ := h ω hω
      obtain ⟨ω', hω'⟩ := hAne
      have hIne : I.Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have h1 := hI ω' hω'
        rw [hemp] at h1
        simp only [Finset.sum_empty] at h1
        linarith
      have hIcardpos : 0 < (I.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hIne
      have hsqrtIpos : 0 < Real.sqrt (I.card : ℝ) := Real.sqrt_pos.mpr hIcardpos
      refine ⟨fun i => if i ∈ I then 1 / Real.sqrt (I.card : ℝ) else 0,
        unit_witness hIne, ?_, ?_⟩
      · intro i
        by_cases hi : i ∈ I <;> simp [hi]
      · intro ω' hω'
        have hcount : r ≤ ∑ i ∈ I, (if ω i ≠ ω' i then (1 : ℝ) else 0) := hI ω' hω'
        have hcountnn : 0 ≤ ∑ i ∈ I, (if ω i ≠ ω' i then (1 : ℝ) else 0) :=
          Finset.sum_nonneg fun i _ => by split <;> norm_num
        calc r / Real.sqrt (s : ℝ)
            ≤ (∑ i ∈ I, (if ω i ≠ ω' i then (1 : ℝ) else 0)) / Real.sqrt (s : ℝ) :=
              div_le_div_of_nonneg_right hcount hsqrtpos.le
          _ ≤ (∑ i ∈ I, (if ω i ≠ ω' i then (1 : ℝ) else 0)) / Real.sqrt (I.card : ℝ) := by
              rw [div_le_div_iff₀ hsqrtpos hsqrtIpos]
              exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hIcard))
                hcountnn
          _ = _ := witness_mul_sum I _
    have hfin := talagrand_two_set hne A B (r / Real.sqrt (s : ℝ))
      (div_nonneg hr hsqrtpos.le) hwit
    have hrw : -(r / Real.sqrt (s : ℝ)) ^ 2 / 4 = - r ^ 2 / (4 * (s : ℝ)) := by
      rw [div_pow, Real.sq_sqrt hspos.le]
      ring
    rwa [hrw] at hfin

/-- **Certified two-set Talagrand inequality.** -/
theorem talagrand_certified {ι : Type*} [Fintype ι] [DecidableEq ι] {π : ι → Type*}
    [∀ i, Fintype (π i)] [∀ i, DecidableEq (π i)] (hne : ∀ i, Nonempty (π i))
    (A B : Set (∀ i, π i)) (r : ℝ) (hr : 0 ≤ r) (s : ℕ) (hs : 1 ≤ s)
    (h : ∀ ω ∈ B, ∃ I : Finset ι, I.card ≤ s ∧
        ∀ ω' ∈ A, r ≤ ∑ i ∈ I, (if ω i ≠ ω' i then (1 : ℝ) else 0)) :
    Work.Deep.Conc.prob A * Work.Deep.Conc.prob B ≤ Real.exp (- r ^ 2 / (4 * (s : ℝ))) := by
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · rw [hAe, Work.Deep.Conc.prob_empty, zero_mul]
    exact (Real.exp_pos _).le
  · exact talagrand_certified_aux hne A B hAne r hr s hs h

end Work.Deep.Conc.BruhnJoos
