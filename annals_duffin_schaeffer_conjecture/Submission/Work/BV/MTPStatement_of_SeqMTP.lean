/-
# The mass transference principle for countable index sets, from the sequence case

`Submission.Main.MTPStatement` is the Beresnevich–Velani mass transference principle in `ℝ`
(`k = 1`, `f(r) = r^d`) for an arbitrary countable index type `ι`.  This file derives it
from the sequence version (index type `ℕ`), `hseq`.

The mathematical content of the reduction is the bookkeeping of the index set.  For a
countable `ι` pick an injection `f : ι → ℕ` (which exists because `Countable ι` is *defined*
as the existence of such an injection).  Turn the family `(c i, ρ i)_{i : ι}` into the
sequence

  `c' n = c i` and `ρ' n = ρ i`   if `n = f i`,
  `c' n = n` and `ρ' n = 0`       otherwise (padding).

The padding is harmless: for a padded index the condition `|z - c' n| ≤ ρ' n` (or
`≤ (ρ' n)^d`) reads `z = n`, which holds for at most one `n`.  Hence a point is covered
infinitely often by the sequence iff it is covered infinitely often by the `ι`-family
(`infinite_iff_image_pad`), so the "full measure" hypothesis transfers and the conclusion
transfers.  No hypothesis on `ρ` is needed for this: in particular radii `ρ i = 0` (whose
index set is not covered by the smallness hypothesis `∀ ε > 0, {i | ε ≤ ρ i}.Finite`) are
handled by the padding.
-/
import Mathlib
import Submission.Work.BV.Bridge

open MeasureTheory Set

namespace Work.BV

/-- **Counting lemma for the padding.**  Let `f : ι → ℕ` be injective, and suppose the
families `(c', r')` on `ℕ` and `(c, r)` on `ι` agree on the image of `f`, while off the
image of `f` the pair `(c' n, r' n)` is the "padding" `(n, 0)`.  Then a real number `z` is
covered infinitely often by the sequence family iff it is covered infinitely often by the
`ι`-family.

The padding contributes at most one index for each `z`: if `n` is not in the image of `f`
and `|z - c' n| ≤ r' n = 0`, then `z = c' n = n`. -/
lemma infinite_iff_image_pad
    {ι : Type*} {f : ι → ℕ} (hf : Function.Injective f)
    {c : ι → ℝ} {c' : ℕ → ℝ} (hc' : ∀ i, c' (f i) = c i)
    (hc'' : ∀ n, ¬ (∃ i, f i = n) → c' n = n)
    {r : ι → ℝ} {r' : ℕ → ℝ} (hr' : ∀ i, r' (f i) = r i)
    (hr'' : ∀ n, ¬ (∃ i, f i = n) → r' n = 0)
    (z : ℝ) :
    ({n : ℕ | |z - c' n| ≤ r' n}.Infinite) ↔ ({i : ι | |z - c i| ≤ r i}.Infinite) := by
  have himg : (f '' {i : ι | |z - c i| ≤ r i}).Infinite ↔
      {i : ι | |z - c i| ≤ r i}.Infinite := Set.infinite_image_iff hf.injOn
  have hsub : f '' {i : ι | |z - c i| ≤ r i} ⊆ {n : ℕ | |z - c' n| ≤ r' n} := by
    rintro n ⟨i, hi, rfl⟩
    simp only [Set.mem_ofPred_eq] at hi ⊢
    rwa [hc' i, hr' i]
  -- the set of padded indices that can meet `z` is finite (`z` is a real number)
  have hD : ({n : ℕ | (n : ℝ) = z}).Finite := by
    refine Set.Finite.subset (Set.finite_le_nat ⌈z⌉₊) ?_
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn ⊢
    exact_mod_cast (hn.trans_le (Nat.le_ceil z))
  constructor
  · intro htinf
    have h1 : ({n : ℕ | |z - c' n| ≤ r' n} \ {n : ℕ | (n : ℝ) = z}).Infinite :=
      htinf.sdiff hD
    have h2 : (f '' {i : ι | |z - c i| ≤ r i}).Infinite := h1.mono (by
      rintro n ⟨hn, hnz⟩
      simp only [Set.mem_ofPred_eq] at hn hnz
      by_cases him : ∃ i, f i = n
      · obtain ⟨i, rfl⟩ := him
        exact ⟨i, by rwa [hc' i, hr' i] at hn, rfl⟩
      · exfalso
        have h0 : r' n = 0 := hr'' n him
        have hle0 : |z - c' n| ≤ 0 := by rwa [h0] at hn
        have hz0 : z - c' n = 0 := abs_nonpos_iff.mp hle0
        have hz : z = (n : ℝ) := by
          rw [sub_eq_zero] at hz0
          rw [hc'' n him] at hz0
          exact hz0
        exact hnz hz.symm)
    exact himg.mp h2
  · intro hsinf
    exact (himg.mpr hsinf).mono hsub

theorem MTPStatement_of_SeqMTP
    (hseq : ∀ (d : ℝ), 0 < d → d < 1 → ∀ (c ρ : ℕ → ℝ),
      (∀ n, 0 ≤ ρ n) → (∀ ε : ℝ, 0 < ε → {n : ℕ | ε ≤ ρ n}.Finite) →
      (∀ x y : ℝ, 0 ≤ x → y ≤ 1 →
        MeasureTheory.Measure.hausdorffMeasure 1
          (Set.Icc x y ∩ {z : ℝ | {n : ℕ | |z - c n| ≤ (ρ n) ^ d}.Infinite})
          = MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc x y)) →
      MeasureTheory.Measure.hausdorffMeasure d
        (Set.Icc (0 : ℝ) 1 ∩ {z : ℝ | {n : ℕ | |z - c n| ≤ ρ n}.Infinite}) = ⊤) :
    Submission.Main.MTPStatement := by
  intro d hd0 hd1 ι hcount c ρ hρ0 hρfin hfull
  classical
  -- an injection of the countable index type into `ℕ`
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat ι
  -- the sequence, padded off the image of `f` by `(n, 0)`
  set c' : ℕ → ℝ := fun n => if h : ∃ i, f i = n then c h.choose else (n : ℝ) with hcdef
  set ρ' : ℕ → ℝ := fun n => if h : ∃ i, f i = n then ρ h.choose else 0 with hρdef
  have hc'f : ∀ i, c' (f i) = c i := by
    intro i
    have h : ∃ j, f j = f i := ⟨i, rfl⟩
    simp only [hcdef, dif_pos h]
    exact congrArg c (hf (Classical.choose_spec h))
  have hρ'f : ∀ i, ρ' (f i) = ρ i := by
    intro i
    have h : ∃ j, f j = f i := ⟨i, rfl⟩
    simp only [hρdef, dif_pos h]
    exact congrArg ρ (hf (Classical.choose_spec h))
  have hc'' : ∀ n, ¬ (∃ i, f i = n) → c' n = n := by
    intro n hn
    simp only [hcdef, dif_neg hn]
  have hρ'' : ∀ n, ¬ (∃ i, f i = n) → ρ' n = 0 := by
    intro n hn
    simp only [hρdef, dif_neg hn]
  -- the sequence satisfies the hypotheses of `hseq`
  have hρ'0 : ∀ n, 0 ≤ ρ' n := by
    intro n
    by_cases h : ∃ i, f i = n
    · simp only [hρdef, dif_pos h]
      exact hρ0 h.choose
    · simp only [hρdef, dif_neg h]
      exact le_refl 0
  have hρ'fin : ∀ ε : ℝ, 0 < ε → {n : ℕ | ε ≤ ρ' n}.Finite := by
    intro ε hε
    refine (Set.Finite.image f (hρfin ε hε)).subset ?_
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn ⊢
    by_cases h : ∃ i, f i = n
    · obtain ⟨i, hi⟩ := h
      refine ⟨i, ?_, hi⟩
      rw [← hi, hρ'f i] at hn
      exact hn
    · exact absurd (by rwa [hρ'' n h] at hn) (not_le.mpr hε)
  have hfull' : ∀ x y : ℝ, 0 ≤ x → y ≤ 1 →
      MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc x y ∩
        {z : ℝ | {n : ℕ | |z - c' n| ≤ (ρ' n) ^ d}.Infinite})
        = MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc x y) := by
    intro x y hx hy
    have hset : {z : ℝ | {n : ℕ | |z - c' n| ≤ (ρ' n) ^ d}.Infinite} =
        {z : ℝ | {i : ι | |z - c i| ≤ (ρ i) ^ d}.Infinite} := by
      ext z
      simp only [Set.mem_ofPred_eq]
      exact infinite_iff_image_pad hf hc'f hc'' (r := fun i => (ρ i) ^ d)
        (r' := fun n => (ρ' n) ^ d) (fun i => by rw [hρ'f i]) (fun n hn => by
          rw [hρ'' n hn, Real.zero_rpow (ne_of_gt hd0)]) z
    rw [hset]
    exact hfull x y hx hy
  have hsmall : {z : ℝ | {n : ℕ | |z - c' n| ≤ ρ' n}.Infinite} =
      {z : ℝ | {i : ι | |z - c i| ≤ ρ i}.Infinite} := by
    ext z
    simp only [Set.mem_ofPred_eq]
    exact infinite_iff_image_pad hf hc'f hc'' hρ'f hρ'' z
  have h := hseq d hd0 hd1 c' ρ' hρ'0 hρ'fin hfull'
  rw [hsmall] at h
  exact h

end Work.BV
