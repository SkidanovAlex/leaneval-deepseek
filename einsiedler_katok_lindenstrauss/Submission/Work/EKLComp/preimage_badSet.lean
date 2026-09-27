import Mathlib
import Submission.Work.EKLComp.BirkhoffDefs
import Submission.Work.EKLComp.birkA_shift_mul
import Submission.Work.EKLComp.affine_avg_eventually_lt_succ
import Submission.Work.EKLComp.affine_avg_eventually_lt_pred

noncomputable section

open Filter
open scoped BigOperators

namespace Work.EKLComp

open Work.EKLComp.Birkhoff

/-- `∃ᶠ` at `atTop` is insensitive to shifting the index by one: a property holds
frequently at the successors of `ℕ` iff it holds frequently. -/
lemma birkA_frequently_succ_iff {p : ℕ → Prop} :
    (∃ᶠ n in atTop, p (n + 1)) ↔ (∃ᶠ n in atTop, p n) := by
  rw [Filter.frequently_atTop, Filter.frequently_atTop]
  constructor
  · intro h a
    obtain ⟨b, hb, hb'⟩ := h a
    exact ⟨b + 1, by omega, hb'⟩
  · intro h a
    obtain ⟨b, hb, hb'⟩ := h (a + 1)
    exact ⟨b - 1, by omega, by simpa [Nat.sub_add_cancel (by omega : 1 ≤ b)] using hb'⟩

/-- The set of points where the Birkhoff averages of `f` frequently exceed `ε` by a rational
margin is exactly `T`-invariant.  Both inclusions are elementary: for `x ∈ U` and rationals
`ε < q' < q` with `q < birkA T f n x` frequently, the shift identity
`birkA T f (n-1) (T x) = (n * birkA T f n x - f x)/(n-1) = q + O(1/n)` gives
`q' < birkA T f (n-1) (T x)` frequently (note `birkA T f 0 x = 0`, so only `n ≥ 1` matters);
conversely `q < birkA T f n (T x)` frequently gives
`birkA T f (n+1) x = (n * birkA T f n (T x) + f x)/(n+1) = q + O(1/n) > q'` frequently. -/
theorem preimage_badSet {X : Type*} (T : X → X) (f : X → ℝ) (ε : ℝ) :
    T ⁻¹' Work.EKLComp.Birkhoff.badSet T f ε = Work.EKLComp.Birkhoff.badSet T f ε := by
  ext x
  simp only [Set.mem_preimage]
  constructor
  · -- `T x` is bad  ⟹  `x` is bad: shift the orbit one step forward.
    rintro ⟨q, hεq, hfreq⟩
    obtain ⟨q', hεq', hq'q⟩ := exists_rat_btwn hεq
    refine ⟨q', hεq', ?_⟩
    have hev := affine_avg_eventually_lt_succ (q := (q : ℝ)) (q' := (q' : ℝ)) (c := f x) hq'q
    have hcomb : ∃ᶠ n in atTop, (q : ℝ) < birkA T f n (T x) ∧
        ((1 ≤ n) ∧ (q' : ℝ) < ((n : ℝ) * (q : ℝ) + f x) / ((n : ℝ) + 1)) :=
      hfreq.and_eventually hev
    have hstep : ∃ᶠ n in atTop, (q' : ℝ) < birkA T f (n + 1) x :=
      hcomb.mono (fun n hn => by
        have hn1' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.2.1
        have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hkey : (n : ℝ) * birkA T f n (T x) + f x =
            ((n : ℝ) + 1) * birkA T f (n + 1) x := by
          rw [birkA_shift_mul T f n x]; push_cast; ring
        have h2' : (q' : ℝ) * ((n : ℝ) + 1) < (n : ℝ) * (q : ℝ) + f x :=
          (lt_div_iff₀ hpos).mp hn.2.2
        have h3 : (n : ℝ) * (q : ℝ) + f x < (n : ℝ) * birkA T f n (T x) + f x := by
          have := mul_lt_mul_of_pos_left hn.1 hn1'
          linarith
        have hlt : (q' : ℝ) * ((n : ℝ) + 1) < ((n : ℝ) + 1) * birkA T f (n + 1) x := by
          linarith
        calc (q' : ℝ) < ((n : ℝ) + 1) * birkA T f (n + 1) x / ((n : ℝ) + 1) :=
              (lt_div_iff₀ hpos).mpr hlt
          _ = birkA T f (n + 1) x := mul_div_cancel_left₀ _ (ne_of_gt hpos))
    exact birkA_frequently_succ_iff.mp hstep
  · -- `x` is bad  ⟹  `T x` is bad: shift the orbit one step backward.
    rintro ⟨q, hεq, hfreq⟩
    obtain ⟨q', hεq', hq'q⟩ := exists_rat_btwn hεq
    refine ⟨q', hεq', ?_⟩
    have hshift : ∃ᶠ n in atTop, (q : ℝ) < birkA T f (n + 1) x :=
      birkA_frequently_succ_iff.mpr hfreq
    have hev := affine_avg_eventually_lt_pred (q := (q : ℝ)) (q' := (q' : ℝ)) (c := f x) hq'q
    exact (hshift.and_eventually hev).mono (fun n hn => by
      have hn1' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.2.1
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hkey : (n : ℝ) * birkA T f n (T x) = ((n : ℝ) + 1) * birkA T f (n + 1) x - f x := by
        rw [birkA_shift_mul T f n x]; push_cast; ring
      have h2' : (q' : ℝ) * (n : ℝ) < ((n : ℝ) + 1) * (q : ℝ) - f x :=
        (lt_div_iff₀ hn1').mp hn.2.2
      have h3 : ((n : ℝ) + 1) * (q : ℝ) < ((n : ℝ) + 1) * birkA T f (n + 1) x :=
        mul_lt_mul_of_pos_left hn.1 hpos
      have hlt : (q' : ℝ) * (n : ℝ) < (n : ℝ) * birkA T f n (T x) := by linarith
      calc (q' : ℝ) < ((n : ℝ) * birkA T f n (T x)) / (n : ℝ) := (lt_div_iff₀ hn1').mpr hlt
        _ = birkA T f n (T x) := mul_div_cancel_left₀ _ (ne_of_gt hn1'))

end Work.EKLComp
