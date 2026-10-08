import Mathlib
import Submission.Work.Hering.AppVII.Arith
import Submission.Work.Hering.AppVII.arith_sum_sq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.AppVII

/-- **Arithmetic core of Appendix VII, Part 2 (final step).**

Let `ι` be a finite index set of prime cardinality `p`, and let `n : ι → ℤ` be nonnegative
integers whose sum is `q ^ m`, where `q` is an odd prime and `m ≥ 1`, and whose pairwise
differences satisfy `∑_i ∑_j (n i - n j)^2 = 2 (p - 1)`.  Then no `n i` is zero.

Proof sketch: `∑_i ∑_j (n i - n j)^2 = 2 ∑_{i<j} (n i - n j)^2`, so `∑_{i<j} (n i - n j)^2 = p - 1`.
Let `a` be the minimum value and `z ≥ 1` the number of indices where it is attained.  The
`z (p - z)` pairs consisting of a minimal index and a non-minimal index each contribute at least
`1`, so `2 (p - 1) ≥ 2 z (p - z)`, and since `z (p - z) - (p - 1) = (z - 1) (p - 1 - z) ≥ 0` for
`1 ≤ z ≤ p - 1`, this forces `z ∈ {1, p - 1}` (and `z = p` would give `p = 1`).  All inequalities
are then equalities, so all entries other than the `z` minimal ones are equal and equal `a + 1`:
the values are all equal to `c` except at a single index `i₀`, where the value is `c + 1` (if
`z = p - 1`) or `c - 1` (if `z = 1`).  Finally `p c ± 1 = q ^ m ≥ 3`: `c = 0` gives sum `±1`;
if the exceptional index is the one carrying `0` then `c = ±1` gives sum `±(p - 1) < 0` or
`p - 1 = q ^ m`, the latter impossible because `q ^ m` is odd, hence `p` even, hence `p = 2` and
`q ^ m = 1 < 3`.  So `c ≠ 0` and the exceptional value `c ± 1 ≠ 0` too.  The final counting step
is exactly `Work.Hering.AppVII.arith_step6` (`Submission/Work/Hering/AppVII/Arith.lean`, already
proved) after transporting along an equivalence `ι ≃ Fin p` (or reprove it directly). -/
theorem arith_final {ι : Type*} [Fintype ι] {p q m : ℕ} (hp : p.Prime) (hcard : Fintype.card ι = p)
    (hq : q.Prime) (hqodd : Odd q) (hm : 1 ≤ m) {n : ι → ℤ} (hnn : ∀ i, 0 ≤ n i)
    (hsum : ∑ i, n i = (q : ℤ) ^ m)
    (hdual : ∑ i, ∑ j, (n i - n j) ^ 2 = 2 * ((p : ℤ) - 1)) : ∀ i, n i ≠ 0 := by
  classical
  have hp2 : 2 ≤ p := hp.two_le
  -- The values are not all equal, since otherwise the double sum would vanish
  -- while `2 (p - 1) ≥ 2`.
  have hne : ∃ i j : ι, n i ≠ n j := by
    by_contra hcon
    have hall : ∀ i j : ι, n i = n j := fun i j => by
      by_contra h
      exact hcon ⟨i, j, h⟩
    have hzero : ∑ i : ι, ∑ j : ι, (n i - n j) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      rw [hall i j]; ring
    rw [hzero] at hdual
    have hpge : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp2
    linarith
  -- Transport the whole data along an equivalence `ι ≃ Fin p`.
  let e : ι ≃ Fin p := Fintype.equivFinOfCardEq hcard
  let n' : Fin p → ℤ := fun k => n (e.symm k)
  have hnn' : ∀ k : Fin p, 0 ≤ n' k := fun k => hnn (e.symm k)
  have hsum' : ∑ k : Fin p, n' k = (q : ℤ) ^ m := by
    have h1 : ∑ k : Fin p, n' k = ∑ i : ι, n i := by
      have := Equiv.sum_comp e.symm n
      simpa only [n'] using this
    rw [h1, hsum]
  have hdual' : ∑ i : Fin p, ∑ j : Fin p, (n' i - n' j) ^ 2 = 2 * ((p : ℤ) - 1) := by
    have h1 : ∑ i : Fin p, ∑ j : Fin p, (n' i - n' j) ^ 2
        = ∑ i : ι, ∑ j : ι, (n i - n j) ^ 2 := by
      have hinner : ∀ i : Fin p,
          ∑ j : Fin p, (n' i - n' j) ^ 2
            = ∑ j : ι, (n' i - n j) ^ 2 := fun i =>
        Equiv.sum_comp e.symm (fun j => (n' i - n j) ^ 2)
      rw [Finset.sum_congr rfl (fun i _ => hinner i)]
      exact Equiv.sum_comp e.symm (fun i => ∑ j : ι, (n i - n j) ^ 2)
    rw [h1, hdual]
  have hne' : ∃ i j : Fin p, n' i ≠ n' j := by
    obtain ⟨i, j, hij⟩ := hne
    refine ⟨e i, e j, ?_⟩
    simp only [n']
    rwa [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  -- Appendix VII, step 5 gives the "one exceptional value" structure on `Fin p`.
  obtain ⟨i₀, m', hrest, hsp⟩ := (arith_sum_sq hp2 hne').mp hdual'
  -- Appendix VII, step 6 finishes.
  have hstep := arith_step6 hp hq hqodd hm hnn' hsum' ⟨i₀, m', hrest, hsp⟩
  intro i hi
  exact hstep (e i) (by simpa only [n', Equiv.symm_apply_apply] using hi)

end Work.Hering.AppVII
