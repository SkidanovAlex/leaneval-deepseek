import Mathlib
import Submission.Work.Lattice.Accounting

/-!
# The §3 accounting: the *prefix* (Chebyshev) criterion — summation by parts

`Submission.Accounting.sum_mul_le_zero_range` proves the charged cost `∑ w i * Γ i ≤ 0` when the
per-rank weights `w` are **nonincreasing** (Chebyshev/antivary).  The actual flag of §3 however
only certifies the weaker *prefix* condition on the weights: the prefix sums of
`u i := p i − c` (`c` = the average weight) are nonnegative.  That is precisely the criterion
`ω_s ≥ ℓ·j_s/d` of the ROADMAP (with `p` the step function of the batch weights and `ω`, `j` the
positions/ranks of the flag members).

Here we prove the two equivalent forms by **summation by parts** (Abel):

* `sum_mul_le_of_prefix_nonneg`:
  `Γ` nondecreasing, `∑_{i<d} (p i − c) = 0` and every prefix sum of `p − c` nonnegative

      ⟹  `∑_{i<d} p i * Γ i ≤ c * ∑_{i<d} Γ i`;

* `sum_mul_le_zero_of_prefix_nonneg`: with `∑_{i<d} Γ i = 0` (unimodular lattice), the charged
  cost is `≤ 0` — hence, by `Accounting.prefix_accounting_le_zero`, so is every `k`-prefix
  (`k ≤ d`), which is exactly the bound `log ‖⋀^k v‖ ≤ O(1)` of the production.

The proof is the identity
`∑_{i<d} u i * Γ i = ∑_{i<d} C (i+1) * (Γ i − Γ (i+1)) + (C d * Γ d − C 0 * Γ 0)`
with `C k = ∑_{i<k} u i` (`Finset.sum_range_sub` telescoping); the first summand is `≤ 0`
because `C ≥ 0` and `Γ` is nondecreasing, and the second vanishes because `C 0 = 0 = C d`.

Module `Submission.Work.Lattice.PrefixAccounting`, namespace `Submission.PrefixAccounting`.
-/

noncomputable section

open Finset
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Submission.PrefixAccounting

/-- **The prefix criterion (Abel/summation by parts).**  If every prefix sum of `u = p − c` is
nonnegative and the total sum of `u` vanishes, then `∑_{i<d} p i * Γ i ≤ c * ∑_{i<d} Γ i` for every
nondecreasing `Γ`. -/
theorem sum_mul_le_of_prefix_nonneg {d : ℕ} {p Γ : ℕ → ℝ} {c : ℝ}
    (hΓ : Monotone Γ) (hC : ∀ k, k ≤ d → 0 ≤ ∑ i ∈ Finset.range k, (p i - c))
    (hsum : ∑ i ∈ Finset.range d, (p i - c) = 0) :
    ∑ i ∈ Finset.range d, p i * Γ i ≤ c * ∑ i ∈ Finset.range d, Γ i := by
  set u : ℕ → ℝ := fun i => p i - c with hu
  have hCd : ∑ i ∈ Finset.range d, u i = 0 := by simpa [hu] using hsum
  have hprefix : ∀ k, k ≤ d → 0 ≤ ∑ j ∈ Finset.range k, u j := by
    intro k hk
    simpa [hu] using hC k hk
  -- summation by parts: `∑ Γ i * u i = Γ (d-1) * ∑ u - ∑ (Γ (i+1) - Γ i) * (∑_{j≤i} u j)`
  have hlu : ∑ i ∈ Finset.range d, u i * Γ i ≤ 0 := by
    have hbp := Finset.sum_range_by_parts (Γ) (u) d
    simp only [smul_eq_mul] at hbp
    rw [hCd, mul_zero, zero_sub] at hbp
    have hnn : 0 ≤ ∑ i ∈ Finset.range (d - 1),
        (Γ (i + 1) - Γ i) * (∑ j ∈ Finset.range (i + 1), u j) := by
      refine Finset.sum_nonneg (fun i hi => ?_)
      have hid : i + 1 ≤ d := by
        have := Finset.mem_range.mp hi
        omega
      exact mul_nonneg (by have := hΓ (by omega : i ≤ i + 1); linarith)
        (hprefix (i + 1) hid)
    have hcomm : ∑ i ∈ Finset.range d, Γ i * u i = ∑ i ∈ Finset.range d, u i * Γ i :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [hcomm] at hbp
    linarith [hnn]
  have hsub : ∑ i ∈ Finset.range d, p i * Γ i - c * ∑ i ∈ Finset.range d, Γ i =
      ∑ i ∈ Finset.range d, u i * Γ i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hu]
    ring
  linarith [hsub ▸ hlu]

/-- **The prefix criterion, vanishing-slope form** (unimodular lattice: `∑ Γ = 0`): the charged
cost is nonpositive. -/
theorem sum_mul_le_zero_of_prefix_nonneg {d : ℕ} {p Γ : ℕ → ℝ} {c : ℝ}
    (hΓ : Monotone Γ) (hC : ∀ k, k ≤ d → 0 ≤ ∑ i ∈ Finset.range k, (p i - c))
    (hsum : ∑ i ∈ Finset.range d, (p i - c) = 0)
    (hΓsum : ∑ i ∈ Finset.range d, Γ i = 0) :
    ∑ i ∈ Finset.range d, p i * Γ i ≤ 0 := by
  have h := sum_mul_le_of_prefix_nonneg (d := d) hΓ hC hsum
  rwa [hΓsum, mul_zero] at h

/-- **The flag form of the criterion.**  This is the exact shape in which the §3 data presents
itself: a flag with block boundaries `jb 0 = 0 < jb 1 < … < jb N = d`, positions `w s = ω_s`
(`w 0 = 0`, `w N = c·d`), block slopes `Λ s` that are nondecreasing in `s` and closed
(`∑_s (jb (s+1) − jb s)·Λ s = 0`, the polygon vanishing at both ends).  If every flag member
satisfies the *position criterion* `c·jb s ≤ w s` (= `ω_s ≥ (ℓ/d)·j_s` with `c = ℓ/d`), then the
charged cost `∑_s (ω_{s+1} − ω_s)·Λ s ≤ 0`.

Proof: put `e_s := Δω_s − c·Δj_s`; its prefix sums are `E_s = ω_s − c·j_s ≥ 0` (the criterion) and
`E_N = 0`; summation by parts turns `∑ e_s Λ_s` into `−∑_{s<N} E_{s+1}(Λ_{s+1} − Λ_s) ≤ 0`, while
the `c·Δj_s` part is `c·(closed sum) = 0`. -/
theorem flag_accounting_le_zero {N : ℕ} {jb : ℕ → ℕ} {w Λ : ℕ → ℝ} {c : ℝ}
    (hjbmono : Monotone jb) (hjb0 : jb 0 = 0) (hw0 : w 0 = 0) (hwN : w N = c * (jb N : ℝ))
    (hstar : ∀ s, s ≤ N → c * (jb s : ℝ) ≤ w s)
    (hΛ : Monotone Λ)
    (hclosed : ∑ s ∈ Finset.range N, (((jb (s + 1) - jb s : ℕ)) : ℝ) * Λ s = 0) :
    ∑ s ∈ Finset.range N, (w (s + 1) - w s) * Λ s ≤ 0 := by
  set e : ℕ → ℝ := fun s => (w (s + 1) - w s) - c * (((jb (s + 1) - jb s : ℕ)) : ℝ) with he
  -- prefix sums of `e`
  have hE : ∀ s, (∑ s' ∈ Finset.range s, e s') = w s - c * (jb s : ℝ) := by
    intro s
    induction s with
    | zero => simp [hw0, hjb0]
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        have hle : jb k ≤ jb (k + 1) := hjbmono (Nat.le_succ k)
        have hcast : (((jb (k + 1) - jb k : ℕ)) : ℝ) = (jb (k + 1) : ℝ) - (jb k : ℝ) :=
          Nat.cast_sub hle
        simp only [he]
        rw [hcast]
        ring
  have hsplit : ∑ s ∈ Finset.range N, (w (s + 1) - w s) * Λ s =
      c * (∑ s ∈ Finset.range N, (((jb (s + 1) - jb s : ℕ)) : ℝ) * Λ s) +
        ∑ s ∈ Finset.range N, e s * Λ s := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [he]
    ring
  have hkey : ∑ s ∈ Finset.range N, e s * Λ s ≤ 0 := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · have hbp := Finset.sum_range_by_parts (Λ) (e) N
      simp only [smul_eq_mul] at hbp
      have hsumE : ∑ s ∈ Finset.range N, e s = 0 := by
        have := hE N
        rw [hwN] at this
        linarith
      rw [hsumE, mul_zero, zero_sub] at hbp
      have hnn : 0 ≤ ∑ i ∈ Finset.range (N - 1),
          (Λ (i + 1) - Λ i) * (∑ s' ∈ Finset.range (i + 1), e s') := by
        refine Finset.sum_nonneg (fun i hi => ?_)
        have hid : i + 1 ≤ N := by
          have := Finset.mem_range.mp hi
          omega
        refine mul_nonneg (by have := hΛ (by omega : i ≤ i + 1); linarith) ?_
        rw [hE (i + 1)]
        linarith [hstar (i + 1) hid]
      have hcomm : ∑ s ∈ Finset.range N, Λ s * e s = ∑ s ∈ Finset.range N, e s * Λ s :=
        Finset.sum_congr rfl (fun s _ => by ring)
      rw [hcomm] at hbp
      linarith [hnn]
  rw [hsplit, hclosed, mul_zero, zero_add]
  exact hkey

end Submission.PrefixAccounting

end
