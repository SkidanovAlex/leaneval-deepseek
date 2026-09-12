import Mathlib
import Mathlib.Algebra.Order.Chebyshev
import Submission.Commons.Analysis.Real.sum_prefix_le_mul

/-!
# The batch accounting of the §3 (de Saxcé) production

De Saxcé's §3 produces, at a suitable time `t`, a family `v₁, …, v_ℓ` of lattice points of
`a_t s_x ℤᵈ` whose wedge is `π₊`-concentrated, and bounds the (flowed) log-covolume of the
`k`-prefix by the *batch* structure of the Harder–Narasimhan flag:

* the flag has blocks of rank-lengths `q 1, …, q N` (summing to `d`);
* from the `s`-th block one extracts `p s ≤ q s` vectors, of flowed norm
  `≍ exp (Γ s)`, where `Γ s` is the asymptotic slope of the Grayson polygon over that block;
* the polygon's slopes `Γ` are nondecreasing and satisfy `∑ Γ = 0` (the lattice is unimodular:
  `γ(d) = γ(0) = 0`).

The accounting is then

    `log ‖v₁ ∧ … ∧ v_k‖ ≤ ∑_{i ≤ k} a i + O(1)`  with `a` nondecreasing,

so the only estimate needed is that the *full* charged cost is `≤ 0`:

    `∑_i w i * Γ i ≤ 0`,   `w i := p_{s(i)} / q_{s(i)}`  (constant on blocks),

which is **Chebyshev's sum inequality** in the antivary form: `w` is nonincreasing — this is the
hypothesis on the flag, namely that the *position increments per rank* are nonincreasing, i.e.
the `L`-positions of the flag members form a concave sequence (`L = modelX ℓ`) — while `Γ` is
nondecreasing with vanishing sum `∑ Γ = 0`.

What is proved here:

* `sum_mul_le_zero` — the Chebyshev/antivary step (`w` antitone, `Γ` monotone, `∑ Γ = 0`), in the
  `Fin d`-indexed and in the `ℕ`-range form `sum_mul_le_zero_range`;
* `prefix_accounting_le_zero` — the prefix step (from the Commons prefix averaging): if the full
  charged cost is `≤ 0` then so is the `k`-prefix.

Module `Submission.Work.Lattice.Accounting`, namespace `Submission.Accounting`.
-/

noncomputable section

open Finset
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Submission.Accounting

/-- **The Chebyshev/antivary step of the §3 accounting.**  If the batch weights `w` are
nonincreasing and the asymptotic slopes `Γ` are nondecreasing with `∑ Γ = 0`, then the charged
cost `∑ i, w i * Γ i` is `≤ 0`.

Proof: Chebyshev's sum inequality (`Antivary.card_mul_sum_le_sum_mul_sum`) applied to the antivary
pair `(w, Γ)` gives `d * ∑ w Γ ≤ (∑ w) * (∑ Γ) = 0`; divide by `d > 0`. -/
theorem sum_mul_le_zero {d : ℕ} (w Γ : Fin d → ℝ) (hw : Antitone w) (hΓ : Monotone Γ)
    (hsum : ∑ i, Γ i = 0) : ∑ i, w i * Γ i ≤ 0 := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp
  · have hanti : Antivary w Γ := Antitone.antivary hw hΓ
    have hcheb := Antivary.card_mul_sum_le_sum_mul_sum (f := w) (g := Γ) hanti
    rw [hsum, mul_zero] at hcheb
    have hcard : ((Fintype.card (Fin d) : ℕ) : ℝ) = (d : ℝ) := by simp
    rw [hcard] at hcheb
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    by_contra hcon
    push Not at hcon
    have : 0 < (d : ℝ) * ∑ i, w i * Γ i := mul_pos hdR hcon
    linarith

/-- **The Chebyshev/antivary step, `ℕ`-range form.**  Version of `sum_mul_le_zero` for functions
of a natural number (the ranks `0, …, d-1`), which is the form in which the Grayson data along the
flow is naturally indexed. -/
theorem sum_mul_le_zero_range {d : ℕ} (w Γ : ℕ → ℝ) (hw : Antitone w) (hΓ : Monotone Γ)
    (hsum : ∑ i ∈ Finset.range d, Γ i = 0) :
    ∑ i ∈ Finset.range d, w i * Γ i ≤ 0 := by
  have h1 : (∑ i : Fin d, w i.val * Γ i.val) = ∑ i ∈ Finset.range d, w i * Γ i :=
    Fin.sum_univ_eq_sum_range (fun i => w i * Γ i) d
  have h2 : (∑ i : Fin d, Γ i.val) = ∑ i ∈ Finset.range d, Γ i :=
    Fin.sum_univ_eq_sum_range Γ d
  rw [← h1]
  refine sum_mul_le_zero (fun i : Fin d => w i.val) (fun i : Fin d => Γ i.val)
    (fun i j hij => hw hij) (fun i j hij => hΓ hij) ?_
  rw [h2]; exact hsum

/-- **The prefix account.**  If the full charged cost `∑_{i<n} a i` of a nondecreasing sequence is
`≤ 0`, then so is every prefix sum (`m ≤ n`).  This is the prefix-averaging step of the §3
accounting (Commons `sum_prefix_le_mul`). -/
theorem prefix_accounting_le_zero {a : ℕ → ℝ} (ha : Monotone a) {m n : ℕ} (hmn : m ≤ n)
    (hsum : ∑ i ∈ Finset.range n, a i ≤ 0) : ∑ i ∈ Finset.range m, a i ≤ 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hm : m = 0 := Nat.le_zero.mp hmn
    subst hm
    simp
  have h1 := Commons.Analysis.Real.sum_prefix_le_mul ha hmn
  have hmR : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2 : ((m : ℝ) / (n : ℝ)) * (∑ i ∈ Finset.range n, a i) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (div_nonneg hmR hnR.le) hsum
  linarith

end Submission.Accounting
