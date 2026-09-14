import Mathlib
import Submission.Vdw.CaseIIIThreshold
import Submission.Vdw.CaseIIIDDZero
import Submission.Commons.Analysis.Asymptotics.isBigO_of_natCast_le_mul_pow

open Polynomial Asymptotics
open scoped BigOperators
open Filter

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Case III: eventual pointwise (log-free) bounds for the assembly

The final assembly sums the Case-III pieces pointwise and then passes to
`O(H^(n-1))`.  `CaseIIIRegion`/`CaseIIIWrapper` give big-O statements;
this module records the equivalent **eventual pointwise** bounds (needed to
add the pieces with `∀ᶠ H, a H ≤ b H` before `IsBigO`-gluing):

* `caseIII_subcase2_bound_pointwise n M` — the subcase-(ii) region at the
  canonical threshold `⌈H^(1/M)⌉` satisfies `∃ C, ∀ᶠ H, # ≤ C·H^(n-1)`
  (any `3 ≤ n`, `1 ≤ M`, `n ≤ M`);
* `caseIII_subcase2_region_bound_pointwise n` — the same at `M = 4n`
  (the paper's `δ/2 = 1/(4n)`);
* `ddzero_add_subcase2_isBigO n` — the union bound for the two pieces of
  Case III available so far: `DD(u_f) = 0` (`CaseIIIDDZero`, unconditional)
  plus subcase (ii) (`CaseIIISubcase2` at the canonical threshold, requiring
  squarefull `D_f`, `DD(u_f) ≠ 0`, `A > H`): the sum of the two counts is
  `O(H^(n-1))`.  (Subcase (i) — the Case-I-analogous `B ∈ [H^(1+δ/2),
  H^(1+δ)]` sieve — is gated on the Fourier/Weil extension `fbound2`; see the
  Roadmap Session-39 block.)
-/

namespace Submission.Vdw

noncomputable section

/-- **Subcase (ii), eventual pointwise bound.**  At the canonical threshold
`B H = ⌈H^(1/M)⌉` (`3 ≤ n`, `1 ≤ M`, `n ≤ M`) the region count is eventually
`≤ C · H^(n-1)` for a constant `C` depending only on `n` and `M`. -/
theorem caseIII_subcase2_bound_pointwise (n M : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M)
    (hnM : n ≤ M) :
    ∃ C : ℕ, ∀ᶠ H : ℕ in atTop,
      (CaseIIISubcase2 n H (lowerThr M H)).ncard ≤ C * (H : ℕ) ^ (n - 1) := by
  classical
  -- the subcase-(ii) arithmetic threshold bound is uniform in B
  rcases caseIII_subcase2_threshold_le n M hn with ⟨C, hC⟩
  have hthr : ∀ᶠ H : ℕ in atTop,
      n < lowerThr M H ∧ H ≤ (lowerThr M H) ^ M := by
    filter_upwards [eventually_lt_lowerThr M hM] with H hgt
    exact ⟨lt_of_le_of_lt hnM hgt, le_pow_lowerThr M hM H⟩
  have hleA : ∀ᶠ H : ℕ in atTop,
      (CaseIIISubcase2 n H (lowerThr M H)).ncard ≤
        (CaseIIIArithSet (lowerThr M H) n H).ncard := by
    filter_upwards [hthr] with H hthr
    exact CaseIIISubcase2_ncard_le_arith n H (lowerThr M H) hn hthr.1
  have hleC : ∀ᶠ H : ℕ in atTop,
      (CaseIIIArithSet (lowerThr M H) n H).ncard ≤ C * (2 * H + 1) ^ (n - 1) := by
    filter_upwards [hC, hthr] with H hCb hthr
    exact hCb (lowerThr M H) hthr.1 hthr.2
  -- absorb (2H+1) into 3H and C into C·3^(n-1), eventually in H
  refine ⟨C * 3 ^ (n - 1), ?_⟩
  filter_upwards [hleA, hleC, eventually_ge_atTop (1 : ℕ)] with H hA hCb hH
  calc
    (CaseIIISubcase2 n H (lowerThr M H)).ncard ≤ C * (2 * H + 1) ^ (n - 1) :=
      le_trans hA hCb
    _ ≤ C * (3 * H) ^ (n - 1) := by
      exact Nat.mul_le_mul_left C (pow_le_pow_left₀ (by omega) (by omega) (n - 1))
    _ = (C * 3 ^ (n - 1)) * H ^ (n - 1) := by rw [mul_pow]; ring

/-- The same at the paper's value `M = 4n`: `#CaseIIISubcase2 n H ⌈H^(1/(4n))⌉`
is eventually `≤ C · H^(n-1)`. -/
theorem caseIII_subcase2_region_bound_pointwise (n : ℕ) (hn : 3 ≤ n) :
    ∃ C : ℕ, ∀ᶠ H : ℕ in atTop,
      (CaseIIISubcase2 n H (lowerThr (4 * n) H)).ncard ≤ C * (H : ℕ) ^ (n - 1) := by
  exact caseIII_subcase2_bound_pointwise n (4 * n) hn (by omega) (by omega)

/-- **Partial Case-III union bound.**  The `DD(u_f) = 0` piece plus the
subcase-(ii) region at the canonical threshold `⌈H^(1/(4n))⌉` together are
`O(H^(n-1))`.  (The eventual Case-III set also contains the still-open
subcase (i).) -/
theorem ddzero_add_subcase2_isBigO (n : ℕ) (hn : 3 ≤ n) :
    (fun H : ℕ => (((DDzeroBox n H).ncard + (CaseIIISubcase2 n H (lowerThr (4 * n) H)).ncard : ℕ) : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  classical
  rcases caseIII_subcase2_region_bound_pointwise n hn with ⟨C2, hC2⟩
  let C0 : ℕ := (n - 1) * ((4 * n - 3) * (2 * n - 1))
  have hle0 : ∀ᶠ H : ℕ in atTop,
      (DDzeroBox n H).ncard ≤ C0 * (2 * H + 1) ^ (n - 1) := by
    filter_upwards with H
    exact DDzeroBox_ncard_le n H hn
  let C : ℕ := C0 * 3 ^ (n - 1) + C2
  have hpoint : ∀ᶠ H : ℕ in atTop,
      (DDzeroBox n H).ncard + (CaseIIISubcase2 n H (lowerThr (4 * n) H)).ncard ≤ C * H ^ (n - 1) := by
    filter_upwards [hle0, hC2, eventually_ge_atTop (1 : ℕ)] with H hz hc2 hH
    have hz' : (DDzeroBox n H).ncard ≤ (C0 * 3 ^ (n - 1)) * H ^ (n - 1) := by
      calc
        (DDzeroBox n H).ncard ≤ C0 * (2 * H + 1) ^ (n - 1) := hz
        _ ≤ C0 * (3 * H) ^ (n - 1) := by
          exact Nat.mul_le_mul_left C0 (pow_le_pow_left₀ (by omega) (by omega) (n - 1))
        _ = (C0 * 3 ^ (n - 1)) * H ^ (n - 1) := by
          rw [mul_pow]; ring
    calc
      (DDzeroBox n H).ncard + (CaseIIISubcase2 n H (lowerThr (4 * n) H)).ncard
          ≤ (C0 * 3 ^ (n - 1)) * H ^ (n - 1) + C2 * H ^ (n - 1) := by
            exact Nat.add_le_add hz' hc2
      _ = (C0 * 3 ^ (n - 1) + C2) * H ^ (n - 1) := by rw [add_mul]
  exact Commons.Analysis.Asymptotics.isBigO_of_natCast_le_mul_pow (n - 1) C
    (fun H : ℕ => (DDzeroBox n H).ncard + (CaseIIISubcase2 n H (lowerThr (4 * n) H)).ncard) hpoint

end

end Submission.Vdw
