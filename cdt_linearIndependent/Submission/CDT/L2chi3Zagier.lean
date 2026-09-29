import Mathlib
import Submission.Commons.Analysis.InfiniteSum.nat_mul_geom_hasSum
import Submission.Commons.Analysis.InfiniteSum.nat_sq_geom_hasSum
import Submission.Commons.Analysis.InfiniteSum.nat_cube_geom_hasSum
import Submission.Commons.Analysis.InfiniteSum.nat_pow4_geom_hasSum
import Submission.CDT.L2chi3Real
import Submission.Commons.Analysis.Integral.integral_mul_integral_mul_integral_interval

/-!
# Sub-leaf (4) of CDT Theorem A: Zagier's hypergeometric evaluation of `L(2,χ₋₃)`

The paper's display after Theorem `mainA` (arXiv:2408.15403, citing
Hessami Pilehrood & Hessami Pilehrood, "Bivariate identities for values of
the Hurwitz zeta function and supercongruences", Electron. J. Combin. 18
(2011), §3) gives, besides the period-integral and Pascal-triangle
representations, the hypergeometric-type series

```lean
L(2,χ₋₃) = (1/27) · Σ_{n=1}^∞ (4 − 15n)·(−27)ⁿ / (n³·C(2n,n)²·C(3n,n))
```

i.e. `theoremA_leaf_hypergeom` below (module target).  This file pins down
the objects and proves the ground facts:

* `zagierL2chiTerm n : ℚ` — the summand (`t₀ := 0` artificial, so the sum
  runs over all of `ℕ`); values `t₀ = 0`, `t₁ = 99/4`, `t₂ = −351/80`
  (matching a direct evaluation);
* `zagierL2chiSeries : ℝ := ∑' n, (tₙ : ℝ)` — the series of the paper's
  RHS before the `1/27` factor;
* `theoremA_leaf_hypergeom : Prop` — the identity
  `zagierL2chiSeries = 27 · L(2,χ₋₃)` (equivalently
  `L(2,χ₋₃) = (1/27)·Σₙtₙ`);
* the absolute value of the summand for `n ≥ 1`:
  `|tₙ| = (15n−4)·27ⁿ / (n³·C(2n,n)²·C(3n,n))`, in `ℚ`
  (`zagierL2chiTerm_abs`, `zagierL2chiTerm_abs_cb` with `centralBinom`) and
  after the cast to `ℝ` (`zagierL2chiTerm_abs_real`), plus the elementary
  sign lemmas (`abs_neg27_pow`, `abs_four_sub_fifteen_mul`) and
  `zagierL2chiTerm_ne_zero` (`tₙ ≠ 0` for `n ≥ 1`).

**Brick (i) — absolute convergence — is DONE.**  The exact binomial-step
ratios are proved from the factorial identities `Nat.cast_add_choose`
(`choose_three_succ_ratio` for `C(3(n+1),n+1)/C(3n,n)` via the cast
factorial expansions `cast_fact_three_succ`, `cast_fact_two_succ`;
`centralBinom_succ_ratio` for `C(2(n+1),n+1)/C(2n,n)` via
`Nat.succ_mul_centralBinom_succ`).  With these, the successive-ratio bound
is `abs_term_ratio_le_half : |t_{n+1}| ≤ ½·|tₙ|` for `n ≥ 4` (via the
exact rational ratio `ratioE` = `abs_term_ratio_eq`, bounded by `½` in
`ratioE_le_half` from the polynomial comparison `ratioE_poly_le`, whose
positivity after the shift `n = 4+k` is by `ring_nf` + `positivity`).
Iterating gives geometric decay `abs_term_geom : |tₙ| ≤ |t₄|·(½)ⁿ⁻⁴`
(`n ≥ 4`), and comparing the shifted absolute values with the summable
geometric series (`Summable.of_nonneg_of_le`, `summable_geometric_of_lt_one`)
gives

```lean
theorem summable_zagierL2chi_term : Summable fun n : ℕ => (zagierL2chiTerm n : ℝ)
```

(the finite prefix is reattached with `hasSum_nat_add_iff`).

**[Historical route note: the paragraphs from here to the "Box form"
paragraph describe a polylog-summation approach to Brick (ii) that was
*superseded* — Brick (ii) (the identity itself) is CLOSED, see the closing
paragraphs of this docstring and module `Submission.CDT.ZagierWZ`.]**
First component sub-lemmas are committed in the Beta-integral section
below:
`beta_nat_eq_factorial_div_gen` (`B(n+1,m+1) = n!·m!/(n+m+1)!` from
`Complex.Gamma_mul_Gamma_eq_betaIntegral`), the factorial/choose identities
`centralBinom_mul_fact_sq`, `choose_three_mul_fact`, and the
reciprocal-binomial representations `centralBinom_recip_beta`
(`C(2n,n)⁻¹ = (2n+1)·B(n+1,n+1)`), `choose_three_recip_beta`
(`C(3n,n)⁻¹ = (3n+1)·B(n+1,2n+1)`) — in the raw complex-`betaIntegral`
form (`betaIntegral u v` *is* `∫₀¹ x^(u−1)(1−x)^(v−1) dx`).  The
**real-cast is done** in the "Real-cast of the beta integrals" section
below: `integral_pow_mul_one_sub_pow_real`,
`centralBinom_recip_real`, `choose_three_recip_real`, and
`zagierL2chi_denom_integral` (the full summand denominator in integral
form, with the `1/n³` factor attached).  The remaining step of that
route — the geometric/polylog summation of `Σₙ poly(n)·Xⁿ` over the
resulting integral family — was a candidate attack: expand the summands
into a double sum over `ℕ × ℕ` and reorganize to the paired residue
series `Σₖ (1/(3k+1)² − 1/(3k+2)²)` (which `L2chi3Real` is, by
`L2chi3Real_eq_pair_tsum`), or to the sibling Pascal-triangle double sum
`L(2,χ₋₃) = −1/3 + Σ_{n>m>0} 1/C(n,m)²` displayed immediately after in the
paper; either through `Finset`-level partial sums + `HasSum`/`Summable`
limits, or through a creative-telescoping (Zeilberger) certificate of the
type already used for `Commons.Data.Nat.Choose.zagierC_recurrence`.  In
the end the Markov–WZ certificate route of `ZagierWZ` closed the identity
directly.

**Box form (DONE, appended section at the end of the file).**  The
summand is a *box (triple) integral* over the unit cube with kernel
`Z = zagierL2chiBoxZ x y z = −27·x(1−x)·y(1−y)·z(1−z)²` (so `|Z| ≤ 1/4`
on the cube — `zagierL2chi_boxZ_norm_lt_one`, `zagierL2chi_boxZ_abs_pow_le`):
`zagierL2chiIntegralTerm n = ∫₀¹∫₀¹∫₀¹ P(n)·Z(x,y,z)ⁿ/n³ dx dy dz` with
`P(n) = (4−15n)(2n+1)²(3n+1)` (`theorem zagierL2chiIntegralTerm_box`),
proved via the kernel power identity `zagierL2chiBoxZ_pow_eq`, the
single-variable reduction `int_one_sub_sq_pow_eq`
(`∫(x(1−x)²)ⁿ = ∫xⁿ(1−x)^{2n}`), the product-of-integrals lemma
`zagierL2chiBoxZ_pow_triple` (`∫∫∫Zⁿ = (−27)ⁿ·(∫(x(1−x))ⁿ)²·∫xⁿ(1−x)^{2n}`,
Commons `integral_mul_integral_mul_integral_interval`) and pure algebra.

All lemmas in this module are fully proved (no axioms, no `sorry`).
**Brick (ii) — the identity itself — is CLOSED** (see the `DONE` paragraph
above and module `Submission.CDT.ZagierWZ`): the Markov–WZ certificate at
`a=0, α=1/3, β=2/3` is fully formalized there — the closed-form WZ kernel
`zagierF`, its mate `zagierG = zagierF·zagierQ`, the WZ relation
`zagier_wz`, the rectangle telescoping `zagier_rect'`, the termwise
identifications `F(0,k) = 27·pairSum k` and `G(n,0) = t_{n+1}`, the decay
bounds (`|R(n,k)| ≤ 1/2`, `|F(n,k)| ≤ 2⁻ⁿ·|F(0,k)|`,
`|G(n,k)| ≤ 14(k+1)²·|F(0,k)|·2⁻ⁿ`), the `N → ∞` and `K → ∞` limits
(`zagier_rect_limit_N`, `tsum_zagierG_M_tendsto_zero`) giving the WZ
infinite telescoping `zagier_wz_infinite_thm`, and hence the two theorem
declarations `zagierL2chi_identity : theoremA_leaf_hypergeom` and
`zagierL2chi_leaf_main` (which used to be the `sorry` placeholders of this
module; they live in `ZagierWZ` because this module cannot import it —
import cycle).  Everything this module pins down (summand, series,
absolute convergence, normalizations, box form) is proved here.
-/

open scoped BigOperators

noncomputable section

namespace Submission.CDT

/-- Zagier's hypergeometric-type summand (paper display after Thm. mainA,
cite HPHP11 §3): `(4 − 15n)(−27)ⁿ / (n³·C(2n,n)²·C(3n,n))` for `n ≥ 1`,
rational-valued; `t₀ := 0` is an artificial convention so the sum runs over
all `ℕ`. -/
def zagierL2chiTerm (n : ℕ) : ℚ :=
  if n = 0 then 0 else
    ((4 : ℚ) - 15 * (n : ℚ)) * (-27 : ℚ) ^ n /
      ((n : ℚ) ^ 3 * ((Nat.choose (2 * n) n : ℚ) ^ 2) * (Nat.choose (3 * n) n : ℚ))

/-- the real series `Σₙ tₙ` (the paper's RHS before the `1/27` factor) -/
def zagierL2chiSeries : ℝ := ∑' n : ℕ, (zagierL2chiTerm n : ℝ)

/-- Sub-leaf 4 of the roadmap: Zagier's hypergeometric evaluation
`L(2,χ₋₃) = (1/27)·Σₙ tₙ`. -/
def theoremA_leaf_hypergeom : Prop :=
  zagierL2chiSeries = 27 * L2chi3Real

lemma zagierL2chiTerm_zero : zagierL2chiTerm 0 = 0 := by
  simp [zagierL2chiTerm]

lemma zagierL2chiTerm_one : zagierL2chiTerm 1 = 99 / 4 := by
  norm_num [zagierL2chiTerm]

lemma zagierL2chiTerm_two : zagierL2chiTerm 2 = -351 / 80 := by
  native_decide

/-- the positive absolute-value version of the summand: `(15n−4)·27ⁿ/(…)`,
matching `|tₙ|` for `n ≥ 1` -/
def zagierL2chiAbs (n : ℕ) : ℚ :=
  if n = 0 then 0 else
    ((15 * (n : ℚ) - 4) * (27 : ℚ) ^ n) /
      ((n : ℚ) ^ 3 * ((Nat.choose (2 * n) n : ℚ) ^ 2) * (Nat.choose (3 * n) n : ℚ))

/-- sign pattern of the integer power `(−27)ⁿ` -/
lemma abs_neg27_pow (n : ℕ) : |(-27 : ℚ) ^ n| = (27 : ℚ) ^ n := by
  rw [abs_pow, abs_of_neg (by norm_num : (-27 : ℚ) < 0)]
  norm_num

lemma abs_four_sub_fifteen_mul (n : ℕ) (hn : 1 ≤ n) :
    |(4 : ℚ) - 15 * (n : ℚ)| = 15 * (n : ℚ) - 4 := by
  have h : (4 : ℚ) - 15 * (n : ℚ) < 0 := by
    have hnq : 1 ≤ (n : ℚ) := by exact_mod_cast hn
    nlinarith
  rw [abs_of_neg h]
  ring

/-- the absolute value of the hypergeometric summand for `n ≥ 1`:
`|tₙ| = (15n−4)·27ⁿ/(n³·C(2n,n)²·C(3n,n))` -/
lemma zagierL2chiTerm_abs (n : ℕ) (hn : 1 ≤ n) :
    |zagierL2chiTerm n| = zagierL2chiAbs n := by
  have hn0 : ¬ n = 0 := by omega
  have hnn : 0 < n := lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn
  have hnqpos : 0 < (n : ℚ) := by exact_mod_cast hnn
  have hc1 : 0 < (Nat.choose (2 * n) n : ℚ) := by
    exact_mod_cast (Nat.choose_pos (by omega : n ≤ 2 * n))
  have hc2 : 0 < (Nat.choose (3 * n) n : ℚ) := by
    exact_mod_cast (Nat.choose_pos (by omega : n ≤ 3 * n))
  have hd : 0 < (n : ℚ) ^ 3 * ((Nat.choose (2 * n) n : ℚ) ^ 2) * (Nat.choose (3 * n) n : ℚ) := by
    exact mul_pos (mul_pos (pow_pos hnqpos 3) (sq_pos_of_ne_zero (ne_of_gt hc1))) hc2
  unfold zagierL2chiTerm zagierL2chiAbs
  simp only [if_neg hn0]
  rw [abs_div]
  rw [abs_mul, abs_neg27_pow, abs_four_sub_fifteen_mul n hn]
  rw [abs_of_pos hd]

/-- the same absolute-value identity after casting to `ℝ` -/
lemma zagierL2chiTerm_abs_real (n : ℕ) (hn : 1 ≤ n) :
    |(zagierL2chiTerm n : ℝ)| = (zagierL2chiAbs n : ℝ) := by
  rw [← Rat.cast_abs]
  exact congrArg (fun q : ℚ => (q : ℝ)) (zagierL2chiTerm_abs n hn)


/-! ## Absolute convergence (brick (i)) -/

/-- `(3n+3)! = (3n)!·(3n+1)(3n+2)(3n+3)` in `ℚ` -/
lemma cast_fact_three_succ (n : ℕ) :
    ((3 * (n + 1)).factorial : ℚ) = ((3 * n).factorial : ℚ) *
      ((3 * (n : ℚ) + 1) * (3 * (n : ℚ) + 2) * (3 * (n : ℚ) + 3)) := by
  rw [show 3 * (n + 1) = 3 * n + 3 by omega]
  rw [show 3 * n + 3 = 3 * n + 2 + 1 by omega, Nat.factorial_succ]
  rw [show 3 * n + 2 = 3 * n + 1 + 1 by omega, Nat.factorial_succ]
  rw [Nat.factorial_succ]
  norm_num
  ring

/-- `(2n+2)! = (2n)!·(2n+1)(2n+2)` in `ℚ` -/
lemma cast_fact_two_succ (n : ℕ) :
    ((2 * (n + 1)).factorial : ℚ) = ((2 * n).factorial : ℚ) *
      ((2 * (n : ℚ) + 1) * (2 * (n : ℚ) + 2)) := by
  rw [show 2 * (n + 1) = 2 * n + 2 by omega]
  rw [show 2 * n + 2 = 2 * n + 1 + 1 by omega, Nat.factorial_succ]
  rw [Nat.factorial_succ]
  norm_num
  ring

/-- the step of `C(3n,n)` as `n ↦ n+1` (exact `ℚ`-ratio): -/
lemma choose_three_succ_ratio (n : ℕ) :
    (Nat.choose (3 * (n + 1)) (n + 1) : ℚ) =
      (Nat.choose (3 * n) n : ℚ) *
        (((3 * (n : ℚ) + 1) * (3 * (n : ℚ) + 2) * (3 * (n : ℚ) + 3)) /
          (((n : ℚ) + 1) * (2 * (n : ℚ) + 1) * (2 * (n : ℚ) + 2))) := by
  rw [show 3 * (n + 1) = (n + 1) + 2 * (n + 1) by omega]
  rw [show 3 * n = n + 2 * n by omega]
  rw [Nat.cast_add_choose (K := ℚ) (a := n + 1) (b := 2 * (n + 1))]
  rw [Nat.cast_add_choose (K := ℚ) (a := n) (b := 2 * n)]
  rw [show (n + 1) + 2 * (n + 1) = 3 * (n + 1) by omega]
  rw [show n + 2 * n = 3 * n by omega]
  rw [cast_fact_three_succ n]
  rw [Nat.factorial_succ]
  rw [cast_fact_two_succ n]
  field_simp
  all_goals push_cast
  all_goals ring

/-- the step of the central binomial `C(2n,n)` as `n ↦ n+1` (exact `ℚ`-ratio,
from `Nat.succ_mul_centralBinom_succ`): -/
lemma centralBinom_succ_ratio (n : ℕ) :
    (Nat.centralBinom (n + 1) : ℚ) =
      (Nat.centralBinom n : ℚ) * (2 * (2 * (n : ℚ) + 1) / ((n : ℚ) + 1)) := by
  have hq : ((n : ℚ) + 1) * (Nat.centralBinom (n + 1) : ℚ) =
      2 * (2 * (n : ℚ) + 1) * (Nat.centralBinom n : ℚ) := by
    have h := Nat.succ_mul_centralBinom_succ n
    have hq0 := congrArg (fun z : ℕ => (z : ℚ)) h
    push_cast at hq0
    simpa [mul_comm, mul_left_comm, mul_assoc] using hq0
  have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  rw [← mul_div_assoc]
  exact (eq_div_iff_mul_eq hn1).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hq)

/-- `|tₙ|` rewritten with `Nat.centralBinom` (convenient for the ratio bound) -/
lemma zagierL2chiTerm_abs_cb (n : ℕ) (hn : 1 ≤ n) :
    |zagierL2chiTerm n| =
      ((15 * (n : ℚ) - 4) * (27 : ℚ) ^ n) /
        ((n : ℚ) ^ 3 * (Nat.centralBinom n : ℚ) ^ 2 * (Nat.choose (3 * n) n : ℚ)) := by
  rw [zagierL2chiTerm_abs n hn]
  unfold zagierL2chiAbs
  rw [if_neg (by omega : ¬ n = 0), Nat.centralBinom_eq_two_mul_choose]


/-- the exact ratio `|t_{n+1}|/|tₙ|` as a rational function of `n` -/
def ratioE (n : ℕ) : ℚ :=
  ((15 * (n : ℚ) + 11) / (15 * (n : ℚ) - 4)) * 27 *
    ((n : ℚ) / ((n : ℚ) + 1))^3 *
    (((n : ℚ) + 1) / (2 * (2 * (n : ℚ) + 1)))^2 *
    (((n : ℚ) + 1) * (2 * (n : ℚ) + 1) * (2 * (n : ℚ) + 2)) /
      ((3 * (n : ℚ) + 1) * (3 * (n : ℚ) + 2) * (3 * (n : ℚ) + 3))

/-- the polynomial comparison behind `ratioE ≤ 1/2` for `n ≥ 4`:
`(15n+11)·27·n³·(n+1) ≤ (15n−4)(2n+1)(3n+1)(3n+2)(3n+3)` -/
lemma ratioE_poly_le (n : ℕ) (hn : 4 ≤ n) :
    (15 * (n : ℚ) + 11) * 27 * (n : ℚ) ^ 3 * ((n : ℚ) + 1) ≤
      (15 * (n : ℚ) - 4) * (2 * (n : ℚ) + 1) * (3 * (n : ℚ) + 1) *
        (3 * (n : ℚ) + 2) * (3 * (n : ℚ) + 3) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = 4 + k := ⟨n - 4, by omega⟩
  have hD : 0 ≤ (15 * ((4 + k : ℕ) : ℚ) - 4) * (2 * ((4 + k : ℕ) : ℚ) + 1) *
      (3 * ((4 + k : ℕ) : ℚ) + 1) * (3 * ((4 + k : ℕ) : ℚ) + 2) * (3 * ((4 + k : ℕ) : ℚ) + 3) -
      (15 * ((4 + k : ℕ) : ℚ) + 11) * 27 * ((4 + k : ℕ) : ℚ) ^ 3 * (((4 + k : ℕ) : ℚ) + 1) := by
    simp only [Nat.cast_add, Nat.cast_ofNat]
    ring_nf
    positivity
  exact (sub_nonneg.mp hD)

/-- `ratioE ≤ 1/2` for `n ≥ 4` -/
lemma ratioE_le_half (n : ℕ) (hn : 4 ≤ n) : ratioE n ≤ (1 / 2 : ℚ) := by
  unfold ratioE
  have hp : 0 < 15 * (n : ℚ) - 4 := by
    nlinarith [show (4 : ℚ) ≤ (n : ℚ) by exact_mod_cast hn]
  have hc : 15 * (n : ℚ) - 4 ≠ 0 := ne_of_gt hp
  field_simp
  ring_nf
  have hP : 297 * (n : ℚ) ^ 3 + 405 * (n : ℚ) ^ 4 ≤
      -24 - 66 * (n : ℚ) + 261 * (n : ℚ) ^ 2 + 999 * (n : ℚ) ^ 3 + 810 * (n : ℚ) ^ 4 := by
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = 4 + k := ⟨n - 4, by omega⟩
    have hD : 0 ≤ -24 - 66 * ((4 + k : ℕ) : ℚ) + 261 * ((4 + k : ℕ) : ℚ) ^ 2 + 999 * ((4 + k : ℕ) : ℚ) ^ 3 +
        810 * ((4 + k : ℕ) : ℚ) ^ 4 - (297 * ((4 + k : ℕ) : ℚ) ^ 3 + 405 * ((4 + k : ℕ) : ℚ) ^ 4) := by
      simp only [Nat.cast_add, Nat.cast_ofNat]
      ring_nf
      positivity
    exact (sub_nonneg.mp hD)
  nlinarith [hP]


/-- the summand is never zero for `n ≥ 1` -/
lemma zagierL2chiTerm_ne_zero (n : ℕ) (hn : 1 ≤ n) : zagierL2chiTerm n ≠ 0 := by
  unfold zagierL2chiTerm
  rw [if_neg (by omega : ¬ n = 0)]
  apply div_ne_zero
  · apply mul_ne_zero
    · nlinarith [show (1 : ℚ) ≤ (n : ℚ) by exact_mod_cast hn]
    · exact pow_ne_zero _ (by norm_num)
  · have hnn : (n : ℚ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn))
    have hc1 : (Nat.choose (2 * n) n : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : n ≤ 2 * n)).ne'
    have hc2 : (Nat.choose (3 * n) n : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : n ≤ 3 * n)).ne'
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hnn) (pow_ne_zero 2 hc1)) hc2

/-- `|t_{n+1}|/|tₙ|` is exactly the rational function `ratioE n` (n ≥ 1) -/
lemma abs_term_ratio_eq (n : ℕ) (hn : 1 ≤ n) :
    |zagierL2chiTerm (n + 1)| / |zagierL2chiTerm n| = ratioE n := by
  have h1 : 1 ≤ n + 1 := by omega
  rw [zagierL2chiTerm_abs_cb (n + 1) h1, zagierL2chiTerm_abs_cb n hn]
  rw [centralBinom_succ_ratio n, choose_three_succ_ratio n]
  rw [pow_succ']
  unfold ratioE
  have hnm : (n : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn))
  have hncb : (Nat.centralBinom n : ℚ) ≠ 0 := by exact_mod_cast (Nat.centralBinom_ne_zero n)
  have hnc3 : (Nat.choose (3 * n) n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : n ≤ 3 * n)).ne'
  have hn15 : 15 * (n : ℚ) - 4 ≠ 0 := by
    have : 0 < 15 * (n : ℚ) - 4 := by nlinarith [show (1 : ℚ) ≤ (n : ℚ) by exact_mod_cast hn]
    exact ne_of_gt this
  field_simp [hnm, hncb, hnc3, hn15]
  all_goals push_cast
  all_goals ring

/-- successive-ratio bound: `|t_{n+1}| ≤ ½·|tₙ|` for `n ≥ 4` -/
lemma abs_term_ratio_le_half (n : ℕ) (hn : 4 ≤ n) :
    |zagierL2chiTerm (n + 1)| ≤ (1 / 2 : ℚ) * |zagierL2chiTerm n| := by
  have hn1 : 1 ≤ n := by omega
  have hpos : 0 < |zagierL2chiTerm n| := abs_pos.mpr (zagierL2chiTerm_ne_zero n hn1)
  have hq : |zagierL2chiTerm (n + 1)| / |zagierL2chiTerm n| ≤ (1 : ℚ) / 2 := by
    rw [abs_term_ratio_eq n hn1]
    exact ratioE_le_half n hn
  exact (div_le_iff₀ hpos).mp hq

/-- geometric decay from the index-4 term onward -/
lemma abs_term_geom (n : ℕ) (hn : 4 ≤ n) :
    |zagierL2chiTerm n| ≤ |zagierL2chiTerm 4| * ((1 / 2 : ℚ) ^ (n - 4)) := by
  induction' n with n ih
  · omega
  · by_cases hn4 : n + 1 = 4
    · have hn3 : n = 3 := by omega
      subst n
      simp
    · have hn4' : 4 ≤ n := by omega
      have hstep := abs_term_ratio_le_half n hn4'
      have hrec := ih hn4'
      calc
        |zagierL2chiTerm (n + 1)| ≤ (1 / 2 : ℚ) * |zagierL2chiTerm n| := hstep
        _ ≤ (1 / 2 : ℚ) * (|zagierL2chiTerm 4| * ((1 / 2 : ℚ) ^ (n - 4))) := by
          exact mul_le_mul_of_nonneg_left hrec (by norm_num : (0 : ℚ) ≤ 1 / 2)
        _ = |zagierL2chiTerm 4| * ((1 / 2 : ℚ) ^ (n + 1 - 4)) := by
          rw [show n + 1 - 4 = (n - 4) + 1 by omega, pow_succ']
          ring


/-- the shifted absolute values are dominated by a geometric series -/
lemma summable_zagier_abs_shift :
    Summable fun k : ℕ => ‖(zagierL2chiTerm (k + 4) : ℝ)‖ := by
  refine Summable.of_nonneg_of_le (f := fun k : ℕ => ((|zagierL2chiTerm 4| : ℚ) : ℝ) * (1 / 2 : ℝ) ^ k)
    (fun k => norm_nonneg _) ?hle ?hf
  · intro k
    have hg0 : |zagierL2chiTerm (k + 4)| ≤ |zagierL2chiTerm 4| * (1 / 2 : ℚ) ^ k := by
      have h0 := abs_term_geom (k + 4) (by omega)
      simpa [show k + 4 - 4 = k by omega] using h0
    rw [Real.norm_eq_abs, ← Rat.cast_abs]
    have hc : (((|zagierL2chiTerm (k + 4)| : ℚ)) : ℝ) ≤
        ((((|zagierL2chiTerm 4| : ℚ) * (1 / 2 : ℚ) ^ k) : ℚ) : ℝ) := by
      exact_mod_cast hg0
    rw [Rat.cast_mul, Rat.cast_pow] at hc
    norm_num at hc
    simpa using hc
  · exact Summable.mul_left ((|zagierL2chiTerm 4| : ℚ) : ℝ)
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
        (by norm_num : (1 / 2 : ℝ) < 1))

/-- the shifted series is summable -/
lemma summable_zagierL2chi_shift : Summable fun k : ℕ => (zagierL2chiTerm (k + 4) : ℝ) := by
  exact Summable.of_norm_bounded summable_zagier_abs_shift (fun k => le_rfl)

/-- **absolute convergence (brick (i))**: the hypergeometric series
`Σₙ tₙ` of `theoremA_leaf_hypergeom` converges (absolutely). -/
theorem summable_zagierL2chi_term : Summable fun n : ℕ => (zagierL2chiTerm n : ℝ) := by
  rcases summable_zagierL2chi_shift with ⟨g, hg⟩
  have ht : HasSum (fun n : ℕ => (zagierL2chiTerm n : ℝ))
      (g + ∑ i ∈ Finset.range 4, (zagierL2chiTerm i : ℝ)) := by
    exact (hasSum_nat_add_iff (f := fun n : ℕ => (zagierL2chiTerm n : ℝ)) 4).1 hg
  exact ⟨g + ∑ i ∈ Finset.range 4, (zagierL2chiTerm i : ℝ), ht⟩


/-! ## Brick (ii) — the identity itself (statement + first normalizations) -/

/-- each paired residue summand in the common rational form
`(6k+3)/((3k+1)²(3k+2)²)` (partial-fraction normalization used when matching
the two sides of the identity) -/
lemma pairSum_rat_norm (k : ℕ) :
    pairSum k = (6 * (k : ℝ) + 3) /
      (((3 * (k : ℝ) + 1) ^ 2) * ((3 * (k : ℝ) + 2) ^ 2)) := by
  rw [pairSum_eq]
  have h1 : ((3 * k + 1 : ℕ) : ℝ) = 3 * (k : ℝ) + 1 := by norm_num [Nat.cast_add, Nat.cast_mul]
  have h2 : ((3 * k + 2 : ℕ) : ℝ) = 3 * (k : ℝ) + 2 := by norm_num [Nat.cast_add, Nat.cast_mul]
  rw [h1, h2]
  field_simp
  ring

/-- the identity restated against the paired-residue series (the form a
rearrangement proof works with): `Σₖ pairSum k = (1/27)·Σₙ tₙ` -/
lemma zagierL2chi_identity_iff_pair :
    theoremA_leaf_hypergeom ↔ (∑' k : ℕ, pairSum k) = (1 / 27 : ℝ) * zagierL2chiSeries := by
  unfold theoremA_leaf_hypergeom zagierL2chiSeries
  rw [L2chi3Real_eq_pair_tsum]
  constructor
  · intro h
    calc
      (∑' k : ℕ, pairSum k) = (1 / 27 : ℝ) * (27 * (∑' k : ℕ, pairSum k)) := by field_simp
      _ = (1 / 27 : ℝ) * (∑' n : ℕ, (zagierL2chiTerm n : ℝ)) := by rw [← h]
  · intro h
    calc
      (∑' n : ℕ, (zagierL2chiTerm n : ℝ)) = 27 * ((1 / 27 : ℝ) * (∑' n : ℕ, (zagierL2chiTerm n : ℝ))) := by
        field_simp
      _ = 27 * (∑' k : ℕ, pairSum k) := by rw [h]

/-! **BRICK (ii) — DONE.**  Zagier's hypergeometric-type evaluation of
`L(2,χ₋₃)` (`zagierL2chiSeries = 27 · L(2,χ₋₃)`, paper display after Thm.
`mainA`, cite HPHP11 §3) is proved in `Submission.CDT.ZagierWZ` via the
Markov–WZ certificate + the analytic `N → ∞`/`K → ∞` limits; the theorem
`zagierL2chi_identity` lives there (this module cannot import it without a
cycle).  Absolute convergence (`summable_zagierL2chi_term`) is proved
above. -/
open Complex

/-! ## Brick (ii) — Beta-integral component lemmas

The first honest sub-lemmas of the Beta/Gamma route to `zagierL2chi_identity`
(Mathlib `Complex.betaIntegral u v = ∫ x in 0..1, x^(u−1)·(1−x)^(v−1)`):

* `beta_nat_eq_factorial_div_gen` : `B(n+1, m+1) = n!·m!/(n+m+1)!`
  (from `Complex.Gamma_mul_Gamma_eq_betaIntegral` + `Gamma_nat_eq_factorial`),
* the factorial/choose identities `centralBinom_mul_fact_sq`,
  `choose_three_mul_fact`,
* the reciprocal-binomial representations
  `centralBinom_recip_beta` : `C(2n,n)⁻¹ = (2n+1)·B(n+1,n+1)`
  = `(2n+1)·∫₀¹ xⁿ(1−x)ⁿ dx`, and
  `choose_three_recip_beta` : `C(3n,n)⁻¹ = (3n+1)·B(n+1,2n+1)`
  = `(3n+1)·∫₀¹ xⁿ(1−x)²ⁿ dx`.

(The complex-valued `betaIntegral` form is the raw Mathlib object; the
real-cast of the right-hand side to `∫₀¹ (x·(1−x))ⁿ dx` is the next
micro-step.) -/

/-- the beta value at positive integers: `B(n+1, m+1) = n!·m!/(n+m+1)!` -/
lemma beta_nat_eq_factorial_div_gen (n m : ℕ) :
    Complex.betaIntegral (((n + 1 : ℕ) : ℂ)) (((m + 1 : ℕ) : ℂ)) =
      (Nat.factorial n : ℂ) * (Nat.factorial m : ℂ) / (Nat.factorial (n + m + 1) : ℂ) := by
  let s : ℂ := ((n + 1 : ℕ) : ℂ)
  let t : ℂ := ((m + 1 : ℕ) : ℂ)
  have hs : 0 < s.re := by dsimp [s]; positivity
  have ht : 0 < t.re := by dsimp [t]; positivity
  have hG := Complex.Gamma_mul_Gamma_eq_betaIntegral hs ht
  have hGam1 : Gamma s = (Nat.factorial n : ℂ) := by
    dsimp [s]
    rw [show (((n + 1 : ℕ) : ℂ)) = (n : ℂ) + 1 by norm_num]
    exact Complex.Gamma_nat_eq_factorial n
  have hGam3 : Gamma t = (Nat.factorial m : ℂ) := by
    dsimp [t]
    rw [show (((m + 1 : ℕ) : ℂ)) = (m : ℂ) + 1 by norm_num]
    exact Complex.Gamma_nat_eq_factorial m
  have hGam2 : Gamma (s + t) = (Nat.factorial (n + m + 1) : ℂ) := by
    dsimp [s, t]
    rw [show (((n + 1 : ℕ) : ℂ) + ((m + 1 : ℕ) : ℂ)) =
        ((n + m + 1 : ℕ) : ℂ) + 1 by norm_num; ring]
    exact Complex.Gamma_nat_eq_factorial (n + m + 1)
  have hYne : (Nat.factorial (n + m + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (n + m + 1))
  rw [hGam1, hGam3, hGam2] at hG
  have hmul : Complex.betaIntegral s t * (Nat.factorial (n + m + 1) : ℂ) =
      (Nat.factorial n : ℂ) * (Nat.factorial m : ℂ) := by
    simpa [mul_comm] using hG.symm
  have hb : Complex.betaIntegral s t = (Nat.factorial n : ℂ) * (Nat.factorial m : ℂ) /
      (Nat.factorial (n + m + 1) : ℂ) := by
    exact (eq_div_iff_mul_eq hYne).2 hmul
  simpa [s, t] using hb

/-- `C(2n,n)·n!·n! = (2n)!` (in `ℂ`) -/
lemma centralBinom_mul_fact_sq (n : ℕ) :
    (Nat.centralBinom n : ℂ) * (Nat.factorial n : ℂ) * (Nat.factorial n : ℂ) =
      (Nat.factorial (2 * n) : ℂ) := by
  have hnat : Nat.choose (2 * n) n * n.factorial * n.factorial = (2 * n).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (k := n) (n := 2 * n) (by omega : n ≤ 2 * n)
    simpa [show 2 * n - n = n by omega] using h
  rw [Nat.centralBinom_eq_two_mul_choose]
  exact_mod_cast hnat

/-- `C(3n,n)·n!·(2n)! = (3n)!` (in `ℂ`) -/
lemma choose_three_mul_fact (n : ℕ) :
    (Nat.choose (3 * n) n : ℂ) * (Nat.factorial n : ℂ) * (Nat.factorial (2 * n) : ℂ) =
      (Nat.factorial (3 * n) : ℂ) := by
  have hnat : Nat.choose (3 * n) n * n.factorial * (2 * n).factorial = (3 * n).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (k := n) (n := 3 * n) (by omega : n ≤ 3 * n)
    simpa [show 3 * n - n = 2 * n by omega] using h
  exact_mod_cast hnat

/-- the beta-integral representation of `1/C(2n,n)`: `C(2n,n)⁻¹ =
(2n+1)·B(n+1,n+1) = (2n+1)·∫₀¹ xⁿ(1−x)ⁿ dx` -/
lemma centralBinom_recip_beta (n : ℕ) :
    (Nat.centralBinom n : ℂ)⁻¹ =
      (2 * (n : ℂ) + 1) * Complex.betaIntegral (((n + 1 : ℕ) : ℂ)) (((n + 1 : ℕ) : ℂ)) := by
  rw [beta_nat_eq_factorial_div_gen n n]
  rw [show n + n + 1 = 2 * n + 1 by omega]
  have hfac : (Nat.factorial (2 * n + 1) : ℂ) = (2 * (n : ℂ) + 1) * (Nat.factorial (2 * n) : ℂ) := by
    have hnat : Nat.factorial (2 * n + 1) = (2 * n + 1) * Nat.factorial (2 * n) := by
      exact Nat.factorial_succ (2 * n)
    rw [hnat]
    norm_num
  have hcbn0 : (Nat.centralBinom n : ℂ) ≠ 0 := by exact_mod_cast (Nat.centralBinom_ne_zero n)
  have hY0 : (Nat.factorial (2 * n) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero (2 * n))
  have hZ0 : (2 * (n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by omega : 0 < 2 * n + 1))
  rw [hfac]
  field_simp [hZ0, hY0]
  have hcbsq := centralBinom_mul_fact_sq n
  have hX0 : (Nat.factorial n : ℂ) * (Nat.factorial n : ℂ) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast (Nat.factorial_ne_zero n))
      (by exact_mod_cast (Nat.factorial_ne_zero n))
  rw [← hcbsq]
  field_simp [hcbn0, hX0]

/-- the beta-integral representation of `1/C(3n,n)`: `C(3n,n)⁻¹ =
(3n+1)·B(n+1,2n+1) = (3n+1)·∫₀¹ xⁿ(1−x)²ⁿ dx` -/
lemma choose_three_recip_beta (n : ℕ) :
    (Nat.choose (3 * n) n : ℂ)⁻¹ =
      (3 * (n : ℂ) + 1) * Complex.betaIntegral (((n + 1 : ℕ) : ℂ)) (((2 * n + 1 : ℕ) : ℂ)) := by
  rw [beta_nat_eq_factorial_div_gen n (2 * n)]
  rw [show n + (2 * n) + 1 = 3 * n + 1 by omega]
  have hfac : (Nat.factorial (3 * n + 1) : ℂ) = (3 * (n : ℂ) + 1) * (Nat.factorial (3 * n) : ℂ) := by
    have hnat : Nat.factorial (3 * n + 1) = (3 * n + 1) * Nat.factorial (3 * n) := by
      exact Nat.factorial_succ (3 * n)
    rw [hnat]
    norm_num
  have hc0 : (Nat.choose (3 * n) n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : n ≤ 3 * n)).ne'
  have hY0 : (Nat.factorial (3 * n) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero (3 * n))
  have hZ0 : (3 * (n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by omega : 0 < 3 * n + 1))
  rw [hfac]
  field_simp [hZ0, hY0]
  have hc3 := choose_three_mul_fact n
  have hX0 : (Nat.factorial n : ℂ) * (Nat.factorial (2 * n) : ℂ) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast (Nat.factorial_ne_zero n))
      (by exact_mod_cast (Nat.factorial_ne_zero (2 * n)))
  rw [← hc3]


/-! ### Real-cast of the beta integrals (the `∫₀¹ (x(1−x))ⁿ dx` forms)

With the pointwise identity `ofReal_cpow_pow_mul` and the real↔complex
integral bridge `intervalIntegral.integral_ofReal`, the complex beta values
cast to the **real interval integrals**:

* `integral_pow_mul_one_sub_pow_real a b` : `∫₀¹ xᵃ(1−x)ᵇ dx = a!·b!/(a+b+1)!`;
* `integral_pow_one_sub_pow_self_real n` : `∫₀¹ (x(1−x))ⁿ dx = n!·n!/(2n+1)!`;
* `centralBinom_recip_real n` : `C(2n,n)⁻¹ = (2n+1)·∫₀¹ (x(1−x))ⁿ dx`;
* `choose_three_recip_real n` : `C(3n,n)⁻¹ = (3n+1)·∫₀¹ xⁿ(1−x)²ⁿ dx`;
* `zagierL2chi_denom_integral n` (n ≥ 1) : the **summand denominator in
  integral form**,
  `1/(n³·C(2n,n)²·C(3n,n)) = ((2n+1)·∫₀¹(x(1−x))ⁿ)²·((3n+1)·∫₀¹xⁿ(1−x)²ⁿ)/n³`.

With the coefficient `(4−15n)(−27)ⁿ` this gives the full summand
`tₙ = (4−15n)(−27)ⁿ·((2n+1)·∫₀¹(x(1−x))ⁿ)²·((3n+1)·∫₀¹xⁿ(1−x)²ⁿ)/n³`
— the integral form the geometric/polylog summation over `n` will act on. -/



/-- pointwise: complex powers of real `x`, `1−x` equal the real powers cast -/
lemma ofReal_cpow_pow_mul (a b : ℕ) (x : ℝ) :
    (x : ℂ) ^ (a : ℂ) * (1 - (x : ℂ)) ^ (b : ℂ) = ↑(x ^ a * (1 - x) ^ b) := by
  rw [Complex.cpow_natCast, Complex.cpow_natCast]
  rw [← Complex.ofReal_pow]
  rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_sub]
  rw [← Complex.ofReal_pow]
  rw [← Complex.ofReal_mul]

/-- `∫₀¹ xᵃ(1−x)ᵇ dx = a!·b!/(a+b+1)!` (real; via the complex beta integral) -/
lemma integral_pow_mul_one_sub_pow_real (a b : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b =
      (Nat.factorial a : ℝ) * (Nat.factorial b : ℝ) / (Nat.factorial (a + b + 1) : ℝ) := by
  have hmain : Complex.betaIntegral (((a + 1 : ℕ) : ℂ)) (((b + 1 : ℕ) : ℂ)) =
      (((∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b : ℝ)) : ℂ) := by
    unfold Complex.betaIntegral
    rw [show (((a + 1 : ℕ) : ℂ) - 1) = (a : ℂ) by norm_num]
    rw [show (((b + 1 : ℕ) : ℂ) - 1) = (b : ℂ) by norm_num]
    have hpt : (fun x : ℝ => (x : ℂ) ^ (a : ℂ) * (1 - (x : ℂ)) ^ (b : ℂ)) =
        fun x : ℝ => (((x ^ a * (1 - x) ^ b : ℝ) : ℂ)) := by
      funext x
      exact ofReal_cpow_pow_mul a b x
    rw [hpt]
    rw [← intervalIntegral.integral_ofReal]
  have hb := beta_nat_eq_factorial_div_gen a b
  rw [hmain] at hb
  have hW : ((((Nat.factorial a : ℝ) * (Nat.factorial b : ℝ) / (Nat.factorial (a + b + 1) : ℝ) : ℝ)) : ℂ) =
      (Nat.factorial a : ℂ) * (Nat.factorial b : ℂ) / (Nat.factorial (a + b + 1) : ℂ) := by
    norm_num [Complex.ofReal_natCast, Complex.ofReal_mul, Complex.ofReal_div]
  exact Complex.ofReal_inj.mp (hb.trans hW.symm)

/-- `∫₀¹ (x(1−x))ⁿ dx = n!·n!/(2n+1)!` -/
lemma integral_pow_one_sub_pow_self_real (n : ℕ) :
    ∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ n =
      (Nat.factorial n : ℝ) * (Nat.factorial n : ℝ) / (Nat.factorial (2 * n + 1) : ℝ) := by
  -- (x(1−x))^n = x^n·(1−x)^n pointwise
  have hpt : (fun x : ℝ => x ^ n * (1 - x) ^ n) = fun x : ℝ => (x * (1 - x)) ^ n := by
    funext x
    exact (mul_pow x (1 - x) n).symm
  rw [← hpt]
  -- match (a+b+1) = 2n+1 index of the generic lemma:
  have hg := integral_pow_mul_one_sub_pow_real n n
  convert hg using 1
  ring_nf

/-- `1/C(2n,n) = (2n+1)·∫₀¹ (x(1−x))ⁿ dx` (real) -/
lemma centralBinom_recip_real (n : ℕ) :
    (Nat.centralBinom n : ℝ)⁻¹ = (2 * (n : ℝ) + 1) * ∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ n := by
  have h1 := integral_pow_one_sub_pow_self_real n
  -- 1/cb = (2n+1)·(n!n!/(2n+1)!) : use complex-mirror via field_simp with the factorial identity? direct:
  -- (2n+1)! = (2n+1)(2n)! and cb·n!·n! = (2n)!:
  have hfac : (Nat.factorial (2 * n + 1) : ℝ) = (2 * (n : ℝ) + 1) * (Nat.factorial (2 * n) : ℝ) := by
    have hnat : Nat.factorial (2 * n + 1) = (2 * n + 1) * Nat.factorial (2 * n) := by
      exact Nat.factorial_succ (2 * n)
    rw [hnat]
    norm_num
  have hcbn : (Nat.centralBinom n : ℝ) * (Nat.factorial n : ℝ) * (Nat.factorial n : ℝ) =
      (Nat.factorial (2 * n) : ℝ) := by
    have h := centralBinom_mul_fact_sq n
    norm_num [Complex.ofReal_natCast] at h
    exact_mod_cast h
  have hcbn0 : (Nat.centralBinom n : ℝ) ≠ 0 := by exact_mod_cast (Nat.centralBinom_ne_zero n)
  have hZ0 : (2 * (n : ℝ) + 1) ≠ 0 := by exact_mod_cast (ne_of_gt (by omega : 0 < 2 * n + 1))
  -- (2n+1)·∫ = (2n+1)·(n!n!/(2n+1)!) = n!n!/(2n)! = 1/cb:
  rw [h1]
  field_simp [hfac, hcbn, hcbn0, hZ0]
  · rw [hfac]
    rw [← hcbn]
    ring_nf


/-- `1/C(3n,n) = (3n+1)·∫₀¹ xⁿ(1−x)²ⁿ dx` (real) -/
lemma choose_three_recip_real (n : ℕ) :
    (Nat.choose (3 * n) n : ℝ)⁻¹ =
      (3 * (n : ℝ) + 1) * ∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ (2 * n) := by
  have h1 := integral_pow_mul_one_sub_pow_real n (2 * n)
  rw [show n + (2 * n) + 1 = 3 * n + 1 by omega] at h1
  have hfac : (Nat.factorial (3 * n + 1) : ℝ) = (3 * (n : ℝ) + 1) * (Nat.factorial (3 * n) : ℝ) := by
    have hnat : Nat.factorial (3 * n + 1) = (3 * n + 1) * Nat.factorial (3 * n) := by
      exact Nat.factorial_succ (3 * n)
    rw [hnat]
    norm_num
  have hc3 : (Nat.choose (3 * n) n : ℝ) * (Nat.factorial n : ℝ) * (Nat.factorial (2 * n) : ℝ) =
      (Nat.factorial (3 * n) : ℝ) := by
    have h := choose_three_mul_fact n
    norm_num [Complex.ofReal_natCast] at h
    exact_mod_cast h
  have hc0 : (Nat.choose (3 * n) n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : n ≤ 3 * n)).ne'
  have hZ0 : (3 * (n : ℝ) + 1) ≠ 0 := by exact_mod_cast (ne_of_gt (by omega : 0 < 3 * n + 1))
  rw [h1]
  field_simp [hfac, hc3, hc0, hZ0]
  · rw [hfac]
    rw [← hc3]
    ring_nf

/-- the summand denominator in integral form: `1/(n³·C(2n,n)²·C(3n,n)) =
((2n+1)·∫₀¹(x(1−x))ⁿ)²·((3n+1)·∫₀¹xⁿ(1−x)²ⁿ) / n³` -/
lemma zagierL2chi_denom_integral (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℝ) / ((n : ℝ) ^ 3 * (Nat.centralBinom n : ℝ) ^ 2 * (Nat.choose (3 * n) n : ℝ)) =
      ((2 * (n : ℝ) + 1) * (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ n)) ^ 2 *
        ((3 * (n : ℝ) + 1) * (∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ (2 * n))) / (n : ℝ) ^ 3 := by
  have hc := centralBinom_recip_real n
  have h3 := choose_three_recip_real n
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn))
  have hcbn0 : (Nat.centralBinom n : ℝ) ≠ 0 := by exact_mod_cast (Nat.centralBinom_ne_zero n)
  have hc30 : (Nat.choose (3 * n) n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : n ≤ 3 * n)).ne'
  rw [hc.symm, h3.symm]
  field_simp [hn0, hcbn0, hc30]



/-! ## Brick (ii) — main summation lemma & coefficient manipulation

With the real-cast integral forms of the previous section, the summand of
`theoremA_leaf_hypergeom` becomes the **integral term**
`zagierL2chiIntegralTerm n := (4−15n)·(−27)ⁿ/n³ · ((2n+1)·∫₀¹(x(1−x))ⁿ)² ·
((3n+1)·∫₀¹xⁿ(1−x)²ⁿ)` (equal to `tₙ` termwise for `n ≥ 1` by
`zagierL2chi_denom_integral` — termwise lemma committed below as
`zagierL2chiTerm_eq_integralTerm`).  The whole of brick (ii) is therefore
equivalent to the **main summation lemma**

```lean
theorem zagierL2chi_leaf_main :
    L2chi3Real = (1 / 27 : ℝ) * ∑' n : ℕ, zagierL2chiIntegralTerm n
```

(no hypotheses; this is the statement the geometric/polylog summation work
aims at).  Its proof breaks into: (a) the termwise equality
`(tₙ:ℝ) = zagierL2chiIntegralTerm n` (proved below); (b) the geometric/
polylog summation over `n` of the quartic-coefficient family with the box
kernel `Z = zagierL2chiBoxZ x y z = −27·x(1−x)y(1−y)z(1−z)²` (whose
`‖Z‖ < 1` on the cube is `zagierL2chi_boxZ_norm_lt_one`), via the
`1/n³`-decomposition of the fleet lemma
`Commons.Analysis.InfiniteSum.tsum_quartic_div_nat_cube` (which requires
`‖Z‖ < 1` — exactly the box-norm fact) into the basis
`{Σn·Zⁿ, ΣZⁿ, ΣZⁿ/n, ΣZⁿ/n², ΣZⁿ/n³}` (summability:
`summable_geom_div_nat_pow`, `summable_nat_pow_mul_geom`; `ΣZⁿ/n =
−log(1−Z)` by `hasSum_div_nat_one_log`), interchanged with the box
integrals; and (c) identification of the resulting integral of
rational/log/dilog-type functions with the period
`−∫₀¹ log x/(1+x+x²)dx = L(2,χ₋₃)`.

First coefficient manipulation (for the polylog step): the polynomial
coefficient `(4−15n)(2n+1)²(3n+1)` is the quartic
`−180n⁴−192n³−41n²+13n+4`, i.e. the summand is a linear combination of
`n·Xⁿ`, `Xⁿ`, `Xⁿ/n`, `Xⁿ/n²`, `Xⁿ/n³` after division by `n³`. -/

/-- the summand of the hypergeometric series in integral form -/
def zagierL2chiIntegralTerm (n : ℕ) : ℝ :=
  ((4 - 15 * (n : ℝ)) * ((-27 : ℝ) ^ n) / (n : ℝ) ^ 3) *
    ((2 * (n : ℝ) + 1) * (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ n)) ^ 2 *
    ((3 * (n : ℝ) + 1) * (∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ (2 * n)))



/-- the polynomial coefficient of the integral summand, expanded -/
lemma zagierL2chi_coeff_poly (n : ℕ) :
    (4 - 15 * (n : ℝ)) * (2 * (n : ℝ) + 1) ^ 2 * (3 * (n : ℝ) + 1) =
      -180 * (n : ℝ) ^ 4 - 192 * (n : ℝ) ^ 3 - 41 * (n : ℝ) ^ 2 + 13 * (n : ℝ) + 4 := by
  ring

/-- after division by `n³` the summand coefficient splits into the
polylog basis `{n·Xⁿ, Xⁿ, Xⁿ/n, Xⁿ/n², Xⁿ/n³}` -/
lemma zagierL2chi_coeff_split (n : ℕ) (hn : n ≠ 0) :
    (-180 * (n : ℝ) ^ 4 - 192 * (n : ℝ) ^ 3 - 41 * (n : ℝ) ^ 2 + 13 * (n : ℝ) + 4) /
        (n : ℝ) ^ 3 =
      -180 * (n : ℝ) - 192 - 41 / (n : ℝ) + 13 / (n : ℝ) ^ 2 + 4 / (n : ℝ) ^ 3 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp [hn']


/-- the rational summand with `centralBinom` in the denominator -/
lemma zagierL2chiTerm_central (n : ℕ) :
    zagierL2chiTerm n = if n = 0 then 0 else
      ((4 - 15 * (n : ℚ)) * (-27 : ℚ) ^ n) /
        ((n : ℚ) ^ 3 * (Nat.centralBinom n : ℚ) ^ 2 * (Nat.choose (3 * n) n : ℚ)) := by
  unfold zagierL2chiTerm
  rw [Nat.centralBinom_eq_two_mul_choose]

/-- termwise equality of the rational summand with its integral form
(`n ≥ 1`): `tₙ = (4−15n)(−27)ⁿ/n³·((2n+1)∫₀¹(x(1−x))ⁿ)²·((3n+1)∫₀¹xⁿ(1−x)²ⁿ)` -/
lemma zagierL2chiTerm_eq_integralTerm (n : ℕ) (hn : 1 ≤ n) :
    (zagierL2chiTerm n : ℝ) = zagierL2chiIntegralTerm n := by
  have hreal : (zagierL2chiTerm n : ℝ) =
      ((4 - 15 * (n : ℝ)) * (-27 : ℝ) ^ n) /
        ((n : ℝ) ^ 3 * (Nat.centralBinom n : ℝ) ^ 2 * (Nat.choose (3 * n) n : ℝ)) := by
    rw [zagierL2chiTerm_central, if_neg (by omega : ¬ n = 0)]
    norm_num [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_sub]
  unfold zagierL2chiIntegralTerm
  rw [hreal]
  have hd := zagierL2chi_denom_integral n hn
  have hn' : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn))
  rw [← mul_one_div]
  rw [hd]
  field_simp [hn']


/-! ## Brick (ii) — geometric summation route (first summation lemma)

The master sums of the route are the geometric-type series
`Σₙ P(n)·Xⁿ` with polynomial weight.  The **first summation lemma** below
states the closed form for the quartic coefficient
`P(n) = (4−15n)(2n+1)²(3n+1) = −180n⁴−192n³−41n²+13n+4` (see
`zagierL2chi_coeff_poly`):

```lean
theorem zagierL2chi_sum_quartic {X : ℝ} (hX : ‖X‖ < 1) :
    (∑' n : ℕ, ((4 - 15 * (n : ℝ)) * (2 * (n : ℝ) + 1) ^ 2 * (3 * (n : ℝ) + 1)) * X ^ n) =
      (4 - 416 * X - 2530 * X ^ 2 - 1340 * X ^ 3 - 38 * X ^ 4) / (1 - X) ^ 5
```

(verified coefficient-wise: the numerator was obtained by combining
`Σₙ nᵏXⁿ = A_k(X)/(1−X)^{k+1}` for `k = 0..4`; e.g. coefficient of `X` is
`P(1) = −396`.)  Proof ingredients (fleet-ready once the shape is fixed):
summability of `Σₙ nᵏ·|X|ⁿ` for `‖X‖ < 1`, the master-sum closed forms, and
`hasSum_geometric_of_norm_lt_one` (the last is proved below as
`zagierL2chi_geom_hasSum`).  On the eventual box kernels
`X = −27·x(1−x)y(1−y)z(1−z)²` the hypothesis `‖X‖ < 1` holds since
`|x(1−x)| ≤ 1/4`, `|z(1−z)²| ≤ 4/27` (max at `z = 1/3`), giving
`|X| ≤ 1/4`. -/

/-- `Σₙ Xⁿ = (1−X)⁻¹` for `‖X‖ < 1` (the base of the geometric route) -/
lemma zagierL2chi_geom_hasSum {X : ℝ} (hX : ‖X‖ < 1) :
    HasSum (fun n : ℕ => X ^ n) (1 - X)⁻¹ := by
  exact hasSum_geometric_of_norm_lt_one hX

/-- **first summation lemma — DONE**: closed form of `Σₙ P(n)·Xⁿ` for the
quartic coefficient `P(n) = (4−15n)(2n+1)²(3n+1)`, `‖X‖ < 1`.  Proof:
expand `P(n)` by `zagierL2chi_coeff_poly` into the monomial basis, then
combine the five geometric master sums (`hasSum_geometric_of_norm_lt_one`
for `k = 0`, and the commons `nat_mul/sq/cube/pow4_geom_hasSum` for
`k = 1..4`) by `HasSum.mul_left`/`add`; the combined value reduces to the
stated rational function by `field_simp`. -/
theorem zagierL2chi_sum_quartic {X : ℝ} (hX : ‖X‖ < 1) :
    (∑' n : ℕ, ((4 - 15 * (n : ℝ)) * (2 * (n : ℝ) + 1) ^ 2 * (3 * (n : ℝ) + 1)) * X ^ n) =
      (4 - 416 * X - 2530 * X ^ 2 - 1340 * X ^ 3 - 38 * X ^ 4) / (1 - X) ^ 5 := by
  have hgeom := hasSum_geometric_of_norm_lt_one hX
  have h1 := Commons.Analysis.InfiniteSum.nat_mul_geom_hasSum hX
  have h2 := Commons.Analysis.InfiniteSum.nat_sq_geom_hasSum hX
  have h3 := Commons.Analysis.InfiniteSum.nat_cube_geom_hasSum hX
  have h4 := Commons.Analysis.InfiniteSum.nat_pow4_geom_hasSum hX
  have h0s := hgeom.mul_left (4 : ℝ)
  have h1s := h1.mul_left (13 : ℝ)
  have h2s := h2.mul_left (-41 : ℝ)
  have h3s := h3.mul_left (-192 : ℝ)
  have h4s := h4.mul_left (-180 : ℝ)
  have hsum : HasSum
      (fun n : ℕ => (4 : ℝ) * X ^ n + 13 * ((n : ℝ) * X ^ n) + (-41) * ((n : ℝ) ^ 2 * X ^ n)
        + (-192) * ((n : ℝ) ^ 3 * X ^ n) + (-180) * ((n : ℝ) ^ 4 * X ^ n))
      (4 * ((1 - X)⁻¹) + 13 * (X / (1 - X) ^ 2) + (-41) * (X * (1 + X) / (1 - X) ^ 3)
        + (-192) * (X * (1 + 4 * X + X ^ 2) / (1 - X) ^ 4)
        + (-180) * (X * (1 + 11 * X + 11 * X ^ 2 + X ^ 3) / (1 - X) ^ 5)) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      (((h0s.add h1s).add h2s).add h3s).add h4s
  have hpt : (fun n : ℕ => ((4 - 15 * (n : ℝ)) * (2 * (n : ℝ) + 1) ^ 2 * (3 * (n : ℝ) + 1)) * X ^ n) =
      fun n : ℕ => (4 : ℝ) * X ^ n + 13 * ((n : ℝ) * X ^ n) + (-41) * ((n : ℝ) ^ 2 * X ^ n)
        + (-192) * ((n : ℝ) ^ 3 * X ^ n) + (-180) * ((n : ℝ) ^ 4 * X ^ n) := by
    funext n
    rw [zagierL2chi_coeff_poly n]
    ring
  have hval : (4 * ((1 - X)⁻¹) + 13 * (X / (1 - X) ^ 2) + (-41) * (X * (1 + X) / (1 - X) ^ 3)
        + (-192) * (X * (1 + 4 * X + X ^ 2) / (1 - X) ^ 4)
        + (-180) * (X * (1 + 11 * X + 11 * X ^ 2 + X ^ 3) / (1 - X) ^ 5)) =
      (4 - 416 * X - 2530 * X ^ 2 - 1340 * X ^ 3 - 38 * X ^ 4) / (1 - X) ^ 5 := by
    have hX1 : X ≠ 1 := by
      intro h
      rw [h] at hX
      norm_num at hX
    have hne : (1 : ℝ) - X ≠ 0 := sub_ne_zero.mpr (Ne.symm hX1)
    field_simp [hne]
    ring_nf
  rw [hpt]
  rw [hsum.tsum_eq]
  exact hval

/-! ## Brick (ii) — box-integral setup (kernel bounds)

The geometric-summation hypotheses `‖X‖ < 1` hold on the eventual box
kernels `X = −27·x(1−x)·y(1−y)·z(1−z)²` because on the unit cube
`|x(1−x)| ≤ 1/4`, `|y(1−y)| ≤ 1/4`, `|z(1−z)²| ≤ 4/27` (max at `z = 1/3`),
giving `‖X‖ ≤ 27·(1/4)·(1/4)·(4/27) = 1/4 < 1`.  These bounds are the
interchange/domination hypotheses for the summation-inside-the-box step. -/

lemma le_quarter_mul_one_sub (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x * (1 - x) ≤ (1 : ℝ) / 4 := by
  have hsq : 0 ≤ (1 - 2 * x) ^ 2 := sq_nonneg (1 - 2 * x)
  nlinarith

lemma le_four_over_27_mul_one_sub_sq (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x * (1 - x) ^ 2 ≤ 4 / 27 := by
  have hsq : 0 ≤ (1 - 3 * x) ^ 2 := sq_nonneg (1 - 3 * x)
  have hpos : 0 ≤ 4 - 3 * x := by nlinarith
  have hsqpos : 0 ≤ (1 - 3 * x) ^ 2 * (4 - 3 * x) := mul_nonneg hsq hpos
  nlinarith

/-- the box kernel bound: `|−27·x(1−x)y(1−y)z(1−z)²| ≤ 1/4` on the unit cube -/
lemma box_kernel_le (x y z : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |(-27 : ℝ) * x * (1 - x) * y * (1 - y) * z * (1 - z) ^ 2| ≤ 1 / 4 := by
  have h1 := le_quarter_mul_one_sub x hx0 hx1
  have h2 := le_quarter_mul_one_sub y hy0 hy1
  have h3 := le_four_over_27_mul_one_sub_sq z hz0 hz1
  have hx01 : 0 ≤ x * (1 - x) := by nlinarith
  have hy01 : 0 ≤ y * (1 - y) := by nlinarith
  have hz01 : 0 ≤ z * (1 - z) ^ 2 := by nlinarith
  have hABC : x * (1 - x) * (y * (1 - y)) * (z * (1 - z) ^ 2) ≤ (1 / 4) * (1 / 4) * (4 / 27) := by
    gcongr
  have hP0 : 0 ≤ x * (1 - x) * (y * (1 - y)) * (z * (1 - z) ^ 2) := by
    exact mul_nonneg (mul_nonneg hx01 hy01) hz01
  have h27P0 : 0 ≤ 27 * (x * (1 - x) * (y * (1 - y)) * (z * (1 - z) ^ 2)) := by
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 27) hP0
  calc
    |(-27 : ℝ) * x * (1 - x) * y * (1 - y) * z * (1 - z) ^ 2|
        = 27 * (x * (1 - x) * (y * (1 - y)) * (z * (1 - z) ^ 2)) := by
          rw [show (-27 : ℝ) * x * (1 - x) * y * (1 - y) * z * (1 - z) ^ 2 =
              -27 * (x * (1 - x) * (y * (1 - y)) * (z * (1 - z) ^ 2)) by ring]
          have hnonpos : -27 * (x * (1 - x) * (y * (1 - y)) * (z * (1 - z) ^ 2)) ≤ 0 := by
            exact mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-27 : ℝ) ≤ 0) hP0
          rw [abs_of_nonpos hnonpos]
          ring
    _ ≤ 27 * ((1 / 4) * (1 / 4) * (4 / 27)) := by
          exact mul_le_mul_of_nonneg_left hABC (by norm_num : (0 : ℝ) ≤ 27)
    _ = 1 / 4 := by norm_num


/-- on the unit cube the box kernel satisfies `‖X‖ < 1` for
`X = −27·x(1−x)y(1−y)z(1−z)²` (so the geometric/polylog master sums apply) -/
lemma zagierL2chi_kernel_norm_lt_one (x y z : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ‖(-27 : ℝ) * x * (1 - x) * y * (1 - y) * z * (1 - z) ^ 2‖ < 1 := by
  rw [Real.norm_eq_abs]
  exact lt_of_le_of_lt (box_kernel_le x y z hx0 hx1 hy0 hy1 hz0 hz1) (by norm_num : (1 / 4 : ℝ) < 1)

/-- the kernel `Z` of the `1/n³`-weighted geometric sum on the box:
`Z = −27·x(1−x)·y(1−y)·z(1−z)²` -/
def zagierL2chiBoxZ (x y z : ℝ) : ℝ :=
  (-27 : ℝ) * x * (1 - x) * y * (1 - y) * z * (1 - z) ^ 2

/-- with the box-kernel `Z`, the geometric/polylog hypotheses `‖Z‖ < 1` hold
pointwise on the unit cube (this is the domination fact that legitimises the
summation-inside-the-integral step toward `zagierL2chi_leaf_main`) -/
lemma zagierL2chi_boxZ_norm_lt_one (x y z : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ‖zagierL2chiBoxZ x y z‖ < 1 := by
  exact zagierL2chi_kernel_norm_lt_one x y z hx0 hx1 hy0 hy1 hz0 hz1


/-- pointwise domination of the kernel powers on the unit cube:
`|Z(x,y,z)|ⁿ ≤ (1/4)ⁿ` for the box kernel `Z = zagierL2chiBoxZ` -/
lemma zagierL2chi_boxZ_abs_pow_le (x y z : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (n : ℕ) :
    |zagierL2chiBoxZ x y z| ^ n ≤ (1 / 4 : ℝ) ^ n := by
  have hle := zagierL2chi_boxZ_norm_lt_one x y z hx0 hx1 hy0 hy1 hz0 hz1
  -- ‖Z‖ < 1 and box_kernel_le give ‖Z‖ ≤ 1/4:
  have hk : ‖zagierL2chiBoxZ x y z‖ ≤ 1 / 4 := by
    rw [Real.norm_eq_abs, zagierL2chiBoxZ]
    exact box_kernel_le x y z hx0 hx1 hy0 hy1 hz0 hz1
  have hk0 : 0 ≤ ‖zagierL2chiBoxZ x y z‖ := norm_nonneg _
  rw [Real.norm_eq_abs] at hk
  exact pow_le_pow_left₀ hk0 hk n



/-- pointwise power identity for the box kernel `Z = zagierL2chiBoxZ` -/
lemma zagierL2chiBoxZ_pow_eq (x y z : ℝ) (n : ℕ) :
    (zagierL2chiBoxZ x y z) ^ n =
      (-27 : ℝ) ^ n * (x * (1 - x)) ^ n * (y * (1 - y)) ^ n * (z * (1 - z) ^ 2) ^ n := by
  rw [zagierL2chiBoxZ]
  rw [show (-27 : ℝ) * x * (1 - x) * y * (1 - y) * z * (1 - z) ^ 2 =
      (((-27 : ℝ) * (x * (1 - x))) * (y * (1 - y))) * (z * (1 - z) ^ 2) by ring]
  rw [mul_pow, mul_pow, mul_pow]

/-- `∫₀¹ (x(1−x)²)ⁿ dx = ∫₀¹ xⁿ(1−x)^{2n} dx` -/
lemma int_one_sub_sq_pow_eq (n : ℕ) :
    (∫ x in (0 : ℝ)..1, (x * (1 - x) ^ 2) ^ n) =
      ∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ (2 * n) := by
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp
  rw [mul_pow]
  rw [← pow_mul (1 - x) 2 n]

/-- triple integral of the box-kernel power over the unit cube:
`∫₀¹∫₀¹∫₀¹ Z(x,y,z)ⁿ = (−27)ⁿ·(∫₀¹(x(1−x))ⁿ)²·(∫₀¹ xⁿ(1−x)^{2n})` -/
lemma zagierL2chiBoxZ_pow_triple (n : ℕ) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1,
        (zagierL2chiBoxZ x y z) ^ n) =
      (-27 : ℝ) ^ n *
        (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ n) ^ 2 *
        (∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ (2 * n)) := by
  have hf : IntervalIntegrable (fun x : ℝ => (-27 : ℝ) ^ n * (x * (1 - x)) ^ n)
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hg : IntervalIntegrable (fun y : ℝ => (y * (1 - y)) ^ n)
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hh : IntervalIntegrable (fun z : ℝ => (z * (1 - z) ^ 2) ^ n)
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hL := Commons.Analysis.Integral.integral_mul_integral_mul_integral_interval
      (fun x : ℝ => (-27 : ℝ) ^ n * (x * (1 - x)) ^ n) (fun y : ℝ => (y * (1 - y)) ^ n)
      (fun z : ℝ => (z * (1 - z) ^ 2) ^ n) hf hg hh
  calc
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1,
        (zagierL2chiBoxZ x y z) ^ n)
        = (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1,
            ((-27 : ℝ) ^ n * (x * (1 - x)) ^ n) * (y * (1 - y)) ^ n * (z * (1 - z) ^ 2) ^ n) := by
          apply intervalIntegral.integral_congr
          intro x hx
          apply intervalIntegral.integral_congr
          intro y hy
          apply intervalIntegral.integral_congr
          intro z hz
          dsimp
          rw [zagierL2chiBoxZ_pow_eq]
    _ = ((∫ x in (0 : ℝ)..1, (-27 : ℝ) ^ n * (x * (1 - x)) ^ n) *
          (∫ y in (0 : ℝ)..1, (y * (1 - y)) ^ n)) *
          (∫ z in (0 : ℝ)..1, (z * (1 - z) ^ 2) ^ n) := by
          rw [← hL]
    _ = (-27 : ℝ) ^ n *
          (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ n) ^ 2 *
          (∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ (2 * n)) := by
          rw [intervalIntegral.integral_const_mul]
          rw [int_one_sub_sq_pow_eq]
          ring

/-- the integral summand of the hypergeometric series is a box (triple)
integral over the unit cube:
`tₙ = ∫₀¹∫₀¹∫₀¹ P(n)·Z(x,y,z)ⁿ/n³` with `Z = zagierL2chiBoxZ` and
`P(n) = (4−15n)(2n+1)²(3n+1)` -/
theorem zagierL2chiIntegralTerm_box (n : ℕ) :
    zagierL2chiIntegralTerm n =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1,
        (((4 - 15 * (n : ℝ)) * (2 * (n : ℝ) + 1) ^ 2 * (3 * (n : ℝ) + 1)) *
          (zagierL2chiBoxZ x y z) ^ n / (n : ℝ) ^ 3) := by
  let P : ℝ := (4 - 15 * (n : ℝ)) * (2 * (n : ℝ) + 1) ^ 2 * (3 * (n : ℝ) + 1)
  let d : ℝ := (-27 : ℝ) ^ n
  let I : ℝ := ∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ n
  let J : ℝ := ∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ (2 * n)
  have hprod : (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1,
        (zagierL2chiBoxZ x y z) ^ n) = d * I ^ 2 * J := by
    dsimp [d, I, J]
    rw [zagierL2chiBoxZ_pow_triple]
  have hf : IntervalIntegrable
      (fun x : ℝ => (P * d / (n : ℝ) ^ 3) * (x * (1 - x)) ^ n)
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hg : IntervalIntegrable (fun y : ℝ => (y * (1 - y)) ^ n)
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hh : IntervalIntegrable (fun z : ℝ => (z * (1 - z) ^ 2) ^ n)
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hL := Commons.Analysis.Integral.integral_mul_integral_mul_integral_interval
      (fun x : ℝ => (P * d / (n : ℝ) ^ 3) * (x * (1 - x)) ^ n)
      (fun y : ℝ => (y * (1 - y)) ^ n) (fun z : ℝ => (z * (1 - z) ^ 2) ^ n) hf hg hh
  have htriple : (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1,
        P * (zagierL2chiBoxZ x y z) ^ n / (n : ℝ) ^ 3) = P * d / (n : ℝ) ^ 3 * I ^ 2 * J := by
    calc
      (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1,
          P * (zagierL2chiBoxZ x y z) ^ n / (n : ℝ) ^ 3)
          = (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1,
              ((P * d / (n : ℝ) ^ 3) * (x * (1 - x)) ^ n) * (y * (1 - y)) ^ n *
                (z * (1 - z) ^ 2) ^ n) := by
            apply intervalIntegral.integral_congr
            intro x hx
            apply intervalIntegral.integral_congr
            intro y hy
            apply intervalIntegral.integral_congr
            intro z hz
            dsimp
            rw [zagierL2chiBoxZ_pow_eq]
            ring
      _ = ((∫ x in (0 : ℝ)..1, (P * d / (n : ℝ) ^ 3) * (x * (1 - x)) ^ n) *
            (∫ y in (0 : ℝ)..1, (y * (1 - y)) ^ n)) *
            (∫ z in (0 : ℝ)..1, (z * (1 - z) ^ 2) ^ n) := by
            rw [← hL]
      _ = P * d / (n : ℝ) ^ 3 * I ^ 2 * J := by
            rw [intervalIntegral.integral_const_mul]
            rw [int_one_sub_sq_pow_eq]
            dsimp [I, J]
            ring
  calc
    zagierL2chiIntegralTerm n
        = P * d / (n : ℝ) ^ 3 * I ^ 2 * J := by
          unfold zagierL2chiIntegralTerm
          dsimp [P, d, I, J]
          ring
    _ = (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1,
          (((4 - 15 * (n : ℝ)) * (2 * (n : ℝ) + 1) ^ 2 * (3 * (n : ℝ) + 1)) *
            (zagierL2chiBoxZ x y z) ^ n / (n : ℝ) ^ 3)) := by
          exact htriple.symm

end Submission.CDT
